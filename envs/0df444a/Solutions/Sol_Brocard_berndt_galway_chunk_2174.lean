-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:17.314703+00:00
-- url     : https://prove2.me/submissions/e3bbc700-acca-4996-8b52-c4f47782a43c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 390827338 ≤ n < 391007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 390828588 1250 390827338 390827341
    0xb16021e060f0903120f010e01080d0e04050a021605012a1b020d061d010c210509072102090109052a04090606050409060e0f01030f1703150a060206060612 68
    0x141c03a20391700a9401d43d0a094500800308610780c450200a241243c0c0714550b41700503640c07101b041680b6246005807010004102d008800c101c0d1405400283c2c1280c0543c000520f018a1842c22103001403100700140c400e691506401c500556220404100c2e94000d900090381c1c034044510028010800c6d03a0001c42110b01c0c00039880155540c01c0880743d0520ba0024041080380c2140d858507890502d0019105450b500e00720040d0380c400d0260310444c0c00034200f00709001962444096800090070302801000c418407585001007080340c1a00085640d1000d01105880d0b030301c10f18410446100416007115507082d050000b80801c4819080484020b0441e0320340b1840780e100341110b66209800f40390302c07031400642001e000040c0c1075000002001541e909c950b0601c001c17034896600c0c0780158002d80703140808103007090040000c10383c0c00304000301640c424202c00c2003030001d44600d5850b503003060ba8032120413030906550451500c0c081403c40001c20f0f150020300018034000f000240b25004145500314040042070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 390829838 1250 390828588 390828601
    0x302090a0b03030d0603050615040219082208070b010815010303120f051801060f080a02100302090604090203010512010504032f03030403230301030206071203090b16021e060f 77
    0x10a60702070484d100c0303080240c1941c0b0304000c0e0b600e41e42600c48041c0049001c1440c4081d0416008a070710919802c92140701e401618a001c88548030010180041d00d0340c03540c0000c0d0107850b0030300803030704003409035162985030411410186011071040e0302800305980814203141022601c45600390451b9014140506e40420351a201d801a1140f10111201d00707250504010340200c01d000035120403441d140003041116101c3c0f04c60743e840d04040c05000c10300d40c808070341c2c0700061800700c1119032203600314030b0702504000105000c181a0b4120303410117101a90003100522050070081ca20416001c4139000071f001c00e04041d04e01621141070604c04515148012604a02101c0401e03020903009001c032040341e0b501d140a040040144184041003240305600241509084c03080c0c40c1902d040c2c0350000d0403a441c0481c260388450021814040080506403038002d5030b800720b02400d0081e4032429141d54144111a07480f4002400e00000e04604100c50b03502d8908154011170000e4201d40c00300304049110040d440e0007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 390831088 1250 390829838 390829843
    0x1204030c03050921010b0108060f06130807060804030f080402150f0c0f1005010f062f1b03010e0102040f0e060301020403080d02070201080c07121409100207080c0405010302090a0b03 80
    0x102c0b10f01c3e003107140c9400400045091156126200c10000c1c02000508110401190401030a403070306584200f455980c3c001c0c500d88540180582d04207803000c1d4445664802143e400c080040c0d0043c000308207980c00b000b0078983c01c004071582e845620310340301c40c040c81c2c40d03800520350300d801c003242c1000750701c0208441c282c41c1080001c407030512240c407089485034405080c044d55104a0f00032070101c254102400007440d094854400c0d020340da0340e40c840083c090340e1354480e400c6046007101003480300d43c1e21800400c02480c0500c800580a00810b01003654030408205050950301c1d85400c10281ea07204001c02c0001c4a20314002805071400707405818201d4407100300082c068080d80d0409010054005903c18040302d141e401003013414400e8031303015200d0355483c9081c1c1e1039015510000e0403030012a038143d002d59100b26201c0e800490104021402c0890b44800700d60222400e103141409a44221070500121030204203c0b151890119400d020540c15a4080740a1501c060820000e00303494145904283c0c0c1c05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 390832338 1250 390831088 390831097
    0x8031f09091b1a0f0706060302091e070e061803070806011e05031b060a02071a041802090d020d1e0c0501030e06042d0f050f0f031204030c0305 63
    0x484038107000741122410040390405041c0c980c10b10380e82820000284420818180320b00185094412504221603a143c44480f688051000c95010f581c4a0000c0b0050b80c0381c1000c0d0340206644c403170428903124010900588200c0150207d814000301c420443c84a0340c4200441d101c04102d180007608004502010078681101600106020300417a03001007507a2103a0080c0710038000c039080d5000e07100d507070380c03014592111015020340b4031400e2030094080248c00c1c141d0040076015082c0c030407546140d80d680301131884070b50314942c07025200300002820003400e007000101c01403074100290110302c0c185204000407500f0103078401c024014001444030b8824007080c00703250b10303c0d8900390924501c40d510301e1600c1242200140580342c0402d15020117000512000580380d0300ca182e001409020600900c0c20b440500f0b41521440308018008613040400160024405004148258001c0c10341d10400d4401900b04401c01151078038039030041c0122845a00542c88103900203805045c00c148002a50a084416108 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 390833588 1250 390832338 390832349
    0x72108060d05060112260a021513020904020d060501090b01020f1c030c180b0a080f07080c03060f0303070602030a1d0a1104060801020a0206012d05130b0d2105040308031f 75
    0x82c17140d0116140092600030158447c10741c0c262885594001d00c0702481c0b076001c3d6483c41d42d80100f00014001824481c05681d00180010a1000c0200300c40d55542c003555026004800743c03588681e00b402040d60100500c58110107008054406507614035207080c00e0150b105039004c20580c0350030384400d185016100340744464802180501c0b240b5200d400d00c1c1265801500790b000021100d40c002100d00203010303403150040c0e00303a0b035542c00280c443d0403000420350005815144c1c810702494805240740d0b0100000c00e40c60384600005a2207160a090b104c0440b606c10303c0540d0030205034510322140720401310308a011b032584011600b4a4944a0000c10003c081542104020b5803000442c2c00019800007201d41c100c41405502c00d040b1900541024001401103180c5200d07100290814002d81ca032035610f89075200446a000241503a5100018030700007400d003000d0b00c15240b20100f55403c188150102000b4004c903042c05c9203050b18560b0386034010320004000d521130380a01d07a0800440b0b076440d00e0a200a24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 390834838 1250 390833588 390833633
    0xd050c09120307030f050c06070c061116060c030905100f06030f08120a020f091e06070c06020f0303060f012f0c0a0f030f0201080a02072108060d05060112 68
    0x1d88141d5440e0b6903804900140d01050b800014005080d11030411110003900c42c002500980d102d1040070380b4280482c540884525444012078005c405c0c0120103000900703a00c2400100025032400c00c00120360b0071035020310425040481280c003103040007c0740d400c4030040c61000070b440c4401c07040320401420140c00007080c40003038000d02c10512a07418040c0070303030028000800446403107407984c110481c4141103501c100d001042c0513106030361410082001d0442c00e010608400c43e40b62400281340d030351000008549416040805216050781000368040c106845802145981001c20008501c964010704190410200950b11005140d22074070000c6040007101c11015100c466200440d100c5204028190141c03511403c0091040b12028011080329000308183c0c0d00c0b28159001107071041d400504880c0510f40812200000402c1341c198440460f0440c2040e0b17800c211040c000420040e405400e8910a0b0a0104503a01041012a48504441020491040005d0245005005000c03903d00382c65041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 390836088 1250 390834838 390834859
    0x18061c0504060504020102010510050a1203140408070810060515070f120f0e0102061303052b020301060e0103140a0209010c02062703030c0c100e1c0212120d050c09 72
    0x80b6103900200c1c000ca2007600284480d5a6034602e15200700c44074811542d0000046034100454016010204c5041c5c0c000e150000740780040c16042485503110764000c2c40c09502000003000000410f0020704030300b1040c0c690912250349443d00282c0551385903172100400341b4001500c8810401007254001d041d50b444403903010140302e83c15015118000b182242008a003940503060200e40c8049110f030711034040c584980e5622001c40d00e04894507040030110500c802000c80c20b02c0e0b0489621100c50307524004001d405a0f43c1c0d81040c0d4000c041c1c0a0ac2d1031468103160030154612900401c00310000c1d480140f44500580340c030041001201c21840d441d2000e5000600010b0004143c109500384020b9000a0341b18081c10307200020500d9075900c076440300320949800c80c00c0d00c65003e01e400f0050f6410285180340c10b20624004a0008900c800c14003105010012000b4146045003440582d0002c0d106242024200446203d5800e401c64403a482d03801c1d4000d556000064214034008081d41c02d000b1024100d102030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 390837338 1250 390836088 390836093
    0x11401120210050c102a080a091a04060207050c01050c15190f0204030c12030c06230a05150f18041a01062c0f09060301060905151518061c0504 63
    0x100020b440850f80032003500c06c4134a5511049022449205040c0e44040c50740d603c000400d0028002c25a0071104412141e0482850704c8030380620502490081d0001030340c23180a490254501081e00e203845050020900505034099070214643d140c00e0200c40810b6030540d546139000111801c0c2540301c01c03803070385030680c1058456602d50181042d41d22580310185841d407245401442a0f0901074002e00282c58400c0907030010361190820000a1290040ca040c1720380062040514a60100c0342d0841c660750b0b500030015140128415403050000079100009401950008500032410540140840341a60780200f000c00c0091040c034060032103480700403081540c642c080100381c070709410714010391b000030301501c08440c84802840c0130461100410380740b182c41001d414081c0c03c010041c4210303415580c4400000351401d55025982c032450903400501c40c1994102c4c100014513150482228118500344031000e10240504101030034240100c500c16120685140b0400c0165038200d25280c134030b4104001d01c800c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 390838588 1250 390837338 390837341
    0xe01090e04030215090d02010608150105060705030910030c080601082a0f0c0601062a020f06070203060a0e0d0302040f060c021c1203180b0601030507020307021c05011401120210050c10 81
    0x20202c00c1d6600a204071541c801d50719a07560380100e44180d400441382f004100d14070b4031800611217284203205680c01d211003000000e2005e0b1602440ba0007098540300300f40581d030303404814550b01c86001d003002c21003410603180e031020800f650040c2542e280380e9151040360382100a810380b200c07040c492151590f520600d0f02d05c0f60721441c081c0318550100d03507005240100b01080601207081030244422031030829030f9580810503a43c4181420301d81041c81040040c0142c0c0302804114887c0e04546d40214001d1900140d0b130b86001e130740d0420142014070500051007640e40c07074140001220303061b14008000b0503290001a0821070490124980080009210170411081c0c605c941d100c1c4103540c4040105443d1001400c2c4600e8650900402c5401c0365070000b8002d601903441141c0101461041f41c2c10000281d0104041a140e81c09217000842600384101c200803090180c1240c441c6110300c5100300d0b500d044001c207240302901000a100780240d82400c0d10662048040e100f810b441601140c16100d0500031010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 390839838 1250 390838588 390838603
    0x708070e06160507180e0601121101030f02071a0c0c2505090103060506150c0d03051005060403050f010b100c0312020d0204091a030f0304030204020d060801021c0c0e01090e0403021509 81
    0x30700da410500c0b8a20b10803004640e40c2e0488045116607910003270070b80c0d10300d0750080e2200030b11814103035070341c00f40c90340500c49101800702103101e0659082c01c4120a64010900d200082400783c1509040040c000640d2010038500c0e481d201012411074503440c4e0104041280d60a40c002c00d82054011000005000031500403c0c000d01060710140c01c20300d008952100e0a106507101e424076580403645d10705d65503102c0d034010740d80b004120351803801c1d080d221000a2819445944280c030b60754002844c4036100e407020f201c3c0598501c0b080311241070700323030302680003408207900c542d0003a090150b2000c0098107440e0750b070121012400c5200c1c0c119610380c0c030780d20284010500c01c131040190b18903403407907030340a420002581241c1c000d1817402035040501d141c0c00c00010b980b144110412054030b075200000d59410034006405c0c010b07080034000070b902190300c4e04c2c10103e0701c110080f05c0810481010580050341c0042c509010b9940c0ba600c288003960301d0b41000c3c2c0c5050000514000402d0040040203888400415001e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 390841088 1250 390839838 390839879
    0xb070810080a031707030608031b07090504260c1006030b0603150619170304330e0d0b01030b01150206010506030610091206020904050708070e06160507 67
    0x296040360301c40c110959240d00311040100803c091907405181e181602090580c081504d14010625684440003582176401c94946000f1140b208000c0c2c9139160403d110140c080e01802800300210315043d254004207191030010a030088101542d20182401d400b002c61708002c0042c02110000f640d0030400f00c0052015100aa40c0103625001040e424038010801c2007005821070544085500c0b001c003007000303ea039031000208515440c0d0174002044400030704c000c0c440aa1000c05107440718a42142e281142103a003909541020502c2605034a5100420310508107118a00d002c1c066403080001146020340845000341030006803034000400c002c1284c0e201e6058508030211440c0f403034851003043c4c0c2d40c3c11081c054184d0003c414400101c0c1030130f285648500ca000c42c1c0c588000b959507551000344581c6401182540d481c0d400190410940c249030003115000305542c40c1800e001d280503a001041c1501d0b40818a2007070000280346604d19610341400810190090152002d07030369118500004490120001c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 390842338 1250 390841088 390841111
    0x1021501150908011503060b0303070b090d26010902070c05191a0c060103110301111201090b0603040809090a02040f09091407030f0b04060615020a060b0a1202090a02070b0708 77
    0x1c80c000c90f06000d090000c41c44440c280380140d0441d03030780c54007601000b008070350188400e02c48540850111020740340666011009003a10b00d1540b1001008580e540c0304028800707045020390348200c840540480e0458803c1e003c0140c176842c85140441482c01c07640d2100ba4011055a40c02c0000410109118101d5904001c0c1a03d0000380114490280c0511007401105810840042000c1400242030001c80d2a001700005008001440c0d4002d15401460702c6442040d0010010f02044010344205251003c088a800c0e003185029a40c0010b544290701c0d125000c1c1800b10040740486c4815019170700a40010500403c659454000a0000341040e10090b1034204c01545814040180860a1003c0e690404502120201c00c7c1c0c0b9040541d6101510444100c2c0e030704c0c00c00003450a450748005004c02400d50240c80e2701400c500300803066640002074a4460b0764100710800403080941c1280f51310b50750503140d051155403000d8081001340182d48015101403142410445407913404180d1501c1203001144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 390843588 1250 390842338 390842357
    0x8070302330a11101e180b100e07021501141908100f05010506160317013503030106030f02040f242a050109050f070f050111030a0e0102150115 63
    0x400070540e440301816464542422010303c007005646e40092500080010b6044404409a40d42c042400021100c1c080000b60501040c00200b83e031203000b44c0c004680744001c001401051100c0150510180f14082c1c81c1d840b0219600425200c500a416401d254480c04010326a9a038003945d0301c0707004021329107000603c1c0800d440030b6000d4074420036041c0da81c003070180e500f041e21800046c298480c01010685c18850304000c80d8074181e01d40b04c1e856002e006000705c0b28440318240c0d03c2c00c2c00b619111401419600407040307541d5405c03900000a503811600c9918010402d00292038403030b0000d209640001c560300c4105c0354040390b0240b03641310700d5501e822500c5800d100c44660313000c01c891003001c080301400e50600001072500e2070140e0100f01c0000754058000001c08919655900b131810209011040c0e0f160040c0c1d81c10004c0303800c10201d0f0710081c4403c1c01d00c20000c01040c1d04290301c0b8031400960b807090003d01c0d0341425250340b00308421120109007150701e280c69615850b072084280f501c0400400011580c82 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 390844838 1250 390843588 390843613
    0x706082517070810170c090c0c0102030114010e101e120f0e0c090c0a140913091211030720060703110c0604030305120a0f110903060108070302330a11 66
    0x1507440151a40d005d001e014008004010098800300140040004003030030701618401c60400e00c000c40c000c00b443d20702410f24810703240026141cac04a803141f0512a80020702d920000903080b0340c2040f200c80c810300d0303041c030f0003d40040243e5000001041c4803031a20300e41803540f900401280e0100d02404000d1080301e605d040513030104075400c8801c840d843d0004130140103200c0c800b07001d010301e0070120101c042018184175a002c0410000340d8600380c0c1c12641c80d01c87c02c02c0350a00504e100c01500790356052918298042146480940e03c1c400c02d03000030040090655183c00d94814030406c016543c400400076940d6401c84d080c01070a074604d09405100b140100d0400320000e142c0b800448046036070644419042c180f401011074200d640081c00d480c0e0043d01c2d494046080455440342802010000303101c191074101040c00d061401c40160000001640701e40d6060000d6500c85443d41c0c03c0c4410f100740292030f113001520060503181110322580700348030b000c54503107401e40d0400e440f16000c00041046400c800d00b42c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 390846088 1250 390844838 390844859
    0x30d0204141503010819020607060c0c030909020307020c0f130504030917010501260a02030d0c140105011a0a0c0b01170606041e020a0207180501080706082517070810 73
    0x1c0c451040d060f8040720b105146c55081d140d00104083c0005d040c82d04006007500c3e107406984014400200041c04100900105500322040c1d03009009921811400d524040001a55981048170703100d20810b000000402c1550b120850a4003a49540109111070300b001d02e4040c00a801c4c50040038603005003a0095007880c0b0341442400e041b664040001d6000070050b0091008189403003412a5003405105c54140250318104512a00c0960540d10302c001140d850030800d01d41c250f88400c021843e41020010404070b030741240c1c3c620031110031038900780d0348410a4034180c45003104d034807005107600134083c000a00252200226070240107400b09468256407100108822100d0000314040f00303130441c07030072981d881c500365000e05892481070045a85107512080c40c03220b01c040f14054051003980703a100600a100060010200400d40c5003008403c030306084121aa0302c1d0706106e004903075800081d00801040703100e1400416195403070441c0da811400c0c00c800041004400301e13440083c14a480b0800141000d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 390847338 1250 390846088 390846091
    0xc150f08090601121a0106020606130b0d03110f0106030602031009090c18330e01060c0f0c030206131a1c020d150e040201080f16030e030d0204141503 66
    0x705015000e40c0c0c0c00d01c8011601e09040200c180d4039440a1021040085029900030b0f0281609400504082c5091000c00c00c80913042c076440300070346d8100310b0034000d140c50320031030b04c50410741c1410500101e0350032442840c40c200100848030b00360360130b2010002c00e120540c0d0046005100c032100740c0da012500d54030200c00351609080010481d01101004111035044942c11750100c1100300c80c0450502c6049405040b00c280f00d04c805107480100c54a84900c69080080c400020b07c04084200095858240c005d4104406800702410796030541c41214104440023201f81c010b194020311440c0c594040c8210154580c045004c1c200c4c40c100e00342086101403a00f401501c60400c441d004400c10380d45040540f5000e5009072141000094584468409a600503610a0040c100c41c1c6003440042c945400014441c180140c51429103a020b4001d104140310b100240c3e1002c4030141c00c0106851260f107050524503c502c502c494129031002c240840c58440380469110355203c00c0392000b000c200351640c0000103100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 390848588 1250 390847338 390847351
    0x106120204182a020304080601061107060e180708190515061e0f07061401031104022a0f0c0603062d040c0302040e09150c090d0c150f08 60
    0xc404524110515243c00074078103024284140c0c6196034460008400300c030183d00d5160090b030404201405000c1b0200030b014014003151034451001e000170114607441d090540109010007202420b0031100e600d0301c4004445442c040c1082c400145030a010050190200790b0386050304403071001008160f00c00c14095035002e08040381c110021f506002041000c540d01c8100310307201a1520484203158141007002500002c41100344140e9030704424503088003100d5109503500c481c0c03842c0c5030060001c500c003030a07100003d502c10b0b540141e8401e20035100684405030000c150052a0a0200711250304101181084580307003100206d03840382410804200060000f00c624523004205080301c2d0020010b400031003501c100392082103241d4414202c010800b92403043d12800003080c1c00040404c5158840900c03641d101c1c00b48400b904c1c0300e0f14645840740740c208001d417103203403103040109000c0542e50300c4180b00050154407027000358029903900003440312510351032403520209120301e1004600034041d0520520604 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 390849838 1250 390848588 390848609
    0x30604030516020f06030c0909071b0807050f0f030d0b09010b161403030a0203010302120a0f0303110d0f0b03010b090f01030f061b08041e050c13020906030106080106120204 76
    0x100c96041402e050701c10101d040c3d0340f00384018421141925200001d60240c910780f84420390315403c10041c850010000b9014a04004030f584042c0010010100310b0400d00350301c426a5984c0e1101414040c0c58211350002c00c50700e81c000c1d5807a41c844580c000005014407040c2c4107050250705002010800c1044c400d1042d840d4000c0700300510002100c070440c0700050307548180000c1c8514401483c00d240307507820481e07a41c00501c0d400001801949060301d00e808042d20306400500e004580c540d40d14840040802004ac14191103804013100e041d141d90070b960b584021044100026480d0904000c06000c54100c0b1a02039440d0540c45480c90414050103441844441d00a0000f030346580e642c10340454001900f5140300d640d500410041c500006c90103400b01e01255500682420310f0704100e0728995004442000c41508601c0c1a0001007002c50708000c801e000b120300303031100136000c4444800391140480d01a4407140c0000040344042d008108a4180c400d29a140c5020b0449814030000324800c5014400111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 390851088 1250 390849838 390849847
    0x7050a09020c070e0f060f040515040507091503050f0c130e0a09020901031101271e0e0c0a020606042703030f0606050c0c0a1a0705012703020c0306040305 68
    0x140d11640003000341c62900ca00700c8030007550701c81407004000301c2520b51503000029034041c000c280c84d2010003c406c416040718100840e003441d0a1381028140c00031416400385d0740f6900010080d5001d00c03c2000102014448024200b20b0114020000d1108440030103403a0300340302c04103280c0441802034800b0940304507030713003403904c0d080030550008480d000b401d01e410035440300b0488005803500c101040c004d5115480710000e50740d0510014140004031604501d10f04252284600d0b00000c070207000c000c650008240020141c40c0134400c0e104c901c4581c0200c0812040c80e4180321591801e6001411110403550a6507401d40328181004143c0b150300c1118010315000307808007954058202240700304180b090400041210410444505a6201da84a8030225402240402e00881c080c0182c3da9060421110b654581381064070000d103034000e506031803d03480e1002c074419040000951004031034010030401002241e10b0148030078244a10501c0440043c025100b243e0028200082c046000e194075468090a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 390852338 1250 390851088 390851099
    0xc15050703052b09050c220c0201111207020d0f081b0c010e0705041103011206050711010f150504090302100203070c0f06090b16080a15241107050a 65
    0x70b80e0407941c2601045480403500603110b142009003064040043c000104400720942406400c200f00740e8655070180c8000007140b0040140e034030022107648100c5500240d4009480c508030b00410740c4248004204c80d00103411903208200c260118810340e4503600711096010b42c05000c45609080411400c003003480813001c2406800c800600c001c501a22801c00d908080c2c06001d21420755046003401160b03a040720303006000c14100b502910031030404404032903103554581048a0a01050101d0240c512940c075008120458407070503820103c0140174000f400b040703030392005400c0208601c0c0191400b071201c40c240080d442c103050090700c0c1415015006000c02c180b00542d10701c041c2d840288842e0410540c0c045030310000304080d108140c5a40500300009407900540340038890518050300d100940d00c0d00c040300607451540411566800056040c0c04120242c84140b6642800c2194002c2c4010742e0911414410301c1041441da030902804540c1c880f04d41048801c107035a1a00304900400c0c0d00240e0f0007209110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 390853588 1250 390852338 390852347
    0x20d020c04020307030e0a0b040b010f0b070b0a0204050910050a06080606180109050604170706020106031e030e04020a0206091501152d0c14060709030605090703050f01090c15050703 80
    0x107128400d41000306d03101d00e0707000d41c150806298260850350444400c050000380603001c00c03241d025200c040c0c13440040ea0b013010700410b158040c00c60000c02550a43c80001c0c01c2c980c0c90f4040d00c00800000c1c15000c3c480c10204061042d40b207050052038015064440c00250081c41111207074011140680303420b2800780d2410301c1e4070a44013281c00c0700e4103003e0004c900107850b850b070100400007007000e01071042042c2c8100f0703101820840103900a80c21681090402c0c0003186603080d6202e0000305800c0442c1041095150039103000b4030501165a10906c0801c2c1c0b80a015004035050703114895140c00d0303901221101d00e0460004c5428014001030b10301080c0505249401a010702041c0294000641c103a01c11b51081c05001d900c4c00c0609030b001400d403081140411181d46051031640030036a014290f20300d0010002412003001d880084c101646070300c00f2902441003804050003540d000420b450443c041030703500d180a081e21143c00c035250410381a001440c000c88102c5450641e030203640b00c5140c031030251400c85 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 390854838 1250 390853588 390853591
    0x26071509030314031504020d09021507030206130201050a0f0306080a1a061206010b210112020315010e0c070f0218010501090e040c03020603040203070f0815070509130c0509040504060b10020d020c040203 89
    0x10403996645540c802b607070703d10102e5090030700e80c030703004954a4007185402401c122003d40102d040e48864900030005031b801c841510440700030791501c0c1404102244044020701501d0348220203074004d03000721070284401c81030025202c03039410300f050045444503000e00103440a4168806096000034006218605440000f88109403c4002c8400c0701c0d26001454202c907203080e84922200701c2c00302d01c03038800c505050041200002421042440561500b00c0310b0042000091000e482d0020025214080210642c3e04201c03141d00900070180c010751040540f40845028041c090101c0c5944a00013500500c03181c0c464480c561040c0b40300001c41c0382d5030034032055410103003049906000300c00c00400c401c0314200c1004003c2200c9002049101240c0c3c4440032051000760000d010050704205401a54580d0074141620961090000495070343c843d604540b2406924846076005050100b0300050001702d41080c00b03282011a0001011252080140e0340c940d04c0888000168000074401d4800d841c20380e0103903 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 390856088 1250 390854838 390854857
    0x1030305070303111303140c1201050603010501060c03050a0e06071a0a06050a08030909180d05030f0f0108150601030e030d0e0f07050a030602090303041224062607150903031403150402 81
    0x166451811500010790541c030b8500180700c3c80e950bc00c01c00005107000d0207500e004118034148550648016100100144a150500024440c1c280c08411081d2108003c07a80da141c0c214100c15075a0030350714840c00f5155800d0740c0707500003641482d1020032140b40080040e0200c40041c0000d6185c0000d1005004003544001e00d013510702c200e144141d9198540902454800441540d03c50b9030b03e1821500e2981320800c050585030768900ba42c0c0050202038000a4400c1a0303031404041243e8171b0303a520700101d0203440e03520040d5003580008208404400420f400020b255944070003503607450f490850031181d907024548100341d405901f840f400c002081480c1d0080000300c50150980303141a440d2029031f0888940f402040342c0c0381031490a4281400022000c81c940010101350601106107055403402c02c12040c041074895401e00d2205204551004002c21030040100c03841c02c10903490003940144c00c0c4000d034803054012651100c40076042c02e24850442e0720030041011550341192000007408000d41154456 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 390857338 1250 390856088 390856093
    0x50a0506030f070e131a0a0c08040b0604092d051e0d050d0603020306040f021c03051c0b0a120b0901050f1303050c1501080106080a05100905150103030507030311130314 74
    0x2000109400d010801a550808190004070341403030300b001000c8038865680231040081100900000074405187c0c3c07034010404440128220400f400c060206001ca41c804010031780b50700844640b254050740d85000d116019000780c84034003903107070b07001074000012403046009504080380d0403100380e000380040c1140c074642400c0029070036125404039180900903981134810900802d80c0c4011868241c4070751858103000c1d140a4076070702081d600a086e9004200210560800340c1030110303810785550744056030854000b052405140e0380c507442c0b0b44111422600c1540c540c8c2a200001c1c130341e54414029180505c0c024175045a4540d628000c0c04d4bc0c09042c24000c0b401c00604020020b1640c80412101c840005410700907a8254505a42c450855180703612a0000c0d40050b8a02c07000b040000c5031005c481c0e00d01c61000700c0e801c0c400d49000c1c0d0409098070100100d624080d130011091644c094080d00f0000d2107510200b14101c981c450120150064018583c1101c1c0d03014824000201c00c9200721044a01a07007c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 390858588 1250 390857338 390857371
    0x312070f02010318141005070e0121090c090b0907050703080f18011b230412110616060b04050f040f06020c010603060f05073b06030901050a0506030f070e 68
    0xc2c0d800f041d5040c5d55a1443c03543c0034402065400c01c542c4101d5401014604004d111003080c135002a091b1032001440300c101c80440910601110b4840d0094042c00307600030031074400300f61036144040c02004a0a180c9014a042c00c00107011103024070115400f03240c06895132281175440e60701e010381d0b1450041503041d1000d01103103500e100d0b01c0c00740101c8132618550006011070320889100140280340703005141e440402c0200c444030707500700ca01088800b0b846501c2c882c03116041d0542801080c16001c1ca50f05030308038034000b40f900d009a200c1c40411101c20706c60603060044503e141c08100540b01c050b100c0921864401c0b02103070000d280c5040e1828207030b100d04405400d00360041c1850f82100c3c1181d0060300c40a0705d802d000d0441506a12071280d0069081c1410b4001c208941d408114004201034a003c4000340000e00781c41c800d402a011040c00c4000038044c960ba842c1840400307010307200541d400341e41c042c1044045020b030b28000c0f4404801c1d0350f4103002884d0080ca40200181c20200282988212124941 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 390859838 1250 390858588 390858593
    0x109050a0f05012727020a0305070f09050c0a0906030c0c1709091b0a140c10060918050c0d17040305030318060c09011d0a03060b0312070f02010318 65
    0x28680201480303554107072002400c0304c0503c4035414284480c11000d28144610101c080d503442c1020301d010300404461005243c900c00b00d111030f1010342024196104001e00001d4081c14540c0e94401d44441c00014403c6440f80c4043c02550f0250440c1a40400e2441d2410300c011031299211606203c45407500b640d50744002e88924107026548040f130b0002c4100014406031a0400d217003242d03002a0b058040034084d0b03025981b04c0b044d50003141514010800400304e0b0b00d602503525401d89144520341c1090b152400c0d45a00b40720000c0170180b09032429582000c90000800c0d80d00b00000b40341c50b4110003d0550400da80040018542c0340e00d4003240e010400c101c00c1f1900060403c042c0002e144510011030780d034101000304011000d0f40800716031203640100e0401c020300c80c40350140c406511081c20110001003a0b034115a003d040101c45080d00141610740010500c81142c1245058000503001c0d941c40c000310b10307081045032141520143c00701c0a24408100154865032100351f18818034500b1007030010103079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 390861088 1250 390859838 390859841
    0x20a170d15080d271e0f060503190c090b0c030403140c1807051c14090a030807230a03090b07080106030b060301060f08060301061707140105030c030109050a0f 70
    0x1d4002c040e440d8043e41d0049001074005800c0e00034892000881040f020042c0030035000d6803524024640c4040f0040310314100b950701180804042c02c140c00b881e04c1c0440c0c48100082c8103030012544042e45000c1c060714804488014801d0b80e003044e0320303603a4105101c0c0c2440d6854940d81d11040c0c3d0f10005100400c400404240602d21005c14071001a01805048040508120041030003503050512564080103000c03c5d190080c00711100304400c400300c5041140854426002040303031074004c0a6030306190f02004080800410b81d292002c2c429181c0003015126000300b00c4081c1d10700c12100207552035440d0300f240450880d07006060a001c0034903001ca520f4000e076640f108a14025078003080401c07038400060180540500a6400200090303031000c3c01e562600c20010f0370442043c2d1a6810311407107402041140d1800c0d04510302428202e004030307142402d91058999200c0361840b9040c500018048500c40e40d47c0301d10202e90141d14071345509401c50342000050002000050700e20311500c1d5440300c18007000582c0303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 390862338 1250 390861088 390861131
    0x9030905041a152a0a020a1205060c04060c24180506130b0609060102011d160504050912030726150103052401050c100c0f020a170d 58
    0xc02d018011244007107042c0300301c502c14121000750001c414404000c1c1d1101c1e0007a40c0010402d0303c6081003004040c150b0711030500e81003100203500031600b200d0108a000e0f0720b40c4001801ca111714104c900c80d580e441c0401c03129015500424001500c0b03000c020000c41c00c403c101401070900482c0304c190b28245544200202ca80d884050308107449004442024402d0502c41031f98011304080100300c1c000f45968507900c1d0b034400189000e10070246200401d450303134801d5008502501c2c281590120300d41031006069654400c9071181428540d084c0300c0410281041e00800f8011507403140140198084c40f080c210098100500100c20803954002c0c0000c00e031464541340d1680c000d01075800301c2c1c50801034101c180c6449600051418075051030103000e086840d210000d003414a440c40c074500c1122305070700101d071030b4490445900300034480e04103115410b039540d5001d201401e8403038441c61642094084103a0b1588044840903181d9010141d05400381040500180754552011a00107071220001910f03c510424 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 390863588 1250 390862338 390862361
    0x1c02012607110f060403110307121107090e060c03071103030403031509090201080103170408031305030706080702030a0807260708220204180507080105070e0a14040903090504 77
    0x1905024465800510071a02a48070b007015240c212118592980d54540c068401020015041e0001c201040140250340696034070048500c042518843d0041012801b56041601030054a600141c0c00e035181c4640440c0b09518000b40c40320b0390f0388103411515a0801860b81c01400429011100044000d000652041d446610001421a100c0700c41000502d02500041c440d40d00d09241000981c4c3c01903142c0e41141d074400145407649105186280f102d015a0340503038081d12010071200c0258615082c3c910a90350141d0854200c070b41d50300c5044425983c20b844c031030090b07001089070b40c2d45640b098852030383c4031400c4e007000011800e8000c0314115001d108000d05801126110070f010f103441c7d00ca480d13150000c00c600e01e211043c06d00c0002500403524001c0c802403003641d56000000301c40d0140f01c0d0b2080c012341c210094412041e07450000034007a2804940d60800902c401d6251842032504d041c00e10203440c1c0780ca0710071040c1604042400000d0494420940034081008000075181c1c0d22406003050700c13079 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 390864838 1250 390863588 390863657
    0x3020d0804090f0209032e1406040b03060f15010315060201050405070501110d0c05070f0806010603110f03070c030c0209090304090506040603030e06070602220e0603010b1c0201 78
    0x5142c0207120341102d240640c5015100d0040060048070b64000070740a255820b01c400540150a400320b0841c00c103040e030701c1c203030907483c1c10000701e2021201c0c181242842910191000e1240c02c1c420810184c84400c1140c24424a00c503501c0465034500030003000d2031204a0604000804102025600d440c04019500280040c6e443e44108010000b081c0b0212004180030b00f03007a500d40c081e03991840c1d10307211102c03c4101088480c1c40303810f00f0b0110803c0404010504a8a07280310691200c81d0192a800309008800c0440d042c0558441600301e001704581d0303011304c078100e400d00310349a040f030840700540c2c070310403d808010304961081c0150ba00d0b22117aa0240381e440000710354941c500b10707000090352001081944a070f4a0441c081010a81000c1c40904100d81110400c2d170f101e4641c608040203010301000c50041d030007804e1800302d0403071030712010405a4130191402030315603807000209401c0c3d070702842d00103402c20380d051100760394010400060700510344141481c40b072924000301d4200c40c104195003001843d6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 390866088 1250 390864838 390864847
    0x60a0e0a0e0a081c1e020c0c04060306090b091504171920060c250c03060614060712120e030d0518060403020d0c150c09030209060a0608011205030403020d08 69
    0x55034000e140b1041041203500c188045484030400c954031040700c070f18085c0599000079251410741d1090190084050000304100f055070b449003003540c01803000560880d4409840d81c00300b0f01d4030388005180780100c1d041303000314140b42d50703140e48414185510141e0b45211020a100505600c8240c02078401c1e07032407996a490307030302c401519030790000c1d0906950524403980141060156028400d021a60340c041207540d981e5541e00b071310f492514001355002e0050f280f00b0981501004102058000204480880355042c1c0313580c580c001004400c0c41000341c020031325521f036032140b41000c2c0241d1080c4404c0c00e0314140060314800300d02c142405c3d5408200441005a40c8404100301911141c0030f0164040e0980002d04107031400b03680180da1a040c6008900510420188031400c02000508071440844249818070600c082440d0103440f109403400f0491180800e43c00140090500d110384800b1540d01741c0d25191a07034a44052001c4000a9040948a50204000c0400941c44004480e448603109110203a0b45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 390867338 1250 390866088 390866107
    0x100213090222050a0303051206120a03050a080a02040b092b11030106061701090504080f0403050c01110c0a03020f0a09110301090c020703020f101218030e09060a0e0a0e0a08 76
    0x74542c10303402461081943c1001840440e50000a03149115401e41c0480e902c2d41f034080c00500c50100c6d06110324218841d04003114109070340000034010010554964800030b8940c9880401a801680203610034280140a040154034099601507459413130318880d20030080c0403441a103010200c0040035a612404c0c3d1261060b28117007403141c28020090341c5040c0e149030003004e51800032410180304114005440d80042030904c0b40d400105c0361003078803000c4101c3c2d65558920b000d903101c40d201c0b2801d0303000c50b4414111000c2d480001c1040090080014010051507095078200449400003045098002c40508408a4822258840d0761350341c070007000210307440f50714001c44001a80c0307403d040d080464001040400058980d03070b002c1e007082c840403982651025000001142e20100f2640c0c070040450900710b1744421404902c030624817a6000b55076841454503404d00748101d8030350030358240340c0003244e010041240101900d026500002c4580010a92000c1c440005140000091050311160030000e40040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 390868588 1250 390867338 390867397
    0x106020f16050a03020d080f070b09010e0d0906120b0a0e0603282306070f0e0103020408071203050c010e10052410111f0e0303091002130902 62
    0x8107032824004031245082030041841052a0b10000b4050648580b4503800c11411500f83c41100005148103070f2503440038206800801419a40c00456511300034003000500c1010840c08245180f94507500d0300d417031410008480350520198103182d400c0e03a5a60b000213641d102081100142050011500181007590805003803031561100c104030b01c81c0c0844c00804d6906540102c1400c150400c6d40318070342800b1906200c149459218080f42240504010884a582c00003500304900d0101c0d6a07803030700d2a1880005400700c0c4218050a101075014150400c81c189101d000000d0240c4685485801c1181c0900e4071030030354410700215519a040380e40468000c080300d04c103031075101d1150600c0445944410192228942080b40d14070700a559160b60080c2590058180c0001b040c0d0020440c1c5980190790070340000812040c1490140e1400c10100100b10705d00002540c0c0501e595101038240070400009000080d8080c9500d88000d004c28030000a801e251031020348500c00d0881c07012180301805812050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 390869838 1250 390868588 390868603
    0x3060905120310030204180b09060714070b0123030706080105090a09080324120c0f010206011a03040c0306050a0f06083d050106110d0206040f0303050a060b030106020f 74
    0x1d107040c60610400500c0000e960a090840760140e800041c2c0c001c1c240d6084004072540e4901a050034001030501c0402680051024419043c0f9a100b110302d0050134a660701c60320034031308080c21001d4210014031002d01c0342206008440850160303401d00140380310109050000a40c000b0010448c0361004010908103803180c9035010007100c0040010007171719607030740c152030002405911040f20441552044035503040c01080c14110000c08050070704028140e06980c0c0c600089585024501c220f080740ca51754000141c981c180c4088150040700880c841d60307041c0340c40d0001802a1200000c842000000c00c0b198440c190140020200118000c151241e90000340d85c04e5a000c10010390160390401c0102280c400d403d1100748140382c500a040321107c9101400341d0148203d02002c40c07421000284590304400e1382009580d0a2040e208000c1d0219001e98403900f08581c060051410403418000192103940f0555100e5202c100003e001d41d110700340342c00c0d02d8000360800c8025a12108018101e40020058803 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 390871088 1250 390869838 390869863
    0x90913060608030406120e0c060f210906160c022e020a050709020703030609020414120706120504020303191220070201050715050709051c1a09011503060905 69
    0x1c3d0314080c0340050091480205c40e80c401056039940d0b01c00c60300d6010600841090020080005440b01c08042e0750403404e90095148210240d821a54550155034400c844d070f1050040d00e000d800d00d44c2e01c5044041e00d41c0303040030740101000401041100165030707001d00c0303003203400c43c14603040128400c074070841c0c0210b0a11030426080d07502c120121780001c1c000283c1d22054440c07134000583ca030400c619003640506202d80000131142e0002c50046824039140309001e0502004407482c111541500c02d2840d111540c0b4010240041c005100c0d2445c00e514940081c4e401c1440a41102d1901c40c0c08080c01c4030003500310602000240c0320701880701750b131982030213190400c13985480c15900300a16070b01786120521590350000d042c0000850355400f4082010280c0e841c1086622091085141c5060f0003846c80c0e800b4000d0a01c43d42400c0c0418418900c1786c2c461a02c2c5c598001303800406203076000160160702c10020412a00d543d210a940702d00600c1c03400c0d56800440c80f8000105104020745002400c01014034480b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 390872338 1250 390871088 390871093
    0x408040f23040b030f0a14070f0602060604020a0e220507050a170a060e0906222406050402122401080a0c030b040912110d050d11090913060608 63
    0xc8060007a041c0301422003011079002035140102c01c08213040100706106180e450144084502c10700c030300c0c281c1c0760240c141c00c4825528010307111300f100c02e14410706010b0383c0c00603440305000880c1800e150740240342d8007485041c0303240454a85000241c04004080b001000c1000c03d4001400420943c014203400821600305141080300c044001030030105034030306000b40008503102264052030750713a2007a405000315034542515450010182646d4407402e032043d9406006500742444080a07000e54942c2160380700410344a80e0b4400c54011201c4d400d01c017241c0d100749941da900000c0079511031000b0484100740e40e440500900e0004900d000e08510400d40030881060840c00700c170759a03230001c4510ba020412602c0003800c502c20001c110000d240e080c50745034103e03282160003024411098902c581b00202d55840300c05403d5000c000c151245d400e0140e0b400410821320a0041341707251600185000801041030a00344600301002075071185064448250007085508904240007260166a02601e0341000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 390873588 1250 390872338 390872369
    0x30c0204050c03090d1d0d0c060219150e0f061302010305060901030215070c030c0b030103060c092102060c06070e1f052502090a0c020c031603030e06120408040f 71
    0x100170745680c8903599400030842602d4085042d28461002c0402c0c51801401030000381d555450500d60303141050080d00058815984c400b8415101c2811103100180e02101501901d54100d4260f40070704031800707411400e80504c00510b500b4403801c201d5580329161307001e01c400012615000140807514003034903003400b80004000500141c0c641c01c5039241d05641410301947c1e42c15a40c1404000b07240740780c01c005c01544115100140410403000514140d80c003565003046814070240040c0c072985910310a810110750324150360300352540072050842c001400603007280c0c5000c100740845410240111041ca0114220b0000e08600b810040b8641110604006180c200e4280740d050150450061500d041d030300c101184185080030801e0100c40402c564098000c0c817050a101006030060200245248010722444031810014600006e450046881c1c15403d442000c0c00c43d203084500520100c4041e401c6602006005219501030a81310301c0b540c0a4018140c560342411500c22017030216600c1288012024030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 390874838 1250 390873588 390873601
    0x10050a030e03090f093114010203070206010312090305030409090302010c02161406210405010b010e0a051009050603100321080f0a060b0d0e070e091e03090409030c0204050c03 77
    0x140044000181202c0851450b41d42d1b4003008000d61110075007100001501c080840d02041d51250810b25601c105080501c00450060807400c03800112201801030340b242c3c00406c00301d413054030b0080a4140302d1421000c096142c1e251603255600580c40307100169034556450040c1542071060030007403407291000c0c0103c4d0440e07403c0b516025006010b102c0b06400b0b114110002c2c0d0f900e00c800c6942104c55072031486d01503039411140c510012400c03101504c082d400d0082d0107032070b503100390901d0012034030042c0100c8000d400c20f02482101c1d00000c2c00b01082c0000d036a80071a040d03407200040d52050580c0c0110f0a21942189441d184442295840803c0345d40c0d40288181c01c3e640104103103a02c200040c55100035561821000c0d00509500d5114440c10f110005002142d0700180d00040c0c0c000c101c0c1c3c011210100c0d0348150040d684001140c41d00d0701038100403400445e1004103018441c8649080003201c0c1451101400a811100c220a0803800300303480310340c294110300b81401440d070b1100c0701c101c0300c40c04e5181c205d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 390876088 1250 390874838 390874849
    0x2070f020f010f090608060102012a0e0901080a08030a1404050a05010f021204060e0705060a09081504020f01120605150a02010e060601050d02070c1d09100c09051e10050a030e0309 79
    0x140503880038846031b040041c003564400d41c0050541c4820411704280c030045035102c2c180c20600040000005103411060100c6401c00b902c8040c101d8902c0300080ca4030895903110880247c002501c0e226800703031901c0c19296950b0b20300c1358250140b4051000343c1005041450410308440750078000140b1503005000039004505420005a80160061008101d05948000b901e0628107540c004a0b4090130104180c0b51855000000710250380340f150854000314817000901c01c0d00082120000e511852819070701301654403905510505c80c11804011450340d45500000300304600d0340c444d0402d85100030a00c41c4415509005000f44140c49001419542c1040c1c4002019480f900750220140c030b40000d28001000402c9000310018500012000c20b0854128410031401d201074440511511030103a1460107842148518180d071005900c482400500d002c00b031055040481088441031282c5003041500d40e183c24240c12402007803030b610741341ea42c80d0aa07000b07000c40e841c0003902900c41d807080c4142115510390 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 390877338 1250 390876088 390876107
    0x18010e0703030e1201050705040510090302032104090612060605010c0b1614070503070605091b041104120605060306091906240f06080708041505091002070f020f010f 73
    0x540b80056901c1000f1001c9080325110003502d10456103080d040040b2190b1000241c000d03201d04444444800b01c1c28582141c9180c1e29010181d03251f04401280e000100201088507420b680200500d81800e594182c4003003241c185a000d4008585107950700010449036110300000761509080c00d40c828842a21421000c22000700048403000c0c4403040d00946074000c0344d202c54001c025814096a441c03080c600507845ea0404001103603d41d0421010500100010034090150358080607400c500d0740459080101074124070b203022140500802c00860074840e007043c61340d40640640000301d51030a1202c1850310b0888010030030013113a0015080710301c0550f540103280c0e40c440c1e0451404120100020521403c45800549907150050201c00006034410200c14a074200c613683e45594030981c1c0c881106640304070044500800104120035064030741d00b1f07a5400b50350001c2c8560300b120840c00024410a0032070340b10702d5090340d060a21208040851921816031003190100f80b0b0856125024000081c14480c0d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 390878588 1250 390877338 390877343
    0x20703080a050a0b0a030c050a060f12020a0e09042a0506180a05030f07030519080a1805040e1f02090a03020d081204060c080603010b13091a0108010518010e0703 71
    0xc55030b0102d44141c21540200c0801c0c5001420402180d9887c9001d10300015148034031070041c424154001070040c0244111729490b2819103039207150002c0c401c00c00d8001d500500741102803100c68032415620740c9031040d590744214400c4007021180c0c00302000c8012600301c031034888410711424840a12058031543c0030350385400e8404102401e02c1000000290608680c0e0308800d80600c2a085404503070b03540014658212030048082d03c02501000d41210409090740d4800b80c44101d0070071194010b28821000c00ca1581e00c005480c4030665128000038060300c1042c0c8194240394420b0080c0900141c20060b4512810407010702145001600c0300410080e076050300c4041d114000341c60b03408003070000d1102140d042800000700c2c240c0c00c1c503151902400914041040e040003500080c0051302c0c6040522507020340700341c0181411840c1680c05210405022141400c0703400000100f04103507890034410300d040c0648003140012070540341c214420740c445035084400302110783c1490340c1e03415200b00100c1c3c03000a03a034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 390879838 1250 390878588 390878591
    0x1b031a0f240f09010f030605010207051002030c0708010e0706020106050d0813030512041d0405250305100c02011103100b21040f0312140105060901030b13060513020703080a 76
    0x544061070000210740e810020518407000080c203400750040c2e500103080f880703804d880b5003e962500b010b086003184c20901400e030150b40321303000600c0700c0c0c607050070501c3c1609041e2044a10340746000c00503500300626584140141d80d1160b1503411550402d100140290981c3e2000f0010302d03103007100080d01c00c04030b8440a0310404000580d01800903140341000e015540080444502100e8241c0041441c0d0003840b44500751200d00c224140f0288100f82d020340165000001819600e041d00e0943c2c8a00074000500303103000c10100800000550148244000d50030850303000501c0040a11019013503c0003100b060840c49420010004a4140c0c0240e8900340c030030a5840540f102ea02e1411111f580c441c04d94441480c5501800308410031001128042d140d506c83da81d001c42d91000002c0510076035100d401508600c8a04500511441c04d202016001c0c2c0a414540862045a4080855401d024074000a80b2180e02c0b51024030090038031305806066a141c1d410118644580d030f440042c50194050030310039045 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 390881088 1250 390879838 390879859
    0x24041103072607060507050d110c0d0318080a0210050901050f0c010e3717040e1b0406080606090d0c15030b04201605011b031a0f 57
    0x151401c000c05406084444003000140c00b04907415844140c002000c400c035845441c0c3c0c0030880500c100c0c00e40e08240d9001c8000d14650038080310640314440074a000103520b1081d2510702c3c80d10b50700c81403a2a0001d0007070302c4a04c0e104001921031401601c89801c01c501d40c5e44101c44d0b50b00141c44103120b2151038034851034101c4e2a0854100100e681e440380030886007001e01c01003291030b41c000301984095070200801049038186514440715204d4000c0f0300c0c0007000e450074012220307075802d007038000c3c83d0ba0864440e07040030890020501d0140082c1c1c115400c055120164202004410340305100490345103114000b100b42020318000008003851030080c0301c1d80c014032010502c0c0030300e0303121444a600352691000d240d140751611400010800d10b103840101000a0600b24400300c00e042c00c7c4140081c02500d130021000c1405d940340c5d010300c0d0b41c0c00722a207041c1c0c0041c0410111301064080c03081c1189120080c0300e0b85008a1004401811340d18402c0c4d41c9c5401c003110b00160880303070784c8807400c004d5014015544c1103c1c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 390882338 1250 390881088 390881123
    0x20616050d050103060209030c01080105011b0507030b0f010305060f0c0711040e010915110403122303010e1603022803140405070f120c09020306041d0a03022404 71
    0x15402180c1e049603a107420240007108001103a00505400300065044400300d080000044039102028450107010524030b03051001d99506851100751420f004200301d8028699070341d0b070341b01040c1c03007118400382c0221000010b0003084402d0102c143c00c0790302c4000d99001030804140c1c0c61903074843e007540141844c07400e100150507600eaa821480307040f8190002003003103a0003030030b12214a100d80450300b61b2151a10090340c00507c1e24005450035030750407040d000a804000301050390011074000021034104500c1c02c0c5009800f440100450280c50004065007017824071903a400501e80003100c000741858010b1100c03603070014004181400c0c00200c5403444440c6403036000182c00610910070340c1a2105840004c0200b442000201002211081e2504090640e41c1c6c030900054600c241800400e420fa074188200314000c040d402860304088028070000d80401c0a90003140d40703034060850862540c1151140905164051101406903040a1030f4001e2201c2d0043c040e110b5810001d0004040d40040915000f8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 390883588 1250 390882338 390882347
    0x3040627051807082a030606090d150c11030d110c030406030212010807060219030915020a05010b1f081902040b0d060b2502030c06030a0209030c0a06020616 69
    0x4107809031162050352448880c42d180850110b03100c0002c111990003081d0071104010f40c3d410103106070b0344a098442d41d00310103000540e10141506030f100d44d090160785810b5640100c101c100c20701c24001c100c10b00e05d107034107170b031041c0e40076a4504002c0c40003000b80d80007941004800c8542e660700075000060400408410f10900c5c0c06a520718036100d200106002c00c03020b8056000748111040c500300c903411aa0388441e916550080f40c05030310016004115602441c0c80010707100ea07080c5200b820141040c5407a245501c1030103006050801c0140d0001c0e21010600a0030310a03048034400603242c1080d20b688514803100c0c1c146901c20513004026014001442c030094a4120300c0706800f8415003503546681c0c420704231419070000401e400d02140344c2100043e290360000100c81b420b610f00310064960800413403440a5400e0003000c00ea806004542c26403e0b49e41c0d9200c001c5100e102c0380400143c541c0624001c0c1450f000009030054050045070605001441d00007903440c2d403110280200740e0180307103502c1040302e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 390884838 1250 390883588 390883667
    0x302010f02160204110306031c030605030a11090a0509120706020910080108070e010602120a0e090406060f0f050f1c0b0708010501030f0507212004051002030406 71
    0xc000a1010901644011105100301c0d1124000c0350300b441100d40c034a091039210322040c0d44042d850703800700d480300d081d07001c400307030380e00c5840c0c4140c10f001507465503ca003c0790511882000840d406824024008a1450a44655608401d08480400041c80c24052003540c0f118020036208202c20013190580c100040c079011264040d1380036013282c5400191520150803146c1c28001c202907402101008100d065416901030304139941c0f5402001030b0f080b81030019400760b10020000003082803e01d20415141c60742869280124800d141c0015201c0c64180d082c046420030b81c126007410b4401075030401031075032815440704e2042030480710350030700d25030700a00c0204140c40380380002d008007002c00411400c190880e145904841c42a03d06000341c1000c0710340442103400485803800881d1000c0844103030f86251405080803981003500000f42500740c010018840c2e45507080444c00c40d41c0020f42400f82d0f013491001c88120482e64001141480d0800c000581400001303481c8a00c016441390310a80601c40125150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 390886088 1250 390884838 390884861
    0x32030604090606032306070504090b06090618031e0309040c0c050607080402010e0f1012110c1006051918061d07080708061c1a090a110103090f0807030201 68
    0x803c03516503603190503d05a0301da4410060a0400e032880c2c0c02d2aa000030404610421403030340c030685043e003409003100c000c2030030201c3c664102c1418007407900103844034801401c0082046100803510b243c40000c0600e40f91205c2d410002d64101d2200d04800e200d0000180c2d0321450701250003040d03402440b0030480b0350811844010305140700320414820700070b420003074082c0114000ea84680c0b600120707400707210045002d000c3d01900a100c0c02403404003d441420940da2280031100d010a040c50f030345602c06440e0700f000f00a00f4154001d07004a444001503845114001c1c207040c0c65807052412491803451081c01184900c0c0c41c0c0f0004110038086002184c1c0c0881d011f40b0030101a02d00c9825180303500d000d64031085800358041a41030022620440c06a1000c0c8e00c42d00d402010000c0c07031001c01da4280660100080b04542c40c64903840c603405110712920156100344030100080c20355490711301708024085402e102e0303207051500d031429540106401017400c80c03c3c140c01501041d42c4504a01e42280100360542c0326 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 390887338 1250 390886088 390886091
    0x1806022223031213080c0108010f0b03071e0f020f011a06070c09020d02030a05450d02061014130c020a020d060213091a0108070c05100c320306040906 66
    0x10040051313050140242c2e20400103c1d110840b102c00151403020003801005001107800e10104002e40c01348000750391000207854101009030b6034001c010003403603034090f805002c150001250300010344c8c108010b1a0808681d4024401c1c03240c44c3c514008c1418031012842e0240e200007a400052049400e036010081032422000c41d43e0b102e110310004001d40068442c01c248908020101d07400c901604003815495044610800c42002c4280340c40541c24401c0c5144092140c48080594282e4810b00c028402e5a110303401800c2d040c54520064201003a50390000620405000c003840c1040e1180816400500c03079014000845062400051303151a941030802075020305c5400c1044108109500a8000c074109121a8550252200c5090341960041002c4907200c5909000c01100c0f58030400c0480c1c0c1115050400140c07490141d1142410311001481c40d001d15604d4080c8881c100707a0001c0000c0440182c01005664442422426450f225000f45042000100070000c1201a900d41d8440c22515500c07800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 390888588 1250 390887338 390887347
    0x405090903210a0507020c0306010506030604150b040305010b01110d0e061911070603020f0d05130f0609020a0e1911190908060106020303010e010b030a18060222230312 74
    0x1880e80c240ca030460710000c0c0309084c4004034212900019031840074007002009003103160b0070b001c10b010003900010007941e4416100c030302489450040d00040c074080d004000e5019581d500390b0500500352408000098100007041001e00315901011510312845081407404017408056180011114040c0703005a00000c24550460822140c2046d44070305030001843c141d4458958031001a4200c0c09007001c0294940700400c400030107000303130794490f55201c07444200c106810b00e0300380c4407100c0c42020141c003140c00c5580c0300014800d46c80c06000e00310040108407100345182c138104a45c0001d0041008804030f95a841300c0c44400c40700c00b14001c2d40c014945141c551180c0c260200b80051039450144141d81c3e0502507800041101c6201108880c10b950300301c08080096483c016075845103500091624000341e030754803101c3d03941c1c44040c1c4184002602a06001d600c5440313044404401640003c010a01550541403c01c000a0419058102881604000304e000b01ea03400c04681080107201c0040307083c030300016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 390889838 1250 390888588 390888637
    0x711010b120d081b120402030a0501330f0b2809090609021810140a05070b090f0c040b010309140102030f0c0301060219020102030d14090c0301050c0405090903 70
    0x184610302c03a00e569125407180d26005841a405650307180c982c0e14103c400c00c200c1200c4080071040c150401d10142c112610401c50703841311421100000c14450104011000c190015564554400192001410715490451078650420301076003651059a548040101e4000c04040c80b21010420401c0450f0004084ca401c442d00204054801e01982e82c1079480c040d008600241c0500c03d5403100c0c985c00e410014100d208808005851000f01c040208000c0c150807860010175940000d00000070064603071603183d40c1076141150055070000c2244420341e0100d0301340300c41200001407000b60041c0548000480106000c0100e016041750140944100001000f070005c2610540c011032266810240c210f1881d2183c0c481105544020703c00d202c0140e000c1c101002d10619a4481006e01f05c0c03050044900c0d10300344d4101c50b400d4a00c3d0101000c50707000c8820400c03005c030380e0601007481c00d2003084008200600d01115041c0880c0503078050140244551000140b9440c020000c076030b646026845510841103c0c0c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 390891088 1250 390889838 390889843
    0x13060e190806061e0d321608030a020c01050f0d05041401050708010f09020d1404140f2e090f050610060e01080f0604150603060e0f040206030711010b12 67
    0xc0e00d1144c05140d85601c040122149007aa4849900e00213269004039412526034082107142c80502d881104440ca0000800e440c1d20300c4840400502034004e0a03c41020740c000340d0481d545544501c6041c1c001308801049141e001c03c20500346942420602d4442e03420000300b018502072a50300d455002d103084240410301c500c2e044401d01c1500400b00a004541d22080101c0e841130081c80340c20300303040300740c0c005101220060b0090001e4400c100c000140c04401d05000c20648181601c01f511302d000e5070488144844030a002002d50003040100800d444020282000d0000c0c0e400c122030784400394400100001c00d032060300240340031500094100d0310f242c0c0038107007284c48602c151400d0407114010500000d005010752102c0d080b03040c050311000c1d02036903401c07006a1410350081015900c5507441c608580f54024000c080009400541c2d40000c22906201c10402c090601030b0000361180211420000141d6540307080303079444000340c90800200d4559100ca503000d0304100c1d01381c2d035004490240714140c10307400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 390892338 1250 390891088 390891091
    0x10b19030b06190518180d02031803030706050f06010207170d03020d0b10050408010b090c0d0b031e070f09051b1806070b07080609060f010e0a0510081b13060e190806 73
    0x240703030200891b1101450020307502d4840285000258006201c1e80060b10f5139150001803600019043d00c0c038155090340c408040311801c40304800d003070b02448140042564104481005068042000c403280f41c0544051940c894006690400705030300020400202401c0ba0810051001e02920040040c1015240a0929000350140036000c0d071a1000e8010b41c5e2402544103402019104402450102044152001b5001480c016601807041d0703803118400900080546010390320031030142c096170f410f140c0205240a01503200791042410f19043c804540309070900c032210f48980400c0180d80b00c143c3d00250090000c41e02c6082d0741300c1004030b1140c00707100b28106c0580c49222a95180322466490749c1c03c121100ca03041d1026900049010240842035000d0780714135400440003050b0b8400b1656840005120103914400c2e440010070000c144914031026100c50844100b1000c2000e0409482040741d0003100054070400041290711700c011340307544e02d8011110035002500c94040d001c440d00c42d103003e42c1d207000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 390893588 1250 390892338 390892351
    0x610050c0d03021e0a0507020d0f02030d0f0906080405030f03071e211a150d0f0207060b100503190603050d080f01060e03032d0c010b19030b06190518 66
    0x50004d182500b01400e8011a010742c80282c540a090420640a21001c034189440440b9079012841006c400f42c0d401b0410a40450820307580e80b0701110003440000c000c2c8040c0d92108003801a00781c20700c00042c4000c0183c9030305542201c1440c0d01d03541c988104550440032248400011104541d00c03003180703075001c04d83c226915650240c0102c881000c82e0000d003181d1010210f1000d288042c161120503190600c0c3d104c01156504c0151410220f45038444001c40b002085200c517003550000d400c4003088100e0107130152140301161180d0307000c100b000d4054024480144203000b090750859842441040c141e0201340031b15000008c40300742004038403020300a04015201500311030b5213203000080240c860300340c1c0c0042c0743c00907003d1402d0070340d02c800000700100700e08006181b03645900203500300f8000560107000c40514120000c111a0080380c00d100c800000070000b034200340922070302030000c2094048041d41151064482054030001c0b98903951110399140c2115034040c0d54403254120301907031110058082c50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 390894838 1250 390893588 390893617
    0x4021e070627060902061e030a050a0c080f0a090c0b1201050303040614032d0f090102120426130e0109020406020a150207170406021605090610050c0d0302 68
    0xda900740c20340b81d20050312001600404004a0440015449800407011244041c0640341460382038000e0100200040d0428520800e0200420402542a015080d00309031074020402840210751401014402c008140d0300c0000103400120fa25503000358400d40069810402c80801a034840d1802034540c0d1003a6021035035402c8000000c1018a0003000300c03000c0b00c0650325540c02840440c4e0a11101c1c0e00000c1402680f0813040c0c9417042c007490311111440c110410440a81c409140606140580c0100500054904d83c418030104042b5a460300103544c019801125400d01e0b451150709190b148c14018041c52108000441d0568944510003546010340e0b541c0442d491440e81c03101010b0089004034414900164050120503010074800700402c031480403182e402610b0010386813076219900e2501740c0c243e10601c074005801c01000d68140030154030044440c140910711840c210006d2240a0f015210700c0c0f20700c4080d03a905a10034000c8040340c0044c80610251007603a49403e2000c0c0082d08034905002080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 390896088 1250 390894838 390894851
    0xf06010e01080105060a11070503010c110d05040b09040f0e1b030d0804050703140f03040b0909010603050603072607121101080c04060f0c05030d0603111e040b04021e0706 75
    0x560080c03582d039058850192680341000700202c42101c0c80b42102c80788a1240c0910080815142c03000e0140303100b104015202e031306c0d00c0107005010f140f5000c4901d401c40c04103e4184014020480c040c0102c80040104a90106003018680e200d42c0090100c410b4820080c0f04003214a2048151079008604012049054650720101084180c56801003250b00420640140c2401e00015802d10407070290094601c003103455080880c01464515886500501030107600481c00740018540041d4042c051b011700c1c40d0512481c01c10902299654a240c040e822005000102001e8020324441040740303801f03e210100d4034955650a925000710300700910a0b95544079403050619294090b20040d8000c0005040030380c81d0500d0030004a4003440880110810841507034414401300c0c008002a01d03640c0e440b8800010900e02c0e41c030f40111400100040349010300001c0f82d40c0150b407000b904842c0861003041d5404192210580d000800a10404c138001c10000407880a41841090040141080703612841080003203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 390897338 1250 390896088 390896117
    0x2150c2a1e040e0f150a0501090c050702040f0209130b090c071e02010c0210080f1f0902091302030115180e010501200102040803070c0b090d031103040302090f0601 72
    0x807450040050403805070094203072050b8200360b40302a1104103414150f4484412120f51a820711180314a5040b248800505002002c5600c0c883c10340180017407a0200030310401c2c5c0c0d102402d940520140644126503c0e4000601001e042d0121002c0700b10040c00d8045032044414100300030117030448054041d024400000f440c4c800130504541c0e80b5034020004226045100c80810450901c000b0300f28108460140883c0050300d891585a44100d80c03034a40201a20b005070640800c800018040b220f01400c200450329607420320f040880c26550001009655003158401141c0c820700c20541402c50310748000300005242103102590415082c596950540529000c6a0000504c56034020440b0301c081180040000d5070042c1d500d1104040f014068105001410000500326040366109901d15000000d84d0810400c42c0c0e14004050b160040744107050448136408a407103403026020040c20b1001021301c0b141a01801c0098400450303000b00841c1240ca01981c2c019140c400070b0310394a000c2102d07140c80888 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 390898588 1250 390897338 390897349
    0x706120501140f0603090c04020f0a0807020c0a1a19021609020421050f0703030815030718090c090c0f1d090601270e01051906080402150c2a 62
    0x380b500000c0c800d21201c09020100a101e90020b020b81c13007244994040034800d5203d07800a030980c2c2408101c0642c4601546a01074140c2100400010864000814000c0640d440400700020744c1c2801e039101e590319000701074a24007480780958081400e41c20348403555102d0780c00600000196580300603640c246a0307401c0110240d000f00d004005031107014104508a060400103e41d595a0080d0210b980000308a810f06084c10313440c1d00281e000a409100b00712414080c1088034050381c905600401d1020f00d0300c009070400542155600021689461141c400d100c1d00401b5900542101d240400c08100000030240c0640c000d0468035000c617040c100d070105000b00c6190b55500945018100402a81d14040116000070401101a00031010340c10910061f140d4081e004000e09540b4070191000c0d41800c0c00c0064407000d460b140050301e241200184000360703024103940d41159055803025000c0340c405600322081e018500c003140040c482c01c0e040c42c561400c1100c014003100c0c0350080920000120390107014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 390899838 1250 390898588 390898619
    0x306042913020118090203160306080309032503050f0f0607031404030c24050406110408151e152b150b06040e070305070c11041d0706120501 62
    0x504607520800c40da000d54002e075944c2c4c4070610303d440014041a101e48906080f40c001396540034800301c480808400301a014890403014144540096040400d41400a566000e4408100c17110405106005181640c03c09980b0003a590010944050400d80c8c0c2c0c00d180e5461010b0100b07040c5100f4070021a000b00d00a105a101401c440d8091a070241e445031810788501c900442d08a980100030040280382544003201d00a05031480e03100800d181c1080d0401c002a0740002e040b5030302080701008200403c100020783c0801400700818410217568860080084502e6490690281c0a080c0303410000204101040e05568800450300d04809412401301028695082c079070341e15000300c1003601c910209520325401c5800c25213400300481c030108001c010500940080d07001700021650701007030091803600b501a131030b8031801620708150b101165440300e46c140c1034003241d83c600450342c5072194145c0c04440303c1d903a0704480c3d0070412510055520b90008000d8100c13220344024107031802c3c0000c0340c070780078005400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 390901088 1250 390899838 390899851
    0x207060f050d1e0204060207031b0b0702090a0b180f160e01050c1218011d0d020d0515040b10060809330109020d0f020a140309070503060429 62
    0x60382807000c41802c280091110340701150903800b1041e04020b181c0a14002800608590f0303010f03110b803602c2c40c1303468012000524030f000c00b40d0340300c08002d01424403d5410703920b820750115002c084c46e0b01e41c404203500030311a0801c09a002030007148001c078400011132040f801884200542a0a507481f0f800c000b40710068666001e0011301540c200d00e010758810fa029011b04a4118103070780140741c1c000980401170f4400d00042c00039038034081ca000c03a550b030000e42002216404141c0d20116001c08800100c0c10189240d0092144281c0318040c0f0601000300400e9148840403611070016042a00300440c42004c01c4032104e0501850f4007012421502c07c10410b40203210780d10080c10003042c2c07440e09482c2078415003041a04082d1521242d519034511900031402030040700300041c1e0b9400850320324804e41e00e1285a030000e15004110081440b9800743d40d100a02d00315500c02a165200c024655081082e56480540e2610400003408180480d171030040c4800d500030012114214104241e0102d400c6045418 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 390902338 1250 390901088 390901097
    0x3010b0907080c090915031207030e100e060309060f070c021e0d080f0c070b030f060909031306080a0b030106080604030507031b2301051b070606050405160207060f 72
    0x21038802405442c4003038100040114090070b20f40000c0109102d45001c50b40951070740e00525000d215801c042c010441d0014003210010f2600c0e1a036100070b807401c1100b403c1c00d0701407120f8828094050b1300c0b42c0b209490420000705840e07541d0a011703600720f503200c00030381701c240c20030010f2404909120b001e80300030008182c0c090600c400e06001c00c50503032105841c1807251600509800543c100284043e40140030410030f1103940f6444092014500d4070703012240d0400d90030001c0c100103112000304911115540010200c8003c852503543c10860b6045014622a081a101b400c0c600403d1a94112420922480354028200f181030f11080c00c150036216039200d42900f9820440104011070702c60340040100502038103101002c5404080348003a0070002d143e0544800c41c0b490b90708000c2480228001d40a241036070000c0c0400c0c18660034498184040f481515244913000071003400b0021160850b40041000810030041440c1800d503418a00c1080000900140503c46000c103c2d68040d000030100b0311590f544 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 390903588 1250 390902338 390902341
    0x408100b06090f0d1106220b040e0c07020406030c0906030308150a1e0509180f0105060102060105010c060605030a0c29030708070e150406140f180604030c0305071403010b09 76
    0x740000007104d400d058841000520003290651214001042c13100e0ba212a46c2481c055405040d101908003504490580d040030001000740c0c07890340b031020780c111204a21650b40c4c0c148038400940108038940c001840300e03100e0400042c0b10070041d07002c401164001e49500c4190741c0c50b40300380c550b1030707003d2803145e81d021030780c0041401118050781e8083d0304c20700140c0c030b11040e103900c0b030001400d81042154003401e400920b040418080e541070000320a80401c403002030041d42405000030707440714014003c01c1d0421150040f1113061090581200d001080c0180c146e800c03c420398205011001421300941070f0103040d1000d044070680084421020315003540c480d1a0031611134800450341c900010304150704000d41c101d550780e020f43d50940c010102c40034200ca000c0e901ca2a00340043e043c0c10581e524410810010b012005d00c0c607111808483c2c41d005050f1028524a0182000070b90314092a000038007840750001d03001c0f00300000090710320260350707c0008403454030a01e1002c15003a6558040c0c495003041c900030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 390904838 1250 390903588 390903619
    0x603210c1703280209130e071406040b0d090311070b0f0f121306060f0803030f180703081e091e0f03010c020105160908120a0c080408100b0609 63
    0x703019682200310302c1d2042402203c08002c902c050030b442107410700020f900081034210b61810560034980f040c0b00c000140a0140000d00fa280c41c0c01084c8914800043e50b1b841c5a410340d0384520840d8054198443d889448290f03926030800244090201100400c40b070110070703080000f0001d590b104491003030407454a09000a81c1450641e0440c03175981c04900024400c0c0e42c0c2051700120224803c04446405504000c5036040c402c007510240d03841009508401801401002000710440e5800985809804125114401c649044050130a180003107070040300c501208020907000109001c862050b0810031408074040d001c1300341d10400302e5007640300e00c8204070174010396104540d00c0c2000032b00070403900b00350b070743c44001c613080d100c01e400340e0350060355200200069480c04801403c030207941864421047c5041c006519550900c0b082010740000c004034042a1941c40741e024007040540c000d41c10f40c0c0b00c681d01c407041561540c10303c0c1c0300c408050400200f81100c3c04d202d4150b4840210042c02200239407102c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 390906088 1250 390904838 390904883
    0x10f030f0e1b2b020a03151a040507050d0209120a08191812021504090b091e040206180a0308030f060301050606160503070c080303010807060c030f0813060603210c 72
    0x1003c0c101c0e08503002030400408500400100040708021400c042540d800d40c0b815803202e022803001c00d610442c03802e81403103809540701003682c032508c0100c7c20044c0e079130710f024001030055005407080215034031400c4011020440d000014101110320760204040910032400160f628080d5100340d0207020000020800075140c0203401502c40c240003600790443c80f16a003200b03601550140c1c00441130645c8070341150b040f604051400781c1d40118a103038030107051102e10fa140341401a000d00041d102c2c590104a0a48244003150042494100240a008903981e41e14003145d050b00b0403640082901480d100103820b605042c00391a11851008040d9072070001401e40700d03010035084d9081a07800d403000384000f50000b08405c1147c00030b040758100a589a41c54103d19070303d008005d0300000c00304103010300d4860000e500308068003950a041d0604030701d690307280c1805440031142d803540507004038240040042030107280c10559440e41107410400034000358085082d2203000810340001d0204a80e103101d66006da80d103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 390907338 1250 390906088 390906169
    0x60b1b07030f0f15050a051509010b0d090515090c040f0507120c0201020408060c041502030f160311010213030c0b07260c0f01020c0d0c050309010f030f0e1b 69
    0x111130340185440340f200b00b04100c0c0c030f0448910041c2982c1d0028886816502ca02d04041d080084070200559810140e648255002e40c5800e10300a6884a5541701040001d10110340da2200006122005240221589903255044188140280d00c0c10000d41c200700000d0141d00d1241c015511080ea0083c0503260315030050002503201c0c2d0446d5401e00000c10a19018170182d401500c040184035162800c01050b001e01d0150704146900750341c401c00c0101401201c041c2a10811048840300045e06100b41c202030b248040c00a04410756540f0004c0c0803000105401604000c0d2401040054400d80c3c40d20410560342c450300d03030701900b19801800d01048441a028552a00c010303c2064641410107010358285400016802d1002e2a500442c0ca010345032400c011a5010000741e1804c0d42280300540c0f26503440707222383d9071007a0400016409107000c05010381c100d44403901d0350100c20042d855030703420101d8480840318604007002d189240c0303840540c80e000c5503104045043d40d6054020a0f4071a6030728888171034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 390908588 1250 390907338 390907343
    0xf0a020c1506030f0f2104150e03030403020907080a05090c132003040503030717010f031e02061b011103090d0f18060504090e010c0806130b04060b1b07030f0f 70
    0x50039110248130300c001c3c444a80780d855404001d11200308501e07100444090301c085820a0700c03000303200030018802051900400390f03c15041c0841e100c206400864114170075500065082640300b024015500d070310040140c800c0000041c2005141c4580700d602e6158541801082e0f4042c0d108810b0340307000009a88040c54403900107104403002803403042c101c1d406800840b0191500d80021041080258222210f17040251220070b0f40c510542c1041d500e13010860103030102030500119894903c00c072024203001c3c064120b03002003503680c45880740c46110410307041490003a0101e50a00744031010240d181c0d011f0768001d40d044005060504010b075800c44519524051580030410380c00f1030081d110305215a10700143c02c20740d88503980c643c1080714050640b03501d0f400c0360100d40e24042580c5e40700c44d803000c18107410a404039a8088031f00203c1d1940702c05420300d440d10591107450f100001402d4403140c0d000b40303180c0c0c60a121800201c20803c54a58a445080c400689410042011500015010790030b100a1a2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 390909838 1250 390908588 390908593
    0x2030c1314010303020d11012714100b0f01021b0d030516030504030b06030313030303020a02010e15070315030b0402060a051603020c010801051509090903040503030d050f0a020c150603 81
    0x441e441d0208001000e910550144e041614200030056100c1e24500c2d50102e40342c028059041092507111480c0c11508140c80300f024241081004c1200d0301c50184075522222040300c2c0c41450464404004000c40034006200c1c400601015a842d4000304e500c5e43d00328502c2803c004010340300018880c80e0856024110204070f810421400000300d15401c0d0103609000e41e8542e521603066161900d1408800307008a842ba60007030215403580c00c031011550040e41da0501d0056180c0302092001c0e4090a407029002c0c849000b4141e504900c92017405606210340761555083c172112007031045140e8261218040500070780c04400004025040c01c40042071601d0b0300346030651501a5040b49080180560354040b40103070030826000485690080741c29026060440712515006140c00c46000c040c401c4804c41e5000e2444800041d050000510580f40204406000d8035901e01040250f44014002181e84a607484180c002254040c43c051090300d544400050003080014202c0c020b8007050400148005da051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 390911088 1250 390909838 390909851
    0x1090606141b06070815040b0f0f2b06060504020901050a2a1203050c0309030d09080c0f06010e070f09061206030c0909030305090a0f120203071b081005010302030c13 73
    0x11a010408148200d0844d911030000303003080115003000c6d90550701c140d4862818200c140000380d946048032079034008200e5030007044d52003c501140300034030201e02040f0289101c90418400124980401e05258801d10b41005641d0700c8400300b10480c000e40c81d07400d00259090107161580d81c0100d458070100a48400740700002c0100007680d0001e1043d49034101c40f1500d10202d103803c016007502920382c11464050300c1c1415441c15100d005e50342c2c0640312401021588170300aa00c14004a4000c41b080340700c4c2c09041e6400c0e01000e48456070b030f0304d40a11402e2a10240c440004c0c100d5032090340ba1008501e1981c7d1110071003498401c2c1120443e1054141520060b925000000050310f085000c10080900c90000b0610f1601810044d040b40e600600f101c20791b030842c0307030041c0009155814040e08160f104400c0f10441c0c61072201240740d4081c1c0400109460300c0085203080d010b168003504411180301c40201d40e000c003041c60b107541c240c4400b840003d400d80e20606d071020803454003130708030403a00c000d245000411 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 390912338 1250 390911088 390911137
    0x11713170f07030c0b1303080a020a1101052e0608190b100f1b080304030f0c0c03030c020f01030c1e030222050f0d05060109020d0e150105090109060614 67
    0x30341c8414411400b2030300200782d034420444445e42d1158405001c031200d00c4502d0050310040d046100061044141c0d9500291900319940101113654607001210020810b86c5095565900d407422000700f00240b84603400310940c142d000c0420050162100d941c0c1c0c6004c1e98440c00c1c00d007a1004111728042100c46d40700d20f105030041d107513121962442c51546d0b440040742c0c02640780c064140080d0070060401c10310000712703c601154510044942190345860400030783e4044210495030103070340c24001001c2c0301711801c2c0001810741c8000c0c5200914003ca0b00080210581d80040d0200d4034075000220219503507001c1c0000300040c01c110f0b5100c500c45801d0252404d50012040c059181241c1c032100100342884030140000c0c00c2c40856244100e42c1a6400b040d4146542c9076a070344c541051141c2d010362500001c003c0350400e440d03000355030416181e1085483d00c80c100c03a29404000024058140501d5850000107200d0000d0b002c0d90045604d0740d1100300d4440021803400320940c3c0b025280c200e03900e848101c00d005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 390913588 1250 390912338 390912367
    0x30c150e0a05100b01030b0619170a0902041d0a030c1110020f0607231e03070f032906031b040f140907090b090d2001171317 55
    0x501c6100d00068998043d8015805084034204411503041610301202000e180d02c0d5802210992414203201181c040214401150f000001c3c400c240034228083c001c0c08804c20b41500a8030100c2e1080381c0522102e141c48402919610301541206495408903900c3d0004c80d0141d20f1603c0c80902840d1080e0f441c50700e031b2020480c00019002c24030b0044e0f1092002a40320041032106a400000398a84500102e422280c400bc0c0d00d081780030504501e19000460f1139100e06900301c40c5034407200c4076104035281d140024001d09003030a429120004241002a80d0b04900c01c00da54a20745c15803403407007031110304001a0500250303804c010141d02716107140400d202507840c10400900000c112000c9000d00040c107021044000d8070700220a240100340101c02e2100d55508100c0b0402070720b05481415840c3c00d16800000c20120072140040c1079840c903100300c1d42070f80c0c800064038207000d0780c00e8070780b0284d01d04da400180394a05000c89409200400d44a42c403c0050740001d281a07003506c42d141700d642082500c4a1080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 390914838 1250 390913588 390913603
    0x203010f050907091a1008070903050703030509010815031216081b2a120a0218060a2102040902010207091109090108010203061012140a1505030a030c150e 68
    0x201143d10020007080300c038205004d15011803662032144c51000c4d10201c041242c070302c0c505044809010100000660491040500b00e006503000b00448003880da80f418041c003942c1c410b1501e40d00040c0100c00041401c0f80801c0c40007a0007001500504c100c1d401c0d44a21619a000130444481c9078041d100d90501050140c0007600821800da1020070405401201d0a840c5c58041d195184020904007080080070f6404110740390700f10020703940c080550400d03049543c18001c520310000d5115401c0305040902508507250707a407048001f03072003032a013194507008200ba1803107864080038609004595040010705245d0440307402c10b481030044640145c2c41b0016981540c0a01188020700140410070808a00e41540260300529140c4000c6165040081c0880c10700142d81c021181405041c01e80d1841c15903166126440c100c00d014a1902d03d8100824084040c08550300490380d0301410001c04503039031401141a6000d80d605849900d4040f02c990307034140080f82c590115003417465840901c0d6500010038000704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 390916088 1250 390914838 390914851
    0xe03030906070c29030703051302060c0601180e06130206041a090102061003050c1207090c09080d180303030e070b1204051b0a1211040e03041809030909090203010f05 73
    0x204110f600309000500d9146115985440140c1c0740b61002982c2c0c00c0180441c2d401150340e19001c581d40d91070821030041c1d51400300c7c000350000c10001c1d5270301304035201040c040c2c1600d03088020b1021180c21a500700e0301355100e0305c0c0120500e8002c1400301d08150b031403540e0101c5d03591000c0c0241c1d04103035452045146e101c01c50f40380e04500c0400041e141707105603814040907502030082e42400003c1411912620b989012420340740e8058503442d000c4030380303040c0108043c50046c0f000e20030500414040c42d0340180342d01000c0c480d9190910a090440700285c0c060400240360814010f01c48141602d59103003240603200090ba110000d015021000c140380024400820040ca507101c1c00510034101441c1052034250045034040006180111190080e92103160800803152a010316010408880c10441c403c0301d003021f03800e80d000b45400340850902c400030014004942c09950401401c071301003007501c001e0307400700b10005001658592040c00400c441e0b6100e402e0160001d00001a0041c040007001d080b01e5066450 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 390917338 1250 390916088 390916103
    0x30212070303020601050402120f0601021e0109020316030b0c070303090609060b09060405010f1716120b090c0d060c03090c03150b01050c0a020d0512070b04030f0c0f030e0303090607 80
    0x40c000c2c96010070560303005201c240da08500d029107a40743c10642441c050616444044a8000b00314242e00c00c00c110058000d0044440174006a1000118020220054202e002e0702902101c0050140820141c2e01241d800038807514055982c42ca088240750b008071022400c1c5590356041c0c8000c070702644580f20881e4410780c07000a0903001c0108020b01440c004140600c19402c00c401232168120040c2c04a08030380e100e10000310700786003121034a81400242210000a1b59a00c10b0029000c00b0b96003d100149000700000c007115225001150341b10308114030b81c0c0750000003c04000000560300e40c044040d02c8190b141c0002c00c0a00e55407404284649a8820b44840f51151440641444280709050001000b4240180740c47c43c0b0760180750301d40c0005c0502034400c4500600700418402d05201300c040850580030001c2c0d44501d40c0c41c3c03880c4010780607101600098403800c030402019029034410180c0c2500a00102d0303103107402d554100c40d0350820502c4550540028040071200382c885074080d02020b44034550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 390918588 1250 390917338 390917353
    0x8060a0212011403070e070908061e13200d060507030c0f0c20120303160207050a060503520329010309080d0c1103042607030212 57
    0x7aa0841e0720410307000218031600c0c001407020300d0750700002e42a0896941182e501000e44e41e040059802005540c0078541e1401424100414409940d4009203500c0b610010386125407104401d40004250ba550001d010001503020000d40309103801c0c0d03c90414800411200020100d9a21401503800550b07280010036200c2c1d420f1064941c2103801c41604000b41e00e0b100344a00c42c180c42d040c140d824101540138a403a003034480b51101c1c0e2900081c1c10081c0e02e941c0c1c00c907079682c00d0070603800c15507080c4040f07401b0040c0103042004c01d040c0341207000082200c41c2d82e03071501d0464030b0300400c51890480d43e56504100746110214201148545803204c40b03135040c90000740324601190418090484500100f1500701850705110300b42c1261040d803440301e6001c140300c1c5090419140c4005078010151044007800d050f0300454807510154041d00300c5192020b545c2d450029011070641015524065406031405100c1c80105140300e10381602c54807817840c01180e0884141c2070380e81e00809d22660b19000c00c00c4c1150003810703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 390919838 1250 390918588 390918607
    0x60b0414100501050307090524070309030b0c07030804020906031606050408011113170c04090c140a0803030a0b0a0b0f0406020f030703020c040b18010801020406020c040509060a1508060a02 83
    0x20754800145800e003086840d500e05100c1c024461020360060354841d0003000d403800e207100340c00c001c003040c0e41d0b080000c2c039035840c281820301801c0b10341548000c98500c41100005503003d84a00e0540f41c1c1e450b07254980e440300341c4440d420003840070002442030342c02d482920101d52400c1c0030b044281c0000c00302074035595983c9041001050a440c8030607014001103c0400c8000c043c0840400e949003120911805e0040354000c140c4503138141040240c5403a0301c00d003401c40c40001d00085540c2c0b641144c1305512004e282405a800b07018140c0f41034030031101d190f00705000140f0140d05582060784041c100074140703d40941c45000998042e00559119400306c04d01040610855404009043c0c082035841c00444c141841c0d641c009640d24000701e1f50038060350321902c0300405520b5020550800036040444030b00c1660b100c0301c0c21070003034100c0d01c510001131049515949040c20148610760140c410350001c0c00ca140c0c2d45200840c06840281104000079480350760025141c00c062040e03600504984e5009642e60b031046 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 390921088 1250 390919838 390919861
    0x3020f071a160c021e010203071202071502061e06040b03060903030906010501080c0703030218040c0c05010f0c05031605040e090f0606090f19200d0f0e0d0c060b0414 73
    0x2c03100c480038054948080400341c1d45d0419400700c40074240c02811a00358040c2c004034214003607880c00420f011501d00c02e402e00c840d000b003890030503030360421442060151f10040883e41ca0760156182040ca07800f00e5650403d514003080d0190780850702500102d441082040428503084085500911640003c001d101d4014414080140104400d280c4205581011107640c4524801c6c1000101855400143e19035a17808040714504802c1c0300500401c21900422000740204005180860781e039483d0900d0301e8940c41e01481030751042101d96407584c0c256900d40c07810f03404a4036601c501c1c006212003800001480601c894609116244110150025050203c2d29610702100a801c05214924100420075144041c80b40150b000710a240070851811181c0d261070010308019460b003011030000303220806564801402040034480401082014a4640030034408480d51500c1000080c0c000344d0000f21902d100b0850300c00e841e40603207400212072016900003006c030390104a4220003d40c40008104460099 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 390922338 1250 390921088 390921121
    0x308030f060d020315070215010308070c060f120e0a0209010b190302070308040305070f0b1e01050d050c09041502031513090213090f1a01170c0d020103020f071a 71
    0x155074003042c0030801d40c0020b4075000e5001e900c07281140e200000a825520030040440c0381040c03007100d02e8541d612800c1034107485e07100c00c04c2900c100740c0340e2000040c514852090500b41004540d07a891402c6071809503280a4500d5a409000381d00c00c45c06190091b948102050340202401007002d981c821046559510b400c4d090842c042c203152051140c400403c2c1c109007038651103545458040e649004070316003404e40d46520700c00039210900180802960303c0b440c01d44404140100c0f480c25a681c0e0ba1441004000480500001d00c40d03045902d00362003605000e000c1c00d4109101d00b0307801540b1038079031101800701c3e0004c94086d1152103242e1107020301820140e112494000c10a81c040c0100c001e00d401103079480701d600d012030812954400409040c8285003000c0121160b2000100c040c03c140c5e4000302c0e042020a0150007004240600c3c405002400002c40c4c8105610140030081071055903001940250485c4003c0c2d481000c00b080034000140c405184c0d5020301c4145110b4070164100070185180c130010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 390923588 1250 390922338 390922351
    0x1a04031202031804090620031807080d050304050f0604120306090c0c20180103020306060901030c14011218050c0f060d020904150603051b0a0e01030b0a0f0308030f 72
    0x4100301c803210b2681801501d00f035940040c1c40c046030010151500c80d0081c44003403502d000140c1d403a405c05904101000007103000c0c9080c8811a101c0c4040781c005030391180610b1040004590200e003011400070b020b98059036006008600381ca00c655450003990b030900404840480380650350b0b502c242c8105415102c0c84010b810074560421160502e054090400d40300030070301502120300e015070000b18200c03048002c8039500c00903100e904c0d02245030107411442002030000301e00c07074062800000c40074148510001d040700e401c0000100c0c0c43c0c0c030b8050708001071140005542d0401140301e41c21a02c000280c0640d51036191b5182d44c0c4140108142085403e055104004901c00d24035448041c071940d0b1040c1c02e0f01d2085011080050762560030500060007000031111200c404070120070002440b6426a2006100d49032009401c043c0c0a104158064588118040d0001040303041380c0d080b5075548a0b40c4031f00600c240203040e04198a481e414549580700c041e170f0040310000070000401c08082d01c1c00c0c45860b000139 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 390924838 1250 390923588 390923593
    0xf0d1a0108210a08070e03011e050103110306090d050901030b0907020a0605090706020d12020921010507080c1206120102180f100507080d090b0a09110d05190c1a04031202 75
    0x3194010042441501905560402940303403c40c541b45c0e6801e6108890142d03090079203038403110001c19054080e0400b40320603180410521018010f0341804a00326100ea0001c00281c0b099020030034081e185071304400e42c0241015540d801124032a19400d00942c0502060780041c2941102481c20000b50b41000f409a6065003145400304291500001c0c1c060b03410102e41041186a5002d4000340002d020b540441d90340708030050025a40d4103c1010400585019000280300507038a50078156803404d81075840c20204c141c00c00400082c80801100540c0046008200320446a000c59a10b4207a8100c014109031440120b0418025460000b42d00981d1000a0300d4070005034240f1413002d000c0f030241980c00b8104e980000b4210340040c50562200d5401517224140c8410f5040010040c0010f00a0304011244440c1d2100d1012003843d021381c080c04086c1c3d01800030f10101c03500001040320120051001c990403a51128049813a00b880101125041e010300c4100380c4aa00d5400c00d004025102408c2d20150f4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 390926088 1250 390924838 390924847
    0x3010c02010c23120406060e10030221031b030414010903020607120c120201020a08010b03060306220503040905100501050f0d0c1710140a050f0d1a010821 68
    0x95040740c06080c0c112211001d4902074042407016405521411815244111441307041000f00541c80d800b00003078034800000b1004a41d0740c010300500d4a41e503400082d40c0000000820440007001040181160241c80c058a082080c0c90080101c0c5501c20765000c600c640020506001902094043c0e070304009091030500c03010b920750740120f00c441c4111b03680641581601840d0310746640c043d201c00102030358482103400c2c2e0804280c500030f000307400c1b46c40150b0018501c1c1000040b00d107104000d072400b0b0311000f0090002600e03078241c0b40100001c00190b44000c0500c2c181d49402040303091000e0002440318120214191426003010080c007512504079078180300302807000204190222090360000d804403800080d04a0040405030b500741c140c01c82ca8003010461201300400d07451005000001c4030b90454403444244040c00404c04a1f040c40e0203800e4101070045c020190380d1070a40380796040640250301061609490690344110721a003604001c0480d40305401900d8111070706244948a1500b012445040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 390927338 1250 390926088 390926111
    0x150b07030809012f070302070302100503040b0c0a020d1d0604080303090c030a0c03060b130603060b130216110d020a080703031215060c2420040e13050102120f0603010c0201 76
    0x104c3c900c00203509410b103001c20f0940406008103c1c100140d500100f60040758904010010015841164102c0e41002c1c1c02d40420715000d086000d55200d01800d4014280c1c107004030200320350030b0214084032002324070812400c58194171150010320103010140080c540e6841c090400c0c41c6000307400240b43d40603038003405002c2d0100f0311441c40303041600d1340054041010313540301001900c404240382d0440f0401c0e103002c07800001c000c110751025500240548407280f40c840f120505800303d0003006401c4c0110b076810000107001400c501c0c0450380ca100014050b1000601c19004552096117035000001c482e070100c2d005109040e088900c081d04658171400a00c243c0d21800d4a15868550700d102d04410721280c2d0415004000b0115031a40741807100d22501e070034141038000700714050a26a841c10701003001900d41c2d00407600380c15045a090360046100010305803283d40e07907500d144442e2202550295401e115000d80c808140c5003240c041e04034200c0c0c0c41d000741080310806084400300c80d0320030306580c5011401460b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 390928588 1250 390927338 390927401
    0xe010618150e090c040e070f0206060111030a03020904020f0409090b13020d06020a031d010c0908010524120a03030c0909091a180a05030c071a0d150b0703080901 71
    0x19000b02030302d60304265212a40380001502840e040100e4000340c2904005034590b0052038680c80c02c01642c2115030986840c0c0c01522080401825441241c100700a01403050340250000c020b800c4010f000140b505031200340100007500705800c401c61803a1258071550521601402071030704400f00c58039984090300e942c1c2c00201c070408200300091980340c0100f010560140a82d20402c8940c002030381c0c00c0c245d40074005d03c2c5402003148411102c0070801303201e008200403005105103881131035210b80d41031281745100002070141c0c0c60070143e241d10865a00ca030105218043c0096800c0500c69100400ca007581007002400d0946250000c1a54074540700c643c0c008100c0c10b0b01700076000310100035828030680711141d554403030b03010280c0000d09034812003041c6420050000010500c0318002c02c00e80d82d005464004030500b005030385441c2c48600d901070207018040034207640314410400b50580d517840029502c0410b0190380e00041c82c2503000c101e541c020801466001c1c05911b00c80b40207400500140d5418102e08136 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 390929838 1250 390928588 390928607
    0xb012309010e121c0503100515090418020102060c0903150903070f210c0525050d0302030d0f0b0d080309010f0c03020c010c080c0a1119080c0705010201060b030f100e01061815 77
    0x748101d40441c1c180a880027003200701c903e000302c054400d000c0e4543c00749002c480d80709084400c900501c41d48001824455061b0706460061800402401c0c1005d00a588001030004c05400007813503003c100407080000e01a600d90722000e910521010070503015404c40084c0020a5a840005010030270100d00b00040c030101e011101c440300d4000415103066451040c60b8411195003016030820310400804081c1a0000050404038410340d0050141c108884440425030700d40d042055000b441030309218001481480c00f559010f40140b0000900c5c070700ca44c4209054071301007549100426030006010760031b14800e008415548196050024003401c2c441d080001511400030b9040c2044900a0140c030109810b114011003180c131882d4404000d005400e11108a41c071110000c0761520584100040d00e5006004030000c9440002a90f4110740c1d40c82c081006030840201184981a210711001c54184004c4032036078080d003410754610000c01e00c20320a6461a484035000300b035000e6514114128500c1e030184001c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 390931088 1250 390929838 390929849
    0xb010e19020a110f070503060615030402060d140a0b09070c031d0112050c04060908150c0d090c0f180605060906070c21060b012309010e121c050310 65
    0x140e0b0340d080c144080f210240c0c800c00a8540d4040d50280b505001e07000a00d9000b0703200b0880980c0d4030358485100b040380030450f101164407043c03024400034016203001c9000e8803a2411800011a6002840d90351185802c4210741c080741482d46e82a40f002c0b2400c4c014802d03079105c101e13800d16456220042d24050091a904c4849009008001e83d0141480c0d00c9004050b003204540c00b4280910f0802e150080407580081c051840000c0329070000103111007000904402c40714406503520714030740311000d026000d9406160031940d140d4480710007400248141d04054002c003504229045803505262040750000808865104000c0c10050f09001590b171b070300c04407582e505045407050b640c0c1066181180045016501c11a10310910081c0611050300c1022407166103440b901003000400091801500c503004141d01d40890043c100103001060000040109048107050408910141004000a00f02c4030301c02c4424040e42c1003180c005140c5030f400d80d0307031424000650420b541549805400426a0034461090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 390932338 1250 390931088 390931091
    0x1021b01066e0108162003031b04030803010e0c0f0711030f0c090c0a03060b0f070c05060406080a0e1c1701080a0206030a050a0f0c021b010203040f050d1a130b010e19 73
    0x502c010600403039160f81c0d00001200b0081307595400301001500c90b0012200302c0c41000e100401c9c40b00c011a0030342190141c035441003041c3d0940e401d08034204e070301c00d000038210014000d0400864280100e24000380551500c60312004108074503080c14981020548891026242e0008540c1e42440c0c1c3c8900b0810750000c103030540f854454480326000ca014140315804110304013000685400c003a204030009041c568000e20340100059170b075100f8000380344601d1007113000050f42040410141c101c5500082d032946030342000c544956002004031040a49050240302c0031820b002148407004103501c82c100c3c014050b00c00078200c070344030070f8000c5041440014181204103a6400002d2031441090f07024054007920642d040040ca080031401960f9080c42d041a0120300030303401142c1e481d5610000440d41a20744580140004518010a04c003401069400880306540444190140314104041d0a8445c2c007003010503510b41a43c0c2d0400d101c0520cc180c2001402d07540103405c21480310240810101c066101c86c60 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 390933588 1250 390932338 390932371
    0x3022a0f0303070605010f031b150809070b13061d0306010303080901060806011d09010b032812031b0c030e0d03021504030201021b01066e0108 63
    0xb4114894958024943c07440c16001103000300d882d00c0d154040c1c0b4880c900c006904024404c0d007a50a414034822003905040c1e400c03c0c600345600c01c150300354021801e030085644130341e1200c1c9907081c0358100803070b0f0b441c0d4007402a03004c1100c20342c403010a0b03034155100034103644003040711008251642e01c140401703001e12491f43e0204002c9102503020400070031404058aa4a58441c00811244040003c0d40707002c0c040001c0208001500621030041e88140c000c00420600300321a103a5000d2212110608201c120407a6409011803106007881803440c01c203030740010b625078031010500300c10101074a4000800c00301385410720000f80c0140e8681040c03841103c0040d6071f2005498102e140008d403500c03161080c922141070000b09901500070307110303988100c92030151a03521041c29131b08990091041d413010036110038000b19010f101540342900c41d41108848440300c01c00700006102c81004003480c01c010440b0082c8024581003e6812420590300005610040c48120000034251040a040c84020303a08402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 390934838 1250 390933588 390933619
    0x60421021201020d09060b030f071a040305030409061a0a0504030b0c0408100504022d04050c160f0b0601170402130216050304050a050604030305180a030f080703022a 73
    0xc0c4140504150754000399502e014503098000900342c0c11078220750b42c0382402d80e0001d00c1d1034042100300d040768020f002000213915000c80c071059819000d0a2003840b5008100101c0812010320040c0050543c4030790205010380b901000703a04110a46504a60044040c1302222009074854116001c4980041074075126460703866440d03199201c0ca9102862600c2070700c1000800d40c1c03040e08454400ca000300c507100300c001c500d04a011803441c2041044583d020b01c00b4080c104038542644043e80010303950144a04244400c10103005101240d10243c40000e185c000d860201704003c81c40682c005400e00c1e0003080c0301808607402403c000041c00c000d104003001514078656810a80c1603d10888500e4100401c18005050441d00c0364030600a00d80034444d40c910100d5282004403c64085940c150b9410b0300c0d141175803007605440f09031550714940c4043c05510000c08180c850086400b000d001c0c1407a50740c1c510052502a29168084030001c03041110000030803500c01914030b07812202c07001070311407004450b54030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 390936088 1250 390934838 390934849
    0x250605031e041106120711190f0c03171c0b060307110f0102040b04030b060603150d1e061a030a020f0d020102070308040b04030302150c04210b15010e06042102 70
    0x5000d0741040d4049004040c2860f00845c0502542c100d48512405000e20451b880c0c071198150158031614610210304070010b45a642d00070b03502e5000d100c440c0080c6489980e2050030000080840c15280804664020047d440301000c0e141405010401c00521070110701155113400020110020710040709002000c000003170003d11480a00c00001f1555941c0b2202c01070465085408203803442d0841600241c068200743d13040340d001d01406201d0100c6801300d102008010321801c0e00442da401019284410402c5445400c50300d0584035110206840c8098540b01c20b14510761140d0354481c0e800003c0e40c0015846000e000f140229080ea01d00d1306450103400141c5c68856030740d000030100b001c00076001a94945020240094900c03d60980d0b41d500d14080e0303140640e0a043d01c0c803d001510400c420450540d0281c00c420540e43d4011105103111203d071650000c404e003c885a100c00c03400d0400ca05015a800f4074050740220088901c20304050a01c02010340700c1c22400032003c00d10341c1201105056642c0d2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 390937338 1250 390936088 390936113
    0x2010204051206040f1e1202030a03060b1201050405061f02030703030e06070e010302030c12090c0a05030307080306060a09030501020c0106050306280e0705030d030b09060f13050406020c250605031e04 88
    0x408800b900a030701d820701c000d41c3c83d4070586181e00060318210001c194554dc81007126424041902e000c000c84e42024100001000060141548014000010602303034409001a000854141d0040c503240e09050401406641d21051130325910707000710313040140d40c41d0040310800c4891404e00c1c0068590366510203155840c4125840da04800724482c042010809000419821100007603504e01c44061b40c980a050307880c060342000514008090000540c42e040c03200151000030818a13010b1b00700f555940f646822a8407151071170455945030079050165050400c0b030540c2062060301e01d00c3e0040044101c0780d00002c0d1060f9004801503c90103031a091010411050001d07000041c10340728190f9030040e0280003441440081402035041c000002c14600e0003c1001d400464040c000c000c62003211101d5600030440240101c981c15801e1040131103501c001c02401d0703228101c1e40d005007a41e01219003401244100781c1e1280b801c11070100108105489d088580311032190702e0148590700d03515a8a404003c0e04007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 390938588 1250 390937338 390937343
    0x2401050c0109050309030708060c0f0a090306060b07050f070b0a0e1f020f0105090a080a080406060b0f040303020f010c0215090f0d031d0a0c0620010203010602010204051206040f1e 79
    0x2c0c040b00c8000e004012006100d062412030895400b10703a02c100c225111201111003402c02c200501c0008401040b400080a44c10214941084125202d6407514201c0740144c02414100c000841c0321801c004041201103120722440340100140391409029007654451002200c08012806420903426196080700f000c4c400421019038a43c5049240000d43c1d40f031000301101e0280d030030180410355016004c10a00606604000382d40c1c581185100181ca06000142040f502503030b0700d00300061407802e2480500340f10024180f00c2030f40c03a4514207000f0301e000303c0301c078030641143d14080c0400c83c05500022502d102c4000e11009403030703540da180d6100307040c0703081c0050301d566030b0240d1216007901d04e506a0040c0c8021021100400351384001c06a030a9a0310740090b00141840d041050034010355004844500c1500c81070b0000d1102c940c0c1c0041400d003640c00a07030020000d80c0d004103041c0210b1901ca0300103846903800100078021440e01d901c43c40215081648064915181d0b038201c80d101b0b0042420308800d80e034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 390939838 1250 390938588 390938591
    0x402070302061914010b210103051b010806240706020a020304060f082a0f12070e010507080f03060d06021602090a110f0f0c070602160e2401050c01 65
    0x419420040d44560003119640034000250b082d5582109840c86010302400c50610182442d0f82080c00d884044d0b40700e8243d003140183e071060751202810003219114041c5205101608910880c020f820003d1040a01c1203414400b42e0303810410b55450f181060030194071000112410303070340c1280c0713000494072503004003414040c000074440e600300c2d030000020801c0720704641e40e40d030b07480c0c1946004458801e01665a992a07503240282d40d000161407080303491001900352440c62600740d08200c4842907502c103414051101e114001003006040d00085810000e28003800d1152419004e982d94840c85e01c12205142020400400400c4203034450703203c0681419031042c0c0440d0f43c0d03c0c3d0b480e00c800c1e080c40030800492189052600140c040d486038003503c040680c80c10001c50800d400f003106000c1a810020940071401001e025103c031806040042900911580d0040c1102d148070014948070b443c200e070032100c0c40342c42d13000500160000d400045d405000e10b00d205102504180700c0102c41c280b144511480d040d6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 390941088 1250 390939838 390939847
    0x6080705031023010603050405061501051803070f0314010501080304120b0403090f03051506040b0109170a0204060303091e060c12031e1406030d2007031a01050f0f090705180402 78
    0x99405031f00031800360340034200b160300340c0d958200c0c0185035541154515000a106119000039960300090300c0003101002025194040d856504030520420103501c26a021100e440380304030310032403e03c18107026041050284d494981000c0c902d11152280c0040140706d00502000981451300c074540072406420301c0041520301c680d981c20500d03511155400c100060844c05c1001c64820b00d4144902d480b141c0d0180c46a440300c610b0b20050725108080d0b50183c400500401200304016030b101d110304405035104e61121036595081070160000ec10031155500d15900410806010180e00215082c0030545d11518012807400400b07003c40190504154004800d02e004e040019640ca940e00400c842c52603402241045581d25010181e4070003084400f107010400310344004041c01303181c0c070300000c00d88d11890481c1c01c41913895460407410245d500b0036282c0307142d00c800148014070b0704403032034040004202c0d9614124940300d8000740012700c02500e0541403010000b206100c4060b00d01019080d04030062046444 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 390942338 1250 390941088 390941099
    0x6071a0a020418061809060207022709070f0e070201180305041802120103030341060102060702100b030c13050403180f0504021b0f0f010608070503102301 68
    0x42d401c40c0c02026600d03204120740e0040603d0030b00c9040c0c22100181c5965840c0400300300400c0003404003000660b1040c1d000c106000140c1c8502d044910b0b840c00128407018070f8003d41e0021100182c01502140050700074050400116900f485c01c502501d002e155003000540310500306030700500440408040241c01d805660b07050640010250045130240000c402c46240800242402c92260102c9505411403900c01400400d20a600c0b90b240d802e401000b00301c40b9002100094405d0610f1501055a500d0022081000400364074890350080400c1c0000d14481c103029101035180d040341c0c2008908151795010f00950b660b400c12802c0310310398002d40105044141c00991f08007901d411542680400c0e00303020740403105111120854200c8240b10b20490f1824108420040650b000000c018020818141007004090003400240d04610700c3c000207048401c100c6100c142034450345d0b40f0a5080c1e030820002042191070100c0d4002400800383e4000404021650b00c003190300883c400400907401024001152 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 390943588 1250 390942338 390942341
    0x40b041410030b01052205041704080d1b1101230d020c060603030c06010e04150e030c010b0901050f010c081b060901110304030f05031e090c01080907060e06071a0a 72
    0x10740c0d0007200303080100c0c0e0b282c0083c4455100c00c013440d1b52100d804040ca0079079034602c0e603001c00e400600c90049518100b41c2c0d40101e1009402c1074004c070040d9045081850b5001c1d0304001024500345004105081d5001e00d82c844240c10340b205a0504d041c421500c102c0e94168030880c008403074030309818254580780ea05810211000390000f088502c1c00384502c001003605803500005594004003600010003c130fa08109044c1102c64015100300e03203021500f80c0a40312072005000d0f1180c00d902c0c6500450f2900020b00701142900c4085400c24043c0c44828010300054546202c107003020002030a1402d400c50061030030702013600c03562055010b050798400e41c5910041000c605a0b000341c1d07580009201c68000e44001003130910003640c00802240c00000141071090141e00616400507140d140001e20240d2074078201010b08089031200b0a941200f14184541c0d81c0114001e50070640076030040c0782c1d07a400c10b50041c180c0c11246150505c85e600200f101c100b0040311801e50f1445c14201c095038500390030b00703000100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 390944838 1250 390943588 390943621
    0x306010905130c020610030b01062109060203090c0d0c0b0f22061107060f030b030c0a0305060a200901030504050313080c010f1805010e0301111201030203062202040b0414 75
    0x900500501012806c0d0040e403546050a0301c3d0440c46d4209140d02e080c400f60b90100c411340c48010503590711141d00b8080800d500c15020400d0040c6d00c0960360f40b4000c96914103140180c041e181c445c2078800d00d00c0f40070800c0750800009070385408451350b170b9401c1c100751010703824040e07050a03ea0842605404c1c00d804400c03c1c3d102d00c104c8040340c40303009650044e2038403030f0380b149042d009590010782c45810f07051005210b03400c1030b40355100c05400c0c1e44094800001140d14200d90f908259095800348082c0000b01405115640803c640035514070758800610240c074103140700d8120060b0406072207a0110341845010310840742400340840010f1002c2d96120401522580c680045602180c14281003030489401100340b81748044030f2894008040b030600005489508010304200d400d1746d41d4400d43c440426034a001090141203480f00006658514410075140083c01031011a21035450300c1ea401032040c10500740f40041c2d41c100c2700403a4148280c070100e0020a0f074801040c070030840d0842405549103801d1500c2 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 390946088 1250 390944838 390944861
    0x2030907090f0b0f060a080a1d01020309010507090b0a120b06040e07020708062214030f040f180b060a08090307020604060f021e070512010b040606170604050714030601090513 77
    0x103804c011a03840c00c2000c039000740c0c0d8000c0c0c04a5141c50000b00118035607400448111580b10b1401c4014100200140c2240c00460382e030381d0b9136035544040c001010b4104180780020030345845d60034507042d1102402404045815520f0880342e80324446404a6611201960003030007500c602e11040703141c015002991000350b80300c0d1103014001d60b000320f40c14182114040c14614548d0700b201110400c5652008902183d0005460040c0400c2c0000440d82c0601001000100030783d18100729076078101499066200a007240c1140000c0c50003504d2000b03512100d06468011655003002000303035441e840780310300314842c4000c001c4d40424006404036184d60803040d1071003031080365400c40b940d02e10180034034014442001000a10b030342c01040100134510f06451792605040c60304002241c00e00300031000c40c064550642042c004104040c840c100c400c201c4405c4142d12603001c48044c8020708210300040d01c01d030385100c9145a80d1800000281d000d034040c0d0351110040c00702510441074840302401804c010104da0402 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 390947338 1250 390946088 390946099
    0xa080102280810030305031306180b0105090f1308040801050103030f1806021b010e040c0206060102060a020307050708071103070b0d0f050108030a32030106080105010c1502030907090f0b 82
    0x5075400c0034420503000b8450300c1ca00200c00e070b6240c01e54409540c3c540000700b1364042d502ca10b9030304e2800210180540210300c1170685510b9450122032420060390306050304084c1c0180400001c01000c10550001c950b00801300980441d2084190f00b041c240c640f103247c003e007503190f003454000810154808091081000e1030b5a83e0480c40d440c410148a007030480340304540040c0e102c070b1040c27214001600c1d480c21400e00141044400d44801e80080790549040c480e02c400541c100d00200101542c041c0140b40d480003440204510f180b8101d50080c10500030310f5005095a400480d640c010441c40792140c1e60383c55401070803210819900c401e1411103a1100920910850501c5820740000c031369401068181c8801c0800341d42415028101180d45a00300c5551500704941800c01b030040302000b201c8481030101d0742c1c0e603d40c1d4030360415078083c20160060740700710b0400440760400000301d81320290310480101888000350343c9803180540742e850001d42e038000c0300200c0c0c50105220101c01c0039074055540b941090300ea = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 390948588 1250 390947338 390947407
    0x180e0c0909060607050d0e0109050409051b0315070c03030207060f0c111209060304080403020a03050c0a2102042d0b0411040b0706021e16230304030b060a080102 71
    0x148001c1e4011302d1030090a5500c440c0c40ca131070160248201c060000d034189040b0008607595000501665044a01618160030107121080488900c0000c10280074040c0d00410003a0325080a041800400524000800c0441c8100a04145c401e40480c2d0910350010000d1000d05900300c079100081907007490f00310101d4074440c902e0b0600e02004c918862104a001c480e1400c20740300a0a008982c1d100034811510018200408001031390741d07001c020013441c09400100130280c442c1c0f0900c8900440c54011601000d0406074414682290340c280c1e54295a040c0c8002c500e000240d0b220f03030300e08503005107242d421421801c41d60907074070016400009404001c42d000e020b04503225150004030701ca24081c0802d1410100900070124450b034009088010400c9051894500340001d085170903041070030481201d8507480c080c081807050101c10302010803540c15001c5107002604031510340ea031149100c000e001504c40300c00500140e540c0d41d000700c0146000d00080d9640c65882169502d100c8509580540c499006e41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 390949838 1250 390948588 390948601
    0x2101081c0807170a060506041d22030c030309050f161a0a0c080708070606090b0405060618010201060f0b04030c090606020d0302030c13090606021e060403180e0c0909 73
    0x5007682c0211910745403103500c84080200501444002070018064545030000003400e0340300c80c0020b000030446001000b86000d0806400340005001603c442820020301120010300c0342e81c04004000e41e54107013003601e03400115141c103801500c105000178047d4001e140140404407008142c5101e0010b04918030b0200c2500c03108034984803440d13106e41411504043c0244410240290204c00d1214065130b0f810f410410699102e0840c0c1c0c7c40b0701c00440341c00d611844200300940540c0500000941308540c1804285001408102c1500846120038078024071454402900c0c0d00031346c03080025050b0081c01c00340b920303155010b141540e80300384411500a2038031440000c40328000d10803182940c07031640c0640300c4070660710002c80181d0001341030008880c0702007000c1407901440400b1000101100880490303900c2c60001d001e810305000814846108c00e505028940c1400013140743e076071142d81424040350301400080301420100d09074100c030201d0850784082c8024040c2040140250010459803100c841e0703580b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 390951088 1250 390949838 390949847
    0x603080415090e04080a2706110a051b040609060909020f0108040c12080f07060605030706031103010e09070b0304080304020a15120b3114010b030c2101081c 69
    0x503c242e00d03c00408501060001760103034010b101c0c92100c2e10380301c400b44c4080c802a18144255510314401c065003450304000d210307005803035910030928140286c03580c1c03140307500c40ca511134004a010003072001c43d140b0100030325591540042e01804001001300030341622842c0c0706000f4044400c0581c89070207284030b40507141d0701c92030700c0311b219650020b580520b213450b1020107420002910700c02c03510240180a518071150032034010b010914043c080101c0c4080c60101811705040264000300c0c02c140c03c2c4545034030340b00d001d40120b0f8115141255018015540c1d0b03000325060141541050181800000a10080c000c0c02c001640c003903030007110041c140030740c3c40c402c1100d07050012100c1c1c0045007207040303810603c8065520804840b403001d006140440700301d105001031102d41d600f4400d84000d21034004404030169125000300c1d0b04007214028a15410042003a001d0302000300744000c84c580024480e03190080c0e0403030401c2052407202c1301d1400ca5840300000c60319844001c0f20001e180800c2d80345242c0a0340304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 390952338 1250 390951088 390951107
    0x170114090316060207151103040b0f070207050d110a0303050d0c05091f0c0b0a020408010605190e090709110702040506011706040c1e110d05090a05220603080415 71
    0x401c203425041c05180c1d030303c110203500000410746005007030724001d00740d5940074064040440740000c01e181d924a0203103089030700d455001c1d02d022503801b4143c00300070744641c0003d000815204222202d0061904a24007855040950b102950300030381c1c964000001c254014014040e00b50888805010b5a00741f5281202e0f2401101d61040e4000d5440049406580c800340b4200018002c514200b0f0b090381003034541055006059a01904040d800207003000303204400e20030280a00812107102e842800080481149803c8501605002607486000f141e0010400c0040c40c0051180000c184244003c0c0380a40c1d0a030f40040380c007039010b641004d00150056201e0b8003101c000081600020a207030703c440f41844020300700070303480c4814410f44500e840f054010500d242c5111450039034400719039110307030b03403545041c441341200c00001d0000078400c01d00990b91f0030100c00300b541c200740c6905010a140403800c808010000007680e007214544003001c001d0051220042c0107035002c040c00341e021580d000e00201d4800d0302 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 390953588 1250 390952338 390952357
    0x140d020d0f0c0809042f180123030c1303060b04050c12360601091401060f0f090302060a0903020108070c08040b0306120706022407021c091701140903 66
    0x104010401d840e1600b64880740802035841c9030000d90440f540303c6c01c1d04101c640c03406185060000300c1d2254a4030220000420119002e180c8044241d80181300079078107031140340c1a881c0c40c0300301000241074450304400f61080304012100242d07d40e40d884c1010401020f00518060240741010005289a1600000c03600b2003c00610581c5031550b0b06401e600075030103030050403908a5421503220a44c2001c2c0441d03185109a0070016040b40d514000074a01207407012917011406403a0b600040000700d410800040c00703500b903814262825004d11a045810080d10f03080250b0089020403100308030341d4488900340070750b4400e0721107445070317214010300f5100580c013118000c2c80403000300424000008164003460300010003910b22464440043c2440d420302c551500050010303408951f100f0301c030304c0c410003403400c0004550701442d109060850b0003d480303c40c02141c014080200700f0744504041e1044000354020242d480354000c16000580085018101c0b030010040c003000b01b040402c2110360044200d4016a0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 390954838 1250 390953588 390953603
    0xb0c0405030a150f020f1306110a060b012313060212040b07050102210a06050118060f02070e071701080c0a120c030203010f09030f0309021c140d020d0f0c 68
    0x10700d95a14605500e00b07425803100426141c0c50041c90030406400502403892409a071941c9892687d4503200c0c0c0c4000c0b5900c20410030080c0c02a03c48640c1010413810043c980150b400f05560440200688801d015420f82c51540c01d481c1032800c9a0100c0c4901901a1001c01c080409038650354580c101c2e80c2e0068143c1100e11b0030f00c00c22040260701c1805c4000c1c02c189200d40d0016052a036076150209810040307640804c102c820481c01c1040b420a50b10650028241c24289004500c0324601088400001c0b40640310501461440b06c0e408075000300b000400a07c480c090b00650380c540900d00a05c681d403031514000302800100004190b1140c0421a411403400141c07080b101ca44c5000c404021b55103008005480713041045c000400581c80c28003400e45400c1038114081901492860010504251503a400702090b141000c0d01e4010307550180800c45181040000301c40f4941181091550403609103440041403007042407d070005900807500f4020110b0b1611801c4a01060340e4040c0d442564001c002003110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 390956088 1250 390954838 390954853
    0x150102060a0c03110403140d050f0702060d0b1504091107050a0b06120706050301030c1d0103150b12010e0f0319080a090f0605010f090c170606090306040309030b0c040503 75
    0x210166001840200440c0f4002c00c40d04941080004281c4c02900103540020341c110020102000801c14030654007140d280a500c0c1500c0c1c081d03482818025401c009202320340001ea01c280d585c009800c900806007001b000304101c0b254801032010b090b07109104440e036450a042c4d1501285020b003060300e08181e00100904005503080e5038038442e00c000101403e501055403220700301c440c0001c105007005030101c4e4a44540e40d50450908810b000c101c1c1e40810400201d1034503680407140180d40c000d04495200e60500002a01c61465401900c1e61118241d0051992508918101340c150803480590721781800741c41030401521a66a240d100d00000d141e66440c40c14070030030b0264407031500e560f0700c0022a20b0018414646658542400501e14402d9888035111720052104c00c0a2414450040160407c100811007907402c001d0014640b94506841801c0e0810014445445032400c885a640004007542d401e407030b0516029181c0f4249000c01e642c46101c84000410660b1588111410781740000d0050060 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 390957338 1250 390956088 390956101
    0x302030307061508100c090f0312030c032403060c0305060d2a09021e13031509080c150f1e270c12060112030507080c0a1a15010206 58
    0x26101041454450f002d610000292020b0240064290002c202c600499040c0090300010100401e94124a0b00e001d0200300c100005040f003000054452100d0030007084804070b42d0801d070020100101d0f00017000c0e404032419400c424900780c0c0e250942c1d224440c00c0203a1204c0403c100d0480d8001c03103441d0781080c8400d45240201c2c10740706c210310303000c10003030310303003041001d030301044590b0686181d0100b561141c000c17403040481c1d240715030038102100003005028140840d62070b9640800d190f80c400580f1146035001c03030142502c0c2c40d400031040303560441c180a90750b54040c07082d80d95620412a0030107609a249000c946080350004180c0d0151134400f030040951862840899076103003018040b400c8074440380d098102034114500300041d044014001400b03401c00340200340007610390015905029a00210010300c0784400b0b0080858141c1d405161540d2a0483ca16100c00c0a10880c4040300041c4144401e500410038514407103090804403e040e00c0e400d0700e84100403070644080c00d40050158200c5c8000400303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 390958588 1250 390957338 390957341
    0x3060905100509040f1a0a0c080417130504020f030f10080303070806040f050106020c01110127080409020d0203011a070b011e03062a050c190326041704030203030706 73
    0x8205000741c5c1c88485421895a900c00014110078000c1a001103c00800040c0700320f0b440b514502e0303815030400261500d01a07441001a0280c14104105002c002c00c0c40c000c1a4203c1003541c010b044081c008550b103500c145403480700f680045138190b5082c0c0303402300060218044001c1150864040000840c210313101c2020903a1480e0000748030f25003242d5507058135042d07641d03d03000e9103008103840d401411521070088001400c00b8210307501001642c0c100f42031000822841d1010104d640d08011660960165501d4040751500c1164468000c40d4000700ba440420380103503004504942c680744404502c11b46000e4182e5403405078a901410341403a001c01004168402655068030003a003180568910b52240d0303c20089480000030300150040720030541c40b07400620104420039403180d0400600f0128120b1203030340c1d00c248500125042117038400b821402c01d4045d189a281d403100030760402c0c04178810481661190107044900b41c60b0304039205a0600001c0c0013030f00b202c007642e4029000d5450410a52140c00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 390959838 1250 390958588 390958591
    0xa02060306010309290711060406090302190c06031a0319080f04090506151608090310020301060e0a05010e10050c0a02150d0b04060b0904150b0f0a03060905100509 72
    0xa040c503840c1c002001c0003440000c180090391054004c20f400380c00e50318172000e00880000f000c500900c89900c569180c4407000040c410b6225a0180c0c001c1a0700c0e0180c50220308042c003000c0c824900c01010301c0b0381410041c44d030907001e06444203940c080180e0580315480031000e0811950454240d08040600d071b80b030342c10314000c80c002c203401130340031034070b0b00d00d140c9400c014940c815489800000d40e10307130500400340740c80000312240c6d8003000c03540c601701582c81400c0300b400d0300c0408005141c100c000450703000c2d50b18180403099149044100454481d070790344901900c040d440548440c45095403030800324103036000f00c102000006002e0034800d444415044103680d035a000c081c190307107184200c21020300160b039041102060520b0a1000c3c030745509158011030300742c4010750f510600c00d1341005824028504118165024108112001314041c6e5203904500d80908440e080180c0070800001c07406d1450703000200811601140e55000c101886c3c0d90410401100c80030b482d25150540b09140400c00d0f450403400c5203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 390961088 1250 390959838 390959851
    0xf03080601090f060203130e0f0f071205071d010206040b061302090402220b04030f030f05070605010305061902030c09013f1406091807030f05011505030f0a020603 72
    0x2620b41540b10b88110512040550051005030310004200b10f074000c40000c02e100805169042940768107080500d018420002000c0395101c060352000102c259120740c8503d0b40380721204500b04158140604028285245d40b0a0306030303540303841122504107510005065204030b800132400f004076100d2008114200b001076a11914554003407010710415600c0c1d100500306c9a010761002900130050289540b1554100e91185000c1300d024402080441c128040001c011941840c01401380c14041000b0341c2c0030b015260020700f45928280003c030802c5000070701036004074403203903d01914800690a00d0240e21044801d41220042070000c020b8650040503102a0712490400700451000f004000355801800004c5100c5098000880d005008465206000c0400c1c0b0240f80010503203000000300350040d8016210000d414901c43c45807081710750a0000764051640110001a50103040c100302d030107000c0003481200050441403001403103246c0045c001d002d80003410081c14000301c440d001c1100075000100316 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 390962338 1250 390961088 390961097
    0x60d0b070c02031605152104140a03020114060d02150d020f0a09141017060619020309090a050103030909090302120309160905010b0405040f0209030a1202010e07030f03080601 77
    0x1c18005030303014070268184100c40c4d82c00415a07450201000004c800942149078074900c00c01c00d40d001080903c007140c42c40b104003a038a1016480700d00d01107400c8419424160000d0095900143c20154190090302c0341c001005027500340d0f0b0320786104100c4e110100351f40080d8840b19680700c8040310b0789480050b042103040c0c204e00508203c1e1809480440e80e00c09180e00340040c04031070050000c501101d4103115900c500f0750701001d2406880c0d00240c1146440566801c002d07100c100014042d85c1c5030011119146482c1c69003200d94004080043e5482d0040705515225a010000140b1003100d20310405048a82590304e0a80d07207403500308490003c014620050b030031406051510340030683d00c00015400340700d01c60028181114210b075014001011030f0440d05040e4200710040014140c8607040e10140c410403100010100721185c942c0c4001c0c801d000d00d15816025003044002841011060f45240900300e4000707219440e0300304041501c0700c10a010003040000e1014070f036804a481110820750066042c1030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 390963588 1250 390962338 390962357
    0x150303090108060d060c080108060f010e0c0309011b0905010815090408030901021201030309051f080a0c0513030b0103020307090207080a0c051615030c0c02100c2f0a080303060d0b07 80
    0x41c1d400c286c6482400800208180900410401108100c0c05601c00c540c881e07112010350400d0542c044d201005420b03460310302804000b1507072440081d40a540c8851821040c00545509518050200720345403052130702081a00002501e0b4119448a4112101000341003030f60039980c554410900d600050540300c45994280000000740324a101031034080d40c042d803121000d881c44d000c00c01060109110411420a510307070b07001e03485550401c80c1ca0360000d900e41c80104010007409412120341c0209068030740c2e5081100380002c2844425000c0506803070003942581c4c2d0b516103403008001a031241c0000240782d05001c00020070110700c10309084108500c520b00b501c45000342e41d505a03c901d00550801c0c414803140d403003403110f17454152045141d40003050520782d070303424000c1d00061021500018450244031250010404120112145440440807600355065004095001030102140d840300035026401800020a540780000b09492140c0341c01803000b460400b0b155100214103e000d4001824800e8082 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 390964838 1250 390963588 390963593
    0x30c120411040c170402060901141c060b07050304030813050d0506070e01020a020303041226040e0c0909040f032322121b0306110304050105150303090108060d 70
    0x450500031805529410780d21400c900c20841260180d000d0031040c85851051180c040d01690780c407662090f01202d4064440c0c90303150050b02c410880c035105107417030f80340041e000340d900c4d4003045030070a03411550204000b120b407110640400c5100392a00507100380e00521041000810081c024802e0140071084910903d58030004554089180c1804a609401400810101c81d61041039050108400d1008040781da009801298a0b0301c070714094100b200d07a180044009106040c60010f100002d05a811240c4607511601150141c020b4003420031083c1d6460041191080120140c1e818a40c0c002e107032465588556881c8075101c0c0b050358048084c803007000c0c2808503244544001d0070720101400350980d6251800080600900c9032a40c00300420007901e00144101c40401c41400c62082e401401103142c1803041b04404140100713035000031300303181c1049007014013a81020007840c01030348113000034803507030f01e60b4901c3c0c0300460760440710b09401d175200b480848441c0d81309036a0305d0b80059000d80860f84a1170030341c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 390966088 1250 390964838 390964867
    0x307031508100f0b060d0e0102070210020a0b010605180103020c1c0c140102040308030627040812060f01021f1e090c1706060927070801200a05030c 65
    0x1e90115070550030000c4940900e280030b02420401c41021541042030220780740000d0003a001d9640c52420495407242c0300224200258100c52445800408108088010400080da2600200001c44000c3c180100004030540640e050700c140c0880c1490481c6003e038907400441c001c0d00031205580c0d00e44148a514000d00b002a0240041041c60356260102d280b82402c1180024410800c2d200c0ea50b0b2040100300701141c004001c0d65000441299a0901c04c4000303503000380f10800c1e8422107440500783c54180f1041040c51801031650303480115594070300d44d450a04000200910318841405a080800d440f481c402d4038020b03410004e000380d00300042a82c0d040c00c148040074800740d17071200e020360307540c05d99800c1c840d80c507401200921a8010388001c0d0681c242c20310b5200e80001e041d0600900c481c4000c00c9488800884e414108100c01105003451201d070015507598108038070842d1501d500e0002c600031100040007481309410f80480b60a03241c150381310400c50361a803004180349480b4070144400b01070902e40303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 390967338 1250 390966088 390966131
    0x5090112030507140f07060804022b05030a081503160905100b030114040501080303010b0412031106040507060306080c01090b0901050c0a060618020c1f180c0e0603030c070b030703 79
    0x14840200044140b948200c0c2c071b0521a50051024014004204801a9030303030090080c1072600103039460300e00521ba00c0c0c240e04500c0c0884006001740000714089030200da00407440b43c850482c05040c00c10014140080c1510741c5408140d03981d544c000040d06211000f8613410880d008681d000c90020483e507201031020701a01f0171b810100403a03c1a1070940b020380340c5030280d5405029520090351a5501d4500e0004103881584101207040800d01c911340f044c140900c02d003038020308804041c0c0e00c0c2881d0a242043d00c881c59805608007092901e0400b0940c0c60300022100303031507c8103841d04030b550340c10080051450f4000e4982d05040110400156446210602008034864803420700170803542c0c10100c1c91110594004004c08000f8030512080404603c005541e88401d0360a04042a01d0b070801c585040190005542c2c0b0110342c02210090313003c0003a145070704000c0703130040540d621454031540c00b0181c0f28429170b201c10f1402da0198000344040780c0740d41c0046030068914200050003404515003070181c50403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 390968588 1250 390967338 390967373
    0x50a06020a05010c0305010f03060e030706021209010e03040b0a0e0d051207060501050108061f03060906080f0f01020f030115020709051918080a0e0d0b10051905090112030507 77
    0x1c55603002008400d0060f81e1801c401d07410140110740c10700110640c080440d03c4007501c2e203505e07604d04840504041c000c0390300460700120159580ca6601d004104413030030a840c400090b42c030b441c414060074900801580c043e500e581a00e1850200520812100c0d41019021264481254005100040c004011052929031840d055580394070403810310a040b00e10591049060210700c008020080d62080c0c035030200310040c44243c054800c0181b204600070031640c7c002003000d515200e40401c1c541400a90700ba00300e94403504580d000b44c0c1c4201210b00781e0240000750049580700744010300031034042e032410021101862044a0140d9501c590080c140e420543c2c1c0f481c0c03108496802010342c0417981c05a54012008200300d5a20711001d44d40e0030745240304080041041001c00c1300c4551580d5203025062802c03c1e0800b00e4940342e410301a0348800081014810284101e0030620542c0c60302e00415030038000c039100141441040ea2038000096110310000308110100601000000300040303040c12582c0301c052 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 390969838 1250 390968588 390968593
    0x914060c07151701080703170c070609180b0904060c050f1305090708040323071506060219050307020904080d05070201050114030a08031906030b0f07091a07030e01020304050a0602 79
    0x620039002411543c000780d40000e03001c10850050049500000301e410440307034000039005e054000d0f00d541c40e107540078400c544440c500490200250b120b9201e08050203592071503110055503a01001e405080359003040402d9004103040c1c00007404900d080c2c0c0252540785050800d5442d0000200058485a100d14260b114100c81d4031001d00443c140307c410305601c041e6504015083d42416240036202c4418400c010701c000d0064805500308603800d405a590782940405414000e44d9100c944401500007801117200510a1640c0c0300350b02c0e045200b0403850940c000700a94a02002602400001d88008009a8220104000f1110714000600c22a8404c0485a0001400b03504080503c0641c217a6100610320950181d410381000c650114212500702030b4030401e141c0622100c80034000a0a866070000d84152018410400782e0243c556880788943d840381e42d401501c80e150102180150400703506061601d00522180c000030340036602c40d160090f01401100e09041c1d0302d40000c5d2a25107150080c00058 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 390971088 1250 390969838 390969869
    0x14150c0d05070507020303071101020f030a091701061811040b0c0c090106030b03030d1802090c040905010602071805040212030309011e0e0c100314010e090f0a030914060c07 76
    0x2080328494960000064078000c0d18000007030b00000da40780501d2030054100313041d400e440c9080368001c10242c494692440203aa0300c40300a43d402602d840014441d40429404400e03009061030010311500068074412004200030b03800100018000b8601d014030b04411000401c804554000c485018101041c010001095918000e8003407200032181a40164281130400140038401d903000300507208422040c581c00584200300610b46a803103120303e40302941140a040c288000d43c03905c10010019a0710100040c0456669032108996a41b414440d0140d410250301d04122040c2c00342d00b12981040c0000c1450118504241400e419a0310907907140c0380b140e54075202c4603035200e00308281c119007440b81c9104001c841c002800082d200c1c040c04a006200700241c0b0040c000040c06a0701c4802d1000030b000b202109581c413000000c2800030241c4841c41284264040c510414800052219600307601d47e6403500010b10b009120046441100350195011900380407000400e1000c000c0c0e400100030040b5030b400765 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 390972338 1250 390971088 390971107
    0x708130b0310032603180c041817120403030b0409060c12111801050702011205070e010909020307320304080a1404060206061c050f070602070f0e0414150c 68
    0x21800704c0d10b0802d0700700401980349000f40ca55401d0300d40c0000b000c0d05244c007180e58500f045042c08026504560320a1901309488403440c07819a04042180c4070707400c0a2072003030015032400010300890b06001c00c5000701100041c00030b0302c2900051207031080540041044095a96164103071414484084009088240040d1081d15940103c0700003001340302404d443c01c61140840c01c40c102001c801381e4140040010010304591091011008000480d002001541442400102801100701c21580090075551001c00ea0031802c0c0308690151607103480c0c50301d2507600d40703000324525240c41c8501001e40c04100e03420300071043c02000843c440c0c1d2040c0307002d5645080101002d02071400e04040784000c2079061206200c15600018150f410480440381906100480810120070003c1c0480040c201d0003400c2c0160041c000c0000c40b0001d4903510340950703060b25158100e00044900d14410310700300f602c2440105001c04e42011101c00c84804030000e44024204100702801945401d4852442032100018441203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 390973588 1250 390972338 390972353
    0x81b07020f060d0e060c0c0a060905160810050105010f0804020d11060d1d07180b0411181f0f050f070b070c031205010b22030b1512010905030708130b031003 69
    0x46c070030a85603409040c07400c1101c40766035814444a00400160b611840e940500c0700130821410b8000e5001c51901071b00b0f44803a24681c4420300f00c0000c5c04698100b0001042c5036002d1440301c401000c0035561503021390740b81c0d001c102d0301440a003010383c5c110076002d5075070300107444a1b0010890304600560101d560788d89008981582c010043c4005400e40021f43c091000304009040728000010010000c074940040f400001c00601408450001400d0b001800803100402c410403910000000c40391000403841e00d00b1070044105c0751201e110002030484100c40d00140c051006048414440310065091202669074000e6141040e1446004210046020b504266002500340c50240c500c00041c8141d524194518686014044220414803d054040c044524211010500540e04102d956045080600130b40c2c030200c910040050064005016070303404102d0501074038014582c810020761811100381c480700c2d03281d00820302c4d400c203007200a00001605207241000e58001c82401440500b00b61651a000c107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 390974838 1250 390973588 390973591
    0x306160801080307080712020c0415151706010c0303090203010e0619060308030105130e15011a0c030301060e030703050708030904060602060721020c0303150a0501081b07020f060d0e06 81
    0x282070b4410044c10700021a400d05940c01c0c15440f0151590080c0c440006a06100f203400c101a04940380034204060920f45207040c40468408042c205082c0349103501c122100d0a0100e0a80081d41c1ca00001c00c489510505a601100780240340014908405070300007400d4400d0400d190300c06600601c20b2001c0c66164110100c241200e0040030019185141d89100c1d2a010501c40c0902c50309c1040840601e07210f8941103003803904802c4055680da81070100b001a60500203028090310580c0395011004181c1f0000700301da85881d1908025401c50b0b180a408840c5480c5140c0000c2c0c06000e10b4100100048042016001410b080c4018640368010703081404101e8040d03600107011544400240100107410000380012024202c804509410602000c02d0291041c85c040300d00b540f0002040150301e1401040784a19560215210600309603142e0045903144426600c81c5c0310450380e003071003840311041c00b8002c20440e8405030003402e01078070040019410341c00081c0340c00c2e28691200e54104c1c1c00b290501105 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 390976088 1250 390974838 390974849
    0xc040905060d0c05041806092004060b070b070c0203120309010b06041d060a0b0a21020306060f0715090506070206010f2702190f021203060114180306160801 69
    0x44995040d49800f800800c1e9482110301403581d0b0040c1820f00f4000d020a4190f941d040035052000011628041c01c070030a4481c1e22984113154285480210302d443e0051001301c1c1c640d00d40f140e04290480d191844203441c0a0a40401d00c00032400c03000040e1000d101176504002681c4020344c0f0382c07500a080f1420340350605811482000c0411052045004400c000342c45c00d000105d00240540d10071010a01002c00703900705d500c8194002c01c8040203940d1047c10000c0008030b0302140d09112024928640580c04203840c00d961018043c0060041080c0e110301400200d801428040081c03048001d040040b0707210b4100582d010f412030000c00401c4c0760101b00007030060003d0b039118401c451400e03020610a0310303002000e40780200f0600041c0c0b00c0f441c0036015680804e4013483ca64045501074403025004024501c1100c1c00b41c0903501c004080300d004c51044c0c902c1200103031500a0041c01c0c2e160b14407481c0d4885c0414202c2c6000192032106c843d20100105441021826402500d03821802c5000d4a4100f0582c0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 390977338 1250 390976088 390976099
    0x3110d120f090605091c050f0717102706020d060e06040b12101a090c0304150203011514070f060506030c06030108280b0907091d12090d0b0c04090506 66
    0x500b086c1d00c43c8550b20706401401360703a901c0d48801d0b41c603249080c0340055030074101500c40d02d1004196040d500120003036103621803040703c2010150701d542c1c00581c1c21070114079103a403040300403400c1d011b03551380d000e0300403903110307601c018505040300d101c000c1102c4058100c8030013074034400100440340c1400c0c400e00d442c00780115000100c0c0d01100d10043d0303035050b03018583c0d040903880300070b0312540c4a8800441d00c030802000b0480c42e524900140f1310603054104480548509001b05a8901364481034400c69040e00c4174440310020007404080192624a00304202c40c0a2207410458071022503012808030b608188110004211800c15408140c509070201e02080c2c4142c00410040020b40310000303454641401409040b500050207040d00a0403030590745001e40b810030f601c0100001d040c40032400000740e030b01002c0c0130042c0c951444003965011f01009084038059000b40f4a2a21445d080e0004e1700100a0050900e03031121141d84d911a02800190307894680c540c80032a040c4450015401540c0c0c7c003075070980e074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 390978588 1250 390977338 390977347
    0x318180b010e101d0411030a140f060904140f01050a110c060604090c15030e100b0603130c08030f09090106021204170709180605010501020f030403110d120f090605 72
    0x192100f140c40c078009060010000c140c0c02d444049800d9403415140c0140104080c0803d4110b002c815401102c02e41d2040d4a420030040342442811240c602601e180780480616035600c800303211100790003030300544810015a001105401c0c003001007003200c807d100004038441c2081300451040c1d074001c40c40040c8416040c80903c030341006c0041d94560115040341d0200b01c411403400c20b1000c0d101c042e0020760b4481d4010001c00786c0e040d090b4000040104100c000ca500e07400b12802c09404484150319070a0b031250040012982102107080c0c1150120b002d406841c1210340d4480c41c20707286502001074403086181c00705d4020107529120880c107004201d24006040f01000c0542c91a45034444c50040280e9500902620b42091404000c41400b40408000401c8801c02ca9240f21040c9010150102ca034141020000318665202058240d905c0c5072541c0210301f05070842c0e88030159803802111440d00103841c94020400729002c641c00e450b40603241e4950a042e40004100102542070940001050040c00c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 390979838 1250 390978588 390978617
    0xe21160b0a08060d0b09070e01050d03050702040c0315080d090e0912070f06060f08010b1008070e030109050d09061b0302072c0903090a080604050709090318180b01 72
    0x508a0700d01d12241d20342108180c0d42d02001501408520300c01401d510f20010070001140d00c0040c5a4050742c10340c2107502d07034903130340d038020414589500400100001d0050146030010305194100d411201550b0a0210f514440703040ca940015005601825495100d03403507400d03826401800031006440e03203d561040c2483d003102420b9460710891602601c91000050210030301c8100c02c07181014541c08542031004030f54030b5004014001c40c60207180302035440c202d0740101910b00031280b1500603555844400859a924800f42d5480c09030a0b03419405540f40c0300788800107003041c00140034600c441d0721001040c90414000030079084410f113a20240d400d04103603010210360009a0070085890f40d403038142140803910380001586030780702c0c500d00d0450504010f1090401d004006014401e00544520b00c03059038456080395168000da401401c1504400c0303090200380c007650070840300103000341881c400100030655080045126644035804580341807280c0485041e82c1e0040758980c0381d003440c000c003070f56030240c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 390981088 1250 390979838 390979859
    0x5131704050f0603011a0307050408060a060609140d02011107050a0b07030215010803071506080a050f010e03040311090603010b030f011a06070201080a0e0111131406030408040603020a0e2116 84
    0x2d0902c8081b190340400028061481740c0704503406414118241c490500b46115104090003640c0501c4020880441d400b051500380350342141c13079903c001000f20031b09000c1a001510f0729026a40e034a0b03c18010080701250700e0315075008450050649011060340c4051505000b41080c20005040d000340301a0b900400181ea0000180ca041c1d50304015001703000c40c051040c6ea001080c2a0380104000e000e4841014107003c00842c2d030003000e661080003030040c2d65070810610389174815804001e210342c1ba440d82c6400c8500b40f1041b01a03000c04054000140e0400314000a454042a021402c1107607444540702c500c01410619900c481c2e600566a0f581400c2440d0700180c1200703401092170036080d617500001104c40101350495846030048140031940c8203902603a450074880c0314010040308420b203058601503130034000d0480388600e8015200c071741403074100030080307010754000c0600004008070b4a00740c07110b82c2d486c4049100140c003000a10086800d207945218100300c00030b4003072180308040c03510801c02e40d1001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 390982338 1250 390981088 390981119
    0xe012409051311010c061b1202041815080a0b10050108040b0a020703030b06040f0303090e010f06140f030c0a1b02100309050307080a09050a08010b060d05131704050f060301 76
    0x1c40f1407030350040c01ca0360040712048904600a492241008000901d800c81c140c00181c080c105540c4003040d05207001c0ca80790a91103248034608080c0e08503c0c000400a24607401400201c3c0100341f0000265a00d0000b00c1c40d0154030142620f82c242c501042c004082c0c002d4065030010542820803d125250a445e6800c030403100510f03455030580c00040441c20948a58001d0010b000001c0050742c580d0b450341c4500f446a182d900003100401e09a10b80411680d82c0c4045080c102ea00d0240415042820b041d81122030b151059400320031903200388036140c03101c54024041c40c400c03448600415191a28410300809a45c681061100c05074150807517400941c44032010800341003071900f800f15041c54640341003455807054500c06800a9008981c0185040e4080b6014040301c1e03080303a1201d003140d182da0407207080700c0c0d04011003544200c040101d4115400150030041d8410781110401c0f400c2c00c2503031079406140005501e4500071020024052001c1d15103000c0040030560140c80131030856042c40d0410941128 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 390983588 1250 390982338 390982343
    0xd11150f0411060d060311040f110405041e0204150305070e0d02040e03120a0902010207061715010c050a03020c04050c040f0323161d0405030307120e0124090513 71
    0x15010880b4460b2129811908041404501002059901e0501403c011021101c00384034a081500700348020050b0b010b81d1150520000101b4a428505410000109154400307c0381c5510340340082d03410220303e03202800003080c0a80e0b234015120203201004044641c010b00c881c05000500745002142d48070b803210000c08550645002411818214102e407941c041d1140c10034000d03280900704080d56100c0d800542210340300b80c00b110180c0741c072000c0654000d81320702d102e00c0c03e1503410000540381da500e16499401070401070424100a103030540300c0070700745002507100741c1c096404060070138164102403041c280d000201c18503090515003800c00464481030948005004080c035142d141091810b110220340b00603120804548030700082807410750303441b0745511800e80d0000001c1f000c1f06412031030071510f500c100c0d4014040c1d40303584e07030305001030399803640c00c0901d02c0101c0d0f61a108032252900c01d100b207130340d1440d8040e045c0011210400400c034020307220390006030406003001d040c01605498400d00510903507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 390984838 1250 390983588 390983603
    0x1314070e030102130914010509011d060a05120a0b06011b08030c0d05040b0703050702060705160c051216120210081b07080403020f0a1505070c080d11150f04 69
    0x14003540000d01900800c0c4610380e0b244040c08000455250a40c0606201915107161001d107a90303c00070881250400d10998050160790940246003d148540e81c980c460b400501d464040703902d410110f4404600b08100992507480203074074005002000111a07403000c3c3c00d10706103244044655106114102100004000746004000729138a07114050543d10001c0c0303100002c000324549400c001081c802e040d240040424900000310f1040c910204845100d90019100e0a2a148403030091120240c4021416a6501410540880d40c1d544810400e481d522083c001080c01d031311801100307030403d501c5611107240d0b181c6007510360380140c4402c2c1c07030306040c4545c50620307802c00d41d155480c0e100e80c10310540d09403000280020300c0700c00300000c22015209803402951110a492016005c2c01203040042c00742c203030220389509100f42e81a01c148000c2140d540314406010026a45000c0e01c0d2404600c0707803004020400c0c40c0068104100c081202051414001555110a08004482d840440000f40000e0b2224 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 390986088 1250 390984838 390984857
    0x10603030e0613080f012012040803060103020c0105070e1206012d03140709050112050604110402090a08060117070e1620061807031e03021509030702131407 69
    0xb905400d10080208840c5068031702c10340c82481914000c207a020119800311041e001f140302100b2000c4103a424142c000300e01c0302c0d000e8696899100031600010100750406408018203240740c1001e010b014054009900e401152040380420400ca2102c41c809650255001c0d40040005141e010b0f03900101400014032003202c60300541001c3c05420050f0000350001192016451030100002859001c4944c1001c2c20002641c03282403000c105440c1d0750010301035510a02c00314011848081c1020484c0d00d0041c001413a0100c0d12000c2944003003150f0001100b5007000c07004100480a83c40b0f042c2c41410140c010704101e9081224458034808007130801c80c0204040c130300405420740141006181c6180344e50611203001c1000c012559100e02c125502e5070f0000b44030075403070181c0f81b001940340c0680b0b1344403201d5004403001c5485a56010400340301601144504034501c80c8180600007294026040340001d503698800c14014000046840030603d00e94500d041c00c40d4045101c0405102d8001d2034514100421 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 390987338 1250 390986088 390986107
    0x507060912091a090f04051f060801060801050105041d1909061d01050403020303040615090e0f0705030106081f1508030a080915040b06010309120903020420030708090a060207140f010603030e06 85
    0x508c03c214022504a080007000c5170309070b040000c50f8100c513801c5e40c40c1c4045a0321040110341600032440394007001c901c1d0070440342c01c00c000078903420340c03150030b40c3c3c090782c42103110407042420ba0342140002c1d29041c1d90b4000044003a01021540070704032030858024450340c1082d55009581e440001e00250030a65a007007100d0070710542c00f451340c0003440d800c5814007490500940d41500d800028000e07011504c0380000002e01828113004080c100c42d07841d8003402401c0303105105900e50344040c12a071000c0507501e0030304600c10090281c568014042850080d612001442006000c2d26001780000030141d0181506100440070300c00659800b950020003803506888800041e4080c00005400601039440e0124000b611503000f01c1c800104da008580070b20099516528403042050501c1001002200c00c10004180354000c001c4540c20041c91001c039008988941c0b40c0354100d070441e47c0216071020605841101c000010080c01c2e268941c1e110003045480d1640d913000c0c2c03041181b00e016a00850000c9004c110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 390988588 1250 390987338 390987361
    0x1e05010e01020f042112031a0607060c0f110d0e010c050604030810170c0114070c0e01030c0b0c07170118050a0c06090608070507060912091a090f0405 66
    0x340d103a80358000c1d500d40d5200500c0020365005400f848000900c25048083c0e985001204150540c0e00300c2c0c26125481203074402240503000b12a5030b1000040700e411b4051550f21406d0090003100d014000001d0742940b901d1000301100c1c0701900030010040c7e1600b00030ba410002040602c000d00d49400c0911b11000064016102c44d415038101a00901600040000345608200c40d01d1040d40301c140210301700c90302c0c7d86600c9100d201da940a90100c1d8050342150700741d0350281c01000c0303c103a100d20072103083c1805a580e58200168680101d00300301c01480c0100100407140300203002501f403104403142080907000c42c0c2d42d0780300203501c42d0690304800082d10041d182000e60003c03c004001c145080090b0400e410029034560032003404890481d01400c1c0050154031550440d0240c5003981e841c43c00300c0d2030b50130741103030b030b9812001046c0c901945d00c203411800180019400081c1440a442c0c1e158118508103107030080d5000700d400c0e84010303a410803001e0740d07551342ca10074210404001c40c0c5c000b4154072005d00004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 390989838 1250 390988588 390988601
    0x30907050a0315230a06080d03020a02070e0619030311010506040b180c090d0503070210050301030c0b0d020f03090c130b030d1404050a0e0f0901090f0222060b0a12091e0501 76
    0x284240503413014040c1440c25900600256481c1c1c504940410700302d440110100d10a48030b25500603000200140000114045250b4100000074190701100c0f04865144182c01a2075008902080f094114481519001e0007880e230f02800c101d400304842d06203000440c1081401c40704040c1200716034000903080611010540703202140103071181031180342c02e00c0c3c496541e9104290036882184840000b10708248a00c0841e03060320750003001d4002c414540220144a43c003d004400b600b26001e2107140e550b0324082001c0c6200b05000300c0140b40c269504814000e44a0f00c01c0c0d01112014104605582191400100480c0303107420391800000030b54410309854800d0080790080307517118005060004108580586d4030713010307000050b500c51090f11000c034018200d600c1c0a40040030f0264804c140c0c0e0252911001d4400302d400100e181c03e00e100c0c98010024121006500410060700c80400c000043c20351100d1081102c0e0f40840c420401d20901d52958003044400402c44000180303816908030400a0030b40014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 390991088 1250 390989838 390989891
    0x3100b0319020a03020706060b03010b1204050c10030504030e3007050a06030605090f04020d200a0608271209060d020d02070210030902090705090a0e010308030907050a0315 76
    0x110b40f54000184014041d40c050310b025600a800d0000100340c0c105480c0403130b8107d82c003401c80c851401d440041e6083c415007004000317840c80e00034009518040d4071007007140800114035070b900142600d01803502510884051100f0303402050100e602c1070000343c0c1c2134448000d401d41002d102d0201008440460f00c3c0144642200c0e0b0407182080e4000744160b0550000015520121040c42003541c0d5503d04070180c2c101241c002e9482000500c14502051b4030000c20031088441c4ca035500c0030141d00e50302050f81030800c1d91210001a0814042000280c1081c68075010034451108005250042c103040c0b56a5400444440c0ba0f4214002102d200960b182c500303c80f034642030b44c0c50954403060704a00c444000d4000e85400c0e801010700b14041101d0b18031921500004e180c1c001c1004280e80c641440c21650341e00056040c81c0c000d86d002002080203c80512031078021441699480e60f00c0c40c080301d4032400c04045600450242c88910000d20000f050800001d00564125800003104082050344c0d109008003031050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 390992338 1250 390991088 390991091
    0x100503070e01031122150f050319090203010510080606030f07031401021e0c1e030304031107171006090c020a170409050c0903070503070f090b060921011103100b0319 73
    0x11401a00300181c0c45d14101c0340519410801c160000b481900e030ba06000c410f100c0002c00810025004080800c010140c0d901000c10020381c00c200c82e40882e084030703000c0d24030f249031891100040040c0c200c00c02809a010505401070300185c0242403000c3c0d510783c4136000052480346070034082c00a0500943c103031f8610b02a41003050700820f00e001a001c1c07103640100c1c40078080e402030041c1600c0d40d40e016820322400c03044c180000c5207990355944084451812035031050140b80580f850010b80101030b0b409005d4481080005807400c4000c5540c800101e44242d480100481e00b008100201e503900442d1002d0380070340017009002c424442001d00900c3d0310541d08214090b0b443c0000b0300c4003404282c03001d88001308054085500141e140c0c410159218410301c141040c0504a030014003a1003940e400a401141000e0146401d241c00103001440141450710b014540f0100302c1c86041036260b09000b00c04200d02038211f103501d1401c240b010103032080d181e4010809280b07400008602c448030703201410300501801807030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 390993588 1250 390992338 390992377
    0x111030703140702031615090605030a050402011808150907030f030c030c17030901050f0925050307140307060f0e1e0a0e01090f2304030c0602030901050105100503070e010311 77
    0x2c0c2a1b40020035000d000703521442c2181d41601c4c40e000302141d40035030746141c460500310b990304c1300c102c409003100078000c23410041181940c04009100504150117009500c000e003c100c1e414032072108011034002c1200103503a2140b102040400d240300d00600c00300c0d0301403820031259003072400c0c00c3c0c90650340c2d0000200b140300145c0c281d000c100c1000e00698001c11550703000348815220345c5000041c5c0101a0b41100003500728a6981503003841c0000c40c000e05003070040800c2c243d25034920001e410701c48242d02c20703488140d414050031510b283c2484010301400080c02c2a0510303c9200300d004000d41001c03048140031341050b10103542148001101c03410b010380010701074a042c1d40c030380c10714401f68503081c441c54000d20f0504904040b9035126000e003e0071055000c2d4000c0d80c000d000158800d592a01030001d9080c090a8089400410481e000030352040700b20703000108083d490701080c4921100c9020403482001014000d100d401d80e4004603201141400b40f8020070f6460380e50050101b1482901d41c0c401c07881c00d0703a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 390994838 1250 390993588 390993613
    0x9080f03040503031e060102061501031e0c030b0d03120915020a030c1b050c090c090a03111f27090c03050901051b0307050a030603200906011103070314070203 70
    0x10045125481e000341d034040c0004040c190b2124181c0903520305000d40c09c41000541e030703003218044007082d00c2d505241c00b0070603084419600c03048807815010074081684601c4840c6c0300c1500b6001c0ca00c541c01c419101f648070880b80e40c03001000813044001904085440e052039100b80300c40c6401c000061094868110360340c6180c00c40c00340c001c1c400781403940c0204003001d44604580b2509111a0050741e006406440c0d5400c23981c040100303540c0010080340d400d040a0040c0381050b1101c1990b0400707103224810302030b8000e0600040019403803081540f041c1e0f801c005822154119440b640c400080d560041142d1101d20001c2d80e000040111754102e0070105190000041c000390f41900318074041c4011078020045030329051f050715800e00707034000c2034400e1040800220341543d120f50f000740041c10051500107005c42d00c4e9074030083c03c0810350180206101c3c0310340c0d02c0d1101d403800c850380c907801590909018142c107002d0256542c030f83c020380c0c0e0046d060000300b07628480090406821540d00c0c1da8002c080d41c00400609 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 390996088 1250 390994838 390994843
    0x20a021314010f06020c04150905070908120331051207150e03070b13080a0906110606010915180306050702150f040210020a0f0b01170109021309080f030405 69
    0x204001241d240071000024142e0210511941552260350103482200544414080503010320f030307680311140c840c1900004000c542c41c0314040c020136690b0380c0d4005840c60600c00da45018484828044104070030402c0c44003010000341c0f400400800c070307950350095655401c011034100d0081c0c600505680140100b1b03c528011901c001e001561243d0500d0401c40040800d00c0121080c04141070281d40c010060440850190541e40c1d62061138001a110030308025600d184175504a0072802000c2105000184030f482d400003070560720401c0440c002d120a142c0300c00000e04200c128458154412015401d080b6030314412030741090702c10030b0b01040d500b03902d54a240c910010f0204494603401030113444158403c840401c2d14660182204040c481c005071203035000c002c40a203080a5600c1988221282e41d8005150100d40e10505030040b1b494051a61600e00207034000708441004001c0d0783d00d01851a0011781e1688800e1501d11070400d0005584042803070b04030500d10904050005c4000080104020007400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 390997338 1250 390996088 390996101
    0x60e01030e070e0601111504020108040c120f060f1401061202040f1403010e0a1109190f0b0405060109080303220219180207153803060709060f050a020a0213 69
    0x70381e200800165540800c64a030a087d04501c105001c040000c40c01541c131542244ea0418010305c501c04086603200c0001c81001c180700b03011215051082508010b01c411882003c140748d071035401c00d01903c04500786038400d10005000d41d0083c40b40d00c141405d205801035050390080c00080100302c8446032608e4650354001100a1960300c2503082400030440102c0c04254250511b03070103581c4919a861110801c407080c80010b0810070340b00010712103a40c074000c40e401115012404c0c000d00082010320715044c40250364000b0080c0d410300400b040c0400040500000302d0394041281e07030020002c0b2960070941f60750400004c401a5005403500701900c0400ea208040c8000c0b01c01410000202c0314241c03014505030f0055006c0544000c004500880c110751454020400f110212807401c18054006100e140070f40c0c41c07240c02881c814452030000c1100b800c0802c80d8507080ba4150500d500c1151405070300a01451482d01c191b410400080b03034030304800340200600e03ca640e03402444d2998420070000a10300803e030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 390998588 1250 390997338 390997351
    0xf011808071e08031c09020117010e0402100203041203030504110306190b04200d092009010e040b010302150c07270c080105060711120120090a060e01030e070e 70
    0xb8030300d0740000c2c48032000040315982c00002e010340031501d0031414680d00a10007020f05a060010080c0340003c40c4401e41910342c007030404c5025004060409006219904400e041c4080c01c0d54010007040c481041155100d40d02c20350b25242c0400c0076916840c0040c0e54041e14080b6a03050320039403040c090034400070142d01084000040c81081034540c808100030542c2c42c44500400d03c0465000c040e0b480d4296500200b188815080021074000b030036a803a02d00160100800e4411407a40c821503a5140c9040c01c2001d004000d0601b00d0861801c182c0c0f910305100c4010b200080c8212812000c00c80780080f400103452820309910b081e10b01d1075a40b1000b03c986403c0828a06880810700701c03d26518041d035118401030707031095079220052030b07081c41c00b8001e040d4800401614855110420844c580e600c0794403844a0319946030000c2080c103100c0300d00400322f06001020a003e400144002d451030380307440746c40c0011500c403807416907200c2d25408010f80080102c205101007074010440045048602c54030740e03d00450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 390999838 1250 390998588 390998639
    0x30803090c10020705060a080403111006050a0608062107090c0503042a090c050405030a150c110d081b030a150512060a050402011b050a110f0f01180807 67
    0x5114020407070f04c0d5021801640c4c0d200c8000d00c800c441b414481c003801a8018801e050031152400c0c80f01c082803404c3c0001e02080d0a181d100c034401d11040c1454480c50008010a00b05503032a801e042e00011004030140111107800c1c0120408449100010020032004115a200803c0381811305000101300b82d104450a4514600300c090714808080321410407020341a490002c401d000303080c00da094014101c014510020000140000305c2c803070307a0600040034904c0c45080b41d03c0c0c0b4590700c00b1000081d01c1c404150142400b02074011b2090070768010440c100a006245030100a070b640d40c00060512811456040b05541004000c1240c0145240c2c4900448450b2201020701295984100043c05030107885011180c1c00c04404544100299081183c000b803050404c48070720303440c1c038a0700301c1c44422010082c0c403a0ba01401c07440c07051120900c00040800000d441b00c100301d94040d404a9201014018068104910039150701040c41032035906001130844642555451540c0c1c0f50462220311160301410700c0035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 391001088 1250 390999838 390999859
    0x110708030703141503060f0603010e03040605040305060603070b0a080712020403060e060c0a0e0d02151309050c0414010806010c0206031302040b06070c03080f0c01150305010e12030a0213030803090c 87
    0x602c000038040907a04d00003030041086644035202c60001000240105401d5900c8030340100000300c092010380003900030741e650380d034440d032441c14002e1920501030140d50281d00407800034064201e40100301c4035440d04a00305010907440f1488102e038141c0320003410701105071020401000b00a041e40090300d00694050441e072180e11030281c41442c6208200c2410003250003018455034906001042140f0f85000900d072852007003086020103050b070702001001c03501c0850040b09028541c070320321545800a80b0421120305280c24214100c6841c10700120300c82c14001c8100000349640c2c803d03016a0f44040d03020b0300759034407410204c214421050302a001284641d0820882007280e00303040003034030b186e0ba801141c08400c00340f031611480e030035620401c3c046040040030007040c880701809010f0baa83e19500091080c1202c4d140d4140fa6007120b03d001c030000f20b42c1d00501c5140000c15500c0040da1781124120000583e540f2088030038406011141e40002c0421a01204004500b000800c0c02c6a01180690364401d41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 391002338 1250 391001088 391001101
    0x9031902040e01110301150c0803040605160f020d05030603101a1005031e06030307050a0507060e03010510060818012c062208091f120e0601030611070803070314 71
    0x341d80641135101d48440081c00100b000c0c0c82010340c07811041045040c13013a940a03e5480300b0501d03602c2110140c03002ea8540f030610aa1044100043d60044058034103540080d4920000a484400000030401040380200c0880e1840d0303000d20643d05a0030a04008010895910240307040300f070300140da154810403031072007170982a0307000350101c070302c10614500342d01c00c200714215521007021405440320707426210522490001503401c03c003007012180500002c100b4645480c0340140011040d032303c0ca42c0030380d06050600800740141100c2c00d066a105040c5a845651104c0b005614000c582e80d050780d444d82031001c06a031000444179100740c1203444207003401d51307140c3c8142035582d82e01007907070084200c0a0048481c900700e00d80c0c1e00c40441080c4145070382490030101e0400074240100d8030100d003110300d11074010071b05020342156005402c0c4022003014403c00c41074900e030b141c030703a203052002515075a2151002007400322803c04580c0b8a540c042106d070745034144a60000c0082415005030110312036490040f031034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 391003588 1250 391002338 391002341
    0x6030c0506090a0b07050703170301080c010c03020c09090f1002180a03170a030f02120f07020f0703261201060207090902060901031a0603160e3309031902040e01 71
    0x900c0000940800106480e121407813040c2e5201c82c0d81511540030300b490100010b01e441c00309040401040b43c4554403941081030050400c0140703910f9a06004001c080c90002035004500303400360301d200322404200d40c2d075220189030800120b40480710b0701d4001d6451540004445501410890b03400070030228105400e41d0901000d100c0a00028082041c680074009018105400508c045e41d0319180216a1102410070401640c020403a4443e00382849003c2201d144407010240f079000c140727840148488200155050380b202903500018151955541c2d51071a00750648001c8110f02c80030f86003003039544040b00c01d80608032000303000d07901c014054072000140d4055a40104100300d90010426850700070300c4030041d4024106480414449007601e050300c1501c3c5c0d01c01000c0d512480250382d01c0c0ba0f1140e48071800621180c003101c2418400c0500e080c0c002e0031509144410b292407006d610b119414214100c415001500519405607454030800c1140e92418444800102c1c4441c800d860a01001207940ad4850 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 391004838 1250 391003588 391003597
    0xa0501020303040b0a150306050f071706130905160314012307030b040f2004030b01030f080c0703081201210809010905030a060b0a08030c060f060a05030604030306030c0506 76
    0x90040c0d2041c00030601003400c4c81d2680760411000d030740000303039400d005d02441e0740042d0550041d607460395210f0401482102c118461a070080311890042030615a64640ca80304d800c0280c003050190f44c12103441410141141c1c001141140c00c10308a8000040046168030340d45828001243e01c544101100d4a110b0814050381810b054040d089411820205081d42d41c0001e00900c99020107071501d10010007a1038511031070001220300040070034405000070b2606024800c0118a1680c02d000300020004030300034006e4541920307808545070035030000c0390510b820140181500c2da299806080c100104020718440100000602c1901103840ca03070b45e440251080001c180d0145000090400b040d1002829140040094810506189140c1520303071020034900062030300c00701c41080e174a02041895161000c100f00c0184501c000035480e0018500b1195220320020b031211440202a40110390315656200c2840064a0094100c80413880d09090040107850b8511098680a400d00c0000c00e06051010459 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 391006088 1250 391004838 391004849
    0x1508071703030106081e16080105010f0e040218130911010813030c061d01200304020d03080402040b040e0309011707050f180d05070303030e0a0b0c1815180a 69
    0x71401e582c41d01c2c9059a40d02801400311a55004001c02c20740302200803214503004580e084680084030501390409081c010040c0c010b01d0500002c401d00400041d88a02800b50140c01607030003607115002d49142c595010344840c1d03841c0d440300700901c08010f2140b15a0190316100d000b0803501d244034500c90019a004901614130514080340f00400300302103030094000c0b80941d84030742800a070000c45401414900180900800c840707035190014041d582545516038440e90342d004211300d1460500e94001945800d0408004050050740030000d8107650f2540d100a010181c058003d204d1503040c08080b0703840758044000d50f030108031644c3c2240c007041206861648078441d6030b19003d150441c1c0b00d44048003a00140030740e40641181d0901041c0c681c0b500e010b80303050284540000d0000c2d6007149409016130301c01c08501e4003070350300031035126020034203108140ea0403400c0c0191a0303070340340a2010301c42003488610781c3e011b411400c056007005400b03400320000d082611161002c006904003074000c000311100148101e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 391007194 1106 391006088 391006093
    0x4030e06042d0e130804090903050d05090606090a0908041a0310141e030f15011d0f071b1e03090618090509010204050415080717 57
    0x441260a4140308414240b07800d080f0b02c0700425100500325400c0d420010b100005210f0340d2402c1340c0c05400d800d20207109440c074608002e84a540030000d41c50140d4500300001d400302e000400d0260243c24018104141521440d641d4000780c001c0d940192148041000002020b0503502055800c3c1c0024060090f16440c20701c801050303090003507101042e121288130010505698640755100c8026101102c610f4035034010010a150410042206501d0b1150420b410301c1543c0d00150a0304a5400516420f0900c00c0c03440503200543c425540c1d049000394a00219105500501c141d2413000c06141c921109541180c9a030001200c080d01f03c02105801c0040550906512001c10b4001c0d100a0030f01e024048030b07003001e51061071900d114007130085658a0102d00d01e440290100d8008200040c014008010301200c1d001c00d415180c41104030b43c0c0b00d000c3c80003621080040848043c21440c030301 = true := by decide +kernel

theorem cover : BRFrame.Cov 390827338 391007194 := by
  have h0 := BRFrame.cov_init 390827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 390827338 ≤ n) (h2 : n < 391007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
