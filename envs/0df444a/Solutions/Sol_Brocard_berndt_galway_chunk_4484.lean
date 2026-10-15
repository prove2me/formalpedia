-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4484
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:25.26299+00:00
-- url     : https://prove2.me/submissions/52f2c5fe-fe1c-4767-bb03-97c4cff6fa9c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 806294964 ≤ n < 806474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 806296214 1250 806294964 806294977
    0x50a120b18280209210a031b06061811070f110607140606030105072102031035011a0f0f090702030c0601060806130b03011d0102190302 60
    0x5001c09244401544424028035004024500c00310080340090540d840c0b5070400d40714001c10481c09601c0e06100303420701c16007000c241c134103100c5c00156014110f0161000300e080000342d0b0700751400c00c900728070031341038840e200c5840c080c000c080c6480d1150004c0e5003030000030004d4000010701c800344a00401003600d401c80d8080d41e40003401901d9850441d00015503402000c1c140d04502600140c14a031a0352500f05640000104008103174110b041003107146e1400b88a02940400700c1e007001e503c000303c403940c42080d00280445400f010303a400004185c40024420f08900180398000f042064850324034000303d869603060308031480030440c081d0a20000030042c010130f842a001000d00c41d00fa40340c104108402611510302d81500011039070a40c65403030b2640d09610b403145034550000c554a920b00d1007850310b0550140d1100c01089104828404c040c1d4814080501da07000120000c00d00310441d40000e40181031032098141c07440061007207500c0d040410340103070203200c20003208141207820200c81601170b0310885 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 806297464 1250 806296214 806296219
    0x60201051f060f0c020f040f06030b090708060a020d06030c03111905010c15020f0a080115050306010c0201030b0415060909140903070b04050102120c030a23240a0303050a120b 77
    0x19403d00d00602d126484142949000501d8114903000c0300001c07404031400c84586011064485e030703040c0244004510040d420400c0c00008000140c0f07040b1103039840342e4001e040c00d92031035000035450300116250b401c040051074100ca4101012071f035030310780f1410800700d03070394640c1c0110500900c0846501000740820201d0300c0603121400310000694481005210388072040c903245a0a202003511040d0700f0019241030307202074503010314139410880f034480d05007480e0f4192810000200100b1056984c0710210190300c0e5820b003001304110f00c40c036000030302801074845080b03041c50010100240c141d43c4002c2120480b03103e42d004000c54400b08c074a40120b00d0f0103d070071074041c0e80200121030006107680c60322584140100001410300c030510240b0301420302d044e51034091190001c0300b4400c00365054820170f16400c405000100c0000300088e40340340c000000400442c6041070450b0070340141010b950111030600c80017010403401644902d0080e001e82c01a09440c00003031801d200045254086210300c90300702100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 806298714 1250 806297464 806297477
    0x1005120f16050702060408030a021e0a030c0b040f0203010c02060601030b030604170703122c060609011e08010203040503180a060804060b0a1d041515030822060201051f06 75
    0x41d041d01e40781d10030701c41240c12140030000029030328030500150100c807032203038098032581040c50300d140341c80c3c01c05030f440310015080103030fa0200194000c00d0403a1402e600031152289036550b814180c021192602c0060741650900d420041c0d650350206000d072183e84262000c1020702c02417030a15646840c00c031401022001c8068005030500c001300094910148286460408a04c41903514001c2e50902c176036400100c40390082c100710792091118400f003d000c000f0010141b524005001549002c01803090304007501162200607080040540060f01402d48a0001c0d9a64105464a107949a000d0010004540c40100030349600340703003590540e821180c8a07a03c0a03a42d450300c0c0c0318070b8000c10100d601c450b4048014030000030400ea036400c2186072160f03159801d0006140a06081c6031800d2482506041c8920300605000c1048407030f0b4003201a20b030041841b42c0c0b00e10700c200d1540080000c0c11124038203021a40b600280c46a030540003988201040f42d0950b2450345682c80d00e0b41c611403580a103a011803503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 806299964 1250 806298714 806298751
    0x5060103290d02030a0f0507050a0b0f070f020a050301060605030105100903030215060316081f060b0703030b03030d091b05010521060d0c08010204061e05070b0a0b1005120f 76
    0x2422080b00c00c140b0300040541720992000d0755005000c24004100311032030f80011a040005180501070781008060502e002d07481c122104001d10001d00c50014002c1040d81100604010754559403282d601074107001e030003000555100c12000e8601e41007480303482e201c1c410b03400b00201c040d8440c04070241101d0781a002040540141442001014cc2c02000c064061140b41030003030b10500200c06a00c010b06554010b0107031018403201810405000340c10340da424506120342046072035012811079024a03007601c2c001581c0706000c0c00103400c4d8440c2d0a607180166041600700d20a12418100b643c151031510f007954484699600c0c0195000d000701c0d180010110980a49031920400809115500040040c52510b041842e542c40800d040c07519046003060b82e5010030180803503a00003072000000c1440f8070021030045040e8074010300a00c907024005115440400215151240e590400107070100000c000c0594200c1c811030003802030f0810f40303070b8451282003080030070036010f140c0f029107000c0c018100328412003e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 806301214 1250 806299964 806299969
    0xb04051908031e0d1e050f07050d0e070503030309070807080a0b0406050901091b0501020d05040b0a030c0219050c0a090e060a05070e301b09100503030c010506010329 73
    0x505002c00d90003404020000498001c146102d540156007120031598031105c580659203040741c20040500c0a4401004148040640c0101c16901417920340d010108044000000712418007109038482c41e0903110110500400500101d100c8090340c503900100da508030354400c0c489513295080710b0040c02104044000c680499107541100740d110b1600e0001145400c21903581c0c3c3c1c2c40f5485400ca064029444e004180311079031381489180c6030f201c02ca00e42942007904000c0903a0044c460303051842c0c02c1c103603610101d10f20b240c0240304022166142003100c1507511014101543c0f035078000a882849080e06c46c1c80807500d1209031190b0b8201c0710030b220081c02070395501c10440005100141c110b10034000590180d81190b80c030042903003032645000c02c40201c001d040e0b900304075850320b0300410305203640c105c42030654242021211440808900f100c29822680300c1071940f00d858810360700b0154050100207100e00305e1000540089006940c20398082045105100c1900c0e00e41702c24ee104201c0840310b61654a2451 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 806302464 1250 806301214 806301247
    0xb07021513140d0801150c0312020703110307060203010e1602341202030f010b091303170f060f01030e0c240714061003030f081e010b0405190803 64
    0x5840b840312011401503585109140c07881603d03802d400134150500500c400310742e46511642615050928083c3c2150a59024020a8100910340300b480d40c0800c110b8141485050600401100b0380180ca03520120b81c107006020794401d00405d400101c070a000f0030310101041014100103129a8040c0c6030706510660304004468105e44404480440c1e84408106042011903400007803007a07881804004036240305160508ca10209c00a82607454086400d050742c852802d9954412101048150710f40107505c4d0035600000014000031204004404000b039040d0300010050050104881004080040100440c103030351205d1803406d0344c3d810030191410103007010ba43c000744014504400c003240003001e0310480700305c0e04000000e40e1201440392410744441c1e001d228294000340501d851003e01421a1030140001003900d50481c200000f03040090010011b03010781c41860160900e08022559480e0300c440c4e0702d03030400e0003424802c840b0002c0c141800c0d130070700744d07814101c0d0501c202031800c09000b42c2504216 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 806303714 1250 806302464 806302501
    0x21606050c0106080303010602010204030b0c040f03021c0f060902030c0a05010909020c0319020307032a140c09090d122903100906090303050129090118080a0b070215 73
    0x1543d00d07a071000c28062410710146001c0c004c0e41d030005031286d2035400c00c8254444041e08440c0c03600803c05c018803004440c502490f0650303030103070784a00c180c0b000c26010401d85680c0d07100c0505041c402d40d0151082003100d0700100002c500031811036401d20031b00f104200301d81241d40b01d924040fa10310502041080c2c141e4028200740205603082d2800d241803070510807071f00c229808141c0d00507000099004109500700142040606c110003101f03840a43d4626401c403012144403001c4c10040a004640d0104c00302001207040442c4054840422820442d04450340d404c40d8103225004a5400d0003240c48be040c09102d41801103642c1406a1070f000e810b00c00705241c021036191040d4050084c200400c441021038018410310300c2c40703000c002400d0a401c0c20010210350040e0401c3d0b500c00076404202c4140035007003a4030303c020045178900c1da94a81d0f0b40001650580018841031740a50005103002800381c00226031040d6160017649482d59540c0c4050b0126240c03040e07000102c5403180064040b412810402051440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 806304964 1250 806303714 806303737
    0xd080f16080f15030a0506010e09061504090804180609180b0a0504050a0803040c05040f1107020127090204080c12060f0408040e150f040509030904020d0b09131202160605 75
    0x24000500000c40c5c100808010241d030541d00031001000518032518440f40e008060310040d0146040031140e0003a136210f00724402c0e10030f90301c5254810902c504901210001e0944c041000d0b00c03681f0302c0d8601406410f05104407075166140840041c039600c6c00c1c1c01840c0065034030100e4403043e59a080401c0004ac4000303807080d2868414040c0381c4c40091f030040c0055001d240196035043d04640342c2820407042d94041c81c44103582a081c01c2c6a0300b195403c1d181a02c840c2a0309080007520241d4580d8107440030000001440d034050480c0c4000215081540d00070300990301403c1c02d48030420f40340c005200690031030021100150b441500050b12010f0200802c41e000303442134003040d140035070701c181100300600700341c1d4500361452691207851218605206d038100c0c2c0c044140c4041c08545030845c211601ca00800d08014011900051024181c080c81d5100500a00000341005498180324848070b50342ca10b50981100e040d850440c3c054030060001454903060715250280e143c0340c5003040c40403503040d001a00d5050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 806306214 1250 806304964 806304991
    0x101503060e150c0408061006122f12010515030402010c060b0406060e120a0b06012001090303150b04050303030613150b0901091406040504020703110d080f16080f 71
    0x202d400020741030040c05403a007056030769111401d11500c0c030b007071840c09085804107540c0304000b085416041420800344083c003110001d2407001040401c1c203981c5040c001b09003202040e0b007065010500d5035016180b5070807a54503848044c0e88a50034011741000d4039060901b203e805100240040d80300b1401c25441034498035010910346104d901080c1600d00b43d40190340072400c2091103401030306103802c10115041925000303003110f1106884440100380c000c0d0105040195000801001d001112035544030145910000c0203520003034200140100605110a11950700d2200005041d542c914252820b5400c000c2c0690302d103440e404104442d060f841c40791001c2c0c0a49170000e89448000b8803000d1070040501e61200781d0345032010000140688615005038409089540c0d1580c61522030304251000d8800564006035207640c903080070348511070200b94038101403044034450b211180c1c3c00303070460f80604031900c2e0300ca441d62520303841601ca9207401c0c40b2030800a12100002202e42003d20003280d000a04107030b004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 806307464 1250 806306214 806306233
    0x121e19110a090603210305070f0e030304080304090609050907080c0d1104020a0809121e070f05120c07060305090a020904080408150f06040506030712051905010e101503060e 76
    0x880965510758026107812001031720580400f0803440c19071007210001e1038204014506040e000c7c05803076805186c442000300204024029403010002c0b9005001013a0440b0b407501c4c0e4804026015000c5401682100380c00d00001c00c10442000460b54140ca640c080030b0420403941c5d00038485406104202958441c0545002031003a85441c8010002451595034082c0c43c1d06e00540303034500d003e00034140080381440c100000c11680301c0307426100c120b091610100b03075552955818084501d0a1031a00a811806151200c014000c600f000800c0240800350a5800c1039076289016821608200e40700000764000724100d10040c035084411561140c0325003007050a01303456050552510a0f41c5c0d941004050842d014083d180c000391803003540c40541210240980c1c500039021036143c4041d40304404528aa0300c01240c10403505000703c0e01610440700c0101e0604046050090280a402038010000e0142c807056959000c0c050068041e03a00000010141c010700e5031740c407040180f5081540c09058050926403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 806308714 1250 806307464 806307479
    0x290702030f161e060c05030c1206040b0a0e0103140114060d050f030c0a0c140a1a0702100503060103140f0c0c01020f040f0317041a0304030c02121e19110a 68
    0x611a400080381e50340203e040d500e4420100d480d403040e07550500c24144100308030b2304803007011103007841d1105500003129151038000ca8080c00510403542c0e4440328440000c41c46290b01c80d200c0b4102ca000e480203041d089200c0e4030035406c031814822a011501c5016001502a0821b4280d5100191007074003101c0f441e55070160001c0c11600f0038a00c201194000d014090b046c001c0c0b030907001c0301510072013148030074024040c000185a81402d10554001c90b4001e1148409100c1510944030859009010303400b80c5c6581050080403588104c038010f01003882c004824010030240e0440c2881060010515501d984400741b0204050f0000c00c0d07810100d40d001c0100c20f0141d402c400145c03009110034124640d5a509618108580031075a50800540d000d0500c01049021111203c9007000c1061b0301d82c01e9501d07160f43c03e08584166400e50084c5d00b01ca00300e07640a100f6040040e00d01e0400b1100200e002c41e01c840c0050040d200c2c02c01e40c203034514140c00e911203200450100a54241e0b00c00008101510150780c40d600e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 806309964 1250 806308714 806308733
    0x3040311150903030601091a0301030201030c170901020418090f030e130f200307020303010e10030b0f1807060e10030b090103050309030105060d03120b01030e0a290702030f16 77
    0x82e0b0036103981012042c400741c0e5802400e66030182110030706246101c4415001031809000511019041607103401c128030703640c2c1c0104141110850864111502031410f480c590380070754071501ca603400032500c0c24000c481107052031003045611940002c21071540081c9032001c80b442000b42c6000c03a84101c1d44201666003068912842c500038204902c00f0032002d88580c08013203100190b40a420b038045081080066913075000c402c0724195001160052102e403594800881c0b000324a810003003060030403105208140b24441c090502c14410621014603100941c03074150745030341643c482c000208440807050125491301100301810917410b4500040c00c10100c43c00036036101801c1e48103659540000456680605084c00b84c42e07400dc03802e964184820441d590020440000803988030086565032145903daa886071f0481c0609501c010300b00d400241ca00d04140c16240d100881c10b00c2940c0980040b07000c9158010320070b44c4a0210f5402840c24403403150300d5500750340e21100f495120388800002c1c1c1c60001e840d81a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 806311214 1250 806309964 806309971
    0x2b031b030206091c0512091207031d030d120b13050f010303030c050a0c02040f1104260c090c070302012a0e0102010e10150302090a090b0a02030c0304031115 69
    0x60003050b45041ca2240541400c0d0b01562060841c1d10b65801450743d1a0070200b20f5400c88024054001e040c0c2d07071803003450b081400d411212049840c0019007581410340c09000c50060302e40102d08078246120303010816503101f0f0150002008121948090740c0c411030385034840f6080a10140c2200500c10b15101c64008840080301d004e503803114200010b0040c590306102d041020381043c18236500e4001d103507001400750394503800002d00ca00d490f00c007224ae1901480e004041107980b8581c80b1034a69441e082942d81c5d00c4402984110140c4110040015190001501022807000580035402c651100f01d40400e10741e00500c0b06606640d2104015003464109402d819010480c207240b030803a0003c00c0d5001407078240b801e40000e04681c18417a020740c05001c0840c443c81c030009084800240010401c034120301c4584240c1c0040d501c5440e07481044401111500500701d2070380b1400a11001d80c1e20920400224001640c001080e80b40600003d400a801405032038182100c002c1100d180001400180000329402c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 806312464 1250 806311214 806311217
    0xd02030307030f0f03020903070b0307022d0d0507021311070c080102070c15141804180c050901060e0d0602091012050601140f220909050c2b031b03 65
    0x201c10f032164194040130340c0144107000d1800b94036003480e5100203a030b50701580c080c90a00c400000085082305000304056210303024104c0c0d0441c1c049003c0c40480c2540764010501444a004070007403101c2951007141201c0081d68000d0811074284111201400200303a0380248804c40300003009080041b0300c44100c80310040282d0f03800503030b8a04003803900c4044c850740360303200c401d01540d950351060741c2c2c41d0000c41c12a51002e007080003c7d298001c11003103c45055180e07280355042498541030900302d40c0d01c03c0007642d90901640031445041e030f5070300030300c440c000007446001c0028020f00c00c00c010a2030161030045407140116400b41c2004810700001b04d45010501428012410b64140c0791140c500502580303501c00d4003400c1035250380c905d0003e42107091040d07a0001c1c01c000700028807020003d000f014655118180b4030b264190594644c40391320001e001c441c2090b1442d00c604807080c0098039040f24140507004031601861070396100c0c500f0300d0a94a0f9444011020310081035040183c14440c060444c214601070b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 806313714 1250 806312464 806312477
    0x2030c0a0c060e04090b150a170c040501080d0c0312060b0417061005011205040204180308090c0901060903020d050129090a0b012c040903030b0f0a05090a09020d0203030703 76
    0x14654054180f40c28000b03414051420281c0c084003042c3c3c802c1c281a8015014a00b0502280c9200c0c0015050003c0ea04050750250003024520a0790350000f42d00c0300685801d0700d0401250340caa10400d50303030303034441c21521000a960080e0f42e00028400c4101070782c01c0c900c02c0d5005c110380d61202e4200140750456040420401414505880340060420016420010300e03d00703a0f0280d410039000901c404010580c9a03405a00d032000b1408646442d4081d220110303003445502d503550f5044c40d004006401c155290300c0d0707512440c04290918603189221b10704071012515032502e01071440d420701007425014181070300c2c07556070348110040c0c0d800d4000d044000390121154030304030185007104011030fa50b4060003000d01140340c0048031641c3d9030440341c141c1c210b403407403048080c1a100003030030312090000d4001071a82283c105003a1800301a0950060507003238008450545580500c503052050000a6214582d480300d2884003040f0980071660159940d64001741c10f007508a00aa00480c1c80c50340040e0044001992 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 806314964 1250 806313714 806313719
    0x40905070e10090807060e0a050d030c03080109110a11010e0703080405010f020327060c0d03020301050108070206040f12020c03011103041703040b0a0506061b06010e01050406030503160302030c0a0c 87
    0x400c0c00c04028011a10700f000782c1c2c51401e0075801ca41d260014050001400a110080b80180d942c80d0030f040000c05000f40300003031001c003525004208036401e141c11404104110000b00381c3c00307040c3c00340c00100302d0f03510181410814450720490f0301c200c0c581517a003525580e0300d103040380c444824404e82c40a10700a00b501946c0362302d0617000500b0303c2d2030100c00d81e0840d0401c2c80a0400c200e0044021640007602e91080200c200501002504074468410020b0301c52107400345d050b031901d8040e000b0f181294002d88512680d5502c6680c00e9849100450b8020300c400e0007844060f00043c1c801da182845002203104941030140560003007802c40c0c00711301c861003002c200403080208004062441048190b0710785400c03411820a952030b980c0050000c0c1c85c41d0781c01071303e0320f0008840342c54280503119110f041e10080300040c540d84040a496820a028442e0100e034441e001003820f061a018000c1242e600000862410540f11400d40000f42a608118110f00080004400001081103681006800303566a5800240b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 806316214 1250 806314964 806314969
    0xf06270308090304140d06270606060906020c1003270c05030307080f07050327040b060a0207091d0f0f0d0e09040f0204111b012403021005040905070e 66
    0x6002461510b4a0b44204800d0000510380a0f0b9200e0041046c0c52261140c003c502d40301010306a82d41c01d00c14055000503903508141c14805144040c940150401c0101585441085401d1103190207007601680c4400c10018690403c1302e2507050005c071510780021003400c0310441528550200c2c03040c03004414011504010f001941c00140c000b080110300441c9000390783e40d694141402121500d09180c1c5000c120a0140071080c811180e880081101c02400c1404020fa6180f55000340c802d41d034040d07031522840b80c0301030a01c2c0d021a03c9140c1141c0041c0001443c0c5140c4201800342c260001c201848120244031100d08104000061f10039840090b01541c0d42c451402ea2412601410f030000f08041307034040341c000c2e41b2818406a0860b411410504000d400c0740003040c09072803201c801d1040e03c240084c1d014008050243c1e11500e2102d103c000381700ba4108441c45107491400f0561505160800400c10401440d080700024100103540c1005030919555084910484200722a42408a0640c01350380d4900c0c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 806317464 1250 806316214 806316227
    0x1020a09080109031b140703060c020f010b130902040605180708090304031a090a0f03020105090c0d0209060103090f050706020c1305070e101704080405010809070308070f062703 78
    0x4101d41002000360803001c0d1402001912041030320880060340c0050102032203076114003200980d2804080302c60342d960b00d1401100403c00c014000307006010b41650040d130000107003c0c400d005074000b402c6000c050a05080f0600800340d2a0f02240e0041d5603800000d85916881103443c41b846d00049000c8643c50311003409050300d9001006040e03950800c02040c4000391101020380780300300182d101c0d00700503030342c1080381842e24bc0f80380e070007610fa8030103089a4000c15a0542000d81b25040300380c2552a04030804061207a06c0300e0720200203500600703900002c0d0040d44264002d484040c0500b0301c40708800c82c1c036100d40707081c0704807a0403040040c0c100c15071124417410a01e42074441c41208a00400c114a440c1000802070004108400d20594200b0221800544a005e01c04d080405c4481d5520503400c1074580491242c1c090300c83c041c04540030344001400305a0100c1d00c40100d82c6c0000c001441d00f0120384d00c100c4003034581c04046a903690788005ca1503070364240343c0324140000340340030b1026203110040c107010703061 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 806318714 1250 806317464 806317469
    0x18090203010b0607050a0b180f070303090b09031002031b0d0b100806030a0201080c13060302120c131a1b060411091014030f010e0d03060515040320030f01020a09 71
    0x500c0080105200080c000036041214a03080704000740d41d6142c81150300200e540c000048c0742c051103040070900308200007088103001c40b8400e480e5440341c0c5a880121404a0066a8101c4d0303064101440d92131090722590000d560160749411024490454921031110301e400c00c10030000c9460369452002401c0c01c0c0000c0381d00050b0503a080103582031a0200009581c0c055010000381001204004107051511140954180030040c12200c055541c417248014001e4001120000710703041d02c0c034082400c0120240071100040f54007103c5c60700048c2040e02c0248025404100840c0c44801004081c850111070019421103002c1c0c00c018225500302030504500128200c10514070a4a0002c00e0007800c03000c007030361682142c0c40c03800f0b02c0407209001070009080050500000000354200b2111418403e004038543c0f0400b000c41e00c04003c07058440040c0150072003003074500c61605100300400e00c0400c1c039607040003070030002418106040203503d5002c80c1c02d04480c104101c0d01603402040c0765400c0c54000c01101c02 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 806319964 1250 806318714 806318719
    0x105010609030b1305010b09091506060307050f031803070c1e1401140702030307050d08070309240207051005100e2205150c03010f0603140105130618090203010b 71
    0x20207a0030740d118048104409058005842e000760b800d082007140039000103088081c010144c1425180c05c60000751034880006c0f81c088181070b40b00028030f446c0b4140302500d0162145507101c0c1d0800048120b4034040e9440503080c220f1551340b00924502d6040200020300025201e042c210341c43e203181c101c0c000170001d01c1010b03620540c1c070301030010701c000009584030003082c030024030344140c2103246108845101d12480001a4045c00300103000301c10312100140042c0c021071182d8460f507482c0c1d07505000320300300c642d9a40020042141284000f603000c80e141e00c0601d408c4116040146044400e03992149040d901c51144000d150308c4404200b04e001c030031403020000b0408103500701d240e868a4111340341c9800315403a55401c480c1804005a044c04410000840031a121900d00341c0c0758101417185003ca80c00c2445142030548042d94040307034a900c2805100c0fa0081514810001070b420001007001c0d0030500c048550585c0d658541c0010800c424480d449840700303040780b00050100740c0f03005060030b446804850a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 806321214 1250 806319964 806319977
    0xb13140c100f1209050a0209010e0c030103021504080f010615050a0903060906020702130209090703020c0c150d0f0603291306110a030f1a0a170c2101050106 69
    0x8691250300d4595552201d5141041c01c09202c9402580c00040e910003042101d03203812a01010000c00007183c0c40b00c07600803241c03125a030381e0720030310141518400c4843c1c151403003043c0010001414114859200001000c3e8910708041d204e07000b40382f8002d1002c0b440c1403d691549010403101d0341d0071082d0142d04802d4980a4501000400c02402c0d180c0140300040c141030781e810501d801d101c1036506490a80340e000381a02c4406000c3c20f200b0300032b504900041032152031b1220101b080da030302034401c0381c0114041e131018100150200007080100071311500c418545d1042001a494141028403c05403195a29080000c000d419030800740c030240e68084088440900300d03102d411568405c2000f886d484050340c038154900c42014503080029000300c2504e1150039001041c17807021650560407071006074188401c1040701106803c12848044205104107400c000d50700c03014004442020a502c41c070f0380c112821503480c01000e80204456004610b40d0410442076000210103e034403c0c01018010f1040d4079002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 806322464 1250 806321214 806321233
    0x6310b1c0b0a260102070503121909121b050d0f0809030a05120c09060a080f06181501020f33090c060a120c050c0706111005060d0b1314 60
    0x100d42a003207040c0300f040382000e885980c0c2e0590003501100c122075401411340e602c50900c0450500c40c21825240942c1010001540f001c200300107110700c0b15584d4100b80e2000e08039901440540303000e0124a0031070313401507100c2c60000100c0c000304008101a102e95039403120180c03003214020a1144084c044040540003049141351071755115054510484050030303100c01d25105c0f844101d11601c9030404031030300040007103080c030051034205035014070a100e17100c23035541c00c1d1341d8290030058001c501000c40320160b200100030072280082d10405803505034060045510808800c01c01310300e480c144092688035000411070408008440301c058841c0c010b440590008035086c100c91a50704ca91542d800180a2100400c01103100c5101e5641601c4229511104215050b659030008190351720280c1521035038802c40c034001410510030b0300c0c0b46194130908409800c120070485c940300090907028168a901c400c0320f110b10300110b509604864040d11170b05110341071100051915000725041a00d0700d00030f5401030000b2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 806323714 1250 806322464 806322479
    0x7050a060809030301170a0c06052a120d0605040603050f0c030303070c151407020d030e0f06060d0f0b07050d0b010e030d1206080102210606310b1c0b0a 67
    0x503207040d01c103116034030b401b5481c404c42120314050100401901000e064400010b100b0f412200501010745610301981c2e403951225201e0707036800c0b0440c004002d07540c05041404100714841001d095202000c49010481c6039580c00060152185034105489a400a01e05407221500c00c00864080707001c21f0f0017443c1075250060000e004410b0400b80507103070b212488682604031074140c2c0103a00c2801c5e1103150301d409080c003030b000070741ea887e000c1d04000c0440d15103203110b10205000952a0704141c0210700401060703580c0d00a002180d60f54503c100c90001c00000d01c00006030094902c00c0c41000c180d920261244200c2e500380b0207644500081e141030009041850f5070586012448ca105003603d801e212050307003094209000200550362022940d94400b08501c01501891002d6040e03003000d803281c12070f003601c40e41d0800209200361415282075240f41100b041c1c0c001008203442064260100c8140c07401691000018456800000b001542070003203084400180c0c2c0c10300c2101c1340d40409403010b000141c106105c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 806324964 1250 806323714 806323717
    0x31201060e0a0306240306050717010b0d0b0411161704120308040201200304032001080631052d07032a02010c021005061f0c0c030507050a06080903 65
    0x58031550700ca2404001c81101c0d04030345c8000701818094105183d9590408400401040d01c054000880014100860842000443c0d05880b6000c070001d180c406c81c610950001c2400c1241c20b90000c6d21802e1011090312060f02500c442640d180b0396140c4142c80d40ba10b650032510302c2d035a04102c68000c2c0024070158000284035004544c0c075040208198480340011b0b05c140380c0c0c0c1d1440e80341c0440f549481102409021001d0710840e445415009117900703a01002202004916890034000b842e484001481031400a0412000a0009070406043e400358000d0b003200c1d03010094290076558032141801041c03083c451210700700b105015404000e0f08040c861005a00002070304400815895003215030104501c2e000003a07464085041560116814800c040c2c0030b0000400000c000d40107031042c2075120102c44c0241407144900500207079021030440300e040b004546400d4000204103215080400207449100701001541c043c10062058a19013030402c81091442d0f04480100108074041c468907900010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 806326214 1250 806324964 806324969
    0x30f0112030c06090317010b04060e060720010908060c03010609170c151c1d120f07082208010606020102120a05090102072102060c0415030e010608070305031201060e0a 74
    0x18012030302c04010300301150705d806d64002c08564084c445000158001042d0001c5c0308840b12502d0f11100c82003400108401401101e001034044414840404c0318094040450302c01035605051580e440c641394040946410400c561880c80340500100500415070032151031001412401c031005562a0780c4401c0a49030340081c02d00034010780380700c1a5070107400d07080020b850030103c1c500c4130041001500b51030400030b0401e0420400d01c41481d03680c10300a40c02c01184e50114070044500310f51078a402860040410741c00f400c0309a941110520003460098509610041800c03010703040c010526050112035401c41e0b099500840548e841080141001070880d8241e82c3e2003102048001895900c800e001406031080f44002011a0840c0035010b04442e007414410580344681d0b8200c80782a40c40070442e40540c45140101203004108124000e4424400d421076109085580000b14199a489403001c1c5043c02da900304880d190000304e001c40c6081c0c0051184c50041003507103000c2d5428590103010801030303205030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 806327464 1250 806326214 806326223
    0x150106120b0f0d052409150603030d090b0a0501080c030d0509152709060f0603060d080c1f0c090e04051603121e121d0a08030f0112030c 60
    0x420201c40d155030340940800c0352940242030340904030342130720b055a100d82c042c0300c94981c0040b100401810344825a03400503c2041c1c1040280140c00001548110f0000b0080c2882da0602c8104040d16040000d401071030800c0e0f01c10043c00e1141c1c10451661019944141c01040b0541c0c0140004a126580018034001c180d1580c01d00c02d82da000c484000c1000b000c20311b0302c07810040d140001d241c0f0100b10301c003400310001850285068008403040b010410050826100c80c1c2d800800c0b40e04042c100c7c03030008002c2d80c00400081c824204403003c0d0381c4111003500300e11096045e9421031100c440c01c251001d200c42c0c22580514030100a001d02c20f401c003502c58032082c0500d415540328140000d04008007005100b0310208070400701c52555035a072038003242c4030701401008000145e08a02c0f000210541520000401704a9100d50489110304c40c5890f008000c05007201403a0003154a4142282d20140040c0b1007090040e02050356902c0c00180040c020103040e0300c10034841140003180c0340800d40c010700e5412031a030322 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 806328714 1250 806327464 806327471
    0xf030705010c0c0905010b040302120c09010911070f11132c031b1006051e0405131b0503061b070605060f130603051e0a1203091202060915010612 64
    0x9400c02140604407500450084c45ca8080049214014503004d8030489208842c9001c040c54103016070381c1c1b50001e91008a8028819000512501941c2d07002582c49041c9404050306003400b5072680786800505e58010b44548211101e40b4143d4203000b211a250202d14010070320005a41482e03409408041d50400c840d4030340c0040c048030079580d0a204030703102ca210a80c41842040e680c4455030780c9401e03458a29520041c54184001020f090081b1090168564001d81e8101e00501000788806410001e1800100c01404220000003540718072000c20420048100300354110304020525181c65030280c402002c101126020085070240c9000311100b1503440007001c981520b6100c08181c011407142401e41d030000c3c031f9044140004409a00100031a4041c50032a00e055000303480901c00e010281c0003413030050f0040c0c4000c201141c0000c0003100d811009180015249504d40c1b07c0701c2e140210070240300016000746040c01005041000900040b00d4038551102c1554540035001d03200d40c03581030140c103040c2d45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 806329964 1250 806328714 806328737
    0x90903140a05090d0809090f010608040311010e190c050402030f040f0317073903030504020a09050103080417030a05040e060a05130f1802060f0d0609090b01050306060f03070501 78
    0x1140b01520042c0f000540801100506480d08003441d1304150151030152031a10000750940d88078901e294100c45a50325400361907141ca840c1116440080044940ca0313640b90220708111203400c00c10f00c01c00d00a42015840741c035000349002c0041c403c0723a40c041031042d80140240702c2d040c0d545110352901b09510184414400c1c446281c00d44e41c04285446201908802c4000c00c03014540160440174803206400c80c5d00422846400d2400c0c22100b0340700b60802c404150003c060010707000b6030110341c06c02d00090404812541c0c42440400f990300c240c008803034940f404281040700c102c00011510400c20214040c5050510043c8024620b0085d4440c11074450200008507011784c5844e069000500300c00f0304069680b644507180040544507120a00c440d680c6000f4580300105c040d540f0586020b0790051a480c50842d01d90b002641c036810001004903400da481a00186505c0c0b5442044001c81c8035812030740c400d61500f0201414030340c0c000d091901a641c0848105502e50f00850070200360343e000d0800024000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 806331214 1250 806329964 806329967
    0x9011e023a050112031b080d02130504020304030203191b110d0f080a022b050c12041503061d0c0a0507080c0105090d02030414040203040f1a0103020406090903140a 72
    0x4041c01e2541c22481c1c60040003080b80b8a00e071100642c014000e844a50785122554440640300c1c081000113440f1880500111002048a800414180303d202c0b0904031000d03200c40000b001c80c0e000b500d00f240540d1002459500b401c88890740e601c00c1208034103040100d049500240c40d100f0b01d072904002d207610021005001035995940e140003082d034204103034406081c40c510301800507a1040d83c111016114010001081c0c0c2412515035891440d4a288054109907050041d54242c1120401c1c00c5540a140c141c0c455401341d15001c0c00003807102c11846246041d00c50000303401c50b11507030840c1c1c1100ea552b0300f0704040b0306901000590404502d60907030365207001d01101100c1500031803030010032441000841d10400c000c15041103002d01c01000c1950706941c0041416643c9100710320a9600c04203850403480c1261400c1c0e409142c0c00b03805aa0a0b0100707855a9498052203551409440008440ca02c0103109600300352007048080c001d10b0201700100080c0391000f4068800c1e1179020440480001405030005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 806332464 1250 806331214 806331307
    0x5250806070e0d060f0203070804060b0604050d0f0311030c030d112a100221090a020d0311030706020a030c030b0109080c0f0d020306100e0f060f2709011e02 69
    0x4417540b0000c54490401c408020846041504d06584240c00d0480c03403002441e00703030115403c17030300c006289541050103591510034507861120142c0622401c00420514000e0900041c03060200ba00041d5690780c501a012008072075441d030f1140b10a41080c0700c8030030303040d90704a840300d181202c8609041c01c40c1101c001e0329103440c01c2c3d0001c140e5014001b00e019044120008001413050300c50050445560b5914102c50365102c2c4ca181c0040e52003034400c02400046801400c4444086001c50107480c60034503070742c642e401030707920003041180080e0b601e140250240da41403240d1000c40e00c091030b00a807000d14003600a60343d000d008420074070501810200d0703c910b075115801c01040590280585070540341001500480c0743c0c0b03038440c0b04c40380a01d02e00051070710070208000c24400c8070000c014000842c807403001e0080c02092501ca810315580c02109180750301c900900c0303007403180010300004914441e4450203c2d141c4041400c1e9070008500600100848174100072840c032064090400c504120380d0380a0306040d06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 806333714 1250 806332464 806332481
    0xf12150b07061d07030303050a05070e060a0903061505010f020604020a170c13020304120306050307170109140610060305010b0322141b0306091203060303040305250806070e0d06 78
    0x1030f114007181500d48008900c441c100c1e40203450400c4155142c4c12010241c5034219000b40010381c0d051410300c81c81c581140a040d84030554644a0103031a01c0e5076882d0111b8140c1c8410368030100d101d200030081581d114000e4003a6040a102411042c1056408610301025900071807031540c1c224684011189001c001084280e1310040c0181401c1408806c200c0096106607070564501803110503540c4003034000c0c06101c0413540050f0041c01d6403071801d44080c1201039140350542495484c0d100b1000840c0400030003802d0318000c45e01401250804810003144260564008c000f4582041c0c010040c80e20114150ba5100e031003c030718003022100803041ca000c50305100c10002c16113001092061a010400a42e410206003412840b400d1441c0903810150340e010202c500302c074940e0150035070b010301ca6982000b55822000c0270f010cc0c2d04094480c0d41d002e04018140310741c201440c090322180380801c0700300784400c0000c2080c031000d020700b0b040ca090001d268211f031a984c1d50080c440d801c103030342c100203070781c0d000c05807 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 806334964 1250 806333714 806333741
    0xc230c040e2b09050a06050901050a12090506010807091802100c050f0309030d090b0d0b0a0503070b030604050a0204030f11031c0c150506011d06040807060f12150b0706 74
    0xa042042d00da2080075040c02e0019440000c00e40740d000709007800c0c440f42c5d02055481c02d84425090003a080700456090380700109031030402042c8221071a00d83c54134001c1039101c920a8025114543c14a00703c149000c01d15401010a1800c10040c2c1a005804078405a800e07074050300d14084401440307106880040034020010698801c401031040b9104002c0042d26000d00100c1c01c4e65002c0700c0c098000c40c1d17404194008e4200b80c1c2c6082201003069030306a40010340c2440c000c4c041d2951203503128006414400c0c40d5009541599001040140c68500b51141550019645130110304190441c0c98031420703400b66001c0248440c841c0c005283c0c9030354007001541e4400c030a10607550440c02e41c0c0c03200105221801402103a9140411aa20407a28900c1c02050b10901040e9960300d44c201c040110038540e4048484c00f260000e0080001003500c0c0d01c141310b020040c188076111146400782244004103050703a0021080050351414000c0b01e600c07140001050100e81c0f030114601c1d00d07403842e030401c200248818850f814 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 806336214 1250 806334964 806335003
    0x5070302032406010c120e0d02100504030308180319030225030f0c030806150d090c0e0a02131703090406030c15110309060f12070c230c040e 62
    0x9036400000c840d5040b4038228280e04251611614015104c49040300801400505080e2400307014600c01e0f400c06901c02d5004000c1752a00314180c020550100e414400f2000240000030309105040e00014482c0d0841c10b812404c10880e0b01e032804a9450380150122a042c140400052800040c801e40641d450250014815080c01d182c3c1c180104051448460880124248210308000d2134001c0c24640d14094158075505441d03680c84041000e215500c10502030006003e1145001c0b10240c1d00c2850002c40c0700d003900c040d6042c180514400520303030080081c07407011300400c4800c0d4200907076100c2e08201d404500074100031940e184210303410b50250803d07a5803c6460240e00106015000e040c0908966003d030b41304000c6130f0242e20488407100810401203640c3d004000c017030351500700b9800410f000a5100c0c0d880d8240111800ba4000b4042e0669280300021017400903041401403180091410603ea402d03c1200c810307401584646801e004a05603100c1c550f17442c51654881d100740003031005001e043e40c210 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 806337464 1250 806336214 806336233
    0xd110403060f05160201051005090702030708040f050405100305030a0c1e05060402010f0912080a110d03020c280f022115010509010305060103060f0f090f0212060c12040507030203 79
    0x3034003d0200301c5554400c200340094030303d0914010700c05d0b070b8014040028450041401d0900740001806c000e044101107210802c42000803c8000015001a00851841e03112a40c50030080009131640a08114402c411044d4200001a00001111242e804034242222842100d08043c11400000c03a011401400b000c014441041004500345103e10310036200c4011407004440111a000698042c28071600250070244010038140350161018118338a081c50031503456074501e1f400d102a00c1022000310b070b0041405c0c40b044100348142009080090100c80c1c8610082c000c20040c0525404003500034800b50214100303544485845545c01e4880a404541034014100100d5591000e6412011105c01410004c40d0a01d00309000318100c1c2e0708000207144903402d507110b0800074802c1480c0814800d9032160110704801542c012800414001c5d840106100c82034014000d03184591402500690414400c120b2401e01250942e400a01141c080050603a59072800c6460300c0d820350000380d4103100e8501403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 806338714 1250 806337464 806337491
    0x60e0604020411090307060302091f090e0106020a15024014031e0a0203011e150f0b161a09070f05030a0f020102160806101a0d11040306 60
    0x914029403090b1000c005003c0301d5090780055008000304075600d41c108050820105200790013510210f40010107060520400039801c2d00e800284101c928007065a1080410800b41071642d16801020107001612010025030745440e813025000420300c003a1617001c00c00d00450b0544030f4219554100c141010141002c541076035070030000c03410100f45850404903801007064101060f074056110710281c014050030038580107a40340003a200c0b071a542c5920034030030501c4c0540e03070034060760b00f15010004c0341104503440004c0240903903440d4541440c4114410504000d0207010b07010f01c804440c014181c0035100c02d0303001c90222400300507207806840d8a003001290107010101c40c1c0f445006580460403030309042d0b070303446180030b841c0640c0c442e090741500014080d0020854030b41820703414500c144181c50b270312a030101c12051482c0c02c0e03804c200100d40c0410104022221a850403101410380c45801108680c90311700d09a83c148605241c2400464036501c06036081c514003001d4a0245620a07014058144080c80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 806339964 1250 806338714 806338723
    0xd0f0503130f14100b030708010b03060f06150412031214010e0a020705011505030d020d050901081513240810020a0509030a06020a09530a060b1815030a060e 69
    0x800e522030300418000140c1044140302b400460580a0082c003500e503a403506000711030f8001054940c1184644002640c2c11250300c006101030310b07a80342150f100310b039607003001055075406103041508149040300d44ca100580703105c03000781100e0010b09000714543d900c040c0072019024202d0000c000350b007000e0300d5045003091450320303c0079210160100d81d091280031030102e91350b298444403e0003044040090f060070394032440c00680e2044113074224080d0700900c0e102140c061a0f600c004031088642d0381200c4d528414004041d5a068441c1c000d681c40e000341011119611500f01d41c4450003581c1d4005048409940a80240c0c1c0e1580700c000d0030340c0c8503a03015003400d201a5004101070f00c0001e01c82d00010464850301034001d5041d0722010004c00d0402c3c0f414146104d0049008110040c8092000d032000080c2a0207040c03030701d480c9000300a0080f40f000c5240c4801500c00004001d840341580e070010300c1c4d058400100196210851410115017010b06c2c001090619122400c0501800d061501c10090b5000004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 806341214 1250 806339964 806339981
    0x515181902070624030804120318030f0c090203060105040501180906030f03021203011a1815041410021c03090b132f2407050d0f0503130f1410 63
    0x204d266811008050340d05900303405000080003004284018070840002c80c40040700d042c0300c0d061803000d111108110445041c0355a00071a6480d80c48000704e41009880d1312400018101204298214100400041d00f540190300400c0d0400080300c09590402c001080c104004081c00c100c100549520307404d000d0303c4140100d1080d0058172408605c1e080301c2c210300044a0481d03d400c906050f20f0414000040c42ca44d100c00021061030f4003101510840e0751340d11541d00d40c0b0462011465a480f4030301000d42d00e45000e40c0f0210f0348901c0c045084140d2107a00030900c00403254161200100a003884030b0103400030004d1241c0544030308102e07000c011140007040c00034040c450156030404d80a405228070b0510200c00c0b800d0b03030424041d108034800718034204600650003400070402c500361a000c03490b126028680003000306540c1d561004200c20801d07508581c3c6003410045c203242182c0b9525102c5c0086103142080b0f00020b00001820240d0014406034210b00d10181000b01c00f80d622040c2404c01060103403001c0b0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 806342464 1250 806341214 806341241
    0x180112020a1a31031101110d201504020628050a0305060d05070e0c251b0e060d030905060c0c0a05120718020405030d030501080105151819020706 64
    0x10310f803800c42c980030824910039200c10b080c1040e01d007540d40c0c0c141c410840300002411320080782440c86880f0000c0c4510611000c041c1c0d00c0040c600d155070403c42003113403072550900c4150041c6444800c9044820410750703100d6015141240d8030302824407035410948045021682c11002c074014803407400c1d440070040c034485045070f90a200545404003008840b9000ca4402425035000150030000710034a1480349a110064010003400c00105030000442d40d4155400fa4105040030410303041009059660310403008228484d000150382000816094004041d04a80c418041c081c002ca040502c1051032601515018025989410040c1e00190b40ca80e101082c9070311030380d01c0d8003000c02d0504000340c018002103c4400142109440c10b10341b415811102d095900041d0340810001c90b00e83ca0400401185c0400740d030380080c03290714180900e800c548024042c80c42d1480c4500207090b1b031750340d801960007424400804a1405485181d10b03c00200c1800c000103015500100380c0d04107006a90b030103000c4042c0755 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 806343714 1250 806342464 806342497
    0x40b030403020a060605090c0307080403020f07060c02100302030601051b1218030d0327020f030304060f03060b0301031a153c0a0608090c09040606080c180112020a1a 73
    0x95401f0060300d11411101200d005e003081c000503a0f014419001503821a000c0d005a5480d4184114240e0601100c3d030401d8002c22044040f820840c184950540d038162110f1404508500344040001c05c203204891030746507a845003100c2015000c3c1c052100000440d500c800340e40d50382c400351010000ba076280d080901e109005146101d20158007900039508090030740c108401140031040c011603070010340d1720700583e0000300c092894607aa403010802800900712039200d41114200c0c84070010280c9140c0e400210610200303000400014001441010544000440c40202c0360703205041107201107910341c0c0c1d45178017881001d1400004036440c0a1043e6008002840440744007400078100700286500c00071503080180b1010400215102d000403c1d0804460001d8411880b54640020170415058405807440c41d03486500b00301d105410444495101400d8400d1340c2407907031030110f104104005110718190324a51164002c115030310f00380500060320000001c400d960b203171185101000d8200c003064154420b80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 806344964 1250 806343714 806343719
    0xc150f020f0a120c060b030706110706020a051f15090c03060f05130c020f060c03060906010e180901090c090906110301083307030e19031d06040b030403020a0606 71
    0x700482d05030b40d4076411207024680002d800303c084850100c100001d45007903a881307401407180d541c04c0c80a40000c180030341d20a1003407085800d0407809c1107029406101950300507000d4200044020440d8840300301e440c4d26400e18080c20042d01c1c0c001c0d001d00100036113050341500e80402d42c131003144d00c01d001c0e10744595000c001c5151603400401c00030440d130052903481031080c070000524100981000020326032a1040e00d821148241031a4a0170b501a43c4031a080b540100421219042c202001070b4070110034a001e03a925201b510115103521801e042c0d07282c1c4500c2000008000c0310b001d4120300c00c125403000c81c0f0f04995030341d0031608009100e841300c22201c40c4d04000400110b56028026a810398120401502d00c80c030f0500684403c03100342d41040d01501214444440042c49001d900343e03c01e2126413008a4042d01d1020028105543c0b072134032030f1035000c501680501203079103d820503c100348002c100c1c0c44078401c2d800001c1c28a000701e9001541100c40002004101a80840c00301c0c4c5591046500b44000d94 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 806346214 1250 806344964 806344993
    0xf06010626040602130305100608060a061d1f080303010306050901020405060442030507030c0e011412071e090302060703030504020103110f04030b150a05010c0c150f02 74
    0xe4034410107000008107001081c04a1026801408080c0303144845015143c2d8136600e087c2005102d9404942c0b80e0740d601c0c010007550b8001e006803540204038810400039182001c0c1c158201c8510070015180b02d60994000401000c09000c0d400c0048036a1034944c8442c580d1001d01c0340d03a0f0b40c404d00044809074105004580c0c016414000d40d000c0d140000d02060605040c9515030400e010702503548003000600d0301d4056030b0a100d040102907a0b1484405c50312901c41c0c50310002d01540d101034031600805180c1144407405c983c0c070002d654074004007468031108035034150b00140518090a040b4a428100083c14840c030345802402c8007500640e40c01019541410f681c02c20b40e825025440080d40102c4100502000039120344d03c10f0307500510505000941000403858681180c0154800640294000806100b030103400e165035603209820f60781c030030649114200856a0345000e44503150520103814840810410304080340f8018000e07100318000900c0d03265000801d4029103203040030140c050200a4085d40c0d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 806347464 1250 806346214 806346257
    0x406030c330207030209071205100602010e07211401020a170c04050102070608090a14010507030f1107020907020f06100f050d1112150129120105100507050f060106 72
    0x1c5682d8024220b103903e15020b00c513280d1001000d5000b002402c1600d200000524030902d806004000c0340d0305001c07410144041c0c03c59010000600c241e80c0501d008000009105103540c2e80c1a10400007103244401a142c0042c802c002c05140551075400407070b11102c0039500050710405001100b10304426611581040381d02c0b0310a500070a030068004110512103030b030040c019030380c01c060024101c84041145031241740700da040c260b40b00109a5100c84c24480329070b40c0340c042e60055440303c60003081006071315580305482c2d1040134002030042c44c4020014a40314006e00c480010002c00b2000c1c0d031114a40b0094a80030a105800303400c00f02d185414010605040c80d5200c3d0412550003001080351030540320820410903001e200808051207402d41034568810f00c0c0038814000c3c0f8066503400528000ea0105003903883c4000c07882046c01c0028420400034560050300701d41180d9050b076803aa0401c5810350129001d10480780060060b10809000e800007850006c0c00354121071180d50340000401480702e240f2401c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 806348714 1250 806347464 806347559
    0xd1406010c030f0c110d0c180c0207170c06030a020a140f0d0504170703031b020a0206041206060e0c0d0b1e010e0d14102004140406030c 60
    0x1c00d100c80200c2940d0242d0313013059601d80100708081103e0030040018070700d02c021701030072541b07a41c0d1400200028840003140c1c04d440e9010340b2080c071501e01148402591281e031b41c428401c0c2040450404400104144446036081a0140c038855882c40d2100a5002030748c058a84040010228810307501082020f105035140c0540c40701c003c61410000030380501c054900a8801e440015007046154400007121f0020603403240b1075140855410171081041081d00b02e188802ca066401c004030003001642c1e02c0c0200c400381c0d41405810200891141806401000e1a8110450800e200c00500001c0100b6a01802e016188007038180801d01c0c0b038600303006142e07034020b00c50400b071001640d01900759030040008100995014199008500750744d04c6000320005a10403e098581003142d054402501c14058046490015800440c6100c540901d41074580b20310700c602e40c0300c1d8601c5141d005180d651074220340011908482a4044182c03650034540c0c0c0c000d100e200142c0c008500303021400107088020f180604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 806349964 1250 806348714 806348717
    0x5010c02010c060e120c07030605010b0a09061d0a030c0806061e04020a0e0406030b07020d0f0906031a0a08030406110a0b07050a02210a090e19020a02010b0301020d1406010c03 77
    0x5516602c2d6440101400649004640501641e1a0701284070303500c9014000c900e184070001c10006207181800380840d101a000044403500420146004d1500a04007000300d03941c0e4540882e2182034121140a51902034107103560110030308200005021181c207120303094030b048101307582032525044200100c1c20001c1d4482c00e40c11080c00303220740f068038055014161048850921130301c1e00e018000018105ca505030401ca0f0b092070182c0c14058501d904200048400e100ca0400202c9200401d101404082c10f92052000305626806554000811003260401a000150105842c180c540d0102074503a00a40034640018004080f0000070304400540031160503004400074103641c48050049860742e10000c407544c01c2d480f40c05d8040640e03603000d88042142c0a9654942038a40c00ba403600109031840f11761000480e41c25140a1102150480650f00c000d1040d0300c5005990b06c0340400c0a030b0141c01c0300881160305503c0400e03681580d1009803c4402c21883d24040c0d520380b90745190040d10b070b06c00128030250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 806351214 1250 806349964 806349977
    0x601020c010e1e12030c0105010e0408030610090503031c0e0115090c0c020316030312270215130513050f010e06061c0212060108092a062205010c0201 66
    0x10483e050044400c40491400d03000160301d420740c9070115007400002c1219080707036800021901d00000e001e1140380c2c05001d100c1603582c4582801c2c0c54003001808050103952282034400c2038411803500400c01c141c000c110107001d40c4d4681c60000c95034503540c00c5031a03140465504002a00c4150007040c8618207a800350900390108642c1003101d0040109004d10858041c0061440e0030005a82c04018035110a03000200c80c0041c1c1d401d52600030041c03079072004030032030782410034100c009025001030070030460a60004201c40c02d56031500000303060080d07240d0300101c0ca2400003102040c0744140421402131300d105440020080c150003202c001243c4040b070303504606801c0180140a030000c000b80d003641020700207003040e081c00d00e40f6110800e1400c0b160001e40c10f895000514400e000000719a0a07031207035007401d0112030b80c038000401075194042011039100c91681c1011140f00c04007000340c10b02007500d000c3c26460f201c01c08107516941e00b4440c0e008040302c04441c2140010b00d98882d03980d40d031844c3d0341a51880c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 806352464 1250 806351214 806351237
    0x806010e0303120c0d020c10150f090c210b03061e0105060309010f020301060507150b090a020706090f0c0810020f04050d030c051204090b0d1109130503070b0109050601020c01 77
    0x9000d06001420304c00ea4075108000048644070580054114200b030100030307164403801042e0b610100d411201440080c01c024803400c001460140000c071040707580c00b5402080e03040180e00700300c440c4072039205030310764401c1c008007607040706411503000d0005141c05a00302c07420b68032207008200c40302c05120800882000c4480043c002c0307041c214003864018680c10f0001c40c4844620300e0314000e0360400d800100003c6c002140c144188032001d000328202c0850054100a801d2926003c186001d60040260505580003d100c00c00c02c5038076803001d810107821101081035283c040c6080903200c0340340d1055103194414a5406640d801039482111107030f9590700c200524080c5484140116207900d01070030340c144041581d215010035014030076109464440c0e40320590361400c0201920840e035440400500401300820b0320000540e01d42c4420b11000e000329080c1c006c95940c0500d00844007607114000f0024040441e8036020480395000070303416118101418002e9a40740001203039a59042188140010b03901c90b00c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 806353714 1250 806352464 806352487
    0x180c090902060c010c0302031005061603030c050c0105040b011703032401050714010c0311040303021203060303040f0e070f0c02180a020910021c02010902060301030b090703061a010806010e0303 85
    0x36124207440904030700c1c00c003050200e5140c00c454074158050302194002040024215020000001516044031501d040c0f0b80b1010102c110b812580d08014241075a82440724046400385050310711010100c0003c0c0304c140380518180b80c074200d0038800d665181c4662a04011521404000c0d28032501480007000c1d8140031440c58038005074021004c540c140802000508007182e8a0000c0707918a020340e03000480c4100070510001c08544060340e043d83d85040074002400080d50100e1305480f2002d159550079241e440d5a00040d007544243c1c0c0c0480c0c9102040480080d41d003900d61034043c0f0510b01926486100c0d03149101c1900c04810088000b0751050313021411200400400381681e07003124904200508282407040840e40040250307500b000035a008841c1d0b8540245016400c10f4600e1552000f0300a034060380d0702041d0a07000600008040c1219034000801035681000754100a64000c0c80911030000b201da0040d20202d8036030300043c00a2411400962594080d40f80002e40e074401500461170001500e04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 806354964 1250 806353714 806353721
    0xc0d14151b03150a141008070f03020705010621110603040f12090e07020c03101404150f0207141005090d0309030314010303110d020606030a1713030602030901180c09 73
    0x100403000f0383d040e2541000d4941000590182c607499241000c3c0e140e01108000401c0f00591803e0100031480341001690769000810082da4002ca090250b1034407010300e015405480960800311000740084480f00e0b1200a4181c0c008500b80140c2146402a14000621101c4e210454000c0c118207564481800065001c800e003600d406501d28001c4c80c0d8030307200d00e04d1801100782a02d5401c0184e108001845840c5400c1c8649035030b03c01c00d82004c000701ca12035070001800c000c0c010400762996000c00051044c00000c1c0d04561402c01e144e600455071841c082ca003030f040c0d0070081010b0216034071079264034901d0070302c880c441e160050250380d00500074076003a0340b0300320042c1015a0301102015144d00410410352900c0c08240e0186210b07445600f0844d0240710310a1402d150a42d0000865000340d0500c4840c1d2001326a4070070350b40c3c004031081140c4801400c00c00051181d040400f00325140d01d48000140f0034140d000d140205541e20007803002c44454010418009036104020707000100c90310003046020001d50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 806356214 1250 806354964 806354971
    0x221a040f0b0d09140c1201091205070c0905091606030e1e15010e06090702060c04062a1103010509010b01170a110309010903030b06040806180c0d14151b03 68
    0x18000304000d9001c0d55888004481c801d00b0504c0c96000342000400f030b18080c50900d240c0342810b0002c00c030a030200d4075101901e0114510907828040006004404d016541900101408161005100604190031402d98840f10020001e030003802c00d03c03012541500c03901580c02c1c1881480000d24421415100054034a0780c003000d004041d10900c01c00a51520110290500a1a41d6004601e0900e0808140a4510701c014a100219004a4108280000e44005450958010740f520407850b0007107008001c0c00121361003520b00d00355191210a0b0410109000807402c03a80280d000b4005602d0b403103040c82c20703108a4a02c09001c1344c0308640300119200820f200304d40c0107400d07003000701d480b43c05025103138500e900a507a00c0541d40d448004d40300500d50036004a40140f1402c1d12490324141c0340014141e00c4581c054201740500060f15118180d4035010002d455415900805808200394203141141440c030406041c030a6900441d0050048440041f40c500c1c030a44035990000c21164100c0001081035000a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 806357464 1250 806356214 806356237
    0x30b060408070b070606090203011a071b0e04020a060203130b0927040b0105300c060c030c0705030706092d031401360503221a040f0b 59
    0x10322000036040001c0000303600034101402803036610412810154180c6007a0740121030450700400040154503041800e40d240c114413550125240e685c0b61070101e51025030f001c454814a48415408607448004004d950b003d01e2007100d20300b000ca5617400090340c0307a00500954515201511904000000c000f800800710080014004042d10300c030010701526103000d15030341c0100e03480c06008020801901450300c03401340a04460b00d03c424424102c201610940c803c411300c624031145c903011028030b00204451114903100908403034903032a01d4024241d80f6008080d81c00c0641c0f1420f08005590f080104420f0180d0703806584007070600c0e040407121001c03d9583c0e400340e19401c180203084009481c60b241c049014511400003180e0070524035500030b080d11502001e05150402d4074406001901c08404016a91003040d202c03680015460304180d8150300940000e03040065020a40c20b0041c401054428150341007034510880c204a4965000f001d40103e009802e408003a00d0380501c400066100074001d000c85a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 806358714 1250 806357464 806357467
    0x601052b050328050c0606010c05030c0111130909170715060f06091d060f060403061805010606080f01090b130216032703080c0c030f07030203100516030b06 69
    0x20780e580303440e40d8441c07440901c502d42003112403540c5040d810321450660003645002c1c0c0c02c0c40040508613840d040040e0500741403003040c2d1951010070009000355800a0341181c020410f10004a56108803680152480e4040e401c9409000c0b400420522130100c1c40341d0002c2c20b44a81030a50080b81c800c41d407092100f9110200600c08a02400c21140600c001a01c407400c0c050000c5481d051020300b21082d560404244250340b0344181880105420315150300100455104022141c2e07031010032440d01ca40e400180c00241084548084168103141b120f45144c4604020481640ea40034125401078003903a07081c0d20700410384d004101e20f6555421000301c07204000c26200e400c4220b480310390200e0b44044044042c030380c181360600003410342244141d0381c8001030308001108000d41c040801102181800000c00d10040800c0c907144d000410040a50b00c0c4201908a034980085607e10b6560f40440c0d203c201c3c461300c252203403240c890354580501e5000710103080440710708810288090300501449074010b50483c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 806359964 1250 806358714 806358799
    0x30809061e0d1d0a12092309090624010917060901060509010f0e0c09180108060705070308060f0d082205031212040804230f03060105 59
    0x6103004038580c62418200361640d620644a002c0007921a20072504808a5103100341c1a000c2101155440035540c2c400d284512594501e8000c0c0c641e111603801044000c403002d01c44106031202004c01400c60501200c000e4016510340e421669070756000c44400146400b1862114808607104032000d031011014180345000c252070305102007079016005940b142e254000000d00034454428421840642010b841c00046581480200140c02582d88120350070ba81042c2c00250235801072200340c1d07c801100400c01104401e900c1000b0700030503800e0184400781e00812012a040b2070180c030403100110341c940c9801c0301e15520001000344000708461140d410103a06140e440000380090010a807520301403203540c02d00e2000b07051034014500d464111038081c1d4803030300c0081005654803090b0360304034050fa4142902c6956924200c4050b00490340950780c901e444013880040140c03045850701060030306640242c00c0d030743c0d45401c05030703030f1402071140981150000049400c1100b0306441c00515000c05078007903e41c2007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 806361214 1250 806359964 806359987
    0x3050d020f07060903030515030705060a121b090e011206050a020c01050c0318150a110c010c0207090f0b090105040c031d07050f01020703170313050f01050613140103080906 76
    0x303020303002c101d428070b41d41c492040825406201c2e05030401000c0002007034450300030021070703034400c00c0d409010310030322010544001c0c032440b811480318000d980c40c030140000c9007400d140e20418140f03800c0501c0410b001c000c0c080b490300d2140013003030b0481e4941e101c0440c0310603050311048003c040190000b0441c507002c021074490380e0400d020301400349800c80d071299600d240c1420f18410703210140001c0d2030f00c0c3c0c01903241150042c89403101c841c0c0246010000180581008a84802c54031a004488140d9400c042c0c0c1680748507008540c0904480314280248900010812903108442c440c0d0401d070f174002c03041401409a030030240c2c0001c407a41c0840c01d0008101c481e9689151601c40c1c0b40c0c0d4a000154000c4200340410700f82010711600b40c0c4001e0000340f09541c1903583d40000c00000c83c101890799040840003995200b0400b1410303450035040001c0c0da01194840115601074442150003a0080c0340c414000808200c051044051008503040120413903401d560790000540d21444626501290500c001150f69 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 806362464 1250 806361214 806361217
    0x60e07020a24181403070201021002030916030b010f0e0402030a12030b0d0f1a060105030a09082811071203031109090c0c01050c030609010303051e0a120e12040303050d020f 76
    0x4070f0150441e043c00710000d00d010841c13203039400300b81140e0303400601000340180d80005510b502c1ea107200c1b5015890355580d818007854101110300951002c210705c1000030030f100c5107a020324180c600300c1400c1c142240d100e40e100c1002d1101035400075019401030b602c2e10089612155401c0c0d0259640c41c000c030f00282c000c0d0000300680820907080d2110949019240300b000181e40742103d00454059081005251283c00a041400000c048c425915203c030680d504000302e00044075801d40d04d00d000b001e41300114220291050090341d080e13a0101e81c95030b46488075203400080010440e010141c2501900066507421400f0b8070003480b1044404c84103000e50704450b541c130040742e8072400ca5801c04503110f004851400d82520005000442890020014010680c803410340c0941500d0701400c00580d9145841684043e40d44007011032401040003056582e00c03268810003420b541d00c1544000d03c0806210607009803600207220003544070020810040001038059070103010701c0d598418006007880d080074401c4485 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 806363714 1250 806362464 806362481
    0x10614040519060914090105071b170310051c15021c09050c01081f0911070b0901150501050f451201180201081005180406060e07020a24 60
    0x8081d2610300007914022000d175410ba05c09804c1c0024041818022005000454200240101905506540030078000300103a0204400402d007503855403481c1084c0840c01d1402c1d507020302c1d44903401c0442c2c011b4050000c1d10881c071070303250884d007042d8120b400802050001e6100205504e03010b00428400000d1180c54031440f00d0450188001d0700120707450380001896240000c001c6c03a80103400141c80c000c2d08a20004180940d14200000070b540c0c0b4492000080c140113500c0d00601d00700c10801004501c09043d00803514001500c66648821500c560054515005600401a0010084c050040c804420409000140b41c4154400e0390304840b01d01001441070380c005c08070401400581e40c0800070f0500094000c0340481802c0208103600c01c007241c6104401090402078100480c45000ca200c8500343c52041008050081282001c914192020700c8610030407902a07610900c1e000c000500d0040365a15544100b507a41e01502101d00d080d50b0300a2a07402c050385151420b48024258903044500d44100e084c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 806364964 1250 806363714 806363729
    0x8100f030f050f030f0f03070e06030405010b090702120d150803191d0f041a040f06050909030703080f0405011d010b120102190e030a06020f0309010e01061404051906 73
    0x540046400c2c82880c01140c0c400600080d4410012448041050b000b81c03401140e2024050350f4a031120701080b20314501800c1810f601240c004144410000154005035142000b56500e9030541d0305d100050f170701e0701403644c0c030600c041500700301e0300c00050301c580d2104a0070504806c448032445e4a03002494a55000000307141950b014400020003280e40114404024601c13000780003030300ba015200850707000300c0000700c0c60f4010b649603440182c100d16029505a00c0e020042e00810030129154284000740030184201c602a140c80c81c08034101c400c0110884066a40580b180c3c03100b600e85064111260301d00030015200c3d5503a40c076a2607042c00f030fa030a880b0001b000343c000118580d401c0c41700704400407852810080c26030f0710401000300344024a440e2001d081c2024201030b0102d000240109081c50060b0000802c0248001040d400c003032028005140201184c4c0001c22805000c00e4046088404d24020f04103451010071444006203060f070000740e40b02c64042c00b0760940f0803144452400b83c0d4004d400c0b008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 806366214 1250 806364964 806364983
    0x6031202030a030e1f050a0906022709091e1c08060102150103200301020c06040503310506070807060e0601062d0c241401080307110108100f03 63
    0x1c01c0c02e54036005610b28000e00b44040e2145990300c01d4001c0101130155910300c841070f00c0e440013600e080c44a511090000d5044101075540300c02d069940000b415189034180000341c0070100c7c0181900340084c8482c8209424001004107218426080b046040c0910036078585100b030b503400078004005109004a43c401c240c1703a02c081402e0210019090100e00804c00088250355030040001c0b41040003010007401080c084a501c3c4204040030901900c250222004d4a204080500c0f0030004000024120200c15102d0401e85084145007150510740c501c0c060304500301c0d15681882140341c150000c01e04e1901c1481107624121080c0ea6680641d2400c40c0380082c181c000ca0300400c4119000000e21a41000f019052034201004181d04419840080007a00411264000300001c00c509a4068400d00180d00e0044c910300d50101866005070000020b00071000d88a0800001d50510000a940c401d41c0c1c083e910f80d02ca540050011504000d0003081d0200c25250804001284012200c0700e40140d4041c1d071154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 806367464 1250 806366214 806366227
    0x1018020406060809070302092e0509071701030305031e10090c0504030201090e06030f06151f050904050901110a02030c0c0109050901060819020a050a0306060801050f060702040603120203 82
    0x1080740c2080c2c2c803850030b0200440401c1011000802d400c4c003030b81ea04070340220049c6c803501441081111003032500303a01d5015901e600071200089004a104840e0700b00d805250b030703581d42c20b4211801030380c03007901020454100d001480001d01a101031a84a11101ca450019080038a01d15001d041d055801c106903018040040c00201414000c0004613145803c0c0700d840c140c07865000a000d0740c5140300e680406c1410902080103982e0034498464180883c0301101c01c282441b10040713580165001d100f0344070304054110010300c03d242084042d00400a6190142000420f50902029040c0282500c1d01c5560712082c0703401d48240c0f1006403006000540c0115201e010b2411180e1500c102d000f541810710483c03003070400c0a60741d18002941962001d01e040c030100e0b107030309400d500c1c4040394010710720f4001d0011441161846e030200c00780070050380d03941d0180880c42e41d9507401c0c0c0d900d150a004580e080f450400d41003d0b1810010f008054261002e080092119940c0c2c172480c8140d1440d2441d440160000101c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 806368714 1250 806367464 806367469
    0x2040207030c0c0608010f03060b0f0402210708160305151c0209010b070b0601141e030412030b0a1203090f0b0304051506100e0301150b1b240603101802 67
    0x14401804841c01c5c244055410409803003829080e074480204466101ca102414544960f041d00842c031002410a549800500424044407601c580e0b24400c1640d1220004983c14071030900c142c02002440305910b08624503c508030301402c40148600c1c0c203000540c501103811f03142c0e28050101e00c0c19165414041000300d01c100140c805040e4044020a00144084008140c100d01c100350007038401d00f00050101c40285007001503003e9800c4003814550108007100095040c2d00c000c52107140301c1d0301950000c04054200380c0850780040d2401d90000400d07001803145410001d06011120300a0070407025182c1d85032401c0080c40026001504507503004814481040001c100c0b80b80105121071003c0c1140c5052401b0075860034080380010100302220310400e010391000c3d484102c41e444c0060034850742d2500e5402c60501a440206810044140c07603001075036480c0040780e065807004000d0f07429203880c0250700340390400280c00380600354035010b02440800b01003070741d106141002c07148400026968159004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 806369964 1250 806368714 806368733
    0xf0603150106230f040b07030908060405010902041407022d060c0a20060a1802061810021f050702190501060e131e11040f0e06090327010c02040207030c 67
    0x30803d00503509114094402c1d0035030050340c09981c02c001708161202c0050808031200e81c00c941c0101d4190040e031040c04103102041d00100304c894000da4050002c00000303040b1012030017003180d41100580001078641440c8006403c0d1401c000c4042c648401201d05000e010b03410700314281c40c807000510700003990707000c0d4580040b00d9a1b480311150b1a1a200c542c0d0103c3e030b80b81c40708401002111815130700c0d040b205c003494058443e80d22840d0040c1c0465280c0c3d034200082c00d240114890458820102d6040b0413030801c0c800244181680104031500b800c2c0c02001807500043c0002030012015070203040c80c104040241c1318034241e0302c280501e0002c101c0500e0300341d000d9074000d800340031040070a100f0120f44004c5039180b030352005010310000d0410032010507030515800a155420400e5400303814a01d0904485265402810708028a881a107603943c48400c0c00682d00d105040b120100c0e0b070040500d024021010580030306d000401030504041403541540000c0c02c0f640803030b0040b0042140300c6002c03802d0014101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 806371214 1250 806369964 806370017
    0x1e030f042306041a0a140403150e12070605040203150408072105030103031d310c0804081b030f070b130302100b0303070c0f0510050a080f0603150106 66
    0x885503840d040c24800081e42c4e103a1902d02007281d410700003d5801140e881440b140583c041503024003500c2c0c41d184c0c9040c000010260414014141c1480e418001c01c102c0803814000e0030b203007842d1702f91a0032a150394280203058010020b80e414050201401c00911000d14000c1c400c51240380390996500c0c803850309007880a40d04403184150510321002c0320f01660020111390559802d0300b01011044c820f016140340c00c4c04091207264024002d14035148601c0c081400354510310f55084466400084070002c0c5c14201d91040420300d001446000204001c160110700920130341004904070048210380031603442c6180c0c0034070030203000345000050301d0051241c040740d100c1d04000e1103a588940c503036094500a5030354002600045207107a03074240c000c40300c0d5020821180150303071081401527070580e99150350b80d4080040c810903009006849400030594031800494140c0502519400b200351503d20540c5041140100720a405100d0440d00011102210341418002d2129540754040c2c00342542e520180c103110030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 806372464 1250 806371214 806371219
    0xb09091510050a0e13060e030418020c0309041d120a0e0306060916021f061706040b04080304030329030705030d140a031104141903051e030f0423 64
    0x1030038000c9035a03a03d0214101c9003420100350141d02d46401a651000020308000c180b00e2074919007904240000c40500100da000e29a81c0c8602c4001801d4002a8400c600031664260003c000d44106d0b4981a8844014840c441c01d40d0035650207406d90132443c040ea4100d1fa9250800e0104032411003e50052608a0042c815006403560b8108240451040040680180414408500c425a6485c800c00c100d0301104580c5155002d407029600c9013600411a5015070401000d4001c08507000c4034001541a0043e0340c011440c00c0320f540c881c0c44031212078101900441c00c05840388080030503191340e10107422507659041c0300d260700c01c005201050314150580d40028086e80121206100b1a80c00440c02c08a1516203011103a03600146c990850040009440180f12404c0114000c40d1050481c10a0100060b00b6550407000351594071a240d4130a040f440300402a51121003415100f10044400352840c0c82c000c82100d00b46102c20b440505035030400d4201804010071500f0b000800c00715405001d81c5000107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 806373714 1250 806372464 806372491
    0x40e0403090b0706020d1d0309010f050c151e0c03070f0e04091a01060e0328080705061b0f090103020a020109061d01181e03021006090507081e0601030b040b090915 72
    0x143d01f42c1c9a0003001e81c964140140e5502c81c6454034058400c0f40d035000d00380025180a0701080050105100c003d0741c08981040f5030ba0304850500e40c8189140d4000c19100ea1402d00b140d0700e011040b603401010748101d00800c82d036041c584103582c0395405801c845a2013540043c00b1514042845401c65005074001810080005400d0b00545c4001c0703007025000214034845041005100092500043d10440c01440500d000603580103020303001c41c1c014085c480c0c00395180038426840004d00500d00841034070313000c098401c12440c5680e43c040c4d4001c3c440d141042c0000300d05000251110800c4480d800c803543c1100950340d00642c0da01c04284186400704894900c0f41c44540450b0b2503400400198135110b1148041d0761141505050081002d4000d0311400d58050003104d0700d03410008003600096840e08003113031144c4c1c04600c2094030b030800044400d036008204001c5076034500044018040c10780c145a040750b550400e100240c0c8544400790710035089080100400340f01c500c600c0440c3c103401840c81052040b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 806374964 1250 806373714 806373761
    0x50d0801030b0604110c06010611210a0309050c03011d0712210c050d0c0b0f060312030a06050a03060c200c01080a180b04020102060703060b040e0403090b0706020d 72
    0x1002075183c006100342c0c3c00041d01841c60824200070702c03070a0b50312100c51050600000317600d90300c080070a01c2c0241e800306960310580c26548074401e5644c2882c1031000d07540d05000c001d00e002d209504c288070950085003101c0408202c040803a003180c0300c60041007401d40c000c152130001c80200f005140e0040001c1300340c150204200707441da40c22001402c928030100103540305c40304440901c80c01e000802141c204050b15040340c0c4200001c2c101c0d01c9070280440f100c03a52400058403444e104001140f1450000d0003409500101c6501d0b00d4042d480242401c1e5001c2e5101000700c0c6649490b01c01340090b612910740003074601d0300741134041e092282c0000c8052a50080c040c82104500c03010803601d101000a08040006031a032441080180034842c9002d40322544407000242440b13210400c1d540101e00030380a442e00c40d15014412400d448290046070503084040100700204003040e401e06510900901c1e0051070180c440101e078400da13120203c1500d605070042000c07070701d1100d20312956945442c1120725240210 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 806376214 1250 806374964 806374973
    0xd0f0212030103060c020703080d050405010b0a0b1218031201080705120a0303020901090e04202d030703080c070f05042318010c1106150a12210507050d080103 70
    0x1c0140030003400c02c0d48031415030401314002c001c400051076014816503101c030f41e48002c4200401c421035091300c0c65030804c144610785051020b00d030005e544000d80f10a14281c10683c034038074484409030880314401c0110354400d14003c820301c05400e281d41301d2040c1c14119403511009903d4419030b500304510450a0510403801081d00003103404c4107551600300540c4034031901005840c202c081e58004004c1b0441442040104915000115500b440c000f4003400b5000142051100074500000700b10000310f030144c0039408452119503100760584005084800c140c1c0c4a80d50030825400c080000116948219000d002002e20154004054181910304010225840e0582c0c603a608603500c0314044031034490081a42c040c0c40c91240448512404000d00c01507a00c400020014260721140d8038142c021500030440c00710581c420410290310040c02842d00038100707910707074050922400048031030314800c0000f01070030102c500c61600c050fa215211036455140701d007829820019090443c01c1041118401440040d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 806377464 1250 806376214 806376217
    0x9031c0f172203050d020708040302030124090f023001060f020d0813210315030f08090619210207230304080102071101031401030b22060e0d0f0212 65
    0x100322078020400070450381030513105445004441c100150000603400188207055004104991090300200207245004079000003c042a00000300359400c000c01c10000486207400000207100c9100b030040c5813880c5007003d20003200741c03206144850381c415041110311803400288140184280e0429644800c1c28600c004e4940741403010b00e105000070b0741d021490b404210a072640645501a41d40441a03032120f02180303a020125074400700203824184000860700d2041c0c0901c0449500940049250070950b55129094200d00d9100d0340101c0107204000346092600b103404810b0302c041c0c50f9080045c021180d0749031034120042e1f2140500c0d0042020500140c5108052050304030411545007108240810a0f810341c40340d94003203c0c55600220b2200107000900900c201da40e038003600d040200442c1d02076460b00f200340900c0060180000300303000408200710459508140c8802d0002c291070f1001d541d640004075030036000109880c0d484808540c0030305070400300c00092070030103000502102c08000207101c100e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 806378714 1250 806377464 806377501
    0x10e07080a15181b050f130f2304060f021606091103030a0905040605030106030c060813120e040c110d0c05070e0c0307030b0f06040b09031c0f17 64
    0x110000d030700328550b0034421a44914038946038001a000520910b04060b05802098141c815140905010000b010300d00411130112000b0098034914440c0f0310311946100610b406440c1c00d0002e91180c890300c82e008039400440c0c44040b17507028100202d003400d04040003103807103500c03181241c28810409129014041d10342e03000c0207944540301003502401850200d508158404010ba014400803d4600a26410034900002e4402c00d5400300310780c81c1c0c2d503810582610268840940b4420a01e0b005000c100c1c46140043e9203c042c101c404842c103229035440714000144080c1480000301014031101e094949400f80004401c190728120001c45105100300303031210310701c404100c14071802d0f044102c00c1200c20b000e070b00010080140d00700d40c070313142509000d00964000c482030300019240c810082070324903014000e0a8401d80c05842c113400c003824860302d071519510203083c06a02d88502c2c60f07000301c039031140000c138444e140c21a079440b106c0c51030f5214003425010541409030a140c5c822b0040100c0a03c0c0d14101100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 806379964 1250 806378714 806378723
    0x1a100e09010504150902040f15061106010b0f220e09060f040506150301091202060f1b040b090d02040603030905180c03040b0718030c1a1611040209040f050405010e07080a 75
    0x2c4080a031b10000f0014902169104078650070103040c8415410032804140840e10079484060000340c91200160f162807090098082441090122044016140002d0104282034403040800380d580c1c0c4420b07980c2002d0587c401c030300341080c08007003002d491014020039400a20311a0841da89046c1541c55545031000288034001e07450b0f824001480c141d80035000703d10344580014820010905080340291941001c0700c0d104901c06040000c5075400d0084500c4691204d004014a42810b080040a40d1181d21038600d15501c00c0d810b0300000c01603030701c034800c40d001903120340c031008581f0f40303441c06000881f2240e001c0c02d100b140c0c2c0e1001308580401040212a071080d808070740300c5905d5a800c60709480c4c882001810310301441b400d881c00700810400704403580540da554044112443ea07080703d00c8440344034070f0190102428880c01c1800002c0c18000c5204900310b0014405400c140703228002c101101c80c4883c102d0812915001803100303001081c4500f5052040600c054815903003856074140d556161101c00a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 806381214 1250 806379964 806379971
    0x6090618090f06030614060a060c03020d0e0d0506150906040c0503040204020a1106040303140f0402030c12070b1c06090b0102150c07080703030b0a0f060e09041a100e0901050415 78
    0x31035900a0f80e2000c0c0c0a99404403040000f02900544032107550000c5400a015007001400419624081c0c404c49400991581c0107052550f0110002c03102c00140203540c1d40c02007001607500e4006a01807100b0f610032580541e00302c161400200401c0380d50003000c0d01e240d00880ca030070420008182d1101c100c80c0d000d601070b100036941d591404c500304c842640c102007400050261405001c105075058110309540c54240c40c00c2729054440d030305910090403043c2c030000e616500c00780c044948c5080900c1102c2c1010041401c0d60b220715900d00240d88070340e01c0441c05044500138100b0590318030900d48a20405042010000c100c003000c2000040d45d109460000f0314100c41401c0009500380700c50070f0444d070301581e2201406803942030034a0050043c10200b1856407045c00030080200307080d2035001503081112101d540b041a41c9440b2001e0100c4801d001c0e1055400410078004804980b941e80364841c0500904610281014504a10000010005042d50240780d060074103001c0819100384014a0002e020715000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806382464 1250 806381214 806381231
    0x41b120e03040f03030f02060601031109090405100e010c14070507050909010902130507080603012702030a0c0b040509010b0406020c0105091c060605040c020a0b0f040219080303010609061809 84
    0x610754080c95100e5030280d500d5003008010183c1c800c0241e541c042c03058086406a444040c019810344810f0b20344440d41a9043c07100031074a1034174015560708117010340300b911504007030790414409482c084d8502c10a241e441c0c0740740c4048103078007817550350311520410f4205040542564500c0d444070001e01c64248a4890f980204001c1c80007980807036801d41d4000c2c440c0c203a144640003000064641240d5500120701c4440c005146401c06000d10b0074a07107900440800f40c0da01000c01c8801c1710f02c004005903010720130504410001210108071a0141c0740b902c2c81d4a454030300d804208484600142c0001c4411007080c001000b9a03074002608030002c860074201141c0b182840400720302000040c81411005800400c0d074001030051700d50141c02501c0b0203840a2240303081802083e603032545207a0b03004040c4c0030404009240190895655500184010801d929122207140d000c10041c440d42c00c0401d15420000c0104042c03034011004034014812814200301078160171103851940b48030b6205070460181c81d111781 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 806383714 1250 806382464 806382491
    0x606090a0c090e09060a0b01021506011d0d0818240d090510061a040303020a1b03080307020303090615060910020c030a060b04060608060a090e07030807060b041b12 72
    0x2c44003801000600740c00620385030540030307601c0c9801e5664030209031070a1441c070303050f51000c11310b005078000b0038014505c1341d2140c1c0c004403011019200001883c004600503010156580803410842c2400368504070703140c8030035000d042c04003004080c40781e104602e465508507c504150008941c442c0303020f04c2c05a2207805545103a000380441c028010001d019940d00c0022260307281d8400c1c0150f4641c4d180a0103018011140300d1001d00c501d000141c007580c89015180d0000f50381c2c0440032507100304000d0b49010b0700c0ea65558070b1660b4000303450300b80150f0008810462010404c0004607800001a42c10070580c0340d042011501d180320700321140e40a503c40c544aa104a1b00030004c810507604007904a03000000c241c01d144004100d0780b003049126500f8074000140003407141c030b00680650402000f1003021441d010b213440041900d050090b005014540c40000440c0108c1d000c3d00c03c841c000e01c40401c02d4201e44042104130f82142125044030801d081d0141134aa86c40740b0b80610201c030b15240050440d041c4103d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 806384964 1250 806383714 806383727
    0x1c0519060f0612091505040302060106032c0a05030c071701050601090e0a0902031618060b04060f1e03020d051b0a0507050c030319020601060801050f0d11090c0a0905030606090a0c 79
    0x130701803d082040041c9203003402c0594040c521460007a820307561181d8170341d0403c03004d0300c0101414041c14060b000703582e485810b80d01c180c2c5401801e00001c4400e00c2d80555a5142180c2203c00e141c816a0854a410082940c0c1d4000750b070034064592000704498a03000c0b000ac1d00d440c81901440740042c440c00c0c0018109101584000044ca40080888000c0c1c0c81010249900d15400d0140c1100b11001505a42d041001ca004481c1903540d038110042c00c0034200342c0c040b40c4103076680c0e01103000c00c00000032280d980a041a0080030f008174555003d070380d4085900c900410f5807009010104410161078002140824000650710344030158a04913a4407159401c00f1490000d41900c1035030b050000041e00b40208424422885022402303400713a80715070ba600c442c03d58103402c3c01d00c2141d4000f100d034002803075603103012550303906080c0c421024010141131070804075080d05012189041c4d001c0000600340e502541001c2484000c0000306c0c000c0109203000b07800b14001100240c00c0c15412a2a8100350111501900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 806386214 1250 806384964 806384981
    0x2090612060d050f071a1201060e01050d0204090b040c050a02070b090a05040e0a0614090c01032a0f140708070602131802071a040f171c0519060f0612 66
    0x40700c600310a07214243d0303160034051042c94001c0080180046c0c000c500743d1300307403140040129409070711a032820f6001da6446296001c042d0402ca000c006074401149144007800250005640000307054a401c010b00080300c2070300c2a51010b1040a01034480302e075a00140040540340c0f42459581c5a20640c008500920b020380c000550060602105e030ba103203c400121291058007400e010701c40c480521610b441111429100b2590503041442460810b50003900042c18924401411040c40d01910400c6010300035080786140005a0786811500050350110f059194100c8e01c0801920340740300c5a41b1081580300342c49004080130340210b42544031020203242e000040421202c62100d19400d60101d4000754050b01044804564a4071085030b108038020300305208941c81120030040080b1030f100c802c035001440030140444801003021100c41a0443c5100081c000a0200801e07103060020450b40000854484001d0040c54140200131841c03405011404495050404152a10070012310002400514 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 806387464 1250 806386214 806386223
    0x150b01020c01051219020913091707082b050124020102090f1203090303071b0e060d030e0a0b04060c060b041a54060306150d0501061502070902090612060d 68
    0x140da005d1000c00d156040f11127007a12680240300c5003075612203044001e006000015104200503c4024200d44130115083d00035103401aa00041045002521003a52001d82150954080c1182501c00442444004051000050000794102550030380030500b0b041c09103203658421054840703100c040220900440c0c9008201400341c13a50b4911500b40f6816002001101c000c07000307200c400014802405100b524068507005006901c0c8511544045814401c512a0710ba401100c4120014501920700c008000500076503c0d62148032042e41002c1040780c90025125018500705124550801c680448003ca1600b04a444071401400140c406d98107440902d000e000c00308241008081c4290440035040344c0103600c2110000039110030700f01c590207483c1a44c03919015480000800c201306204016507040e040090810801d190a40e20ba9509455a0740e1010740070110100c2c1e8030001a1b0b05104a00140001c044158034054501340400c82d144a030706001010b80c02c5000108101e0341d602d5040d2a10780b40c10 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 806388714 1250 806387464 806387479
    0x1b0e06041e082107150f050124020f100507170c071e0f080a0302070515220507060806040204050303130e070311071e150b01020c010512190209 63
    0x850403548000e001078010315a082c45000c3c0f080c82d0185810030403a1851030126002400c2405a560f565100c0221082c485a0350303480e02c502051402c02071040394002c0440000001e210103420060b00c505042d610f00350011900520884c2c0400c2d1400110f165541e0b04d20a4001a42c1d6641d01040f01c8041065070725411500254090040301e000407005018054025040403410314403010b540186400781100c0142003254a01011011580503030160544a450341400743c94504690303a9281407001c0042e1480400d0740d07801c01d0004121609074250060b450012582c001c580c10307512174a55580b4940704482c03c0020040008e00181c0300c036015640201809400c0325181e500421304401c00c01d80c0c50007082200021400040d41c4140300e4050403c02d6001c02c813805140c84910b854094841915031800d408070124855580300007044050525600b403903c03071000442502c080d00080c1441d4007680c84c541041024002d0034084170b0041c24441c0c201900490707006052035010003040281c0030300040c980d0300c80d1030b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 806389964 1250 806388714 806388749
    0x12110f0105091c12080906070320040e0a05010503030a05071202070b040315050705030c0901081e010b071e0209010509071403011806050411030c07080d090f0201030b03011b0e0604 79
    0x288102c0001445014040b441d07a4000508a952100480d0302c441d187d4424400f00c0c2d510390096000b10401008450043da03505007908480d000c40d8040d600005011400c0f5041150600041c03013011b0140004130f020307515154411000074800d00a240c1d0280c02100420050a4010b00800c90100100114a2915140d035542d0601c4000861010703607806c81c1c582448000740d5541e102e407044a1003030003210b8005041c500020300450707600c2c2000b800103070f030b054451420340039103208600e90380e0007810301c41e03529991505185844035110148108060900150260102c0141e881c500d406040d60400c1d1030031003041d9241c02007182c905001202c031071005000000003003903207484030600544404254200f0f22006542d181070000720b4141c02c55182c0364034020700100d90681c203542d000b0316205004488180c2014070300c0d0170240440c1c2c2580b00c1164161019101042156058082d018212070b040b402040040c2d103980c1160115040c06a56034208100400d0060896440c07105403400b0f0900740756010441e40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 806391214 1250 806389964 806389999
    0x20618130905060a0905070b0a030b0909030c0f03070206041208120907080f0c10052a0a0b0c070b0a0b0103090602120114030a08120406090501230112110f010509 71
    0x15075250155000e0003010000f41c1824018001d241ca4542d1040044c004141790002c4020180c01250a440405444100c0c050b0320390348200100e40130b89480780c099992400b00320003440c0781c4441101d40d480c19400600580015030f036800c0c1a2000c94440c3c41c00e850041742e003450000c0c0644102e01080c040a41a4030900c00f403008001001002e0307030b1200044a48800034000c480e80e48880c20752207a940144401c4121a0841c402d0020702030010504140c200094120061100b015910b94030003003d03a401a0142c80034002259a0075400041d070010480c90f150389612140018140181840c60160b16005071001341e912030352007122150740003081107440f207201142d2010100d0082c81121048100c030a0080b5852401185501c4210f40c0301003003900d8181c2e01700c2440c103034a01c014815a80c03156034410140c0072690a0264039040ca140d04020300408002c0519140c2d8401c040e00031401d001c081c400800b000943e403503c912511801119024481506030004a401348100d0400641000f610140c486480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 806392464 1250 806391214 806391221
    0x9030a03030906060602070e1303020a0209010806070807090303050a1d0a030506040501110c0a0605070203040f0b090108151c0c0302060a122301030f051203100f0f05010c02061813 79
    0x114810f070000c1c031145581d02e4040340e42c1c040d24003401543c000007a002c00c02480704540300013010b500c41e0058800d00340140c1c00240700c00074240c2c09501c003a00702e1401c001180707501c11140c991040345801c05500440c2191030042c000d0103180d000c9814080e580444a1096803202c2c400130700e1b000010800b0174160340342d02e06262a2413041c4d600300c40b6507003000703080d4412040b1142a9030310f0002110041c85848415115840982009410b8a065000410000c200c490068404001501039455019503840750000010b0900100a04100300d0b56440c40b00e41c0380c180c0d074a1040300750700300d2003030b03008103084181e0b0030700c4d060060f0981d00003503000344001b4052040c41c2e000004a8a00304130b8400c10001c0ea2498001e407095214262903d21103260b1800043c0300082c0c180e18400560380c050422030b0351083c03680c400d1002030307441a150b01008083da03000812402d40c0808540014104403010018602e04d008006040130701c0080b4000c3c410341c0c000c584e141800e50480d0000034220b100500c891102c5c8091140c03140107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 806393714 1250 806392464 806392481
    0x3020102060f150d150c0e010e01080601020616050c030a021c0302130504020a0c0501050f060a090218040b06130617060306070e040b180906010e011505031b09030a0303 74
    0x2601541c0c0004244645806500e44582e5500d4400c40b0000c4504081244d0110215801c466611040b04055080003107031184803004103241e119120345010701c100140910484003059410090b9840c1004a2a40e01080d940c2c0c110b1261120315581c00c464040035a118080c08214840e503220205280000c107074000381100072080a01031810a5a150810840a0b032003a140c3e40c01d00c10620400810903410a940100b00e51149403071f00b44080c00c0a50354050035268241e03050f94502d40e5080a011103844c241c4041001044502130452a0075001d50000301c2c2014a60391081c0300c0c641d500004070321500d622080301d500741c5107000702e0711045440d050050000c0b0240b0160004608a110004019080008065000d860755480c1d410f1840c408008220150020000c500d4200b03202c00e04000c0fa4640b2030034030900031034208000d020b503507042c85450f4103401d005a000711207040c5030320001155250000e046070380141e41d0980d40c03c54003101031020846841040360298041c0710b4695414241681540403070117 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 806394964 1250 806393714 806393717
    0xe0108060d210801120c06050306010c081b0714010801290d021c020c3004031416030f170f360f010e27040b070201060b1b0f0102030c04030201 63
    0x5071340d803603002041c0011000b10b40140001032122041c8045030107000a140d10031030525140f4150300da41e9036400c1d0070b40c0081c15204c090f28520310881603079101c18090030010f041c500340321403001c1c2c0340c4000007801e624041c410183d91840c144509000303902001c10400ba078107144200f0075a202030f00411030009520680c0074114081c03080507680005c001c0360080340c80701d0300054014030219052003420400107450441041c8007800c070890148000c56801c0c05000218046c01882072542180183d0f14201040c070300c650551800070042c1440022000c800708868a074002c20b4900c00d001c030551040d1502e20030361b080700c070000b4030109000648040c403609144c1d40c0e48030302d8680d82642d0300c81011000d45160395201315500070120f1507450301c2544102d1101c030301c40c800105050f81980700d01d035001d0b0003020156095240c0d004018100300c188501118402e0300030304544000c0054528184268105006144420003100361041c40b4400c0e40303004100c000c01425001c0000c5580c0d090010800180e603015100490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 806396214 1250 806394964 806394977
    0x3060c0a031104060f031505030f16050d0b0708070c0b01090b1908030f07050a0209040501090309290a0c05070e1006090b040312020a05070315050c0702010e0108060d21 74
    0x10000d1002c10151070440340a504c0740760003c4e01081041d030252844154021010022090004a40d9000c200040045852030064841c203084908000704c0445160400c0f80200031403600c05002651a6070820b0303000d207240ca000081901c8103103040300ca0241d0004003802111a541c0049800c10842c0d120722032007182110000401012a48401c0307841145100c2c00c0c289410510408407207007803250040400758803c20568044121690000e0455041524192003980d56680307c8810140c00440c48030141c980074001c502d400b40c18503003041031040030380394900c0441c001190b00b8070514016482615010b600c0300503075500c0e540f00c0100060b030384401c880c42500c02c260400001000c60042c0199400e42d18a003c001d40741604548601c415038402c0b4200801314801c01c9010004254140301640156102d410441801811207208000f42c1d0000741a95182a034104003072001030b070300000520302000342030a210f83d25582d0710000500e0303400c0d00321004c0c20981000008030303c1c030500e11403103114034222501d039003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 806397464 1250 806396214 806396231
    0x1a0901020a0f0f091e0305010203040b0f071103031609050301021c110c1203062d0a151b14011103040b0106020109030c030315050a15021510210203060c0a03 69
    0x211403e030485404000400e40c1c2000a000c240c502104072500c0c0a580455104491b80d030b03945450032070344122402d0312100481001d006d0360446081e100c6800504a00c0c02d0308081009061040e224400a042d0811a900046181c070105024800390350003094000d0003191030740c0c50420b03404643c02413490444c01c154034003a035403d23861141c107003564820305e98400104628188000d80c00a1130340040c1141c1c2d842075a000e071600012900264078141060f40101c08982d10a8240074000042519040304412040d80c0d450b10030000d902c920401c80450701c01c03002c1c0c0c1c980e49507030500398000d40c100c01c85c0c01d0080d420800022858106440118015480356101c0d1099a903181c404038200c1d0b6050340b004002420110189020900c281c206440b01d904441e064a45031781e481000403407944240d03000a41d42d441080182c03031869010710800c0c2d54030b030700b0012070716541c60580d80d4010048514060520840504890100001107503a1600c0c1b2555000c0c08440c0541001c0058901b2500304030300c081c0001c1c1c00c0400703c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 806398714 1250 806397464 806397467
    0x60f0c0302040b070f1a090f06010b030c2b0606020a0314040303081603060801151502070819030210020403112106240a0b1c05060a121a0901020a0f 65
    0x201c41c00c503091030001c1400c0c1509170b43e030310401101d403490640302c00710074440354805402071910050041c1c600c500107001212001c040c5509010050744010314444050040040c1a445070781120900032100c2c4800107005144d408105610784003950540c1207034640f14020448680000344025071030701a0715107600401c05c03001c0e00120791081d8040200000d14090218003c5e404248082d800c0716a039043c0811525158000c2908441c841102c1810b81c00f101c01c1d0070030041c1d03548001c1038400340261018000050038800c0300c542d690000901102c0e11801001c00405142c400e001000b0200030541096540341d43c0c0741009801e00102c1c8107240d01c40d43c013105c034010f605401a00410041400040035000b0381c0c0c4d4950b1076240343c3d410a6214070312a1200c0142c0000c0c0da55003409040904904071801d61034203e0b1402000b012154a88400c2c00d5619040034099250340e0044e00904481c42100194170000b114580103034113a1788072160050f1074120f00306000000c0c0043d0060409084190341d00402095a02070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 806399964 1250 806398714 806398717
    0x111030403050a03030203041a070c14152a040b0408010b0d120e060d0c030f1a0d0b0a0b0603041202010b060909040b060a12060e0601080a0b31060f0c0302 68
    0x2009066502c2441c400000901035006158000d014515155020b143d41c49d503201d48400c2168883c00090206200c0001c200c1d895012071101e65035075000300080c400416010450290180908212848040301e800701f4026a0b03464804e680704955285445582d100800301d1203800c240601f00c0700303508008969106080001c80d1040040c0c200c0b8410858864042056490f0600b2603010f0390800d800700800441c000342401180440161582c0001e0003d1800030f1204c1242d4005501304080240072958210315581c003e141207109800507102c1c0c1c4940ca4485814004040e4602d40542000340402003000348a40c0c4810817101000316002071105664100400405100380d4600f280d12042510100380803030312034041c40d03038480701c050001e0441546030140301c0c100d01a01241200c2203030711103416041c0034800380051707401407002500070001480d2650301c242110000034220701c00d440f4200300403890920700c4041c45a15555640081d42c1c0c990f00c50418502804902d40a01c8a45050005030404c0c07034400d20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 806401214 1250 806399964 806399969
    0x120309080f0702030705040e0a110307061719230a02041a13030503032404050105031e07030f12110a02030c1002031c060608010806060d02150c061501110304 69
    0x8840e4074205215500c8002600a000141e801d403044810115003516a80315050359901044014866403105250111440c180864154020380140101f0064250051864055440000100121940e54145064450b01705011708241d103401e0044407240b0586016807440e0107a101e0001504507500d810100040c3d100c0c0d4410350b8640f503044a40c07500070710b910300d000d08004c200009a40d01501c0d520f441d4036184d40c20944401085031003544442e508503210400e90390800300c041d54140700561418000903100c90350100c4241d00c25030103081c0c6005490083c450000916804140303043c40681900703002c0000c9800e86071070030214121064041b03042c1000141c440743c8550040060600802180911000040c001490800e43c0b005102c0614805100100e40c9807204890000042042ca000d13402428401d041c0d2104480348c2003181404200d464200043d0745258065441015086c031828840f40d540c0301c1c06007a03050038000c210911201e220310a01104401009a0754403085d144518809a2070b48602d1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 806402464 1250 806401214 806401223
    0x50a0b011d010801150507060c1101180206070b1017060a0f0e1c090b04090c02060f010608040809210109050c06040803030a0c180e0f010e090d030504060e010e0109120309 75
    0x40100050200030510115100c0c0031b20b000d6003401c410f80c0e6181c0588104031007050120301c1801308803420000034482c0e002c258403c0b00002450b90000c0c1c0100b400752003200c00140208004600149406504c0310401005000220b154081c0008601d046c43d21984181c6010701c0050500b0410070a58800f405000c84001004014142c0c501248513441c165214103840c040611076040c000007581c0040c20041c10050000500c0891601d854400007403c0c008014a601d0402c180c1b200144142c640c09003c07650300980c0304984565441d00c0c100003684040c04010401c04080c4400700c07040c40c64406400ca03003288c0c6d12030011030301c1c410b010b1001c02c0300302d0140e8050150507600c140005044921640c000303032032000d2941400c0040900303282440a0740d42e96500150b03100c4110000344188034500006881c014031b480c0f130341c0c0d4159060180c0340c1511001110001d8081507240d40100742802401c0c0d00110340e071410b00d8020443e0342c655080c5140030b005c1c000020ba48504009100806d828040d0144200d040da10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 806403714 1250 806402464 806402477
    0x120a09120e011e05040f061724041109030115060509010318021c03020c030102030412032c0a0302060609090601030f050a12030e0f0c090c0a12050a0b011d01 69
    0x1598030844050145810003410032a54011101c8420b4402004101c908216582d4680c1d0354200460b584410b012944031600b00301401809800070104a0010f075000851a460b0300b0b280d0718400e01101e02440c40c40c205030342c0203290208101d400c4144200910b10280143d0007406030140103d4182c0b240316940c4182c0002ca107040080c251158882c1e88030140359103d1503040d1100c0304403a004034010720203a1903074200000502d40c0300400c4c903030100140845c0842c110020361139803400359102c00744015a10142818907444e2101401c5415051482c000c6e0003c403400c4c80700c00c042c1c46402259660325400e038140d001d8090040401e184d400c203100107500c920f40010081c012a407840d524070300584140c5409a034a0b02840d0002400181114614040e02c615990042036243c0b0b0300104038103103c14490701c2d43c20343d8010b00c0e4101d02e6484260140364004c00c06500d841c1c81d90210101a165180100703e0000c406140400704202e55009070301260b1041401c3e40c0d0b10045540642c2c00b041c102c40d071006560301090f40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 806404964 1250 806403714 806403743
    0x6030b01021506040f06090905030714062206020c120a0e010e180910180b07020312041103190c060f170a11190806030d020a150506060c070605120a09 66
    0x5098000c0250045e2000c03000a000d680c81070800c0407142d24171401c61b82a0400074802c400d1007200090441e00782c0d41c0760b001d403040d400c20b0064a03c00386161500100c9100800c0d00d010103002e25a81a90021040d080c140c420319207000c0038807420740e807081c0b140c040407d64610b000d0800307501c5540741c030808040203000c0380c140922201d17410a0107503004041c40014031030f180400345106024000d50500b80803071900c3e0025800146442e15020500500c02400c540c0103100c92004841072071044d40d0029007101850b100f03154080d0101c2d00307051320204440c10940b0510b11000c101308600d000801241c200755103200140405a9089901c80000072861181e58107041c0801e26102e0701d64402c0e1000e0440b10365013468000c000e8843da070056103130300242010034030050410400c1e04040c88104190f030100e20207454410640d0b91824580541d82c440b00101d140c1da0741c00580b0948031207044480a0324244101c17078800782d88140080ca0780d40018140743e040d20000303010450f07050741d034001c0c10301c6142d000003191050503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 806406214 1250 806404964 806404969
    0x60b04090209040920130504020f01182619080406031a150c0142080708100e15010504051b04080706170402090f0a060902120106030b01021506 63
    0x4000091243d8099507814209001940c00f64035240c40f0780c0802003902c61100302d5000c1002d000300d0039182c011018200000c100040ea00d201004016403000d00300b01c05200c10341103030040c50001a0704445003107142d44418141c0000403083c0300c0b00090301c1100300d560790310910b44c2020001c0b4581c04020101a014802888824000d4100c0203020303401400e0800e10003030403070010701182070020012480060000d07451040520070b008072441e42810404821200e1140c5003c1e2130302c0d07019614440b01603c220382c840030481242d01942c4008028080445091700c0d1a4482943c46828500f0284101440c00b079038043c981e0720200e1401200c80c481405518aa8a8030040c04090800245942c00544110700280341e0b03240503001600c05803940320010107689090080140c1030401100c6910185c8424804020050303449040640e0700000c50f012001c0107403240c08000000d031000d41c20008c903444c004100e02108500305140c0c0f504848003640c0a000c0e0344c00742d400590710313030400042c000584a5410006181030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 806407464 1250 806406214 806406217
    0x703121107080c01202d0a08010509071106071b020a0f080106140a030602090613060e0a090227010c0b0f010e0c160303090c030b0f010305010e01060b040902 69
    0x4101060105032000103292103091640000c10480300700c1c1c40401c009940d04401d100703000c1e0390000400c49083c1420741c02c1002100340260b01025200c4a0965aa06034510180c855410b180c0b248000c0c042d00c580956401620b5000240911802a5410303000505480d1140709221801c08061001d080300d6114144201c0b00369182c0258020b501d5811002a00180c964560410081003c10004c0f081a401e01d0f91440c01c1d1001548401080300c06454088240e07955410110300701e907030051006a9a000c810003103125801010b4600783d96113905100007030a01c1c0c00607000162050708640f0f070390035a62524140012070080c0c144821000400f200c40c0414041300c0e0741125004001414000e1900d00e061b590800004001c803050103c0c0c21141c00100580e96080003802c1d0402d0707041c0b12980c00c00308044d440081e00f0080400203420940c9440d0041c003071004508480010b590007103802842c900e000308032130070041401c2c4400c85080d80ba0001081c6c4041040c410710060b40d000012103481e11b4503154910029 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 806408714 1250 806407464 806407487
    0x60106050d0203040f050f25051806030a0215091003290312130f05040c0203190915030509060f011a031b0c0d020705031f1808030a090606050301110703 67
    0x45e0001c0b40708800110308100000070b076845605000742582c0e03141c1540c51051105134803440150070340c401c03400d01041e5110301c4508a0100015410405541c44200091500505070800381d0401403c0c480703455504040b00c000c00b81c0c001d040c2d6a62001e11a9840c048046071002d070105000c8a0035000d8803280354018084401e56500c0080c11140c08400d1403001e510309030b1091070a092050780140c0304028100b80740420000604089400300444091708034083c2d241d1044922200307001804c1440d45000d1350042c20b00740040c00406a000c4400c01d0502c0b4090010103080d540c411052107080700043c00b0054146005041c0c07224440c1200104d12103140100351500b014080500700c803900b2011400d207198000207801040720310001400c085000250290a00d03007141c22090080d005010744002e40c09080540c6000308400740d9001907030607081d110000940032034446c0101003000000502400180d140c20240e88c66000d20303070800ca080d944404060032990344005820541e4021b0200c800440d0003190310850 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 806409964 1250 806408714 806408723
    0x3090e0619140f060d020d06140a2d03030c020118080c010e060c030a021507080c09060d090c0b09120c030d0e01110601030f03113403150902040c02060106050d020304 73
    0x82c12849100180c4c80b078202c40748488401360301040300c030034014150142000070b01755550300c13204021098012420004150281c080d2048442e107010504074040ca0421b54103030881c0c0b00c400f18640d00d0340b9000300b00c1c0600b098140d00081813a00341c440c84d800c03c14842c0c07003181c900d070004140315040040103442c0d001c41e00300000e50101c13080c0040c01c44484d0500081c9001180340e03015200b58102583e01d0404a40094064402c00c0900010000c0b440300c500e0444810800440b641501c034207800c00c0d07003006040c021100400c0c0080c0f6140002d5080105006017008640868022502c0401c802004e591003404845455240d402060340b40d42e194010138030340002d1801854411242c0c0c011a11a030300e4080e007a482280c5100030b40701540c0905d0341c0301c00751804009031003001c2c01c5000d0b0b08100f20303a01c205212015911519402c074400004441c042c04d00001190f02002d0100c481a481c58604002c2c540c241c000da00690415064410280c03010840b20b06030391064854504040e03d00318410001e410041040700c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 806411214 1250 806409964 806409979
    0x13150204030b180d0f0906140c012906070807120318080405040b0108010806070f2f1606080a05090316081b01060b0f0c1903090e061914 60
    0x820b8038201c095214030110000c0c1d07070350007064041452034504401e0f0401c3c100440c25034100c0c086a480080101110744605e002c41c40003510750001800703841641c0d00d81c1240d6103000345d92011210510542504a40c1c5405c40c04450450101070046d0b901c035106004214000802803074000400400c00121000c000d0f2800040c1c0078482032070b0fa076046140356825154860701041c108170501c0c2c02c0c0640e500468080c80e08999952400f06641d5803180043e01c24030034460744201001070b56103d41c075030460301c40d140c4400e01d81c030b6110050301c221070400c180d44100490090b5055004109420031440d0202c4031155104150756441100900040401600100090004000c41c01e88000c000a10b40301c4540941c4103155513510305a84850404c5000c0280482a41002020400a043e40b410f41c2c1c0d42040700c800c803543e140c2c0900202800e001c580c2024100145410940070309260f0311040210035648107008281c3d0984880081001c3e880c0d11075040d01d184145c40c40d084c0300a4500340301900c0c81150150158 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 806412464 1250 806411214 806411219
    0x609092d010e030418060302060a0339080c0703020309090a09050a0606180e06060409050102040312051b1c0c11040518070b12520813150204 62
    0x40e095401030546241a640045411311481c01c43e01e01c0c10401704070000c1c082001902e183d0100c0c803140201d100c2c1300280b55441da24400b1400385442400e030140784c0e24500d08105400c800f04c1c1240320f920343c800c0600044c00318000809042c0756404031903400350550011800c0003051000c12580150050503000f0207901d41070282c1c006482004070641c11445503402043c1141080c501d958440a426851154141000c0b03554001c50404900d46411201c00c1d034002c1200c81c1a42003e50180c4141e5000520044d0f03255840e81065078040d001c0c01070303d8111000f000501068404103980d07030f20981c03811f03490314901c031481001072030252910054041c807a6403a14540c071841000502107810032150221052181001c0d089582014840000903001440c5050709001e10038199800c80d40d801050038211800103c180300c5291214104515034400381d419005900d110341c0040c5409030200e0007403039001c00701c0e04040c1c1665030058074a68402c19160000741311510054642482c08800075185212256003080013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 806413714 1250 806412464 806412553
    0x30915042a06031a0109060509150d1d0307112101150312020a051e031c020c06010f0810050a0204091a1504050a0b0a090e041a060909 59
    0x2860307030510750250340301045450400090140c3d9640c840058a200c130f10300c0729a501303170380104083c0140c803a01d1404603104e450754008a816010103017925081144c0c0407401d0303440b91400d6001403608240b5030705240070500300c0f000c0d16640e0740103441009108010107240942c06090400d14400907480c60312002602e8003c5038440f508454122051460401c41c0d02d50510501c1b05a0050342c1920f00d0a100138170840b1141c0e225103031600240303d608080ca07140c032005048248010026900754205461100740c0c24404034110700c009502c64540c490f8103014400002803c2301c144003c14003202c0c18400a064100e42400845008050003009401034960a12002ca8841c059108000500c3c43d10103102420380c08034400c01900300080707080c00c8600c01c0204014000383d110301900b041182c00404180740c0350030502d141030302d1620481d0000b02d14a11201c042105119440103c0b01c4042449010001951107000074010188000c075000292540a0745418081c9200950180d4101c1001d0040303018041002c1c54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 806414964 1250 806413714 806413763
    0xd1a0a0902130903020c03031912060302180a0e1603080306181501080f01210c080303040804170604110f04230711070f0311061e1b010203091504 64
    0x80b4081042d070303a8154600b0107404000084003c0c40440085040c0901540481302003204240303110100324080c0342440b044412900002d001c0c50b40149225040c40f03242c3d041340c1c400035040300c0440c9034509041c10300c00008404203404030040215140651a681540c9480c5101d82c000303018207410085408107000c600f0303a42e801407409090990701c44140792f00c03c40001003207404003901000d0140600300c01008004011076a1900700b03030102d01121044501824403030400f51003944180e11074000041000300b040407120003002500e2111a242e442d0780560a60503954103030494000b0201d50245c9540ba40314500500d03110701c2218000d00215428801841299004a015048910445c0380406001e041908512411040f15903100107103402854200e503e12500c445200160034915480c00c2801c80da116001141d414031b0f203190080744405a0000301303e1a81d480910030300c0c411100e44421008501040c02207038003400c0c4040081c201645a141d00402e40d40000d00304840300d41c029110403030b48106581 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 806416214 1250 806414964 806414989
    0x8042901060f0e030c090402090c040308040e06010306060e10030e1011070204060e040f030507060b06130e0a09030504031e1205071e03050706050606090402270d1a0a0902 75
    0xa50b00c110101c04218040e14039103058180d00e100c1d070070000300c0d11000e1b110041120750064045407850032945803a414800e4603c100d410113009520000f80201d000080e20704505d002c0e0000782d0301081a0341c1d580100315800511784114680c00300401ca00c40386c80902ca90480304c43e00e19400140e03241403000300f5a090454101c2407104e140c481d404070306102035260900c01d1000920082003a800d5900c1c3c00d0352141c82101c1031400040c28440c1c0440c104041c42074a6000a910010152031159250a10407030441124000e08c21b13131078105d0080002489219060084c0023945a0548405040c50b040d5a91054468881c00304809100500c505500c003090311b0442644c072020b51a2a86551819281044560368000c514200700144010031080c0029502030100d07000181c10400c00512030300c508000442500c81c008032960700900125035100b00503605910314040010418008490403c0201400100e40134900c02501c8006690040c01d50180382ca009260711099004001854901e40ea000805142201 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 806417464 1250 806416214 806416217
    0x60619030b160201150806190e0604120e090910050a06060c03052104081810080f07030e06070215060a03020609130204030213020304050c1801090e150103080a021603030804290106 79
    0x24028416086504140c545014541c0602800041d005103e581e13500d61000c2d0000307103200e0248040c0540e4621600a500d80dc0c41e000b000000e9038100003070030750b54485144140310019031604000c5a8000c515209076009c6030b601d40c40d80c03800340105480c140c17082d8215540d006180c01d00c03071361020301402d01c1400c640d00c285c0c482c032000c0b03881301040c041e12010004801c03007980c010000071416002c10360f00148101d52007903011034000f10b10307564030303104a0180c800001c146120344900c10910406070707000702d4000300d448000c0070100015542d80e0100702c1d6807891484040c1d0000010406020f89040141003042c07003400c5030501604e001e51ba540419908450010340c0128254003005000402c0020303c607032100c089045410101019540700d040034445018802c090361180d403040c2803014900c090004101440c50140011b900d50f941c0e003043c0200780d0041c1c580c0c03001402164070f501c2e041005024444292505507031034150b03070340e140c0d92400715511100c00350380000f001c0704d81d50b1580e4840e1100c48601070b1106 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 806418714 1250 806417464 806417473
    0x12030f090d090f09020d0902030a140d031e021e030115030507080f0a02180402070c080606010c0c090f020d090c080607050c1009170408060619030b1602011508 70
    0xc98055041c0510348400070100030702c0b1501000072507403181c5010190703840312400503030310529440355200410b20100c0094040c09520022014031417800b100194048640c403e5a02582c0003810407400c852035128449600f600400581101ca5042d60143c1041c818084540044074006c0c0400101074009a00410781c06c00c03a45012180036606028207034100903c0c1c1010311441c2400003654000100080c03500016650101e0300f007600d0000c41840d1881c10f10041c00455848003282881000002c440c0681d110911580b004111305510a24090070030700d820041e10781c843d5003010300c400003400d507080b10b10300031071b4003880807201040f0f8610070080d10078412031070300250034030f03180e5443d061900090030300c800e000d030502019004080105020800022500c000030303010250f440c040d1001002c202050048090100d0042540d0800103004d50181004aa080003184440340160002402c01d010052400c08000c010903165603c00340060100c05403400046446025550140410f104a0744900f00c260f01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 806419964 1250 806418714 806418721
    0x4050a08030901120b06070f060605131401060804080f07020109050a0b07060b040c0e190911070b01270b0109081b09060a0302060301152303180622020312030f 70
    0x8011412264024004e801448415094000a440c3d40502c1300040c041ea030261781070b08200300c40355114101908005200000f41c40000c09036200510324a0150b204415018002081303c0d4041d000491003203502480c0ea0786401d0303000c04540012380090104a0500c00c00c408003080030358450750104050010310044030340703e40030b0b810315030300380c59102652038043c0d4542800880340950203003039540a00ca0598800311002800c02181800c010a030f4020720549282c040c4c0100e1001e98070b00100b0000d40034071204003442e600d55181c05100500d54a00c2c1c08064030308511641141610340048000200504020a107195503550340c80c10000340380d942d050485a40c0241480310314010448941201094501121484c00c66010031740c0d611060007802c184941400c0452403041c859000b000c40040000c4100d0448940710501e800c494105032802502c034905111807220740800010740d42d200d03602420060b00840354a19074a080400a5101642c041c054074140c00081044070000310301505c1900080b481030314 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 806421214 1250 806419964 806419967
    0x3060c0721050a0c0c0f09061502070e0a0902011e0201020a020f3d090615060c05060117010216050f0f07060503190e0f060604050a02090102060c0f04050a08030901 72
    0x501e01c101800101407210300c0e1036a01d0390000648000105a04201034500d04a00300700201400035032211000104ea03032400305441045400400c00c8070a10504c0307541918050070181c0e125101c60088076804803880c0001070460190b90400141940181400c030f2410001c00f0001e100c0640c81100503000d82e400040307a40d01c0580c100007285004c03407550047d00d840c8030300595041540e00d02c4001012042030801c010720900800480f41d5965031740c100d004000c0c000061070f0410240040800c502040d900c5e00d42c00040f8240148000740640d07038803038054061a800c160b00403510303c010050082c1c46640c28001c811312032624408644134a4010f20042c4142c8d425401503a19110a02002c1c20b91038101d18400c00a01b5000360540fa0010300c00402e15041c0410740842da0014040b1a89511082c07003149400c490050340861000d009190a42e0148503950741c01d01e42c0720607172080c09242401a03005100249980e072010010380460a22a51044e2510386c0c0d0348001500d05429800190094000181e04100d03903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 806422464 1250 806421214 806421233
    0xf030e010234020d11150a02061501030209031015170708070503150f07020a210305280203060604030204091401140114010e040f05090f0c09062d03060c07 68
    0x1029140905862002c2c990108140c0400f000d801402d000c56040d07030b00e01c90f07130b14601d011803032003190542c994a8607841c8400a550307220650326440e071924441580d011030b5109000b107d4a440d4090010980c0c040c0d80341c2d07028010007010803d1050780d0314007040800c034244850505d41010b40103a0003010014181000c5508014541e44024842d5002c0c80000d17600d000010346136580b121500c0d035500d0055540a0003681003035400440140304400d82e02c1d45244070310100d0940c0081c41401da500704100c0d51190184204443e9180e1800c0c02c02c0c2c81c186201d44085091740056a00c44009012907003002e549601050540e50240c0049910951604120100e03903800d202c1c0300204500e10504410a500d08010032020081141c8a00d040220b07500c0301c0301d5107840f030790401e4170b0302900800104080c0c03a1013010161105c0343c00407142c00c6800348420700e04040c605500300600840c801041c040e0042200d00b900080f240c0704090050740c10300280d0046900f0359090020f20f1258000766540750b62001c0344c3c901780190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 806423714 1250 806422464 806422537
    0x10110c0906090402061e030c030f1f0b0a12090303021903050103110f0105091003050106020f060108031b0712080a1b0302100513050f070302010f0815010f030e0102 72
    0x64030840081010640d103150b500c0750055010750301965070345100d0101e00c1c103004040304040c03003941d800824000700328004001035114100c104440101c0e40c50709480c0c0b504210300d09000071800a0281070500000086030010155031030182801c001400d22050540b003a1513038040140c01080d030114110311800386145800d0024002032804006960560741c078080480e81c8025624002c000c5100c0e000704590080085510900c3c3c0141504c840401c200348c0100035120074001d920040c02800b8406035004400602c59050340d070540c001d14108601d03650a9850401304122016083c45000000114401c100704120001806200555034503c0320038005800104003401c00042c8031401020200400d6000c00c03541e41403454920041501c3e15241030504c0028000070002c0c24a01031f000c84a201c3c0b400026031842201d1003030b22a502d80c0c84120b0016140003204482c074090900c403c0c2c800d054039603c61040204c51800701d080c002107174000d0b0300c0f51608a070403500c42c441e50804004ea40241c01c56019490504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 806424964 1250 806423714 806423719
    0x11d0708070602071802031e09010f0b0d020a090b010203041d01060801060c050607080c0c0f0a060e070608040b04150f1e2f0f0c150112020d2010110c 66
    0x284c1c00d01d01718425241020352210035150a50100c08501e8120418001360340c4040c030807610303006904007107507054020003090408071800c40c641218170401d17050840e0040e0a058008007445003584c80d040644002d0078100111a0450004000c00324400041e64001e0040ba040c1001c441d100d076041c2000500f0b00d01042c1c21480c1480303c102c0111000031000112036610507098a81100c4a07100c40e10100f810f405841c80525440c0210342030441c19007000140c1c0500e85015410910256080000c850340310f1165011b013100261030b130f00010340824107864a198101e0300c80e000c1e001d4030b18100310740541100c3d01240c8103c8c2c40758580640070300e55400800310005540c01260204401c1900801ca0310038803040804d4421001244070b441c84c000006401a14440712207011100e944e007500c00380080e05d84400342c017107140849685002084c00000814080002d50740a400500031101c41d403640b0020700d02c40400b031824800200d842116544811030010400c01c004d449a103188c88807652500d080000c10b820050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 806426214 1250 806424964 806424973
    0x6030b1614090a0b0922021e040e13170a0804112b03050d0e0327030a0627030801081516051c140105040e01090f02040c02011d0708070602 61
    0x40540d161031a540451310b4010ba4160790750f20030000300e1094904425540d10500844000780200b00c131a0700240383d5030010501b8403402081034119424580202d0240c098641e803120b000800505a007140c01182e00e000d640d90000d02520380c20020420b82c030280604001500c0f42c0240400c000305040e0359804002e048800079501c002070042030411301e15041005c0d8a521082c92407005040c0a202124120800307c10103000d41060090042e0343d030f40c042078480d0400c0c407020021401e0942c00c600e002100c2500103020305140145900c5a0303025000b14103010f1210100b040302e40301402030340304421408601c070b0f40720303c1c2c1ca944c9003010b00c6090120450f0404031407281d82c0104055030640d82c000d00280103050500e191100112070b800c86041c254002002401d0386450b400d121400044281c190407a08216070612042040c00a180d0131f85100000090a140801601c1c0c401883d20390030503914000c0c03510000840c800c48840c01e10518040d020400d00c2a04061820701c01c0c0b0b0300a00400014003445e00040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 806427464 1250 806426214 806426227
    0x90a0e1f05090708060906010e04050c0c25051003060905090c040c0f090e0a150803032517061201020d05160e06040b0a021009050c04061a0702060d06030b1614 70
    0xd40041300c010a100e104001352000195160300410000c000308401504c100180c1c600b064091055034406260035030140302d445c000000041d01440c0314004100e410800705800c91424050011410f580382202d07050585409000c25000301030301c145840f41c20b1200052803001100014082246d804020340c03000c00ca403820000304102c0d08454102c0840e002d40d0b03180c52141d551030000500170401d803ca04e2449000341e4900107000d400c004040c60149c8002c48061642c541c004014a2500381000800000300b80c407241c031356145401c2c80360580d40c809400390099402d6038130181801d089a00103544504103594541c140105a0360b0700221040340030541c24486110354138070b00064218008d0b8810080c85250018000c16118420b002c0864202d5940344180300034ce89c0b0745000d640f01c01100e40c2c95405030b45820800110050001c140e0b0b0307500d40004c45902e26000d980d07000e001d05c583c8000701a070241910352100000290020308403901c01c1c0b10f064820040c13100003242c01410342005100c8500c00d1482030043c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 806428714 1250 806427464 806427467
    0x40f02090118050a120611040f0806160f03020c0c03030f0d0501080a110904030e030a03050307121a010f230403021908030f0306031507200f12090a0e1f050907 70
    0x131202030700e8040000103441da41038503100010780700052403848a42c0c008034001407810110204802034076846810703504e696480704001d031292198061008002148500000c454501940c01084010000000c1e2030310481204d02207890341c1c0c0404a00000400e0000d07150325014502d129441c05000001c02400c0280c41030b03100d002041c0c00080910f0310a032141d5011604050140c15290030000b005070a9515104a0b41400b404a4000300d58610108045800402c83d08020307104448036001e4a86043caa400c21940c011641208041418000e204160f850004100703810198211400c1840c4001a66107045205001525100f040d500492924210b4240007221020096030b9803d114030358113035141d686d04d80c0041d1401d00601c080140040c029000d202559030b03c01c5807401581e6132042c580c0c0c1c4220440d407880da070701d99645254180769000b100e14003d09006540041559180050151000e103445803801d003031450302656902c0f400302c05500d40414601460028100420045400c0b60040c5410b41c0d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 806429964 1250 806428714 806428729
    0xd030e0604020f06070501092003060f070e0105120c0a0e2b02040b090403030905070501020a0803010b03101502012f030a0905010e0a0f110607030527040f0209011805 73
    0x91240001070503c141d16154402070b00c1e201900b240c0217001e103014030304104144010112074605480c4400c8550005070030300160040c05040b410294402940d5202c40071264240242e4160781000800c204007a0300d40c9464030340e24040c0d68442d20f0700c0c0c4d41e091230401c0509001110250117008445401d10024646030440081240d1401c1c3e0315034029008146c0b0018004201c40e0b294580d000c040d200c02e1105045d416400452a14451801c071039035140c4400041e41c0c0c418442784000e0170501c0030001800b030212214040d43c0c11610ba0200000323a20b403108881841001500d80080060707655803201583c071a00341701c000c040001b40c0105804851149180c0030501d10008010b128125100c00050082000075805050901c41c1c04c81034490703681907480d00c0c1900c800084001d4603a001c507506031107000e150000807580c10030b5154594610301214800015a01c1d071001980388101003000c0481031442d100d50003032000d01c0200100040e51200444009000300d00b510004105130742e5245018001a00c1c0d011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 806431214 1250 806429964 806429971
    0x2e060e0105131e0b040213030609030806030f0304031707050d051e16080702011e030b04061406070b100e0c03040b10050303041a1611010906030506090609070e040e030901020d030e06 80
    0x1030000c0790540740e0030089401b82c4108003003800a04850b04000040c0100d80d403202c0040c3e84250344001150300c1d00d408041c2e4074004030a620843d40c000708400c100080c0c8001030545841c3c0d1904107103007404400d4903910b050080e0308090710701099001079502514005018000180464019680c1c01c0c4a0034100e4100691042c80000b071a00d00d000500e41700356030281496460407200e20007004d200c81c0319000020050407000925a00480c20701c580401c042000300c1d501e401825020785075504003082034542d0032803180068241504071f91842804030380d880c0d80701c0200d4410310302d681000360740e81804e10381780703002ca880140040f0038070b28144018406d95074048102e1742150440034455450140f03820070740030684a002d1621601e194600f807400b0400c10342d20600d160300c64090700c0308007600d640c42c2c034290306550045803a9680855008009080c520f4031000c416003200ca6840c1c0001800401004541180c50f419201c00d00c95002040145c159070341084520728010080c9018401e150603141032655a01000c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 806432464 1250 806431214 806431271
    0x1802030f07142712060103122304080d0f020c0f1315080a06060b0313020607080c1504050d020a0f080a05130306050405100504052e060e010513 63
    0x21541440010030080e80d8a00e50000c0640d07102d46101c50901c43c515002c5481103004140441c8006003048020540e98101c03504004001402c507400403007210180c90050150401c80b84651200c2140c005080151000d4501400241038a5040c140c01a04040d42e11104500315031091a0303e03051500c0f039600e5060a464150b50b46075141c3c03445690031004d8040241c919501e49942e0b280050700130341c009900715620340a040c0030000180c848802d101c0034070049840301c800a601b0101c090050405034000d064090003010101d040810b0810b03040d061041a408a1070b247c08240709200c1842402c1c440d0020402135800240b0700300b00c184c2e071040e071402c4a031074010300068801300701c505c82c1c180501c0484d80210750101910b480c0d182c59103040c43c02400151404e444078455803d900b420106070317200e014060751300040102020700394020110a000c1c3e101c2d400c12380082082c4005129401c980c00f4820241021003501005981010103000c4522801c0340c4002c205400c1c5402d9154440c8521403460518004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 806433714 1250 806432464 806432477
    0x803160302030918061e0904080715060306390315150807021501050d120c0209090c120307081204050f1b010809010b01120207020409080307091802030f07 68
    0x1504081c0d0035800707000b6a03560000550080c00e034000c900307054058481d07001210000400c0b00c103a2581c0600f0074401070402c2d0001c00d250041408241a00040c013801d40c450320540d844031a4400d184000e58209500441c4c03540c1d01c4000843c0100381c1c0d400b84e4641c4110702108421056111034090400707408100c0880140340c0e0311000b40107a1a48454080090541d0a02c48240c0005440c0c0080075110308940301001409802800c00d110103100c40a14100c0d03034014000101542c01d501d0700c2e1900032940e81e1000901813410680350051312010000b600c0384074070902500025a02c1c1042c407166110100f04a15103800c2045484009042d60040e00c0d41114802e4500219a0f80c5180c00e40c03400c2c2c1d580c209010a0311502c803002180742104480131400d16020f0360703003503410b032201ca0304182a1a0483c8401d404145011180994450164090005580020700c00b1034110f00c203840d081c100d40c0c01500c2d000b000824100084c80080001444100060031880f4118614a0519004038031070b00090880000c1154 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 806434964 1250 806433714 806433757
    0x3212c010c150203010308030906011a03010303111608030408100501050d06020702280321080403050a02241021120309080c06090606030d170612070306051f0803 71
    0x46002d540d00022281c0021583c035610b909102400da001110b144000344a001c0000c20180c04003140d904032100c0180006003540d0a44d90b003031701c02001040c0d078240380e403081041000108010810110040007000050369469007800d102906101e45266854155401c1c5001002a82c494448100209410502c016104c07111071002407030401900000420079040c2102540d245080c41d030040303088902c07881900030300064041c50510070344280400440442c42480004020a014000801200b0780c20702c1a00c60781c9001100d103140610b000c110502480d01044c0401001c1482d00703c1c0f0b000a85800503501e24400c01c44101c007441440611401416190051a43e00915000b5089506440c0c6c0c880c40f22601c6800380400c19540701c0040314444140c0c031039400443e0a5003808990355000a0031513542031000824014050340715071010784096000134030024403825640c0c00380800400b4504c6100003160a0600f101c812860303001100c10000c50347c581c00810880c0704800001c89900360b92010461101c2d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 806436214 1250 806434964 806434973
    0xd0c03110f030d0c0224010f06080603102a050301030c05010c0c06050904020d0513061422080f03010b0c011112060906040f06080106031502031b0c030403212c010c 72
    0x1d031b00614078804122400c01000040c04501285040c1c8001c1c00c41c0c1010299205000c032045032069a103150142c0052400600d0000e094010360341c00c441401c04088484c0345106641c1018000b411224000b031004030050040140d2284043d004080034a040c22104803140c41c1c001c0d10240d240b10b4001448400108107009480b5a016140700d4009030408000701d180440d21005540030011013151910300e810700c00000311054038901409460401000200d4409070302c000c2421110a4100341c617420303011b0044403980c0168100440c061b0444a804a444014200025081d01c690706010b00d150303103090081102103407402002d594449000c03502072040d0344030407000c0303001000c40101d50b2514500f024004144408150084012284216203a61182900341280c02c100e00055584010720800c0030401c03031805040300050300c8014100c900790307480d01d40d40c0e03555051542d170301c020800c01914030085001c004030b030404030550341000030210b421a4210809482030300310510701103407070601010000c5c00c070601 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 806437464 1250 806436214 806436223
    0x30a181a032e030807140109170d020705060408040501080717040602030a0209040e010204050f0a1401110313230301090b06010f020f0307061d070f030f0609050d0c03110f030d0c02 79
    0x200c1c1a41d4514180c6a042201e007031760000c101038030a55400521005c4052051285000f0640c1044c6940030700245c810308281c06501c60651068582d4090020502040b0288421401640300700e16040d5038601e4600050030455001b0481c3e41072202c041c0b070b5015420174001c42d17142d010360310000c0117030781e03035560007100c8024002c6401c244c1c0c016103050410103007103030154020030a68004032001d01e100c907141c1c4100324050099000d43c01001b604980d078071204e1b501400d24501d46034500815072f800c2004198074038024200c1c1c4d50111100205084e540e803c0303100040c2600b1110a0150000d20010525480f400d0400c0400782c5034604003ca54009207095620a10071000030208030815203513a41c00f541007031005050781145590610700d045070200b0300c403030300000c015044036040c03030050711170a2540d11110002c040140301034407240d07211030501c00018402d00484000040a844843c2c400c4058180280402486440800150302c00002c450300c1e13510000988070030b441c4058011560b03020602e41281003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 806438714 1250 806437464 806437531
    0x2404021c05060a0b060c030d0902030c180402010f0f0c11030313080601080f01090c090527100507081012020d0b0c0a0f05070804170a05030a181a03 65
    0x40d081a5484a04002000c503141d801403228a00c288201d8040c0340403ca000c1c03144c449001d001e82e20400100340c4a82c0c0c5600f00c52802400241900d81041100005c034080c0b040c20703c908050761054808001c00c540e000302c24055403407421b20704200b00d000654009491880020009400750304150300b4001141d50401c1102c0c80c2c0b82508001400c9140d41c2d6038155580e60080c02880160b004203031105d51800c1c41481109103c0d500100000c111602c1d015812000302005003a120017854407904a01d1400405030300c121029030a000244106c4103910540000c03101c0181c841820444c982040c8241c2e480203070a42c3c1d042e00c007034900300001909688002803020345240c000520030307800c2d981008000c658880148c1184507403134481e5550000028002c0700e4501c1030313080003022074000740400e0201c4000c0c07a940b2039120f585441110310640054440c3d5185400c03682d017035400655100d61001240200d560204000c04070000c032a1074032a5112442c894078000140400755260b6071480780e804000c80f0110f2a0034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 806439964 1250 806438714 806438749
    0x40b030604380a0b121f03121718030a1413031a01090c020d1d031b040e0a050d0302032e05091f210c2303240402 50
    0x90301c00284100040710100300c900c0e1280140f01800516840c0907401c4400010121041d08050381d1841c999240c400c001503280d4000300035181c40400002d0b0400c210000c0550140ca403581c8000e40314043c00c8003440c0c014400c120f11204090300b0f850b49071000068510101e881e051800110840c1141c00726540128260300480c5030031000000b0520070350382d26161200c1c00c200d44100b03d40e0380721180401030341c544004150041c0d001301c080d5041c086c8988405040d10308900c0f6281d1100300f1004c0003a01c0d01d15031052408a035610700345881c940d80f91a1180000710f80d060b101415041c0340e1502d0fa036442d0800440080141500000026400d240400810308a1134612101e0450740d0803401e0904501c804501030305010b0000c900100380300c001e00d680903007403010f000340b0b00703105c0b072400d0108500039246c1611f20000c1c40c0c0c8203400c008000480326001a40a81540b480700f2a48400031400702e1a020240f081b480c2c0039030440030415071107844505000d807804c00c2c00b0030a40190b0310b4030300c0410700031400d80e100c101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 806441214 1250 806439964 806440031
    0xc02012307060506041805030d0914010212010609050f01050405040203040609020a080a02090a140403120213080a020a050103181e1415150105040611151603060b040b030604 76
    0x90800800758401e0b0300580041d03804200364041c4068480150506c11000f0300240d2050000410304da005070000b0049910904003881030341c08140c0028260781207103403841900c00085006204082d440f000d440d008200032101c14160b00a02c00029115124078002c143c02160008001414400346400c00c0402c0e0781c0c081d04006000e5500c2a1141d02d031900744404900c102d0110b804128800303680c4c02400f00317041440315000d0041d1155507003a07c2245046407881d91481e000e001d5050301c1d0803844a0400204581c1014280344400c5104221125540b0307007045061521b00028204602d50380c81d20403540e1a8042c02d958080b240c101030300e40d02041e030400010104e42d05001c90381e600346808182454030a2480b41410070b113840301c01d0302d0280700d00ba82001600241d01803204010356480380c0007198242d035140086d91603943e490600da4048030030494115807007a146500703001d141a41840b40000034252aa6020304040c00c01d168114244000340c00d09d8456620303603144151a8910700b444801c4030315603203582e0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 806442464 1250 806441214 806441227
    0x10f06030e0111130603050c03010e07030504051005070c020f0d23070b0d0b090a060602101113060801051f1d120709150e060603040311120a1e0e010c020123 69
    0x503d500c2d81c3c82c0105d01c000fa0600021410441c00740d82540d0603128805860f01c481e0741e035031400324028013000b0019183c1d8481c58685104110561188600440c0b4943d074502d813003241c500511102104a800245c0240f40d600454008a5164000a6607001c0d040c920320b81c1c1040307005071309071403d000e50b0441031a80c000040c00e00d00c03030100e41e44142d10121055407042c1f150794a13400540b08072000c61199001680101d55035080c0d0300706a0b80081d040c80ba90302c8000e03040c9040c4508042002c2d200381c03c4800818842070050000d441c0c0341c00003090340314110a103c10320720560342c00144800d4080e0150b001940d420b07407000d581c0f96500d060a40a000e005c40403102d0140d070b1800320354060181200d02c5407241d0080700b4045044280ca080543c41008050103480c5152515503048403d02c00f0441c80040900901b07200e0f500c0401c4001c01060711031401e540350765007240200803c54001c038101039140d09110300f0745510350850740c0018000c0c00140e0242005070615065203140511401600320081e00c800001900303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 806443714 1250 806442464 806442487
    0xc012a0c150f0212130b06090c0d060f141903110a0b22060509032a0d06050402010e010c03020c010c080d1d0c09060918010b130221010f06030e0111 65
    0x500704c5550340c22111201500d410345a900b204040c05030107042d400901001410b2810010740c0244c002901140c8245440b084140311401c40f0070681140b0304c1411690401c02c20742115110181d00c2e200101c03144803a011406444004090881c80020710300c0c03641c01071880c219030f0380c02a06001440c001d151540e031080a9008803c1010740004110705001c1d5210300450624890020f50b01010406002003004031b1040712100420040741514a00362030784400300100f075840d0701c00b1700701071140703d207501041c0c070301b040d00c005401411280d040c1410401d0300c0300a074010a0307000520882c895002c0c2040380c00b40001d0b09003080c0c2e07445400c0419400031708041c0c2e20420000401d1001c29481610420782e0281101761082064011041e52a9613220310b24001051200100c00b14005410303480000001750360884202040405001884071840301e40d0100b1090b62042441682d10700d24420003844541541c1401004030f4404000e005903000c05540e920041c940c0c1009511000240070703401c002540390500c1d540c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 806444964 1250 806443714 806443717
    0x1005010e1006021b060304060b030f1018030c08031906060c171e0c01020904090807110405091c030b0607050a0c0e04112808030c012a0c150f02 63
    0xa03070303107901c00d030070600041e503203102043e00d02c040c0ea4040c2440030601d51007000c001c42904094000c3e50300c07503603402508a45a0b030800264000c1407203240039000404040f0502e07400c0710005190310300e50010304040e0b040040d0340145101180c0b0760082103207031a9280c0c0010310841d0f60300302c81e0f00e03140310f4540300e804140c0303581140e80f1201c514465031450405c15805800d40b11140074540c010142521042150030441140201a0541c406031038001400c1000c824001402d030360050100303640c40300b80016001e051100620361500c8510701554103107c00d0402088881da10103041c074010035411126601c55a41520a8200d0a00c0c41d80081080da110181800d103151107400c40c1000300d032000b202c20000980001032000c52481160422119441c0b40590414050f0008583d00a126041848021400040300d1005407401030a80c1000a40d02d07030070318500d21800c403151b04030070641410008101d108111150380103c0c482c4ad506151a19450341c0380d00e0051301101c0b0000100c003083d418a074070300414103034950 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 806446214 1250 806444964 806444971
    0xc140c0708060117150a0f0e0601560d1d010207050607112a040e0a05030a0c110d0f02240d0e030423034c090f0209010902160b091005010e 61
    0x1035485c000500c0680f280c00460f0b81400c1450201203c08145c042802f80b0840507840d460000600d41030940004031801070b168000c0019040041e0342d55103c85002141c02000d01d84044000000c526140c4180c803900d81e500381c010030503002c00030303041c00074005507500748200c030b64488034038404800000080090480c50303c050090a8001d515080b03111690300d00000707211101c03a4120003d146010a0003000700d80801c01c030041a16243c100841812298503500c41240361940980a001030a4041c0d104100c40c40f24988119201e420800d01c9080d4182c4910088032a0200c40d1100040c04000c99040e5604502841e404641111180c6402c041d080d07140045005604500f10705540c4042d400301e2611001c20411600c031b040c8a800c40b101c10500249480044c110300400c80180c41341174118401501c2651709080040700c10301c800107420400c40c01d014540c507000d00b040311815401c01d00e044030301c840c11000b00c05020309010404808550500001d1106512540311020107100b00c0da150f2210031403408054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 806447464 1250 806446214 806446229
    0x60201020418050115080601020c0d03020a021815010e030c041d0d080f0a0e0a150606080903070305070f080f0304061a0102010b03030a030c140c0708060117150a0f0e0601 75
    0x1c9440b80b580024611805042e10100b403020132206110b442c0c1107901c10801018581544107007070440c00150b9a0255144143e48079a00903d044030a500c148101d072511522458512207142c1c0c1801150703e02e60024844841c802e10704034244102440c002858644d400d840290064504004505150030310080172130009524000c4800700c4000c40c0d0102d80003070088400700e0000d050702c000304010203480d070031210740e0880450858100c01d020740c640d00821040d035405202039030b985043c100700480d0010350159001c5400000344d4102803142c1ca000c0c0240c45190f10041a984150b040002000303407040a85002c1200c2111158032032400d803404800a000c2c1e04040310082000d06800c210540c814000c82d101d0303007009009541001c8501400740c010b49074480c8001e0134401c59140000102003014003802484007603100501d00e8074648580103040800c1030b0441840c2601038042e45907150700001e20035625150030418900c05a507266141002480411b0441d10394a06040d00420364800011300c0c607050300c410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 806448714 1250 806447464 806447489
    0xe191503230601080a020306040b150a17010f1e0e07031a03030306010c060b010c0b0405010209120303011d070c051615030b090c07060213080a03090e0c091003060f0602010204 77
    0x25106070811850046a040340010b240c040000c4803409950046d40d00100c0240010556032100b800183c4000a1300941d90343c42d54000c1810450b0f10b41c0170700e4062090313010a0741ca011550400100740b580416901039031024800350b40280c0c1070161099203c0005012100c00c003107060406c0c2400070041d041104801e10800ba114000b100c552902200300d0b805840140c58807104081c0a0b62800c02a14403061170505004000800e40b020554050909100d10b10407000107030745002c01002c00c12503440040c4829156031007880103018000140303031104445100703184008559916900700b180d100c400d13244000c00c18054a14000301000c4410b1812042c0c1d9140c07500e1514804010100300c4c100c0300c0402200d40d0184410000c00ea03450b001a0007421442c2c0208070240c81d101c20001601d11f820200da0207000283c0c82400c083d424141d21544802c0079001c1d0407852485030815505042c0c5501034211600c0c4100511946003846078081d0780301c02c2c000c145090314944501d9a942c0041d000b50024030880c0f010b00c00c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 806449964 1250 806448714 806448761
    0x2151812390411090d0c03020a0b0702181b07080a02010e0d0e041509050408040e060f060901030b1801060f021b03030a0f090902030a060303110d0e191503 68
    0x46008421040c15244506000d4900c01c0100310242440c81948108010100b1543c4110b440d034003035541c00c02c1e000c0c5500a00041c80d5106001c40b05140703038400d9000c0350040c40b042e001a43c8040c00340074020680768000e200d0f80ca0311000c503100075600b0000c0c09800540000e05c3c50030414400058501280e090f0020440143d540701019201d4408210300300006e00000c958840c1e910b01035020b2018280c0202c4c84a90a94036490030001302c8070181c80a41c1c2c1c5680c0441c0c10402103002c0350301d00e580920143c0300a441c01c500c84c0042095402043c42050505440741ca021190f503d40074080800c03101040241e540e42c0d60f44410103481c103550400c121005000384144032020b40710310020700d0100d65002e0010361404540240c2116010361051004080010084001501c001d23540007031405208001e8000641d5481c1d0710700030b0030080403803132015084d42241c1c00556019030840c1404080540a840910104201c41600030b82040b190704580c0c0c0804409200c0c007080b0b0f91507401a4140c0703814800c000b81420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 806451214 1250 806449964 806450023
    0x3150609060f030322080717190309051201091a0a0c05032a0f070c051e1809010b0d060b010206061e2b0b0f01090902151812 55
    0x446030b41d101d43d0594820050f800040d202c1c0c20224065015400d00403c8a54480d034103981001610b07030184521801c008104d0082a00c24005900c3c02d034a54603c1c2d000c071400654015000f00c10a12a26108000d10b05815a1801d401e4220312071165001740344e05400c00c12956103070344d0102c0655070320700040d251a0021005600550407a80180c0c510f030303407125034409214111142040c928102000c821014031080240c60f003010040c0200714400c410200205041a0034041032004806581046124180406400c1e03196402c0d414030404529031100d0903650380c10b00d514050024410400d800485041d182d005002180d0b0200d0441d81003603090310200e4981d1410070050003a402091070301d2501e86411000c8924010325017410000d044010f28610051341203500d004c0c0c108110058580c81c10800070055103011040100d805016240e03c1048502e0954021a06207010860500d03800b800021700400d41c80140d1000c5140e441b4002e00114042a14500c0715443e003401011414450100060410058 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 806452464 1250 806451214 806451229
    0x10f0303050304020d0f0804030305070614060d06050606220906060212030121080f0309010b0a081f0212010b04060f0201051e07090e090d090f030323090315060906 72
    0xaa806640d0241107031126000c00107400b0340b00b10f04a40e103250541041c0c1c002100c010244c0021740c041c1c2c8070705444000c036042680941d002c59640400581000d0708000060b40d54480080a00d40c1008000400340d4610010404c4d0348079080241c000b48100300003090125604084510646204082c01c0c00515a43e520690342e502e41d01c1c3d4505000c140500050080400c1407030b4074024405099034000a81c0e0aa484a09013980201c2038001045000020400e00c0c4800f400f60a520b003034180e0744241c1030340c601440c0584030b0000502c94218054041015010140e540e010740781030640c41c5e00701c01da80d5651203144d821345034428815500031407451a5003141070750041c8605031245000d08088500c050207041c0d00021090010030384800e01c2100c03140410417101843c05140b003030f0a0b0900804034141c04102c003600d8002154007006024110140500000390311030500c054940c1e0041204000c5120b405075910903001d5900441e400d40b0aa04e80c070601042615030042c021f0fa01030b01d0700b44003903c0752020310040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 806453714 1250 806452464 806452469
    0x30303060a151202070f1112100c0e12060403081302090402010f11010e010e1002030c0a051b01050a0605151912020417030d0c09140f0a0b070317010f 66
    0x2481000b044800200c80d480c00c11107906107004501c0d08180390380303081240c010340d40594004100501c420704200407031510340e070110070407070340e03408102c0b09180000d40e00c00d54420240d1405441b240b00003240d07800303180501c05215000341b10a60101e41007804940c1c8800803a0241c0000f01c2107008511030707081171079030880010b402030614203c0307a03039540040d03914a100780801000c002d464024803120700c10a00c0b41459042c000d070700101711000c039000c8080c54a8401a03890303101d01d10400c1481f10300390001c3d007243c080030a1400d1450312030f4180303c8142d8481c2c03a0000001080e5081004000c01030800fa4003180c1580d001b111600002c40c003c1d081c1b00e0403401112030202d0642e0801000100441c0128800c042401d80110094946901d4214808000881d28400c29882e400440d8402c0c450085e03015481980982d071410803015403600820a05024a241c80d00d030203101e407601e245040e91182580d003400b8220300c1004a5031840c0c80c0c50028045540f91007598001d0f00c86c1e40000c00c8107552a81c2d10400c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 806454964 1250 806453714 806453719
    0x1c061d030f09010e13050412020c01050301032a09050a0f11030720030d0605030d1803031b061b090902031306020d0e0d0f0e0f01080712270c0503030306 67
    0x14015107000142155000d081424188100e01903000080d039108421994203d0040f500828181003c1ca490300214015142e403105640060881555a90788201500d0450381c001c21080e08c070040d0307102000103101b00c0300c5000184440e480808500e07072606810031030040e0801c080401800c800c18400f03c0450f042c4085000c040e40c810404215518482d00340880040012404d013141e501c119030226155902c000c0d41c1c1850a516904104200e00d000c0c040611454194209030711181c082c001e009005040500005092054460442a900c4031040c0600b1a070341c1c4c00351040100260702801c0f10719050703c41e03070b00d00001080301c2c001055400040c000d40b4000c10054096107a080304d155030b048080d420580d2032501455590b90500d980f82c9040121a50740101034440b81000100c99400402c4c2c40c6000c60804d024480f00120140240d0380051010340c0309000b0f02c2c055070700505008810300540140316691042c10490b03480030544528a100c140d079010300c03400340400000e40c0c40007416200d02080f2400359 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 806456214 1250 806454964 806454967
    0x13050c160804050d120912240e2a190605030c07050601030b04050c0d0c060c03020a05030a090608090109050316051501060513230f010507050d0507020414090c040c0c021c061d03 78
    0x42342c08a400c44035000303055101001151100da5441d5040c0b03031408119a0728100c00417441010308403a040b0000e001140c80c151b541800d1100005803850a0102c58840c10b401c0000000c00900c90301d0104064174001030f4800280e0b035540d65242082d40c05118282c0701502c2502640041f06164500b41e8184041e440e404074242c0389051401200b540d100110f08010f03000d50107000e02d00c00000b00140010320101c00f09890f8000607906101c00200b82d150018160341150380b601c4000c0c008141d0000940f50076625005410314000102e1030310a06091120341075061903036180b40041141600400600408001400c01c00c50031a541c8209441010181c0380c0c041c0c4488a8107070310800c60400391071030302c802d41c41170402c149410120340d6181e180c0344401c41640d0001d50041401c01c1180360500030140d40c20300d06150440503003005419161103026100401c1e21070381d600c0d40030603122070140c1c1001030050b40040441009250101e980c541c8040884011190f545c03800342c480c0081001d080b54489242c040f00c0055 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 806457464 1250 806456214 806456243
    0xc0e06010305010e072c15130b0a0504120c0b0711190501091421030a12020a120b0307050a0602010e0d0206070c0f0c0f030f0213050c160804050d120912 67
    0x14459407040803c02c0000d0340d080307070b10000141c50311101d01f42071074001c14940f035568145000f44840030b21240c01c8529106810050003d039181d00609440588100d4202009c1c22881071900c2c402c0705c0f0300c0754030409044402094100c144522116210410388096950170710201090a840702d1000c810300406001c24607004090003001d480c0c1003040d540340b1000c3c01030f480004482c803a0550000b508652030405a02c0020b889007a285c1c4a45090002c80700404c0c158200385010001600c214204920707803800d41c0e81c9000310b10056900700824001050042d000d801956242c0400901900722481420070300d00c90224040300c454400101280310311950781e101108044995604074500d8422017003a144e000d0001c002040c4400316007000401144620340946903400c0c3d038814400c0f0114070145500640e0314042c100b203d4411407078225140004850401d020300d1005140c4800c0318011038024540101070800e0210400812503110340c50417605131140040590360b803c44400c0c0700e007a02e10040c91042d112010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 806458714 1250 806457464 806457497
    0x1b0e060f0f0d020f12010f080304180b040603080c2505030601030f03032004080d08101e0320190311010e01023409020309031b0a0c0e06010305010e07 66
    0x342c03070260402000945007403d2000300384999004290503411810301800104140c007949200c9900510007034020707605042c500300340c1006028000d4001c0000c10348030140d00040d41d555511081c0079541c015681034562400d007020310303600d007903c8c0c084c80510841c15240142840400e60044115103008009001aa0a50781ea003c2c81590b0302e0802c5040c182c07140c0003c0c010407403040500380c92a00440d8441e4445252182c83d5103400044001076003030100d00c42c20b0205005c1c580c1404802c0e02c1c074100b154131030180b000740540a103400543c0050715004030018044101c07009180f4081584c8400c4885092603c20954002812001480020039400880d49000c10a5008500c050401c0c1014015603c540410000c1410036034031b51005131956080d5100c848005c2c0e2441410680948541c20b4114154904611700650381e00c584a2140b82210304c034090804120820488481c02c10307840080302141950b180c014500e003c0c410354203c0d0200341000c00104e1881e0403140040d200d82c0403581c0d83d070384540e41c01d40d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 806459964 1250 806458714 806458717
    0x3040302280602210702030a1214030a050717010605030403080a0b060a0206100f081504140706051314061902070503011a090c090a0308030c0d1b0e060f0f 68
    0x1040200e040324081114050208800401c024100c0d900604005600e090162402c603907140300031902c15030140104009610000340c40d24029034007040800702800e405c03800ba40d0070040220f02c051200000810844d0403c540d402c00c5024001c181c540e2030110901c0e4400c0910350f02c003401214002103051000401080c41040015004542000700180445650303003c00c000d0fa100b9650f00015a200030180103c50f59000098001000040c0c01309920606180342c00c0e8403960b213200405034592010001ca401d10010b0000400b07102c018408a4034141d0b6510801360a0360400100c5034450280c03c000000d0a42a0702c40e283c01e001002410280340c80501c1350f4199100b901400315000b1441420b00126107511b00340f14074021030452921aa6200d450f003010441c1002000349282c000c0c00c2c007440380074502c0c0c1718440d5000640f64000c081d940c595a9883d464070b4a4007401d03050207407080c00e001651190118481140b0680441956041ea011231040b0620081d442a0320000c0034000b0100a00ca01807440d000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 806461214 1250 806459964 806459989
    0x1b010302040b04060206041a060f04090212070f030b07030b1c1a0a0e191205030a0b0d06060821090402090a0306240e0f0a05131208190b0303040302 65
    0x18014245030302e03001c091840c0d4200e41c000d08050390104061005006822020124002c10b88030086032600d0003001080c0548c510145441c002d5807150080b41c04c540e500940582d580a0502c00c4419556840e0300540c0c420b520b51100ba07400a20f60004200e81c1031180c0030740c0c1c17281c0902400002c03841c4612815500908419070f001d84000c1030038030503952a41400901c0d18090643d0040118091300a8129182400a11880082000104010b0300f0001c0c4007000d030114003103118140b190300d960780c040444020f48501c15840ba8406665807080303082000c40d61000703045d5541c0034120780e042607228406601c4000c1015107000080c0003848200850310709070700101240d290103003044403d55501d40e580c10688400c540105050b1500c1000385d034000c801022413138024228000b20503854240842c03044c05d5100f010b00503200b170b19122000a01512551509402c41c03981c04105005105c05c0b1860080130104d055540c20b5985220210103100f0510902508001c1d10008001e545840d145a080042c07441002 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 806462464 1250 806461214 806461217
    0x90215120f1905070e01030c05120105060c1504030206150103180b0a06080a060b010305130b1501090302101101060b04050303030f07020a12050a02070902040803071202030903030c0f060a0507021b01 87
    0x42c2c942d0003400c07a680590b50180a0a45421031803000c0700e00058161680000d50f003003001000c0c84448440a0041b129904607841503d1040da241d48060f0461306000407111490381c084205014807040680c00684241300720382d1402142d03148130711003004609a0391405a078220310458030190b01c5c080303001440410380180700c01d90300017070069460020500b0901d055400341d4402d540d54544407250358240c0103043e40000c200c89104214200e81e610011860310240c0240e840610f40100c7d410945d00408119001d5500240b00303401d20303184000020000c190894480c1c415508000b00010310004141c1520103540e0000c001e58195661039010410510004048108521403c100240421700d00302103540e8040366075031400d6035140201d030041d1510125a0240038258070401080021030000300c2178039a8103a0014000302e0316800d5581c1249180101602c0a915020014001c011580002901e4a07000c1c1c1c4482600d006954054104044450480d5000c0168010407040c00b501c0d0300149404d81c42c650305 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 806463714 1250 806462464 806462491
    0x327120c0f1f0e130606080a15030c03081b030a1d0a030807080408160f18061e050301110703081303050f030406051f150e010918090215120f 62
    0x110110319001d00c85554018020400b081121990740c103000910b81c00c2c4204c031107030a010a910300b000040c0b40c050000d01641c2c0e00c59903096954501c402c03100c000f100079504100445a00c9440741402c2c5120b50281a000c40006610b80203442c4202c0e0100c02d4910810294491048414020305000d46a03500201d250b81e111441900110020f0f8901d406015514000c2072080c2e1190704100c0c2c07251608230300000302460921108402c1002e6000002180c0c280c51943c01400c41984956070b83e1005010705421680700a00490640406110314130112030865108034028001d44101e241003e0007441000307400360002d00038a00280310480508041d10b0903e01ca8580146011044507460b00030f50402d03201228486c0c0c1364000c4c0010303845040022840c41543c100d000b00254030b00b41213042c0d4160709001c0a424000c00e0103000c01075a0242c944080188103001c2c130000858a132100300c100038090620100e1144d9146141c0c44c210402d20300a840c5202d5241c4c44c00842502c4002003030490310fa0007022038522511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 806464964 1250 806463714 806463739
    0x9010c060f0e15011403030d0c0302090a0303021605060723100203040b150616030305061c1b0e01082a0310090312140c18030327120c0f 60
    0x40384035002c14581d89401820700d1191011921101c00030681c8010340c40e40c28126a0542d5980120071580301c0d41e5424000240c100005400381c000c0e004c0c0002d0a0b5000b0000c03c000000c0c1600810084044d40d43d450a81070115120310800005c2c0c0100103015081844415041b0b2001d0110410740e070609421000b1a40c040503141204001e84c0e00c101c400b11644440042400304220400064000c8100c0440d4058100441c1348413041d4440340b94003015041640b580042000c90312044190f6185500703440f01d64900740d055013021760b544c0225031144001030303004040028451900c0c3c650203044c0e91008000e003008603510b00103607500c1104d481c0413091203000d000d180350b85660200800c1480c40d403407640109060740181405082c0d101d00719210420541810652944074841500e0941c1c080c1510f01400c1e200c00a2480b5001c00c1440021080d415120014128602c0e22400c0401c03503241129046500c8429102c1d0180211100060969841e6030302c5041c914019140c0b000300007100c01c1000c2d000b010b22a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 806466214 1250 806464964 806464991
    0x4080d091e15061202090403030b030a050313050640230103050702191a0f011403150109090614130308062e090306050a0c030e060103020609010c06 65
    0x70480400d056141c6004400c0c40801c4a4203600071107001104404000320751428075801d9800c2e8940b58000e108090503000101018003175405151600704c00380c2111109030040c03400c56500c0c0d12100d075001600790f00140c000b80c1480d003507049545124020801000304026040c0301240c04505107099521840c000d60340c100c0002c9a046e01d10000c09400c2698111202c02c44401710184090707281c1c60b81058100810450801d0300080d10554070010724841141817031290400600102c1e040000c0c0002c0600501408840b0300c0c202c641c51b0680d0180b070814682030115030201661030034000b003038480300340c0f100c001008000c19541c07203d480c41d40241c001040c501e13403d0070f842100000894488983c00d88440f041000c1c903501c42009940f00400b0754061600a000c240d00007101d81000c00300b0000c41030b014041c101410700c0341c100c0800945d03003c1414011030500820606c0502007802e2124000781c54502050000b41b00000c00ea41201d8010300074a01d480303c0400112400d911454080e60309685500c00143e066 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 806467464 1250 806466214 806466233
    0x601050a0506160816081b01050103030509100210050702011b020c010f03020f070f03120b060412080306030a08070c141f03050c04030c030605010f05180606070f1407050a0906080604080d09 83
    0xc6d2040c50340729950340742c0d240007a07041c1141911107484d6030715000060002a41040c01c4030301c80d103c100c0306001a00740c800c0040349401040c91080b4040d50501040c842c10540540203031074003080c1c0312801e036040c02d540d91080b81d0700c07650a0782050000d50740210407001c581c060b41c01020804204008180742c801d1640314110444107508044002032065403180c420340f0300c00d11074000075520807039030203280c10700d0502c01030101c10620401501200c00000130406c00d5408000b401c0441e580007015648a8105d0305200481020a02c1111500e80950b10200ea0900d00000f180891840440c0010031329800d1840c110001d1800521201901004100100200d841e11140c103005511506000c10158100284844101041e600140c003c00340ba41c9924107500c1c1114440360f00c0281138841946507500c5043c01d20143d00a610007a09111200d6488220704601040c0201070350015280184180c0e034803003501007111458400c680490708040c010a000903002340c020041d00308081c40c0410040040e03107405145 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 806468714 1250 806467464 806467507
    0x108070314130605072d030204030b04080a091719230c031b030d030f0f020316031d0a0209090f06010b0406030605030604170c0a05011a030601050a05061608 69
    0x2003004002c8800200072641c082d450788583c4a2800d4000b07908040004c54a034120005082d49025441c449000304522030b6050300d0042d03800c40f030b51040b9800e2908000c06550b00c805155400980c00950228800302440ca04071060030b400001000401207d20b614680c050380104112000d04000138209031243d403c1c400d411203071124030068214008500209407400040e108514a050100950407540d030b9000318100d82500740741d040101d00034402d01c154500800b646080310644a101001340040f00500400360403400950f501d04000c41d4085180201140c4026903034061b0f240d21819091005003498050141c0011448088034004c2c800120b00b5030418000342c001059000700410204072140d4036009078001010f090b0003411540c14291109507006034045050440040000380410005c2e03c100001b04455800c80001c020204d407004011044d0303075420a55521074865503001240170b10342000800101d82c070060000c0d02c0e1042c06407103401c100499140650b20b440c014010318a1242044040900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 806469964 1250 806468714 806468731
    0xe070c12030b04150f03080a0c05010c1e091a071502070b09070906082119050d060902180d03110f07090c02030a0804150603052b17060108070314 64
    0x240b0055210620040f110209882d1040c056030050030000050401001c10981c2e4115100560324101c580094901c4a14254010b11079841c15a0001025510000921304003c032030950904450007400c045071460094022480308020164841c030180b1658030040903454842c54501c181e020b105c0941d03404036005103400f51006039100042025818080c01400003503c0c6c0124100f00c441c1c10849141c1d0b0b164080d009914140c2c03010b0070011810070110041c0e521480d92400442c0030303001c0f404d0009040d50045c210b241e24150900304086008045402a9181c3d0101d80f085100280216000c200c2c3c41c41403040c00741c0c14851004a000c0d2041000d002900c1450403410041c04e85601d4004642c0844420010f40340441d0000e100b521603da0784a45070315080703900140851000c0d0f0108101d030004040c190700080452240c8822807002d815003400b00000d926a00c4035104e4400c1501e507007540c480c1d01c003d1501d8660f1610320001411580501b6819410422030300c0c0000d8599200c00105940d140262520304 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 806471214 1250 806469964 806469971
    0x417180909060a05160e010e011209050c010e030f0318061306030204030b0c07050604151e150f0e011e030b04050610060f020d08040503131d010e040c0e070c1203 71
    0x10011015008842d081185c01c4101c0f95074600e5148010402402c3d4400c43c0d040120321444081c850f842103496043d141d46d071001c108803a00301c81c40e01c140d40b40b26481c1d00a003c2000781c03d880344180742c04205d655030714281c2c00c040e61a05400c13649900b003000c107503510340764031410900c60f60310303070b00c4110b0151406080c40e42c0780140d881d81141800704030040b008004100c0c407102044150b00140c0d005c80c0c01b0390416840701030a101010301c0707401d0801405840260490114801c8a0608200d4807030300240c40341d04110030b04101954649181c110050032a005075141408000c00402800d080300c003a909200b0301e102105020162a581c684040f4a402c0d5800d444640c00310040c0560303602e21407042402042c0d24101400b0701110008040e4450740b00803590410b00051000060038403009100325900c00c80e00e080710110307150315000303010005d211038000886a80304620021030005158070b000c0b401140c000303600450451608850860408000382824200300046d803201c0006003407080e1652a2040e40c0d00c020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 806472464 1250 806471214 806471221
    0xf04060c03080f16030b131503030810030c051201090510020a1206080d030f0209030f0703050f1b0f04090210030506031b0f3001050f01060503041718090906 69
    0xc0480300c0c042d0034840d042d072003002400841000413a84030b800d0b800d079060124501d00141c0004002006005034101810f00700701c514102044c603542840d05507031080c1c488030700b980c8a1a101da640c1031f03c240802020f016038600248030524010706e9030303075401000a001042540040d40c0e0203060a04134010407910719008140c504e0099045121012004103000007040814540b40129070781c1c008000c540410b155076010180100c04080d01240c2e0b6071075011703040740e240c0600090026135a944620040c1c07107a0052071009405404040384000d5003801e0860100b0300c1c05940020400b140c0c8040c1d1040e0f60242d91f0741140c4005072103086190074081225100054145001400e041c2401001c882490003c0100e0f10050000c0d65030640d103140c000020346070f400e072000e03a001003c07641204040280502443d404003800352182c054101d40d204a684100039007460344c2c2c9500941c2c05002c26134000b000000c20707100000781450030001401007a00702440c0e44008814401c04900c7c0a00151800300c0c1641011040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 806473714 1250 806472464 806472467
    0x40603150b0a020d0302031512060105041512030e011106280b012102040308070803060112061d09010b04090503040e0c07080d0c0309020414070e10120e01020f04060c03 74
    0x10000340044512a40b07400010300d402502c0b0103001c2e4100d4149075022021862002826000044825003c0c00c0003c9042d07041040a580c0c440902c502403155007031008568a5101d520130420440d90100e00c0c50800b825140d40c192492040f50400e541000281092035140314010055240609648625511107901d0783c01d000d10002904585031550394201803001140d640c0c0029880c3ca20100250713031003da0150f555000d4060b200d113510242040ca00854040280003803c00114000e1100340c9510441d12014490f540c01e0f91154410090000b900404040141400350b0f10258448803000000079040f9070340b1300140c100d030380c010300680b103903480810140032241480b0300c40b98000104004c106c2c140b507155501c1041c103105c0c002c50001519190328070a09907074001d4000c1c8036085c6e8000c105216140d4201500c0b004100308682e807500103030078000401c24030705248482c20442d0b03000c0e03078882c245291030030480006081d4408040d02159400c01007582c0720060040600041c11817a42d80b0f55078086903090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 806474820 1106 806473714 806473751
    0x50301080c0f1f2a02060702061831050c03010314070e0a0b130e030d18080403030f080a1806051f0e090706020c0f0d021203040603 58
    0x41d6010b607541c20803d4058400c1104e4400100624140210441110f201201a402c002e007089000b004d410400020018150500003d080c42d45c0100c022505030514056a268040c00c0303900c42e110307183c000500d039107102e07030201c0c070280301c2d5082200c80603949210610005185468402c403500c0764a8040c00303130034000c200b00000b020446c9000354070403015003485e2880c0ea10441c1c1c400303081c0542c0c104d07522a52642950381001582403118100242c401801c244c10038400880e00a1220780004009500500c0914481d030b40b00441d012001303401401e42e03000942030080d201d09154602c0158691b0540c400001c0780c001c42c011480f038580d00c61440707080c460200c2c0719044100b28800881c40a5224000c0d5004000703900807074820350380c0c4107822070311b8100710702400340c0c040d0004c2c2e202d00c22441e01c2007a03001d0640c0000c203600c26209400303480515540c815405040801d031203000c115154a039100 = true := by decide +kernel

theorem cover : BRFrame.Cov 806294964 806474820 := by
  have h0 := BRFrame.cov_init 806294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 806294964 ≤ n) (h2 : n < 806474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
