-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:27:38.614388+00:00
-- url     : https://prove2.me/submissions/a32e9d8b-0ca9-4c36-a962-a3d487d90629

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 362410071 ≤ n < 362589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 362411321 1250 362410071 362410109
    0xd050a1205210103052d060405100e030f0706110408100507030c0f0f08181504030e01182601020a090e090304081b0406050901030c05010e2215 63
    0x120303000b40000e00100c0d0803602e003074200d0301d00045040c80a110180c40c0da8010300c0c021480030902201ea0b000c1c40449014032480060b0000401d092903802c0342d040d215908411041c0f041819603000344110001500c1c041c5185c00c541d5042416035001d003030800761281e40c0d52158015400b40244c00c070f80150240781c08903042648660040780250000b124600f00103401d000c019412240200c9200d82810310640301e420380b01140400407214075100410742000c805910110288602d410301c1100d6190480044108561a243c240035191311080d105180c100115004054400c0d4510400d01d003d403402885250380c211071441c042c00c181856070100504c44d5100007694012180c002a41c20210303112000e41c2800d99641480c820745034011881034010315001390f10b07072014403610500c41c0b02c00004001c100242158480020030f4580e9403d0b04100c0d1400c20034035051015681010382608800ad04540307440c4003503420f0141940360038946801380141d98079888654641403005840c00302404140070305a810301c1c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 362412571 1250 362411321 362411327
    0x60301180b1507050d090608040b0603280b0f040302030a0e0406030215120606030c120c0409020a0801091b05070b06040e010c0507061404021507030c060c05071b060e0d050a12 77
    0x80c401155184a49204000b0803800790711241c007100c0f0103481b0b1007949e9540d5140c400e0741c148010640366043c080c0314202c168401401c203084580c010b040c0c6215204003924904103e00d140c0261010300d021640d0401c1100080d40042160218a198030340141c4028041012801410a40c2c100030350211440c02c1540c44140810094012203006034404441600c42d981030004038801a03900004a0b00c0403c860260f500b5134244564000040e600c51524040d61122103000701c1c1c00440001b000141d6950040104261a00410040f49d0040340400c5c80782e2001c45018005108c1c050000b0102071401c80060260f5a459024149017002c00c1c0082c0080301001800415580c080081210000e280080c4545c4032000c1d010b032148079035030140400515030b4200a03020303500e420a1070201d04000c2401e0b414800641c9500070341c070340c1d0401d42d25040d0325801c551900000c01000c2282401c0c1031842c1140402c00140d00c40101c06011030295180c24003a0598100103042048a45014100e000c0b188506030a15034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 362413821 1250 362412571 362412577
    0x20304050603011532090105090904230606220e10150f08060a02030606070602040f17011b03050604090602270d1109071b0c06140405060301180b15 65
    0x1ca680d076200c44511400d42c00401d200d00c0e945d800c80700300d492100180d0b0741095030050500020504001e4200b620321000501480d608480884420050203003100090500f00f403001c0c0a80c26000140204d8500000803d1000d22000d40302c002c1403980b070891004d00a69a840020081a0042622400c0c45000400c2d00a0240c0b12401d82c6080b09080780003460100b4501c1041c00e49a440d8080c1400e5240c55080724040d4102402c0250f0140f420003c503400592248004c1c8000e00d0040ca46000c03803854036407611001500c24103000780d00d9040540c0803190341039807140e2031803034203032410002103940390280454001d01d50044001e10461000848120401c80008980082040390380c900344101d40710000d1040e030142c0c122000b0901e0510710b1780390038286016144162b220185141c04051311100b400c1042010903074800540340e00d07051280511420303074031980403850b4900e006150b030729161170100441c5981c40140302c1d0007400d001c610300310928980d80390000044407900034216440801c40468684841d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 362415071 1250 362413821 362413859
    0x5033c090a110102010e070e09010b0a1e06110c010311090a1d070207050105040b0f0d110a02060f06030d0c152c010b0904030507020f090a0f050f01050d030c0302030405060301 77
    0x1100b900d040070303940d0b105000b400c401512030030113041e0062900c0c1c01214a481c2c0601308a015548034038000c0c2040e16407404070402845039021302d091201c44100126000300c6190051000c102d1303814000f100f0201c0024250040f204286400281a01c02011600890040341d107050b505c028078445c00103540e84001c100d40101c5056103400714054407004010382c0d031180340e4820316001c200c040c481000640000e001401c000301d00314090700d2a04072040d0381c4500b1245282140b015000f4040350796241641e041048a0b400440d18107440d0726824a80f00096481d151680c0c10801c00218031401d10401007024900d0500840041c0f091040740e01d0f8810304048000516002c007050348003004040f6800f0414021060071000280101c1c1e0729807036a07203089a50b80d006030300a030703000304000314941341c642c8a40b409117120b8943c02c4000900340f409500b49100795040944008030254480005104903540c901d43c94140c1685810800d0000c070541c42c007a4154040c46c1e01c0750f80c1c00360000c0000502d84005007151080c803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 362416321 1250 362415071 362415083
    0xa060507141e0d03050c04030c031e410c130f0e010c02060709060909050901090515010f0509150609191e080d092603031305070605033c090a 62
    0x60751003046c24005d9018622014060740c480b800204003050111889002060112012030000315140d1290005240b107d4031685080d03441041c20b980d01809070f00000d1008980002184000244016440d56680e940c00c03020304c03801449580b02d40344401a404055040005a030500c0b02c60100000540205040080c60000d4080e03400001e9003248108820f0003580d010740c4072440200e00700079154008010040c4401040d65030340125001117001008800c007041a0b800c1051140e604100889070811025032241d0b0213606018103104400124214000c0c0c01b00094501c6034640002c00b0004100f581c0c910b015042d40380048101240d03644030301d019600c0c0da00c0360715412160180e4504c0f081d0ba0f5010f51034403200015442000c2480042d0485544590a0340040303c0c0d070b00510742d10083d00e420f5500c1903940c1201c0041b08000303842080014424400181401d05101e411442d10038a100c1031004a040d41590201003070541c810000c60507401c41200910880320400186070010700d05907503140c0b6140641d03035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 362417571 1250 362416321 362416331
    0x1a01080d09060309081b0601050f0402130e042f01030b09010510080901110a18060905090f0406110304030201020a0e040510030303020d1d070608060a060507141e0d03 73
    0x40140006800921108107948554126181c28000c800a00024004076500c01d0b0030403006844004400100b121850110054400e6501d00010411342846921610380581d00500c40e100c9040e01050002d01250000d09412803190740d00c0c509620340d2014540b0000c904c2c0c03600b05100b20b00d003203001015014180c003a00d0030071034052086c0c1044215071003442030a501c641140e100e08081c2d4403aa000903040407030000041713000000c100c2c1c0c11195030881c0409100081e035407102d8001d6a802894032000074081c90404482d5141480082696040f0040440e40381204c00c138042000c05c0f405611000c80c0142580d802602c1e0f080500c0c00034045e610160010380064041050440309203410311565004443d20041c0420b8545140e41c150b001c0c0d00708500e01f0940f25500c3c4541c04a102c4030309400c001c1d8503c120301400449080850250a4403c094107136406100c003008184401030300402160301094002682c60714044540b038a162801c0e1100d4482041d000d4604c91071841e051000428500002c6e60f43c0742840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 362418821 1250 362417571 362417579
    0x101d09010e120a020d17010306200a032403260c070f06030e060610030914011b0f02160501050d02091003020c071a070605180f0a060501080c030c0f060d0501031a01 72
    0x1b800301280d04040c0c003208043e000410002e130341607002c40c0d040c1d02e010305120300b1030500940203042c0e0341160808102090300c46e4414500030f40d420081e00107003107130050880842070650b1034003c0e0900002444c20b03110727410003400301000d80031042515440c03007001084580c4191142140b288101281c441c0700c01090070440e08132841800030403094880c0f00301038143c40c09030480210403005044860340540380c1520640c40e030003140c5028010b88180302c0e2500008030742c0b916088070085c8224101e011400440d00080d901041c414a8401d1100031680c09103000b0341c40360200b092800091142162159000d8685500c0290254064000d80350700240c4c0015240b88642c1d907101805944140b8580c2061030f2410406c450002e01c441d8000340d000584074440311002000e107040385d1324180090701417102c1c03640309440e81c3e0100000b07401200c2c003500c0311b4005806070954400109a03101401c101c0648074010b86a1640e040d0344800f07080e650440040a803c1c0030559590803c2400e1000d590213802c070007246140042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 362420071 1250 362418821 362418827
    0x4050f010f020c0906060405030f070e0f150d020a0b0d06060311070503030129040902030610261b07030903020306010b0a0503040f020112050f0f101d09010e120a020d 73
    0xd01c0245080c1c000d81454002d45040100500c0001d22440e4010000c1c031002c105a1010440090350f00d41d100c008100741e5081807214544142c004000c030011400b540b081200e0500c2d40900307003080c41825640c0d010b401d9810b20004207880c1e1560003a419161010494601d04121078114800b101e11a490800c0090a00480e0031003a209803440600250b01c20001045540100d40300c451030550303003400c0e4410202130000d041c01c09030701070b9210840e138503004418880c0a1030603060500b844d0556081a04560002072141c40e414060405e80c070202110f000005001c0d068803040008031040f00e6a80749954501d10310340039240401a0100384d01a00c41c00c400032494000d8082103540148403600e5503401c541c0e80d9961a120100d081c2da00300d0403c1010081140010080d020f0320780598101c040140c09850400c2c00948030340c50041119140e1401c040c03003040005a07200c861100e0300074014051446940c0c1001441c0903140148003075101744942c01c80c01c0c00c25012030b0064901540a5800e8440304d0744035020403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 362421321 1250 362420071 362420087
    0x7200108010509101e09091a0a0b011e030b0a1e150504050607050102120f1e041713051f0813030f0509010c020a03080406020f0a0c0618030606060504050f01 69
    0x28004039000c0813000c0c05421400c025134082110f84500c0c100c10161658044c0d01039a000b89021075500c5d0185512890860076128079a500094413281040100341c40c900003400061081e800c410070004103200344040703078420b0300484071b1840040c00040040d40d580c845000004901002004c22041100c004181d03c08242c0304c40504144640e60281070500f841d04011060307001c034208840a40d03003080005000b07000c5c4000c843c4a0307050031044240a1070b010740d0100f41d05402076284000c08078124100000943c207a4210a404140302042984484896141494902c0c0f44e41000f0750084004042150072148800c00030301c04101c03a502c140303494594a017001614005480000e02084464403030340d251038440e4002c1c140911051400041c108501d03004101c40f181c050b0020b030b40d550f60002d03040c00683e80400c4000741c2c40281c44010081d848542c2c59288a00415001d4102001120040c146166261940c8003024541040b410002140d4072079002c3d045900c01d100d8140200c2410194404d507600072581c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 362422571 1250 362421321 362421331
    0x50d0816020609060f0717010909020f03010506090a2304060e010629130504090f0c0605090619020703080d061e05060a0f0908010f150e04020607120507200108010509 73
    0x141069105d03a2800d00310000300404040c1000380002c0200c001c0d64016a86600070b2901c4000010004030b14010701c655000c151000324080d0b030420081c000301303071104415503a2048440300e000409e61009180c0800c001204010340300c9100400c414802071020300d51211045469560007000883da031481c0360076251701d0221031030392008140040d100d8151b42420062034072164800105010540301c60006003160f00078031056400d50303580d0f2184010400c0e08901d81002d04000d041c40390401e000c92002552500c250072620322903090030001c055540703008101c580041c40d4030030403494480c1c003007510200080000e880307000e03c075100f4070104031a910001e43e035400030f545001e45807914007035403500c050720000f540d00501010030000010004000000307100b8045d05000c00c500102e02c03070014032014400015250059a4560f4858043c440140d640381b0031a04441c0e0f2040032189580690101620240160400500f0340c8600d9542100301e52224221441c100f58262110252641c0310300502c501c280046503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 362423821 1250 362422571 362422573
    0x11a03060c040e0703022b05180a02150403060504030c120306140d2102010f0b060a05070b100f03111806130b0f1504181802010305070309050d0816020609 68
    0x201c144019004071840a84c07000749402c01500d003050345a41283c48103502805001c2004940d140c00902a200b40640c41c0c01100100c400042281d580b070310300382c6481e011007000b80304643c000804845400da00b0140c40c01150001400c1045103014100500181c0d207480d000c992617070004542120140c009e20442c400d45611000807000303501044240110140180c0c0c042e100c2040f080d0440854402c103c1c005240c5849330f600114202d51081494401d41d41d440200354404c480074020250b07007076407190941d000c40b80c01c542810f40588880d0300c8404480c80d2600008400711000d08040144140e00e503074681c40340e0b0251007040c0b041c0c40e440c030366015112047d500f07564480780c40c0340740c08a0803419410070400325000a200b1102940d0b10030010b03070305032400b00500c044080e001c1000c000c00c1c03461010310f4001414070b100a200310803c000343c0d03a40100d08454020b0525940340c01140801d88241e0058003065406030890300401b52034100680b42c0402252048201e1205000780d80d410b901c045429400742c50240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 362425071 1250 362423821 362423827
    0x30e0d14070209060301141f06030b0d17120907060e0f181506130302041d0303070807030f020a0e3307080c03030f090d08042001020309040e011a03060c 67
    0xb078208164401c01a055907415034950110a1b00f203819002c246010b4001c0c00032002c18014801c000c00d103a410141e1000c4141442d0030280c0c44a6101d410501c40e48584c015020040512811030460703903400b03840032200e4820340301c104000d204100051803e083d500c464a6a00311122044200240820005501d6401085014240c55150038025580d174106210704104034800021002280b0150400c8241c1c3c4401129198200154109407181c0c6d0b0b2903442114111004040d012071465a900c03000c1e00781c1d400c115008001448845c07181d401440d200d440c3c0f5105650b10140c2d0b620080c10304a80c0c00c0c682e44903400c0d5a0440000c1100301101c0c00c0f5810203110041e81c81c4c0c1094140d814103821107142507601003070820034061030344c0d0b0500065104a0303040c016003000b403c14005461808904425200601c0103030f0040c00045200e0342024120300c0c610401ba840f00c852076500403402d50244070200c90b0468240300200840d40b4064000b4504300082056900c60251003c0802da0388034015164241c1590b420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 362426321 1250 362425071 362425073
    0x3100515010e01020c041a0909010504030f050d20070512090307030602131a07030f0c0804051c05010e151012030c0c1a0910030504122001020a030e0d1407 68
    0x180d42c40c0024200500596221012904c0420103035990440a051458041d491800d06071070507003d003a0f0085400e000800040c50165800b42941095850400138010046004103c0701481d4011306111010355900711800d0310081c3c4090a160000d9404913498000e080082c034100035a00241d682a900043c000c1c4610391964403024000e41c41201083c403042080398000c2035a440c0d5006240262072804803082c0e5500590400401e0241e0a072661030810005946070808141e554080d5026904100d031020380d0410342c880700540078150088014003a50800d4074125601d500810701c10100c10250038000011b80d1090190b4071840070f2400307441c1e0450a420181e01c0443c0c8100c910100641c41807a100100c20b03200c80d080d08402240d01e01c54180ca01000031030381141d0030410a50030514070241801d215504055035011001003101da0613804101015511100c54500540b48041044c42c1c0c42c0219680c0c148087c1c0140a03101c0143d1001c010f10650002a543e14400c0712118442c50849844034242501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 362427571 1250 362426321 362426327
    0x20703030b030a15091707030c05070e0c030109020a0c02100201020405030118150507020703051621021503150d0b10050a030c0504020f220609090e060c03090f0f06060310051501 78
    0x42030303001b035a00e04121150420a2160030004010440c0640c4640020980c0d6140c541d140a02907044400f25030181000d1019a01e0410252810740b0103031540580c80710110701c411500c1c2880000003a41c01440b111f180114a9011b60081c4107450041e0001c0c440c801040c02c00388848031210701c000b0501220203040f5980d000b911303442103400c541a13205807418144c0c4c9031100c40c07600405a0502e0514501c44c0002c001c80450000140d0503004180301940500b005074000030322a48603911150542000040011582a08040c08504000c40245900400c02c458100a140f000f021204007242d9000a03034041001c0c41c203550301c041100d130300c400e9808407241850203000c0a904000c10b00309507050700780321000454484280225200c182e00982254035480c05100815584450344416030051800b05226101e02000c210540c4c030451090344255280c58006e1494600007200c44801841d0254846052607400045403850242008904032201d104914404c64100c03031096031020801a10180d0219940d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 362428821 1250 362427571 362427581
    0x6060a020f03030106030e0601060e1807020709020d0509101103041e020907020c01030501090c090e131208040506071805100c060c030c110606100c080903010609020703030b030a15 79
    0x114415103101c1015100214a0740e002070f000030b000300b41c40e00a140c400341000c01c44c1314014070580c901580fa5036140800324a5080340c001480d100e10300c903440011a114002c00c815001002c95003001c559503d820400c0c10010301e402d9403100682c0c001d4050000c60303110a4001c20843d014540c100d6451074075160f035903812203a507011440322a1114013083e000540d482c000032910803e029000b815214444000040880301d05811040403640390190804036164007007206825030b048080c07a80c031a500d6660f05070011850103100200206090b41c2e058102d56030049100340240d100354100c44980e03c401800f501d40c01d068102c1401e008050750b100f04510303d0b021600d00b2080b038281c1011600c2c181d8644401c1c09440b0380c0501030010940b601440c403c60b40c2d009611520352544070001c0d20b26800c0550000d004100c00038003d10400100c003488800703001c6034000b2183d0b0a03900900810840755076084890180d0003a04055021a2421218088900703000c121021035546c0241e220700c1c4220042d500f10000c05d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 362430071 1250 362428821 362428837
    0x609030c0510171e0c0d0c0801181a0d05030a0810030b1513050405010b03160b0909190c020d1101050403140c070302030a110405100e070f030e1b0a06020a0b0606 71
    0x200c101100310100541c4c00003541c0660f10700c40389590707141c807000c9040080d13640b452060410000c00c4001000b00e64280000202c040c041c140010aa03c15069103070b02980d02914400c41d406a2004440c00401c48000001d208187e01900c1d002c0b031035660b4102145a180c4a440043e04ca0810007000420700c040d281c510311708640000705002c80901c1e589003040d0840e0000c44049030180e641d161102218541001804501060340c1c215140c00f600f03100214107107019020b100d13401008044041902406034048103004c80000380340c2041060541c12000b942d9502c10310810000c2480da4618804100040c0100740c410358050311540489407003d02076607226407207c0807004050040b040d0100050f60306000d02c0e11034502410b10208254104401c1000321803022b819006010782d0208101301a051b00003103540d101c20641814041c2400c0c0a1090b8040c0058121041c014010b1032480d0011420701050894026400d45107074004584542003680d584c1c601c1344c1d01030152030070003002070749901c1d000000302522 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 362431321 1250 362430071 362430091
    0x312080907091e023402011d03120c1f0b01050723030c030415030603050d0513031a090d0f05071b120b152e1106010609030c051017 58
    0x40d0b03c0032095000301d8011414009003803400b50003011081d144510545094000420346491307008050b4006444a113180d4100740c400a0a01d807400c640c4c0c1c0c1c040c008120011680301c0040d035590441429a80c483c2c1c0d0b4038266030310801e20840c00c2142c1030007034410411940c1043e1105850302400d42c07182e05120245402c4000c8428000c031100d1a054020b001a20786c00d40c2c500001c6450341d0406540e0b95000005229440402d460110f0800115400088200342880c041c1010f031f40c2d544000040141d5603011b034101a00c4000350107034040e44d2226007004944038a81c104d0175507400f803466803802c41e031403400141e07658005003091100c0b00201d0401e05811a11080c025800345410f0341d15a003101d01c104400d81c041c1d0b0707604c854804114860701741d110f82c19500ba00c1218489000403a09000c407035807208050760711050381000458074103080d019100d01321801383c0a004560056941e00d50051580b03642d400200c6031060104800a480d050010b03c0d4405c0720544c1d140e000c039000408104529408008200303100f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 362432571 1250 362431321 362431361
    0x5010f1d090a06060b0406080105090c0a0c030c120914030a0327080f061009110403060b0f0a03051c02031c11040b040320060c1b0103060b1201031208090709 69
    0x422130710550300209100741010b921145080009000c0b128140e0240e40100c1103034041220301d40000040b0744c9400e10b10b0602c0120040329080032a20800c1801c1c000780030240144181c2c81039070300714250f1421030f90b101c02c00307003442c904c58410300d519600442d8000300070030410705501c0c02100c00481c038949104c401d281d42c401d00503580c540c00c9262000c1d401c6100e05940009041c05541154010100c02404501000b840301c1482a80031a05130b120706d21015022aa542100d40300b01c3d903d501140c82c81190017003201d14500d860b410b00d0b0b500c1e100040d0107241180c1507414280d42c083d0011003581e20400c0400d40542145103a8100e01002c1e1150705008403181ca402c1101242404440010308051401685038440302d000b0001900701124000a2080c4a02e80601043d10308240025420b4080c0c00c01c08082ea502c4a000c10040e005044e040d041301841c6200458940d4680307500c00901d41c102c074003680915805510380d50050380d0900302514028038035005840240007200c1103030000858a80c0006031000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 362433821 1250 362432571 362432573
    0x9010b010c0b1b030a02030702070f060203040e0a09151a0406050f060c120c0d0215011202010c020406080109050307020f0108060619050f030108010218010302030c040e131208010905010f1d090a 85
    0x3c03984e00c02c075425840c9550100900c1581a0f04200b039501808168070701c22055428804080e56034001c07485a039403d00925400140c4c0c00c400e642000c4052548a0b0754802e411585a014001502ca50b007a200a04001d40980700e50b24603050298400300d0720054201ca56917001d40c0d00b480916031100388182814460030b408030303410440d1900100b4113568060f0160800c1d0b002c807031000707081226498424604083d18001070007004009110072000360740c24240110302110350b10218000c0d0440e5400b4800c00e51808045005001d030110060054500c221207410050010400544801e103003070324a00c1d044501404486105049010035a40c002c6c0903042150078140c4403a8038200c03da10907040034181d030350003060a000d0010224507500118400f42003c0d421480d1460000ba070b1402180710301c0380c50101c0170021030701c00c01140d00d024150540202582206010811010b02104000e2041e0301a0503e0b181c000119043c908a0782030541d0a182e4070350018602000d0030745c2d240035028024490b28080c2c500c81074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 362435071 1250 362433821 362433871
    0x90d0b060319030f090602011a0405060a05030709150e0702060c0711100c0b0a060506311706010f0b030403110f06070f2a030c0f0c03050a0b09010b010c0b 68
    0x32440c148682e130741841e000890000201120015400030055a042c450410102003100a948607000426100040c66546100005840c11500c1e0b111640500030044c0200301582940c00001e0046c0302410070b00e000036911505a07100c40b0701184c0300341c01600100e0200300ea81100704001d11400380501c5180402e05012000100709810781c1050300e0120b94038010400402004400311b6611100070a0200600c47c504408a122032050840c1408041c486c1041481c0c4488881c1c1325610001c0e0401100300d038103888003090340b1541d82c1c00462815900c030702c0c0d00005071255008803030b000b500d80420821f41140c407256004d0710709040b04400441c040c0508401205444804c100070346c851003145ea1504100047d00301c0103062864010006020b0700e00a80464181e521420a408a042e80c03500c0c00340903c4080c0d003820004620740100042038103280b040000180b000004145e5091401200340e0341103a03d13507000c00c3d400c031010b0711201d50205280b8246400814070030940e040d0300102e8218031403c0040303402201d03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 362436321 1250 362435071 362435113
    0x306060f1e12090102031519081b1516080904020903010e0d0e0307050105040512010e0d030606020105010e04110d030e0d080c1605030604060506150c061605090d0b0603 74
    0x1280c0c00c41c000320304503142d601c40c01c25140e040380c00b48000b186103003011000302180b40102860180103030380075101d0194010582d0f248000500684043d50320b00c991808140d120601610b80716441782c082d240725140c180c04403204071104c0721522404441410307101d0741d5198854004061450348070b6030902ca2600310351401c0c055042c0183c02807028040b801d00441004d049100201841070090740042001e1101da41c100003101c050b40c00441d27801600108401d410740c058012110820f0090050701e20040c265a05604400c080c4c4005400138446aa00c8400300b11f041207007101e014040340300d40841114a810010008025240070340b40c664980030310080416580d44400b0011030b50800c0008280d10350007c10b0003245105150481c81070f88071450840001d81d1804040c00c080d008070350703a0020445654581c00601c07402407105000b2074840c41c00040781c5440d0901100d40101130b03100030b0350900209200d4001c654183c4401800010f10b191503444070b141d0110000e21254261044243c4d0380346220610303080b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 362437571 1250 362436321 362436367
    0x1d040e0309040e0c1008060406090c020a050f0115140420090a0909081b010e070303050316021c0f0c020607080c100203040c03022e050408070f05060306060f 69
    0x660360356008074184011100740003074140703050308100f08066481e580d0042a80c04441d1a25005103503441d01c9000500404540e07200d1580245811540c21030750343c02180000c1024020700640d4a11019041410709951007a0541c41c40d85048070801d0114080c44645454226000781000030b40904205041045ea10301c1d4000c640b10071030100e0102c0092514139a180081c00e141e60051000d4070083d1380d1790020f40603480900b4501d00d02d005040c4400c10003544000305884007101101c01c8280d0f6414080c140741d000fa100748043e032118040300604140002030f00203103003411a2a190391b6000a0604440c404446800f80d0b0400113030104990259590790b0207042c04500030002c031a0b5942d10360712141d00e040c00c07d081919015005004000100f50220310348411284c051760902c0035483c410102c50320201d13503100d801c1c045000404014130705503404406001036a5000e000c5600d05512400240103400c814411aa40314004100103402810314801800000800c1070f411400c1080b101000c05045440c100c2c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 362438821 1250 362437571 362437573
    0x110f0a0b0406150e0105040605060c0c0f060c0607030f05010e040302120c0c04020403060b0f180402131b0f1b0b0c090f1c05070603050f07030b010e13090b0603030a020d1d040e 77
    0x3005203c1b40c030741486228020b000880360f0610303000c1e0360244507440300e680961040c81505002c00700e02542c0c4900c422183e00050503401d4035510f24281101074010092609100091494a4000300308400c1c3c0b440c04174040c5805400605170340e40c045405103640e91058580322098081c82000441c1e58842c0d0004c0d00286100f01000301b04903826500380b240c400241d1780074510584440c004c0030745800200d042e035a007254040e1400c2041d0000011010040d0011480712601c15111440180005d544111814102c00c000d43d2801c0150f1013100030200303608041600581040a480301041407060f51000070072130b01c000909030048001030307800069032004030048094514640ba104000c1081130038001c03280601070750300b0104224140b24020003e0500014981d009160303407080e04a0150707010700c02c020480040244010001c003100e4144170b01516803100200e40100801c40401c404e40b4000c0266030000c0c0e143e03030040245004400c0201c8010502c0c2494540303e900702001c0e50b100784c8841c060700a901401702c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 362440071 1250 362438821 362438849
    0xf03150a1a0405040f020316030c020309060a1101051006050f03061804050a12080705090103020703031d0109060f0c0e010f09030803070806030606040603080301151e09030201110f0a0b040615 84
    0x24148130558466003000010540f0400c108460b008040b0f0340500c50303840d41d1600103003000c051002a8070314440c1003289a441074020502c000c1040e8054146442039180b08000d2100d9104d651001c243e218081c000d91010070400e100c81c600701e4000c64080d65200c2001490a94400480500240000000e5400b50303081d4006141e0482071100000405041c0301e890b1034207081074900010014114000c0011150401d82c00003980014140709800c420710300c0d10305801100c8104c1d000c50010703009040543c2d0480318142802c0d110b030820001841200d855011a40311b244104544800441c0d0b2203040c42e40e070405010b040310010000c202d50b01301851181155442d103400e11300b0182c0402d441c180c40240413602c200e081c10001d1000070015002d49046461034401c02c00c241d05903910903039040d02e040394251016846841c1110a85a00030028401c1f00d000382c8888a21052401c0002e80300d6035a1451444150301820f6080005040094019407203809200001164001d00882e405542c000b680314013402c02c1c40c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 362441321 1250 362440071 362440079
    0xb06041505030916030302150a0f0c020304080706031817070501051003020108090a021008070c140c041103150d03030e0607030b03060115082208030a050403080c0f03150a1a04 77
    0x10410030300c158040c00018035010780b0f0760742d009546200c0794103800714248e11702010524544046e080720500740c009203010302066180540082d50b030b40040c41200400d00c03c10340001962406482121701000000c04180d40d43e003000d4803142510310661009082030507081050300d010a0081c07080f01d0043e10092001000540345000041641c000901259600c0d00030300a0f0390010f1b52010f1035900045941e04249030329a41d0200191942034001e0009000b4503502c812094660b0b1000c6101150081c0440f401c0122080164600c0a50b0000f20b5840f0f0308601c400609200342c0c030b132109004064900c07901d0041140b08401c0a10b6003000c0c0d081e02c003400070948031b0022040c140b50600404bc05000c0c84400d10045442c288002050800007804008404815901d81d00c03000000c410700304001030f0006034090b903908105a0060003410121429000602c11342d01241c2580b0348402150841815407180c43d003035441e29000880c403a000c6124031603000500c0701c03000544107803620402c080046901c5545858a10b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 362442571 1250 362441321 362441323
    0x160807031d0f0127120308010306180807030c050313090209040506010e0a0620010501180501080a0f0b06010c15090519020a06050307090906090507021c080a0b060415050309 76
    0x422405140b04014105840741c0c6039034480ba01d02c00350700d4401e21201001c11503401600c22040039400000d001c0910750100c009254200201c1030480e403007500d00b0807280c1100c40d41800d0800c1d03001d8000340324240030000880420700c1503240595850007041a2817414458041d103040310009a072040034000d0700465603914901e070911480d6800324003800c00d00410220800000c4101045000310400c0c000182810700540b640d0301d2038071414200c0300000704001d503107400c99502d48094a00e170342000d00f41058000310795200c000c01c02501065001d4084180c0a4007aa2141480000104640d041040d44101080030440d0361144125920034024000f815002c1170429908000080c101094101220310001d0700680340c030b0504004544162070b15584a440307100301114049901e5218030901820507001003903840d03180e8000c42c02900301d9000c4030030141406c559520b0215035a0149004200081c0002d00004e84d603130882040e0010040c001ca15140d161406010b1004468003001c00241021007085140c1c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 362443821 1250 362442571 362442617
    0x910050106030e0607030902151806070f05070b0702130e0c0a030308060f060f09040c021e150a050907050f040e01020f0403031412130602040801090b070815090a0216080703 76
    0x425146c203024480581c3c012400100c0c0711202c40c0b0100900041030341100301d0000100c5d040c5000101100d40d03e03200ba0130800007480d1440c005071041d0254020006e98400c0b034400700c0c0d2100d40e01900500d030181e154400c40c1c00400340c105110540780140e10006090f80d80c2c075000c10020314440e44402c6107d00b04034092001c240400102c0303a001d200c04100c10140e6921034010740b11040002c0314007080030586240b04904000a81c0f08030b2040c1807180744c0e8510544c1010800c00540306031031030342c0c0314940c1e5007203812001d03124207564510316031304071050903c030904051b1503d05040c4406080411035100e40e404043c226441100503040800d4049800d1007090703482680c506000a03186000e078103000c40e0380030788098000080c0a5026001041540070f04001c141e4061b02c00902d00711000304240d00060422118070641196060005080741001452142103201040c4031100040c3c85030081d43e0f60055031000035805038581c11403108039000002d001482010042420f10720a5030740612107840450004500303a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 362445071 1250 362443821 362443831
    0xe010603020f1e090a0b040303030c0507080d05042307050f010e151c0609050f070201051513201c0203070804080304020a0e010618080a0f020105030910050106030e06 73
    0x90300401140d007031032100b4000e855800c4690049094484444148116948144010303217422011451000885900d40d6026100b240d00031b44081c010300315402811940e070700c541d0714000c0074404c0c14402035910740459881198050302c228541c0c1c40848031306400741584183c4110694180d44450f81c1407000782444010a8041503003828286600f1000100140501311321a0f260745400740041107007824800525110109100c1d16201001030b5522803106002074881103c411003908002c102280c0c5861051091601c1103c943c800800280c08800c208064840400c80b84e01216460701c10080181d0030040400010301440300581d40e4a01079241c021181c103080fa18403184451050080102c081d800040f19640141c1c00307403200b60340e9a1076200041900030280c21861040300040e0022603056049040b000e90040c0803210304a0140c2e8030300640d45d5800943d0002025140502203000c010350007a8003640d044020002551b00142e59111132404550090f4002c900194a55880c4d007000c01041c40000d07002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 362446321 1250 362445071 362445077
    0x12011814150417090406030f0201020d0e2b08030117070e0f010909020111070f05010306081b060f1e0a0f0206100512010b0312130806010608130204060510090e0106 72
    0x3404114140d031114000040025000039049074642c07104018403c100e80b58200005c3c010042035482e800c12032000d44120004a0161180020741d0782280d024006035590044028004600101c0d10001e8090703d03039000c0f1601e0389854030107800030002200d020255018121680710003415420f01c411032458554142d100b0551001b10005019401144952990540e00b00c0d400c0811841014401290400c00048c80a4a14021980081110644050802c003180d20036a0706100d43c41e140d00042d07803200f503038000c3d100300141c2c0b0042c10a00e90a09a002d01b0100e45400d490034144801e00c541a83c0f0450140020191600d00040004100b0780045117010154218030080c01304d46070400140b1909a0103000b03541c07003212001590f10b4500025048400344100c05402e940d112950600060703d01d81008080c0004074a400301d011407085070004e0040c1c129007460740c0e0340c0055241d0200c861031011522106036000b54440d40041004e45030314082a0444205d5510441600e2500a0040f080304060300700000b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 362447571 1250 362446321 362446333
    0xb0d090f060213240c030e060304030e040e1b04090303060519090f0c081803040b041806120b1b090a080d030e0f1e011517010f060b0d0b12011814 64
    0x282d210315004c5040c0c20078500f40b03811010318600b0140c2d02801c08100341a40007000000304010550b01031000f00ca100c50030303502846420582428180c440018a01d0000500c410000c030406c2031900b030b00329030b00c0a03029080002d0420f8803540400c00da04c1d031a002c28a440ca031424010440c800040c45a01d4100384040010800c1900c0c001c0d0081c50890081d040800000c2c0040e0202c18015050040340c00404002d00c640e40ea443c0d8882d5a408026100c80b00903004d5860244001030180da012030f03802400703510912172941030b52805004007070000b0004482c82001010b10095141c0d8440004050150112800409014510010080c01c3e290b003d0031502030350300f000801ea0300303140c400951110301b50003000c00051000603600c80c0790300400c90007a03461300f003544460740052000102c11090080c0502a03009102c2ca40d030a40191054a0061080c2036491004120250803840390381c0c000303164103e0081c02c510000c18400740c0d4600b55178641031034031144440f00c0e113014100140c40d901900c8510010000c1c0803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 362448821 1250 362447571 362447609
    0x9030f17060a06030c2714032d030706050a05010504180b060d06150e070207060207060818030d060f1412030702040b0319050105010e060103150b0d090f060213 70
    0xb03031018400c003020715032600107401d030850260061a02200a0703480004031140b00d1548055500341a100d01c20b02e0100c074620400582c1804070300590000481c00942c04185c0c6c1c440340400000f010f1120101e9a03000900420303000500070300507580694280750000c5a95414502004100d5601440540903002c0e5490040000f590b0008103580c0440101c0c0c18005041e500d00700100a8001c10080c0003001c03544034004030750200071506003800f174100d9a00700d80000381c441405980e90145405440d0100e40082c001800b0005a113012500d540010f5003503909040403810b408082d120950404020111240b106102e0000a0402108804400c90b05600b03900d4031a440952603200e1f40b030010f0700a5443d255481c02c282c80c20007062101142c4070401060207011814103c1c02058203018030480200c0140c040b80696109000d03002441c0304050440342514600140440684c2c030800503801625241c92243c0301042c841d0001e4408e05018107800740c1c0c0c030749a222101a061a490304041d580740c1500011342 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 362450071 1250 362448821 362448829
    0x90f260307051314010903020f011214040302161a0306040e06190e010c051c1d0604020a230910080102040f03140604150b03030405060a0c051203280207050109030f1706 74
    0x1c40c0e8040d1034240427407840d0001214502c42d40f11062240c42d041440107411150690301441c81603000e07a00780c2e2005041ca910091464a05209042d44954504211600d07074031310750b000310b03046040200002012a5001102e5081070303802c84045404056880c0249012402e03070090140451b0911b00810542c00c507102c01030800c2c0620100c00d028689042e100c00010f40c3c40fa4880d0f080342130000417003901d0903d0840b8096440d9001c0741c04a000310551400040c404400c505242500c68213814030000e40707a920360a02c01e60300e400510b080c05400c004840052214000c0c8014005082c0c175aa0080140d800c41c145462000055040c0010175403000c41080041104030070041940c030301802d1701041e1000b402c00000c1ca1030055400043d800030000986908250f00038601c0c0c60034a1141c000c2e40c0b00d040c280350840742ca501048825008403000d400c4141c0e03078841c54404400090381410001810302c469900c500742103c8648100310041248055030710b41c031540000c051a0a42c003500c80100740c916208001c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 362451321 1250 362450071 362450087
    0x41a0115030e01141f090c0903030e040912050909011a1909090c0302180904110402160b010b040303021009170a021e0c0a09090f26030705131401 64
    0x2030410141e8a000c0c80b0b0b0b10303040a4000f1410107540c80c044403001d00746025003140859100c8040c10301d540c19040001034100150003031142c55200350b2201e200c92031454900b179540c01d8604000607032144d81c0f034566000040f039184466444165030f54640b9128100307407040c02000a410b802a02c0040070700b0b004101606144001c07070f030a10860042c480340220041c0026039910071282c0214840300d0515035600c00965241e406020030048840c14a00c0300e1000400b03000390140281d40150002c015070989140d01d04041d002000d040310715036094040381c1c0c0315488028607400280c001d03ca80541c0010200140356042100045200784e4400402c00d100b40da695140003080000d40350601c0342004100e0000c403500a0090400b1101c058452032003040d82d4490040d19501641c2100d8404e4a00031000304c1c10000f54400c01051580c0460180c11114190b110503d4140080c15007280ea80c50041d510a4034407030600c0034501801d465114181c4411400644c0120103403203800c42da945421050602c18181e030701c0121 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 362452571 1250 362451321 362451359
    0xa0803181c17070605010e060f042306061b06060109050a080601230d030306051513090b1c0303060801201b0304080d1e080c040b030916060305041a01 66
    0xc54104280d48041d00b61250040c8480a84030f545030a00010740c0c40c2c43c0e0781c410b52040100b114442c81003010241004211001c1c1c1420408810408029418407031880a400e034000400400b21410704207007001e071010200300710b9414061740e0021014000325580241042002c0c1c0b2044403002d1039982466102c40c0c0e04c113014410103410300000c80a2020100c01200405041400509000094441070401401901080c8900780c054020b040e984500c1c0c2c00e41e0300550b0300c40710030420345a058624226118014040002e503c17030384030800700581e002e14414201c401490610035200442d006141c030034245e00b158010240b581840341003908920115081350104da841301480b520301111100180031951650280c0d0b0040f076898890819141003480d004101d00c13421018180480315000321681c402c450746101664074690807101403205110304d105801c050740d804600803040340e0b24000b41401d070316070301e40d155440b00380440d995801340000d0244184848140e03100e03503034040340d803540341100c10300c002044c80d10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 362453821 1250 362452571 362452583
    0x412150e070602120f070605090303181216080d091a0703020403080a030c0e1002071404020c0a080c010908031509060306220201020c0a0b190309050d080705090a0803181c 75
    0x640d4800725409001503d203410b4007d141003040e440c000007a50703641c1d0310a5580300e103032880741000414526400a4000701100c100c5030311508140c2900c0c1d001d040e44654050440b0070318030a01a6400e1a0042d01c100e0044502424100e20b120500020000400310003404c040205401000180042841d09080b1a6003401500e00050380c0050040120b40c2070b442d14120aa01c0142c42003c901002c2d400036050068407400d0307005c2551402c00340208422442400c5072011160080c100300301c0400c0003440927141440c0420b0011802903003036690282c103076200710b5402c40c1900016190130302a0510303820442c1c0c80792040e0001c080509000700d20102c0c0e011040c1c0005076066201ca100f004592081c403481007015000340501400766180c4409460b02c1c3c1141481c07800c217140d002400541e1a120340642005690494098000d03541c8104045a021900600781018001c080285000546404a410004000c03080256031595260301c6454558510aa041c070700c43c103840484110507550070400c032092554000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 362455071 1250 362453821 362453827
    0xe041112100905010e040206070516030506060301060e06030703230319080106080f150d290601090b12070c050d0e03120705070b07060b1906230306040b060412150e07060212 76
    0xac07400380c0c07030003014030300d8194000d08413100002004000104c0b81d009200c101d0080c020b240e1280071280c0030b001e088036500d0341a8462a410030204501c00900c5214034074161082812030100364415103580c1c17000c0565010a4019201d1252080d4001c80540c00341c0b150380341503111800c0c10f003203820400d280a040c540401104000011b4983d8685442d845116884168949075009040300e442d00300d0000c4414400381e00035440020190740c403808030700098130f40c002c0d81d090520081062212003600300800000074480300400443c08101c082003003905084165031442c5a031100017052508003a00c42c030310820240000e0040d9000650045946410b035000000070340c3e02c6000c1c07410142c01400300b000750250010305a100e09950240501040b000741c03190758a480703c6180900c10740040b0300180880030492140305101003401d610f40ba401c92098454000c1145e8100354542481540241c44080f00b2548190700762100c1400580070700030800519541c0021b00001440c2030800b9451701841d50018507090800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 362456321 1250 362455071 362455073
    0x807140112112104051c0c0809150d05190c05120903040f080a12020307080301170a0c080d020f030702010906121e0920100e041112100905010e04020607 67
    0x1060390021496030410410300e1012510b14a043c44041c0e5055a050160102c20b10407280c500c11100c20000c0309a5803404150b89503152241715411010b41c895000f100c0484c024040b0342c0e51000b51103c4800303d0400201c509020035404030f500420012800260708018580400a8026003500d80500610800004a030b95088a140c11480360750484140c811305c41801040814000504010030351141c0c5000421075500d8000382e980f40035100d401400c01c03500300018400b004405804110884c03c5404541c07040c88143d4034820541641d401803030440d4000c0211125150f41000040929810140913514006403070b00001d01c02d03082801060180905060a8041c0313299551201d21442d1000c60700e403526141a86084015048880e000e4a000010042c0350542880c94031000200c0d482c02000e500804046600c207555000003500310741c2d4060f94400340d140440481d074008001c10b158402050230a0300d402c0346850504407150700041901c80c40c280050005459032a5400d40082c1c0448507a5211402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 362457571 1250 362456321 362456351
    0xc0203121305030105010305010207022b0206090d15270c06110304090921110c010e1206011214030f03011802040305031305010905060c0c0d030306031b0807140112 72
    0x10303800700d43c0641c03030306000205104043d40601a2184201c03000590161900398080c00c0d2402130a0a0042c06400300c803082c01407900c507004107a40c43c40584002c1100d8041e071a40e0250007500880d080803e038407059403940130400c64048038050001807198500c08036040d19100e412680e40c0c0540001e10a44006600c0d00d542e040059030000c144007502442586580d1403d1400d583c0f1072411200302d503200b20b11400b1034500580600c95590080c40050404044d4240111074195000001c1d58219640010b0740f1200034050100b18081c010002030701c01c0e060700b00e20380840142030440a40300160014041100741020300d40c100c2e1704640c1c1324440410310218000e00740d0002d10507a0300080c058400000c0d000d9000c0126010f10084071381c00d880d5003014a54a070b09010061261940a140640044124844030b1403c4039520005a02078a0001625a01da69800701a00e021442c00c1450910340401004910070400c5188003510002c0320340c8040e01c21800020380545a00380000d2800303034941c848283c080324 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 362458821 1250 362457571 362457607
    0x30904020a03110a05180d050c0409060204050402070f11040905030301090506031c0210050109060602070b1308030f0c0c01020109110904140d030b13020408062206021b0c010c020312 80
    0x5642e650075999000b440707000d060b40d8442c00700c824200000c456241c211f440c14504281c1c400f500300c00a000c030440040708000c001c002e201c808884d410782c2408081410380f9188080c1268a1146548910301412400c007000b46000404030a480b41d403d00030341d08000b400200c04e6a044584410300480e4903116000002e0601c8240808407080410301960700f0700055002030000d03c94500200c0c01c102590f04e8112140c240ca0140c043c0b140564400743e0304000318112680144065940322183c0c1040540b5204400d0559000240a4042c48030115003c1c0040c1424046a0081380e0240001c0100300030540d02c455100404142c098452500640001c061061645c00c501e5100c084609444204211030700260041181810081c016001c203c01031501c81d04e940708840554920000a10160b40c0344455120f8014021400b00e28030320b031542c2013000007a01030002c0c4c01e50881100d841c11075603402a074003a01d0078032362012540c10800540303848030150f100070070300150a8029a90840d42d44405d5514585501 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 362460071 1250 362458821 362458841
    0x10509071b0305070f2f01090b0a09090c170c2106041d0f07120b0a0504080c0f010b0f1914030c1f02150c0f0d111b01050711030904020a03 61
    0x401c100204404118a164400781080000182903e06d40030800210003003039426055035011800541c4e003030002072184409411601000e1034407024260710354690300240d4200030b04000100302000012013403403402c0d2030700350b03844110114020b05020000c1003110105080b980120fa615440001060231038071160810500c1a460759038056401d0a00103d0541d10008400d40c503845008070103000c120103020140300d800e50307a0040c0f0706140a03103a4106d004d00030000a0001c4408010030422020220428031440281003480310000455842d61001d01404000078400380b4480c1c40c007411020354070004400030310309913082c90700b504080c04d4907003020919201c00880c005078001d20302d100d081e40d4107071039400e504400d0034650b0035140701501c1028204400c19007950b100f24014418410714515848440140000d04501c500c003040c46545815560269405201c80c400140c0c05200300b42a161401d00405401c0881442c1000c0d8600c00320390110344030301960001d244500d40000d00044464860781041c5144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 362461321 1250 362460071 362460083
    0x9090302121c2007050607080a14060405090c0d1212020c0307030c060b040204080124080d0c06021209011b08090a150b0402042409180203092503020108010509071b030507 75
    0x7200c0d13500749981e65400c200d80d800002210301000440c03404050091200e1140300030305a84480d00c800c801c000190100030b00301e0900744129012181c041e6211003820701c800d0b0150000203140100380b0341c01800d443c0d0002028a2240c010807034081d141d10000121004680c040c5003640c0070000c18504030b00500040d86ea215403182c0049004549848194840901c03030f2151205500190241d0400c40708074503442c032800c0c1450f0400410355138440e005600c1800164482c020040c980720444040042c0d0f002d06a4501c3c0f41690740702d400c0b43c5046031031904142088228107100e2420300e0651005030383c8114488004092803000d40100025054a4002910505005005645850f150981c50301c1144803442c141d0325032103101070b510b00514014501035040d14035500440c1c0c01d580300314600b40065800034200c03050f03611940b480301c24480b0301140b02c0c10f910500100ca010005145000050002d44180c0185214103aa40e00b0700c160b00e5006156090340040e124000c4215107100c4c10300340c805010f601c00240070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 362462571 1250 362461321 362461327
    0x10050d110a0e01030f0902030616021c09030311070b090609011b060b130c02100b01050903010923060907050f0d0b011d15013609090302121c20 63
    0x72500500c0000800c0402e980401c000c82d075505121080d10614140607415420000201e107004124051800f08211140115030f082c0c1e0000c0d03902008070017017500450000d0985c035001e00401d6800300020308080b01500c001c04900342890380c401980d07c14480c0d140c1c8140000548008241d01515001e24941c82c41c10a08041c0f00c007070704011006d8042011040c0c811003208030303110112249032242c912120041c0c2c1c000d18016000300300000c001c2441e0200c0c14184807040c040945c40da0b4090141c980ca0612601001c55542101d00005130030212407034103045590000e004210391400002101c41c11203104941c1030342005200ba0208000e10f40040d401f811504100d8000314606018000c02c2c200401030310700045050b81d0700700c0070400c841009090305002034030050340303484480d00714190030040991400840b00700042c01500e1254802c800c1e0300800d40142ca0705501c0702410340500181c4d00200f940c0f41502c1c40d02040d8680300704440c0104a40a85095481400c02ca6030241c11130f42d8800b4959142106907 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 362463821 1250 362462571 362462587
    0xd1b08070c06020f030a0c0803060d05030703110d0e1507031809020918070806090a1803020a02040510030c121511070b010915050d020628030c080610050d11 69
    0x40740540c601411000d07104807040c84009040c0041210309880b00d99a6020803c030180d6940603590340b01074000740e480364001e070068007c90000d00060421a100c1d2721050840c0301103514183c10590012000002e01681c003c1d25040c07502c5003117103010084580031849a0798121842c0c02e94000b050862888110000000e0200f90303069564000e00d03180c4411500d000500481c403e1406803000211884000609888086281402d1003120280c101c03003c1c031f4000c111030009183c640c900301d0340c05e0002d400680c030401440c0d0650400e8444c0e150130504c1c10000c1c6512501310707280c8840d20b20b01845034100028801c1804024000159140704040200c0c0c0410f0010b1320b141098a409600400c40640f0b40791080000080e10980320300c101c00103c80341103000c002603841d0400300509003044940c2641c10000c10480c00f00c80f80c000082403004112041d000300c05404040074010200e40400d01e2450a026606003800190b070744400120980010500d0425036400c0d00d80e20b060080c01d10041d22414201010440c20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 362465071 1250 362463821 362463833
    0x100e1506042414031c0c1a10030c0b0f0a141e09090907050f04020c0c03190c0806040302030324091801150f03020d050a38090d1b0807 59
    0x5402c8402c2c504000254820f4102059207030f64960300c0154001c4014003c5c801c089000756881000a07014100441101e007202600098151044030305650342901420f050080080404020740981061036905003409400740c0002000d1142018502c24010100403039102c070b4032071900b00c41445d02e0840400c49180040f10010030503400c18a40070f4482c507860400200d138060b0000d82d00d41111001400c101003050103905200c0298060182c004071030103003505030b510380e4030b04000385007441c008041c4100b0220400e0601e003450010f290000012a000172040c040461750000680e0b40010400701c140101800b00d02c646504403145240d003580040310541040641c0c0700c600f00d04480342003070a0003803121001055040030141c1181c040c000c000b00301414180b01505022070102c2403a0703c11003c44170709544a031038010503210400d800982809400395030080c10803010700540c10b24489640c0c0c1421606000804d19258084107103c4da00b040b103041901610310982c1040090002c0d003140b00e0750307922622070907c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 362466321 1250 362465071 362465141
    0x180e030c12030402211e030a08040311070e010e1605070c05010e061b0a0c0f050a0b070305040f090b0411040308160302030d0c02010e011a090f060a030c08010905100e150604 76
    0x2013041180c01c0c06c605041000b00403581048400d030788035003a0303660b00e03603098030a41280c1e0307081d40180c4070b84400440d001d5050035036a4081c4c000c1074508a001e240107120a5120400c101c42c10307007084410b1000c0070000c2e03050b2014209868003400c0c0347d01c1d01e642e90008180e0601600ba204850318500d031003081500b1101154500c400703409460020009902c0341009203075813104d0702c00c0c03030b800c10080e444c00c200540d9004040c2c210301d4807a2515600c0c050b03541c001c5a524140d19003003408160303910345446d6242d20305440340400f0750f907000342040e0515265459280d4280280310380c1700180341e031080440b01003510900031181d408101081c200003d018a40c00280205400e201d10300c810b618101c0c0003242201c00098040c2c8a91004000c0701311139641c882d40c4c1c10601c00160003160050740e94000400000c03040c4288001401c4003000005004800b0304016150440300100a1800d528000d000d42030540e000c10301c1810043c070b02d040e180140d156800806c00402c40a221040c0360440014800391a0303e0504c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 362467571 1250 362466321 362466343
    0x303140a022701120f150b0f0412060615020d2706120b1c050114010b070323040b071101081b0f21010503060a1a0405040305090a180e030c1203040221 66
    0x6c42140c081e2603010b80d40140c814071030320303000590007804200102260641d80d010340921480c0040360381507440507a2112031146e4071503080542c000744102d42403980e00c00d40d507803031742200d41e40d08040051401100043c00b04450080004224802400c0079801920b5004055a40303009001c2c0360b0612150010215a4105000c0844013075090040d0080d0501c400440c090590750b034858201d24004240c0d0b820b5489003000406040e5401484110307460301030103100504010036000c044a590f03030042e464000301411070300044034140410344050046c814242c01c0d40d043c240000d00082c0707a9031400d1140301c42c0c090103501800200000d4035541d409803070703000450140c12591b040c6c00b25121904c40060101c20354140d00c0c0c148640d6200403603860340502d06900090b401601a05000d031900e900d003804104054001d400082c004040c44942141a010510ad00101612140c000d1420004e00042d01900e4240c14220911302c08004000b1506650300d05202c164544044002c9100308104c420180e503d840641c0c1c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 362468821 1250 362467571 362467601
    0xe0a05010207050315220b0412030905060115020f030c07030303230a0c030605060d0c09150c080a090503030c070e06010e030a0312020c0a0303140a022701120f 70
    0x10019095000286420585030010098051034080c1d4130789113003c450043c03040510085001000d00403c4d000020301a110b8052041d1a482e413500303060600c0c0c0310b405598103004052900304c41c038003c194013250403410f40c0c01d66110510015000d081c01c914007c0258021000e6000000d40070b1130020001900c001240d12982b8140181449088400c0f0320080c00507249518140000010343c40c0c914540c40101d10341c400b400c0c001012a00c1e00042401a00400140f48045507a064641d0b506508100084001c1913120440b502d21001e000000701140c80c034620003420928049041070600c0d008000c0c5901901c4041c084945411141c80c4c181e948545a114401181082001160b0554400c104000900c80d000d40106204515079404803441010b143d07407603094035828803048a6407203041c0a00180c0e5402075402064180c00c41c500101c041ba8003504a600311441044180c404841000e00d8101c03014450868003a55080f44005030b032068400314020840b03e160400080c07040c22107521007403003081e00300c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 362470071 1250 362468821 362468839
    0xa021c1712060d050f2e0c050f070305041203081b0901020a060b15070f060c03091a093c0c010905090916030804140103090503041e09020a11060f040c050d021f0e 71
    0x20f120507040f1601400f000000400400907401c6020a49e802448403502c00c0c90200d1402ea915180c444244444450403400101e0740c50500040a40030b08012800000000c3c4242ca480401d0340040d5031000600c0005058036100c0783c816420396141d40038051415641c128250b99010385141117400441200c000b210340c10715001c0701c120081d03c80d1090140169000c400140414000014500060f40050054034540304800d00c10001e07070030000b0340085c0c89640040c09010012150b000c104030800d4a5004102503104441c1011183e9000d12a4800c4a8007596680140d8030703194001828418102e08803c1244541f5100004115181c402001185c0d510034010070f8190343c11004409803110500b001e03100c1d5105001c103000205090740c0003601c0540103458031000c03940c0d4800b150240c0c0c101302d01e980007042815258035031940c0d00b0701001360f0042c681481070130603203890742d10b03114480410300074a401000105550b000315101c02e500c0e9524280c0c8520b9000b40c040951900510320451015540d0141000c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 362471321 1250 362470071 362470153
    0x130f2c0105060906010c06180c060327140f0307050d090b130e1003020312191119020f0d0b0603072909030a021c1712060d050f 56
    0x10722901d402060000c0145040c2e4540360300448141450f20000e8a4156480220103845840030058140d079910400c0ca000407a440d102010701101c0001c03003251f2040d4401c241005504020f0b40034542040e6211500d212a9020710040c40c0c9005400190094184030008288050000000b00104181d02c9982c82c07040a60726889941d00030f00039443c421800d041601d40c144102115080081d601140249202415076030701e80001c2c0c5020040c08401c0d00345400092240c020a200030101042c0c0032150502d225061001c2c5403051341c070004800c8000203003402081200840da0b0f18598080c40c080c4c020580e00d0f41480904141031a20b60683c0c425101c1d205000000642c0405610603144102c4401000007200072080607050542d88032500c0c80341d043c0035800586c401a565042143c0c580171100d10b80d040ca003a001d00c2c00303a400c010481450b0043e65014450381c02c88035514004030354000010384200d03e5581c49813400d146040360b4560381c0007041c081c620303c4242007140a4a000c850b115200f2203d2106404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 362472571 1250 362471321 362471323
    0xe0a021312110d050f030f1b071208030604020403061a040606141e0c12030a111e18130b040f050906160224011401020c060405130f2c 59
    0xa50000500304240e112803070750386180c0b5015039203103103005505032840117603c108010f06550082445150710300021840c20001020307404108400c106590041800304c2c10201036004034008040001c0c07816000000040081c0c50301d0301034034001e503401602404540040803901840c060040251030103245030000c00070725144540b8170100c141c01c50b00000c0d80390500d0740340c0308044603218103c0000341000c200503103203030740c4410401c014680aa0082035030301c03400d0420010041d40c243c1c0880c0d4504031018445c9040d941c010900c1c210340d841552407003942d540401e0b81d070510720459170400260710489481c000700e5506800e42084c16110002c039400c00100c0425468041124000c0e141044c0551150f000500d00854100038000c0007055401100c2e00c940c074207074600120030310104140c03840c0c01f4000e00400c10140c40340003800080b4000d0001e01043c20580020618a020750312803280310303001c040075241c0d070f01d4020343c000c5c5500a59440c080c480c00260211020740000e40115089620b41180301075444008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 362473821 1250 362472571 362472599
    0x14070314100c05040b070203010915051006020312010e0612010c030509010b012102280c020a061d01050310030c0305010b0a050d050606270702070302090c0a0c060207030302040e0a0213 81
    0x902d41c50781410141014060074040e00304400498156680b188007102003000003801c640e010502c03200c0407807549020046030034102c0c0e017030b400502503610910144141403000c0c18145d0548130001e0400043d03907a074000261030300d608800e020361294603102024001d50303032542002d4425088600284000314a020046071200661005500007114290f04880c1804582e0000d1120359207003d13140c0200256264003188222001304014045032a00100305c0031810110222001003600c1e0910116440480c5e040c10f02c08079031581d0f902d0404c100000000c40f10014000f0b24000307148c000c00c003192405d44a00d040d0b80201070303000009103c1e0040500c0001c5918181d0a8281c40300d500c50045c000c5500c409003406200200d0b000300000000071b03500341c0d00500024030a901e204191550041000c1440d50041c04081c4402400304c078200e0508204184503541c0000c003880c03980d03912000041e52200c2c00c0c01c08500074001d50308490300160680003032080384402c680190401301c0d6100c1c10b8941455403180096a684 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 362475071 1250 362473821 362473841
    0x5040c120f0204111b060103020301050f0f041b09020a02071a0c1515090a0504170310142b0c05030303060d030c020301140702030c010b0d110d1407031410 68
    0x70710050040c006060940044640c4a1081040c60a08035126415500c82441d806000615400344d00104250b1030240646070304868039000003216410300ba0405014114000c002419900c042e1100d00001000f10b00e0301001004035210464480f00b4803100203450f140b141c441c0c042c86003041c46a041c0134010030340403240400b4405d0002c10603281d45411078017410314000c000c0302001e0740c0241243c02d50b4865054803842840806800250303494245007030300d207903141c107900d1a0248801340100480000083c941d04d098589c01743d846050042c0c0030b000640c0c40a0041440c1c5031100c01200c044082010b0b44da00320510314400e400c00c001171505d03039041c15524001141c070036601903090030034800881e00554a0821550016001150034a840340742900251f0042d641c0e40d0050340f002543e042031080c28418600340000841d00c81b040f00e071240c4c4410f0455105514820311411030000c081307040100a2109a614100c4103058a02803552801c0c111140110312942a11f079025040e18010094134502c110800340c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 362476321 1250 362475071 362475083
    0x31507050715060915090c0306081b1201020a110d0206040c050f182806031101260903030403090e070210020d0e030f070606050102030f19090308030a05040c12 70
    0xa14a52101442075030110402c10105070340e07503c00301d185015800b8066046140c4508603100c070f46030000030b40c1281c500203070050030149002c9052040a1021070700d500300d031b4040d070b800114000c920000903280c1c1e884482c000880398800103440d090990003403034881d801ea08a5082d1030a4044082041c1c0e00e0b008203d5008001a50512062045141460819802ca20090031050501241041c10f07031034058113544040160100060a8426040310170083c03010b80040e00d07081c810075141d55200c2d910070520710a0340381400506051120042d4105803040700800c0030704403048040c14075442d03060316607205079419000928440c1001c290441e5052800d401240070b40e006181e0001012000002504071240c1000840e03100d1a000c8442030041024141c400822629681c1d6a0003602c0d020b411280c46600c424199001400300b5004880840207545105007402910315100c80c245200300d5000d10280c00003030074041c3c0030091010310f1205500051084e84581001c00d078041d00c0e01c419584003032482030000d241c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 362477571 1250 362476321 362476327
    0x14070506010e190e0c03120406080103110f06040f0302030c120c011817010b040b15040e090a1203020a030b030115052103041d0a110403020603061302160203150705 72
    0x2500306100680781d01c9000740c1504040f500b12a2140815502c04040d40b00c02984414416861442d0a2283c500300c404100c2421703180c20b14009010745800c80500c0080c1004200c0803881c00d9503118840440d104900051000ba6030b07545801e09110a0100303800160b01030300c00ca1007003240a0501c2e018222280d86000003d103440040040111510755406010100280c07480c40000703582c02d456040d0301a010b10207070000c01c00b40c070b992060104a8070f100ca240c0e0710400040304016914154801180c0954038000300075211959529141440d2520005000300003e80c0400f00c5640b80d640b59018149041540d03605000c035282e0301c41010300340c1e0162244002542200c940411103490171040c42282c4003030034011610000541328141d401c0d600701c5e610600216070760300010001e44a007240ca10340e000c05000740070080000000030780d454900450100900880380040450015130741c0324000c2c0660003e0010070340d82c2c0c09084509075a0805000720490180c81960995403d40030b002d07007414441d9219a9610381 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 362478821 1250 362477571 362477579
    0xc1503060e01170a0503040f170601060e0907020a0203060a020703030b0906090705090316080f12040f09020901031415030705040209090c0a170a060e070e010e0f04060519061407050601 81
    0x350900f0022010450300c56071082800042e010b0000d880280304205841101c28a81704030314001c222281e00c00c41154110070014091150842072050034050f041e01c0d454903075500d04005030300d02004404081e605105103410481c10480c990018110140319550130301c41d07140400180029607500b81e8400f588102031400141d5a54407440c09444104002022030b4002288240c5003c0c41c82080d0b001480181c109180511038110104031100c2042a40315100e0b29191502c181e2040c1d007406400303105400d5400013981d100e282e1081e0480180306a084454059600300580e00c031444241c3d10902500030701507604000742c1c5141502c03e0390001040030308012455075940b240c110083d0b1207400254140150665a1441c0b16100b8180c0351284c0740d901c034001495800c040940c44490303001000c41c4208103160380e4048090740d101c0201c9181c0c44054805039200d095a60018010b80351941041d5045020000e00c1004540d11458007002c41d081368540c1e0b000c45441c06021841885001805070070395004c280100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 362480071 1250 362478821 362478839
    0x5030a0b010317040504090807050c0a1a0a050c10050702100905030318011107080a02011815050411030f010219031103011203090e070c02010215011508100902070c1503060e01 77
    0x100100d0418403459141a4a17600020b04840181000382c070102804624032080010401c0301c110750180449040f00003a1034001e81400140b101c1924406040c03000c03030264402400303442a40c0c0c4103604403054030020100e00c4030590050100311ba0100040c07083d11070340c0605451600c680c1c540a80c00c000550701c1c2d40d41d45101503801c040041d210302010344d139504269090043e18005010316910501c0c00360f03952100d0890003420f55141d081640c3c0b6400c0c518401400040c10029030a083d2561942c2c041502c1c1d0b910b0078151502011680840d41600540c1c059440294066004004407030001307109003010880c4d102c0c120f00b01e0b4000c00802400705010801131052101d40081524803d103c4d1030034025164403164501114102510f00502280e108110441190b07018010750220305060040301d200382d07141c40e012030510948001e6082c2840382c0312001c21122000600404050500c002d400d65541000c0c0c542350001c0103451144084078524009141106403203800390310215078001e20000c4250b42401c0b0a2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 362481321 1250 362480071 362480093
    0x302030705041406130305150f10050d0f2001080a1814030c03121905070206181903020607020d02031812010b12030406200d0e06070804090c0905030a0b0103 69
    0xc81c3e04c24810b00c08808142031860250010758071820141000c03a82c9182e82543e650400b52807901c000800c0000c0248200031480c2c080219141144d000c64440c085040c0700103031700710071603001c0c101c42e110180c4080754609500c42e4803107407071084c0d9501d0140e5941c94021130803540d040020703010545c24289604081000000280b50f000111780c191303480c200041c0502451503200ca004a03054503064002c1201c04d902406c45031461b02c1180c0e90500c001d103403070300009440d240024440c040d0003003400c202d4004801c042080041075a001d0711640d000380307041d08010f035494004580703600041c418009450007041c4003000392042c3c0000384801c65194042501000307001422560710104566880c00c0c1c11800307039101c1150700c2c0303507950140c0036583d15410a1802052560407200d02d502b40c102030041e1007001800020f002c07660360341c40d1401c0781c2600d800800141044c41400d0307020f000301401080214001d0941d6006900e6203489440e2307001140d42d03840c1456109c9880c0e40c1e01500e045903030f07001080852459424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 362482571 1250 362481321 362481359
    0x60b03160509150316050414090403120219030b0d0213020f0c030301090218150307030f020d05070917030702060403060207140d0302040e07080105010215090c0a080105010f050619030e03090a2301030203070504 92
    0x440580e0588544c93341003242c004050400e20500c0c1c582d841d1a2060b050b200300300f12100c055800380d0302140c494020560b50349402d00780140071513000030b802e0a1b00b1256001e48507072002c0442501e641e540d40da1440f4001c0d401002070781184005a5604614914120070310000b0b010f00b100c569819543c41240c2a00144505440180116000c00c43d81030705d00c0c1948642ca01c00c0350140c5448206d14203001e60044107044107000d000e56540f003003000c000940d803208159000c5aa00c00400b6a40d41424600507072102e48441400a85114135141c2050141c4c040e00544203807000c501c0b020a00d940c3d040c00c222030004d030a1245602503004044c0882104000301c058980c064030303880c01c40701085d00150110702c0c004044e074020b0b106a503407200140600031f840c0d15000300812089921078240f00c0d620488006a44028051005040e82c070141c2c4041103030148107407403c09000400144a9030b43d50800500c407882e40780311151044030101c056586ca0740c040e2007903901501d501d82c1c8180c1024184100404000f401080c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 362483821 1250 362482571 362482577
    0x316061101060e0f041a061c1509200a050d020603040309030b010603020c0708010506030309011b0609080702100f0e04090305070b1513060b03160509150316050414090403 75
    0x16000ca40041d00140b2075001e40100c01c0c4d40002c521381401c0406211a031601007101005c0d428090041c507a50b0701485030030400383d0905200c080121490b0450a40d50f003030a5000c680f906280300c51301440844034502c0c8440031004944200350351000c0c00c2082241c944d00900b40c0c046294907019000d0b04044015503402403007820720b40801c0303859454559000409901001c0000c0d0006150311111006100c00d400810b2100c00074040c83c2032030b8000940b00c0c014160000d04216840710701102106214a101c0c1750305402c918100040b44c5141400e40203980003100c142d014a0010180550040c0b207003801c0300c0c44100c640d5509030791600da9010400075001a910580400005001c40e10209580f45085030242c08249030849828610380d06011107a03182c00d960b0071000345400c03810041c01d0364040481e94070007c0b02c400301f20081c4401303800350f5013400341e1409940c03c40050110a902e0240d6200114095a9080c00130200046108000c803114030940c01846030a1b00b846800340d040b410040c0180d60400e100341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 362485071 1250 362483821 362483831
    0x10c060e010209032a0301050c070201030c051e040306140402010801050418080d060e0903030c03070813060c03090203010f450606051305040503031803041503050a0501050316061101 80
    0x100c0040e24203007401000c015249000081400429540903644e0605c4500354001c0c8180e01e03111010b00d1490148850107814181c03607900480082d44100205e07086140d080002e480e04035088000410b040d002808102c0d0503e01d00200c0750540c00403940000d2050b0744c141e4a58a09030708000c144000341030514094a00500c04001c6d9600080b916009031086403a880000202c46c5d20f0490480c0807004003418580c55070304108140003082480c402280d07841011404d220909494504103c103903501000b90180440d4070700110b104100b5410340180c000d95008030020700811020403620821510320ba038105200106442d4094807180038802280e00f11040d450212580b030414240a002042c1210012190b0503541c4509100c180741040422140307105030f0604012614180d80c50507660311024060450061003280d03880410748007001101c0203001c0c0d201c2000007910840d0310150103004162090003c45061400201e85030400040652800b110102c80d000301c145000340c00e0f00e0b603205550003429555221 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 362486321 1250 362485071 362485087
    0x16020c0a062304030213150e0a090b0a020901050405011b080c0d120c0c0605180319080c07020616080706110901030c0807080c0c0723031506010c060e0102 68
    0x80140d0800038000c54491003001400b251641c9140800714401140180702070000b80b000d6102c1e03000364421803100100000d0040c00070518a013031031140c0d600c00c00d041a440000c00000202c1d0740c21141515118a5a4101548940c00300c0c10980c018040f03c1400a403043c08204032941c0f043c44030075400c0706020355072480801e403904c0340760540e03009940c45a860350140d0b644c07180c5280c1c0050307200240d03017020720100b08800241c08020b1001c4032609000c3c003c90b441d140403910409041c0380c120a1100e068003101c1d900c0d01102d00382083c101180000001245188001600c0c1401c1c000c2200c180e560b000f818645070040c40015555a00703042e247c1603e60b04814000703c40040d0143c4105112028100d411507104c0c164000010151214807407081c0070800700e44184003003160088511380e0000701680410707032a108003121540c541000b50b4446400581c9900c1005102013580c4070b0807c0001c07040c1c0960308100d05031800f80c540c1c11404d42d0201d00003442c04e589200850740c00da0103001035560580001d4940091 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 362487571 1250 362486321 362486329
    0xc0d080f040f03050706090302090f0702011b0206070f0806030a030318151a0d0209010306021b06040b060102061303090b09130c0f081503070e070c05150105010311040e16020c 77
    0x300e50480d080c40009a1014418820104000c00c0249003d07d0810314150540e030203e500e0a00107080b03003280c1007107400402d980b68000c0d08030201940c4079849500c82c045424000955a14080d2822030100d0301350013420308558490204c1d80c0c032500d0090300030300841003655000ca008016041148003044c101d8440c060000304031503040c1c10f03101c4409201003580c0560b003801c165200065142103102e900012460030040e2038165460781129000340f801a142c002001c0000440d50b1001513084d91802084100030812807501320003030041e5801c0c0c1c201c0729540d070390310085051901114400390104200540401a040450307005042a4801908450748000c1c0800d0140c180d400c40c0768450049040c10b003241c542030f50f01040f002c3c0d0101140f01c281c0710101d490400300c1c0e00c810840c01801101100200005c0307013a805500e1041c2c400c1da0060440f1486060041c1c0d041c8000030a0107041e0000e403c041c6604003103620303c81964182e0702561401303070240c2c44241c000c80d500c40b0130883c40025406121100b41160ba1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 362488821 1250 362487571 362487577
    0xa0905030c060109050a0207020d02091f0306020309060c0309070915180506100207050d0809041b021b0307061403040606150306090b040c0c1403120a0c1205010501020c0d080f 77
    0x801c20000345503550500c11a0801e0b600028103080031588103125244c0503a42c0c0b148070301344198054401e111103840e84400c1803044c0b19081540c0c0e400458400000081103000e0f80110710548100017968415140e0a84894507407005841648503035101d520300b4407945400f80d1000c0c03141d09200c028117420642d40c4180d00b5507103107616a4144180d1b5100f08211507400c2114501e184400c0030700c0500082810140007402e050100d40014068600200d0840ca103601c46500214503010300c06984200c0c0036a95500075501d08800508043c03001035540a5001410000340702e00907075090303480310410200c180b101c18029420003071064076510340f01c4000240501844900300060b08444e6800305299040184900541e200310881e01c0c0503600d0303e60b424041d168045882500b079030f8030007600481e0f0300300300d120280740d40152810310502e00418024407004081035070080e140894182c5968802c0d4540954260850750241700e00c4d405604180e100003590f281240251000302d104800403408c0c00c0000045440b690 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 362490071 1250 362488821 362488837
    0x50d030306051c02091b0f1902190203030d09060f0504200109030c060c02010207030c1d0a0209090106181e030b090303160c06090203060a09120f170a090503 69
    0x3076660714040c05142840e80f040851080210000250814150301040602c80024664406218650010702c5101c0b0390030103c906040501d50043d448a50403402481c295104030040c401602c5140b0440314210031643c601505590010040d5041100301d00e2408040c04003150110f4000c0d41d074400e409803002545c411180540e0143d1140c0000429103d200c01002c0c18040e213090620040c1c040400001d03029a0110041e81d000746811801200360b480140e04d44030b000d070001030086d07109030004101c60511038044d420303401d81000d90000c0d989410380004100c3c40b4000c28550403c10841c0140f08481c05145103003840c0011008510f28690b0350005031901c0740c9240c101d0400c9078019603040082c4000c0102c61500304203060061403840c1090b010072a507200780c1400a100b8000304064038014001c4d41d13401420b8041d00030382a0b03100c903c0c045402c41c00401e50500f003196804011104d0035000c52280c982045116103c2e210b19161145055080300f0480004115020f4552500902d84c00500c040c00030f02180 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 362491321 1250 362490071 362490077
    0xb01030203010e0f1009020a051534030305061207080601050907030501060207030f05011b0e031209010e04110c15090f0d08070c11041a0301060b0301030b041704050d03 74
    0x15411403040500395848032140218591194aa20009443c045200843c200c22490009000741c600d1003c82d80b8000c4a6004903807141000f20386070180303152003000740704038240c0c00c0c03071901d99802550b091034540e004000600040f00c1c2c81a15a40040d02903401243c100707900034a00105914180c0700c161504680750040e81d01500107100401045c201104150b42000d07880c14240301ca9810084001e40d14a01444041e008040b21000d40302404829400780b0030380038041e8110b400322549541c0c09019280d00b141e03c03502900ca264110041e90254070280e9542e02d9059440300c0040310210304000251114021410743c002041143d0110100c00700146a92034045804140c1d40303241c0701004a040110442560b01c098010002e0000f60701d6002130b52680c000f00c6410502c0d59490641001d4240000174003226030410b02d030054440c948903034400070003d0f8010031070091045a480742d01e0880a80420310000700781d804950b003c20f001610f50501c201021040d02c46103820315070788a00151144245140039408 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 362492571 1250 362491321 362491343
    0x10f06030c022a130e0303070c030e03550201020c0d0605071106010303051902160b040f060905241201140f0f010c0b09010e07080708010c0207080309010c0201090909 73
    0xf16051001c0101c000c403a840e1010441403042070341e0710303880e44030081001c4104801d02c07903032408250050f08280240100941107480420310b00001203a02c2c134a40140b000c2d030b0521200e0182c0d070440c03203003450915208035007100c800700907130b1070f0070101004a03281b0200e056015505100165442d4045800c0d009402100301003190b041540b4060481c46c05810001c070190043d000510209800004542000c150071040b0440324082c1c1808900304696000b00001040b800c0400249030181c25000d8010b4802404022413005c1c1d4440056540ba403051140580200b082039004803820b40c0c0364031400c00e4020070000035150202d44280008803120981094003502480040b015560800c81c0a41301c0c82501540c40707411035415440041c0c4a19640d000c020400703502c240c00552041803c0d0480d4088a0030304085482054075805078a44441603130268544541c60300740040c006510024a0800312080e0314083c620704801100111690110010300381e041c40008000020517859512604000c54001d0a100f11 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 362493821 1250 362492571 362492653
    0xa0b06040501081b150d051008010e03210c130b030a06120b060f13020403061a0a0315020c21070506010e10091a040c05030a050f010f06030c02 63
    0x45035010703000b4009690101301c0072208a09140d0700c801c02c0343c0c01241d0381c1500900d8036209281c80e1003804528402c1d07a080c03106210038112518188000d5900500c002d00c64034407100d00c460b41c5c9000c0c1a0b400000c90500d00d107008400c003038100c4c4941e081041c00e46054075142c006410503652440c0c44c0c1c40314840c102d00000300300d0780d4a141d104110203851013000a03007520280b5200e00d034048201a0416206280080c405170b03540d6181c0d050740d0301015920702c00395207881d600d04041005201407100a10501e00454100d4514a0648100d600380c0358004040c070a1140e60f046108001d41080d03c0100c210311811a10110075080c421400100304490b01059a030b4449901e015801c0800680c490b4104c1c109803400c3c0882c0300005440702007a1102c6820008101c035016266540307081d161308040d0b4000b032134806004e64031030f80900250311403034000405010a41340d120f0000308440b024410b00d1403401d500e40051203c1c0c1d1180d08803103041041c5204440030078803122154a4040340440541d10890002c080e145 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 362495071 1250 362493821 362493829
    0x90812040510020a0801051c0c061d06040b070b0408090415080d11280c09020301030203060f0601020a03050c0c1003051e01030f0212070b030a0c03060915031e050a0b06 74
    0xb961a100c050015414074692500c081d04040703040c06007034030403041d5803d0b1004d0700c044141c420003015000098141c00301d50380c0f200074042a00c0900348800300000c612034a94907060060494080310840500586001402e440d16859604040e000302e82d20402040101c00d542d485004101c3c0d031450888bc0e02601e240351a00d111720380004103007248103000a420306010800800300b04240051004d050881051400c100202c03000e0b4040d0800422410009001045040c4c2a81c0134605891080d01291500d46034002e0101d900c02c070446c3d0142c0168030500380040024032420141862603100c000302e842d40d01c0804d000071800f031000b40b14140025640d404008000c603628405c034114840b50000a203182d411030300c0b0b4000324039420324082d0043d98800c086569140b8200148001000c568103416102c0c205425904050328040a4200000381804030201300c0918038400e600300002c01413130001c582c07455603032089981403510201044c5501d480d40d0b0103000c100144040032000380316507030b610380c20300d0200100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 362496321 1250 362495071 362495083
    0x1110f0a2016050103230c030c0d0515010314240a260c01180e071704030906020606040605011b030311070501061a07020a06050d0b1507050c04051e09010908120405 72
    0x1b407103041c2c2031004000342c801c1d001c0b80e41e683c01c01a1111440c1d50380c0d9032032580350814828196403507903480c5040108515820012034140c4101c03c00d030303020b00815100c040c1c0f0800482c000d031445821305041e110610001c40350080600850040541b88295043d642e20b46101d0001040b1700329000e040300e44210000c41350b4113002c0f03031880c00024205840344568080b81120b1544c007a0068000080d903c0d404110020b01801021203a00c03d13403004d5110602d0540f0380100000d40301e1207502c006d4460040402c069140500850041e548107940d40c50201004090898201c100c9000c281e05042d990103c0f04001c040600081110134050400825103501d80b940c0484104c460000c802c07003041c014802c0400603510003210008682480c508291151812400c0303c0007400081c1c10a68040841d100c0785c0000b104550260041d28042c6007641d0001d00c4038824403054810842e51554004205031218840c1c006000c14035411546034000090b04010b603035144103140d44400c81e4000d600740d0902c10003082180811032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 362497571 1250 362496321 362496341
    0x3060b0a08011a01210912020f060105010c110f040510050a05040207050d0804050f19060e07080d0c0f06021315051303120203071506060201110f0a2016050103 70
    0x3000042d000105076280c42d881d1080700c13410000060140305402c50011444681c81d00b1000041041c1942da2601501440040e2201030250140500c100e00c10440820340383c1c1202c906840d5103007810855501c07150001c100c3c0000e280e2201800030b00aa60b0785a40c82014440e410310440f000c01141880d0402c4010101c551000b4805d034010000c15001500100d1a0303001d681250401050a813a0340c40c0560404050109150041c07052800c200c40c0c2d9007404103a10029400b80c80f0800c0006a03c00305a07894a8080c05101441e9001d20243c240c4a0b10811503140000d0003018a50b034503034a07075582d0a06a901601090301c0c182d045c90b4080c440451403e103450102180340c10603910700032020030080d01040d8244005800300740042c4001130303610700a00441e10f5032680070a81610340d00030845404020801ea018500056103031640400d04640c50408842c0789000176960706042003501c2e03c08441c0070650302c01c00000740000e01d0107850175074020042e0608400036070500f00034160a001c0014200c40d101e0b55 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 362498821 1250 362497571 362497573
    0xc010b04091505060d080a2001051303210615030e0607091202063603071a0a021e030403050d140712030b0a03030305041509080406050c0a060603060b0a08 68
    0x7078010005180d0200342c41c2c031000707014000c1060380d520b000058801a51120103060140001610081c05502c543e0082d1954000c0200074640004820340900700c0d00110f811001070b02c0302a043c42d010034010007030341c040030308000b140d6000e1140c46a0000251103195200d001440d0000d4000c0e09001d03050f000c0c40c51f010800000421080c0740000c4020000380e80c510a16450046440012040d5200c803000c884d208103810050700c02051907009a44441c02203102d00d0f1082040d00d070024801460081540d400710b640c00004803603002200c4888041551241f001001503124850035032560105103114200c40b2048031000e1341d1198a54101542800c02440c801d20130000e91844a40e0013951300c1095034240c6411050310454100b007914103030000e02c402007040b540300a1181e0000205507168000500c01c0d44a40b8607004410302c201c0001c4140c1c1e00d01c0000501c903100074032051020612980c05021120f2f0040304440b820204c03521000202d5039160010b0315442e40b25103502c482ca05180f9030172402401440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 362500071 1250 362498821 362498831
    0x103050d031413032604020f010815040f09050601030f0b0f1605031005090a0c020c100f0f18090501060e01021606030b040f18020913020919140106050c010b04 70
    0x4110b040d100b010040c5001c1420209400340030502d403140c02e80031a0020b204800802c604010b001011001070112003c03445140c003d81242141d510440800e4000c1c00003480e9036036012101c40c00c0102410890904a20540d9a00f4146000c00e0341008098002d502502d1418002609810581c04541000b4000401c14943c002800559802e01d94a103440003510b1400702d440303441c0d0201c40d443c0304103039a1000b035001c8100030038817000c070000e81d0046414441b0786d02107501d20201d050603c01c800c10102c4114020030049507807201801e001380000c20080145180800030010201141d900802c0701d81c0081c240141d072400140106c50304100d492040b52824002810820041d20300001c01d041c00707000d80e404040e02c460000b491501c40b50007000c00d10b0506802400340e4887c1040030200c40046400691050b1041c00c00f20b401003c03401c1100d4a003d8014241a1440d994110a401c0d001101001040c92554584e0b0030740300c000d0402140c0c3d010300000e56030160740306900800c10b82941c242d20300d00c0b442540340c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 362501321 1250 362500071 362500091
    0xd27030807020607140d02010b0a080703020d0813031220030306090103060c0c171909030803010b0f0c0a050d091a090405060604050a0909150b030a0204110d140103050d03 75
    0x3540545101a0b8110ba115540d980396180103600d040001d00070380d07011300ca5205039038612070f0190080f464021301594072410555544441c07541c0d541c0c2900c0040d40000c030800c913401c0451030110050540c030211140b190141552540c6500100084051542c00124400f403c0ca40e040d02c44580190002181c00085040d810400c0c0080c0c41100f061000a00460303480c001e40ca00f041c000c0d40f01c90f00e0b135078010282e4178078001f64040da0f0000e54040c80250311400824445199241c3c000c000f46401c3e00d03002860740d4196802e10001456a60080b00000032440080c800b16041301410070103507244512841c0502030280801c078029100991903000080c02c2d200e07564801402000c02e4042d101e0204040f100400c030303a150600403407442c2c0304a401041d00060502c1c0c000c45d10b07420a03005495064440c42d100004440c2c0145040b0456000c101743c0703070707154010039101409440e050304040d40c0c074000c41d0f065618005482401904480714503c0906494805000404c1406030074401902c2505203410705201884403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 362502571 1250 362501321 362501333
    0x8101b080402090703051f0303090f0b0a0504031b0b04080c120f0a0f02060d1415060708040308091302030a06030203060a020a09150504030b011716210f02030d2703 72
    0x4004c000d50201070b902d4000515400c8941403140c410081003080b02000c5031603040042c6400303518043c41003d032100381000518013440100700d0754144501d5603001e08082c2035540e003003820894060302c1c0491040e162008030322600007000030002400540b0007040b01100210502240d00320080e242c2e11071350400c0802ca15084004a680e5102e04e03030000c100690601c0610006400d4060710144c035001d24541120030701140e45c1d08030041d005682c020f0074074500c0000e0b1800c000c910700c0b0b07001c4020407150040c8010070000340004042d04010388010854129203814403010b104a80007111010003c07511540100b0030340c1018400f1035006000160150714005a0107400b80544941e4411019202d8a0f8020002c20512400030f5901455000460442c5543c1d40e084140700030921100101c0d09010b41010780c00ca900301d28410604560411403491048200710682e81888101c1600035640341d4602808a001039909000020b80c929440d00c03448482d0243c800b05250400d003c3c40c0d604078009150100b40b0204075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 362503821 1250 362502571 362502589
    0x1090218040506211015210203030a0f020f0a0605010f0f12020108060d1202010b0f061920100f05160203030a0207031704030c12050f09040e010608101b080402 70
    0x429213440c88540c5010700019850311064184120105140000d451543d00809004000711500e0070501225118403520150a845140da4000d5160380104005113800340164605000c0e01694019110400181150340707003403440d043e0040780c6250303440b07005015a040e10f00c00d0301c010380700b140585244141414584c810b46080c007030300a810b10030140c0015140c0e90714170140303050041d403111910710240716910005c1d02810702c6200c40c0e4800c0e401810500640c0c2001e00554052000c0640040074503c901182a6032040180b80c1051256881c0e00c0c0400b48400200818101110f104000040c4044d030201c4500481d43e0280074209034a0400f203410003110360000541760000b584100c01651400c80340b90035500580305010403c0390381e00d848200028550444500080d2074000d00351280080099481240c1c10b200740100d9a06015040c841c10b40e145c2850381c89050482000c3c000000e440741c0320700090345025450003080d9039898a4000d0440c901110110402000f68070313081c400ca450800340d001074108d031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 362505071 1250 362503821 362503849
    0x122202060d0504050a140f0105061f030b030f012d0c050f0d1b050705010f0b181801110703091401051215120322030b04240501090218040506 62
    0x1a0322034000c0f038180b01c014041c8121031030f4002c5040500c1c10102c00305503100c44481100190300d51800380090ae19041501101c44032041203c05d11100821204041e070051040552903505403103034000c1406003a509120b40351584100c0081000f1044800709010b01240105050924650811030151003c64001d030503645815100f589032074440d503818110300010104000c01c10318545034440503101d2035400c0001450201d000c0e0000380480340700040c4010544094040c1e254200510442d94201c0c00008140150400e03603d44600844110b0701c008035003920080d40200859280c00110801010380010352103004103c260307000c02144100100181050280250070b22200b46808002415400e02001840ca4404001d240300134400044d4a616920340180348a95407503082c1e03070f6079030341103040c402840c508680c1d1090b03103144986e94a998848260140c52840391b103010349071000f4400c1664600400b0b001c0c0c00c04210051320b6660010900c0308800840c0741c400c0c0614540800d000c0541c0351b15030540628 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 362506321 1250 362505071 362505097
    0x1110423011707140d051e040b0703020a02030c0a0b0601081609121e0525080309010302090102072106110910030222140f0303040e0a0506010c050312220206 69
    0x1030f941d010303030540c1c2521202c102c0101036100043e10844100c00d95000f00d0244012650480500c00c10030b1651a20402c1514007a00a402c004006030f08944280c00412424196105072410250614250352a00b480501c04031a1508440200011542d1000e141a03101c516440c0d041c6c0c204102c0f5102424903180c5005000e4240d12108480c42804000c503080d0301d41c0b608100070404a4441e43c10071a4690314048401c5030715070406010819200c142003c00c1c0300703441150000e94a0203441d00010340081d401039035a07505500a50400140780b8401d242011031015105503540c20021051034031a04485003461109041c12090040350001d480f03500c62a9442c2100c5c2c140180d842116202a804e51900d0054031910500d07007210101d404443c1c0c0c402035440110689001d2005240c2604160302c0c0d010ba03008075806001c230940045d0a008481d04490742003101818110200c000f6a10f44506580c40190703107002c008402024450103002c90b000880480340c0100c0302c0140980b060303000465070f21409001d0000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 362507571 1250 362506321 362506367
    0x90509300403020315070f360b031816080a120933080103050d080402060403200109090501121b08030a020d020c011b0803070c02030111042301 63
    0x800003228100d0303014540007000c84a101c01050130342102454221508130000d02140d4161015500901190103000c2009800c140e070114412490f050510b06511040400700e090307a000101e51507001c2c000c2d4010080041020015940003074407a1500659060a94454140d440b003002507150104030b501c5126448204412001d0f601d0900302e03024951500a880c01c8a943d25011009952611045c0a07070403c42170000300b03014020b14150f40c0040d007403202038103680120f80c090b240c10713100701c0902c0d50083c40101041e080944a0301c3d9010f0f2003030002d02d1b10056031030301c040030b9500f5070700308101100401c04031006020741e60510383c091005e074007400782c01800c51068a48082000d0b4042d820840901580000c40351510103d110003541c40c1e41040265002d4082c80440610a51180700101e6258408407082005210303180d41e42034540e40300800300c0d010000c104003001e00503507003030040c99a10100804c66588540c100014200c000d120718030f4482101d001d8074864540d99801a0541059028010305001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 362508821 1250 362507571 362507653
    0x7060b1c0303230106091404140f0c041503020904200d09020409060e030901080a051b09010c060c05190306030f120c0b0106020106030c050607020f060d180b01090509 73
    0x10260600070100152000c0c0c900045050f80d40000c146e011503002e20a0100003035030078000d1108a80380c40810385003a0100000003582e5100100d0110b4201c060b01c104a441c3c9540d0702c03401da10700c48401000e1400207800090142c031514050281c40e181e08010008480c070b070310601130004c402d44581c583c0b006d40d450702c9a50110a56642d9403140c405160410014002a42464034854481d8440b0500b580800c2261000c5040da00d06481006c0c03140b020326600600d43d01d84020420081c0c0c0200480c1c9040003541c00300140000c3d11402441300c146120780310b5940319400640400c2940d6040404c8404043c80c0c03c1d010004030324148921003059801901070503c00c01000c2c0d04444a00e040000a0082401c08000040c51340d0305500800c100e9015904100030152198200038441c4251400650320425082a82e034003440d105000f8642d100d0380c80c4002400424003209108410b1040100303031000f0440400401590300c250140341c0d88164220080d14040c80310000034285c85842031001c50090140c840d042d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 362510071 1250 362508821 362508851
    0x1a0103110d0203010f08010507020f0a0b0c0d020a03050405071403071202030a0209040525060819060504090f0203060108030319021c050c1801020607170c070602040b07060b1c0303 79
    0x456408020074255600e60f100e00340031044a1881c03052101543c60040000c1100d4404105095441e40c0b20029060783c41454940243c2a4406403420310803010401421424150520080182042d44c4e1000b15491030141003040c14000e455100451900c0012110506542c01141820580b0269141003610b40070380d001007071518111640c003d4000dd2140d090006100300043c50098580700c080303800544104101040500f4a040e115200c0854034a01c0071440c19450000707035080b4803186645c00a00c01d03603a440010f055400029050300c00c81d004121010540c1414442140540078100080d86907082865001c0c0102c80600610030704144c1c0407502d9104010910b00f0030010f54a4240c05008a0600a01442d10799010070304130a041d518020300881e2550012900b2441140300d51175201d1070001c801c9102d0b501c03041c010040d6010203c104851800500d8038030140c0013801c3c0760140303103848010b44d252140c00c0b101d607420442c1c46040000310704082c0b10140001c1c4111641d01d884c0105060108070020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 362511321 1250 362510071 362510077
    0x331410050910060c050c060c0a060b040c0813020f0405100e0a02040506041e0e0c04082103190902100512250e01031415010224041101050f0d140a1a010311 68
    0x1c07d46c0008009842c40c40c61000143c48601a80991400c200c1300710008100021034440c030443c10082010003001608102e10750241c2e1800d540040c000c0e40340c040c0c0071744c002422038004a5031408000042078080c80050703600354605500104074a011441d040c02c10700020110702551040c1518035414a50f11103041da25450b051004001092699115090000f440e0145401c1402090000d01c580895802211f155250381052804101411491074031031440b00341c3d4104817400b03010400c076194400c0f640140c41e45d00c9120690310703803075507079540708c404041e01c8405413400680fa04100d10385400b50361603509100c1510414102007030401000080e4441c00680c041e00605c101031403101248400c01c0b00c2004101040c0201c600240d0039610b00d9021031071510450041e6042401070a07a130308000400255400c0084a402001418600d04111410006181d0750303110101c043c2080b03460351030036117140041c0c51170f80d41c00405800c002d00a0700c00d02c244550044021210720341c100342c0c031400700c00a9002e501d000c0b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 362512571 1250 362511321 362511343
    0x9060a0b030408071520090d02010e0402070c080a05070f060f050a140304031d04020708120c070210020f15280f060e090d0309331410050910060c05 65
    0x1701401106607641100001e2180041550311182c0d0071171600000250642225089071f0000e001c2c0c1c81420f20350f0011201215448a400d0301b00307500304041c102042004a0329402041444010302600c0c00d80e02e002401c0c55065400303841198001c074024841190007a5680744449490b18066403101098242150b501740d03401802d6405010020603c42810b03480124000358004000c41c02c0440000138081c00124070036100060003a04040c054402c54000e05c1c203049402401002c03c690808010b50009800c520918104c00c0159220400d5a8069101030000c10300d10b0407000507103600d500e0025000a9603200407401c203107000d01518a181450350039580100b800e0f1022203020803501d500c03641d08841c1440203540c1c0b010a441903a09119203070740b00780141683c00e40c0c07010750800400707c01c900004060304c415034504140c0060150103424800c80340304161400125001e80c0080d03060078200505040c0f102e0301b10314080d510307000401c900c425100c0030010895400349408078200701d007410001d04000c00301d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 362513821 1250 362512571 362512583
    0x613030c020a17060703050c030c0d0f060815010806070e0f101e030f1109010903080703050d05270a02090112020a08070f0e07020109050601051c060516030b09060a0b03040807 77
    0x2c202483d180c00110300d48500c400e52001c1000307468a01d1b408209010032600d4001540c000c1002c15003054480d0054141501c142e040450a507407250f0885040c51500340040c404101e201c801000300c1441003103890380240b1035003000c801364801e5a02107424210b07445001802600350b54860054584911071003448180c5889001c10304401c4000c0080c064158191450071103824141000214000b1904076004e000c1c05841d61040103243d50754807a4190410a0194207004051203ca4034041d101c0c000d280c41402e0074030244841e0395915004c001100e554131800da007182d00c090300c11001a2100104070381500c48a000c0204030000e244001010202550041036080c084c00d00000303074101c4240e0030542036821503c16956599542e040407400c072907001101511039070140d001000740e802c240c900860b60526048100302c01042e552290000d484069822640010080b218481c4840d45480f5031a1014000c5445440a00701040060410411400b0780014805d000001c10704014070740f400c41d0240c5d40c2c049 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 362515071 1250 362513821 362513849
    0x60302132c0a0f060e1005010809150c0403020a0902030f06040b0d051f050f1b09040207082701050c0a060b0d20180c16030306170a140613030c020a 65
    0xc40702d80c0260000034003115007603060800c08241c2c07604403850740d481080603900c034801443c034040c01196840d00140c81c0641901800541800074001c03075141c1ca08c181c40e003072041c1360b1780c03442c601c1403200d004869484941e58520610a11030300f0007084000ca43c00c05011600403400c0d16243e80010083c41d40000e001700148110706826580780c044107a42407801c4441041040075540301c2c132412007045011034181049a00010307880803012080005031000540123040141000c81984c3d076002c0070b80c4280095000900b0101c2c003808187c00325008400c4804080c40c5c501d042015080d8165581d0071140802010300e522500d000c01d60381c542041180b043e540182c00c3c46041c11100d03008a41080040e076006000701c14800768141c403280e20b0440d85000300490103401c0d1410745400c050100c4c090720b16404070308064591f2400905171034100c10f24001802c000c0080e0007074004501c1c0000040c41d10f43c0554209402250801801d54030318110302c000c0c2038050030710401c07591440c0b0005c0c1039906280c200f10b00b1400e0760 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 362516321 1250 362515071 362515081
    0x50118110c1b10080105090403050c010b100c0b070f050702010503061530040206040303081003060e0f061b070b0703020d0c090806070c0c05060901030e03030f06010207060302132c 79
    0x111204040102c400da07014209142070035012a10305038240141908110844040307000244500024500008c200f000010302e11103400009200d141c40c902c0000005a00c0c17912501440554091150000054140b00c2c540488039a4054040d008400700070303040c8070300440012400e846401c103014040748045001076a070303150710101c05840080b00450300d141c6404003551001070304889003001d0143d50010440c1d4285450765034202c032040c00003401d1300c405d207059110000014540c1d00400f441030b00ca10b8040d03c11400382d494064035120340180348030301c0d100340c41604141c040c1c40304048030100c1f500226413801980d41e40740c0c190701900c99020440342c04e03843c0007041911540c5c0304410741d0594006c1c400391100e540300c00c41c0c1110707016001c2001400e8078071000d10801c20f40c82c060300204241c2206040c00310b0032504611400303045030400c990b00086d400e0b070103080080703943e814003244c1c0c080c240608045040080061000790290883c4c010905850000b905440c964102c1043e0401c00c440001c4d005490b52800d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 362517571 1250 362516321 362516353
    0x11040b0406140915030a0912020607030b0d020904080309070b0d051501051e09220605030c0a080d030c0c05010e1e030a08041b080d09031203050118110c 67
    0x181c4100000110100b200426403510502281c02c81c40005108100c42c24003602c4504060f40b01a00d030800c03407941c581c0810001a4407003c1c8208182164000c2d203480d2034068005010f488040c0d5070a48600d900c04144c800690310309400ea5040741d00b109116899a0b52078884030b103000750503000450030380320200d804000202d031a00403d01c2140694134407070000400c1c40040d5454095a0711010390240011040d2140584a60141a215000600c81003000c400c440603004c070555106074164101d5101c43c8203000ca400d040003d49104201a0b55980344a132502d05103a844003620044071007055280d141003510a482500448603094102008022100030b01d845241e0f25a8415034404084407a0740326844110780100035192034a030151105e00403680c0719a12210f50030901d80043c0b50b25088030001081e4018200484d07018601c0715100c2070b04807410350619201c1300751000b13482804c16044c500103111a140810030728040086288001c10f0f6140f07000429001c0d0f01032009007560604c1540081c14094030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 362518821 1250 362517571 362517577
    0x1c091e03140903030d0f15080c0418121d041b0e010219060510031b1406030402010e0f0a0b0d06031112190609120c02011d0906040c0311040b 62
    0x4403a444207050806041c2219840d4001c0401090f415002030100000d021110f801042556446200c006211214880381a1303041e41241c001400c140c2c0300da240101d0340d0401d4410700322034581d0910003411100b0103035108402c42c24410071074420022441c80600b554090100d00740b5410300000e00a2024000110201064240c012109000101024001c0780c1950011844461511401a10032200c1d100b507103407100a0138024080002d070510b86840040030034501a0103485144c1c400050403145450307c03e4414401c0468048144519010400e201c0141c0e00b00c149031400321021740d010202c1401e40c600040002e00030340e100c81120100055104000c0c4140e5002d24180c030f20036403c49812550304410302804591244640c0440d47c090031800c410b040c001ca030076104083c0706820200344400d60342e9905141e00d681036140000300d03c540310300404540c1c1007003130240c0721550420b80031410103450000070552000606040d00559442e1031440f8400d21940082250304a81c010603682c03282e48a031700c000c40c1e40c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 362520071 1250 362518821 362518823
    0x1110712081608181903030506031e0a0b130606060207081002040f0506130b040e040309050f030624030a0c031a090703110d050a03090801050c0405061c091e 69
    0x61031800003540c0d01102c00000c091000060342caa02c0c0b959114808880d413140300c50386a40f40d40c8903440c200001c07960011038002009219a6002c10281480d009041c9131011025075800b03a002104500c5281c0800043d01980b4260481000d4030aa00c8032078440c2a800f4040324040c2c481d41c1001400300310241c000648008946114049856038006003103030600f00c0c040c90040c446144518001001146400405807000030384411442c81001c0c0d6035640c100042e401580000702030301c0f4100c100000d040d08540110000c0c6400c0e101807280810407c0001c0d19080020a030800c071192110791109244482141d101800c10003604540a20713030780381050307800c8400c103210403503d4029903803c40312005291245240540c40c4400203000540c111754039145440e440d03404503500712003050032440106100f00701120b6114000c1d01d448034214140394490f801d4860050032484609002c201c1005961201c80480c2c103100007070000040840154480320303014000b6590007528000403140c50740c0066003500301c510045 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 362521321 1250 362520071 362520077
    0x32b0e0607020c0f060d2a0f020d050901080f040809030a0c0911070b070c060236041b1805030708030a1107030c120510020d0204080f060c030c0c01110712 68
    0x10074800c4080209190b00f030303880306412a00600c441c1e0720348445a040160480f0310701f94401e452246030070219440d40700c5506031500140d806a84410181d40601c02c059901c021860501d2400819030006403040b013000d482c41d21700401100006061051038800d44d8100a002030503140d2710303000e0b41001485403c40e0b0041c207034214500745011080400c04811904456800524240d02e552814026204000303803103401d031030580e020080382030107031451007541001100300c048040101c2c9681000008442071464514012841d261110001c00c4a0611035000003d1518125040d00c5400070f00040402c07007507200c650140310b8000081042000440503111a110581d294416038003070003103c03a07861205100251040050312000d01c0500c8074120540c0285018100b1126056242001e1404a900c491464400b059011505000340d070000d00038801040c60303500041080341840038000c800c2d0f210240100c02c5c0c0000009000150810030341040201c2d0741a403100c0c07074440c01181444220607941305681000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 362522571 1250 362521321 362521333
    0xa0e0102040605120a0204050a050111010e1c080702060408030a09110d0501020a110d0806010c060e0d0503190209060f070309080a0c05040c0804030807030b030a020307080f07080a05032b0e060702 86
    0x117040c185209490840d40b00505107100103203003c0054840101580180c4019503c407111520148400c102e40b101ca65100c1001c0c200c015014074004000040c00351502045402c45014070001c90705d20000c1e00e40102264100058200700782c907041224050b01a0182c2d0803805000b548414003c040d400b8084c0700801e516800c113240b0604502c507460300841801c0502003021040480c1055125020300440b0070f100700d83c0003441e44d008100c0300d80f420305071041c1080001c8002042001d0140d54961290702154542019030800c2440c0000800b14040c108040a0320000400d10000303161140d91120001c041003030540d01031841e1400c00d560007000c0d80c046c1d503004a0070300700250446485403c0c52882a5059550000c2c991a0345404401402d01c6140281e4180319100b07079000542c0c0c05025200c028002c66005049400044011030705115250307000091301d810840506002c994044102d0300c4200f401c6400c0c44a602650300002070449a4200107000d052510211601940e40040d0310b0b402421960225a5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 362523821 1250 362522571 362522581
    0x20309070510050403060f02090d0b070f05070f080c0a0b010806010303140a0f140d020a02011e0e0d08092b021c1b0804030f030503010e010605120f0a0e010204060512 73
    0x20444408079042c01c0058400c22040020902c0c0d5441403090113031041025140c403c0620005140d43c50740202650260300000c10701644a030840501d2050182d10704061b0b0801405403501f03020403668040241c410140001d108800300c10600c0011207540d031058001e40c407961252400c1d0f64403802404221b01040000801d251034076060b4094400341d03415580d4880c42c01a0118044462464014182160403418845a2840e9815002500c145001e80d1700000d15280c07070741d6039030043c0d62032148144c60f00d61404006013138507140400e0640041e05281000c04c1e0350b44402e0584c80c98640b02c04a0b0005e042c4070210820078101411030380c1030f031030540d03030342252a40300d0b00c0910386060455040d40c40010030342256000d50000340c00b0142c0040f40c0d010340781c07143c14030341c1d00c0c2c90f101440307811014224000b5074008010311103035000958040c00b500e41850701030b0519200f403180e1081c58002a10001c0b015180e2030000d202003010b50070130340807800d02c6002592216641c2c500608079811011500f40950004c00000d2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 362525071 1250 362523821 362523829
    0x60c03162604180f020d090c090608030a110f010c0906031b05190203090904060626030307080a09050706091d0402030a0605091002030c0a0306081b01080c07150203090705 75
    0x1070059031407101d00c60715261400a01c08901442c001c440d82d5940c0d2541003c404d03142c581d10281a000341c846101017420b2400740381076054040b41d074202001c0e01d031502c41c047c000400d001050300e00d50072030b9061000c0048581d55503d0318210003440d00361115800c000160341ca150740303e1061402c4a415480034000695a803285410240c11b03201494000b03002401001c0d030f103255a000d907000e100b8250055900e45200350000c40d0481e58100d40c103443e03040c0c0314079042000368102418070300141092100d4110104d0000b00094580c440941201d003002900008286008903d43c0000c5201764040c04980d01c2a9a904024080c001c01e403284e48422240e003032030745066140b04007225200360760040281c40d4440079079640c44010280503019a0051049204d403501409840c07000b1806241c0c52540701703031102e607111b070000d06548041c3c000c0410345c0c205450940455000140581000c84242030441c0603980d090b20300c8902d40070340030307020302410000c40070041c40c9145540118080d181c0750041d54034050300c61080c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 362526321 1250 362525071 362525123
    0x311060712050a0504090203101a0406050304110f040507030b030706140405090414030c0a1b031e060b04020708030906060a0b180105070c0b0a1206150e060c0316 71
    0x150201d50300259110031644604000c1008801d24240242019260380b0444200d03042250540d020358a0300c402800050040231720302504041c00d010307180c502403c1020090490101610003455600c10001c3e16034a075031841003c0d1038183c1c0143c000c225a00e00400018081c01e080d0000c2d03070280c01004000315032548501182c407502101c609900d0714203450701c0144010301c90003d00680301c8844a000030b0300f0720768040c001015504041ca005118105c198203010701c074203d6124001c03030b100151000030000075003540c03000c295208503040c0e030501141080c02c100c07024100b0003c0c80e681c03003480060ba480c00c0114200c051400f9150010440f030840d40c1705801d2004503003060040841e0800305200c03000050380b907486888407061040c5443ca00b003030500c0d9141d92080c40c81d074010850b0b080c80480e01c0f491403940012900d00e618419102484441d2030310034005060b84100c440f06082003401110701e1455111030040b15107280080007103980c2d40640554000d142c05240030202d40c0c40d024402600074800481e000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 362527571 1250 362526321 362526323
    0x40b0604110a020c090901090209070906030608190201050c0f07170c04020a08160e030d0903030216031101141b280309090c110f01050709230d0309031b03110607 71
    0x401d04d02c0094010088004e01c0108080d1056407200c00c140b006840d6512010700031000e9031078141030036041c42005800c0c0c459a40040146070b006010340e04010f038244844000c01c540a00741180e451584003800390400142821801d030b44d01c2000750024580f982801e03501c1000810310160341d180007200003000160703c00c00300b641c00001c0360305011481400b041c0726149406e00440c10041603030500d07040400d04104840c2034540120340711071001c00525030148015481d4161080c03401ca200c0b0b040d5079410348142140000f803410084a04c0d100c4007040c100300300710398504403819107c1080f21b0003602d1565440d41e22811221400c00c034280d1040150108105900410341c0c50303154410a00d04000605004100005c460360402440071550031502e20b0038841055050f03050300c0003141a00d0800000b070150b14660388005003400c0280048503610881605800d1480c0701260320000b244a030703050840d00e210880e0006000f01d20709003110380c02c1040300309140c2e007181d11402c4080350324118141048028003507040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 362528821 1250 362527571 362527573
    0x1030b120606040b0d060609020a0801090b130c020102040b072d0b0a051b13090c0908030d1a18090c060c0307120201150e06090c0705030406050f12040b0604110a02 72
    0x10204502d80f03069040021504401782454503043d1042c0c499406407040c0d9404565002e9002818221040d8400c4000e805402c29281c140305018285010030410f483d00c009a201a41e510440110301ea0310070740440c1c0081c824900b48079100c0c046410310311012030640042d00e0906c0114402c0b0f800d0640a000c03085002134005400c200c60350b464448400151a0041020010041c07181d03002e0103503030810002c0e010b00c0810f0011101e805e030a1016a400312280754aa02c024071850f00d2041000038000000c481408048400c0452035001c403070b60407030895403160a01648001a04225014803800e41c0e0440d10a03d00c0d401258080b416403010700c0030f6403241210003100c03070b0420090790000c9054008001119003040c4000112200d8245840d0250200d642041074655180d006008c01480c1c441da2264000c0c80201c181850721510340d0310350740e0340c1c8a14864032041c0580806c881140001020a0b200d501f24401554006480c2030700d0300d40800359089039a1071160386800364110390700c1451000d5034081c02a41d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 362530071 1250 362528821 362528833
    0x3031124010b0a1701090b03070501110a030c0c120803090615150702130608100f270809030a030f0f0314072d0207080f030a02280506100501030b12 65
    0xb650410040e805080e812051250903861165001080e4103140d008094200700001c1680c2403100b058101341156118a0400c005e81062070042034003c205014501c0d41801c0c20b5000322400d140400522045621168801c82c44841107014440c080f00214414401281910b4040d41c480c3c40000c4004d80c070300c01103500300007a035820650850783e803001000c41c0c2e03000410016205099084000c19641c180d041038103136400801d5a140c0b40340640c090043d00540007101071192035804118403100a04e41d000b207811848201c50441e0604c0412001c0310002d1201070203071001403080e4100580003051203446140080c1d43c3c1440c4a00b40c80c407038400c950109105080c5080a0780320144110760b00518200070f41d108111000b00403101100074103d5801030304e4607401504002c2d02e440c421034140340f282c0c086810749820400290092903400704060b150b003a040d0203200c03102803140000d55030044050400525501c16101070181050039810342e04111340e401da03414805480d0040c217224090100580d1020941d00171 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 362531321 1250 362530071 362530079
    0xb070810030f051f0209030d0207050f041d0307060207021e01090e060a0f03050703021908150c07021008010e0907080c040b040917070204150b0a030e030d060303112401 74
    0x5002c2e080380d50003041114a5034695049141e042c0310b00b141e50307140e095800950303c00a402d003071012820f4440360303001401c50700b860300c404103c1c1980304084242c8075998981442c4075000f20482d2020000310341038200c81d210001c5242810007540290342c241e101c1c01e003221940c0ca6a030f05102c2c10340040c06060b5520b6960601c1c0200702d82c040300021b45010ba00424004001c00c0102146403040010b60060740189002443c41c010702046140c0d600601000e9044164144007a040006403440b0052150014003513a661b21485440c040c001c040d0b000b17600080804015016941c0860101d050794140c4090300300544a42400c4d030342e0ae513854410b0b41c2d1203410168550070b280c905607000a12002d000352001c06c0d410f955944103d50450170001e00940050080340c1c160550070507100b060103000c1086076013071501e17041454507400703405072019140030191106a0a9843c2c001842035440160145a05101e043c1c2c0f24580607154004440e2030600364480c071940c40c0c0c4203405003202040d030300400b0210320a259082c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 362532571 1250 362531321 362531333
    0x90c020a2f04021c1a0d0b100501140f0d1103011203030c0228022e020f0721030903021201060305010e061b130308030f090f010c02030d02090a0e0a02070b07081003 72
    0x2500d02120f15070100d040b00301651034100e514071005100d0202000c023450801d40103401060b8071b8010301d04201c4020300c1c1d007440b824a00304403240784966034000c0f51283c16214040010f0010801c102a410802000016004182400000d0040e1180c0c4051005844d0700030102da07a81c1c59800308960490000c9451038010360100310350301e002c4d800502004030003c0303d2200040231000f607a450055016507141643c0c44140d06104290390031800002074030070304c1e1a168002019920b902041104008032a00703010400d402031350341d0401980d01620300c0c03070041440700b05103000b08201d100584865085c80701030000c2c4500807411a120760718010340c02c41c107002e03101c1c0300341c04580204c0303440707040d41c0c4c100e0002102042d00d91000e184141c40b00c170410749091422207038071401c10485280c2aa22a030501801241d02030b004415142c21142204005071110315542c0000d4481d00542d1001d000702a145090190b06401c9400510038280181040c450303948404400319200a8100d4040c078000390141d41c2400000c40b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 362533821 1250 362532571 362532581
    0x1a0d0305031f0b030f1e070c11120f1b010306031203050603191217160503100302040f09031107080c0411040e070c060e070e01090c020a2f04021c 64
    0x99900d80003409484030030145240c2c0c820384006800701125400c2040764001400703220a40301414222059034100440050300054418a00030b215001c0c5884605403900c3d0003c40300c80e500310042c12112498040710010b03031185820b003395028040c003003801c0090355019001d050b045035071008040c4607800e8012411401040058075155140c01000c03189810100c02c1c0c590f45034554024001480c04029112015007006225428445540314400c03c01000380800001c03d00b90701c0c19400d01959a544030349045e031303510700d4542000358407034580703001141c503c4a150b00c501803507840f03901c0c4d40c0f640c07054460145513514240c0c81035031002e921910b0a50000d042a070071103642042030b80e0b422800d01d511220203621400c001c851200009403070100c060240145402032212002d040000f4017905424103880300f2003400140101070086d030321a065103074a54400c211050311079400c6600f4039034054031040000f08240b05440104024074030914108400e1405108076101da080050b10034000c01c2405400c0002b80c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 362535071 1250 362533821 362533861
    0x3060620031204031b081305040506010c030c021c05060609060a0f031e020a080f010f06060903020108091014010f05030102040b0304031b060632010801050613090f1a0d030503 77
    0x400710189a40d07440000301c10501e0241e1151003000c0c3c50fa4044001b1f030180b6243d651040d4816070400061001d0359801c0b615250a0079054641860b5031582400810301014000d80c031074500388400020b05043c0040424100d018030320454013500c654940c0030800221038400d010f20608042105410400900402000c0b21184a404014103072100300d0f8000a00e40101580484020307008407150703a24010081c4125150102804000c000c441d0030010001c00c02c0b1803601009040c4a10301011481050041000482e144121241403100440c04c0e03690b1103502c0d00a11039601c403c401c00401288034941802030301e09440581440c40c3c07d50b6101c0d00c08907442c40c603110113150b030040e003028610046203883c05050098051a580440d4142940c0e9038040011441e102d00c0c48412001248100c082c0c0e4082e03d0a41112400c0b500582c0b524010100e1980b021566441148441d151030360361620312005400c041708220600e050f14407244007500601c4130041c0d62900c020b000070400c100140700c1c1483c40800c0c80001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 362536321 1250 362535071 362535077
    0xb0909010b16120903060b0405090606010507051002070c030b01080307050d0e04020910180506070f140708010e07090c0e0306010306020a0228050d02150c09040b0d030306062003120403 81
    0x142c1d800d89918a0700404a00184000340d01480c040c0b0034460340d8025a00240b8065a0422083c680131900b40d80394080a46180c0c10440b0000d1070400340074040041540012400404550728042441c08501e040e9480c801110b042c03e4540c0001421000030050300c16194000b000b500782d40d100d1040484028500c011640c0e4400c0c2e09100708800e40c3c440344c070b00f07114020881c0c07904060321410707494a8031861060761046100f50000c1020741b0000703261150908906920590105400c680e41c000d260401e0781d5174009680d55880d1941041c103440c40084c0701001c8940d00350b81003009e0307002d143c4121155181600a190954894001000014415401005041d00502c15503000603410103882801d0354502e914141c07c1104100210280030091010500803080ca00003030003801994408040304413402000c9041c1410042400d00007038a640d0031480150400404a0030800c20301d2801400030051030160300b0004110510640400d403c0094a03025800c01400840c00c1100d14a0121500d00d4010411010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 362537571 1250 362536321 362536357
    0x106080c12090105060f030c1302130305060a0504030f080105210f0d0903020a0e0105090106050319050a0c0206090705031e011119121116030c05060c0703090b0909010b 74
    0x48841803078449014240b00c01c000f01d12400c0c00d100300b00280f842d40440501c6600b00c22020310070340d902d444110480d45100345004d80c64075012413014a090b107440d4000b801c0fa01801007000000c00603940140d200d0380c801c0d1207a03182090300103012607401d0000d00803207070081c1d00820016036034100c0d000b000b400c03a0760650031200d4100003c2102800d002540044001051224206200714a01900400c02900700000b00811540c50240000c10400040c864501841000408100d49118525404114044403241440b050408203615001040c0c42c40d5014014040c20001c107401c1d003800f2a2801c1111001001442030018130301072941c07091841c03c050007056513924a02480010503001500c100e0f2503040d04881d00400028010308030182405402010500d080c003c0d8090f41d088a00352448406160b01501d2a49503910f0182e90b51056144040c1c204d103d10020084803504040081030b459121355120220300c2c1e59018074040ca40144004143e000320804014000d0940c4c031760142200c82440120056 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 362538821 1250 362537571 362537587
    0xc07020d081306080a0908120403020307020414060f0d02150f04080d17100609060c0201020309041409010e0303041101030903140a050406030506031603081c060905061203120106080c 80
    0xc00c0c2da028541e03101c0035121848042002c55003041459034016001e01081c85010f4071a86c0e15889071040d0105000d0001d00e200201d02454070820a540420754084c00030000103005561848040d402142c1161042e425960000680d0130700e69500301000d0360140281c440401f000f075200d80d690304003a01c029100c2c2c030141300002c2d10348400c0206c1c0c22031800d03640ba0380c071807a144903585442c0d9050050141034410702d40ea0b01007111a600c5150718044481c1c62030072605031541840101e040d03118654a02c2d41c402d0400d000d80f41085440c5568901440c14440208221108400c080e074884c04101ea01408004080c0b45a00084d4002e401241d242e512034505000c502c512041108140c0c0c21200d4904001480030030180f01468040c410181c10001c1100102801c01c503c1182e1101e450490200421080001c80c040c5a03c0c100703800001c2d0b170356985410602c100c50300d40082400520040b24100c0c0318981c842481c1c460480c4c04412941c21084003c0c86008503030800780207491008010b04070209110302085214 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 362540071 1250 362538821 362538833
    0x90512031506041203031d0d0807090306020c0705030d02010911040509030702180601120e0a060f0209060408010905010c0926030702040908090312040b12060a05030a05030706060f0e0c07020d 84
    0x40d103031100c03490030925005e0900408840d00c0c88444642c0b80311404418541800010f850000000a80b030048050741d41c030070044a00c54140e03813004142078008144903800600220341d18064800a42c00c07110300c411f448600300d090308c24420001d007812080c000c1c4001d0038101900080c3d0b00050050881b1b00d05200755000c10101e022a525880d601580c038802e01582c0e40c4d0081194031b0720702400c10284414928101017030b40303d2954200040c0004c0e509c0340c21441c1809641c055904001d0001c1c0b10a45443d51034074007038081c0c041034004840551038000c1c100f288074000d00c0304c0c0c0140c0b841d1901d400110070036680001104080541c4a48a51005101401c0140c0e55030142039201485401e0f80380e1104030303010a041c900482e01c2e29030100303844248018802c222110f001d54122030031b0b03c0801a03041e10b030800400c0030034460750400c84e0035000d54036440042c0700d4000000c3c040548500d0081000c96502c41600e040b412090180000c400000c4001c20603d01c00d00c070240c00c00d2800280070b041c1c0882656101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 362541321 1250 362540071 362540077
    0x61802030c07050f030315061213050705040c0c02150c0a230102040b0c100506091501030b12060123030309040908090a0806010603110f03040209040f080d1a0301090512031506 77
    0x1249151700000402c14298084035401c1400b500c2903903014146a000788a2045a004c010107903000212400c11f0041401270401c007500051101802c10000c1a00222004060110f4079100341c0c021140302c10560001c21120049950301d001076000303001c4c10481e81d41d4503e2803030621200ca80303201040c41900c003034501081c40184005c01d00000c0103561380705200703070702400c001d12010861803081c604400c000f03541d1201c041c0240c0c08400c040045003210721002c01a802801014012a04150118510b03d40801c0001e1614142d441c1d0844c1800c01c1d40b482c021812091064200e0a81c16070401d0044078002c0c03d254005100892090030046e0400404801180c9044980d602100150740084010030501d5050f10504000d800d2150805140100da00700e804203901c03015000900540c0c2c020001810300145c407001c1001240d001500d290b46411001c800700241002040d0343e8902c2c0c0d11132801c40c542d40f50510854544a601001030a9500006550b00426410041c84c4501c13030b01c0d2004000149988030001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 362542571 1250 362541321 362541343
    0x708030f0414010201181506120b040209010e0912031503030307030b010801140d11012102070201030612020306070305071818061a2b0204030b1603061802030c0705 72
    0x800d40c44a01d0308011440c0c0014261416043d649089840114103900b071806c04810350300310030141c2a6190750303c0d00c00005e00700ca511a00155107120014402c1021307401415001c1ca000701c81c07520326a625038500240e040c1060750705550ba60311a004a0030714491100c05182d03c1147d07207000c0019020400046400c581c412074030074002903500d8109002a680001445000d4203001d2401700811144030701040c130181007450054092164454510030503031246005d40210420354403030806801401403080042d400056040f40400d04288010074190070b030300c2082e2a40f41c0c00400070300213170312600c2090380103001c0a0021401c0000c201c01403018588400d9141c2e00515042040c02503d0902e540124129055500030f0101c0303031a04804c2041c1d02300c951065030024503682c10b107001202c24180000000f01d03800c081c0940000d0001c40d00009001440b49098491030503190391100c8000104021011075915000305903a80c0200c074500c0e9040c108541c00786900031860340642d0b02d000f40c0c60701c82c2440c010b10014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 362543821 1250 362542571 362542597
    0x20a0b070c051c051c0219110c0102061509130c0b07030314010503150907030b0103060911012a0515090106180c0c0f02062802010c080603070e0702070803 68
    0x9a5000308a000c000c201104000802d00340310781c14055500400500c142441580c8407100c00174003120708074040e07048841c1e601074480c64039280301d00f51501078001054001000300c28044c503180c0142550000c81c1b039902c1071240b00d0086200c1304010003000840180640104425030403400301c800084d80b001c01410107000c0d01024a41c4580e0740e0314000f02a60035070640c00c080e4031040310040245031800900d28100c201d03062005002e0381c1d13403856400d15012081e0f2015040c46c0d1410000000e0204607805101d955000d0001d0705c00042040c80150b800f4009070f8000c50303800c1b0480741c00d0385505250035450101507104200b034038440c090710343d0404071051041d1807600c5d00d0303552a9810032503102042c04203554400000b030184400103802e08041c0032202d0030040640441c5411548100315070300c80c07084440d07942801d000d4a02c0250b81c4a16691080010000140558601500f8800803401030481902c2203a0040003000703000e08001c00c040d12450060000000d512800c1d00101c0c2818080c030143c50582d40500d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 362545071 1250 362543821 362543837
    0xe01060b0c07080a172104080409050705032701090f0605060118060507080a030e101a040b0306150301020f030109140a060b1204050309120304261b01020a0b07 70
    0x503926042c0a2994842c0500e507100b031a100c00000d07045001010300711120304d041c1d038170764092145480c0d1400800344640030312900503040100b0824440090015201b144204010300da880c444107650030321040e19011a020012207801100e061164900380020030810300200d0b2842c800d0307070380c00900d107400b40d006c0782c513103443d4170404c101560710142d002c0c542501401c140782e1540c94480e01416501c00ca4078003a2810754001034012025003ea0045044046104216030300c0300d00243c0c07003400801000d20b400b0924003004003090b040d0302d07241c095040c181d40300501621081c0c862041d0b10204100c40a0300f1505550244840c2106880e10000b450003041922408101c5031030465402a40b103100a10410060b883c114041c0800100c3c0c5041d18400c420386056940d00340c0310780c20545c1c990b0203440342c0c86912091660b144c0f400c0d20700c04005801101c0e445804200e0345032203131400c0f0700d00744400b058100c030715841031603441c0200d010065090a03924060041d24070220054a0b801144038013120581d020031850 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 362546321 1250 362545071 362545087
    0x10c09080f1c0f1704050109030206090c01050a0c0501060506041d0702010c080112030e21070f060f080a02090d060b01020f07150c0203010f0501060305091504020d0206030a0e01060b 80
    0x140164800155075201030400000c030007064005601038004968104500c414480b4651070040107040580504c801c108004d5141034a8014040e1151020440050240c0004107413403140000b41d20044800c141c45980c20304035004802c03640c1344000f0806441c0c3e5900d0703c0c0001000e480b060001c10142050140700484000341181070f800d40c00f0003604120071a0314001501082561000300c4a055600356070f0b0f84038034502107090072039a1903c103550031540004641d04902c904c6109076200c00c030004095050311140b81e9520640342c00d8071080d10035080403c601b9811040c1640c0315181d81c079403092210303030300600701004072010601c02c2d15203981c102d0f501503440700c44401d1507804100a401d4034000d03c00800006041c251b83e50182c4203a5074a030b4060001c0eaa03880b0341103540030b4024000c21540a0010000c942e51203400802511050b2420102c40c050f8030456400c41381c4140256101e01c0c4c0141c400003e442d0359a00b84410f5500c0100300d0640c0e60740c0c41c860441503117001e01500d4014a0098802070300e450003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 362547571 1250 362546321 362546323
    0x702100e03090901061e0503060609060a0e03150714040b07110112060b0403021305060a0510030e0123010608070806010507020114030f0106080a060303140a020c030d0503010614160f030908010c0908 87
    0x1c1d06ea1001e080c08014000c0100f41d42c0c445049440c900d4098a4081d1148002042514042541404154140200d180b542c540556401ca101d12400079540d5001c40d684519000b003c281c07180d0f0040c0110644204010801710710420382a03445800c040c500980030540080d8801e0444800303030400c0c00c540c0000a4200b0a62801e4580c1c2d0b01040402c40c4100070604188000030310151440c86070364001d2001e0101300c58500d0003580a0180c41d0140002488100d040c6c0440005520394445280445040034001282d050703c14582c00d88503d04580f649d440c50340310f9000542d1240c0142a049040000e6003049010f5400600b019501540c04030a03540c0307145d410b100780600b44c50801030030b202c8164075001040010990080d055807025202113905955181d420b1012800c0118080005805115400ca031028080e400001541200d00656130f0079251000760240f0351462165200200c20b40c1403203040365020800003031810824511a00b00312100d00d80d0341410320309682d040d10240010400c031203020030101c68 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 362548821 1250 362547571 362547617
    0x30c03022a010f031518050a020a0f030e07030f05030a02060c180103091a0f01240e190f0f0302180106090b07080f040308030613050702100e0309090106 67
    0x10301030080c4200c1018030345122010304001c01d00c40d030400c01d20035500d40c0c030b4601a034058040e4103064809a442d0b9070716514248055043c0c80c0c07002000526003400a0880306c001e10903241c4003801c80d81c1c0e00d025002d840c9411000360803148003408007030040700000400200e054224150603881740f005036480381e0f0040d01c00303820100014071048000404101b18500e907207800001c00b0954000342000140c201032410aa8004450010f074141c4815900d001d00c005002c040021a0403207110440000b42141050740050140c86030350383c584045400d214411200f854000182c0501c619100030049d0ac07141c7d5605a4071209006901c001c00c550194a02441981490700d8115802d040031890415154034103c0c00800801d641d00c210040d00c08041120b80400241c42c0440703a044040f00c504030b403956141c1c20300e428542e10030365440c2c0c459000c8850300c2204000034004c07580724081c140c01a0903c00f08a82c50b1402403c40400c1085050100b00103d01071035481c1c0b081107001e440650f68802d0b0f5060021040e9015030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 362550071 1250 362548821 362548843
    0x1508070e030c090106140d0e06100b07080d0908070b0a0b0102211b07230406050d02090a1e050c030f09060c04050d06020d09060e0c060a120b1c030c0302 67
    0x9009500600300d152120f205071030440c1c085103400c17070001e002d120904445015a4600c00c802074201031206011079000100c05014403807800116100c2551a0441b001610821100418400040c0b118030b4221200d54841e02a56002d142c8403840d00c1d9480d694011424021203c003c0c2145d80c8a0141c400307540d040011500601d11074046c040038040d0351074101560300800e04551700c1c0ca01c92070046030024006003c8080186110b0806240c001c520a040040407003d0181c40c0340181d10304040002d0034074044604c1448030303801400740562601c2d10114180600240c500000c901a4040340390035018405101d40c902c20000490400c0d02c4c2e05205054456003000584218071690040090285000f0b00c0801c232406c0322003c03602194400c85616048010303001342006d80c5c0b03105107491540002e200c0b46070810541c190f003200907078503902c42102c2001403038000e1174003400006488008546141d2055440707943d11800007004403d03410700307920800b250002070880c01c070300082807441000101070301040415894 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 362551321 1250 362550071 362550073
    0x50906011a030f150d030e03160509041b170309030c060c120313061d010605010302030114041140242102071a0105061e041508070e03 59
    0x1410803000c1c1d025040c00058020401840c80102007100c00f098090300c80324400003d4143d601c0d911260a01030084052003a00601901034008580c003114401c200c0041a0740d00206420225240e80d141e00b462107001d821031103400b01c801d480c0811a4141c2c4038460105184070402180e0390f16081d0149414034950050715401358106002880042a01150080c0b0749091103002c00d880e9503414a0540b00340600c002e002d0041407030111918540050143c003928089440c0000340801e81e606e070011001c91100748108200921144000170603480d01d904400440c1c0010a007507410702c1c580014404264044800a04034140f02c1d10b01c00c540b90003d00c07051291452036100c00404249042a1040b041da900c1c80c01014803501111130045840c01080c4500004207641c03004000302c0d80d17805003100294000403060f0341c0c0040302c51003040c080700c40940700b50584101411150520350901c1c441d01500c80300e049010001601072002060301c0c244502101c083c11029681c00240d800c08610107000d45140c06901402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 362552571 1250 362551321 362551349
    0x6120e1006080309041505031207081c05041a041e03030e03190809120702040e03130305240c04060e060d0c030f060602010b03150603010e100c17091009020a09050a05090601 76
    0x147c0d0ba008140c640c0d8908104030700c1560b8404510748101141714000070342d990340344003248d20401e102155000c20b11407442699045014040c1800d200440c00d070444005000b2484146142a181880c0a1010422f44070b401d0114001d42c8103050982075812a98000aa80c02ca1b00d650b140242d5111014603000300034103021300510164515204018880c1d4400030b40901e445200300d1200e2101001140c00a00b96038401200380ca0700d07272501036207407108101d21824420860241020319804080c0540c0145262410186440e150150a89040b80585400c2c0d5010000f030154014a803694046c0141800ca29a03000508ce44a450004221a880e82003042160f1420a00710065180010003100c01081c1c2c40c0701024a544c1e52000070702500441c0d5031030610703014111080c01e80180c65000364800340e81075150918906080710101c05907600c1264040b900d58800144403403a130120343c0c0b060b5481070010313003481c3e1482d032203941c0300c1c00307480c2c0c01d6030b000c1140c6590f603041104e511024810070340500403030917403c04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 362553821 1250 362552571 362552579
    0x20306030d140f04080c3d0903080c010609110a0206010e0603030708130303030f02040b030a050a0605030d0c060c08070c0b041707030e090f0705041809061b0201110406120e10060803090415 83
    0x10500d0758441111010200c500c0c0700111f554060300c0c007100250303842003403241e40f40700210105e030103032215124450a1508101c4600e0401a041059646100d03090f4020035040c1c3c03802540145190014100680601007040743d81d0100d014080100804000440ca03140c1c071501d1446d0040495080d4160703600603031f106020a200403000c07503040741d8010b85812800b2403da01c44841031801000c003584107a5151240f003902c0c00e102c80c1c12848048802e4003038901000b103d40d0180341520402800c907000400228420000340002e0250351180760080d00404403c0c07101803240c3c00010270399105d804140d01040000107030344010701c0d181103905d5110340301c00a6580c0c24100404058464000c3d8016251001c0c0c04a2104100e014035a000a200c01e401c00d900f880001c00c8200d01040020808160784010350800d030000704180c0c02d00044504a40d01980c402c1028146441540d0050071f004907018100c0c000d0020280b90552280591000b80c80c0c1c01b0b01440e601d0000904010440310101241c00c0c2540e88650208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 362555071 1250 362553821 362553889
    0x30304050f1015180b060a12050610050a080c130e0a05090d050417121809010b12060603180a12020c0301091515090905060106030e01020306030d140f04080c 69
    0x1c04486000145a192013890304010000e0800c094030550800404981400200c0e802105400040d20021b800c2100f91501010f0002179994201c0e032a0204404111b0307104524440c08409620683c24001c481c2000c8841082070544203041d44001f462403a80410300076070880314401c403504500032100528110000140c041c281e03006d24070521611141000f8001280d030f50900210400101020a5607600c407250750034111800d010340b40d0300c0d021714855000810f059803040125004901e92207400c4d842c56841100b08503042d8001821050a540d43c40005803d126003002000e2045115215440030b88280740300092403d00381c10005c40c0b084e070414400c50089150580941e079030002c6041c002c2121140300c507442d072609605620559006141095080502802041d81c6050310314554080c01641c40c4181410309130b0005950603540742d040229a40841d5004642d002c42c042d142d07007005410b00910700c1460034a604554802c000c140c001c0c0c0001c024620b4084500c220215507100c412404a400321058 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 362556321 1250 362555071 362555111
    0x1030b09040c0e1b030906041a04030210090f0f060f050604181407050d0303020409060b07031e02280b0603070812030c070c03030309120e0d080912030304050f10 71
    0x40044903d400e0b0100341d00e589660070008003460001c0350b050780c074185541c0c81599410102c4007980c9410002001c0c400084504001c01c1c006c0b901540281000c04891002d103000b48009001140c148521036100e17000528104a05405035028070700c001000d064521080e016107034000c0c4000d1007103141c02c0b40401d20386280460701c0c8150741c0112440042c90008e036a60351a14440750040c1c5e07031094440e07001030308041e41a00140150f40c2040420302046649800d603800a014405004010440040454907000364040310396000c00748900c112119402500020070706042d0162403061548242030f03244043c40940600710350000c0081e80203286452030600690b80350071560311050216000000800d030f041810005445120340c06c0540c50604640c0c1c1c0c41c0180003840d00c1e070b008590f4030100c084014000e40c05421165128013001d4400800011030360380310340311075000d0b804a90740000003e80100200004002840c0f060f841400142085010350140a15117000041040d095904014003286000400b00b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 362557571 1250 362556321 362556329
    0x70b0706020c01091b090608120d020a09030c062c0603040b040f050d03021903060b1b010f09050d1101020f0a080c070b0a1a0f0a060c080f07030504030201030b09040c 73
    0x80180c03904002e400c0140504450b80c2c001d000c0350360341d195074480204145107500481c0d400000800030155078111850b21175a100b40c00000c00360003404008803000503a0020a9070702c94a1401a0001e83c50340c1d2200c003001c1003900203400250650901203030340701c0f00940c010f062000c48041920a00601e0001809a1000402c0104036250081c00300c5c1c10042146002e030f030072592160a407090456014001002074000191201e40700c2111404484564000d100700d505561f200c00c00d031444d14000300e8180d06a01450b1200c50899035070b03140040c048060703d00c500300c6954400c0b805080004400729004188842400c41c681190b441000490703c81c0101d4030484000200b0b60920000d1686d41c0d1134480100d015816000e0b2031110100104242c03940b140d40094451011030346074540540413075051202c3c0015108a09400150b49038044c04090702980c640c0a1031881268640c2c0351900c03880001d049a003007031001320049030740400d0500c11076130103014100e818182540c4c038800f07030728058641d51484052442 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 362558821 1250 362557571 362557583
    0x14190f1a12030c0601030f0c050409050c150904090c050405010e0f0604050615070c060305010b12010e090c060d05041a15040b042418090803010b0331020909070b07 72
    0x40841c280401032080e070b40d071000b8030001d80780c0e2036a69041c11244090480000c03102400c0c0c0100c046101c1c58148107244a03a604680100000c005000c140700c5c21445490389540c0c1024280004502940d0724003c25185034418031a001312246070500380025120182c0020760190b0802082050f844418019141e2010044401003860348444002c1b0b6416483d04015042020000400006101d1140034080032282c0d10340d002c010503a83c03002d10480a00840b8580118a1055801004040303030f201d58094101e140781c41581c1003056240c0c0050306540c483c1c072419103c6c0c0c1c2c903501000140080034007180c640c00c214092800e014a007001ca02481414445407103840b60360b8400036000584c5507540712440002040500008454001c406410f042605108508400010104040c0784068601070050702c90340c080422411642418061682ca81000704401d405000303c1c01030721140c44650404415030815080700240744946401403001c0c40b1001414559039510180041010b2000e81045441280d0050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 362560071 1250 362558821 362558839
    0x6070815010504050411031005010305090c06030402150307020a0c0e0124020c0415030b060d0201050a08071b03030e0105060d03021c050903010e061807060e060d14190f1a 75
    0x10041c2c0d154090340e00055007140c5041c0041440f012004021801500c20648a0311841d550300011010b030341d01200c8030700342500702c0480b00031281021000341da001440100010b11000e98600c500550b40c0007251000c0c0141c4c01020311a007401152944070000e069690f4809a81e9810080200306485002d582048262403407803401e908203200344060301c010352004000784204100c0507503004604c1c52602003500d02c040e596003c5240c518049007016030081e8180c54083c1060b500200c00c1e510b8003c0140100d0030f100420442c20382c0007540900c0e61115620948000904ea06c0c40045107084450080ca118040c00030700d401c1e800840d40005502d0f5516802108000b10b51849502c1102c4602a080100d5019030828031703109003502c2d01051b030740d104080c2ca120948044144000d41603403064184106800306002500f80701150030804010482c0c180c50240200d160100752280c0f15014800300c3d00d0385c407604207040c0071401c19035642c00b030045030026490081c8044144800140c0d00c1e00382d00054103115400d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 362561321 1250 362560071 362560111
    0xd02031b0f0d020c040c02010203041a180114040b010e040c090f0617070e1f142e09170325020904030201060302090a110307031508070f030c08060708 66
    0x20407420310040d1070701d025a280c2580c1e00c10041c0d540c084201c80c071031146041504459003188148280c1c2c0c45543c12800070100208011030344010303100d014240b24000000e80003e60b4681009014401245106109000161805041401462106801c400300010103601800302180c001501d080541c2c1442d03400040b021803a214002c0203001c15801814458400320041102140101d82038044841c01000b01c400390323507a10112901c0104079128150b5135080c00d1002c0c00322900004e03401303918440190080b010780d4044c01d00c0f041d011310030641e0704c8064840d121080310420340c880f555500501110505d0b480210b20b20711910344a000306d51040c0483c1c0c2203072802c00d1141e200d100c0300c0070704c043d00a45030745518181818001c3c060170306030005078040c100101c0403602d180710318800c003012042400d80c03103406e50f26000c000f2070182220030040104041c0d6448003040c00709003070040d48001c1030003550b5120160318500d41000441c8041c0d1205d1229080001005161900f0000c0554031601c0d501c00005c0181c51 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 362562571 1250 362561321 362561323
    0xc3606131a0909160b1201080a02030a06020a02071d04030909180b19020c0609010b150d0b130510080118120c1a0c09011205010302010504090b0402040b0c1e0d02031b 73
    0x1622142500c0c00443c15001940170300e42c0008051003c0c801203448030320b0382c030390b00740941e42c420864000f03425030311650b25200802d181c0d5000e8103102d5207602c1580d1440d03030f0b5001c00b80140c947d4418800800c50381040ad00c010150050200e030014070360702c01c090240e65400719202c2c1c8414a1900050801c524940000381c2c8100c00044902400c0050340d4119181c2d0990301b0002d40d10403045031044c402e980b0b4002800f401d40713424480c1d100081c11400a10b031810207140300c298084c00c0140300343c5800049031030100010304814004d09100e00807210810074200d2414914600b03451421022411f659402810080420301b20607201e00e121160b4141805101e45500e4036080b1040081607510350f9111803000d00401d8042c50b4002c050100c000d80e206500e4450b184a140c084940030322000340861000c000411a00c035080d04880c0c1c4405e00100f0050900741da9140c01c0700300d0392106084614542000038100a0700720f100782200a0b0034103001c020014861b05600103903907449003c02811514482520110322014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 362563821 1250 362562571 362562583
    0x9152403030c0a0b251b02040f05070e01030504081603110610031103150a0e010b03030403060b1206010f050402030a0b0d0b04020102010615020c3606131a0909 70
    0x800a012030755a091605881e40d00d030004540210b5000c0f4100001c144107568142c07040c612058610403005402c03c0009060350628100d40503901614204c0360210b015035118403c0d00740900300140042030130310700004010010000c0000301818140340c0701c140f00c08514032809690030000502000e1105882d41e05050f00c003405109100e006510840003007206000201014138100ca11681200102072030000030152541080800c58040e4020703a000941c502c0751940002d1960310031700d000040c646030307070501180c10341d40b25030016229143c445a40b40d005040c41040a481e090a8501070301c103550502d0310f0354030003900a104a922540e0044040750090516511000300d141008045071103407941c51030804030418046906a02552074203c000916100c0d150700c4a0012a140d405880b524209404001344441d80030f00042541b0f550014419041c84c001100140e10f201002880000385400d00420800725100c6000c22003860401c82c2443c519409082087e0410808540e034100960310010b02d02d223408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 362565071 1250 362563821 362563891
    0x7123e12040f05040f0902060d0c0f0302070506060415050409080c07090603020607030e011b12080c18120a0b0c03220803040b15060f070c0e01122a0b0a03050915 71
    0x1230008207101c8038180c41e0f020080d044031585907120b803224419029403c9014160000d0f01a42215000450a180544c4030301c13420112001401011612180454102c5400c4070040344c005000050115016108000240007030207404420f10441742941d0100300203014108004060181d1240c0d031324501d81c00b1f0301d100030f0310300802c1216940950550070700350110f032a00803011011030309000100e010070480d0030464907454801d24110030403035101703011300040d40b079164002c400d14054001d000c0c2c0001d15040c2002c1c055688140f1158683c20981040901e4a070110b481d940317608004100c410019088006595009400062040895681150000d018009940000d074000d00c00140000c040358200c0182c80c810340160725001005484118151100d4400c0c029000f40c07007000100c42e400143e00c1c502440310904441c02590aaa50f4110740c140c1404480c0c00c1569000c40100b50b00c00388941c107114090303129140304020500b401403d005240092809001070f1000882120680c3c4030010100c01c11a0071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 362566321 1250 362565071 362565079
    0x906110a23030c150a0507090806012709050606131e0222030303270b042312070204050a0c0c110406080610080f0307123e12040f05040f0902 62
    0xba201139070f907800710100100d0b141d40ca0140341501049210b48201061804e55410000804a990038101301c4218044040c18080040c0800601450101854040c110f4254811802040241080010864000a005841e440300c620f4191210000c4030b04200041e040d080c03902005039034102d5411a00b003600d1070b1144045081d2822100002003644c141d205400d03004412900b04404141c0c442021820040351001800c0c810f5800c020030007080c4940c0300200400e0011382e664040032041907078a81000c60101801110003004142c000544c01c05008081c2d02c210400310400a03014051400b5100c0900c0d62009003800d0024540085591070b941e003c00c020703281c041c046440c10716100d144426a11514020722040b8020301d189400501000029212101d40c0048201c0d490301c035000c0e01700c5c0ca003540020100501c4002e0048030820a00c9840c2040d40c12110310102000b600c03101410701d01c0d00e08107000389095420108001c120030b0029803104001c2d503408440c04a155100040c1c07500162810a4000e584 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 362567571 1250 362566321 362566333
    0x510030813080d0201021e0a0314040b0708070503060d030e06040801060b0304060b040e030d0225030e0f090601020703080c01020d0c05131d0610020f0d0906110a23030c 74
    0x701c030100d06501000c40d56010100c440040c040c4034200e00381d00a18040302c0041c50020341101c1382c1990344010f00a0580b162800240c4034007020b8615480c56410f807400d4032019807400c00d102219034000c080c9944510b03141820380c514244440451011002d91601078100500c0c0105426503545032400c0318000c1402400a2001a88520200105500c103440894419140810100080c04c1c5800342600e1225580061810708444050441c06940540d034518110b400d42032000d00d40390501031642003010300030359aa12006e0282400c1c800d0356543c908141d841f41941c0701c10801c0d00da9000804400766644421155200c491841015000e4010003880c11030aa00301511250915840b034050003c42d0115a141403455070b48003004803a000100300441c1c1c07011910000100541030ec2911900460030b80d104980100c12150400b03814201d00003044000980304501c02c01c0140e5021a4440f907000782c0d80b001d0000341044d6501d9058182580c80071003002d0030155400c0c10031141c107100b030b1010356850f00141c840c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 362568821 1250 362567571 362567587
    0x60324030d030c020c0409111e0d060204090b15040504111603020d080c19050c030d050a0b040b0307150e0114030108010f05070c12110a151b0c050a020405100308 71
    0x2c040c081d00e00b084801449103c1c2c600802e8902801101c03d441d070002d2000c01017603075482c04c0c09611100c21044020349285426030494030313290229188000c0780603020042e2a0b5051961a0342502c0a000c5001d1044d01003000a0b95107401180484d800c44000302c5000030707000c1c2c0b4024102664011542c3c0c6001902c0c0a0184400345500800e1100d02c0003860b90b0380744090f41e20381d05d03441d10b50300482c0e4450b1002450040070501e6035006100a10401c2c076180d00700c90520700c280c4480c20581d40c1c225110407109484e083c3c1a03c20b8140fa0064400211044002c0c1a500c6d0500201d016400e144044010800100d040e410842d81d01039981c0032100070040c41d0850781c0b90384580700c540c007070b041c4c0040340101c007840c2000044009100d5a40b012603a0350100c1c3c4007990055034041103444050800c110442c6014032407075500080d10b00e01d032001d2401005480400c1545008421101c4010021014000d10992101da40c0c00590041001c49180740d040718001541e4441c0600500e40400c1a000108a031800103401d075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 362570071 1250 362568821 362568827
    0x20408010506030105130b070509220911010c080906091c030e010915050a2a06060f090b09010e04050106031202061501090506071509020402070b01180b060324030d 72
    0x1c0d114410a40090146458600103150250500c0d28040d040c08001c0c00400c000070310500c000c0580c02401131140400b011080100c820103002c9146410000c0da030344100c4404c01c1901c1014118165003400c2240c5800c0c2d107502c55100c503104038051a1b00c00c560028420181d55125000320811020800802507030101c640b9026080c07800001c005030204038046400241c0c0961601250010312403651035030305082c20b03220b05440388494640d00c0c81c4582d440300a2100ca084441d50f035030b020140540c1d8007040c200c0ca0500c10810940765500120802410300408032016100c80c00c00c20f04488020300494180d43d03c5050603401030003117030001000200640a01c0304110390004456001c0c1034800301c8410600b0300c010054038540c1c036900c20190881c2c01032060b0b6001c01e4402070740340c3c0420039001c00803070074443c10f900107412603211281c01c6810155a40c01442492101c66007113410103210b070002c0101c540364800140e028000241107400105030400d00100c42c0c0000400c00840354006011501c070781280d0780000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 362571321 1250 362570071 362570081
    0x708030f010f08030301050a15030f15050406080609031903241508072f1c02060108010c02030906070222061d131e0c0311090a1e0b0109050402040801 66
    0x5841c40c40d49200000c200b9030000302c02c807130487e400180411551880c05542c40758140d40003408609059070b40400c83c3c9082154098140142c4005034040c881e80d00f00020441151341c150886100c50340080100074040100000310741700c440c07940f02001403c41000100300c000d050000004004001c2c500701c0d40101c501d449400c00103649502c1c0d8041d41702c0c45411012524860202c0360080003a401c00c0c07146080c0d0302c0000314101c10405924440240d800d201040a190080b002502c6541c0035414180d000a164140582c5014107000700082c00703481071040009540380a00d40348607114500018580045503212042d252400703010b4217041c40f5100c06103003900020602c620801180c070448103c0451055150390381c03d440f0700100344000320042116100e0a10040c151400c42c1c0d4540301c0c1c0064000820301601c40600114428100c41c0740c01040081400100c1501401c20b02c1403d0610b0a41001400c105003808218110004c00183d4094a8801210708a18a601080e00144006030200d0112019001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 362572571 1250 362571321 362571329
    0xe121306210606030b1002010b0906120a0b04080901270306020a2a03020d0306031707060605060f0d14041208100911040e070905030d110102070204020a030e10060b09090a020708030f01 81
    0x186d0381b8002100041070b800e8a161841e42e0360b0004201d80042e0315441c200b030041c0d26862500c4111120302801f555140c00e010410b4405540c541004603100d40950307413000b8048038108046200401415001d2081ea41140d503501004000640105581c1e25240c0f0490b82c030f80e00032035078614504003104076000701c160702c10181c1402d400600a180c0d580b01d4a41c024010042203030340c440c1507070f40042a41892030b80c807a0000310301122940e460b038400099a81e030340360151084c1c10b90381503010758035a150800b40040b98680c040b0303660200707410700c20880411034111a10901c542c15003000c5c0050b5035005966951001140c11641c17003245030205100140e0300c41c501400030f40c1c880e032141826030341300c02d001511181a2403240c41d0f4141c1c0240901c0c2d4840344114058030b04c1d4990321001600b81002d640c000340503030300244040c0c80003d584541850783c00d0010041146040c000760300c1002420704240941007136114468815005002042c081040c0c00555811180343c6034002c07481030349a0904185c610b200b0301d400e1107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 362573821 1250 362572571 362572579
    0x615131b0215060d150e030f130602010612020d0f0215040608130809190e0415050703090206180604030b010b09011d0108060904081209010e121306210606030b 70
    0x4100c4422200708064060500108101008004c554075902402118400c2c5142c064542c1c0c140e5049401c100081e2199a83c200c0d8880c3d205d4045030704007108684581c1c003c8086a04140040040556011240300c40d0768042d50420f4400649003044d0005000c0120300940100e2042035550182d201e400c00b41c02900c07a55500d40000d912200e907540e0040c42044805021036504020485440c41d2803c400c207407498044c0d01031468141c0d10f860700c0d4031a582c100ca054440307040801c0001d4402c002c511070941e0001841c24100300714812900400d2840c00f40200344040c0140340b105a5001d130740e9070710940d80159401100c0f00c4640da16081c80c40030075045011070b0707800320707102d6482400306036a0149251959513069481480a50307071801049030450018100355452001013040c0c4880c800303001c20444c0314002c8480045a0209002185894207001c80140580084180480c50000290380e84110464805250004d4980504e114681d098040c50121000c500c0c98005c000500503095000b040718601e04603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 362575071 1250 362573821 362573833
    0xd1b0818061012050f010207050a0201030b06130506030603101b020705180c160f060c02070b12040b0c1306030b030606153709051207080615131b02 65
    0x940016500e030000d50b40304030100301c00c0c00300748034071419052020390980c01601104c039a0b03000e50000030b089070312000082d1102d4100b000d40b40c0541d43c26001c4c0f68000002a20414641000c012400041506038002d862140d100040414407603a0308010301060614503020821010f00d5500200310f102100c00601400740c060100f0002d42032401151443e900640081501e07a240e4a034114822a548001d4404500e29094200e03032022421508060710458890030380058801240100a4904111380c1c0c403011a1840400ca0448818486400903070002d0340801c7c262125101c10010302c0541c046d0844c00406101d42003c006445940358003e01d1903108142d0a60b04252140000d108010650302000c55541a00f00170f9610a60b00c80180e41050f00c1c0c201070001000c1044030800790704845a904c0303120000d2098101801140780c43c10210700038800503401001da940c90510030783c5d110a401401031502c1071000b044003804ae1140d0300300019420205d07c0401030840c0d8102e0391000e0303401800c03001005100700 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 362576321 1250 362575071 362575111
    0x9031009061103090a060b042a020f0c0102030f07051905160504020a0e0d02011215080f030711060d0605031c030b0d1707080c0102340f0303020d1b08 66
    0x1c80740a0340d40d0f84080c100d0003655840b00c00142c0031f14491203420590f902640310500c024200c4100c00e44e0410013000c03a00c03617100134009142c203d00f1510028160410380c044c0d46141c0c0c000080f141d200ba008131000b903c410305030404604100742c031440401d46501c40c2c9101410098040f0f50303844d0b01c441020000044644444c05d10040340201c960502c04682850750710765040c64001c032217038401031052615106d6038041d585d02c0001e035081c180340c049038005060420700944030b05104001c0354007517600040d810542d103502e40c400207500c00100940030b00740c0080c06440342d034400e40120014240140840d90542e6100c010401c140c1c1c054085180000d00e0010040c506207030200c0200800c2c2d0704090052460f0f6075210702c0c11039943c86000304942c0c0e564200301000f1001404c1c009840c000200c580d89040c2040c5203041c145614078014050400010031074800c60004450a101b14011a054900146c40ba0f00b03640b0140d0043c2064013000306491790300ca9484d506960300102141c46039210498401780107181c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 362577571 1250 362576321 362576351
    0x4090f0b090c0d0f2910120c0b03070504030c0b0a0807051602120f06090a050c010c03020d0305190e0d090803040506040e22050a0218060120030903100906 68
    0x303414007584403a1a01d4400007140342d5054413100c1a010304248080e04138400d4902000000760076920414400c0705080000c030841c008444001005c0301c10105141620a50f5a84117203c00d601500c8450100400841c1015220790b090724085c2d6440080d18071611b03190315426007103401c1070b1510310004a45030000392000d8440d10a40c0d2061050a0041d000543c09600300000683c41e0009080e0910642000003c80642000302c0d5001c0c40d041000b070040e081940c106141410402c0200d58103210a031580b801c0003d9000400d0ba11250040c40c000800d07880d020f1011a50389189584c142045d418811188909a40424406046c208075140c42810300d036070701d079801d0312400b0b0342c46840d174014000c1c0800c000130071071240701c65070011b1000315032002000e1a00c0d820390340f280d140600707965580c0700c040e9000460810407800c3d200d107050601030303c1080c0f0300000001c0c0703140724030303841c0c04940d00f1594103000080c0410402d40700400d10043c140c80c2d4045910640f0030041c0144a415902e01c0d0070305514140d1480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 362578821 1250 362577571 362577583
    0x605060d0c121103010306060506131211060a05030910180204021606050c040824160207150f0e0609013207061407030b061c0b04090f0b09 61
    0x240205040c8510103105000401c40700c1c04000600c05400d8003004458501d200342c8080105101c0110345a50442c1000320440c0e100d0f42095000b0300c810440d400224205038004400c448081d581c08100300802e1810f5a542a54400191b0f009a0046603055516800c103000c0d51051141108684004103a600307544d042d960103000340309090b1610050880941001d800602d000c0c5444482c2c0384c0c028406944003070803201e041301c00205040001c1005d1100d0f0005015590000180103034082280b1f6800d9241c61000c0310103802825240c2840c0c2e20084094000d2042e907000782103c0e200203c1c51018910060309403800040b2220004e40102004011031400d9410f03520186410381d610602000f22401d001d4888115038004010300008541041002001c40028041640304c0c1c08041400d0380c540040811401c00504840149410b0052100341a11807006407561050301480314006141401803420080040581e001c1d0840c2c00c200c540f00a0200610010070320350320130282421182c2e60f1252060720f41b4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 362580071 1250 362578821 362578829
    0x501170706120b01021f050610030509070e06010210060311030708030f0f03100f0303032306030c090601050403060617150c0306010f030204050d031e05210a0b06030c1c06 75
    0x40340920b0000904800b680020310107036040c011a1160b449803001c40443d41d201c10900c0f2425038039081080700314103100861070200c000034101445103081a400d45a210807803030190050034a0800e0006440e60301c20400840308000403442002081c0e140d0900f40118a540c54241d402482500d20001710594004211440c0076140c1d21742604150000303808070031650000c0d0031012060078a030004a4401c0c3d50000c0e00000b580b00b03803000295082c82400360804d1700a14504066403a241004020032510003203045010080116680d1580380d0b580001a1020702440e00040c2c1200d2900301e0208200c1c1c0c842c0c0d204140b01d0088022102518000f8255a034086006c07038070401803003014000b051840d402a100c214050242c0d0501508042e210f030b02150f20000340c2c1409400160303140c00c2c0a0901c0e03064144181e608400f0b481d11515000c0340d40e05000380c100030f008145d907c40e10400c000860346602c0d5440400802030040035107980c0c4c14145034189068110981d085400d898040c0190400703212486030340111 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 362581321 1250 362580071 362580077
    0x1e011b0228050310020306030705010905010e101407060e0f160303050d0207080f180108010b040501081812070b060d0209060409170307020d08060a050f1201110d0501170706 76
    0x451000c2200c03400c010104400d038880307100194000c03881e6681804070788960382c5690001605c0b0304c2c0010400d45006da4683c0003905018041c1030a01059030b000d02110b080d40401d43e218071341c4440120040324030104641d00c0700d603540408a02c01c002c0101030340242c00c0d1240c0c448103c0341ea45a180320056140c640c150021940703070030100c1c2d04100007030042024008040c001500107040c508a40c4035800306070320042c09044002d00000390551090002c00340c0b9400d05078286020100380d814401c01d00c0003171040e40101e606020b121000070703518040b01d03542540e1b040d110209a44034a15101000781c81504100030458004007480002142401d000282c0e8106c80d800901c0301a640d1103103810320004002181d000e85100b45030900620b5010f030700380000d40c01116076a0003006507100c2080000c1c414440074041714450240340e0006c0203540d41d1540002022181129030500000c0344c1d042c0d01e401400131604200b094140421141c56000031940a54125a02d4800301c20000950095854490405000780c1c408 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 362582571 1250 362581321 362581339
    0x307021921030c050102040932010b09031609060f120309150e120705120106050d031103120406020d050601050a1d011107120c170703080304020f1e011b02 68
    0x425103502207003040038020300384107025050b19101c039070aa074080d4000c1e0141544031042180c0d40c0d100a07600100710307480520728003c0c042003150280f4442d541845805120382010585009603a018086102d400e01040903420b203140c0d039094800040d0901d0b105481c0c204a1602000440c00d00a50303109040030303456038490810303a08248800055104802d415802c100d4082c0d00004913031070b031008954503070081500030b2055501c0c045c00c018003200e00800e000c0351a41402c10820580d100c4032582020280e01d401e0180023110314441503071450080910ba80755072003146c0705100a211466000300341d142c2ea125411702542d55003e006441c0d42c03192188080002e610107000e01400c03541d480c0400000c610514220302a2203504080c0703403505100d90400d40a01040210312010030418264403402000c0d40140001c110185203445512880c2030300c0080c01705040040090f00715a200500740c880000300520012144400005460900443d1504613010458011940780303610050001000c250b40d0007860400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 362583821 1250 362582571 362582609
    0x10c02011d0c010f0908010504241505090c2101050f060a120906020f0d33060c031709030a030c1d06090a05060c030a09050a060503070f120e03070219 66
    0x50010800f0703840c1420001d40c1180441c18031001e00848c1c0c003641c010b001c40202481e41d24100401814520501c0400ca484e1410500c08a843c0c4c1194808480c800c880403240c17655001038683e020b210700f5030f510015120345100c0b1004403101c0c4120302d041c0e480c2610611402928807051114038407510000b000450800d1050111095036074002466940c0f00d00300160502a8201c011001504034507480c000f2581c030350500b22004107003610031090b20070800d48600130020612f42403c0f149402400f6620401131a007003813070140340c010b0101c40156030110b5848201440e1454005459402803680c6000080c28010704d845080e1003881c8038860665445800005415024100406603011031105504024110000151660784c10302600c410410b02010310b80d141d000c0340000341041c0a6412003803056038140c10078031089900c03030152580328580742440c51030011204070584172808040c01c5208a0750900c01902d107240404000b400307010384260761400142c0d4180442da01c0c8a0303128050844500c10329141c606d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 362585071 1250 362583821 362583827
    0x80a0203061f0903021f0e1915121a09011415030f040b0109091518020a170d030216030503070c3c110108091509010c02011d0c01 57
    0x150041c0c0010011101480410049140d40500ca003600703000c0f49000000304158104510080c071140c0d9106614480c1420b400320103072510007920003081c080d41e0345180c020445000c4400c91380c041c1420030070215024030011401030000030701c54201420075040001c2c0e10000548007440f000c2c00e403001003404000d82c0c20000492205621200300c40d80c03041e4103c1c902000e10340858021030040d9042900f02100d40f0700390602d540401010f0340624103107841c02d041800411100e000c0390130f0440c81d07094086021010180f40d40e40c000d1901c5000703580f20500c000e0004040010080d0311500820060a079640844958001c2e0124000d840303109070148002441e45001905c1500199482000ca0034080d010105d1910382480400750405003242d07150f201007460f020300e441c2c034004c49408640440b809a8403200c07a60b80032001804042458144601c2d54041074010700c05000000c00803426103001c1d003245c605818180d0181c0401561030015510b01111040701049400c100c400c8100d20360010484082154011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 362586321 1250 362585071 362585077
    0x110c090901020d14040309080d050d020315030102160c05030f07090e030c0708010917160209070509030114010e070e060406050307140c0c1e03070603020f0909010e25080a02 76
    0x304080d50308010804250b0440d11559003030f48280002030310249071034607001d80100c0b1241c2122146a0115040f0602d45601008491110403140d902503201d4880020102481d01c0a01056071315500104803602000303100242c12000a01a540482d40c01b5983e00c1415281c2c0f0690340c5940311a0040d00e014449a807440d0040b80c190310380c0c14102ca06e0084020959424000150800145a51503441500170320400c00c452080c0781c00c0003000c0d24078003444845031080c084a541c90090007240d00d0742c006642c071030040003510040c08002e802800070084800b40061044c200b401038103544003c040c0400c55403440356401c007442801c00340405107818101401915540c100a00800030018054010345003c5240c90140002d949108010701c404c440c96410480c0c0815240c40701d14a485860801d42441e07540011038404580d01410300581d0396070785001c280c10758410f040a26800108080c0000307407c3d40c0c0000482d2089941511601c1e1041c1306000c5a12038920303504610b800940c04201040544010f5070003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 362587571 1250 362586321 362586331
    0x15100903030302090316030311120906030412120c270501020c120a05030409051504050c0f0702150f0306011d0a0e071206081b03010204031509032309010f110c09 71
    0x884084004d01341c00d86e00e51092a4004500203400000111420103007001010b2007156118030031800c1c40c001c040811410b000042002d0a030302c6001114840703840c0990320028041181500c240081ca06840010380300c40c070701c000c950144020040c4c4404090314001c100100b507400580c084c002d240082010805000c0ca000c0c010500e500030311070108009042000100b004141000c2c006c5282d00d040351000c00d0510480ea01540140e0070501040803881e11003046403800c03008a2070f980d890f0342140c00418040d00c0d29022500b000240003074000c1e00101c2d104051480303518240da038070000e40352203000303c02075101c40003403150404d00800c4140820752121480316070055052400c00ca00ca10200341000079103419a0002c02550000400002882e41b2210112900349060f8020340c40c01f0310310f60b60b2b40c0150086004d40c044084c2c0e40c1c45000101441481401d102c110b064401010b800d645c0c1401503a503901c080881070104001c0300344035145900400350603900003001c034003500d09803a01c8801e2000d40140188 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 362588821 1250 362587571 362587573
    0x50306040f05190317010501210f15090204140105040b0904110c030d09061802030616031104060201060905060d1e05010f0903020708061f060e0a031208151009030303020903 76
    0xf10302090b01281c141c40320202e0103681c926080c440030868010000c0f4040c0c01c164100300566959041e42245030480d030103801480c5900041403800310210100800310b000000c080341007042400a256205a00500241d07044810280c10107055200152840d1049200e0b1783c20b00c3e10188a400e1580c0b4055101095020880045629007203260016a045910182210708441e6a4855080611100f4454030321040b0710301c0c01071139211482d600000d5071508002d118441460080388090502842034120f19506440c0c001d0203510342d070b00c40030040c0c041d01090150800a80c03070140014102d1400c90000e1080c00e80102e000344c4401455001d0308500040d1103400e81da99134880c90051722019040c0708011541d80254003824110b400d103550b040c2406809407200c013040c1d001048071682c00070740c0d4200e48120b41d80c505000ca0b00c46044400701d050032400d50700181c4600302280018040c9a000f20703d00303100300b00012203a4804080764041140304191801c0071800560b004109200080c001e5004203503c4000078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 362589928 1107 362588821 362588833
    0x40603050912040521010b0607140c06070809191a0a091211010c0510060f240e0f040605150901020d0201022107030213080c0f0604050306040f05 64
    0x15055065151740321080c0584800254840320006601602d01c6444401c5420070450ba14550300354040c01c1e00400c00c0c500c00510b4614112401c0c6a40301045c030b810480741c00203102c01c07080b17458503a05046420301000304140e010800030700656561701161507582c840c21032000b01a03511715407201c0c1181c0e40c0300d125000040c60f41110800ca5041c203180080000c107550502c2032810a001c3d0800e04207a240c00320200d0144060341025003656003c0f020b00000c3e01184c03140380c44101119100d280059002c2035078101e0b61034006480c5c00a03400040010981c2c0f0707225000035410350001511102040c00001c3e211180f035806220007411302096000860030a043e030343d01040c82c0350040c0000220814843c00003240c0e00d000b40d0640e0020a081e60850700c0c0c241d203c80c085651002540e22091041716100c0c0c5e01c003414603000d4212019110b024000d0304c0c2c1504c40b81d8815030500420801210180109 = true := by decide +kernel

theorem cover : BRFrame.Cov 362410071 362589928 := by
  have h0 := BRFrame.cov_init 362410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 362410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 362410071 ≤ n) (h2 : n < 362589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
