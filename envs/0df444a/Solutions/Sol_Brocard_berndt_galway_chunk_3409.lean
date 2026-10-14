-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3409
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:50.222701+00:00
-- url     : https://prove2.me/submissions/cd2bb82b-c27e-4c02-9efc-11a78570e059

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 612949640 ≤ n < 613129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 612950890 1250 612949640 612949661
    0x408030301260c010e041103040b10090213150903050604030201050415060509160302160b0105030d08090a080706090f1b080c010507030e0a030803090a06050c1911070512010b0a0504 80
    0x142182510030001582c0303517011041e8142d003154071030b2101e040401c404405944114000c9140200c87e00c0c03c074209040c1c280c0550042103107688188210142800304009010581c3c031984c032950004095010151440074966000900502c110010007041581c107402c05030046118220030054811090740c60030994803103010b19600071034020b0006000041364018809010118140140360201c1c80840700084d039005a020f880080c5000d0042090341820880421031141d6450007201c04d0031700c4d200c8070391107514a0001511420001c00e048043c07120640c05102681da1280b000c040c0011545040b442c80b0590640b010481d1400110015850708042800012154142c4d150740c0350502c150307426a61540b030020070b15082100c0356800710000d0130100046004078114401481308417401e2420130256017008004000304c8006101c0200c5240b04000d480c40d8040d12420011160842d005107145802041d0f4400d651200855410000351306041d4800c1e510708000f40c81d10304149d80c650041c03100ba696903140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 612952140 1250 612950890 612950893
    0x2030a08040b0d060f0b180f040c0f1812020d03050408100e160e0112050703080a03051906270e0d0306053109020a12050309100e0901090213080102040803030126 71
    0x25101c41601b2807e2080340c0f172400107021038005003000000c1000c0f03c0c0781c03030202e401290607a0700c1e10444035000101000703802058041c90380d015040111041c10791200160090080800c481c04a04241c014001d44018200d8041101c40d00043c8410480240c01524001ba600b405029098140d10b05840d0703090b01501c95000c00400a40d1070591044000c154502007a40c2e14000c1a80110000305410000d1072000d15503500072403d8103006840a000d00d800d4560164294580001000404040896105e894000303110825507041100f40042c00b45c144425030407103e00940c43d604403017a07056804001640d00503905c008403801001c4250881300c003815401c0c0024200d2600302c2da01d02a2907089001ca043c805440900d80507078420700b41420400c0c1180450b065000801c00308114203244c514442094814030f020b60500b00d100011988400d01030041468080e00010107064488141801400500b646c0008640c5e17a50b172b8285013a105d41013801000016076800110004400402c500582c0c2840441c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 612953390 1250 612952140 612952147
    0x30d05091f0c080601180b070c0501090b041503050601030b030a03090f06050405010c0f0303090219080c0f09040f0501110d021908071d03010618021803030c1902030a08040b0d060f0b 80
    0xb001035803041c4a44541c09400400241b0104804c001e2001030400d0768802c030039002c005810040054051260703a0040d1711400400e0004000078241c2c40356082a40700d607818000f5185c0c0300c8000407005080d500c1070164061090444100406900c04800000c4880b8008404a030a44518044407a03109600c2800d00007400d4060540114800d000720400c510720a050000d0140003d9000c1000c00c0d01140c0e010420706100c89040040081c14800c800c05e8690498040500c40481c000155040310054400b81101d035489099508000d02540154201101140310035114645210020007070360003c0310640d00280d080c2d0101c1c0c03da5000d641c0030350041c00d064541036070880752030501e4a080e140c1c0082641d03140d900c88200003120301010f00881c5003400000d4000d642d40c510055030042002c4000c1996000b544100710380c00700b585000c9200d084141c3c550454400d51142400000d140c0300d44ca9401801c01840060000344000b407413030080c00c090123611020b0007040e60340c800203070254074140308102002e00c1c00c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 612954640 1250 612953390 612953401
    0x5090f0604050117061305010b0309391809010207021e0901050607150203070c030f0206060609060c010b091005090714030f130f0501021e03130311030d05091f0c08 72
    0x140032694840400341408018614100700b600546c0c6007a4016613150200208bc01a149000c0c010940c140b11541c480400008524084000040e1a0304907500328054034248440c0a42d201c501041180c04446c05941031803d042100600130350200400324070a8030b81e0700701d40c0100e10701000000b14464004101e010f580c1c0c0fa000900416511500c0e04039407842c00200148440746a40c40910300521050b600d03c05888004e103805048481401809010343d44401c0c01c1210965400c81150601d40f02a2031240c1c40e8807180358000d0240c5805904e243d840070755502000401d80e0640700d9071040700d008603811032964840820a803000404001c001c0f022241c02c0000480c10302d221001c081d08540c5052001240c05c0058844413843c0040f000d0031101c503500058500e41c1c0a403016003402c0c00f0000c1b070681c1031450604429104920011100c000d0a00c0040407456100580902c2926601c1d032059500303000c03030310701140042d8480d201c005402c40780e13518031301f00c11419903240c0c0310310b12110740036403580c0120703440e107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 612955890 1250 612954640 612954677
    0xf0306060d05030705070303050703301109060d150e0708070e0d020315040605070e22200405040c0f0203072a03030e0307050d02010c0b1902070305090f06040501 71
    0x82000b030314184020086440010420450310005500a50742d50340c07101c000d0324000b031142d011034403444108641c0002200090081c281c0e61400c02c14202000507064961103224a40e500031402d245900c49404120b0500d5007c06420182c0c0d101f4003040484182612040031046005041c1c4503d000140c00000040006010f09946207454000800054524034242d00291034503030400c50800b4400340c920207000811a043c02082e81020742c50074105241030f40600400c0c8152204c003800b0103074000300c60070356211110a034003810700c07c120f0000c0e40300000c1c05000f07000074561262081a0103107103081524207070039115800311003d4040507405185464125141c01100410405080140e10984944131aa115500c41d0391401184a5260200440740700302c10036060000b1940240d010b11000c40007480142c0c0d0040e01984c0b00c940c054072403900c1e519500060608864442a015411440010400c041c160080054001a0400c0300c88041758403080083c004d040c0200c0c42001e0124444082c0c003500c0041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 612957140 1250 612955890 612955909
    0x50301030f0219080d030b03061909080f0f0403050d0c08030103060b0103060e09011a0a060c081312140c0d080307050a0302090604240807022a130501140f030606 71
    0x14a0b9120f09080101c0040d103180c404e42c4022030941c004d0308035003126074242c015100b910404078044c22080c42c000d608207004180000b880502e181d500c1003020308105040f0281c4014110850340183c0780e601d4081803d4480d8040d010545241c494001c0740e029083c03043c019181443d50220b003103406c50f4030b15520b07c4080d04600c140e040c10702d1b4031070b031002c541c558028068510400b4600004030f4004a1503040004101e03020403070b075014070b100d1142400607540003240310000c81d03880320f1500d0b81c0382c210403243c1100110039080380c61816111a200003e0000d603640c05008041440160740444c4460800c2195154000c83e001306499014000104d1880c02003000d005040f4903820094504246d410000343e89500c960032a807001070407401d141d0b000701060710841940740303a10708103000343e4105800083d40d1303464114418440807004060b00640f030700a44030400400ca10240008019409140c0070030090075090148884511a900000700c4e01d261004201e041d156016026054a40b50041803025104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 612958390 1250 612957140 612957143
    0x606020c0609130c05031009021608030612060f0f011e03080901031103040f0311150a05370f0c090e0408071406150109081504260711010f050301030f 66
    0xc1d089000c040c401c1d103c83c029945000c1c4969102607a904c0c0c10103107074010681603003041101c14414040e0303202501955070140394954001100640f242d40352000151005c0303007a0010805801a40c0500081d83c1c1104200c034050f0007404860b0017583c1c1c80e611107620540c0b00c104110729040b100003040020900c5440140082101031401043d0f0080d14141c46d0215881036030200c50040201c072841d014540e102074102da40c1692803001e8940c4902404400c40896406000011020b9445001c00e041a0441c0c1e800b060a00e5403400500300600b0494801d818000c0882009204030304201561000d01114441c44d000300d40543c580340c2200d0300b411180e0105101c02081116100c00c10404030300420860802031006140030002008140b0707298641d48074064869184c0c1d4140801c458043c85100804100c06680c00b00c401504000d1741d40d02d04100d282c1040050015980e207062040c1c890254491340001d01c090742c040d1400d0155041c0040044801802c05d0501400040c428001800000c900040000159 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 612959640 1250 612958390 612958399
    0x30a0b090c030703051006080d140307020a060c0f031104120b0a020403081215061e0306131d060f01030506010e04080d0c05030a240b0a020f011a0102060a0606020c0609 74
    0x10007414000c80c0c42c1100a81054600b9413200e00701c035000c1085802070401424550014081404210002410030b101031820220801000b00016055a10070005103d1403500210b0038031480500b460050480440c0c02d54400019085c00c031070b000307012010000c6904540c114001480010501d8564001000000d8881040d141d001c00001004c14180c01c050300c0071906d030700c8580605040000607002b900700e15030303e0107024403800d01c9500b02007407082075251002241000e81e00e030f40766541400a00380c3da03500c0c0f042e01c2a16161584c11200380c10a01e00003540614140e044032919110a10000c0000a00340320080490340160018840001c01501054000b442010010305062440806006542d808204000001ca01004000c0800c0341070080c0b0400004800d078181c1070441c01070038407544080a01608503c40f0000600820052080050086210300341000304000c0c0b65a284540701c9040d07452034503005201d0302c00464a180380300c0c481d8100302c40c5c568000f001651451806e12216811105039941c0c80b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 612960890 1250 612959640 612959653
    0x1802091906180501060801060c0c121a0c18042a090e09010b040b010c0507051509060706091b1d060409050d020606010f02010b0306061c0203101a0f030a0b09 69
    0x12490400c03110214982002c0201d560360400c0802000407005078845810030400d1074062001c100b15102101c01e1302c07849499542408050705109518004144401300040a200c0400400750403041c003802c10101c541100a11648410003088180c4000f002021009080c1ba600031201400a0000311007121503814443e1b045a5103507903060b004007080302d040035180d444480007841c03440c1c10301c0b5008040e10242440c8020003080d44540f40d40e0319407401203078010981000d40e810110826803c1d1840298001e108591326502441d00078044c0c40052804c50303489810b8522240d48480c0240131200351945000c0d5010b1000d10100300d040009005407490340c105907102d0390315000c544140b011601d807920580040045040003030004103007031800c0d613011045901d4540003a140750750101d01c0d6034100e0000ca45014084583d00b0708502000001c0d40c0080d410b100d9042c0781450030319290441800c0300b070200c3c4d007030450900c0c0001f03102d484180c4401031a49504080401000034541c113491581000741c40049918 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 612962140 1250 612960890 612960899
    0x40506040e0604050d17090d0315050604030609060609020906160206190305180714012102030f07170103020d060f0f0519060f060e0d0f0f0c0302041802091906 70
    0x140441a541580c480e0410029101c0d806d80040d03003c08125280d00442283e4a003c07034286403240c1203121507404054896044c1c6c00c00142c460840303405007070000c004030754541e034a02c0d084c002800e06401c11030700b00f81801d1002403d1019031082c0c80810b80054030325454414650680082c10301c0e40041241d100c03806101c0c0301404003002c6207070703e14030546841c0099030741422000c04420307801481c10758100b50702040062004030184440401c52500a00700821811034403003ea80f40c2d80109204040031340d1010040041301e42220542174000c617415203c0c02034903901403a43c1150150240406900300c003a8000c0c500c0040c000e80c1c0301c14a001004500003034840103c015007005d90308281c42104d49180061024103550015124801c001c20f00c240688414030300d48034025025000000b074291103800700719a0070085c84400600403400c00d50224140d00b86c801d403480c2140500c031240c0026405a803510000b100c803a00103151a0141540003880c2c01030a03504c0f4460080440006440c3e203030a551034110005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 612963390 1250 612962140 612962143
    0x2060a020a080d0606120c0207050d051509070510020a0c12020f040c050c0c09040209010b0705100c090303030b010c0f062f07020f24071112010e060123040506040e 72
    0x2d040c0042c418045202e07841d11070018074103a4003081e903040b014a44041001c0381f54000403801c0c1220420f03034404c2e81550f05800c0043c01e0210240040000c5041c00007004040c000108060090302c0003101c05141c81920000304980d03405880c18001c1c44c1c0b01c1c801c0400d22962010900c0e91040a100400002202d00f80401141c213540c0c0c1124140080f420102d2503211102c0280b010701c04508061718030180602c1c081d00050f02d81c100c18407503601c0030b0600042c4501404014082404400a405070a115404040d4001442d4640500c030a9000914080181c0c80541c8103403800c01c031003608412101194000303a20380200030480c2503900d49001616087c0e42d1008a41d012440c254980782500290f2141c0c2580140850400000600c03072140c41401c17250a000d0080003800c101d00524004035503102c0e0241c1c50324034541c400d620300144d8440c3e24440004030b41181508081c43d6291840161090ba0340c0c0d4030418103406041c450400080900007441340503a0400303912042e40600c00600c045103004c903121405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 612964640 1250 612963390 612963397
    0x1806051818060906041107080705030f040806010302090709230102071a0304060e010e07090c030207060e0a0302010e030c120c010b0901060908060919030315030b160e190302060a020a08 81
    0x15071000d07004800300940e034505101d400c0d41c001802c1d40c091042004068148000e80308441700185450703004121b01003440020001e5416512159403016a1143c50345041544c460302440308170320800540d00014180e502c01c030a00705c00ca50220910303d51080140c0e2003003242460b000710303060452040c5100010a40d001510000a0880d243d0013141d4a041508145007551900e47e0400305980c14108004044840010400100e44110000060031903255104034041e10950b078000d44010300348140c504c00518086a40c50046200f50020010003401020007500da000e0883e600d5019040702c0340c0420450b1122000f410517a42e038030000030300d0720b17151800250b00d0712086c1c200c900083c8140c8018002d04004024442e000801c4200402b200c0500302e061100d04400b0344401002c1680f511207422504014042a501035680b005c0e014403a0315041d40000c01d0881581400c1001454041c0300040c03a061584954600c54800135034a000ca5081d5001e215032940320200c520118450600640045550b80025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 612965890 1250 612964640 612964669
    0xb1b0301090f0e0d02030415090807031406060306010f06050706060b0a03020301030c090e0a020d15050114040c080c300123030c09010e07051e07020301060618060518 73
    0x251035150040c0c00b402c407038442254199a9105801d000034403600002540c0072100e041000303d00b40e2002d80130803240d251641c1d012076a10b101d202c1c0d01008110400408142d000c407001c0c1103400320f81e604001c05980c1d08081c070801b83d5601c14600c082c080c10748160001c0c00101d006040104500f65507001e540c0c0c1640c880c00540000940c080014400c016200404100034020746d00c0c28410310340b080704095155a0040070003440317034102044800800008500c00c42900c213200c0410006580c0d550248912240d150400030700c95440d2050155186003c0c1010720f00481481000c01d080ca500701d400d024292440340d015801409540d807410108176a03940450b4040c0a0b00704d1590030b01e003c01690300e40b02c080c40078038240c820341003414480c02e147c03107040c55681100e1604440580c944c840300c2043e43c451240b04031625401b100c0051040c80f800c1c1c041c00401420740300750020414a9980e0300308903208030180201c2c13141440303481d000300102031040b00036000c640c2e1210313101241d001c0702000040444802814 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 612967140 1250 612965890 612965909
    0x318080c12040e062d0f120109121b20010315031104050c030f1302060f0d1505030106050105032e0305010e0607110c010c0c03021207150f09030b1b0301 67
    0x100403150034840070102e1055511011a4229405c1c0c15026007094114102e1314010621212544a035980d060501e51200002200800240030759041480740c0d00142003150000c155000d85000c6c101409220141a680e00030900c04644c03803030420641034091020b44814109620340c112588101c0c0ca5000201c001e502c40e48204045034245810701c030950301c0c018544460342c201441002203c000c0600856400203c00304880031010540c80010003070b025010b40c0c50079603040030940b400c0c0d02da800d6000640e05101c800305c1a00440d560300406007610413a00600b40010000e0000c44c10051407000912404049018030813804910ba900c6400361141035481a24940c0d1241701d68204000240070300c0b40c1103a0a8a0407900c501c1c407000c80740b03a41d9040301c503601b410008100420030920140018880146500820242850801040d13080c0d86803294000d68007142103541801101034000c5503203090310b48032515004460348c959100c04034494401022150300e80560201800156005401540a89442c80 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 612968390 1250 612967140 612967169
    0x91401080f07030c0501080a0906020307020c21210705010212040204051b0a1805030709020a0809030711040e0a060f0e0f0606060403080c0708010f0b010f0318080c1204 74
    0xc426600d409005000034805070009003003840071504400d0302100340c0b6401e00340741ca10758403151400d00c0100180039014010b24408014020a194003085075070707901b207003120001e1400d0510040d01c1918951800f04c59082da001120020007201e000140c0c00d1134007031100d801400d00d07407952140c0c6e003a80d211510262018400c84200001c40c1780a205032608080000c042132807060288145200030b1264110714800d001010800c7d003441d00e0b1206601c0007404010302038a0b60300d513407020810003039002000b0310408190300748002500c101001040d9091a40c01903101c00741e90103524140f000900c1c011440096900606803541d000c03c0c281e000303580071a61056400941110a0745000b0305082e241000021540c001c001131050039962941a5025290054036055440f001441c0142c900001d035448500294280540580a49900d40c403168014100b030b241c032400e410360400120111192641c0d15019442c0c0c40600c6000300d4420005000300504ac0404c888980714030380224200350b003142d440b4403484214030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 612969640 1250 612968390 612968399
    0x201050a05090c01080c09041d0601030b070203120408090616210c2f0901090207150c0c201210140402030d0c05070515270102031c06091401 62
    0x501c222940108031102800420308050300007820184050000102d812020456007040d90b06d130b47c40020181800c2c3c0100c006180140d000c281c0b156801d22041c2d0f105018030b8009550341c1d0002c0300300d9034080040707405e8407055070315603407043c2c1d9941200c0c14031030300084240418414903400c4214081100d006070680c0346c00014035130203501e13000345500d281010400402440f00009a05495454101d41c510524400d0380000142d008020b400180c0c0301d40d07000440300c0000034044030a03401001c180c3e025407600030b244080000020305a602044501002500701c6852402140070540003100c550001a00030312251582800607108000030101100582c0000c3c480d1624042d0901c078162070001341d102c0c1e03010f2a140a400080c0c50340c01743c0544606001d5610101c2c0c04100c030034071000380078200c014210f00402e03203c0205c103a43c54101412039402c2c0205400b10400c501d047d000300d10780c030b51016801186000038191915400b802c1d03212542500d42d84030540400c000203603000d085407004804860517070540c0b40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 612970890 1250 612969640 612969661
    0x41d0c07120302180604151b0503120405013603170c0a180506190908010c0c030305060121020f071202061e010e130318090516090f0915090c020105 65
    0x4504d03418441c00d001c000401244010444c460301092a504201040c0307904a000c10640e1072132507500401da030000040309090145500980c0d0f006501600c003c01004007030018100ca645483d1484821149454040d040c416108072107040c00704d0321a241c00d010101c20307001030f902d490750301350b40c17404038104081504416140e0140380e8040102c410043c1d58486031402c004030b00c1d41c1c4901450300210803003490701c04041030b01540444000740b0a00340204105034107100018981070402800b01c000078208004526150310130441d04000b4101050180845008104070a0007940b001c00440c0c182c2005002c2d40f004600c0144c000c1d1405600c3d03401500c211b01d0213842a0400c0402a080340d0308030f100b00c8006100c16000300b10000d80c07001c0b001075500f0700b02c10141400c5c2c80b0786074030784000641002c1d81400496040d4464005d50b0161802c22118990102d01c060103403417039640d501030a0998103031907004111503a1a6001003c684074056440c2981a46440b00c0303400b41d0340686407000260303440e4014020246031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 612972140 1250 612970890 612970927
    0x9050a050c150405060409020a110706080118140a0e0a08040b03090f0307150b0103140a0b010306080c0607020d1424070c112e0c060b010203041d0c07120302 69
    0x4004000ba2a190600002854500440c02400c00c950b9000c030724a52a64000c00c00307003100c5140c505c1241c004d9a40d81400410840c000d000391201c006920302d5903144203426006002c42c08540c0000f0f40000d94408200000510a24549400502c65105054003089403500103001070304080150340d961345080200240303000e42c5440040080d5004110380808178413009640b1628024010012605079000e20040703024044a0000d055140c0341c00c030910583c4800b81c0d1103591880750a81702485155030b0b640e01a0344484100350a00e4002e0b800704428401480d0111101500350f22600b000130b15590740703149245c41c0c0082c070484c001d820580401d00280c5410313004400c690120140c42c00c0c82e1840c5007981c1e44525081c0300c114950080807a02c0c07941140c2000001805031003201d40340300014031f41144a00401d59042c85809440b600c1c41d21a84a01d15480070003183d00740c2d05001202030300220642c0c42c56010080c02170112405800c10300000000640802090707040703611903036001d1b031140100c0810001302c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 612973390 1250 612972140 612972169
    0x305040210020d0f0309080405130207030f090f05040e010f11040e0c0910030518030c0718091101080c090306010e0915040510020c03190215010801110f0307020109050a050c 76
    0x500101402401e69848031305106a140303a480c02043c244518905100e0764081c68200c01d0f4480780307030704244218103a6540070b8a541c80c0aa9031f075900500c04d4410990307200e00580135048030852221000d11172404e05070012500d030a00c003400080c3c24140c5901031390440b410084d00f90101000003400700404d80319481c2640e000840e030441ca07407500301c44070001592540704210031428191904000355032016101440c000f8510403a0a1b40d903a801020f1075540c4859007030280361140c03041d94244140c46011880f608050540c4081c10141c113079080001507460040041120350501c40410aa04072074400307129042c001c00045140341c1160800713881290600d030080faa6011400110001c0101066001a050b034a47d04121001030b5641c8502e043d082c00d5119021989004901c0100d000e21841c0c1d0000d80d8180c054207030b1421940c0c503600c501e0901d0a031040c0011b1410305280078072039000d066001c0c400468018001d800002a980540e542c0d860505519144c180d855030414009541e079420004010782000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 612974640 1250 612973390 612973393
    0x60c0d090312030204180b010e0a06110f0102040b1e0f13031419020918010207260a02070302010311120a0b03060c0a080f07051b01050a14010302100e03010b0a06030504021002 77
    0x50901b18600e10b82c804624001c0c40749600c8060010a41c0d011752030410380350401928400c13441c0d4482c5009007040003035042100e4144201c425000b00c48006100703440c1981c01d030f480c040d8501101c0c00e8101c003291800c2c0c440603002c4a010440c0400325030000700202402c3c160380e69100003451540c203103098811001c4c507800d42150044860b11000c03400304070f003400030f80d40d04644440d069207512541c1d000725400c8140070161036100183e10310505c240d0342440101d1080c850312000d4400080031201d4a14014071107408013582c041c600510045d80030b41c1268554104400f40e00741801c04103658041c0540c2d0503280203580c10b940e034456110a05041c0000d50b07000e804815101e207043d041d07120080c2004001440580c86030010700100b40c050b440741d0111440c0301d580425288140c1690740c4200e000380000da80c0900c05c24540700c0c601d80154003035011103040f26001055081e042e0003202c0c042d50340d00750321130b800390f41035607900f103080c1442d55040c6821006d0130b400c3e50300280600d0a4414415002d00000140c400e5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 612975890 1250 612974640 612974647
    0x106081002030705270414090c100206014b090605100c150504030908101a04050402010207270b040902030a080730030f1406040902060c0d0903120302 66
    0x415030040221605e00314040b2441002d1640c4180301900140c001c1d24041e440b504011401c4000711030143c015000700d03007113003d465401d002d401c10070501040180c120340168102d1790040151541303c0981c1c20142c69055680c0d100390000103114110040c0b00380004041c42e8240c20008085810b282d40300e400b810701d012003003145078203180005125041e1019440200320458103503000700b100003840311028217070414003804a8206480c01901c0890103000d140d0040c418074030100d071031951900490400e0410314801c1854060f0500500000d0017000300142d0551140b420005660703a10406180f0707030441022001884441e03004072840c05c0d556a00c01ca18070541c10103110740c0c003680d80412040c640319800304c083c60b0342e09a589412114045070400c12003240310300c44c901e10586a4005c11401c58030b10141d4042000201054100c002c40e60b1190700c241400c600c04000030803904059000c03031400340c001080c0c54241402c010b01c4510746040f890a40300081d040d50010020000200041c0041d0191f44c00c09508 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 612977140 1250 612975890 612975901
    0x21170d1a031f090602090d0b041a04080720030a0503030a0b041104050910030602030108070e22020f0102070b03012d030308060d02041409010902091f0302040c0302090d0302010608100203 82
    0x2a071041400b441907050380c0d5100e42042052a5040300d080c0e9030090141e100f104581d040000044100b00c60903a1010344000400d04401d0241101503c034550041003181042140c2d03c600404002c0c0b2100807000d2001020045a569001c01c50420b4036417040d002980ea07440d02140d60f4060351028060103000714100b41420f1103c00e100001c0e201915000c1d6102c000581c0c501a052007003020325440500700620010000ca6000c00110f140400e86000c8403003061b131500c6000440c3c111003a0040780c400c1c40b403c0004000010b1404100008140300c0502c1282d0010ba260b49c3c034860f2035442a4420140324141c0d92040e001014625200c03800004038146030f4501520b15103028140b0f41300100802d100c0e0381e42104040441d0341d40d0b407200074074001c0b290001205207000400c0d14002c0c1005441680300ba03090f140069000350b513001400c03c5040310070702c0c80c8d40302c07600c2d5a090101501040b1061824103400b440000001d03103503548401c1045000b0350012880601d0a1512400c02204040341c0d400103004108111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 612978390 1250 612977140 612977173
    0x309080c0a140109051e0102010507050f030f0601052205030f0f06010e130f05060f0a02131e030506250503070f050903010b03030a0e03070e0121170d1a03 68
    0x404880541c0c500c426840b28950040701d00c40307440d42003160f1040300da00c080705941702548004150488280c0082006440c1d6010070390303060103030b0f6034180d003c140b0401c00166080031032003800c0e0f00800181422410101c11001c5040c4403207840c0203202c100e99602804000c03616003006443d50039440c0740081c1039044048840c1c240c46400c14000e10f04001c000c00301140750014002d1200311503030740020906103011164038005444a00c11754030302c11075031005400304807880b805100711b41001019511403100b027803411444041106800c0000c02601210701c9000021030b07424048503128002441d0740310324000c084031000104d44541240f0404021040c003c00807590f03042071150100300c007117040a1362610000c40c002405441c9533031403160103020206c0e40102e0310303400c100c1512400c0300480c1505c0c1e11307c0e00c030417040207c29024492008180c0c1d19440070001d2886010741142c1d00c5010f41c000220f410000884040a82c0c401e14000d13032101c3c1d0b02c900074a000a00005071404441c0f007100540a450b60f03909102 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 612979640 1250 612978390 612978409
    0x10f050f060619120609052505042303120a1e1407020d1b1d06091f0b040612050a0903080c03071101050a02070b0603151b090301180309080c 62
    0x2101800c0080c1d284040f180180c50982c2801c00441e03082c000152a2141c0a010340070a07945d03c441402590680310900c8000664500d0001032551a40d00b4a40350120030145030b4417044032581e011144080b15059a00c003803101c1e00a070180320988503650300c518000100700607481d007161502c3c800004001c0f8001940f0401c290b002c60004042e00e0344455140c0002a14003603003810050900a41140010803200c15503040b4044030b08580d803002400c3c003080342c114842c40c4101c502d03d90120040e000030300960701c013005802500705e003400d140e000716486e40401d142c1540135412020104801002061000305140540c580c00016002c041c00b0710b141c11b1f40c000e081108080e110062201011002411003403141001d80140c03402140284118108030740ca41009501145007a24105580030010b800740c18009071403011080e05081c80b40e003e98400069041112200707000f199a81000c2081c461544ea090140e001d00780c0001d6050a0242d00518003e440c209042e4032544094001000013041c940d00c01105 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 612980890 1250 612979640 612979657
    0x1009030b06040f021207020a0302060109020421030c02030f0313150c020121110319020c0a080702030106030b071206240e03011104080d0f0e06040612060f08010f050f0606 75
    0x41100c842e1143c500c0080d000f03105400b82c180c5c25460401074020381c0001c0d102810b50181e000d50b85980d0301c80103510300740c0c0f049000d10441c0442030006200c41c440400b0303118440030b0081c505105014036550000b800c2c26114400c040f81035201150220392408900a000e00400500603001503440ca0b410f0040d080d5208250b0103414080d20000c42c240c2c1d401880007820020010000400c40c00a45031002c0f0348540081d51544851603200c03a181c0f410a440d403003142c1c0791400c2c004c024039075042940d446244a5201580490b015520b48000000107101400483e004420729141c1d040018904500030040f2001035201c20b180c501c0c6070030203035101248070326051060b81c00c52034a590420b0403000481e000d410041d2064041c0040010300040c00100898030150b80d07031482d5524040b0b04502c240072684c860080e84038980c0800c1c10801002900d00440900160180031640425a00da50300c8071010095034030740c400324031651a030345018244041440b403c6d5122180141858690400c01c010a1050080601 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 612982140 1250 612980890 612980899
    0x1e08010308072102010e010f05040c031202032703010e0106030816081603050a080106030b010504300309050307060c110f13050403090f050906100f12060b04051009030b06 75
    0xb240e10a0140107407071100100401d8003002156810110024000d00250320103075070035440c2c0007080304009801e000e0b0303c0c0519000031030268142d045807039060000424016281c03e5100030000112741200c1c900c440c1340c04050210b0690351401d03c081c241425182c0042516400d030b450864240001000d407070a444107106014421040c07040240b41035165489200b007050800c0c07100641c540b00301a4480001e014441c0f040d6100081a640e0300c105605039090040218080b0341f06001c00e1201c5d00c00307031000d21058080004010510300380100c0c0f090740d544082005074002010440b0501440c04e0400162303000f8000d601c0c100800709042d445005580700f248856510450907290142c040c0c1d170b1031701c0d06900d11010700482040349003042d1901502c00340007403041103038465080200054a2800302010342c4108406017440d860b140d4522400c880c041031440542080c4030041c1c1c0c0d03031100f05581d032007960054007805030440d81c2d071400e0600b003002c001a50300040e804c210102d1800c2c40041c100f0721000740c108600f901d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 612983390 1250 612982140 612982147
    0x140f0603010617010b0a1a03060105070606120507170c010206010b0a020705060a030209030d09030203100f181b0902040302061b2e0f020c19150501030506071e08010308 74
    0x80000340944500c0d030111425071aa0703400b07586003050640c0700c0c00c00c1040c200c1d280007504d9a00c1400310510249030030182c0e00e5401c1032002401039402032005118a0303200c0d03d000546107413154010002503580a80035502c550200e9070906c905501030101941c00c0f0700b207500500d4519003030300000796258014024585025401703e03401d00311500800c440c1002c0c0000401c5291078400034080200250025800c15109100d0081c40f88203da010300006020f603a0040d01609003946a560a00080c0c040407000700b1403a42d40b184107200902240e880b01d410700e4070600070f02d4030b001a9201400f10814054101c40700c0540704000400c0180c1d10a0221811443c020b42c1e020401e81d2105402c0e07003440070781c44d902c2040718a00704581011181010328a081500150000c210b4183c04101c054124000c0c2820002a07521002c2000c20b041d4090070a8030140703120b035090340701c0e00100340d185074140e440030b034801c45003a4050004d1200c0c1d82c2e0050442040c8041e03500350701c06503c1c403c14000384824010300c0094880707407001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 612984640 1250 612983390 612983401
    0x703030e0601140f040212090f0127020108150a060201090501050915060904031202041d0a0504230f0d0201050601020d020307081b0a020d0b070e0a0b09090702030c0d090f0504140f 79
    0x42e015150f030b1381c41f05a6440624503114001c0d5840349419000d1604035440c041700788411104101d01e00c0f00e62150074900f050380c200c1a90040d92860340c090319105141018403485034a6641d10a603090103052140d00200d500000c5140c01c1d401e41301e02414100041c0c0003001400c008050300529580d205000b114a0010340c0c64608095030a61071242890ba40d0600000c0c010504400900031a24035121483d000082d40c0d40301c0e424007045031401d40c2c009001408205002d206908903550541400b42d29000345e54180284030441c924200e000c83e040b0015035119000c1002968041c84104420800e0303001031031900c01d199550302a1880b42c42241001c1041c0012060384c0c1c2c41040018a0190381d0181c40c03156001d81e0340c00e180082c00d20071148a40040d060074026649410180c2c050000c441038000e400b41087c068908003c202d03880180b521085210074800c60710000000c02c00101071601d59101d826803141070103d10700e0351050541084e40214100f1244050303048a400c445580140001c80030402c075201c1c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 612985890 1250 612984640 612984649
    0x3020a11060f04020a0801150902222417060108041106071a06010201090c05060c0111031008060612031b0313031b05040908030a02030406020f030c0703030e0601140f 73
    0x514010529840381400b00494030302c6085440380203034003c54040075410394031003400f0300740d81c000202c1135904021044c00704148030184c2c0181c110142c2056804c80c480b00d14410302d280241c41c5500c1b10589408052895070078075016028141c01c42424941005050540c0d80307280c4020101410040c1040450740001c0c05024581401d081080380050126075218160b0501291030560f50203c600b0000e44400800d12940c0144910040c0b150f1001040c05030350f10f800200800e039041000c03118125525a009032040c0b04c3c00300010b61046044044000e440c0cae003042c16a62070b00700d00401117409103000e44910058800b000007942c20800c10030078031500c4940704ca042a8150300420680300e000f0344e2042800b204021800f0703695662190000300808642d55a002040b05890704010003900c0f0820400129000c034000303400443d03005004010241c581030800fa0541503030340c0100c40030148502c4c041b030600201a81406000c014410440040c0580c2d4146460307940740c05844515544656140d0718101c803d03454 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 612987140 1250 612985890 612985907
    0x1180614132705070903020402251a010608130209060a030203061006140306060714070803041205012d020703030e073c0608070302070203010c0203090a09050f060103020a 75
    0x8000c18030400c2a52009000045042505003155810086000b41000318a9208030b500c41c160340da5588001a00e16003e00000754005c01d4030310008120340750110003a840a44e00403c500e803150009d13811036024007029044511040e0000d00c1041a010180601111801e48125901d50112001080c0340c95000005000072421b03407000790540680d204108a40c2030100300d000c110f6400ba00c40d910900401122050385200c01c66240394010014400c03007022601c0541e03074040703010282c000c6980f1a51901107d61942c0c215910170446944500301c403408104e803e00075141c0104034040c00c99054079202c401040c40f12010108403070502d50100c1e000f801e040c4a40c00001010000030301b51103c0340d40720f81c070701e000c204510044031840c81d11111319411a12420041000007401d003401150081c0e09203082180c0d0004007910507010940c00340320000250b5428400d44400d28943d40082d0380e1001e805051140c01a620b03070100c104540380108111050f885098001c1e1320030001d10340141e03541c103e0300302941c0c40c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 612988390 1250 612987140 612987157
    0x61608011a072a06080a0606230901110a06270510020309010f090b04110306041e0201090314060f0c0a12230103030806191409091e0109020f01180614 66
    0x1a568006003c580005d10103004003507103103081c0001c0391162070a68116000b94042c0c01122030300610300c500d02103200d0140a0000b01450580190b901205c0a10300e0000406010380307103180e540c50382c200c05691102e1265400070200464610b111b60940320551104640010341062540010001e995140c081d40045070007544d14038100710000c0350303003040c80906904441c21214610301001c00c002d01d140c0015a603208542c00070b00192080c0040b1030200c05240400b8080b81440000e05010000540003100780d03030004600402420340340350242e09426503413000341046010300c02c1007110004041d804401141c2d5058600000305260001150b16010f090010b80c030185105500c00000c0300301640325200324041c1200f04c60720892800e03800441d02050005100301d40011044010103405420301c49140c1d68400b0300315003903840c3c914129050240c02c030701c64417406007030703035035030f004210451038080c120802c110710a1a00fa0400030030700d8200c2c10904501e00880c41842008800c0300031a030300d50400c4840304e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 612989640 1250 612988390 612988463
    0xa110705031e0105060301050402090c0a020a02150910140a051e1315030b130b0f04051512010204031e14030f07290106030b060903061608011a07 64
    0x50000703070840c14404204025002c090b50030a00413550a19050045034041c9070024190354650712017a0207a419640109804025806900002030240c0d032040b850301000c11345c490300a60340341c00800c04c10118140302c81421007808a070440c499003038030b240002e80d0312480d07007420300300d03525040b04196111845004684a0100000103489820401081e1010707088500f04d1081c60300a143c510800d40c20344900c10209508442501a85101d1076800c4c1c00100d5200c00241400c0f641c4680040840d0035100308554a000480680c9280f91081c10728907113250b95455000e00850500d0f0070342d0741d807000c04c0d940700510025812019549005000c4074203451301c40780c07114004580d07030360000590208458000311019642a030080c0d810003080d0400ba600b030340401821825407131a5a0030500190000c107a0300040303680040044c07102d031040da141044070724020401000d0340202922090307802845008160003000041e0111a42c00f14000345402c01c2d0307680207500a80c2c41c0655083c00e0b154064a00581d41040e500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 612990890 1250 612989640 612989653
    0x2060c03150d0210030c081005011e0315141c05030412020604090905070f0b0702010e041505030708010b120a05120703030f0c030c180b0f0f04080a06020c010b0f01050a11070503 78
    0x850750103a201c4100c2c100c160f01c0b038600381d5454648c4408180c41320303c030300c0e1b0210306281110302c5002c4144154016904040c2400185015508040c443c083c40b1604800004100500505034034580118400c0c0c0c28101c05103500500d1a0740d0740c40325180e01847c40f0348040c008807000a40c0c02c40d42c500c02500c000c2e1a81d554104114442c60626039500e006601c00d030b40310801e20381008180000e0187c00c036003016806858584810704220213110042c402c80001200c115a0101c002c05c440d5024810600240750a0001184240444080107082079480c1c00640442e41b041d0407440009201240b1440b0094a0b00d01140d2501c955040030b601038031002c2c1101b0071092800800064594269200d4000c0300c0f401c0d5144d180e0380714000c1c1021548050707805504074011041c40382d242604600c1c4002e00e80141c50811680c01d240d9540c252902c0c1a00c0c41c03c08071151074011441d003415000c00d10034110040403c03103400c4a440c0388a070001e0614826003000c40c0801070f10703060001c1c1102c1c007040800c0c0105005011142d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 612992140 1250 612990890 612990919
    0x3041d071e0822120f030e1b041d0a0f03031805061602030a020c090402040b19230a090207060b1f090b03010608010b0a2309030d02060c03150d02 64
    0x42000c01c50b1600c5801070080d110150000384080c42c04070803130380082407203400d030104501582e0446050301441c08258542405007200c030703014031002d03051503041901c1d000009034120400040d101101c1007903080300800d081505021600189280744c080d041050004001c0160030120f02900810010071600c481391403424040100005d54030f880346009590003403a40c0340714101242c8910a00b5501001030b03000740c407031540a00d4048015a0040d1005100203540c1c0ea00501040701c003110360505403080305c40b9030410020880c81074082501e8411000c0700c0c03803001484400180341c86c0a00c5c00f41010341c69001c504031f0200601755211900040b80240070740114001003a0055411014840800009025800000c1e1900503e810799068401d0341d104e0601613802c0c100c0001d416044500c40c9410012a141c0e1084041214144442c081900c000f845036514840d1080c10301d003c0455034290704551107801008032542550095070340080350510488080b41c10040081d54070f505851010b03500540c034040b4200d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 612993390 1250 612992140 612992147
    0x403021503071b1112100e070501080a09050d120209180106030f061202060f04151d060306090a1805100f140405121c0f0603030201060803041d071e 65
    0x144545082d0b0f445004034000303070742290011000c16070014540501a4100c04091401c1c0b2200c04103031096804582d1514412a890001d4490007582c0207040d8101d61000c1c000b81d60704c8444240d000704640c0041c0152030740742c0e5a00741d48036480c0c2e410008011109130030000c1455aa011100c10900007050a9039111140d003120b40250401e10414010901e444544c1011400d14040c42c401c0f6840c05c10340106070301083c0c0a01c0001c1c1c0c041100c4009240e800c1102181c00211003400040b41c1170070f56036001c16000c011044080e0140500c2500c0d110300b4044c010055203944058000f6803000403d0400309101e0b508200b0381005a9050360014554010038040e20f490390b860383c0c00101031024143c02409031100f10200d0301e1401400761405440358210303400520354a010782005100703042c03052110b200c40e0182c84401c20308407041c0862040100e42c8420003001403640c240035420180034100007640c0780ca4036150580058400c0d44150408000c18100000d5844c1e0041c600d40440c440c254401010a889441008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 612994640 1250 612993390 612993397
    0x60108040b0a110c0d0f0f0e0913051501030c0305070504020415030f02160506040b18070b0913050705090405010f121103030f0f040e0c0403031b02030f1903030506060702060f0f04030215 82
    0x90015a0405010031f01f140700e0080310400303050242c039468103034503451002d03200b0302c400b1b05043d5282d11503038155403801c0f209502c250303000392700030040072510b0386c00e6181c101d04102c010307072005224500501007404040d0f142003940b400700d6100d081c00129203400814102c0640200d04280b07013070851b580c1c200e0307041c004089801ea00c510320510500207966030350702003c01d400f4164543c8114560043c1c106102d0011124020300d25160020100034207480c3c05103403403082e244122200030004901003201c0b08541024010305000d882400006d00c020750030020084800d070114117024007151880348658071540c90034400c44980c10217540505555000b842c2d42c3d500c283d489840b42d00556404800020100d0050100b44c1301525450f81d80c0d0142d13a0003000a900234031007042400ea0b418044d03030b03908810401c801c0010308004030701c416902e0800c4601d0700b40502207039801170480e80944001c108880040c3d590108450416400c80303129500c4084480784190701b805a03410080d0004140c000702402c6c0707445035000c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 612995890 1250 612994640 612994667
    0x23060d080a20010c020d0c210c140d020d0e0406030b0c0c0706050903030909180604120e011e050f0f03010b0d0b062107020a020303070b070206060108040b0a110c0d 72
    0x2d000c528844020702d03900b2184107002c002c0045e00584140c8001600c1007102d01020303402038041c0041d0208000004a0218400090a0214070040924420010100d9156101d607052030007500e03a0912211010303444081c0d0001c842e0402006991029207075807a0750140e005190004081e0000d4580304104001070b90003005042e6052144e0080050340c94801c200315410280043c0155007400510010721840700809402a81010403c80204007800d8007001114403503401540d989603080444500600070003410a0994100000c00441c07009200d410340d1203030b8041c0c40d18644540d446800122000755030060b4121000100400000001c040350500098402810006000c21410714008108001e92040d0840d854582d0801003841651050401245502c00ca0a00565040c0c040d5580002c1c1907500480f801c5400307030380391301c14044030036810000554000b0083c01d0808060034152204402e4000c002e1a4240c119203030b110300036103c5509010f0b00e2116009800302d9841d010030420142c03000081a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 612997140 1250 612995890 612995927
    0x9031f0902030741040f060303030b040207260c0f0a0c0f050319020a180519140a0b0103060b0409090b0912071401090b10090f23060d080a 61
    0x1e010810b03001c0d1040c40c0004510511002420000030480000c0b038454074214130139001c54810906686458030301800701c61150f0340030009031403811032030054203d0341580b402c00e01591051011000060034040400e5504000d101c0b04035a280c508188400c1521466003001103500a4484004d41030100040880c0071501ca000c80881e029140d03150f881000c0392a00c1400e40c5940814a40c84003a17280b10603103114240085c04020f45207403580c03101803002c404591b60060450742e590400c010381e0403000310f4502d404140e40e01441401c0e4074840035851480045c0981001558810343d0403c41ea0182d4070503401007020290301d030b8072995201e04020083c00c0d50407082c0d030043d000000046000c4404607109c84044071101c50300f405c011460303c4403c0114820700300700d14150758401c02c1501007120300250b07a01c5020340310600a10182030010000964403880f410403112800d107c0520400c0541c010641c4001e940000310102c5681c40c100025111034444002911424002a4410307150f40d011010201c151180321 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 612998390 1250 612997140 612997153
    0x31508030c1b101b150513210f05160c0909060f090507090c0306080a060e07120201090b030c090d030531140a0f060509090106110604030509031f090203 67
    0x805004981080f9041000080c07200c1c1c4000d007101c08440d030100c8400780034030f0341001044a5031403040200c510a035510b401d100a000c2400301041030341640e855801c80d000394809901e0b00416000350500102800b02c2081c80404076400d01e0203c0d4140310080b0054005021000d0740d42d032001c0500041c00c82d210141c6a041c2818800d8008800a00850005e5548900106241c40c80d05a90000404014000c0420952a00800110140300f0030001004a000310b50004200705100d040703915240c0154003010603900400b0820002d40e0300004401c003228000c0700a1030b6680c1e01c14404c00c03998070803103842c1944a241454004d01f45075108000c0c110b02c810044c042d0031402e103810303040110091881c0c80c1481d0141d94044c2840200c5907201100d950781d5000c1c240d40005910303200805106070194104a00291010490941c1e5240400049004000c10304140d01c4449404d80e003141c98640c001c0014090140003d00e042e0b098404014412880d03815801c00310aa01d044060038000d8101c80c02d085c0e01c01d10418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 612999640 1250 612998390 612998443
    0x309090b0d020306011e0807081c02060702100207060605060a0903051014150102070807171009021305040503091302030907051c0314070f1212020415031508030c 71
    0x300d0341c040035242c00030010302031680f80110807401549182c04403250316074071950014070781c2410000000070f44003503806000501aa4440c1200060440c882241154861070134008000c2e0046001d00913016107400150b82c8041c2414440060130300b40e40300380d41084002450024042c0e000d903908042d64415410f0382c43c244040507589043c0c1e071001d044814071746a900d0100300280311800d02c1c20034201060040c2ea4520b42d60303246c40c80c00d2185940c8804000d40425000b0745a410050007231400070310a03a0410410b80031a83c020455440016050b90300c95070356a004503050181c00c01c00d5800c0d040c00101700340d80b001580541c11001c0c2d003068550003440d12510304003042c1807a1040700389503051084003030101c1c6070615071802c45500110848404005504001040100783c01001c014400c1d40198142c2c010030301c20b902c001344844800b0002d444020f1060005000c400030380c0010544888041c91b0100d8032903104c940c0d203620070748a0b60100c840c45c400047c00000314a00807454200b001c0006c3d828a0002216 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 613000890 1250 612999640 612999649
    0xb13090506031e34050319080d0e0d0e01030f14190609090b010e1b0f09040e011505090f150418020a2601090b0f04021302070309090b 59
    0x81c0c468039450b4010803440200040c1d5900c800040ba41070740100c420102c080c10300420901440c090400005201141c10b081c0e80103080034607030080c0000e50061000c0c1c000011462424102040010110080007968406000140c2c01800c44c49017080142c602c00b010389180030380924955514640032a007441560841c03100c540c0300b03000c03040541c01807241c150b5a810080800e2074006a00d001c0e88603540d82404120b2000d01e124a00001c2d02c1132826401d01c2d4102011031920540c01803904040000034048080c1d00417011007915110700201a0a0761109600400100034103c03840c802c909941c6840f0301011080c030018808403c542c030a80300501030b502c81c1c1080b51b4002c5000c441c0d100044602c4507079241d02c1d0410f64495034208042c0c0380c1d100d40050036540098400001c645c00603075030001000c000c07607a001c3d0807540c462210403190000c00480542d41d8890f00c14400041a1070f01e180e940000060542d207400e48250102110040110b42c1c418851134060010403a034020590900d02c0c21100100341d041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 613002140 1250 613000890 613000901
    0x10b090316152316080c0d030f06080604030e040c11060405100c051305061309140a06140d0b09030c03071a1005061e0c0307050109151401120201180b1309 68
    0x501c3c110180791080c0070b84003100040c10f601e42210014410803404003210424840d005103194283d07004108603034094200001c0d10a2500030109541100d03060000194009900002040050f41c012880c0400d007801074410300c50302e40300e02196028140800041100220321030301076140e02001040f410304a500102c845004460710b041507940080f00901461806d00e024040b80b5103030b0540c1d040e07a030740c0b2104080260388041012442d2103000b00309114071901e07039004034000b40c00300c2166001da00302d607440041c01c201484440a44011080404070b0302c090302c14800c89400003c440d08036543c41120341b0344074003603800034003861810028003408110102503000f040b1b012240000d0a031070600a02a90380310f615041e04c551000369080c1003141007880b000900180a50078011000010103000710304141038100c0c6241d803415411840c003d11500c2901d2800364250640d01030104001d143d00e09803006a50340b20064129500305000044001200d6604074001d020101d511849000c0c96540e54800c10300340e50 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 613003390 1250 613002140 613002197
    0x204090e07062a23100f15090e0102041e0f050a1206020a301112070c080d0f0b01020c030a261902071706040209010b09031615 56
    0x2884086903118420301105a0603640613134a003110305080b02c038080d1000c50a0707414910306604a64107030311211455125a081c002d400b800240103071804844415201c0d00c03039009040001d903460040b08965035003581071340d0140140146813204600c00704490080c01c12a4464400c40c0048140b000c122420001c0c1d0090847c0e120023408040078010b40d0b203180c060f40010b48a0820010f101070a00b803c1440c2c5181c1c20003035505840c02c1550180381d425040240c8120101440f14090104100214100104480355101160f03107031a0b0401c5000d4031741000345118a0401180a9050140f11b001c0c2600c42e9010030303900c0100340c0840e2041000382c41415120b440d4158060404161440021400e22800e442070315840f00c2c0d034502d245132461141d03400012598000700d003001607000110610600203201c2f1904045c0c01000c005007510700c3d26600040b04000c05001d1000302440114515000d600d0400854516400d803400304500d03280c0342c07940f2418403010484081c7c000703403d0415509e441a58000d0700203030304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 613004640 1250 613003390 613003427
    0x603110603060d05070b03190b0607030e0d0c03110a06322a012009041508060403020d021e060402100c05070e0403090501080115210204090e0706 64
    0x108020810049250401000d40c1e40000395007404600154090041201500b000d00449490341020300b00d0b130041503054408115594a070142084899a070801540c451941c5032415015082010010a038a2120024014092755001c040441001120354501142c020240d4001c44000d98482d003c41e10ba80d000c1c0c0d68603c1c5000c2810490507001081502c000c030002517500681d142c10079181c1031a0f883d0070074442100345001b070030030a002c43c10020701400c4007107900d1004103802000c1c05d041604441c824212214803540e40d41c04d50302010401d201c17035a402410070900751100e40c5450b007000303074030303a03e0007003081c00140980c042c1300404c41e180c15442d20070b002c41a4003d0150f0754480d400d0000f42100e42d8480c105000410311202c00007001000b42c000504500c46011102c0c3c10949005041142d0a40026041c80f0980006000644501c4030091103160246032240e844601c408411080540340300f004c01c80309000060100e00950342d0342100011043c440c044964455440b18102c85a190303010b50301001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 613005890 1250 613004640 613004663
    0x18140705030f0a05061c080d0e150f060a030c0803030603150c04170f1e060906040b0708060d12050702090618040b1f03030801030312110306040c020102070210030207150603 76
    0x40188070b031300083e80b00310082c0800008050304100380b0184070460100319182c0c81c00190358017624865000324219030a481c0c0c028100707c454002c08490a140043c07641030035110010000f004da81d2041000b0000390f4000c103500001c0c0ea04d40c50015100d40c41141c055029210b04101440b0745019100014402d01240f280c4130b0406043c0a600440ba03003030a4054201071040501000482c40d042c00240e80070100308014550000b0b440c8221420329500806031601500010104400300754541c001c25172000c003134541400c0c0c0d0780c2c6a00010300804000320000c5c0c125a60303168990b4840e5003041c000c0048038000c90b41c4107690f503103a00402006100e80c00e0b400c1c2510000c080400d00145030b1000e81600b050005001401e4a49100e01911060949a20550001c0c0e04bd00c0100b00340364004401941c0e2102c00c01c814080300281020024841c0b2000d8503040c06070780d60318038811040f82b0079410340f0480f80d401404500341d8107101070010065040124250307800d408590311007480c81c0d102e208040403244d22181a040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 613007140 1250 613005890 613005901
    0xb060a18020d06030b0c1902030304020112050606190302030a0b0301021e2b0204030204050606161b0e0a0509120309070302041d060f04030801060212090d080418140705030f 76
    0x650420464201d1043d12040c000c400078140c20503441c03090500c000e129031203a944504292407002400b4035981990000c00c14000035076404410414152000b4201082c81e03200c1e040032481921a200bc248034041c1c541011405550f4550007c5000b49a000414446480188209801c030302c44c01d801103115940300400164154005805002e402c4032904003040781c0b0440c4140078030b18500341c65489025030b03800503092003140b51030700c00d080d04030105031092400c0a908ea449191a8218108003a094001106180e104076118103000d801402d000110b0030341e01e09040381e00101820003920901c03024094001040d4846607200140c0703124116100c01400d4a030f2844c3c003030000502c05e015034a001c0768100444804007040420002e40034050b000c009600034501410000d00854042c3c0011302150402d040c68551800725400b5100071074000c8070800070340c0380d50713103002c403540e00c035540c82030110f0640580c3c600206040d50b40000d1091070258105000c4c5c2e42d400408603002c1c882126210712113100c510201c0c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 613008390 1250 613007140 613007189
    0x5031902090a06180902030108030306091b0705011b03090c06210216030e0f0a030206030c0909130314030c04120c0806010b0c0c0a0b0703080403140708070b060a 71
    0x80510405010061800d1092030210b054801580c1000300481c5468684200c0d81c15840501002810110f00840c00d550405100580f00e00c005010320f0300c80d48600001c180c68894000300c60380d008061450342c5944441e245080e80c060124044c03c100c2c00300010001e44079040c042e001d8035900351303400051140003900300700d0259040b1030f000722980c0b032800009040a80390201c51008008214804803c100001d0032490003c00e007410050030315006510710f145010081d212002d200041d05c2e0f04569481e01d1340e1b1101640c040c0f500038144150352000ca1075060222a51f202c0d8401c03400a80a03030b031404042d400302d08049069110503140b201a29004010420410b0005406882c0c0c90b88503030303401e10004e50703510030b0300341750180c20f8202d0030001d4000682d107005904200074000c80d420301501d1850300b1600c1c1089590480c0182d0303c1c06400e0203042400101018881e81d16840c24510803200142c8070707902410940c903a500101022240d07003c83c0404117005140c000c3d401c00c02c40d0080040380c20704011200791038 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 613009640 1250 613008390 613008421
    0xf0b040e1903020f070603021902070501080c07110604092315060306030a140708240a0902221d06190e15040f0b0106090e0a0c09170604050606030705010503 69
    0x20750441c00346000c0e50442d01424004172004050507900982c803101c0d40040400100d11104604083d50f100907020486030342c00400c1a42d0010302841ca840d00d03202a8203042c00010046a0300a03030012000801003621a80c1e0f030f124009003503085151010000b10918103002c04003094070030040841032098901e10740d10f0309100840c1c1c4110007406580c4207400307654030318220300c07010750b9042e103142c20052007442408420008007140c50901c0150700b260300c032000395003114000040d248024960f101c0d448003081d904c13070184030410b2203100d11030400101040082d0100509068694008405046041109402000603003e000395045080720304040c1c0c4204c1c00c40002e00242e43d080303c50303015051582d425205800d98991107203020300b0035100e44403141c0c90400309403030050308203005000203500d040c4032041c11032074043c0e4000c91441002440d400089403c2d14001e04941c803944940905000310181c0200100d162400b0340c0c8200c04035071751516408205174507880a8002ca40c0024002d01c00504203c1042005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 613010890 1250 613009640 613009643
    0x20d0503150418050a060c1823010302040e13110d120309033608031911010b1e0915030d0327030c0302060108010b060712210f0b040e19 60
    0x20707403490300035660142801c01d001400d4640c0c07651414002e4405030406148d10030f0002c1500a035a4450030b0009910755a2044607082d1241040c1515001559020783e0484000e0112588034400710700e419101408407014204c41124814001c00340da4040c1d0400c0c0c20307030206045c1e00c24820000803403203a20440c002c4c003000005800f0401d03500b821403884404241c10054506c2070120380d0340810754099001c3d0060000c0d5004801c02c1d80100312255508542090500800d000ca18000f80e1507060452040d000d0712000c9441c3da4003c1d00041d800911102c0703110b00f000d8260050310103203041d0350b8403c1c400c4045000c04640c15050f030010000c10030b28034400c0e88201ca1500c0d0340445420050a4882c10b2144400100c2080b00450f640c0b1481b50203241e0100507050041007040e0080c48085a0400422602c0c00781030001032101e03084560392242d031402411844c640012010700451003160b510082c0c0094641400344207035441c039101007008035013011700806000940031402810341c4154000b90030340c8000102070 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 613012140 1250 613010890 613010921
    0x614090a0e070306140d0c03020114070b011404150812130e090f0714101d030d0f180e010302091003060c0509040b060705060c0a0210020408030406020d05031504 71
    0x10078200420300e41503005441d141e40c001841820050b010f1030062101c0350311442090200b04038800100210169000e980d03081c601070030702040c2113006480c5030144180003407140b4512400481d410f42c5031350342d41810000c2143c06006a0080c1200e018620360180111740d82a00542c666081c068030a20040c82c11040444407030903105d07543c00d02441e02250a440c030404940000300381303e05e00c1104014410207003004c0c50f0140302900b43d14001a50380c0d4500301d681010300c500051000300200e035031500705000c010003030161294001c103e00e00801040000c14980c3c0441c00c21449207440e41c0c8030303440c0300c416607a40800381c0b0307900c2e401c540810070300c0070700281544c81d01c1403500300102c00202d0f07d00902400f41415251152208560000c00c0705442448003031500614080c407092010071400914260040b001c0400ca6580340340f031103000c9050100041451012600001d00092050400002441107521a03800e4542e0f007841650212403a210559100010346203844040005140075803011030304180a16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 613013390 1250 613012140 613012159
    0xe0405070507060612030809071202010e040b090709050306074e02130b090d0b18070803040f06022b0c140c040509010516180b0c061f061409 62
    0x10f462070150742d020740002d03c199403010681c000300758000065a0f004034843d8060003420b410540c0c80d000a40b40c1c180040d0403c140f031310fa01901510b80380c0c0101111034001e042000f00703180c4200701800d001114490b0601a201d40400200c2241c13003000c0040c4409081e00c0b12121544404000029010700172207070100307480741100c4c4440b288540c0c0f1040d10200e030100f24056102d18480041503860403050780060460310040000007850350311410003041f10350784916040065110500210151b001d50034010780301d0b200b1498041013504000004c0c10031610b602c80481d030781d1604e44004030389170020b40b064081d02e0b4140300f03107500181503002c1360450045000e242800b5501d8080d101c003008407403c9084004160803240118889003400e000300f036405071595009001c0c0f41060740302c5044900743c0c60009410000d03a481da903111400008120001010380f401c646459240580c17409494000c2a194241c0b403c048001404002525983d4482110700c00d0701c030100105c2c124415800d00350b0010307000603800203058 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 613014640 1250 613013390 613013393
    0x110726030406090303320304050a0203030c100617070312020c040c112514040906020a0201050726070e040f0603050309150906030c2104030c120309030e0405070507 72
    0xc001401c01044103588000c0403074510704014088400410041d00301008181200700114980d080c841030464004011a41d0f9948500b80282400c0d403558009505000c009000341040a0010700d5000741d68a04400f0001c00d41e0354170036241315500c45800991240c02c050000c00119082400320b50380080c1c5401500e5100c10a035002404940e24a0700d4000400d4108020f08945d0100708444041c0303940d8861640310f440d8000401440e10131031445080c3d0340c04000000e520303c0fa10b07103800004100354400c40654440c0743c01c2001a01a0808480f0800001c1b20013180c8581c00b40031291300e14a002c0800884816500c46a00403103a907010020070580058480048002510040c03040360001c40c050f0300615102e4420304100008802510291601408144110798050303440c18112134104c100e02103032560300c11009a5284601103140c01d848103a130050780400c030500d0340001088008a10400070320880100c2d4000950445203508030103400250081d20882c2942800d80c481d035046199400c1040c00c01c40d00307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 613015890 1250 613014640 613014643
    0x403020d06020327071a0a0801140406030618110907050f0310030b040b0405070611120c01240602070605031510110a080c060703020702090f1012081801110726 70
    0x154044c40b0055128000400581c554405100310414864000714982020b4100c000c04144040c010b0b8019210383c0c001096003940c1d260701050027150f224005010075030703c00f00c40c0c154205d10342e03105031002c900c2c101030007069140141c81c0c1845111940c85817824203096280d000c40304c3e000240114100802e003c800300120b414102d940740714902c65103c0092500c1c0074a4900c0c10003005230b10510a00064490020007a14080b5000c201c0301c4c803103105d0980340e203d4214414003420620030700c040f030064484098400181c00361291800e0b02c0064003107841095032440122582c3c4011030347ca1103207007500d40d040302840c0380140840040c081c451038080c00348118280c616003400c00882045841c10000100000d80b50810b01240c0d074010510300302141481104d4001c00e06642d0014010042003030388000044801e410300414101401310344c03940c0c141c07182c91460300342465800480350650301d0100c000502225031281d00346a036a2000040a01035403454401d401c0314074070300300729031034aa280c0500341d0b001440070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 613017140 1250 613015890 613015951
    0x30708130b040f03031b052d28020304050d0b041406090106050306060603010f0e090f0d09060e240c120c0106051f1d1f03051504020403020d060203 65
    0x520f01030001d180149409801c80c0c031240d103120188490a040748000756006000c1d58460552503000b082004142032038003003000400d0890b141415000b0449401c0382e940400103102024088140055540001c0010303039a0340141e100c0c55030f0203240c00749144002406241d00d2078200f48500820003039800d4800700c880c2000411a00742806a5445074100080c0c5000c016182d0040c10507144240386506006413450b05203610300820040606800200388400300411842403044081002c3c0c0351141d500c100d00504019980c42000b00045a25448c5600c0d031801000d03240508540c41002d461116400710300f500c1071b800c00d07803001905000352400d1524903000c480081542501d507100000b10725080c00204a4807111082401c15076080014401c00540e4000c40c2210401c44940309403801804440001450015400311141001071031114a06e40c1c150103030001c502411a41811440c0060400248402c0b0301507840003943c49110010f030003001c102c0c00e034025508800c20f058810703280854401c041c00b4000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 613018390 1250 613017140 613017143
    0x30c10110d0f050a061a0d090302070803131d090a0209130605040f030305070c200a05030114010806092808120c0705010525110106080d11070b04050303030708130b04 73
    0x1510740080141c00401303841400c014145001104080344104004421140a1108a40d418580e11900c1d001450b008100301c1004050b0003040381c0e9904080300c9110440038080c41524078944500002054107091036400340d05c2a9005002403032141c120f5000c202d158080036101809001200340204007203646805458400c5000c3d1075680c01c400418a8010101c5000922140070032502d0010503000800140e07002c140c01c008000b08104550410f0000361700c84202d94800356156203080341643c1c50300000c44400381294000b00a071516a07840c040c04a440b06000c070540340c40030102590082e2601c2c0220508100c00d030051540f5420700400b08518003000e42c0c1950950258400402c01c003040050900885903c03031307008600c0000da01c0a0ba0b0340d0540403000003d81209100001c0d0000100450075800000101852070440b03440302588280503015402d4294584c048d4021044041415240141268115000a0011490340c0d032035403011240321001034441c0a103810605011000326900d80c1c40c0303a0089 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 613019640 1250 613018390 613018421
    0x7171c06030b0c040f1403010b180402010f0207080a0605100b072d0209010303050306030a081305090a060f0b0304030201061805010501030f0c140c0703020a03081b030c10110d 77
    0x9815410b050110441c010160400007a04100601c004185440604215100050580000000c00c00020f02400b41900e06d0780c2c00c0202c02805020a0f50703050f04280c0154000c1c9c136918044000108100d031034601900a1700201d6002051000c0020b21503403040368009481d01d032001c00301ea240c600b4043c203540601070a0b40c00008640035454080001d0080803100c20380746140d48004c00b5642c0c0813030410030051201030240f00010002031002d480034090211000d611050995035156084d54070340924459008043c040c006603c0050030500141c07190394240c8991350345658000740392440600040c0c3c0010012000c55495000020b0500d140c40b41808100744031400204207503040038001012900362084618095040401c40e0380ca41d81c02840028062223040082581d582ca5100c69034502582e07940000c1d0808a00940042400304110203804242505e250f00d070f505040000091380d90340624030040015412006280c3c400c001c0c1035001035580066810b60030b003013440180b190701c1200d8820f10520f120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 613020890 1250 613019640 613019651
    0xc051603081b010501060207091109120d120b03030d05070909060e0708131203200c030c16081b04140702071e0b040e060d0206040303020a03020c120307171c 69
    0x85203900e00b05040c0c00c042280200419032400d0320080d518400e5208070100e40d640c440d20788610345080d9040741e08044003d0200c0001c80c801001d13180d0340b0801d00c000381000030b121b0400c00c100c220150140d20200ba80080056042c17042d05540c2c2e100800e8044c0580707007403003c0c0341000150712446005074401480303011251003580c50321300f030042d1100d18020403050642c8201e0350414002200000950b908a80c189400154006403c4c84c0303c0701d50560090307000208402059061040c00000010f01c81d50b65035406a400b00c07082510b05002d5045a4050310209070003050800116140c051181903110380000c2010540c10a20003402e4210341c030a58000d8010380003a482888066104100711540f1000410302c5c40c005842d0a1172080d260080380107070303a407101c2940c012511942d540550014500d0b001000c0c2961a50340e8a0040d58501080314218054000e4070020707003031850091202d40e03600c48040003031842d103007540e0740d0121031400c501c8440c518070300d090002100100d040091380958400c180300000e034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 613022140 1250 613020890 613020907
    0x2030604110c031804150e10092c10051312050c03090d02040e0105090604290a020912010501080706020f06090309120a050a0c030204050f0609070c05160308 69
    0x191080341d1120244120100415010708100104868407561076407604400002d4590010300603000c41c07800640b1200d50140e002c00c00d40710700c0580070701030703407002921079204c40d6196206400d0b241030301003200c104650b01144184035000810358620036200a01500c100492400746102240c00584500d212491005826001c114003880b480102a00394200b40c1e091941c28130f42213a1324825503c0c454040c0823452403c0045460700d4005044030400c100c000d010901d4070030039050340c9a0080f036096554846404401e11403511464505844591302656a002e0b552010104806074bc400c05000d43c01401c00605800d8094080c8202400f8100382c1d4080d040141c90054001d261540b100260116500a00e080c0070310040004119054160190385001400348202801d604111455038040e01c14003c0b954581e080014490344681528400c0302c0800198503000f4104104d62000ca5080d908140d40b0303008a105030f80a00c00100300244a00121495000045e10760301c0301064551040b194000e010941c1e10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 613023390 1250 613022140 613022149
    0x702041b021515100c050d0503090610052b0c0305060601020f03090f0f03071802030610030c0e0f0301020702060417150705070b040809030a1104050901150b130e0406020306 76
    0x1010b2440e10a01c000303d041c0700c4500d44800c01c0e000380e86841040c802c075144032a18018428806950740050a54a000c85440c2c406441a070084980c0505406040c00158103007204100751000d803100038180001c429145842c40c0380710307007100702c6820100b20350a03071110000304c500340c0d000040c500c940702030682800e140f03001900e00781d507402400b01d8070741003030283c02d0060300d90b91007840c101032003151038500348404800402c0c00d1224582180040c0c171002107804884030000d400031070040209030b4100c405a110303603004800b01e44a45101200040c02d1612441c154940010001c919100040c00146042640e40c001050340c2c1c40b0788d2060390905412020500390312410301032800d110003104411410fa10f0705141c020103900c64540000c28800c1c2810102c1e040c0520f450681e0090100641103c00400c920b04107c00daa020314104144100c1c104000905c0f610010301405103d070028080d207600d4541081060401a00010907446000c040b450000480d15100005240224020900185d40e82411002e20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 613024640 1250 613023390 613023403
    0x3120c031409030a0b1314010e16270b10020c1f020d08040804091107050106080106140f0f0316080d0519030e010e0f03120f01120210050702041b02 65
    0x5070041e20706000340741d000d0b00c000c01c01001203036105048049695680107440e040c03214029029088510450a5a10300003056100220518125040318140382c1c80e11a0811000f01c0d40c018220b0803644240b92030b60701e00c850640c20344030581041010070001e04100c041485080e0300c020000040e407040e0082c00050071328685200052404070001202038200c804060754450040002204005107840050180f10f14841070301e01030440399000380107628451800c1c1001d50010171054500394a0030500080001c4148218800c4031a080c148410000c4280200119001590100344d080700c00241210f00030313075091220014100224091202035410402e2152411030b1150010043c040100a15655440c0807940b400c0ea402541c44d0202e4001481050103001d00a414001e010302d100702c0704541145a004400340007014001c070b400b0300d41651880890004045d01b841501d0f0300c1004082000058201000b94140311002c500781300d4074004166010a08031801400800c451061222940714180c1d07060104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 613025890 1250 613024640 613024667
    0xb01030614090610090503060c19020c15090423041203090309050d060f09050d0f090e0601230403120f0804030816030e010e0a0b0708250903120c03 65
    0x4400010720140c010074071004002d45118071a00e81c010000d01003501c00c864980213403002805640b4207090040c40ca03c040e070040c0c900120040203c0c0e4490300424400a2180d13840344000f00303490b210501d107280c0039503039070302001030950003980741e0307a072030070641307400000031000040384003003460305140500305041a80c940310300c00b10405052402032000310b40c0c0300d2010b8080d510201d41c1e40d01e8542c02482c00e1001081d540305502407a0b41402d40380e400340038010035094410b0391a5111200845c48601088520036903900450341d1188245010400740e51081c10740c00001d0550f42c80080340c900da500d2039556207170456803084174415403401c6101d403807a03030140c00110031140c10700300840316007000d40e0045c040d244000c1241800023860704507011124030030340150901e10440320080101110301c020081d1142c600010542e07510300490301217041c0c1e620904e101c1d0f11a1060139840c20503995103140d8021151199008a02002140540480820403c02407011031a68903240d2020110071450068408040b0008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 613027140 1250 613025890 613025909
    0x5060609040c0b030a0e0a030e0f0312040e0601181403120307081306150b09030106080d020a0308131203021b0c01050702041e0920060a0906210507030b010306 70
    0x9000000b00d5040b480340c10b4501540b08a5101e654403e4142d0042003424075044851080c0c0f44c0d00000d158025124889001054401071102c000d06c1060554500c055440604040b070104400c000300008010083d401035014075040c3c1030802c001807001414031054001300048040d5041c00f4001e89020040036801195202169082d0701d0110001b902c80700006150b090a00ea0410020040080b10741c00041500c2c040d000c00200507844031081d4007590415600c181c065807915102040034500050f83d8400c05415038020100d0024a0313034100d50300360300500318880d450300c5180c0e10030020780111720040780104580d0300141c030b1341d0854903613054150311116119400d803c035290090b140d0342c0c4001101ca2164055901191070001d100d010310300f8001c4032082036070f45440c01030302004010420444c0b400740341d41080c003410b2520495040203d54800c2d008560081803841030100315450080c04076103010010300003c8200210101c0507042510801c031002400641d46011280c81c0b582c1511800000e000880d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 613028390 1250 613027140 613027159
    0x2180708070309020d0f020109180903021006030f0201050f09060f0702040b01030c020d0f0905030303070905180c030f06060d14010f0b040807062001110301051503100e1503030313050606 82
    0x4022034410811358001401340d546c00690001564010b0051000a2282c0d40641d00c03801d2044070040c008001c00c0400300c005014130201d80707002d00c00500074030381038903040307840d054020041b5801034543d40e1120118200c100c0b414000240a075540d030024100300b00150901c3da5407024144100b02c1111001c2e401603042c075183c200000503c0340c0c00200b02d12601458144040580507440058914a1141d88025858440007007001100c41c1d000c4130440452f00c003950442d4983c10300303450750403807a20704546007400084240009581000c0782c010198204002030000c62074a007080c0c5030081030f2660181007604610b040350040060b1034a41d18000010300500c0c008904180c1040c4141740c9460644c414482004412040d6150510142211348410030111008115140442c0740511071034000b48036051092181c0d0030000d240e4007070070307040301d1003400c0d41d0407a1400750741008100401c0b07140161200020b108851820041c0361001c200030740c050154006a000c82d10460301e8481d01d040d600410700c6020f5281c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 613029640 1250 613028390 613028393
    0x1e070f09140c0a0203041205030d05160806100e030d08150f0d110a17010e010c0c050c0d11041a100e0607062706020909060307050604050f06040302180708070309 71
    0x5154940c2000e56440119514004100c0480c50350007142c100301f00c2c8a0000c50001c0c1080000001401c02c03500c580c100b0f00043d41c0d03101241020071384001c84171001c64030003c001401032501600141c007003d0242018600300501c01c0100b482c0c403e0100703448002c071381002e0502c04000400742100310b4074a800c852400e403031008c580c08030340303480c1c00840b008003c5007021034040d040c0d07580c00c61007078050070030036080184080605c0900f80c0641100c0712154121f518008003201880d2240385100d501c01d0b0000000c0c46880440307010b04c04003940d4010705695136069000081c5065540c1d000d030101840380e5070709000b00c1440540c10414a080071041c0007050248038889903006481e240c06440116030403007000102401c521034515081c1b0710f500c02544008040741c0701c50f001c2200721b9010388820007081d1034001c081e41d58141030654030ba00c9409003070f40c420414007003003110f41790460b40c002c403041010340a542803968a50101c4d20142095101b001c44854000c00c1013001c9034000100c0341c0c042c040e49000d1103001c1300c9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 613030890 1250 613029640 613029671
    0x7051e07030b04060b0d050312090a0c05010c05010f020a030c080a05040b041403040e0c0706051008101505040906060e0a150e070519022404150b031e070f09 69
    0xc0d1000401000b19080043e060210710790000c41d4000002c0c0400c201d014282ca0b255842354014030840c01404c6120010407001ca1000072000703001640b20f005080c8803803c0c04010760b40d00c90f84c150122203941d26140c02250940d2940040c1515191640300032910001031071015004610061504503203a2402007000049501c0d0281560465001070a910140044070003190461041c0e4114980e00d4800c0b03800e1140c054902802880401d00424003003145803100c03c00b6061000c0340307110300031140d441041300e1600451940d2143c10003400040f91012255a00e502180903210245010341d1003990301d070780402940c0d00c089007607039202c80d440c04c0801001f5201c00200c070840405000e50913032010644005540c0b940902c0444002e064000080d803052000c01d40000e40d21102140c90f85e5000c544010b01c90301d00c0ca040d10f41c1c0b85c015944070010300b0308520241c110000410440f044298140b10340c0070111007501d00c01e007041d1008070844002d0f04505003010840c0c0c48180c07243c0c4c000712100380f40c41141c0141d1102c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 613032140 1250 613030890 613030903
    0x14071a03090303130f0602040e100501020105090a1209052101050c0f040905070302070209041209081f0507140d1b0e010815010908100203010302091005030703080c010213080307051e 80
    0x4c0128801500c00d0030b604001401c1c0c00c00d07890080413144009000301c0d0350303003100c0321482c89803452404519510b1380b0b0b4801282a140c040d20141c0982e071000b250130b00010101c054028150009203095480113649400080720f040080f11000c0480c038881e4034501e0014000e00440354090702694020b481e1181041407800303a4481c0c0d02c21000030665a90203c0c210507c650111001c45800400c030102c1400c3c64106030140d81400d1f940800403407911790300020101d4010441a150742442c4411007400154940302e280a000001c10a07802c010b8500d14060700c20110304040e180c5420300d20800100030031681c0080f1049440580160300f03000071285520803a070b9004080c90703884800c54135162981c240d0600143d505840c0c03034002070414050012480d00703204144e8061030489008641140b81030300c0d003841100540815025082d05038000c4031080c000308820788018500003c02000051411858200c451081c040c0d179007002026400c000b4004003407043c1042001000540117100702e914124001520741d8489 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 613033390 1250 613032140 613032151
    0x120f03151917060f010e070c1e1a011a12130203010c023003161202040b0a08150315040807150615081611070b0f07140109030c150914071a03090303 65
    0x1c0e0001c00a000c000c0343c5901d22080d81c0270706004010360039413450051500341904400c0009010054000644082d44038040280e24280140035403030407002d00b00821104500608101521900304d880500580b024072480a521134558050001949503400f020301418415100380c10035100000702c8182a11244c00320f07500325102c000f403a1105104d07a00281c0c0d1841c00110090030251001c6400500300702c140e0300400c518401c554070554181d542c034100619102d002e041007501640284888402082c203a00d003a1342042c0030700d2030941051450b540d060389002100071150001038503034108003c01c001e1b901d0400000d070b400e824034094900c0d095810b041c6140c20280c821003085000d001054507444107100c0c00025040c1c454100d6540d41401c0d402d103926600c10700f0212126400b800c1e2469400d10306200c0c4180541d41030b07803240403100c00da8070f604d40801807186e2040b4109659008410014903502400c444100020018081c59403910390210340801c00d80ca540b82d030704042001040700d40403000c412680e102 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 613034640 1250 613033390 613033397
    0x106140409020f131b1b0311030d0501080703020a080312061527270c03040213150602120a1b06060b0409020c120f03151917060f010e07 60
    0x6892500001c3c0307003088010003260700180250420030307181603d50030446420030041180941c5c2d540c1d024040391750000800c3c401c29028100d0300c90300002403052103800000ca40c00011203042c0200040d8481c1101c10a0703020181540c0550b40030170131070034038082540040c00702c0c9001d5800d10081d0401c054505c440180b005125564a03a01d841c0c0a5110405079041424001141c2c484031003520a0b1a400d1000328450710b1040f03680c2d40351110384031141312481749001d40070b1541c660241c580f000c100145810181c400c0368800005001100f000e1441d01c620403074000d00c501d040c1c401030300c0d1520190400341c00301a80e5844070400c00c452201903030042d2181c1e8900036099a44034943e5000c1c00c05400511254212150030315001600041d03040360780d00541509d00c0d007401a504100200e04d60344800d4400c0c12150750b5007590910001d41156451001c04258030406002d1203940d0740c420081d51720040c4140c1009a03400b010309003e4001d42710230400c29602c07084181015806504001d0f031035458440080480080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 613035890 1250 613034640 613034651
    0x180d020f0f060f070c0e060a081b040f021c060e2202030c031606020d081e25030204030b0604020a051e040e011214011109041802061b060901061404 65
    0x10350b1260b2003254071015070014140d03102c45061138010b0f0044514030952451203070400105600389001c038800350454070003000821103c15420781440e000d1010001890b40903548820300000c40702c07140000d04806824001442e40e47c00c0d2020900100e038032581013a140d04000340108006800240c0c0c0c4130180306d20840d8000110299031000901e0304031301c001d07069098003402d00c000c1ea450444001d0307071703054425540076240c1c002d80850040b11501403c460180c054840c0c0c10981d410000c80d00129a00b041c83e0700a800c0c01c102c6e415400c08100703600384c061400040e6000400b041444101c42c0c142d034000c103040300c0035845c0100c0904010240e0154002c06001c0e0042a5401d0340b207806940c0407580102404044d80c0d0b540e6075102c4ca403100d40300c002c1c0000c1c1d0b4404e680e03210031070140406124000403240003c0e000c86c1080410014817005000080309a2508104e102c4982c02690b5448040c04800002e00c10041003400c81086050510300f002d01015907603810308506000300010b500b0030f250452029100080c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 613037140 1250 613035890 613035919
    0x50a140319050d1214070c080702090103080301090c051c0513050f010f05070e09010b130e090102030a0e1504020f04020403080c06060f190b07030e1203180d020f 71
    0x200001040c2985000d00346100e90700400001250880e4500055200c10400c400308402c90002c0c2c13034070050f841000d1081c03000056940da020310100c144190052144504207045030340803444c803007402e03001955008000b100401803040b5501801107036419910b42103090030b042c4050401d5624142c0003c503101078580c800101c50311044806c441c500d540100c100c4850f0030800001900038030f03480103103c0341c060910000645003030094810164800001e006000582e00c1c005107400d59801580309078a02400100300003c8802c4102c220034098900c820005a403424500458012503201400850190304a41c12032004105c1c0c0040c00d07a03105070142c1c0c5610429034074000241c002e1089400042010402044c40d40c1c141b500010784038400c600c166060310703140700c2003070400c9015a003130a00003214941d001c0701840a103403070741c0c05054000d00c40d04010007101c8442c0001a03648036902d00c54100c4c0d500116100040303c101010200b881c072020788070b411480f91245c02160300e500c800510540034880d013651010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 613038390 1250 613037140 613037143
    0x60e0307080a1106060d0819050d15080c0118090c03020904060306050402090c031902130f030f150219050a0905040501060e0f030114131e0c061107050a1403 69
    0x498040e0300c10030301a07a440b5008000b620012020010308401d01c6044c4c0000e606080c100c0510134a240c104425900302203d204040807400d0458401e1000c000040c07085c0ca5000840b40205951740740c045140c412590b08000d000c2c0d25002080c440c081c100048500b2040d140c0d00c600c116001500c3c0c00410210701140d400c0010740291243e07221464201d840c00f240042400700c1c55100314060361003254141c406840d0004070540c01d00007a41c02800300b40c48207914000200003030340100301d0303540021840c03a61942d03108200450000a0382c0f040da88240407a0440d020800101007103030102103651720460800103840d525103480c03415544e008060010000358225814050210340c40180700c028002c0c0820340c1c440c41e00801c0f0b0b50a000d2b0007030003440c0300c03110100030345410b00403019000c8500c01c00003440d41d44c0010300e0030103d490072419200e200350401d02c03841007e51030301340d506054018150b401c4a1441c0c618010241c500e880074550321500440000d01c01580c0719984002120064003016281d400902c000030b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 613039640 1250 613038390 613038397
    0xc0f0319181a151512180606011713020f030a0609030f02011b0507030c170c0c0a050d02151e0307080a0e06011a160c06030c020613060903110d0306081b060403060e03 73
    0x10098440004006c401010344903c080d00c0c005080607a9131a031981001542c90041c030a80c02d2564000c13120000310003a94203030400d00241d0000f0000c0c440d00c0d000d100401d0a12064160030b43c0c104c1d4442a1410905420060407540c4910620003000720008800c00d9040035030140c0764400c10020700146a50600d446070914104141e0080d260129101c02c00684521076800300c0e281040c00d0258080d0000b0918000c00440210b68020f808810862595400c01c81d10042c0d04034040041c440c20300c8440c0c5c40a48500c03080040020000181c0e94a0500400240071081d0007056000c055081030502484207c001c039090341150103800341c060007009000075140950050303100d00700f841c048006000f402e104444400e2000c480c0241c408002c000029a000c80e166a0120380500d0f036180c418495000254460703201c001d04501920b45150f9031080003103840e0038200b0078030904001035102d44c01071110b02024000c101050320001500045000e924002c5a903600991001400442c1c2e604e8000c400c1c8081403085 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 613040890 1250 613039640 613039657
    0x150b040c080103020a15120203100e0103081c0501080c100e12061e0106021b0a03060f020d060b0a020a0305071407061106010b030c0f0319181a1515 65
    0xd0042140480000300200c07003d100a038801c4001340c03000940d02c400b00c8a01c034030000b003564440118119210300c02010b0f41c00901002c41c40c04a100000440f0f00d40c012015011f584a29080e42c0d84000204046a40c80100c01003645440d02c0d240c010404204009140e0f2800d21050324a4440300c0d10082e4150fa0341a86510b9468200b10302120184840740c0103c0e610f4812000707480c1c10302840ca0b0000f4916800d407424060340c0050b0723101c40c4a0944441c07040040921480004004610650300c0b944e440b030035610302c483d0883c0f0702e42d000f0a01c4010140c0c280161000b804040810703074104000b4001c02542c600316904040c00340080010f449041c040001c4140b40d0031441175088450f415a29013004200c2c0307020803041e40c0e084c003c010010a0700d5a18008681c06101c160f09198200004001c01041d26407001c0d04410540c05018100c510010780d50280c20314500c1040380c1d032001e0140904261140e02d0000441008840c105400c100c44413403d4081d449071701c034082d2417042c20400050100b8015100b01e545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 613042140 1250 613040890 613040899
    0xc0c0f0a1e1e180e06071202070507091b030b030d0309050708011109091003050601060f05131502240c03070c05010e0c101b110d060e1b09010b0403150b 67
    0x765400c5000c0b41140804548500c203001441c0480c24030f1240460303607a110505481d4101d8004526a02d01c1000903192442621100604e006500d541e0103240525aa22400015445140d00c801d01201a49140325044a1341002c1c080706480d40006500c50000260401c1030540d503688040c18000c04101c0c2d680503001c03a60007009025003031050880750b6000540c41611440d00200000d01c814180440719044a41c840020592a400d0a02c01e68410602443c00c0080042c24031055220028103403500f8000c00908811103040200e509009042094024a2401c2d02c0c1401c0701526840c0070302141c265200c140310304440e85035103aa00040f580d0540100740508075600303100c00c14400030000705040c0304041044402c0c03082000c0f03000c025035281c803442400c40d1a050301c299000020441d894500f00d4521001001c94030b03158215640c1307004840c2d0102d06014164001c98001031010111061402c00c580e040f100c103c4c0c60b62402507000120700c207500000702520304114109071011419001050a858000c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 613043390 1250 613042140 613042169
    0x309171519020301030803150a06120203041406070810060e130e0703052b03090201120c030605060c1005090c03070311060702060d090b0105060f07061a03070b0c0c0f0a1e 75
    0x42c034161b02e40094814402d00d07004800c642e00980340401c4031104541391601d07141200c0c10980d1410b002500001c0040d43c4c1c9510400007074141500034000e50784114407540f10f42c500741c02c0141e16094040001d81111041c4203840c98101d4296680c0c00106001110180c3c020580380c200b4218a420075080358001000391054000c0810b44880030b04121031800e2110800c84140d22020408509460b241c01001c0d002c9681e1500a50400e08143c1140b00b81341107a007404202940e07203001064095100000341d06964220345007004144040e4010543c00c5464800240f00e040244400680c4410943c0b02c01044142d404240c8541611444140c4803a2038005100544030300140015a01400a4120484200079502d0002c12245800d20550700f14510121b11541442030075a1040001d050580440d40f54054161811946503001c02042003c0c01c1403a041c1902c0364441c200e030a18000c841004e075841401075500d4255a503d0381c08850b011a40840c04140c0410040a1407075406c4649070070000d03000c070801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 613044640 1250 613043390 613043393
    0x50f030301090b04090c05040203370e0a11131103010b0405010e0109030b1810050c090a060c0201050a050901110a05010516030b0a06081807060309030917151902030103 74
    0x4805141280d0351003406100d01220391081004558110310001c2030361120300010304c21410aa80550b40c03102404250f40190304e05400b50040c101c0000d803410f506851a1000c4c1001040302c0d014622684007014000d05500090b076072202401160b869401d401245502c440062003201904920914540d00c03c0d2103940c0d50f161103980304582c3c4507016450200756192a9100c49502c541d0a900440360004000301c026100c02000b04c0c03c941560b4000c10b01031090042001d0803a0252151600508000d0300566459910000703006000c038441d4000e05c2401000001800546d81120484d81c0e00c00b4235240c6159290003410050b550445507101401051181c41a07107010004158040c60007950652a410302074104014118103489803045882c0c0c0101c100c041c00c2000c01d001d040344907003001c0000300490101844a02c0b040c5408d10b0341c1d10220000e074407481c0090a15800524910107407405071805150310850b1000c02c1e64503030300c10044203c1030041000192400c0003a0000c50405035070800c1c190360341d580da0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 613045890 1250 613044640 613044643
    0x42a0e2508160311090a1d010506071a061c061d030403020a0504090515130b0c03060d0f11060a180807030b0a0b04020706020a0f12020307021504080403050f 69
    0x31220000410000d41060011940151080380c41002000d00200441d848000304401130824501d140c0d020700320900085000ea42c810800201822800c01110414100c1074006840e030441a4052409400104000404616144003107400000a40c820b000d030754540601003540d1b0b4a002d41c80f0b0b0400c054070f04d0304404000e85038008840003503c017405005800c880c0900e140e00c901c40c611009500c00b5002e08200701d44c0c1019002110b95a020f0701c141c4001e003e94002c900b020010445841c40700d041845080c0d01088203071320300140c025110302c50036425441c01001164010240304006000340d031260b1039072000c20206036011114480060b040b80c1c1c55412030140504644101060707544083c03c40003010420140004a201c00c40703401c500880740c0e03902c64200c91002016030144d043d03001070f020081a404600c5600003040840d520f035a506c4103c01010718010840c3c0034050b541c41c0d01d24010814494a15030000b03440d21000c04507488034070a0345562414080798440d651000b030190089168904418a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 613047140 1250 613045890 613045921
    0x2061603170c0403020d081204230d450e0903030402180709050d0f12090b030106051c0617060906070f03092303040f0509042a0e 57
    0x4261100c00340589003049061005030115803082d80034009000400c05441c00c00644080b6038018210541303010801c070445003601c00111400d641020303c03d500e8141004805045d415032200f188041c1c11012030f5030b9401490804080e43e0844d222858510034413651080b1a100d04100d02e00e080d0f07084c500b01186449248402d40c92142d0408110381d400000c80c00b4801008917441160b00070308801180008000f50104200d0141c0070108108a40d64042810340b0b500702101e020b103010b100f62a084030705915241015904910240d41040508982045080c0c4881d05403415116542071298441013410351200441d10075417a003020341030400b5000100c505100040d8444404c0c0321098a10b0399803801c4440f03942e82001d0303c11000046035168981c181520940c001c12216114503c00c3c414035000305078402010381080ea102c41c241d08006000c010880c40c0c203011600800d000d4a100803d86020b4450088210000b03030060b96041710000465500030020100c50040c003860b400000303c0c0d061130391505801e5031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 613048390 1250 613047140 613047143
    0xc080d141503060903160c0f030305030103210f1215030c030507150e012604141c05031306020712030504050d0801261f0506130c050708031003020616 66
    0x50114041c49041c003103030380c0b403007848181d0040d80b9281a024811400240c49081034954244c0400c0228000c01001c0000c0300071400380d50748540300d50440c01e1402a170f072012104024500e0705a000d041c0c0407504001203903444d50701414554110a13280d0a500040e08044a0a022811185034040208481030303041c03100b0b0b82d005170300b2039407929110345140b00710300e4440310402c0100d00c0150150034290b2003a211008801081060110588001c8484500000040d04c013150615a03059504441749c1c000c000c0451913411405801c28400a0042d01030624030020b04044510a090005041071140039011201260741c4841c40c40b99404030400001c0040c2004d4038200c0e80b030b00411110700c01e41031043d0034050507201c3d10b810f24121010959024045c40c200e98202003518003404505214911244502940d894031000340481c06241800400c807150003803900c0c10315218a404500302d4015440421340f100254418a002d076661112829900e1010349a40000e5110a0025881c01c00300d124603007400015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 613049640 1250 613048390 613048411
    0x4051903060b2409060405041d01050601020304050d080d2c070506120106030207020f040c0e030f2b0513030818030631020a1214060f070c080d14 64
    0x402ea0004104101440c405080031a1010f00540d8140600141c01000c05850007400c280c07520b0303501d0001c541942c049d150800c920010000e40d05d10404028041d5035882102440654601403c2a0008258000320000a484414040f60400c110081503011904414042c9440c8120400c4500588a6800d004216803224010301310006101c0c2008403d13903a45409503041800e5507030070418110025007084074140c0c1e010100420804640d2624412000444110b44d42c0c0560f0301400010b242c03904601c1001c0e20031030707440b01a011044043ca42e40f20a000d0b00c80c99035204002610b54411035540c01482000549801990000410418104002c1c0f2060611707469412112042e20101900c500040703450500341c81902a41c108406401c400c017620b412400a110900010140c01042c1c024045812154039000d507a0204400e028040a1032010034400070000c010302d160990010301500742c05400c0070140305400c0140b03003c005240054400f9101c284004102e0144226814110b224099510810300b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 613050890 1250 613049640 613049651
    0x4080d021006030305070b370c0e0904060902131b090603021e0a09090504080a080906090d140c060a060906050409021507021f08040506070e010807030e01020405190306 74
    0xc4030080e0060b00e044941544417039041203181d0315504441000107207a541c96108079034003840500b4010340441401c0301d0850301e00c040600d40300c032228100e560384010300081c00b4600001000540e500090315600c1540110041428621880070030001c90305108075100060400646580791015010703103140a403103694441d800341d580c41505508a2048843e0104d1040c000402005003201000041407200c106181450b5201c0e0345100d0340c0100d64040e1000c541005000131f49038007841d030050004c0d8000c255100079007082c2c14100b001e59035074441c5001140502c5940045550f00d401064203039140312211a043d00c04518000c50014010280303405489000b030300d010070100302070510744607820340756902600d07586024070703c0492000315030041d02c000c99011054440c4803442e44e44c4007100c0c000c036441949170350304142071078a4a20f0420a00408403001c101c403520400b482a0b07031050740c1941140d15800d00241c1071100c0c0e20207902900c17498018a4000791b081c006e8421001c2c415103413004403030141804102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 613052140 1250 613050890 613050913
    0xb091501031b05030f0702030d02040e09160b1e0909091c0206072003090418030e03031306030f0f061220060405190e0712050609010b2d04080d02 64
    0x45440642d04400004606000040906070005102904070003d401105e007008440054001079078803640100074443d12010500c40584030410500151048413500c1000782828208405a180903088220700626040760443c504440c0800c101d134015903020b0101c18803407411800f43e9a0703621b443d080c0c07000410180803103504101c0c40400c0090080103103076508640030f0344141e254500c00c144039441c044580400c0160b001550380c0e074403500c03d0307010150300249594080307810080c0150010130703901d9011f50400c015031440b2104c18a2070070143d40b8503041c001100441c0b01903410003012410400303a81e0320f140c060041400070b24070b0156040a40304204041d411100040c14526680200f502c542c0c002c0002e010501c00307131801c01c0ca000361a440601c800b2402aa403091003444844c0180c07801000709500f1100842d0400c014018940e01013000d44008407554075089070151684112110500d40303803911309a940c0004200f01b403003050b445590080c0d64903281c44602c0f0588603040941c2e01c00151060442582 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 613053390 1250 613052140 613052171
    0x20a0e0906010509010c080d0e010608070b122404050709051302090a03030f05250c060203070f151104150f083310020703030906230705010b09150103 66
    0x14031074501079640d1401d00c10444010740354500050011505d514040c042100d4080c020700c210038104180c14004104c1c00c1c91711203014145030705504200e0340c24808000c2d15603001c6030003100365040702241041313a6240d81154001e41294911408096010781408107100701907074461074a0056440460f070041442c94841005e0040f886000c1c83c89421115815040000c40d01401200f1211351450601d685032410241c4502c50300142d0b4019801d4003680e0703180181c03e01602d2140700c4054115030000390b10b400740c4c680310121001c80395800140044c41c0d40c1002070111145402040c5101490111242c0302d41c2c81c0c40000100600c01040c0e040080c03040d0300c1410086106c0c108982c003034071307010090350518540d0300d24041c0011408002c4c801e001a40a16844a0f81c032006a14a42c060743c82c3d02911545082d4a40200f01007010350062041000c0d80740c0091700300200c0303030030389032a2403198211503520f0310540b80041c054041c40b0540c036404201c500c200a50f00c1600810315003a180260380400155039500c0804 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 613054640 1250 613053390 613053409
    0xb0a050904060207060207020a15080109141303020f0304090506091f142709010e03192001060b121308070b041a090109030318050319051309020a0e 65
    0x5a02903100c10108012039103e500401d4020700a0502603e000c0c0142c0110b03040503060386c80a1400549c2451f00c40724550302810791809080000d5051001d40250326046180d603001808040c24008944049000c0600800c8981001d0b9800001c0c2d0782c980d40e030b6203100c4009000c1100d0941c001c48190700014900c510744104540f68440e04407422624038184648052002401d000558112000c4081080c2d00c03005040307220841583c1c600910003610349040d1142c2940d08001c85484540c2c014011186504a0800385d1314011005141203440300c82c0c0700c581141514445802c05a040d46464000f00c1e40c91002d0000f807000000804504100c0d4650201c280c0c04001d410b8006403c03004140400d01c001480b148100b60001c4c02610354410790005626041e401400c140c0314032623380e5503441e14004141c2c25010752500480380350740030107440c0c0154880585a100380c40044c1d811f010f600b401020401d001c1c00c162601c0c082001030b0300c40c41c00d450716040c1c80250b21081c807090100700350300c820400915044149 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 613055890 1250 613054640 613054649
    0x102090307240503070c060513110a0f12020a09020430080d1d01060e150405061008100b03090106030201031b0c0b13080f130501111b0609031f0b0a 65
    0x70340b03450040000100c0c0c003500041c000d4010800085103682c04520a4080c0d40e000b90b2800b500b0101c200b0f01890810b140ea0022503245002d42d043c0d10081080c09416501300c022111807054000900125200140031080f007038200d0307009941f02040c0454981d4440526142c03040b80d18013801c03021035030380150031407168101d140100702900c10402090301d07102641050071249024141c030800c40c058105150b09644198000d590300150084c10000c20a0960743d010f562050241c50411040c10b00e407000c24840c581e880400c5003803000941c08601083d0207404204014181c10b00000d80700c0c100700342c00ea4007030807007484241d0000b07040032003400e4032059034070f80e854003045581c03a5851481a5990b81c1d60120b14014001d03203d000d1031040603408a8202d80c0208011040030400030b42c0c0c3c015038840700c0484a007507004507041005080c98548001c50008601c1681c001d403003d4040b50b5000540014a140701e490102c54060044546040001808601c4046c0ba2104254140083c9240005000b4060780741c0c0701c0c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 613057140 1250 613055890 613055939
    0x61103030415020904020d020d0f0513020306061c050f0703061a06090d08161b060212070803090703080a03140105011e1803020a0b07030e01180303081f080102090307 73
    0x20080d42c108260340181112000070300058105010017003100300700e03040484036008207502c465404062025920034658000e0440000780045150342e004250303506801031110b40942d403002c9404408180038103020800680c0304044403020038200c204540c592241d807100710392203820060380550304100900a869001e5000c0e01050404c545081040501c5004c20801d44080c40700b002040c0500102905003080103005d282540d40081c80d044500005100d9603101104540011b200e100c0c0d041e80300001c4420458101900d19103a483d10a1a54208809940000d080c4070300012203402c0690550030440e0111103002d86101c80f0780e61000191150701c01d40003252504040300508288542c002c00d078841410b00040d202036092078603640440c910030001d41001105a20100d690800c0551004d589034941000b0f1912110803a0b81124084004a99010007414054110700003a407008581c00f48844094610380301001066a41c08054000e5000340c034260f0090240040c089000715010713a451100426521 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 613058390 1250 613057140 613057163
    0x5190f0c08031803030106020a02180f010b130e0103060b183601020408030c06090d0503010e070c060504060b0a0b04030804090203090f0106150906030902090426030901060611030304 80
    0x1034070550154001062101c05030b1058445809924040010318003a2803da00144580c06aa004000c0100540c10400c00b130107001d54100044403844860380b0341100c0b0041c00345901c4841c20fa41101c2c44c401e843d0820007500490780000000d0001680100c10009400c1e03a04256050980074a600d001100301c442e00390301d04100c070484441a000404000f0b10b0b40550042c1c2407264036844915099a000e41d1000610383d00100d100c4203003040c288580c0303800151000003070402104000340a48103000520900c3c00c0540d1440c00130f41803030300074080c8100c041c0e0f106e0340801c481c3c0307402c1c0740041c0100b4004d404513015415401000c00c0e11140d48040328192600413140794240392802804c4400b0354001040f03507405004042c030150191009008a074080c3c0540741c80042c003168580300080501d04560701000c10181442040005601d4158080360440c0e089240b003035000204ea040300d000c84a96502080c0ea03003600004220001406611050603035030b45666600026801810051752800141d50141c004005071303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 613059640 1250 613058390 613058393
    0x90c03140d0e060d0b120706090b0414101101021c0f06060503060d02040b06070b010303020d030204150305060a0f080c100e0a14190e07021c0215060a090c05190f0c 72
    0x100084c1c01440f00741c0002013501442d05010844c0c00307080040e450b0701517203d1074091102c6a00042c0d03d40180810100e020304041c90300040782d919400c0c0c594035070301400d206180250440c1c41000c2080610100000965a0399107810503141c1200d0100701c1030400e646045c40100701401d0350301510f001c0355069516103041d41c5441080000d813100022040368030659800019159458080c054050070b0700800f40d50880b5851401c0207070030100c6152610082510422080c400d82c1c20042c004042d121031440c001840b6507518001c01eaa54419802c1a4039610242c0400a4010300c009111a03940c00207031154030741028bc0e020191052060403c225901609103a000d215032030b050541081400c070000c0c42d000007030b144059203018041c03407900000b0104484a00300519940c0402c2001c5000311440d902621100b00400020345a035800c0302e000c06442e1145010503039940e502403100026040703030001000030000d60740d07019000b41d200ea840940c0750140b410002007400c4c0206203540031900740d40c440204d1184113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 613060890 1250 613059640 613059649
    0x7200f0102060618060301090209130605060a0b0703030e1e100e0102071e03090e13060e121c11040902070312050915041b0f0f0909050c060a0c06090c03140d0e 70
    0x1800c0700c0d0150350f2080048d0240c2e0f20f1030303406401440d0a200d0411310704001c0c24841305845005001e240034002c6410300700300d230840302000c84401c0c541602d030010703590200d6450142032400440c0381e0918010081444c81211001081303284007410701d440100310f002e140b002502c2c20b07406045070241c0041000080c004500c5102000e4180c881d21a241000c0080d4455550070b1404100751506001107040c00700c2001045120b104d500c20150408005068150801030f00e84100e100302030070104c02d002d2031081010100429040380749009640ca049546843c1c8070f99014000703420055065001883d00c07440407500c01c21501c40c45005444032000b510760044400740315130070014043e10455514403040c413407101c5000154401c10190400720540c07900e544c42c0a00c075a040101039002014039601d860200d50018400007020552000151620780e00d440b0f0b4039000343d40403111510003400f82404d140c0c3c003e04200c0007018032000e4078811300285017148030740b201c415589d171490314442e4003003090034038244100d142 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 613062140 1250 613060890 613060939
    0x6020106091407050c071d66220617060d2003070611060f041a070f1211030402040f0b030304170c040506012307200f01020606 56
    0x1000c2c2101e0071140d48400a03410407585030000da8158507108188076290340904100041d642c1000308810085407144124038501c090a031110400c1caa5980044000101c814103409020792001039081d200582c60324523210ba075002d40200c52284040040d0100a5020341c603040090300c0055840340b40d0340c4078110404101f07602c0680a5980940c4003e01480055641d144480c00d181700405d510041c21042c3c0281440d00246d904200c003844000c0001c421080d400149107503228050003030034034141c3c031142009c0150030010007184844990100070080e2085c0c00a038248198901c0da518600c09001c207001c440c0c00c0ba00c080300d0703c041c00703a800c101060140c40c2c0b46d002803260300703c0e61000041c40c2c010307200040e18560180e4030400d41070039009080c4141c010240010500703140306641c1484a0315152000a051040c5605483d9030301101004040000c83ca4400f559002d80d4012190705000c12a80a400c0084680c401480d1241d60300e004915200d502c080f032400d019200280c01d5503c08088030040070004c12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 613063390 1250 613062140 613062157
    0x30d031401210f110402030711010b06030712020702040f050403050a020c0603041a0711031305010e06031005060307050705100506090a09050d0f02030d0c0302070213090b0a020c03071703010602010609140705 91
    0x9081c0f510130849540c841c40114083c209580f156029280c2d64080c0a0941d1072103071915200345030a02c20895904d4002090540603450103600680d200490b2000500030400c510b031440c0141c5c5400304010070542c110000f040c1d1805140c0881d911090101d0030490345100480d070007000c0c10091240600e28860900c01d15401a0303050400e40d07910984c444025107036400545480081003c000d10410403035800010052030014141d403441e24500d0030450244541003140f041e40c1c0210000000911414881d00c1500d94896101d420358401e5110411a040030b040140c45013031240c1882008506244a1032040f40750090303101c1c010380032004003644152001221000c58034150b000401c90b02507890143d01c075600e80481c140d100181c55842d0fa00521007181070452000c000e01d484c1030810301c0402c0c030704850158840c1a001016a42d021a80c0030385055001c2d6143c020104101040c01ea05902c2e01e0401640c16662568002c101880c3e8803003042c2d087d600707030079203900c02000e8000102d88218800c0e00200440c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 613064640 1250 613063390 613063403
    0xf05120f0c101b051f020301080a0f020109030c080a030e010f08060f030309090109051b0705061f0503030c0106080c04061d060d080a0f0f0302030f150a05030d031401210f 75
    0x7500c44881d04000c0803c488040780e15402c400020b008180c6013610903c004007108904600f5581041f00c0c807070b0340d60031032400078041141850551046a1082104034003550f400456180c02c50340c1d443c40700b540d8100300c1104402040e92090144895481050701ca02460255642c40288d0b4482c0d5050010074101d0307000c4560107001c208092900b0783c841200250080c00c060b2800640ea01e88802c00140d156041d0403a084488001c011600202c3d074009141500140c5042c1c10000c994141c21902c908800070b903209540500000c45c04180c03021041d4404070444a00000345d98400e4401401c1008640c00c0c1c0c040c107a15941c041d00d2401d0b0180078481001c1e840b4502420802c2c18082d19182c90496130007030101e4400081150b400910a5a0710500b44000c0c035401d800d0a50a509111480942e5914001c0040402181c0000c49a005550311642c000c002c1034060250341c00400482d4005000c2c207820030b101418180304ea800000c03043d89500304060310740c411288045041c00b180d070b220505001485011f5440 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 613065890 1250 613064640 613064657
    0x1e0a05030a09170a0512070905010f2106030f0c05220b03032a1c17131502130807050108040212150c0d240909020103020f040f05120f0c10 61
    0x360841c0200802c0410001d4072500c0d21248003121ba1881400001c3c00c070000c03c4070f0f070041000030766041003802e030040540d402c18924a1012500003603500820400700c1c1002d6040c02c0f0b00005210307001144d0800c0f01d0013051100280e6444006005915000d5400d45203c04000b1882c10001c0720560301c50214000f0080640e17240650714200e6205500050821405018981e41032888040040010f00811050038a0020071896100400303420b8010000c0000e030302408000010f016003040056490707a0b654820300c0240c00c01701c1c0c80480f0000f5000113801e214048108500411800c500007041d0301180c005030740c0c40104e80d440b5400e102065041c10042c00d024442da540c0c440721b0007131803d031062081950b1a07013280c41c2e00d13603242c1400c25240340e040303040d18801c440d16035000303100d014071142d04c251a1804000b1803005001d1004070001d20580c481d51303608250110f00815905211660f09044610458054550004941d80c060701c9000c0407560790b80c04d60014140300d81600b01002c0340500011503003407880300e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 613067140 1250 613065890 613065923
    0xe01021c02070e0405060709061d0103110c1c12060308090d0c0b0403080d0b1008161107140a05060a0801030f02130219030e0f070512211e0a05030a09 66
    0x9043c10705881c111096000901000743c065030240c40e4070010061031803e02c4e25140c00c50040e8104800e40801d00741003540310001c00441e00059000c88805180300f02c110754051203407009003591071020140c004005010080700c0109854a07000b00700549070003006103464464803004016002e61059412103010b1400f00d0001609001c50340540f00450085d00807a43d02e9413800110400c03038868103500c03841000025030140d5026444605035a100040f100720070030380f6880c01c1080d5112408031050504600c1045c0f00410325400b10b032100c0350b03240310a86080004580390b1042241502601200b000060344e03c0c001000440c0c003164031098060300180c01741000001c400100006c0e071b8041d10b01c058028800c100140400caa2501c1031600910550014003560242d006203161035188034400c1900c2a00c2d03206150303038509001c0c08840318945007942528009100c1c142d603003e00f9040302c20380d210800200d8655440e60300046003115202d20300755172154916034500442e1001445100010303503404407603210090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 613068390 1250 613067140 613067159
    0x50a230a0801091b0e06150d1a0f040c081603140a0b0a0801051003061d01140414010b1f030f050705040320090613110307050d0c0e01021c0207 63
    0xa003440754004900003040d804c020142050b950900541d0141ca41410056101002c1c02140c1091003110400100c8407090f01c5014203014250325100c40c140b801c28504086074164003948001201910000020b292600800044a140390303014008208490000744002c02c0700c00d02c806e0b0680c198100042d14800300c100300031450700101e031010f42607652008141d09500e0080c0d005401070030003100900c0607103001c820700c0c02c04a00e50305c0000d102035243c140150040c1c00e01c10541001240910081029801500b1000e600344400c0e07505aa80c01031020443c1c40003a0b041c058078030364038005070010b015543c01c5801390050b2000f080c588010142e4032090144401410300074940148400c0ea585503c1d9403e50900340c0d42c01110f40030042a40c1c400180c4019a900c40c0131420f640001e080711000c55401c2e214013410060800e1950701444200c00008014035190440003500102c09487c2c000c0103a031131042c0055480c040480d00301800360707000580344403803144810768890071418148195800c1c50707611440c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 613069640 1250 613068390 613068409
    0x306120a050a12030b04060305101130100302090712090605090616020a02031b12030a03022713050a110316030e0601060801031b1d07030510050a23 65
    0x4803103450410f007111403415454003880d01c1030942207604000e01e51460760703500d540f5000660341101e0030742c86242c8101c2002091055441208503103141060300e480d20103e440f9010300410366454141100b0700450741c0c9120541c0203800340c2e9805410303d00d40d0341f46e00d101581c4000d401286c48207590b0321950013200090440c01000c0c05403503400014515400c2081c60100b00b42480c40b4408110340c84203812502507030b40081d500c0c900000c0c07082042507004503000452a03060403080b070203445210025203000d0040d8140c2c001d01448218041000101e800b0f541081079400e0300d1a0096402051039001469172142030380640d0700301c00031580000c0c083c50983c501e00c8a0380c000710380c801d03508031031295898001c5405006203c400208800038050960400801a03c0c0f0700781030102502c000310321300c5001c8142c11804c05650182040c00b4200c054a104030400c034402c00411103912001904082c08500c2040000000d0000c2c1d8100501c1d202aa07801c20381d0910260f003044d0b10380703d00e42090201010003070302d0321106c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 613070890 1250 613069640 613069643
    0x2802071a0a0e06010e091903080106080606070312050907051503010906080309060403060905340f1202010c02180f0f0105030d050415030b060f040509011203050306120a050a 76
    0x80c24031100000c001000c0d1800600c100107503420400e00a001d060301180c01419114281300041c020340791000090710b40264058844050108080080300717043d0018109412200569251080d030343e40c0d64240b080c58015054010082889649008900c8079a50407244d0310400341e208442c1c2c1c032a80c500c000749140510b2039000c0c020581c004010300603510a4001c000280079a14001e510b00b031850000f04100e40718620015241c9a542c001301801c10501f404500201c440d0f11031101c0c038403c20b50300b0764007002e079030f030122811204c0300a0b0000031403070300e9507034940d04440680400c601e407400e541c1c0054541d02041c00d002c9902208218203a0704803000e000595024850b055407420003480e0442030310f00207090681200d40320758000a4000442d42e40241200d003074561018107052030104001d001e031b0240140c241c030140d000f6000716095042202e40300c003400848100f203580000030790340d46d049900c042a2038500030700002c50800000b4114108010303404050b0b02c4000481c6e1007004261101030620560080 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 613072140 1250 613070890 613070903
    0xc0703030f0c170606040e130804091415040605010f050c01020c010501030524040203060c220803340f0f1205070c060e090a05060d020301020706090b010e010b03280207 74
    0x2104802c04643c403800c2e07000009a98641c41e1900305a0880801000142000503084600c103403001000701e4a42076800412003803009004c00032004d000c1003001c030001c5826081341c00a108c080001d03440c0c42d000b5082101d030b06031035105028011407030444145c4c1c0304000001c4603640802070480024800d1043c3c50083d402039001c0c2170008600c4005240300e0042c3d40d11060300501c2d0500340009a0340c0422030a41020901c5802030741c1b04090f4100f1624503101a030a007607000781124001401100100003424004c505012088081d138814032400f0455004000c0752003802882d05040c00000d41303100808403041d004402d03c00d1094030594607000c0c940c9180c0d155000054020590000300501e08040c5000f0700301d24140401c440c0510390119945060003841161100d45910214805842c0e9043c002c0b0120b0b0098000e40d643c90040c10150054140083c08942102110000040c48076414208070306a070741e602c00d0300d40b9684811100411030151a8208a04039100c10701c21001c0f141c8a10041003494841e80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 613073390 1250 613072140 613072157
    0x20d02090d06050a0b0613260604050f0d030606020a020d081606020405040b040204050f090612030706090b150102030a0c030e09011e0603020f0d1d0607050409061d0c0703030f0c 78
    0x2c04403c160307840d003017850b8007820050015503070303e0000c0442041034a5099060460380b540030728841e4650800d4805014050007010140800c1c481c000c2010850380d0480d07000c4403002088540c0807421610207100b0340b001078020807440ca0040c9064005004024082c00c45c903401c2c101c4442c03c2703c0d190401000c00316a0316600040400403400c2c60300482261034812101142410310f4171002c2030002440d080e5072b9106420030704c00109903640c0d0347c81a011113a48407085a88402d00c502d029070050050110980b2142840c0c0009128075500150200d51400c2c1130340514189000501e0a80d849654400102e0500000c41d07201b0a20340c0343d44c107000d4000e048c440d14880e00300c0c0c07213120010410000c4e9007021003010f004124010310841c4000031258420002c00c8005480003a602d4904c81022078a4040c42c1640104028010034a03880701c0a8001d4030441c4c02c040204980c0c0f000401c090820701d96001320454089000a82d108601c0700c0900850b0b40a4240402e1404080f80703200b0444e044641c05801080014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 613074640 1250 613073390 613073401
    0x7060c02031b2103310501060509010f06182301080901140105120709110703020d08060d08090f030d1206120209040206070f0803040f290604020d02090d0605 69
    0x46810b41030450301c90090f0002c052400c1044011181010701001c040d200000401d802d61000c0005030028045580d4882841c400100100c3c00d01c000414107803190342c2410b40205042ca000300c2811b048a0580d0b904005051070144207840e082c02c007552266140148071070014660900d1442d28000020b20480964148240360000d4542c8a0141540721140e14040c58802040b1001100c00d0565408a45182e00444240442840d007015a003003901d0b95400c00702240d1804a081002d0300041e442a0280c0d000c019171007208a88056044691a50002c8040e0001c070220344007200400300b42c000540f00c08440740b070700c1e00400d1030405000680000249500d51204c010885403040002500050160004100c125000200130900240010344a8807001804c0d608112109201000386907124080c1a201c0c9000d05100b0505500800191220400c001c00c1d00701011240c40b2003030744014003024060f01c070707260702003404000d403c004100425507508000c0781425a90308030702907070b0300c522034803021400d403401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 613075890 1250 613074640 613074667
    0x2010e1305010f171b0f0a18090618030206040803071106040f03140a1e0203090a08030d0b040b01080a0b1c050601090f0204030f03030c0c060c110114060d1103010207060c0203 77
    0x30021029198002a44d40912407500350f02c0c5c0442d0800881d500e00d02e0809041c00200c01e01c0c09580011150000c604080c00400040d800201c5a9801034030b040050041103c4a00000381814500800580200c00010009944d40001d59080103080c50b000034209480000545842420f4030151202007842c0b84290816601c2070307542c2d01144c9800d40d940e082014034000940301102e40541034000c00040541109420f10800c181e601c40c00004108055036540c5e59185a10b80c0e00c410403e42109090010041185c10b050060043c0c00b013045e901c840940d0785282c0528014246080341640c400508214814040d100855400b84540114040e03c0c9030b516007074643d011500702c005900c01890040c0001c001080062540200c01c680500300418440d20340d107403c07140a03113500c070014050b51402c198010859480280130140c150b00318000c00c03e210b22904020340c418402c07105241d000000c5a6860001414005001c200754409400982018101d540e8141902c0c1d83c2501c50005070303c04181064079a11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 613077140 1250 613075890 613075919
    0x206031810110901080903090a17010e010c0e041a1306051801060903081e04090f180206030604021b03040801050402090106091d04110a18060b130302010e1305010f 72
    0x40090200803801c91101030701007030f0081c000d0042c10720640c1d800064241c0c0c01801228030343d100007889000641d8070749074203c8550915001e6000d09601c3c00354101051401486035400d00c4055480700c0c0c40c46800305082101030440c404503825060700001d18602161240a00c4400b2480d1450000c9601400c090511400c48151361a40300081c600c0d0004020850f00710031940300350380e0040d581641d20302040c6986060040c000c040c61880001c001400243c002c013071b030301c01c02c3c8013502207200340300101a0b4607150b01205040c120296102d002000481c50307629150740100108020540c10503241c54610340b085040d034100f5444001c86944602c1007004620b0308020aa001d401c150400d00c0000d400c2401c1c04e40610f020301c055030000103100700403038240500c102040700043c000806c200201c2d41c9520b8440119070115050038482418480c0c041042e8003010140c1d2500d41080b8960101245541c00445100c1c0c0c100712040d801a203107210341400342a150040c0c602801180400b0003882d49000c1c021041101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 613078390 1250 613077140 613077163
    0x2210601091a220c1106040821060307060f030b0402030910050108150a3812010902060f180d061406010c050c12070f060815030d09090e030702060318 66
    0x841e400d0300783c000403220764104038012203415000950210142e0b01035a40e0840303002c80000600c124820442040f2008005100741c5001d0755402080c00c0d942c0245052425050340c002d079060700040c0c814000248926040444c1c003209242c0030070740c1c0214902080c101c0e801501c040d81260410100d2004070540f80c09000c0c0180f035404000c0281c04000007030003503041c070302901c0104190b1701d030f00c00a8400403a1120b201589650300d02d0743c0885214010001402b81d20740600540150002300303001c510301006202d454185a0044c200c45d2416101303081500c3d0a500100c50741610114941112500742c9601004030803491040b01e001030700d000104d1019a000d1401002c3c14100015008401e0004201045203404d044090f070b803040184e00481503007420b00d91180c01c884248900070a0008009500481c00c2c3d000d00592469403641040900034103489a240a0042d00811109002000020700c44d40c800011040110b00f52030070202141d001880962040d80d11040ea0b0720100451030800720706108040448 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 613079640 1250 613078390 613078399
    0x504060512060a09020a0201020309010c080c220f180b0f06040302060306010309050d0e011404060503011a070b011d060301270201090f0815010605030601080402210601091a 76
    0x528021004000707105080081c401c1040c850003207042a02c800701c1e00310103860020000e5454640c5020024003d40089072800341035030905c400080d000b80030b4840716004194102c0344614040e038107200c007180900380704046402c00c0e04208001610140c00150070001e81142c806200d0a0650038001009403030b1200b0320036104040480000c3c2044c1c0c2c44500b102c0c101c1e0350580d13040c1c2d280d0340e98500613802803a840300060414000c07a20b22407445644005a5040200240c0352803058000c02d03954103940b030281e0701861001c0340f002c0005104c50002034031000c03080640305030740918100c4c195031466a0014280e20201c11080148070a42045e549140c000754010415002002041d03808221104407804002804007807070340700410802564429103040d03019041d05600e01482c180d480341a955507040e141100b030f4100c0c80c407100205065201e9400c07617028490580d48c0e80099140c5d0303002c111448840c10410408050300e190100003c840a00c1014020b10030f00600040602d501c51000d08a1910511581e214 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 613080890 1250 613079640 613079647
    0x5071e05030d080403031508031e13060809070b0c0c090106050c1b010c061d19050604170d1506021002160809180f040516030317090115030302011b05 66
    0x15280000c0800c5900c2d11498a8400c9807501e080c19802000300c1e40800089104540000ca0b0900c400802081c9440e600c49038000480792040301410f01c1e0040c446655984850b04904010081c429907120360049515010344841741e40e01c2c1360b1040241c3c0503610a2030300c0d030070002d501001c1c1c1c644068a140104400d090680c5012020031050741c0b2203047c0d1070b0050703000c0d00e41d501a8040364070a8420005a9600c100304105074244070980c800a184402c110303103041d104444424180b00c030404a40300b0907680c048010901900c69a0f03d018a8900028400c03807240c005200c1252004194018004665920301c0e1031200d0504040001b070130800c0d502c100c125070b640100501c0034800c407503c0202c60810b42104100d600c2c1c0841d400000c1c0c0807411004406650007084080c0310f003803007500103072602840c0310300c045400d00c40031030140300800c0d1140d100240114040c41310100d02c064484420b9984001170000000e10b950001c40049800c040c9038100303500507903450052405c0b490324400c0460300601c4608040f0f04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 613082140 1250 613080890 613080899
    0x81b0406050607120f051902010e010c03092103020918090706090803040e1003020a0f06110c15070218090d0201061a07020d030c0f0303020705160803161e05071e 71
    0x8500070071300d18a01040318015191410b14410000e480c05001450380040902ca2980002030281540d00c0c0c00554039440d2501808459020744604255540e000720b5141c19444041403210b00300c0b8402015205042e020400403100d075032803040e14000c04d1101c19a0388441d00780a540c0328644000c1d90071110074031076010b00920016400109507811111202d0f201c0f200c40d43c1c0c0000303442c4410311076440250025039a00703021032608a1254507109460148c0c1d158101c21030084410b50b50b9010490885401c015082107800004c14140d0080201c40d001030140b0031040307100070a60103030300c01c1211038007503641006920303421442d820700900008000c40c01c284100c404580c15503442610070030380000c3c4224041440c80b000c15010781c1030b0280803500b101080d00c62100b9400c025000c1e44c02190300304d03624040c24081c2945003015a88803001e8485090046040001154480c0c1c0303d448051030603110740b018880c0c4022440000c052520020b41310390043d0030340350303c3c01c0740360b03070030365a800e2120229a40084002e02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 613083390 1250 613082140 613082153
    0x50c0301061e051803120309012009010e040c1715031b10050a0207081504030f05070b0a1509060305010f0e070311040c05120403110d020a030c0b0907081b0406050607 73
    0x300401311402140c0096203960000030b1401c8079440404200c00004010044083c5040d407001e0700d50030792102601545075130282c0ca0a964032510b04118082071542c04d210b001401c003607104c03000784402401c084015030b40d520500c8000800c03c90701e100d0314440412100c001400e06005004103810340411904510070628005040441d142c10417904119000c1241c1c80b1b00f40c401c0055030f00821544059070003450f8150300040c2030350300407603050b004a4880101c5c014014450001c07204440d41040380310000e038807031610440141550b417038406040703010a40003085414252140200841c4110300001d41c0b280c0c0034454406658040304450155005004104082440204600c6a4103001c0b1400283c20a000109546a01401d4241041034451504001c101900602c4600001300120215000c94011210803a500c1030382d1440200042d00401201002500d0010b040c0c4c0c12911034015030b0080c940b10b0500364540000705000300100e0301040003001032428613215907006410181c0328685891003948500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 613084640 1250 613083390 613083397
    0x1090b010c0507091a060705150f011413020c120d0609090f0b0a0615020f06180a170405030a1a0603010209060a05030a060e01081b0406031122050c0301061e05 70
    0xa80c0161104024801710300c1c1070b0400c06403042c3c001e080c5500e418583c10250380e0f86000d5030741071000075480c5021034080c80c62100010f0480340032070214844500f901060041401b6140720f0555002d800703208840300c0080c03d210a010042445243c00e80742d8501d4400401590110340c082203c0c2494842c8010120714400b090203626504204075084a45421010340c00428069200c04180c0c0c15026600580d06d90101d8510400c0c00b80e50b04444c0030b5200c0d03a106005628003d01103005540c06501100d00041361070030303044442e504a002d55418941c1d960b0129003044c4030024100c070703803076016064040001180034a0540016041d0000c6003043d10203008110580b03d07401c07000c2c042c0140400003a12078103564114030b0141404c40e030701e800b40d56580e691480c0d5030405e00b5078044840d48682c4101109082074490881200c1e08005442d510a01071004d01100518094400c1450340070f420100d01121000c0c041c0700e00980c0c191a1455a9626120004028107007030084101d9410180f201400016841400d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 613085890 1250 613084640 613084649
    0x60509030601091824020f0403031e020c0d0302030c010e010504031103071121010f0b040e120304020d260a0801051c060f02040816050a0b070c15030b040f0501090b010c0507 76
    0x1604a884100c0c0c42d100e450001780417414445a00001d008109104c101b0090000c40c0d20a85550307000980034402006280340c15426400141d1100c500c0321603a181420340d6400043c000e00580389003582d180307103450a40b1248080040681e440d0400d000c101039001d507400200c24804400340d03080402a6540303e03120036003c00d013103104a80c0d108250700401700112603004a03040e014000c01c4100b40c2c5041c05805014044100d522803482c2078001d40c0107a0740400c15450640d89a00642d245555503400c0019080c0d07194070580780013a20000c1e001420010108481c01c2907112003406483e85c10f8541c0007000c20005030403150044070864814213814125030100c0c400558800c01c0420700300f90400715100207010b00e42c4080064840c0300f110000c503140041d0b40c0303026035009130383c9002030b15100d14a010040c45050030040c040b41900d6001c0141440c0c80c56441407040c924039000c50326603040e40c0014152400000d00c11362040d0340d80010840c11040c0d205a200c2800c0032300f0603180150071603d446032203400c607108 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 613087140 1250 613085890 613085903
    0xb10171605190b07030c1b060203070b25080103020a09020405060319110f0408010e1c080601180b0309061807030609110405040b072c0d14070605090306010918 70
    0x18100002802600c02c05040780140203a226040740c1001480e0302c1c0f03284004d4490304030010b02c0c41caa02c8200c10101040ea000c640095150800d542d80b500d0f50301d24001c0080400c055071404000001e4130354240f07003240c0d0003144d4611760254150300404c141100340754012001d0920412003000540c440400382c0f0380c0036000503201e1403440444459030025100c008820503c41e0b000152002e00d0504c0c860241043d9250940204a029002c0503141c1c1c0d1200c0c60541c240c008081c90210040e039911403220707207601280616001412074116116841c150300d140d0490741400b140441005441c43d03080220b10b44c0040030301c1503803c451140482883d200c4649010107410151a11120018001401d8144d03240040180c02044a031416003052416244156601000500003180001d05182c1c07000f05d070200011049220280030748901c0c1080300d400d110f58004c07980c001024a60201442041c0079020041c415074135115518202101017506012058009512207460a18114460510962180c0b8002d60111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 613088390 1250 613087140 613087159
    0x230402090601180603230108120d1407050c0105160806010c05030c060109020c06010801090809090a0921180b07030509030a06090501020a0f05180105160b10171605 72
    0x3030040301d242c07001c07803030f40d00070000201000241983c0c5540211410a40003610621200c2070340f140720300100c3c0a100381c0c1c0c0140d01c080862040c840304500244404820380b80000748054401040800c07001c0c08a8440c0042100414001c071152020300403154040f03511201c0140c11051004090060301c4068031260421500c40100e504111040044500c00851a411609690b80d202c9400000e940030071003200c1c1c10b0040350000078043c101402985036040c0c0c452a103a01b020925802d1192090380103007191012a107599680010501124415070b0000c010842c2410802d8032080150540b4840503450703da24200b44000c0100510340419a00c0003941868480c2c0e0390003118000078500395000d10050215031402580c501006015401002010345d50b4680d41080410903100750f17403d010319103c8c0031701070000311910f075600d42c401c0c0007c3c0303c083c000c04004600001207442e90f07840400c0440ba010320b04040e1007418001c659107089414039454150703000300104c03400609d400c0007141461180c64094540007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 613089640 1250 613088390 613088401
    0x20d03150830040b09060d060e13120f0813020f03030a020f0606120307060e210705060609060d06091e060b0901060906090b070602070c03140123040209 67
    0x552004000d140c1d0204652081901440d00e00207007560003076641140300340100307032003400c491a0142c400700c3d5007041d0032900300302c050403c0c445940d02c600c020300c600e15034402012486149410086000b542c000150317071080d414900c0c168220400040d0010240000310100300d42060384860b02c02c0e806a0111f17204001c4001174408102510b00b0605001d07414000801d1941c1015800584488071b4009c0e502280c1d400d45500003448041454801680200c0c0c10401c000401b25074907412021000c82018101ea0b0107900c003400b42243d1100740d841c805124180020040140701081007050b800c01802c6800c00d80d00e0030301100040c000002c90000070009900d07214090701b8000f41c800b10072201c560800b0030410b10485880d000009140c42c002c0c1d14401c190540c00890410311500201e03041e48c525859242a450500c0d0380d007581904041c00848070260208101000108000903000003944158a5080032104c2242114251091010151180304284070100c2d0b6021900b0b65294010341c0540d941c210a4580 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 613090890 1250 613089640 613089671
    0xa0212040f0512030f160c150903080c07080304060914090105010e09100504150302041a101b0204020a0f080c091f1107031112030705030d020f1e0406110d020d03 71
    0x21184ca4101c0d4410104215469903400281c6d0742c0040d1180e4904003519803603040c14140c002d41c074100c03140007822181041c8005170b2640c005110702082441219240d035500d2000601e1a0702c2500154000ac0a10104100042540c10415600c0c2400ca8a01103e0b40c10800024010b111581000d440f820700000800d41d0641c0804020001c0c0502900622040e00703c18040c1003005203c0c0b1080b03015624003196845004141010b041207080003e11840703a0f0200d07444201ca20b405480f00b020003141c0400e04c00300050f07032544001c142001d425140c8204a540c00c2001a103048402007070400080002c003c9840e05a1302d015107113240c0208440c07440545009a0310031201d413114082c881405118505e804801d00590050340c08048000300c40101242d01040030032030b2a8000c032480107285500c1480030300c10184482d0050414040044101c0e4100070254007808001c1d160f000c44412484cd00060511445501c00c00d444140e005980c0100301c201d840c1c0d1002507a40c12030780000810556034450b500c191054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 613092140 1250 613090890 613090897
    0x4030c030915030b100201050405060f070215010905100501050c0c0603220c080c030c03100b03030f0a1713020112111902010605040b0103140408031003170a0212040f051203 76
    0x107601c41d0052802d241c038002400409442078407030b109003082c09001e50b0507441401a14421a1321001901d11521400008000f1134000f5080c442507000710741e040d00340d11091031200c0f4000e110341d42c0302191b10300b0304081c6a03800e07901c61f030402030410070300700410300500307100050001c440d10081c0d03459a601e0b650269a62504440690801d00c1900c04102e41c81c01d200501da05441a24048026900d03801251410141d030780205141582c0c1507000016a0700c0011426840800c002d04041c2c280d0703260151100703040303419a10010510000c28482890056803030038203010381d0340c40368404600740c0c0c01c408144c0019241040c4a84005403094554082c56081c0c583c10080d90440d04442540c0c10038030385001d402030301070201c0307001e000d024514042070604598401c2c0a0700350124440d182045454070f442d1076015496200178828090200423301c0000001c5649022014401a42029948440b134020000342012004a4401c47c501c1003444203100c00c501c010307a0b150407102e04030f0b0702909040c03081c07071301c18110302 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 613093390 1250 613092140 613092149
    0x60d02030f0a14011e0905090c010908010203100b070804030b070215010503030a0c0b09100e01020405010e060f03060112150f150c03080112031e270e04060504060e010c0509210604030c0309 83
    0x14200020710001640014a903007009602f40c84c0c204030386031100c800b02c0c200d010440e4100fa191501103410003680c82d6200003040711600600d0b0300e91811b40c8984a03c0c03070005003500c507540103a010074130400c800c80603080380901400c01200a58a0039108172001064003020041c00703816175200d4404940b034000100444030010030f8000040c8911030042c020745000b90418881e0034046002d03107901f01c00500e401811945802c000c0d05040f070842d02c1d00d000441382c0440c9a88a098400e60b0307a03913044080d1814200b6200100641c10b481000141000c809503010707541c0080c81c3d0203101d1058203920000350028030751030668130240300083d040c80850a04032417086070030a00480d41d002c08a80084440c1e40070030070006a40c3c1c815021507041ca4032100c034130101c000502c03c40140c85e1104020400241d4240c1010340c0050240e01e01165007070700148000e007100c4150300c2c204082040081c007602681400061144c0c442610700c88001100541244280c494100400080801c0380c080c03a82c00815002e010010043d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 613094640 1250 613093390 613093409
    0x7110703390608100306140103060b04090f03140d02040f060e100f030b06040e0702070305010b12060f0403091703131203050a08090c060d02030f0a14011e 68
    0x580c0d40e41000504a80c81d901d54440c01c0510105504a503404100c95200c254440251021810314040c02190b00340d6000e0001d45495111100c00004190203004030894030900c041200c51a500d5403070071204880da8261114002c03420081ca8001142d040c484407100c890b010b003080008454110354012f41481001200c4050382c3c80400d000c0350001c0e10400c0202a50300540f10440442c1d40d0b0002c002c07407680000203074070003d0701c040ca01c0c40030640719400c510302103e80649400d060507113078000442c0840040b00d05c6070050348600d43c10020320409010b070b1848c0e4802500c0c0c0c0e980003015400c0c1d068403401c0081040600710f21002c0400e041600c50b0082c1c00007443d20307414410301c4200d0340c007000d9181d50000040c0f8070a1a000b030030100d45044443c200c145060b074162112450244188000d40d40804018929440b42c06140c00043d260344659004100c1c94441c0c000040c1c1c3c91602e1a004c9519040180480d0040c42c90052180c81d00359860001a0540ea01460402100301100d0034510a0088a8010a084 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 613095890 1250 613094640 613094653
    0x40f0b1012060f0321031806021225110109150c0f03151403120301030b25050910020c0a0f032003150924240a0605090112060b09090106050403080f030711 68
    0x103000308c0760b010b01500200310b80c0c604110780781c035030b0540c0902041003800d5080000c1005a24042c0e03008964001c3d0a0b54228008150100f0030b403039114815110220010b402515a6500d82c1c841d0b40c003604440c60303c402c82c201041019110170785003400030340e240203401445201c0d03448032106a50800101404000403001d0540da580c50b8500091000c1050f40c0220745020203a07926180d050040d0f0322038149440603902c0a0034220403000304156083c80c2d0420340154010300600c4415903c840002c0c0f00a88414848071100515614189490012094030164a400313400d000ca40181e0780402d00700f50000106044072002d498101c1340070709140300c02d44038155910101455040f00d60921358200d1103940802462001d800ca4525041d00c500c1220340c09a5000c40301040910131940a41d015010200040c500201105100a503503412030700c6541203080c4c0d00101103181c1c00c0901d850240a801750402d85440c40c00c00c2d2450761940380304e0040055040c003002d008800608075510034450388508a05600071a41d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 613097140 1250 613095890 613095893
    0x190920130204120c090504080306042a1e03090b0106200105091c0201051614120c030a200906090f10080403030e07030201020606040f0b1012060f03210318 68
    0x2850904200c080f00d4a131062003001404c12500c6c0300c0c16200d1900001410700c3c40da030720002c01c8000c180030000c90710254250324001c0300046140907580c000000f280c80301c4540044094208400700b56040101042600740034520000484503200c0c0c504680d124200070f0103003441c00c0013098250001c0e544004076903107044100a040e400018950f810301c404003840c6242b00081d02412030236103000701e4140d0803400a59141d4109188940c040080107100001420705003c000151006e0303002d000e59100c80c0110012003442801c81651107500d42c00c2d2040c40079000038501c01c17032044001c0e0054214491186801294100640d160212003421400c0c1c01004000d04041c3d070403014108140640d0181c0000e0301c9d010078001e50b00d00008101007504d030140c00a040c9603941c0002c000c00303409400c4004c0c2c9455190780d018192901d50b02d4102e4005038054980100c15900071040e003049a0a540c0300c0554813190071020008a54071800683d03031f42c003003c2000720a203104024164003411a1041c200050b032010681b110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 613098390 1250 613097140 613097159
    0x150915020f0d0306030b07080906070c2f090f01210602121303030b030318130e0105070504030b0906011802090102070f0902040302130b0315070207031a190920130204 73
    0x13000d681c41801404040d0b00e4242c001c035400d4034122001c200030761003480030891840c0210380c89210248180907440b03c074007180c1d0300d0103140000000809408d980142c51050b851406035045903110085c420003400942c90900c41d20710250f690703060070014040c858910800d02c0701c0790701240d100c0e200342c0c800e000c80e40c01c207062140100a403c9001703500003441c088001b4030900d008001c0f0b40f4000d1010b03408416000c205001c2001c030104100c42c040d98155148803034038402800307016040c400c107280d4455544586c594140080381410007845210250810001480074071280400401e40c454070600068881181074010f034034181c40e680204c440000c9800002030000419001882920310a17604002498400e908400030307110803601142d815040003080c0100003008200c15503016000d44111442d040d80da4681010a2292000e00f4041d00098030822100c501c00f051021006410090b041003918080c3d01d4424960700201c0c552582040301d001c51041035501d02c8000304080c46070070000c642d110b5440b002e00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 613099640 1250 613098390 613098401
    0x110703020d0b0115110304090c030b040e071a0a0c080d0e06090c010320070f0213020a050d27021201020c160302040c0804030c0f080c100c09150915020f0d03 69
    0x40d101c051283c055003204ca8416100300c0048041034008608080c2001d24900203400e000700740000f0075070303203042c1d54284d95900e00642d850850403801400c003081c04d0825030f40c0090301007a90620903c10030040c10002a50183e0458001d07078014043c0c03929030320348800030700c00f80403d45454075152041d6424400b43c0280410300c5007008809072010005454000500b1404801d40d03102d10b800810140840c2c0041040790144049140c40105292902e640c000c814208980140a000b03000480206031049507400910400701100c031038919461203003005080d501c1e003030201002c00a019000100100c1802c11094059544019400c0309840035803480081d100b0305042d240c40103074815810305068000d07850144c504c10780140c2d05640d5541c41d280103a140c480702d0a03d001800c8400700c1c0c041104e100d41080c01d0140400344270f44081e02007402070400300000c000c514290054030044139001c80d105082c9801c0114801116003070400700c0315420890400768204092401803042074001e2040e030224072a0b040d4071a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 613100890 1250 613099640 613099649
    0x60504110108100321020a020d05060a0b0a0b2a0f0303060a14030717210904050901050705091201060f15080901060f05010e241c020304020102030a110703020d0b01 72
    0x100400783d50380b00707000c04100d0100c2c400070b8071001c042c044503110000120001e0850403550b00440b11450025400300b4041e196000d020780b000d811134010b2200c00304890044c0b10003041d08454200945050641c20b00704c501c91100c5031a2011361010032800364401c02d4040741c801820f030406480000941d66003031612a441207443c0c51151044200100f00c0d00404200031034000c401800a16801c0d0520710084204079840052403014803840c01c0f002c440481c02803102c1c42200354040a03d445003500001c0c0000c1c0d0b03002419000442e4148420402025480010b903a41c101c8110740132030341c2c08818920303540104440c0d0003441c1e6090401c00701117070002c6050311180c5814415542c4100b1955000c000c54200c4d0202d000e12040d000d00014204150343c40340d041040f080c00c1c003d002a2216450103818401328910020141c0c040d040403e00c0a181d0041131080300c2c5014440400358610301e07050740000e4403886030165907020700050310f828480840382040448055940070f00010340c1e40f010703400c1410228000740709 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 613102140 1250 613100890 613100897
    0x20306130e0a050f03040e041211030a050406031d06130c1d06010f02060103020d02010c0812010834090c050d0f1b021507030c0c020a0902090a0501170f040f0605041101 74
    0x44c0c281840d40000813102103079080040d048080d1103a550b00d00144901100d0340c4104411301040c488051014801000a0030340303515090764641c58014081d007501c00002110824406102144003050fa0114490380d02c0b2841010421400406152140d08002160401601400900b041903807070409201c1480c0954800d072a10400c50303001141c00c9940303000034080203400c02c00d404444001035015144585031140f00d10180360a01c107009100241d1120242c1c41000c10f94006010402c0c004480c0c0d09650401010851042d9031801404d0b684101040c3c0344a041c580c01e80c0c170315070304801038030403000d440601c0341608040c05207511410203034028181c00d00950440c49250425080018000240020440003126020400c0d9803481e009500800340155580b051110080c43c20b00140d80c2c03003a0040c0604031141c40140c9592640050008200c11034001c281403140d070b001c88055102d0f882030900c6d8000a2080c44032116507441c68402601c00c485e80c0020000d82c182020302c070810036448c140004241c1c00ba40c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 613103390 1250 613102140 613102153
    0x2206030b0906040c061422090609020903030906070309030816020a0b03061c06150602070e010801020a020a080d0612140c010e0a291207030605030c01080109020306130e0a05 76
    0x300202e4851109071002010f1440305041000483d00031a61341c88180e042030145800c03c1d0803501100032000108441606c12030f0b68913410702080f10300d8031848002d003540740b03021410300300c0200c0420756078424038072000e1003801c020401c0da0805110780c4c1c003640515403141a003610f070042284002c1c801045c42804910502c040d02000c00d0441c042425a4030410f8002c00c06900c0c40d1444d410a01c0c01c002854007524126103480d5190501e003403440c0048020f19640c5c2c010000d903854890181001e0806800a0707840764010443c0200c51940001c144800c1034111203601d5403041c0950f01d0100505440d8010007408202c41418030600c0801459400046a0001501c1d80c034000c0000440b00b61680724070300c40e40101c1d04e40c014030289081109003011101c0c9a00c1b1042d107140c20f0000d0f141d042e00a113038860020100082040201e66050042200400041c0d004000c140c1e0700400291200d5014003e0304a41c1e0360120000341650f803003000c2105542c1c5071407400c00502c404541500d440e401c812030199510321420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 613104640 1250 613103390 613103401
    0x4090501110d0c1407060e0a05030f1b0601030c050907021606030c1d13180b10060f02070b1c090c0b1905040302030d08190609050f0604050f152206030b 67
    0x4011500c03226802100c03c0780340550a5880d200140f10001f022012881031503150300004c1c07c1080242811402c03028150746402d5100314404401a10b2264900290010001000040c1504001d0810b642c41100d0020040d5100c2c0d808a05d080300310484201c0f60540c1c000006001509944601c0310589651b403000e01c0a840480d648041d4130034442d615070001d00d00c1410580958241d03000c07c680f05008062940b40310082e0300c6905410100765014800454007510412440d60001850a81c4242038009005010319029840046000ba1050201c008114010008840401d68024103d2681c004085411541c5030140684581c02400030207800c00c103003491a40382d49004205440840754020020048490700c04c00c12036264501400c1d02c003045541d43c0042c0070032031b42e07402402c0182400c45000142403a06010310a4072603c09800c9038051031500040c4001503007942c2d4015030061045040800300103040003c11010981c3c50840d107030984441040c0003603c00f0a800c021300300d034012550580292280e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 613105890 1250 613104640 613104647
    0xc03010e01150c03051b030301031104200a120e100501060f0203040807090c090509160201052d0907050a0906050a0b160b2203110f010513020d0204090501110d0c 71
    0x601c022880031a2012050f040040c0c454030062902004083c0d40611400340d91880901e5500300783c004a4140391720b000b00e01e40b0360074140304400c0035850480d14455a0590154800164810840700c0d070100544404402000b5800d50411070403485c4880841d0030081c0400c51450040c1020b0040d0320016845620300741143d48000300756816254480041d08000349440f08000003051800b03400e905105410400054581e240a5010f100707202c800070600d86186c104200908403070b4020b0604104e400d01c484842141c0d00022000b401040308100544101c0c0c40d250413807440d14000e03912495101050000115113440242c104c2c0089030000c0e500d2851241d101c1c25501c6c500d00071045c1400014040600b1b40010443c070040c4250050b0311418203486e01c000d40d40801e03020b5100701009038081060781040b041c05c108200490030162070403400030000381c1081600b4180450502c0d001030b114402620a070802c1d50780b00e600030b1100c158440c0c0200010320400c002500c4a401050b80b50303040615107104050792501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 613107140 1250 613105890 613105919
    0x31314131e0e0f0303130308010501050a050d050403020a060518070b030903070818061813050115050702010e030a03090305070e19020f090904060609060b07080708070213050c03010e01 81
    0x1220100c0d000d0500c0031000c01d0009100c901e114001c0c612420b0380d4900680010300056001d241c1804048075079442c01e05020785113000c10b80c0510704000d0104003a48000c0d078000300381c0744102c2e4408004a0316441d281402c81c5400c18400d0054182441c00c0c0911911415900c00401214049001c5d04e4a1036510098444a0f000844810510f038204002200009803000300900050904040030b00a40c2c2c603803004118503405c1404003083c034541c0c2e883d010702a89040e10206035842d0307403e039040c4860760400303459005200d100700c2000140040402c5a2045a0103002c5000d0401006022141d01c64010705004000481d00e20041d180b50050703132001300d5a09142c420981c400d001d0100420001903544800c00000e5002c01c03003440044106101c4800c0550f5448101400307a8000e0f44081003150078406030004a41481d40040c9a1080400c00c00000036540c0742034800d0641c01a41d1181c0f0b4601c0341c00820550b02441414030350652400d0100141400040040c49c1a16060300006a0340c4c3c0e265043e8503034046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 613108390 1250 613107140 613107161
    0x130503070e06040c0c050d0918050603100b01020a0f050303061002190f2102010e0c0604180f0603020603090a060c03050105091803040803041715190b0303131413 71
    0x144a5000401ca420103801800c0e13145118a01140b41c4d508580351981081000009180040e841c014100240c00604030603480721030403844c1c200620f050120000b070351194032070380300d00030710703880d4042d12900b03a00a000c10031510b5000380001499030428604151a58422285a4480c1e000c54041d001480d100144200603500c401b40f90010000d06512140d44404442d101100c48008802130002c207510440b540d00036500050b000400c1003200000024205016100e805009510501003007200848402da10400699841c0000480f401d0381d003819005070100b500043c0d00041f0001c1440620200042d2600c0e00f5801540c007040b03901000d100031015107071f01703104c0c030b50b40064000081000c84503036400073324031168a882120700d041c0d6101080c500316006648004e0400710310b0000710400b803c0901000e600f281c00120204150b1510294200a0720004003000342c295503610481d0105032010000c40e03240300c944001c1180ca107542c81c00c006034880c5100020b14000c040e007151019900101e401621040c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 613109640 1250 613108390 613108409
    0x207060903080c0c06181002030a1d0f0a060203030a05060d0b070302030a0b03101d0307050d110c03010f0b0f0a080606010309081b061006210e0a120513050307 70
    0x551450316444030603041120f2840b5107001d014140c15240c1d40d0300d00107042d140c2e1171041114404106004102d10410743c00c0d03800056400c20403151a0045d0b00183e401d466461080422201c1408a000f09050700c01d0030401a800604039440402c082d40c002001e1803080c82c80a50901065a9850078000750011158000b021003094070041040c0c24040d03006554071041c0c40c80c00281001c8d030a800240340c14000f11510020540e02c0c5e44100452074003055030000c00b80200c0003035203844403039503030303995208584050442000b0700c0003914840120f0134041d10b21100001070090104c2600e800c4170b42e000f0000118058410590281003c41c10700342406807030304a40c0f00a020b05195a540c4c00150081d1001c400c00312101e0328104064071020801c14030041078103020900404080c0303491301d00080910302503040b0700d0600040b440a60f030004060340340044140244400400e011701c40850cc2440c00c081c241c4000d0410340c410100c079050940c410081c112840e02e104a5000c0c155640d018951540c0b5240100e01c0308 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 613110890 1250 613109640 613109657
    0xb07050c100b01021504212c010c0c0b04060306171c140d090204050f240d0b090a05070510080c09030f030409090201020d140702090406020c0102040303110607020706 73
    0x40c035042d440a0950441070054a03003070141d946224285400c2201c04503052040610f06c46203122605101e104442d0ba0381c20210250014015041200110b403c00c44250365404100300711241d1284220850595025014001850300c0f00b502c81c016800900844001a01d400310029101c514001c01200e0015040c0c0a090f400040420b2a00014058040f42c0e042c0002c10310340b02c92580d9694000c01d41003c0341c940004041d07207144100419103101900304241308820000b4021900305081605c0c0c1c2c007040d0105401500006000410791200c82218080d005d00c9203e0b0410210310703404030b011031046105d5015075035540d8441301000204d01c14009010001020f41c0c000451803a075241c010305400c1e41c0101207030501403040c03101e58079544c05600900d01282d00c41d002c1d2011960104406c15150301c280c2000242ca4007103994007142d601411102905c0750140d00e001c5410710045078111000080d000009568894032814054800c2d4050303801c110080c40781c800000d003901d2000c107102e01034408540d1400300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 613112140 1250 613110890 613110913
    0x31407140a080c040f0608100509040b070c060b120f0606090907050402090310050405210f03060607030903230f030903071206020405090403210b060a030e0a020303160b07050c 77
    0x28402c81c01071405000f001c00b04400328029503508820b00081c10b982d0341340207007460310b207007484400c8080741d102d98000d030000c60a01c400210f80b02c40c1d03e07510000c0c40c070340790b090b4200301d04110b4060042c49120750b4010285920840081d00080351450305030210004036505521000103000d640d80044801018507006801c0620035860030750000c1c1710410700242101c003a10490900e100071120705035004c940561294080b948201c40c10456100c043d00010344c007030f042c00254680c41d02140b0005000310310640c8009030040c2014014600f07400655003084a1100d81800000040c1c5c60603100802c9034a9880f41500b21810b4540010840d03040c814058040c200503440d012210319030041040040700c00d1a006e00c4003050039125515514411402a40c6903144000343c40c079044018101c88001540050034440040819140e1030210b41680603107103000294107110700900c038145101c1c40760095050000081340069035002890041c20b15024460180c0e2640741e014050341c1c1c0384100b0210701125002180c0d0113030f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 613113390 1250 613112140 613112147
    0x80c030d0e040905070305241b0406120f0f061d0103020a0302092a0702150720042304060509070f030b07050c062406041202040207050c10031407140a 66
    0x1640b0314410011034100580b01d542c0c440c02d249400015440f03404542c1400010b101500c00d00d1500101301c00e12600c60403120f927000c9081480346003d400f05100c20040c3e102d006250503408159500f1301c85501300110b07159640b18402400952062035411483e41d0800c0c03409541c0d1207020707030403241d00800300c003810343c59a802e00251440080c498400c827010700719501000c000d01c54400e141d848030245015a261207501c10003500c8858000c075224806000e01c51900028034591303507100030444840e1290040c24503040000d01501031070341035a03078003c41c0c0c11000d402c0f800481c10f400c4c0100c0c442c4e2024000759540d581402c0ccd40c1d801b00d10402e60b881c0c03050b000c2000400c001c003030700b180c020030b60380b1b03106141400011901d031400350709642c24907882038400c0b42a101c052241d890107048a03000c5401c981b80c80d241400b0090507840002010740b080e580081d5540030018100100c8a12440c0038280780394010071004040d0041402c03c0090302c0504507400050300c40340c407a8a6441508400b16031580c00d1060004088 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 613114640 1250 613113390 613113401
    0x503030d0c020a0c0305061b030127150e0103060509030304050303070c08090901080604060e010b01050d0b060c01052d22140304180e0106051807031104030606080c030d0e04 76
    0x2d41c000c101c82480420030040f6403c026500030300003410700e410300c828001c911040070b0070940d030130f40c609000500155131704541c855038400115a58038014a2407a81181c01800698241d4485e511850300000c2c4000f0341500c07140c122800b840d410801666000c041a44070b01c000c44000b08650800c00c0045d140500950300e07201c842e03000d406043e041c2161140031880480c4280c00c85d00850f44034034200410422103000358001c1e00042c2001344054000100081c099004051542001c0d0385c6400d0006420703280e51050b031728544440d4000b4051030a01304060403000d850160010480302524943c4078040b101c00301010b01403100e00c803503101c0300c000130f1003c800590000c040464403048180300e800d010303810130805007026100c0241c0303c010009550500d202183d0460325444117690501804002981d50303036160440c3c8141c942c100d100d40342c0c0c1c1e60200310001c116000003050010004100841880100c0e8407103001c2e02c40c660216440340035090101030703458814919540005400100100caa4100703500304 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 613115890 1250 613114640 613114661
    0x30b040606031e1407060906050a050c0304151e0503010608092e0b010c0b070f12090615080c1e1302030406090506070c031d060d0905061b040503030d 66
    0x3141030300d075a500f50240c140900b21a000b0000c255100d8280312103440c50300184010f540003080c210b450040c0180c00313440c05216070002d210000c11010242ca00400c03c0f26000060741c01582d80d5951984512003400108682400028140120a855000d03016140100340c0a0700d403900c42c01d6a1900c18200d514040082201c03216014800b2010f00105400e418000707607021301c0030750101406400100d241203490b402012410400c0746484000480d600c5c4507401d030407034414504428443c811800603070b030b4200001c04034258145424101818000180e1048041da880c001511014079a0b07194aa5aa80b14501100b42d1180c1075140050100c0340d0030060361100e1201404580c40d40b10b000350418200d0304119025102e00d5181c7c82c1c1003082180c103000181d4001403d0500110911054400400443c41c90001c2c4618101c8000e082c50266501c0003501c08010a148042c8040715962a166481325810794008145440340c0304200d42981c00281642e06580e4007400035800e12860315010000741004407170 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 613117140 1250 613115890 613115903
    0xc022e050c0408060702061b0a0504030209220809040c030c02032d04030c03061b1722030c1109060d110a031a010e010509070c060903090e0a0c020f0d09030b04 70
    0x100140f1000c0c1808102d1048203070790094440382c0780082c0b61644e258100300c0710f68250034042020f40d0000740c012040c0da0a4a030141c6004202e56035030781c2508040c00021020100703c9000c00803510030000322000820f01107006680922090100c11000e03400d48030704170301c0c00d800750b0414000c07101e6003112100c01c0c0454410010b201814002407001d54000e075806070301b058402c10202c4d07006109100384c41c01044480b0410031580210003802500c000c1c0301e407000c0810003104241c0d10000c00c400340c0d40841c542007080030a0030004e05012440c500980b42d000c603000101d03401c0889aa99211501d0045150b601c80c100181104641c4600fa82e903c6803020000c0c103069601045c000b4002c4081040b850000e40502d1a0008807402075041c81d482e0707000c004050b4086441601e036002003094082d0b0103102d1030340c070580c89000858030107018074040d551154150400c458407003203c0c04201a0410319081190b075203070710380c0940d54000c000240c0d031500c0b80c40f88a0107001044d080a01080001c004602a503845801000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 613118390 1250 613117140 613117147
    0x32901060e27070e01031b0212030c040e150306060a060203190201060b07060213120f020f060c010e0616080c070b0603100e0a0b06010c020f09070302090a03060c022e050c 75
    0x1252400b9070209490311000115140d043ca16103580500c03455031990080c08406405141902e8001e59400303440100c0d503080300d804408250024007000a440c0509207400d68a040c82c5002560050289600e0940714401d1080101056a500f80130000000355551036000d1450b100c2c865451800c20100600d41c80c00310340d69454000b4204400c07501414040c1d1243d0702c0135a5032203c40718078000c404c01c035801003020317034180782c03c6100045e81d44107c1d001c0360b40d41039074410244a031307404c0041c409002e12000628103500301101090704240200307809116014840d80c0041c519007401048640600403aa804031a030b60400c2148085410f154216510110050440706d0030a24110204180c60528064102a51124100300c0400023000d84540c4d100b882032800a004508980014411070b505600301405510700c0b07808101032903c60f40480d0400c90001e00010326007a0380b85803500060408202400050185100070040607002d01680403030031140312034000f048a001044000104000f03031502c409041c040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 613119640 1250 613118390 613118449
    0x30b03030909100303020d08220204110d1b050403020303180d1505010f15020312060f0621010e130b0606070b0705030f150102070b09041104032901060e 67
    0x8601e10b0b4415000c8203141c000640c60f61030087d180c00007004102c001d0012030000c102d0351f203000e5a81c0030078a05009110b102c1c20507450001c90014030340d4074500c11001c640015000024240783d080040e81950604103203d0341e820381c0d00200d400d0b02607400000d6040d0800c00c40c902c12180341c10b0109200f00b01c01040143c180b441c990b6403164200d4001405000c03a503c1d6001042102c0b03040c640d91004103c1d2010401c81c200b22020001d49900c030303040c2d801c0c46503024100801c0e11525030388244200700c040074148954500f400c0d412004814240c0c9a845001d000040c0041015000d42a00d40d00a41d8600720900000142c0c0da070780314440d10014500c83d00800d05010800204600c0c62203a4020392040d21015030740e0803d01c0040d80c06620052071014200b00c074031003100481e64000f8000040322000168141c591803100f00241c050174030342a110745007003000300f13020051000004c0c4030a0741141074000c101c80d1400000742d55696100074440c00c03000c54140c0000700460300f409041e007003411000303080e1165083c41c034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 613120890 1250 613119640 613119649
    0x924040905010612050a15150314011e080a0c0302100c0209070809010c0e13020d060b0a0323060906040905010b0409060b0a050301110313020111070801021324030b030309 75
    0x1d9000d480010130000e510314121002d03100d400d4000e1000b000074084145001000007041c01940705180614584540c0218040d100b0390111505041191541489596076541302900c0e180801e102140c4a4095000151801d4005445140313141c0c01a480d541c0c0c2c41c5140c00304442c41010405080a0104459041c0300580d10000001d1013100503880f60b4032241005d2402070300315402e0000d2441071000c41c005c0014140d0b0b525159210401c800c40e409039841008454040c00752010fa40218000740c40801c0c0c0c42105500350308211140103910030b20401c0308031052034880300d0f88000e890081e0441580800720780e480c01c1a422003040030f80100f0000c24510800c41c0850100c3d140407005541035642d66181e00840e2502c4480500184011030086c000054030700660100e074070000c0c100e01c0551014186001c11a400f42e110121145049000d403005240d455000602030351102c0e50391a01c04180314000b20b12100758000b41c2d49800c0f6211030208544002081c103074001d00c188040e17968180300a11840d00142d84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 613122140 1250 613120890 613120901
    0x60501060819290a0503100e0c01021204151407050a060e031804091109010b030a05070f050313080d0c0c11010c120c030306031a090d020309240409 65
    0x765680388280ca011115804503042241140034014102401004480284110150088010103410002401500000d07100e00030540c089501402110304419019055a001910f8048200183d402d00c00010004980b104420ba0b20442150000d010602103c03400c03040120050486040405808200c5041d11646070800300342141d05a10082d4042d0402055019010415442c08001c5003890510001180c08a152100c000d02450361080440c00780800024a0b5103549005071205500396101d14141806910842d0300e00303809424400422003080c85007101c1005403070b895035004d08603162800364001c540310050068034a25810f0001c185201b80d01d20070000f0b8030f202c0b51121907200c0ba440c5408062080c40c40344190605c075003a1a40f0002c142c01200c0c03070320b004280c1d1034012450f620524083d001481e07150070140015202c0380f0016041d00406d1110b5004c0c89103a81201d0307440c05000012030340d0784500050682c1083c1c40901c141080104803600f00700f000741220b151410b040c1c0712840e07401282e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 613123390 1250 613122140 613122149
    0x317130b0d02070c0e100504020c0a020d0b0103050f19031d12100f0b0303121308041d090f0c060a05090d06050f0f0906040209060315010e011706091902010c060501 72
    0x280c1c00950f500800848a202030001e248001c0f0240f594500b0a80341000302405104442c01141c0010b06c421401800780200000954010240f03c545102400c03c0c964182d42400202e40c24402d8800d541c48050002401304085940c2d0380d49068403078000d54044801c04585500160141c0c07805041d8015a600c05505003651030000d4000c003480f0100c1584402a640000a0151120f01c3d0002400080d1130100c1164000b5500e002c0032011074545010b042c2d801544082c015215a50100300410504a030345d80310088038280450019646d10f41c48035590b01c0d0510316114003030303d0340f02c5042140c0c642170003030140615070f9031410403038107211102000c54003110007090100c40087d40c030810440d82a082109940d001450748040d81503900d0004030140e070300c50018101a02c1010300800085060380c2c01c100c2011501901c52080c41e8a582d554010340301002d00f800b40e09154041da01d000c5240d10760004596108005060040080103211070307145841118211080c1d042000c040d03000b4010a80324001d0a0091 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 613124640 1250 613123390 613123417
    0x2010905120a200705040c09030b010f03020406050118031b0506030108070905010815190603020409030e040b190b0306120d02030c1b0f01080c0910021e070317130b 72
    0x50005030002803a8500c0000c020074464034402c003d448450300040c20b1001e0b60400c2c0c5d00055604110036082d2a00110ba5000400054001c40007155541e041d2420f030040303e01c02d032000e00100e6224070040d50300303129100030400d82003107401042002c190ba5200c99203040542001d0741d00b5090b01ca00c0800c42551098001072030075402840104460310942c807a89004140c60b6000c0c010342a00310301144440203000c1c1c003045030703041036140305d12000400d640180c00450b03005004200780421440c015040f441107400c1e0398861842c280b215003c3e406c0810113000910050300240d0031540c1072002c00201c40e0000b4115980007404110100388044040110072400f080d070341c00030f5840703100800c08289800c0c0c080c0c0c110701d01c00d1071311800d5070042d403522541e80340b0000e000d08010340c0580e504003601c0c1850040071074582e03101c5641d60008202c2034010480000c01000e5090301040310030807424039aa103d1a03031000900c6042e248502c0a40b030001d21014014030b07903c1101c81c92a080d0b6031400000756400402000490 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 613125890 1250 613124640 613124647
    0x909080408071e14041b11070f0f050d080c0a051c03090804061b240b06071a070203041e05180106121802060a0915110604030f0201090512 61
    0x7190007000800001c12080c4056076140b9203084440844030540c1c41041060b060120802049030768a41140f00c901da400e440785004204000c2004002d030280003005616801115004262203500381c6800c019165104103509629281a05102500900082c03d85102c007040c40500c4000070180102da1025000782c00404581000c0c640f4030040c1d00149150303e0078540341284220009030a0415902140c0c85420324000c901d00c0405031440300032008000820140c2c0c940c402851031441d0b00b6075580060304180081091040100c1800709620a07043c1c0a069441c5120614400b410780c0501143c2c040c0d018130549040a5881c00d5403204900700c140369000c082d80c0b000c028006030030b00c540d4041201e0010100200654034100c40980401c14011000400e65201c81100d100c0741c502407100c0b8801580504041d94540b10144010480c82d00d40c0228012082160100f485403840b410f8018045890000903008a88480c3e0b000c0d5610300a40f03803941e0655403616a86000300e5018425089809441e1001c640d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 613127140 1250 613125890 613125899
    0x1f0f05011707150903030804030c1a090c010c0b0c0708070b040807060c020a0b19020f04090c0201060602151504110d0507020c0d0b0a05070207050603090a05070506040608150a09090804 81
    0x3000c005400060f03d2814048071043ea580e8050f04000403260107081840080d1214103085a24608895010349240c109541607549400903803849442280c06800307582e00d8200450044847c000e401c20050001da00000104451140c0a001440700503c01d400703803841c00565036640c41588008407000d0f036001501248000c1480654014084003000e503201401e0b007544c956551031105034001d081392003403090010140c81030000c1039040b0340110004204a42d2516500d40c6250094901504800300650900781d00103202800019030a03003084c0e02e80264010344e0f4424200c0e20ba054141081d2660160310386201c0218980810004c2c440b92110b0603000c9868600f440303010340f91403000034502d40a20083d40703507a404140d458130007942016003500c001c5000c3d02d505401321310b00115500029445071000050101c8001c00144010601e4420400c0c0c0b0300540d42d41042106a0003a0700c11040400e0001c2d0010b0305031b0300c81950f0044000c0d0010410000291206072600484440100413901a58001001d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 613128390 1250 613127140 613127143
    0x20c101b080108030a0e0102011d0f150903180409020402040b07020f27150a0f1508060d0206090406080123060306061005030925061d01021f0f050117 66
    0x21103251903040c0500194900720140c0d81c1e0748504845407040002c1d4134840d03103c6a2007904400300b46c402c50901d01e0504111503603403e4451181c81729101c2c2c00c4c803c080100080e540304451440c410700011003d94100017005031910100a01c4030896a44117903030f803c4000c0140d940d4030142c40070b802100746c1c00e42c48880f60f10511803c4801407442d00e21480e801c0d04640064401c4100307101003040340c4072046c0c8103a26030101a04c80d21804486042d403011a0007800b1600d841019028022210000d040080b4402c95032421380302144146c0300300742c1040ca00b000710400b504106004145e441d0020740300007903666071060b4036401c450940e004507101d08031000c28500002911504143c10500c101c0140640f4100314001426400740d8540a01c14040e022002420f00d0b1420b005914510010360716841000c26481c65000c0e64104030700411000c24101d40d02a04504003600520540e041d040e0000d000349401410040500d10382c1c0024208203d84034000445080b0792402118000c00340361544001002e000e00409 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 613129496 1106 613128390 613128431
    0x6140d110306100309020a21060e01020912060c0301092309010b0a090b0312130f080c0901060c2001120218040c09030b19020c10 57
    0x21460000c44030045108a5048900c01c1e154440380c4415821540030600103501701c0b130b202d0300610480f001c8540d510015034490021100300754250341c46006542c00c240b000c000c40e940105499481d8180a0140c424070f070f0b80100030b044503141007104115a400148513540204d6207178607110702103500c85002c1c6080070a0018840b060380c502210820702034400300b50246e0048003900b500007180600d038405c0d0318000c1c800078007030300c444010410001d803a038000b9a115010300404003c00144008628490b070000c0c118440544041c07800c06e0708014501034140e1042d0b00744a041c0c1c508500241c80c1090010345650a00c04205045206c480101c419144458942d4096480004c03000191183c603440200320410446080c00f9000c10188101d55290051100030403903e40040400d03101680703841010300000b05214014140320302c086a40386000404110585180e550f010b03110096500010380 = true := by decide +kernel

theorem cover : BRFrame.Cov 612949640 613129496 := by
  have h0 := BRFrame.cov_init 612949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 612949640 ≤ n) (h2 : n < 613129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
