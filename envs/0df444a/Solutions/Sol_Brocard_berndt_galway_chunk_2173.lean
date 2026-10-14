-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2173
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:52:38.218695+00:00
-- url     : https://prove2.me/submissions/ac11f05b-3cee-417b-b4f1-a6479caeb52a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 390647482 ≤ n < 390827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 390648732 1250 390647482 390647507
    0x91208040602070f080307060f1e05090d0e1003090f0602210a021804020d02130801051503060103030f0c14060703050a11040e0c07020a0b030a020901080115022d0a03 73
    0x8660100365135000d040c10341c0182d80b060f001550002e1018201081441e00410b0541000321000141e4480e407402d08400d1460554811070841c0d507030700400145c60f80c208900450448241801c0c442583d802c80010761007054100c1e0358041580380c04c501c00c10030040008001405500000640d103d00c6600080c4d29a1503000f11449031180020000c00c406440c40c0c400c40c0c0d031030b000e0420710802d2010707a5014080694003658640a000340d003000072120921183ea1341ca005485035000106460810082202100b0510030080d07100b03400803801000081c1d080010798901c0082414001c00e004164285900801100d40207040c1301d000d0796080242840e1301d540324500c1070030030580c01c11040c002c001c0341ca4400d00550103802e41c401d11138004100942c14040260164910040c600380d01c580c3c5640c242d645941003610303003018064011464812641c1c000500da8090420718400c01000c1288034030082d0703610303205001e0310341c0d420b154010032409148c00400300c1c00e100b83c1e06003100e0300c641c00c0c0e00e0000d01a021600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 390649982 1250 390648732 390648737
    0x42019021209031e0c03030408060f01060809031801030b100f090e01080c01080a0905152406071209150e013c020109020306040308040b0609060306160912080406 71
    0x1000c00384806201c0c01a00c00c103903400b400402182108131000ba86410045040010750b201c1e041d240d29a50340c0400041020f0300c1c058020b0545c82c2000000c0c034600080603008042405030300070410510200000c02d843c0754650306c0117001d506c2c10418006030010000b000310560401d81c5181103c04040d041501d54036000043c0e81c2d00b076015596090070002212003030094206030b07044250004400d42c8600202600602c1c3e0600c0020501d015a0b202454588044248014500304804104040392403218603804181d90f91201130a06044100103407031441540c00040040c07040c018183c8000d4403a4003201d01030426910000c1d840320044a006c2c040584840880b400500314000040003003070350a0b0601001c00d101c042004454001a000301a1081c110007060210f6503504001e02c0581d500b000101d00a83c06074551030302d507050504102c41d4031980101801d004041c50b506008035078400050090b071000e5601414140f94182c40030071a000310340c5900000c141e031900e07510241842102030040c0101c42c80e40c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 390651232 1250 390649982 390649993
    0x411040f051602010e0d0e1305010e01050109080c030d031e09060e0d18050d03020a1704050a060c031d0d2f09010602100903050f13140105040e0604201902 68
    0x3c034281d88003000003001d01d80040515001850046030b420725070500c010150f5a04089501c5403804451090740540c01e484070400c0100295604401c419010780500405096450740705400b082d034031410780400d2420544e0791000040441d1034400311402d00e00d80c1080c28010701d41103040c220081e1400c60000c1005010b0b4440010541c1d00840124502c508a280c0030041d8503c0c0201b0420100c84880741541075003e804600c030300040c452407111042d66071217003000d0340305c1d400c0c80c043c41038000064105000b48040c044042010035002142503200c20401d024a40d04a120784020078102214000f00400450303c0138006601ca9001e070103090002c0c8001b2015294600c022000c2011220007845004056005000c0b00c0c0ca480c071854000d2136030203000341860381c68000e81c0c296140c842e41c0300d01c1440801c58070824080c052060140c000100401d400d01c0e0403401d140c20019589000080900180d2050b580c0b007a281d07442c05858500d180c0c0b816081e040d4a61a054045036406c603030365652820f6801801030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 390652482 1250 390651232 390651271
    0x1413032102070b13031e0f0b010f051005090409050102041710050c0307080c071a0114010305090606100c05160b0705070801020414040c0e10050a171302090411040f05 73
    0x4401920241e100c05200b036410f0a10f161101b400c0807281c0210030312a288102410300200b0145600010414801c2442106562406201c038404600940203940b080d4800094508030640c000c060b110380c08404c5070001544101450000c0c024421588240000240742d03440c500700f03c001180c030302040780154006010540d10740c41070700c000e440f0031076940c40401c0311000491400c6030480094400300307100f076130440e1060343c0f141c1d0303a0080c0300001d03840400307c500c3c00c0e1044420365034140105604038048000601441c00c0c2030f000500094006c00032401000130400c03400040c042e08001b0303210318940c2c202c4a0302c6815111213980300781d036222007000e42d041c3c0b040c14400600a6170502c2100c0403101000b1310014507070340c000d00300700180c5500712641040140207280c10540f035590010b8030f20109002e4881036651814910082c040a51306240c5440584894041140c140120140405d10f02d03412640c1c5525070390b881c900044072200010360f0340d410526001000b00400300690000b8020408401d1404505c0c80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 390653732 1250 390652482 390652499
    0x706030b0406152a0c050f03010c02060c0901172e03030e04180c270908040510140304080406030e16090c030617210307141303210207 59
    0x85902c100410f6004614038090f00d81e100725205030380c980c4190384c0d20080140401d560407000c5076841050ba001ca4142004021510b80240340700b0615905034000e12040c10349500181d1200700050100107080400124092a40c0c81420020320842c01d010f08001035007000c03051424202010b02244040d80b001002d120042d03010312244070122503040da01c0c1c1036020505024400a085e00c140516a5036003542e07804400902500c0b50300020f04254040c040c035002c02005441200c0500c000341c05401490540380c00c02040140c012141515800d40b03840c0302060740f41004a0b245400d000111441000210031f11041103103460081007141c4040d82c05200d00c5072119121a02c68004d03c6414903401170580c01009845460f804c02c0381141e4460a0005e6002d58448005461507041d01360780c4400e0700a43c0c0c40080b52042080703c0c0900b9100303000154110300c0c01400144c00b0311420b040d0152075a401140168034281404c00400145501042c414100c42100d088402150841150080580140c2901245864 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 390654982 1250 390653732 390653741
    0xe010c0506060105070f0218040b010b0711090903120f0402011701050d0f0206090402130e07030207081204110a06020313140102031b07031406070906030203190b0a03140706030b04 79
    0x94000000d07003681e444400c01521264840e132001c9950b65a01c10002016948000c0424101461f0228800381d03480c0030715000c440650160000d2101810920949012035041241c0b20f542d400c01380e40c210001d4070341203090740c554001c040704201c0e146425000c120300491240c00190080703100b82c941416071500f400704218642024001e1030f07008001e1010701400301750454440708580340060302c694270b030459080104040c0c3c0d0210f02e21401341210038004012480c07001094503400b9441d071070118201406961031000e00e11821016003040407001d8081390502c5406540040c000c00c2c01000c554246680d40bc001c2e459400240240400341c2c8554000a03001040010580190005902551900311401201e035240030117a05039900c90700c00c400c004030019800d451880702c080b0000c40148080d10380304100400c00505608103004060040c01840b9800c020701c406440c502020302ca01107011011640411b58200302c5030304c06040c2142d90b151908202c407011500005492240d80c06112040480c4207000585 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 390656232 1250 390654982 390655007
    0x80c01020318061e0c0d09050f071406122d1305060709050303190212040801020405270c0d0e0d030203100e0f010b0a0c051506010306061701051e1206070e01 69
    0x81342400c0010040c0c2600e00007050028411000040c03400d455440c0e0900e400c02c000117600c002d5020f054140165021a502b000b60584d00700c40e164546101c401a1041c940c1c00076052050030210f000d40090206110591301c45500c40c020500340181c50038180000381880085800d54203805844041241c03584204109015a40b0280085141940c0001c601d40507003008024039045000b100000c200c207518080c020001488040000b588950602040021600c2c1240311402c2c1c208100c1072481e512145031011030f6102d802d01d610640c41c1e10005010002801806034010324602400390090012034243c0e0145009554640311107034026202e403a801c04084c01500c544c0b000c01030042c010040405900c00a01001038285080849000142c2d180c514124441c07481c00c002580404c100015941c2c14440c1d0340040c035041c80c0c4814030b08070411401203802010b01905000c0d10b5010040020703000805090282c270754019250502d8009800e940589806054039102c000908a0320822059803240309401c050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 390657482 1250 390656232 390656281
    0xc0b0c0705100306030203060f1608011a0a05040e240303090d0206210a14060f0d030c060b1504170d050412020d06020a0201050603120f07060207080c0102031806 71
    0x300307820481042500038035252420205610350308007000685040c0301d00ca0052041c114440107070308082e07000300c0c10340c04200070003401c10000c4001040101c2c3e00c80b0900c4001a44481440e50302c0c0100b4404540301c2c4901d81022000c4c503800b009105c4500952003855003082803088180d101e10149070b04050710b074492800d00c280e00042d900000030162900c1d100804511250810720020900d144e5401e00302401c04039048902e866545d0448941d083c8010b01243d400801110018200841480010904500d1100250804c04115013400130031407954805028003800134005081016040c5d9500314640c094040c3c048044400c0881e00b42c02800041d400307a075001e10751681c900b010706011294954584105082e607200c4202c0c0031078004550240300400c01c11556078000b06842c6040b0007414a00051101060584881003103410014950303102502c0815a00040141e03860350f10341082101d50280700c06a94040d40700005101d400c8004840b2070301d251451a09071922607684000d081e00240740d100c0e01c10701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 390658732 1250 390657482 390657493
    0x60c030302030606090d050307150b092404060b07020f06070206250b0a0506091528080d02030304050706110604032d03050613270218040b040c0b0c 65
    0x38001e030040d5600c0580a4081414400d554000a07013103406260155034980000079500d050010045440d03040c0c0800c602c1c14402d036410b040c0415242038000f00002002508821101420138400d0ba0001020500038014010151030304105441548405012445041c04d1000e640d070310705040050b82d51960f0001c1c170080c20035803c111340154050301c074a0440056020240c4480010f80705241650060b80b220100142920742201807080380c6001904200095815000710040d0b603803000e00e00905008404902290a4461006000095101d070000710190042400350100541c0c000042c1d80700301d0240c0c0440b50103550352030701032302e8000040c020b040c403a03000000007801007070003401141a004916080641e60036050703190069055002c07520807000a450710180001c510300400703e40c80458101004000c031031a0388042c0b05807102043d01030680704014203032000075503440600388400c5405030301440071146401e04c1c11104030102154121400d80354a44d0119492a11100395003d10803224005d14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 390659982 1250 390658732 390658757
    0x9091a011b0c03060b120c09180708030301090507080f0c09010c020a0902070f050d1b06050c090a0806010f06110a062c1f1506051315051c02030106 65
    0x11100c00085a10810303407410941c049000440a14003003000310b01541c0002002c11a038010826000840c01d8600f00562080914030345030766401050346c6c0c004d040c2c10564110f000020088a0800750303a6405240701d40808000040c0c440602d4200c503100e00660354403003003242e075210300d03075203964800b40e0340c020320b01500b4001528194011081c061009000801201c80103944404450a980c80310000321b44000c0d805042d01d0400000b040f000c10f040c541400c0c941100c0e1452071252001c0101410b0280c00e8030b4460740400e00c68842c9030212003810001918400c5216103449103550703103006c288240c0085400741c400001d5443e10403851524002c0300700c3c01510860025807903803005001564044c941c0c00030300610f103140c69003c0e13015800408100c4000b90408018032082035120100005582051a0900c84599420924407010300161182070520586402c0524070030040f400103604400307624000d100320407202c2a007240c081c0036620402e841501c0200c1203101c003102079001c203110300c10101d1012038801 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 390661232 1250 390659982 390659987
    0xf0106030507031b0e1e0c0906070f0f020d0803070216050a0905070207090c1d04050108060708041401090f1e120e0607052409060105010815030a02030a0308010609091a01 75
    0x7416113104042000c02d115142d03402c002003c4429591140d11015014241e09554450780d00d850f8080c10030b042c201d0400c4c104101080700340c0301c1c00c03100600840c10030100d82e042200310b044215155401909242e0a0490b525024442d640156402c4016110385129003944541034942c602c00c0d98800b4155141443c504030580d0f02914002d0501d105500a1000100d001e5149114940300442d803541d643d546441d0703540041c03442001c00307180f99026a040c400140805140012901d030040803520b49100d007075480782402c8844850209460a071942010411002c0c070149141d8405001e02400c00f07007510b1120909240c15080212000801315088040684c003010f008040842d16580b0240c50546011b8840da1120306001224812081c4240e54504911741c0b1b5101142840e03010781c2d03d00052600303504000018092100c010200100600c101040042d152030a0110248055010b021201100100e1401800119090088000141095a00003000d80190003541c0081c140205c121900301c4469004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 390662482 1250 390661232 390661253
    0x1090507121805100213090e211209061b070506060111070b0316030608030408060f0a0603080a08010e060d02092e0b030402040c0305010602190c081506030f010603050703 75
    0x102452001d121050402090003400880d0021001c02130050740c8010140721501d024034a80c015050341447d01d281009040750002d9001174044044000380e052000820988245100721200c601105010106102106030f00280c0c00d402804601111800084200070075100c0b405409409090781d4040360106200d540076444541c0e64500180554100c41d4503540c49000f40c0d03101764ad04800c00715140300d94580b22a80340c0725890140c210034000c0c40c6094503108070955a0903001d428041d42084207030224200c8441a0b00210045510507042c0c0d889049a81000c1c0104909110b0904c001005500245880c0b801040c3c500d9141d0b030080c000011600c40d180d002101e5000b41c40c3c01442d0301a55440880ca0351428040ea400808821a01996a01d0984103000c16134202103410340a15044c8001404440e0b00400c08104a600c25007181d071a084850a210312415040d521400c0207009120081d28030f1803072403007258824901030341201c40c40082e1100c61403c903591488081c180783c114000900008601000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 390663732 1250 390662482 390662501
    0x71202070504020703120e0712060b0f0a08010b0306181518070f060f0c030801120f020402130509010b0a0219032d081005100c1e0f0b0109050712 64
    0x122040c03652900041802c80e0b0000c0025000705558442c0d41c400c04070f070342c09652265811680640046c0e40f03410804d8030351010100c801016580c440c0507130b00031030320f400319110340480000f481c858140c1e075101c1c0464002c10300f061505000740141c00004250204040f0f240d0202d01c661401408002c00030b4400c0104064041c0981d0004107141907441c4a2101c200452406000780c3c0c0400740c00c10b86440c4002d08804940c61009041c4242c082c042008a07401516541c11140710854406194215240c0f5180c1d20051712002075029101150303100014454002ca40d080e2007040d00e12040998999020171003030301500f61450b00585c426100c0f400c68114070000c001440f8032a00344442100760140b800300b0000180030055070b81c0b40540c80d000c40d1032a40404480e800c070aa844441030f0660821010402042a40e144942485072116400040040b04014a40d10706c0312940044204410f0b4900501c1d01503088405031901c0c00b80c00c00106000020b4843e0034005c56141c2c035010b034004903000098014103044107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 390664982 1250 390663732 390663737
    0x10020a020a0b0c04081504020904030c14010504051b0f06090d020111012918070f050f03090304050307061416080903100c110a0f0204020c01020903030a0903050607050702060712 78
    0x71100004940000c2140030b809460003081c2c4450130007401c507140c40e00c0c00311000e080c59040d01c14440540c84018160703410540620300700d84001602c0c202484866004098800035628003002c200a001c004249407518024004011104004542c101300c1c284944000f42036114000300000801442e04113240362040c0d1040c1054071040080d180c0c800c0c00c454a10703595441651081104c584400010700992400c00001c5400040301000324410081ca160b002300800140070740510041491806407082c2c4815052110240740d491410700140c45d00d0390031911a9134024492484c0200700309d0f001d040c020400780c0c6850480c60609000c00c1c154081115030700c00a907061071080100380c1c4030b502c0c00d201d102401044031101144606074100d00a00d10300030a00c41ea107190300062a0040050f4080443c28003842d012180961a4210851814028800d1440581c1d05100014136034074a40c2d0454000011030740180c00f518540d590382982603880b8400e01a000b94004d100300040f500017040703c124140030380d8031807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 390666232 1250 390664982 390664993
    0x70f0e06011e0302030717331905090901060320010504090f0b0918102a090614190f09080607050405090612150a090b040f060b010f0210020a02 63
    0x200d00c2c800e4031102d0030002c0c80003035000800c0002984e000344111002c1201c0d01c000c5c041628052a070a510b000c10594940603407008082c078070411035a52100c1111b83c580080525626204d00000c84400c03c8240c1720301d9004401500000c2c00c811018860101166004108610480380031201e0b4016074a211900c80c1c1400003e0001046140b40c911485689260300c1c0700000d0024510300801413030003c020a030095071944d0700310f1103041c55404110303103417400600b180100380c80c4500c5411a034000c40d4801e100001a04602000c441281d20401d194200c4083d6125032507007a040d6005404e0034441c409621180720120000c5810307640c850260320014580d14031709402c90503141c100486c2003d8096560100044001c1410300c510310b40483d4841e0060000c80b0b00383c0000384215441030f2a000002e41d083d664280b0500050300c100510740000120a621400c596020f207004e1821070340284601d002920550724183c90020954090a42c4c020802d070217030010b05500d200c08130050003039801000c10f602180940c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 390667482 1250 390666232 390666257
    0x201022d0102041d0a09150b01110a0b060111010b09060f0d06110c010c050408191a010806040b0601080f0a0c05090a030f0302060f0c070206070c0509040606030c0503070f0e0601 78
    0xb0b10150000e482600681c0c51004080c0c103020031440405070200340078030700c0d014030800043c540b29000301411400c0f100c0852019114070058500c18030300e00400c900c50041c25094000c110a40c06650300ca66400d80703c0b00c0002c1b401c0b08040d8221049480c6982d00500c990740455042c1c901015461420000107140703021003002c036601d5000743c40b04606c00d00704108020810301c00d001c10a00841007260a249001400c2900e0700c4542c035680d054040401c0640403132071100e071050050f00c0e4000c640d1000240006861365030b640910f135070f440c0c20407641544c8515402022641542c4940300f43c9010780140c0084404a40700c060302e5600070701c491251a8280300c801c20051800351074001c2080001c5019085081d4500c03181c1c20040d081c55001011304c24428080e00411890560703001c00e45030100d80645400f44c8605284c0780c21500d00407640c21040d48007001804010420420786c101c10180c034440e064412005e9a01d50a05a48000a0141c5094a40c040743c060241d800300c683c08582c8804140350400c0050503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 390668732 1250 390667482 390667573
    0x203150301090609020f04020a050d0905070e040c1e0302060304030e2d0a0b030601080a1e1a0301140105150309070b04120501050108060c070816021306180504020102 73
    0x803502c0c0221030b402c0d210803181c41503151940c115498190b0a0301c082d480c0000518000b80301c0c0c400c00640c0e02d401603a49011700e060040400150000e0300c50688000d11609150078006412806445452050f90164150200800b2140d4006049a43c0604210308648540d90705813074403841c86a0441d0018011031601694046e0444c440c03109040b41d0345001036100301c0405100d41803180d42c00800240408109104880c0d0340080d090781d024000100008031811040c0c0c2600d03411850401042d101410682401c0d034403e0041d072008003064048000b002802d001c18848496200c003449401d91250315106450403501002c0c0007183e0240600d03040d01c0850b9165602c0c20002e4001e0380001d60410300e4030a0600c2041b900348140342c098a903207002402c0c5445c0500c00c001891094010040610f800031941c00000160850b1100889900500e02c0311010300f0728101c40c008103618499040c000181d05000a101441403151b01c0c002c58040e400b80240c000d100034146941c0182c4e0f080600d0300200814003018142 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 390669982 1250 390668732 390668741
    0x60c1103070f0512060103020306010e090111041523030c0715110909010806011a0f0c07091a0402040506040504050c0f070f030e0102032b090c080124030507090203150301 75
    0x500d03402c20441541007405100c0940d0320b8051401da20f52084005102680e800070390b06045801905046103250f5403441007a004d80403008605110761004680482e480c4490082d43c03508001c20395500d0030088061042070b042088140140411600403c0030070300c0c2d0340f6003800a00404d801250150041845555044101c41c441d0403070110f10540829489100c0c54038003000e07401420010000c0500b541440800300821408003412035010342e0000d40b042c113504440050f1020310030500151041681e42e07640c6000074003001d0682e82103518551011100314034082c801c2c1c506840d4041c150504050a103801c4c04001c00010705074048800301801405100494100104410362055030201540f400e617190103468441046241810754100780414070b07400150a40280300d5904002d40002c1000c80420200000e124040c070203016104100804281d0b25815000000c40840e040100c0a0600003211480151051400010039030703004903c0802031101c2607000b464114459400214100b00080d000900b10b6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 390671232 1250 390669982 390669989
    0xe010803030a0e0d120c031410290316020a0b04060b1509060a080a1e0213051906110c13090212030a021009050313030813080d09060c110307 62
    0xd910010802900300114000c00c40c0d08100c80d0000c00c0c00300002030014100001e81c0304c1400e182035958421521152103034100060031110210000940d0034101c1944501c11070300d00840a00c001100400010306510206400c094580c00b031141c0d055440340c0d0582c02c0e003056003046040c21449814069004500040c4e821401035114a100003400030542d014010404c0b48000e4183c0482c07402d00026a103611000120b440038001440c10b10507a5892040100003400f40c0c4030710b0702844406290002a805065005024580c1c0c90064004007a69503c10480a100030010f2058860308003031080100700d00850780c9140016418040d81c5422060b840800c804416140c507140c10140c0b41c007284030660a2100120050a5072038000c0c514015005001940c0ca03080c11041c0c04050381d84003410020302c4402d1064030100480400fa040a070b03a92410643c03110341120140601c400b10700c91001410400015080f1030f03041041d01c404c410640303840f5051701c1010303a0140548040e81e0004031524503a0b801d11814019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 390672482 1250 390671232 390671249
    0xf070b1c020c07140406050109030b1f08030706150f030b0c0d0221070807090506070309180b0319030c20042405121002070302030f130e07050307080c030c040e01 71
    0x2044c50074104407030fa40504d110640c0568500740e02070201da40d2211428050341c0d00080c0706510f68a600441c070301c409030b40802d070401c200107900010072142804001003270424050030b0140040028030007040000c00071841200400105040c00300009981c89a4640d07000d100b0008003030030200d02c1c0c00c0d5a030030399121021480041c40c0c1c803801074078418401311450380c104035070303180002c641d1400f10301c0a85003040034041d01d0310480c400f007982020540301d41c00d0000509200e44104007501c024100c45c0c809003119262051190140151441c16000d50f020700b0303404107800d81d071303009904449a02c8000507541c240b55020a00c0c000388803000c0007910307507000c0c0d44070904040308182203003800030702c0894140b1416080140b140025403400300740031000281c1006070110102005070794400b5803038207a19600c40c98660046140d40818007180c1c006d907030720b029021070360071481c225401e98a4076030841e42448100d500348003103032442c004280c1c44c981050180d0b60004c090914646070680302c080c0644000e000764043c100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 390673732 1250 390672482 390672493
    0x70501060f0315050613020c12040e04020406050102190f020d05030a1101110a120203090a020a14030c060a0c0611040f0e1605040501020303040609020406050901080a140f070b1c020c 80
    0xc00540034001d2549031420f5000700113904101c0300090944001041c064082a00400c13841c4002006004006c03281501c0f5070460b507190b40c0c3d02e40e081d8120310100c9007640700328a00300000419500200359440d0294104030f0880240010741e40e0004100c41c05a81070341c001e08440f0000c0c002407810002070402000603102c2c40204801556018203458443c541c80e5074142082c01840780740ca401c00030183e00b01c10500c0300581c50b96201c0d19000e240244420f006580095001800100d51098030000304403800150203036402c0401d50002c1c07114900c00c0301c00d0000041c0208030400302017a055840382c80081c440c0f405040c941581c4e002c03412102a1260014405406c40c007090021060080c801c40100d5082401d245041a00e4600040d481e0302008002034040d54443d50150219a104c0d03001e480548070041c1541c0d80355869086265445900040848003e15013030340240c40b440b80016501952412000140189400c20400300100d0700044c000100071200c8904a40600110340064040c0c01120f00c010003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 390674982 1250 390673732 390673739
    0xb0a0f0b1c02041a0d0e0714040f0e060c12160801090b0d02100512060f010203071e060f0f0b040902130c0e0901060c021f0f05070503070b01090b040605030105190e03070501060f 78
    0x4803401141b40c80c220398492001080020804010810070708821540003e26061b841c007950007800100146200d0750260104021849180310040e11442c171484043d1402030391012401d00d0742040c1600b10307070042410100108441405d5030031103c07200b0310140800302510220703808589507850111020b4041070001c604401c2d2002d9110f40b0590003103084032a80114054840081c2d04c900c5808406404180229044489420350b1100070080740c0d8462800c001c0c0721100003581004240b0601403032402030030604c03070206d40e1510707008002c030003a0000c6c129043e02c840d000088000f0310056039610140a0840d180003403503652000c04a0081c4420340f958070b440007091040000a002004200381140d18401079001d105900240d410900c510f6405c01603590a0581007151031070041d02d00c02442000044008103d56046170045800e00b403003901c041c08065118020542601c104403102040c1101c00c1d298843d5004c0b0540008101540c0002501d15080c03031500c0d07490a650898000c1c003420a01e484080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 390676232 1250 390674982 390675007
    0x801090e010221071b03080106080a05040327030206180301061508041b0806040510060b0c0a0206090406050901060302071203020705150a020d0e010b0a0f0b1c02041a 73
    0x40040400c40c000710300e0302109840071842e001c112503c0c042501d15020004a0301c034000d03140c0d140004603c00010f07140c4041480e00501a2109001c0e20001a4800002c6060810240100da0040758107440380c603040d01036035034652043c14400031002c0c000c4c0e008520000143e145d900c01003245441c401e40d1610203065080526080d5041139001444016044081280690340b0900903600158446400f44054182c2500c9e11541e02c0350f50050002c2d8050f00051008103c8006038000040c1107849040c0039955549808032440c1c00b8083c10501c2540000c000200140b0302400141080c01d0010000250181c90f00c0c04035007800c0c000d80041d80807a070300042c0c410a2004442a00e06076038028074080d450030240d9515551904807414002d6010320140300854088102901a100c65401c1c42204010b000800700c82c460180c0103e480443c01014190400b04140d0400002031041e44e4140080c903161411105219000d880a00719055031513509000120b034010560a2494488008050141e250200001507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 390677482 1250 390676232 390676241
    0x302070302031504031709010b0603070809071a04030809040e0102043012030c0c080a0315151704110301020f0307260a15030f0b2a2b060303080109 65
    0x3c800490300480104000240d2040c0c07041140b0021000c2c905071911140c940314090706d01ea542c1075501010200420207400d80c8588007901c5200c044080f2031019a89420409500c4c14425030f0b00c1001d0340420040c40403074103d0009001d2601c0180001510144001d4281d0032600540c018034541e00001040191243c011200f0b20381c60122051440c1d9001905d664014101c0030500400c000d1584135013624a0250003030501d00e08440d041400540d84100504009004001c0e03074215a529164040d07010814000d2140300c000480d8558030340900c1071914000722000414000c1c011100031a41e50030341c03800c58030280050301000c00c1c1d426440c1c1e240d0604100251640300b441c16034000940207003046070541681069210313000b1040c0707000018460016640e000901c0c006800203018401c402d0310000030040e410380d130f0600c182055030180c414050b01e4042c4200d801880079084028090034400581c0c02c00400c0800c0b4407038568400c40320201174401c40c07001d045e920b140d80140c2c04241ca9000401c4030310b649014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 390678732 1250 390677482 390677503
    0x120a050a0512040b090121050f060109140612040f1b1403160501030b0d06020319050601020a0c15260108101503080705120319060e0603060403121503030207030203 72
    0x42d1107042904000000c0304900032140c0890400c07e003100700411102c8044080724210384d07410000c0c03000d850b103410b070604080300c241e95030340c00113400400003c1ca00c91078a1303100290f0b410007458030345840d8050b400c0c00034122001d0002c0d1540c182208603500015621458600e641c8003800803101058500703103007c0300380c2d002d840c6000c0c0a90400d40c12482c6500422424405480c024200081c803038590001148864146900083c5140c0c400000e0180280e81c00c6185000412220800e22056680c6001240c840a5241004002c100001c01c24015844080c481c0e14800c100b030304c0c01d141d5010840242a644607400e0584c014590020401407041c00400e0021220380c3d0980f20080c040c1d803481813104402500c0c640b00280c0021804641d030310400505100c0005141501c0d0265601d03420030600020519031a1407480f0348440ca0111700150910801e402540701d101d0060103042299540d0324240c80c42d8030181d500c105065551002542c0c0304002c1d62610340a103000354001d1616504510505250441626 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 390679982 1250 390678732 390678763
    0x60f010504030f140106180504170c1203060d120f020c1002030f090a05040903090f090921181509091416020f06130203010515010210020702120a050a05 67
    0x20030301c04660400c800340b4403d580032411440c440001040c2900419080e08a803c0d600d01c00300700c0a400b0665608840c1c0a280100301e41d040d13803400084808214465070741c3c8901a42c21418071042c962501001a540c4900c0140c40c00040240c19959a082803228614003000300c2e1506043c82c7d040c1e80d0410140d010071030300b5100d05240c50442e602c0a9030713902a01182e43c81c1d10b0800074003010346032584995030f001001f024105000843c850329000d001d4507401c1c011107144000305000080d0718800b80c01404c48003904000d40c3c14070510b10008110b1448410304030071090100c100f01010b171140200c10300d8401000604003050704191094002060788440d0392010203100c0c10105100c103001c0302102c5175034100100f281d0f0400e2458228005070304204c10a440d040c452b00a9804200c0707680f0000b1803107645a0b100b00c000b0481d50741d80d0303480e4542c8406842e80300d60041e44030021040415811740c1c01891002d000511042000c4a8014040d00d44543c1020403605604095034200c20410200000c480c84808d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 390681232 1250 390679982 390679987
    0x1e050a0b01090f0b192114071a07020108060103050606131517160804021906031a030609070b25060b04060f18020304080d02160302240c03070224060f0105 68
    0x42014003d00e00b150242d0f0031060392070800d032942100340114500021f5842220b00c0c0700b402c2c0320b0210648440c1648559905000c17420142c071081400081107808103a81612881040e0302c0c0d40004400a140c020412f0341c2114042107032400300b668800c005001422040050407071081015002080e1845c41c450740d460b901c012a040c0030800e102143c014200300f556192465440d519800001c3d154110520404031104501c1000710303070103038190007181000c01d1703890b0104407104480003410f1780c80c042124240d449812003403080c440c10b03807644000c00d0103c142603a0481043c5007581d410810a04500b02111400d0f5103410b40e940906040c003c080041010041c407800c290f140040819403401d14441085a00e60b000001904101841c0141ca028005540c030454488070ba4104004400c0c02200082d0003500c6950003401d411820b04601b0340780f800c035000c140942030715042d011400e5900050440f00c1980103810b004184d006001a150041d603c0c540c1c10a1081d04104003800036445c0c11506160400104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 390682482 1250 390681232 390681259
    0x7031824020724140114010207051017090f0313180506030a0f03200307020a0803091302090f03011107060b0409210207030b0c0c0106090204031e050a0b01090f0b 71
    0xa03101150100914408921428089609004020015040c0004c00120540c002141c258071451403040c1e100c00a07000c5882e45504c910030042007001040c0700100042d4a805403400810075140856042020b0900315042118030550032400c507000800310f105017140d901010007405500003503c002460788035a04000b2800d11001098071500c20000251040401c1b01284081512900803018039810740450160110300080b84030b81c5907841280c0581c8070f00050203001c0741000010045a0f02410000d008070351072540c001e040030194002c0f480303c03a40300e9940440c43e00191820701904146041041e641980d80800c2e10300002100d41100d030781070007240f51004040c001034132212804208100c41c60f0105141c8514a0300724070301085034200801a05144080c4070311585108003500ca00d40018009011054030361100404a001d90711000e01060052400002e159440001200c9039600030001d4900000194440000411082e03004801c0140e660054140f5800079105140044a045030618a440e03007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 390683732 1250 390682482 390682493
    0x5071502010f1515111e0c0f032e0213062010051312050a09080606030307080a020313180c05181c050f030307180b040b03070318240207 60
    0x102c0e006040d0384524134048200380500404108146581d200125140843e0707800f0280c1c101003005e0507040340d600c6000260074691400b030103455106000940144100b03480041004001d0b000000b01104000c290352045c850300b9001d000a14046c00305992900c8580d1a24000400011a40c907004c5104081e202401002c0d560105c1c1e040c02d60001c0341000308198890909040e05003407882d00040080c402c480c0060111600f14001c0c0125103916109c0008543d643c184003501e810003190020781c0b5400401620000a61000c00381c0a01480c92040b60300308065401104801061a000000d228000030010318040285002c0c50b0f4841c0c01504e400c50030520300703001d000908010404520b00c50b000038031100303001c0c0d02100b00203007105401c40115520031188046443e00ea80c4150707103035000541c1025800c1d04101c803c101340c2d0100c9a101c007a140c41c1915151340e400454201503d04010140c4a1030500740300440d0680c030143d15401071090300640b2a200c00011100140066055080c0780180701c40c20100b0b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 390684982 1250 390683732 390683771
    0xb040506130504020c100506060a050d0903020705030a050a02040c0e010219050111070b0f010b030402030a060504061112180d0e1c14030301090b0f09040204150305071502010f 77
    0x29815500c440d160100d1540c1c03698108940d400c00c40d009407000c00c1c40103485130300150f20264261140410412501e51100b84402d40c447d1203007031004a401006034150180d040d41c80200824000d206a030304258542c000a030421620300000d8509034850031f1028194942803050b260849000c0c1000025840040000307512400c0e00804010b401350b804500c40140203007900091107181c88072404664034815450000d5004006442d4680c03145642c800215144900c0c108490040760010020a40d9024680d1a100a03180051017102c200d1348480d0541142c403e04009400d040354031201d000c169281031494280c2d42c4040b8420511150701103801614900d81040e9400b560b0712003610007040314210309000040580c041840180a410000101c0c0c240d810088081c506940c0c96079020320000224400b084900d000100300345500580c668080340043c503056008401c44d1003604100800b2564039101d59082850643c85580a1a0301c2800c132801f07164203224000c041c00c0000010440784001c40032015048 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 390686232 1250 390684982 390684989
    0x127020f0312040816080102040806010b030c07081b0f01060b0a0c060605030708030a08160806040c03140a05010f060503010e04110312041d13050c0f0409060e010e0c06040b04 77
    0x81100898449032601c05022031050480c0d41009107a56550301c1070080c0c5c3c2c445001c01c3c01001d0301d174009404074800070103000321760466000d280106256401e10001c04229400600403d280400c1040002d0000e0340c420b000d4008011000740b142040c00c1008503150814113000502da03c20703458403c050040718403003802d84122244c140b401c0c00c14108185807000040600d600000c1c0d151040c2e080015003d28000010300b455055990341d07600036102d0384050200d041000350804082083d04001404605142d800995007070081c4c074010a420382c4254000c1e21203002541e45007541600c900050080c55402d180da800100054600280743d985012812600b55070043c0000341000642c4411442503541000884c11010001d4655070782c0da50742c1c0842502c0d08000130005100300001c0000604140c400388040300455402c200502010b804d002c041000c90b80c03100340010b92207941e0b0242100441c40900c940c00901410358000503011040343c504520300410f400c110b5100c3d0004000034840c18031014292002c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 390687482 1250 390686232 390686239
    0x80a0c03080a02011503080a02120f0313020105090915030610080307260f0a0801050f10030b0a0f0803180d020a15020a0639020a0f08090907020708012702 68
    0x40b05580e29049015005109549520310401c2038040148a609001400026415004c8680390049581c4820850103401305c501c81d840000d00000d040e900712000a1440d02d40b051500030316081e400c20026010f02010386800580e9058140070520600b000c005068001e42c2a00d0110100f91600032020703901c0c0700b4000002c04406811880d0400050084a11040c0300991103400c1c6c2c070340c0740b10703200d062103a0840020f410001740c58400018a50410a200340c40f20340f0b0140460214550f00a02540a4122400400c0c1c01942c07040700051003001d01c0c101e5070007410810703018503074070300e5420220480c1103d002101849200c541d6002001a540c84841c90221010700700d000c2d054800720300041c0c0c20180c0110b8060b0040b8204200410810440d51040c020035901004400381060b800344a088540c0c20030300c40e03001603030100071410f0100b200e42c3d000f5485d00e4032800200b440c0c0070103100800c11346141910028056070110b1001d00168001b030185130740d812011034055407011640c400310f104100c070030380e0040d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 390688732 1250 390687482 390687487
    0xe041412070311010b060721031407052d0c07090b01090e040c15080108010e0c01080c16150203090601141011010236010c050615061905040302010801080a0c0308 71
    0x1c8040080d00040c00c0403e00a00e1b0300d80355041810000008103c0d00c2c0c042c031202e030340a4801c40303003a0f00a01c246121402c80d40305407941c540e0390030b100b80c0e165889840c1d10310103444182c290b08409081c00445d01100241c0310bc00039244c03421521914070340f402c160080010281480d410019036640a0500d00440b000707030720210503544803410001080300058201e40b514200c008202d102c5540c0220101c0d0423998580003c018031800805596140c0d10722900300b60001d61008080b900202075040a001e54543c10400c03411680966a21030380c000c00401d4039064440d07008020010001402c0c002140101102c910150180b0b60100c00501c10601103202038040c0242c5070002031280700254103958000320080d0480c41807003504404011401070002c5080e035041440b03a622425944200030184841b5070150040815032640c0d0f010b104460b04045040f0341015051010040c0740780401001200c4043c6512281d6a403800c3d40001840e40d101604001540d500282c0d01c0400142e00000390821242c0160b40c564 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 390689982 1250 390688732 390688757
    0x150a1e091e151d1605030405060f100503250f060507060908070206130f05150909091903091a0403050a0605180109050105011d0f0112050a0602040e0414120703 70
    0x500c0c602c0e81040310041c9030744605521203900783c0300c6a07015041d11424401d4090302c06004954601c81110020400d40081e404540710400181115400500c1508641c1000341c540e00445e1074a00f200700740d48140140301c2c40400540071040d1400d8040d007202e8910064150515070081d100340300342d0900815075640c4601c0801809182c134291412a40e00034145a40da00910122460f400320342d009000010710342560014862410b0402c0c2e010b404084140c0e2424081d030700d0100481e84800514246042c084c01d01d071319800c000000c00083c0c1e064483c0c1c448850582c240811a14040c07074880c950703608a041000203001144000840c000c001760720000108040e075078100442c05100f4120303540507d640c00c0c4110760080080c1900036905882000b1102603180358450200600701c14140d45002e15080b51000500c850040da010402041d03006030b040301c50b9564680d95010407688140c2c400c000c0e03241098280810844049442650180360000810044010135020741c010b2144142c000e052194011800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 390691232 1250 390689982 390690011
    0xc0703050d09051005010e060a140310020c0601090e0a031e02070305010609020d05100506070b1f0e010524030a0b031005010b07021207030c0e150a1e091e 68
    0x11660032050710014802100c0910780b941e41e452100712590400307802d210010503140c040040f100d101c1c0b10700800782100b0524201600c075044100d0704145405000e41101c1440d0385500f40000c0103500403d800a202640c5058141c0c000c44d80d9590710921503400c00e583c0300d00402d90121a04d81c0016001c41d070341e03240e045607180c1a4501a0643d000600650134482d0000c0d2005143d4041d18680c085c16006120503940c103528984404014000c00744d12072810311400000c1100c3c07000c41d650002e071a402107040020140250100e101d42c4d60701590007511041c006100c5824080da084040c0f207442813403048103000c5642d0902d0b040c04020710b05503006176180c1c82000665030401c4205100c00b4903090030041540c507820004d525a0100300b060b03020b8040344000c0b4001d000c1c005900811a078000340c4a104850620018001701900a0701110b40c89886144c080c106035901880c1c03e009018802030910350f80200c000b0312000c42e4090b40f185418a1611600c8086114003800a05090a20520001d01447e01504a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 390692482 1250 390691232 390691237
    0x20a0801110318010912030e0d0c12082a03070f0e030c1203040315020405010f051e03071e080403020c030d0206040b2d0a110426070506070b0604180203060c070305 72
    0x1e04100d46c00300301c040d05103425900c0302c2c0000e00b00606483c41a4a40042544c8004040c04003c009a40d100c1174082198403c0051640201c5451071415407002400d4a0303001008030704161145841000060050968110800590512240c18500200c082e00000a81c48582110107103000709901d05c4143e030081c81c180100d071b020795440080001500300156201d002900300e030113081c0c08242c00b08010103400c0d0251040e40c21701d00c2f150280350181c0c07420b001032034415040544448144407041c080b00724040c0c080004001410310690740d03000b082c5013904000345801d142400c0c0501035045044410502a4040ba000b075100c1c0c0c10290440503501c940440040c1c0040c4034407807d03400016815460f00041008602a00a0304020740910000d0b429001c10140d81c49184581081d825048100c01c511741260806414a0703011001600c600383d0b510400b213811544a200d007194540d40a6040019500d002d1154070a65249951a2003c0c0f400030b9000c681da444020f410301c0102d0001042da1410984180304 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 390693732 1250 390692482 390692501
    0x18060e010e01021c0c09080d051c0603060c02100510050108091504050f060105101205060415060201291804050304030f081207021507051602040216020a080111031801 73
    0x210365408101010340608480488104d404900388405020801d00c00d0107080141c0340c050340500700008601c1c3e4140c1d0164041400041c0c514036001043c40c03591000d200381300042d40156804078051107090002400c0c040e1041003041d26910303002c184412201034201080035a030742070801aa40740c480044041c5002e680500706250140c0b9002008100700703003c5010301c2e00d90140000c80d101662074008014180080100c2c0c4000525000d00d0b1403042d03c540d030800c87c1c1081000c1d000052249000481c003200580b25000b00300940e45940715214550030006040706100701111204510101510000780c1c141000007000d107920070b840002c10144601072040310011944482d0700100240da80c81c0502c05900403401c08081030300a0300001c2d5259002041c1295007052440c0c0302d10150340e82c9082655640c004041b00a04444030301c0140f030040c0c076144003c09600103000e40f1140220150f104205598440741c02ca09080d0341003030303211001d180e00c0f4008d4a030044411441d41c203583c160030340780c1c0d401440ba000c0c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 390694982 1250 390693732 390693761
    0x71d04110c031e071a070509030a061d0a0b01090b0111010e150603010917030928050c01050f032206090f02010306061805090703020f0309010212010918060e01 70
    0xe001110381c40000000d0040a205044401d40c050b00c00780c004040d8002d1407405083c040048203c94017605686a0159100e01c02e82069802e02981d400828a4105000c004842582d510110740c035221404041010144a042009001058140e6524010b00406100b00d5400540b40c0c9100c0405070f0045660104c04683d0074002c004000c1460f0103213903034502d0700c1411030289095202140c154101030241244507908070300b0050720f44400c071248158a510041240030303c1d0094001d80c120640d0082c018076289154074003c03c17010055410007906200540102c181403010030484007510b481d048082d00d50151207002c2e6003203c144280030f00b12042e26504c3c0014011440c04a50008209480403c04015030003a83d041007000e0310b8403016540d1303069903185020000d601406c03c12045c50005450355115409203000b5042111580d0f6140d81a00261408030980c2d402040904020600880e142e005011034541030141c3c41e82050354000c1c0680f0756402070829a103440c440b403030000c0d003500a02c03a07490056 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 390696232 1250 390694982 390694987
    0x7030905030f030a0f0b1e060912150105010302030108100509012711040204081902060702030105011710050601350a090b062403071e0c030215071d0411 67
    0x100c0c0e40554640c011a042e0210500d03140c0b003085d0008031407140c00003000c0060411610a02244440140d600380409111f0303000004001c4480340343c4501424000c1d03203103103034000d001c9031040d03a0014100d644140c0041303041510500040121107000100e040130780d0107416002410740c88003041d4a0240140c028010500030400640049801004d405565258000d4006003140c4042c0c070704101c240e20071442480b100d68400c40b80e401e1105c0724004c400b100f5a2008154618102a5502082c20348074240c0c02002a01d041443e1000c41d45028031450300c1c3c01c00084810400381c1340600003e010520385003600302042e44246105200f04110702608a64512203c84040c61490301110000150600c0c620803104900d10b800810b2603403c00d1048510b60b40304244400070007195850020a983d00000d000008212100c00403280d445250344028640d40c4865032001c448591900380a032a0400c030f03155481070003030300700104450142c1c08022054808801e20b070b00808521650b0004024010410000405a400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 390697482 1250 390696232 390696247
    0x7060617030703140f04560c0d050301151b03080703020d1506110703020a0e130803010b0a0314060d06050a140c0405100f2a0605072304031502030703090503 69
    0x4009040d40750701d0714054440d04014107500240d4419801d0340249003052841f50207549241149240a082e80805407429041504640a4501e084180d0248030b020074070000c0140304128007406406c4c41d9118900300080094004200111040c10a076406810440090040f5803514801d070110740900c1680ca07800d00080000c1c04a02a0140043c03041c180450381544c004e045800021440c242180c1d0000c241d0701b001da103030005100c801e4800424a0108420301443d003000501391801460180903040b8030941c5504900342c0c0902240c401c0c10300141202d1064042240540c0e90031a08030758182e03c06800704a985800d011040030380f0044506499408056040101d0f2110000103442124400c03500c42c00402c81d004004d440e0341e800100c6d41400261828009669003038603203500e440300c0c41c035003914624500d244c0e221801191400d80d0140700054800d020542c0f005c1d0004015241030325541d4200d49041d10390f65820032106c622400c420032013500400012021130190b84600c04094021064aa84113034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 390698732 1250 390697482 390697499
    0x190b030109111c1104020927150a0e04030c110d050f120f04170c041a0901090203070203091c0c030506041b05130509100608010207060617030703140f04 67
    0x380c8510702c0c1c0180c6154070070203d40c80128010f034942c01e40101c50360341c0d09241c0e1024030003e503010303070250350700b000000d101a03400c0031114240f403d003002440200c038880c0c01d00903400c40d10035034000b545d10300c1272511f948141b1132484413076042e0303030001e07454100505000c003680740c05001d1100304541282d10443c4080041d040c4880414000c1d50700142c4c1c41940d18183d01d602420445006401c0702c1100c0d601c061100b03001c0c0c05485400001380300c5081381207468940c00c4c0000074046d078816180b070b51610f8400030b500b80110b0811401c40b9000d0401100c0c19802d519016400039640d01482c0502c0340314a18501071481d0226402607207822054000c840c01c1c0c08940c076070900741c4da1140103403400ca8025000340b08a10b000d094003000c45003500e4009040000d18915400300201070000500444614020090101c1242600e4451035004054040015840d103c10781081c008450f590382c000180360040c00c8080c2e990f21408002c071401a98141042941d071304009800140314084c90314503502c5104001008540311f10b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 390699982 1250 390698732 390698753
    0xc070503060f04030e120703080f040311010305012102060d06080d110105090309010c03120c0e0117060607020904080c030703021e0c01120b270106081e190b030109 72
    0x104260100c84081d120b8a94107961818111000380004003804080e01d9a403814071000c400e002c40c0fa80c00c68040a859483e00305055000303451165145c0390005041040000011444030507001c00d00781003209616119030480f4107030b160342c00300300034802c1e0481d803200710b40c1c8030760030388442d40d10b47c071410440309445082c1c03103940e00700c1480b2910101d00d8a040600b40c1e017505002e0070f03110300c610101950401c51000015142900d41e80710072001c0c4500180e00050060881c070550020301901c0e52094a4108900b00240c1510790383c0c407840004419800070404161595000c903196036038161443c2c80c06940354240544c03240a83e00241c0040d0200141000c22305600280034000040c202034000c400001800305140d0710080e4010240c00f1134051480c01840c041d440d03001200d0424040c2c9890802011a0f40c10301515a414205544c0c418031100103003e21540170154540c024207048081b00b16000350201041c035440700400344402e9036420000c0148011071600700810340d540140080c0030440091400d101c00f813 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 390701232 1250 390699982 390699989
    0x150403060504060f050603030c0d0e042316020705060f0a09030b18011506120b030717010f060e100b09010c1406040203010507030c05071e050706020d0e061e0319020c07 74
    0x303805c09000c0740785460003000300c4164990902c010180c1406840c800d8a42c16003c01c003055200f075a034240c10810784103001c00344c01140501800443c80e0701c0e0618044058442140c4c841c0210352001e20203102c9a1103201c01c540118510705c80355501c417241c03002c04469555080c0c00007000c4030002d1040c0144440d0212101807104000310003030121484c03004e00241c0e4280d441c820400042d1002c00c40d01c3c0ca806081d40310f080c032804040c044c0c1c0c0545403a4414811101011904100d5aa44d9203080c60380f040101c0c031810018003200035218615080980c10070019004a0140c100c10920008205890b130f802044080c0034642e00c0401d49103500d02c00320303510352540000c8406038000d5003000001544070b446880381081c20780d2180c43c0c9504284690b1151408000c4000304c0c052980d400581407004103804214640041c4240e900400d400140100700501101866110724000d078801e110401148884206038a07109812900b0385860f0755a10002c50800c2844460a80200b440000d0f09010000042244400c3c4e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 390702482 1250 390701232 390701261
    0x40806041103030906091309060204180f09020a36020a110606091902071a040218010e01060324061116030f060506031e010b010e0103140615040306050406 68
    0x350714420040c940c50388102240980d00c200100100c1030070b46070001d41c8480c10b91810000265101c001c0d0b40c1c590881c1e00030307044013205c841c84400741d112000d914000d0045903daa09401d20001c0003941c0825846101802100800b0f513104041001c41211241211104c0c0c0080a03140440f00301c3c01500c0000b0742c029042800040c07505042d035100d281000850a010b071002802a031059640e69820303040d100c10162a80c00d030982c01300101d0010074162510a001c2031051f0900409078101881040181944c0c00060096000f60800402c1350a0b503c00085045070b00c075090101e15002c0c1c81c441160b1003d504102880400402c01d00032502c20780c040324510030502000d0884000700082c2c4403a10034800d080c88000c10b011078032060744002403101d4001d560040c1c4054101d03418400140040c1100790850080d40a06079550030801490f076a010309490310b08802030804010003558802005400c020040245004802006440c0c03400350039401110300071600301004100030b0805150440250074104091920b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 390703732 1250 390702482 390702503
    0x2120703032105092e06030b010807080601080c211501032a0306180b01170d0f0c170c0318040f15151701060201090201080a02190507051204080604 65
    0x2401c1c02d1502c20340d4000c440450080240100010207030303619868110b0028480c50000e000100450748030300030207010394400d1035650165030400395520b1030466954808602540040010070456602203002100e40314182d505401d80c1411075158425949059001d0b80c140c860318540c0c54481416a00c4941640d02c6425a2400300001e41910610f00c080072034480d6100005d1001040010720a0b03010094512160075001641d4070390303440303500d1100001d9200e99102140c44007098040c000c2030011400e065020f0504a11b0303080c0c070640c000c0c00011000c0c0002e26a204610444189991110949142500d64030480c4d6807401c2148403a813900360545181030146040064901440d2010300406c607440d2200c000e004040d44c41d1515641002c0c0b2428008000d01035040001403240f0740c194519400303000d80e60004110002030f40700040060f94000c0111030740c0d910610040e0100240c0203d034008042c1c1900d041c07134444900381003050a100c900030395851203507000500002c0ca034902103030f400d110794050089202d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 390704982 1250 390703732 390703787
    0xf18060910030e300c0709050c040305010b0102150c03061f0e010e15070b1005190e07031a01030f0e01091103070e070206010e13050114190207020a120212070303 71
    0x100000d0544d034048148515400007920300307104070043c001746465941101e0403240c1d212500000c560003903525a100a40001c1c06100340b190074021400d9190003880107142142038008a443c0c00744000d48400507009001020800e03981c0c5403115100401200f0301002e61030307044054007a0103801c0440d6200d000c40c40c41001c064661030064500d118046c4075960365468658280e0380e8100800300100a9007030711402d00c8000c2919101d20380849000b1000c928013100340d9080011075560b46000410040401d400e260860130345460ba5014030200031428200032070000c0b40720314a01e0140940002142c002e40c80c00f443c050600642c03079982d00203503a064081c0d50504c0d40360f9100480a0400b1100c40b800f50b070000f001049181e100300c281640c480e5007003144009050280d80e40e00d007560301009080381880d0703940d4288080800710440c10608806900401c502e0030310b084e4003140c2250700300e211342001082d609404405640324521444045102441614001500c034038000e803007240c1029014010070300a92112 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 390706232 1250 390704982 390705013
    0x3012c06060d0f0311030408060103110607051f0908120f0708131101121505030106120302120306040207020a08031206060721120e0c040e030f18060910030e 69
    0x100d029500103000c000c15082e1644800f9896280f10000300e08101c1c00c401144c140050900150002d0044800540782075459400c14280304c0d003022580900c115402c1096600184000440286842d0340d45880e01c2c821000200391070080c030081101500c02e4000145402800030364120051183c20603098008658a90130001c4641e000e0880d01801d80c0fa00c4082072001044950416141001d0145025200c5030000e1140070146da0500081c118803005014040c407582c5000e0040d4005800500b1425036084030b652002541c50040b0400b80c032440e10300002184003a1a10340455004540240500c0c211a603107110349075581c0d109100d1080110826404120139250020889035615003246540b5282560b2400708001001e850b8840742c20701c030240c04501c047d40e802d8064038608165060181501484200a001c251102100954100d8108200a080c400c14000031340e08842040b014006154488a000c19010311441d041e066105000065110010358075030071070303900110410240ca142c000e804101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 390707482 1250 390706232 390706243
    0x60c0b22060f061505090f091608190c08012c040206031305011b091509121a010e070e0901061e02071e050a06051206060702030c03012c 60
    0xe45032805624240041640e6400620191802c0c031030001e07859030749800c00c02100c201010355002081d00440c00010514100c916100b0080d810364a0000390303d080060300c10700710110703050308060040c0b00000c03490706c68040d50b80c038000020311a01049409541c4a000d82009024403440c0348114500c4c40310302c201d101403419919410118880b440c03071030700c42e5401c020b10b5800042c54023201036120507000d0b001c19001d004a4400c2000800c0b00800b002804400038220302c030742c3d0002e580c5005030012a12200d940302c0a00421a9076540c0080c0c10b000462820001000340c04030b0040704038a92000118503081c0c00d025403401901241c0f50134040005a20a108810809100307040c0440e4803400d5840902640c1480b0700040203540c811b4490150300c428420f500c2c0701180102040810b147c603410302060501c9c2c12404090803007030a01340d08100e0050400a40c244008210600965020900a0441d14108a81d9000d202e00500034003400303000a000e0512116840d4221100364410007007440d004102049 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 390708732 1250 390707482 390707521
    0x4170304031115070209040602090103111801081b0c010203010f0501030903020d030f061a030108190f020d03030e1f0b060414060702180703020a020d17071805030304060c0b 76
    0x1a04201030100c03003c200622003c3c101c0344804580800c01d00c3c0041e50307440e000c107110700d100e075200585a0032258001411105041c0f02100d5000d01005070710310b1074403e2403815040d50700c00d00c2c09800c031f17549040080000d6060003550003400b40d00451240000003040d00654161030041c041d1600c4d85941d000110151215100050301507004103002540e45031013500100ca5615000c50042001a81d40d065201411320800400408810100051000302d00c140595500c88500d00c07000340045185448210100110140c024803405c4600806401c0500a81000f0343c0241080141d034141d0b603202c1d0b1f80250000c0c135500c600c8803051920315103120b580741c518240c400f030383c0c20204030003178101001d818005107620030380080e17a001001c9070441c2001c01441c00c002e0701c154001da40c056111a20440c3c040d10304203414420350140150030300d0100001c00d400d4841a4041040d14100d01181024114400c542645800060305800005000f0600603003002980050900c01e013a00ba505a903407003100500d0f04140e96 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 390709982 1250 390708732 390708743
    0x60609090a1a10121109101b08031e01062f0a0f0812160c0813051e090c03090c060a030b0d060605031c080c070309080a06020417030403 60
    0x801251418900d6806094480b0441e241040410203050000f0040459010300e000011076910001c0f103244181d000e181c2c821800c50341c05500340f464100001c2c0c0c80002264105c0c00b0000e1b000c42c1c490021071001e8140040741d81200c41303103070341e0705040031301c402180b43c160b95032102090701000004e480c0384120141184007444ca0b01c40c5078501da041c1414002500e10103481e00641c03245414240114001e003821110491161781d802d5910b140120108801d03220007804c680072040d026440001c41070b048501c60078156404403050340e40e41c2d00018a00c001c000315401c42030b040070707020104274803402081ca002001c900c02103e01001658994514109600c0101c8081e105600700d165402501d04080014042801c9141008180e120010004c82c401c0c01442c0d20039140e40b43c450f0801c00890809010a004002d03190300c0155070b0340c00c0041d0182070840081e01000d480100011080b051501c1120300300d018040100503a404580c8600303014002e50005d0080c019810300346010841c205400008490450ba84003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 390711232 1250 390709982 390709999
    0xb0c060f090613230607080106110604020907050d0e0601050102010e0a11010f0207080d0c031205070c030e03010b1314070c12140c01050a0905010b060406081501030b03060c0909060609 81
    0x401d510f48211020304421203540c40108031100e542080e201c0c60340080d4840c1030082146140c0618020700185060f44131005021010f09004100100800d889522a1b019940100c15132200702c030484080c8103000c501c034942ca1034906900c0191002040d03090403120240d0092001110400c5402c0e200c2180301001031a24000c41e4000c040c3d54054040d0303a111021900560300d000d6039614030030303062050100a4000140c0c0a80d01c202c20940c011041c030b15280d00e13400c0c0c2003019180c8014082c10601c90000080c007805402d00200001c1c0d5801d4211030743d41d80000c1c1405001c07040200c3d15001612251500121000107000022029442482d889100d41d800901d0381404121941050390300900000c64000003200802040c00e10301ea09009550082e44844000030b04550b041c00c10600b100d1000031001c4c8552020001000740381d90101c400368000741d956440144070b10031103005074010410307060402e070140102403c2204107001c01d0080c20002030300717940e01c0e41d1079501d4408014551040c418880e80c0020304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 390712482 1250 390711232 390711241
    0x11a0f0603191b02071d0705120402240702120a030203070803060d1202060601090906080a0822060525080703030207020a03050f0708010b0f0630010b0c060f0906 71
    0x100d0590105090582c80c0c00545000c02c900d48440008081c01d140c1c0c05a80729900030820000400524007190500031311603019800d040c48024071a03c102400303000700444803c041415980c9080340040d100c0342c091012001c102401c0e0520300e5a404c001c4e0160b22a0a0700c04d000b641240e0086a03c1c4141581940554500001552000780c03541000e002d680d00008402815800a080043c0e05021086942c008207468034081e00010848005900000d2803030342001d40400c091a4009000340c00c166002c00550303119454460400c0c260700c0c0040c82803111044810000070b470140c2080040280a000602070785500c200f201351161104001d84c402044030000b04401030129120398041c281042c030041071400c103540c0d070f52207131461702c252044551030740d800407601004000d10034071426171034000030744414a200c3d8505000590034055a202c0d6070403504450140d04402403013000c80503443c250340c0860b424950b1101441540c0f03410041d4034844d03c1c425140400c4100703413a060714510810401d17004103920ba46 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 390713732 1250 390712482 390712501
    0x18240610050702031209130605030d0c06090c12030f02070803120a0e060f090f06100603050903040801051302010f0507020a05060a0e0405090f01140403020a11010c02030a05011a0f0603 81
    0x38880045040050901000005039400d1254000100480340da064031080c0b00400c00c00520300840c1259125403400c40100003948000c29a110b002c4103074109040c030a1441c0c2808070113442219402018000c04a40214480800101d000e031702e580a070b0f850f03051041c00700800386d1380d6840c03500400390300b9401802180d0140883c2030200364044088003001c158100b185502da0720f44070b41a13800000c3d02c0d41800c100000c000c130800071000c040b810071004191609258103050410344440c040e0f4800c16803070f5000540c002c0801c00454000303260b2180204554074144891419880240b00100d0009074807601c8014060300c1102a00c02d01e90300180310804e403d103441c003003001c2c542c84071031124140300040d9640c0c0002d9445128080c46940014050b2518404c114002d5007100e1170301950203101e801700c10602c0082540081c1c81c01c06035a00880b004900484000180c44140c19480003d506206150b80c3d001002010b40140400d001080103102556041c13200700324240e412503030216000441800000c2c002e14 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 390714982 1250 390713732 390713749
    0xf13110607060b121e01020403030509360610050406080a1a06070308011502030c06070309061b0c0302060106020304060e1c02040908040303090605030c03070f17182406 74
    0xd21840000503490b200c000444c0401035503800c1c06000d41c01c808012619900d440e8010200070343c6040085140c1429650003400700c0c01141c0955019040400c10362a0a441d00c00c490135070030440c4241758203415404074400729495400c451030390051803461312508105010710240d034140c580a496501450303480b0700c00007000385401c40c1c0a4464090b0f1502c1254243c40f141c0091403110700a13561040150306000b903c200164510504104542c000c10800c6840c001c08141240c0003c00c2d454040780001c03240c200381001e02449403034400422848512004a5500084203200081c400c0c1c080c0d40300c070780c0c4c0e803041681c80303000b14821140130400590342c040c040c2c58568030f10400c40c640010b01d00840301c520740220b4100c586103801216901c40020f028006d15410143e01c00040525140203455880d0440d00b000403030002401c2c2905012895000204581c014001c1c40d41c01008401688110310380807500041c50f18140510007140c1c000c01042c40e05000000d0708064441e140740450b202e0944a85081c4106503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 390716232 1250 390714982 390714997
    0x3020105090d06020c0c0a0b0702010804080c100231030b010b2503091a03192a0806041109030304060f050d1b12050402220b040203040b0f131106 64
    0x842c4036000000058494405007100380d40c030900034100e41e808038080c4070f03401d00305070402000301509104a00c0140c3e445840c2d00c0d40180c0c4201011303140e0b0368070810320f450202080381c4458190f0010800c20400b28121800354621040c0f04555642003581208c44082c0e03c109000c041d114050380c4005120301852040105011901d44403010510185054404894401907400702e0009114600802100603d10001141d030200519403a00c1d6040c43c02d00700c0c08541d1301c203c501c210580c507501489a00740703103032034141d14107104001e0f0304c2c1885c54448001032030350008544e1540300d40e1405002d0b580301c82c241010f035052094003800540c039040c00c03c0000c0c0d6031003c034000c0d180c00f00401080790301409441030041441000c005c600d480c40c2c00030040d0024066000724034001c22078624120400001d603507070200b01c1c00c581140081110b41420b80303100c90005408011000d40c0c1090002003400704101804c03a90034450010704480392815103034501c04503203104889101070f00c50b0741e6503241d86041c0d107030031001080301c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 390717482 1250 390716232 390716239
    0x8070f050909010b0307080f0c180a0305030a0e03010e01091a06120a0609031e021b0a2c010501050a08041716080c010c0302040503101a0312040614090a0302010509 72
    0x900040c1d07400034070480380903000030002100c08403e00600c140c0141100e50461491142110145004850302c0e0b05401180c101d0040d0225245400c01180c4440000001442d00030050b41c0e620b00030102c02400c850381644001b8060340c6800b006031917048061141854495226215202038546081c5206c1403100160000380e006044c280d1161034800100629041e00348549030114010308a0b09000e022460680b040f1041200c10304120a5071560115402907114000e0465050700c84000f004101c0003911038107c0045010300a0800002c0c901000ea604191041809480e03103581c0c0313071801140d20b801a14051404249101c0100f800611440f40c001c00803005241c0860074500750802c00c58401c40c10354001e941c40100010444440c050a01651095148a040552810745002c001c0f1342c0e22540d03104ca00304001d5440c00090190301c8903091b42c80f00010020222501081003075058a0242d00610812010640401d9a0790740c52070701c034040e9800440003c052248540c80c5400554076540300c10b011503070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 390718732 1250 390717482 390717487
    0x40f1e0f15050702062109070e040c030f0303113c0909090109050604110418200d05100501320904060b100216090501080618070e0c0a1e08070f05 64
    0x844240d6460400721b600c0c202125280380c103280c445a0304100481d000310814a40c10404c202c04a80c622461000302c940c0592603000040041c02c2c2100103003684140010f02d114002810200301107401c0c00b0030545030349a00c2c002c00007050382e101060048102c0c80b0320800340707606128500792440d10590040e8001c55100010519103001d54545040c558112401c032196103004440880904181c400c04048269400c2d400d03c0c69a02e60301c40f003c03011865090800c4640c014207801c0490749911010140702540b10041340d05000d00c0c00040d001800c02400f6081c10295100200000180c1c0034a4103002400e10408141d02048001c0a00000c4007000b00b080e107210b80c41d6046c1d6010750b00c48040100784071841364090960506160320001207507080d42d01800f641c0b410030f0014400e41c940400c80c10380000a0301c1505021301c1d05010350074200205c45c3d100d1002e00e2086410040366040d10001455130031843d0ba1007003d510441f40150640c1015002d940c40001d86405c0010491030045a090316580f240b41846030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 390719982 1250 390718732 390718747
    0x10239190603140106080702060c0c0c03070f090b06030103200d08120a060801090308060d030207080d0302030f070c03082e0b04150302070b0f070302040f1e0f1505070206 75
    0x880082540c1c1c07018002a68440110551980605240c1d026040c42e2510303120f50300b80410029030318400541041c0c2528030001e01d65102c01020420071040c49009000d48454036628082c84100c0308040c480d00d810a170402c003568040b03142800c21241030f00c3c1d0200217481c00101031022000c0c81204400c086410081607107100000c545030340c000d080c40035040c07803880b0003500e40112264150703a840d500042e00e60f0304091480b80001e03004449968080307000d540100c03040f2141c1c1012484c0c40d82d1a803120149000701022031941a50507002507100303d000d140000315940f2100360840703c0d0020340a025000483d45404a00b907101100c1c10701c00c4100e503601405c010500c000c0c0c105881d0390310581c8803501420300028104048480022500c41700b45050a0071070420104c0e031610303451154001c0983c81240101c000140c4030710f00950544000d040034011714481180c42c3ca0b0782c9050b41c2038443c0f0f194070700c050b00000050152031409010f400c0d00c0c4003d20524850900400580e01e17a04085000c0341d0011040c48101c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 390721232 1250 390719982 390720019
    0x5130f051e010209040c030b0a05061e0a090311062a0c060c010906060e0402060301051011070312112128090e011509060c031107030c05010239 63
    0x780711980d01c60000503607900d0071004200807100b105442c00d05042c102100011307295144103406040301d0f410b84265540300c20000b0607001070304da0500c030741240d0380000c0b44036403c5507800440fa5060320301ca4140c8003090300341042080350381d001d03140c0c15184e18104100e40c255000243c80c0c40301c2c80f00e01080e040301c0500c4003510018503150440c005a1070f0703ea54401c2004244240c0d0b015020080c03c816116802034101600820b54134401402054024043c402c11140c540784152640c25402e10240c00b525503183d00ca1820008000000401c20b00142074a1240e032082c040c045071400c090341c0070721010583c8060b03045420180d5002039090036030030132503040520701e070200036242d10b0b068101e581e031898181403e000300703a83c0c2020182c101d0700780e045817105001080c81d08118240262245410121070040c414503044071002c140c003450030b509002e0114000200300b14100f5074402e540c4240c094404d68a6420012032031041041d10352580c1c8a158034a54181d05078500c000d208841024001d1015140400c511 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 390722482 1250 390721232 390721273
    0x30c1b06040308071206030203070e06031204030f1709011d0303070f0c0e01170a0305130b0a080a05072a0204150f0504060f0b0d0e10140610020105130f05 68
    0xb640840c07840e508201646900041c06010900408010022107045401007903071070303096006206a00031040003092950790304000d420180c101c00d000700e5a8a036140d141c01219401c0ea6a03044900010301800580c801c0807c0d41aa60401010b07500c000d0169103100661501001070941c454040c0010001c1002150300d60101908050081181d1001c00f03180101c29040b4003030503405048003212088400401060120ba101c4403250545081d07502c03010860a0440600560381c000003008000060796209150000c3d10305114441c0f102d4108802da50b9840d045c0c0d07418508004000d155040c10b550300c01070000a4981c03a0b092800500001041c0b0000c00c0d0b131010040e0107400c040300c0182000020002850301d0702504001e405416481d91000703240006ea01c0560041c072101da011540c88003043c4003426000c02501e9071607188008103100c0124422441c2c07445c0309040c0c0389075002d5400350021042d114014040e941c01140031a08040c070b01c3c030315a162035030006c01700c01d0300300c9182c040c1c9444071801e42400280c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 390723732 1250 390722482 390722491
    0x905040f06030209060f0109030b0705041212031119030906110c0f100c0801061b05010c051b03030c040e040c050405160206100501021906020d0f0504021212030c1b06 73
    0x40006800b429401041401040202068480c059000c0f8503009641d000041d04101c9070b000d04441025100c00500781d400d07004a0300000700c00304041100c1028415068150a800080c54408110102c90103a07580c3c4075200300c4042e070ba1008198010002e080d88031354030170050140114000603440c072002c0d400b0f04540d84810105442c50f0b1102010100c0c07280144080440800114420080b0200a03003001d4100b903414132504081c008074919096075030155038144203c4550200c000c2151541d070706000303005074000031200060075100e503040104152002003240d0142461303010180c146850b00040b000e8410b0010300c1110052002040001ca503150b03801400e0046020130709985144561490091510100500b881d900c8941c00200700910307600401c0c40c2c070004441104001d01d0010b1420701c031000c1c1c410710380a070103810316007001061a00225401f1a0080b0320840318400941e104840703135036a800303a043e29072883303940030400f15640204c0f0200038841c000419458008a22125003030702d080503004c03907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 390724982 1250 390723732 390723761
    0x9060d0b0a03051f02070b04020904020d05010e1b0a08030301030f0c03080d020417061003230f03030109060e0f01060318051f0b040c0c0b070e0d05160501210b01090504 74
    0x11060110409104080214841c61504605154032901c4204c40447c02034006801168000c0100b015519080313411850a90400c00911450b591440e42c01d41c1c0700100e0006030f09d100703801c80c104070544c0741551280d81203a85d408020b50442c3d0850b180d4217203c0101a40c100d980c224116030000c0026802000b0780780c9185000b02c01610350703140200304c660316110840300303281640101d0208103140403000e12100c1503e402c10345003211010f00c0c1880c40000100040001441d129004d65111034800000c0154140d48030800f061104540c6c1d64803071140307100c05907402d1141d600020010700c861446640801c4100ca46d940c3c5514404209488090070402411036246207038064610080540c0082c0c041c40d21246000c0c3d404009000c4090b40041c0840a030110041c4465130442c04995824400c840f42d46050000800342d0041c4445440d03d5580c520303441440048000d003d00d000101c960084d01c60b0800d4220aca4500b44c44001d201154500400402c1440c9041c8491a030000c42d564446100b202d1000070f290 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 390726232 1250 390724982 390724993
    0xb06030a1b060201050703090b07030507050c160f050103060308190203040f0902071a01050f01050306030106080706090603061401050315150307110f060721060e0a091a0601020309060d0b0a0305 85
    0x20b0300900b501c070020300400a040c01c0101a80c0000d58414900c2c1d8040704a140015003921100000c844c1441600d001c0e80c120720848202210030a441c2004104a90700c428030309420f290740740015000d4550b1444042d220301020300c01c00c140b1603000300c2240342500061060741e01c2c00b030b203c0d4096032680410741c00031402d8650100ba80c038200600c00700491170b5001412000e071a80c0d0326010002c1d4070340c4d503c40f88040c108400803001c9416610250041c1028007901c205980d00c19895a0000f01020181d01c12180043e041160000707500c2808914154070142c1a0760301c1d491a907030203c080380001600c00c85d0a8000c00107602c140c020b5590346000c1d60290140340d4602210100080f00c60703183c40c90010740100d80e0341015062100c41500040c210003110042d450003c580903013007c4a1005082c50740c4010000c02100f070410100b00321650101d60180e201d02c004d80c49440c07208604003c000300842d040c60241e8030410040070f1920f0550b002d40726092100802140c81c46410003c180c0e0600c86610449482c0d001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 390727482 1250 390726232 390726239
    0x901150c1211010b121009060b0402030a0b010210091e021906031d0c1e06070501020d0c08090d09051e0d0812060603131e02030d0e010806010203040806040b06030a1b 73
    0x28044c50701582c1c0216800064500fa595200c2c0d04c841e4260610b10b00b403a69010394104000b42c641100c0c1241c5001001192286408400031002e40220402c403801801420b4002c2407807025841803407005a04040c4242d800d40014021100c609c0e0f4140060303034081d01c800c407071850426440884202404040d6001324400d05101c00440c030405003004460107980151502d041c0307940380c0b403003800025400e242c0d004041c11514800b242c181d00c168000134100354000900c0401880131a0003005403054503555050340c3c0e83d11300001c0d1780c1703607038402d80e20320002030050104008510301110710140b07542600320382407405041040020020300d03038103100311200c2d00c0c04195000d500c10581507141e03000c0307030a540c0790703240d4501208402d0124042c00c0004043c4031385011480c124900c80624002e107c0e5002c3c1c2200ca6800080034081c025050005900c0d002442c20000181c0d0340d4404000e40b0101c98280c0020180742e1900c0d52144032065000340101d40500c5011142c0011800350740710030502001d00c3d00d503004550306 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 390728732 1250 390727482 390727517
    0x1c0609030f090b030f07050f0406230405060901111e0a0b280f02040306050711010506010201021606050405210a020c060301180504050703081b0601090b0901150c12 72
    0xa10001903001d0004412040010450310f80c2100e0703105e120f03140b00e02e80d183e850700019a40707801070201c040013544000c6004151945c2182e01c11009a02c024112140140303600c088480d43c1c403071800b4440d0841c105212841c0d095015a481c0400c5d40b01e484150313002b200180c102c901244c0701120760f00d420340d4000800c45041c00154120103030458a0040c202c0030403c01ca0300c0b80c0d118241e10b02900c2c4d445a5907145a02c1d00d140d400d50540c1d020795800501803200c1e00301440020000c060700c40d0615541c1d480e01020441e41e40c01442181e24000f4001c020800c0c075041e0391134440c01820020002e03202ca01802c0041101c2212201c5e880c4002c01489136115102c1e0364109009250099107500d03d4080e80003040180b00038482600f50074003001e8000c80104144c1e0700c0c0d141460500b9507582c0001c0c200c82c40403c10003440d5180c403850301c014945071411030310b10380c0e40e030300c405000c3c1c0307400d440015000a0146c0040c416050000d8140d4202d1510741414034044c4003d9441603c00c0c16610710310400031314140111441c0d0303034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 390729982 1250 390728732 390728747
    0xa060302090c1306181a03150103090c0920040e040b0109050103050307141504050309040b091003080739080307050d0809070b04090905012304020f1c060903 69
    0x321070072026410440344410610140200d40104d006105124050a400f00d0060800c14094480390401900701c0c06460804000d6070020396219100c0e24800310402d06952181c414070f2001f42c1c1000b400701101d031410b51920010020030300d03040c0741c0000410b0540101c11000c0010f00040c010314235443c420745400e0404001016060f0000c0d900c1505000042011502c00003d564440350840282501c80841d01c801074a0800400c101d1100703264481e0420040c00800300103054580001c0c1c0301404100400c400300400c10700e0490341880c080360160010700120751004054807500e0721a6008403500314030b000803041d040b43e110910b580c40603e85043d4031500c1c0d02c200c46240061000070011400d041140e548c0075100c1e5441406281000081e00c005900701100b000a0002400709801c15a626500c0b1f0000002400d540702c4103441c40e60812602180b80848148503000e45100c915249005452766420021481512030030254028061b801090304520300c0c608007001103106820004401425142c09030511 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 390731232 1250 390729982 390729991
    0x905120a02090124030b0126060120070b09040b1306030c050a080d08101a0316080402011707020a060212090708030a05040501080405030706020a02100501050301020f070f030c06050a06030209 84
    0x2031350119254290001d80018101c401c2c0c5040c18045012400500122081210858a2203e00b00d20315031740c02640c503020380130f903009400c2a81c50900c2540e1080b40d00124803041620040c4643c0f045030100700c504445c5c005089601402007001c00e80840303102c001000c400c55446d80c4418266a14000c000304040b52200c0d4004002c169031481010746000c68468481c5003480381c01d0203000003100040e000000c40a041c10103801c40c10040480500c000c2d01030011600308844400402840d5401c2c210380c00d00460b2064825a4160f4401d65400307181c029525018001600010940c03040850190008080d030015141200b506213580a46180c03124800d031800d01c107940040f5150300304114180e03400340c1c041c0446013902d6003802c0c10542034840b40b07000d5146102c1c03e90003908040c40425110051603020a140048041c0705030144a01e0343c07150101801c03071040240c0c3d5050a0000c11170140040d00040d00c918480d0b0203810036007134074140d64a48400345d410890b107119100750750704000e108500d481681346400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 390732482 1250 390731232 390731249
    0x3070f170105240c0d021e0705010c0515040f030e090402060306040c050913020306090c0406020a12230c120c0d0e061b010c08010b030f070f0905120a020901 69
    0x50500d00411200c001106000300c0780100000c05241c0304440003c03580e200a02100e8041941d100f940b803400755210303d1007034203200060050564280c05154034552050300140e0328400380030414904030056800d0a101c000c100c3e50750241012801c0c40400741d55800744038078025030301100b0603089450014110000f100b080c03845400710341c041c0809a110002581c0e48804280e030005602179079008141c2c0c03e805207140c2c1c3c503401400c0000c10300300e20070240c015500809040c7c60241940c4c0b5480394000b810f01860281d48016802100380c0c50108003030900400c0803034014281040d1424901c4001d1081e049903050040c1d2114001401c180c00820400c45525070080088865050402c982201c1ea15040c075140503000700710070794440c1c10b06596500200c80041c2003a081e0007501d100404a014080d185101081c800300303c1010000941002c40404c4901c80c03515400b0360803240e81c84180588020248420f10010404800004030b15515001d450050000a060003081100e280340704000503c941600a103c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 390733732 1250 390732482 390732497
    0x30210050c0715020a0606092f0f1303020603100608070212122809020a060804030e011413060305150f1302030c07060c0f030c1107030305091f0503070f 67
    0x700003000c91040300352407111080303c50364480240b04914200c12581c000d42a01d1910f040000d031403000e0b42c0302803244604da00110034030b070b80d03501104000c0c800c01c0c845400005004221404035246450300410f0382c11f02c00c00c0d03003142407a00e036004110036410450304c032620403101c903005203c01031700711001c1603101d541880113090070040007a010700c2030301400301c02c1009070040502188808074038a0170f07040200c1d9040d0031040c420300c2d10b0034404090721148900780c1c01003603044000700300c1c6d521846055100d01c0d015240c000c0d00c208400011122a0582d02c1c0c1808040b6040c040004000c880e240414014201c6580115040c2803d41c05c01c85080a0411054440e802c501c40420316510b500d08044a80100614016160f558a08124901b0f2203207883c001c0c0854074140310307031250642000140181e00000c3d03808020b4801c0100c01901d842d00e520a4030300e0b050380505000c0000030b02c070b00000d0119802c003824440d1403c0142c0c00c01007040a8854242c400720b040441000401948221905010103d0b85400304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 390734982 1250 390733732 390733747
    0xb04030e060d1404140c180c092d150f0c0f060a0e07050619120e1515040e03090d060b09090a030f08010e01060305090a05070906060909020f0f0c0f0d0903021005 71
    0x80710802c4917040d0001987c0c0c1d040c0020000600b0300c0643c0c0d80c2c01130191400481001000349c0740c1a11078030159499103000300c0c000b0a10300303003006c444034208258260849841c080d8446414101d58115402c580603601c10103030718901c150403c0c400302d402440760010100d9102026200c060426030705801890049505020612084030340d115011400700701c500b0700001030310f0101c5c50380c0c1c0544500c0b60742c0c503a18881c490b043c241c01d00c6c0125445215042400e000c2c0003040d2000b08110540d1050720031400e59a000380648003031458041106441d485c4070700030000d04004681d001c03c0b010307071040713030b00402c41d4104040000603d80c1144808103261500e10b000369503981021a85100c5105c1805900205a502c1e00000c1c07040008105084529801004a1711322a9070340500c0740c060462070050310002075054500141032802070080d40c22021242601500349101002030380c6186d044050071409030300c5000644080580c0901013003403084045d64801481c18258010b0042c102e8040e0000400c000d020001d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 390736232 1250 390734982 390734989
    0x11a030f161103040602030a030f0b0109030204050a0906061401030c02030304030207121403070c08010e0307081215090115140a0c170c01020c0a120305040b04030e060d1404140c 78
    0x141d8071503010240640140010001118107036100015900c02e444005404103820750000083c21441c94180d8061040785c05502d0701c03200b511080e4880501040b80034100b40b005280541202d41d110780600000124801191514425114680d1090903e05200243c100603941e02d07028000c1c014140e0b000440c81c42c1404c3da4020350303e134214030503c0c07050420341089404002d009203483d01040902811283c41d0b0300c003400c12001e05000c510506100b9860301c01103400550002c13003901c16542e001180582882502400459252001001000c846640e0300d02111265944640c03d800307002040c01381c4a200714000800341200300d80140d040d5041c03400b8058400c5907036101c080c07050300d240d211890304603035035111142d201940940c5c0d1010030154000b00f41080300000000b0f5500816020303c18080280403035940c00d40844005445c00b600c140070b060300040100303000b00317140200060040d1495203003012030011081100d816810003900b800a90041c807080c4100d010b8190018a41e0102502d503110000002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 390737482 1250 390736232 390736261
    0x903010213031103010501060503130203070b0d021207140a2a030801090b06030c090f030a2310090503091c080d0c170601020607030b06190207080d030c0206010902070f1505011a03 79
    0x71402192200394120bc215202807107100001c2219016503a180d030303491145100a50000401c05c1e14940040d000205414440e191242c2000c0003030901510b45101128110703000c0800c6541d64100750b23801003801569040041d0014003245c02135403603050b1075050802050079a0707140d00d81315118003814007e002180f00b50b9012203000340421100320f880d003d420804a42001c048000103401724640c18a0803400f101c0b040a00380c050840c05090b00c881d2100314180c007048904060014005500507c81c2c0441d41c00d2002900740c80100320304003070520440030360b51840541d0110716050f0301c1c80d80314214410007941080420310040403d0500b54942c2c9083d400007560307100e00400c941d0030140c80c0c10b404006030300d52001722180c40c402410203220702c0c0710042c00a07545210911400d44d1740d1003010b0710406990310900c84c2c98018201e07603020b084c1e20391800340004003070340084c1c0c0150741140b00300980c10700003541c3d900c190600b9513848002244941c5000a508900c4000340310000103a10204204210300902e60305 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 390738732 1250 390737482 390737491
    0x2010e0304050d05010b0409111206190509391f0806040603020616030e03060412080a1e0c090f05030c090405070e0910060f12060f020903010213031103010501060503 73
    0x1102e09035030369542002801b400d5140c0440b40c00c585415810000e02007110791010303201006446d10000d0143e41c02d1034580d2010115a0f8101104000180240c60344c1c0e1900b2040c0c000f555030080702d0b4600d03403804860110112902180c8c41807021090551840c401c20209013500c2801151040c00d05040344000502101031303110510708011502c00082c80d0707540c41d0750000c00915005056030307498036443d0310110114942460140d000c504600b04811843c900050900e03c030750750051084000c030700c1ea0b40e010340d02800058240000540c07101c400380e0240e1302c601d100f41c07650070140d00040b54501c100c68010b0071200705500f1000d61054503040074132550710005070326410083e090702e0200751591503043c041c0c01d000d219040701c1000030012081c03040907040019005800361420740200301c819075881c002c0e0f070400424800d00a0550b03040c0d5420000c40c0b5650710000525401e04800b52400b407125000078220703400030707079154291042c61505005014140008402c5100c0990080000d035047c4000034016010090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 390739982 1250 390738732 390738739
    0x30c13060c0f260a0806041d0a03080604270b06040c051213050d1805040921270f080c0108040f060f2307080f0705090109052e02010e030405 62
    0x80c6042c1100751801c1011070425440e03d400381c5844551000401095041c1c498038401c504100807440c031010b0140b0300e0481e00f00030a006001e11945660203541599000340603640c4203682d90040350340200039803101c141e40e0b00300b820401d450446c20b2400300701203075010b400c89015516000c2e004240c6500402103407400702415000440079615980c4c0710141e80c0d0000fa00a00c10300a101c6840c00c0c450308003d60030001c205200700786201e540c43e101488110b404511000d02400425105140f2004049031700d011904d20900d00892446c040d802072004902034100070f03c90081c0b401a0400016805904080150460b00c000c3c1c0088014080000d100c50400340000d0002ea000941410400115500c0100c1d0100d01641c01c1c4030800c8540c20303d10b0440c8090807521400f80c14180021741d4a4411120244a04081c50384040c850701c803d9003c035929040031404905100700042c02003001d50f60040304003422000c08031504a65042d403c04141104054032280003076a05040508801c0a4044107440a490095 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 390741232 1250 390739982 390740003
    0xf0d080601110a020406080708101a0114090406080d020c060327030415020615010c05060a0209040209090108010506010e03120702040203270d021c050d0e03040b030c13060c0f 77
    0xb024641842080c0500070b51152a1460000d00c2000214000d0300b100c03641c8003502c442e01c1c0707188076641c19110354131800000f4211010700529250300868008684181c01c5001c1e90034441d8410104040314165000300307180307502440300d0074100c580c1007010503401e203003d55086003107040c1400c51950291070313003c003412211801001024241d40c10400c1d90000c0143c0ba200c501c040e5040304000e521440c050300c004542d43e5006d43c00c0811540500210807903140e20000070400c03580e600100000075045a110164002e0702007100d01303d0359481401c4903018005040000a240c100303e0000362840600d12a0580243c00090b1703205100d08000d825551f20580548015a59540726142880311000d00440c620500700b0b00100100e00d42c0340021000501c0c0d88035000c80d100240e00d400320500200070b969600000071001c000440302e8031300c4c9401c60480052844110385c01e080e280c9802c2880c40d041102c4544060303d0204424080020102ca6040108601c1c10000c1c100005520354070f5280a02010240620129 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 390742482 1250 390741232 390741257
    0xa0f03120c0c0f06090501320c0a08090f03010e060f06040f0c020d08010b0f0d0207110307031a0112080f0a0e060a120509073602120103050f0d080601 66
    0x141c00007104072a400300e01e0121064445141001d0800103004640000c0d02e0110003080c6540a048400240a40c8c4020f00010059050002540e01600b00c1e850038103802c01d201000d807800013009814002441062181e03101d0150380140205801d008580c24480d0781080c0d500381e1001c4011448941044603007548002c1d0341d85d00d102182c040c2007480c48a480940c6032028030928182c1c0031502c00514070003980c0b480070700d0740da0381d0014082c0c0c0207440d06030801407420059458078920f0b9a0041c502680704407a0950f400450340d00183c24441907a100340c509c948141000400400045036060140c81908880300c4441200e888144030780c01950701e40940040700050382000303580502d89c4900a03030401024582e543c01420001004d4080441ca40d0b0744541c10f02c000b04404200104142056803595008014102d40100c2c2108014243c81c400c041004006031940c0f44000050004103000d14103818036241c0780d451450404c0ca800e02920099500d1327088204404100c42d131101441d07030000824a4500c40b040030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 390743732 1250 390742482 390742487
    0x30e0d0807050604060b1003050105150c0717010b0a0f12022106070e030d020606030c04021e041401090902070201120c090b070f060c02031c0f020d0e060402040b0a0f0312 75
    0xc05001401c140f280070308010811801d6000455185010f548850100e00d18410680546d8002e020340b80e4451040c804035500201b90700f009d88241e1500400321641c7e0b950301c0b00d001c40c146c00c0b034215091081e5110f400310705c02410125208001032030b040098a014a190000001303400d10b0207800244103005c0340101c103110114a407a201310b0105074600f52101c03800c0004015180c40808480e1502030b0003201f01c1050307800d00110b40c0f00d100341c1024015200661590040100a51009000382e0482032000c10b040d951094a50140000e4800b4000508090704400c4c00586884956480811401e00410900c001030343d220491140038280c5020206801d86681c85c1683c6080182e04074506109000c6000d40034406d4148051940d180504001c02030940300480c100e03200e02c110b4400c0140083c400b010340101d680c660344207010202d04000700604042c0804101e0046d50300391080e0b0201a03125000f1f100c00e51425120f282410401180c14600251502107400c00e00b0116102c0a400900143c404891207030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 390744982 1250 390743732 390743737
    0x20030114010e0621070e060903191a01031401290d060b19031a0705190c12020a0303050703021303082a06041e03080f0612030c010b011b030e0d08 64
    0x102c0160a865138000084e40c900b02d0214100d80d80d40018103810352000d450f00f44281220200c1310090b0180000340e10001c0a64102504200c08840c41d0800b005c0c0e0720403030800365500c24007943c402c184618107401141e10302420744400000d910000c101d441103c03c0220840111250300c400c06039030aa0266296080020080851108040d003010418103642c0e02031000102d081e0030743c2e02c140090084800c040c907141c840e20303004645510110740300700014400d62040c40080c0d143d503620b6140903940354009a440081e881c61100c0000c016034042d46280d02010b0301802241d0f80207103030385011030400c0c107101034846003a90305101c050304101c00003510103d14440e40b040100c10f84107081c06004025407144ca950b80cac0324402c640907201f079100c89640c15a5810001c0d050004503030190b946403043d844a030b08501c07400f100a402150712a18081003c0c0c00b1000c18006020701c40405030000170001d1b403910001d40300101940020b001000315150b4a000a40c014602d001a20425561101c820385c19107480016072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 390746232 1250 390744982 390744997
    0x9040b04151802011b0b2206020406030515030c060306150c0303070509030d050301180c030e100b1002060129071a0106090603140714070204020d20030114010e06 71
    0x280d04000c07801030032400448000c0d40300c600c00e90b5170b0155030380d004200c22030184110b80014070014000000c650282155403014034400c0b1846c03c440c0340d4002d81d41d15002243c0c0264000c5000c039860341c040206501c0e400c0d440c0c01c844002030f40604202404100003455034072000340518411801100d40541d815190000d680e03083c810201185e80e41e00308420040c00c16049008002e102e445a50030718002ca0b80303c3d00c1503a04942c0701808506816241404110150403120744040806544201031440b03805e007007081100040800c24006403402001c0706100f10001001c41c440c081d513100e40010400d20140c2c0301500304401c10002c1400503c40c00c54040704162180c0704014004c0415150b091080e034942903aa18100c801c9500c03420001940c8000c2541680c002a604010443d00040081c079818003c100550841c0054503205203846519030001d02203030400300880340903540e50900300c20b070754010301d081e03600745410302e000c9604540c0340c100446d83c80700d0b420006030b0411045030700002183e142e407400d6514a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 390747482 1250 390746232 390746273
    0x90308031e0405030c070807080307080d180303050f061014130e01080f100b030309010c030219050c09060409050316110a06080a0b01140a030510031209031208010509040b04 76
    0x5041038100303e503407600304050044960042c400c0020314103000280f080111070f01030700030313604000854031803a2054204001d4070102c0b5888401c17864840a00d844004c140512039200060f00e810640c0c5904c9070148001c1c86140030b1107649000c8041143c0011142200780ca20151070b076a184002100d138800108c40740d000720500303060340002258560007c00c0d0791207a41d8a40003160400000c6810b000e058407108410b058140d00100125081540724240160f0400c0c024011658180c0f100d450700010a03142c40c805565940221411228606d0f01c5160150007420031601440f603006640c84181c0c0742c0c8256008914000300410b01c20b01000892200b00d121144e0040c4400d80e07090b540c8402a01a00c0c040b14400416840c101c030b10316441d802180d490805081c1035442c6030030300080303c030160010070000c2c14044814500d01c034008001046c060883e40520a165903241c440d61662409900c5003003091072400a1000c0b1070018025501d81182080c1e000307812111901030703600c96052030040401e20a102404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 390748732 1250 390747482 390747541
    0x60207030c050f0607090303050307090e01080304090623090a0905010c050403022403180a050d09030b0f01180507050904151d040b070c020312033409030803 69
    0x9050300494024010303400b40b820748140c25a0804110b484480440f00400450040082400882d219001544e03108000e41000701d034203502c8500c00c06202609074031000103a800003400b80100480c0d802803800603c0110050307012529103400c191902100fa440550140d80c40c0000110024550b400203111a500000204009205102c00a005074440c0c04241c0c01f400700d456040320421001e46550010001070100c60382152580101403056542c405000c50251043c00c200710007188080c00740d460404055296282558511303d0405c0704d6040c010500d50002c20410010001e01c02905100340c500807503107100180c560b8994500f600c09000d51b02c07075260803d00d40b51003000340d00342a2400c0403c2d06d4211101e01c00342003000c0801d03000d80350f003103030000e28a400020104050601486103410300c184018255084981c44500181d00d60300110703031030408240c1d00104482c1d4400e0a40041807140d88008e110080b000003528054507561140c0301c01000b0320320000c0041c6281d01d040c0e00500c000e00d0300200806 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 390749982 1250 390748732 390748747
    0xd0c051501030c150c02090f07030b130204030b06150a0c0309030b2701091104051b131e080a0b07030b19030b070905011d041103010806070e03060919020d0602 70
    0x503d401014041c03c500c0b49080944c19075082d0184154500b00d90740205110140e60316405001586103010300050280b40c2c84520f040d480759503003015041488800c000042c0c4940c614140707650141c030050700d458000c41200a460704000c049604441440c011170030301e035824510f00d20301214018010340c0080c041c1403040080c40307401d03088501100744086100d80d410581260041445007280c01904006029124003a441c850604080d0403065000090b91040d40b40140b00405628581c0d1044034006ca000300d02c250144812800e5801c8041b490540d00415000300d8280030543e5501c1840d0744019000e80814000181454807035000414074180c0a00002d0254642e01c1001d14140960f0004a40075009100042c0202c1d01c144002011074205075504030703501c0081303031840049080c5035151603005502d403100d0171720320b851610003103000b8a0120014185450100c030000d0074581c81c044154429042030301400005c0e81e00203030245019201804469000000d40300050340e804491a008189500118110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 390751232 1250 390749982 390749993
    0x120302010207050c0301111e070b0f0906090607050406030e0f120c120702030d1407050105070f08130c0b0a020c0409030206040c0f0803030a020906120c040504060b09030d0c05150103 80
    0x5140b02d030b100308103d5004101d118109800e90f0460707071403a80e00440a00c01e981c420204820300540103400e16045078900a0940c80f440384045044800e0081c5000d91414801700b40e600f0007070240c0c02011180582801d00305900000d0181c4290701c200010503444882070303800342c40140401c84c0c01382c501d6011528100401803201c64580c200e10449012801105216290181c60342c2c126030145900501402ca03405191401b552101210305091108050500035000022001d202e258000d56007603c403400c603401111402019113100509260100301035491050020707a01d031480380280c50101d40f80c651507030010388003249031807584040e0340e40c86811b02410405168011440c2c80c0a58007504042003d01d4a82c000388039082c0b0203202c2e4501720f600400000b00b01e0460307940031740f0755034800425851a10752445040e001290f4160f0307804141301400a020419850948101802421050300080c200204400002c0d1a1072249842409024041d0000b404000c030030300480b100e014648800c8509943c590405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 390752482 1250 390751232 390751237
    0x12040b1e190c031a0103050912031009050a0c0c110126010611070e06061e0d05060108062e020a05030d0501050a0f03080a0c08090d0530040303181203020102 69
    0x300074100d10781112149040e03c01e000ba80041183c0000451104660000450003040010044000c50183e01c0310700100d0340c00e510003140102c0405502c10b203403a00b016500d1003124805441000140e00e04460040c440e50000c500240660b0045c010000103601311005035500c0c5c4020110001c0000d42c0c050100d02c1800c201140c40c1030b6001540c40403041519441c03865a01d94941c003c1c1c140d20001480080c01d1868440b00409460248444c480c4660130136006081c0700f50003640b1484140e50301e170410410503580c40540c0755408101201c1c0885100781e0200d610015010740c0d4010070011b145510403031032141c000c000c41519185d000c0c0459545600c11804040144020300665100e040c0c40540003800b07a000c02242419240c110803298070381a400c400c1516503260940080b29201070070300003c92283c1d1580b040d044401d0291001d054031442c43d40d180310200300ca08140300e440501c0019103201c0b1810325030581d81076039032504060101000900b4004141c0c039403513120180c88010b06030f00004051b8103401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 390753732 1250 390752482 390752521
    0x80606040e13030905060d051027050a09121d041a01030e0a020603131718010c0f0602040602010f050105040e1f0603120917120d0213030204050705130b12040b1e 71
    0x9d0b9218094480980001c4169418001c2c480c0b100c40c94085800c054660380b11a03040080c2500014005d01690342c0c030011044407881d840041040c0250450020249104500741048100c80c2040710a0702032510443c4c56076000d04260405540d6002a60110410400f0072595a0014005500c03817a00c04480c2103410481c03c01107e2003150800725002e09004142a00c100700d19142e4020041032400d401142e419140c40e01c15190664402d02d40340c0410b1300307480108060903140d400491400c40f52864041504c8043e8011400340b1700e0000c1900f400000440ca59198040c03100d010081c8031241c511001c064240c503040030b0102c500342d000150141782c0094507002110079007031981c4091101c2c55801c071386605040e0f03080c1c41880020031102d42500c48503802003000d1300c6810041f074541c5840c0d0300803d084440480d01c0340d01154002176101840561451031400400340390350f0032480c100d034116003900050b0300a8030041c0200348600205994030060040003984e40e8030140d1b5141a0324201b20a5540901c0484 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 390754982 1250 390753732 390753751
    0x7051005030403020a06180c090203060406080a12050307051b0604020f030a030c14010905030f0918070c020904231c11070302090411060415080606040e13030905060d05 74
    0x14162001805401600e20598168020301006160b544074007014084114001c070080310040c80000000b60700021001c040c1c0002180140c0703901e0302501b44400c4a0840d042600c0031b41c440442040003c6035900e0900102d030035450000d840791210f07a42511240600c0c0c01d0315614000850444521400c0064450b200d240225410a104107400042c99103070101218050300281e01c0054100200d00280304002c0840680c0000052200c1395485050843e00400ba0038100040300080c80e01c0d00b4504001900f842c900d130502c040341c031401c03c0c40001e803540e00c0030075000780070751030041c005424050030111800016490301c0380400120b140c5482d098480c2d01503400f191600001841031030744544180034084c6001e021500900a00342160204590f568000b40b080b24102c503500000c0000780c5800d80503100416070071800c040c03200340c00907001d40750340c0c070051a580c0103400610042103a410007244881d004000e200e0180d00c0000581400c4588541076080300f42c00c420700198620884c1c02e05e502103442009880d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 390756232 1250 390754982 390754999
    0xa03020a0b06040e03030a091e0c0f0501030e0304210f06051009020a12090c05031c02010c0206160f020f0111040509090304050f060c010b270609040804090c0e120705 73
    0x1c20810040301c5003040b040c201170f481400010440a416842040705500a09118803c20400717207840490601d0035404036407011032503004112003911031000f0009088242800d0213400c52600307425503a4061031103050b041503941504030644000410510003840c4d00034030f4206a07901241000c00c041c001c2941d03803d5105581c00400a2a100316100313031820a031480c0c1e240d4041003829088840605180d02c2d00342c0d0020b8185034002102d586c1002100c1083d018106041c0f070b56030b10030310f000e800c4407100303440d440079904040204800311514aa92149050450034103071540fa510b00707000c03031606102c201070320307050740c609101d403000481c02602810032900102c0b0403052903070710078490030749a0080748101904200f0300004a44289001009820070f01e48200000640ea607544001652030080c99119602c0c14000c600d401101d180c0035815940d0100b416202c05219040503555030308144501e10075444425034540e03c080d29140b040030074131501c100041c102c2403580a0401c0843d1918068070482e446010030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 390757482 1250 390756232 390756241
    0xc100c0c23012a060b0405100302011101091106070f060e03040f0503031903110c070e04060e0d0e1e0a0803040906050108010e0f0703060e070206041b0b1801030603050a03020a0b 78
    0x3d0203100120481400c000500c0001d40b09100c0d0402c281c0d264111003183d15604c2d119905c0e116807203020b00c5020350080c0000341c0361841c0000342003000e84000189069042c01c27907000c042401c10150780d80303070306040c0d034016550485030502c01401403100d64010a410308284080c0c1d0b10281c008060000d0302d43d80900300c0b41e026656800c040c0e4900c80c4241c0282c1f8080e0304c1c0b1004901d903000f544100e2030f000b50340c03030000d1411000000690400b5895049808210410002d0005001c034900c240340040039030714002e00e6556861b16000e00019000d000240c450f01a9100070501b802c3c020b814211003000203450354050588818034252203401c68040d4005480ca03242002a1940c80752042c2c41c1251026a04404e454032000c2c0d02200b1500300404000905031103620003d0842d0002c02d0303240c450398a9502400942c203040c90041080d501442080917902c1c1c0412041c0f1480c2c02e500111000c1186454002016008403001038020308035a80c000780441c02010310200a242cbc0125481e88280e10901c40e0801c640c2d078 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 390758732 1250 390757482 390757487
    0xc0203010e0a05060c070b0a0c090503150f0a02070b0a05060604051c020306090706080c0c01061809110103061526010609150f0f03020d06171e010506030c100c0c2301 73
    0xd00b1b40b028104040c2c0d00041081e000e10383d888410819150f02c0c1c0070758050745030b0006c68540815140340c0215504610104040c0c21b5510004540068880209526140968a413002200c0d03000c0c201c415840da941d0081107441d42d41c1030072200100300c090981c0054941c60039800d203800407403c0e000e034003a0041c20009000650086041416105c041c1c4956407181c44a030350f000e4854000140c6805290b595600108850161640099003092140e4001c030b07203485075190100041100324541418141010018040000000895a11442c00b4030381096400400003d1020384d0031813200c2111080c404030b00218195600402480a440b0064a000252400c12008848469526a81400117405c02e5415a0914401e0300102100040904041034107600c5d0164100b5481072072014041e141d0008000e0440075005c0c0851782d60800020008010624206000c01d85a0740c0c401e5500d0301c6540301c0c102414059001e4a5180c40c4203400c40003155079a901c618080d0a440d1940d005068000c48165001c0c0440d131 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 390759982 1250 390758732 390758737
    0x1030b0a030506070e2b120203071502090414010f12020307030218040c060c020901060305070e0a1403010e03090604031103032709060d050703060c051e0924090f010c0203010e0a05060c 81
    0xc0160701d091b800c26200e80303401c1400d80000200303d0450100700000750129860754020703440c28600749070044e610a000c20400c802c40d01900d041111800403503004001002d1030341d6194040301d60600701150743e01000c1c80043d08210071600025030105401c0c02e003c0740340c0f071042240ba11540c4039030303600e0840c681c0703803041941c010181b450025406510b1034014003107903110b80c100f1604108182090312100e60141c0003d043c2511680155102e0a4030b149514050710702401402c00440507000a98074004080b40499039078801c2e400042c26154800742b040c501504d0410490310202d182e0140a020801d01c01141c0700b00c1c001d041c50b0300f4031601280700030400500e06000c50300d09440e444002070009901d55601c0174080d00da02c0d000301d0144642400200700b06400e2060b0621174068940b0683d80c1d81c0790140c01c02c0b6000d01203205c869002c5401e003a8034040b6070403020031124050390440740d2900050101004071560308000200075055400d1142c200b88140000424203441c0d8810020389a15560343c04041800c1d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 390761232 1250 390759982 390760039
    0x418060203100e1b0912060906100f0605040b0f0403080409060513020c06070807091a1306020601030f030809030f0705030d060e10231002060106030501090902010c0201030b0a030506070e 82
    0x3204c1c40c4801c4446207844400411540c0006403010241d084441601800e095007142c4c2803409070804410004150b4030804140060881000200426402d10342c0c020194052070044003d241c50000d8081460011a01683d0086034440d00065070f454a504c12070001e00464401d040c00340001050004d40d0401c14000d031100345590742c0090901c2d50310200100c1d00720402510910a000346524080f965800341e003814940c08980392035950b969080b01c00b144150049a520034011904450014800141c3e440c140560b080d1b058a40f20145445500c10783d410b621410744038080c4007c000030400e0030481c000c0301820030440e101d2001c02009503a0f58dc200d6a03090102c61100c41007403480d0040c0091400c40242c2000b8601806c810842e00c082040411003440b000d40c0780c41c007d0390004c8010020168140182400342402d4482408a01c100e54000b910f03144020f00002e0500d42c5030740101a2540b6500c200c0c100464100040310f410303050101000d405103a6043c0400e000d00e1030310201d120744034460526140203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 390762482 1250 390761232 390761251
    0x260105090d0201152d150c0b01080f0a0825210311041701020708180a0f0f360507120504050c06091f0206010509010e150f0418060203100e 61
    0x43e80c170300a0000a8550459407451100c2c0350388100845c1c240a00d6040880030034442d22507180003101030074200c040703c0e816407100d103250707200031499818204086071405030960302140c3ca980310240c1170740c00d50780d04d07801810940701d04105901100a10011a100b41c602c08200e0580700500b403140001201030303400f000e1100f05401c008100c200b042e1072207a4680780306091500001400c0081560f1642c07042d90004101c0d070743e001c1c0c880390360460a2400c0e0200c10001c0994800007440706191062020004071184a6040c00e40c10480203150651540110f4031000c00c02d07004215415010b05d0062401084142e40c000c0c0003a15614231000c5038012445060700070740d000401042680c0340c0303904000656011a004d15007042222015080658861850f45000030f4030b40c015000c80e42c108014803951240c16404004018900e1042c8503400880d1051004038443c00c1e00d00e011054031003008207018002c000c0c101713a0110152110b8100740605903025501601c44150003407012540c2d0741c9250308200065507107400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 390763732 1250 390762482 390762509
    0x90d3f080601120e1917030906070503040c081608010f27050c060c06010302040b0108070f1404050a0303030605040c051314010e040203130501110a0207260105090d020115 75
    0x40e40d0701580e580c03120783c100b940021440c03181ea81401820b01ca2030030040080c11152003018002c20a030000300c01170314800352069a06501e4000d00c450b5071154064826802c1c0000040440d06100201c03181e20054407805049030b4030607060700e0302e18413001042e10814145510b030106079001c1c0480c50140244600ca8426015100072580050b40007985034510308035010f1044440381445511440301501c549030501f00900481c0d89140144015118140580360410960404105045422640b990f01105961500e10b0505028140b4040035100d1504103e900001880000040640c5504082e0a5401c152014406400104010f664a0060b801d00d0071602d071214909002e010411b14810000c0201450004840b28035080810101d030300650388803640228030f0442030f00703019003401141060032502407651f01d0a040c40030001c1d1540344034010302190610000c1400d258182d962074424003900d1b080c00030001170900e10400da90b210041032400c00035500f4400100e03d440348001c000c50031500240900703070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 390764982 1250 390763732 390763741
    0xb1801140c09041a03011d0105090111041205010e010e030c010e0c061e04030c0609050423010510020a0623180c010c0201020a060608030a180b070602090d3f08 70
    0x10b0003030380c101030200d21480d0040703104c5968240185075202c1c813000b00802c41002140c00d00c3c0d003034076401401d510302c5030304003880010841c11000c211003c65003030030200e0b044e000701d030710744180581080c00e00c100c440e6007080c5074001c03892404030080000040c0b0740000c0007020310000d40c254880302a25040c50b8446010b1290020391070102e02450848181042e4051a25480342d80b61400c0030b0309a0040d200080d40b804081c00541014400c000420400b50005486000c4001c5d20300c01c0034905000301c601400500e021b090400b4000c0089401c4690312000600011240b50b16040c514a081c540107441c00c0c0c01d020104113004087c01024200403a4800903010f102031000054842d514000c030f0483c118800c2c800d0b4400030070414810200a001131001035903542d0444080206805071f500c0d800c01d104004520104600c101c400103d8501c2940540e0258807240e02100180414911090184c1032210f108444000403a10560601d5580e005852070f01c8007102051201022a02036441507007c42c2c003580118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 390766232 1250 390764982 390764989
    0x11508010e0f04020d0b01060507030801270e030d0609140117030712170901050702010c09050303030f0402040b090106020c0301051302091b0d0f0605030c0909030a0c0f0b1801140c09 80
    0x10350b100340085c05007003811540355582c900d199004d80c0f02400150001c50030100301039112280c01c3c01017007455060304100a800b034164210001102c58017004d95a902075002410783c0510a6525100d04160100451580c4241d404080c0c9640340205960266a9002140c0c4a1014550440000c0110f009608001c030540e2040a04904400c0241c1031184d034032031501501d03207000e20b180c1c8202403040010403035040c44080a400d407550443c4120500400700b005102c09e450000981c0e130b102000b41022081ca85070340c0081402807030130003075194204100305d001042d110b8000a903a03120000a60003045540d07102004c0342c25020341307540000e50010903900410085222a440c540b40700596401c01072411402404034000c8440851004d1015522501d00f0451407034217000806001d6016164500c2504d0700c91001500d82c40303602510030601c811406800c1c2401800380703030080c0441d486100e005441c04d14420b03240050207218884640c81d800c22b41e040607403542268911b4001c5e400b000e9400d0814140c04c040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 390767482 1250 390766232 390766261
    0x8030f070f020a0306020d090605160c03031d01290d170a120213030b0a0203010b0f0d0902090a0b0f0f130c0e1f2c01030905010b0d0b011508010e 64
    0x5990000710f03800080301003a010710041c08801e01e5524005100d40301c514083c81600d1000b07045080b00400900d9845415805c24410b5654a0741342c07400149030301c00c075609603d03030703290b0110001000d40c60a11004100c0200c189030501c05000d40c54581221000b080400142d41c00c0700710003c21401c080c402c40303200100c2c0c0d0009003d8210b030394141810300b010200102800ca8011014104031845900020400c0c4800c2d00c05803600494108025803842d814504d280c03005200d40c1c174130565148070014030200c041d0503c2e4090b104203540144020002e050030200c40d0042c100b8850094811310400500101502c1d1a03400359141d664060b00c4c01a10100718401240140300b2300c00440c00340050440014042c1e135031070348000c1c5403e000d0b00d81d070002482380f4000240b4010110f14030780005011454401c2245a841500320803102007440d0225102c1d84515010780905401c0c600c0325080307040fa00d014010810021415410703a11000b040884e924518542160100e40c04c1c42182620f11000e0085443c0e107115816 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 390768732 1250 390767482 390767513
    0x9030b04022701092307080c0403050d050a0f0201180b06010e090c0307031409070509060612090c010f0201060303080a1a06040b0d0507030b0f041508100609050108030f07 75
    0xb4260400c607061440b42c6010021001820744211448010711113260144a0f07081a0b5135805005c01d10600070980b04094041c020b40080c0034081c2040008480080100481d00a541d200f4296003105800010280036600594008408104896800020b00f0710501c80c0080090080c0185280751491b611041ca00050190509042009401e15040c10341c80310118503015810f904501d550781c1c60107000007000c44005046011800ca0980e0900c040058002003070420340c2d0040b90b10110340e4030781100054191040603c290f03032507842c50041041d0500042000000031a0a03204d507000c0c2103207a0400c07402c072411030000038003250403400070541c0701d9442ea201c10000400072110303810120004000440d43e4220740c1c4246070040f000200000424098098540c1005050806002c00c164640000d2034014481409500440d0780b0641a00d030070308204a03002c010150031007501c40c245900c0c2a4080a4110741c001d01c0003445c140710002aa00c034000045a1083e036104400e6402c1c01c1c5260380312036501c4031024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 390769982 1250 390768732 390768739
    0xb012a030e01030b03030a090f0f120b0901090b010e070e09010b0f160c0b030106120501030809190302100903051507090513020d06180513021e031c0801081c09030b0402 74
    0x3084d11915072003c10040c401d45506440740d8091602c2c05006c0d19100f081a0000400c00300104400c000c400104240710b06020360101c004500d42d82c2e0a2015401020040d034040d00350114503000203004d04200080e0b0f030042c6003903070303411601710200420701060b240300b2b03c9082c1954000304903880401d4084030150014980c00f6118112801076a101c01d0b02c050281c0d008054080c10000040050607041000340102d00c414003c20f101661540c0c540600354001c03001c140780690301e19110601402845038024015650003002807410703004028000700804101d0000311681e1194501c8405030241128159204141a40d58819251300b0b10060040c0c5038207001051840507000d001c9000e01c18a42d004040162203412920038030040d40814176000d48001034000c52400038001900c00158540001c07030b80000b843c0c21807511741711a4860100b490000030300c803103041d060030895100d086154801c040e41d04032131110040395030301155283e044a00c3c015403484180401c660000820004464580c520707070090004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 390771232 1250 390769982 390769991
    0x609100c05160803071101140601030b060c120c1002090f21060a1a0d020a05011103161112070609090f1118010207080c0d02061602060d0b012a030e0103 67
    0x9945050748480b038001d0440d50600b0100800c00460f074045004a1185000f034028400e0051a81e510fa03404400604258105502c540c001811a120f490072160501e030300c08115074a003002c0b4031030807105411000c1542002d021b6425400c0040f4024003e441c1040d90082906659000003400c1040380e1002085a410701c140300c120142500405001ea18407030031802c50045100e40f10605840084610131164901c50f201038801c2c40d0158440e00100c505981c020309141109080e142c02d0740e880c50080d40f400d0443d4000001c230500420014002400084601381d0300c5080e84014600c87e651121503500030080000c8101108100c121999046031641c0144004001030250f02c0b000514103035801100310054140240308100d819581c108044001807402030702a048a4103e24000f4818240580d8080e01c11070000c1148400080704104070740718180c0c010401e46d901d44d002d940d02000362501440c014040b4034148100c00102c11a0b984000303684070480000b0000c030810f550241c54800d0343c2900d507030415686 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 390772482 1250 390771232 390771247
    0x207080c211222050607111e060f04140a08130902030f0c0702040f0c050a0807030b010509060c07080d11010b01050304020d290709030c140a0608130209010312030e0609100c05 77
    0x500885014280326640c1303212887c060480f0300d10b043d514840c1c540d2880b0501084a1900c5404030b49950403182c4040120382c0f507141c84c280400141e012402044881c0144810002041311000080c2050300c440e0042c0fa80c0c03141e4914001c0101d010481d800441001414002603509000300c0041140601c0107100061401c2064003040444180b10b401e00080303040051072a1800350032034141580b1400900d400c1c0800040d090009100d4040d44904034001d90b13010400c1354402d8414404070014103015000c0350600e02e0071040042c061501d00740b2401055103080b004200f2548541e0440340724540181c070071650f0710020341c1d404031030108694080e04076000c82c1d90190070825502d0381e10f40c061103a6a441c0da50550960402280c05491036010341803020110031042d0300d9468003030700c0c001295440e003003030203071690f07105101c0011941c6d084000354865580700001c03041015a21002490703695a550800c200c00741d084065036181c006499a11041c0d011166003604040b55800240c007800346441e00c1c50506d5a03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 390773732 1250 390772482 390772493
    0xe04030522081501080d050a0323040c060804031b060b0d0602090103150f06050a0207080a0c14030d0905100210050f070f0816080a0207080c211222 65
    0x481148500e00340060001006000002c201412080700070f001000c400d945003104c401e42d1040c2e080920018841c01041c103048650290740010090080008542032000090b0b145044406013110115040362500c1d001084052090020f148100e42c5a110201607010051080b030701184002c10480f40c0513203828810140e80c032070150003038140e0b105190140c0c1394048000098280c9092590300004a02c01c604108800c105d0410076000302c030420300340103a403601d10074405c81c1000004d41108000340300b169460b00410541c24030b550100c6180704901c000e800403d00c200750b2a81040740142001032141c42060007e40341c804000d07408440c0a004803102c20300c5c190b071144142c401c00c68507080294480f004102001d900880e1102400b2240e182400c1585080074010083e900040001c408102c0c0d040c0025000d120642d0488080a410814054035048198829540c503008066109400d907240a25101c1c0340d02000305484072115a81000030742c0d0f560b1001c40d201e2981c104007083d0b1010350040b40b02d00202d603 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 390774982 1250 390773732 390773767
    0x1605030411131112040309090b15070204090b0f07180b1b0106270e0c06030f0a110d09030e0301020421020301021b150114090403031a060d1e150e040305 67
    0xd60780f8080034443c0342c07604010b4903d80148d44206502414210304080c56684c061803000c40702e4130323190400e07242c04c10303400840d0042802000c010403800c240c50034049031183c01e90030944901c0300355075011754020070007042018080075442100c2c5201000d2105800d6800d415124203c0216504000030b000ba0f42c0b42e8100d040386040022058115400501c4060b0300c003042d0084000144140e4020120030b030404002c03a0036071100070190f09454000601103a500e00c6160801d5441443c41500c094507040300c0c00240000701903840d8220086180c00e0103004441c10180213407000c07148030b882c004400019803102c0c241440780f28502241e00d55800c0286d628440c0b0314442c0381c0410042400182404124a41182031411041e0810380b01c0c941018607004103a9140d10b240c42d84241c0c145800305d05810b0740340341041c0c2e4002d6403450707992096011030f0343c800342e525a070b02402d4041c5d10005400b055803074050441d02101c00f8180c00301ca0074003556506005588030804d086402500c20315040d450048803c181d10002d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 390776232 1250 390774982 390774997
    0x6150313020f0f030307031107091a01020d020609060118060f0b190e0a2709060b2107060e010c0807050105150603092a030307050616050304111311 65
    0x80031a180c0015401d048006040000041d50b0842114143c07400003a0707079020b074400040030000e8608110101d624244041c0005040e404014000c20001c200d1340c19401d8207640203940144035000d180d80f200c5200161544c0903030380b40009400281d00f8942098050450640e801c0a215121000001d0286803100e01c031005114100e4607989a11010307121065907185105800204080d00720001c0321542c5800c901c0c41100c200043d903451410b03078030408039604000c0e0502c0d0400980362084190031311507140c000d4543c101017200c5480c6004046c04132600d06c0008818000110340c02040b080c04001d0007401043d080e4401410312030071008842ea500b0b5669403280b43c044030a0b0b515201408261045c0030b100010180f001c840741421464510301c869a41c881c04015110403107005884001d03940d82071031058645000150a4030380d60031041c1400d556868080d030f14401400400704110310003a01c03810a50b030040341c0c081c03164004500c01004110048030079002e040015542d0b09035211154150744010700c0701 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 390777482 1250 390776232 390776251
    0x3031b09273907150c030b0f0a0305030906030405120714070f03031d011404030c03050f010908030a0903120c030f0b0319020d1a180f070f050603061503 67
    0x240d01e00b404075101864441540d10040821a00304070005a00c4400364403040c005100655880d0403481c01d06456014020f03410100e298503040001d40880c1e816040281d0002d000d032640e40740700c0c40100078413000010f280f002400719081401810010b00e000001590010702407401c46042605082e0b003414268440e400803a1041c0b03031007482290741042848030200506000c001001f0381451518080c01c2e14005141d1008082e80c0c0c086e1a1485a01a191004d0018401c2050644803601c034600244095a41c2c0002c0d42d482c03080c0480810201814010b07070300c215911504050840e180c03203146002a040342e49080302400041c01082000c03a42a1151400c0803241c2d5502003200119003003644220f50020100c3c90180d0010b000795120340f0b4030700034070b05092903054035046056210b60030513890b40886410007054000541090085003403440b01c0030140900c8100c140c2e0b0902120361100c554035401e5114050141e44011400c001500c2c1c45030180d644402c3c05001a15112a6040a0596544101e412140 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 390778732 1250 390777482 390777559
    0xd120207140106081e070e0a2a020c010305010f0b090907090302060d09030e1002121803030d0c08010e04021f050702040509070f0503070f050405100f03120e0303031b09 74
    0x1300885003540031141031030070001418941d81460700c6500780c680010f00f88c2c0c03c020b41750b000b41c1000c0ca00c100c07a554601d954002c10844e81841c001070080d1650400c5000c40c1c0080e0405c1d0010603018041680b580446c0c050900da10301c0c0082c00d000344803590f20010807000a100d001800000540c460400928003c04000d00002d44e4071024a00a08100c280c20009405071b4800500341d01e04d6a000a07840380e081700e1403080305485550400c01c0070b0400e410020456054003001c031340424601101c2d00300801030441d580351400b1580e01ea0a8502da0030004460188d440184042034076040701010130715440074071217841c1051074140705d0340100302940c005691852a95200c80820805001030350341c1ca001a120403009000141e00e042446030704000140649442107030b9070300101d14000c105540c81401082440f0f20b2800c3c0319a03d091403940c0c501003030300031008038036102e10b043d00b10718020040f2441904001409810000180e480d5003194100b5440c06030840002031b00031242d00500c0181307682612075803c4410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 390779982 1250 390778732 390778753
    0x4030611041505030613020d0617070602010b010507030c110a0306140709120308150d05150a180206030a0b040e0f031e120408091302030c0702120d12020714010608 72
    0x48402e180c1d1104101005014000d100c1160b86081000b1409000c5482c096110003440041e20020403c0ea84840600a84c00038098418000880c0e0070086032a6600208102c0402d0b800644840c0b080f01001000a40e28020b8070000031442000080402000340200e881c0580b00c0d070301e0b1000c40d14130108a02200c0240d50400607825403100420024060901000d11615030698000c1c000000c082d04400407035103107401200030380d100e160420b405c1075000800c440483c020341601c0760440c0f0055581e1443c1070300b400140c0521002d005c1426695507030207007185241d5690072070a10001d10705542180d52094642c07158002802041009450001260002c0e56480c040c0d804403000c003000134400080c808005102070310003031984000c000e620681204020350307a4003004001514940a0b040145091031001c0203119081d18060041c100f42031007a41c90b80100c036034081c010b50346ca1020882c13880010702c00440ca00c0000384103070040c100d401e214299600c5c00c200381090007420b660040c1c20903212507001d601c110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 390781232 1250 390779982 390779999
    0xd020a180801022d0909131716080306031f0c18030c030b07020f0109030309050c030a120c050102090d081e03010b0304020108090a0609030203041e0b03011205030403061104 76
    0x40009007480c0703000314500600c00d44619001c0c940c0c0000c5000d0b213002c02c03404408045080040340e54000005103030344894501415440e42d0b9525910042e1007045070328107600d00c0024108102c0f00c2040404034038038152030a41e5503501a030381c070080546406000c0c240c081c4490300852a44203010000c031010200707108624000c02801422952180e01e4000d44410081010824607134000044e2070708030860820503921240164502070f003036402c5001d03a61070a02540141030303040c0d11858442d4400c80c19117140078142c10030190b0f521020703200680518400c00c801d480342c1d4040c0d10141031003881140098140b0105000180584c2c9008900b594411000501400c40c0a82d02c41c80724250010743c440e450455060400060140c000100000d0501803284007143c0003140030000003a8980e8031103400c0c0581e2072145402500d9070028800c10b00ea080110a0100e0030f02c0000d0b600308190385100301d1030780c10350b0301e050804040d8510001c0d0a49035400100070220100c3c140b4010542c0d4800c0d011b101359035580c0741c207408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 390782482 1250 390781232 390781277
    0x1b120c02120708030c1204061b110706081005031f06080a030c0201031d160e09010c0206041502070803010b1e0910030e010605040c1d040e120706020d020a 68
    0x11504154000c40d1015203074001d45480035000040716460b9640c20072140e00c01e10840c981c85441d000241c00b008200070707840c1c000c1304000316440030f045541d01d00d0304420390307060b003075007425000c06d4011070341c1800a180700b003d00e15031100c0c02d0007500040907583d1010905040024540c0c1c000700c40d0301140c80380207070007070b0180c60010550840105014185a10000c201511800000b41019107410b131503030300e0020002004038900402c100744c404840c50416a4843c4003800e10502c030b4036440030300009090050620840d04a0242500504500d03502d0b5610f2403c000c3d48800c0e145d502a60074441d0002094a01c00954085c158180c44241e4801031480004c07000c9144101c0074003640020000000380e9110804000c03010041414045543c3d003c0c070320850302611031a0051a0030034a000107055070140d200206038900c14044580106a02d00007040c0415180c140c2c1c549009030b03110006c0500c901e40c81c0b10082043c0782c003030701c030050410400354004030a9a10800c100c0b030010750035401c0b5025540c000c403032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 390783732 1250 390782482 390782501
    0x30e010e06040c030809010c02150306180c04030303020c100204030f0b0a0908180117130b0901090807080310050301061d0f010e0c09130609151a0f0903011b12 70
    0xa0240386820f60340c00c00f104186000040803150049110034440c0d0154552540103540101503540c50706000004110641080300c143d44218002c0a0b107444e101e80c807903000c5008411030896145000d055440c04da0281d4081e2258a015124a903c24140e142e050301c064030140d07116041d204c441000d1410408040706014080c0040c4030315194000300060343ca10b00320347c0e0419005445103501c04a000059500c80b6541d16601d00e441450300c20401c0d0304030401035401150788288480003181e1a0b95495600300c0e0300d0341900038041c01042194901144200c3d015582c0140d0104605540c5502c501c0031900b0b5480507800450b0700c241c0281401c400f1030910b0305095128105e2552006158500701d49450244005880010580310009042c107017034440e020305540403101e45000b444400e0b51650303080c0040c1204000702100d05145100810040c0f800c01140d0031341c0403a20102406c1880d010f000400725840314403101d81c550342c0c0b0000d10003140400b494103000e040c005e03180c10000460007142c41c019952002c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 390784982 1250 390783732 390783761
    0x1050414010e03091e1e1509031b0d120801090c0503070f050a0c061d01060f0b040315060e07080a1b020a0611160c0303140a05090f03120a030e01 64
    0x1280144444070000c20f866446030201c1d41d0001400a614290003450b441204083e0400e4109084411060f08181b11110140c000d58050502081000421000340640f40301c241e03040d04102d00701600c1560480d28542c40b41d000030a8140d85009170f5540134010407559841c00089020000100038903d01ea100d840c818018504200e40b1310318201100811600c420162001400780100e010310300745110f0440c43d08c0e5240c0c848000c000c695807036282c0200a001c1d0341d44611103982070070320101e00310a80000c120201c40788811039a0502e81590354144040741c125400c01c18a594460001900308902e1411380c0c019081ca45909095042020400c0241d440c01007000114030311980200905a81c0040c40e490541d81040c0d0004140700c0084038140e081c82405000c0246100707001c085130502087d03100c80401c8074482c1c0c030b031560780c1456403c00103003d01410f52000301040091004840c1400c101c203060400c80b40003020b40354a14040d04002c460b075080f81c450030b40000d13640d00ba8201440b8091003401107200010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 390786232 1250 390784982 390784991
    0x5010f030b0d030c050c210f01060f1401030b040612060b030115050402031f06080f010602010506100507110a0b0d05090a02090601050c010b151c060b040501210e0105041401 76
    0x78046a031001080c440101000a20390300c0c0310502400707000221034407a0080c514444069a0100720792000000d601c0a01240105140580601070520500b011a422020240503861900ea03070040d10404802c84281450380320086800a96102d110700700140c8024444131540080d1803c004c2c0440d2032411525019031700d48085501c0400c003001c003010449030111009603480c0c0d59189110488448034890b0100d0320740b4410049581500051800c1c401c40640e0b00c4d25078a6a42d400d8121f090318004d41c1c1080e04080c11600340c03480f8510800042c80e015001d030343c4c141c048219004c0400c81c0404650f20070410280302150071410004103008954210010f42c00521030b010345c980000d4078110000e0070140c184100000c1d0036160700c2c404c1d00052a40480245205410780308500058110703840368001c1d00c90000500d488100700701144c401c0e001940c036445151030900d03040500645403440b5000c003c98005041102000c10001d06d405140110080c980000c201410180341484144036040c00d001c0103641071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 390787482 1250 390786232 390786251
    0x80d02120a0c08160504050607050a17070c0501050c0f1b030d030209030303010608190603121b0c030210021203040602040f080a030806040f1404050c100c15051f060905010f03 77
    0x26a240d400000b081d2100b44c8042c032800d41600c1d40c2c49646d02c8140c1250010a2540c248600072400c074483c17501890216990b1303140c40f8818042c910940b5002081202000014131813544610098008071201000320b030742003000f0140312841d103c40300803c0820303a00a05845580e0303080500400c1c0d5003c0b214101035003802c00d440d00007500c0340014000c5108108605e1b00265070110303205013041390600c141c01c04002c0c8580f030f81880315448407254001c0c0c4c0820048c40001655404044851919075002000003500c1401c540c02c12960101e44020f910031031090715503074261001030400441c0114441c000c01a030b10385c680841008000039540c045542d41c0c01181d0214042600300c0800e80d030101d811034000440701150140280180360f1a20a07030400206041008100640007440714084e11003125040750804009504a030042584040244503c4005601c514200303410f07040302e500300c1c0c0e4800182628440410b883e90102001d5444440080c101e5402002603580002d103000c4852070500d4140f294044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 390788732 1250 390787482 390787487
    0x191214030a0906140a020403061401050904060c03020c011503020315131101141b07051f03090c0806040f060501060905060912010b060c0c01020c0303030906070807020307080d02120a0c 81
    0x30807030340545840e5040c0b88200302007030f070100000303440100c0c01c505142070102085000790040c3c08200c410343e1410910700500c140e62101503048a0008003100700d2903aa69560202030400184548103054083c0013034511024280038031100701e0003001120383c1180c03660040606e42040210314040345c7e00018240040c0042c401c40303100829400207520800b4000c20001240d01c000d010450900b07005c000305001181450242e060b001c5244000121201da544800c03c00c0a00d00d41320200448000d8500c1d628001140070303030003040c81d40303002e42103c102d15a519060717541019012181112030800c1885150b04110302c80c80707000c0c0548030a181641c0c0c2c0c41d08040c00f213401445050310b1248664000405014008001d401607440180085e00c4142c039a0782d40c109480d5a0741032413020302c0c094012200c00d0b5016060000070f0720300ca802d400d0000c0c00703162164501542d600c030b00a001030046000800000011440c108010440c00b0250000180e480c00300250380c0c12001e0000e032403000741d1810140382940583d0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 390789982 1250 390788732 390788737
    0x902040f0207170c1e0a060c0306060f0807021e0109120e120f061902090a08030904232208070317060117070e03010e0a0c0e060111030409110705191214 67
    0x17015682c07500b41c2280c01086458440507010061059080c0340f400800c240e4180c010f41e04548a41d100d0f24100c80c4420010b85044404030307208001a8081d4000c24840c0510b8820340400e04010000000d29410035240c803048007c4400c43d1a000c81e2848a401031581000c1c1070103090900c118000c1c1c000603100090f61901c07107401600070384101e10b01220b4440317900e401d030313044401e01d000c028400c880702552004456142e0300402044c0748510301d01104104080412010b2080c00301002c0551b50160391810103d0b480240d480e01c20404010180c05004005010380008180c040d02a4580065035600154044080031008100b2410410310002c4403508586c281c80d00b640240311801d00303c0e085101280420b0052940100d044801e2040721030f4207040c4405c038a940026200c494540004582c0c035000152040585070142144075441003104009105980c1d0048840c401806c0050b0300c0c008c0300d40c441901c1c1c104052a10000b46040d184074000700201200c44260291243c100300080c0601c0000003001ca0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 390791232 1250 390789982 390790003
    0x3040b0406020f09030d09180c050f0f0f13080d030e0a030e190e011701020406050a03021c051501030b0415090b120109120e0d08030114040902040f0207170c 69
    0x6801081180180c03443e1810b860b450680641100c04243c001e04000305001114031070003c1c0c0c0302e0f07048003154012a182c001d8400029280d01c410346031914088054500d50f01400c3c48040a4074248035450040104030018120f40010303491428041741000c0d4803500f0201340008610a15161504c28049402c02007081a0340035054107051b01c109021002054901044040c0c80740010503c00020a00507001130301503042c0d4844440da078411030780d28002c0508030300c180e0141c60040b550070301040007818420380003482103003d0026518040c4102c2c030b8110080c1c0740245c03507441124500004040455915118002c800c1d00211018003500c0c025848125241119028444189860f9600c0d030003640c560400d0b1183c2c254154008201450003803d040f45480301d413603c0540020104654180140b03050750355401e4030b54120b01c81e6440c61741f0786000f000c03400310300f03004064200303840d54030807009a074543c41520a41c8010010140e40c50700c0d01d14001000e0030b20128904040131080c40520084540050380380c111 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 390792482 1250 390791232 390791243
    0x170d0e130b060f0a18052206091d15010506030604020c031e0a0206010e07091401020c0a06020601090c051c050717070c030906081e10081203040b0c03040b04 69
    0x290501403020303000e0075000032280e400201c0000c0119206210030000d00303074840f40b6030b1034080c0e81d501110b01449860a80c0709a9502a40c000f0003c031380070409a8078005015402c071310005195580300720840903624500151840382074118038507a495642070007400b0304030920608642c0d8641c10031000440c940005400c0500495021803489841c82c17042046840d0580c00045018480c6130b80300030002c941c2c5c007081d604001130040600010b600d05007803100c580121455211908564201b005041d0f461007082200390440c4180d111007030b41b0b42c90398150640500820781c060500340d030411114006480e04a500441000300c20410b0a0900550010b41030303030707000026808145502c3e400340c02c1790102c0c0211461030701c441080701401070883d00246198032183c030a403510400b5075550b80040e0303105602146c1c4116040c0c0d410003540c00c0303800d8402d0a070f40c0c0314200030301c40103040d919440020328142c0c524402501c4a4800002d20040c00405a0a1680b200c580d480240c618030b844e03560449140d00180c0020f10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 390793732 1250 390792482 390792499
    0x1c0b03061803040e130c0b0711100917100c0c02010215070e150a0207060f0806310204081902011413030803090606040c03062303010204031b170d0e 65
    0x11041c42143d00600c05098800c2c13150400c1c8000500901d44014212000c446840700040c5079204403094418098104e0a15200806001c003488680c1018072043c0f0f040150200000c5072441c21780d030303d00340751a6021b0004c000e07807269524000100d40260111500b0300090400d6400140e81c00592101c03c01034010700301085031100e410035a003a6902030320117076001705030035031401070f511509010b0494050360b58225407441e50f884001b41c1c0c0c10049511000c0005103030342e00141c43c1e030811528400a00007048c03040549181c1f401301d0300c030000407600c1c890000c80d0b400007801c02c00343e2410030080b8405c6401a003902007551389a80080c115195040e44501e070901d010070608029650350307005400440d00055030560340c0c90254030041d1102011550648141e1070413664000d07442c400c4c464442a205070b0856250b01d030701c0d4510b05800b921340c55200b466041d0b400300030110018034419045d000850409a548100078108020a241c080c0040c1159174684d00c90f030340c803560740b90340f02401590f16402915100c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 390794982 1250 390793732 390793771
    0x3040603091b03140111270d05010e0a020925080903040305010c030902040c031a062206030b03060a0c0509040203130c06050a12020f07020918010e031c0b0306 70
    0xd40c10440603242d9014000c1d8600c000084c40b41e081c44100001d80030800800a8000c00c0c1840046030052100461840c030000300f880500c00705050f90403e10180040c00708070030915582c0d07040c2c02d40b005054840c4442d04841140411800d2148040e6001b500c5280040b94403a00f022000c3c03601c42241c0a49010080b048001c18082001402103074095a006002400092120100a4040d1a85503012030080e4a030034007802c04248244620350880303500f1094400500c0e211000c10595420209400a5548030301c00d03048054443c55040c00020112a02c002c01e003480345000301401c1c240000d03c261103d0b030600c5140385070b442c1e200c811284100d03802c580c0140c580e10340380019103038000c070940e005024494011020944d241c01c075024000d8001f082c2d0750741001ea00d05030500c0c400d9004080c0c1d0181c5041040c081107005203001982503070300002040020503194803c0b0b0409007903440002d1404019000051710000a1245580034450f17507061034030a105039030343c90300420b40e544e4000f04211146c1000d0001031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 390796232 1250 390794982 390794993
    0x17070507030c171810020d030b0301060e1006080c0f220506070b010801051005032802100c063e0c1f061401020a031d040f090303060501030b030304060309 68
    0xe2800341e42010b4601460307518210f0540d420741c4a80c00c200100d12140c120642107250080f80b2900100550b4041c01c11205620705c2500540203503000309505541b1194086090040720007458401c00e0110b2440450515109000d042d09002404c1c11905078400c01103554038800309411520000b00c070180d104881e00c1c09151074070451003190001507011000042c89400e201c4c040c03440354103a8801c00020803188e1255040400c110302e05204090305900700c2041e031500c02a01401c140034207605004440c2800000d41c0c00140381107413081c00000410320300c0300444180402481002c2150800c0044000421003e090041d4844100102c8844440382944410103041c003800c29180030804410483d21050401c05000e4811503110030034841040c50440c5c00282d2080702428041c0d41c9a040c0c010b015282d0340394030102c03003d0040c01c1411940003248907001d862521548a604683c10030410000340107120703440d000302911860781c0100c2c10981002c84c55a21350707401008490440c0e00703078180003501d00141d00c0c18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 390797482 1250 390796232 390796247
    0xf1207020a0618050c011110021c1404050d090b161a09150a021e0c07080a03030f0b0a0803160f020405161701060906030f0b03070b0d0c1707050703 65
    0x811160800400c00115441111043c0e0228407640545a050080300011500480b1001e003045013680000b040c10b0100702950300403c060b00300c6544210000070351018040030707154002c2c0860300f03806280c0e0801050050074044010144c3c51490b041f0021890321190348103030f01030b0000080f41e9400300031000c810012047d40c8210440ca646000303150074606042e86a490300300d030f0a070b060f00541d5402c00040c0c2c0100980308031540030704003040c0c4040c1992401c200008541180f8100b40042c4183c0e900400c030580104000020b40340700e6034001c502c4425808040056031042d900907800b90040000c10701250348044251344800d0070351400036141c0a01ca0515004d240280000030750040d16200c2448090200d40c65038503d8100c0f40e0311003031442c1882c40d6030503084820074401c21000449060f8140001482500151a10140c90300080381c0c1c80d40e0307440002e041296036441040000707400102401010100e0142c0340c10780c016800c0c0044819030340201d9080d060001001101001710010311642090301035081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 390798732 1250 390797482 390797503
    0x1021b0d0615090c030b06040603090c0f0e060f060a1218060504060b030f060717040c080d020109060e030c1506120d020607081006050a03150b0a02070e0601050f120702 74
    0x201445004042c48010510340907030700602840500f4100380ba94041c4c040c2c0140741c140c00700600700328a05460800300300e008103106801112450004440044d40030884030080c40901003e03508500142880d001b0091b9180810300140d000d4501805040c21180d000b84c0d032043e410030815000315200e00204003071808035007000b00c001d102d00d2414080c04148000c0d64820b0800b440c054048030403a940c901541c5a0710711081ba01100007482081c0a010781040200e010340d001071050a0800c640b40d1101401400c108140d038400005070754820002d020700145006480d904a01100510b10704400d40c6c02e02c9880302c01d100940b500d2004d00b0008642d880c0c40d221980c080e4110008107595266400107802502e850b0142c400c00300007401c500104440ba070808010204031003964039100c2c6030400009094000d805290340c840e8403484100c4000510250a100410407208182d0107001601d00f00780004503801e0014118504101c401d2200d9555144024100c85940102400c1003500d80c1e14080e04070f00e020030002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 390799982 1250 390798732 390798743
    0x18010204120b0f0c0301180e1e0d0905010807020c1e0604330c0f0201111b010306090509071e050a03061e0b011e03090b04051f090201021b0d 62
    0x45841c000e00424000d0310f07000385070310440c00b9666294000003850380c1c0000e004544d01c1035080c7c9141e0040403099441160100c2e003101c1610b007062000c4000c3c01c4500c0504216200030f80000c40e5911210364080c14034000b4220908046031103003080080256a0710000120602440c8440700c160b01002100b83c0c8843d060000501039550b60381ca980b500440c5200903a645d4000b00003603540c100140301900500c0c00760350415503d43e10b101e64030f5158001d000c02d296006034140301082d030328103100c140140110304038600c0b0350410480554429000504940240d80700c001070b40e203084103102d1041c10102d0001e0880700c0800850042c40301164204e0003641c40d0354056a4011804a40001089203641001e4104c2c13590703405038005009500d0880040d20b000c8840d4038001085c01c07070380c5c5000346028103200c149035006207130000b0014000c1c0c1c5e078000c02d41c2c070036642910198082c444034501c840c1e0659403c4443c480388107090003950802d60000c2d50b11400e021040c1c40c07051250000400030f448030850140c030283c00c003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 390801232 1250 390799982 390800009
    0x60f3b0d081611060414120a050307121101060b040810050402151b06090a1703130b09030f0c012c120a0e030d0c03091a12071106150f09060918010204 66
    0x80c2c6c2c07441086000f81e4030f441d004803650641420b9070000440c44851168005024603c0d12015980b0004245400c004c0ca00c00d01c01c2598030b951002100344182400b511082c282c0303a0b69030b0706152115107400814400941e00600f003100b00401a140c9040512083c0c1c07944885603100c0391032215954201c180101c20741000d205d40e204026141c0000a50358103c3c90055040d1008007860800c0700c1c206110888400d180800003082080000e401c0300d5a80b90301444c42015079090803200c1c0c824401e06d502203110420269100c1c202226a0a86078494144070b0b0b10b0401503207061150f02c800540c0701c00c4c06021135010040302180000055000300c06d14414000c00409403a0001e07110355000c1c0c0703049628002600001c0d071800c004120404101c0b6011002081c903041c1c3c500741244040b40311100d0200429a1040000414401d064408100410740c09a02e01031055007896601600340035200d6050154588508100c005000e0310b61640032503580c2003101012103a0515464084481c0a4840ca03444a46000d011 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 390802482 1250 390801232 390801239
    0x30901020c0d030c17160c0206040503030a03020301050f0d0f14070e0103030210050c0301080c13090209010b040317070f03300c020f0313060f3b0d0816110604 70
    0x2541c000d8001410b0382c1c80d0902e000c00d03000300e000490517040b00e034000c1e400f001c055811802800340e00344808241c030060580c0d1901f0b0720b4070302090440d00324540400102e40c010006210758505072402142500f000d40302e02283c01d80d10345075220519141980644041c0c0720f4651440c00070000c0c000307000540702014810700a5603507458025901c085002202c0e000d20314107c00b0071545110f04040b03e040b5103c0800500d140400d5404010300399284a58034000d00c0d035074107012030060701d40c0200349008212030300c401a00d40e807131801c000c41030309074811340640001c2e0104600c100007002262004202c40c0c151421203080021621005660031f490441c0025981e0614400400003c498000c544c1c105030136400d03581075a8001c1540e607503074005e40180071200414103c09225a6115011440020400707103410750203020214122001c001c5203e000d0390008035140400450380000003c01181c1f0001034502c075400841d11345640380301d80122020300f14072258080f00041440322040c03040280e12001450319945998 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 390803732 1250 390802482 390802487
    0x3060302040207150b010e03060601050c0331090606050d021b0105010e0601200705010f0216060314090a1a060d14010501081203090303040303020d0204091b021011040b030901020c0d 80
    0xb40300c4e031006001d400e01a4002c4594800e0410aa1072503015000740040d0b100e100040d00c40c0c1d001b00100e0a094801440135a031200799082182c0d03110340116040d0b410341030200d41e1503a8900401e80014494905164081080981c081c0031142844840740c00182c171038450001219801003c03240c10b041c250700b040004102040b244510310700541c000d80ba0201030508401208112600403100c480c242c0d00022006c01065015110791503006c5114816214003c1c1d9142070000c1c1d52402d904000c000039038a00c401507143e000307829204d1300700c61248001e1030f402401e540d42e81052601200801502403410010901c641c076502c4a840301e0a40c000208481041030050f924000c1c0424401c854140c8106d5002c50486c0000c00100c90044614102541c0b03140c0d1140c41c00d601a500ca100e45804060b802c02c00003816002a2050009034400c41c0f00c41415005c05200c02072034940c0c0d02019000b1680750207820801c074001310045900321030408000030745980c1d400d0038141c024042d4080c64001c9000c0d05a040d0403065 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 390804982 1250 390803732 390803753
    0x3010e060a051003051807060e1216060903170c06060f0102010f06032d02060304122006040c06090501090e06040f0212010608010e0408121801020423030f07051003060302040207 78
    0xc1012010709a045128038040b6507d03100c034030501c408545000214005400c1c507403035440106140b901202c0300ca4440d190801e41014080d4080c0c2c00040780140d0520800110a40c00104030859510541c241988500203e442d030754060546845005400031b1021203074000e4214440c241d000352001c0046035a2800c1215484058169011400f014503000703d0b9000d040f8014402001e401500707040c11661183d4a241030340740107642c480244805d40c0310034105000b58112a0f407a02041074041d01c000d080524040c00f0159860304100103110040405228999200000d01c04a407000c903080e500c00d4803443e010600030a411103107000000c2c00014400380b09800d4801d018100c403c256100059680d81d109921701e003000c00e03a40180b10b070b4010440c1c4001e601da601070050700040000826a02c030300ca141060350890b0b009601c11030400c094946501d10580120441075007a5406a002c0d10012041c2c0316525101d50060140b584520041e03403602c56854425409100175650107081151750706454101240400e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 390806232 1250 390804982 390804991
    0xe06010c020a0b0c0102041a0a05032e12140d1209110307060c02010f0203090a03171207030f0b0613090507020f03160c120210030f02091c0309050a030803010e060a05100305 76
    0x23030144100e00000758080c44c0481d031200340243c0d6264119103810b9030301c140450070610b401440c80c4c0391a01452501e2000d00f000c1c8001e051000c900042c0540c9890107040c08260708000180540201410070350b070640240b440c0c818010b5000e8006120708181c5000110507403250b4800c0c2c0c152040f000301148094220301c14545c00c0307000343c0303403100c404641d1542240d40b4030500c11483e4001000d440708100007143e4a54034021881d80007540d81c01c0c8418174240840194003201d50900003500c0d00903501d0500152b01c02c00305049403c2c0d41d00c1e880c01c0400e58001e52441c04a109a07207116556000141d241c6100307010300c1c0e5010344042d083d690383e240694a00c6484000180041e150060310702d6001400c2c2d00c0707800c0149041b503070141c40030006040d070103420780040032284442c886564081000316103d0b035448500d020070074100e4604421501141c20000e12102ca241c00950007001102c0007840411304460949044a5010082c1580c80ea51a00030483c80301071235000c15001100320403240390301d94042d00098401c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 390807482 1250 390806232 390806249
    0x151306030803041403161112010203070e0406050609090c0a14040f081207110d0204021b01090b010e132006040e0708070306060f0e0f0d0803070e01090e06010c020a0b0c010204 77
    0x100703000c4c00512a102c2c0f08000c48008411a4840040700146030420030404015000704901d4006807842992402d80c1c0c0308440100014004c4c070800d203402d203000d00c0781c1005082e0544180f82800e103140049100d130b03c000f510000c1030a0340498244200f074802d03047c403526000e41c01c044035215944d400c261b5464048502401801d801903ca00e0701450b50000309440b101904942c00c00e8282c081c0c281800b102080107841641c0160f020880760b400403407400448080009144000500795042e410040c40852068104030000e40303000c0140401040000e044a0190b40c0100701e0405107030b003400f4041580e143c0500407a8000d0000324000425001c491400c070f2241035151111001e40c0d503003000880c1213a2440c040c1d81c010404555410048038417460501070703110b00240000d29440c86030000101c620400c03140031680c07442c0000c204181150710001807104c11a080c00e100488604000907120f1509008148904000480b4800c0301550394488050004012140405507255008a0010b01135481400790510f07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 390808732 1250 390807482 390807503
    0x6060f0f0603540b0c03150a080d110c0a051e1903060c0f080a0b03070305191b0e06090702030d06030b0615120115180602060a050a0203060915130603080304 69
    0x140c18103041100107503100b4000350165881400d05c0c4259000034051440340c1142c44000c0d4a035171900c0100c50094200d84004141d01035150b00d0090400350403511600c1d007600071b2004012710361114a41d100503a80111609040e00984464807002002c41840c0c00368090310760040070189c1040d6205410035240105000e0010310304414064070640c0c950121070300003601c52030002d02d0780c051952066254810040642c8d44960b80c0740c42e01803401085074208541058841c48242c100b040c2916055800c1c080ca55096502d2481c1001c03426000700001c103454028409400003640a0703200b0700c111000d030701111600300a1691130b42030041c8040301c1100d03464095100700f00d891051200752070580d5842c020508040f6056800c03d01c01880c1c0d040105c41c0c2da0188460304c0007041103041030320130000140c09a680140080c0c600050207206072103014014514542c130400c140700071034649245580c6c0c00302e8031094140001c6c01c82004140268038425101d0308181c43e00c2008020024144021070103140205039840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 390809982 1250 390808732 390808871
    0x307140f070312060e060d030807030b0a08010626070603110906030405010b12031204021c0203060c2d070f1509060204170d020a030809150106030906060f0f0603 71
    0x9072100e031709440c110361080110b219400003901c228a0254031000e546004203124241a001c079140300e52640010405035110039003805840140c50b000250081440d5a1001000301d15a66549802d00c5010f41304c00c150711400020311000d2131100b2142c041d02c000c0c0c401a902e20300390822030b0082103101c6101344200051100f4000040300081500d40c0203d0451110000c0c0e10350b582001040b0b412000054802003000d40450050f130303011b102c0c042c03056020b582241d644000070751042100400007080340030307001c0d0b41d421005401002d030401d03034000640c80303039038242c42c00f81ca404c280c55202d103a4024641c925040c41000010440d1a07000f500450701e402094042a0200d090380b41c1e10303165280000001039101d10250000320388900326458010100006551600c0b1100b103640100f840240c01181c08a500d800d031035020001d9920480d8001c100103000d050905041482c83c1d1038050301841100304140d104c21150109000f4401280070501c220300d00414004422001511078081081845901110300c200c40b6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 390811232 1250 390809982 390809999
    0x120a0c02210906090f0907020303040c0b1c0b0a080f0a03180305150a0f0216050c0a0b0906090105040807030b0402010908070e060607080903070e01080f120307140f07031206 76
    0x400e441070304403144509000c44541032049941203005200c0d40181d52080104e0f4903190401c80fa1301070701150703010715541c3c03030107041001e445101c1d0391000c1c1c24554100f020095540480746241d00704030f804880030a8044541d000102a0072040d00520400c0c001c03480b4980719a480040c184580610a440d02c3c400e0301e0b81c48c002c10166405603c0043c01e2500020f8013806900b610000c12580300450040002d94403001e00e0180c0100d030400c003035400400d00507420420034010104580c42d031818044032902e04581c140000d202c110b01603c00d0240c007401000c280c070340460703001d1010b0710003500c101000c4805143d40c908009440d00d600340d805a000c200c12a6001c203187c02c0200b0b20405030303140c2c00b5003c405521000240304159210031030030765000b1010f200f000c40658041c00444010800040702c000741f5411701d440d032402c0220a00a4480c654402010200070240c12001d0300d03070090950038816a400000c1c00c5508492282d60201d00c410100010814105504003c28080c4d41a025a0401170180c070f45580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 390812482 1250 390811232 390811273
    0x8061e01050d110a170703150e0a020108090709090602040905130c181b2c010806060a020109082803090f020d170f0702030105130215030408120a0c02 66
    0xa40b5000248007100300c0c08100150505511140b0262203802c00650300d0300d1003101d4a01e403c404003801c2e0010300c810410f1005ca00080d101b60b0f40340d0394003001940031513510940c2e00c0408210081c10f001f14900059140a4140320b6000100251902448115070b0303440c02030001d45c014021052040c0c03034180403910a40301d69202d4190f00f80d1050f6210340081c02e0103000f0000d2a09034000d07011007512045c0d40c0401c804001a8001070745010f4031035000742003507030000240001410307580041503140c81200c440d00eaa0300c51003043e004171041d540c9a6440a83c220203c1c0941100305025015480014086030300c80d40c000656070b01c0e80380e1a880c032002d0801d104412011745480040142c0094441280100580341644800511174820703a0180ea40d86c060b548100b005400522030224910380c041000130a508080c01255445a400109101c400c1c0107980020400050b950358200903071004400203003004114005c076403140360640000300d090701c1d0000d00c04020340810701d403000060003840b00c0d0000b4840b25414 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 390813732 1250 390812482 390812489
    0x23010b0a200703020607030e0a0b0c1002090f0301020301080703030908060f0a0b01020c13060303030b09090703080307090306090b010305010c1107050609011701030303050609090c01021507030902030708061e01 92
    0x685500404011400303031001c20103401c9480c00c0b4000c2a00000059540c640204a124881d448440c0754059020400c200d4401d90f92021183c0070041011144440c0c0c0490141400c842d020401a00c420400d0040744003599130040303158045d8030000001c10b98490000e203010840f0300c40d0761003d44040d2510240358903510262031240c5100e03088408141c000782e09810a510b1b07498103104481c10381800c1800941d000700c600e0071000803e95510820b0050650500400d20b4400090340e250321203040911032039a54542c50301c00a0300d0300c40f021000c203e1551080b4158401150440010301a82c85030f800c007040340d07903401c0c402101c2e1580381418a444860040111307145000aa00180400901e8507043c0007041c0c1c0b082c43d1403410803c1102c1000d140061081c0001e020750701036940021240740c82018041c0248002e042480b481d400842c20a55680e40010080c0010010109190058a40e0301082d4081c01d000d05009505001d07039030703002c6038002001031031071321130582001c0240c91402540000c0d22142c3c801e01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 390814982 1250 390813732 390813737
    0x180c290306010f0c0b0114130213120f050109060b01030e0c0a05060d06030b09010509070503150a021b0d080405060604063b2d06062b23010b0a 63
    0x39881e50f020b00a48081c0c114036050841e104616a55400c410501c240c0008500714580c040240c4241404147c11422041c3d2910461608400302200d61071005684540d1002640824543c002c00060b0021181d000364071600030b001901c1d8a01e483d03405440d031180b94500003450624200d5074901c000581c010b54000c05425900101c0c10310050002540c030813181121201e0310398030000300040300c0000b221701c1140c8690001801307003008202c0c2400d2880c03d0f84040c0c440d5201091000705400f803080f065401c40180100140e44803510300c0086034003155000000e5041c059507034134003603072600200100d100f00c0c414400c0e114580c1d102d40401003154424042c007501d0844590384512005404110110140307644080c009082c0110042c01e940c0e41e0341201c03424640c559460a10001800302e90710100031200c1901820f00d02c0c40c043d004038245006200452100c00010300403603812104400d078041a00e8140b1005100c0c0c0014880d0034400c01c51103101565a01c61150000211000f4420648594801e9035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 390816232 1250 390814982 390814987
    0x102120316030e011107030309050c0402070308070c020301060b0711012003041202030304050409081210060c1b0528080d201c09030506130503040605070303180c29 72
    0x159802c90040402010340c80540d960382c04c458580410716405001c0f514840d540c0860444024075000e0b041c601c1180d02d06020f18010f004040000b50400801584100c492a01501001403400000c0c050540e5034464003411500007031020510500741c5a42d90769000c00c1c1ca42c6407209881d42e0411205420480605801d42c00a10044c800d2000f1740b4001181c46000400b00c034186074440c000101281c141100464049400040091000440f8800c41d0752101200c1e02001d24140b42c044050050213001030000c1c00303141c06ea40d0600381203500c0c0d40d150014100c0640700307a45c400e2a4000380c0c000060000c2184c0d00c450081b00c8005108100055940a60140c940d25852a80340d40310540d401200007420380045802484191409104900303030a100e40d01c00d0751f80c2d0b990341d6861420000c0c20090080c2c41d0907001058000940701190001044808480e061b180c0343d03541d409141002c600401507c0c0603600c0c0840126140c4040c010700d0212802500c3d05588400081803141a032950101564105210000b200303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 390817482 1250 390816232 390816271
    0xc08090105090409150903020d030603051b0d150b0f09042003030d090809120d0207150e0909010b270f0703060801230c040f03120201060b0f0901021203 67
    0x580c1c003900e088180035001285002d4103554040c0600306221030001030a5480c00e4180c203040d410080070315500000e0808000326404c548801d601c40401d07213420f18410364000000b6996445000c0c0b081d0900b174020310342ca502c00b07a400b1074120280209480e4944075410743c0c010641c80b45090701d00c05000d82d1348401101400018030020761610443e402c40c9591501080c403004481074a240101840c1602c00c10b1541d6640f41e42c403041018808816607007041a070b0000c0e1840304001d4000a0f03a105035012902d47c5d06524841010454900c10741103a4540c002d407503081805041074054000701950035045501a01d05000000f0100c1117100d540b00384d014003581e25000c146c48584100450390009600d26020501a407102516800d4035811841e909030a000030508804220354410f0081e0420444601585098500780e07121462100301e0001411690020510b90752050003540000001c0000713180040c2c8800b140f0190024075044a80114050302403216020440c40300d4804803482a2140e01080d0405881c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 390818732 1250 390817482 390817487
    0x60807180e070302070b040b0a1503110d060e150a24060e15120412020718020d091e03020d0c031e0e1504180b01021905070506030c190c080901 63
    0x10701030804401e0550070007103000400c40d0800f0b02c0d44078902521180c40e03541003041c541011100c0b26002034a6400740b052003800050000503150000c81402c64000041c0d406c5420840020000b48121500d0b9200c0d180c03400d074140d58041078180c40342600c3d2070300f0000d60f88101710050307140744141c041c0c12090710800030074000e040c050801c107800050040e20baa0603034100300b09428207a07403003a1100c95030610f50301e0400003080703002c1103610b981c0400752025202c8586010b002c42da2030000c402e0041241600440c42000c02031090780401201e5801c0146503041000b444203844092042100031b80c0140551100d03002002e0247d4502c11a1580c140d403542e80b2900901020300b10f0342c4d14542407230200b0040440210390313075a48015051041407a00007440e541c41c6403080039284022050361201c07046041ca403191203141c1c1c003c5407544030074140d002e00e00c80300c00c6949801401d210140d08243d03400580841401900803040005d840d60f820f02c0400c55000701a80003080e0340081c140c40e001030100d070302045201d80952 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 390819982 1250 390818732 390818759
    0x9060f06080c10090906060519020703050c04020d02070c091422030c081c06090e120d0b030a0b0a0204090b030c0310020c070b040b030720060a020a2706080718 70
    0x283c91030304402443d1582d95607401d8882503031107240010008240e501d20901400300002c40801c03140001d0400c14590359955441e0806040c000c1c1c46581d0110341d01400302443e070100c036041c0780d101840790f01d0541c070344c4010401481d000c6c0041c11907041100025140c050411034640c4c80005220b500540300c082a0740482e0b00c40a502000ca4031018140044224030640c000008808010454089541c0d0304103801502154240f60300e0b50700d55804050000c002080440840e000c90410903c082441c50346d05002c0391038900d40070345c010407441d010010010702008035800b60041d80e040e413409211101c3c0d98001c06607601d090b40d1285625411901c4100c40f100e5180d0b00401200748681c059503070380c95a404212803180c104c0c1c1c0c07010011800000402c44080c1d0b1010f01c0a920b003e80020540200c0c070b1040030659501001000d105c1920f03400913407100001e0141400880b40900c072480040340c40384400c00410310342050300c100c0c0b0102d0251004115004e014000700521055040c1107150294588107070100340c41e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 390821232 1250 390819982 390820009
    0x31b170a030605091005120d08040215070b070503040b1b0a180b070c0806070206040c030b0705040302060f0c0705100c030e061303031806021506220f09060f06080c 72
    0x150b550103002074182c4690390202c0c401c0000c084100107440c600400d00420f0103003011800c00c540c001030510000a40c10200c3c194205405440c0454500c103e02e0b8070090360322130307500060100800541085050f583c050001c0d407007584104540c1a0030380355448040808402040d42c51901e81c0280501a941d5120718032082044607501141d290b026a50306840c02103501603a41030b11103828a0b0820f11941000b003003c907410000c10b1004051034074198a95a03140c25143c0401008443c211020075441c40c440d50658001d10b400074403d6941d8030110076a06026031040c51680c80074047c0100000f0b03d468850f403801805050b940300c55220003d56601102e607101c03440320003617009005110b0107084401281903400618803d0301c881801252103500c03e0309200581c0e000000f154002c1140140c0500c14003001908100181d41d40f42c3c3c00721500c000e6000c0394090b89903035200a441c1c9049421440e0303130307608070110380d5004450400200302940e1203002621461300981c0120f91020100c0c00d820708144034502c17000b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 390822482 1250 390821232 390821237
    0x181802031905090312010e040b13172701030603030e060c0f0a140609060907142106100902041d04080c030a0207170102190f03020d0e0a031b170a 64
    0x148070240941207480075603940307201341c0c07000c942040426041030081d4098034003c200c0d08102c0c03416030b680304030300c0d81c00502d49c142c1c2c4980200824100195010b9040d1520181c40c8019240c3c0800c0c803070b9281c080d5501ca0003e1000c0b0125100800c6540648911000d40350140c0e079802501c50700c0018031581d5801018100050301c69001f81710602817003070080a44144c817440c48004483c9105c0b04551906d4006020380d0400c4d000641803050800d800070314002140d0820380d240e81500030060028040e00c5c40041c0c1000038651198415400110100e4a203100c0d144e03042c001755501d611003c0b0030003240030314007511804401e552114410000100310041e0711911030b070400352403c0513003400641140c204e00800030140c2c0c040c2100f80040b445848010b110000e0801c000c50401020780e06240420710f007400350ba000d105e41e85c0c1d00d1101d0390780f00741c04a9004140c510018001c0809942080b82d40d00400f417415000200c1005000c101c034400500c080c4c0300c241d0400d0b420069410180300c100803c1e8816a1040c09 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 390823732 1250 390822482 390822511
    0xe07120231081506040b0901061205040212060a14091906050606070c090c121107020d020a050d083001031e0209090d080903031e040503070611040618180203 69
    0x850040403ca1425445080b0b001404541040028403003620b40094035039100d40910801400481d40c46400c010604c08e0259020030344d6251400411101d881d10790003100b03035000d1070003000509503007a0050a81c04550910814880c0d503402107142c2c84204000030b202803800038440350008a80241c2101740c010341c000700303301c0c50020995118000c60f14203078440c101c03241e01c0307102d02207000e60408861400194013500912115110543d80343c0c4a100c2c80100034030900302c4c04429010754503150701940213024040c103211084000b030305080b1201e13001143c4600740304224009c0015180401400115407010386100b03070040b41d003181d443c1c84402e2070107110183c2c0700305050840341c0035a50b0b42d100c0a000e15200000b03482c0c02403142000a02c0c5070001007440c400c42c1d008000340150740e0400c00c0c200043c01840301402189444a25150b03041d8801c0b0500540200c1c02c003505030351a014007000800465003c0c1e00c9e440300601d00c019041d80103441310310481c00c0e014103610001c0075280c1d06400031a8800300c03840c401701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 390824982 1250 390823732 390823739
    0x4050f030307020a060c0f050d0e0c06030a060e13020907050d1b080103110118050d050f0d02010605030d0801080304050d0609020301050405010c140306030d030c090f0e07120231 78
    0xa103580c20440340ea10043e404920b11006001d410b102e01d040440300d0346043c8211241c5080c014080b40325044841400560742c1e03004074014101444040800340f0010300660352803c14081d400c018240902801c08d07a42628004a4000b1000d1004d54a440740c4c09031000620356103003070095030300750410720a0002c034580b107040310056040b00004040c41c0508684540c0d110394114181706c201d80e510001c0b0740341407007503688044140c0001c03140303103004841c422140d0f40d500080516080717041003a98400001d030b80c491484202400d03034044d08058181c4400b070341224101140030508840b89902803103401c4283d0000c1209229908003c0c5280c80e0b410300806000c03c4900e003d84c040b03401c68000b00c8055900365076850b02d440b0b001e9408194450f40b1400542030700c2c29801c0c0300700043d0b102d8000070175080031700d640c401048610a015085d200d00401c1e90100880300c40f035075100c1030003015404607074000006000c402030b004800071602c20740d0004003400c100d040c1c080c030715030b1200c42101001001d5400388104100000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 390826232 1250 390824982 390825013
    0x150a12081e0d1506030e0c060f04090204080a05190305180d020d0b0f07110303061003060302120c03060a1a0904032c0307080601030218060406030b070c02030d14120405 74
    0x1041d20a0b60034000060f19040c105a0900009698100c10200f5080240d041d00d0100300140d20035500c40d041394556912050b5400801d001c1c0b140d9401140e28600100b000200c1c084041048048075008034103131003100c071900010743d144031303010500140411401d2089002c040600d20006501500191100108400c1034002070f4030014801422900d44690394104410246142071054101c500c034240300c40410fa0420002c0d0b20f07400014040c80c0031740c80c3c46030342c51100c51094101000464014050180c001c2c4421a426160406800024024440c540c00326107520460720940680d51598404182c01803180c008000000790003400035000c00800d40c0c9410a05500071031741600402c841c990861401110350289810001d050340141c1450b0011401080542c44044020200c1c100080f0b4800b41ca070745110000300284007a4001800d0840c08100700002a900080d0303200e100380c000c500f20b07070648006500460301c030111262918100c1405020314011444d1610145802c40d11400540d8074000600e03144 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 390827338 1106 390826232 390826237
    0x60606120c04091404110609061812030a0306050109050306090d0c03050f030403120e0106030c090c0309020301090506070909060e061c0218150a12081e 67
    0x401c45001102140e01808280d8002c001d6880a40402a40310303404a80450b1112203010b90101070346030450076207000580040c1071901d0004a14800703031070901040f02031600002c90303585645811070300384090305050701a40d400203422440c00c1c2c0010200c00f45d81c0d000d68000d4000e2018400180c0000c20000e194030300c50b04001c0010b460924080b102807145d02006100d900000c800d00c0109035001d81000400080f0b410240034100703d4840d00d600300c9140e403000500140c0080740c2044030710019042010701c003041e4100000c400c001c580101e801d4554000d012180c503000203017000041504011820b01400e98900100300007070030000304008007000034080c00c0c40f4801e50300e08100e64a070035907982085980c1c0070b0012201c409450443c1c07051220f05890041d41602c0c1c4604039541410044506c00c201c0702460140c041100c0107458032010781e40014620031080b4840130202c000c502c0c21100 = true := by decide +kernel

theorem cover : BRFrame.Cov 390647482 390827338 := by
  have h0 := BRFrame.cov_init 390647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 390647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 390647482 ≤ n) (h2 : n < 390827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
