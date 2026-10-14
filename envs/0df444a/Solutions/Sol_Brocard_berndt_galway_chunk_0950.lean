-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0950
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:27:13.87164+00:00
-- url     : https://prove2.me/submissions/acd2645b-ad7c-4c4e-b604-b4a15a7dd647

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 170683453 ≤ n < 170863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 170684703 1250 170683453 170683537
    0x3030c0503010b090d170a0509030d02062e050d0b0f090309060702060309190804091802060d09050a02030706120b0f06040e1315050403080a201c051512010b06 70
    0x447d160659035003000103042c451000f24165020140390060484c1c0d110000c403503582d00e00d00591016145090741d195982d8554a20f103511202903602c68003c11a0400380900c1103410701c0500d0100300170754a02c1030700d0b030307401060340c001943c9004240ca0003d0080d00650402a1144200002040390b41e08200610301303c01a003e00520944030503401c102d00300c1e801511490300b0ba0f50508002c20980300e65030f100004c0d0790340d00410780ba0411082c00c14000081c080d5110840302c1d885100d0303206c00503030380412500e0010144c6030742d142e0b03d400200c100384090314050401c642c01b507003024912000301ea40341d40030348068502c1542100901d5458a40070342c1d9044c2180800b41c410415025003001007840e64010f24485c03406610b400207507413915401c00c81200c0b46803400883d40d05030301c91099a110b40b09401844503400c41411030400f190f01036070044c00c0b2070080c0ca40143c51030020003440150b0404462002221820000801c559182080800c0e51846010502e010022098071404a41c0441e0b80300c1c0503400c9030304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 170685953 1250 170684703 170684707
    0x34170106021c0221090f0d0501020c0c0d0803150d080a0509011b0b0a02030702030c0f070807120803010513020c030316080a0b450403030c0503010b090d17 68
    0x441019403141109501418403024a10764514880d00004100c141d070400051380960b4003c080034404240d40012100c181c1c0107101c03002848155071424003400035680100001030360740c3c0075144904d2130a189804210300510456801038040340156051720f9000b0346001c0c2007a5001c1014000907554405114020606080030456804040c1e00074041d082c058005e03280e007180100e2405d0100054100014000c02d02c0c071200e07002031320407800ca4004e190002a5401100e041098440715103042080c60305501306070341c0c0100020000c81508101d844010050b48002c0c84600303000392540c42840c44140500e038000e40c1c0a64250b135405c080b40d4111120b2003d110b09a94a9062503d0750004070045402c0040002c0c0d142000b040405082d0710440300039200c001d01e03091010314121041850303140302c01c025410003440181070b503031700389022100f0a84401610b10242c4142c81c01d4034024045441d41d0400400b0021305000511034905800211601c1071401c8510810017017452400480c0c03034540c030810078440100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 170687203 1250 170685953 170685959
    0xa06050303160c0f0b0a0f05090d0501050603071a0414191509060e0a12110d050601080d0c030c030c050115090f0b0d03050909040f020307030f0308341701 68
    0x6420707107030b01ca40c2c42042454851071380d4504101c121084d9026010404004011029580d07004001081000c0c4050030242e080ca031003c0009a03840718400030503200d59440d4010003046140034040e520180402507600c61072103058810030a0f00d400f96000380d24a440b030030074031506190b0310980480b61039091903828002142d1a2000d21403048244c01350340d00450003d04010070b0346400f880a00c400110040c00c403d8030345186c6603698680d0809068292039100b041c41d40e80300551980c4548902c01802440140b0300c551402c28442d20b4403208032402020400d80b105142d001035400344901e101c09800d8540502d02113010300300303580142030b002480f04142d1900d07040001c00c01c1031504290301e0003840301c90170011008a50207014070700880030030040001c4e404110341082403401e801c030107130013034000e041c01c030002a040e46c08a40b408005800a0740c40d24404a20300381015803114100d5403010300d5030901705d211808030041c501845030400d00c146203c004099145039451049103031243c03c08852020002d5565 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 170688453 1250 170687203 170687227
    0x90a06030b2d0106050d0b0d12020105040c0e0412030c020c030a11010207050103050c0f070311060406020403020f0d020109140414101505160f03030b061305040606020c0d0b0a06050303 81
    0x20075045290704041c04a0081a4800b28020524101c81140d1241171900416a11000c0103000610201c0e6106800700d9420380450041007500d000c54000390000940c505203818088050142035000d10303031581c5103000300f1002410750200184d0008441c20049a4000f04010507400e0181d41c040306900761140d50084410711148901c08034503c02c1c20307002d0710000c42e2034500450030f0390b404a80c0301e100b208040110346255080c407001421818001e02c0c2c1041e0070740034002e0507820168160f8060b00c407107030003103801e02c01e40c81c001c5c0c40e0711001c0500710b81070003042e5255800a0a400003a11405083d01030404074070180c1d84581c1c01c020030b0140c0c86160084a8034003110182c3c0c51100f24080c0000914804100c4000e686c09a801c6452081340219020709929860b940d03200402c0080a0840806441e101c01682d0340d152500030f01204007401d02541500ca0901062104031002588950110341c003031401c2000b40e80741c01e00340070402030704032482c1c1500e0354520114030064482d07a4480c5405100c005a481880a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 170689703 1250 170688453 170688481
    0x40b0a390b0718030b0601020a050a05030d05070c0201021908040b04060203031501030902180603010204091b1205010506090906030102071a090d080c0919050406090b03012702090a06030b 82
    0x207101d008401c015884826084032050311445a4450889000800b800811582408103511100503c12240703440070325a1028205118207404540303540c004100c81c01d0002d0b072402269401500c503d0440310000c240d0700000d40e9040d0007541b030382c001c804180590003402010822203015148030701e425a5269503400c0000e607281c1c01280d94801407002500c10544a6200380140c5034070640040c904a95141d4084881c00c3c804405042e440c1d1642d030030000000e5191540c050581044c00300301c800d48155440c500c01500e145401c40200401a103004010301480d95844261050301100b0b94903100f00d50303a0600483e00a00c9001e00282c8a060303c0a0f04a2801e051703005030034030481c89001030380c0c04032050840070341c0d014101b550842580740d0103000d0750206080c80c4d040355034600241000c48025603643d80100381201c0c21900841c0010ba01c0e500009103c3c1424000c0c1301c00c101069000c00d01c4c2c902194090468040c005100038410359039000469101d014941011004d150803440c0e00e03519040200400c0c6242c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 170690953 1250 170689703 170689817
    0x150310020f12010b120424050112031101110d0207080f181c110d08071709330901020709140a060501020316021011060103050a0309050303040b0a 64
    0xa4001e00004180748a00c181911620101d04410f05c140f610b0303a0f910b1151000030b0032000311400c0006917040401c01903500401d4024a020fa0f107543c803503820f0341030080c0012003502c10b803081e076810220341580f20000c00c001c07585100030094006807140d4280c0b6041c0014443e0311003101d035024020580320030742e03440c1c840d03c140355100480e469004c0a1200b190340e2001000300b4400f820b94903100b51110098100307510303002400351017044400d20380744040e902c210f04000c2000c52104414004180986035080c40030000d445400340c09010f02010311300b01c0b4454000d2074a0b00706441036400108620855900030050500030b00300104060000c40c000030b4003030f00c03a00703800c88682c03491605003c0c001070705500100032100001d507483c03040345d44800c1540a2100c2804d9042940c0304001d4000e00d40303901d9003014010303e40614440c10280981c104e81742001460781e1130981100e1311030b070400c0008020441c0c01c6c0e0300f1240c0050090034800c01c2a811656480f00c09180040070211305500d0103580c440a8102829141203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 170692203 1250 170690953 170690977
    0x90304060801120302060c030709120b06040c030b0913230a0510020301060503070311040b04060203090907030c0210090501060504020705010b010314070903060b030c040c08040c050105030c03150310020f 89
    0x51070380c1e540070364103403c5150b503005800340e00f1070000720701071070071400007075506c41c0a038100322600c0c9607030b48501e0701581c4286406640346042c0c107080c450613140034014481180078901e4203001000c60400040c1c0301030030103480c0c1c0c40407865101c0108208800c3c220b80721986800c082c100100042640106030b02c0d079102d010119912701480b07a00340700318406407003544d05880143c1e403120308594502e2000e80050801c1104611030300c60600c40056141100001840940403030b9001d191581701010034403611001c0a0000000d250400d81e440d130f9510707800121203000007046480480d90301c000b400d1540c01010503805c6540c0080c00050382805110054000700c07100542030f60100401403c61074010503122041e12100005100c00e4070420124040381c100002040c1d000b4191110080814001402c890b4002807110210f04080300304410300108001744d10003400d081c28070390324515000c1d40c2034840384402010f0900712080125000416201081340b03c1049560700c07402c543e00e500708001c40703550707801800528034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 170693453 1250 170692203 170692217
    0xa050103091734030906030e0c03070807060306050303030f06011808190b090c010203090d05070504050112021c0807082107210608031b0a1b0504050606070b0402011d04020309030406 80
    0x407803c416040d00d44040e0940c0e501c0003200d04041c0214043d042080301d103003091041502486040d40c051040c07500070180b081c0103003080b40c5080ea024090707036403940c002d5209406c00d0041144000160078025800310b424606040340e41e81400000c0c0c9404103942240000d4440e07039440880c10300140105810f018000c50080c084d0b40d0300d200486585520300099035005070010b0001c003078a8204542c10460b541d22600999440c2c54807031001c10100c2d40242e0005541d02200810082542000c410001360142d200040011405454894010034810a10b0090615a0006200307102160640c103203444d01040c001540d42a06040000402304070101c80c0030b018100c2518403950200c1140e10a0004845032100610306054800d000d1409080001c64814510302545c1d85600005500caa800003044011000401107030b0701701001d11040700d0004102a006903c00c00404000c54500d400540d071007942481e10203820a001c2c28034603180d00c0c0b070014013034029001002b40401d812000c000383c0300307aa100ea50385c66 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 170694703 1250 170693453 170693527
    0x105120f04150524010c17130608040c0e0411030a06150512370609050d050702060702090a0b040c0809060f0106090e0903131514090a0501030917 64
    0xb001c942003502d0010024080400c030000d00c00c1c0e5032000d40a10030341410035003402c1195440d02e4402c410640341038812058002a2412962140d0001a018019524000c4500c1c074241c0c2d074a84442c00b01d401400341c5403070311100150420613030300c103031540010026041d030701d01028904d070423006044140841004c5508400e000b00b014100680da100d14101108000c007610442c02400e848500e1905408819180781000b042c852048104030b03400405106440020302007080381042c81c10719102c0c20540c01082403c00226000d41d580300c06807008180c04860a13610f80e1502c480703981c003c1010710007168225040c031451150450308001d40501c182c20550a41e6141c0d41c1c1c0084070100c0007424040c00d40416160007050101401c2c000c1020740c040504021640b420307000042c9075100e1152a0320400845140c428a0380205a220b105144c2802e1031000302410400e034040011072039000c6005590405556082c10020b101d01c08454075a01c01081c04c1d9541e4428035441801403c1906502030b83c11094405444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 170695953 1250 170694703 170694743
    0xf0e0a170c0706030207060b04050f071805010519020715120b090103020306130606050a0902030a0b120c010309110d0c0512060603190201051b010c1209050c010309020105120f04 78
    0x44001801d08009068414181403080e40250441101079509a594205d4600d03039407a503201c0c1074003035100049003580d5071a00c001d0041810070200080c0081c0800024100b000345d80020a8901211888405909022a440c012482d000507544460310382160075080000700c0707401a00061306080c03809000d2110044000901420307840070b10000f034041d803054001030f643c0300989241c40c0403a4403603100441c01070b07030312000030b25020841d801a24030280e0000c01d0002004003131246001c24102541c1c03180000d0020b210568988e400342c8442d03418191644c0e0040d013000201240300d4483c000042049440c0310301c90030228080f40741401458001c0006032031402c081c0c03400288640c40303240c00030014000d0b00182c5095016851005c64202d0501c01e00f17109103240d0f064050000741c0380381009000060401804d000007000b00c0b60141c3c80c803070424607103200c41c40803403404140508004800e08011a4903601440122918801c401e1100306500e13030a41881001c000072180140620b000c0c0c41d050350011000d0b181 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 170697203 1250 170695953 170695957
    0x1f06080c091503030f0a021006080616030f021e120705040e010b07020a08060421090513110f0c0c010f0e030309040e031903140106020a030206010b0903010f0e0a17 72
    0x184550103400c80d40000c96011240c106010500c070b001d42524140b69079038610030703601d4001c01d9a08001d40c010207000d03c16246548240c500030840900180501e00302032000c43d8100c1c542c1c0c0624801c0580303030301c1031800410803501101c250200014103400e5880c0d8105070007c0e99081020b150741404070100c0400d08030b074842e000341e80580e034104000b0340b8684d180c10700c43d80c5603510228040f60007140101d4000b030b902c94288400d512803409215803c18072810100041707120900d00003500113000c02c2a1b030602030740d1a1100d03060301c130450440f0300140701011101081403600604c10600e803241e41c0001d5040c03001402180f816a0101d0a884280f400d0100c09016034910340e61400d5560183e00601070b01c00a4075252300203138080103485056918250940d0511103410f074100c5c101c680400d0b01ea4040165400101403520b004200e00e00c00f82469206541c1c00a44401040c403800c01d40c1c80740400e6071081d07070342c083d07200c3d240040401c0320400601c2c50780c4418030380760b400c0880e003561401c1103a41c0c0d4401d24030552003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 170698453 1250 170697203 170697223
    0x801050603070b0903010906020d0e0601080d02030a0c140607020d030606030504020d02011b0605010f06121512080c0303040309080d02010b010905011b0602030f06100507030207030b0403020f1f0608 87
    0x20142c8409070510780083c450b80c0003407008039410745d02e400080d000308405100410305100c18240c0401c1c020305214040d0300d0032106910400241e88040740c50301c9502d5012043e100444034a20300025461601e0400707050360325581036940303407500919040c490641d40001c0c187c0143c5505441c2841040d94800d4194100c88040724040c0d00900c1103040c440042d84500c0d100b03601108481912241400140c0320f4100f00d83c1e00360040f00c180c1e0b624103030911540350040b940f0700320a81c884009005e85101c0744548a0311700c82d0381c4284824030306440980c2e030400042c442901e11845681d41226220326044c10010248141c40c0b203800071601030b008130402000c0c03041c001c00020744d0042e1211000703945490011280d01124a1a860142840c103640303500103007150000b94090350078041158843d041101c100005a40200e0040c2c2c24050f04020600001c0c0e00031480f54112034102081c60301076a9941400d0b401c280311000ea44019006070b442c440188840c200c2880b5041212170b808008680e120051305a40f010038003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 170699703 1250 170698453 170698459
    0x1008070503010302060d02160c05031203011409071e0201050711160b0315061204030906050322030c0203010c0320040e0c0c03040f03050a02090609070806040b01110f030d0608010506 80
    0x40c0f015003441c400903c540001564018504840140800d0402c03460040c12a40d0600700d20040241e0700e0100240c6858400507030059146500d850180840d02c88424001c5014020013030000f0f030000e0050000c2c480c111090707000c00002421012009000300012503104c40440c44014907901c1c61540000c036107411000c04109500b146060640c82171080d00018048080c0340c80e1070004001945a034006800d008296154511941c103041c035014060708000d400c070804211040c01048801180ea540d01a0795000d1010000070803485030034216501a501c0301d000c0d4066080491031074645030306500c1030f4180c58400d0052032100340c81d038494000300d110340e00c2105507921040c40410300d400c1c0020001e0000b01e00080490345441d0303458145110b8068103520948517500082d4100f025410020b80e01c80e440041107502d1245031400702005004001c02a0030f0b140207998030b200c1e004050b4090040c2c81a0300d030040040b10104e0051b070307540c19600c0d8000b141c0070381b9480c10400005036040c4e0500a80d0f001707136401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 170700953 1250 170699703 170699707
    0x504060c030b0f240a050d06060810031101030902060c030903121602010318020d2105040b071b24030e0c0d140a08030c031f06200a0b07080610080705 66
    0x1c0e042016041180d043c07040131841c08400b50549140c1a40100042d2001d0340b00d06459010a80b05002282c411364001c00074421006c0802580340c01d00241c1e4000e40c0e60108100c410440102c0c0101c0082c218804002d400403030010ba40c1c10705000c00805884003030011001c0300c042c2c0044a80d40c2c1401c3c0150402c8000720808001e030240158042e40140d04020761018000d400701c0c0c015000a48000d203614004e9540000419824900362a007019418620081e800d0041c40c3c6417404d5501d06052042d0500501200080802810701e410740556038801000e0b031602c1b50311a4103040301d07004003260190885001080c900b046908480c1000318588224610013021a843d14259032200316429844440d48151030064220308400640c828018500400c00d0311910f54a03071500d0156800c0504da0f0756143d0100c910060400c02c29964080c840e12050501603000e0100d82c21240b40c042d140040301c84c0700404000400040080c4158000041c9110740d20032500d00a5005008105884501c01070303941500040c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 170702203 1250 170700953 170700979
    0x40819031b0f050109061506050f25020301060e15010c0809090405030d0905160603091101110a1401020a03051609030308330102210301090b0d0c090504060c030b 71
    0x180004641a05005018054800c0b00c5a5225801c603841040308032089562a80e200c1c40380703429544c8840181070350f420000c0c0b9100e180341c0c1205040c0612003a1b501070002c0c07032441e00406400411a846040c1c1d000c2c00900400c0d49032803a003c0c1c9890211050500010026002c1c2c9841d88140c070b0798484036030060700c02c40c507041d01401405081075000f80306607040c0c071082218001e05051480398440c0c05000340c001d03060a80c07a8019072000b0392110360101e010142400c0d0388101180d00c0c200f660300528802d00300035030304035240641c05040501081e005000828101140007180c84c0640040c400e4034071907601045182e50305002c0d40c0b940c0e440c05c100100000d590042c20310000c1d00841c881e580264001a0203d2610112035503552058007002c0340316120307204008005003d50301082462071054242122184c5070b00c1040c210a4103010501c281c440311926030100d64256120903800c4582c65810156807000c042d1101d81020140100348d0741165403030715010186001510901c141c00501000601090700012 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 170703453 1250 170702203 170702237
    0x10204050a05060921012c06070f090f0303080907090207080f0307090e09030903060c0301050d1115031f06020307030804080d060509130201030e0106060503010506030c0903060c04081903 82
    0x44041e6810170340300c40101e450100401c101c01c503503441010001c00c10522444c100264021842c5200c544815000140c0f503500380c020600503404100d23460080f403010007542c1d040700d240700980e0244080c201386038004801e0603400000c1c140f00d00f1180048622155413041c17058124425480701a003400030501c0442d60180d1746400464010406151107410542c5130140480e00d2102a00d03a019903600003e00310043d802c061052035441203440344001d0556240202082818803541e00c010316500750841c04041c07654a40c1191000000b03009084da4403860139111488084408a050141c2c0070307400e842c0064030034400000c03200c041d6810f655042e665201c0d41d4170180680c205540300c0c141c0d580c80e0f250100e0644c03584040940308551050540f10541480d00001d030440d8404a0750203c1070341040c00600c2500d0704201120f04580c0d060700d417140c2d207a46080151b0900d005003d90350380e00d8010318040c020000e5540010780141c845d4601901da14000e1102c803030041100e0703842e00030040303a408403444144070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 170704703 1250 170703453 170703457
    0xe06160206190b1509040b040b0604090b0112061d1003030207050103111207020105070e0303160209070909061412010c080a021c0f0f0522111f080711010204050a0506 73
    0x2c0042040440d118a01c0c1000409003210b002c96540354220216451881c5d15140c0100b5910440580c1c0402102c86030348007281144c450782c01000c565640f21940b11945912525005140007100390042081070f843e4800980c1c20380c0c405004010140076400440e184c2d0a48000003000c0f281e0540040003003924110041d0040e09000b85806841803043c8034406d18050019940b0b48910782c40d900010b250310308100040c00b03007040804481e0099105100c105100f41c0500450203007940c04907400d5140d50b40740c1d403049501c01d46030f400c07002e111410040000780000d001044585e81030720807190280701c0303054500300b1400c032040700b000b44000440140c0400c0110b18644d005152a0188402648070510650715030403d51b001039800d4802556100c0f214024019944103040c0c0120a103071001c40c01e501d48a12000d5400030f102805010480300550905156036240d5031901c941e011000e17100d00300321620a0150101c6000c0710580042814000314a103200c0042c0300b25410ba95004103201c2000b4184024840e40c0c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 170705953 1250 170704703 170704741
    0x50912030309013e0c06040c0609120b0417040513060509070305040b041121100e030304080a080a091e021008060d0f14030301080d0e0913060b0a17010e06160206 71
    0x4d24020420114100024400d0f2845540280f103159081850048000d01010242d48040c000081803c0510000b640c000c1003550402d4101c0c58000002e859042021807901c6194486035024040030000d0f00000800d400110440b0b40466240c000c40c0d4440360146c058a1301220005c18890030280020300182810500c1500781a01900e0603c285001110422000084918032007039030780310304a00900ca1000f0b01588510b021a440618107608040d900c80805000b41c421600c14004200c00140c80b05040b54050f0324450f400c00c801e10790406006c242030ba059034403450305a00031000c030303485c042c121406640540c3c01510040c0c0018425040341e141c020074008000c1d402c84800c00300e03810881e11040104040d50182412074081d2140641c028000342000c8007601900d40900300010410031082401d04070410010307000030000c65020303840400074070102c10320703001010100061001c20342d8038203055201c01c1745211003104940c00e079240d8140019280890300c40d04001688040009240c103500c0303200f00100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 170707203 1250 170705953 170706071
    0xf0604090c061214100315110a051b0709060e0604060e010501050f0405040903080609180705040f0b0d0c1a0304050a03110708030c010203071209021302090105091203030901 76
    0x481d10303050180607080d0400c2e60f010503080740d00c00d17060051042c9081c6600c0460700b0110b04010341800316800200b40d024045a4a040c481c01107031075000c0e5138401c09074032041c1080a050301c22383e07501c43d204500101540e000748030340c2d044004002111800c0600c100c0c400c0d50310b10400001d880c2e181c0001102d550f031040b0710328240c4005c140000100303516580600ea413680c1c466196201580b400d081401040f400041140440001d2505000c0d0f507841e000c40e950065a00c286d03804985000140b04480191246907052a04460703500081014490000034040603912864511411083c050103500c1244c0010740e4050b0407030300101c1c0000c1c0042c0c0030b840d680135401d035607000380d548043d65a500b050850308404692103007079400004000e0038941c03099800c4803030a03448808100c0c81160b0f8020031142424100d04031400360b40007580d0495030703010310700790358032031400078080f0350305030326100c003140d1290410b07118050190b08180305080c03107c54107003d1100c0b000d01f80080040303204107100c10009000e4004c2200c41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 170708453 1250 170707203 170707211
    0x1107140105040b0712030b06070b0c070f1a090f0705011d0307170607030c0912020409030e040e070320010c1e0f0b1f0f09021803150f0604090c0612 65
    0x2032184500c1c2e004c1c04070280507106100a44054250260903600d80d41c07403451103500c0810075540040d103000d44d0b10350040303038150050703440340700350f20380301d400010801c0014103075400074101000d100c0b610f0000507101d540c04006032004024541d803c1d0b43c0e00d0030107000da1804203004e140c11b59030091100c50781c44103050004085440059882450b084890402025007580c0e40151003086070594240c061404069024908641074518019000b4002c19210744c00030311490311803c0302c1084c076100702101841504010700402c96510003410107580c0c0c200c0c51008440100030200c1c00c16400e40105010350b90048103840341c0451542f0380e69070b114049148000350000b400340240040c0031a5901c0403c00b1090710500c40c1d0300712400c090078000030980013030002a643e200000000d00248229609140403500c038100090307103800003403041e40030042c0b20170101905407040211840071040c02056183c025028055084030360b0f100e1a040c0026100b0303030070020708410481e4000700101c40c4140c1c240c058500711307070600003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 170709703 1250 170708453 170708459
    0x120c040306110d1a0a1205010f051303030e0601060c0212070e04060203010e09070503120a11030c01021b0106031a07032019020f060615071403040f06110714010504 72
    0x1004031882c94820340816403011505040e058030610814600d0f071036141c000540c080c02c1ca4005041c009450040d40c0c003204006c407800081103401d4102c8041c054000c0001e10803881d0a00b01d034035a1501d0540164006820104003488a602c081270107810f0311f4aa9072084400f6610f0380a00800c0d2528500000482c4603000000620074503144000340124416940075030b0340e524000700088113090140c0310100c9a008900100140d6800184030303900380d0900202c0307035200c22a180054640801d40c40740410540000240e4243d007000641c003d10401d51200004a15641c01d5810342e4220390b82d5000082145181c02c00c0b401d0b000c22511041680401a07150115100c4280a0110030400880d906a805000040f0b010040c81008600601c0d00711018801411411542c9e00c20070b942c0c0034042c00c598000d1994440e4042d000d4060011900c80580104900d00d13148003a00b40d2aa0fa907000d8800c04074914103412000c03c03840c0c8110801b1030440054001402240d00788070303032851701e502420031644c18410200000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 170710953 1250 170709703 170709713
    0xf11030a0506010906090f020a02071403010f02030108030703091d010501030f0e0d170106020a0c050d03020106210210171f0801090303050f0a1404080705010902041a01020c09070203120c0403 84
    0x50380a0710100101103149450201006c040d90780741c007008840240180b06054a081d40050084112481e42168045c81204080800d0051089003030800c00c80d4000400030400000000051043c2e501c2030742d40341c004d85d549400800d00c1007078501c600030703194101c00300401c602d62090b00310940b081060540001c4052128200e54904074283c0348000200744104490b49002c590f10812a00400d8180081e0001e404c060f030710155008440d00440e44a803503841d074020141807003580300707034058444107000b17101c1203890410003d540e80792440128464900c404042d00418890030000d9890000e001d11128030ba1103c1c03003032030100305400c0110f0458074240c182c00108000240a016001d0340692000100343c02c1a25410500d1440280205040350030220b12881d460a2240e605501580091655032640800e203816805001d61840203580641001c03003088080c46030300a007188221098003164600842c00051140318901101c0d0140580c0050140c5000c40316046450fa0b801101d501115103401c1d2a6564 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 170712203 1250 170710953 170710963
    0x4050312060a0e070c0501061707031509050312090c03010b01080402010305070c0203100921020706080406060e010311030105091f2403050304080709021c02070303150b09041103040f11030a05 84
    0x14080005080248170020f000081c402d0340080c00b8a8502500c12000c503060541d07540d011440010010b514500c002c640b0341c0001d40c449190544d0080680f0781e00c040012102c0782d011001d48100c441805890b2110505117014070070130b01200c00603150410302d5a1650019401054010081d00500c045e100075580140d400f8007a901d0500000c400c0000d04204508012071001c00c60343c001554410303a000c141c1045030300040d40008480140ca008800b5030307200c0c5011400340401e0b901402a9440060001c0100001c20078405142c2400764002c02065036948040360f0b90342a1464481c1d41e0745c00f9000c0c2c2c031044001640100380ca60051541c10b92180d007203e043c8000518440d4426942508003090921482c4000e0040c00c0080c17040c11415818034001030b1002103514000802c0c1003003260b00041403401c060094004013600f41e03c08011464003030361480c0082c016030018246031b1140e0703c2c000c81d4542075100441540c0c001d40c0c20900e04446002e050380c0d461120110a0740e126454130032468410001581000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 170713453 1250 170712203 170712211
    0x30c10030c0306050307050303030c0708041505090f06120a0e0c06030c0703020c092e030f110112060e040809010c0206160b06010306060e01120b040c0903150504050312060a0e 77
    0x2a00091003046188010212080c907049648a900102c100f0007d65a0000680341c100c422165200d6403008a4a071900d0f043c0310300c0c0d22001b034036405640e000d0380c0d06030058060840d1020643c2d2030420903000ca020841c0f20b108950409201704e0000c8046001c118495106d64101e0300c42c0400c03540c0d00c00c80c444c005000c0342c00444101c6244140000c0b03003c2019814000d8003071100d03041c0c515442c0c2c0c0c2404041040d0540542110f0b901e901c1c1244401c2c02d025801c054113100468010004495030380060038011410108007421034007041140a81e00960302d0280300382c0041703c844503408a41c07500c071683c03801410b61040345030a0401000292103005a03440740c0050158002c001002142c54085103030000070018000c280c6030500d454080204545500548154190304003403a18101d84003188440300c1c010507450031020381240c0b0300104600040e03001b0b004801528010aa042e161024104000382620806c030b500400c0d82d0418802e5040404400c0c0c001608080002e051280081d194a80303040d0049040b6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 170714703 1250 170713453 170713457
    0x302040f0f17031606020703170f240303070821010e01030b0105042310091a030c04060303050f07080c0a08120a0c02060612030712031e05071d030c10 66
    0x20000c00010036a80d84401109142e60003440c00e102480151508480c40380320b02400f201d80014901041612851103c0318103000d50121501608101260300c0c000b180490f01042d82c0d550945503180301d114121891291100024001d600d13084507596034400700d03000785041610500c0c410259820500103030648034085c00642410000f998990b00b0700b208a0b80c07060b40150f000768a442d03101d072004540125031000f110102c800d140381c179803110100e854000fa8550300c00c0482d44d203800c0200c1e0900c080084a0031b03c2000440858140220b03410802003203800d1484000c020400c01c210001c0706504c1d62003d0f0112034010124075080060040c0c0703a600b40840041d040320701500c00501c002d0710f1485001d5003a04200c0c4900200104000e03510007940e9288080c094074828034408995440360f0000300103e80c0107660200c20b40f520130b00d03e600c016018103100e28503200e90303a01090307506241c16800c0c42010310810301c91f981d10400c072482c3d81003001c00c3c4400d41c481030380500481c040341c84e007078a83c820030782941c814503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 170715953 1250 170714703 170714729
    0x51309110402071113020301050603010302062109030d11040503070608060d1b050a1d04080c0a060212010608091b060d0e0d20070810020a05070f030507020102070f05011d010302040f 80
    0x13504000c8000b204400002d90240705000510107a150602a24190b9a042e0390350340c1e844400e03004400c10a0202040341421404081c01c00c0400000400a0721040c408214280240801c10040080300d0055000d03880e010390002100b004030b944100002c50f00107070060107407801012180c846200c06403001d10005401c158850702040701d41003401002e001000007605e031000082c25400214888500900040e2400c6400b0800c5d030f07a500010700150f0007403903005100715580c0c541e0070f43d02c070f42e00d0500b48500004078181d035000a40c028008144c09901c000500113101008209004220003a0030400c100c41205544900c1c1c210700340d204201c404800021038481c01e948100280800c100c03404d644800c000a9000010100410b10000a498800058641e40582c8485a0450440b101e00842e03402800d0360312003040d81000c0c50b801c000101540c40c000c1e0b0070341300d065032500e104034015291031182781d0000e20741d00f02c44a0102c1c1c0001c03603041003900514002d460146c0d190108051030744070b6001501c0803409 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 170717203 1250 170715953 170715983
    0x917040b03160518010f090b0d051801050403081609090c020c0a050102030c0309271e0f01060f050903010609151e060e13090804090203090c0a05130911040207 70
    0x95025103405030b0100785407162414010b9a00390b0041059a50558103011000f070104d02040d00030311403003001e406039842941c3c84003a41029540a0082680c452464a0520b44921038100042c01903034460f81c1c0644452181e40ca0740e102d85509603445628840420203030060201707280069004a0122150315802402401280c1041003022009035000c203040d5807081107441d806210100540d111440e04a03151000c1460180054140d6030301d140245000003441c00c00c211801140d03008034010100f5231451500540c0d01d544401007940802e0240780c01141040608002e00c07445000141490740c005400815910355422034501920361040a41179440d00729042440b0900d615240d800050900c4841c1481085c50a14041c00c0003a0a0303015034000d000b2200c1042e11b039102a0060181030303600102195440c1c2d501d0045600a40064601235600c0c080e01001c00200c0c507180d80004203481000f0520b510324141c1c915400c0041c988580100c03415081010814803a0741d8070f1014200b298029450700c200e10308 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 170718453 1250 170717203 170717221
    0x100509030105100e070e0409051006030c06050c0309121e0607020d02010203011a0c030403150921020c0105090a0e010312091d01090902040905190b061c060917040b03 73
    0x50042591280f110140401c02c0a0040000680e403c800d16040000b861052800450050084484064020310900603c801e400c5c0450b4003080880b401603e041428503124002181d09100313000c6c02c0724641e403040c00f401e441450501c080701e00f08601002200c0008802502c0106000310000307190400b50004d604015883d81c05103d800802011403000b10718542c18000802c5c03260301e0061107904545030210310480d4107002007003240c020f150400803c15022980c0c0c44000c000d006400707001c179204408141200900c0c00081d11881903001c194016020207010b21004468581000d1103195101c00c1c2a140000c5440120704003134040c40c0203020340a2428030240c0040c00c040c20301c1e840350011840404152030030301203460782c007030544444440100c2c42c0d900500000300030740091a40680f16004042c070640501c46010030300c800b02441103191011990f190000c04c002003000008401c1e186030300305100c40008040303510680c10b591240190360b010119010101d003880c0c000e6004086049800030911000034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 170719703 1250 170718453 170718461
    0x504060b040b0a03060509120f040f0603060b031f15050903060609090a03050c0a1a04020102011103160c050709020a05070b0105090118020d330e0609011809021005090301 75
    0x40d02510180040210607011490b0750b032041c4400f0b401c1d0b9075a0401311303071881e02c14071124044494015405488091410498006901521542511701155500080c01c18024054241102c1c00e12161906550707410261980c04040019501c41456540038082b0b6811602d50150326290640d13901e2940303840d40c034800d151500c60046c0909100d010050104942003900041340c2c001164149005520752008076021403414440040082c0031a92486008c00c01a4031441c50038441c9000368024090300b50380052001d90351000356424001d120884031406440c074060540346252500c26411200125035400c0c01074100c0c0c0000a0500c0052400101c100501002d041580c6c00b404080740c80741d0407035251a81c4d042610445400e0b8201180e00402c0d543c00c07941440d403003000e0003891030051610400942c141414808010301d81c0c901c03007000840000c10b0803503030349880300d1280001404c00985a400c0c01204981d1510f02d01c0804d030b4803074035002c0f043e0040c0c449410701262140b2035150f643d203440031901003500392 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 170720953 1250 170719703 170719721
    0x7090e011424060a03020f0d0c120c1418092e05011707050c1506010f0e1c05160b040911030402030c06180604080313270c2001050406 59
    0x7107164118025449266112003a0a1401280c0080c0d4891140134150040c1c020300b81c890100305008655128a8480e40e00700b8290324000ea07581c100c8001e0000622000c90351460320120015204e1240c6030104608080145244400c0549040b60751001400003510642c0499414495196903981050078000360a21002400380e00105150034500f4400002c1c0b84004208a46541ca00c0301004520f0282c000c0741240c100f41c41c120700703480560440c030140d0a00d840040e035000b400500c060b4120194240714907410108081d00034641c0364600035422000e288a54007100a4440e030246038207410103002140002d800414071a03d02c1030f11146000000e41c1203444282c3c3d44041c01c00100308000c0141d1f4040f622032101c84040f5642703621440c1805607602403a050380405500f00380006804a0f403080000003500341250200b1100001d0381e264500002c0c103402e0403114002e080002c04429030385519542003807034140314a03e009070070b900100c54030031044801400e13604601d941d202c4c10b000c02d020260184c1e00d50 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 170722203 1250 170720953 170720971
    0x1140102070b1c020721030b191a0c0708030a090305073008091c06050702070b041a0904020304120e0f060706020c01140403050c0601050a03021e010207090e0114 71
    0x3040e40100507243c0e58291980056002940040c3c540208001c00c4c04a20403070f010303100700301c0744080e0405000e00101030b0360319058410420f41070004190b28200140b4425610f0f2031000101c81c6c1920b00610b8003680000c03030050340e14090b1010208810030300304090107001005903a034041141c0365041c443e082022680001000c007201d44244031038043c0418400b01012514030003043d8040312810001b045000794000701e980020300a19035108034511200c4000000c2c000c99003013209442da10720981e9146400d103e9000407083c18402007007100040520030144a82e0344031014330300300110000508903842110122400110f17840b081d00c20940c4092032488804040e01c00c4041300c1440000108280a1071030000c0c030464000441050b60b141c01e402070f0081c080b911481c04118103084c40c01030130617084036828484911940e4000580307803802c03003441c004a98015102c0000c50a11100d51001c6410155080381548a071400c001040b10043c0b103020f04810741c1c88000038039100c1c2c2e50820a00c694019100c2d500c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 170723453 1250 170722203 170722207
    0x10602060421030b03070609140603060102190302012d0e0106080601090c020f03040f081507120902040e0609100c03020304151806051303091e0e15030601140102070b 73
    0x40020560b418040142d2460039a00080708030801d400c40c05084400360440d05070288000000b1119040203401c41a40c44100d200d04082540c802800143c0c0011225140113034440e900380311441150783c850f0000540288000b0802580d0444e55070035001c820741071030b204144100810310002e58248030300f04c0d070b8010920090200361318050030303950744101c1809282044c07980c071440c407040f10740204451540c1c0e207105002d483d1115a689a040030354a41c5115865217401000022503034496040e084900c0f40c000741c0c803640440c5003c49450002010215400c0f40c01c1390307232030a014940f105d040180718450400d05004050fa003c3d42072803082502c508110960506005100380400190800036091200413228000a25107c1c50340c001511640d610801803c01c03407610003030101c4002114001d007450350103a10f9465080d41e483d00304c100614503824100c0c1d406408184103110b551a400c44081e00721601c189001500d00035500001d041080aa00080c200720f08180403200c04d50701840488002c02c200c5104c54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 170724703 1250 170723453 170723461
    0x3020a0b070807080c030612011508010b010c150f090803180d0216051003060b0f070b010b040b07020d020109090e0115060207050604152a0c09060b0f03090f010e070e01060206 77
    0x504581d0b000b0b00444a112070103c001001c0340ca80c02080700201e07082c10000c0c480300404ae490090210304a0040d040c0d1542829140704595005000181909030b0180d402e0020840d2102c428000b0052480d07041e9501762030305d4601d80400c2070000614090019032a003c412481800a52450a40c420b001c90342550400a62003026441405041c002c03240180c840807101018000110000e1110390401105030754003040004196440c00040d00750180b0800b14101e090741c903000c184890f400303180b00c2c0d0300010008002c61401414180340042c91144107040602e480384d1101ca4000030f480c0c204042c180103079524040c000740c800c040581c900c000c00c1180094001e1318203100114100e0701c114091134141083d044012052603100b4611505a01900c0300a0200340200f9581090352075000001969426145503001c125a001d5120300c80803140f03048456850007400702205801500001d00c080958090032483c1707400f5a40c28010300f518100d5140c082c242c0e9505110158034005d106801110071540418104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 170725953 1250 170724703 170724707
    0x80912070b060a0f03030207060810050906010507020409080a0c15020405010813110d060207150c050d2f070308070e0f1507020a0b0301060306050d05030304020907090f0303020a0b070807 82
    0x100d11540e041400391415503500701c007282c1c680300302d41c0c030401c1040180321000040c540c1c0480d41e00107031012a550803140307407151100b4802c000070301e0007829840b44110000c20450740c0100020240e82d4405000031502000544400600360401514400030540c100c010700100852104071601c2c5040c030540031828241084c000901d40c40d00203140404814007101c8480c03c0c86805581100742040040c88030703d40d24554500800603401101d03084940c40024194008000c185014101c80c007601540c905003000d4007010004068696184444601980c07004800c3c260720b000703100b0300300c8240d0340400c80350388400d1450000e100203002044d0008001941c03200705c074581d441c0884240c00a42c21506007030341703c0305061580c1c01803048900003980404180c5001034090101e80c061412503540360cd0401401e079491083c050076482a80008050703030006c20005005190181c0055044601443c2201d02c02d030304d881e401080c40e02d1a802c10b40140c0e00101d0300108102810701c400f0340c40b080d0352600151508181c400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 170727203 1250 170725953 170725957
    0x12030a0b0603130f02030703050703110f0103090b0c0a050c0f01090507050a061b0206040519061b0503030a020d020c0a0f050607031b1d06070f020306131a040507090501090c080912 79
    0x70007886a840042c0e40c4c41595010811400519002000d807055165a868400c5c902408000e5040c02820681c0b0380c110258000e00c074140005800c440214541c1c2e41d42d281020f840c0d400000144240304040c0b00014105a041103c003034a42400340001519904500f00185003d0069008d41d20501e0036080c24401c0a038411140c41d0312541e46a18500300c0c00c842c0c0700092042c001d5400907074000d0038000c48d03008804143c0f00364804031466612101d0941140d4003810302d004417a0403018143d40e01c10030114404910a034010050100c01c014014286012a0300c1203080c580341401c01e40d0060911181c04d030034000280025500100b003820200424200a207040c0c00e03040c074400003103040c040c3c0282480040c080c0c3c2c900108000c1001044c1c42e0340c800c1c844c0780c43d001e0708040100980c003902c5184005241183d4210040c044243c0010920700e1506004002d00104000100112000e02803540009044c1d00140030340ca0180100c0312011800118010005100c3c00b0010280501c41c0d0064413010314191040e42 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 170728453 1250 170727203 170727241
    0x150c0d12060905040b0402540408180613030201030c0e06030c0a0201230f07020a0f03120b01030c05041802070b0c03161106011701090512030a0b0603 66
    0x52200386085a092210000d1039503500038421a410a000c000800c032901500900c10346c030072100d119100584001c8030201400000500c40c1206540c00d00400401c8070080e0138012004560303031880d144084a5400c0402d25042c0c03070403644490042003107681c095104010410302a0103490715420500c1283d04161000349a00c07019040c15603490342d0300d80301c500c04d00b17444440e80005803d8542d24200b45580c00e2442d40198140c0d001540303040003100c0485140e01e829031041d2289c0c402d0400030388840d12012070b40240980808298484c0b01040e400041d42c426030131300c00c64000c1d103c2c08440d55400e1002807c0c0d030050204513042500d440300200029400c40d0642d42a03902044d01c9230010001c3c40ba0240003846610000b074440220201009055500e0400071403003000420703404400800c41420035144201144105030554100b80c005005140401451002c1e018080d00046002c880c2e5031103060600440d0610001c244600004119181582c0d018081c0d111070107176005803a610304000c580c4005c07038480e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 170729703 1250 170728453 170728457
    0xe0906090c090a150201060603051312020f160501170609010e130c08010f0605090415021e0d090b0601090308030a0509031306030c12050103030e0f060d0e0606150c0d 73
    0x44041820800481c0594810060150400450549512000b42c0b59550300b8510360040d03003403a0002c81c800c1d109002e12030045a01c1001c4202d070310400d41c0c43e401c02d6600340c20080c0862140c034040040211040041c2c600600c003d01402c2030b004d050800040141e0049500c0b41110240d00e01880416250110951f04441c400c0079141d04075120200071840d940c2680c80d018100311410358000c11102c2042d0f0110b0b0011080601c1000010364030707401c3c000c1115041350040c0c181c000c03d900d810b91b408281d400070511140c04025500c00b00c40e09849123a03054001c0c02c05c2c1d18060390784d40001302c2080450409140c0151007424900d2540d46981d0b01e038a014880141813490003030700d030030104146c05010001d41351002c000c51082002c403920381000900500c2c12905140008580c40c080700d1b03c04450744560341c141d82c0c051790382c40d48a601807806e2040620003007104980011080009030070030407140c80707281d80100480010b007055003440d501308036076a040b041900c0329500c002c01002c540501c0000300304015140314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 170730953 1250 170729703 170729719
    0x1314040e0d030e190c08100c0c06020906090402210a0b030a26031e07030207150902010e040f06030308060f090115020721290c0708130303080609070e0906 68
    0x44582a0402105000c003d85030040310044500300610545128142e90281d011107400d50100c04a00e01550b01d400c0e412380c041180000c156000c03400c20340060500b0780010340a58600401c840100341241e00c02101c4803403140c8454444001c410ba1590003a801181c8a0300900c400c2c460140060380f1640403c00c000e14145072400510f4414044c0c140c2403010004150000d0b40300d15224034083c0401d00303a0b1f49680e24030001c24000130a141d0003407082c0c8100b260000d02032000c52000144d00310007801c03119020390501c08104666940c560b600e006922110703510510205c1c4e164031394603000e000300f00b02511aa00c10f1110151944d9030340c030769020080c11502421300e40c5d00303895a203c10503802c04650b81c0183d40207020303402042400d6036910280075031140c4158a5100202d4030b9141801041c0e6005250030b40c250b43e2200481e003605180e2002d022090300a82d0128642146540204400040c550040300400d0806080107a50324182101d194400e03902d08081000b000503034009034002c18000c0102d881040d013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 170732203 1250 170730953 170730971
    0xb061605070b0d0204030b090a0302030d050604020c0a03052109030906070f05010e160b03040b06090901110403051006230d031124010602010209010804020d0602070203031314040e0d03 81
    0x100718000040800c55941c40d40c403400c03000b41101a42c05404140e40d03a040120100d10b00c208005600078459400d58095803e01c01505008005010007402a6501a4090080364100c0d0301c140003403074495103e0f444050fa05c0c8004074a800c2050201c1400d40000d00000c0d0030084035003404030440d0003042084a034642d5030b080c00e140030601c20440d10300c007600701e62801d09900c1c8031a03000981d5481224490b1000300070b00d541c511007001180300482c3c00a065981d90004103182e030a2003840c2c1a00080003030000f00d094420111400069001903009840e10707480842d5811148042d40301d40341c050b102064480c030000c0d400c1c59031a480c80c40ca80070880d00031940c80000700149842650403125048003a400d41e01c0c0e0305002e20a02c40f204040f115601c032490030f034100010700c6a00500c2210421030040e181c2d201c00f81d0b182e0b0204030340004128800d80f88070380c08111280040e84c0501c0108920200d100c0426406401c0c14511145581482886401a440c007000b01d40c1c1e6038400154420303102e440b80b40200710484 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 170733453 1250 170732203 170732213
    0x3090f161805071803050105040309210b07020f10150f03050d0f09050603070f02060601020c030d05031b040f030606150801180603081812390a06120c02010b0616 71
    0x200b24844211130003410100441001419001540250b01a0b40d4281c80c00b51114514100351100d01141d9a04141c402c9140b03002903c80c52100d6808500d0340183c61046144042c0780c7e08003540c10400c0b8a415036503000d40c180d0041ca00700020301030300342c00d8140002c01d42141c1c0e803250303101d00c07031440c00c0203000d180803400c4030f81880348084202a003400750640b078881c01c1601c405403200504403100070141c002d07440000e0f0305501c00181e804030044002c0c0203004001e034a02060303035140d0020300748003085100a22580c08001c0080e0080c4003c040e0f81c0d88960750781d8a1406c2a00c1110091341108008180802640001e15402041176044d6134400741c1c01001d0b107040c008100000c1080c0d43c0000c09440001c10200300300e80101c9441000520143e6885c0441c030f02410105440309581c3c3c402c2d890581c07026540942d0742c1290b9640c0c12440420b5206180300c821503000141d070070100303030340080c0000d8024860244049468015000841c1d641d00007804406083c40014089011307200e045e41c84641e260001c002400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 170734703 1250 170733453 170733467
    0x1b0307030503010b3001081b0f13020903060f181522020301050a0f1107150c12050c0706060605090f040c0905040f05040b070203120c1e03090f16180507 67
    0x207482c658003400c06044c03030a05c0321032100244100d43c403034011048803524100160b0015032800c1070007080300c405080c140e000c2105020b6039a600ca00d00990034070907110f554504100d05070090401006040c007a00d004410110100c85c0000786070349a4005003030a4400220f03604801e40c21214406e90340046c18115220703000100c1c14504069490b40c00c00d028400d8082e200c0c1c2c8602240d85105406100d00500c1c08900c0d0110b108480004102030403450300900e60800e10f0780040c020400629020500d01c20000d1f040d07080e07034004d4031b00c0740e803000c030000f164004c0080c01d101d8a401411581403172800d1001050000e280d46003d201440d002e81e0f181e10301c1d0000b00e1301ca198076101170600240100049450840401c0c000d00080740d0480d5503400510200798500e0000055911007000400340b0744d45a682c000c0340c000d064004401017810f01400b26150614114018082d5100b01d0000d40101905820240407078542001c0e02d007500c0b00301800410a0210a5841c401c1c0700382c09080b0701c0c006c9220384601c5411201c01c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 170735953 1250 170734703 170734747
    0x507120e030109150c03020c0615041b03020306030c040b090601120f02040f03020f01210f0b10020c03010f060f0302040207050c03240901060605041203110f031b0307030503010b 78
    0x19440c141c511000c010781c510b600401d440ca2010b0030811417035100740070f4040744909809030314168402400600c0490700d100340c007202c00704007a00101d48510400d0510070a00b80031505000840d030013104014075410100070004032a10200c4050016008110100d41c2150700500b0b441c0c1080381440d1401c0c03c10003207400408841400c1c200440d6255070b520310701c0d00c2c4010b2a020807849135000302d190b500c0c1c961041d4400c13402c02580742e000c0710001c00d00105201c018094500c01c030301032586030300424030750f9555a80c200240407165000b6091080101d020903013140e8004555245032407504c80180322801c601080c00042d25419100180d60b40b20b182805d41ca000200340f02e490340352181d00080c50f051340d0340c1006003006038403101e07482d009521244001c82c02d9070300600902002076002d0008000d8a140301c03c41342c40c482d01a051104050f0700460545091021000680801d5440003d400d0170590540c40011039070a6050003440c14070009a0300100b50f0711061180c1805803002240401d01201104035840306 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 170737203 1250 170735953 170735959
    0xd080d09050303090c09180303130c0f1d0a05090309040b010c0c030c0f09020414060f1e0405030d0507150b0102240103140307030f08090a020a091b02030a0507120e 72
    0x1249422481c40307545e02c190301040c074001d19114000c544c20b040403802c210783c645440710155007155903040f03007211042483c2206640d05038030303a20b00045c00c208100d40c800c00307441804412107942104480500c29180c010b0002c2c002c01d4074100400007460804001d49510000486011883c0c030385c2003004030f8142c034401c44058654007400300d000003003200d500d40e040101c40d0b004412200a603034491000f000c900451040c8040c40c03070303070000708a41480c0241c0105800c4000902e52810443c02880840d0141c1215100c403540100000e000d010ba89010010322113482e00500d0014641603143c0e45000303d14402e1784850082c01e4039a03200c5800341c0e001b8420f030808826044681c0c181d0003100c14040995000a12040e02e0560040a1000c00d00038080216000d5035013540300c2c2c411038042d40303104454200000340b440d6002e00440030380c080181e464028020050a10800100300a010303034410300c220701c04850003203080d580704002d28104145c101d0140c40003580c12048224821111480c1030ba031882c081c56001b54 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 170738453 1250 170737203 170737207
    0x40f02030702010e2a0d06020d0b030c040b030c06030408090904050604020406050109050d0f060b0a0902090a08060f0a020702040b0909010c0806030607020a150f112203020d080d090503 81
    0x10101006501952080c0d00e140e000f0303c691811803404a440300481c0c089040d00c170040d03581c1410b41c00382034001020500f501404c1400c150106031620790498006003160681503444902c00d00a03881d0030408038403890b1080f20200100d50740c1d500000c4d611422102d40782d0013100301000080c14040303400103a0750300020142104a4618003031501e00d40300c1d4000c4408a20841c5071140100d580e5205840740425140080c01d0b02918034690b0700c6482c806c1138600c4046506546400c4001d8a40d10391001007801042103d60160b16003450300100301c050b4403da04840d803d0340c0541c0c100f10504500c0151503810200c50310340181c4e115214004580a400c0010003142c01c40c01190a000e002d034415400900003403203640e21800d45032501c3e8100b40d2540f40988003a001684a21a6070002c0786d04072001c440b06070044000015011030842d00c40c001d0b11b03100c1c909940c9801c0003162011038104464004d03003034400d00d1902e02841a0550380000d80004240e0301c060114070340803940c0e000841c050b521000800d500441243d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 170739703 1250 170738453 170738471
    0x603010b1005071502040e07051b01061205150c09060711060a0e040e0106080c04020a0201060e1e090604020a0b03040f02041a030c0609090105190b07080a030c050c07050112060504 79
    0xb0b0041d40c8030840032a004500b003a0f03c0d0202d51224425101030b03512101100400303488281c0111100e400c00420349101030003000720040441000d200c3c44008040c031501f0342c20a0b0360141000e504081403000c850350401c004600300728800030644101c68a00701c1c00ca484940321855410894403400441c01516001040000c0a405403900304420074106501200e0a01c01e040803242c00720300b070307640a20a6405589c0211700f80300084c602500600014000c034400040d49590b41c4d503845946010a607440d080c69a025941c00d094514424040d55100100340010a003d0030180c3c0403074170f00322641c403400042c1040840460100144810b5034044c0580041083c0545001c0c03540c20756503241e82c3c4002c00d110303204034048010103042c48010785251103001081c4643c640e19040901401c0c0150003180d8080d081c0c00c90003c5103411a0001a041c6140a606459100c2d01900c1015086514041149040c0007003404410401940000c180098500a00e4260003500c40c1c0075007100a4411a0071003684941425848 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 170740953 1250 170739703 170739707
    0x311013002070c2301030b1c060207060c02070806042013140a090312020309010207052a060702240c01020f031e040b040b0603030f030a0c0905030105010605120603010b10 75
    0x5092514050b665164032103588500b03801441000c0744980016113800329090055600992008180410142c0151300c1c19040e00e01e00e485406210504455032a408110001401614030401e40701d04083e00041400c07030700b00742100c4d0383e8000088c0001d01ca40740d4080a10549001311480e11000341000d4482826103494800c900050903180400c22010440080090400040ca02038040d1107034168075280959500c80c90650080e50008042e050150340801580e000210200894020241c501701095840380b108005590181540c000c4036100c0d200a01c01480960b8982114161180b030040403500540c2202c030700c25506000f800c200000e5941b0208003c3c2c1113081801c000c5200d07003025a40307642e0f18903404414403401e070340075070b0040c0000d61200b0000d0002a00440002e40048005080320304207400303400e1014187e482260440e1040d0b4a0b6100c02c8000d540104404016200440091055605100c0700820500400e003140f00e80e0103100c4085010794a0079401611503600150060103034111903000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 170742203 1250 170740953 170740957
    0x1b060c060552051605070e0f0a0f0c21060b040b04080708061005010c060605040204030c091a1c0f020604080105010e0702010e06070f0512010906061103040311013002 73
    0x101550000ba00942c90110308508009040480e648810b070401400c0e68601c031a80d4400d54049a003449220000f00c2d6807501e10341103d1082407401c01c1541a407400005850581d0000740071954010b0421400079070355038012551241c000303034238404c0001c5250410320b504090004c5c1c1c0d105901c4070301c00040c0840c507a8a500010030039070b020003003100c6c0440d40d5a0b036810364030002250b5a00c0d84504400303003808150700c20fa00c46003c07240a001d0100f6038a441c0c10005049030302c1940119100c0010500410290545010745102c40d0301c080341e102422855140400c684020741b00b81c150450701c0021184082041174068204026000303040152129180d8000780e00038002070041c0140e41c1c01c40c80c0040c0b5054414083c2103905a04030f0003402144d1684003068401c1000b4494010500c8410301a60000349219418a8000e100124000c2001840e1100c0507100704105005107107250001c100c180007040b03e400c507007881e2850a01e4102a050361503074400d18904041c11170940001e44012101c0b04080ca81d1b00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 170743453 1250 170742203 170742301
    0x11115070503061e0a03080c0f0106180b04090c0e0c0d1b0201051605041a0403060212060906060702030309060a031506020a0201020c270709050a03030302071b060c0605 74
    0x501d4501a01c4070807450b03407248015440d440e400348072220b0920024800c007014003076000d507080c1181c4a120030700d2708541c29a840c68000b405c1d440368004103c102d0009600440b00420000c1d0380c2002080c5036500c1d1654040302500544002038643c4000c9040301040394211150603035018410040300300304000840b25001c00868410066083c58003180400d1645102140422100d8456a02e058986141a130800000316044224100d042c00000041401400103001040700b000100750b1600d442c80420a5254001c0c0031540075017801d0101400503240001102c004020465001e62109048032086020303045044042200c0c0d080340c540040c021f0317000140c0703240ea140300340c0946514428540901910001000b003240100d215185040d41d00c061f00002e10ba00701e541498811600351302c0341c0c0412209a00d80c0e100700c3c00a5400a0a98180a141007811440c0a241140801410b1a0200c02080100a8100901515502c402254203918442900000804007a1507a103040b154611000101d15100d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 170744703 1250 170743453 170743459
    0xd060305010b09010602030a1107030206070302010207050d0e060702090603070f1203030507020c061b0f0d020d141806030a0e0109080c0c0306010f140a17060108070b0903070501111507050306 84
    0x411030541c62400c554200c0c10307501d0350344c021401c3c501c8e02ca400f224182e6500e5071514142c0540c00c00400942c45510003000030f64003940015a903130029113450342c5440c104401400411039080c03121304480d5906d4088482e102d4044450a051f42c8540380080d0a01845070300084000c5590f50300040c0041c41e034521219640c0c000c0d10100710030b0391540000c0e0b8a070b1000522081d401a0100001c092236904100008250410b24040f25000100040140d01d01194003030081c0259200c50170b062003050307100d9082c64070002c20001443c1420360314800c183c0741102d03082005100c0d04000c400583c1581450b884041a0205140280100c40d1141080051540500500f90303c90140d0039101d410307410000307002c9040300c000c000c0d00f114151501c00f07495a0007010341a810303401000707100c0008070001404280c04052242c500580034a514000c140e5142c2a1030b680f00c0415540c1c10301c10049c55581c00b0030f034401100e90a0030084100350400518600b0800440303410a01c640214041c052455844806180b007404e042d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 170745953 1250 170744703 170744711
    0x6020d050a0b150f0306130b10030605031216034a0f0901030b06150d0b010e0a060e0418080c060615040812090a08120703120c02031b070b0d06030501 66
    0x600c240c00a440349131120304800c0c20400105200f0304100f25011000c24030703281c001039010302c0b002c006140c00059100d00c20010791154030070300891500b4050061154815001c0d140f4020b90362160201d0505102d80c0502409010b446031130354513010044041c0608042111400380d0381c0c1c40b07107801080001500000040200d01a8900854100030b44540b08400009124144980c69a40d41d13001c2924000d2416030013510003a9002d099106040c0076003401700d1100404940e0311451400103204041500e20503100380300c86003007081699000190100f04140640b004104c2640081c8003903a8880c21a070000e104580c0007a125001403408180c0c1030103420202d070640790751007007a0302a403060f0159000b07031090307a008428411a41c541c804020140c84202038016a500c9598440107410482000130410f8001e000280000802d03500800c008408205000100030280503440c00960740c0c024542c00e40003010b008050304105410800004004080e032020950359910140c0c6d030b00000d80071900c0121110760070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 170747203 1250 170745953 170745979
    0x2010c0e01020a06050a020913090209060906010801090b0d0212060a0e070f06260708070215040f0318030c15030e0f0a03051e0708070302160503061306020d050a0b 72
    0x100d210040c0d0490300581c020041118251a074000802001c0c1c07200110303603801c0000307402940712540c40104030140c1c984006102d501030f005001107040c00910003072003212030034100a1140e8025002c0713419184d00c1407000440f0600d01002c81c2d82c00b00702c1c100195104401c000c0d506511a000100c0ea40701340c0303440c003051041e203d603e6290307542c4944601500803c00c82c464030a12145d440303071041c1d40d502041840344841207811400c801c3c1d44508250303005d40000d81c442040018481c1c0410451440310801d800b001907e1400d40c8420950607400d0000504010b1011003086107005008c6150300956089041c82c4540c0303a6401015240d90844e0000c100401c1c07c0200e81f11001102103040c0b0000d408000180244180580d0100c03003c6d409410b6500603c0c9400c05000401f001e00000341600381c0c07180c0c186560399841c5040c0a031810020083c1e02000c2c5a803075105114a403030101d03840350082d2012402000601103072a000c0c020b805078034007010075146440108460071000350000600d010f01500c207105a509 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 170748453 1250 170747203 170747207
    0x9020f0a0b0d0e1216030206070504080a032d02010507110304030b0610020f0708030a030e01154505010e0c03011206090f110910120f1112060702010c 66
    0x42540300756a0003200c28080b0046054860704405070701c641d00c2c0b00791802c03100a4044c80c411500602c48110410b5807090802d1704140e01041655004500350410b60b0800e803500621035950a000d40006081040319941c2d88101301583c51803031101001d01d031700090381810f03922009000340000c980103000207940141801500f1004030854094a0304074020340301d155a00024481c2c20402c540e04141184034011a03007038041400e1141001410003100603580e5040d09040040a45010b0f0a00070762507458a9014100400140c0c0010100c440103041c441c20700c004100c0c60300704103120300f01e540001d03404204004a42c401c042700900c0d00c9151120100480e07602d980141c12404001c403804900a002040188486020592101e0420340300b18004140b08006944403000f541c021207088801c3c3d04410a0343c5038038684040f2041d40095a1140e07003814610380303c0f4000f0050540407001d400700858150344410700141300300c2001144c401070000ca8100f810040e0042d96240c045442c60015480c026102500074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 170749703 1250 170748453 170748469
    0x60c030203030406150b07030e13020c0a02130e0a1a0a0501050312160c08010524030705091f0e07180b031f090606021f061212090801050a09020f 64
    0x260580d008600716625035549400a2060a80d030400c941c00c1004001401c0c0d100300002c20340948666581051412040140905540041b0704503100034018807140d01c11040008511001680444072044982c110103003910040082400054160082c0c200311801d1240c2075070460000076880404801950360380d14010308880081c00b445515401411485c02240c0d07042016040948041c182c151015101c2e98072402c40c0089170b4002f80031651114100b00d03880f00020807050b011091800b494001030750341000217131a59603c1c0501c81c82000181c0202d414401d00028280c2e4842c940684080f5040d2282181080201c08a07010400180c01c0642c0c01c104c1c402d6545100704a841c0600c185042d80c03a41c0a03041c1904000c101040080104a40006400c03181c1d4010789000b019150080c00c0c40000400d0101091080c609020f2405824504200318003064409034010080d000440d00000c0c8980072000c40328440c0303607804900c842d0b007480f05000340b40c60300740c1c400c1c0f028034403c4500307086d128221810f0103004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 170750953 1250 170749703 170749727
    0x280e0103020a0e1b030114090f090d0f031107030203094906061e17030315061e09100c051b0414010b0d0608030f0f1e030f07020706 58
    0x81030700a00100101c0c0d005103d12a000290002c038540c4e1034485001c4d48003580c000342c0c003020710f40f40c0c1d40f5003000880c20010f121580040c00016003110a10740580c3c2c05a03181c222120b000b00300704c4142c0d010302901d4070950100d402110070503a01036035000381d400d00a60325088420b0451146400c0c081d001c280441e00403140c600044400030050a8035500c2e221001600e55001c04004404218080d010001c0c1c468401d00307014040034003500c00e400c0c48a40300010708800d260001c032018450721a001600c501c00000340c03035100c40452604030b140881d81c1c0105005002e40900c0910302518014071902c4004494058054050242d0750141d0120350080d08407503246410b08080e1498020182c12502c1310390030a255800c13420050004a4007102520f005400758009921440c41218042542111000d030b90103080c0c02841d04600031400c013075082442c4041da10400050040c410360010f8140744480500044540c4558a107220940360b1603d00c8808141000440c0d080d4018021110007040b2903000d070000400c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 170752203 1250 170750953 170750959
    0x120601090e0a0510021602090901090b090a0f08090d120c050d050301151d03030a020a0606141f12061401020105010801020406050421050d090608010605031e1302280e010302 76
    0x5001c01540d130402544259942e400d600241c0c980e01c40940c8a5400c5e16015018941c0009190700342070900010b680005005e01205400c20500f12000c03c0d201c009990301d00750008c221699510202c80040c41c1d85d07200e00300c014040055a000c0d040050380140384242c12034090f20658000b8482080103d410303200c00d0050341101c11103500c8500400d4458031802c008200b40a00c484041c03240240028519085038103a900140d110082c28400c04c4851700640006000d011f0003000c80e43e079020001070880101c2500008148100005401240d118800080d070720301c00110104090b545030070300f40050600041c44940550308040c000940d100c01442100c003114030590341c036420070f41000c10310040850b0940700d000d00d40700f90351744040101d201405580c84100458071031000e07803490210040c00d1100140c0c003075000c2c840184204034400300651290002040d9021230412039944d01d240f0389005007101c140103900040e420003043e51113251101d0707038a0402c01c070804203020300b66203a03520f02041c0d209000080d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 170753453 1250 170752203 170752213
    0x16050406080703110301141806010c031202070c0b07021008160e030708060109051006020a020319022110201602210106140415061805120601090e0a05 66
    0x401588030340c55a40e04000d8615021850b4024000c1300c12443d0000c0c0c10400007980240b004042d40e1415400c1e02c0c0c0c0d00030b809816800d0314540500003804654810502500b030100c008113200580e0f040e0741c1194a042e510820314580c598440511174129041010100d005502c008116444140511403062042c400c2038a4203400c03800810701103c480100e102070580605c544940031502000504c1000d0107030208100c00511841c1010811503807184640c440029500320f68603500c00b680740802e960140e444100300c0701d03001d8119480800d08050708504443c0d031544ca410103000b45004080ba105035912103c5505004020940c1611a40714a8480d12140c14000c100291707414032404100c0304a065000400d1894045151300403540007803101c01085805075960081401640004003420880080544041000b400a269200030007540760040c04188890108803c50341044d204002003d0321000d02035041c81c00030b100340e45581e500700303004900e10705051800c1c0e968503643c0019108002500000201 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 170754703 1250 170753453 170753459
    0x40506010612140c03060307060f09060315170d260609150a0f080615090f0a060503120d0b090f0406021c0c05030402030c010905060f090f0405090f06160504 69
    0x203616110b010040308001912207070300b614820101c20219105098245119959242c060201410544a82c00c054140111010618503555000c4150015030300c03d400c00207906000d0083d00245240c1c0d41e88840c0c030601c200c030010080d0fa1000700d010003448000b500d074441d46409882c040300c0ca43c8222030850000320040302c0010301e58078010502c6904100c580e1441801d0030380c4040070031340a80541c1c0140c440c043c201d601c10481d03c0000c001d130960020361150345e1002e6500c40d800040c1003030406401c00444200b114089080c501c0280c2c407800c000c2400030110360120b140c036580883c4a800500e0084009480c1c00b5070050a41000801644100342c018024002ca80c1d560340c42800a42051002800001c0c07009101c80103100c3c14440c00e00030070320f00d4848640b06e203082e10426103440d4182090341e04200d0040020043c6403203803002e540a008128489a40701e207642c00100704142c00940409600c0b60905091042444000c2030b040700c058189819590720740c0e20f49500004080c0200403000004008000c20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 170755953 1250 170754703 170754707
    0x9060c16170c04050a02070204090b07140a0c12030b131505040603050a031209080a17100302030c040b0112020f03010f09090209060111030c1b03010c02120a03150f0f030312050405060106 82
    0x210385c40783d0740c0d10006090071025004242102d0390080c007280d490742003e06000b8150b40005d19100d43e000c007910080c3c5000245c0702c00804100503482d00a2400796031506180c034140c000e0b042540406c00140507100f404030449101400b501e0000748504402c44810400300701800c00303006a5050b40d8100004150726506036401f01c5083e0350314244040c13525070b0b5040420004981000410782039013599111a528500b030030f5410303416980541422151203c4250030401602e010901d0303298490700b00c500040400d03c45005842c06a01c044485030410702c00982c0694040f900006181614409046282c001e034640756440100d4650483c0654400c0e40c81000482030761080c807240c000a1602c1007603906141012101341c0c40e0100300c0280c408048a200c0b6610400c2c103007407003890640c40d01880102100c40d803090b25004644508c1d00700204064481d000c0048100c54500d644004011041c1c3c02c2c0c010300c3d610850b0b00329490660004130001090f000380f001400005004440c020342c0c01601a210030b074030304001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 170757203 1250 170755953 170755961
    0x2030a03050c0a12201f0c03020c0303010f0f05010918090602070209040506042619180801060f14031b03010b0a060305180304030b0c0f09060c16170c04 67
    0x40e800d035101e07284480c0c0028000c0c011035642c0032183d031186080410740e1744091603807407041e004d640941d5014290411245c0c5c0401c02840d0500080f0900003050801800201c01074882c40710002510b120000000403410b880f803c0398012200758040804402c0d4642004448003a5603208610100c400d8030b949460041c40c65021008561180e00c00602e001040d60110b00d8103501114291519080042044180a41425034204244120195801c1032000050185160040c0d103048618440014900300d145402a00e0300d001e94144202c88107911170352640258060301d49801255100d207400040080e0504181c51882c2d14504010082c1110b00c61452503200c00342c0103484c61952540d240d0044a02c240c07521018200a0304545d507006c51a0301c1d0040e04011902c11050780d01e47e196204000420201e0280300f41e040d002014442d07815602c60b07000700a4841401288015540a40c0014400380f400c0400689906003080c0030303001320780c03c55803034041e103c4940340301c00d042881c0e0f04000e117410703581d14103030744 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 170758453 1250 170757203 170757217
    0xf0102090a031518030c050f031e16080712030605030c06040509042607112709030d020301061d0d030f050d06091b0206090313030308040201020a20010e010302030402030a0305 77
    0x400503a031150104152001004d0800c185d010861904912090140504c44c1c0445424401c00031450001601000301a104122401010885011507203594144460201c00c01154120800c0e44d15642c0e2401c0215002a01c1c2200f03801181c5030000004680c00d0100300b00807a007000a000e18245031038041404912240244210b49070010141c03850754641ca80c48d820f89080c503101100300d458400520b060a000510080e07200e1041380b03441007140c942640e0030010242074140c644a800d16868140003640385006138403403020703414004400414080e610403410701c090940600050031040d40c0c8014880045e030800300181c001800e0080c00c0c0304d00b9025400900b9404002280010850390ba000c601044610a610f0001e00b46c031101401c0c10707020f42c100318440d00700c2c4440380a1441d04030000481c4041c1c4030584001028404800006800d680c02030007840780194010340303c0d0543c19055680440042c1081c080c150200d452510b000b41c171540300b032094034844c2d0f41c003600908810b0ba42d518240c03119081a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 170759703 1250 170758453 170758493
    0xa030b04030e040903030e0c010c150e030f0a020303040614040201020a0b06031603111525080d050f1006030204060912080f070305030402010806060c030a030903050412050f0f0102090a03 82
    0x4000b04500341c0341c910420700018040c2e640002c2c0750800103985400c001004250034108803d48404001041e240450030b0100d0905c1d500003d00e030000003490600310b009120425082000210f50940250b40100040d4821845160f0401892880d10641c8182560079600640141e01601c0c0220008144100545d00400024120703500541e0144200003a00200e0b002291950003903842c26025040000b200c04611500007032641c1000ad00c58070251100c11400d10101d83c00c2005040d0f10288100c1c0411520700b251038207002e1000345083c07a032403400040269121244198020380c0014040c0c464401d88054030059510f203015940703003031540f5100d200801003d07070b081d41081001071943e101c2c0c0c1000305030203846030701c41c21b40301d207002e0001400ca154020038840c001c4201b042540f80740c10020084800f80b00190900182e00426030034110b405005c2c2c3d03008081031001f1900104180a0002101d81040243e4000c0b0707000300318008a900e00343d000700c040098000c40305103c00d10018954000e020400c2d4140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 170760953 1250 170759703 170759717
    0x30702121608150a09032106090615091a180307090501030c080f0c0a030b15040f0608100606020703080a030905030a1e020706091412010203090102090307080c0a030b0403 75
    0x1512007161502155101e000d041c1c1c8550030307207a5080c0079044210391143c04201c0810400c0016100903080e1002e00c81840c14241007000080040241548400081c2c00039090400c52036494001840c1d241060040e81000304092042c009001c0d8460740c0e900c201c8803549950742d404c090086031701ca0356045070481d80c1c503030500486034003080000c01403003014025400f03071244021540c6481440c07070620502020048964000f940009401d44441c81e01c142100d44c800c10b007031401d03590f0f152254141d18a0704006030340b0500f4040d540c0e00b0aa15030b0001d4081c2c80b4104199100280113011030f10840b800c80c0700e840b0258101d2827080010402c0300010303280d60081c900703010984504550303d95085901078002040818418581c80312840d03400d010140210005000409020307080140140c003c0419104003440c1d142074200201d455240c5200c0c8119a043c140002c0d03490f410704400c4103010750801c7c103003280070780700740c040006078028002500f031480440508540c580c5421a00c1e00000c41c8001001038082c0214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 170762203 1250 170760953 170760973
    0x2060405040509160602150c28020c01030b09100302101e0314010b03092a031902040506060a1704110d050a03090902120a150503030706020408070b04030503070212 72
    0x346001c2d0501c07030740030070003c2c0010801c5944000c040030700c2d90304100c0455000b641d003001d0001f00c580480c0e4001680030040c607101c1e5070008076040c0303000c0da04a00f1000c803140c40c0603d076205500081c03100c0c1521000d072001d000d02d0718040144203001004a505401050407034400700003500300b40c0a10071800742d461400240400b000308508070201807902c003650000c1c1c1d03500c80030b29002d6031402085d4003400f00343d02000e140d0700b0600200e540d140ca1001415010030b00100c405841003c6040060525001c040c050740c226011203024011807a062800580c020750900000410901d8020b0844281c8021030701d412101c46020317000e1684d1a40c009000b1142c4d06541c0e00051386e1603442d41040d040ca1440792000b803000b801d143c580189141c01c80c0d071041c40342c580103010030300b01142c0c1503d545038011f480500004182e480b01c10f00040780c1040d07030b1091303425000000f00704042c81517580091042d100104100c414160303980c124042701d03100d544000b0384540c100740070441c01854070320240c0000d0300301c0300201c500c4029 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 170763453 1250 170762203 170762209
    0x2060718051306120f02150708071b120c05030d050429042303010e010506010c0305093f030a0507060e010f0203090f0f060708011203090803030c0405010329040902060405 75
    0xd1130029600d40705502209000c62404080300500e00700188405030502c245a81e41c80114000c0143c0144a082030540041c1d00300f60314100382006084010390341c5001d08080c10111481211030003480d0203405500300000001d40140101d41c1102d04807402a07100320440501500800803021282a00100801c000640c007612040048084802c00001c00035001204041500315200620a40050707410101040345c80c4e80c100c0034848003507800d4105565154504000140400400300c0f0b41e5806000302031308501d80103110014000c45d91a103445040015400d00310183d5079014800a0300700064040041d5800900c262304040d01c9200c058002042c000d803030034001c10070f03178004894681d291b82c0001c240c2405408100b03c0740c0407110500015104ca424031884c018031020050240c1c1e5200c451004c01d010805210720b0b050b0000b844041e080d070791241445941047da0f0750051246900007400d100c0c40503951032403038402030741e080018030000d28a00b044105102c05410b80c018183d074411400d000000d8203031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 170764703 1250 170763453 170763479
    0x21011010b150919080303011a09030a0b01051009150e041401180b180403050a12060807030b0915010303110f010f0204030507060f020309040b15120702060718051306 73
    0x1480da0b0108907190000c200a00c41100030098030b500b804032054004001da0003001c0100c0c0d0558082d180010100c0c000c0486030001ca2140780c24498040c4034010141003402107500403503040c0c0c4c0003101c0113024100c0d407130300843d40411140200403086542d84615480701d070041c120540c21980180021829030b2007826096002f5000f42c2c41030008004111005880380381c4c6104210b000107003229141081840058004003940c4010304c000d0510a0020314903141c28040c118180309203030461400d120369600d503a4019203911852200f1945000c5000100d86003080c049000030b42d46085124800c0c2c90303031860300c08541e40103c100f1006444d010781d00c0c0c02403030740c0028081c3c1030354200b601c0d201698992462030700c0d52515880d584850100145103003403002c00c41d408011960600011140801ca940c602e40c0040e0b01030040c05140143c80c84005071100c03070010400601882100d003502650407039642c0030401d444041440340003010b43c02c016803040c000c07803a14581640b40d0078034010001a80701c0c3c84092001c440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 170765953 1250 170764703 170764729
    0xc020105070306060c0c05060a030207140c150301080a0320070f052b0f020312040303030903081803070201030203090304150513050d020a0504020306010c050105100807050a03021011010b 82
    0x140d4581081000342038060048000808091400b00d282c3c1102d92a010204500390190a124480014040b04010320907019a5400c03a00103415069a038503020102c0d595882d5041f0107130046100c9400b003100b42e442401a40d0480e044400600503000386560121240510701443d0380581c0941030580f08450b070308211342e902811a621810b480141030004010782c1c442ea030005c8402080034a030421801030160400311500940c00464441c010445100190030f2000100103103188080104002090582c140c10244000c4c2c0607072201d00c1c642d250804515165003102d01e14102a034020003484c0300651081d0b0003143d1180c4048281d074205031301d81e081140089580322640380080e20125071072914894200b0160b00a2900300d0390140e00324030b16404504400203500c2800e110355400300000d06140d02882d0101202a40400200801e24000d00b500c400c1120342c0c003a6403020720984e0700c08603030b509208100c3c000b0b881d001050500d541490f5141251001004000190719541b036404440081d1900241c0d8198 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 170767203 1250 170765953 170765957
    0x61306060f02060a0905120313020301050406020a08090d02190f060e06071e080c07060b04110d0e0a050c0d020109270e03030412110a150203010305010509030703050a1808010c 77
    0xa840e000748000b80741401c00b0342888016840d22041c103001410000d181c4510740c0c2e0049180e5243c0d0348070307204404601c3e4a0341b80a5015401c1200f000100b00d07041c3d004081c3c078219a00c0301d640540303801710410740d1072040000080150f0300c140307076640350304a0301da1700300600c0e80c494003034080591b5490707a800c810ba980f41e0b1000d000d140d10160611500c0c0b0703044055812000c00c0001014080380d039403080106104000f415200a40000050b003005005203508008400c401c050320921101c86018495066580507060301c41415140c29035142a090001c60a6001c5940100c001d15410080d40104803012240300000c0f1b047c8140c1000c002082140c40d4012400d11042d040c1c0c0410305003c68403440c05440191110080c140c00c100204400a00b840c010021411414a040324102c48034004e035615103e8983c101506402c6c0241542c0903414240d001181680c0c4a88000c1c003540e180c1c0c440482c0d507401040c00080101e00c040c050b5443c0c042c0f041d0030848825900052807003a281d5030710308890071a1050020440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 170768453 1250 170767203 170767217
    0x609060d02130605120d230403081b010e0d0905040509030405120d020c0909030a031a060f07050705030327012610150906120f02131d06061206130606 66
    0x1210741742540c145008800048060304400303100f444004d2880d4100701d142550304030304e000d40d45903480300001610061503000b281550b65440c6403058603a00306401001d40015802d00e4003c102070900401c024000c0022a2a070040e114181000c0102405005083d068548014000000c47c0e540305511082c802011001030072a0302c44502009003444805e00c03040e400303200c1e003a0510095000000450345007070402d2900240105501c5842541e0009000c50f02ea4400d4001c0750905469005000030701250744601c04864106039a0703024982ca90045551154440000d211300c102042000b904483c0f01800515000584401100ca01c52581c0c40342e80410a510042d00200200226501c00e00000b5005280c980d10341d0349194a0014084420f07802070b1010817403055091461503a036500240800d03495034070155143c40724804c8001c2c20307030242c1c4290700c00c1d07511140f03081c80c403012411036443c06008003411036440c22401d0056494100340140c0724580040c0070f0b0881003c3e5006512485001d0300d45552140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 170769703 1250 170768453 170768459
    0x2041104060c140a020906010c020301060522200405150705061302130605060d1d0604030807121509091104050c04090c03110702040b060d09110a0602150609060d021306 74
    0x4a1600d8803940d4042d042c0c0c058403504000da6541e9120303947c071000c2441c00e1200001c052000c64054041903000d41e070090380462071000c81054800c641c4d52581040d43c1d080200302001c60000c1004054205903101450381004140800d0401d05001c81d80d80704d11901d8a45043c5550340c92030320b071900849501003d609526100740c00c41c07801d040811141d40c00da0b00180589810300380000da9a210781c071319161003036075a82c0300c0f8030a0317044c0780200c400c00740c1b148070545103503140c80d007400380a50300d044621308000b4001a07400c40c0441618444c2400f4400c0e540d243d00d510f5400c00301030f84014141c044003510200c025080c1c4001e0740c1e45038000e20b40b04e850980c0e00c4544540c07409044009681580b01310405041c20f00141004d040c0c40082507400403030b0101d90201d000c0032010702080440c07141c12039103030348903003480786140502000500441c1f002c0f00641c0c5a120041d03903610100c1c0c880e000c420000340158581400b00b01070380f921442513a04411300030b0081102c1c48035503001039104968520178500d6241c41c1c910030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 170770953 1250 170769703 170769713
    0x1030b07050c10020301050a1e0608150d05060a140403050301050d17070f050111070213181b08070b07030f121113090b0103020c0d05030901020d091a09011e020702041104060c 77
    0x8e031009103c030341240e494000c40042460780f1000780340034903020054028005a00c1d0000c01c6d03139040e140d01e000b03810000e07200f04600b08103454210840314400842e051201e406c001010405200340708582554649045908240400c0201183d803002503911a902c040c4005021040380000d08003140b01c6d04510882068078500103003514a491120348601e001032241c50096140c1c011800d00c2d00f40b1514000580e41c258005440b1a00e400f007101070140b04665000d01461204450305109880303080040f1603440b699646007103024440c1d100700400045c0c04c214a19561401200040c08204400da0042004445400c80038086d8110000320640c03200b410104118602c0da610035031850f18800e29041d403034405071228503955051258200400c2020000001e8603c0e1000e50554201c00c040910a00950341182000d0010310340404c8140b1a006841002c41c220040511511a4001103e015020703042440146000250880c5034103070b82260316094607480c091a910000e10261085403a000c0c88402c690130f01c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 170772203 1250 170770953 170770969
    0x21090406050a15020f07080c131103010303081b0306100c06110c010915020c03040308131e03021807080a0b031c050c0616020c040f0f09050102091206040b01030b07050c1002030105 79
    0x1000400d030704480d00071f0101d14004110f0000d024001c1d0341c003190852030014400e00800318903112050030030001c0008800c06a215030381501800c2c954144211070101000540803a100946004d64000c040900f004d2026000d586000d0485001c0c400001d0340070a4078071024111f0740095a040150b0759510340034400c0055079010b807600c400d230035442141050300c49008159213106600014140700404214945128000e10020000e49401300c4180400c0e142c00c62503100101c1030703000c102d125120708940040101901c44416100c0c014641d83c0f100251241010350740244090007a5a8050144600e04400b0b11344240800ad8401520f81c1c03107990341c41005000504040002c1c1040104c9842209018642c69001801080401003241c0005444911207410001002c060004011160803d80c200e000c0c40810b6000c0d1006a400380d48081c4010416107074281ca07210111001013031400103800501c0440d1410920550200701810690f10305100416414602100616102c3c0b26940002c0144030605044071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 170773453 1250 170772203 170772223
    0x7030821040503030103170d18060b0f130e030708190e03060f0412030b19030c06090b1204021801080703030f0507030e010e2701030c050321090406050a1502 69
    0x4480c00242826510942c89120611026294041c0a9400e502001040c003c85161680c00c0004218081c58400b011054202504094070060700d0702000c0789642c2020a085000501c00400d032444100d02420410020204000c01140510040c89280c000402d04002070016400b89801c82c0303400007540500034003148c01d581146000380c01c0035040c850301401c40781070a5045179001b00482c84100c0c1800c411001441c100341e03a654407050119500000009242c0c00d0019240100d82c03c08030140c0301d03041030781c0c40580b500c500c1071014010003090034194048000386801a10060110718408003225907000852000e8011151580082104004040d045110300712188503030b09109003022401c0c5c80191800450504160610203221080d040503a20380640501030210030780c400d16204202e9020300442242400110f501c2034410704081b900703150000724111804186424850f16000705c00c181006900200708194000380c88041c0424590b0700c0c00c1c401790240c140e00c03d038501030129000e002460082084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 170774703 1250 170773453 170773507
    0x110705100804030c0512030a29010905011202040b070503030108060703090b011401090b031501031a06030c0a0309050601030f020f0a032d050118050d0504050d0b0405010e070308 78
    0x2034004a000350000c41056115406040100b0408880c0c245a0b0070030300c0c103100c90641c01000100700710760200b450303008042814000c9140c0e100f10410b0b12000034549500c00400d401300b50081c00c00c000541c4506400c0d11800a182c00160070b041c1e0f58407080090ba00801d0341100d080c0c102100500c21700001f0007001e0384c0310030545028408000181c590740c0350001d0601401d40c15000308020030741700781d000d601260001c0c0310100c003450341c0e4600b0060302c82c0d0703c00724144001d000078102024044d10250989200c0b0030004024400d5103140c5500c03801e803442d0340c040ba49800074991554221008901c0c144900350081d401078034904020502c62041101c020180c10324244035640c00309040c80440c20f1140c00707044c51030800041850745080c01c03a40300f1030301505c000c1c010455805c0c86465803030742d0324403821100410722a40841e00c12040703d0500360760500a0740030f80340c1c00154480d10803000c82c0111001030b400c540034100014054051100c02406c0031810f402c01e40f012030380040c503d50700c03074100d48149460400310707 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 170775953 1250 170774703 170774719
    0x6030f030807080c1204030302190f0201230f09120c07061205040b010e060d0503041409010501090e0606091c0b0708060a05010e0402070503041d09100c1e050c030406110705 76
    0x8904d0440150103080c460580d00100400024201402a030444145100100c21884902c41b0064020140700c8854000c43c010350a04c40d041d088c0011a409411584000c1c40300c1e0241540d9661481400f000006c01c1569140f01d680344481d5110320b080700404c0c14107459009409940d060400c003501c1a00295119420f41b45800e003008081070303140303c000741074400c1000700c01150745520340007401e03102d00000d0240c000d010004000030849a10700800092680a5410039002da03690001551480d05501c29011032150035000034445180c0440108264080140b0340d08a203103288012120040c0740d18411174000388000140400b464104403900ea000404440748003440381030400080c65085030b46801ca0143d81c010039140108030051040c0e8020304440381c02e0852355024a0004d11515000343c0f4008002e010309041d400316410302d03004004c900f41003600c03250001180000180140f4070b01c1d40400341082020300c0141c060400503c02000200101c0c0d840e08260125800364605000d410703440180f140c18a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 170777203 1250 170775953 170775961
    0x41e05070f1a120403090b04080a02120303060306041202030706050106020f010501080f1513020402030c071106070c0302090403031509150509090a0312060f060807030c030506060301120302070906030f03080708 92
    0x100803c466643c2d40660f118041601e40345001d4401503180e030490320500307a0102e004a901000003411400b210300813601c0416444440415640300d100594140350135400a04c00140420b44070446c0da1311020b054811640740a005480d04802ca50080c4c102e100180c01c14035103201d04030002d004040c00b6103040000b0f014490707074556441d81d40c0c428540c8181005a48030002840030803c20210003c10364000e03205665901e42241e182506501281c0101d4203019401c000b0b5849061490580e00708a0f0300c805138000380ca09580030000741500040049017090b40f14640c5e00d82041b111060f000080070b00c0079002c220600356043d00090859550400e601818603035080041f40703100024001c52450b090300384469040220401013016080a4100c0d241d03848000c01d000888507400440b943c800d81e131030741d000c000e140a40c2e5011401d5900c00d4801652025085c00140404c003190f51580c2e542c24428011203206aa131144400180c8450740d0041d00c000c04105480c40615030400040713940030301240780650440c60 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 170778453 1250 170777203 170777249
    0x151b0f04120b01470c010e01140f0903040306050405010b0a08160605130e1306050106020c0405090604170d06090513170307051e0d09150e0d0215041e05070f 69
    0xe0684c00418040b01d01c40c803001c1440c40d014201c0e88140e0040000b841640041e04995000c0c001241d00a500854600000707402040010600740c000c2443e400a9840d00380f440c4c46082c082e00e400f91069800e9580c43c1d607454144d64500c04801c0c01000c6c000f026100e0510b82c0006c0e0403400005034814000c0c82010803003071040256680750b00c2e09880060540b0b207400d489480c0300305002400210028000c51030310001203400b980010b005401e80e4402c840c04d2086548543c2040d0b01c03000d0546000b403140030000141d000010a110282c0500c0520740703400a40c4c00d91716644501921415580c040034503d0100301d45051058590001e043d80403035014803850b5040c0010000c0c00c81c4205103400c1c41c4030038807200c003102c456465000c6401080d0314040c140414602d0b4200f03080e603412107e42c81410289401040741180340003007101004c0300e006801505224020040c1c04147c08402041102c0311040440344400f00c2c5002d0329a09005070040c4002c1000a0034600e0005004900e074001601009054030307000c503602 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 170779703 1250 170778453 170778539
    0x30c0501051c090c03020303072001030207050c01030f1b090816120b09010227010315180b03030408030a050a020606010c211713020102151b0f04120b01 67
    0x2020707040009650b0039207040c03130b1810101c56000250f150000107114414054070031800703003034030b20030719040d01e0341003001c10042d0200c2c0300300c01006019410680004003507602030f40c4180d9802e008440c1c08580c0016480310030100d0415683c030f03000410811381c428030901e0b00c1040f44146282943d0940c0740018284001072083c25010680100200c0ea540c0c0040d034040d1017901500c03030080854800d00c04c400000d40e00c110300f01c0c0c107080b440c0e80028a841016800f014601441c1d000b15849254420302c00517010650001600c1404801501803108002c0040c110400308014840d2682d103968403500c80042480003401e00350060400c9041005218402012a41480e400716025180c800804950f419010058441c1c120001261070440c0d590f070304010100c82f0040d80c01d040e85100342e027925a64005080b9084920030700f0744502e01500308840d09160081c08500c0240b40340700751f0340400c505142d62000b240d4a0180b002c00f0450301c8140c6200108101038403603210401d40301540983d1440c1e00c0151100003070750 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 170780953 1250 170779703 170779747
    0x60b060f0906030c0f1204050c03010c0f0302090f0a0b0a110a120c050a050607110106090501080709110706180b09011b050901031404080703080106090f140117040c030c050105 77
    0x8080000c00b0410b010366010881d13021102d00140075071070351b50f1110b541007640400ca400343c4190181e040700d03501500c0d041c490084240401d032241d600010700130a0480094116150958004503220000d5449580d2400111b00420200000558510000900800300038014600340c1a03079000300094400240c901c0c080b0040d00310039107001c030038000441c244249402981900a4594050700050210266000060f8821100100000c2c03191075900c00c0c4140c2103030b80901c0b13420780d50341151005002e4440a40c100002034030000c280581450216114401200c00c800d20f0440752130b0f18540b80e001000691000344d40d0000c6000300801041c440440303000c00307501d2240c4040c010054000f0324103056030b01941c401108800207159041c00d5140514058050307902400058001c100d00ca0000501d03036103e40c0c01041074613144903000610b00d14203004058100180c0000c0c0d4103001c600d8034104402d08980320224800da00641011880f18030350304003a000130f01140c202c10f040107000c001d0041c4000d5015081505 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 170782203 1250 170780953 170780959
    0x3070b040201051305040207051e0c0f060901180603020304020109050f06090409080408010c03090209130203100504150c03021908010b181804031805060a08010b0a0e0310020403060b060f09 83
    0x340e1306001d5120b040d1200203422482e4802d2002c60b0314000d100c800941511346801e01124000012002c0345601e40da0020782d00540c2d40104400c10b0701c07644d03060a001404507502c041c1007200000015040e0701c5030710f04041d04000300081e40801004150760340030303891400610b01a0782d08111461030360b01040c0c680c4905481c00780200e40303030010070007007001c100300710303401030400300002c10518000110040213411400c10503072203148141c1c042194240361a18100413950300a0040c0403502083c5051800b03084002c2007034900e640d800c0e02c0000d00b6102401588011940e581c3c0c0103956107010020f090141981d030030340c201000074100060049403040c1084800400b12040c42149607611840003855038000400c030070303215942e008107110400d03400c00d030081d00fa2400645880c4000380c0302d03021310409018075903040000a02440041154507407080060089440314501600341c0e484210210f403030103d40e9440351800550029013041400000d12401c02500e03411500749240030301800200316240912070017188 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 170783453 1250 170782203 170782207
    0x1b020301020c0f0d141207091e050109090507050909070905030a030e0405101a090310060b03060a0e0402010f0804030c020d080307031401051011030d09150c0c050a03141b0c01030c0203070b04020105 87
    0x11f106000d001520000c3c03600c829200385071410444a01c00c0515644602404140410008038404080b8020f40d07201d05a6503a07a18101041d440801c103100e03402034070710400d02003159808202c42c0c80c01d020030b0724514000d80b82c25070f03074140002c2403000700c4200405104000002020034072540c1205d0000d0000d940c40301801700d880d450f60800280c1481c1c1c11034819038556203403140002c0c843e060303400614461402140d141a0301550b03807105040e400b0048030001d00055254031405400c1340201c0d03c0310b41150192403c0d44050400b6030100300040207025094a0146005c01000881a4180140f449009007160300c903969526103c08a55101d6101340004c0070b0020107421015100820016604420b40c003990a220034586030400101000d40084440d0710503081c803100008040c010150498140c1d03020008110780304c1c0e0780d00c003180d1104074440c1e113040c940010000c80402400343c1c2c3e9240300d40001c480241181655200014003201c2daa50b2043c8203540044c40040e000c9401d240b000341d4407580a0074455 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 170784703 1250 170783453 170783461
    0xc0c080a170906070207050312040b1804140a0b011d2116050f180406090606170303012c0a0e030f0d0b01030c031a011b020301020c0f0d1412 62
    0xd508807041480320a03080c40040e003002542240060054000d9a103a000e844415848500381521001c01e005003550b01c110030001003009524410080220a90064003014510000000203003039580540c0b03400c05642002040c4081c4480502c581c01d15540d003401c2c181c40c01d0340050560101400f6440c07000d40b04aa51240040f00c14807400740010540484400391840c813581c040b000305071300c0214000c0074054907450b2041034407806c11031090502040c407004819140c2c0e1300c80d5502c101910900f4003c81d601c0b03446540004411a6100087c107902d0f4001002d140c07250304200c2c0110100f0041600d0401b60000a00103041ca4680030300315940003000c000c00420400c681e10350544c42d520803c6a0600d0701c00d0300080e0346a5008581d0700c0460038203403d90317090200140080084081c0d85d80400aa00300c1049412100080d42c040c518150100030800b200da2004038007500001d00320303080302e10190701c5900810143d4802207800d020910f030441c05070410036803c01500011244034003949041079180c02c0414081 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 170785953 1250 170784703 170784707
    0x4030807020f120c011d100f02060a0216080d0b06030109021c0b010c021c1502040303020f060402010f0c1106030109020403021008040308040303240801021b0102040509040803060a0806010e0601120c0c080a 90
    0x6c640c1140d000b600080c41140307244802010b454044486400601401010609604a60085400303149800340c04003000134080e20b59000c20b5210364124007000c3e17a00d13511700c2c410b9102d100c044c600810109200503214070450094104001d82c0d0341441d0307825490300c01600c002c0d80c0c0104150604540503543e07207200c2d84094190500e0064001005858060715100d0060f102c04035400900c182c0703100341e094482c4600700040c2d45991305001e0714001d01103a65140900d032000e00c071f014030900844c0a40780f40d62405c0c0481d0086030041e0310a0700320740c25a680004052055040681060144107601e141030400d91a094600402900010300024109502c82c101000e100c105886050006080354210b444201d6840000600035880800103031800c40c1900e04030624614103200b61402c69401500061065031241d9a0303442681c001441154040020100450342c9a001c0104502903c40c5140c16403e03030a0200000d001d0340409412440424205541c00c6040b03541702d00b10388560340e4440c0d8210384400c0c00b4031007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 170787203 1250 170785953 170785997
    0x209150919090c0f1e08280f050108060708010909080405131401080a050a1103010e0a0b07020111180f0f131d0d080714040b04030807020f120c01 64
    0x5810704800048801181e81042039014840000d81a1100c220314003101c9000d80744000c01c12a040c564850b240100b0a1260058011030f5203c40707204807120895403040005104400700103811881150746501c01c00b003212407072013803c0c09000b11000401c120b10700030070000d055000501600170180d03112800e00c0100800501998040d00c4024030a40b801d03e01140820003c0c150328070300b000510f80010000600711004203444400c5038010000e440155115115032105c11521140c81d41c06658880d030082c3c130301c1d400b40308503410b1610510035501941170201c402825070b0b4201d0020115802d0812140b0042c1c2c032141e000400700ca1060301d000c4901d1103035500240310100310002c1180c1145407014244c0311a8415800203c513100c46109c82040d04810712b8100e560392155000000c00304615401080d0300c140110030180304240d101c882e05203041d403280800310b03a43d00309900844907201e01040350021458105c281030009282641c00c102176541514000e80e0f5200002d14042c1401900c08ca20039000c86580a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 170788453 1250 170787203 170787229
    0x10b0d060906031a010905060f0603100e040506041406010518130204020429070302031608040302040f05010501030c02390402030c04030510020901080402270f060307050402091509 79
    0x1402c10000b5682c1c01c00301c841c1031240318003000640030700c40040303603c0c09144501070068401034400c4200c802100c060200f03a91001c0c0c944540159007141c00519007004a0f501882644a6400341505042900c0d0010540d03007180d8102070f09800200052009031a0316042024880746841c10502c991501c20402c55640340103d0302a4000f0300001c0d000c00c0340e24042ea0708a1070900e4121a8910703185030090f00b5032272405260741c02001600104070388540006000b0007050710600943c0e95034541a9285d0004040340c003444604c08850351298010032640d038041c46000d0408420b40068441f482415000d5001603184071043c13050f040c4500f501a41b080030103041840a4180030b0070444d40c0341000302d880d944c25001031004684911501c480d440c6c0e540d405000f1b86d0302d400010303150011035850f00c0e400c0241da41500c520006010100d07c95803900642c0d2440c1d1a80034013544058108282401800c0c503041c8103098000d0b074000d90041120041540b9901d91020400d010b180001e0b4480b0f0b49800090028400c0313403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 170789703 1250 170788453 170788469
    0x30507050c1b01020c01050723030d050a1a01080403020a0b0c0f0f03040b0c0c030a14190905100c1e140607120b090105100e0102010f090308011715010b0d06 69
    0x12100c00742e980c071024410507004a09070200d842c0d104074440112200e204071080103140701142d0445146011000f0712a000f001640303000d580c100590806902d00300c0300210b42414009803503a03050480240640c0030088085028a07181282d80303419100079581d514035001c010b00302420000001c0c14501c25030107403408110100183ea544070400c0081400c03d802c2600c00765845aa0342c0080342d044081d040403540701704c2940e0041c506007101d01c50103807400c00703540c410210b95801c00c1005c00040026508828154841d544402a0882c28441400300b40719100c03201c0c00074001c910001c4400310780c0c0342c0404410706021280101d003907085807070400300000844a040005200711410700040701e4016800401001004008001814200042010b01c5000b881440e0b00102041220404203228400d10950740406000102c0d010013484903030001c513250f40070190700068000c4014820f181202c201e00140401e10b1004010102d5503881440300040117116007110a0705c0014014040d0011ba0080b200400c0d01ca = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 170790953 1250 170789703 170789713
    0x90702070b1315230c10020d0e0106050f03101512151112010b0304060b090106260106090611070b040906052806110102250c090516030507050c 63
    0x2a0074601e07515a00d401028030708210043d4042e0f10510454140040f111441c2e012051014650040706490b0710086102103103000315841c2c40809501400202400d2001440005d180c0c070b80c1504040c2180c0d1203400c2280b250702481e0000d0401d42d40000c0b00e16104172041d100061000c6904070a404200c20f69100c050038009152032081071009000c0f0001c0c041f00f00d02024403003c4009191090300d071240d40380a148144204005201c0300011b80043c0d82c1c443c2c80741c400002c1715510200001c0c50381009a20030720001c0c00b103500514101300510705540e00e00707544d084200c03a59414000041e00031081ca00031501000780c40803a8211003802004010010111480c109a1b61900d0704005130141c000c900800d80180340c4004c50034414640300f54400c050b1803145030300c0c00e140340c102002210016a03588104104c2e40d0244103a41c070801c2c0c00340701500d03045680424040e05d88003e00c0d00c00550406944524600c502e02410004401840000d03117201d800c103071a00095590325140700303890500400034291054424 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 170792203 1250 170790953 170790967
    0x4150201050f0705091f02192a0b0702040504030507080403050610050102030c060a0f060e13021809060613020c01180204050a06080c0f0f1314010509010e0402090702070b 75
    0x66214074003070300041d640074415a40d4035034161391a100e0310710183d800111502d00d0704100e0164215060980109105403a58040e181035100b4048540c081c003594081041ca5044084111041005540b8400944459042d03880d0a6020149000740100640541e85404c0010200361241d81210007a9500044054a840d01da052459482101f19600d111100b401c1030040303043d40c0000142c03245100c00f00020250341e512100c0003030190001e03104509200307460749004907074140382c0c40020b0700c00d400303440ca0104009294010810b4078034600b4083c0c040803140d00144004004041001c9a019200f59070314024442d210080c1c0000744920a0810025481d001180c00728200c803041140c03410740200d40601c290303264000c030881102e60700d1281c0b141e075a005411010340ea00b84980c0c1000040402002c1400d07145103100407400303000790402c030b01a0039691015002130314410404c0d01400740009407080d540544c103004504041d10005800a40300b40b40e0940003980e0148200455009850740d00c9185480713041c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 170793453 1250 170792203 170792207
    0x904110d020903010506090f0a0b030c0402070b16090807120c1d0a0c09150806060403120f18050d1401110423100219080c1615030b01120f020415 64
    0x10342c410350b12a5003010003141c960320f0501d0215028101d158807a6001e9110040008010b02024030803070341501030722020140540d2288043d02e5054059006041d651505002207032000f0310001c3e0764014001c5141d014004240c0018030002994810340c5500340480440c02c046114403203e91040711005130000761078442e1080401154000d0404210078851100030b400c083d40e0919031801031500980c00b540c2036544243c8202031240d044580503003003d01c0c0c0b94880d12030440181d5034036801c10114081d200b00c01c600365801080a21503020301d940c50f44006080a0004071010a243c0029200c554008181c603001542944004070300d40b1803408555903107580da00315002c2103800800444601e54a14000b00c81c40c00c0c1034240c4822400a40d001c0c2401500040c400c1c440e410a422040d030f80c0810034800700444034010404422038141c00388184d041d25213000082811000c10301144010182000caa20305942d820140e03103000c2110302c203000705240c03001c0f81008000f409154800b6009805172050690350b56 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 170794703 1250 170793453 170793457
    0x17030904061517061e150c06010302011103070816030302090a03030f030614030304061b051f0509030a0207060f020a230114040f20090a1a0f010c02060904110d02 71
    0x41443d0b110a003103050a540700c070320000e80403100c007a045078840210940491030030390300081003000202200401255948801030756001038070340c941c3c1030740002c00500035907070455008805241e0301030045260072459564000180102003031014210f1911111508260094043c8e400c100c5000d00700301402030752420002c204062901d840d1011074a020404920f00405540d0004900302c0070b0004e40c0b8107403411504884c4103445078414503040014041d0000098400d00918600440f0142a8007040d44e01580010449001800c04400c43d032042285a901d6500891023008807282400c1114030009100b80c140d080c4407810400070b00c4000c4000007101d000140907007128450801c1c01c001c00401100100b0368907404030035540a007000c80d03440c2c40c645c0060502c1d14a02d8500320704050031381b1007a800d140810500001a01c204411540f9011890350690329103000580240c0102c0d0841d03201680310700060000700f41c04202901604e0006182c0015890702d400c09500300075248641e543c0e1301413003e0004025 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 170795953 1250 170794703 170794739
    0x190803130e07090b030c0304060902030d020c1e01080f0402031c050c070b040305120f0f030c0306190f1e0503120c0105070201090b0a02070c051302070303140405071703090406 77
    0x74661a01c00301e5000d0340704403411004e84113548512491a01c07400100545500001c00031140b03961183c03003a40040e1020f010b000c48604054006210070f0540c6c0041060003800d884002c2c0e4084501000490282c0e4400c9006420244131035000302141c840380082070604050300c10800300c5c04560b80500d1b08266000300104894500d80f8192264140c44040c03502c050310491201815941c0482c4032401501066070040c5415010204102d01c0c29054040c55449900100d482c40055800402089801d04214806007400c0320020400000a8141004540c0001e43c60050140c2520b0301c5c012005903101030600100640001003ca44d03a000b20074003a001960700c80810b41c1907a508100c08102c503107005010f00700d502503100740d0850242d070761000030384c00a400902096510405c850000195a00c0300310f04000c446916103400341e0380c0c401e82d0402600751441a64072606010b070712010440031980100b25101920b02840b1074840203016210801d285019000c0080d9200780361600c0042c01c5112926400d1134 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 170797203 1250 170795953 170795969
    0x3020c121b06040311060d140c0a12090c090207080c010e061e070e010c021f11160b03070809120a050d0507020a050d050f0409020c010603050c09090c19080313 70
    0x1112010301c184019400703203100041c4070003c0e80100c11241c2c0b80c0b8101410440d130034000009051070341c00080350400c10081c0c64004104500182c03820312990700007130145003d0030000080c02044c20a80d83e01029112910441d40034a034041100070401100c501150b04114458001740802c1d01494100c9440f501c050f20740511025241014150508000c0f0342c0c50721500060311104000c080b42801074074008884103040f039100d41c2070420340c0134000c85c10200003005111540c0740030141c110f50300360340e05c1e002c015810f001e8222401241003104100d51012207906c4686403170b045c44c003500c07600d02c1c09203000a1082e09103840e91000c111601c2403540040500100f0902c00414003880d12101e9007a82c0780d126a40029142c3d4001c0714a00001c075000f18010b014410150944602d0b090703071783c05e0702400c9070000008410305944801040042c4401000b55114860040300e075004c0c103003072603444140c3d5409a020785602652418804c00c5444c40380e103940200901801086d65a0707a082e491442d0b518a030640200c4034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 170798453 1250 170797203 170797243
    0x1806030109050a0e0d0c0219081005180a050604140304030b0f0a2a0804050c030709230609010e0705040509180d02030f0d0513080403030f030605010c0f02040903020c12 74
    0x80d121100080c090300c44080f81e12410151b00e040d03024064085040002c0e001d41202c82038002a0b1500c007041032840c1540741203000150740c20140808614028100c210104642c13101c2802c10200b0800b150040e0400d03403207800a80d0562000300703a541075000310b0f030015010300e05c100c0401c0703414406007216601ca1160a1030400420520b030709101041c1c4000c0d5402041c1c12207986032411030501548a00742c1050080c000c64004002c2e01000030b00d000030b55004000200d0302c4044810b03112035000e40c94500400e400401d0f400d89d1a1500100c0d0314280c0510a00c0195501070011500c0780c0c2c01441260003601e005403501c611450507980c24280302c1e215608901c0b03603100c0c4a4140b82d81600c040142c40544065505282c50300d2005d1016001600c8003a00640c019004006254002640305000f0402175200e9240d1900440c0311038000341c1216004d0348040c2c180700070340020310001111032944120711503045134000f68070411801e00700c0c5014a02182560880681000d0038100000000c012400d0300283e00030380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 170799703 1250 170798453 170798471
    0x70f09050306010e130c0905070c0203010614010e0607060609060608091902011b050f030a0305090f0d021002030a14270f030301090e03070605100905010b07171806030109050a 77
    0x50742d01c08003440b9150030307072200201040080320822500d010311800742140d46091138544031000100d400a98811000c40c1b2410034090850074280242001081d0100004643c01c14000002e440f0128800c0880e109102c00228403080042c10f42c4614041c00745080c08108607a140c0101400c1c104050710004400c0c822140045500244040099030321a41031350f406500490030148600080c42d0007804486600030002607600c2c030030080000c4d1940400d1030368041854204145914246440e00c803003804140c1107078100601198000900282110916800503501ea840003060802817500e440f108818550040034402c06900f0080412198040404d2070760b0071403040f0b040d0542da0340c00c1100601c0f440c0c205200400c008200b40d0720081c220f034040c0003a01c2c075010a9540e181d044650884010100e10320041d41402481c8041c4105400741114855451400700760391101210418000c3d50407640c2079001404034404070949007451400103001d80b100c0e480f541c6038080d0001070203045507032540d80c518206000e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 170800953 1250 170799703 170799709
    0x60f0705100501210c05040e010b1f0e100f0c0303110705070501020f03040e010506070f050a0803040c0e01031a07110109031e0e060313050a020d0b04030e0a0803040603020c0a0b070f0905 82
    0x10104c0346600c01c0501d05054605010b02c000352200c941120440d56968010b94919190800b4000903030500c08840b440211034000040e0038000c00c03050351400340380d201828441c2c054105014030000c420b11304001d000b901c09843e00724013a21040038903601d52400031801c1c02c00c0010009440c0c0c1a00d2098080d11003001003510090354a001c0c51003480315540520004101d9410042c009251250003405060361040d050f0301d6076444d18846040841d07100350000304000c04e2109034502d1401038440c4045000b41549076454fc0e10314a003851040385000b40303126000c03074015070040740080c0c58150544000d004001180c01c01810000102d01500d00152141298030071585c82000c2c81040c100e402000d460454480070304641029440700d0040703816105000d540c2015940d100700e109070443c4145400d02c068502031030001c4caa401c43c0c0080c03e00500303901d0800c0c400d140c404010384060798003c1c5401a02d58190148441c50081c212101070b0480322001c09000c8041d41c000e0207003600c10711680343c2040300c80d503071018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 170802203 1250 170800953 170801009
    0x5010501090e19171201030b0a0207150e010e1207051207080403030f0909141e0408160c030204060602010b150906180f10091412060105060f0705100501 67
    0x141c0c0b411500104091a0420425078280d58000d01511003401c100e030b07103000804125070024100c2d201e010414801001000300200702c1c039074402112281942848900e5a0700c49928840105241c02144c8402c0009001e4109500401401d525582110000e036401c4550a5040d8081030040c1d540b40182c5a15103032201781d0100300d5880341d504c003540f42d20303103031840d10221800b0702124404820003901407030000304803060f40151305004258401885040c18030420028103000403041e24240e203403240d0200008645c2c1c240030394450040c0c7d50711114910400b0b20b084000d01d185a040258491310f056408074034590305602400d61107130706803520011481950004a1640078440840703034481c40400c8091412884a00013054100c4060f103071f412950844000aa640c010410811780000d88414003040b02c101c52555100c40510305903043e803442d000c080709858407100140505030080000160b007020440965040f40c071180d401000341d49841040c4d80d44203000c1c10b020305c1643ca0030194600e450f008588000c2c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 170803453 1250 170802203 170802221
    0x325030219210e030c0a030e011205130210020703060207080909010b1608130b0a030b01020601060309020a0b22080a111509461403070b1312030c0501050109 69
    0x582c0341071202d0890100080c0040c194180c101d80030074021180c135000c040000400d07052003921945200910070000500900700202803950650410040c0005161148500c40001d501034580c825401c030003000c00d918040c3d10f94030041110b440015480c0a00c94540d000d4003049100700e50f90381a5980e03c50342034225000710500030005148000380180021001e07001030420f05a1046820f1417180d8540c03110032076401c40c41c59000031035102c5031010079541c0c0c10300504d80582102e0030100500701131600880c1d8003185a0281c00080e40d00001c0e00060520000c41e5513038288014802d0700316a0361516842c544528904c003044071048110030001a442c60b02d10000c40b00c03203441144a80c00c2c41c070030a003004a4003a92103011140c6400c0d0200901d60701c00042c0d07403003a003e1100d040c10300407410300e20180d010184099000e8262181e0803840e09003590360100b00c90307048a03d0450103684902d0100c03007145a01150ba8000d0711f1000307000c1082e0040542224110350002d0040300200180da030f13904801130135240048 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 170804703 1250 170803453 170803487
    0x1b030c040507080c030604061d04050607050c0d050903030409020f0705060603030337061d1b09060703090b0d0e01050f09060115020304030b09031b010b01080703020325030219 77
    0x8001800d45141d110140d54810b200810201d641503272041d9821044098500020036582200204418070900308512500706a081c42e1607450701c03494074919034171000003000880400c200010340c0382d05035808105542c080d040c208021503032084041103440c45030380141c808848900640c0001a03072407401209503480f500314003a40350008514250040607545542d0311200509404240d5082c1c021017078400c000107044144940706401c030907944d13003d0f5024801001061a02030701d03409506041034000656a100c401031f01d0094840d9540d19098031080d1040e0403481d9403035400b1400c4070480340250060360f03c3c00d40c034000030041030311000c403600010041190000f43c41d50002d801084503840e200e000c170380d80344100c0c41541d0500d510307680c600902c02c03000d0700c9801e601d500100702c01c9a6061360f022900c045c055074500801800e03d07040d002030a0000020148030600d0b6000c0700042900c40c241c0130440c96400145001c02d084190140007500031340101084003040002d90500c42415030203000b107048600f03070701 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 170805953 1250 170804703 170804717
    0x30a1b090b1b0a050d0e18040f1e06020d1407050c070314030c0f071707150f0e0301020703020a0c120807020418020a06020703121b06110c1b030c040507 67
    0x2115150b0100c0c4030029a0011442052044004202d00f80b0540200b101966100742c086140f41c01041074241c40c0c1c4801e05003d6aa90f824017001542007091903003490743c032040c00d041c0c031908003000f0204000b0050010f0526800065a20002403881d031014029841901e240d0050762150041103035075000c1d100121031a50700c8a1010700200e11440410407240c0002401c80c1d2925450148407810012554010a8150b001c5001405140305048202c601b4840900041150601d800c00b5141180d500c10152820f1105050024100390300c80c4000104498028000b507580e00302c60312300259035280c0c0d0002a2424030a4150118006e421450701e41c02c2c040e0410b1402d030034554290200401480c000d00208c01060340303507179600011385400d561040144a2034019000035481c500b0004071420710115814100511018402d031180ca10f2012552250340000c80007516a0070031712a0f006034071541d402c1c9550b03031085c1704010440510b0381503044840710042d010783e006480031a062009440c0c0170f44007140400d04c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 170807203 1250 170805953 170805967
    0x15010207170f010c0e010c140705040e1606050903060403080717180708010b03120f040302040603080705241f0e010801021c020f0a1d040f020a0813081e0f030a1b090b 73
    0x44102560030004001c00349c0d0202c3d07945100003001c40e110201002e1558001541070202d11155154200040085050051400044100007615400f000300020140711031800882c900c207102f8281c40c104032182803061030311424038500594100c42c503c041d400c0d840c4240940400c1c00d540c107018070f0207041000ba0003010301341c03a850f08001c2241c02514140000b4038040c000040540d03541e014050081d401012425501c04940c00d04c80e0401200c1064004c48114000301c00014407420350703526900003040801101e4a00800901c8003107030059500481110040c4400420821419802048801c2c03004c007446510030421a11401a80114001421030440034401e40c0c40250140c0e0b0704003170204123414070180c116103000c001021104101402184158080b03a030840b1103400200481e080300082064082003c60b03565000014031411000190b004d982600c8610059000000c0c1d0704045550a001d9480c2e141c483d0f07000c001040702120800c01110303a80391001c51a4054034446003500c0c040700d03641c0c0c9000301c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 170808453 1250 170807203 170807213
    0x61d0d050a0c020604030308011d250203070b07030507020f070b0d0506030f01050403120b1e04020d1d0c0312040b03040f140102120406111215010207170f010c0e010c 73
    0x10001d612014011000701c00b000680e114001000558840c0c0c44541481d41018207103103045945d0020507006850090510030490f10982c00c00b20107120040b00300c1d19410004000f241103004290005081150360740a20101ca90582c00c003920940c103560071162004036000e2a103549070220702c100542034a0410520070391035055045507901400103021260f0700b90720a081a400c407501110280c0c00220080100b0f5110a6240999106070070b0881d00401000e0450907820000c0701303403802c0f05109681c00600180d0f000c0b000e42001f10404100443c110450401540c19500c8240116016210f80591048000b00d03003130107070a5030151100d078840103003103540700e6441c16000c03607280304156090a0f000600d0041140240000d08441034004282c040606141c0f40007001c1e01e0385805a024030800c10b03c186c1001d80c04a8510716072100032038040d03525003200c120040c1c0c140032403900482e507501000001e15031030580c0042c5841c000740942c4000c102d02600d04504a8138000300c0486580050783c51030320301e00811 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 170809703 1250 170808453 170808457
    0x1e07050702010e1e060708030907050d03051c0f020f04080d0201230403020a0605010b0a1101020307050a030207060e030a18060c08030406050a0f0c09060801050405010506031807030602070807061d0d05 88
    0x798081d21940014180130300069450740080c40d0485800343c00104000503c1d41c2401034000030f01d0240d980c1c42050303565035405845802604860f550410042610790900719261700400056804058115601c1000a000d003069502074080d002d5a44561800d50105a00c140f00e62143c542c644500c65a2201c03925440d40381c0c05402410903411446030000b09000304142d03101c0e49000300701c0d4034842030340c40c140d000010b004070081c1c0c5071050850744188100b1110940000c11a02026080d140040e601c03480303854a9801096200e4040d6402d2001081044103103801c0740456482c4c1c3c1c00f40c01440b481c41e070744403011144c001c0f0840c402042c804061020900084080c1c02660f04201824808600300720240c1060f01113403c0c00003814002074148604001c03a980204480d400b420040c0c0c4c080c4103e41c10180414040d2001414000c05c5a040700d0000092074001d004e000050b65100b42c0c159a69092070602c5040354000140a03101c0c2441c1400720400d601c4601200b489a8004a024001d440c8075290192180d03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 170810953 1250 170809703 170809729
    0xb0c0705010c050a0b011403061807060c051005040813090209060906090301240f06111c050c03180907030b150318030705071a0703090e060f091e07050702010e 70
    0x984192503103100011740c002460350203882d01e1014803d01c40c4101c401c1514000016241c008845210401c2641c1039401240c03030790990b5954101100d614140e45000d0f40f91914160080d05114941003e220401041c400100082d12000d41c8038504d180d100c51b1000200d200e50340400341d224008100d00000f40c2044800f07440c6400700100001000b0003400c06c030508200c81e001072140c9108501c0070510400e9140b054510180000f450320904900382002c5495442c0301303100c1d02da0305844100303041103a010311480840340700503c0700094a8555600f010707001124514254020300c0f894160340000c00b090311910802d14025801040070103044c0e0101c0c943e005603400034140300000c0c1900508403468810800040c000148204028568035250070110f403854a0400c90214180c4020095034021940c416005001c3c1c800e40c2c500f1840d1a180c213400155a42d6403c9a16604520a036040003804e8052140c1d90044c0d02100f06d4404003070f070352103508840364071500b50001d001c03d498203584440350804602c6580c00d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 170812203 1250 170810953 170810963
    0x3102c07050d180302010c050c06011a041509060f0f0c0609050708070b07060609060f0308210a020c06060123070503070b04080c010e0a0201050f1e0409150b0c0705010c 74
    0x79010703101c0c0c0064103030f54901c0c02d24000030011500400415a0900c9001502e00881c0ba013507041030b5284500070303114103040c82840c132143c0190740240c4440e800d00d81220010038030051040188100303400701030f000400a10961000c20400e29000620500640c424046401503684072107011201d6030700c0600400086030103559034812100d022038442010024480a0115003881507110612890030b0300079a84280c0006035044e003014002c220114016818000f40c80d03005820359214403580041c4005100c8451034085087c001000f0b1001c10411f0307900801d00712141009a9615a442e4801565191202143d0500340c03412000c91501826100d406041240e1042c02500c3c41c10700070ba10b4400e072001e416038055454600002d540b02c040602403087c05032491440b001303088503007013a400180c0303603015805040811140c00640e050800c40380c3c0404182a040c042d09203616036855408140c000d2401d6141c40c046102481c1d8045800e20455042d12000e0708000c005045040c00c01d40111141c841d5507000b00d070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 170813453 1250 170812203 170812207
    0xc0f0905070503070c050f0607200a0507030f060e0628060806011a070210171503030f07050c09090105011e05060702010c1a0a020d050c03070c021512040803102c0705 73
    0x40307c45014480d032400b0b4421580c807240c01149848110b50303030440e851000c0d0f0859110090040c009800404d071310048a401c0340d040740d81c1355003900300100501220020210b05e4001c0800308030b0441c0c10010207403222180b85049030750381d600780c40d4007404503202402000308541c069401048410420b2007540394038000c0041d078a007800165070106850f15544c0320f05001090030580a401811070118140740d005c1880d4800b1950041144082512031298034400b9042000021315042441020803002c1e20906010b00700322424a00134075054000c080c28000c036015030b1040031115040703425449001c0f0549900422803458140c0340d900640314040015011100942024400d500c5c098041d01d0702031041c0807080740582d403a030500010034203c40008040190384942401031164240c2e010900c00d140c107906442d840031080b804108201c1c240644100040c0d2400c0c8a010442080081c9001e98010010381c00c0022a0684030400301c6100e03103030035000c911141544000c00d01000c0c07000e00815009202424014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 170814703 1250 170813453 170813473
    0x10603050f240a0b0f09011b0809041119020a02040506040c020304050420030106030608010c03090809040b010318140f0a03050d0b011b051f051003060911030a0c0f0905070503070c05 80
    0x240094101200303c172042035001c2210b80884d41c2096800303545c100e000b424100170f840d4035a03c0485e103000740c840040c060b0340d49a0b2055400030481007110b4040e4182b400501003440c0120300255030301d4540320100c0c081d500f0600824250308081c000d054050703189802031410182001c0c00d100c000c124500384e40040761003000d0f144c560510800011070103840035a802007192811720201c0d9007513580c1c1c183c846003010b01d003420200108800344281e0301801001c4074049860486400100d010b014541c0e221440304040850a00c2009014965804540705010a440601840d4603080751a00700c04840038000c0744040103200b122a0003603111070300300641410084e409103214155070108200c0c6400441d00c070380c481950141820040b03004125030300c0310f1200c207003c03d14141030348140719406480b0050401d6101c2c0545410040701d514080f95803000941120000001d074100f601c01d00348207100d003203504000c2400c042260350480c05070318400c03030040c2c6440c0d166031190722088a120703001c1001684d190080214003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 170815953 1250 170814703 170814719
    0x39170301050310180605100317030c161a100302040b0a080303040b25030501081c050405060702060f070b040c06020105060117090316110f0109050a03120c0f0308010603050f240a 78
    0xca4010924a81f055650310f0a52074804004003003043c1c94100c0b04418000c22000c540c0c0301d41143c642e00600f1510403180d8855141401c12004c016154496003d401002c00c0040da4000c112201242d00171501445140101800d0120495550207003c105400401c00a4045000e42202c02e402441841c0300008505001603040e0245e410314015a00281d15000100450442048443e00e2144905d9a650340c000341940b000e06148a00d11a040c011080840c440096541d5902515041d5110401c60f540d110101d01d0030140c108000c6408a03806100c01c0310105c1c03200d10501c00c5074400c01060319200103408241580150600b80140800b65034030041020080000c403080100c40f80c180700c0c6841152490720481009007070050600341d24100a0070000400039a0740324050176007266000000520051907000b000c854000030004041c0020690140c42d908040e408503459040b140142e038100003640b90508140c1a020064410f002c0030300c028001c071001906010700b450b4107903100900c55413502e41d4900c42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 170817203 1250 170815953 170815961
    0x180909083001090b010809010b0108042307090b031203010b0405130e0114070e030c06031902040b120f0f01080607210608060621030a391703010503101806 68
    0x10002c01d490300c4d5400d40c0b206580102001c1e80080e41000248a460380c0d2000003000960010005003079440d0b80d00610f074000140007100a5401046820744110b01d49500580018202a03460a40a0311403901a04202120746c810342e4142d464091005142a1401c4104102007503807a84600c03285546605000120030b0920610307103242180758011010b441e1007000a0800114980aa8002c0d00103461aa0707081c0d440e0030031254812400f4000c071034138142d903400c50340080c01190002c4100180002e040e00c081d0b000300080a00c02c121001803548682e541c840106030a0700c00f803160090340da00003c00300d4482c600a00b6003042c1a508401400231071740c01144a0000d43d0265400040076401c12414050141044011030038102c00c05445110101540b20f54150340f071103a00340c024200149012000300401c4940848954855081c800140d030384000f0032640c400004140d8103c03215000c0585003201845001d0036641282d0000f400303441d8030f40e440382052016180d40c903507d290104130324110300000340d4180700b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 170818453 1250 170817203 170817209
    0xd0203010603140c0f0a05130b0703090801051b070201111005011d151c0c0906060f030b030c0906061608030903030402090f01080a080702040912180909083001 70
    0xd0b002c241408551060400c256002d0100240400304001a0000d215500103d40d90040945030003a5600b581e05c1031240140c0060300641c0c03000c140020081d060542c4500000155031164000b00000e45501c2d28940c501f440003085182032040902450000d580110b0070155420007a106692824480100000444000340c1201c44580c413001c101620034410411400d5020402044040c82c140c1d505000480400b2a800c0c003411000501c031001b02000f00c1d006407140144150380040c8001c90700d44402800c1480281204000289403c0c0d241005103400110020f091602038040d510035103031503083c4116a8844800c88482c0d4002c0c50039180050486001980329841c0320019542701d00b4584100100c44e4001b801c3d6041e0402c0c80d1006110b0a000850309800c25a03001018642d03500c0c540c0302103000390007031807000b0b00000c01b9001c11100d980e401c02c0010031401d000700c51000000d5103074800780c4100c410240300a002136a00788848030f603140c40100151b84032000060950080500300707108a1100b00260 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 170819703 1250 170818453 170818457
    0x3100f0e0616090b0f0403140f01020a0203310b130305030f0d060501051e0a03110d060e0606070506060d020f0d0609110a1d041103010c02061f1503020903030d02030106 74
    0x40a440d0316a9030203070980014004e8905220300c1c200300e903031011400703010ba8000540302c0c40c51407100b10840d1104002c0b450b8007441c1c05000359140d0036418001b80d1203800440f961b0b0208080300b0503c00b011004014002605060004606c90301420005458080c0d08052608013291401d103801101040040000d00302e22103e20340825500c1e020b01c051001921050f501003410310070140030700c0c8452488003282d02400301d66941c03466190482c00744102c3c0504030103140c2d1510413030006450703010612940c2144040e24082e450601543c0c85040034801e40e8400d400001e04030b900014041115031408900000081c0d000601c10840081c1c4400003c06400040000f203d5a0b41d482c500801007100c00e0104404d2501d0403680709030114906101d4441c007826611030110115540f400041c00c001078501003844146024000f0400c01c071b54000e010b543e42d8815503031176403513051521011040514500700d401c00e40d6914113074182180594001900a90400502d190385400140482d050b200014030156000300169 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 170820953 1250 170819703 170819731
    0xf03031d030d06060513030602030411130507020d0f1b020a1d09010b01090f030b040309030605010602030d0b0306010302031c121e0f091e080909160f020601030203100f0e06 76
    0xa802d00c034088592a900860601c1006e00c201440c41c1601e038414011a0781004d0f025960790b441d460301484a03418000c03010790099903c124801e4140d01603010f00d205048903001c580040d61071810584078905c1440d1600009884641c3d08400c0c00c03156040300301c00e5840613040c0519240c6840080901900784c1885a070300f60040801c1190100e02400352010105082c20b04101c560b040c0b082000440e006e50001400072132010021a04142c403c4030b4003801141c02c01002c0010b5611018002d440c0d6000f50318441001d42416441c0001e85004910181240e900500501100e51200ca2106004004000c2e00301030040460003140814601e0040b440100000041c1d844400c081032804011551071134401080e007860300020300000b030007010100040d85c510411a10026410b45840401e0381f00b42c60342640c1004102c010301c440540c81074400714206e1156225108544c1004804a80c1d070701003488043d40c0741e4450744a602c1000c1860340700c201038030303c0584080798440b281d101581c504407083e03601982402da1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 170822203 1250 170820953 170820967
    0x3060a111c0b060d0e24150105070f0b010801060b090f01030506131406131a090c0409090f03141c050a0b1c0203010c030c0c06110c06130c0e090a0f03031d03 69
    0x43c4400c210062010f290b0403048504080d03038003100d06d0010441e00e00c0c04400103400030143c2c025400e41d15940d5202c800c1050b20308c600d29040d541c904081c0b040e0300c515824060b02003031402c07022080c0c60503103602406004030809040011006494007800d0240c2203201e8941c0c00ca5111581d004019222290700001e18182c00d01d8000c1c420034071b100031b13144052986044056a8100f0144101041001084415100ba03488141600000744031315403240030a180381c214070400b00004656000b0400c3d01903241d4901101c0401d454103c58452041525900c2044079500c0816080c0341e400705400148801d4005040c403c40b802044a18481c90b042415044580d00040c2c1146801d0280501260940c40d050011a180e0800500b240c6009040105565280d00c24542e0703520500c410b403034000140741b040351140c3c1042e0410210348001c010b01600c1120003c4408187c0f01d05007590303640102d80401c01052007204607120741c260141a840220201503d8016502040d110806080c240c08030200c0a10794541d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 170823453 1250 170822203 170822231
    0x31805010501051e100f110f0601170102040509040f081c02030f0a1a120109050d09031214032a0408010b0111011803050a050d020403030e03060a111c0b060d 69
    0x113920306000041c00c4000001c40340c03e886000c80300e188400705040066161071110300941d203880c800c14907074100344030303045403240b410400041c00c80c100d51044001d401284c032414841c609030300c124004c05820a4100c00030400041c0c0aa44100c6824024490942004042d5401d902c01c1f11905624100031074000c0140888a80042c0c1e01030303000800c0d8102003141d014407001e181949c0000c1d8030900e20400740401c241c02880001c2d04000541c0754400305a0700c0003014000041c0041c201800709940a10130042d68150003800703608182c0c046690004014195030701c4500c0c00f542c0d15480b500c40240280b9036503c0d40010001000500050aa91000866100344a100051a80c0c05120505420340e0608405940204408407180c0d10b8a42628109a45d07521290050320244104880a84e20a10000d000801d140d4851901644e101d022011b482e81e5850b0760f035a00040c1c071401902c400710404100040603d0f5408044c840c00046184100452091030441c001603982c0c000360600003c0d90788818505600c01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 170824703 1250 170823453 170823469
    0xf14010813170702130507020f06011203091202040b03060a061a030408070209100f06120f0506131d2d0304061205070e06071211010b01021b0103180501050105 70
    0x88065680c00300211803900c500e01070901c2c001c400b1010780700000e03520040d5100c051072a801c20500031010302c603509000074025a41c2038160345414140c064540085026060884524031031a0107a581c0740001c3d08140680c1c81d10034490104990241d50341c9800c0070540c0341031143d80c0c45071503007101c0003480c1440e000c2c0b203019000c41c1c01003000c07151000f00f0400c0000782d00c4005407141180c054a0305159503650741d95001114407039030030400070012112400650540d204102800500c0010410b101c05007001d186101a184c003665010351044000c070500209210b40d501611120f40c1e1041e10002c05040800d042e1308001400415400710302507004035910101d24130130400c06208031000190f140c2450000300401c00404681204850740d161400714030150b01c160700d5042c84d0b10008040da659001985040106807034100b010b9008104c0181c40004080c0040c8030f007066041d8181c001e03140c034000c14181c0701c0c500c4004024090616a550385940070300f15141c000042c6091054000240f50b5040800b00320081c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 170825953 1250 170824703 170824711
    0x1020106031e031112030429070e010203190e0a12080d1a10020d02010c110d2d021e0a020d021e13020703111204060807090f140108 58
    0x15a040c020100006451030400c180303003541140c004480603003940341c1120840d9880b50322001d80d104054000b0300e0203001100031400360748140c0b078a80460000e000d40341c14902200402d510643d0007440090603c5001c1c0782c440341030450500c15240341152515452108e242480c40840002c1c4c102e0716a03c440341004400800a40002404000c0c0480745075a001c0c3c4070701c100d2a0721802c0b2500ca180300c0c4400d52a000b143c4144c1c043c01007804100310f4098400a40e10403e0310403000040d82008c020091031400703031146440d4240b000000e00700c02c1810900c00e607585040e44071070402c50500c0b00005d0180303000789000810842003950241a211481c40b59200e1201c100119070307800340d00071400c12401665803014049110ba4107403413402d40d1170301032104c0100294141c66440d0b0800700c68042c03811300747d100340c1c0248046031203034030b51003800411080746694903510142800054841004203001d100e008035800c071761086142c0340c003025203611900c040c6080583d541c40541c00c110f5902c0600000e41e0003441560340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 170827203 1250 170825953 170825957
    0x3070e090f0408190302090604090507080a090b0a151d07020f0d050412050a050105100f0b0301080d0e03070b0408011a10090b030606070b010f0503120c0a02010e06070605160201060501 81
    0x1c0703400c080e100c000051059409803800f02880b042500302040c001d40554014034030090034103468941d04c540e000d024140484503c400100f4080009100190601c100448a900620f07e40d000e82d0720325010308014000500000035032441981e0003e20700c3d258080e024900e0045507c928030506001001a10380400d2401500c201e40005440580f40c95000782998200c40042c0c200c04030720704450070024102101502c0291455082104020b0b0795640c80c2c40c14411111054041075620707171388001202440c003082c003071320302290081c0601f81d50481c45480c0c90b101c541c4004050700d00e990342d41c0745840029806540400c400b65150842840004070b1040709200c00502580c00d041e008d203c01d44010031034a03182c0100e03048183c000c030220315140ca940d01682c400ba54030041c0344105586407c0e9200305182c4a1103983e10a01c0f810f108041d445420200f0b03580e450034618010807241d0348650054859000000110307421440c14407429020544074015180104441c140b2036481c2e1990100003400e5032078607005181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 170828453 1250 170827203 170827231
    0x8030712050c061f03081323010509091b0403030305040b0f0105030d0c0510060b0408010e030909150f0405040305070201090b0313060b040e0a08032d060111010f0203070e09 76
    0x60229001c82c005610122400c0038242070360159080c103100c0303c130640010f89828000700d5542828052003510800392003640c81c0341c0c0c80041700c00ca0111407080404103068006030040c840c500345400e003215200d4204554010a000d0b09000f181c1c0d2440680003548140c00290712031043c0001d01c41d9810380550882251400b0b240d00d176041c0b0021a0340c94030310045c4081080802103000091040500800c1c41940344805d0074000310750740e200440e046400ca40100007055203031081e10748a015002084440ca61405002403e581d6121070385900c0906c044071803070b43c0040c07500c00046550780d100e208941c0704500c01d4035403c1d01c032030302c50000500c4114580c004c0881d1000070002d1102d00c2d0041c0d00d01860103a8030600c041041030303211002c94094010050b20036583d102d800000400c000c50f4401551050b84a0150018001024441d680301011a0b1100c1c1c7d40c00030002001c14900c4d442081d090403404444000070803c01c14500c1884200ea008031407100001d1942403111500e858107104a640201134042000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 170829703 1250 170828453 170828467
    0xb07080a09080415030b030105010605040501020f071202190e04031e08012709020a1d090106050f040f1d01060503070602010504050601050d0c0801060807090e0d0206060f0a0902040803071205 84
    0x742c51169000f9240501c60072149070303801601c0394109803103010010b00280041e585d202009041e98026008060140c0111648034244000001d0717060200c030501444103401c1c8800c2e40034080c100e441000c0455140710301c1c03500800e24400c3d05d505240251f21a0303455800a108402d00700e94103421602507981007202280040200d1001c10741c5409182e004c010000c0101180f007041d9000034a01118001c0d0800642c00000418008c00c801000329020074140351812075950500341422914a409103940c4924501c10b0000c0e541402e0b8001100b000c48002d00042096000d003c283d014040006144641d030345a2605102d54182404400010300c11030001340441c0c00c2039601d054440b034050042ca8000c41108004409101c980c80c0140010202d0000820203030303880f82c011903100d680e0380c040c0810881c00c050640c18011800a00e814080106501403e00750300c440c020400210044079446034800310710f000108000000b0b20040c4010300e0150f00440e0748004901d4040018980c0b000380e503041c002c05000c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 170830953 1250 170829703 170829713
    0x180103140105040e0307210306051c0f1505091b03150606070201030b06030c040602071202010503070e0a0b0a0302030f0a0b06030a0b0315130b010503030a050f1b0a0b07080a09 77
    0x205040d0b400440d40401c0502204445600d035020f5684081e1000c0185070f0b00c00708100150048040f00040d075901400499140e0040c05a192144008210541c0710b10a050000c5510740040d010203900c40e0114840c000c1070440c5c41303400c0c0c41d000e40b440b28150b0003000c01c0e03501d4890306440100d90004294050304d910440345e02d000300c84a100601ca2070082900081c400110ba201e507011382c0c200b9800411882d280e0801290b28040ca130018080c0c0000b5214911001c154403d40d458000700203a8165038652a60380c410b4412114a004840d04d643c11148012001c45c0402d00c80d009044400001d135070050b20b9281903140c1401c0400003601c0b500c3c0292409000380519201e078002c403035000c00d48072404200c0b030781000046880d2400440320f00c9078401e42103060000181e40c201350740d14110300075400000942d884904041c1c42e449a0020f402c0499070820403035803040a07140140c2081801c8192615200000c42011810105071900071200c00040740200000300c0e402c580025000900b03882c0400200071030b0390790 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 170832203 1250 170830953 170830991
    0xd14040308180415030b07020c09041e120c0515090d051c140a0f0509030306010e030705060a0306060207090207080403030c021306030b07020d020312011523180103 72
    0x409009404002030001c5228100c11a648034448054010491942d42000424004e21280400c8500c20381e440041100e951000403004d160400052900c0156103c5682e2048c503d1000c52446410785084450180458000a85a40d054100b40c403490b0010304180740c01418000d80380362051b8000022824000508400580007030390311164200079654000d0300c14103020f50341e42071606e010410300b00b0304005084004800c0d41c2d40150200c20091001d251841c2000c41900c03421143c11407168030510004009620507445600100c1014083d180701c1501e030340c00305805502c0400d600010a03100c540400c4826070402140e070040c007205000710304090452740c8542c940d2185100190400c10180e41000940d40c95402540307400030010002c00500b07540e03240070300b92050115485400350003080b111a05c46400401100d01c0341c42e21450241d2580e00b0141850070b0311105002510030005030300000100205a095070400050a0015190301e40440c3d00703d40415800c9800003504050802c801085c00b82d160000b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 170833453 1250 170832203 170832209
    0x9100801120305070c24030506010c030e130209060f03041103030c1015080a0b01060806060c1f020903150108071a030609070e040f0207020901050307030302030a11100603080c0d1404 80
    0x646559200d40764240307610560280d0304049842410080c0c0f100500000d0440d00900032491f40702481250f4a62005468074101350401501060b01b015000d1514070b00610b00102407200c52800509012103080850040e802c410202c21054400106000620200025901c00e00004030015441d051140381426102c8400d544020300f40341d02d030781e0700b0a44890322443d0380c8081e00303080b412a401c8104074182144c9500080c031a22000c900454042015414420300f00c9288510017002049190007051404246000d050442c0d100c0c0380d420f00800506550500c01e41035041c01c00e2980c01d40d1365060224250400855900900046949002c2e00c0302600c440c60070360f07500ca5401c0343c4040155417842c506481c2c849503507500540c0f1a01d40300484a241215502400900d4002d03103486580c0c1c0e03220002d140c2c0d10509400301034050ba00c20f000e020f201520400307190389801701c100140c602408a2102500030758900e6002180d80790b401141003622035108120382e503094685441c03d010b000b108805594403d1140740 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 170834703 1250 170833453 170833457
    0x3031d0604050117060a0e0403020a1a01050f010c06020f19020c0301020304110108151207211e030302040315060303030b0f0f210f0c031002040f1214010908091008011203 75
    0x2a0008501ba594001346000406e0030860742c084d50320349880d000392203150406089a02c00741c10942541c20b2003410820505a403005418907100c400000b00540ea5100004d90881c1d40a408000821440c1c01c0e68024102d094a4180c604600046500002c1d0a0841e0803c809009a10610401010a82d400213500d0391340000e081c070b61f031181c59003510a8580c940c188003d81d000301d001e03d403641c5407120000d01c140480741003454065084c60088420040c20b2001e0102400030364a41e10241e0034071212441c0310180030300ca4180145801c0e0381c2d50380d56481d401210701d400f0041c0e50700e0108001345a014017820710340407001c5508860030710a9000040300d8540c0b010ba80da004c2c48990841c0000560414418200883d00c042152103094540b490b8603038603448030030924002e0040c54681041010140240c6095641e030a06011200d42031942c0701c0300700003201005035081e401c00c00866100d10028415420001d000742441c5c0d070b68003429410710110980c0600c0190400803200d0041007480c120101100f540e5501d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 170835953 1250 170834703 170834747
    0x6150f14160501090521030c0f03101701050402042315150315011704120309080f070b1506090102030f030406061e081203060906010e040608010603031d06040501 71
    0x400c0c2000311854005000030019864113840f04144400091640c12002d000e15080c080a1000e548176140c03404280e6100c50169003c3c406001000d00b50f1029551100c25128581c0c821aa114041c802d61450400e40410726550744003400b0070340c1000d0280205508414104003443c00740207001411081000309114484501b011402482c1c0c3d4640340c440043c54200d000e4503407241412103480d2442d03281c5200d114040f4590b84120f0000750340c00b5840300d2140340c012a80d4007806030128401d802501c41e102048820b80c501300211040c130440132001d03140003400740c49148114542404540101155460214415030041c0003410540e03a00000300e4001c2c09608042a8680e181c074a40303070340a04403940282c3c45a002421048901c2481c1d030b2002c0048499580440b0091a403000c2c8880c4548029a0710b950030060000000d81c295004810002c88403001030030000715541d558400c5805c507002900100d00080c1300f0202060f006446003070401521200321085817500c4d20f441e00107090801860340701e45880c404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 170837203 1250 170835953 170835967
    0xf0904021c05031209010506030304030b13080a0305060a0504110405130b0414091c17040302100507020705010306080d020a350706050a050103020604051912030306150f14 75
    0x1e440340000d00030801034061032001c021450000e4503600034040d041c0b88181d40301c00081a28905005407402076201a01071490302d0700b162a07a440c2c01c600100813404061455070103c0000303c6d03001c010010020140d900083c9401d0507420044484000da210318852403d18001e250101080e81c03c480440b5022503d0b4034a103803c031010000a03284a03d9a80d51140c03620701c5080800c03040f44202485403550a085e58036801c20031809000c0c800710509010300040c2c80d4205c3c203035000843c0d509103130490b020b801121442c2e403041d29414181c0328103d445e440181c0000760208584d5070140a0040980440d9000d49100322824400955400000d43e0180c0044210691070800508801c80d044050340080500e1f0340d8040c0c40c081c0026035502c101c0c01100c1440c0b401c400100009101e11901c0d06a9038024000c2d4500340c90542041039106240d900b408800c016a00c00190a40e101d1407a490041d100b51004240c4518007400080c800310782441010900c03085410402c2c11341c2c0d11210701d8001204101e08a074480b08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 170838453 1250 170837203 170837209
    0x1803020603270a0f030f11060a020d0e0d1809020301031104020a0903050f0303010e060f011707030608060103050c0406080607050306061810200a031d030c130912050301050f090402 79
    0x10403401e03442e100e0107288404414003000d031005558140c000d80301c02441e030900c11000c8079581e022411600d1580c1028010415202450f0014440044031140106880750301e0440b0a0400511425910124081001c0f405280c54200b800200819003c0702c01c608542c91901c0700802c022090b0003940c8207a40c005540c80000340a00207100203141c10804403190310080a621550300c0e8400e0040d0840c0b1039501000612520380750030302000400041e0740d022406800c0c002a0f1035880b0300540f03c0400c2c1500c42401081d104003c020450085001e94004e015905401040c48200e40960704000c0e400e0b0090810040465023160889411940564105a480141c505612a010340c0c41c517034140c0c00052a614000d1440d400301130f070b1102e10005020203c01405e461300e510f9640c03145840040210741a1a100c413048515007a00810a2002500b900e8900c52110300140d2442c83c803c03042c41d0081c0d5110524400c1c4000c4503268062803daa007040c91440d41020300003958040c5205640c1d116141520024086403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 170839703 1250 170838453 170838511
    0x10c1d0109030b07180803030105150f0706090c0503102702030d0e0d0c060503160318060506130608060709060206010501080109050a060b04090f180b13050321071803020603 76
    0x714504242d403c00381e0300da0f550a6208d074003c0c85024402c210141500500d910114115100f034102050054a0082c6d285d48040142ca01c5250654446400c00d90000d80350324244400252610b44010008442c8040d00d90181e521030081d80e85200ba0b001c0e6981000182c4000a000c2c00c03003609420b020007400d04c40300000707103002401c91004040d4020301100140140c0c00601a40c0104d0511100b03400c07454080c01d0460444100c0740150290101514503e000f181031075005035000314019100d082d5001d8000084025144142d001c081640e101500300180a5440140e000c0a00b2061014041551401c000200710034818003c8140b0b0540d81c1000c90141116a4428401032a00703c034151307100c0e40e44072404002400700d285056002030510305407044c43d983d041800d40d41716520540c440125190110390100c1844113a81c2111544000c110a198104c0c98007050901c22250120480d9603181004c0d0081c01a400c00d00182c962481c00e07541440180c2d224420f481d8424021102044005c0642d80c0c889000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 170840953 1250 170839703 170839727
    0x1104050d05031603091d040c060509010201090203030a020309091602030304290910110f03041416030c05040f1b05220305010608011803022814010c1d0109030b07 71
    0x201d2402e8401d0004c050308851410112070740040d2107100001c070768580d102ca940c8110b900402c01c03000308078140700090040029109903d010b100005e180766040d80401d185900074111038000d680080b58801c01c500d000301c00c0d26807144c0051034180000d222178501950700c2c000a4402420f103201110524043e242040c000104451070710030882103030400c104120340f40c2041c8502c12081d6402e01d00d60340e01c12000b0100300e94401410300300c450301e141e40c1d680300d10410380c41035500c10340c06025a025100b4491030b042c4005018501400c2100b81c5e4074075100401c4222403010b4800300625041c4481105000602c0c0040401131000d81012039a6210316684c50542803c0c8180110f0810b50000010091107415031060081e100e01c840200405031201c000d200d541c00c000c04008006901282250740d10703070421081d07608104c00f59004d40149810720f84d1030301e03105000e609508282c1da40d078140c410145580484a000304400c09003405980c3c5043e040001e001c0d021901000c0c10101041c03000c1642680b10329008110f03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 170842203 1250 170840953 170840977
    0x1412040807061a01020d1803080703020703230c040c020c090604020d090f020307091506050f040e04051b010807050d050c0f030903071a070801090b040b1c151104050d0503 75
    0x200b042c2542440350800301140841d00503c5504504881140100b0b0341f442140166521904903034510340e510880e541c8068001c6085004041c0000300103070b00700003d172a802600420000018165084403450110550071180c8501d00300310f0200522a004954903a02076015940840c081c0e491001081c040d20030741c0c410030306080c42c2ca0860800d001c091300e030032405940700b1020354411940c0d409001c02503400c41000700b0009504800101b013514001e100074502d88031130054107810242c1c4c503540303c0c101c03050485094030a9003140c002c002454010b409802c1614009003444101414040d500030700c280228005000c40e45d0313441c8041260050544281c40181000b1000c45d80c1d80e140c0300b181c1036280d41104104650717140d000340285080b0804000c015100b00f1a965441d08140c0c0390010860180c8156031129410945c3c03460302900039140c0d00303852020189801c00600e0822414500854124003458100c2c844034a0a0040340e95141c500d400c880c00c03140c0449032000707015001d04006080d8407481810ba40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 170843453 1250 170842203 170842211
    0x1c200a050609160b13050603040c0312050a0f110616120606210b0310021612030c0906030e030f09010909050a051914010302040e03040801090605010801050601141204080706 76
    0x10360010b0015180410f116800e00d0b95202c80e41da6180140107000e4800d41210203154260140540d0400340e000e164050300509144040aa503070b2181100741c02c091512b0701c0000c0000614540f202c0d00103002c0d030049165450a04003421402c0031458441030701800701405825420044190300340b152001a150100d074a41c2044800e9680e00c0141030400d000200030340d90400c2d0b01d40d05604520522410240641c0030b00500f02c9550b00144400080d40440032494901c482c2035443c0022071449031505084046540f800074111016203c090602113403a40484101401d104851110350404010341d8203071031040079a1030b1500c85510061f180f0300030580085080500e450104282e000d0150041c43c007403d681c2040c61207000881c080c2c0400e0f0f0708072540c50b0b0525010080104018141503004102e80c007641c0d8241c0b8205600c8801c03090940d200c0e110f081e2405a00d682c01809489400c2c81303903c0c1c0010090804014015004140341c2c643e0282280c44603042c036211000405120301388041f50407042e40b00038104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 170844703 1250 170843453 170843461
    0x809010c050f030304110a0305031602150307110f0f0307081305090403020a02090c0405011d010905060a020a060b0d02090c0c010f02040303030e01060e0606071502210103051c200a0506 81
    0x2c3c0d07481d0030488065031400e080082c0c41102d07003800e1003e081981d070000051450001580f4000512550203541260044a1180f010881668240203540200384a80e10060b03100381807000c03039140008131074802e002a008403082800c829000022150800d07404404644c03a90b109840c400c600c6181a4001c40d0425291020401018ad0109020021320320885640d0100d445406000320340303001c1e9006482c04205907450300c0c1030740081c140702c00301c0840051400864150301c0b5400301d00075030014880f0101681c0150300c0070b02042802e018035092854241da040a980c045500050152100500104668600041d200310022429080110382024840080d556036035646001401040900c8030443d0395480c145001c00c054140da0480d5019501c002c10381c07410b080d29070722505038004107807004111560b801c0140707440a2030056420551005000d2100205601d0b42c1062810451001c100c500d000d48010324080c1180e40003011980000d0a41540c4a22540c0d901100d510b0012000c2c00545244a5a0300704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 170845953 1250 170844703 170844733
    0x3031605070e01060302040f140d3201110702130e060106050304050d0908121602040e030a0207080102070209160e0406030b1501091401052209060e1807030809010c05 73
    0x38400301c2e6400a412110703030380d0b103041c01c500301d015500070203400e03810104007040300701d104aa510b400b4034002000b83d0210b00c0c46541d040700080000c6245a000c0307001050140c21140301000310505c055210000703004155444002400074401c500000340304071a01d41039141d4029069100f101416810800ca400c4d95031200030151041c1c00c04c85d81294188503141c1c01c1c81d417541c0b181c540d01c8201c801042c000d2803480030115090030b0b5500561040360440c04012000c00241e91240104804070b45058040c580d11080000000c0c00c2c0500354100b9500c41e801004400010303203035050b540b030344660301c0e440301801d02e0f60f000c104680e102000300040ea8400c0c102140070080c814254040c9000e101c003000c10618085403000151031039881d0344600c2010a0509807000d001d075000e100104101c49031140d0540c000103030f0f111120a08503594000c980010f66510040c0049883c0341002600440c0400d0b8507811005401e21b859624007040c0801083d40e1004034568440d81d00030101d0348444d0f944401a40d00c400781e05200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 170847203 1250 170845953 170845963
    0x602060402041a01020a02060a0e1e0901121110030902100f020601050118030602030c0403020a03030201050702010b0607050a060f020d02040603140106050a080c0a050403060504080304020a0f05010e0f03031605 92
    0xc0e0710035032603c03c015020144001c14071070b038140d041c1c0282c80c500e000d50702007001c40c1c0c1088200d00d00380518805000f9032036485440d0f2008451400b001c250311100da01d030034031002ca00d050f00000f0011030840c601001086020203880c4483c0c078110381d00c404007900450200e02030a00384000940010070711303220410503038002c42c4040408260354203c4401d40c5e640c80046400202040c5c441514180c2120181b01051058004580c060602c1049a190503500d034045001e02e0080c0e4002e40042c1d40d0f072024020055420b00a030f0300c803418115507040c1001101e44920341c0314110200000c201603501e1920441c1c2a03107a40654480c944060700454441d0381d5486d018000c0c00810200c0704100303183c01c0001c00c00f1030050054540052056035050740340c1d5a8000a0002988180c40950030300009100c0000011014010244518442c0b0815601d03402e0910510007103500c0e0b41c11041340000c0a83c010b0100d668170400d200172001040703c0c0c070501050b40b4004a41144180400030026000315040c8000744480090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 170848453 1250 170847203 170847211
    0x130306090f060e120906070c0b04180c0503010609060305070306090e0a0b090102161b09150608161b02040912090302010f020f0d05072103060812090a050105030c0d06060206 76
    0x400340955071203070043c00e454035120710080b41e10010070f2281c91031a0416070f01400c0e1261040d9021601180c980c20351180b150095800740745401d0103c50b928440f040540904401841d240c01c01d00e007154140311000c0d01c0004d1038082c8504050342c5600207a10380e8829041311001703000071081000180380226502f43c64111444041d00c60404900101b085c803c014400c80d10b079042540784210074520036690700883d02d0720381c0c0c0928040074003100000c03910002034410710030006607055400240510f0300801030100e0f0001810061810801262a503900e900001c1000842c00303c0c500c0b41c0180652440090b0040060041c090240211604507944d00c6400c1000481070324001d8a4900d818031072010120703035030310400c0f0081000b80c000c442d0741c01c1414013410280200c24401d41020440c0c40f0107034070702c0c003030344080c00c0324000060345452042003084000d02c0059114150300c0c1000303180c000c0110214045210307500c10241084070000015011105603400e551416403140c205214080c6d69100081d91713540d041e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 170849703 1250 170848453 170848463
    0xa02031519091b1e0b090a0306020a0207030c0b070320010f0e01020901080c040f06120b0405130b010b070b060621010b0904150e06011409030d02030403060509010e060a02130306090f 80
    0x5003000c21882c81312818842031110601c2a034980604043e19850107401401800d600420742000c003000041842c00a0148141d20354001d1407668a14100345a4141c81640114800320040220401080c5c0c050405030500f5a110080b0000d036007403060305801058104c24141c909807070f000d41107128039410340081c00e029034241c1e00c00056447d8001908028840c900c1140300da05140c6400b00301660254481e00845240400001010700c50540802d096800032203541c41e80034401000c8500300b12101c00c0a5026145840325103042200c0c1d642c40041c1090302912682c0710744404100e0305141e44008100e0117001d90003024814465941d90a01c201030b400280c560b9120b40e040007441d030304a0f28130760344c400100c0c1c1c0d02c9110ba601503241c05c0c00640c0d400082c400d8403039045030200301240c05c0d51410440f10481d071003260b0007540e8940c510309000f0200d88003c0c014602c117905040c40c0c3c20000c800000c106400c465842c5006a6560050400711584e40707081d4402019541015030a5040c0110040b21a0203a8020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 170850953 1250 170849703 170849753
    0x90503030a08010915060909090305040b0d0c02060c0a0f030e1e030d06090912052208030a030b030331150305040203100b0a060e1302030c0310080a0203151909 70
    0xc2203140b00402d8146c01040009204000708001440c259005a41d10b9030081c01c1c2149002d86400c0c09003101e40c1310b1501398490030f44580704031101d2513040040e03683c030161030402582005480304005201c0b6450003000802c01d41c44801044940c3e805016200c1d508010902000c0e0010490301c20300d440390441c100c01c0c0c0301c42c1d01d01000000e6901207802203038000c550246413180b00758800c02017503425070420901080800c0700407081040030080003c000010300002c10003191641c01c80900201a04e02d41c00c001c0380a60400e020f02d1128682e13402d05464001010661803906e041a00d42c402d80f5408a50300407240b01074a0000c80712250b8241e032205004030f0082d000d0300c0b44a400c1a241c0c41c03d4400c203261198020602900c100459407181d4606050000c004006010011407200104207a070400c0d146130f040f007d0004140040081600012002081907501a02e07440289800203034580345c21031038041040100c480020300d101114260503295140d0b070042040b500549080c00d81c480360001d40c05071488014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 170852203 1250 170850953 170850971
    0x1030c0803070807030f020c0301060e0115030b090106050a12020316110a0507140303121f05090c04050607032703030210020906070f140607080603010b0f030a020907090503030a080109 81
    0xc003104071882e294000c030300149004c010f81c0c1d0483d007110708584100114014010b46100c01d41c1e080c02040000d01c034200b032000d007e5040c4a100074801190344001003d261078084141c545448040c00700d0304550302da00b09540c403141d040000361405464400b0098010348008100100580340a180c00255090350ba5021580d00c5020025607440680c4507015041d0391000008020302c04a48102e240042009820740341445c01ca140d15500040c1c06590f964218160030400f42090300349a80208024074088424250509244110002a20540c00b030305015800004515003858012500206042900440260f5080c00780b1900e05240013140030440042c040c10b520862000d00034001c3e20030a15000b0710310b43c40c5c82c00a07a6400d10801d07400408440d07403480c040001d03410610038020641304044c20b48400207140380040402d0f00315170b0f0036000a4401c0130b40005008403030724000388100e0003a07815100c0002035141c400307013580c42001540c404c9501d0f100020340440391030b610131002812070307943c40b40c14840741035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 170853453 1250 170852203 170852219
    0xc010b0a030c14040e0606090903040b0c011b0e100e0d080a0203360603040f0803091f15030f0501060e09010905060a050c0f0f04180c0e09150d05030405031501030c 72
    0x1c25045e22075540c05a0041211443c2c107000e410f8104107031804480c545540c1d0003050300350f500201d00c0c108c4165034801d4204105100103845444050880c9088404800c0c06400030311043c00344d1b180e078401c01000300f621103032035251f40d501002c0f026040a100d5445000c411030080d5640e000c090b0000284038210900c401c00c201e04280f02405110b4800300d00c1882990300140881600b00400035a404180000d03088041240b2078010350240c00000c0c0a055030350340e03403101003d03000080540303a006146410203141903140d0100303003d01925800020401292280d007000c13405403069403c821441c005040a00c42407010550050311018899400c0d5081c90381c50440c41d104450041b12002d841800401820f455900d00c00010580094020680c0382042c0d11800d18103d09510313a95040c000e03ea0b100300103140142c210790707074280d0b620b000c507001005440c7c03111100c01d110300c070401c22078003076000200000304102050040e640030b0701001d000c449a03804020302074808440c0c00e20056039000011a40858200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 170854703 1250 170853453 170853461
    0x12030b03030301090b0114040e04021f020714011e021e06090a0209071e08060117070c021309051b0a06090e1620010c030c03020a0909020c010b0a030c1404 68
    0x1800003005035055130320f00b080580180a4444100d81004504404030b0912443c6d203020304050081c526400c00c0303504c0c2c244107010b0400c1c66055507014500c0c0d040030250101c0d900080d000141c40c4040c40c940070401c6140d005032521720b480041d54a00c10014854891181e034001500b0b8014008004424103440c142c0c4d00603915108140d403a841550403d40340c03480503040030341070980c0001c00c5250151807013140c803c212101c1d118a8042a0014828500b805550b690200d141110001d04444044103802c0414000c1c200d9080c0d010024000c0a1501c50301085003026400000c1140d0002c05482440006d501c210b000080c03104201c83c0300d5565204085403980c460561102550711180048a4503150030071881d50316100c440d911740c20400741005800c40302a0680901c03000840072000070900171003400c0040c0c06e0310301368000c1804052040c0320011140c0c1e80a000036041b0780740e40310700590700c0030038039481800340000b200c2281d0001c6c0404400070810081d006810100d40010b000f80c001201d400c000c1000f66 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 170855953 1250 170854703 170854721
    0xb13020a021009290106030b0111060411032401050a0f06020d0507020d1a0f07320f0304030504140109030c050906030a120e0916090614251203 63
    0x1a8000c1d5050b081414440e401800e14070702440d4101080101d000c1d0480e180c60b00801c81c04155044900104003050701801080304102c42401c20240c000c407030300351490b074a0100810160001c108013412041d592024800d843c40d00f815001207084992290030f00c280100c0082c402e1600a034071102d0300140d503544498a0b0815510a64040d04203414028030807503c9400c501b4044e079104681208400010f6541c03040f0300708803405a2207441c45032520005d940c1d03044100810040610a0452003400030b0700c5c0804442100088103e44210a156031200f51825030007407109500350410f000060106050f0450094812150841e0106180e42900401121000e07002d04c002000c00011107400e010307520700810015844a4040e080310084011503c0304504d840108030b001e000300303204518000740340c00c1c41103100b54868403200c103405003107610003801814031003103105420420540001c103588070441e00301112481042d01041d05d105180083d41c15001105420f811260303805e04801081015029014030180 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 170857203 1250 170855953 170855957
    0x1009060e06070816080f040e0f09010c02060a020c1608061009140a02090301021207090f0f121202070e04030201020d0e0607020a0b060a03152007051c091205010b13020a 74
    0x140340341d450040b140b00c014204c1c01c40ba540010300483c641a11315201400062200d8500a20b040c181410500c032a26800740440c4030590502c07a16030105d640000f091500044000700041e500c1041104443c10070301d02290a503158140d03030500003a40340000a00f18020344100310905025980c4521000c1203d0300c210a8500400c0b40f4800101440070981c041d002e030030b0003e0000b514000b4841c40524071013030112070303990120b4050181031000c200c1c1804080d0242900350140101d190a00301c01103440300340311a004114032045d40e1303a00401171080c01110010041c1c6680c1e1440c2e0304080c84d02901030b400c14581c0301c0b84607182528240d000b41c000034002d80a81c009402800b038486150f1038224044200810742c41d0810389040001000880f5041d0020403c581442c00080b03004003c13504030220f20751003500302e10a002c10700c10103002c103102042814482d0341c03d01c014035281411542c1964070407080c0e4000c2c01d5041880d40403900f80041900030303540e0094211003e201004101c003080080740240c20ba0f0740c2c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 170858453 1250 170857203 170857207
    0x503011409120d021b07080c0301021204060b0604080a0609031b02010519090f030614091609050a0b0d0305090102010506030321090307050106061d0a03080304031d1009060e060708 79
    0x2e0722101c1c00003040e100e016100050700c5e082110b001c050140c800340210022a50101c0300030455048284546141e50314218025880e04585810100c0c01000140002c0e01081d910407011516544040448005222200580c0d4084a25081000060031f43c1c00e4190045110700c0b5110204d031078055085035800d5416144e00d4101135031907504043d00310b004400c40e0148a03c0321804644540700e07030000401075124800c04540c4158180b95030581c2138000d802d00000740e00501e0803e00c01031103c6940c105860340c0c0e5000080b140d803100c0354000a4080c0615494002d070f50010f411050540c00001020500000c3c0c0013805a0380351007041c590b8a1044248810645405c0c880b144441e4520030041d03500031290030210380c10580b49407242800c44440c1c3d4445000b103604280315030514540d44d80c01204140b012644540721a1854454216510004000404020340034152440c00c1c59031102d0b102c109100608a1504e0031081d440c040c0c507410903800b48401050844000080701e03d440d00c1102c100c1a4004a81c0d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 170859703 1250 170858453 170858473
    0x72d0509040b10050a081f0b01050a050a0210050705030603150c0a030c1107120b0c130302040b0303130e010602010b27060303040e040b01090e0a0203070b090a0e0c040503011409 78
    0x112000c800f804940c40d0301e400101c00911942d9a84550000d8404600a02104004404c01038003c1c004412058481c60601c041409240c2c1c00c1001e41e000f181c114200340d551152100760807403e0078421010f0b40d031010301e06000d0040403540f090156203e00c0b420381c11070395141110810f9800205040381c000029500400c40208120b100e0703003040310080d43c3d41c00c03d004c0c50400e00c10f585090039641e402c4580d00040700400c100c02d11546601064010a010800760302e405441816013402c881136000c0039020310780f16104034555803803c004498000c151802890621030b00c1e894018114002131041c68015800c016100d019480d000c0320f1002e5503202c1030001d03403040700c100c15001c0c90a0001000030b03038540420300c400a620340d45513101c6481184143c2c4401090740c1404100801c03211400c5102d0490f90000f4070b4440140c5000039a44103807042012100d0300d80032900001500080e0503007246c4001b54a00d018440c07902a000e002d031007039400c1200240700041c058505041c080c001200c00d4080340c2c0c8554080 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 170860953 1250 170859703 170859713
    0x2120a0f0218041104050d0807020405060a0e04020108040819090302040501053a08030903030f0f070203180402041503060509070810030b06010e060c0627030901080a060503072d050904 81
    0x24412070200e540d040c41c00e041d950310010f070150300d0a000584200c2303400540e007821840d003481210b40c040320440394021803504000105500b0300d0000d00090601400c50086000d120041c010303210520541c88240300d5031000084020181c85c128401240900d00341400403503940342c9a0b98601c0c0c468038880b000e4048000400f80d0302200c544507025034032844031551145c000b043c100300083d032091a151004682e64101380e401d0000420006280700c09480c01c10381400345555010007190360300c810501e00b400e818804100090300903c160b600c40803c038643c2e0500070052a8064101004540c02143d800c0990340e1030007410340c3c82c0d41d801c07617004003c900d48450620010300342101c3c00e42c000030107250030700c203a5503580c0c08992070741d100d0821100c0580c01a010084c40d85049141510354030038041d08104620688207445690b4020b1980203414030030920000350001d01e0990210300200001001c4400140c0c0d10310301c50300c00e44130032a444108108046c1c58014600b400d60b18000c21154080c11f079900036642d580b12 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 170862203 1250 170860953 170860961
    0x10e0309060d0207060609020307091502031e0d111603120c050906030403050d060909110427050c06030106170112020306060103050406090f05010c020c03070e0601080601020a0602120a0f021804 85
    0x817034007070f0f9036550041141c800c144061072203100036480302000141040003804c120400403881c0303c119801000f4030b21003115502000405a414a441c549c0c80b0070049442001900d20711440d044140320115141e18102d030005000c0c03840318041d40720300c01c040502c0c445400c143c4880b1005072011a0041000f10050300340003004503803050280c41d1142c01e06100e5502035007500e5941d8810700840343c13245041c0c0706100c6944101c010a81c1c0481d000c002489864100e1452240c44040302c00038060502072060230700c601446940301400c8020715103552503031900d00117400043c04507040040000c443c000441c00f22592460020b1181e0010010f1002d81d0f154070045020342801401103407096100c529807400985888080d2012030f101c3c1e0004101d000300701000925280c2000043c510030f51000d002008591400503205410001c21301e00201503503280c000503803030300c400c4500003802c0034400035060f1071f003003401940280074184c60034080c007030342d00002e8804003607000b8500004841da000702401001da01c1e150740 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 170863309 1106 170862203 170862217
    0xc090501080601170a06030b090303040c050603070503011a040518011e0e0c0a14130302010e0a180c0e030106060503041b0305060103060f02121503010e0309060d02 72
    0x928403490031240d883c1e00c0010074003017181450940c05c031402840d08600c00075060b007040001c0c3c0c0e81e00e0f0701c21078055641003a1810045890314100f82102e000d01f10683d5400c5c156401d0a40ca06580c61014140d5181239030f0810000038180c49149005400c1c1118644030790141d890002501100e40501640314882c111400d401d2260109000030a83c110031000813503a103506208a0503100386085c42e210200d0501c0100301c0b03190601070007660000343c074400e0341c8410100c040700050118801e84d6014240100000f02c07039100820805038821044c3c2c00aa1a0440c9001c141c800840c0c02c41e4480d4205800040c030000400c002d01c0564000035032031419016080a0b114659120f0382c0e01c44006010080c092500d80240401e600180d406031280000003c04012840c10030b215207505242100070a1806542481c000b00a01135000c422b882004c800640017078603024220380e40340020340c403800c = true := by decide +kernel

theorem cover : BRFrame.Cov 170683453 170863309 := by
  have h0 := BRFrame.cov_init 170683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 170683453 ≤ n) (h2 : n < 170863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
