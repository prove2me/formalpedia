-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5432
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:51:00.043077+00:00
-- url     : https://prove2.me/submissions/7e563433-645f-470a-99cf-41c7d098464c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 976798561 ≤ n < 976978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 976799811 1250 976798561 976798577
    0x2041e150f0e030f061605041a0c011803020309011b08070807030c050114010608071701090c231b0d080406050402040912080106030c140409050603031b03030421 71
    0x98880e0407403040c1000c0c14186010840c0c801c1e40420300d004414883d050850304581c060003400038240c4614100282c40340b400c24103040c100b02c05071903000c00407a9898a003110005580c6200f032400c0d04101c1a4162205c0f44108030784150030007035125070101c00030600140c8a5030602111211074181c2e500d80507084031b101400c10304141c3d1741c3d00156000d40015014408940d401c50001358090290124036564000345803d15450140301030b103130340c03070180049040c8803100240d10712520b02405070f581100d96090f00814070002e01002070b500c940d88510710341c1e0042580d643c0c030342100d100301004002000c484007031008407500c1a1031240e00da002004603140040d040d940480c022800c15004150001e00007400050801210f86e15440340703a69070707022000030410100042003e80d0700752158501c1e03806641004640c0381e800c0c2c6100c240501c981e000d02145142d81e03601064030b0f41c5082094a83c810a00b809014441d1800f082c4281d498000301c0302220107080070700f002c1d0300524200c0d0b001c2c00c10400c50f4135003040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 976801061 1250 976799811 976799849
    0x1020f0d0c0c020a0f090b040e0604170f12040510050c03070804060f09120305011a040302242701030c090b0901020f2d0609120f130902041e 62
    0x9030110740d4240d420400307184280005a034076400c0a800400780c10070402e10003442c1290308000d031018070710300512940c6059a40b80044e08081045a4810782c0408001c20031a01d01c41802c1c1c1c5d60040501e520142c1070086418044041d00001290149000b40e0450b0340360810b040998081d0b902c1280c0089114405001058110340690051900180b00300d00210350540a8201c103821100c0885064862807420036840f213031180c051141c41e0150a40c980742c1c000f050181d003540340c003a01c514400280141800f03106680e103880c0840c1480908092680d095980f0146182803d55800310f51038050512a03030b1a64080d01d540c02481200ca001e8040d4403104103552034840c00885640090803c1415401540380d203203084901400151a0400002d004540c65007820191034956102c003100c8031126403000d41032086200000505214841d013940546680e240404c80c1f4403c6802800300d05903031b114041e00c0208410146401400c2a43c04145000a850044107051026280e071446504501c1160700c103021 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 976802311 1250 976801061 976801087
    0xf07090c022104090c0c1b050a0501050a09032324010b0c0c04060b0d270803040515010b180d0c09020f040f0906080c0105030c09041a0303070c05010e010201020f 71
    0x305031040c580541401c060f07403400800c040e05c011040c010001410048a82c1c2040725035010300d140700c4141c3c40b15079001820700010509440860055a06110000c54150b03001845000d0a401550f4040102800e01c1c070804103840c04050030210300c6485020780b81c442e40b8440d082d10040c400e03098540b00c142025034601800c0c007a055203c0601407405010b07000f103c0c1d44903210b500494005012903044291b441c241c0d5039900e0f0072101c110415001043c00340c842100003080c02d0919038072841e0011001c80d41c0e0340b201d02c0e21030702c1e02400500303058443c00884000601da041d0107000c0d01040c11000946c80311b45c0419020414074111800f00200301e00e42200741402445402d50140000f00f0b001100c4d1490151901d81103021841d403540b1901505890b501e050004050601561007001c00a0a0030350440c02c015900090034010b81c2c1e00c0301d0080da601c1c080342d901c14418003150b5050303c1014064a50350b41040c100790401068501600d07020800baa045400b880d48140308481103004c071000e40c0c6083c80f80c408005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 976803561 1250 976802311 976802353
    0x1308030402040603081b07120309030209060301060f0806070f0e031c02030c0304080705041815110403080a030c030b0603010f060e03210301140604050607080c1e0f07090c02 76
    0x20380e0072a603500004400102217800800c2602112001046034a14515407603152224a800542a09100380030740b1000030f80040303810040d69070440b8916a165100e9022a00406070750b400005980d03d007031000641c1020200d511070140440d0755411100800300c0b07000742e5105c02d00c40c00098143c0d12428010170352000d82200c1d24001121841900d00d00710101415a15641164004220503004143c040050b8581445a05690480e94480c82e15104003a20342c1201d0205000c00c40300b0084d100c0d2010305001000d003048078061684800d681c0c1c0c440405000007401440c0c00f43d0520b01091800095010510b4200103590403100c10038940451541460400c072800c015560000c2c5c1c040c072030f03082403549103280788650840d07210034114500c1c0c4a61400c050001407000c1c114030b56000b0b000411090100b0340320002200c8845402c10b0301e09a44401d09130205141c8030b0701ca45580542d103034001840407081800300b81c1d08828400c40c2d04a51101c2e4540442d901151043c212606c0980d2120320068102103400301e170 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 976804811 1250 976803561 976803563
    0xe0a0e060603100509010b22080a02060a03060f030f060c02060420030a080309011514010509091512010b0102010c02032104140303040501020a09060513091d150103060c020613080304 80
    0x215003d00e55680c80031400c8410203030080d030211040498106030404007072070a03d403d0645140070022441c50004819118010b24402a0181200003641d1a60324081d400030001406c1e610a020300140c3c1ea800d101d00305506025007210454109a42d031100c1c28800a0311078096a000010f4051007080805080b02c0e00850000e07041e090300072020310720041880e010103948a0344480c0004a41c00c0f0000310b18405031039403500140c80e40e0451203804400c0381d03489800d0ba44030324407c0d24005070035155803160b0302203c200c0090075a84850215240f181405040d044421083d20a0f0001c0c800405170000c140d80328007030008481c1c580b159802049402c210350080c11500079016640c0300160a103001c80060460340200c03030036036480c0e400080703801e2420781c44071185004000919045003040d0031340c130880d02c240c9000c0c410480c07817035254030000c44d08070410041c161701d42001000302c407a21031a020f03c680240c0c100344001c1d9403036403600f500010034500116015110700b4042d00c0c0c4040d00c0103266202d141a40000d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 976806061 1250 976804811 976804831
    0x7090315021e0c0a020d1101080117030306040f0f0509151320010903050d08040209011401050304110609030a2d080a0f020c090f041103030408030d0f18030903030e0a0e060603 77
    0x110f05005a101c0c2c2004e0002c150180d007c6004442544d800034110041c180c0c400311480300c0c00b0310030045100010040e00d0704400201c0300441e92030f11001650004e08820015182c1032071800c410700180040000d005652414204841c0c0741e2503444001e008154054032402038080d900c2075500c1d805400c614400720400c000141061041c40f44c494840c1490803014141850114824609210551611a64407401002490414040e44842d84002849404007a100a01c40c281038a0440040d941c0c00b0306032010340b00003404031683d0032442d047c1450b595020701c400d40d640940840c80d440500d08085a10000c654000c8400b40c900142e9250484e845408549a80b003107010381510102c0301c0e0340b000c01041c0a88082034100784075050a0a0030303286040c0004d06284070340e0040004220083c8044291040140010400110101c9127401c2e0f0018143c1e0080c25041c06110b0b030911010150002980d20581c0c0c02540da59280c45140000e000b40c484c2d0901a001074080b903007000034900c0ca03016005641c080d243c60 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 976807311 1250 976806061 976806073
    0xc1905070503070b04140606040207080d0f1e0f05012102010531060305061813020120010204240801090f0f2f070c050609061207090315021e0c 63
    0x11329400609041590200e40318403581c0440324000320200010703500440c0445046280100d9a9a8a41d181c0319511031010306075110506085800195403202400102c0794540d201002c1b0401e2510008060813000003419500c0c203000804e03100601600000102266403540c6152075080d0015922600481040550721035001001c1a0804000b0b000404060b5054160503506003080b1000d4260b4000810071b5008a9440d1501600445560041c90700180d812101c2d00c2c9410aa0004844644691000c04100e110096034a01154015070090044480c5080742301d000d00c002c2403500c403002c5010b07404080042e1100c40140041c017002d034428405081c04040c0010071411040c403c100351140301c1c1a1120b50441e516200044d814400700d800c50070b400c0c0c2160f06290050f1070381d5451240409008840c000c580105800c1902d4550904941c0d44001e1803a003030341245881c0000501a8080340007c40e00c084002c090000d40400d00e00030b030360700842c0c40313600219104d41000c40008a42c220f0000c00320144640 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 976808561 1250 976807311 976807313
    0x90b0106030c1b02060915040918021c031e09050603090c1906050a2f0105010311040e06010932070e0612070c03020c100509121609090f02090702030c01050c190507050307 75
    0x10b80725144240762b014420728404100385c010403090a03500c2c0d4658103118100c20202002940c0000642254101307030000080d04800c40c0000c0714102641c0d000039030005000030900008480000304203014817002c80341800b10030710b52144503005003030328132441010400038009240039600030101000e55086a40610341d040a0081e540154120b4203aa60112650f40c3c40042c018006c50715006807025105850602a8039100c3c0c1c0e1003640d44170b0500c1040c569680e940c0b000c03600000c00b05c4102d00c07803400042c2d40c1c21a07101842d4140f64045803d0f11200c010520410001c2c2e5a400c0c480c0a07103449aa140d00d100c2017650f24014103448007100c03600101c085002d45602000700d036842d401c0da48003001b11030352096124800071080c04a28020065150602d60044401100020540d024203040e2013001c0c001207150b000c2d502e04810310000c02c1800a602444071401c002d51140e001000c2c1c45290182d800a04c110344030016003409510600103000c010142d0b0961041181d80280002c2103114403803411603103001c080d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 976809811 1250 976808561 976808579
    0x10020a020a0f080703081f0509090c060708031005041514031c111603020a06140c07030609230d2607090602210a080a090b0106030c1b0206091504 64
    0x2200b8200e403840000f09641050590106601d90b000300d0300910b00c00d1615411241e400010001d1141034401c9a510000690058003801108038808019007650745910040c503280b000c1d50400c80303090b44108101d80c8001280e10305030150742d50905644070641c41840c10100905550030a040c0306542521408540d000d92025410120070624070980da9811703040c0424032020300b820241482a60b48003140c084c184003583d14030400348110303403250904038500ba659201041c005d00525443e1840c0380a114400000c0c4002500126541449000b05860700d41d10360059484c0044500040c0b20203a1128004001e0309010b00b6401c100440c11094070044dc05d100707840c40c00318020032606000010f0075150b041000a40401001030040c005520b54943e806c0c03608210116402031110401c100704100c0c012a440c280c03240d10130720711507801c4503504d0640e60716080058060700c0b01c40401e500051000020302c5424600307141d4100c1555006084615081091007004002c0d109807943c9500d8110400001844540e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 976811061 1250 976809811 976809833
    0x60c0d020102041a040509010e06190e06010f0302030912090f031c020c030616200d0201060e01051e090c131401022b110c030a080301050f030f10020a020a 68
    0x4655800980c1c3c8505050705030200c0c0c210343e50840307078800050005003d9a564100f905041d2013a60340c00c0c0010f80e82c1c0c10005526107101410070300710344203076a101140a080c039411440c0303d010281c03561090315a5000702201284030848400c0d1554019422441c00342c0c0c1240000c02c010080140b030101d030b45868000107400c02e1030810000e4010901912080a810f4062003148026041100504203503d400048000340c181200241d86c200602ca00d000b41da042c5020040a01018400e01100c0d03071400d8982001e8002d03c80e078025402010f0b685400040c040c640301000c225149030300100d007074000704c0c5101805132050b0060094001ca81080c041c3d410301d0341030600440c001706400b00340040d001403000300180c2011000341107000142c0403005c0d000b160000790102c1408000385ca1605280c04040c090700366090030141c2940d9036050052340580b1003031205550145060301c4c2d0403643c0302100c000c0c03202019a648140300c000c00d0b0f580c0050340d505100103081c5e405408500c1241c0140c0710300c0104c42d0707161100c8003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 976812311 1250 976811061 976811083
    0x8090d0201031e0506090105040e03070b0c0d02030108060a0b030f0304050d080408030f040905090601030209180a05030301080c0103060b0a2a08030708090c010905090a1538040f0504050402060c 85
    0x10340c0c4c03402006404c0c13408182c110700401c03003644d00700f01d03490314070f00041e48a03c90310b0000740c050051800891481c8041004030382d80403020342011912540c4030044030f0b40742c0030141ca54190860800c0500c608614010070f02d4038100e000c1e4001103180c0b40c138250900203070351841c070003d8038021800d00c0000342c881d10900c01044603240403852360b40d031241004100d40455001400d9004070303501601c01400161244442c103501f00680c4a41c1880c0d801c40c3c0900700d80341090700c101c010440c1c0404400020346c07600004104071194000d803001c1c043c4949880c0c60b0071080c001d80315110f00090088a040c80303200d40c4010fa903011501c59100030002c2082c16140c0f40d00ca0b134400d40c1c0726400200d4080420189c80300510540700d412200b482d000a502d441c000000752404001f829032140341c0d0361070702c0600f160b0003041c0d896001080901104140b00b50b800908241c0100c111440c0c26070003601c0a422451301800e001282c0a42c2d12140d806490142008140002494020412070300002d040117507140207a42001010200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 976813561 1250 976812311 976812371
    0x503030c070303020d050f0d0209030307060e1b011835060601030f02132c040506062e0e0609040f050a0605040b0d02060901020a170408070b030408090d020103 70
    0x1d440e43c070303000b031070108100c1e0f94404004050000ca074600200308200c8100c100010030250303c40c202080000d095204520005003450301d88041e0404040c0c5c08100c58403101241001610001034803001541c04039072640c845400c1c8805ca1741b00780f084950a010184001c0039800840000f56120403901056414001d0700340100d0740008100300456a00d0300038080303800e021440642c2004160800c00c038420005000d80e010b0319001c02c85012400090744284014810078003046049411705017030064860074180c610500070010b01d540582081022403900d00e0b006011075030000b85070000300d4212a100c000d500c107564005400c00000b0720a686a0080842030b40700c00c400026503041050303403502120142e5100d07074012401c1000d2000f01d42c0c1c0d101005d1481d41e0301920708903940e03005000100d00302010000d00900c48250204d40e41d0001035001d0240c01611040e00c103d80e81541c640420f80c9050008a4005000307410401010440d82004006600d820b803042c1004200004900036240100788004210441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 976814811 1250 976813561 976813573
    0xc050310050108190f030f11330714070204060f082d0d0509060c03040b03100906050a060507032f06340e18041a0c03070e0a0503030c 59
    0x4440050064190a15980c200009042d070a17513540744414242000140601c0082c1e090000b96074050018014404402d001740c074003000d0010401510300100341d40c0c8589005d8092036004164020240c024050134581c2c0790600070020540580d4100d51050000300c4e04680c4480000881881d021411000381880d00080d04c084904184507a034046074195075010f040810764080e03082010045040d41d5903000d00e1400d1550740c2011340100b4031510542030312039070710712001600041e00001c00010718058180071440d40121a9940c8007503064030500d00686521101c4940c04001260103540101070803882401c02600320100b41d041030852408101c10340c0310b5034507075094164030608240002da510070b0488519042d00704840e400000c01c001c508445855140e10303140e59001c000e0081c00d4414481320014021414440c0d90301480000010640c0c0884a51006003108510140d000004a10604826113083d00319030b580384084a01805132400da542010403a0720109950b2010700051404105200003048 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 976816061 1250 976814811 976814819
    0x2030106030b130c09050f03070e0406020304330c11060403081b030f012c0403050d06060f08040219170a1209061b060b0402120f09030a02060406090c0503100501 71
    0x1c0700903070001030380f0941ca4046045041074001044e102500c005803090443c40c440310003c2440d28500341c01c0702c207850305e4540c100020080d07280c00451113030b4070504049a225001182d820110354900281131100321424400b0840442550310406401c4040e240507001e00d040035400504100050307605030001041da904100b10074440d01600243c800e5580c0c415441c1d860205807800103000c0c10302a00724bc441040c9206c0341414560944480030320003280840d002d606041c6000340c583c0d0300a01158040e0b41c00c1690001d100c0d4010103400003503081c1f076207640c0959a00d55082240c40400c0c3d40e1a21800d40848601240001c10b0000c2894a14000c800400324040203003410459013010b84124030800000c1c2509005187d444910340c00200d2000c40780300a0550b441c03074280b0181640b2440030750000d00c003189807810340c11410350503801190041e8100006440d1031004549074803803800080c01680c40756000c2400240d80341d0002d0b5405008007507182065482d00000380c10809201c0e01d0b00202c0d42c840300140 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 976817311 1250 976816061 976816069
    0x207080f0712021207020f090402030f0304080d181202041d0703031706030f032d0f07060e070b09060c2506090e07080403050d090503040b071707020a0b03090109050102030106030b 79
    0x15103814801c64004d41010186c4c0c2c0041c50b1160035202480c00340d40c50002007000c54404001102007440d401060300d440f03544894540b030b0754054180d010342c0055a440c011295500e18050010143c1e12400b58030f0044140540134070000d0000d5048004081c1981074900c081a0010301c40e640107140700e6600d01c800910214981446000b014040ca4401d4006080c21400928000120754002146030f840ca100004090814503051015988550b81030b00001a0890140000300041843c1c5105030f6080140781c042c3d40c08555194028024014142c90030000505c9074940b86010300310107110744049555101e00c08411120000d0f41810000d01c140803a01c0601c00b40b40c1080007440a032080640546007440c1010006054500191026083c044006071004017040e003a045034a40a4000c012207580c1c40e91618020642d61041c2d20580f0060482e03440600d00c403842c04201c03416180c004107107221f040e050011890799544040c10480d2300c0d6580748141e1000480a0004e94000c0105403000103404942d10180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 976818561 1250 976817311 976817323
    0x1e0e03070c0f0b09100905041404051e030a2d05040807080c060a0c050a050a1211030c0312070c060501090209090c0a090927080301210c090207080f071202 68
    0x2d6024000030070750030b00c1411940c0c2c0a0711040034080355080203130b45c102d0a040da8600001d41206030414101040020994802100341d80100e109408442e00c0004030085000452842e0701da40e4100d0700100b190040c0c2e648141c44011602c02e10700e038550310007990044d855404214441c040c101150011130304200c84031040c49240000e00c1000c0151030f04841c203100048440c400c9101e5902440595a000c000b40b2070308210036105a6480300881d00d0030602c6007000311241c18400b0710030300016490b0034107521f0f003400802941d031598204c000440c282184840515a1010024034074000c200c440c00050300861141d006060081046500050380c3e030182c00c05100c2e01020007002c5040e54641041900021640f21040d801260314020300098421140001014011300455110524450744481c202c11300c490500154101c0d0103052540c20100403036410303409440189076011b0b00c09800320710f00b0000c1c1d01d0190004d200d40c0340314141041c038020528191002c035801440d410341d69074110034400300c83c0d0f035010040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 976819811 1250 976818561 976818569
    0x8180f0303192a03021e0307020606040606020111030420030d0e040c0c031b1401140a0c020c0303030118060b04030305090f09240301090803160e04050106121e0e03070c 74
    0x1d0743e2880e00801c1c10300c050300480e40814000b0142c1c0041d40c10341049a01541401c4003140101da0399481c20040002550307240113841c07440c442e625160700042d0003401403184a41504d0000b00c041c1c156940c0e501e82141c40250140580d411260790501004035075014010004e0303194684d2204401c10703d004003400110745401291605008205440070046038010301582a02d500d003080984800c03500d4504911001d1002c1c0386010250b0030705500489181e192410701d4030401406c0010007100240d41d50881c2d50350ba5405510703825800c200010300c0300c150907880b4080b29040030b807030101d200b90341c460311040260f000e0f1b841600060b00c00300d00c0605030b240c0700646207400101202d0000c8581001d0a0005417004031002c03480e00381e000c00504240c244c900303420071305480d5048100a0b0701d0346480c8055201d070760b411074850344c0000c410280c60101441d0910526059404c1c42e40d1307000ea01e8008041e0b901c024202c10340301c800e07503411107142502a04d003603000701c1c0000600079014541328805c515207907030300c0300a03500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 976821061 1250 976819811 976819841
    0x10090c09050f012103020f031605100204030209070c05011e0204090f05010b0f0702010e0904060204030512030f0f0c070f031e091202090619030317070c020108180f030319 75
    0x401c0030701584803420b035200c0c54038005464200c1661409a2502d800e1005804050101142c02c4003009e8904284080c00c038000c00940f44200f108440520480c455070200942c499a0203000c9414103209501c03030104184980000902d800310500001400d10708807403902c22890700040c090140359a11300680406003078030801441603504007605541d0b5400351000495040300081610415a8810010642c5251010700041494141414020082d40c0180401c0c1d44503c1403c80a031070401e031134804c9a110345401c0c10400f903c1e4503070001c020300402001d8000405d10b0030a00001c1f021602d21a8120009031094071022040d550f03e51f0070003400100e0a4500c8180401c1e94405c010001c4810001c421280d41240c4614a0b50354204c0002d5198600303500d43c0d025000c40441c00b004060704410401414400303400e0155569950000882e21030302c4011009002805400118185041d5406801d400703040150507900c000c4e40c40c04000c0d1443d08201d8202d4801c000c5c02c804c41c0c2c5840f24a106906140d40c0f4a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 976822311 1250 976821061 976821091
    0xb1b0c0a051b010e280905010b0a1710050d03170f091207211b120806041b08040203011b031a190e1506040311011716080910090c0905 59
    0x40090050b0504510070310169483d0708611429805c0c0031180c2000e800210801c0045585074514007015402010320b041c081101e00440c1d0442d03802c04030b1018481d10700d0130042c18001e070820f4140420700c1c0101404500340715051000c1482c80281001c2d40d4441e400c1c40c01402014035199046500c2c046a00641e100f41080401524001c0344410b40d0400850807800d4800784144040102165403800050384c210241c204154071108004002c07002c400e40100640d1075041648814080104440509a07020540900c80345c2c60188240118811079002d4001800002c60940545282e0082c04a0b80a81c2c40003035900d0102c070b807003550021070341001d0003001d9800703000720303420304900380520b14550048214010500001540c4502078901b1054806030180c40c56480301c0d80c81c82e00001c2e00015042840c081000c402c0c440d044810031481d030074451441e40d20f4101c038040d880f68041c0c0c0c601c42c016000c2c2d10a4015080500325034407440c018504500e00c41d030301594515143c1f0581b9030868002030060041c4d413200c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 976823561 1250 976822311 976822337
    0xc041107110f0d14070905060a1e09050114010206091605190302030a060b01020c0103150b0901030605040203040c08100608060c0f121014030a0b1b0c0a051b01 70
    0x2810940c0e06055100101480440c00e041c005403103000c0b61110030340d00284145007041040300307810300d800015800c003040341c80c82c07611218a07400b13403801101d141e50012100c000030082e103000a0002c140703220702c912403001e40c0c0e502c5846440c1030f62000d81100034050007113620f10589590400c4019400140c880207040c803551600c6010702c0c5807800d0301c5014420380b0424030502c40207504105100096900030115075000303003945064006171844609241c054014840b0102c0107500070b004160f080d000d40100c000125050001d1000c1070b81148584504241c0d803076402040d5910f841c4011030045000c2c8403034002d058a889041d07445e2418520201e0b00312428004c0c10000c0c1c540002c0c02a400401c0c175a00c0586403c106103c0d00d0381c80c0241010002c2c134016000600c42e034404881001701c10b803005070380719a082000710030600d0b03502c21313140300014040803050f0009014501490410b01b520f40b00300c41201d18041e4042c52652400071030680941d5642c01c4a00300502c00e03c0162540b60101c182070800310080140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 976824811 1250 976823561 976823591
    0x3201902061302040e070b0a03060303030c020f1e0a0c1409061801140103091208010314070f0e07020c03160e0a09081204060b0409050a0b0702030903030d02090328050c04 75
    0xc40b0002c4c012074584032080302d2440c0602440002d482c40204072074480c0c1c03c0100c010082e01451000740c3c042481c0540c440240c91000c650f040340b80b10074500400d040580a1501b402085189500c8191802000c500c0000110f0703031103110008000d06400700c80d42c40d900e2030402c01071600c050304c2d070b900c51903c4d50004081c0404101180e811582e21030055103a02c0d034000c0060707000d40068640280180c40c08441080d4494104081d98180c0e805010300c0c883c0760103104e000c69906c601a0240ea611400b1041301004040545405581d00080c60302c19240d40144003030100c0e246c40c0c0005a140b030500c012500074082c620107003a000e5405526000248148072994075010600c1c410340090709a041d000c40c0004080c443c2d0f0350440000180090020486282c0b1424000e85690600710100ca12040100109203254400001d030740401d5802400b44d0700c0c1c600030200480c001d602100003581c01d070040b43c07407868240401481c400c06c030440041300d403414440603151050a20303001d1440346101d5441c0003491401058 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 976826061 1250 976824811 976824841
    0x360a2108090d0c0606030f2010051e041a180301061401030903030e060702010236010c0f150204060e030f190f05190209011a0a0305070320190206 64
    0x10150801043d0416142462006010160800381c65540300e000282d00300078021132401349004240c419044000071308030800c0f044020400681c00003030b1090102c80381800c803150021b00016140c40200d486c01c1e40d644c200c420480903150150314200c60104e000c140107255002d201c0c0c0d0440d0210002c0000c035041c0340640c5443c280d508080c0b810941c0c3c400148040602a0740070268018643c1d0881d292481c4c040f800038080e522580000103402c0a00e4640d0300301413000c54049280c0303e024403d2001e03132102007004440c034200c910300a0f0341048a00b54800b02103a5a6003c0c0d0803042545040580c1d940d0400001505044450450900030b50001c200c8014454003c20f0b6641c08140c00811400c0548690510513040e11030f802003c2c0c02030103140c6582c15004040131010a00728420340d02845541e0780c1da801e250f11035030030380d5540c070005408001e5a0b000600c00d9005652001071400c1c005040d41c80c108150101c6180c124103481d05200010b4040b1403d180040e860039003040a100400003442c040d5041d80ba414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 976827311 1250 976826061 976826083
    0x702011e0f030f09050f0319030b0609040b130f0621150b0d080d050105180c0a08060a17060f0c0405010507080d0608030a05030a14360a210809 63
    0x590340b0703d1101e08071805a00841c035400d4100084401e80400300310015141d501004441c1c2086598000c4040c010f4005d01400108240c020100c40c20900c1e0032702880050607a1030b032316943c0503051113050091441c43d88a00f00344590010360025607a401c203035404030b07440341c40030740c0a03810321600c2032440c00100340340030241e0b005401d5900410151030840c003041c980d03c4540700080c5121004903480b02800310550010781200c1c0219a4100311803d0045031020300001078540d2140ca100070000041c1441c01801082d40000001d803100803030907640c2c0e21302000b41004003e0800c807504060706004a440aa0013900e4100500300d100902c2e152400001030140d1260003130043c203440000c55004100d100c1640400010094501500d507124000c0030000c2c05a0300465011a07507c2c0b50040c07a50142c600d1208140c440d8000c05c2c0c1040c141c0661081407520380141c035501d081c1500103414000005841404142e40040c41090410130032080d01c0d070b466000d09082c000540820850344104000d4220000c1e80c20911 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 976828561 1250 976827311 976827317
    0x120204050f063703030305060f040c0212030601050d090308041a0702070302150d0507080106030e0307200a0305030a020d09051009231005041d060f041812050702011e0f 74
    0x16407216022500c0d200f0712603108003088589184004203040c1c03d03400881c810b140490b01500341511315400c200480d07441807203517001640010038075410042c4000056800c24414140b542c10180b0820035503066650010b402c0f0000b070036103002d2004004455040203504030034002501d65600c1c198500940d505007070700c800b81c40744000d4005201e0031722076031085078035102100900b8001850b0180002c1c200400078407610000901d801590f007100000801507079039043e03001e00109081003100c01010500f0202440f0580d00c00d01c82c40e00080002c504000070706030008542c0240c42c881240385000f07007078000143e00440c001d81c045918400601e600210072020b44110302d81e09c80b06103070841d0588404400f21041940c008840c1c6060656068003d400b030401c0350034850b041c15031034081810721414044180c0360f142e0002d5040c1240e02e1185480c4d040300610510684c40c810a85001d510741050750402441c00c1d001140b400904081075580c01420b00d000d91007008003500021394000c20007410350b64100c03440010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 976829811 1250 976828561 976828609
    0x20c010f090b0c0a1701120c0602030f0306040218130606120203041509051c0903170909071d060f0712051c05041109070906181214030f04120204050f06 67
    0x41e80c0d0180302d0094217480c1600000c0415a1210110b4108040401095690000b05000000d0342ea100008646000c1c030040360584c15601c1d1801848081e4000070420280380a94881c482072944921492400710f02800c031012665a2030210b0140050360228403010743c1900400411000c10034940360500c2b4640c08034400208200a03041c80e50070056a402e00d0203080e03101c071403842c1159510040030401e490140041d4280f1015950094480340310360701746990070003451030002c0c9803c0e01410407510381892441035a0a43c1685a0001d042544031014441e501742d00842c0190500190b8284084802c10342c0c00d001e803400310340140030348005801d1240300e021280c80707400050401c0300780a82c55800c1040540941080d00385040d000c1e00d01c4015000d82d000141700928039500c1b411100f4a040c0845001d6000c92500000da9181d080c001403d42859052500c41004909205000540208020180c00711500075450301841084207960010340068030807503812040c0601d42d9903015039400c11070340c41074440e40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 976831061 1250 976829811 976829827
    0x420210619022b0b0a03080307020c0103020a020c2110090c0801110409020723061e010f12170301030c080d0201270c080d03020c010e0703050304151110020c010f090b0c 74
    0x80500301d010b5244d600841440d40010030041705002442c05840316070283c3c1c40d0b9005d00d8004400324025501c6100060340014001c801e642011242c291104900d581124008030511042c1032404050203004151907540c0c1c00740005000001a040000e4040940244030000c800740a00b0340c42e000d075006100300203a0004000c030401c20303250f800710007488840907024640817400300c040352500d5045582c0c924030082800044040d6030704140c1c1506866140d0256101241421a030f0a43d00d0725415040300d80181580d42c2191044565022311300071803280e04086003490030010400d040003d10703150181560704100c1902d42c0780b0003180300f120320310101981c0d03640b610300c403400c0940c01510240e0000c1907034091321096204282d4560000d00a40390400000e02040111810302c907076030401e42c030024025820034041448102000c04038900940381c20300d0b214002032440507010703041504000182402035400284400d0100080c050000c458141403001c00c0903009a45a0b40c08a1a0041c441d00c080980004c40724 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 976832311 1250 976831061 976831147
    0x50307110106050901060c020f0909100c02030c01060f170d020c011215180c09080604111504060504140613030303050a0f09080a17042021061902 64
    0xe002000300a0003600135594642c1c0c082e01d0400800b0043c2c0c028407a07507840d1601070810400c0c00703001c3d007003c0d001000c2c60030792150600c00811a801c0060b045000810440f0307e503000034000c102c080c2c40c0140700c140c0c00501d4032000b40c0103110b000c2c40c02080c84d00544c10f1864019004542080480f0003030070300c2104281030700b103010020030180a0410742c0514100011a0041c41d81c1c48498000c1c4000c601003080e110342581c140c6102c200741c03103890580e0388210006000220305050f40420b6210182c00340c03c1e030b0b031000030130241e041d041500302038000b801c003240400c00710a03200c0c11042c0d40a01a1030442c070740034000d03c036603244e80c0702e80c0009428182c41d100410314001d0b165000308540c40100c10301b005850b00c0c07841d0200c900c0e40146003107400136060a84280030881c051400300d0050350300c28202e0b10041b2085603080e011040d41ca100541c000ca03d1301c680707184051404071040b08001ea04000e0b040746d20f0120044a03244d11700d11000b0000074414009100482d103000000182c0c11264000036880709c00c01c801c16 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 976833561 1250 976832311 976832321
    0x1e0a1107033816170a050103050c0f2b0b011502060105150a0309030e06070503180105040e1614030c07050d050c0717030910020703030e0418080d0f0c18090c0503071101 74
    0x55030500340c3c4008001817041258070450503244940152094281c0000c01c020302d40c01c10118280d0b001c500c01e01e07507200944032409600030941d84060480b00c070288503201c3c0c1520f80c000341d216804400096031641840342d0705019403405428201c0f90b440384030784c000062a0b124060f00e46140c092641d60581c40c0b045c58050400710511141c0203181a0f615081480c02039241d401122a0640502c0d041080854960190701598150303601c036681c2d01c2003541c0e184158502241008070903000c0c46103d240c4503050440541c001c6200e245d00d0380080740c0e62101460410301d80003100004c0300030017005001c81c910104011405c6000c642e82c03084410300d88504a43c0581c20752013a000c001e17620010222180c1410384d00452224200c90094039651050000c0000b8041074907080400684035082c0300500078000790070000541081409044000344003811450000308071003070100c80c08041015181404002d6000c803400d24040c0841900c240300500540102070152700001d40310500340b15602130b5480000c42d0075808 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 976834811 1250 976833561 976833587
    0xf0e0601020f060720010c02121305040501090515031c030b0102011506090f24050a05070c030b0901062c061c11151e0a1107033816 58
    0x269800382c101054041e00c00c40d46029691824496030640301c0d505c0d0340600c107150108186802910100003030004142c0294030070502d4840800d004030001c100e68a403031103118060055680b0008160030880c140c81e0144800b28041c0d072082e0710810148903440116a0304001030602c0e810003040d221138180060340503040325a1664491191080001070055110809000f21801001000c03252501ca44507401d000c64100305980d90702e00400311003884c8921680040400e080b05141050411060fa52500703208101584180c401c00c42503028044000c10070303c03800e002001c071600c1c1d212501172203400c220084c01c1c0700c0c4194071007003007410002603540e154140c5180181819001030030540407585846810b9800b601801c0d4060505580e17083c0a18003180226105540c1d0300711032695162120049104c1980f003020103d0401066070346508084030b0400c001000f452180520034200c04006a84039100c500b100540d1042c05040c1c0c0d0041c0d80e038020100f1043c4c1040e000210703035881021280e4155120038180b50 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 976836061 1250 976834811 976834813
    0x4020f0103150b07050c0f0117040f080f030702010c020d05090d1e080a05030403020c01111e011d060a050f1014010c1a0601020624060705101b09050a0f0e0601020f 72
    0x2082010001c006c030f081c2640180c225004540030308584011160404048452448120010045030101d050000a94041071040041900d000140840781c0e903d03400549140c000b50713440b00003102d030340c075010300136a040c0c1d50a500d450780c140b041110020340010710a04016000a0300f032010006504084248544d25a0300186d03c240d030b9510540005000d603000311401e0700140100390b8010010741c803983c82c095016820600522880c071420f440101c00070a400400344007590b81312500e5654441d450701e00e41142041002601d56071420720919411713540b00130703c915061810f40c010054000100c06003407003070302c48600b0100510000800140c0307009071103a0000d807507100c44d40491100f580031101e02e0b5128040aa090360352907141d0001c404180107a983d5841040111402d000595007000c0e006424480d01036822516000c2c2c0f1940c800d400c546640c500c0b4400c40307220050010304242c011548400070700d010381c1e010709081d01d0180c130041d59483c140100403203010341e240400d085038400c102c0300c640380c00448 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 976837311 1250 976836061 976836067
    0x2f120d0f0509150d06051c050f0601050d12110d0f1403071e0207030f0c0612050c090d05030702041a12070e2212090611030c0a0b040804030605090c150304020f0103150b 74
    0x47ca46c04078100b0b1041046425110b0150031058080000c0707800c504070303407014040325101c111070b81d61044070200c0c804080d030800a00c00205c480022041200004402c2d9a4a80c8800801c418030000c3c8080b80d0102e5246140c0c9082051000c0d00d41d1007004030070b2451542c0d0f1030000212204030124100714180d4800341131098000d15403020b001c0f290382c08100b11a07030343e1203050030100d00c0740c1102c05850b0b0448043c231804606002007409820004400c1e40f6031441130b001d0f20701e400203a0340042e0848041d44040c2c80106003000510b84d0509100030413625500c88580241300305032400c0828019803200402e01000074060900754000074a800c9800c1c005a60307c80d50002101040c400b00500d410230601c102c2001503811043d00c50841008002c44109000303140c0a13051040f6641c50780d0b01c2c0e0240161040328011002c00c40080031504d54841d09002d08041c10241401040000411404905401c408890014100f05200044e03440d0000000c5502c020700300441c420030410980404c092040e40040c81e1b0200c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 976838561 1250 976837311 976837339
    0x910210519150f1d130b04140f0a080406110a12051e0d050a151202062a0a050d110d0e0f130222032f120d0f0509150d0605 54
    0x10304c10340365000c402d0400c075130741c0e10100b0001265180580191070058481c0100d00410088240c0b0194034100c10304a0308804800e109807440c150001c40145c070306040210341406a01e900c4050041c50030003541c000d007461002c0703440c0c480f4162103002e2808103200000481c10030074900b103c0861041005000c01c242c95900b080036850140c4800c5584003000740c5000c4e40946a5564144543d06858460311020010a415428800560700c5540c034a1100c0d070410168030341031b98290480007020100e0340c016210308102071500c2840d044581d44050140001c40e080c4010f01070f4002120540ea00740c610b00a03d0400401001c0f40d04040c4420b5555001f144a5001d0642d094032500100200110f140d80c0b410702801c0640400b80c00c50171400000d0413124038003c2c5010108600c0b2a501c90f188480c84607002c5d0f001e101001071480700f01c0340d5842040350002d00054060301d401104a40208045050040c58a210000061110341c00c0300f0710001c000d8000308d004150401168032540190801a1007808a000c031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 976839811 1250 976838561 976838579
    0xd030c0e100206041407080c01080a060306050c040f09020f0a0e12030c010621030c0201080a0f0204030f030e0a03030e150c030c03030105030d0c050703030c080910210519150f 77
    0x401c1340c06581d609607a0014000505d00028500111039240018107204440c10004584000019005004181d250341e00170020554030700c1781e50301444c07141c550306595501d003801d0b2200d003903500d42c06096030300c2c070602040000c900c40310100d445000303983c0750441c400001d650010b00030086152102c0c0b581d2001041d05804403a0552020f42600c0300441181882110940b018400b000310110080014214210313400065015215660f042884e00780701140e8003210f5080c0c602243c009a0094500e45031054400040c160482c4442c402760006941c5100341c40e0840d1400340111801c848154001c6040c009412031083ca11400d4900c0542000300362907840c07600e240000e98941080c016144207004a14030085443d0003000340e0840c2540c083d004d03024461030754500743d0b0f0441c14003806407104041004000069a1407411004005240b515486900c00100c10b1200600e02002140010103181c80240040007900d01c0e0b91913451410600f0100c0c9070102144d1502ca5800709501200759400e81c08404918812 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 976841061 1250 976839811 976839823
    0x140705030105120c100f1b030e040506090402240d050f040c060c031e030902060309160503012a030603050625050301060c060c0306052710080d030c0e1002 68
    0x181c1160302c1c0540d425003e054940343da03a80c07089958820031103084040f03410f0190840c1d80d007040080c24008a8460300c0e02c4103204020142d4001c034006005a40011045d03c2d003841403030340001059480310881d192171380c0415060041a07400b0000d402c2128100090095198126844c046c03000400f480342c1d0500b030003556140041610121250401e9840c04208c0c60f104881281500d81c0540d541c09000a03c80e2010080941080c045010146c840451101580f51000103500805420000348a000340200d1080f03001c403030b65000704d88a641092079800c45d06101200c541d1307450400d0f524012500080c000d040d002041151310007800f45c081c4504200d00c0700c034100e1840c41500c1c1e54910300302a1201d41c0c00e003201d103803109000c1c2c071001c540364900507000b00c3c505901c113001d1540d150800103030030b80d2140e00040002300010030001503004005d40c00a102000c1c08283c54000305c0340102800403900345449182c03907024200c00c0c2c0301013558407022294000d101e00e010003c4400c01174621074909511090081d1140307 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 976842311 1250 976841061 976841069
    0x30105090a09020d0f1b080c01030507020304060e060310080610060206091c0831050f15181005011706090705090a020c070b0307050c0d030203010609090902041407050301 75
    0x3403110005503280215001d41030042d503000f426204600c400360b54109641d03030705007002c0d907186071255440a0385000c000201e070064102e01004208007240c850004013a148010544401c540051004000254000ca142004e0b84421503219407243c0c0c400007414004103903075001d440503100d18024040300710150001d120641d03509a00f940d403641d0b01d04856940d9611280c0c024800e504100c540701c01c2642c45a080340b078009134041d0b21107006d00305041601e0840300c1e0461803036450741408503409040000400c03400e5111540344029280541e8801265084d02d00020101c1e0100c050a0742c50300c1a140c2c09004420040e191004100110758440c580b6102004043d480450148030f00030109043d1100000c1d4030301140c40040c00c2541e10790316010742e01c3c0690401c40810403580f01d251130104440c0d66850145200360102c2d50b4158079042081022854901c100300d4000a04d0710401c018485190320082c41d40c207460400d0800309102c02d00b48041001011046411080003906005000e14030380d009005604803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 976843561 1250 976842311 976842319
    0x218071403060d110d05010504030e0a0905010b0d0203070219121106060a09020a1b0b0a060e1005060a260109061401051914070f0c0b04080a060f11040b030105 70
    0x54054584003803444281c403056403000080700e010000407a80042c03203401c8200507061160f400703081c3d1b482d9400c0d00c0d01614220081001e02800d00803505000c0d094000419040109100a51610101c404140b1512985030512500080090420b83c0204020820b1002c0740548001000702070a04101a40740c001d841c01c0081c00111040c40001000112280105070060003560003d241620400003540803003060414080345003a12002c407201c001ca4520366a0240c83d02c0d9200e071905000500844503035802c0110200c2070320080c0400300703d103200c0c100140c2c1d4060304d00c9076030354101e03480c190358400f5041c00c455081141040c00c030358403650f01c0750500d04a401d02c0307009110a68654000744240380e0020b10040c000b54085c0038200301559407040d41c0c01e921000d404c1c280880e01e0150b52451055000c44400d5810384003900b429020489080c5444c3c006140702c121003801c09040103a4241c5849002401524a544902007603202d214164420615136028984056030703141d4980d181c40490b0001d00c281846 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 976844811 1250 976843561 976843577
    0x20411190e1507050d0804020a0b0c060a0c03050103050a080310091a030708030c0c0d0f080f191d0111011b0e13020a0c120201020c10020403060e0c0105040b16021807 73
    0x81030150000783e8000e00e80c00400b8110a244441c82181e00507801081641c1c4070b6402000025805401c40041c807958014074050000303460129603010a890041f21079100b018a008010030200d000481ea44204640c042103079548c07900e5049000320b40071a50f40101002600c1d044410014418042121500f82c805400b1394944a985103d001e80f2402079110f0320045800180c4505854507010f0344094005214400d11100c1a060b51581000343d0050402d001c103aa4001070004100d0f9180c60410414080e0303460310998076100740c0c20010b558480021400e05014021116140c40c0a00f90006d00801d4110940c6404001c038400c0010318690300e00089a014000762060802030039041d000b112081001d07a2645a80e0b40c54070fa442c0b40810700c8014400c400c5560a00c10545140020b02c03001e10340c0400c4150160b00c072811410700c80b04681300c03811150900e52062044000a981003c1907030b0480d1841240c55485040c1d81c2c01808060800d000c0003948850708270030800300800f44940e50340c001c40300c90f41c174444 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 976846061 1250 976844811 976844839
    0x40317090d230115031a07120908070501050901060e0c09062a01140703060b1602010e0a1d061e010822140a03141804050714070f1e080304020411190e 66
    0x50b44401e0f01c0990014900311a208c81e99241d40d0031a07441540b190700c080f89000269250b0a0846009a603c80b0300c50b51245401c2040350404441b10b40c00410601d0518503001d030000000d0303550312407581c58003002210300e0048030041c000f0005040c540b0329120004e0110f110074291032507407450304580c0040424600000403c00807000003d86880014550918000d40c01c1500192a1424241c2a0a901c292901004520a201401c4d0010004c840306004480c9040c014208940000d40c481d40e4032001c050180c81c00a1030303034007403d0150440e9014a0802c4601c0384a03080010250b0400e00281010090150300300034401c001908116145c006e030f5602241c0c0440303544841c0d152103400d0340074010704840c0d20465043c0c038082d0711240e003001c500d05181034410559440b0745600d07040800d0544940502d030144805000c6080d03003044071980d18409034031001a040d581d5074240c1c00301500107809181d40c0e18010441c03e12000c111160f0040d81c4104118012081c080204811030380703540d046c0034100a0035101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 976847311 1250 976846061 976846103
    0xd06092a030f020f03031306020f0c040e0a0b091c120b011e11011b03090506010f051311040b19020106080309010807050a02071a040317090d23011503 66
    0xc00780da034030803103541c11003046030204110b24440e6400c040d4507001c200310b040040c0540c40f000b04010300840d00a0452030b551050400e0401600714040c41c0103604140000000c4040403c1d91031b4a103622920061031078482c10345140c80d24400124085031085111007925034507403c401c5c03220001d41000c405101102c16030004548184064508020a0410399013071140c0900420035801048080400043ea1010b41d03440c0880710072080d0b41000c0420717994052030060110030b010607030250504c40181400c0328a80000305101740c055000c0d02c10003a980707004101881102000301d400400941445a455150180841707000144141514001d50301c3c1250000d6018000700a07101c0090058561040ba0f41d2110307010f0710140d010201917011800b41e4800820340416007200c0d818000910440a51110304501d80000714007891654940c10320000d0014400a940b140d00b100c0749283c1c848000507809090104e03a64000130540e140306415424203000710798a200b01240c80701113034003400424180da22441807203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 976848561 1250 976847311 976847393
    0x318030a050303131505040308040501050a05150f030a060507051308120a08250f18030f110114122e15020a0501060803031602030c030a08060d0609 65
    0x307200341c006100142100b440c1d00000742c030346800364034140d00014080c0c200908544040380c048003c42c00b84400c2c041405024401d05a100511010800c80c909040401400741d1010601e014032400c0e840c038050000d0b0b201801000311483d4019404e20540c10f204801a1042e000030303110b0328107880c000c0400510070700c0c0012840811264000702030f1400340746110444404800410390308000803100d441402800c164009081000c0035a69007507280d820500000701110000380c0015203c6101ca071303041c808503c403079040d60300c00c1c0d03030216109074940090001603421200322540040110408200b40b1507034560300202074840c0d00c113092203454900e24004036160122948901c40c46c118000342080c1f00d40e0403007458140382c0851600485800c01c072183c2e90242903802642003d150b6410220074400030001568882d0505641070000c0c504025090003415501e010300d11031501000a80c0011451503200d10450343e480c3d60304000701340112409410407005d55510441018010300306210280404c41441041d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 976849811 1250 976848561 976848563
    0x50918062509140105030a0b0d050d031817030a1103011d0112082b150503010617030712210504030e01050316030e1903020601060908070e180a0b090318030a 69
    0x28401c0d840d0b150743c0111540d801c010b20002c211b0360f81d01032020082e42c44541642200d40f045000345955a09160010181d41010b0f040c941d81d04104030039200040d44280242168141c8143d80360703101e9a031900604017a0040610300e03d00b101c0c0002c0003043d40c0503039030b80c442520142d5000b0342d4007590347d49110041030700e08810081c1c240342040c0f00c20710a0700300f64000d00382d801b0402c174a080306184000d45410110707005003030001a48580c1407402c00c014182030007000003c1501203009505080030f048a542c8030710a2540080c810101c40d03100403022401110300076103406001e511400b80d01c01c6129000f0003481c0a94017900403505410f1080825131007030301100c1c492551003a0107021005a00000c0e409003540700c06e48841400743c4034562005c00a01d042040300140698010030003945030440c003402c85443e03504900515004944180100c81454801c030350010444500e4a981003600b041260800460103401007401c0c90240038420460f6002001c1e102040e030030075000b141c00d4a21010075607034048441d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 976851061 1250 976849811 976849829
    0x408070b1e011d061905042309060f060d050a1e150b0a23120d2007061409030a0303020903010e1906110408240f060307050918062509 59
    0x4005240d504107500d2425040a804201c1c09001e506c031000903060b03500120b1126100d043c0d4000401c5e0220300008150382040e41b00c40030f803d09061140044100c0320340100001d00450145006070304100003007092415454010440e003680c141c05045800c0d035a46820002e88940e01001d90360b00d0410f4043c03142980c0c5410013004a12180d00e041c500c9400c104545501000ea515000c0d648a41c6440741818000d00c0001349024080442e03004a0140081c10166911000c1e40301c1c1a5409621060024005040c2c5080d810141c090590340c160200c0d040c86030110480c1c040c0200c401001c10035425070060714924504030000e01201000f5030105a41d0300c040740701c0340c2c1c00c10142041c80c80031814a5020b07942c0449d20b841d941d490691107102c1149880c1303e00d0328140314480c4e03544806107180061180d06821040030015641315060000000b50389a0704e5024481c0704001d4a4042041c0080080605007160700401c2590030030700d0005070305604917000750390301c90303241c54019045024980b043c2d04040603101c100e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 976852311 1250 976851061 976851119
    0x60905030a09050102011815060807120b10141306090c0314063304030c080709110c0309130f1802030c060f0301090c09030206030901021314180408070b1e01 69
    0x103150b1112410440800808c255903d9002142252044c41181c01500c4000b28400007800d6902d400c88002000030711002c1550201e4805004108801c1c1000300115400c0f1040c5110000c10403540c0003d100540c0003050b540e261000e80404030b90143c02420705070074a4002030b03450340d5501c01070055071004e030304100c4109103400044591900e000005440499132529031213052548a0b030754990424880c0d007150381641d0001208102d07051441c0103004207103000304000e030300b042c03c6901c3c916920701460400b680302e044044451102014030b40d01203240da00a812040c015100401400d039000306110005074041c1c05400c00a020701c0c1055070442d03010b10034498296181d6031820301528001c0400c501c902007006034100001000d80d03200c0c0051750080781d000c0001030362100c0c51601e04604580c1a8817965401360401c8401c912695006c05c42104104100100c2009994910308207001d4401c0c50801840038080d0b03001c3c404143e0704083c041440d0340892645603442d036251010300031411030660b0380346203400100c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 976853561 1250 976852311 976852313
    0xe15040f120224090a0209040b15150901051c06091a090907030b180a08121b030601140412050c12010e070522060b0306030c04090f030e0a03060905030a090501020118 73
    0x9002c036690310208000c00d480b80705c0483c1d8005a84c06e102900e05441702c0700048244a42544800d0f0a182d4004089802800e1126410103040301070140c0409241403140c041201904200c640b03044541d00032180c0f60410101340c5035800640244544040f800c020340800c4104c1130f190401000150041d6080c000400200f071641d0f5a034410311b0002828100c0141800c0440c800e510303003c1180d412190700c559651501e4003100c0d9160482c03184014600403118075505919000c01100f5021260806405e1801821882441c0b524550910860740901c0318081c820290760180080841e040241030400c03211410080350f01843c15098a80400041e09150070003181040649001c865005820f445013000e80302c00045800a103080f0f07031640e880704d1084040001000203629090080100b40c1c20100d4041000c4000d9880d038001d0201031060040a1000c105021116541c800907d80001d66002000b44104040740c40c245440390041c0c1000d43c00b185844801103031660040c01407a841811803602d241c095511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 976854811 1250 976853561 976853623
    0x1e030e0f07032d0803040c051005031306150503070806040201030506060403050d0c15020a020607020c1806040c030e0d0201020d1a030303132a0e010603021c0e15040f1202 75
    0x310f80c0b100103c0101002103800000c054078040c6200340e00418000700710034a00001e0040d0740c2802c0f01d81c2c80c1040740400c100035204051030017054035980c10040000f040c61a50146480c0044150000c1d58580f003107400004400e00001001842280300b07980c24080e94803420180000342c0154000141160010240348082503c038146500391a4001c4141010298a0030140c208a903c042201801a00508100325a1a0301003080389040a0143c60520503c20a03840394250440d001d0f0050b4440d0384c90f107003071458403442038000c40c80700307a07800b8241d41c500c94520802034001d6000040e54070382182401e44421040c10903114811140750058007451460b900c58480c01c0e1903403c080403c880c5581184030304400701050034031904038038064008100b101400d0003000301c54410142c1c45002010300410681104000400704a000140784e10804504241c150900c981445481a4080380520351841040140b1001c4c0541e551124010821520350100c50380049890315520030b000c13002640c0c40002d2080c3c000f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 976856061 1250 976854811 976854863
    0x151519081c090b030603010902040e01201903111b0d020c24070f080408010f0b0a061b0c080318040c0306030c062a11131401050904031e030e0f0703 65
    0x145c01000000c0d4042681d000600310740d00429008075136903480f0040d220300f50303801c450040031000690b2241e04010340c1401190101c0148456001059205d065103826201000151201c440300e40c01011400090780410395910f00c00f84c00484010310608008a8150605128031003d11010711000060125212a6140715502c11141141c4080040403a400418180d50107000904509000854001110035004040d00e0101c100d0b54806c880c800420010150450552058080011185e03840c80b02c01c2e06101e2040701c52035022200a010008810031b800e01c0c04072800c100054120303020091040c0311700342201150b98500004154242080b802d0040318054407024010340440c0d90014206400c0c0c0e03544502e880450881110340b0928242c11040c14505258606060114030b58100035407040c01c64111038884043c400c4074050179110700400c051500c81c401020920642104020329003a09900080c0100842e080229447c0201b111000700c540c00400c0e030b5000c0340e03000724030010b2201c610a10095524 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 976857311 1250 976856061 976856071
    0x90f050d080c120c07150c020706140403020d03110303010e01030b28020c01022817040b01030602090d020306130c1a07020f0102071d1b0c151519081c090b03 69
    0x4003017071010301e0000340c04c036031074006440c40d09002095071841460080e03d4030507103030010014040d644c01400b50710101e6100313403002c40790104c52880c410107240c24180c9a04da080c0a08003401c4c0400000824408417418006048901c00c11840b002c40c0d44403a007402e000b03000c000c0c2c019803200f040b0b404c41c3c20700032450f0050304e00603041200061030082c2e0521540c00d00078805c0035096404800404500c6095000b4248541190300d2220020345440c15071b503403040070b1805000c01070a0702e074041080341194544105e903c0d02c844d400350844005042a10802c1d0b000c8a040c002290680458800450f032500b0200c003c940e201c050185440c1000201d50070002e09506104101c2d0442c0300b442d60018600035807520709510f03c419802c1038034450420940b007450010213010070704400c00080104801c1d101d030002e81710400728070034440d89aa6440c1c0111215045a4601f11039a208080a02400348503403807200250855940001711509032080340003040c6040a05034103d80800c22540082048541c40d0006503409 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 976858561 1250 976857311 976857331
    0x9010b070302031611030307240603020a06141204032d14030a0f02031006030e010506101101060504020309030c070f21051018060b0d0803150a09090f050d080c12 71
    0x5201170200f4a550880081038591400507115211007a6110b81d0042d4043d4000b03c007400154256004a00402d8040c07040800704100d980c81c54040d580c2200643d90764160272030b0f0502c0c80d0700301750038001d00742e4200340440f01000d8200c3e0b500040094400a02c500c816001d500e4405d1074005544151042c0e400081641042a440316003001646c000d5100540c8a80e4614424901886c10b0a000404131034001086038a140c0c504800c1c0b1145580d0340b444021800030500d07054051500c908241405000242d21513604140044103000031120084060860341e4914000c89440a540c1e142d440b10101480c401c0c1c601d912507211207450425a01e5000b056018011802c543c08220303980101d0040b16200c8000381510143c02c0f4203101005940c2c042d840c401c140c21542c070142a00e150310358401500c0041c0038503905800f090704070b090644407414980c006041c641c1c030802202c40581804000003042a030304403010b001e00c90600c014039004e81005070141c06045601414100f02034403003901070714058400c042d2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 976859811 1250 976858561 976858583
    0x20c01082401020f0601030302060714120109050402130603060209150f0d02092701051f0909020d11040e1605040e04060207020d020d0606080f21180d0803040209010b0703020316 78
    0x5812400c000303550085101e58000c0002f440c02c290010003540c04c0e6105000710f05000c004255400180c1710380a41915852000000c464407684001454045c2c3c00e100d9480c2c0509026000090100541c050403164405980007100c501d0307441580002c611030900080341030481444402005e182d168094102d00d4009003414030203514680100141800058a03441c004015030014803986c140001580d80341b0300c0d400d1044106040e43d6101500600f440d00030f038041c03264007240c0103140e50745c1c94006100b100ca185110703594460302d40122012505044415582840c41c80e40c0758039803030784510121001c681031750031245140d44440e80c40b0030113540440b005036401070f1903c6080003d80d8800900c0408107100e100001000c48c6062041418428064281c0340c00b9007041440c180c5c2c801c0b0070b0000c1504030070a101072a030b035040140c1c03c290160584400040d04001140400c1c010001c038000154040d50080395150050380e80d800007803009100d1280000e005810521220b500c00c60b40080e240705140c85000c9000e1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 976861061 1250 976859811 976859833
    0x30706090b121e0103060b040c260901110c0105040c0501020a0203070b130e070c05062206021c060320100c08030402010c0206030a02040f0e0c041505070602041401020c0108240102 79
    0x100f080f600780c00941e00d0a684004c803004a00e0140300d00b000e00035103400e1040c190160000c41c05c08015a038544c0c40c1c0007a00480000b0280c1c00300b13502aa407103101da008ce41d9140c01c2144c3e50240200001ca6080b1345903460a43c000c902580001092185d0070750090050002c00d00340b25a80b0980e4220556299422884c040c000c07414100c26060640310343c007683c2c0e400034100e1079030400d1440d100015103080035614103965180d1083da6082c40031441141c10210250384d6010162030309881507889929015414608880401040454088a0701c050300e404107408580030014200401d0b0705d1728001c41000b154218102c4000100190081c5a102d801418161078248068003c500309500445910003601d600040c248240e58095501d100900880e80c0300100714581200c40106a12440c01480442c0307075140c2c01492141e01c103034201d0300da642d4403601c25500e40d560f8000110741e1060340c01c07040c0d015010741c01060007154403800001c1d20424076040799505080710b0740310321002a005a0304403070442c0101c05030b0306 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 976862311 1250 976861061 976861111
    0x1051806030a09151a1e190302130e0706031a0a170f0a02030c0f1c050d080a2a03090605090d0f050c06040303180b15030706090b12 58
    0x544114408440442c0c0c80d070082c50544000c0050712800c1d0300c02843c0c545070705c05030143d6000184020b002580c41e5105816a40500d0300b03071131243c0422a070b00606c90105450206520b0090303c003224402d88a411420003100074503010781d0780d900341511503a03118100c00c1115500c65080f02e1010090070340030300781041d2002c0114003400c0f500d4102014003446040d45115814040010310708108001c4060440d05c90103a00282e2149031940d030b618450300c605282034195a5968203400102071900000040c0030740d9924125807501d4255034010081140f0f07070000b8501c1640ca0243e0b2401d0070111400d15100c2080170010003140104080e61405c01d40d4070980100011641e01c03445000f240702c0e0000b0841000c502d40c00400d040180040e0408025003404000402140005c500307400c2030b0306042c041910081e40780842c843c15002c500c080d01103070b030200c00d0280400d505001074443c684154240c6040c103864020590314a50300c0d11412208040400404440c60391b1420203c0d001119441c41d94502e1180d10780603 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 976863561 1250 976862311 976862317
    0x12060901150806042304030207080304060504090209030f0a050d081005010e150d0c0203040e070302090108040b07021f2a0906120905030a050d1a0d11150d06080609060c040501051806 80
    0x2040480381d002403001f89a010008180140301000c0207502d02810020014010b000b903205401d4065004a0400455501408042c402088034011500417200f10309003075a5411601101401241910b0041344a0b9540c0b00809410707928181c403040b0b1900c0309082031100b101d007e007110340340240040c003217920300801c06c0c01111301d141c81f42c0d0b0003961500d0401c582d40803480c41c054400414903104020f0b58220782d1308100125840ba0b003019001100340e40d25001607080c0740c3c258080f00e1600c103003030140d039000509a034400340c90300007401c080482e05481e135480002c09074444c000c0710700880c842c0c003810410244107088000c00c50700c16403400314296543d5a42c992654003c00500d801103407000c90100751030051445101d0030400e16900c0b100b800c0e5904004104031002c07048019010341c0c05a4a200082d884040c0d800610003141c0c40c0c00c80d555070b1210f810500400c224001c00140b40a820041070400703900144440c040c01c0c500c85518601071600c1c005541c5980514211404002d0070300042c0d16580da02800703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 976864811 1250 976863561 976863611
    0x3060e07050715180201052803020417150a02090a17062a09120115030605160206090c240a0f0e060a0824060309031206090115080604 59
    0x8080d180e102d189072024020810015005110345001000e1004840c0e02c41d0507401d160302820300541c0d0750348616540740300c3c16010520600340c20000b804940300c694558001c02c121000015071a00c2e04090f071145580f65107031580302c0902818108041a80c14042d54004c210842005041049017030307481c2045609400410703a8210300390482000c1142000404403c40c00b0f80d0f6401048001c982e40910008125018901059000fa0400a04a545e034102540f020140c1d2900e80311401110380d90b86820005484211542c185424640c0212400c3d11700016407076015021a20151004800e1001800300408001110390400540348984401c8400c16200600c400c280f01e6407503807084904820040c01c941d00c4128240d00a140070801d0f41fa032154407031030180d0020040b0700351071200b5120b16504590b01c0c402c507c185600c018008244048200000020720074101505540c1b42d090351107c00b0403205180074450b944403807002200e0001502d03c030755011644408010000184010481100402c0c8059014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 976866061 1250 976864811 976864817
    0x807051b011a09090f1504170316090602030f0d09030e0d03050c010c050901210b0315040b06120a15180f0b010504110405011b0501140a0f090b070c0303060e07 70
    0x2a02541800c3c50389005034410f00613401807510811103841a9074940d000310044144820000101d400c111500303003c50b104540d03610140340c032410b04942c228080700301009a4000701d1030664000800500220680f030002c401007140b58185076260003002d014015019044040140d505524803240c1e595440c0041d03031078040d550342c03500c8120082815086880500184007800f4060240115507039100005101c5480c0b406010003032500d1400c004005411030b290041d03070600968000a041c4090100d501d80300d02d0041401c51107039116841406401082441140a1038000c2c510307038030201d280f1f0803804603503400c44203001522002d8511031340040341d0891011103501c42000703241d00501009409180c05000100c0e403c00104088401a601521491180a0501940f040181498804031030b480410b00d81140c02800700c03003d0410040c516140482e24100c090340391010f5540000304a00c1030154442e8008a51040fa0725200e1040d5401944090220708060304ca01c40452100b03e600e010701d0003800d07262 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 976867311 1250 976866061 976866101
    0x16080307080a060b1c020c01110c10060b070309030f05031e0910021506040e0c090106030c1b030f1419050a020c0d0b130503040801110301180c0807051b01 68
    0x400d116040e035030709501c40704c168402032107400040c1d0030010410802103900c44005a54032050702c103031405000c09003041d41810201280002c0c00740d01c0030074048150300550000300040303034883c0d070701030420700560310040c0014041040c144006002c031102e04031101d0040c41201c0c10030707101c3708041100811104d841042110007203203450450a00d2032400d10f10300460b0014141400d451040e00000354801810ba602c21511114410502d807400d10a10034810b81c003910101d481e60f101c003000b07005072540f05070010004980c1c90691010981c0300e0300b046249645580e81d100e041d8403080e000c55407401481d41d050442c2004021900e10001007036075400c000000b540ba0552035000c0190040d0601c3c8680c2e0055001c0c81b02d2a0084001070801c50401d948000c442c044003010680d5414101c1c907601854003c070a140d86800344c00c1c01080000806181250084143c00e44070380032059400c01500c5542c50604007141908010640107409072029080710404091a2145c80e101d504440d401e445004071a40c0b2031030409 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 976868561 1250 976867311 976867321
    0x9031902011806050c0d0e060603060702031611012f01060f05060f0a030e100e0c121518250b0a020d0e0402190e040615020706051608030708 62
    0x51180590405140020400c1c4500c0103401c2400c42e400b182c2c0202a42e5550300059028035004003500e825103810b0740200404081c0145d071aa491f28141e0740740e4030a200f80000144c80c90300c00821203001350508801032540100c0350740c0b46c07c00d5044400505040c000a05402008580b090003886c0d01440078862001a400135596058211142d58102140c111200c0d4000e010540740c0c2000c83e6003520380000e01c5940c2d128400d90803001025082d41030300590040b80c4000401102c00d41051070340c800013030300741c40c04080c10030304000c84640d0705003604007250813100d5518000961440f51035440a01307680104190704202c0019424150191080d0b4018030b00d011040c101f40060b4030096014103c09000a860075203043c03000395031100001401000c0110803070141202d5145d5130183e92800e130070b00c4441c3c1c1c9000d20302c4001504e203582035040300d4012441e200d00041c3c1d201c00c1b03412004030169242c01820143c0d0503c841140c655000703044010b4100380e00500500024900c10040d40714014a5031410094141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 976869811 1250 976868561 976868587
    0x219150501060e030705131805060f010803160b06030f03031f0807030f02211009050c0102010504020901290f0306010f0504080c0108090f0a06150e0c1b070e0903 71
    0x182c0054007000000040104907031000521034003520400c0701e019a048440c000c400f0701a000c80440d400f545461402c040003042400901c00d4001d490040340030704103070f032200584c564074012103141843c0d20a2542158020a040860941c3c00c080090143e40c0c554280c40c8a903031955000782e4240c80340d03110608240c0d10103222010b00001609072000175001580ca107840308200801c642202911a0300c08405041c241c0da0303000403140c1038051440076120780da241a99088002c0c03003a510161070b2030040c0440541070b9071040c42214404c69005240e92074a9080038078002c4c64443d003241c507024210011104c0c2642d4641d0b00040c1a08031540300c0029600e243c18000104201c401c000b030b03d818000103000921a0341d0380410700000000c0e007881c0c503035580c1c3e6032641c1c1185490698104103019000c1d05800030240011500946002e0b01d40da041d010000d03948903a19000410211640400c0010034040034000e000070b4410000f020038070b1070842e241c035522407900702109041a900100580c1c0005140c0500502c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 976871061 1250 976869811 976869821
    0x250809040b06090312032212090e042103020c01021204050c0a0e0106030213090513020f1207090e01140c1315120f0e0d03051f180b01021915 62
    0x1c00d603506800d200c40795011a03a01c9818050180c00210040002401c4802806c0716001c1940386a000c2e00e6181d41c90f040188100307401c00405000544130032400714000c0410160103002d9584520403884000c8446002d01500401075404003c04d40c0030031900d804040240090400400b05c101c260340142050b14140d46002c8040c5111400b501d10010708111250000f004c090440c0c20324117000d0ba0750040140d0654000c6580d402600c401d40c544024423010070000c0e040301031807502c00c1d29200c00303040c1250104071044aa4054241e00b550090105000e080010340200b035100c1c8051002151940c442c1c560160405401c8401420b4480e02044500c45001b5800580c001030100303c50000391511010030040c0071150108a0040d415281c0d40044482ca0890b4030601c185c2c0300070f6003a00c12090301d101c0010090001680c0c0c1c0301c107030505040c00074500202006003c044030404500c103072220403201c0c07884024100c0103207603606501942c05181403401d010210310b0a04d0780700300c2040e00019980f61a40f41114 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 976872311 1250 976871061 976871081
    0x1707140405040506011715071101060609080c2e0206160e0a121a010f03051507020a0b090712060b03010f0b221808040f121725080904 59
    0xe41803900340b0022030004252181500c20409000003400c0d1340c461011303d0064180501c15005ca050b0040001844e40004440003804c1300600030f001c1076903a0328003250b20003103900503a111034000780c0030210146000c02543e07180c072001044e2002010540001818101041500040547c2201c8104600f6031001a0fa100c0741000d5410001c0d402d4141d000440e00e44410b90052030506e000901c0e0440030322a1000c003000e072110b02020501015038480c00c4150b003410191104680920510340e882c030b2100c51a450061141406034010b21220f10b0035110080c0110014003800140c0c06010b0002c01da00d2052521842070a010301c80108034068a407062500311020005482811407a014600d0884d039207031950750384660100e00040d9040322020f48404020080d8003400042d00190440c00c03810411841e01800442d038542c014406a1039807402d104061000e0540c00034080f03402d032403c000007136110340094001079822100c6614414090702d43c054001d01e0820054a0340000030076104d51601d018060580c2035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 976873561 1250 976872311 976872319
    0x5190c06061413060b041401030e16290a0309020a0f06030b0901080604110f01030f14060111030c120a0e1c11010e130504050c15071e1101031104170714 67
    0x1036180c58090645030081d402100c200f511905070381403041e0310a0700031468ac09404016a0302d00340c4607071a490007440c039900c41d0fa04000081e014203240d001e00942d4001c400c00000c8200d42c941b65050320214020018154101e034015001100490101c2c1c003000c5400c003800303880e14000382c200c003000100f06010405912007482d517800103041000152180486c85890350302990714040c0c1903003c000683c0644541c42c8100881480c0c00c0c4444502c039241c170207441c0910700a8032694050300c0b0300088503403240b14100d0a860141d1000042e1900804a40300401405002d441c0095801341900c2c0000c100005000341102c0c0e0710070440c69002402007020565080e03a0003424200c90004003580400d0520a41d003049010490f640c40015040c020240805011100028090740200b521840a43c08503004034000b62180001c9101c015110200001000389598102e10940c8088400000450280a14404484c10b402003400006502e403600e10360301542441c000040c004a9040c0401c102803517010107185841 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 976874811 1250 976873561 976873571
    0x909040b040f1704051504050d11120307030801030218010815190204170c09060f010e04020d0606110c030a0809040911040527030702090c030a11030411040e0d05190c06061413 77
    0x8558030321000c20100d03682b010b0840b80d020700601c0040d22000320001442928080041c20743c0c101079002d4140fa050304d00c00c60701202c5241100078991b00c0078509010b4005581c0c0202c052080f0307a20780d401d585a009804039240174200d624412502c0c1682c02c20360011040c08000009680c6c0050203110250344001d06031040034081c944080080c00ca03000c100c40c070380d040c48039a15041200d900c40e40c040726000d5040c0301090100c10340c2d074100100203242c0c0345d0440c032044c058080400c00610300400c918a9681c0c02074802802c051445003004001c000f02c170001c85035402004081480780d1124020240301c2c0504001c0006250480900b0340004e143c2c1e21050b1003140c01c01c2002c0f0700145da505441ca5080701c40d440e406501d030744e6072882a8000300100e912106405c00040304000c20000550140c2075044025103060054403015100c1e01da45211101d602d02c003080051041114480b0700b0711003c00c08441038a4600510341d22a1214000c880007500901d0411054401c105110306140440750512443ea060400c8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 976876061 1250 976874811 976874819
    0x60403110906100f030b030a05030c06040209090c01090614090a0807080f0627100218130515060a0201060b160516060f050f0f0c06070e0103020909040b040f1704051504 74
    0xc804020b600e20b5045c15512026400192000c1083c0321907544e200045070f41d2518090034a66039940120340172403043c8071000003d40c02d03440100d01c40458440684448441600b000d0060342c0c0440740e40c0c200c0442003001d00c00d80c043d0b0f41c0c86861110003020700310040c1607510b042103040350401100302454446544000240100c0c41c0383d80300704001311601c2055100b020030b41c1d2001c540c20701d8a03115a120b01d1600108082a074a400e04d4612040e000b0111007070a00021400c4040003038402c100d5007803810380c550b03481c50700c140d0406c40000c256035581480000703603a54032080c55200341e41100258444007100c0c11401002c0100410461820000c20b401a000f0389103000c0c0300524488030110b028081290100b900e5001101001c15540c07031301426140f0703603103039498400c2e41603617082c08494842c0081e45100e082c101a502a10860380300101c054540440e50b036031500c5040104030003800840d0408801000c50b004a185800c1401140030010b0324150780d03c1c604010816210218940d025035408100f000304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 976877311 1250 976876061 976876067
    0x6040302010207170307051605030705010c050c21031c0b0405040b070c0302030f0301030602090108010905100e040f0203031209010b180411280f0f03080405120c06040311090610 78
    0x71a840e00591a1340d41082a402905502461000403c00c2c0310f040500d9403145030815006050f148180e041b10320241c0d62308011140c400700103001a03c1c42d000880c4411107810321240700c408144a4030301d040c401d608002c00d22441c42e480300d145200d180c1c441640c010185400f500800783c1f118400c6509001c2c604194407250710700e0303401801071014801c05c034216200300750081c000c0d540d0414440c20041d03100e41c0e403800c10401031b41c0b0210709240000c01c80800496030312600c2c40307070070701802c105448204244d061900e003541e881e8000d0020781c0d80d0403203084041c0c0107940420044c03070741c0c24011784e40c030200d403e2420605080d60004403070244074841c80c183d009d40c400b51252120f680950423681620743c0046c03400c042100711046507045906030440c81031400318a5481d2038100300311802c0c0580b2143e1195241581d0003070f42c0c11030200401000c0100000c10043c64800c4083d0321400c04138050f2103414054500042c001c0c0d215520484188251403109225890040b8040303a00003003d9130380307120040b1110401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 976878561 1250 976877311 976877323
    0x1e02060f0a09090c08041a0115050912060109020c07082a1c3c0f02150c0109060e010c0e1009091d1c1202030a2301060806060403020102 60
    0xc031405000c195241d801d480791685100600b080700c3e0402c202c01c00500300516581c000c45084d80c042615502d816480c03601220741604076610214510704e0843c202008880e10351000a005c0d0744030011703616180001c0700604c045802000c4000005940350340b000c0d103c506028903540808102e802c01400524000400000b0701051054020b0312003008040708001010840c0165a03050034800ba420744004011302c801140c104070b400d5924254107540100107040b04124200c8609071081381701d041c1000055a103c0c91595400d100804110030b45c8007514041d00c054120500d40c03031702c580d1a501c0d01c400f402030380d00c00c0300c400c0c10b4804001d010300603284202514405000d250a800741301040c80303c1002a22992051014182d290428001c0071031203007001d80120702a49080384d131070003450000540030710703d0910b0a0322100b40ba1a552880303c02001035000a420041140c90320a0b141e40303c03403042c442c40a00d04148841004100d503043d5040450061000000401d00e40c000d403130070041400540e80002d10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 976879811 1250 976878561 976878577
    0xf1d01150b2215021e0a0206070f111f03060605090d0210121806050f0906070e01031b080912090d06090602070f0c08060a0203010e15010201090c09091e0206 69
    0x50b0b115045503100d0305103195001d40e001e8210b80c9848511466240e03404102083c6074201c001d21134040414600f01c56403283c00e0710000a40c0710038100f02e108006040340d06410310745806504400c43c000100b002040030065464184458081e000c0380724001c7c0ca4040c8541005005c0c5458050b0600121802242a0303413000900a4801c1c0c640c8254060308600c01c4140c40b902840b200740074003084611034071140f140b0845aa0407a42a1b06200c0011111030000c10042d00c0350000038010f041c41e82f550182540d1718003101d40954100742e2111989582c0c1503e488100490003c41c0d61140c140c1d00e030207042c1c0c0341807051400c0c0c4c10021001c01c0281000c035a544100509003180c0107140011643c1c0c7c94508140203100707402c00103114402004d07446050010700c00244c800c0b1105941501c5881e981c60300745404a00c001d01400104648140c040b44076008141100100d0107818000044c50a5560311103c605441d9031380100721098a502c2c51908024800f01c00d01c605080c07401c01807907146034590005000380074420b5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 976881061 1250 976879811 976879837
    0x71511040603092103150b0711060c0a170712140d020901030902090a090b0114181302092502070311010c1a131103030307090e0a0f1d01150b 62
    0x184500741300d0810349240e80c40b0300707114424403a20074011014014140b1030b40d483c420b42e2010368001440b01150822104403580c80010303030300038a80390020862241c0044e040388a40748600c1c1a1440010900110441d0014644203d2601c075401460603010380752041110008200083c0c05054400c0310713000c140e4080c20a04800503847d808050012001030880c14000781d40001c0001c01d00241c10a90303070121f0072090044010340038507071701ca510680703040d030150700c94641000c2c004d0495101110111100d0f0f0b005154480c0070b0055240c0c58000072250407098034241102410700e24030b03003100c0664002c9662070165600107491b01c18038686421506548a102c3c050521500980e04410004c0c2001031711012910301e07011840740c1c14060100080100b40c15422140015107580107269440e0000580c1e00c40c020542e649003801e41404040c20502901524a0340b546031070700070306002100c940c0104a01620312080c01f41d402445400241d0944440c055500c2c00400c00d11000e0209411210841c3d031841c901c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 976882311 1250 976881061 976881071
    0x1e010b01080a0e010b06070c1403150c030709051e01020106060f02030d052a04140f100c02040b030f060405100c12020304020a0f03030c0c080304060f03090f06090305071511040603 79
    0x20f410140540056052160320003800140f083c20800308031600815140c1400752030504142d4a4141659001d2050440300704400282c00102c400c01c08000550340b1410038075190300255520804501f51589800040c01100420401ca100c556424440c48005000f28a0700031060400034034040e49078810707a001a0040c1c0c0c0c4800006054005003001070200005003e4800ca080140c881c0060f603a0700180640341c100c1c1524002603c00d40340c45513002c08210802000314801c5e21400100b502d02015041c0101d8216445003942e50850b6020700c940442125100c7c0502024a802e240135428160f00300e1b668003080c0c0c901800058090303031040e816240c0743d680b004016645e4940c1d000058090b2000d82c0413132000158210007008141d4080d10148100c1c2c45403a50700c0740a41c40d600b4481e02c1e03020380c1c003c00c8000303404503c8a040851287d00f210001c40e0040c2c41d01a0342000c20b40700c1c0d6050b94466001038010500010b80380c0100b00c001800000381e406900010000ca80174155400683c0c4101d00c05c9070105500c407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 976883561 1250 976882311 976882331
    0x60b0f150d061a1305040209060406030e01060918030210051608130c030804050405062e030615051c05010303080f07031b120c0c0503030c03090304171e010b01080a 72
    0x150b4001805040b204040d2407aa02400e80c20740d035203030b000304034414100e144140b000946040500903500203c80090550f803c040c01e06408800034000d0300f850a07030964a444c00013a841c3c83d50711541d82d20881d42c462007541000103040c042c1c030303140114940b100c04515080800c20a424034450044035a0010710300030b01d550b1910b051542580c1e418800c0585842881030740003017040344802c0203100b280c43c00d850502141d5601c40403c0206022072900280d080c9644030605102061228060030714100f078280042d42030b44640760703800d01041d1241c0c2640428070004504410401d0303101e40c04000240480217100541c11650020030004001c0d100014003032504010270140350180d00078500300600402510380c01e00d0001002400d50340c80400d450b201500d0800021582d81c407a8034012030f115005402146103444000c00107041d61b00040c00800e01d40818000481d20b00603074100000e0501c420001800002149180340b81c038043c2080e08180144e242c04400c44c01640c200d51200d50080d01c0b1040000c003a804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 976884811 1250 976883561 976883587
    0x40e03070b0103082a0604060b0619080c040f080313120f0321020a0e0f030d0203120702150108160504020a020d032c15100609300f060b0f15 62
    0x38420417070703e0510361101c078042c50703a0000492030720a6018800a01c403c0d01000f003440014426000d1346a410500d00d0000c840f214014018140c001810740a01ca14140c0d03101e0810120f1034184c0c20014464000281c0340b0240000040001c02030b01d4440b400300d51400030307540c9111101d150303000002c003480712101c4d43e80d280400819000050340c10b452030075035603481100307401483c0c0552078035445d12551503142c000c030b45403c00017411200c1154a8009600c1e010001e07a02c07021000004215000b188590501c440e00c110214070b11070b0003041184000c0a048030b0b54900245074660701c0c0c0006004d01e106008c480502540001c00c1c1403c07d105040c0010503120012441000104032541500103801c2100050400030000804115840d100c15010b401c07030f259501001d55030300340e81c8108400120002e00510455030001d898941d02c5600f190312152207020360603a44140c860640040e11440e2501c544072041c840340e80100c4100c0202101c4454901c00240c00190100120040003080f030100454542d0007001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 976886061 1250 976884811 976884847
    0x7030b0d2004090f02040608010c0c031803020d14100c0504050105070309080105070c020f0d240f0501140111060912090f09012606010308040909061b020705040e03070b010308 77
    0x1402902c18441201c007402d0800901c0c0c481c00003203004514101002881100611074807003105503030b1352103c05520150720116070301172a0018050b99440e4403400080140d43c1ea1081040e0980308990341d042044140c89240d0814544508071001d00c0d081a404a60700d40c0e0060440b41036410908001da2189c40d1418103c2d1840040e4129403150f40c40c2c0701c00e1018090300040000c115030310846030420500c0069080c000344858040004103a25034400820368074207504414031000500e5903000040341031038543d441c000e0340e0b02030340f1804a21038422003025055901020b00d01c81322051100902e0942002140e49503a000c41c4081d90081ca40701064a12855540191541901d80001d140e0440c03961119000490041203110707500c1c0c200014400c4610740f000c04112281202c3c0c004104604291810300300e40040c18040c4000c4a10360f0355503074059954080c1d45068141d401c610350090092a044c1810310088440c0c0c0e014252a0f60b0050255030700040861005074156540420030035110510300d110041c1d400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 976887311 1250 976886061 976886123
    0x90e220204090803061c1e020d0b100312051201051905280f081203060109050315060a091415010e03061e0604050403050a0c030207080d021507030b0d 66
    0x742419040d4003480100ea01035030142c5c100b21000900c01241058107800712103c444010026901406103440c28401c43e000262007600107032004100355100d6441083c808800c64500540c42c695180500074000150b1040c00100e16504143e49800701c4e020001040311814850700e449441d009103225504190440c0384402043302070000007041100150011411200d2000002d400050040016542e000281044203d0b01c0ca07501030070340c01449050b6001c0a503c000c240505006101000003182d407410041d0025145825480c242e40d414408200082c03d00709034814102c081c14021f80040045468040301c2d00002c81444907006d5400070780c01a54007040300092a41c0c10700402c81000503402d030a404060710150655558081c41c3ea942d810003040314429100a00080c2013400f0307240c0301d0782c0148202504c1e14040c3c0121100c2c80d0f5101c00c030390b02d044165140c040058104001006001c05101080c0c0e4106055007010711102d1628004104509104103026041003141c0b016144a0104442d880d6030309 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 976888561 1250 976887311 976887319
    0x1404020904080d06080304080c040c080c18120102030f0901060815060a0e010e092e05091501150e1008240406030614100302090a0c030b03060403020616090e2202 71
    0x13040c0d451141c151641c11030b2040aa0601944001504910b0544640040e42030a6200d48006865278807440c032064000c01030b4182101c1d11402810040c1d65003c1c1505c1003034188100140e6607103480e8200f5001120b000d0700f1412540c0c10810180b000e144003003140918070740702c0494207c10340d480c0c800103080000b050344800610198074001280c01005c12050b280315000400c00c4035103402c2070700221010003005c81c0b242d000f10080e01d42d018050b00ca00e6044960090b010008840010f6001c021000040c3c0081c0c2c40700c201002c06072a5110082d400c14917440b1030301400c950008065088500180585100402501501d06190201c0d00d40c40042a2083c20124000d0b1040049030f80380e1500500030041d048561401c0001040013402001d941c84801080c6ca0b40a0440b02a5844130b550403000340c20340806000074103480b503100e0121910100000d0703100314002e6000b04024146101e140702c00008120960040100f98032051003010303a4404d40399084007440032190a914103190080e0000406070a000f584 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 976889811 1250 976888561 976888571
    0x181107080c0606030729030c27040b030102040f03060e190c030b011413020c030c010f060509010501080c070f110d030903060c05040807030f1716060f1404020904080d 73
    0x88074000940c1030f100300700c00c0d070854510382d403151000b1100403000d205160200c4607542c0c191a0076003560b006190002d106001e0b05080502c0b11aa03201503828540c861110076180b40350807030300c615090046140250f816402146404e080407c80201411b0b2400b0250807191110b02840c0d5610f410024001c0c01ca00b1070341c11285488c007500d09a005580717a4801590080c0c40b21002051549c004103001107c08001071102c3c6c100101c503402c40b4041c2d048401c049107280814840520051800e0094021001401b5400941941890100400c400d0103812650400224800304500128150110380c0016044540400801d5042c6007100c42002c998a2446c3c0280c00d140c902800c06400040000950744a888203010031842c041c0308903040d000ea803241346846d501c59401000820101c400e644805405010002c47d00c2034080140c502c01e50000300c41c18000c050144610b03091100034400e182d00c00d8482c800c01d00c40003465207958000741001500c064481c211354000300e400c10803920300301d6080e440d42c9401484 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 976891061 1250 976889811 976889827
    0xe103e030703210203060f0918010204090b03010e07060c0b150d120f08070f050304080d09150f0525090905130b0c0a05070813051f12050118110708 65
    0x40402c1c425822408401c43d02c0104003040072083c000d44c2e11465000e02001e034401214000c03c000080e0140c1015400112040229000700382800100301600d02c204010070718180000c241400c6075030a1820580f80e40203840c0c10700030b0542c0b20095289168011440507400c0c1c603250541ca000c8190b41031216441840020307071100b00a1028900c0c0e865550302e4403541415001201b0503258054100c4840002420f070022600e12180610050345d00507000e000000d00f02083e900c0c05100301c3e080b40b1000c1d590b2100585004035180d14a0251311012001c4180612190902c0040d280440001d090000c42141910300302c032400c1841840704a004107041e80040c0000d052001841c04e03803174042d20060b40d41c58420307000201450710703d104880040419941d500e1030150103403104644c9410182403d14040003244000030740b60340c0d08200c40b03018510100000070000c0345220141640183c1014055860305100040005c0c4440060080441020007804941c80c1c400c20b5081300c842c418000300620003040070500780 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 976892311 1250 976891061 976891067
    0x6080403030e010621030306080a14070b0a02070b0a0e090703060810050606070803371b020d120204090e010e0c1e220c0e103e030703 59
    0x16009038003070340342001041d001c810071070b01307a540501400b44201c2681044031a408080e40c60020881d009190018035541c881003802d040c841c8440d400c0d9692804c040049402070b0041c400c800c010001d5012032407809105010207501d8900611480c3d100c1c007008075080400c6402008120380151004042106c107140540b000740017010140a18065403058400201c450341041c4212401840001c0125040c03400d250740d00b2400e60310091070300d689801003120802d149102284901d02424401d040c04004114525190044481000d128140c241030001d401000b2600820910340d8080246030112030000081e0110340644110341c0b101c10001e29148100e05c0c40c10065100383c418580316130558212841c0c1000b004035a146da01400c950072580303412880e945180075480c40e05824201d1108100e4844081c20250844409507425030220f80740c10380d181703ca403030010009000d040550034080c0c2e00c102c00003841604030301481804800c03001300003040707420924140c040c8042c10340740c10216640d54145260003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 976893561 1250 976892311 976892327
    0x50901050405010c03110d050604110d0b1804121d03030412020301050106090f350a140607090303030534020c01140a050a27060908060f0606030702010209090106 71
    0x7030ba4154a40701d0b480e0801c512030f0144084250303c0342d07140342c10040303d070000500620020b04555409a80c80041601b1108a02c000c0c00b1440707450a0700081e80c1700b80c4000e0019508084100040c4011410104000200303180700d110a03c00451804000848400d80c80c60001840308030031560610001c10000340c1000a00d003481286072090700240aa83d98405003559062070f0b901420101d00c0d1420014071000494442103c600c080c031901d071440201d1403000c0c25203824600c80030340225400c5161800d003840341c2d44921a00a6154000400f07140c0303000038004120140d40c3c04001c0415441318041a540b220700400c400459100121140c00c0321840c58680310041a040c820801601600c0c10340500c540c000c5661b0f482c6656290091442e009038034004407001c0d40801c1c0040c00344160040c020b20b08800090550400c103e44503150007805040c503401600300925603001c080f80b42c0c498070421540450460455400c0703001519056142e0700c507600e080e800790142e541425000580700b800001c00d00c0d030046103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 976894811 1250 976893561 976893563
    0x1051e0105090402010918060911090a0b0903070b0705010b060a17130302060c090f12010905060a09110f18191a030c1c080a05030106122904111c0e0a0c0501050714010509010504 78
    0x8080405e070307640b002d803051409106003b07a41504580b008004940d01c031070050242c14820800058090900f10008410b41c03c21131002d0700003800150f0115072034607801d03c2c403074118a51401d070900b244185c0da4020b50380c0e0b00c010403041c881100810b0040594440048852502030001e02508643d592101030a00078a8401010f41300c034440d160115034202040e100c0c10201a030444407484000190505008594010503515908403a9800343d243c00540f940b00301d80d00030030403c1d9030001d841d4003001c5039105440c058030b80c450141d600c0c410040801d9074002070702c0414050990700c10030032000043c40c02c05000c80145c00500f01200000700050312961090055058480944031000c0b10728580e4a014101e600c000140c1c411049441e041802d000d0511800e80d601e41c000800210b655000c490b4132044a401050b0111045414914010803034040d0340155010301003160010b241d840095240c3c2e1107103001c5c80c03041d6412302000168503001d014818a0071000552600b00038485410415001c5000b401d04580c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 976896061 1250 976894811 976894819
    0x102040801020c25051e1003091b0e0402040e010204030f030203280c0b0c041e090f050610050711061204030e011404051c0501051e010509040201091806091109 70
    0x185807030850140b00305501314620001080c09070503080c5030911a0800031622011035064039080b0b0341c0c84664840480c0b0f2144009907a0200d02000340c0d142c00c403c00d04941f000d55500100d41e400a00521503c2201c03180d125804135070115440140c10045030083c440c540026101e40c00103010001031603000001040700d61100401c441014410031030820208200f003a001d030000f2044039422001c01c1c120390750b80c1e400070301140b092440d0540d643c48012400302031030b20115071103900e41810000305815205417030000150b40e2060100c0e143c60000688a640b0f11803659007407080210302c220a00c0207100c3c1000d20340102425140c0c1c0ca2180840c10898014100d0701107000540042c1c002146510602480510300550b804580c1464207080800c42d8441e445020100b0215001d80001c020030800d005c4e26014030102c003c1580c900c2501c01c105240d49405030052401081c030302c0140001030768030200c0f150450f50f000351510f03200c0399503440c508043c000a5100c0c0d1111801c0c5500d2801100507030f8024101c0c150129 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 976897311 1250 976896061 976896073
    0x9040812060603011a07060b030607020a05010501080a02062d03040629060d111201240504080a0f020f180702010b1215060d0803010e16030e07050f120102040801020c 73
    0x9810440b182c80240621801da145040040b241d902048010301072184c4116008a00d4002d4400460b20300300044a00c0030069000e8803002c424000c2c01e01c2041d001d0b01085010380301e4180c541c0c0100d64144500700046444a540c444054152030840100c01419901e44a540b13540e800e0a04010b000b82070700c0c0081e4500001c03182041e0003079039010100c92505c0e240181040b800e090400e05140000d21040c400e03c500c01004001c0110f0443c0890119400f03022610140588800c00c21440f0940c0420940020140107040106100f075000008014040ca0f40c0090254900707941c0340b01040812428092164100c0035004ca502c1c400021607042502c1686643d008101c905400c1c0100001018400120411600441d0085540c8186074108584c40303100a4007800046c2d50039030701e911903940240d0000c0c0b00c040042040c40b0f6401032507801d4003030914440c5800d00807003182e2111035480c0c428034891588500d440144d07074603842e01d8141c550307138042c09038100843d02c0d0303591240d900307020398020881404c0074015a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 976898561 1250 976897311 976897321
    0xb1521070c290a02090102100f150f0305030f130801020a0207052701030809011e02010b0114121303090b07050a0c0807060807050f040302041a041104060c020f0f09040812 75
    0x1e4244044640321100e00c2ca807183e280d60054200030b611003000b0310704500428604103007403c814040d1001e007030110f0704005008103401c41c00c81c07180c803115040074050b140c60850130804500000190784111124100099590007944410841814668000480c80d400460000300079900440d409044510958201c034010649400201416421103000307582010342c2d50050010400240c0034019030281810032000c0300c1c0c0c0000c4006030b107010f01700740080107079101d800000700303568844980e14408000b80310442c105500c118454100010003004100000a03080c010b60500d481202140d00401d100204a0343d40ca041d070034600d8981c0360b00002640d4180741c0760310005812800180603030480392a83e030781c20f81719180d46e90f00312140e91001003240c101c07080920000c0301581c3c0300c0c480c050141c141002c1ca442c0c406a00d000740825503e40c3c2c0b441103600201448100521031b00f007007110301c041d40e0403609803150380c0504000994036000380c40501d4000c4806c10800081045000042503280e10040c0607400c00d03510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 976899811 1250 976898561 976898603
    0x1f030b0702120f07060506060906030903130e06090f130c06050408011112040206130503010c09080124060e120d08042f120a15050a060503010b1521070c 67
    0x780302000e0f44969800c00603207020802c00e90250b03400a0780100349504d0042003c000403a690002c2d41c01c0c2d00c19400000307030381c00c040c0e8034010050300502c8124214031440c80c00100051012800a0034009100c24003070009651486c1c5d04d5030300700c500d54008204000e00b9119036004106401c140900ca90702d6181c0390103603910811400036074003480080c2200389042c5d600c5034240300e65a0859804129000c00300030021401c2d680071301926800d003800f980c524504900c2d22041c40d0035901c0e025402607010007500c503010032208100c00c0c0798040c0e440906000544a45900c04a0b007490150003c410a0f4000e1100002c8025402260140624020506400304034181c007110105084020701000301100a02600703526802d045403880c80081c842820b465004c1101d4030ba0203510390103a40c0c0080340680e10350030044aa9128810200a00f00a034000c00c01000700d44081010745000c0b00d04424020008201503491202200c09010068100d045c0d81e0910309190b003000e4620040d182c0201c400d00c4d18036501c0d16020703076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 976901061 1250 976899811 976899817
    0x111b060705011b020d09170a061d030f031005010c02030d14070203030309060702060903031e0a0b040c08190605030316020301020702150921031603030612030903020f010507080d02031f030b070212 86
    0x7031040241c6188c10300365503180014113011920341c41c02400030344e21269400c0c041c4050b11a43e900d0031042a0303245000080d0008100c1540c00c0720b4180802e004100001d41c40001d03c44158402600703244028a1905007400624065270000a600d0f01c0008200140c41c1404102c1c4c03030086400e0b400b1a0348903210b1800440e01c0740000c450300c4c014440e0b03081403000400401e0b1030751500407100980010381c07042850301017019070b1203146044000c20751a030103224100600c104980c0704140350b4001007254a00f4100041d40340d10988601043d40604441c0d02800c2d95020740c100c950055008080c01c03030003507094682c120982c0152041c140300fa07105000b05105240c0110601134083c00100c05540307003800ca0420301d128a07030030362816000c050340e030140840c903040c0d00440e40000b50b01070748922141c1f62842c0f0401c0100c4441c500303142e0402606000725030008072440305641c4001d140210160b103c0e44d61030083c0c0e02d404048060080b810507090400024884100041402000c090707090324400f07508080b203146144 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 976902311 1250 976901061 976901099
    0x5030d0b400b010816120204060f0807030c020706180509090604061b1b050120041e050f01110c0a090b040b0102011a04020d0209130c111b060705011b020d09 69
    0x260703203007002a0711815545c154403980ca980b401d10881c01a02110110b040b6001500700c88040744881041d00c08194002007103030792008903890144919003214400940f2500980710300c005001c958500d520394080120000400380c04054900003184c03030708000c000c0e502c0b0029641030b1096880d10510030030640301e01c01103140c1c0140a03201c1010074030540152445407601180c081d1001c3d540c40325480510240c01241c150440c00c1c18043c540c07507504000042108000d8030f46041250503100404105a40301c1c01c1000300c12050909010f4032811079007003901e00340820074401a40c08030180d1404648142c1590184d00030380c1041e6010031001000c00b005a00b00e908110303900c244091026500150340c60940c008203900d40c81403c2c050300305280c810200c3c8503886502c03070061071a519014220344841c0d02842004544040c10003d14140750500707200c0c08008040e02c0030500640300041c00900340a0250016042c0c032041e003c03074204a03101104025114110700d0041700001d080d40d0710009510301c10803084c0b542c01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 976903561 1250 976902311 976902317
    0x309030b1308030f0402130c0801050f041a01200a030309061413111206043806040f061215110a0215090a0f0602040602150405030d0b400b01 62
    0x191074134640b03a00110001402260306c00c040c907203402e2a9000a010b0000250300d6910362103090350410b01000040407250300703840d0055181180800a0b030030030507810070402030f0a09251580c07114500b00202d411410301d4600c4454420749500300200746d1b01d903121740140740c084d5204200c45072020058200c900803d4032070821110100e03e890700450800000c030f82c00b001c2e004001c601131605100b00d5a00f00070084500382c80c400c8564030322144144000c9a51007056a600079680c20f107100010480d010080d000c0c240c0e0740070f04e55501c1405006401c90b0b100101400c40c0c640510718962035031921210345200f1851a4418a081401110441c01c80314281c504041040e00a0000102c4000d414508110001d018422901c200d07000c0c50040f4424111500c1014000d00015a030b5a04000c0007a14203810031f600a502000c082003040080751001c01a02c28000702c078003011610202c080c0024000b82c00207132041c006a2262040f492428261014108683c2100030f01e10540c1540b40341c15104032201d802d455408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 976904811 1250 976903561 976903567
    0xe1005040603032c150d0507081b0c150c0702181515130806090601150801180f1a0405060915090a02190c030e030d1409120a0309030b1308 61
    0x101000c04213030308420150040c0203041c0d907034070900041c0e914090140325800886001a40200062503400390540c002900d045c0101e850038658045030f406442448104459080403902a007050301c00e00080c02003441e0a584002e1360300f0092005d0a0551150100324400d030b0303802c6e03a4184140e80720b0070424440e00b13100030a90780c04100107060088840203610207200100b0304004540416044c011881c0213845114000d0555242038261140351980607001203088000d017000203080181d000e0495070640705541d000d4a40c400b600081030029000c0d03449120304c01410924500c0c003062100030009a00c1500316818002d88d01c4203000d206002005441c0e4949002c0081040b00181c14400c1105401c0082258018684021450102d4840821b011180c00044e032109500c2c0a155000510000e1400f04401600606900f0500031b059504840024803040724003103a0381c0b40640c1ea50344840310300c41e1340b4010740e950f006c41403600406458a82c042140c0034404040030074460007043c000c3c24030059001c1c1450749 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 976906061 1250 976904811 976904837
    0x50409470609130b2805040506041b0e06060c03130b03090706030e07090c050d140a0b010e091515030405010c2a1e0602070609060b100c021e06040e100504060303 71
    0x100e040302d00c5600f40c0c03d540c3d9201917641c9122441818403481c01007000d00985c0c105442c000354000e00030311401400515120080c07201c075000f40d41d056044841182d04a50303035588082c0490441c021401340860846610b9000901030910000841c400c0c420041618074840c0c503050706808644294074800f0343e95020034001d00c00c2018035030084d172860380e40b030400c2030030080c140c031640c030603a400000300c0d00c10310040302d041c4144620540100b410010f02401e181c8126003400f40440c0009000030040c840444040025030b4441d22505521010f4107141088140d892601d4144240600b01602c08800051542c05c0006e402d40c0c9461f480300074405010b500c045111401c0d40301c8185000c20191502c000060355442e10300015600d1000300a81c9201e030340c000c0b03940303e40c905101d005c6035092603c06004106a10210201d25070005101079140c3e4100e40d0031410401c40119408040f02030000e09401403070024000c0780500781071410b184900c0a913084181950307221401d10055800c5440000c0100b00b1900000c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 976907311 1250 976906061 976906081
    0x10c1e031704060b030d02010e0715170907030512091c020a08070b0310090603020319080d0912020d0f090e090f0a140f070501080a0203071107060309020406050409470609130b 77
    0x610301d1a03861901e4000c0001e107420410840330706035149503c2d07912208040081260038418070360544109685141007480d1080842d00c1d441c4207107001450311a500c00c03100e0442d540c001d1028098641542114403060320b40e90355226a60054440a61070304403120f0004101c0700500030881540e602a0140601403207003c561800d0411703103d41180d88042c280000003d8406504c902e001c628000c102e00147e1400fa9100a82410300d5082d4880401c1030260b0081d41c180e030844011000c4a405d044c00701d9141d44d0342d0303c078141016450340c0400da0030f020782201c1c4000e110b5101c0400c0f010210020545840000a109140e601c41041c8191804111044000303900a022903003e5a8010f40c54248001d00409440b500b50400c9007542285001c02e9032050000c0550030b291081c0c40242406840400a540c520303200c0100b100d5051496079030711950086043d0381c01c1e02c903a015241c9001c1e072660b4100304840ca1094240e2442d0b04030703107450060b1400000a82c800d61105134038207c0c0713600b20201c008140c90b401010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 976908561 1250 976907311 976907339
    0xb03010e0a08031035060114011809111c050403021209030c03121c0905070b13030b010f0e0901050403082703030a020301060806010c1e031704060b030d02010e07 71
    0x1d1035500c2600304e000a00000c0344000c1805140c250070b105221201001540c001c40304490141805540000010f001d0f03ea1800380081c103030082424070b0107800f41030001d0b00c90110700c00d802080b483c5040100401484c107145000d81101e21090907803d00d0b0700980f41c01d42e8120b81044902500580c401d00044120030058401000401c030054281c440301e1b50f00c08046860700034101030b005950f1a0018201c82429001d070011010854410f10500144020b61078280d82e5032514080c071000a84000781304030b031408000308120000c0d6401900d0103125a501c0801480103a111312031000c0c44869040050200340c1c042c42990b105503455100d00840752100400300c906000540c0c0020f860205040b0418050303801040954400d8401120161b529810500020203820b030242c151810b00080c03280220008145425003003240700c81440001034011f190400f207802d944150b41915948600340305200c14480d06400200401c0019021103000d0f4080781310490803544124403240c0e181c2c11441045c40390366075072458 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 976909811 1250 976908561 976908571
    0x50103170307090e0c071a06100f020c15040f0303050a030f02040e16110f1b0a0b040b0c0c041107260d0513020301050108060106080c18092a0d0b03010e0a0803 70
    0x40320b007000070703c0d44e0715030107607d01d5065804800c1c00b6104018003441c0505c12501d0004180c6041038076011412006540d444150b40980e2080c0034120000080759108026100101241405409150b68070b043c060702d150f00450791000000d05100c0380c90480c40150003154211450181c3c5249540d940d50f1540c0102e00d89440e00c0d41c20400d00c81c9c42c90007144c030300f01711405540c01c03c10090300c0a03040608000c145001e5000c4014025801c0344810000c81c8006070550341103400510340c01e5903642401050506200030740c03480d00d600c0b51800e4545944002030b00f02402050303200d880c825040302203403601030040d045241201030915504000c03903556485c80b0b40141b0340001c548800b4a401040aa00280c20744800760010100c550000004011499000f0021500301101c42d032598a084011040e0080c01013000c10514003035200d180200d4280034501d84000e001c10b40d0324480a800101c041e0760281c1d00e40c01543c414403450305064181c111864184642a0801d80301402028010308030740e6022803a400040c6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 976911061 1250 976909811 976909831
    0x3050c070305160b15090a0b01080c0a02011b030c110a120c0f060f0209090c0906070b040305090409050c040b0f100309080d020a200114010308090a031401050103170307090e 76
    0x2c00000001c0d910500640a00c0f00e04070612003417600e803801c0c001080c40040c035580c211400c24000c40703056600940d085400841011280e40e80d100140d07000e9014004c9407412004030b643c0b2044000303403550306500c090340c4c0d00e51543d00c088640c070040d0301484e61000103101c0941013050b01e200703800c001c1d4050000002d1842c4282465052102e1544500c01150528403000c5091900000c102e100c5142c441032142c0d00c80b00d407250003030801d8400f0000c148a0301903440014038040c000404a4107041c01441074400402000b401400080c07414504552a01130704a5814001c1c0d003041a16030b01c42c034060340948030128001d040c6090f0b8218000c01140a0440010700f034401c9501003080a0759540140001c00412a4980b509209462003042070303100030f140c00e00c00030220791500808065405c45280e1040c116a0049034990b160039450f0300184039001c1c0303940018045a00400e141c003000d0410f4001c20f040700d0041403a8100f07032182c280140e429200032245600014544142800403c902420994000700030308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 976912311 1250 976911061 976911097
    0x105160f0e0904050a0b0603060c030114040b06030910061205100203070917060108060c1206040c030e10050f0f0108030a321b070503030d09051504080409050703050c070305 76
    0x101c042070312414192000c0c0d40c1504040b005405021116003000e411035419001407003145000c800f009558001802200000e0030804522080d960315034100c2020054002c1c0843c0d80c03814240d0120343e45203290030906103600e041500c00200000902e004c90034481e0020042d02c81c5c80781003000ba1009500003000c1d4800d1000e07015010800950b00700864103005102c000034286c0754185841c0601c0d1400c02014243e40382000c1000c0c1000040d00118903030032140c01d07900450321620701c2c0003e4024091501d5003c0c407500c903c03100c070002200683c00050250f4510070341d40c0b00d00d45420b548280c5080090145528940c020003400806038822030b8006c98030716032280356105501100f44500710064561082c82800030002c500080e0703140000c00b840240301d4250300106089072078100429224041c18a0188007035136180e03007003814000180070691944602d04c850b01101d00d824034142d6042c0d00701c0d009100074a8544000107920b18001e2044a000c0c00b0808012814124155003c450b01d0740441c564440e110204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 976913561 1250 976912311 976912337
    0x122114090a0f261b1009180903170f01061404030204060609090c110c041e06030f1e03090b0c0a050f0705030c1f0c02031f050f090105160f 61
    0x11118400030f00306984220000407a20044240001641c0221000c203810540d003c00b141c1061000300101c0703030f40036100c02803100c1c8102c0c0103072840002d50b441400c010a0540d250300790000395034031980e0400e02c01d803500141400c2c040340061403250b044030f150510811640040c02501d0042501480c1c10301d942e80d04514180d00d03580801c05540c2030380e0181e0003043e0b4a5406001d0014030307009001c00884140b0b0080b03040f00c2e8541110b43d8581e9904030303040c05542d0f00c0d45002d06c40a4420164507080c48070840c02d012440d540d103800b40c0f6003c45030409031001d001202032000102d1035600002000740d090340c2d80c0c0c41c8440c1005140c406543c405ea90301149403044c1c0b110203000a4040c00483d2401220001400800e490001030608004030190b046104000c80319031010250602e1103200c8401c60140303000002c114180c03000ca031402005201a050052141419040c014190b802803071042130102c0d60340d840c90b12000903090a9660546031060440214640c0c0703051075202c1c45032140c13184054a0048501c400b8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 976914811 1250 976913561 976913579
    0x204140d020303070f03090e33060705120909010f0b0403231006050909030a0519090b030a020301061e0e010c0305040f120b010602070e0408090d0c122114090a 70
    0x45280c0c12800300314607c10170400105840e02d410f42c084c1c2541c5401c400380c0c401402c03240c04072601502a074140d0071805c00314103140d227418090760b11482d1b01004842d120605483e41e4101508801880391007001568000b207210b441040c544c404a4600e41034642c1014150b9a640400d040c0d610555910000394021000604800b008481941051f418000940c03c4c03c1c01c0601412903001001c1c5c04041c0e104110452540340d0290440e02c02c100030b40004055102c8110007110601e20552080c40642404400d1000a190f5030380158104c88982d02c40d1810120b22809900c081d07a442c0c0e0074500403c1000e00b28440e03550050010000d024801c0ca4a0ba03d0140c56060746102c032800b507001803080301c01c0e050030f000401039150140303070150256000901c1400e1910074806a0004020401030103080003150500b80c036141c5404410955501000c500700f02c03619094800d80c0c0c0842280d056580c844040038841c001c2c00e0814803030f45115650b68803e9060b4403901031000a55101450564000440b20300005a10031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 976916061 1250 976914811 976914833
    0x7031d04050414010f02161e0501140f07030b0f100309080406031d070f05130608030f0306040c1d04023621060105301f0204140d02030307 61
    0x445a140f008440c24107003c01400c403030702064101605481005039100400030120204102075200481e0300740d2070400e0421500c880a072040c018803030b42c24003210351b072444940da141131701c100c06110714800203641d00030048060f603000e0700000b60805242c034080269030a09521100503c003440c100814918041d5942410b50f500c0365218000103569142520406081e01d83c062262503a54402820414140340015030351100740c5c49110300c070301c048a400d50034121040e00032600034000c8406407901d903002e0510040d403e40c411151107100c0c42c82c02d02d0401076240940111009445580c87c058462001c034010b11009600881c01154a5100312002c01c50b5021034240105124540103046190000341e541404410719020362251070030342950400f10740310f503000102c503030440310211001c4075201900e0410f154654180542d1240d48143c2e6624480c030004001100c40e005400602d031100300d21b00800da403078201c2c000d80c01100252044c82030303d84007915055000c000f419000130b040d02e1621040b5034800d40140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 976917311 1250 976916061 976916063
    0x270a05030c070506030f280c0e091e06090603030d06121a01080a06110405100c03020f0f072603030112050705090906040b040303060b040603020c0c01031107031d040504 74
    0x10344002110050a4001c0c0051801440241c6685066040c9084511000c002c000e14a001001c1d41e41d207042e086008018440401c105001001c200c583c0721201c00802c0c500b8014200c0d0301401c807180229210700d0711000c44130140e002030120400d958440200f080901c0b00e000c2c10095041c0b005018120803480346103c0c0c0340c000d100c3c03050540d015100910b40400150440b5180c40e23403000490004002e613640105410710426030280000403600d0295000a6039030069400068000c040d084e08584050380142090800074040d170216601d10004c0701d603499440c0500f15800c0e000b03401c100010460044141c044170302005034a001080f0184c0c01c080024607680003640014011000c100c0500107120781400348034003812041c0c40c6043e03503242036802e0303544da280e015200030221442d0200260074144aa0b209001510314481070320b50300d0359900323801806504204d8002c0c1c582e000740c0c0140b030b00a41c060f1142c00d200a10340030700c0e68105007064070700340d031549603103c4480c2d07061b03203508540e40583c2d40e2403040e20301c03031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 976918561 1250 976917311 976917313
    0x18030415050c0d0c021804020114210a02390f0a0312110a050304020f060d0c1b020a03030f030e010912080901090305180414040605070206130b270a05 66
    0x80c44403042083d18110080300e0b07840a01c0f80d0602100050703101c480409450710004060382000d61200e1004a450703c0e600088a54540c04c00314000740c2588050010603990180c140002e001c9407140b200c1da004130f00c6990303d90070b00d00c00b100c0f8074030018140d542e80c0c41c0c03000300402a40101c40041100e21908144802d01046001d40000c8818800c05400c07902c10a003c240c3d04204200011418040001512490034a241400b6002c030028085590f28080701000503806070001e9264290102400d01070304200d02d0b0740c80071a40c4030401c0c4074403034030000d038004650350010451400c03d85952015103541c001c03605600c08042d05d41003480700c034010074010111054400c0c46007600540003510000c2018801400307580640e41000c040c074002c00d6201066446446085400320203030855240000d0051110245a80c0610725180030401806099400300b072280080c3c1c0c081da01c265842e80003100d03420321440c6000300a4480c42d40032901e1115401d00401b039100b006008a4210406001c2e1140b42a165140407251 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 976919811 1250 976918561 976918567
    0x30d0e030114010e1618120609020a03080307090b09030601050d14010c02030306123d050c03040c0b0319020d06120c0303020c0604060e06032205010c080601171803041505 75
    0xc1050048100e1040051038035044021801c41c106c40c601d003405c0e41c441c03c41035070780c0405a48140400b9502c0404810350091582101035034030724202c10690421108900807030b11902e00021181c4200c012142c0e140b10003000ba10060382010308100c502442044140e60140c3c03003109071031268030240301e50514120560021904ca140040c204640e240c1d6070080450940c000b0004401c45400c444040711180c140c1c5564400340b14010781d1041120b252499103000414200010701c1612a1060000c6001c0c90180c20220301941e20707036070044454031081d0380c0400119548080854110b00960103001103040040006c01c0c031035a140021200208240c00903501c0403801d000c01c00030141c042140010200c030944600d81802e19114000c0c00e069a083c10850040c2000070000b042d00019024201003030b4000030604c50841c50070306119008002d40150100415403000114071158000e450384c032511b841104142c0301035521b26411100300b03a01c0c88501c00341803006010100f10718400720100714000d0140e90703810b91 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 976921061 1250 976919811 976919821
    0x210209060a02101a0d03210f06090605030c06041a040b07030e0f0307120f0809040c0c1104062d150509010206060a0303141b03040609030b0f0105030d0e030114010e 72
    0x401c50b5a49180e44c1400c0300d8a81c0c404505803a00c441c0600d44c15014100741d14183c4da062200c0311481c21202511008130724000c072124085d8035961014041d01c9000e68200032054961040c10764800900810b558000014041086900d00d05038032120b130301c03540316138280c1001c1c1c0e10340c0c00b162190001e900880200e2805c100041480c146240034402c8140c1c21801060f06510f000c03041480760000c0700d00a0030900c4181c00e80014032607610200c07041e0103800707041044002c421210003005908910703400c44500010403000c1225107070034007a010540302a480e01640a828542182080d07040d0500d80e2501c403182c0c29400500a0099001d1050451039a129650f035069903200080c207080008155a00c6404209414000302c0d40c008210b4000c101c0c03029402d55a20011100701030845040e0000e100c0324071000030003003905c0754856946401c0f01e12401d201c507059258001c076100740c0c1c4002d000d501d070140e01064408603080d00c200d42903010080d014cc000190040c1200c00c98003200000d0704400d604440071402d000b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 976922311 1250 976921061 976921093
    0x180902040501080a0902060a030c1e081006020d0207150e1806040f09170c2e0b06091f0504030f0b060111060f1b090607060518030703210209060a02 65
    0x1e6031104c025001000040265030029080c0e004000720901015903441c034091000d4094a003581c02c10000d021001c4110800c8240140301d804201c40504807994010400500780e4000203400c0140080794000e0408981440d00d0034075410341240e019410000c1a100b429055100c0c0101442c07099407064a40c019403901c03034184400d54070f0803081c0d01c104034603003110f02000c01c3c80d60860049139011103190998415030030981d540f4003180c2d0342101888201c0300740c90500810546240f01c1c009410b01d6000d0200315809001c004860151400054002f016950f401c0c401140304110b00300f2051340d5003800c40c1010f4890700c8551552000507002c58070546c041007804800e40e004049900c180c40064001c0c03200b40b600325440c10a944014140c40000c03444040c0c00075000d220394050750300e00030015024649940030350418030301610090b40e0f0700254051500750031140079000310450b6146501341e01d03a0210081101c1407507030700c2001480c403134480c03a1b0300303200014075507403000b005244804142c0d0003486941d5104d42d0762 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 976923561 1250 976922311 976922327
    0x80310060f14070f08090306010e040515070e090403020f12090310020a090e0901090b04050d0e060906041a041214100510061b0501020a090303170c120403180902040501 74
    0x45414484070981d4102c0d56244201120802a400410b14441c419645031040c0d82d4021500d07000d40c0f5001c5d11001007503c2559911152050703000d04101c411020072002c80207180f06017612000001290049450114141782008941040c0300380b0403203141d8401702c01c003d0708105108180070601000090100201d103070401041c14402d03101c10086181125101d00030300b85003c0f0b481406448400c0b00001608440294015500d0702c0d0040442c4c08146000d28159440d4000b00400f000070400401105119060403001d440e005200500302c20315103420190a03541e890030001c101e02000701c0400010a5002c90160400da01512030703100c1c1201c14029582050501112004084078a49040c0410a0410342d001c1d0701c0302140c009041c00c18a1441c800c505d03210480c00c10b03001810302c1d80000b4510a000f07074009000720480b8001d42c0c070030500c0c100500b00340c0ca800d401669000620441440341190304500b15003819041446802c1401044902a074586198030040d4007210b40581d010804214550b0070401c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 976924811 1250 976923561 976923587
    0x30303052424030a061715070c020f060a020303040308090109030e0d020f040e160e100303140433020a1a060f191e030b041e08031006 59
    0x1000d295544990481c1407580d00c9030079a1107081020b0081c0040300b03400d007045a0182007496090707601d00e08501c541018201c01d1040c00300d4801c0c8552507a00215000c03072001448400840d081c0b8841e1a14032048855260043d026a03000c52610790325540c503512680180320403c069000b43d500d91625060103848490000d010034201e904104404000903072000f2145032034802254036256008007800440e02000900032141d0304a445c1404043c040e202c00580701c2103144000340891181c42e00d828024903400800d49009818802050741400080c1c002c065910104441040c035500b410783d5524007040912402c981200941e0000540c02110300c81d01001507005051400180a001c8440c0d460381030000c900051003503072580460100f0300640c1c0300310051018003802031100c1d0344c4000301d40c00d0f0400201c40344150210441103440051104a01446c5842101d0300700030308803031a9407a501d5244164002c40d448404912458104000003001c140146028405031005140c2103410400003901d101d8555103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 976926061 1250 976924811 976924831
    0x4050a1229040303050a0b06030411090c0711150c0613051b031027110f04150e1333060b0a14040506160c1208090405070c05011503030305 61
    0x300c036070980c60400c0300c103a049541450005003903500e074132000c0014520368202c40d510040c004140030900500003070705100741400700d90441454485090040e03c512800b0001409003801d9459003000c1d261000c1c0c1c046807840f001f0300c01481c04541a0300641800804c80c0c07081101c8a6100440c014003404020301d800b00f402e071016081c0038207441070000b0b556044215444040035151240300442e4190700304040c11020844408800500c1d40d450000c0d800414030040d1800b510003060315209602c2c150150312034440044400c1c1094500b007149010b52024001e00300311a0801940030400001c104607501c4c2c00c0080040b40069404140c017a06900b10b0007855962800030f810a039050007210806d004403030f0080e45608282c150000d110520b540030b80511b901c0142d00400200302c42602810398004044440d12840e5020851a12203141c40501464002c02625180040c840c501c01800e0640c0310581024071820046e44151459031003e09417003041d0050040b1081c03c1c1010402c064050286903000f00302c4403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 976927311 1250 976926061 976926113
    0xa0606030b0d060f06170a030810140603041b03110306160801090b03100e0303070f0216050f010c0c0306020d0b0402031e1f061d03060603070b0d0204050a12 69
    0x2100082e048040c180000d407100c0c1d40c03a100400c000009a02070001081c502c03850b40b440b600c0d400905900c65000803425400324508900003135003442110341d0402900e170100c807907d10b03501000040c02020740000300b084504840748480c0c02c40318140c0d025913100461107030442d0a00b40c401031060600300701000e00050804240d04078491070302c90300161070314152112103400080d140c0d080400a807074121040341f02c0540d2807401141d4100044040019071080c80344d51100803403020b00344801c036a1000104144040200311010500c82c5141c1518210100300c014541041e6280781510b950849401c140d1003155030b07507030008101c00c10903924059100400b10440b411805d511b0126025070f100c005070700608070301c400443e0014401000103c44805202c074034016030b40d41c1c640c40f0310300903007052100b07a00c9020b10112400c6414403031800007041c600c00e8401402a101c2e0600d44500c40c0b4181c0c1001007254002c1d0340900c40800e0700d0301d038484120010034404101d455541107a0400400e00055885460415134105e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 976928561 1250 976927311 976927331
    0x902040f091502030712110409060608070c08030a0b18070e0d0519020d080a020a02130c0f0807020304120c090e01060b0301030308090c0a0e091b010c020d08160b0a060603 75
    0x2142000b100380c442100c0160383c039070700c00e00112101d24860045007800c40c07414180c800204c03480c04c0544180da5a094080060607102e03541038a10355070448851000680c43d000c030100060660010319000358282501041411100c00010b070050042d03458100d801c540c0000f0000c64a605c0820aa081001510384980b07044017a280c00340c0b602d500101d00410300000440600454036a010722080e0715030010701319034032030110040003500d414070003200703901c92510009503001352400b900c6440c1e080d034000e8840b40304c60400a001a10104c2d0000c00001c154041800002022054498442840391151035842d8400d4104003420081341c0d00401c1c41d840c0c40c0e2403e4028010850100103c90550390141054102a40c41c6059545420400101550001d4044100040301100985070078002c0346501c050341d60010400402000000e01d02c8113180c00a81b1100d0500058109150048100c1d07005960325883e00b0000034643e4082c81d01c01208440680541d4100004d10103548515070240509142c2400b00d181c035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 976929811 1250 976928561 976928573
    0x501050604051c0c030507060809120a210f1e181b0312030501150f021f020c0f0c12010b031e0f011a2803080f1201090902040f09 57
    0x38a01507540901c2d41d00c502201010f460000d40c560840e03006140d080721645a240170f81e00c0e10303414460900402d10301401700c1c40d0050042000b019586d010280d440c280340a00000300d80785403408130381c0d00c00b41e922183c3c0c10070011140e004540c203020034403401081e403030441c600d02110030181b4541c011004e0f19001001c0120804d4002c10042c458004485400ea4a1100c42e00b6007044031310b07071006102d901d01e0301000280a800da00907034103d9040300d46520700c05c84540700035606403000c00f4050740180c00a40026201c0c0a0120f00305441000c842da00500740840e44100524055442c1c000320140d80c4041c000c00100e24040c5524007c4240d01d000070b208000207640466640d00000c0d0481d41c03c1c400b2035242c04680f24003001004402d078180c0c0004d001d609141e0f003900310790720070b42c2c1403950003000ba400c560011044000e80321a0516001c0380148012071840c1ca941016070440d00581070100e0080182c03034540a103d0301500c0c040d018020000401d00d00520410044401230001400d901e81041c2c420700100d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 976931061 1250 976929811 976929817
    0x304020901171204060810061d06031b04080105060901170c010c080706050709050f06040e0a0b0f0d080c37050f01090b040501050f04020303030c130f060c031205010506 74
    0xb102041042601c5115082e542c00d007101c50b1941a070700781e4045000210250302202450041074510a40c01c02251125400c44030a2044095034000041c80e6a10f0039250030714100455014025541401101c4090501180f0590044d40004030a80d156000d0011070700d040d42e003060051070f0000403032070900e204c2d441d495118015a06440d05102c0200500018000401c0455204035845001081245443e02024010301030601a29004820880705e420349400c0c804221002d9800030000c02820350303208500c3c1805070585800081c1c0221007080054065200e03281c0140d000d0388103015054590300c50b00b503282d01c0c040410700b003c2008805800702003010300704880c8a803200c0036228081d085200302400c041c2c0ca81006000340e611300358030700054803007840603611040740500c0c8124000e100c0c503210740ca4140c0c080042a00c1c065030541042000c02d00300c0020000a00c91601a000d10020466035105082c0c000e1140754841808507803096110000c0683c004c421440c2103019540030041c0354104004540303d40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 976932311 1250 976931061 976931069
    0x1050f0a0c05040b190e010f0903240c0804051002091f1106070c021e0a05130b0405070804030e0306042604120f17031902071406040b011a0304020901 66
    0x19075641c4000318076911890884000d0710701441c50036a140810420700d83e00c811041c00c410b00060408071000c0640d8420b1170031640d0329000b0b9444070207260441d101c6411030208040c500e605503200704030114407940b0300d00500c205144a82c661544510b403c1c1086814291004400701703039144100162180c5907640004050301c049604100c5520301c03030611007612218180e600c4c001030b5102e013108104120742d0000009240038800d035102c18003484040303142495080d641c6e500c5076010102d0301c070a000303604003074a00d1516145135190204d5000c9046010401710356080d20400d000810050400c0141a00080c50f07082400007980181250314054a607202842e803c82605004c5000c1c000d43e1040402e0106e003500c015108a080388111300c4d015280980070159103600880380d03080460f000500201707001d000c2d40d21490b0085041003c0a10b410b4041c4004d41c0b00c58001c6650700c00582c43c501459404014440c42207104103000c0aa0b941813010a440c5103186004d0000e001c03800f04100401170300d400310301078119 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 976933561 1250 976932311 976932331
    0x1f02070902042103033902011a010c030203120f040c080309010206060603060307050a1e08120301152a0605010b040602030d090f0506090d0e04060506091302040b0d14070201050f 78
    0x1802c01d91a086001c0d10819040c1c00c904446c0e4241c103906030303900c0d450000b140c15034802c0240c408116501c0c02e900b40d07981010001895a607459299000f9409103100b211800e00c0781c8180d031700d043d20807005070b180050260354260f0000c074004c080100b005042481007001d001028000c0d4140705040d00002c0d42ea000040071140a060084041007440d1410841c90703014010051010b6141c1da1140c1101a010b218442c550b6038449004100081c1c0c00340101380b10407218008043c15286070f0900c00c10042c0d80d07603040303159010001100b041003c840460030800001d81810783c4003020011903800c19400342c520603080f80600741c504020070070010b40c000088075200301000700085091802c0b800c01e00501c46003c00c0160807800b964042141d1420080f0350300780080100d46a0560305d90401c82448203d42c214082c00760421410041c40d043d91806d161201070758181250054034042c2c8500c0c241c034040c2c0009500034034854580b10207090084100109a40c0450544020000c038a040c464402000750050211811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 976934811 1250 976933561 976933619
    0x30f0609080d230604020703080c03060d0b16121b111009030206180d090504020c070b1b0106050603060f150904050c04051e0619020a021f0207090204 66
    0x42168200c02e4854880b0048400c100d0100041000364402c2c800d0300c0d040c5401a801c82c0000c0a0f8074151081c3c0b07076544e1701965030706229640d80911400d039031b10140c60941d2050030800c1d0980040c4144002920a864044417980140c4408030702504078030308450413490b200d04000542e00071403100c4002e2100500748c2e180c42c2c222001304401740b50601a0382c0700f10301200d5060144503401d050300003074041d0190b4440c18001c2110314030804000d45986421294400083d00c04504205500d800d4010b0080204944281c503078507a55004031103c141c0c41a446a40c1c0c1620714030070810b1402d070a124000041c00250703405482c500d400d00004249244004c107903403140f03c4800509181ca42c5410a503100040c000c1e1080040f0b06000101c0d110b5074215100d261311981c040101070a6590b02e0b02c2c0158507606000e0309441c10150842818401c400e0342404002c114414500c01c1c82c0969103140079010960f8144001c6c1c000807118200084c100445500807501c1c0a004000c02c20403040b001003101c1c4e41860107051852 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 976936061 1250 976934811 976934813
    0x50c1c0b0f250c0210021f0b0105070b070215010e09010e060f0705070807050106030c030b09030a021507031104090c030b06040f0302010507030c02060c28030509040b06130e0f01060504030f0609 85
    0x9954400400203500410002c25000400344c0004500340451081080b1590390407e80c0c0480c001e40e0400003281d400548107000c19400074000003885900404140195400706c2641d50010021500c240c1c45100c030704540400b40709110a0070b11a461009195001078a100c1c5001008509290400341c2003004115001a180c401d001c0fa03401039880240c1d2280c028000b03280d5a042c50340e10b01c21140010386d96410354001003510350500204503032544650707070080d010b003d13000e0100090b4260000c02440c14580c403001c215116040d0307880204064240c0e680002902d041040008045401900a05006a41c1004140140c1c6040702a110460b542440e0150340d407192850215190311051000940240000c144001103445c08a030551003d0700b1201c3d42d520f85450203126120b603172241c850180105000f00300720101814550018035198002810b42803405203018142c40070001180d000281c000411002c1c403000c0480e03284074030b0050840f850068145070450704d520745031024070740340145102e41e1800a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 976937311 1250 976936061 976936067
    0x9040b040609051c090905010e15120d0513060206010b1204050c0a0b09040507080c0904110c030c0303070f09030b0c0a020f0f01021c091a04050c1c0b0f25 68
    0x20702c0b00340c3c440c3c15500342041d90640510402c0e55183d201c00413a40710000410505c3c0a071045134100c0d09065841081030319040000e01e001451112090b0b0090418440c0d411995001c11034401000c4c42c0796200350341e44002d400e1012118009400940c2150030441c0104860080503003034071098001580c0c055070544840c40c0041c40c7c141a00500303a0085000103000807904504d2000e0400114146e900384469510008100c5012400312000d1400309010300000314582400c0e44200802441c1e0b102d554600a06014180c0c40c54118064036402d43d8000000c02506070342c40910301000920b1400c090010500355501c01038055002400e83c8200d00001c58145d008034070030000d85200000340c1060300d440c1920046070314080d50021420003d00c145d62228007040c03280b14860319000316007000c00a04040b1444582900544c00134205480d40e105640e64104180d50320f45120390808840c1c4c403403440010381d502d80440103407070003029084d0200304101013080900b654a0305081301d001d8500729540c2d140740d0090039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 976938561 1250 976937311 976937321
    0x4031a0a02160b16020d05160c0e0c0702190303140723030a09081c03020f040b1306080117071403150f0109050c1905070204090605041101140909040b0406 68
    0x181000c190b103102d0103110310300c2a11402610344110705144111003d4041e1782e101c40c00d042c0840020020004080104280041609032034403422000d14800e954014428040c042900c0314419032000280700d000710320b40306164109031428409200d0b8028a580c401070649109150074211507031000880d9410010304400c10680102450040310b0701c1088040c02d03d0342c0e5040301030380d500802c0101c880490f494200044015221902071480740cad00410140d8128080e400c20144880041010b0101203812105140503080344040100088440c51804400400100e010b0340107440c1c1100e0081d10b10781c14000803881c0c1c010b0302c401c00701c884241c6500710003003860450404502e4900c08040028000315031401d80340c1174120b42902d8000d00c00d58032609490350b4544182c0440c848001d00300e81180d080e283c0908050f080d0980018000564400b16440b20806c0d81c00c100c504550030450103c07020140c0da0028203821446240380e0034035040501000c046807100c48040c1000d41040d440e81c00140c2000507940203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 976939811 1250 976938561 976938577
    0xc0405040c0201090605060d051e031c0c02010b180f04031407060f06060e03070303110703021509090f01261c1d031612050f070f140604031a0a02 64
    0x8101079000340100900800080d2811240c0b00d0506c00441e101c0d140a81d211450386400c4030140410185456007200c1d24514000c001500f4001804050307404010210f100320b803403401e40c90102e91016441c030001e0854202c142d9940c4070700c020642c1c21720788001d90b0050340d40c021403e80302807046071510305055610805030321002500d00030000e108000c020207034010940310380900e2418408207031140c00550300b0104070b5110f540c041d80604410000b0902c00c81581c40c0019034202910359840e00c1c1c0d0003184071011008800b510a0800149404403400d0408407240c0c0400c410494490b80e505000007000e0b440b02d1081d4070044d401c0c5e44000740640610a020b0310907440c5d04400d28000c0740141c020054403100743c08401c2040001035100321810303401d002c2004422a090021040409820a0f54212000300d201500f40c8030f0744901d4100742c2c07554908201c414080c0c00d10121284045150043d0724003580745890758540145d50a01c0100b00091484010005c2a061140d6222065549042401c024015000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 976941061 1250 976939811 976939819
    0x70606050307090f0f050403020309090403110d030212150105040b0a09050d0b240609121e060603010c0e030a02011b08070c1706070801170703060608030d0e0f0709050c0405 76
    0x160010f55200c06501681500f1503540041c0001c1380103220100c11070b0402ca074041d01680007080340b07540030714107526401e51061280c02c290300680c207100c08003464201d4084006001c45c1d070000c1c0111b40c8281383d203160350b4042a66014403019940e4000024a24000d5200f1011004404100c1801716405185000040c24000e04035411408090a01c14103943c401c1d2417201e400b540c2203400c102c811140707521088007101f01403c060b00c0c2114100c00d11082d00000001210303203028000f0070001c00e501e6001d000c1c0e80001024010f00403070400c3c1041508480d1001c0e001018855000c441c4002030310702060711502141c09080c81548810404031585881c0159000100403120002d0000100610195030f4001e03034151941d500c0b01e80d041034410b81c0d55502c083d5000b80c0424151401045129030116034070031006101c1c03090302c04660340c90303540d08240d5000d0340042c503407500049002402e03148640714400c1c9996020008051010014203540c0d1174042070300605000c1c984810014203101c256904440007003401030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 976942311 1250 976941061 976941073
    0x12030c230a08180d0308160e12060a180302100c09081608010518030706050901150f03020306060621090a0c15120b0a05060304060e010c0512070311030a020706060503 73
    0x11505a00951000c01c051035000400603143d003040c02d1103160110404e9040e11612241c3d00e407403103195100ea00004240003046104208582552510070002081140031801000c5134142a28020181c400180404000700d40307103c030410100e07a000840b050051031442c000240d0804014003103450030300c2a00142d500d4898080d60020078640b00b0f49103c201c9882c171000708825200c04203040d0350410203903015526503005010040118040351b0045401003038001c00010b1b080715401c054a04019180d014a90840c1c03010000c1055080a000c0780780d00c1541199001d02d040503400c1d0244411080f48c00304601780c4510000104090010440e00101581003400b00358020365544290348007004100c19040000d5003400d500a0b1a00c0901800744158030081c9100b4480d0706180a00656400080068614a17200e030085600b1030800e1203981d400b40865a1080d03910320007040303020b140300400341c50700c01010301d0f045910400800c5401030fa138000e810010003596441c0e660030700a000e001c00303401c03030b0340c4c14007443c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 976943561 1250 976942311 976942313
    0x10302250501200c0705010e1003050901060504051009110f2203020618030d090503061603240303080906070c11042a0f030203060f04020705070f030f0b0112030c230a 73
    0x1502801c8108288005c031522a44c841d0011580a20b5201c9265004218081000d1213607000c0d40003564000648000021416552400103003625010341e030f01a91450b20b410240131042c410301074801d5080c2c60084461801c03c4bc00107009051141c5044c1101c000703180040001e0b1400c0c0482140010342d0002c001c15102c44409940055000f0903024040c40307407141000d02d42e0320600600c1040d0403100c0c014054039055440f180e04c0c0380e0002c0e0280040040656950016501d23500010104c0c12595864050a41407410362401800415020305000306942c083e80400600300e0b03000c0a440d00d07142d4440681c24100064001040150039a090442c550794580000300394091079810550111881d070b60f4840c10450803444058040344030555119403c00741c2d82d051010b2500341341c0c0081c1391292049040b1030388113a854218a03c0e120190b08110b4003220880001c0f070a00c92249410b074090f000605000c035941e621a6005003400c1c1404070001e0501c40054030b601d00c1c46200240504d4140d941c42c0039180b03401d03c1e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 976944811 1250 976943561 976943621
    0xa290904120212132402070e090703142401030503091c080a0309032303062704051b060c0d11071203050705100203061e131a0f010302250501 62
    0x1d4000c4e60414680f094070006414804105c0c40d40c90a0190058404c242c18410142000d61004081040700d00c200c240c00400030304200c03400b03169020590007030f01c245541c040b10140c0c00d034440000c0c80c00c980d10170401800440d102104445003814203c9180c6080126948061000c1d00d0850020307004034004103240d0441038140d0020100907110f90390300000c080d05180784407081c1000c0d80c160a41c2e02c0c0c0500c006003080c2801409500c41c00f15a00e030030702103420b0301549018222401c0360211030300c0d0440324004004500140c0100f1000e2421128181484050070120f0f654850300f1204008121031035030001c074002c2080c0011030261240d01d400018a110508000d40b21b40e20603c2c013102e65205440002d10840704620a6900a000c001d100c207281024100c00b500200710004451903001c0403800b12041c210000d031081c0400060107040580c0c51103004800c000006608802c40d0781410b00406c44600e180b4204000c1076100c2818002050005060f030809600510b903045450080d44c1502103000841c0f0303e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 976946061 1250 976944811 976944847
    0x3091415030109091205031e040f080403080c0127020405072d0e030703030e0105071a150f010311030604090c0b1b0601080106030b04140f01050a290904120212 70
    0x406512005c074090701e0718001300c030b00e403008890450b50700c0207810591607000c0445452581150140b0300da040f400c02d00340c94450040d40035903c1101d40b0000001c000010030000e024506002030760352400e1500e1740c190b490000e041e002220000b44110350710400030f0115806031090400b50b0000c581c03181a8050003c544c03c84c408050a84100847e51008200301c05250029885050360b038165100c0451102103801507a09401c03180701240c80000100c5203a400508641d11148500c00d200440310004426809004078240442403180c10503003044486d60704c0741c00b80300403240c00500c01d0f50002400a1641004c050000c1e003a00f05442640002400f150000350f002130002c888117100b01990749690340c4007011030803540c192200403c25840c410000d00030034000e44031184450600381c151480000c101b04140d00b10b03241200d80c4d4801c0341e52030405050000d04444840c03a61100210004481c2c0314030000602400c030014001409075042c0e40302c00030b01c18400c2c080d00c206e00000d181c0d981d490b40800d03082d44030710780 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 976947311 1250 976946061 976946063
    0x4382103072f040e0703030f17241e2202130f05090906041e12090810150b07020307030203030706051501030b010c1b260c040203040309141503010909 66
    0x2901c503010140d10f00c1c140c03143c03881009201006020355850740d1341c19641030f040c01c1401c005020a601090b80409400c1e040244280360491500b04482c514884814810400a03049409540100e040c2c0464039514214801e560000b1078010300b2508501d00b02100550130b40d2780910b1350701d00214109000301803802c2a18240c8050048070301c2d096440303400f1b220554108980d440c10a81c071000c0400c0124070158090008021002d449800c04003d6403642c00c5400c7c00c0701c0c1200b00065404030300f002443d2041c81f030b4610540520318188081c250644290403400d82d280910074501c0000112281155010031503480110b902406032500d980072820b105000700380c2212080c150b04224040120a50304c24030031402c040e0016150f04107062403507255050b004845203c494800171034403001085c000c0c00764942010000101c1c251100d2114440f003000c0c20401c80040e02c03401940140240000039400c10301d510280e510103100850315042107000580404515101c03810254400800404c140100350400300c0380c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 976948561 1250 976947311 976947383
    0x6033b25061107030b0c1306110c0906030d050f071208100b070803071215170708070807031506120f060b101211090438210307 56
    0x80365680d006030b0340b05003040105109504504400d000242610880d03d400504100c9100e082c18803101c40550306450540080c004204040c00c15511518204444021010305840d041203606215001ca42c8d142810360030300c800c1c40b101240120386c61201c4019910160380202903c00c68170b000400c040c01c002070986642c0309a500c410004241012800c08960042d6440a20b040c5960364280f411141c2c084104060403660380c4640d540380385208001034460141200c040d9040b01c09459034000c40c0380c043d881e441081150044601080441d0303000c2741070021030b0740200741060310301043d0000500a1400781c00001d0024030050341e080c24003c94505041025200704401c015401800c010016006144080d10340001d00f11034109121400c8d0750081c5044000d5241080d05200704180007a0949040215415610f000340d1070718252031140c41d1603042c86a2207220005201c0c140381d030100b00105101440c02610380c0d003140a0300d400742030401c216602c0640282040d80ca021a000e00d0f0701681c001c0a07030096038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 976949811 1250 976948561 976948633
    0xb010906030e100f200421020a0608061c15050a150603111c020c12120f3705060103021c050402220501030b0106033b 52
    0x20441c041d11500e8640d48a200081c07080c0800d00c29210040c24000c59242d010360b4a40301035240d0b107150903400300342c40040ca4015a0320b841c10a20070485c4c82d00c01c0c4d40a0080c03c01451850000341c0c40f600e80100c1564018078000140d030307a5002c045610314041d40740140c2108102c40500d002c0c0850031030310690440d103101d810f002c203854442090703080e0744144040c19986524100d080000381d000e82e104103640c10746144824140031030242110003035100192100700558000030044058101408000781008800c00d000c1e050094101c04144000e030002c5c00d0401d0901050b010490101c582d2420350f040742c5529000c0d914150300004481e40380307004404015441424500403038a03540c000e009403690003000c282c4140826010008a101a0401400981c1c00c0300c02551034480504005803100c40981c0e5004000ca025495480d248076460016400b00040614003240d50b01e035102181d0000d60034500d503000491141008811f2050000261b2340124600d11031190102404102d03080c240614170b410100040e4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 976951061 1250 976949811 976949819
    0xa03030b0406060e0108190e0303162102070609061e05010e06030c040f02040e0408070c050118090905070b030a060801110306090c0a090b07060504050105070c05030301060c02040b040c030b0109 85
    0x10503500e03070303000d0760011031107064442c003040d4811b001c520303489203814240c1c500000420351114121121289440480e41001040000c5c0601404581140d481c0070714117000e084004495480c40040d1811910303064640004a603401d10115402003130003140c00490402c2807224595452410341c04807060ba00c0c0c3c4508003000018207410351b06105201c3c00010b030141442243c0d00f01000b00810342c00c4d002c4e0403165401d0101203000c0c461027801d58402ca214085c526540c090760706200740d007030140ba4026030411440d40c074500030351103d008011084580101d40850345400502c0e00c2c03418a0400e8101c1c030300301c0e440402000300094094118500720b03400c01d002004290301e030842e08070017031000321416038000c8861004180ba20008100414070102c03581b40603e1519114ac00419442c2c0c4040030030b0703e0703c41d250014802400400c2c49501d81140c418140700c00a50340740d0340d800d03172a804144075410030310071071011003c10b42d11240c0000008800040003000a00007198000e40107110180e540b0703000402a040201d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 976952311 1250 976951061 976951069
    0x6030b10050f10050d05040503070302071a0a050c0a0f061b1b110a0e0109050a0c050702010f0807200303040302010501080a261207110f0c0a0e04140607020a03030b 72
    0x8001d41d10050700c98191a00944188425a90a44000410480c1c03c100512030541c0500c5500e0041c0d00ca03030041d6640702414200203240c0380154001da804450003072000000c542e2035004480b0700c41030a040c00f07600e480c889180c01c1d04000d0114000303007003513421400050421039142d020350888901040d18005200346640704450100d07204182000070a0400050310103e1408100240c0140300103110161081e10303500c01104810702a4842551a9210401c0c000043c105000e540c0c600880c0e85421170800d550340d00020325150f00e4040d40d400303025900006c40c203440d200301c201c95820b40f040210f08825001c13415865551f80e20407501a00194038040020880717100124081c0c01044d044810340442450740d00c0d03c26400061038540070710840c4100080703a5601c2c41e1f0103c0610403c500e0312902c00405928032074508044030024541c40e1038019103011092907a0b00f4519105403180342039aa500e036030303841ca08040003400c030729640f011921910003000015a40042e0525289110b0740d014861115200188 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 976953561 1250 976952311 976952341
    0x120109020609091f03060903031803120f02220321090902030a0b0409050309010905100504030320150a11030417031e0a091a101707030b0a06030b 64
    0x794808801c00c448500b52603c40502908020281200c84c4e8180e00c04c81401942c80180c3e000f210034640341c4400c00c06140d01351007403c060120001300805d050104e43e60042996540c40d804c5403d05aa03603048400c94406a410707030765013451500454000c20603800302144242c0c9107102c200c845050031262107211070f64030904081030001a85400c0f6900703007030081040194000038075010042e0381d14041c0c95882c0d5a075000b8890b0050007040074655442c00c010004001407c6d50700480d019011aa081c007000039800001c460450341c151626500744480749044d00f01000140030307402c0d114071840d4000014112850308090080f540368908102c0800c54500703440f01c0340011200034005962020b0b101d070520710400011984510070494500c1407680c02c9880c0f2013600410b4552040765681da030100300c20403045218640216075203002c903281d1440d12002c0104210740d140520009003180c4020141c009004001101c00385900541007592403900042c60f100414903071105865201440700824a003050b02d00d48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 976954811 1250 976953561 976953563
    0x150e1e070f0f12030302070c0314010e010507080601121107082809030f02030a060626030f03060f032a090112050601150903201512040b07031d010b120109 68
    0xa0040194030b4422107900d0900f11070781c2038060540801c00c1d0b5000840b00c2940101962003910944069004540500d084441e280c64074071042e031600040c00800d94110b00c1d601d91100e4240791032905c1d0884e240940000e0081c03284100783c2481c001c0b03000400c1140300b001506008031b000c116002c1085480010101d002d108400d10004a1070500303041c004203c40001070354050380041c08130f038250081b60740c800c01201c80c250f0040c4c1c00880d0082e51280e6070509004140000b18224004600381001003c4184140c171010744924415050150304101c135403003d111a403688854001c4008495886410070000b003200040480d2040c0c200e1400801d07540a09005060095009070007081e0036820640d0751100400b130310a000e020b0016012002000501c4155601c00c01201481c41421111710482800480d0904260040824200b80003888100e002030700e0983d84030b908641c000c40d107525000c80680c01001141070301c041d800000c241804407918150485003107990180c0e6201900d4010000842c00c0741c15080b4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 976956061 1250 976954811 976954829
    0x30d021b0d240b091b1806030a09060c05040501140c070e18060f0415050604020f0403030c0b070816030209061902060907080d022a0621060a030807150e1e070f 70
    0x3201e640308600029102c2602d070324107440606c03060312000448a4104035910300c00c807a01c130740b200002c21025000340512800e01d801d00505160801d00044c00900d403905e00004c08400200301c41140303001c00c000c100010444180704d6440c0b410070740d01515850307926070600c803940c0c418003000c1132a640ca9420703181d12850300030022064240010f140303c0c02826006c0c12a551294081c41400450b4040000410085200b0f1716485440750480c41d19805201e0000c001200780680c403420081c040300a842d0507140e0f104c141c078005a5a8074650f0009109003e02d545e1420700c40340c40228030f040503800242c4140211410300c11140020307070ba882c0065442d0209005500160441c070849202c00c882200d014665601ea000703288010403035800410402e4000c0741d8410318031114180140801c08020194540000058820301b2706141140c1722003002e846030321030040040e0080894409000040c2d403100c0c003005e45e504c007581d0500c0d621307205a00c06041c55150242c240d0013006800034181625a00c11000c50359402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 976957311 1250 976956061 976956091
    0xf180310330b072303041d0903190c05070308130608090a021e010210140106180303080c0703030b0d0326010e01060c02190602010c030605030d021b0d240b09 69
    0x6a102c18940702d010490408483e400d007182000c6010510107080501095003010300d80840c414600a047c0340003404500701a003080110840700300310102d070503a40454a00300202030641702d20708180303000c1a55101818040001c90742c000200c140b99860011070300c3d82d5a48030015101c02d010740751180300022000b54451156800c0e00080e40070840311485194050058a031070700d100c01258000e42d00ca61664542c2d60303035450010b1000b07a82205404080340203488070503240c02e045a401400d20b0502a10181000401052030010584aa00011284007010b0540480301d48036140107010340000d510401650460391228080000c20075032028100d40d0481031180190f4604142030f540314240d070500b641c010f00e907080e02050030a01c0c0e03500034009144a41c000507100c1d1003142e008080300c2c13072600064841d4107d0b04501030080d42c0040d410140780f10400c0424000103140000428003440b40c1c0009000d9050a02070050003201c5141c15400120028428040d40300c46008000b00030700308480e025000c01c500c2e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 976958561 1250 976957311 976957313
    0x7091a12010b1e04060806040f030215040302034801050a0e10020a02121602090123011413080102280c030e03070909081e0f180310330b07 61
    0x83c1c0c1440c032034a80203030000624a4850f5901401c1800454040c1e8410700c51500b40020158100060500c0081c2c09c1c107221a02d003080e940c020340340d10800c82c010b0140721200000c400c2600c61448060440c110421032010180300207001f00355030b03c00080f00154a54a08000034200002c05c1c000e0f5031320340c480d45000d402e6400c020040a00290050328000f01180309048136142c551003144000c0081c070607140100401002c1501c10800301d441e050300300c1d880c08104000b520040e150404c000201842090030100d080d80c0c0007248071f0b50640070751440c080000c151000700080000c270640c01000c24ac40d00942c41c040050f050380404440c11480054070002460914040c00442d10582000340348c42001003c3d16015585d59590106031006250181c0f0700c4140001d82c404801c0d21400407409070402038071500d0600980f4120700119020342603019170340c151a48010300c03803a83c081c072190628404a11081119066480f103c2c00503c004c800e50b85048484514002082d0000020180454800508081c039114072 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 976959811 1250 976958561 976958599
    0x2d040c0f0302130f080f060702011e0b0d17041a070b0106050a03090f030503091615050a1202030a060f44010c0f1805061b07091a12010b 60
    0x2216255401030314900404c0c0244d5442403903008048420040c20b5441d407000d00a410810094803580c15685032050840c0403030310005a00900d03001201001550706010030100d034104c622118000d200806904098040140810250041d1001c8201c40910440480300c120118801c464020301444440f03c01082020301c42c07401400c105106141c0032540d11426604c4110640000204501189010003000303141c620401c51460501920140711032540d1400b112404a100220b80342401c01c1340c005070013458103000306030080c19054484c904554910b006001c48d40100103d02510950410b00c4a0016000e17583c0003c108100c09a00180d805800499050726074031002c0380c202940d01c8480c0450300101d00c1080c441e4000c6010a070321990012480080c0c000d2504814805004d03060900603828400c0d40c0300c1c0350030303948045c0c60f030907140550180391400f8070700c2c10711a0740c01011240d06144000310702120700302d01e4a545080503a08803290103c000802800c0e02c0000702c10701d402080002c080b07414500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 976961061 1250 976959811 976959817
    0x1080f0406050c070f060c0f0e220e06010e0610050c03030f07170f1803070807080f0912030406030c17190f090c08060c0a0f050c0c2d040c0f0302 64
    0x507030b10f060580342c81000da44141c84001000380948405541c0c465030289150006424110400140340a4032490114400142015001c40f511180007918069801c40d0007a02e0740950451615901201c0c102d40c1d54190000024000b00ca05600440d90169401c4000b0301500940b010b012800e80518250740c0e502441d9881100000d0040041281e0880c0c0d0042c4101070703030181805040d40140c0c4180c07170300d82014200c244200d1021026610780c410090800070424040560348040c0d40003410a42e100c02540300c8843e030f070080039115540024803c185c0305104000000800840d0200d440c1440b138801080d2050364014460252001111420030010303031050541c1e603002d580d0600f003040014580903840310200c01c0b1000e403401100c3c80b00c038800d824000c0640c00c0114903401039548000600e0050b01203030080021b18080c40d10410b0040101d0628042c000603c00211100000381003025909001510500000c210b42c500c0901452450000201d9042c82c3c010802c1640b89a2920341e100080c41400310000e44c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 976962311 1250 976961061 976961071
    0xf010b0603071b14211303081309020a120c08041101081305121c0203010501020c01180902030f040b07110601060f020705030706022401050d060504030509150c070501080f040605 78
    0x500d10903e0318000a904084601c1c800340000014407440540d42c40c070704000ea00004d82c54000383c41c140010890700802d45005c905503540711440546901c0c0c100d00f41700c4022001d80046540c00c1c000305e662060941d00515601585107001d2051142c8402c000050354111415680949011502e600440c1254020350609401504044880344109810b40301c49043c4041a40c043c60544400243c1548503079008400f010201c01d40c1c1c1085185501d020000b0755a10b217081e181d0360610100c504d181c0302c3d100010780100e000b00b065180965880c036000d188a80319071802c075021100c010020340420b0495116107000c03266040710f10000c001c643d082540a03541c58031400c502c6401c61069010124060f101480b040c8010503640d0010260440c01e640702c0e42030381d1100d0071860703a031040c91030040007140c3c0e403800c80a00f8580c101000103900e4541d4102140d080c841c4022003500044800d0011040100d40d10003480c0d6030031000c1c15a92200c0d1140c00440d031118040e107210310030400d04030100300442c050354811a040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 976963561 1250 976962311 976962347
    0x31080708070c0303030507170906010923040809120c0306010501052a0703020103110c07031104020c190506060307030308180109050a0b10050d03021b0406090609020c0f010b060307 79
    0x1c240c0aa4441050195940048000a80b580c0c207101460350000c02240010742204040889450011714055488a05200b117000c2161554030141d000c8080114041d54a1072642c00c02000d072506050071841e56104560f002d000c1d07001151380d43c00707600c4003007441c80022400902a00e002e9107000011030707030380e0410b00001500208010041c46c0d07803466401c2840c161310300500500711480c51800090115400c000e039002966604020b4416000004541c01d41581e84c4140c4072019003644030301080c0207008101e02e44149100700f8454160600074001582c400c148100120b401580d50f0000307251726903c0500c801804294010081014601080036866200070814000100c00300700380c59851030103190401c02d0700c1e0259100d0610102c440c0c030480d848050035054894101140141d175000f03540d15800362420102e641c200241100640c2d0701d42140e0002c10490764103010083c0c445040500079403101904210300e2040d10114841c070301040c050030b8072081009000c00d085a54856040c0c845000c640c4516400e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 976964811 1250 976963561 976963567
    0x605070b06041e0f0603120203070f0b07020a0b13050d03060510230a0807080f0f0610020115060e01181a07060615121d070603020f0c01020c0631080708 67
    0x14620a40c03141d81c0e132646030b8003004500c480c078605004000c0208010020119001001020081800000040400c1c7da2102e05004590740b4000100d040242e03841c0010403407616417041c031100700c4e04510540203250081c01aa03000304254034003581103691610605130800c003001211408207014001c05000303210340065201e43c8035803001300b4503d9a440a074503036011405030409d12a10701d0b0b0040d20300d0391000410200703074034a007080d01c031030202e0080043c0014810945501c0c1980901d100f90461682c002c1c07000e0410b0802903c03410302800c000e800940440c00100d2121000608440741000d020480b41a105007221035440043d0019640e440481e00780c2e08552210b800140102ca140c10913880f03a0340c2c0d66034445000031140c02d504195284020800e425006c3c01c40325424100c004100d400450380d0a0a0060380c070014400c110a8a01030480071007400e510100c0d06c0c001c070304c40c00b0610318481c15040311380c01008100030064040007800f840c142c603403003141c2e81c50302c01c00110140c000304022402448020b007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 976966061 1250 976964811 976964861
    0x70507031806180803070503030114040e0d020606040e0102090f040902190b0712170f0907080a140c0604060507080706060e1608160c060b060705060a150605070b0604 73
    0x440d0860310b60001e4000f03648122080e03c00a14551002c0250071500c003d14904191521955620300060045100c1500c2a501c5030140d5510307a0b20000e030802c4800b0030354400040d011b9019444031301c200c1d0654015070a01c4c3d401300300300c0c0d418401c032180000c2c010710100080c04228188401494a02c1017260003124005595425031a106014002406006c4009a9440e03d601c2e145190411101c185014006101101040c0148640a0f160310051810b000001070707540302c40e40c615000c1c03980e101035001d025949002d010311903443c188180b107021200c102e540b0700b004881445114801d500c19500090000c0c05010f00151502d0000c0068034000c035800b0881356203a0803e640982010340f00c0301c45800d240101c40580340c0c1c00604c551b50041d004503001c00c3d0b000152001a03c02e4103c2c0c0700007082c40d40d40d0505d43c400c0740d503000192409030360001d0444085240c6100e03114002c4c100c802403e0800880140c1c0001e0451040049843c680e9015060054079200c0009000181081c104150030110043c01140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 976967311 1250 976966061 976966097
    0x7051e27041709010c0f02040b0d030804050706080c0409050907170a021203030106050f070203072601051f03060507020708030f18040b09041e0503070b040506061807050703 76
    0x22040c052989092610306280c5424112000006059080c1100503c42d41050303a0700403c61003985070304000803c820126030310000e0014039140008640c400c10792424003042c16440700206115038891811558129201c480039280316000b201c040b035100303004020030710407600107412450304102d004e02228995900c030f0704040c0c10400402002442e503441801c060b8150b2600d01c50000025480340055444c0d5410094028000c1c4142c0020041031400080d08c1c10464404015450040c942d2040640040002070f400c120f01e2040500116410f41c20100450303c401c800d0980da40c200d80882d21800501c40c5141e94002c003519000f0141c3d0150b006400340024003520900041611139421000d80303503508030a05002d41e4207079000b68503a010780c0c540708d00c69410303803a83c07140b01d5045a0005884812074402103140700041620f07500085c614000818414204100803243c103000398800c4090700c0a56807900140100320500742400f003058071190020454030750041d8010b2051900070f240802d10100c2011003d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 976968561 1250 976967311 976967359
    0x3041e0b01120501050a0b031b010207090507030501171902011b0c0312090e090712020d0c0305070504111908060f0a0f090507020d09180b180906070207051e 69
    0x40c1030842c0500c00c0000c1041402e100d200e40c402c9040134108445440b0341e01007540da0b00b82082c1e40442c080c00c806905041c0c0e00800041c00100349019040c06149010314008020741820300c1410185042003581900852010610f0340390b41d9500c1940c4000340b601900116480710250258a8542000703e419201090401200364040d6002e4940c0d00003501d080d9000800c840002d6111006040c0b01009202c201940810a041210501622442040000d00000304102154040204604050800081000800b1a0300300455600310780030400c43d1038810704070303005204001c01000105002c2c4100305000c0d000e1341400d500324034080d08805180b10100e02041c0f1501e42600803117003003a400c080400018095020305544290305101900c0720900721800034004d5441e90061301c014004c2908062900c18060f4410421a100204255078030440d41603240000401590a2400b40c020440010846800040e1107021660081d05c1045c034110701c40c040c0c509250b12015815409100d0100903d4440110071031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 976969811 1250 976968561 976968569
    0x4091a0a050928080c030c0319081e1315141602030412081c0c03090512090a0521030406020d0905010201110d0506010e0a081e0c0603041e0b01 63
    0x800102810002c41d064034100e6914448a83d6028506895a8026120702c09641155210340d5040d00c9041e105200c5040d0f0040780c010940740e11000c0382c240d01c03180c9448025060f40155840e02d03411904d0300c0c001d6030384440000a10342580b11001d40440d100250301035110708014001e10030301c218500c001050740c0c00e550f1002522455282c2203402e11201c4880d0b0020740c6902841800214903040c81c001d01e0850702c042c000000b420850010800d0960810f81081250821810800800c40e0410401000e00203240702c20f42030b01c0078810040c28410054820003190f41c6084000e00b510310b664600f030100840d01c00c0c0c90b090804a441044406084103500300050b00140039a034018051050a0070760050041290341d00080c11a8100081501c1c440030302e104440c144129000007044544e142030041e1512030815030010340003500484e001a003d500450408940c001c090070060300c0c2d440c8012907503912000ca9032500c1d0300040800100303000500284c03481c0c00c0c40075800203496003c502500c40c2a811802680 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 976971061 1250 976969811 976969831
    0x406080d0e032b0507030215070507051501051e0f18011a0a0f0c052506030b030f12070c0906090605040f0212041218170c030d05030604091a 62
    0x2004072001d140c10300007016580c5503000c4000f48403545401d68021404101d090700c061220004482c01803501c01d0242507000b401c028100c140d542080da200030195170004c58152030600540c455002045072020a0322b04030b5030000c20074911040645800c503104034000d15450b030b20400082d0042550340320f0b43d45522215078003110252083d0326002050012010b6120740d50562002048078040d000e03005001201c81c0c2c1a1b40c44d111403d03940b5441d00e9450103a41c0040d1601d0150344241411010a48101c820207440b074a59050014840901c14980c1da0320280541c0c0c000c6401140788501881c008001610043d8040d0007405143c0f642d0b80007010032224076400000065032698001e0200382094098028940d44201c41103142034418010005180e1000d000185012025440500428403d4811083c83c95204440c2259035588141350550010125207808850013041c20303e90b22031901140320040e4088684489245560341d0041000074110302e0005c541c01c0b40801e603000c030b180c400c1c4c4144500c2004002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 976972311 1250 976971061 976971077
    0x20d060c090e2e1a0d0b19170304030b01180221040c0f03020f10030e0106060c050c060c0d050306010201060e070314010b0903030409090204090b0f01030c0b130605090406080d 77
    0x294441c1c0000680b8440c0c3c0003407030000c040420108000304a40754070380c56000328040d25080c170324459074080e01c69040040d921120800c0030a80d109440f60114040311030f0040700c00080001440c5a80c2c40f401548000f80203411900c00411004108000c0c020b10b403035040c0070061406040007280d02c03035101500c815107840300c49a410403003042000010341d800340000c256100010b52440e400207504000c401d0500d401102c1e101410000240213400002180609500a009580c0c503040300500166a801d0181c8151086500380c0040781001800c40729083c0c46403010780020181ca50702510298805810300781107658600000610900d0b00c04007030300804007503130003160084070909484d20801c41a080b110402d00d080182c92041d540000840342201d140a41c0401c0c0e051a0b400054000c0030310350806044a1000b07410080880352041125040c0d07481521800070054036807140c00001c2c011150007100c158002081401f800340200b010304404000103002189a5031108081400d1489958024010600103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 976973561 1250 976972311 976972351
    0x304030b040c09090215070c030618150213030b10050910151701120f021203280801120819050a03110712110a170d05070c020d060c090e 60
    0xc0c19610300401d0fa0701000c1c4541400e5400040c1c00030000d40600c0c0d55000300140c210b08020720b00e2100030003580c01503410082c035854000d000c8000340050b01c00721a907030700740c01030140d04400078400c0c0d94031070314501c6408840c0341c155590b00040b004050305a01903c812007000003000d503600f0800da44101607849408a07428a0002015101000c0e803402e8001c0c0f041c0400040145181502c04030304507291030300c1a101c03050881c03c040f041d110000502a40011844c0440c04061a0000090040100e540420b406511600404c159805400418140040d43d01e00c01041540030b080b5910400d24025a65039150100424100001d40c48c1c0415900200700e0100c1c3c003d0318607800d44641201c034110041c8080c940515076031100845c030a07110b141401e01c10981d607440381c0c00c4820080c810125502c0401250712a01d40c01c1384c007803540c005130360347e941c00c0e41464000b40c4100d00c5084050000c940c060700006107100213a50307070405001484e45800c201302c000c00c030014580803d008524060320240092804000103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 976974811 1250 976973561 976973573
    0x50c0f0307050706060503030307021506040b040905341401050d1406011e120903020c130501091b2c190e07030b060f07020d0222050a0605100e0307080304030b04 71
    0x1b40e004a100e41c100b80104150541c01040300310080c05865641a21541d8a000080007480030002150f046032a0003402070400c2400201d1a230141d10b405d20300450b00c0d0380c10318900303102454040d0f03004559a20a0703082002038048802d420280205040c01800d0030034401c0c0203001c584e04000140c03030119041050102701d5030851103401c0c00e8594001881c00c586481100500214500961012040e9549042d07506241c404e00c800300d06a00000c1c0382d4211541d02e15031a10103040f003800390700605403401070781100c1c10304456860050f1088646440030b043c4c0300e0707455441c80240300102c25035078200c803120011040d17551060740d69010603000450145480c00e000d00d001484800401ca20140752515080641980c0c0c0c140c2a14070000c10200c3c1da40e41c8a0681c40400c440399a2048000d4004290400e01103003841c05a5092200030201001005207694500d804010380b0130b1485803681240414014042c42c0d03105030513500b407404000d012140c505942d20412499a4001e9100b41ca0942c1400c00740001c00c80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 976976061 1250 976974811 976974821
    0x20f1507121e020c2b0f0e1c080310091505061602030d0906140a020c12071d04050d02070b0417070503070b0a020f061006031a0d05070602010b150409050c0f0307050706 74
    0x1c20b03540b03011480400d0030014211ba0901d007074110500c502c950341d041c000ea8900e00c0601a800b10080ea0742c40c0c0268510f014000c9400595289030050703001100803401017480c0c03041154003240005020542c6140109102807540655180710907070100710007090168508010000940100760380e403907140c0d498031f20700501c1c105040c0b40400e11040100000510103900250501446100b15601c61003003426465140c0742c8403c540c80803840107044404116010780842c4100d20a40c007540a07500c6c9010340b03c030101e031141e08a01a111000601340418015840900c01010025160f00300f201c912a483d580000d10f4201c3c950300031203200c03400142e1021041da05122600404413100010700150800700b00103481c0642a000c2c480802d43c5d20a00d181b00c140c80c2034460f01441070f000e020200c0007040c50410395181c0e401800390b0009903003485071800741030501da5800c8070101110f4041c2400d09080c402600e000d0b00000e0710b510784960702445529040c40040d40250f004080380d480c0e96607200a01e151903010b0324 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 976977311 1250 976976061 976976113
    0x19021b0a050d06020c0316060b12011e0e01023f070e04050a0b0907080a110a021c03090b1503060604020405030a0219080d020f1507121e020c 62
    0x10303120003820455a111140c4607105554440000360f1250344003001e09246010f6107071400310f1190401c1c020b0b070500c00c280c3e0201817080300135501c800c8044210103142d801ea070002458038107440000c8884a1a14480798800b05004d00d03620000b602d44054084014584d0504105086082d25400790340f5010708016141240c000d100751803006490325283c40040c04001c1ca2440e00ba01071a2104001850b10344664441d0b100880c00801e851090f05002c0d50003010010111001300c04503143c46041d145121100d0305840c8080ba180d40107101d101e036aa050001c0d9001e40305110300505850358140c02c009403102c00d002e44120400300341800f059042004161401c070010705810b0145204000c00c2c012610085403c480301c80e0141d410700c0310081903001e600d00786042507000c2034141c09148940c020030b550103e4800320b034078021807c40300250780001001c401c20b8000d03200c803130102d10b007030b40c1508441000740c0103481901c80c07000300014000c20700b403820010703039000f00c0000e4550303009a440c10380790540d07524130a8203607 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 976978417 1106 976977311 976977319
    0x60302070302010c0813030c05070812030916030b1810050109020c07080d0c0308040632070206071202090d050a051c0c020105030c0f19021b 62
    0xd400400c8218019401c060503022102d2242d51390b6802a07041c48a84003800c2c0c01a581500d10201c05175046499000b46800040c2013401071102d812503c0030111103035503a203007504c101c41c204003140c81c1c101c012442d0200e041c8081240e1420007a07001080080402c480304081035200d160250348612501124104000421401044c5e009000300340045811200c800781c45000680c0c0341c0041000d0343c40042c0c0030b04500004030344100891600b00307000b60302c0000e00247d100000c180d502c45811000c4240420f12240708040c94490304a80d510462034400b0303141c10b0038110340003441c503105186801061500422075140b0f5a8490b200300d88544c0d80001101c60100040c80d0040d21941541c899101d8140b5450303c0448039401200804104d590580d030301d614580c0d41d80030340800c0e50010360010058001c20f01c5024044502d0421441c03540d91140c00a040d503001d000001b0030040d101d103080c42e0103 = true := by decide +kernel

theorem cover : BRFrame.Cov 976798561 976978417 := by
  have h0 := BRFrame.cov_init 976798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 976798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 976798561 ≤ n) (h2 : n < 976978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
