-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1346
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:29:56.82024+00:00
-- url     : https://prove2.me/submissions/876502c7-b59d-49bb-a702-32c71774f230

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 241906474 ≤ n < 242086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 241907724 1250 241906474 241906493
    0x212040f1406070c061d032109011e0816020a2f0a090b04060501020f0705012d0f0f02010c0e04110f0705010603061a032d030a08060a080f0604 63
    0x5401c1d00580c04000100216844010613401090907070f4a01040441050040407000d046000040c402e0308001d030102ca609407498004484c4016010766107594024010040c0c1d401400d03c0451a5001000d1251040e01a00032052078822080c04c00c40411070055218101d840341e241e080000c0502c1c040703020030000350744d040000c605010300d0100406144001140001d440a00e142d11440c2c425840b05480c0342c441c10305026a0300106001e000501c10082c50740c450580b41e1a5602509041200c82c078003213900042d200106e13541460301305100c5400e18030014002800322422810300d801045488942c507400f91710512402d4210a81d0342e642000207452503041001908c0542c80c800c00908043c407084540c081c4080003001d04910400001600600d503181540985441c080c403400100c400b40c00d2241291408141c0da100d00c0782d00d00c10782d1030380320070000d1051620a0030b00090783d0603c00890446201a0020001e60241a0441d0802c070803568412951b0b03510a1009603602490300910003107400034070400c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 241908974 1250 241907724 241907759
    0x6060907080f0c0d0f060503191e03020a0204020307050a0e01090501020304060e0a0321031107020d020d1401020406030911100212210a0b011701030c05011202070501050c09010212040f 81
    0x4829031070210f5103418031301a602d07000002c03400035030780700000c009a203801c000886035420031860008410780d0940360405001101c004c00d603070304102d11140c442014401d01840b800c46500a004644074141003400400c283c000c080d001021810200450b1030399800303014034404648059000398682802c0c49811152903102880480e0019140c060200001c0c0f98020b040024040c850160349502501c94001002d6401220f800004102d0401055001d604d80314000d01c070a0f6010756554440170381e00d280288050300a440f06c000154030100700070483c1945034101600aa00410001e020040c42c02c0401418041d0400c0c0d400241e40100c1c2c00c680c00400f40c0300580040e031803982000100101e15071544205c114101c07001c0846a54614000300f2039a00026104003015255444003151740c155030305c202c20801c0e10b00559040c85240c0e41c24a1074490650112050590701034000d01c043e0514007401d002c55007000c2141c60160055801c800740d803600d5041990211090784840e0b4510610302241104d004102e02d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 241910224 1250 241908974 241908991
    0x10e1603060b030103051609182a03060507030e160e04021c03081602150604021c1a03010b01021b011206030b090709110705031b010603050d1106060907080f 69
    0x6030720008145200b100038500940c0190041e088595030190741d1180c0450390707046001e030549072001d0444450010003502100720350050070648000c400e1050803803948141445080c0920300c540002c03041290a402440c001c68182d181070040410060f0080e490700351101d0b100044203a0860200722000041210329000380c00504089083c07020250001a103620000041c0d0105542a00f8040c81a841c10320002800d16140f029100100310001c2540290350098001481503401044080007040480e19071585d510b0084010002501d0040103a00503a02c4544114421751134250111955400401d2680c44412034012016064007a8801900c81c1401003150b100d24540c1c0f00310100000d01c0c415042402081140d00a00410b40380144100540b25071215207021544d041c8000000990b0000684005041d900d45100880541c122028010985c3d50310250613403141c48170381418240c002c600e01003e01c01304002d842c0d29075500ca003841a241415200c40000851040008000051500c44150040c040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 241911474 1250 241910224 241910231
    0x50c071703071407030504060806060307050a11030f0c150c120703110d0c08040b06011d01030e010b06070c14060403080703111006060203040815090a1203060b040b09040c0305010e1603 81
    0x4189840d0144d4000d900120b003c944001001d01a494015400310791294003201c3c080e16500e80610010843c1c000d10003000148980e10f85200c45052060060340d2a001001e00b9864445071440b024075691034a03c01701c1e5020410143c04610713169540c02c12141445a40d511704c540d82d48401c80218014201c03504d41001010083c090700d55002480e0080760700003241030350b030b41a641c10030341001c03464018081d2180e418041c0c00599403405103144c500c9100341c5442400d00080e481d54528800d4094049416156800f220000d040700c20400342140761815a00000820080c001d15102840fa4510503400060901082131210800180c0316001202c50940864161504030310010865030966196410079005a00082030500c46480d0403c45e00d0b02c11841043c0c40011800c102d002c0603101d6881c0341c001340500c0700c0f002514488074080d0308060000c0c00742152140c2e540380c3d44c2045002d82d42000011a1050b414100344131513040c80b9005440c140c820b000c03035007952600c4122541001c1c2c0141048403081c03680f0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 241912724 1250 241911474 241911497
    0xc0303050c0a0c17010c08070219050a05061023030a020618030f1c0302130303051614061e06030c13061d0708061e040203040c151101050c07170307 65
    0x2026411200900d1382407030040f180364014148500399600701d002102002221406c001c221b5078009080c505904000e1400000e82c040b034280242042400c00000e0a144604d0052100d480c8010703a03403404540701c0b041b400c3e4407900e858000c10b00300306510244541c103900a4840f90050700d00040140082a0b08111443c0314900b081e01007420451103150108403604100d0b041c2004401c81c841c7c054111009141c118903043e008000741c0751086241c080502009000314600b62007421000c00a042c081d0003800c0c001c01424002c2e0155601e520445140010600030b40e14030884d00c2e05000071501900c00180a0b0030761018010500180ca90315403034901c0842c0c0c50b91740008080c0390010301d100103501c400305c4103c518588102d001d010b142e0060400350144130320702c00c10002030b8912801c0c810b00714404c17a0096526141d038140b913a1b41801c1600442100c941c01007002c8805074001c407401080c044158001d00c080c1d03860706104001070003103100290070030080e11002c4280d086030b034004541c001c0003400d15422000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 241913974 1250 241912724 241912733
    0x5030a0f05160528021e03030f04090606090f030818040609020d0902041103250915081006030204050f010315030503030408030f06041806020a020a140304180203040c0303050c0a 78
    0x80c110078041c1c42680200040c01002e0102168613141180c00c3c400c02d040d403000f240e000c81c0501c03e003040038001030b48900b44105015503091086621000340c4000c51600c6e141c071880840c008000d203110b031402090b4280000110a61940007440803030750801080d078109950440240310810000002c158455500c00c001f0031030300c80b144041e088441403600000f401891501c10f00044900b80d00c030702c80702c0c4c48080c010050078071421241410b0b602c0740400d104100402e00081a01c600711250001c0a0b035080700300d100301c10301c0e6110740d40034800d241e0992451150344d6208001e804a202e203018003904a5400b0181e220b0550280d00704031081020044146152039480d20303050b05680060321300710b03108940001840b2449040b4003010342c0003042203404009002484014503000361441e038000f803d040d00030400009250080c00741183c4603411866004001400f450102e8903036210380255019894210310100a03403e0074801d40c0c2c07086520490082c401401c5440036100c50b08165022031903840b0300c46c2c807180000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 241915224 1250 241913974 241914007
    0x3031d060307050405040605060726070b0109020a080a05010f0b0a0507120504061106090a030804020d02090c09120106030809060304080d021c0b270a06030803150a0501080405030a0f05 81
    0x100603680c1e902e41c41340e043c84100403e559039036003e903202e003505003c600c002c500200844044540351042e582c03544a400009580b0500400c0303000307040311800400005a00f42e540d001012480650756600e11a66103455101c42200c0082c042d00030302d0300c00c2800c284450010403000b0030745880103003007503400d00e02c047c0d84031100402c80300c881400160020404002c202e42107101c0303013000c0c0c0e1044081d01c01403521142c0c00344d071400c0c2444064100311682001c40c1c290b44034284001c1c0b0068002d8190180703445e055904c100306500c04103c0b14050701140704c01811100d01849030405683d88200340b0751402c885401049103070341004d4400c2d96620020441e00010442c00d1009040e00503241c44180100481a0000d504a400000960b8001e41c150b00320800b0300000c050400700c890181e42c40d0f0030385075124101440003e1480b5000141006000828862550700411608011075021100e0105480d01c60004441404058800611641c000c0c000c000740b45014800420301c200309454881d0410643d0040b40f00d10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 241916474 1250 241915224 241915231
    0x5120f0c0313050117010608280e0a111005030f04030e0904050f0111180d0804080703061d0102460f1101020a0e12010f09080a0f0c020a03031d0603 65
    0x5a0100d0402000956002100004a030300d01d403000b45c043c2d61500202a080b41001070400c1680c2c6280710a02d001032804ea039814040740141701c410000300b151407100d25038640c0040001c0c1d400f1b00021122a146250414501c103042005940d02420b64a8221001c120128090002c501b0303c41040c0c60308a2503143c0c00c1c2c106101d14051001480c80c0f1042003110340c01c641110700b2142d03000000300070058021866010000c40c540c1c054503100c01c418058109021a40510780001c030041c042d83c1400001d11410703401c114040c440c103030b810803082c29124032440c0c201d116600ca00c10750100c2000c080c4101554203402d2007031080035010080c0741c80c0f4000800440ca031034680c3c104408520300982e6200d02541c401ca0311021015040001c52a0036091200a000c1500520070607206801400072071042010071b400885030102c0910040c8420261440d0140f01c54104104080014a000d86070444007031250035491002da8010f070140b8803450a41c1c40840ea00f04031003024a110303503a40031140a0703503100d280c0103510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 241917724 1250 241916474 241916497
    0x3030209060c030f071b050108281104050f040c0905120111070308160801060905060c010e0a050a0201021506010503010311061c020409150e1f08011505040b090405120f0c03 76
    0x99906a501c0e0114a41b40040da041d40c3c8228600c00c00d00c05a40c01c807010540240750002011840c80032000780071600060714484003041800d08480c02d42c40e038000d070f02400648100700d400c03040340c8400009000c11214484544d01c001003030760008003c0c50a080c00d4691001c03044000210702a00e2000c40300080e030344240000c8000404450400004920320114604090f0040c03814182c0c9515142004001c14020f0250324420f0724005501c0b2035003142540464444000c0300b06444d0146128204503842d800b01060503805409801c05401c03145c030416003003504c078030016101c42e402c50b420b42e214040510034024085070082d40c100700000fa41c4802d40318196000922500140e52542844050001d8801b880e40c502c50903580c0003002e12560301c41c0c0c03101c1a40840f00511403003a001007201814800380c0300f41d016000c80d510b0719841070410b04400e2014000d503030098500340030346103a460501c00d404a003120050101c0e0041d0351307602141c560400040025480305802c20b070410035107091043c01e641c4850001003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 241918974 1250 241917724 241917727
    0xf03120106030609052a130e010501020111120a02160602372109120c17042102010e0a08010f050a0e07091104120624060c03030209060c030f 62
    0x481e450b0305009603005083c188405004900303154102000d4214071405034840e039141d0042c64041d020344070084d81e240034000c602000d481907846e0044111000c080c0611401542004042120030340c1c00f0040700d492800b54805800182c3d160b80d41c580007134112401e46880111a009004085000c070b00181c0743c02c0390b5140600320110f418421303c41c1402420014212008100c01c82d1b1624250042c0440311402041e50032402688201600c001c000c00c0e501c0d000400d070740c18000b18180640e40c880800010241f1400301c54550900c2011040b00a0085101d0032a8040117550301d68402c2e503900c1d20b82d1500030701c107040c400c0440e1803a5002504c0c80d1452b802450300d580d074507800e114100302d20303004098124040407404c00c412000c1104180e00c2e9038550107100c200c0e40c1c03180b0f58449030070110b20444c0c0080c04044a443c54002140c40d03c4800360014030300384c1c1d1019441040e621205050010b22108542c0d15484114411542e60b8069020350405111154001c0c0c05004183d0701480600c010b085101e00d40744540e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 241920224 1250 241918974 241918979
    0x60601020706030507050f0d060503010e061602010504150213170d140405090f04050a021e01080f01050603220609030203090a0f0503030a081503070602010b0307050316170f031201 79
    0xa250070140da01680800d4101020b006419800200311a180058580410303a5140d10700c2286003d0011540007507050344c60030071180721201d8007149007800b41c000c0b4150080200c00000c405c80c20ba404c1940e0240401c1d81401e000303001c4102c5580101019603101220008166a07a000503161001940010401e0780041640c1d400c45507000b984e002c030181490b461b42e030426040c01d01007041c0e0023005108082c01e00d40900401c09100c01000400c0c43c0c140d0040800720010402c440000d080c54100d004a400b082800000c2648003640305681810707184054070f00d03420340d6100102c42c01c00a2401002100044582d110308000c5a03850042d030049500076001075a46803d00418020003148035441000541045c40e400c0c4035682c0c009c012100d10072030524101041c0d8580405082c00302228202c0030798148500c80c0c3c0041e910390190801940c89200300c0654010725520302c14191180900c10360b011048001c00c40a01042000c005c40c1c1c4800e03000d10b82180c08000e040025145141d20400d11083c2c2c521200c07004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 241921474 1250 241920224 241920227
    0x40203160e1023100207090f150e04030e01080a14010803191115040314071a0109020c060429070302030f01090204120609030e211002070b071809020c060601 69
    0x548010020721100c400c000d072001c2000018198400c2c6003500ca640c4e080a43d0131142e20130081c04014003198202000f00090111700400140107031804074046208003040002d026400605003403003180c140d2105ca601403000c0b0011281004014001c130502642d40380c04c01c0c0c1134403002e046c080c00790086100a60b40c4802c440010301002d0b00c1181d28400b04202d2a0603580b000201080300d00c201c43d0320219420564840745000c0d50310032050081000d40040c045281d03410b00580d220725480400002c01412520b0340c03501c0251050344240000707400071354408800710300001d803a20307082c200345d8a101ca06500c0c00300d80d65000702169802941c05400084e000710611402e0303624440210f00610003e40210320301480c003c941400e2a0740c41001811860b600c0c010101494007452a1940e00c40c40200254035612102031b4103003e9042452000e8201d01c030f904000034a103805131080300e085c1900302103000056940e4100844000310701ea4a580c416084201c2e00040b00d0419001403e501400c100c0034245a240c010300 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 241922724 1250 241921474 241921501
    0x7020a060510270b0d0f0602030403030b060a0f030501080d05070209042315090303100b0315060d020403151802090702010b0402040306140703111905070507060306061d1503040203160e 81
    0x24510070308011508000244d131a0006c02c001da90300c01c501507200d5445044c2503000b00040c2c196940c10000c001201000103a1050000083c1007007903d0804c0980d03241c411282e9540101142100404c4080041c80050328149400c00e600034828422124203945410b00301c44803c804000005260384003c2c0d070328200c40c60340000e1342e52003171600000b1411468001e5403007141002da4425004025800008240384140000042040080107000f46030344800041c40440298031520080d00d4200e02610400d45006035809a4406040c41d02c00103d010380140c0c080001c0c0c440050044410b642d40c4a50f03c00b42610340f40060001140074020006158400d00307620209044001d11230003c06207424240c07100c001440040d940c00d924100c1a221400b07103030800136070f05032081140241592249100000d02c40364140c00560a07074030b0755031b29551030040b14a110840009404d03141076011902c1800504d6901c000700280d43d201d0f00040c111100802d0000c0041510030301e540004060b6030f060010810076802c00c08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 241923974 1250 241922724 241922741
    0x30d0929060a1205060f04050114090601140a0b0a110a0b040602030f0105041b1d0301050c0415020f0a060b0d02040c020a110d02030c240409060f090507020a06051027 73
    0x12490540000d43e41d4032182c0702c40f001030111400440440100781405025030080c000c01c104140b440303500f03040c00d0401940d40c00003445050b030003042a1010b08440d0a0509800b402c4a890711070f000c1c20094039210650719502901c090f01d425108106e10900899410b41d03040e07004a0051000594030b0410003180581400140c003c81c0c02282000220141107074601800c40301d9041500d4030703a002d6008042c1c8070701091594205168950b080a042c0011802148010003c41c1c21070440c404424120324002e0b41c0310764040713141400640100329103a0111b0240e8004c0c200c001c100403d417140c000d01560020701225840c0404d03000582c420880c410410145880c04400741000301c035040c1c00414691300082d40d403d42241400c1c0910106c9001000c00403845a05068035081c4c62625900c940e00c60314100c3c000d04840c40341a00075250b40c1c0000032500030b41d00c1481e002e039409901030100302c85c154803840044c01c4090300101d088c0920450010300c07045004507241c04000900040003040d6565000d5a0984007502d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 241925224 1250 241923974 241923989
    0xb0301050c040308070209190212060307140a1505040f03030513050a051c021302040320010f08070309140106060203040614430312051503030d0929060a 67
    0x2c000034000300e00c0c0d503410b440d80e8680c11255079000d0790300e807441516038078444072640600c1c50010076211010f104090509114200540482e40d03034680e80c15414902c10380340500326401c10311381002403003600d04515040d104100a4140f15203130940d142c6c01c24201403080c0c3c1c82900003510115000c045401035810f4400200f030300301c03485070b000c034280000a8050100300030070350740000d0149018000c546412400101d020213a900031520380c0d41d00c0c2002d036120728051110f5410440c080b400f2070700e00c3d03019240f002440082503490140a80d1100d13070035002032007849400e803085044030380c11580322042402000040e00d9030340d0145480e0f6140c6800a000820035511001440c501031011540d001c86464401300404c40359000700358a0505171040d0316000c80e10404a4002d42d506024140078140c10501701680300c071000c042000aa520300ea21400201ca08052031a4181c104110f41009000660003610255010303002d00e50700c0c42c203240010003038104003000d40941942d0103010800a4900300401c0230040404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 241926474 1250 241925224 241925227
    0x30c0c090204081605010519021603230d020312150d112b110a150201050105120604050a02010503070201140f01060905090103170f0f07050604020a150c020d03110a060b0301050c 78
    0x5d040001c1c040e4096550352180d072014082103040614404c0051004901c140458081d9203510303410708402409101128003000c4010601d0b07210350800c00030781c45074400c550f80d000d141400c405050200301290040c009002c40070040d80300e90f515980f488a9055154071650580e03402064400a0040e510f11444883d4a11548034207000d09090b5000da22049450344a035000310344510460001d121204542c1100300c2d080b2012202c410216015400181a503070200c4011140d0907520344281d55492044038010441d41100e880b040c0154010409507406c030205000124690048440180d10b0660444035109400ca02a0040011b103421000c000041d20050751811710b07541c15600c99200042408519445400c0c001502524400003041510914070707265542907541c2d02907062039a952402610264412604080c00041c84010364050004a070070503280c00d00e5500744c43d000c114040310002c2c1c00760240701c3c8455070311000c16001e20078940e809105a03800a44a5015800e042c03c5880052442062150 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 241927724 1250 241926474 241926479
    0x1021c0b0d0c0e13120509011403010311040e032106120a05060c032a0703110c0112090204090b0c0a030f0b2805090a0905011514010507030c0c0902040816 68
    0x10584011040ea00030b88800d0402d6200c4c000506035401071a0000f8107a104242000e0611641c064000c0003d61000d03a0381a10019802451108612080c0310080c02c41c02c0c00007441e50705003415088940707681042420740342800c2e402411024044165080c00b45c03c1e4280e44104583c81c54002034015440182000804404034184c1e14682e480c0301c05824041000004000507440800d181c0d0148071849881060354500c000f08000d1424640001d80100d0101c6c01b490300b480c400500001d0f591a00c858142c1d07400c1c40d210010f54a11005080c2c2010582e0030640354a00000802e0058105600807600c0080050b0f94034520700001f002c90340041c81c00303600c150030305914001c1c1d584c9801c0b01c0e5400421090065a081a20360562640100c49070310480c5c0016445040010351240d40d48080d1310705016100910449a648058503044005402404e026108100314554039521601c0a400e84c1c1d4481e0400f80410b6905459200080b800d683c480714600e50001001e011513181480000b46034032a01c2e28424480e0f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 241928974 1250 241927724 241927733
    0xe030d110c0604021e0411090103050601020f19020a0e01060e011d010801060e030f010c200705060d0902030304080a050a0c150f030c09240207060804170702010c020301021c0b0d 78
    0x500544068030034402c4400300105c42c3c50041414009000040040100c024004901001900701c6001140031a2a21001804550010402800038501d1308007810f1401c02400044038460300c002d0099810000c0300f1004189165000c0c50280604140d4444e26009180c2500050141c00c0c6013120792008a00a80446001e9170800101390540c0d20703070309002c4204001708012030318007495110011142d40c205008070840580181c40341a4035410021030ba2104044603608030364415003441115040a01000503058280c1d05901500d030462000701a80d103801d680c2c11383c140c640743c014541540c1c5508964460b000b005034000d4002c0c024683c401e081ca80346040080080d05840800300c5140905132070b210044d900c0c912070a4010080c00700e8000c00c0d220480c4550618045008130815640544200140481c13058002c14840c0d1280394410590b4102210041030104c10303803c0200124103000c0d5592001c070041e039007800a02020092040300205200030710705c05c8019108503151450103043c004c0900000325 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 241930224 1250 241928974 241928983
    0x50d091202090c16030306140102070602150912040312080a0b03150405010204120c0f0605030c0a0311090604140f010e01020a020409110d05030c1612020f0409060e030d110c 76
    0x181c0440d100301007030380e0f62803280b21140300303401080080550b00600711017010781560010059401c854018148502903000590760b5040302d001d48005a4810f01d1404c04c2d1f07040d510b02c900d41c4401d07804150b0780e0302c1d041c941c4d00700c1c50b03500142c00c00c5880340c6103800c04800017640320082c140e010181e16414013081e80100003090312050000b02c0e1190343c0800b240003c042c0030007501102e008150501c07244009a001d41410f031b0051398a801801c0c407008030701c400068410b100707100383c81c00340c60304061a9180402c0384200350002d00052600c0e04c3d140c0b50521514401c2d0b610071010300000c1c45030880340a040c0400320b04000001204941c541d040c01070004488006136030000e07048040943c1038030006590a15400d040c6081e20f91020260391000a00d60044104017000c4082c2c45c10300c08020444e075015410305044103520244e0300a12190040a80800c0003600e41010071401d6008003034400500650075480d50002c0ea000c64140c125603500010304644071541c14071a00c0803094010519504008a10340b0607500c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 241931474 1250 241930224 241930259
    0x2030f03031f0506030606070f0c090905060a09020f09100807120201030e010c02060a110d05150117010e13060e0a2910121505070f030b01021f0c0e06070807050d09 72
    0x61f600206052042200c040721540d0b000790080c1d0422841c4d640c4a45180103880b161800311503502078100071070901845070040c0d1054aa0052a100c0715840003410f002034031724014501009401260300019542d44c0a000d00070203801d8500c0c801c41e9540060001405541c00301034000c003a40e16140034500341d59804034529420003011038000c030308481295410682406000c0e1403100c0d4500c0c010900000014a079001c0c041d06100703888180c803141c40d5410010240409100c0d015510854200058051241c541001001da10495000403200a059032480c41d01e001c0000880309030124082c2040703c24050b800f040c50500009494000c58a05906411080307040f502c6081c100c21070f803106080400c1481214500c1c06600e10310100202e00d0b01820040c0f00550003448040804d241811141c0c40b0352010507500002d034181ca43c003c080403100701d4000c008040c810b0314074007000414a10082250348920080203070a002d803503026256017150600d141031508901d0000240300b007003c810002804502d540340c0c803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 241932724 1250 241931474 241931479
    0x120e1e03031b090109051c030306050a030f110109030b0f06120118260d1505010e221b02150a0504050d050310091d01050105061c050c0702030f03031f05060306 70
    0x11070301c00b2100145c41d4003c042c0c00450b0310031391911021048211103460040028040e60b4244440b0703542d44140440c1b88454040540344007462204000840e40e10300442580746410300d011104155a610344502d120404d4035160298545803043c007c4915104d82d0361003013080b116000b004040521025181c40f2007400e0401010514101e18808060601206103002420040c03202942c80317030392030340d41d000901e84010601c24810101c81c01003025441112601000c510180c040f07a07003150110701070040d006407212030a440c19200c03e81c0b60304203211141c40f03010305030464005240c0c50303000384103c810503180241050422460701d41040f0114a001859600c2441503003003040d41c0e0703150340203844518107545e000600390070708285c8610710841e08071081c2241d180e810300007003019907220f004110442c451440c80461000d151040040041c0c120790000c0d4109180c03010f074915044a9501013801c101c20203224400a1b04007104001c170805110810803203001008008036602410500041d003d404043c00550 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 241933974 1250 241932724 241932727
    0xa14090a0201081008010e0a050f010b0904020d110a1203081b040e0a0605091504200d1505030607171003030c08030619140301061202090406020a120e1e03031b 70
    0x448613081c03409100040d0000ca80244281e40800144c0740c0d803010a41c1d012202c3e40310b0b04880005403c0184242c1c40c1b107140c01442401d06807502e408001f40d5940f19201920036800400e62460f081d550040000020000721007055140303800c03400c0c09000c0c000000c01c20300d000321242c2c080e0203800c0c800d501101d040e901c4520a8141301e4455620450061126800860700719480c0000e000011120091841c1006800c0310b0500c030710004c0070400c9900460994034059400018400580b018441d80c101c201d0b4003a4109403e0781300744d52070700000c1c90300304151040c03404200c12202c001d1443e80e400c00e4440d413016480071140441c07861990700910700603900300090710700e080c0840414580d6403214a01400c00002020f040900c580320610500c003003a00710242c41c800d600e403000001d220745012103011542c5400074001e88450703456898110280d03000725074100401c24405540301c40040e00f4495245044d03e40002459107010103440300c0000a42c01c068214154024420004140300703c1c03041c614003240b05100c1a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 241935224 1250 241933974 241933981
    0x20603040f1b0e070e0102060103200a030602030421050d050a1b0315050102070803120a0902120a03021005240f04060e0a150b04060f05210a14090a020108 68
    0x41c41c1c0305a840c010b0003200c00c91511104090310030000307000d0340e00c0441c4541660b1035102c0c0c2518030041c01440070b400340c1c2041e00100041025807906030324901c800f203003518003006064000345100c4100e4000310f804c82e0b80403040c00300b03000c903060030a00d2400c0407044592245503110f0000d00030340521044840d0380341d101d00020300d28900b160883c1241e03130060701c0b115003400c0c9264406005803010740e02101c1000054000010305610004500c3d0448500c00d01840c5002300c420408084103900a082d2a001c0c0c0d2500d00400c016151520003540304400c05d030180c09030804503c1c00038180b00c41d141e108001103007884c0c14082082c0c1d080c0710b07180031068071000d0a0260b0007114049440c000c203200b2030960040c0f07440341c00100701000d0581d851144441100070400000c8590302c40080306a14058802c84c0318003480148541400394070070b9080350303001d400c0041c284450010160204000850410401e60b583c01c203021036103449000700003c0b031960070343c05c041c203141110055036100702904000c3d041154180c0407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 241936474 1250 241935224 241935233
    0x5032a070b0f061206010f0308070501060b0f0714010203042022060306051003030906050c07031b05010f0c080306011b05060a0b0a0f06080105010f02030903071413140402060304 78
    0xc451003203502605501c0700e49000c0542840c2080119043c90156403030706080e465558020400c20306907032005400c4c8801c3c60854440b840c09030440c1c0d80031240c0d0766950a000c11000e02d00700141101d18010120b540d601d042600c0e200f40d0140d894000301d41141c0c0180140000541040c0b485505035100310460742070b161405000640d20f40b00403c143c10b01085040c1c4444104040e40c02070720949018240070700c61620340ea40d4940200900c0c1c840030340029600e080c01d200030f40c0301c1e03c0140722150f034000171543c2e440d449440b0382e200414010143c0200c1100200204007e58009035259203c514906280d80300f42e03426110030341c96210080100c2d0412460310800301100c3c0b002c41c006121260844100d444c103103030141211000704940e00c0400d110b45145100003407c45180d4442c2e07029550300340d0300c50b03465034070b400015154294410991420b5000500c05040306880400c030f08070042c680140e482e00c214601c441400f1070101002c0e100204c840c144a00d08800015050405070440d6041d03540c10b50741d9031103042 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 241937724 1250 241936474 241936477
    0x3140c1005090901150e2d1806090402030708060f10091505010f090b1c110a0203160819120b0402180f010c0f03090603050f060d0f06020d0606051905032a 68
    0x40d090703448401c07a4010341d07449840703078483c11203031000c9280141887c400310200710b041400f16a4904500810703000040003820301c3d25007142c0182c40581100e80daa611451031a0030400101d44040511540400304141c0b03402c2c004040d0001c2c8150340302001140320344100c0000c42442801050b06105d95401c00140c454132030024030006004c1100c0c070030b40300d1b0b4100909000a0f085144030312102421301072583c2c0100e074038030100c0700707003490a4008610301070714000c9100c09900c0000c030030348148500781328000c10009440d100302c2c0c1d02c00340c83d6240c020304100c1340008011240a03505d0940554414060703443c400c054031030061007900e01140c2c0c03410190a5a001201d804c2205480180340d5402280b40038101500a402e82c0142c80c85c1d52018004e03a40d07403101c0c60243c40800c40366254030031503160030b200c007280d05030411080c4a0f0003510050302c4e1400a466a0096801583c8448000f034400075102c0b86440c03199000c035120400074945030b881d50801c0803e01099401903c10799a81a80b070700f0000c1e00e418540f10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 241938974 1250 241937724 241937747
    0x80601080405030d06031a060f01090e04031b030f030e070b04380a02100b060f0a0e04020c07030314030115080c0403120804150b150c0703140c100509090115 69
    0x2601400b0171a02c0c1e10300b0000008106034296101d401c100c001c80d00d1850310510034480410182d4030200310a00d020710355086410007600543c00d2024100510914500751900d00081500070344076118041c0a84000074205e40d20222140e402c5e400401060111918440c200c0c0e04940c111241100440000481c1c02249030700e40c80c85886282c005030b020840d5401040240203450303031035000d0300c0e8403040807031040003520200c884036a0b00c41420010410342018403000791512403002d16080942060f04030100741242d00c40c194400003a80908002c1007095800300080d00c002d805100600d044d54500107031110200c0c141040c400c18452510005000d41c141c840c180e42c01990001c8101c3c4500d010440b02401c40d580c00e071000c1d01d000025481100011215000d00303281030901601b10005070441e100041d42d0341d0440781b00d4034114041e005000001c24218900034547ca01d0500c0904602c0c004141041034191038109204148207007405590403569400400f1411100c00d889003d00592036548121800060003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 241940224 1250 241938974 241938997
    0x60613020c010e1006030515090a0314070213020d0e01150905091624020d0210020a05040905040501021b06070e0f061207110c01140702040e0a0b0103050307020a0e0708060108040503 80
    0x110215200c109107a00301000f03c80c014010740d4181550044540c9040b001120768270345c0c03540010305980010b0711488000300d5140404c842542060155400076440d421001d0422a0140e00403d12621015092203070032920003111000b00440c3c40010300c104290700f0144140c403140ca603140c00180405905000312009455040318581600e6119000000710010300c41c010320007003035940025603000703000041042d10004985c004240090351110018041d600c0401507508001c0d0138030000072100440c2c041c050003544a04d0026071190800c1402142500300b0b040403000c01e03444903007403162041d00070132000c040c82d07000c0e12920200d14903280441c406116070070024104101100400c401c0700e5101500400403009003007500d44054031703580110761448000840f001c41c2c3c40104003d00044c549503004203c0c0c00b2086c025143c5d2981c00d80c45000d40c550382684166215000021484114a800c01b6440041d02804034081450b0401c504000c0c04100018a8141031040c104c000c502030010400503506640203a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 241941474 1250 241940224 241940233
    0x211e050a080a0f0e09041101140c03120f0105100f05121e01060201020f09040207020a080703031805031504060b030a02030601060905030f0c0d12120203010e090609060613020c010e 79
    0x10300d0050102c0c0d1101e0580c000203000314000302d00c104d124030308045116000400c0020f840d1595100c0c0c950803484a4800c03811b201000f142036a041d02c0c84006000c10386840c601940d201c11003c00301101c13400000f089107860000d194014003071a509c52220f03400552440c980a42962030000080d200e610940c407005601094400401c151074003075444130f40c0001c0240844211507680c40d0000d82c00d0f4050784000b4102900144155916828554044c103512390005210722645c2c0d582d42c0b001401c013065500309800288012184252210305507a4080042505400400d01c0001d44e050f040741c11100600300070811512134903001e401e540c0c100b1030901c4442c0c004054039500d503500c0101500100c00c602c10780303010380a005094030002c5808148290b100c5800f4240d5608911560794201c5112401c1d18003a0a21501c0d01030369032951100c2c4041d501130000e804640c003482c240703099030518224005010b040f5550002040003500d4072043c02040d2151182407016072941ca4401e2514050076246a43c6c1603903118 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 241942724 1250 241941474 241941493
    0x61806080307121803080315041b0309050c06280e13112701140c07030321020409051801020702012a060207050c010e0102060702030910050405030a0f0507211e05 71
    0x30308010f502400b40001404a40323050001408140c0361041e000030000000004c01c0b00f070840c0260015104140300d00150b810100310400010345981080c041c59a45409000020351030482019500c0d0b001505414580e44015101c030010746c440071801d880200302525071a00d104001c5a41c0c0c240c0b40c000888a2040c610f071151942070940c0004255130007800a00032a2082c02001680c004451400e4014000b0b09402811514107541400c2c0389480010021030039410440310341c0c0756101a1024100340d180204140c100300c16142d12108a8485440c0243d01c100490300c0181c1e0407460100c2c1460504070795060602c2c0101c410743c0418164000a071005000007900405c1000c045a01d004c501c8098803440350300000d40004aaa44100f06c4050025030700400c1580e080d4a0841c10601045c4c1c40c62034120300d03103625a00481d003800d24004d011140040740e0040070040090600c10300c406000d0a61900000c40584911001510710103075010300030300c1000d1070854070140016100d5034602e4102084811034007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 241943974 1250 241942724 241942733
    0x12030506040507050c0705041d030309010603052a0108150a06080f010b040b0703120917030f0a020310060c1a010303170603121c0915061806080307121803 68
    0x2180c05038895841c0000140086000d0700596070f125200700020709281c1e0405050000500c11143d0a14081080c0c545454041c04100010340c858a8504004a201841c40c81c06e145071904d02c44207940c0013180781d0440828100842c80e03201960780240307840d81c1c0390b071242520034509010788050780350414045a1702140382e50b0000340481c00f8020364011208107070303070707501c80b40350320340a180a0203030011000c101d00c802092280301d400040d00d0350303c14001012109969040c0345010155480481c106001c4108494220034900042d8030007102c050640c80d40c0f40c182203400030440c86001d100300381f01c0c0e2502d41c01c082c00340d00d61401150001008481186584900b000713030074507100c03030842ca031650980400542c40f4100071407100b0100700044020390030034040003481c1c68044008501d07290f0040c0e48041600c042884650034210070b000c20400005d20506101150400a540c0006401114100741040000d040c001044900c5c0ca500301445081400b200c400480d100450b08010540da42d0341c4100110031310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 241945224 1250 241943974 241943981
    0x102031602071a0a0f12180b180c210f011d0a0f150e100c031404020d080703170a1a0306070909020901050f1309110304050a030e040204031203 63
    0x22926030225030b94103503105501c0d00025900310460303030504018810b1005181c082d0401d4180d00601e401d004030120301c3c0c44031200c06c8680e115605000140c40303614010901208000c0b45400c164100c07044480303145040d02140d03951140345585402824415010030200400040301d04079112800c0c1a01c1940d180b000d5101e02800240d010b803031000d040c684020502c15800282e2500c105d9014a000300303002026150f200e0a10003d80844441d00c1c1c440c180d41c55807030428000e400d0921810780b40020350080407040201290319440c11392040d58045000e000140c6d9a500c0c04060041e8003441035541c58030139203422036400404a0b0006400d040310803c1c010b4101c034541045070722804c900c00c0e44ae40800b5840c00c241e66944107490282c04141c4108007401180d6481d00202414601814010b01d0700004200701381480c0e201c01ca5018900f40d190505201d100e005008901c101c42c941ca010606608043d210030340c40b00c8566000a0500050b80c0f5110f040340c681c1d4046e900296000500c2151003041d40c80c000e0043e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 241946474 1250 241945224 241945261
    0x6080a020102061630020d09030905042a0c0c1202030d03050105060a0f03150e0115020705010206070c0303060b07051b09010803040515041e0602070806060105091c0203010203 77
    0x503000d440001151007603840500b52201d800350795000340c8800c5c0420b9000741420b02c0c071003480c451810b002c07101862510b180018000d00381d443c80c00050082d65818024808010303034200074407075402c0c000f6025040342a0710b1694100c05000a5160707050500c0c01056811980107e03004000949200300040e03071000d80b0340740c090450b0080d4140d40c4041c401c4581282103039824001c1075807240d028000c01c80d08901c580f480f000110810b040006031455480c40079080f46025900c07030b04210f1008001448220803078034000b0500c1c55940020078100c0d0600001030349032007006003280b08024601440005261107a0403040040c059003400729903a40305410070b1030301d903940c1c100c3c1c4850060303002c1d4070140d460400010305412035080130055410a400d041c100014103642d81a5030a64440074040801c140b03803905542c245c01c1043c480b102c10100d2030050041e0421030107a000006603000f10007044010b0340c000c4221350200408441c0c0141c0e241c0321100b0000c840700ca81700040d401d5803000c001c00c111099a000950003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 241947724 1250 241946474 241946477
    0xc1603051002090901060e180c0c0106050607020604030206070c05090a020a0f0c0c0501031109030d051b01050402010519110a06151703041e0312030b0906011814030c0406080a0201 79
    0xd010000c603103880c060748540d4400381c2d089014a4010846e5920070403003180c000170010300c842404c0c00ea00b51040c907040810b035040000e543d00050841c958040901c12180100000e5481d9420702e030300d40d000500580201c1c071020b03029000010318501081603000e410400362800030700000c000c2c100f4045600c0250008540040416148102140c603a8050b0a0098030705901c03d00420300141084011005400c40d02c14a02600c103060000308120b81d8203020368420a02659113a40c2c075108030400c1c095400c01c480c0d06203c001e91518041c400581d03802401c5a00b240170905c40d1121141d03401703c04031401d070313541040c241c2d043c0185181c0c0002c10215800a8202604c00c3e88075110300c545411410400c945840303032301005036004100c00c000c680306001101460211015100340b00d25139a80b240781145410141020003c1c1d9030f17910321912450210130b5142c0044003842c00b101c11022824a01c0e510380501d00801041002070201c16a4503601045500714005014109001c0702d9a80c6039503070ba451601c031404a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 241948974 1250 241947724 241947733
    0x3010305060a0e0c0f10050d110c0105070f020c0f0d0f060f0b18180f03031e0a0605061602041d06061201230601050412033c12020c160305 61
    0x101e000800013129050803030b004014490700c00d81d82c0c040010000505451009200e0107110300404018203100301912400207010103566030f051010b03110b0858800034107241c14054207480002d044c90340001c81603066082510403651620500000501080980c48010011b0081415050800019400100307240d5841c031018880005404208040084c01c1d0608410000384c0c40001000c89140306170640082d909a415960206104400d0701d0646d403007191040f40a10390f11828504a0802842e010313032180c1c0c400810054503090134002480352241a480c101166643c402070001e650380c540c842c080c07041f5032600e100c0070f203c00036040e15201d0720201c1d49103118440303040448500d288180100c4420344030045503042407a501d40902100c0b10005800241040760900021463382a145112000d081c06500c5103c181c5d0711795214208100404c5918500840e0081d08100200140c0c641407002e0342c60324141103070200200381c05d03c2c1c000e00601860b05102c0c0b10f40140200d124500c00c0030142034a000e20190b6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 241950224 1250 241948974 241948991
    0x606020c031c0c0b0606040b04080a050706020705130507030f050a0b030609010621051c050711120607050a050705071401020d030e0a0803041e06050613050f0109020310030803010305060a 82
    0x10b1080b031041e003500002050220404074005011040e4503680000000c18090a01c1c1d11407800203102e03006a040b48131180d10854024003071000070400d0000a0046200422805080101180d455040b0079040b0a115454502050515019801170700c40055038800421043c50550000700281c207c48102034000e00a040c08110300ca4010b02460381510402c000e0755462900c010071912504040c84000c1c1c490b40226004089811540c059005102d0020303a106c40d1142c2886c103081304054924401c8521803814002c48040b541808500705501c41d070281806a2140c5c480da200751500e10403404002c26501403140086101011880c5c2c3c444408000c1e400c96450341c01c01c00c03040d822180c10001c1c4201d25440320708140c000030712040c000c650080c420300200104941c080300c0c0014981e090030781202c40c25203440c100513041c244400e203481c0c103c01e400c4003031240e400c1030300c40c0160400f41800340011032070300000022074803217020031520000c550040d10150307a0345c2d490802980ba0038066840c050341905080320b2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 241951474 1250 241950224 241950253
    0x516090605030c0412050f030403030c02100807080a0b18010f06020105010b04080304030b06011407060c08060f0d1e0b010312020606040b060909070918060315141503100606020c03 79
    0x90b03030302c1038003078400e041e24242c00c00f1a10602c2030001d8030100c03014481c008001510320010720181c002103200e501e440c05405440d00c100244060a02c0314601002590020000c4281c2c0c010221900183da0311000100c0358801d2011030342191030303a0104180043ca081c00040d079010581040811100260b000300003517600c81e291520188258402d55000d50300030b01040c400304000503d01c075007142050500b5400003101c080c2c1c8a00740c0d040080280c030856595401e0b80e050300e8008054030f50151b41110542900510500000c2b40034000d4031000d8806001116803c1c1c108a501c00c40d0a070003500030240402d00c0d03039203140c509401c20711000158010b00802001c10b03060705150040344218140104801e04041c0c0000611104100c02001581000443c2030006055800311400075041c0b00664404150607040d4203140195044080882e80200e20742440c00b032440c040812119000100f1841c4045144000000641790440481d140c4251919107000003440c43d40003e24030074110720079001d59071100340010f213 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 241952724 1250 241951474 241951477
    0x50c073215100f09150906090f0f02040612020310050411031005060901140901090b040f090b0f030c010f1e17090d020304050d050a1403041701020c100c02030d0516090605 75
    0x140200a842001c0c1840b83c08511740010f8004200384000b00200c070786d0796561000b074a0aa902c018011603030795070b0681c60360070307203018841d820050000e0a5140030318040380140101d0110003001c18041c3d01101150410404440700402000028024014059220a00b0301213500548030000f05906007000020346040190546560110503120950455800f102c0c0c80c0c0c80358404100181007151030030010443c0600c600c00341c0054016040300c040c9248c1010302c801c0803558851303600c9114840f1842502205c0d900020b0090040c00203180001b003004646030160740c2903002c0b9015450700804102e101c2051588000005c030750203c0300f0300078605510b8820a150311100f0392820040140c004010501107410607107800c8504a104404581c40190a41c44564403400b1506560385141c200160070894803130240000d080c9000342c100210b00d0008007040352a504c441044c6049a19521600f40001d502e00032300565180d03c82c40d0b4000e002c01c0c9000341c407002c07080440403118004100140030200300b040c881c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 241953974 1250 241952724 241952729
    0xc080910090510020c0a020a0f15080112080705070e0412030b10090501030b01020a06020403061b020706020c0405060d0b101a040303170a06080727050c07321510 71
    0x1030160042d0b010407003a4038060f510204410000b480780100700300040c1c9881d0232410003018034910f450456820014120030070703041107860000308052100140701c680c1040503102d8001c0d500c0000c0554512051400c6800d02c4030070390200b501e0b544800c04000074010500840c804403050b5650070002d81602900b0022a0300c80461900c1c0007807030700a424811175009500000325007505004407102c0c41180d55408050741e006400450300c03c2e855001e400416058030080c00420105130000e0945d42e410120b000b0f6584100c403148520070358440c0080740a0b6106d44140040f50f6811102d19042890140030604000100c0d102e100d108049005820506c0095101604c0a0b41d915940f69040c0b01505491011010006008011010350312840042c420904105610081c0031201a650102d01e04074003418a80c0300351060301c40d04e1b80c109800c000307007036042d881201e52965101c0103003d2019960b5102d584512600c0d4444407408003007002e4140c02d0240041c400030704000741424104503540e41a0b42074104291803 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 241955224 1250 241953974 241953983
    0x903160e040b0c040824060315191805010515010305060303072604031202070807031a040614101e030f02091e0106260106080601050901020c03010c08091009 69
    0x2840441d000604541419070006600e0f000c440c2030984407a071480c200070204800b02d0500340030a2a02200350344013039480e9031180040340a040088a0108068100c0500400400b08603540f250401070341c0c2640c1d440316402d603100001010a10040e03242c500d0003088150341c96495036084084d04826503100c0c1c015a44214005030240d03050080d195a9203605207078408018030811604e0100d0307440070907030001400045003d06007030f90700240c075000040e062a0741c81c0c1100450782c0002e4001c0c004a00b06040c0c0c82e00500c7c60100c442210382d00d03400e2110042c500411031808000c00c0c034092085106c0101c8030681605c00502c901102c0b0040b01504500420161100600340b4244022000c058582800f2459101d4119444140001d03c4004007240c4641c00f40c101c0e40c00b00e94000c0d03d00b085061aa49003110a4680c4101c0c00c00315410200050005a0002c11084c1081400038107805140d100380070f26412214054001e00911030501001f0b031004008945560040c85054403804004d841800ba0400e4107400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 241956474 1250 241955224 241955249
    0x110f0c030706110c040212040b0f1527090106050103060603020928030501110d110c060412021f1a1806010315150809010510050a05100e0d0305090316 66
    0x10840c0c00d42e5401c25030140046540a00102c03104c4d50f45650005000206500310000e69514083c0b80582d16103901134510340c1c1e0444071400b0130158009490700c480c0f42000c03c030360688614280060307441c41d031140d8403088102d8a0a400c14001e030141c054002c20142c6800340c90a1150395203800d01182280104d4040503841a4940741c50288120f0384d44480e41c20146074101d410500b61a6112603080d20031020440003102d80c00502508440014800d402c1e4030340c403142e1124504204448010355404000cbc0000c0d2601c0c81c112045140340d402084080e4466080350b00000c10b03008034030495070062540d00882c0294103140601e0305168070340740728540104001c03007400c48042d49410004400074108500300241c113042030940458a00d001c00131001003c1544d590741742d42c0c0d107402c40c120760030f452015001d110800245c02050190355240000a415214203841070080c080c80e0540840341d105008041c250401c107440c902100780745d4440014603c0030300039001c0f201403440d041d05100703601c242d0f88925240c50a5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 241957724 1250 241956474 241956479
    0x513180605090c100819150609030308181e0309191a03090303070c11120a020406090b01020304051309140a03021501051c0201090f0b09090105040605010f0503180607110f0c0307 78
    0x15226583c500070358030b0040021f919a49560100d211400075040800480c10040342007080560090b0361b0359100032244100030300c03082c050720810f039a050f0404001e200d5640040e04440302d800700300140c2da82141d0080940841594906c002c1c20540705501030520511107128001c0c3e50065140200c0380a049038000545c51760b552040201c0b1030100d07000d402c5982e400d002c4245060380e92a0380034004142c041c8c03c0130300084c0c07481c2e2041104569203588610740305810302103405030740d86e0044240c03000c480d802d942000200d001d07840c40f80d004003003a44004013611a0740c0c00f50300115034006880e4422921980840300c1400440d00d050400072024416158407c00507103240d0051000d04900c0300080744107040100e01541c8880c841a001e85040d003242c141c891000c00c85901910700403c030310307004100680e1700300181c50401d40001c150030290303044039062000c000301003018680c40b91403101181c1c0540e010380e441406c10401c000c1c00c0b0782c608101000d0510949075a90140780d0080741950311000700500508041e40b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 241958974 1250 241957724 241957741
    0xc0d0f0207020102030a211a13060f15030905060a02072a12020102011508010e301e0406050304062912010e01050406060e090d090513180605090c1008 66
    0xb0844022034401c0300303544c0c41800f06140180180300d24220900e106a22101510051048550030000b410102c40d040ad0420030000c0a5070b045a42915041e80d04071403044169402607028021184000340144518010040920b0f202d5028000c501c3c8906c11540034040c00102601d41c05400e4103c5804941b100c80f810400f1600541c2100015403040c000400c4600030a00080c400c001c40303078450322143e5180c0b911881919002d0180c814209a46030072a03815484000301c2c881d04c040c14540002c05d1300c40000390007120401840290b515050394103801039441d62a42401002d50300150b0b0120b4400b81018038030900700e01c1c0d910200d900320303007010b01e0f0369014010002000303040d4100401440d000c3d5a514450b40c440c5030203000f070b80d1085000e40300114007103103030182d181e04e1004002e140061036000900d540d41c44503880106407040700c0048500116034881602c0000082c10820f200082111641c004c21701045041d070001c40c031070240042501d182c40880c0d014002e022042d000c2d50000141250005804c11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 241960224 1250 241958974 241958987
    0x603250b0721020105010602070909110f0f030703111302070209131103070f0f0609060801120c210b07050901050a20060f01030c050d1104020d0f02030c0d0f0207020102030a 76
    0x60241000c6030400810b8054542202120285480140d454a0040c03081c1038040204000a02c42c0d6442005200002c0e202c04450b8480c4462030342c410007299800e120b1954500582d0350a2010040c00d03603520030340d0f902e4049100110004941d0280f0300d11021b958240c400c5109551506070040c00f42402d42d5101100c0703030705041207010304482408104034141c10302e071420025000504411030f040e00c0c4c0e690810100c100761407001d600100400c1040802440155400b000b42811660f04500321101d40002d032900181c00d44c1d0302e40094261220802400c821442e040d5882c1c00e1042c091418041e86440d43c4604030368511503030240034040b40040142c03042c05441401c40c20305550384185007440d0640989202814403106490400c90455000010b0051090200d075040c0201000c40e80c0007402c056a5449000c80704022040c24410382d40485d4000c1c07108600d8110342403880300d05000710364908e0301801a005030780224142500d014601030100c1c068a00350b200b15014150141c0056042002d1640d088a0300d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 241961474 1250 241960224 241960237
    0xf0a14041a0313050601091d07050a0302060a030e151501030c09050d081303050a12030903020a0209091c0f0e0d170a21051816030602090f06040306050603250b 70
    0x72410203c100c14041001800098041e10304c0c2c00d4080782600841224129030140d0f0b50781d2540c2c517046030800b00821341da0b15446400301c0b941900ca60391903048046080d0001c00b050a280402409002c03001400140d50858a41c03084030561030703900d90b4580000c01142101c680d0301040d008120100402d0000303207400c00f8918402da1084102a00e0034008940705034800b4090b80c4100c0f0185d1001c1200d008000141c1d0130341c2c04020fa18a010003006000d900e000f0343d0b840f8072100203405100e514000c600c1102051102c41e031404540e0300751070515020000b006100d041c101212a000405030482140c0c01d01e0024461040795402c01f6880310301c1da6022000105a0b80070448000500000101182040c00d00604000010a2618001a40c2d02d0048a084d03072000c014111940309801c00644e01458601e04400303036084d80d40165006840301848408680c1c1443e114070300303e40c0080301160020801110b80c106501c0795070140c00f43c41c41c1418042080c01011001c20f40348010603c0040c06014442c1d0300c0014110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 241962724 1250 241961474 241961491
    0x60c0309090f0b1504031115030411040204090c09080607030b030a02060d0216030905040501090e0d08040c080a0b0103061b020703060216300e060a03050402060903030f0a14041a03 79
    0x9a2890642c0080d811044c241c0701c004801d140840d040082c880201d4841c210150141d482851400c0c11081142d020f01c4000c0004040d030b14102e094410315111641902c01500702035208100b40e4000c0103002e4207105c02c0d40700300456440340d800050b02c0319100340104000a00c001d002030058411550802c020754110303c80300010f83c1c3e401d00c815555006842d08902c661402038407034154080c1000c06110654030142c00c160062402d20500352808000011080f94a45151030a500a80c54502d404d4a0681c031690040d10113104d01043c040a024200611b1030407644075950401c0401480c00742401003000c1c0720603407005604101420008a00c0f10380060108200c10b4401c05154140c40d82c1d90816604842590900c805080c0c00311031641010701c040d800c41e9002c0c1d0800c20b240c8000c0c0350010301300d440740b10320385401c054450300480c4c210f460306001d544c00c03800d00030b09076900c402425200c1e035203581000c01080c000031a04110f4088111441e4115800d41c3c044003801682d882c50020200000d0348080c04869 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 241963974 1250 241962724 241962731
    0x10e151c051305070e1302011b050303010801020c0f0a02150d0b0904030302090405060a0b031303200105041e05031e0904090809040b040b09070e060708030109050f01060c0309090f 79
    0x89001886104251146040082c1c1e550000c8460415610700700c1c0c0c541140410000324018010300c030060f10314100c0840d509180000c441c2030501085007a5120740d403801062480080004207400c0419000390510500781011190712180041500359030f0092800c019400140c105850b8644102407002894242003004001c03540420101c0810b82e5407004031030a6000940c0400c0755001031603d07004594021100311110005241003c0d90354201d840050543e18060201115032400c2502980c141d2001e150080000081502c05c0c0e114240a040d00f1201292045504d108580c040e00c101c01003101d01d141c1043c021410300320140b1070440c5021580001c0481e240007481001c0d4a51f0b5140520089a481801a99203078007003081448190f507141c000891050342051841141a1600c18070144d0049030392801c0503240090300c012810b1072043c00340107800348100000101d07207581190007580c094051034500000030307a40c0d210100e405101c001e50050018421744000c00110116420071a511444c0c541e001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 241965224 1250 241963974 241964017
    0x40b0a03230f01030b241002010f052409070804020f120a050d080c0a12090305090904060603050c040b010c1b1502061f030804031b12030518010e15 65
    0x2030310945000c0768400c0b01c070106000184100a203404600750042030700001040e000c500c80e40e200d04240d140e100c44500981440d03941c0c42c0310714400d400205030690301c00350800ca1820702e9445844145060ba2038001d82c0d02d0304261460382c6050007030b0518404e00c4956140180d0362215420441086c00804400e0f601441500e18091018018442440321a215100420103149615005090710300c0041c00041092002c0c003122030301c2034110780f42691203688180001500c007174501d802e45640c042e00042580100400b01000f0400595910443c2a00d002d24121008020b000c4200400e82c1d44416000e40010880000c60b0009900f035588200d84800d80a400380e00b1544031802141009214882c10005900080a025060591310302d04d41c10708540c104480c0c00070f8155180d21480b48118880109002070f110009140c540c07040120201030811401c0c41c0c658031503e410014030682001c401908900090300d420540b40d8046e240314005c645000d00644004488030718415026003002d130710400640c03008401c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 241966474 1250 241965224 241965281
    0x215030604150905060f090c0f07052e050603062203020c0301110d06050604030f1b0305010213030506070306240c02060301080a03020706051c0b0f100e15040b0a03 72
    0xb2003c1c10340c00b40c000582e4a0300700c0412502c2246000101d0061106105102240c42c010342182e990b400000740444d80c078546858418a0304a803100003c00840f03510100402001e13075111907880800112a06021030b0b240e0f401099202c01007501e0203161540d00030b03102c1d0321580c48441049040c5000340140d8402008070000b19081d1040703410001c001a0000622801c171050034410302010741340940d4101e080609650759806040c40180018102c06d039484010042c038100e040041c2e0265a1000007551074034404030380b10700f41c20014041140c11303008400c0000e803c0381c0300c1e100380d000311410012048120080458083d0f444034030410040104005040078001503119080118000c0170403a000b00030355055810f0007800c00320702ea0401800c1100030040102120306d4290300040c1c540000034005184541c6100041c110f0051074810741e080010120180059900040c20144181c010340f13030700c2204414003000341c41d58441c4bc040d0420081e0140101110301c2d120b039102200d24640107002d0640030180041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241967724 1250 241966474 241966511
    0x80c01030b1c080306102a0203071d0f011217030601021219091703041e08011b12020702130c0c02060708040329060108040303061a091c0215030604 65
    0x1d055502800004c00e004041c104040003041003c241c0c94040140c020a0320010404800c84291448494106541c1c605640e02446007000802e0301c103a0a0302c001d850411700c61110346045541c1c4044040204c00020700f4620074204c4500603500c159250206480000b80721056000600b8150451040001c902c00c5039600308010807006107855800101310550b090028041404ca0b0007841c110390000c20130410041d00001a80d0070380d0501d01c680314800c40c00d1a0512108081940418111360900300300070b01d0f44c034a01d000071070041c80030380d100a60000b112101d81c040c2d101d1618000d4000c8600800a190260740340d10203604080c56141c1203c0310b6000c1d0f0005041a002844140e8503039000041c20010841c01e0f6030b031300340350344400e00402d2203264803c007028110942c010070075810f0050010000741018401e03800600034002014110f4a5443c00101c10b0210f500040580d502a40030b02c5540340d007000140b6400c0d4540c1d0f50003400006221100f941c100744070340025010342d030429120300140da8100c00616 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 241968974 1250 241967724 241967779
    0x6042a0516030509030105090102091507020105190e0f0a1a180d1401061e03030804030e04152606010b0705072309130302030a03090c0302090112120207080c01030b 72
    0x152144d868078944010182102d80151031410568410404800d6545490940c01d09113202003402945421181c00140e42c21311842100340011020301d84603d02981c0c02800340c083c0c5003010744034a90300780420014020010380c00d019a00c190000b401a011500da20340000344200c02040c00f43c400d0110700400071924010710640300b00e903007446000b182750100009200759001000d41c0c9804180c9404000041e0210103200c3c0000303010003ca0720001801d01d03018040920a11001070400c10a214044242c400d00c0703d040e004000e204032803010b81d00d28503402c400f0101c03e4203643d40081d1013070b40d2820303000b02c04581c850383c412901c0e0b000c3c4070b40002d000345004521054a03000c03c19244009165102040250b010003048984005d03000344220300030030f0340001500e814040350f050004001540d400c0c0f100c10b40780290300003540901070130004580080e001764003260f030512440c0740000c05400050140e071100420b028108242d40301d10790300b503015071290300490324059001d1300c80140744013402158200c3c0ca1440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 241970224 1250 241968974 241968977
    0x60a0e15010f03030813110d030c0b09010605101107050f01142712060103022704080c010b0108090d0c02010302040e100501110c0315041a040303050a0506042a051603 73
    0x40b6820000d1541013000310b40d1054a407503400c5840f0a4503920500550707200000d0b9030045480351585401c25004962408000d0b40182e01480e2500d08184182d0192200e809518050055070000304100380c0a6950340034003050b102d010700740850400041c13010707030101102a14108102d4103e00b45c034503040300004140f564140901d8070269644001d11000018180c1a040d000b0581042e51074411000841c05506580c1d0407200c1101e482011204805c035151070309032483c05a42002c5c140010422458001c1c80c40149080c001d0144880e900300556000c14111418145600f00c1c1003021900e5114146000d14036105060041c203280c2c98042e251088401200c40c401c0b64000a601480650307040303400040c1075480d0000030003400d03041d41c020a440b2403440342c034154007200d01000300c0e0401121038905401d142140e135821041e85007505000f40030b000103407a00d55a592400000c114a814240105c50031842e000d0340c10f11080390a03803032020142c0103c403014002c01005100d069181d1103803001c0e03408070038001e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 241971474 1250 241970224 241970249
    0x90403030516050901051206031e0105060a050103090804170109060c02010b03060a05190e010e0609070e0108011107020105030411030708250806040f060204030503040e0a180302060a0e1501 83
    0x451241c0300090000009041407260504c0364031090307030703124007165812010702c0040d4280b51100800b09240c100c81c0e545010a002203180c015814084c150702440c40741104442c01c58030540d98030015401c44600c50006001e95408010038030110300c00850103400c90069000008640041c0d8075004126488101e0000c0180d4450031080d8142c42c0c00c0040b5038000c0e966900400613400c220000103002c100c0940000215915401110b561000039400703490325600e03030020345e8400c0c0780c000c001c2600c650702d5014055903007000703000100d012801482a81c2e0600e40b004640e504d458015001914283c0005008549446120a8082c020b4500b448100c0080c000c58000784010358084001085000c1d60045414823000280340c1003112a2000540a4020350003002400216802d030600e400a440f0359000a040c41c4000034001409440850309144900346000c1c04103c601030070304401c51203545440002d80180c0c01140410011041c41d80840251840c00040f650604a54480b60303001420903400321101011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 241972724 1250 241971474 241971481
    0x506040905071e08180a021005030f0c0a0f140c070303110f0c10051b03040608070905041a01030213050301060e04033c0509130e0c0d0c0b03060406050904030305 71
    0x1004070f01c603e0907075110700d103165803a200746030000c0445800400781d513241800106001d1403500e0520001c200c060300581408454003001401800e40e40c02540d10f21070424440ac0069544009030b4152080d041e100d0350b130030344100000081250840004c00301c2d4601080100802c00c0350140c200b00050046100c0d8a45c1c80c4240c034202c1c0c0d0070b820440c404010210702d8011b101c61082d941c0d0745c094480038400c004d00300f058650082c1c070303041d16107641594041000381c403000a0214510b50404104ad11900c0295903500c90203813900103010550b0140303013101c2008120281e60b424190700070b8015210060344020107540d8280d48000003402d617541940003c100410700800c2c4814990f00280d004006260b290030300404824903041043d00742002c0d081c0e9503440b80b0480a01019030b1142c000c440c5001801881c500d045004c0b1007421009104121090105201c1d2486401c080d041c4550141d11035600011114111450503082d05980c0d8001080c03254001e0b510b2001140d1942c0300d49980d4069406541c00144514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 241973974 1250 241972724 241972727
    0xf18050c01030b130c021212190204030503030a0506010e04020f130b0f0403150624090e010501020c040905010f0c050301090b061e0702030a21170714070804050604090507 75
    0x1030010340d000341018100040122140c84071a007400c091300d15154000341000d40c030340c4200c2c10142c062141400e0701f800002d40b031003103006003140c2500851480d222a01200c6184030340788201d1045110061403a002440041c04040c2264401c0e0762001c018109440c00d1034802c0d002400302c1e80320300d9040240880c0818000c1201c03e0511045014145070604640b915504022900141c0100e20000b420001b40b03510300d03048140950010b400902030a01c0205240500e15081d11421006000d8040001c1100d4000150711070056a0541201c0040e005401e0703080400c0d0a12014004070030050314659219950380d2540d0846214201d00810380765030316030b125410801345005a0310022201da02c206001e101280e000c04041d1180c06040c2c0000b40b426036200c90610100e82010150304000d411072094138444142c20108194820001c06981d41e1885058192540d403414001c3c1501d10000041c0d03010a0903141021100c01004481d0081100a0625a69000180c01540160000300d02e65407200180710010303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 241975224 1250 241973974 241973983
    0x31002180303040506040e0c0403060c1106091501140120010c12050603030d0e01291908030301030227090102040e0129032206020306031207030c0b0a0f1805 69
    0x1403044029510701031419000030803902aa00860420110f10760100d8030814103031007100c0c011544503409200303e4400c200058140700f5001e101d03520a003e203c00207540c5202c003184030034104c2d514042d2480700b0b90038694507444441c100a031807418069040d401d40e8500d08003121682a0f820380000208481d41003001c0200740c410b400013074900450410091140c1c650b000300641d8541500d4410010340b441d5044040d80c05042c0d0b500500c1020703070402c410300900038070382c00c40d400b0034131805d0366880d402144004c0342e10140c0c0e00902c15050745810610060005250180030740c1d6100d10381000000d0140522a4480f000542c255509152a0b500150030018892003048541c01006000c8207021800704179058850070400c01000311050100000c0010b40c008002198040d0f44d92450b90401f442c1c8480780342002c02584140d50052003486001da66824200c5c26408070f40085074165036901b01d0841d039030b890301064a000341c1040340d02501c80030903182d60070140c403894038480d014201480460b00b4604110f42003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 241976474 1250 241975224 241975267
    0x30f02031203010e0f131506030b130807020402071407060504050306070f05090f06041a040519271812030501050f01140306030c0409080d0501080a030801030b060f031002 75
    0x2400700c107000400210743c1c0c0600f440d5004401200e07111a1765500c442c0b6030503000307007108010004580e0300b8076204600c0140d4082e0040d64480c100d00b84075521048064990421184001001700304204100801801e054015103c05841001d4110b08041151222414403205130884400a04049002c004a00e420011103030000d0640c00e10284001030740f80001c003940304442200703006806000d0200f8498403542c00300e4008045809201010882d181c054607015405441510b1058900348080b0392140707615400c40d1b040710040501c42c5064103c0031085140700211151683c181647d520701c00d84940c070803024240700c46101e945800b80c081480b42c400790890340d041c2c001381e029091254404d803843e60000003403100072550904040c0c483d40c6641c006071400c901da1071040c0d04207040a011030200300c019409800c1052000c601402680c0e02d035030b00d0a64410888201030001103584004002184103000981d400c081d014102d07140c10049000401d2500300c10720507a0141c2c0350f00098000c0c036045415010882e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 241977724 1250 241976474 241976503
    0x3120914280b010312090b0c010606090509010501051e1306080910380301090501060302010906030203150d0204020706110301230904060c0203280e0f03070b0c03070c030f0203 77
    0x50350807191112404924140002408043d0b00740d420b6200a014007610340061803016101c81e5100f202030080c5000e0708083c4114808941d40c0a004503403454450303410b9040c1d8804ac1d5903541040c0c10100c1d00300a146011101c4d4441040c20018034042122440090016026a07101c02105040060300e59250841341d03814103607200c0c509060110034030380161540220000e180243d141c00c2006010007900000701c03102183d8103600e00801d103020400190820006c480c000d80350310a2945d075070310703058003a40b1044520016041c40d01d00c80000c1da1412568000c0d5141c000350005040c103c0c540d036101f0848000b4508415074501c048010403040405807210301c100183e2206050058001c40c000c550000406040200040c0d00c444035102100e10800581d090450142250503102c400480840f03a074803c100041000a001c2c1901d5000d6401c04000e1071440210103030090522514040002e440c0760031850040c0d0b89800304211107000701d8038088000010710300880d80790360301e070582e88101803a00a2101d5142e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 241978974 1250 241977724 241977793
    0x201021809070903030f02032b0c020d02030a12020909150301060603110306041d030307030c08010911090f040f0e010609050105100f08040c12031107140d03120914 72
    0x4816502c01c80d0f100480ba070504056080d01e41018069046004400c1101e2541c1308400e0101ca00b220348458007040071003e00c5040100c2c03072051600700c2c0ca0b081c140d90402d02581c42041038204252041482c0e82003c42e194400606020000e00000c044540035900000c4000f1184450206443c003841000c4c001d0079030341010800e00d440c0c41001c1c41035000042c80c9520071a900c11940c1000d10382044648004e40c5101c054a6582c40c015001900411034880807000203a011740c00402c400b0030310700c2441da07622040c3c2c4525007444400300800002c0300c041d49078160880e0311101781c42e10400d624002c0e10800c10100c0000b14440e03040014807000c58105a010038410f5841e89104400f454000480300e100004038607140640e5074545c2058009040ca80d440003400780b0020354210141036000d00001041d103600c4041d40c100c00d645022420021904400150b07204264980d0080002e0044541c4a0182929080821030009540301da445540003d801a412034004894060803a400c10840002015131012450b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 241980224 1250 241978974 241978981
    0x7090c030507173709080a0807032d060b1305091b09060f040e0a05071b020a0b2206180f0f0303030903050702030609010617010203190216050d0201021809 68
    0xc40000c1441e84a8407001c4c0c280c9640c3e8004e1400041194036200d5a80014002074125190800c2241d100f59000c030b00042c0618082515940f013401480306154408812035151b0b14050034150488100c1100500362035074881c400216100b000b405815101c1d418514140c0d4146445c083c0070110000410101102c181e44841080024000e07040c2e071003800c0c0c181d841c1526180d07000c1405440b031191784c1000c034407085000200422012290045071181d41256503d42d91041c1e007605c800300504a14070002d502001c4030600b0710100500c1707006000200d90301c0c0c00c840000c460080700794600281e02e4100c032000420410b075900340350103050038032002000081c4915100301e2400c3c24019980d80c0c5800020100340c1c483e5407034010f2501c80c00540b80c0c060303001403e0302e606041040000380200071901c642c1c000c0300b042d13241e550782e02c0b601882070741d1183e81102c0c240b040001200280b40300950101010380038403a010300941d008200100440c0c80c0009440c0c000580c5c6018642c0341031020420310f00040d100d5281c0c403041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 241981474 1250 241980224 241980241
    0x115050a140d0507030b04060b0402030603060c0a03140a05070e0a060e0103050a060b220b0901021e12070b0f0c04050d1113110315010e0d0b0907090c03050717 70
    0x1086030110304030720144602400000d2184040510003034900d12a941d000700500c02e50031042400380f840f07803504000e0701c4000002d00007603001c01c032012641031704010000b400d5410b541c4000d1030110104d29000440204584005008540a40b002c0c0d41050340c50f801c2003091600440c8548140d6002c451207140302e0b140060003000e080b110701400c0d0405490740c1c0030454103582500300c4409000a80ba8141c1c4810581c0e215160b81010041200190a4405000983c1110410449000d01301c180c0c06030502b01d004000b12003240300611070b05403a40c0b081d46141814291032001030483d55108074581191410440201d9400800240044940388e6003040100000e03540d000301010600d620110194618021900103103050040d60b90045030709040848aa011700307481c40045210322200b0030740c41802c0b07400000440d2030074405294981c001e641e040700440070582c041c0307a4950026030781c021030340d0250f25940418241c41640b80b1400200740c641041c055011341280481303400d11342c3c0c120110b10505c0c0c100ca5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 241982724 1250 241981474 241981489
    0x30b01090207170403050307030305011a04090e0c030115060f020607051206041b03020c01061a04030201050c010e0304060c1509200301020f040305150a1a0603130c080d02011505 78
    0x39259a89900040300b008010020010844800c000000d1580303030b582d41e0a2041d01c0307901c50a402c034000ba1500c000410390001f140d20140e401c0341d841b01e10504242c244440e010040c9500150f4146070b205aa100c1d01483d5024004c580c09501e41000d03070520795150203000383c40e29011030001d1055400200030400780f254488141c0e86d00907500b160b41d13945900c03480085401002c000041d48522030300600c1c41d030b10b0507406d42c00401090761040c00800c406caa6441034041c40e004002400e24010b04100300402c05580700d071004e032694040100000603441c9405603031500c0e5500c558007801c04116207003000e0303060040010516032181154075003402200c0580d80e0364400d40f00300d8032845845020501c00003016032401d60564821081c8820740c25952503c07401c14550b1129032482c450480072003100010310b81c9240d03006401007030925880b04041c004640c0c0400c05590002420419000d5818071628003046c03505800000802c0c1c03020142610b150320101c02401d544603162900c85031101501c0c1044607803100340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 241983974 1250 241982724 241982729
    0x90f060507030c0f0618030207060216030f080c030d06090b01140a1e090509090f0c06070b070309060e03130503060603190f0212030c010209040c0906020a0605040204110d021b0106030b01 82
    0x120300d00c2c204030292070003c005040d44c0142c9200c40f0711040300c6c0300c105074000071008190740c4a03400300e510614086150846058890100900d2031a061141400003081040641020403803081940d00300740c800004001101c4031503001c020a26150761140140d5600011201e445801d41c00c2050701d407051010020b054115800c0462001010498981074201e214280803000fa080041034140707a030812994180d0340e014118804002030140c140740d440a032a107a812aa88203902c907048003400d81d20490f040c0e00034100c6110946500d42c0390b034481554844240020020722194024094030642407000341450444000c0140d40643d00040003d8860482518032403800c5a1144081c1400342c640e2000c5004c0d011140c10f0302034284000b043e0581485010b40281c00b1090341a9820080c500c11a0011108a0300034441c440c056002442d2010119071039800031035001d4000b40001c1224a00c400100045a014203a8007405a81c080303000000d10035100400b07003a2103000b034000d100307160464031400c62811061 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 241985224 1250 241983974 241983983
    0xa030614010e06190207120c0521060c0a2307030f1d130216030207140a03111e060307051b0f030307050c0c09010f05011206150c02130c090f060507030c 67
    0xc1030301d1301c03030180b00308014000b8100f100c88100c0c00306d0350f41c03a02010201403409114445e00b080300c0c0421261f1511b03260095a5050a802400c4a40303603c0e50b5041c6640c03080c030b6180100103080e6090300001c0c9903030880700d000c0080c02d401965680c020307041c02051036618070705001c108000b54482d22407401401c01c440911a8080b2001c59000080e01001002841030341c00785041e885900102d0701c00c0c1500840d45c0000c0b62142248040700d420b1180070844100000e01000f8100c0b10803025415682c180520f541041d6400d01c5980c000d00124400001c0da141c000300c980c140052000604600c0290840516510141e0343d4402411001c1c2c8000c0c085440f0b0000130f101c4820008041442406101c040005908202c00070b8603200312940c4030201c0b10402180c6010343d501250000800c032042a1481c070441045502e03291010811480859007120f44201074801640d10052041a1a2804440744106158214a9111220240d01c2c040c0d00c9078145403541d0242d018082c052052502003504040d0103007206500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 241986474 1250 241985224 241985257
    0x81e040507061d0a0e0405070812070b04020d0c08030c010f1103040b0402010909090b27070e1009021207110304030302060103110d05010513051b1c050c060a030614010e06 75
    0x501c03031803801103103e41009036002035480c4000850110f940e041601035402501a00c001c0354a400085503a804550090308c0e00140070000c25000c00c00701904107030000e200030000c1203c9070301512000442041904680c405801c00112443ca808d4240b00d15020fa103a00c0505001c0b2b0016154111944c1c007006002a06100006c00090110384c803a80001015000e5a9410000c1c400617081000030a21f04450103400c0911601f007104002062021403910301042c440140036050a01c031602c3c809000c040c0c40401d207501ca0210109026030f07079002908404820f0300c076000040c90642402000524940300d00c0f4082d070410002440420707408940c0d075064903003140e11200001d01460100c1c0c1da1707000400c0098600c0d46003c0c00c0c81809541519001040d0b40203104442c902e003022501080c0541106843d0f560045c019010b04070055905004020142e00417001c0d243c0c10800003000c562582d000c5803824000940d14442405211042a0390256441c400e2031f00c0201180c922010170414881c0800e5000c0c040d08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 241987724 1250 241986474 241986497
    0x602120c0102040810020301080709020c030d1d1b09060603041a0402060702120d08010e060307030f050106050916020106140105030a09050a020604091d0a05030a180b0a081e04050706 80
    0x3001d40403074005000314021145590030b050000c000a40003805240f825000303260000603158014002c0da6650749101c4091454056041400c8000307111200790b0307081e85001210161720314002480601400b408080902804016202c10410f502e40020000d500c01e080500c14080814240145494844084a140a800d8590740001000b9019148000394414201c1c00143d4808201050031291000706072101d550603602da1142c6580b1210848001b41c159214440800208e0464282000880c0c01840001956903d5401080c44020304032044520300d586002e000710f41c10707424840c03c1c00402c50300780c034418412001e1000030aa80310262400c0c0c0c00035150a452000e00005102001d4860b9005060b6a0f0312559559044007504000b40c9000c0d00303105c422881a07103d100801c205003182c1d03111002c8c51a042030b5a04c1612a50300c0002c10807892010300c2d0002c510140008010300c0101c2d0b1684231000e443c034050b4080000b00f101c802d18003202c2105c100903c03002400c00100142952111f0070031507032414 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 241988974 1250 241987724 241987747
    0x5040c0302010807180303110c01030c050d0902010c0c0306060e15030703110103140f1006170f1b0c01020d0605030f1c050c011b020105010e2202120f011b09060212 72
    0x50301c00f02401c4c3c0070682c00b1000810588c2060705540d130500c0c000305441c00c6001c82c42c010350840c0c0c0d45c40800d0010a900b0403110145030701e0380c2d110f0b4000e00d1050500322010801a11141003844440d00304031119542c8a0701840740d0195504040c0d84000c0030450a641d0580c1040401d440f0400b42c0700c01030880700b01a2080245a0107038016440980b6101500c07486450710172425444840151030441001c56445000315416108640c04c1010403400c402c04130341c5032540b400318280494001c200d06402d000c64031611421013240d40013801c4031100000003603180d800c0c890354401140d10340c1c3d0155104c2e41c000c5602c07141c02d80c4086040b042031081055184010b440348030301500c16108440c0803403025440d08120822800042e40e144041d840c032540200715a0ba00d40946c6000118262041114400641c030041e051401c4190501c503400d00c00f4052060040750160300e07a18180d0725011074074440e51240c0b03240400c2e0201044c803200001c00d52518036600c5140c01c001a44401e51406c030303003803c1480000d1080002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 241990224 1250 241988974 241988987
    0xe0a0315051506030f1015140304061b0305010e0a020304020f040b0102010f09052b020a1209150804050f0c060703031512030206010f08120d050703140915010905040c0302010807 78
    0x4000075181c9035883c170f030007981414199400c039400e14481c0756400c0d001c0f403e10150b00c24a4034070160f039110780744140e48501d580e91054000400c1100c460b80c894582c1c011094004008130414486510081119410101036250802008116504c480c4c4180300300409655040c40b80c0f000c0240580740050b1008035880100c0c050300001d12030000c00d5041c810141304025000618691054414502e030a204040c5003500d40b541c0f8011002d01e0040e84005030900204002c0d41c00f91342d829800b03003484982141e48908042000585040c03907400325203c0000c210034410144600440038a9850203021008020000950a030103544406410142d407048034200e440e1401d40e00300c02601285103060f03015119854001d41d40c0000340149400300625440010b41c00c0b00019034a10390502a0184034140000b40d0700d0039004103001880c0070201601e4030500c144c02500151414001d11504003e00a10154200085a4884181d002b810803e28100401001c00c1c1c41d0009401070343c2d07091900302c0c030b191107698044884 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 241991474 1250 241990224 241990261
    0x9010516050f0c13020301060c03261003200a17011805010207021207120609061b02010b0f060906030c0708070b13030815090406390e0a031505 63
    0x7a8407840d203410148101c000741502d01d001c01111800d08002c911480041680400e210b503002080182180d880001d002e00700345100c0c0d107002581020400700213002c0c1d1a1400c0d0030b59041200c511000400d206001c440003154010483e0f0031a04000e1140c55070100d41d50300c480e4403170030b0300006055000b021040020b40012a140226002c490122081414043c1c000d60080304200e2091480c3c0e14030030720303000012030918101c90a044c4c00340c0c000d41450b124400a402580800c584840d40d6445501006101b1001010031036090b60000030001900303003d01c6800081070382c1d0240301d00001d02c640c4109940f404100c030b80c406101c0140302d40ba0300b07980c81d2030310799401081350040074444100d0030004501c4500c1c500843ca0f0307020340d98010300ca49540c03120340c005404144005e5080701c04400003c0100c0c0f4242c0080b160841181d04954403c083c00303c1d40d6411001d00d10030311031242021a001c140907940a010030b140c1c08011200164540e186a88503c2400b80c18451000e0164403500081c030b1038402c2c241d84072071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 241992724 1250 241991474 241991483
    0x1c05040906030503120108061009110702030d0c1b08070306021602090a0b040f14070e030718021201050906012a2001021b0a05040905030c03040807091b0509010516 72
    0x41c81c2e840e442c0082d140c2d00401a03070007100f0000d40c00007a0711000000c0d803038081c05440b4400c07042d05003400c5080002d850891820142d90900304110401030b20300700030341c40d44441c3d1a0740380e0380301902d2450034840d03030046040e0492040300e00c507800380485040400d0361000c890703010f80010b0340c403050040620303070382000325501039800014032080241901c00c54024a240441c1201c0401076102c001d0880000c59042020036042d0390b180000040400d8000c4120b4a900340c8018202d07180c859641a00c640300c0e44424a51000c981e40200398601018042e04e54580034140454165042e41b404c800002c05540542e207003900075000307100180d40310714540056a0003007a004a1050703c603066008618017550740310380c1428018400c100841e00604103281c01071798030080060024100f0740c58001001b0140040d010300b40d4039030008001d0165200401c100030002009900040c1c52940c0c40c010740c4204840000f0100001d82c42c09988040d0410340c480115009410700742003494036030328604000e000c03a4501d41c80050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 241993974 1250 241992724 241992731
    0x40c14030a27050c0301050106050a030510210209061e0907050c161e032301021b010c020d050316030e0c040c0504090b180703090215070b01051507051c050409 70
    0x360000300114154080a000d1000c0f150900c42c0d50060500f07c0b0001d1242c1d0002800600c54205810300c01e400058020419980442d8029162036444810560419100f0402c441001c00d03c4114240b0640300c41d4060811100205144000b2102c0d100b41c00354a05a41d100e4908440001d1805000c0c5003900c8010070508125070f050500d240c00c00308410014082d10000404084401c07a0440c456901c8506495000100130101c03081c1e04600407021190782c00310325055400b07000324402c801041c06814002d000b940d00110318590000406818283c2c0c442c1d4210030001c1c208108a401d09004075900210b9002d0b10b40019000b850000c110306000e5140841a4040d04010700c54091541c800090010f441e0341c154100f142d420b05004000382c038080186000303030080c10980010900e034000d62115080e180041c190080348544000440b9007a844904100d420b42c041c44014040703402c00c0d01d0841c0da081d0f00ca8a00d83d261503140c0e105c0b1a40c500c40c0c03002c500304402080e903078511002c1c40341041c0d500801400f030050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 241995224 1250 241993974 241994021
    0x6081e0c03040209160e060f0c010911040c022e09021201060e0105040204031e03020a0b090105150108150909030f0c0f0c0312070b0a091a0a0b040c14030a 68
    0x80a50703070064405920842210340800c02c001c1503a4056040c0464640300d0400c0b05101000780700d4950080789034481941000d10403004480802c0c016480151b209200030103035400c0e80403c000440d01a04040401c40d44044c5c008011000103140a5405a03002a42a44c1c0052451030a40240c012000003e402403168050301c2c40c40398054102d80d09940c800c0e1660562a070301c80040c4402c83c081c83c07202038030501d04041d9100061300e800210789460381c002d206488040d40301d521003014404054841c2d40301690346804110400906820740800d00c035007403a00d0601410020a02c0350000384100c09a4451051180031840400003041164001424440800d464102040c60030b9202c110945000f03159025460040c00145030208209071003e00c280c00b101d0a225040d11104011040103124000c85a07840741c03500040781120b040d48500115150445180340740c100c03c0b06065a142d0b000c2c0d2402076007020400e90040340c1105081c800d41401304401910303540d68840441c060311402d2600050040c3ca01602d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 241996474 1250 241995224 241995241
    0x31207020f0607060e07091b03050c040b040b0a0e180402060c010b0316030c050d170a030e100605040f05040209060f0f04050115020f0a20060c010c05090a050607080406081e 76
    0xa100d003000d004065031012903487da01d10007554001516907003403031407001c100000306000f54800c0c0c1d00641c1d298061400c007600c0300d20340e1049500030782052526240101c0e003160710980c4000090205034064030740c880bc2c40440c0070126412903010740002d00c603d802140000142800754001c00311540001c04036000072b44200c1c008401e9142501041d603002d41440d80100302e030700b0444520102c1540c0040d02c0350b1440c0304500c04507026040003910200309074032600b1503001c4403020042c0c0202c0c1e8400c000f000500c030303141c401003008440030b0a05089281d420314040001607541c84203255440482070f070703030445039072401000170f4000d210542005600034505000414806101240c2a00161a80d000c07a0700489404c08419591100080028101054130f400c61640750040f8040200b06940503040c503081400d40c10541d800c0d01c10912072500014404207800c03c0078038040340000024402510740c58a00b81c500d07294810706220301d000d0038040c003114001003250501400f44040192407041002d041a007002d946 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 241997724 1250 241996474 241996481
    0x1401110a03090503010e03030603060403050703090b0a030501151805040c03060515191b060b010c050a120e0f0f091b070308090d03020c0c090907271109031207020f060706 75
    0x81038020361a06e400360b90300d501c0c00000c803405140e0040042c07149a0355503030121183e070b0200c142101048085200081c2843c442c0015000820640c0c401142a60511041e00d4003101d0321144841009000f1030280200e80460142c242aa10243c3d000710f01c0141501c02036015000d160300050f001514202070302091012a0064101d841c091041600d22013401c0310216044403058011800c030408201c00a400280a5070003013408200c10305100f120b901c100c1e1100c0303050050b10700d01510700754203250150f40400c0d40014002c600749000c9850301e5400c8045004981042a10103801d0f00505106005c140001405030304004081c080d50111542c9011038079004041540a4a004941d4800c40c503201c00c50500034000c0d40c01c1300b440031004100901c88003003044920030020300180e01a0290003c049400c03050180d5000c40d4041d4240082214071826004800321050f0000800005106104000c00c0b030340d000c00c0002c01d00d00c0070300320319495030004e00020b480310480321181688840006942c1c0c0400800740c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 241998974 1250 241997724 241997729
    0x8090a09090204060501030b210c090c1305011407080d02090d0f0b0a060b0702010c03120507170105030f06060d110d06090615030b071d1c020a0803040506041401110a0309 75
    0xf2020300015a4a6005600b550010140c059002100c403034041c0b1002d060011002505031101c0860310b0302c1c14981c0118803103a409540c402031428001034011500c42c0740100c4003000b44820729005000e1082983c20358004d001c0c50000400d200c00004086071a4840354066a40040c0c0050038042d01110f1464141c40c090780108084945000311800545000c65601c5810100c403594000c07a4682905580115116403101380300707c0600a218160944686082c480c141c4a13100a0b00d81700d890054030303141c4241112059101c0c0303100b940180c2c410b00d1104030205006030451415508208400200c1c5070242c0c3c0a082160542d03044554814041709000c500d0b00101d03205401107004108020328401d42d42c0121000c0e01024007908800d101041c51a8451600060384130464940c110701c0c1c244440c0000c03000316400c602842c41101c2c065a0b681507281c1540304000a10594008502d00340c40c01d40882c1e554010f51040180c445907030306d1301070f01c103034060362090210110010076200e0369989442e020304582d1150 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 242000224 1250 241998974 241998979
    0x21f09050f0607200304060c080d140405010c021015060315030f1a01060309021513051801030501110408070e06180a05100f060503010509060406050d050f1c05070b0408090a090902 79
    0x403d9803071340b00a0100441c0c054400710341c5d4500089a090b1517000b60303130380808000951150b0715018694100c0810507914000c8d88903034008a210b00348038400901e414007007402030a6951504000e181d000d40c169480e00b0858619003401700d910422034521240501440d400030b0400d81c04007560000700305109403642a03400d4856910b042e2640c031120704408464a000300203401080c07080c00d850380c05582c80041c12282c03503001441801152600301254031000400e0b00c0c0301024401c040107000300102801004441390940a40c181090314002032143d464680303115003035200d8100008282e0503203c020420340200d52100e5294130718144071a40100074841218001046104800c0c0403541e6062385803072500300d503c143d503000e040d03134245410044441c0028107096800740e40c3e004000b0301501c41000c804401130150020300811124001c85a040c86484403c0300c0b0b410401e0b04181003401d40100969180741d0308202800065515440c207118039110307040303215a02c020036210004000195801003600d040c030a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 242001474 1250 242000224 242000267
    0x60f090f140d0f1d060c250603021905210411010e04050910020309010f090506070e030313031119151413050d0312020d020408010c021f09050f0607 65
    0x10440120340300309803a0361040015a402113a0b160000941e260b400c03004030014a007a00e00481c0b4400145030003d06440c04a00c11051b038004d900f0b403842c1404c4040180380b0350030b0540c980f40e01004107069000810303821074280000451403807a0100d03004100300041c1c0a10310401c10500700f030f08060301d0703070340c0702004150002d600d04040548a007480d01886020311415801070801c440103405501c00b03500000d04000a070342d41c0700c049004460f214041e076511103008001400541c24412402484140480c0145021340c0c4204120207040401c020150200d0350407541c11404070010100140001c55900203004007e198610085428a03035110b200480d12442c1d241c000e62800000303032080c064040c1d080c8541810706c2599042081d42001c028400620340310b03140003106040d1035480c1000300e030060200c40004980c045400c0c451031500344520085940140000c00b41c0300000701c254110304c0c0c1b11690b40804951107140c0c807002c00004004207041100c4142c03e580c00c900d002c1c0c01c014075070000c2c9020300042e07580 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 242002724 1250 242001474 242001493
    0xb01050415020c150d05150a1203050705030304060209030f010b150a11071403010b010801030525030602121b0c0c12010917030a0b12030901211d0f0705090103060f090f14 75
    0x14030444001d10141141c40e20502c1d201c07568030b276844000c00560078400300304038040005805100030340c40b5901c90600140c460600605161415242c03041c428a1a8945030039801d071940d9100800b5549103140b051190b60300040d0200b100c28001d24900c0e01c0e014450017002003074103152200351a0546038141c0003002230b01d03c4c403c011100c0038401e20001d0019040300d030cc0501140d40d000340b070b40640115020003000c01e076580c3c0e4514003241d11050384658031190004c04d0048000d03401d80401600d12000b4125170929540119450b10b514001031014400d00c800b626490f620706080d0066625140c10070170718180c1c00c010103035480b1382d0741c8100c41403d00586804607009a5250555414025450450065040c800c0550041d100101820341043c140c641c003280440340e00340c0300d00400707031104d81441126544460740041c1c9480c100e089011219150000e0000748100d8440411181c110794002c40003140b040b0100500368000d24481c5801341c11804460050010b05c01c000303881c44659011042214000e0a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 242003974 1250 242002724 242002741
    0x1e09030305040b0c0f250f06050601021507021e070b07080d050a1e0e0312070e010f03110a12020f0301031a070507110d0507051f02010f0b01050415020c150d05 70
    0x41000c1e01d5100d80b00c0140406d00c001340e01c0300708481180707011200d000e040800644481d9006a01c0000440e403860b00d40381008401c0d64140070b0f5900c46000401d00303250310300b0a4200a5180c0a200f00441d01c40b40950b000b03819020420401200104030480007c0d54841e6681030030740c99a80f04143d0411518280720104014800ca0311a0180907548228201000c40141d05908081c2c480400700c20703e1440140b00d54030912259400700b6001c1ca0303490300c82003410303070303400c000580041016002c8206052411008142519420703040b01d11044092030843e03040c00075003150000038011009070000268012001004011601980129280c168160030b10141d40341c1c00100c4580c0320b0480c00416094004044840300d00b804010040200d11482c1030740c0805480302c010511810180842d9a03171284400128280c0300d4083c4240700a000c14240d09014041c4888001f8103248a24410a00c4103441242c1e0912414800d01051380320b66402004040003022895030728449410446c1800340062400c0c001c41c890a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 242005224 1250 242003974 242003977
    0x40501141201030308191b0806042007020a030c15090e060d02041107060f05060f030604050d051c050703090c0602030901090e090c1909050603030708030a1e09030305040b0c 76
    0x110140900c40e803583c2c00d5a40440350444c01500000f400d8406a460408803203150143d40e5803501b840300c0001015004100050000390040c1c64280600e00d05a050714404581c2d40c5100040d050300215180c2c0c605107840462480c00060740040c02e40c05400d1404a500140000c091075000f0160380c440f50354030707200c590601d161001501c03215840011115450010b0805030000c0e01114164101a4284006a11401c0075141100344c3c282300c5503506e5040040380e1070040100d0460420a80090010b0b140607900c407580c49840d0302801051140110b03880c00d000c0c200c2c000c0103100c160510030910250a00d850042c001d89002101280c60074410000440c030144004191001640143e40301010b152905202041c000e5024220412078040d0300366a00709074440786201c40f00b40c2140300c1401203051405a03104202e80028100c28032075042001808041110081600d401c00d01040002410040200070717030480b04282c030700036216a820154104140754140c1d01c901e1055004100b2040c0c07507990300c00c0c148000e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 242006474 1250 242005224 242005237
    0x170f040f050a0b18010f090305190b1303050f0f090d0302070303122a030b03120405090121321f0b01021f2307030b03031602040b030a06020d0204050114 67
    0xc0f44c1401054410561085500035500101c5040800d4034a4580d1501800c2021074020403600840e018545000c00100078031140c3d111000d074031032101d24001550b0040c80c511451400310f6074031002140d08014010001c048680302c041c01084d401c4405d41e68500652500400e10083d07020400258540000050314041c0094000607001040b90348094440c3c03c25260904000341c00815903507545181c12a05c040280010820380464603580f16807812040000ca41030507013100660328400500031040460300201120301070ba105ca8100070002840705070856100c4480f14a07901030007841100b03e134120011581030101280c41c00c0405030a0740030305c003400580303403411001e500680c804254003104580001c42c1c0c1c040c4000340040403803810544006011100246070071102810b04100c00c0c81a40740d0140b00d5040c10310001e4016500b0301c000c006880c0080e5003c01400390081d6141d4a01c2c00266901307102800800d548010210f44944401b80440020b4200d1700070180400c40b007148499003041e12a040d25031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 242007724 1250 242006474 242006497
    0xf01030b06190b1803160303080121150c080703050103020906040f0b12030c0d0306030305090909030c011d0706110703060b0d150203060a05010c050a170f040f050a0b 73
    0x11901c40c9001d0041070b0aa40d08940380d030314080b10000c1081680b02d00103103000c5000070120261401100100350410a40a46601da410f01e01c4208000090308803a032a030442d900c11180c00080c401c640c40c01c020040300390400404206034040724003241c814507400f0b59090a040c2ea01d0340b80d903944040068044a00a00029600020080000e02c0c0e40c0b03442d401a20404e40240e8021510b10031000110304803000b40403d00d1031a0b04080381c00824810208440240e021061500703201c0b0700c4c40d586005c0c040c0d1052004035406204900c0000d200c030701040046460007880c200082140031030803910301005011950322540c15000f000000250280f2920a103440751a440d00a0188a45103698400080400710f100d241c00c00302010b54440480c580000803c2610610b40d805079132403500c1c80801c2124000e40d084281404002d40030200400c03000502480a19031000c40710702c3c6c01006d006428101d02422100c0c595149000a002c01c40b007a0708a0b045003281c60a03100210030745c3d10f0301c180c0c01c2ea900030890341c0f20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 242008974 1250 242007724 242007743
    0xc091509090b06040306090807060c051c090804030f111002070617060103090b1003120302030c0a080603121c05092a011b050102031006050901170a02160506010e0f0103 74
    0x1d9481076100c000300d6407004029514056917945d640c025208000d40540e001d41c004107007038003404882d001e9483d18072254039103545010128025604c0c0459120030003c500b41d134890703150b010816102d080320701640d008818400c1a2a181c50b1070700c01c030b0484020444c06001d01c0c11082990030300004114013907461544405d6101c42005100f44a0034000070a0181050b461303650400108161060040c0143c62403070711130005600b075003403510b045c100804510080610400c1002654010b01c026100101c515160002041c0c03a8100001e00d441c0302c000460414040005282c020741c0360210b4806800d60f0100d0050000d603440c088010348400410310610540c4900802003e0901c0002c03c2000000e001414019840b600050384011403181c9d402d002c0b145690300005011820220340c840800a01d0f6a103010351810f010a0002013442402d0041c08203090444008111040d2031501550304180c800f049404c405011418465030340c0b1800c0c42250b201d40100004941c14001008100c0e050301d82028554 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 242010224 1250 242008974 242008979
    0x60d3003061a07020f0423070206070e0904150501060c050709020f220801050708071d0a06050f07120c0c1a0316020a0c091a0117070302090d06020d0c091509 69
    0x14265100f5101203912041c14102461242d640c2d10030b0001a0030402100c03440c0880080400f00380b840c004d0a48400d40d0b10442c01c2000150b405031010319100000c0d9000c2d4850388175840d1840400400404140720541032800214055610607010110030f030044048801d4141d07a110510100d20400c1b0200c0b450038030070002e01c0001700710026440500c1c20600440c3e940c3d580d85403516400c6880503108100041c00344c00a018601d40c0c8008071a441e20512035210b6501c080d5100080d1301400f0320320821041c02008103840d415001a0025034400a07004000c0d00440340690400501044065104982c480d034030f202c0100d940c0d100c01400d54807060800080c039113151511078429065a05c2010340c0c40c11440381180200000d0350040c04280101126800800c691900b4003820322010040c0c1585030400c80200256201619200410b83d0405000d08005170f4940c407800205154000c283e0300500414000107624603c40c84560003200c0400e500d54401800549600c12001e080171500310550016407102002d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 242011474 1250 242010224 242010269
    0x150601020d05280507060f021c0c27080a0516060206010b0a05030c04030609060603060506030f030412081b10050a02040510030f23090610051503060d300306 69
    0x301a603c0743c281071141c1442d425a40c0d20303007a1003044207852045500400c0402d05000c0040d4040c1c2d000a080000340590341c02c1e89402000c0c0041604512104e02c8011401061202415031040180030820241d480d200650b042045e5101081200994046076010001a0003440403545505271601003808519004211004980c5608082e262615802c2d080000000081e424403a24a01510a01d80400c00c1481c50405c03c0444800524450294000e00c5010241820100032035040d1440c00440d0400c0e80c000f401d0580b02402803400d1203050411440200560500c00148079031601460042408980d0340d000c190010b80c017482c41240e4004107016000c00c2864082d4110000c840c22030b010000300c0d92088143c4c00c0910956205455450001c0310500c80c20201c14464258082124103007107403010301d000003054990040b08258030200b000480032038602e580e942810800d0715048007001d104984200c070890320300701ca0404407101c00500c000703a1f50000c0f4024080c0740112880c9480b218140080c00300d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 242012724 1250 242011474 242011537
    0xb09090721020a140408010f0605060301262401030b060303040e0106050a0e0307060306050f1504150302130905060f01030e0d050a03020405040606081008030408190201050c150601020d05 82
    0xc0f4400b4440580410303580e0108100191000f0b104250002c960f440e8080a014202c8085800040c024041007005204040c0104d060a1391703000208601000c0035025003102e8200400100c02034840004c244105070211028801181a64094140d412164030791500b0155640700d40e2042c0065038441c4001040f18a020300080c00440b0010b041c801240c000c6480042d04144258109101083d541c40e02842241088026101d21a40588042110141078961003805009501c545d5003015020b04c13203080090300c00c2c1c056a1000072011000e0700d00c903885a003450041c0c401201c20b140a48038440030b2500c6907110b405101e40e580e8101c00500300c0c03200100c108842651103456080f080c140c01b0400003c0a403128803405000713140d241d03242d006a0400201001c4403118550001109901c280000c0c09484804500e031501c9500c00c440b1800310201c98070040c2c1d01400b60a081508074000e40d660001c01a028015240c0328400903820741d03481c0c12a142c01036482e0f0080a20801800c0000070b80340451441c820b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 242013974 1250 242012724 242012737
    0x911060a110d120b04060506071b0902040e011a030f0f07090f08010c11030a02120703090b0315120d0819110f0403020312090f010320040b0909072102 66
    0x601140c031106566070301440d1a400b00741c41c5001030300d0514107203030380d4416109440c950041260217101541c42c0400203501400341c00d00c094500000d4041e01c1061200f031451100062541141c01d5482d1555400c115a03089c10074411840103145542e1903c01c444000d108a91140c0b00201c172084054890b040c43d2605c840f0001d03d65014880800b001040e500005007650008041c45400400c1c1e903403c0c540000d020341a000b0b42c8204907403080c008044115000703d0201d8040c54040310039070720b50045041c100d5aaa22a40c00180c42c10300020900c00103200420120620890545002164010315080e8036602d03852400c50600042102001c1903215400026081c810318850f000481d1445203690000300c298000ca84d545104900040c04004506081c0074950819545050036404c0203201000301d2600d9607580d203e5410187d4542c0001c1600c41c00500100054400e1000a40c95a4a5050000c410741c08401560b01c21803c140c00104501d2250213070084002003c072589503080001e4401801a42000d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 242015224 1250 242013974 242013977
    0x30f0506060906072319050d05070c06270305030705211605031b06180307030806060c0a0506010f031b030203070e0903040e070f1d06030610020102040e1e0a0911060a 73
    0x148680d01e484803003088061040c20046c0f040c080b03540d601d8078000f40f404007001d500c1da061160500642020900c2c07480d50780211142818240740b000102403000007244007035550304c2060b0000000200074410000040e0441a100b2000c4940000d08205c0c0310701c07813024075008100e80701c00c20072458040440c074904030705200c0c4c0b0510441e81800c1480881c1c2042003402d80c203021096000c1010420030800002030741d00b11102070000385103401501d40740200b183c000188002c1c090347d000100303108500c0341000345100d440c1c0c000041d07800650716002031181d48110752100b035500c8481042010b54103481d00e55102c4c110380d4018010090035160541c10350044800234074410242c0030500002900c400c082031320a00c10040d903500e0204030640c01c000500440951424038036400c505412440d5183c0721282141c1d040841200c0d0031000404101e4104c0c0640300c0d5402114103140c41500f03000c1c00b0214211086120010380b04c090b0865034404112104480d44100b01601f8504a0001e1900300c0c1080c500401d6240e41c175 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 242016474 1250 242015224 242015273
    0x10f06081002130504020304060b100c03050301030f050f07060305070210140619090509030406110c0d0b18120a0f1b030302030c0912100c0e0108061002070f0303030f050606090607 79
    0x11040040d04980040300d0a50782c09c1d8032042c0c4100d43c1e252011240143c500e2605180148502640300100507000c1404010000d51800c3c80031010b00004001c03a119181600c0100c0c1c4a540c1c03210001030140a09036188005403003030540440e40e01c0b0a034040e40d4203d208130079800c025950ba86040051003041200e040b4440c1118050115451583e40201407040c01e00720300859484d4940707000280802000317010204550030200302010b0719036440b000c03403c400d90000d00d040500d8684c03030104281e0807a640410b003600c2c810301841500c80d41c665005021014038a0b210740c80303d0b441490b000d46a4003020820556010307995942140028001c1d030145810880d4030808904010551010032602c03980c01440030126441040c9403401c0011760f0080200f03220350340c50035a099550600c0043d1000c10702401e0284900e100c4034107501a503200700070280042c424800000e600940e070707050140081ca01c42c1a102c6949041c880000d416040c0303c1c040355405000a000f05140000d140c441e500840e400d8040c4113002181d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 242017724 1250 242016474 242016479
    0x3020403050d030501061d09040f1104020c061f0f09020d060312030b0a1401020309270f090706030501050d02210102030c0c1b01020316062c010f0608100213 69
    0x704111103407200710551000034655040178409043c441c06005806400390355051484a00c0d1911140349400c00c0d8403501d46a0403503400e16001a8005140880079000342c80070a1510090f8000100c190003079000701c0c02d10320600500d01c85c1080700f880d1030007414040c5c146400d040281c6051680180360000c0c881c800007861507200d940d1411461290440314001a40300d101c034120615290309504c000740170400e0100c03c1d180f8810300203512070041e00f00c0a44241e203d141c0c403c80d840c8001c00710840000030510a854503140c04c02002691100a94000c66180f0458002064842c042d01c51076040e900002e100b08103032151542003204410f1810710b1070800c0004c801d682c04680d4000d0020314083c071491010580c940546141c0189005842ca0030900394041110f28000540d801008540003160440c00c54012040d150030f03c80003400c071150400b01403003a032030100103010b83c280c481d034020000c00000178400002035041c400141c8400e8007802705c41f6000100c14078198105035005009284000344540d2086a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 242018974 1250 242017724 242017733
    0x1a03060a1710050a0605031905100f1808041502030c0616020a05060108030a0e0306010b04030209060303072103050604051608150a0803040905130c0b090d12030e0105100b180103020403 81
    0x10025034400e501c154450b04c0074072480c0380c1804044403a014038844002c54082d00c1d143c484c4e540407000f1100ac0e804e030b902c4032280f030844901c3c1c210070000c042e5490400c1403403016160011090380144501d0102d0103c086550071060700c00300031105540c060100400041c0c80300c81c0f80b8545c090181481806520a44426800107401405014020f0000e800615100c0c00c3c400805050742c4903c01c40785100781c00c1400107001c0b07081d0801c296002d80390103541c819100c0e80e909012a2640c89445c4015110444440d103d00450070424000ea81c011503c0d9014000e90300e40c0414081618130070794001e05810358118003081a10700c5418030540c05180040755054120604000c0b520104203600a02126040010244a03101a90040d650009c241a034400c120010f151a903c450b8001c502404192080000f410009a0fa414862141e11600142046140f801200000e801044902c44481c035039420b0400042000701500710190407104000d4900303180c08003200030140c00442146910703040c140d0a000100114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 242020224 1250 242018974 242018981
    0x1503051e150717040b0709050d080d020f210a1b020d030b01090f0617070f0903120201020717070b07050913020702190803130503070515030601030b13061a03060a1710 73
    0x4900500d8424a6406c18031402840d0202c142c200a000d0040384003102c001034030a0b0100c44000b4101c2d500140c0380d000c80100c0c203070503100b444d1050b10030000940c6450600340f07142c030015008000e40c07482000301e019406444170307822841203521405600300000703402e0494000e4100e1080030105150a5503100e445424031110b041c15034000c200010b080c40c013a40303104002240000d070089400e0a00700900c24103d44000c0401d11907000041440c0d101c4012207200d18004d405860445900008440da519034644604045400c0184141c805558510226162900550480350340c0e5402030526a416a050420900a54403e480072a000190082c10360240c5c0101503d0402030800e80b0091540d0301d204a010388403005190b04110320030b4200703140800c180d50356403141162011481c610b1039280d980307400040e40180240381500e500305008141c0b07030079243c1d00f07507110030152501031644a051005c41c5c90440c04074042210610340051071342c0c50034000691031400548000c43c4103411107038060807604c6124182c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 242021474 1250 242020224 242020231
    0x150509010807060e1905012006150f0909030d0b130f020324010203090d140601030c05100206040209060d230606090606030403141605011503051e150717 67
    0x1980004509101c110b91041c40d1205071102254080c8005c1000800880d500e80d90303218540c18481d544c803c0002e603074080304a0119400540b429a043c0d450100c5440503101e25400c4e2072441000716840c0090146068100140110440002141884420a1094000d1048607613050b40007100f00b19400460015014200721144062805612820521054080608a0300007441c5070080300900c280c4d00d0b640001558443d44044504401844490420b83d200010140305400c083c09844000301c140045c03043d052003112416504040503580005040f82c641c101510025404007000c4041801494019010a00207028a4041644141c0d2007a100b18001482c80100c805030041001c00026103000350a495200d10143d540314a1854a5600104a804030308078440c05d404011032400e052034005503018134141c0c0d110000300258000460340f040b6140803403000711458445c00d04c0745a12003110004210700354841e09c0051509024030540c0740c911450040441c020808511441500d0301d2524040700d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 242022724 1250 242021474 242021489
    0x918340305010c0306150c030c14060708090f01110702060c030408100f05011203080414011509020414060f040b0f07150902030f06150411090405100905130b0a15050901 74
    0x68120f10f1003000340c1550350b16800366110540a40c09020442c0d000500c0580305503042c500010928250701d01202054003040100700d0a114000400050a0f00801500d000705188000c8810002c00608040d003030b0b805a0050303041c09030302801b8200040c20800040c020300b0303e00d48244c2c1d06040e01c800710a45400c3e100541d1088481c0c40c2d000405043d41726100f5240502408001070038000e4241d2009025650003620042c8480c2040341044146007003944000c20681c100c05111103241c1e43c440514019400030700903e10305242820119109103040e42c12154101005034100342010301d00b1128031815003100b951110101c8003002030800080340c032449513a01c550b50303410000b428400340c01810718107107090601c00d465a004a090140204211000d18114101103c0c0441c21500c10501c0f60414000c0e000c015070042d00b81001c1c400c4d208220f40c000d10aa80c4490402c016a594001184102c0b036408600541107140361404150b041d400c94000e40407504a21a82d18510341d500c030081400040300741d00044c13 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 242023974 1250 242022724 242022731
    0x22707050d06051530072a050a0305070c050603040f1b0e01120303060302090a090b1005010801140303091005030709060903050c0628020a02091834030501 68
    0x580401da540720b200054082a1985040e0724030000b104c2e6164800c900c4c1c0c644202d40c07458240c10124036065540840100d089589001504140c54050a020109420b51006201301d1a140f6003841a29441001658002000b0801180c50b5101500d281c1d011841c00d0380d604605000104182d00d5003002140a40d00c0751480d05150355080c10003094500f1105603154500d580c1201c104101c1d1045600a41540c447c02d000303c1810180d481c00750700611550f84001d40084003242049445011035110702c0c01d860081281e20486d55600300d442010300c145001f01c42c0841d5a29005101350481404090707000c5002504907898000000001000c0f41001d13039a00000400000030000300c0c66004407800b0040140381000400e00741140d603441c2e01e495090040c40d01400d0301159207002050306400304000314540e1590301e43c1c0321030204002503c6900d240001e0703014101d030380086480415140801140b800e140d070040c121101840f405081d40034100c1c0301c2810040203142000c0c003c11540c88500c0002c40c42400000f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 242025224 1250 242023974 242023987
    0x30f020703140a120302030603060408090a05180a1506120b01030608060f090c011412061908010608070e0412030915060f0f060f0503010b0a18060309031106090a02270705 75
    0x2d44a511304100301d04101030040c02480f480e0385001800d0b0f0b401c0f80c0c0c010509901c4101e8400480d1a549050380226800002e80c0c42004000c0c10b1020b9442c052000c00e03c05103c00f203088841c16000720b1035885583c00043c4107040742c00450f04264804a000303a030502d00030803000e41d90168036107851400c4d104820181103120a20500e400704104910002c1d0003801c040b50f260011700c0081c03100b400b46a03040d140c00010440080c0d4595202d4031030a603a400e4100100c00126250850317240200a00d02441c003191044880203d0761200c0d0b41711061152f030b489003908000b640721110480141c00742003000c680410f59904c81032180045405404040e0031301c0c0520b04000d5151505201440940f0b0740640144689003003410f4582e6400320403241503030030b070114540d603445032000211a05031600c528a11030001d20b190104025905401800c0c1450295441c0602d021b00395220644450054070300c91b01d00d9110a1002c030050038007541c0c091540015140c1240d12900e202c6011003e03090486561b03001400c0090003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 242026474 1250 242025224 242025233
    0x80304140606091611120a020a03080106021f0e0a020405070f0201050105121e2104051927020f0c070303081b030105010804050c1008070e030316030f020703140a 71
    0x1140c0e200004071141040d50a11804413801800016030081c20482c05403280500400300300111448840211960b550b00e40a6110003074540f540e015040b0f001400840000603418400030b9210307d4407070203407240c810345442c004030b282c0100001441c5d541d4501030b00342000050b80e100c2c81103034440c5041c0d0302c4600b0603004d4003070000d0848405811152080f4a0380e4640d4075107800008400c14100d007003030001d012080300f2060451402e03003c0111006400301c20501c00c4140c03240d01018000315402982d105d12081030161070110003080c80e000c0c5044085a801412000c01c907003100041c40e06400c20b10044c54449200300d00d001540c45061b448107542e00c000410410140c0c0303d400160322a41c0c9100741840b00f122151a640d2920061180700d04000800c0045030510006000301415264014034440050140074030140c0103210071602e081c00300d044a0056502c5040c0801224100e030802d0171140e24031182d0380da0a50302400d0f880703400c0c0218410144048002000c20140d0f04c0c81102c0d110040007001300500c0c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 242027724 1250 242026474 242026483
    0x1140a060206151c050a2409020f190e040b0403080702030f03060d0c0902121009090309030f11060c03070b180d0c0303020d1a0f0904020303030c1608030414 69
    0x1000465001004110500c418180e848101000407100f20784440001c500c41c0a00384c0c420440a0081c1c042c0080c0300c020442e80c08401c1801c402d0405005a0000d510075411007121180310000c2d401c8584030040d90000c0c60896580d200c0d10603000b000c5000592500c0480c0010700302140c04450001e040c005110600d034003c1c0480b54482d0003031000314601401000c040781ca601015003454040c10340c518046040040756003003040038024a140c210f49405800075a5a2400b0054685011040e1140004154001c0c01e0150000450301a181c0303074145407444d680c01c145000b084805446102c8080d466600c1941c0e824010b05200400b4001141c03200c0ca81d04100669002c045c0c15010712004450507109070b83c901003242039002820b418000d42c0c2c400203050a80127841800300d884101c82ca0203940b001d407189814411b986a24007600c4421901603a032080c4000444240d4002c0d5043d40180001542105032500808844103d03140c041c0c00603156075a00c50140d0420340d402c0f0380d604003060043c2c5200c0d00811 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 242028974 1250 242027724 242027729
    0x19060f150f03060b010909110d1d0307080309070506040e090705040b0a092a0903050c030604081e0c01150504050a05010b0a030b0a05030d0504082b050d09060501140a 73
    0xe00362050900d001d00019022409102c001e090301c0d160102801168000e40100b4010a50918140700d8250720140c69113065209480380711031107140c0100c9000200100ea9440030a0710710034011450004a41c6502040303410060000c51288280c280200f015100c140180004061a039004051800d110951600782203941d08402d004030b180100c80c0031680d5030780504000302d07800400d00040141d503030844080c803c0e0030500440d604d001506039070541c50b40d2291342d100449004000b501d1810905600705070700e0b0361b401d44016101e03203810300103044126692192018201060030143d0b01c3e024500743c0650a462003902d860040b49500c2600308180e00781401500d81c464000d00081000e07604141451496024003404a810150b0302c4250f0b2403581c8612000e83e0160200600312043c2c02442c0000508980c010300900107140518001940711034181c00500711044100d0f5102a01c2d0780c1c1e05a0304a034a134001c0401c205802e511024614045192841020701900b0301c82c00c2e040005c943c40061001d50307011903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 242030224 1250 242028974 242029001
    0x30e0f012304080d1506020f150f060117070e0f120a060b0d08070b0a0e061003030c080f0a0c050d09030b0112170309060406291219060f 60
    0x25980c5004824400089050001000303001c40c94403281081215405000c0030f0540c801d10300004807080020f4203684078110303107466003120701d9041d08000317058980b4060114000000180b030302007180304d00c0342c0d0071041e8030100625100701480d07142060100301d00c009032000004500c01c411032113268102000c2c2c481e1002c00c152009180c00f0803910707072107941d44207090003c1d0125aa600607000c041e03a80065000015410020046d119009418010303403420741511680005858880022209040030a040d07218014581c4000350f060b1440d18150348120416100322a2071300c080001d440d001c113a84c805045c000441c0c0c1d40d468008101c614001e0701d890107030f05c40142404040001080000c10241100d03055640781e0704690b007043c607207140ac1c40c40480003c0a8120442c000301c00c100407000006001445180038130414020074038038140165110a0304900017001c0d82403402d50031070600300080410900503404007124149800e80e41d140702129013a45040b20840c0d26801c40741107030346a03402464800000c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 242031474 1250 242030224 242030231
    0x100c09060c051b0406050423060126040f0606030615050919021804050c1804060605030402090603150c0a0306090c0206190b1011010c0e0f0d051c030e0f01 68
    0x564603600d40d40c45490510000143c40c6404054081d1030741d400c000000c100c042d1040c40b0030b00102c03241c1d002c1d1040050400081001540020f0459071056401c200c0700c08016181207207102205200e030090020052043c0c8400c010b000b80000051442d200e910010741c010302c80054070180c20080140300350b0080e807046106041c00b5041c41003d52035006801104403000000584e288003c0710501000202c03c105c050303115182074100120700c200b51008080d4036194074100c9041c0701e03e407010401103035a07501905000407070600008006040c170759219904810010111400c1446400c008200e88400f01c032800e81c80e060100d401842c00390180644c10107018100c50600c03c0303603019070000303641d03980003000e16807500141c086019481045502c49028510060032026080344101c0025240a1301c08090316001e42c17034a0b0a900400380b00304c0700700c4a5004000c0c03403884011500d20400c017607480c026a044d0740e03034002c02d05803000120440707640c46500841500c011414a00800119080864002404600741d04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 242032724 1250 242031474 242031497
    0x40602131403010b3703020301020c0102040e10060e0616150c030b0301060524070c0803130803090f190e0114010f0f09030209040305040801090f06180201170702030c100c0906 77
    0x201d0002d1500054402044005d412042200d801c00300ea24507800650154400141720400345410340040c81595112203d519090b1500f41ca203010b109640e100d007100044000b941c2001d00d24000d001003054800c100d010003003091054440d02c84031243c41d050b001c0b80c10b075101d44000c900343c0c0500403c91344400460007040550724010101c2c115502842100220142c050b00d1400410520b40944111079000b64801c0c20054a40032561764942c00120121031040c07507080c0025201800200302c548a60b00905400611100380c01400901c20308401d81c04002175082001250b450642110175000386005100640c6011030301002501c1c5420000c8900c08100c840740610443d242c01000c0c0c0c034104c0c0e40c1540c00a40e030f0354a80c241243c05000d01e03000100c0c40c0d400c080d26001400b49003404007140d1400f4100402c60b2004045d141e038003642d05410000e01141c49240210302d1a01502c0001e80e0000103401668540039010301400d0406904080f0b07800120394940002c0340e0654819155030241035982055042d542 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 242033974 1250 242032724 242032759
    0x3031104120b090102190306030209010f1404050703110a09140604210609021c060e0607020c0d05100c1206080d1e0905030f0a03140a0e09040602131403010b 69
    0x1c0941005032400b8030100114401d03440c01d60490b111011404030034110451307203440040242ca1103200513881282c1440c00400c910300f1210480301200d00400c03805c1d03155410407051101621006114006240d0780355513001005076140000c058281565956010301428000071080340314006c01c4a0b0300036a02400188400d10494018140101088001d41251000d510b071050291080d241c0080d0001024820100c0000c10307907045450081c0300d03003001d02001003000304c0d15698110803034200006a0000d55902c400713003030080501120600800035120340a5000075104166041204d5900009100301910a1202a1031080701c02401084014200d1440c0c190740c010310f0003944220304026055040c40c030038110b60091500c40300a00e0007809480490700345071005529000d081c0c10a80200d8403042c070154404100c241203510303d0300e282c1c844071142e01e42d08d81032045520700188103e46140c8d00f04503101c2407074100785e6010b00411140303549039203014801e010306007503030040e4602d18014800c00c4801c20002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 242035224 1250 242033974 242033999
    0xc01050c130e040f020a060504150c03141b1905120403051b04020903010603050d11150a0e0304080601030f021c020d06020d020706020c0102030703060608011a09060714060403031104 80
    0x2c0d078040003495056102c905240340741e00c0003a00e00a6200c0c2c90601c0004500360004054030495090090002d0500401041034400010b503100040000b104d000002e001d9420341c8010f4070704c01c4031010203403100c4120100c03142d15080c2502c9039890040040001c41c070400104120815013038032007030003a504292460f41c9007960340e111440c03220b04501d54040c00b03080a49490303041e03a850a60080c000e000c2ca582d241401034640450725170100006110035210900c070000081c2113004a040c00030030040ba6680c01006034000c00090046502c1d81c04200710005c0c15030300800019000e54001d820000784c4002c00d01c1044840c85240561903500600b148a20003d0303690304548400d801d410a0015941e1201154007000034811742100401d582c0c40400e48040300c0e10150b02840c414800c0e40c4042042a44481040d2104542442003001980c000e0010300e030a141841c001c2c001c05000a000c0300d0820107142d94035100c000034003c0000140c1c0c03200c0e00308014141d00d80a1201340d20b499240046c609801c0884007480b5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 242036474 1250 242035224 242035229
    0x4080d0c03030b0301050f010303090911040b2505030a1707020604030e0a051003020c010b0301053c0403050307020111040605040501051e12070207061409010c0321020c01050c13 78
    0x60012850903001458082c1d004080c030500c00800030059480c0c000010041102c0a001c00e6001031181c070004500d0451398172590907030284184140341400d04d0005c244001350302110010301103815810100729102c0e001c0200d03203026407181000d135480b00c8903403c0c01043c08041414203601c00040b041800758858002c1107882c2c100b40c01d85042c1440d21174405c00704a8185d81e40d0300264110040e05c0c001028958580d01030300c1d0b480708050092029609441c2007500b601e0040c0d445582c014124040c0651a0b0500c8920722400c04034a10b4488000b29006200708030014119019000704200004214040e6070a02c41c90000303801320003038941464200f520080c090b001ba03000d464140100001e001000040d1030b9024103c824652010300e641d0301c2070790310f4443c910740250740c00005071042100c042119802136940803d9890743d4800c4d24285144800111541d1900710010fa082c0f01001451011581a0001c8103002c100d1340c03e07015a0f03032800c0d003030790300d00310b890080c0320221804d070501c076030006480504501001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 242037724 1250 242036474 242036477
    0xf031209030201140a020f030c0703050c04020a08180f030a03020c1504050705040e010609050c0a11060105060f09010309021e0a17030403060e030c01020a0f0e0609151e04090b1504080d 81
    0x444480e007030011b81c58007042c2884040284808902c80f002c0d1080091894262031180c0203071403c4000e0003041c041079020311080318010511290000704d2010400402c8800c04569100b2500584905170b10b1078210383c0b010b14941e0020307400150148091004101c40806590062040006d51500f030b10ba0b151503401c01c1c0100c601c03a6031034002e4850f45240941100c4c010300789402e030801145c10040b650182a510120351800810964800c2c0c200b05407010644604032031001d00020b1800029007003103403051344a10015410b0507a80e51410b00075880350048020003250515070f038180c082c1b01d03008005400b08503901114180c403000e00c204071180e40210544044030307031042c008110008007424887c11400b407124001c00c1503201144c580b00051b07002e078511000b08901c0c2c0300c1b00071a032049000c1c4825481034030246130f00003030842c07004d6030b844070628000e11460402401301c68130107281000c5400343c0e038051350140b0250740d241d40c0314080d54601120f41039840c0c41c40c2245103141600d400758135619008607820860 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 242038974 1250 242037724 242037727
    0x30f0a0b090a020301050108030403060c050a0203030a110f0307030501090e07080307140c100302030a050c03450307021c151e0603050f0609210918010f03120903020114 74
    0x780902000c100c240035450b4010000d110035a1a02c010780d070b40390054071080d00c2c400d043c03100c4c64070b44500442c115205010268003444c0b4580d140f0b40024003511b100c40703c42c1c078586010401d840401d1108030146010710100e5401060740e5260075603020a5441c40d0308280d60a0b0001c5204000103c03001048503030650340f1019004030702900f85201820300d400745102d1500036841240c3c00240f1a4140c0c0154400c505d51642007250362108034003040c8038002110042441201209000840e060714640640350303800340c0108005043e504100b03403070001010925802d0740d520120f02071046140c00b00b0494030300e00020310181b5024405844103c00c541c1c4040d840305005654a00d02d85008455540a448a10b0000c6051141039500e01d003255603001c09100c0b01d00c0038040c51011850404020031911500780c071410143c80d4040e48041420995400301da84154492142d203c400f02001c1040d440d0740c000e01504551041c0140707181010541124024001020040000d8040c00144c0c3c110300c00080320300348488440e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 242040224 1250 242038974 242038981
    0x303030e0709140414071a071b08010c080604090305070807030c0206070803071b03080a11070f110102120715050a0213080d020f01150b0f04090f06060e030f0a0b 71
    0x11400d11010342c2100312901d003450140100c040c0460002c40c010b07803082e0065035031318040e000070986860550240031800440c0d80c02500c01a00300d9006026030b5409000c0244d08800c030290b4038409925540d00140c160f035100d0710b14518a54100c4240c42c1d0060381590140070010a65400034028440d01303000402d0140301244c19001e061080382319105995001d0081640e44c43c4500307004000c1d4004840d180001400703e03101070340d0a0b00f2003144009599058603034503c00c1e00d81d9030684002e04010703461100d1290041c0100f40111320100181c40000e40517032004643d01c903400340024202075103216688502003080103940d00048040c2e82a031000310a9a800203910349403100384101900c04c6d41d440d405d003080301203804a605280890031902481e400c1e02201d50307040300b01c001c0038240c0703000d0150f500e48150500e80401c120306103480102214903501010314640f503101c89421040390101d240440480340d0ba403c080c0302241d000012000d10001c11001403000070703c41103400e5600c190f5886c0080500d1070760b0002c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 242041474 1250 242040224 242040251
    0x60703050f0421060501050f10050a0e0303130305010b0307080a030c0606030b0a0c020607030e0a0b0603030f030103080a09060504080307170c03361e0a03060c030f060905010f030303 80
    0x1680c0c083e000041180b0b60306803424694078140c08440e40b0a88004d40b408000240310b18000c925002191800b514150009c05061420b48140d0018090b8206100c0d03030361135620710b0f0f540a100819604549001341a856411030528500b1200900d031aa0701983c02000144801c0c0702c0050301030507699040c80c0c8255842c18030300d4108041c0c08981d20003003494145800b804203101450f000419038681a50807a0000d40c1c030078008506031006090b4425032500071265001c04507900d94600b50b4440320207002c07207203007001e40388001e11181e009a2040d140ca080126112944a90004403c0c004240c07500e419030034982482c100f0b640300e01ca4030200a01c00c1080784124940c4140c41001d80310f4509841060300d45807410016580e40039410f895640c2d046a44000481400601e440b008504100c3c1c0038005101c001c1c03142d103c0d0044880b5244049034400c401c110000001142800b62002c8400e06a0300801e03002081e04402d01524181d4020150490808006000043c0f484060030100c079010314010600c050119034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 242042724 1250 242041474 242041477
    0x7180f020d0e0102071101180e1510090807061701090b0a0302030f010e060117030f0a020c0402031e090109080f1e0f071a04021f0e03010504210806060703050f 70
    0x7000c52455040444140b4400010f50180c9003560003403881c0c43c40024035400459000c8500d1150034078500b54243c0c00d000c1d8400c001c12030360b401082e003004602c68102003c0068461004140a88000f829100c018440c0c42024000c1030010080b50034608a01101d06402600f44001400740d0f0050580d240102c944640d80c85d00004011030300502a191100140c2214602801c036417212160948a814000203440b000d203c009400d0b982580701a5040050326a08030140c3d07480315401400b1880340d070b6803504640c1c2c1c07103200442c040d00800f161b48111091840251350144001003071120b180c0d244c01076440103d0160001c840394040a9426103641e6601c040f081c0b0707000c1c04414540201c4100110309a510b0a66600007440d800d030046010200043d82c6040900c180b00c42158000d41040e680c810035030090f4070000c0810b22101403800c001c9640050f290100307003127400886041c1c1b054503842042c81103000e0000650a010780851810042c83d203801c1e00818098400c0c1d00004003007100004110f07000c41030320310 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 242043974 1250 242042724 242042737
    0x1b1204020607032715020c0d060203062701050103140603060711030c0106030c05030c0a060e011b050a03020a2904110303070b0117101b030506040b0a120605010807180f02 75
    0x100051442410b2074504004c01005028000c103000155660742495400000e42111124000f004045000c0d0b0320764608000c0d42000e0100c41d01719032100103c0d50780100c4140c0c440c2d0059003030320513485150303d418001002d5560889400711009134560500105483c007080c265880301c02e50501207401004005094914807450184c03046079444d04101008218890008408840c41101101e4080480d20204184000f961181a0103c0d80805803022070794060034031400e11040440c0c0d80d10800010361141c82c00c1400400b02200181c101360448070400ca0200d154007223103060240404162805030102c0d4008000140010341006569000508507035410801c44040c00c1e07001140400c1035940701c4401e001c6c0258102200c1e010b0051000c4101c90f54068070510010350750740c0089445818003010240c0080c580601090341103625110403486d16100e00000900510030f0140f064182561070400e4001c840041e000b410143d0040802040b00844038880020134800d1510700044441c4080344e860024420304 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 242045224 1250 242043974 242044007
    0x306330e03030708041502030301050306072a0b061801050d06020d020d180c0e07090e0a110a20010603050c0118030b07090806090115120507050a0e1b120402060703 72
    0x5007610130044101c01500c115000c2e051000040c0184003c07c0c0d03205c0c0030034054550190f01500002d00e00780d100d188800805020040300000390b0b402240040030b28110001d0a58101c84100140605800e00300e5003032014010140c442c0300d83c2d5040400255050070a500050300e0b0b9038000c20115080306041e812a003800b80b4106003006076426100c0300a241020010342031300c10000c5036000282d1800c3c000841c9224000c15070382d45050314184880110040b6024282e1a502c940d55010a6000405131004100410668130b8002ca2030f2042020494500c00f00028001164101a000c0000a07800a010500c0303e0702424605026403c0340e0403501c0d13901099202522807001c80701800f03a220f4020441c00e0664403040d0554503142e0710b03040580c0c26201440e810f42507140c81c9540421002c900e03000d0820340244078805592515986a0000c0ca01c0341c0c2c00d070418081104802c080c4924001c1c043d00d1106004e5100d450241032002810210341602d5008101034007548001401404161145100d0481e26041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 242046474 1250 242045224 242045227
    0x1201110c060105150c0c0121050907080c040b060d0c17040803060f0d0302070302010e19080304170d0e060d06080f0607020c0102010b090a090305040b030403020d0306330e0303 77
    0x100c00140c0c0d40c52000780b0445008042031a80c280d00b0681c0311003101c10181c886401001001046401103403100c0d482159030b0501002c04c800b1080c07140301c07802030b14001d5003540018011a42803aa03410b050803ca000054032a07441d010b4456a151151000c2d500c0700c1c80200000500282e480c03d0580b044040d001c8145c1d40c4a0041040004008090b0080e6001706003d54507041080d080328244009a060480090090384c03003010201b006600c21031365048403803c003520402e0f000c4c01c04041d0b81220b03281500004040c1d04041010300c6540c0640141c81d0840409100401d50912040000b0740424094041540155400181446034500d80c0e0070010081220034215401c4880d440d800f1529003074203446950047c09888400181503105004040081d40000d04600e59600d585500b503006100d505030450034848103101c0004c08140d24005144910300070707000307481402009800101102d0494200b000031410800500402c0c80c005000d218500010341059481d00c40d0080c800c1d109802c0d07885616505100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 242047724 1250 242046474 242046487
    0x2040510080a050106050909041203020904020426030f1923030703051f05060c01150303020f0609070f0302060904060902041211030613033614011d120111 68
    0xe004001c50310032400c1d15000c110301c0e42c84003400c039110b228903201c6030340c172104d00c2003c5008108200ca01c01d0719035500741001403608100b0340c00705040e43c0140c4c0c0a890805041c1807a841500310a01d408108070241e07401a525204c0704668009a81c080e114103a052021003080d807046007405034401c86c03144001b100290503503c4003407410700d003ea8012038920000a0509007c50301100200d4114040d2500090101560601308014007249030481c0c10f640c0b0066481e40384800b203a503520280a0701450082c1e02600c401d10201685134603060014021907003075880803008010140301c1020341401d03039130304031031844e95020b29500090203030100d600040c04c0240700240c000b50f030042030720905115511400302505c25091140415841e20340807601003450035148000400003900c5400c605401100001d100409510300700380400f0b0303511070301c0e0301013500f210b20990511022829402415031450700746029410021118054802582d030601028001c81a15003c120284829009038200f154841a41d40d102c61 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 242048974 1250 242047724 242047727
    0xc13021305090c071b0e15040c0f0230030c09031501030f08031305071401090608090d140408030d0f0e0105040f12050d0e010b0405100f0302220c030b15090102070b0a0302040510 78
    0x7440c591f4a214500c0d00da00080380c1030180350b143c144060650054164015903600c9221004401c6c0100702c4108c10100107040d441404230003440c001c9512445913500d544862040c1450060301d241d41c110010303048401000080d4071404240b001507480030b2019100d844c3c1e07002c0700340140045000201180680c500108085a80310160000d100003641c41d10380c61a61100b054400c060259643d020302d820003000c0030380703490068a0090034540304191107407a080e82e401005045400107521508125103c481403240342181d40901100392504000801c51400d0541d18140c54801ca801d0013458421404035a08405d0701a2096501c0802101028042c0c00c20485181e4000c02111460750b00c100c1c541320100700c030401640e8022098450b1301031034100407800e5030200300409050200c00a0150346c0300c4032900031000580034003030704d140c815100440c0a001020400010441e503400101560704c00388507080040c0c1e4001203d038126400c1d8500196501841c1400314040c0c860f0b13810003074001c1041c102d00803c49 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 242050224 1250 242048974 242049001
    0x30c060e0607020d09300206031905010f0e0f0c0d140105180601020703060b0303040302062b02090609091e0c030906070203070809010f020c13021305090c071b0e 71
    0x2c146076801d60b0011944090305441015443c041e200503000d801d594200c110282000e024041145506085a40c0711a6030004140760300031074210400c460f00c4100d02580110900405024081140c2c62682d000e0078000d848200308002400c03800b000744514003140c5102c03c0d250860380e030602101c0b4103202c00c800c209040351529100b031048c5400340580c00c1c0300e8028110100486801500d059000d0081e4914540328840501407102030300303505000401001006980724001041a141c0c501c0c81181c08040760191304402d0154240c0c3c43c48103500421100c51300d55650403c4600c0b544040b03528114546034001c00c00b031071190242002401480840c24080c1080a13080603611510580c004c41b082642d400d8012601d900904000620000c4140182000c560040207282420b80707181c411220543c61541c0060340d00380c0e000081800041d400282949090140c25071200a0b040a40e4015868104800891018442e041c40139058003400c40301c0d420400e03003103410540140000c1409840e642003d01c1601d041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 242051474 1250 242050224 242050231
    0x5040f0b03120901080c0a05130e04030e040507081f0b1210060f090b0706380609090a0c02030c0303040803060108090c01140c34051903020409030c060e06 68
    0x10780b2501060031290074402084610060044c1c0d41e80019031186844402030341c02112648003800ba05009845419600514000041c9200b0700162002d05050030083c100f4060170401c0b5001e10304000400c500c064100103103640004074841038040c41c0038500107d54090304103410140392040d000079410320308500281100d0280140400d4104010b80c0c0c1c100079110b0010016a05000c02e21030f440c200100c130b4040005d044094052a0042003294015514115950f80d0b02c0c0c84001c01e124052000018000ae1041901c4405050340c1d02d41c60801950001448074078020030b15a0226120114292518070900960ba5850140700440742c5070300380307490662915001125513900081100700010700c0c2450004491204585c1a1a21032504042900b030b800c00d035000e41c9410a1728071490f852401605406020700842d00e1800c09900c01020440b095000f504446074015440380b44074001c624030301148a4402421a030341101d0020b00182e01d840c080d00ca068030303500c000e003c491a005040e4a90034011032294071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 242052724 1250 242051474 242051479
    0x50708070503060a032103050f04050c130216140f0d0e0d06060515210402101805130618060303200111030901020a1101020a0516020a120c080609030405060f1305040f0b 74
    0x280e03138271111b0010144080b2030180540c0e000c000e840d80300382840c2c42c00d0003d02c0e06c510005842c090f010007078074501280c4410704881010b1070400a03203400406110088980070b4100c068002034890f07880040111a1f0081c24610403a00300200c070f020840700740d10440044c0005040c0b10324901030100465607030f0b044036242860219805040190940904440601c5243c0c014140c03d0307000344410044404018000c1da41c4c011102103200840c496690070191100c1ca600c0303030404200c65040604c2c801002e04040d003d000340b21b08010040c4000381e040111800402d00d52000c09138140e042840d05800b5001000c1c1c2001e21420000500a003110190002c041c842c5058440c0728110700200d401c02c3c03c034400d403401d440004d102401590125541c103184007a1090005101c043d0941c1c0341c110202e4601000c100c220340ba58000700042007078403010300c00c20b0740c0504444041d6040524010100c4c107107214020380c002085500094001848081180d1b10014142c041c004000c003040c2001c4180040c02015042072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 242053974 1250 242052724 242052731
    0x31c18091e0b01030603030912021801171902061c020409050a090b091621060c0327051c031b0221090604050607020111031306080703050708070503060a032103 70
    0xb02d940240a044200c950503544c80315180e1400581d400d070800c070a2000c9a028030307001243e800b0310780541d00c9140604244103040707000012070241d0614140c42c42c404034050307200a0950101503603440007078482256601e0f45440b125855854224000d10954005e04d01d01841c1009001d13031201103501821480e071040c000341c00c0d2a140c030403405a54070030880c211081d881c50b50b6018441d8903800c914141c4501c658100070b4801a415980d03840a03a0036003000000026591006200d01c142c0da0b80c1000d289200f1100c44210369103250b1185500da400005205003107849207042154064400d61045a0780750503140f10707007560703000104000d4896040c2052601880313401c160074090411000116114800c00400480c0342510384002e120240e04004400d9040c05002e801141e80b0980c1030004040340c8211003030000750755050a1010b00911400384c06403041500c0c1c10104042c10740c000c5856600051f890038200d840c0d540709000211648240d420060006002005c1e480c410301c4840ca80d42000c42041c2c80030b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 242055224 1250 242053974 242053991
    0x515040f1a04290103081809010b07020f06030f0f1506030907150201020c0a0212031204080d0f09020102030a0c08040b0c06060406081c0c020103020d05070e010806031c18091e 77
    0x60b00b400f1000d01c01c02652004100040002400c0d0000074070802c0645084040c0c1c0d8096600014081e64090f803016114107000a403031030852a100f0800309070090201c07a01829414003010346c9802d40c03001050700d08002d480e42d0208940340c1003114044603c000c003c10059491401c4404940c136401c05109501041030041f0080d0815401070007a81c1c900d648010040441c40c809408000b920307603000004d10980d010403c1106411112808038901c41c44c0901c00055880ca90822042c0444640800080f141d51510314604010303a03010003110035031003031407420400c0e804641c14003448a100c0d41e44503011104001801c1b421084000c0b035500d11800081707034100401076960302e803c0e403100c2d03501c44014416060b55510040d1540100c001141d164010702d40141400b080061403000c5803c03d48091380442c0505158800d190703881886907521403015005060080400e0690b055540810040c081c28081c1c0c44107010014541c0003c984e00504403007101b4845d030400d1400d115440c03011190418079440c10400350 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 242056474 1250 242055224 242055263
    0x4080c01020609011b08041524080102090d060b210a200603281505100c08160206071b0509130b0114031005010803030a0b0d0515040f1a04 61
    0x2c99032000d41040f280d6117400f074141021114148010000c42e422114900c00c1c02d03a41c52180300e50301c44a030381c1280d46560700310340c0b00c800020010a60301c10a800d80c01000203000070740ba011481740b205c560013900820b0445e1414000741508030f6504c07181101c403405144424030044001900b0a0450003a060544001220120462200004042c203070f00500c0410104115511000d1f038584880711480c403001070640c06501a07815503101d420464100c005604061042d0300c0d114604124030305c1036040c0600c0f0408d00d42d40380f006d18042c0001c48103e40d13840107040415034650500b11514a6404412210000c046443e0361103c1302e41070103501c2c01080d0020000311101c070000c17a140c3c603140e0445607001312a860700d411810070350507150360b86800d4007505c80c80c00da140c00c16028050103080d100d4007842d22480c01a030018200c81306005c1c02449010540322501c003080c004108859005194943d001c141d030350300d0520b56001072a5410080c50f404018885182540380c200ca2603009900c120f1055002503038146c007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 242057724 1250 242056474 242056481
    0x8060a08011a010f02120703021513030905060a0504030b0f010e0609040312110f0703020709150f1415070b071727100c020a1101080403080f091204080c0102060901 72
    0x556100d182110b00c0042c81d5030142c00c0c2c5008585062040ba41200d400381055000368000020403030160b4000f2103002220740000c0c0900d0f1344600d40003501e290a50301510001d01c1c4808902c1141d004160001312014281d20900c2240c01860304400b103c0c000d400c1003108080321910900c1802e0780950350b04041000e80c6441258640116011360316440d822a0008641703000301002c25901c16010020400d08903060407480c0503054181c040d401500010f4503000402040d5440380c011000a10800a01441048171003c064015a5a44006404100c0040c00850741540c2c0507006c2140c40c00d0089400c0040100d45221548503465594910041540f06000412892400d1303034021240d89007115007031011300c10320064000542c2e9000c1158400075040307030b07284121001e6511802c016002a001032043c0400420318904600f800c0c80c0c54085403520b40c40080001e04050b0070525603035500c001040001c40c0030090510340b54015025590f03113603551a941680d462040000f03c1c007600803540040c1c1c2c00f00040c032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 242058974 1250 242057724 242057741
    0x60c030c07050927150a0902010201050609090a060e01091403070c0b040f0e0703110310060806240c010e01060902030106030f050103081b070e01032a06020a02010509030a050d08060a0801 82
    0xc03118520003041d4500000b51a450903100013610441c903044052100d80301c2d4403801103050450001b14842c1c10300009007943c0c401440e80740118072480920460800000f001c4600ea6040070707000407260350103404503001d02817688002e001c4800301c100c048101c0c0e00120051544a200d80031240715195260007500590046101c0c4030b8000c544803804201102d00b080202da407004840c0b400150340d0242c100ea50140307070800c0c3c0740050000003060041c0310b10703034110031811b0f007051048076003094840306840b6421000b03003904040e0110000200e0101c08000c0c094000d04441d420306002480301035100c001c000300a400c00d1048000203070401d05000c4020746a44180341c1030302d17000041070307103020001052840c500c0f1001c441c607600351040d40c03400603507440e0340c4110034065441980101008010056031400301090841031145c1e00d54502d00401400707400041228245a080c2489521442c1c11800a4186030450310040c16a00030980e450300c4403940000500e00c07039041182d540042c1030716880c10b0342c00c840b99007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 242060224 1250 242058974 242058991
    0xb040f060804081207051b01021e1303021002150702010b010e01050a091401050706050a0e0f031207080403141605011109030316020f0a031a0123010f0e060c030c070509 74
    0x4102a640000c034100c04194440221b0034446c0c98158410940d0180450b280302582060354082104c0310080046e65400f40c5a40d04d040b041400c001925109400340c0c89a4440203100b440480344e80280700c0c1c001e0285450341110034403045000e280c00365000c2c2c060304034500b0702c42c00204003214698036036005e0026240d5403076540c0c0c0c440304407078200700c01d000c815041c3d603c1a90500006200540003d009801020f01c10400c1c5107020a5030000c0200007484c1184426a501043c0c0060180303440b103400e00300400e5802040780c6402d03e030075255820280da00302d5110b640d0390000e000000d65140c441701c075444811580345c401d80080110300c9103100340031158007840900d40c2d41074208100c40c0b107850603a2120142d07024001040d40c1d00054002c0c0000c0c1c1000c803940e104984142041002c6800c0b0600d0400b154010070f40c03822401007800f41118400d9414601c04002d40c18081300c031030501000703885180c5160603171001914950b5034414440c40c440d0349030000c0c1000492849103080100c0c031030800907255401190f07003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 242061474 1250 242060224 242060227
    0x10305160f030b040b03010603050f01060b0f03040314070204180c0504020a09050402070212060403020a0611120703091b0602030d0e0f0c1c12050301170c0333010b040f06080408 78
    0x510202c01910071603520355449500c0725190b6015640a104501c0114440c0000301b110318841c0c60f405080d280700741c2c00284090001d2091003450f0010070101c9501c69031514066a124182c0e142c0103400b401004800b03904189400803041e900c01c0740703001030042a8002c17014020f0040e501c1041006900c1034400c46070014540740c1040100e410240c01030301a0b20310082c45020300c8400c01c410a403404500f01c4080c3c00580c02104145d0030301131035115071058110030108551802140c04410503404401034468010196500c07888000d000c00d1454444908a507030b60705050491751410005c0d504e40004051800ba149001d84010034800c2c0010800c00095440780500418036003c01040b0655145502d401c3d00289486942c00002d40a0603170244c0d484030079150f441d02c0e94100080b800341400d00440040c40740d0302c100200c0201c1d9400241030804c50020080c0e00402c00c0148a8804070700c080060b400b0700c40d94054002050313101030304018109983c4119141512140c0d650002c40d040c02c81902c014292400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 242062724 1250 242061474 242061497
    0x61a0904080a1103190215010605070503030610030b15030106020c010c02090c070309031b0906171e01060509090a1e0305030705250c0810020906091207080a0b0601030516 75
    0x1e5090f8440740103548043d2400c02211810300303080c0301808140d000040c2c0007049520030b07000c0825107050242c0540e29116043c190a6a02d0a58a03c80070341083e10400c07078101c9030341c1c5991003900400b036100d80142000c054004141c4071848039030400c0c055000503002c1c03500481125480b51180f115401d0b0014524451619084c180c10070703540c040381060303042010040010000c01c0038071284602d444d02c0300d1000107116240401302c3d0308440c2c842d002806601689240030f0145840001da402d1400320001c100760584000c4280180104421391250f60408890010441c05040c04545c00c076110b030140c810001189180300704010f00c11515032001f0b020840c1440402c44061003840501070700304055100b01d480b400a0403c90450400149080b10203142c00c0f401805056014000e003c0b8200070344c5010350500904600240f11401291501d5000300000504040944410032451000b00ba8031000d03035a01089604103800044801c494160210307003080c0c00310f5003c0e804107880b10403200d006c3e0346805000c007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 242063974 1250 242062724 242062727
    0x21b190504020d110301120203120a0f0f05091206190506060301060c15090506041b05010912020406050d0305030901060b03040312090609051207050705090c09090c0706050103061a0904080a 83
    0x41141011070b980550b00c582080c1803000b160000c1d0301034100f800000e90700701c7e6540b0416150001c00240c1c0340f003510301804040969074202c000901e02c0070307450602006c100080303003045a9601030030300780b136030f01c0020785000103080f0001007030280c010602c07603001d050550760649805007036603020364915030000d4042004000300ea108180203202d0520440b4070703074105048001c0700425251a04016144c642050050004100c2000d00c4450031512a160480400c0d01d4440082c048a040b44038030002003400300482004c65455500a00c09440d00508907041580319050041c00c80c4c0003124404025031800c1000b03c2c0c9080b01c241500c0c440d90307042e0346604e00b844909488401806ea0140111441c0ea00c40f01888000340d41800038801c2950756121017621107156040c0b9600d44283d603031155009500349028000c0f00e4a00320121110503809a442c01ca5075200c3c0d100000740c61240d100064040d501c0c0c0b00001c002c20616800049943c000403512003030602041c0704010480350103580c02041070304200441d02aa5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 242065224 1250 242063974 242063977
    0xc1603050a12050c0d0504090e070f0b0702130c030b010212070c050402070212071502070603050903160503220905070e181302090a020301031b060801030816050d021b19050402 77
    0x441c014500b0f5818884568031185c505650710800d40d01190740400d007806141ca15104070162011b2100041c03144030303c2d090610002400600415000c40400a001e50554494203e03000114060311020441041c0c0d20300e00030010000341011500501400c103400c0e1050315003006071160b407034001c1042c04a2034500401c0200a40c04103108980040200101002a20040c00850028048045244202038a0820080c14070740c031038200c4000d140c502028058529400410307036455084255540c10002c8040c03d183e0f145015807101400226884074110f12403015000d40703401241c0c0c00c44001e100e69180c144007692000324155415070008450201e2604041c0c3c1c14002c150461201c0b030140112a5658010414400d02111400e0b16190004010020010301c1056203034040f681104000301c040c108035004010100600c005400312001052b0224548106007070050f025070f000c81211031491490b003001c2d4440c141c18009004501405a0300c0742241042078421b1000d00070005011796460038202044001d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 242066474 1250 242065224 242065253
    0xb010e070512100e09010501050103060801020412020607060608160612060b07031809020a09050f0a0806240604091514030a033509010516120c0c050706050c1603050a 73
    0x1000f0301103400213100d000200458040c81243d030002c241c3d503041c04c001405589103a03026140c40ea00c104001c002900404524042c920380c100d030340942d141c0131400c100d009404907802688503405600c0001c5200304110f00b1035421182c081c3c0300c2458403621080e1240031541c003481001e40071001082000e00081c41410090100b0302c2c007074118803a0380d440740070311400c9810400c8510086111008140602d01c2c02c101c0254400b4022110500400d0070016166101d81c0c0151104003410f040c0c441489000d08080c0782c0700541340e00907203100d4496650710407041c090001d035118800390301ca100c50003007034000720412030b54114100680103080c05c11444c2e40032104c02d914110070004000201c02c404001803240c041c89400e44000e80c141000c41d00705041a6401c483c0060060404454007070381220540d030300034168598541e04928000380d0804100001d5419070b002d110024a030340222a00413031178a03000400350018010781d0717089a00500ca0750718006000705e00d9000282099122160300c0300001c6444041c40e01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 242067724 1250 242066474 242066491
    0x30a0c0308130b07050c1501030309050112090b041a18030306010c030504150509090901060e010e06030a170a020705061303170c010f0204030210051206011202160506040b010e070512 80
    0x120583d842d0360551010542d1060006803002596411010381008200300d03400480824002d2949542c0e03001d050b91616100e103905000b1a801c0d140c003588102d500141001350001a442018034003442c14144503255550b448000150420118403501180701e0b00d00d4007008004020340c5103844030030040d00d004919036421401c000040002113000c078800c0d071000c523072f5007450b0b140c1c2034441141c60104800703000c00a01c0c91089a142c2301041060b141c0c4000080e0440d40302c0398541105840c2e00c001700781048003003480a40b01b89410300900340c0100c40ba400409107004240d0a45e0a49a00d40042104500c600c06d0044040700003003c1c1070010030003603041c1c030500051200c0c00500d041070700130116007550b2340034004c201020744c04a030400650600c2d000d464040112845d0840ca08005038130198081c140c0030b40030904100107000c0c10441201300780e045810340070f10315040c82544c0b051440d00c41c1da6a2000c484c22145040094000100e84045051250207014580c0ba05420300340091030410a640f401042140e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 242068974 1250 242067724 242067751
    0x10605030a080705070b1602011809020304030c020f1c1202010b0d0309080c090103030f030504020303041a0306150c03071101020309041b0216050f0622170c0102030a0c0308 76
    0x42030380e03040103100c9105206010094903242503040c42400c01716158440c0b0f124078000c200c880048428880e8000da25942420114a840b001e041e45041d41242034111020403807000003407005140d040340340d2500d410b02c2200c403640400c0c00d00e8144810311180e0500004e40c1594041175200040b01e03507010b07600c3c448a0780300010341410313103a0000e1342c110b14001c800c1e00030a000c1c043c24440e200b014440c1045980c4155010402c0d5403540d41c0007810f040c0b4601c01e210030980d486010404555003401103034010403840c0c1410404104a18407a00203601c10f50701a841844c230084100300303d640000c2a2800701d101500030714140200f940b50360250303062803000030b0304501042280094075030f40c601c076058513307002c0d9601204485080d0300c003a2405240e00760001c01c0b441d64038000c1000b41d64407000c851a00030241d60303a645070340b264071403030054950340c1080d1070300c065103480041040f00707450900c3d03519946004103c03042c440100005984a21982c003202c0c0006d850048008003090046c40344540003000301c501c18 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 242070224 1250 242068974 242068979
    0x15110a05060c0310050a060c020603091f0b120a080910110316060b2e0201061d07120515010e030a0606080d02070f08070e040206070b0106031509140a020c0106 70
    0x2036080681c2101c003425507a90200620150040865020015100a54070889401c0c1040300141c405030304410000e209200000004002c690180014888020301980c40d04001070220341c1c080c060420f070440c07103009085910014524074800113040000300c0d00300d21994540381c40442400b102c0d440100b0030740107000007000c01442c0410200002c060040e528108800902c0c031501d0071805039800108694403418480c511f100d013840143c1d42040b451300701907001700c02920007038506a002d881160f000d1015014002c1c2600c52000030381010310700c140c04d1995030703125810040c0100e4048130015245880710202e541458580341d40a60300281100c82c0090450381d0080a0f81d55007801d5856607001a6103075005880a1902c1c15010007004000d0164402c00d00099410641000e903141064841c44007006800b001050642d2200d4040754a16a080010b0621030742e160340c00075001e46071a142804802c042c003100013031001203034401c2c521004545031b851861a280c403015a8041e4001909601d0595030340d0000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 242071474 1250 242070224 242070233
    0xa080a1d0604060e0a030b150f010e13021b074505060a0513090c050105070201021b0a151e0905030c01080a0b040603030c0212010903020a152c0106060915110a 70
    0xc0d4801c8060012304a000d081038818480d0f040038140d1441d040c0442100725004964550700680b11481403010b00684520042c032004041c180c0005102e6094054107c010032001c120100c3e0380000e42d0800174400002051207002200551000c070480605004401d0307003200c0503080d801007a0040380040031604090740703078000144480c0754404107030112990340c48130400300194121000010300003401c22908004554002035203522624606220500032200c61404a41e03a582126014102500c2003002e100a0094068070303c001c402c062188981148a0410a481c4615103420540320301a002e40040b603282c10054580b018040d04500e9042d8440307580b240039499030710611009500990700c9445061032801400341031524042d02c04010707410180d000001c203070002000c0c01708950050090044403803100b03120008254203000703086a864001c4540c40c140e02e000001c003281021201c0204082591a0402e0b202c0d02410300c184084520b5400300b010f003880c054900304486511610a84039030a0305580c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 242072724 1250 242071474 242071493
    0x1f0c082206020c120c06040b0310080d0908010b0a060903030f1e03061e080604140a08270301090b010b070302010b0a030f1e050703170c0a080a1d0604060e0a03 70
    0x1020040c1c0c00704003004818640b540c01407011140f400c01412859035070784003141c0244112300540d803070600c00002003208100300340602c50083c00c0140540300c1644508034000c00140301445190019803c042c0b203c9920f02d411318008003202c00355118820a149581e406681e401054070025040c080c4c2c020a03c1d007400e0150842c944210120b9400040c01410206042d4180d0800c40b040b0383d85a01030070090103d01000502a90880c0d00405c40122200b1010a80c52404d003440000408180c0007140c06030744440138220580304541d07026460805031303207940d051500300c4101a00107884d40a0043c01003200320340000c010302c4003c0c00b91001180d400c080f00d0102d1004165a801140d03d511150590414840c0c40314114009110f2140d240781094115101c4944d1405140000303840c051405c10f20000c01d0304014100c0c0c60084868041d20005452401c00c107455800036a08000400e21411400c1140316140030070300d400c00002401e06042905140c0208c0d600e03202c01500907001340c507100011000c60403860 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 242073974 1250 242072724 242072729
    0x60f04091212061a0a0503040c0902070b060f0904020f0f0a03020301060e0a05070c050a080901050903010e06160c030801290c0d200c041a041a1f0c0822 67
    0x212082080b4294600340b80c11940c40e82e10541d020206a041840120703240d0b130443d40320360264540203440c0c1e102c50500b024040b115500001c49103200150078010844568407162040380100c904011050103482484041c0d841101c0095001000f0f109a140c0c5140c840c81c030402604c000361103804c4032038503540428211034403600a181605080010083d9003040d50040c02d41c481d40368500200c01089036980c85503960380200008041001c089010590350340b0a0043c0e40b0700d072078000d009000540c40c003000309844110584841007400341c48229a50000d01941c909240c580d403540d030341141680b0307003035100103400303c0b6100035401c480c2254501d14006074068040d0a14545035800b90a04e00007948010344215842501c8072484201240107915000c80400e0700c001400003a43d01041e05042e00150145c2c07105880241036016141050b01000611110982d020b0000161380e10f481d090714202105200001c6480130100241480c10340d08009000c0a0140188195501650741482501c0b1100402c041594 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 242075224 1250 242073974 242073977
    0x1e030f010e0c01020304050105030c18131b091202060c010f02042309010b120402030c0301050705120a0501121401020403051c0f08160f26040b15010206060f040912 72
    0x2603901441180c1c003403110703210106003400110300d41351502c000030345240001084031000000214400440b41580009801d10410003822801018401510032000b00b5000214031045548110b0f060a114052009102520210814900f20468a0703003002515480706030015019501d030b46091850340c150b400540080c10300c3c0300c1c5050390f101002c20000400d20810701014412100c20004200e0092000100e445001040c140050242d41d54000b01e85406000e13402c181d0198a000c04110041d07034440043e000031146082940b805480d15403203030050356028024940c1140040d44803d000910151115101415080025003003a0303407500c89505040102120020014410f0b07103840806904c2990141e2070b02407030034034a941d41018541c146035084080844000e2006805030301c13020900550301314078a001241c48074888140c0d032000301484103200350b130100c44d88144440400d0020088003c4912205c9040e03008041a94812040103000d10036542001e40103544c44028402043c20003007001140900c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 242076474 1250 242075224 242075231
    0x5070b2109010c1205060105120709090b040905030a050304021c06050a050c03101a04180b03120304030e0103021612030507080114090103080a020c0303041701060902040308091e030f01 81
    0x2140400394040000d0a512290b4580048050000c0d00004070041900342160700151315a91140140c499109209018040c0f4000d541000711103548810030300f040e170340006000e001ea003080c1020310080e110000b2004259400910a40d40c80c40c0c0b007070b00515840741c00100000f028400e1014003585164403440143c40311501e40c0304000e03121040d4003410360405a422281ca180d441c003154024a040311074001c10401115044840c07010b03214650903200545603c0006050003007081000b003005080d480300041c00f82c01003100d0940e00b0480c2d1020b49210b40c3e01074031004902504800110029440103821016207144d030a2424049a140510700c0465070b01520005481d08019102800d0400168000c1040001030b02c61f416164481d03d9605045a47c013449550719026211016410883c1b041006500361201180004520356201c8a06555984d0300d4000c0000c0c40d107849640c41644182c1c000601403210030070011240d4180312554410306407143c2a51603001c0302600010b81892070340441d41d81c40d0ba46 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 242077724 1250 242076474 242076517
    0xb03011e1805150105031510030b0a171e0616050d11070c0506030106121a04050c030a1b051b0a15200301060c14070b120906090718020705070b 63
    0x1045503d10240c45400d0a2030360030342c6494801035040c82c2c0d10350019401210804149081c0c107020b504901d82450b0004d003607061542d2294900b450200c44014084a640305108c00d5006804280642084454132880940082e940b0b1803003e0000c0280052280d0030041c040005108949084c42105202c0c0140381c68a942d4a4540c2400094001b264004520502d01000100905030b08810301d01182c40c1c20007004181010640c181e80300860018814a400c00e0074a001c0080f034403e031000940c41003030689010000c00344100e07078204200d40288030304808110304101000c48020380303100b044007041d658000c540c07011200d40d64100c00b510248070882e82c1e80303842d0b00340003040514643c8038002c111071054106055600d003000c000d10004d1402030251408808910b40280c280003880000701901c00d030342e01c0c103030346400840030020700003c125840001030242c1c001045001002240342c600711446030000b108445016030b0914000d40c08504125500e2140101c0010380305450303c00740592604c1000450900c12 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 242078974 1250 242077724 242077741
    0x5070c0b03090f0111030105010e0a0f060203120901090b040308040f1703150d020303030105040203090703050a08090a140a0e09010617010605100c08031302010509060c07060201060b040b03011e1805 87
    0x9141c980783c28860b4100781894031849050400e41341100c00174600707000800c17225008191004d2094211030380c0142030130f02c082101c07500000100081c00304100000d616548070481103080700c1c00d10b003004000c1c0c0303081e030049070100f845145050342241c000d14401182c58202c2c0c3c0d44418603520001489080340011007000030884405d450f2043c602416200d05801040e1540026100d02c414021540b0482c1e01102040da07000d030801c41200515402000c540b5098241c1c140b135401a040140141e100f11008107002c658900003d060602c03411006c0d00d0b007120203013054101035032008001c1640e040c6d5035030340d6000031303e00d00c0d4000043c0c200a4000e00001d42c250030541032002000f0303890304840a100c0598918000200b4040c2100e500500c941c10301d0300084514030040303410340f04103032178103512010105500102e0600450500100c980640003009016a01d844002c52401b4610455424030424401000445030300c24035900c0c0000e55015078011182c80b00c031400411b90700703104075005895403030041000a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 242080224 1250 242078974 242078983
    0x313060801050423091f02040e10060f03090201020c0307060801090518100f0b041a0a0e0717100e01080d0306080a020f010518040f0e01060b160b0705070c0b0309 71
    0x41409540c24070031000b020b00646210f01c00c10401c007010020000005e40310100c00e2100118481030300c0701c00000340c03d00b215400041d401900910b140d52010ba0003156035134014880b840100c5805884000203a02c2405060300202207a81050341035000b070303c1c07203922960340c10300840d0050142c603292030a01d5410031240308108c03140204003800802c804d00c005642c42e0700029800c1c0d41d9406000003c40c0b8034860f81d00c014060b004594503580c000781050111580e0b0014009003180c03c11050703034404c2c1280d0342c40400d2850054191540000700b800600860468143c4080c40c0343d000e12801c0c182840c481d039601c0c0d5504008002d034400a240c1e0059907910f02c0700c6915024550040075032a00608403800c403034000944020040c481541031000004611b601c0c21260040c02d000040000c0042100d8404c13070080710082e25903140140c500b5464401e010401c4100002990204102c00c6141059820255145180804054074585c00c0c041d00380182400a007107a4442d6002c1c042030389866440f0704101c6d180a250 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 242081474 1250 242080224 242080229
    0xd02241b011401060c020d05010e030307030903030c0938030903030402030708060118020a122f030c07020d0515040c030b070c0213240b0c070605190c02120313060801 73
    0x4080202c00100001684010f9005919030101c4000c40c4544661900900400610214211340c0c0400f00c10446403507050b500841b400c81c0240c03018413000c50010012210b140705c0e40070b22020343c0f803000710341c5090005a145859078201c8000c0000340600d01d0941100b103a4204455811881d40f0000800046060078050600184000d100420165040405580081c5a80030b08400c0392503001c10b203454a503205040b000c5064281c00d000b080740c6480c4100c000c4420050b124511001c842c407043d4480424490b01c11288143c0d1408081c034113041041c2d003000039580c41284266624401e417015012490035242c560340c0558400c000b4107040718a540f500f0b00700c410004000314144501d02c8a20300240e1948481c40e030308014032450008401d00012942000340c0c0d060708014807003140700c6401007035070040c0c10000c00c40b0b00078070007c845035a9980d203411a09403240b00f0101e04482020155188083d0180c0031035054184024090241c0044800c201403464000340e50998142a0b40c0508000403078102e80085d01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 242082724 1250 242081474 242081501
    0x1b0c01030b0d030e0103110d090f02041d07050409050703150504150501030812040219091d0c060d0c120504050a0c09050903180a090213090b0d020d02241b01 69
    0x305807106440c0034100101c01d0104c4d905150715810141120b654001c04c8901e41c1c012090108850505410072490011360100228041c07458030f0503012800780e50542140f08007000e04010150203007446c06020241011000484091017000d101100180447c40d0f514501c80603040001041c0c60242400e0743c0800314401e6281d1503d00d03100050005c24542800c84940408850b0040c3c059100c0744040b0b1012822580038465031805010041587c5440b0382156169002c800381c003424960410b21001d03103640412a0080d8003200402000c0c4080352540c001c4041c54100c0c0c1440d03000c14411245002c20355404035811683e40d00814856410803503008015406800c448500b00050715110901035075900c14410f1400e0000d5484039107640c0c5960b1903040c0d50152416040544d100c5100310303480d1031030868502900da803a0782040300800c604d0411010100c0c019400428040c440e070465002c0c031800e041d0304140122407105000d2590004866070303000300141e85e80c0e00300e41109000c0103000c05085039080c0c1002c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 242083974 1250 242082724 242082739
    0xa18050d0803011e090515040605030606060304120509040f020a020f070e13110303180a0b070b0c03090f120a02070501031118130501030309051f0f03050c1b0c01030b 73
    0x1c81c00140980341940d0088a03c140032620603000d48144c10441e90110b620541020b0803c00c0b404888145100c03001d400b540e00f07204981d150802c150710b40a0454080c0d400031b000344000f4000c10350080e00b4065820403414a00d180100040204040c1c3d406483e0100304680c00003001400c0d01d074104019411001c4140181000f04d003001c5000c0d1454501500f00501c3d1041e810800f0b040c050032a016078402c0400804991740c0c1c1304a10300a044c0010a6981c2c41d10440e4840700003d400c107a0723f4119003105a014130982102d0341c0700c000003400d640014001038400d21a40030150000c00c000c01c507a40f07038007284034400354480415003c001d1404100d0f4100718100360614244800802400303040d6010600c8601d00e4038644094400496255483e00007a901494101000007040c1904949808140da6080c0c2d410310412134043d01c007048aa109203404000104142022070b039942c86030340015001009454039070301e413600042d481e03d070700d01484100c002c1075001051425850f41c0c15209050180745c0039100c2ca03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 242085224 1250 242083974 242083999
    0x1c030902060c0607090f1e1503140a1b080f060907090e130b060a03020102072c1501030b1002031e0904020a02060a0605030d02061605160b151c03050702060f0a1805 72
    0x14000304c4014412500001e01420156080d40d022b508184039400b02100310b940c0c107140c41096507024001403403141a4801d0100010042117209460385840351110000c00003907619500305121516000070104001c120145d40041107581401c540c40e030241602da568009507242900b4540000356000c1c000510500c180441080144d80115584040b181ca901500e048210702c640c201007080d0b07904400b005603c40305010802d42c002c030248043d040740070a071b900300142e0b0084000d00101040441c00fa40c00342e801071240031b030504c103081c800039000d114400b0340c9401d092402010400780d0f00311202450240c1c005c8010407003159194801c03040145400c5004040d03a14415034040d441e070b00060100044c10740034108040035031340035104542c01d280038549004010081824020750801040e1148802a018240d4882c81841d2000d4012508840b40c9450f070b44080342903405846c0b5038000311f41281c04c500107020003240340030403901800094405884d9080d441c1ca090056003000d8280d82c000510070b110080300f4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 242086330 1106 242085224 242085269
    0x203040516080f0f0a08070b060a051f110607080f070e0a03120f090b0f0702030c0603090601080d03020403050c040e01020705010c02010b121c030902060c0607090f 72
    0x3a0740c00d00301001c104c2901e452601c480038213884030610042c40420031003401e660308950006d0000104a07079407400300741003030f400c40403a15408280001075440700360000c0d6402c00901004001c0c0c240c03850424030140a51601800d46c101c51140e0400095210b800b4103025592018010000310f2480d0b540d241901c1084aa40040c0d000a41c0066101c8a85400f81e1155001da0b104140c0d542d00b02103c0d10ba110a440d00300304001e9a1520561291f000180c440303000039409203200c03c010f00241c0d8100386600d0305d862000c490070303030070503104010420220704049488810114115004103400300b0100099019008158000e07105e9480c2c101c0e130050301c036015448000281401d42d20040030031003d0f049141c0744c20102e0003007123100941d0b0a200c84064070940c00222744a1000300b8950621007040682864940115984408112010021702001140c8011200180b002003161070710890410503 = true := by decide +kernel

theorem cover : BRFrame.Cov 241906474 242086330 := by
  have h0 := BRFrame.cov_init 241906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 241906474 ≤ n) (h2 : n < 242086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
