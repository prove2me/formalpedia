-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:53:07.541738+00:00
-- url     : https://prove2.me/submissions/a65a7359-1c37-421d-96d0-b7cbae8eabec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 183992805 ≤ n < 184172661 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 183994055 1250 183992805 183992821
    0xf0f05010e1506190305061815010e071202030105030307080901120606020d03060e010e0a230f150102030a1e2102040906240309020d1b180c080114011106 68
    0x410890f2202e00919204650700308107903040300e4040843e90044060107480d01c52450180074841a0000341a9a10401000207503030301e44503400031300a1125103140411403c0109000f805140840b40001d0024018170060145580220850318155408642d0030b50f0b40808800503500b0840e610001a0994035018000900035000319490700401040e41c1d04116031a2180111041c5400a02880c014001d40f440099003904081e0310501d50010040513001010010b51145002039104580c1d406844110710140012804111503100580000340003850070301c044070320700400440d04151072110580358000c00c40c1906015200644032054005041242c41b0984800c14000c0d61180c4a01b500c81407800800082e505420190b8044c0f030301d8886002d10058400c01000c9000e021302d418140d80c003180480410000860b900c80c50301003454101c510000091408001601c02504144468001c609101c0c0b0f80e0000c952007140e0343d0640d10004240d8030808000d0740101d0300c01c5640035030008544160300600c1920 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 183995305 1250 183994055 183994093
    0x19030c08160605060316031407240e010503070203030615090a030501020325090303120b090106030c0e03070605120a09050607090816030209010e060d06021b16030f0f05010e 76
    0x450003042e09002549400c02899614819102002c101e140c00d0703182400080c40c144c001c5a035003445001195502d82d1280040410782d411007000d03841c0d10205040064a041c1c00c1000130071881002d00700f00b403c600d81804040d44921004100c107103d60700d160701c1948000300d03200030f0b1081c140001c1c0c00d000c0050f40b02e00d44603000b50b00640300766005001c81080028500360140002d40a010350303a4508142d240b55136410780f2516070011440c546540c039803080c80c8258954841d11030007401141d40c00300303d421040102030180a84802800d0007501308810500620b81c22204903840c1a400d44401100c6d5034a01402030b000b0808654003c08074001d001c2444000384c5c1c08010402a01c46034020f0300c201071f954540d400144000d501c0000d410030f5298004004403001c402201d68441310151031004440507564502040f680140141400c401c0b22210011981d002008255880da5140d0701e207149145c00d5440d001580c0f0b400600c001c0c4005159650b8900b0424203400c41042c00c001c0300200c4201c0310b0a0b030300190720 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 183996555 1250 183995305 183995347
    0x80309010204140f010c031b0204050c04030201030c09080309120c0d08120124030c0219060c030605010507050709050408130f150305150405090c0d0c06110f19030c08 73
    0x100c0c1c0440c8504102c3d80c41c00c41000032103034105071250808014203617015241c81d00304500003010100500404000f41c0c480d401540d100711003c9000c01d0341d6504600c0050300700c0c0e0951158000300542648103022800e00042250b1041c5000c55101020000d00010fa038501401c3c60f03003a5400101d182e0f148000c108958000c2d20000018542813074440e0b882d00c041e00c031266155400e4000381d00803007405411160085d03009a20034101c81c815661840303248001c41d009001000021100c3c80c0d0f4404011080e1503141c0310f0750026001c00d02c1d01a240c80990780303485a944055005100304103981d07501140802100320f049440d510882400031061aa071000e1240da02c40e140d1041d20f1008034080d500039040c46c424820782e8490603a0144001c1d00326101340501c0300810b0010300c0c0030034074401e900d07000d0002e50711200d959017070b984a01200300300242084001850000307410008003050788801001c5421040c0410610326a01c8070f05044d182000490500300d482c1400c0324000b4001c0c650005801c2d41c58480c50080d16a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 183997805 1250 183996555 183996569
    0xf060d020d1a0d0309030825140f0114011502010608120c010f02161106040b0d02030a060b0f120907050a080a02010f0519051803072303060705040b070c03080309010204 74
    0xb2002044405000100c141c15400600003018160188002a001c0f4068510310041c510010714514102c01d40c4a44880403503000d8421a0820b14040218001001490041c0d05054000e01c04002c402d044842c043c0c41c10300480301c581d1f41c002e80121000303100b5031280b8001d0038490121590040c03089644081548048801452035007070100400c184001402103d00d0005491650307503500926844031103c2c8401202c038154860010000000e40300030a0000d090f21110302032005946c0c0c10511410000c40d84075a01c1600c00d40c00038840102204540c50030f0f59203403c101222a4000e9441400c07207420041c03d50040f59000110300b9000c188002c00054051800d4400e80b52481c0390300c50142c060b06c00c0d01803412001c0003005240d4081e44c20070b12030000303402c12013075100704005144c01100010b401c25400360021080c0e1030070054001c811030300c0d008c0b020001c107005401a002d40c0c1046040280030344207500401c80720500002d80a020880162400070085030414152904c0342441049140030f035010b449009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 183999055 1250 183997805 183997841
    0xf0106030c09061e0e090711060603120a050307030603020a06030f0e0f0d050a200a0510020c0604030806030a060c050d0b010216090c0c17030601110a0308060f060d020d 74
    0x20000340114088001c0e2082c82c0c5030b004ca40c0401007810304070f04504000e400104640540114400e031140b40486028541c03c2c0c0300c440310b60400003c071a1030030324000c0000d48030b03a03c041d640602002c5c0178012201c032440301d450260f46ea03548022f1309401404590740002d401110b610307000241e845d031550101c3c0b100c44200f00c0c280401d401d0468226030340c2c4c0c05041040d001d0782042c8000fa40440c002c4e40107210070100c508101d03c0000010b118180a013a4280070544140c00c071213003030f10400c40c040c05480d040300760310181107080c4601c03442c00f1580c0d0480144010107100c1101e011032140e0fa0200414480e80380c1c4190144800e1280e101c0050181d0000088035a226042580051080d800448c0501c4044031020170350648030b16203240c04000e4005c90311020309100068108a01050b400509050008070320b10380c0c5503980c140f001c00113101440b00380201c40709810940d40c10000a5002c84482c1e08504112440c1010031032420004899200b150b50303480007a840003601e8410100341e80c11140070702410700084 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 184000305 1250 183999055 183999071
    0xb0d0804080a0b061807030f0b03030d021b0a030c0b0c16050f0706090b07151d030418111c0b10080609010b0c030301120302070f03060518030a050409230f010603 71
    0x112884528017911a080a5010000902c00a02c01e034481e88041c0300710040480d03903101c40c4000c071b03040d503004804d031f8001550002402d04401112086800a2402040040254401c152001461a4102c0d203000f0038446c440c20124003900d00610a682c88050007980c1d03d41c030900a03207070840e40c0d103c01000e031079040e001d5a14001503c90003588180c007111481030200c1e181103115500c440301c040350841c402d400580c0d00c0c15583c03268901850484442020308008541d40c0341460006010841e5810180c003140f402c7c0900380383d0704101c420941d2a629140300040f9100d180700301c0440080c000e11021030b5044000800740e00d00040d4000c040074041c240a403500503460342c843c942204644104008843c29502c108010801840e00c4440303100041d010784141c441d000c0d2034010461808603903600c203481e1a0740720341c1400f18410a1000b145030b14030941c0f0081d07180c00c4014002030140d000300c2c401c41d6055035071022080c000c00d050041440d440c0354400c1c110b1a56242010081115001c00c1c0a10b0000034608012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 184001555 1250 184000305 184000309
    0x10605030603071a0912071502061009020a09030b070905090c04051503090d0f02070801050109020a0e030106050f04020a05070209040b1905060108060d0302010f051812090d03030b0d0804080a0b06 86
    0x1c13568000542010051508032000709112062500501e51441e030b2040300d40006185104c021141d101c111640c0c05040d00d41885900d48485a810b82c0150b54042d03c10042c00146035000741c0f00a003282e80c0510344d2801c89d40c030140d0130349407074030315921445e0411101003c000c80c1d10b28201c02403050390f0f0100c41c1c0b0300f411126010400d80d01c2c042200c20f90000d501c1801c400d58294020b0100c516680d0051044840094031180a40d080d03860a910110a194011404803001034000000280019041d00200070a610300170001d181c1c44020905030b40150381c0000c1d402c0085104204581c01d86402408017902810186060026010115168800d0b0324041f4902c5821312018011a030084505a5900c20a41c40d900c003001200741038208210305641d42c5030200101e50601d8062284640050b01104103902510701d0f00c1410098070b018210f01e0904104882d800680e03030408800411503341c40c002a203200040c011840c003e28026001d021203e011500040e140c03400a0059441440380c28030340e0703180d19105c003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 184002805 1250 184001555 184001579
    0x110a080a020d050306060732010606030b0609030d0806010309020607080904051f050906120f0601030c0914010b180a0305101401120605040c05040908031b0a050a1404090501060503060307 82
    0x2d441c079804241004044049240d0000703a48440254103020000d000d40c0700440381c0140f8003000303610700c0b90b512b880041112542610540803a86070a84010f403510304d200300000d1711110070320f0800c81408581c00124541e039200c3c2d40044802540a0440c43e9078040c98244400c03160481001c061040c1e0038880012405c1701840001f4114442e922446500503084c0b40800c41c4070000181115040309000070798161058041204500e9011900041c010350750550a1000c0306040e290001602c090410300300100c1410600c0b2070754110341d0640c0403541c0720074806203010b2500450030074666100e0300064022062200100c2e000401001003c4104001f0f1014641440d103903c092152481190740202d402d0082259500015805403050450340100e50304c03a0000303411108007103000d0b00d10520200400c800242c240c11149110101110080c0c240700c84400c00034081e1043d0890705040145120700d405134079503171a081e68064101c081c018032080d85c4070782005040380c10494801d0700c43e00c84d04400190380c00c0c00c02 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 184004055 1250 184002805 184002811
    0x1082d0307050304140a05130e01021204060c03111305190b040b040f050109051c060b190503010b0405100612111b1b0a090209180901050613050702070312110a080a020d0503 76
    0x140446024540940323440d4010181c001d1a0090355400300010240c6051750200540b24502c90f0800150703092515030000c0445405000054400d0b80c2041b90440c0c185c0c00301381040c01c98400f2a03092140201c00c02001c203c080c02c41d4010259100042000700ba400c4114004c0c00030b0b030701d04600f8448283e5464004640b80c0f00e040c403031103030000104440d803044e101d10940352180d079030b005041c042000c2d1030510200d0b170720446100c00b4070044810844284000d02c0e0a020b60544010225014049420450713800c00500380d1520a01c4140018032240008c80401900020b0242c2813194000340c86580e02c002080b00400b100c4401001806405492012440034207410312000d20050400c40a05080c0901a0700039444080d2259010780201403101c0e12010114944d80b0589100001041d103080ca803090000042c0034103001d9268034141810000c1d16980040e070741c4126078101940c110700d112402016a201d44c007440a4001500425155109028240000b4811851640e003152089911700108440e10700080e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 184005305 1250 184004055 184004059
    0x30c12091203070806011107060f020706030504050c010521010f21030807050318010e01021e040b12040201030b04050f04030206010812030118060e150406060801082d0307050304140a05 81
    0xb4004616003901c52801390740e2081041c1400c3d0040041036001500d410b4440e841180000c4481003400c61095040c80058003c3c12542802d11040c00c00d40ea81ca616418101419810014007150b0340650304869005803954020303c0401c08002d50b1207461209010806002d00c00f40b44e1056a0000455010100d0601c15182c00d41da0340d1046071a0150b00701c510b80d2000e420320b0b14554030070301105500b203020320072501c800035400c0005036a0941c64101c000e103100b509020b13016030a400d00c010030031964010100c60203110010000700c05681c940c80160014000240e40c0c1d50818685010004d10080c01425140a14000e408803811a03076106002543d80e03440421001e0282018401080980c14161303000440000e90340307000c41c0040d00c3e46421200d4680441313200007164210003403a001418607100b00000f41000f850f00802d20341c10840041c1d034400c208042080d0b164617840704481c01049629803503001222410650f0ba031044c0c24100b8541d00d402c50b020f400401340d440e80d250724562411f290244102d40e40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 184006555 1250 184005305 184005307
    0x1180b0f0d020904111509100c080f070c0b07050c1503131104110f031506131e05150c010e0a030215090c190303080f010509010b07020a0902030c120912 67
    0x980d03003401510100584100c5030401005c50117030304d80d1b940110b100d108110704c2c00031607240e014000c01c01c0390510020083c41c007071064501c41c0c10003254101080720703040e2810700c1c0540d607600300c1c601c0d020300d04c0403031580405d8030800080f9080d020403201103038070a1503210850b044180202da0141d5400544000c1e0351600b03003c1c0020f901640010044186a00036030401040027076243c2d0042c040000940c080d003540305178142e0000821180801c0f10312100000007040d03039000c0c1844000a19011107850790701891044006486070002070080e0600391001905010704001600c0c0c07001c12118440790002c0ca40c1e100e80d07508000c141d015405001841445550f0103a00503d25200e0004074209440c0d0b02a024012600888944240365202e8821010408148510729070400d0300e50b06004010b5003014240d0302041d40c00c0c800422640d41c861a0b80c90649080c25082c960320b0b80648000384201040d58007007521240080204043c3e8071111000e03040ea02540650080340e6030300c0005564031020b2000310344580540c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 184007805 1250 184006555 184006579
    0x1a240418023022060c0c0b070f050d0e100609021309021305010e0a0905010b07210c14030d090b01090c0206040f03030f0902031608010b0a05060d0c0504030b01180b0f 73
    0x34021070301c492143c000c10701802814469102e0718181c84104d0144000b040c40f0320f4111003046455250594080c0302440c1c0100c07403c2c05080d00500600c02c048185101eaa03c50301861101d800501ca0300205d0b044003c1c04001480d5221078400180d00421050101b10320400750000340717006a8000c940c440c80e100802d07021007a00700001510100c1139065a00e8010b42c486101040c0b6840138441d8901030082229415107d2586141400c1c0000b103042440c040110140b408000c2142c105014070400342d40186030308441617050304140d203107010307030003600d64481d04029007442804405100141a101030540500c10500100e00c2a0b0b6900b5098400400100d400c4c01040d011038400d9200345c820030250b00c404100400c0c03540001b40307004810070410b500ca400030310341008036032401d01ca0005801401e032090840c10b450b04002038a18080c800c041d159141e15218442030302442407049801459020511901c907507150701403204544006d540003040d407880c0219126940c60408138003174400200912020043c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 184009055 1250 184007805 184007821
    0xa02090c0c0a0b090d1b0204050c090a0e0103120e0102060f06030102190c1b0b03070c1109010303110d030b0607020d0804050405070f0201060e060f0d0f14101a2404180230 75
    0x182c003d00f81c5c60ac0311402d228104650341da40c80f0400041809403070066a41d419420701604032050450000c040c0007040070340c0501c03640c0200355a940802120305440180c2c1c0c414004c60b0292081e01c10a1515a1032484500b2000342c1241100800d02e0003140030007a542656001007610038a54040d200b02002e0500c00914400c0c4503042c400701d040c0c8209010341f40845104081828240c00707070822000320350f1107a0304182000042121801404061600f0f0082c03c100c02e0108225100d9040301078001d80c40341141d2000c0c441c410b412030b0003c1102800030009443c1c80a00100b03030050f031b842c3c008019420302000150001e14280000e0182c42e00501518282d90310b581044a5501c454030212172039102d5002c2000032a1080007001450403010300a4000844c1d0780440c03c00305d580d6290b040740c01d007201403110b00b5180c40f0744120586548240e58000d440a10303240400c4254000c82e4010400007120356014039a81103643c01034517001541d1124009011030400c0d01c4000d1244122410f50200300a10024101c6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 184010305 1250 184009055 184009061
    0x1080304170a0506070905130b0a0b0708070f030e0a0905070f0f1b060509010c02060f07030c020f0d0512151f200f070602030c0a02090c0c0a0b090d1b0204 68
    0x119028011038041010a0b0f58090800d8401c0f5001c1020880045c400c02403420140d240c0d54504c41300e070008001e200241e4001a9400c40140075082d0040350214a60b41000001c6048070709554001c03081071070307450940c0360007041000300b894076500803d00451300140d03071409409424040c03041c80d110610a0408440c00b103d010f140c1c1078144003000a12144c0a0b260001c0c0d180004040c1d005101c00b05035417404800190030b4800035002c1c0c20455000d0f2040092100311440d811b80c1112551034080703843c20000700100e2400810042d409000d00400300c5420342c0350b030000f004000610f07018030386c43d501d80c1e10318410f20040b003281c41d269900584a2020180c1229641000d124400301d103082c0200cc3c1c0c181c1504d200384002c0c451900444940c062034155080b202e0070400e2000408017031004524180250030900d441d0622208000c3c000c0703070100301140008410205441030115100d00300c412500f807030b06000c0d0452100307960100e6640a04405030341c106100e00c2c64142c00440b14600031020400f198248401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 184011555 1250 184010305 184010339
    0x151917091b0a15021e03041a0304050f06070806090a050c0904111b07031406061309020102010f14070801050105030903041a090d1218050d0605071101020307030e06010b0301080304 79
    0x880b48800002080e03c1e01010318082542445a00614000f00b4609480300d00782c0350007100f104030394800d110030002c001010610700c000b100040c409945136180c03464034919008820305504500d0141901308a00c0f075a00400091250a0803196860b0a8517245603840031940196001c1c015a40c2c01c014151150074950131040004020304400317031a01000141061b01e0408400c0e00c0c42c1c241d000200c017003090100a0b21041c411429a101910441c2004c100240b44040c0c2c9a58101c5070640350010401503a000b0750111240510395038041c40329000c11211081c4080c012910100854003603400130a9952290041d284035843c980010b40c030301802e100408c40f020700070f41e802115103c2c040045042d9511100e100b58000d038032506044030203d1207402c0c05050702c140c200c0d2100c60b40c24986410001545c0780d00481d00c1441e0440c00000e400c0e100c0103021a02020080c61540b050341c000800e00046075032591240040d58042d20a80b40282d80701d40140d103a40c0700a124080c070a904c00c4c041880451141064054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 184012805 1250 184011555 184011559
    0x705030403020a02100f021006120201110a060f05010503101a0111010e03130608070c03021b06090d0809100309080405091023010f03021e0306151917091b 68
    0x705414591300040c104070740c821070400000c103a4121015110303010491000c2c1c00d07482e500c0911440b82001c0d94100c5542da00200a8100440f41240100c04481404440c844e44d0300700c00140101000940e04c2c4025040038810b0034041e10a43c0340d095182c1c061440f4803a001c5145184520001c24400011034016201c2005c694041d5030b560061f42c03a8000400081800161004064004e140b8003031002c1d0040400820bc10b040c022040015000240d000c1644c280420003058030705c104101c0800892042e0003892101a000700b403202d034541c180451003014200003041105c0155803400d260208030b00f50340c003103400100100010301c003c1c041c515060340f459920000c402c03407072030109a90740b90b441000f090341c0c02c2041d039149404010a860f96440700d406030b50340300c66003400e5181c0b403200e444850840d0300e0119508514407011020886503943c90741c641114007861503220b501d80300381081d084250320360886c25502261851403031003c6180484801c40c4103c81c41d074042c00f0900c411075481d0701d1550761040c06036 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 184014055 1250 184012805 184012813
    0x506031506030c030708150f01060f1823040b0f1507050309030a030302030a06050604080a11030c1909240603050406020f042606100b1303020402071208011d070503040302 75
    0x190a131420480701d0010440e04c1c0081030b40303100c038a40302000440090711380020850200014481c10703810a241112403021440c00712100614100c1a800d021031540110020b10521080702c2d0340042e42c0300a40e594400104e50421000d1542c401300224401d140407140d030090010b6019183d9070441601406001e401070050300d2900a0881c006030a1481c4503c04601003036010091100302010361181b44060041518030303e02d864103101940d507450b902503100070081c0310326541581d0151418000400910070180071490000800740030b441c0850254003409824a18140c10a5a0b42911844a0712018165240c414080d0305040c0c044000d480c004009450140d000c001d104800c0b1a51001840102411401352200c090410070740b50340c01c540800c056566601050a21944100841307081e4101e420407540c595540e400503004106900d41588040c0d8001e2021407600c0c00d01c84003481100c5607850b80d45d0340d01490383c1c940c40c10020300010700b80e2010b064504d1800046443d801076000715040b0307000740111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 184015305 1250 184014055 184014073
    0x1b01051b01021c0501050d03050d2427020301260102070c031a06010f0e040c0905040608031b160605070f21031a030d0806010504030515060112050603150603 69
    0x15007039a0284941c00304002c5280c40c2030402906510071517000d8101100e00c6d0703004800e1038900801d5805116540055290782c0c01c6a6954040c0c0c03580034a810003110010b004d85540d541800c4142118203222084a002e0210b600c640d50a010780708a0f81a900b0500500b0500c4000405003913092072002200191590f0030803803e408107820401c5200258400c601c2c0d43c8402c440002d10381003140b0003411581c1884014840e20049641024000d2101c020544001489007403080b02101c00c0e1010341d200300e801a103841c1010841e20ba010000300610f09441c07110781d008030072000308541d8030140e020021002da0507054007401030034424801003c0550080c1d00503100d400302a1207013400382401402500c940080021701c010b110b600740c082c102c1c1c00d0001040c0d90340700741004c1e00400d403924151460310082104410016402d40c3c043e806a501464011044030700c1070340504080d403404002600c005011030001c3c0603c0314611020301603e441082d000d0b003c0d100069140e1100f09402c2405464240d01d4024103c036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 184016555 1250 184015305 184015357
    0xe13060e040b1b0c01060501110a0f0627150c14040e0a0b040e0105070f030605030304150521010807121101030507030209060d0204030606050904030206040b06010504050405070806030106081b0105 86
    0x1030710134002d2440001a200d07140c0f40014180d080807038984500d6030040d6408401107060134041d0410103030440004501003a00340f0211182c00ca24880c0c481002da844c00340b40b820700409007803408025080d6031080024541c3c0d954251100c09241e0120601810204401c2c01141580d00c00e20303800601060000c91480510000182510030314941045030340e42da50200719103582c0c8002004c0c194000c5040c20020f41d400e00c00802d4581c40703540a01c181e0b0309010303514401040e215000b100c10400400030003401c110800102c1d00740c0e040c028442c550841c071804d000419141d480c81280100e160703002c0207581400e9080401034006e400024481300c01d01d0b909000c5900b158440000800d0004081140140d0b02c0d415441c02e5022101590480360040c1c5444040100284c1c0000b201c6403c80d80002c1c0c03102e440e5541000407105840740f6000341e0f80107410041408450f5400c20340150003688100c0082c0040ca4480091666444440004a94083c806424003440c0e501070030081440c4544503141645001711102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 184017805 1250 184016555 184016557
    0x50421051c050c060612100203041703010f090e030a0c060c021c02010b040e010902060403020105030406020705120901030f0c02120d0f0501080d02121c0203130b0103030e13060e040b1b 81
    0x60305001c9040043c0040c0b81d518244400c99020200b01c0e0b05401c05103020b0412030740c4018a464010072264000082811321420808070030b0382d0f59400500030703904c0d80c4030000002148000d108001c08507040c0413141c042c498010080e181c41480c1a6250405107080d40c854601a04800041c1e2041d80245500395002c0c0002a2880c0b814040540011900300b0b00c00052100b116403003d900c07107190b4540001403005a036240c080700c040b6902403902d50307100c0e112414010000e02c601c481c010014842c10345841032003001c41001c0d00103240309803420010005690b0580c810358485070035440058101c451898000b40404c0c024190244072a4800280030000d4080341040f51005c0c1c0212030294130040455141e558100705120b400d45244007014109060907034140d0402e03080c00d1074801c1094021000480c03042c85100c030301051a4002c07440e100f481d40d5034180a00008900420306000d480400e62542c40203071503028880072101946030a800035501e584901c00459000b41418405000d00d80d0a0f01c03241003000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 184019055 1250 184017805 184017853
    0x160b100302450115020705030d0e011b0501051006052b0902030102030906100b12012c0f07090f050108040f06060f03120f080c070221010c120c05042105 67
    0x7402d01002c0e5040070380b54001c4284800004d002c55000c004140b08903200031852501c221032500301142d4060b0b64000603112011004109801e014200703403001d05000054002c0750003004404030105215807200411034042c8254013070f62000140d440500140040400e03a40c450300d6090041c0040e1030181035002a003660b005a03046101035114005106d40c21305552211802800340a0000d8640040045808403041d01441001c41f1030a1007009002d51034400d000541c403003200d81200968030b150007000d07200190410785480000a41c4400040341350240140350000340c41c8141c5440e0212f503110f5507103802801d0b0440084640b1605d8003400510042c8880d08200030798130600703504484411001e001450018000d60405c00c10022006000c014050001158070040e0195180c3d1110070018900a20404154820007000d40c6840008000306600030714150388149a80000d102c0e6142812003110709000313502030750060a1000440200c15826950849013007403081050b200b03088107511694090303542c15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 184020305 1250 184019055 184019179
    0x50a031d24130807090e010b101110060303030f060b041a070804050901080a0506070503060a1403070b04120213060501200a06020a0807020606010305100b070302070506160b100302 79
    0x242c002c5c0701035910340c080d01c217001e82c0c624000c2081c0400f041c00103801303220040c0700c01e050001d420b450715111035081c0004010145030202c20b00c0129503e00d80140200880800650000d16101d004100761030034104960807180d8402c900484450000c0c1c01c8101c0b5400805d08680203c4104030008050310780050f4180200054805880208080d040041c24254014681804c0200420030010140e403010800c00980c2c1c0300700340c0300101c1848100400c0c03901d0f00e1500401d58920002c240010907074034240510031503a03c269a40c1d02407001c819024010b849481c040e03140415041c41581c0005012002d1400040442c0011143c03001e0503912a101264001a80d42c0009200d0030700f00308106404201c095000030003072900b0046e51419001080c4008105c2c095058445e0340014000e0505100300b0098002d000c0040000d582c503c210f0664090b5242c1c400b0303085805100f81307400a514840700c1d40451003242d402500c04034001554880002e8880b020002d41029003a5040064030201c0340001c001d1400955 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 184021555 1250 184020305 184020313
    0x801080d211b0207090905030307210f0506150708030105060901050d061d0c03190f27050106150e0103110c1e100b0d0b06040b030a050a031d241308 65
    0x180c110013400c2000b1034000c142868202006403000a9000044030380c4016146443ca03c644040700407480305d42e560507000c01a25007080d000c00f40e00f1034280e1081d0f000f92421958100b07200c45042c0702c0f60003402041c5000d01242014001080107003400c400400f43e4010525042d8500b0070003042c0c0c501295540e410517103451950020040b2289280080a0781016018020074154900001d4840d001c41e001c8040c0c14042d602e410f2000e07103d641d1078002080d07007131300e41481c80403002943c20a00400350040c0c100303540b15800d100c030009810945c030505148042c020f980d000b10132040c0703c0055024003e41214448100c00412040f00101402d1183d042c1c02c000041240c0c81c4000c40f60365040c0ba0020100c6203039809442d1010050203079440340010281507a200d020b29415584030400035008058070302400340c041c01600d0345032080010200c1d0f1000824881d4984035100e0341c1980140c3c0310030b100500139a1b00640040c5035600d904c454a200c5590510510064a01c7d108040e2020341d003d20a41c1c0c050101032b44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 184022805 1250 184021555 184021601
    0xc030c010212061c0f02010e0406030302061e01080a0b130b24040209220e06070c1209141e04061d01050402090f0904050109050a0b060f010801080d21 66
    0x107102c0c4412608003e044640014118594110304000c0c01c03c003100808284040131400c0869010b80059411004000c10401c5050b0366824081d482d12411648007600482d41803481240b206000d840c54142c9020100034501c0c4240f542d81d2004542c0058000661560440114070000781c00c1c0324680e11030b4102a45c0040c05030465840201e045190382d625620560040c8107125042c1c0790004506501c075010342c4100105044c01000c48000c00c0b01d80458402c078040c080410042c0f5800030070b2040d04912443c0c0d00b0701041a050400c44806146005012400506a140740514038045a05000c1c100d0002500321070001180000350403140036a002409402504441140f00340b4600c0c5020700503d02500c0541c0344c80341c2580001d070540f103c1c80d04070b44200e2083d40070800b0b0040035400004119403000840704501440d013001e9101e54421180d8034410003080d8401d0081d940301d01041030403510700307000501c6685286841070314600c00b02020f42c440e5903843c600e107a030400702900a41c02c510141a904000c0c640b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 184024055 1250 184022805 184022827
    0x1b030e010f020a0b06100c0b01030803060a080604110108070513080c1801150f09090f050115020a050604110f0d0f06060602120403020108073b0d020319080c030c0102 73
    0x2000c108100d0250341101454201081c03810000681c889001c4444800381c14a106c0155007000d80c850003e0302d0308814030004000c1109030307001940100c1007150321140c2d1a0f910551241c1d65201210001c200350f418075034003a5070754080c9044580004090070370324101800034402c507110140903840068180e201c0d00d00071031a0308001c010503840d944440a01c1c4c0756903041c50000b24941003064140d008018158452400c40c62054104d9805002101e80610000101d000c079200540000e024203c0c1e0181040d03500c42c0e00500001740b01803440d5202c80681003580c1c880d06c07038044880c0800d000980282c1403546e0054550340b0b1440d0100100d1064451003d1140207041003c11101c1e1504030000795440348800c005545105800d48044944c2460510300c03640d42d03c90203d80441401c0300303c01100001244410f103060240c4c40d1960702c0f0b450083c514404004640c100903210959441c040d416411419000c42c1007080351402440345405000e1107880c100c4002d03692032079039104056101c5680d50101d2450402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 184025305 1250 184024055 184024067
    0x2030a0f17091506030d0c020f040905030d020d06151d0609130e070501020703050312041112010c0f02010c0c0807060e0616080106020a0c180e0304060302090f04050c07030f1b030e01 80
    0x800517001484c0a1401c440094928641008003900c25a00300c90380700b14517030b0b6681060301c0303040c0c2c84815030381c45040c601064006900301c80d6000302128280358000c5030321821000248007910040d5500c2681e81680f0300301c8132607107080700c0b596a00700348100014001a140c101991420b1060300030000352205040002c14144032258128604540260104102140c000016120502c071818645413042d225460118410380d0354075900c40c0c1140707041e02c41c216142410f50008540c0c0119413203001e600c3c0c911140072405c81d01c100207100081000f501c00d8102103081140a4030000c1d12030b00000500c070703810249481c9005001c96044000d008641c90b031103070181d448130360036005022134002403240c030229940303944581c1a10b0141e60b02002049402070090a00c0e40c210146040d2150107607a5240e480341001006035000190881c022075070700300b40060300e003058400e080c4038204c138600c0182095400c0c0c0e021a800300800310344c8802c01c56410031480e0030380b519442c544003440c03283e2144814046408009485 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 184026555 1250 184025305 184025311
    0x31b0c11040c05190905030a03090302040507080601081503070803220f05091303021c03270c09090f06021c0e0309032806051f0f0602030a0f170915 65
    0x80341400c44402c540e98206043e188803c020544150740e01d5003000c01112142c45a500080c1c2c14419104940141604650f520041d40c5c000d850038481d40c0d541e00f00503682c00c00c040e038990703001400c80c10001b4000d4070441000b5110701d03c002c00ba100003503540c2c05070304d1031900940381c14014040030076903540382d0410140c012070061500d0311010848a00c0c0000180c12144020b01e100707440e022034503406040600c2442440b603100489082a14451000d200040041600031840c16908230004104580c1c04040c0d20450880d80d4032201030394001f400d10f80c07404c0142a042e04111500551580e480c070001d02c2e41d002920b0f0302e00918446082c10b0000389078003000d9030300120200001d43c100b00205020b40d02c1c04240760484072402001c940c3c02c1d2041c00040d1a1107802000042c0800d0302d03210900141d408030710070f0a409059910032204d01c2c00e855041e1312018185034841c51340580d20402c03410f81d100703029952951149409081000c0c400086c8400046400c1c2d04541d002c00a4209081a813240314200043c01d030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 184027805 1250 184026555 184026559
    0xb0a0608150405070e06061209100b0d0b0406020706110304050102130902070807021509041a03060705031905191404020312130303030e0c18041119060e01031b0c11 72
    0x41500b0a0386800d525401140141136020840c0701c0014000d8071070008682c0041c080d21400742007440d2035444641c0380c244e0758440e80341d240d0030120900402d02d004540c0794540754201401000c1a119991118029400b00b14200c0c0c50948800e805042c003882d01c4041e6100318000e00c00540d5400b0b00079000e410668030f6400c41c2688501c14840d582c0400e40c035000341c4440a0381500c1410480d071908004141c02d004074060ba5034401d041c181000f4101e8001d42e07000c20210010f608030b80103500c0311802600c203400102d0b0200048040e40040c400c1c0160185c01054000d030404683d00c0403843c2041081c800d4401284180d00349800303440c280021424204442080740280030301d0142003602aa540c0300e80c0c018684400390405454200b289e81550307081c0104902c10800501583c03c2da126401d600e071032036804540a941d0b010300404c8803221410400014810080c01c6c0d030309408100c3c20010181ca03007910203081c050405944044d070f01218400141002981c020940301e80d0142d07407035031800e40428503020340854 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 184029055 1250 184027805 184027843
    0x50103050f1203070c02060703170a02070615030305030c160b070305190b010f03090809040219020f0307020f0909100f0e0705060f041202150403030c0b09031305090907030b0a0608 79
    0xa5500400d2004c1c3c17150704407140c907510f03007207410102c84145c0c400842882c00c4850780140842100c0b164000c00210f4400c0d001030003d9400c2240c403181019142c44003070b01190381040060682a000801000c48038001d400e40410140c3d552602c424413101214002c01113075944003440421014002d414860313214481c0f0a100700030031480024003506401c1840018162120f5042042001d140151401c4040c007400c1152100c2d6036910a400e200190400c00f8054050f201d1586c1c00001c0c0030045541c0e540d0042c0c031070119100e541301841101032004111010307501400391001c40410842c0120581c1c1c400c86c8a01040b40020600494200440c6500407032045c00204502c0d081f200c00201034400302c640740784103e0b4100c102800428040c445851040c2c0b0855800100401055049456660070502540c1c464007aa91401d103101e940f44200344107581c1952054004001918007642403d80c0100b521b01660804c030341c2c940d5004a608400d460142c4100e031280d40c14400040100324403181119841e0401c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 184030305 1250 184029055 184029061
    0x61202030c01081911040e010503070b070210030603061a09010609050307180e0a030519032a1e0e090f010e011206110706020a230d0504060f050103050f1203 69
    0x7603540902810741e505004900d00091020042c0c4d140714040329000300300038003000042481d5250f040e03126010300e541c80e00d180343c0003090500300000e05800b5100c100d03402030710b060701300d400b0401c11184141c118400c041d02c4840100005440b8000e4a001c50040d40500100d040d40000308401070708140c10403010451001c0d0100071969000940404441da10701358451070321036003c1c0c01c8002c1d0050311210b0080344180e070358080816610900500c0c46141101030b90054126030201202501c907511440034180484002d10f140003000307101140007600060501865000d4085450000c11160651050210303030748403907140950800c4000c09610624042d0000303490b60502c1800901c9280600907881081003291008003040790650200700c1c440c0090384281e445540b6440c2c9000650b01c815007040c001821a9040e85541c1d014492405e00c80d030240c0301c0a4106100215a00d0090400030700130707900103071282c6120446603c00c0c840c03e03018601450107080c04a649686180c5030584017445010307044420420 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 184031555 1250 184030305 184030309
    0x1d0f13030810050d03050307090501020105100e0601030b040f0213080d020a120e040212071107140f011e030516020615060a050705070803040602010c02030309030a030504051f0f061202 81
    0x4a50821603250520014030b032241501c519401c03100b600195040090300908209150b04039015512900b142d81d150341445480720012800c0c0c2d03605540000c400c0c0342244082c0810023401100940c480b0040c540090790124040018003501c084020308180742d5800215001c1c084035000e219009400e080000b0301e2518189107009650711042d2001801d129101161030805910909000c001c810b4014001e5441d034080c443d40c444001819039404000c0b0b109605021041da0021503000d084401c060346246140155030188117003c44003c912a04100b602900c008517003800e1242c039444041a50740000309403403d03944030303c7d06102034134190040d03501003010000000901104a45001002d941e0540c9500a4120a0301d1a00482c03034002c010740642303803001c2070140d0000013400031034071664001d000a1045002c06e9841c0d00c42600d010300c40e5041044598000d60183d0030072908580b00d002190a259081c0080700c1143d80710110032580e00707803500d010380d0407e40c1900840b0b018050003040616800e0013640 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 184032805 1250 184031555 184031581
    0x2221710021806070c12030206061e0907030c020106030f0506070906051c02090f100f020c120c0d03050f0703080a0506060c100c050405031605040f0e19050102131d0f 73
    0x910f104080004400081141c94080d260080044484c6002c0450780c5143c0603441d09012640c890003400310303001c0340104501903410345400c014082e10342d66490b110703060100c01606255070040199034899000000064140403094030f10342c02a40580260705040800501880c00c0e68000130130840284061003001c0a40450324500c07a4103c800140c0d0341d811080030525a6000540550748040c15481a814041d0403401d480003481142c0d0075a84000a90380c10005d030341c1101003001c0740a0f4007000c5884020f007004003030001c0070f5019052440c20300a4659075919030307900407202100000c0c1018244030520009005050301301404407061703401d180100084503980e00150b60b00c3c014807a00d034244111441c1c0144100e0303014110181c191542416548001c9042030701c41c1c8145409945050000d06002449210b02150707554600060482c02c140900c460f05203811421050703070035560030481003141e070440341c184100030f0100c3c0344050074440489102c070000b40300040034080364a403600100107240d1102c803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 184034055 1250 184032805 184032847
    0x5160503070b0d15030503030a0c020d0903020103051305010203070f02060105010314040602090a030204052a0301030201090302010c0305210105030d03050907121505070503040210020106180222171002 88
    0x7035069510f0303041d000c501c4006000c0f00511004080c1488002006200010008500c144030070b020900c159550035504a0341c4009182044000511421040c070041d8460381045400401075107143c1002c10744c3e500c0d041d003240c0c4140e83e20b0b4040b03541000c004d011160148566801044242410429800300e59203007588843e0040c0300901942d4001009002543c1d11a00790000d0b54024004000514080b0000140142c10200201320b00c5c0d11501e407541c4c15074020007103a046e01c6d0306a44020040b459070303005440e88600c15104034248981130000c0364440e50700549524545000c101c014210b545017506150424100c12a80401c03d405d080402424180c006246d03c111503007074081d580300300401e003071180d044410040c03419156418078042c4176860394000c2c040d41c01076000f00c8456480a040c00f909034203c0d69103101c3e4607100804012401c500740100e9005d090103203c000e8107014510742d8940c0900c4101041e0b0800422400243d40b50b28000e00100010314642240401c03c6242410791150035840701184 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 184035305 1250 184034055 184034069
    0xb041a0d020c1e1207020a060509180703060315090314030c040f03060c08010e0708010e0406020c0607082d0411150d060806100b07020108060127030516050307 70
    0x54180e194101079044034031941c1c0000070745800f8520075040882045200003600c6581c4240e0002140f0380c1e0540c411540c402d6802064900014603115040d5159000f140602d90300a030712020304812903810103080c502ca407102c1d0350001000c81c00d62410400c440e504418001c0c2d00c6240c40301c4200000d030031179400f04481d581700f03900945981e40e80c0d40e404c009100740c1d00404045060340800004201079a0400d960203031250702c590301d0603030b299812130301c019800701c403040c000806103401080200251a417280d00280250005483d002030440514a00385064402c03d002035410303020440009881d2a07100141c4900206000c58000ba07818144443c40019002505001104800e044140d4424030040603607555190029281d1702c408070038000412217440b82c5401c42c0900030006003231a88509000c1c055407582c110403800c045194004551a03e4010b1030541400700c0030b01800309181106c110071001d45492280a900780e410740c81c00740c0c10001c181c0c807000c140440e808000d1007281c0d008075116041d03c1134 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 184036555 1250 184035305 184035307
    0x20301051b091e06070318090c08010e040804030206160b07030614010809010e150109060b03010605250203030c0f0115030b060114040e160810030b0c0f090402190206010b041a 77
    0x2010040b426200000003a0550041300056200200350300410941c00c42103040f020007824598641c0184240c60640c008807001a22540041c00508003c010340c940090241ca5101e0800307440341c0c0403603016400004014184168140304408004c0c0f400016a0320000d5840d05000d1549090a10b02d420030308010a181407000403000a55059400d5200c0b0100100c17501c100d443c100419011001b100d1800e010b407041c410b040100104103210349104607030407a0f1140e514640352581c00e0412040004029502c004d1300c0c2c0318105240c01503901003010300f10111100d80a00450b000d0001c8003421602441d001d00c1c0d0703440286404101281d100d20089520180030300703201d076514180c501c41d51614810307a004800502d0b400b138140400f64409500101008809071180150768035402d0010b00d4241042c40014481c20003400012200490b18010b0003c134000c41c418181001106400142030341c0000500303002544010041038205a410411140140f420361011440c003800d049180952401882c815195414 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 184037805 1250 184036555 184036579
    0x5161106180c04051008060a0c0203030109020f1209060a0609060506040302012006040503120a14040813030c120215040608040308071115010609091a0d060b120307020301051b09 78
    0x201444505400c0c58001c00402117494604a40c845201c1746019540b00361140a000a00303030b40c100e104002c1c03960300640085084d60f01e09002900694030001c41403010ba0703c24080c0c2e085c0c00b1070000a00d4094142c241c094404d51514040c154120740c0350354043c02a079402c00e82c04011701c0d01c1d0f900c01c440950f50280381a00d000843c1c0014040740070785250030010103105200c1000103201010001d8540324201c0c00040910340c4030b0320400820780d161000303440c95490b080d40100e000180c24030010700300c01c23070384000720501c83c0d580761501c0b004070368030b0b5104a08030b042c000f03034210451a007070054540c492002c206031810a42044001040144001c1005040c800c0c200d01040d14030b400b44e065400ba044004045807407040001849507585c040c05c3c0710f40303808911940303804100044140901d949110024a0240c0710b11410400c01c0250b000c0c405080d11000d954000341e0f00162141d000200e4402e82c0304004655590b1765205044c00c68000601346501c04d441c4481d200c002a0320b02040350366000d02115420b9042d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 184039055 1250 184037805 184037851
    0x2150403020a060f12050124021c08220309030f050c060a0c060b01030b010509061e0a02070e0f10093b01050c07030503160504050301020d05161106 65
    0x220540c0c10107944041603103030000e80a40e020545001c8441284c1e034400b8280c41c40d01d04030342501c0c403c0c000c100c0c04000810810384189841d1802d01c41c003800a1048501940c1c00801103401180d0242031000010440c4d0700b0090001031903c8400100d051701d41c0415100c0300551802081d002183c08014030521081e0f8804003072050030045603a055800a202c01d59803000c40300301800c04800d60000b25041810183e140c82c8640c0680719501202c01d06840c7c0602c0c251048003000250340c40b4800ca084250207140d0701203601d6108038003424520036550000c02c2c1e03260414040501c0c0b2a030081c2108a07d104440c01c110303440c00d120290804031401c02c2004101002c8200320301144e9504200c10300220308504d5014148050031fa80602071001280000f0005d40e260880b51180303a01c1500740103030200c0e104002190004030501d400e0022003150746009030500d6155000039007a60700403550300c0d200d6a102e1041c0050030301903031116403890b007041c1000c0fa82440b05019081d1214001050a05a0480382075000006 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 184040305 1250 184039055 184039057
    0x5060c16090902010314010803160317041101110102090a060f1704080316020a02090c1b03030f070e0102010b0f0609030a02130e0d0f021b120f010b0f0a0b070215 71
    0x40d500c118a00e900c09844000001c001c01d182002a4006414044254070820ba107a60050589590401035071501551a9000d10801901e01c1d0031001c200e8000c550050081c411518240114410300e404814122408001417138031f00d035200c9800440e40b0400c1300c0030656603005030702c00444407a0f05200c2240c451524054514089109031160040d80603820041003251180045200f01002c0b206c0704241100420103d9880034100e1000303402c13002c03160200e440803000c0c0c0081c204018624010f0698030780d00403145030440d0001d80d601d203000d00e003400502a0075078000c6000d4505d210300307100820000c096500010400e011050300f035406060300180c025182c1d1010702c00c40b00d00d580c0103001e001030001503840203001030000f00d411200500030b170405220b08a204403075007010001d890f401000340c0c49400f8050036031420041c1143d980050046081c03541001c050001010015030704000254240b941c1c0144042c1d121104000c0f0b00c150303d40304043c402048404140e030300954041c0d90045030f6140c0c5032644007071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 184041555 1250 184040305 184040323
    0x30406090e04080d020a0c020a0803040602100207110a0b09010206070e0105090409080f07081b03040302240403060f0b0907020d120e0f010e06040606051e040504030e0a090c0207080f060105060c 85
    0x44d8070700029012a646030031054528147c1d200f524100b00d09030f0b0380c0e00c1076600ca000f0340c0038140068002010f00029844130b500034144a038090724007003041e450b0dc00001001090250f01039004c001c2d01141c0380c107082d81c0501440703600016506041c000704003a000002c14070b02c02c41c041c942c071540e0f945001c3c000f408001c4c4c0c19510940c1c0b400541c20b5175680c03681000b0340950089580e07101e920b020545001200303140801628101c1e503018102200200c00e0b01060f50b50100d4210014607020024000000403840c94043d400d0f400d6021580000e25100d9001071041441000f003030034041d075021410b00c004682d40941401e01801e903404000520340154920141040742a03060a8815800d018910118400108440380035a12070001004896500c40600610540d4001b500c581c2494504220300700e0b00741038100b15407061203440e0407411060041c0010321180b44a41110400700e990b10174980d900c5404020300c0340644071880080000d85480070815a40711014060180544008a850342e400c1c10104800d6203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 184042805 1250 184041555 184041577
    0x40b070212010902222003061201020d0c030b030c04141305012301061e0903060207020102160308030106090b03040c03020d140307110406170c04111c0603050609030406090e0408 78
    0x26103065415122030882035041d400b900098504844c0c10940b002d41c041882c50b404410b1101070035075440404000801e2703450103000700380e55002c0102c9480c0290910880e04402c049807000680694848203051510041c4580240500d14000f400d9854001409a07503a100d130715110741444c00240340c41c00501424040340890444404640000807a996181d1654145c40d515a035011010042c110101daa0042684500010400301d900c140080360f202d800800101d401801140c111401c0e0a2100f003801d0017a6000380d64088004c0014002554403018460080900200c2c850071800e00d030b1210b00400303640d844020f11503c0d108205200f00004000d1298501e08404151b0340c5500550401c40c0081c101c00c5600c600c21490004089110f0114181d0701581c044d445009103a040c030414144001000410a00071560005002d042488030411052040f594400000802c040e4914a04503140480103448a14660001c2c03205100d0540d00000140458601c940c82c85007689640c2805140703072040c2041c2c89 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 184044055 1250 184042805 184042819
    0x180108191113081c02070e0402012a03170606040f140d020306070504090c080108060a110d0204120c0603020c0a0308070e090906041a010f090f0b060406020601170102040b070212010902 81
    0x791190f0200c0d081680c0000041d41e49040c140341041240c4070303c0c0d40d0040f105007141110108015502c0340458840200b02d103141c41c4580700000d6840070100300c2e1400120005000070203034090020711440c41c41d400850a071161800d2900301a80c0c1d0040601c2c038040c511103544541003500071030f955603000340c21840e000790644440382042e240040042d80507000b0858010b00b842101001c035845000c003281251150703409010325807038000010020b040c1d540501005950b050008501607182440200000d1a0b60300f110a0012664501000d10140e1035010301d00b418818064203e034240d0119211142c00e60500d00059250b4842e0b030207030781c009104104150000c1c6e6400c10400750084c000303000d900450003083d55182070b8081043d085072070758090003401210440c0d14401c20102050b50440c44040071810404540c031400303040401c40315005030740284016444640100601c0b0b603400754101034803001c08020b500d09805c080540e9800c0c07240350402030280701c00d90481b110031a03081d03101d2480f9941c010000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 184045305 1250 184044055 184044059
    0x302040b150313061406010516030309170c01050c0406020c0d050709090b04031b110418150203060a12080a0e1309030503070e01020a0203070e1009020d02180108191113 74
    0x90f0403044480302007203400030b20303141602d904c0381c07090810540714120583d00c0d64070380900c440034140e070444021003c034149034135072400f500016044124904212103802c1d00302e481c0e000701000d8a0948201070008009010200014044d80e580881d6170b54040900303403007520750441a480c21381c1ca0207400b0790002041c1c2d4500400c90007080409424140950700a948500310f030502d003103008005c56a005001484d801c4030345001e0016090a0b0402402190b1310ba900443c0802251100c1c4001c1a84076800104160300204101c0b0a203403010680c8003511024202001c8040c4664035516188a20070b0f51001380300803078a025666a861000303503000304000044c10703c0701c03180d5481c014005400c1074404001251300c0c0c041c054969407002601c22300c96500180180902c6140221000707014502074003400d410100b8901c08581450140011701001411240c01030b980e003082a0321b5003589203040803241c108417080d0103000301c4004121080c3c60815818000003039440380d034099031100d480703004081800800c02c5070340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 184046555 1250 184045305 184045321
    0x3160c0b07051e0d15050f0901030b19090809030d180303030f090807050d02010c050c03030a050601020a050f0f0c100e01080702010e151902030103020a03030f02161203090e060102070302040b1503 86
    0x440e03003030100301703001c40303001e070702c0c2c00822054030040f5084580102c0d10800400209898600b0716402414403000400c10207014090181601c00e008420756403031200040c1a0750300e0408100842011000d03140c294104803642d21650500c4a1511001d010035803200410f46c81c00803240d011507881030740410740359512002450038546902c03c401380c110140d4030f40380b00c00c032842d0b0141040b203a2420404010710714540d683e030560390040602510003811840b40b41207020015800300000054902580001c00e481c410340040b0318500001511340d9030050380075245a50030640c103c02c007400d911809007822402a40c03000d80032070040080b81c00310000762090049449410700b1542d005401507517054000c081c5082c1c111100d01c2648001c0c840250003a0f064002080441c0c404c035000c0d083c6001e00c0c419641031600c11a01d580e0070041d00d400070001c0710100803003d4101908235070240028560404900d4803460b10000103900e5800768440640148c0d1a42022131490355071800300d000216120101940303030f081c8210 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 184047805 1250 184046555 184046561
    0x9011b02010e0d031506120902190f061407020d02012d0e031902150702041e0e010b2101020c07080c2403040201120f1103160c0b07051e0d 61
    0x50b40240c1c5014048104003120303c00e0246840c0c2c041c3c03a0b080403800c00c0c03800400702c0d841500b2000702c2d00c600d41e8031010000103030b03030713810841640300c6078640180e04160a059420071008210350182c001d203e41000c0c0300310440b4400301510b0015404455130078140115000603076100000c0c100d565461000e1001e04c00e402c1000200300c1003082d407103681742c02503803010406255482c005690542d003100c5124920b00d00518120750340c0004501d03001c000b1400c209496002c10180c45071403402651000080c642e0b015640e01c02d1003007600044015009110021405002c16441546410505540d200440d0b0001c4c40c2c280940407140100460412a0507596035200c1d0142c881d00300d000c040c0e1168070402080c1070341c10f0003019451206403020700200d1868030303598010344010381d4001d41c0c0c50100361100c40314111901c2c2841410100c46865421554a02d01400408107108101184506201070000080d02040b81e4504a5a0100060514565400d68086c614078035000588103c40700300c03400a10305100c090340760 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 184049055 1250 184047805 184047821
    0x12060a06060f0c020d060b150d05010501080a090b0115030b21060603030424090305150105120102070804030219030209040c030303110a020a061d070306051602010e120309011b0201 79
    0x1c1d031000c40c9408280c02c11505100c070b200e00658022500b20082010900c0c562003808081001800081582c0c0340700880d0210383c1051180440140e50345c4010442560040401940310316902c1382003242c3d0859a540a00c41c003410b01400c407100034415404402e090080d4004034800e10000c20700041c40600c480e00d00501c8595a40c2d200041c01288042405428000180c409407000c0004c8070300c806480d40a00e1180039680c07071003071003086507a9000002044c0140a41e0500314051034602d4940c0d070414050100d0840d81d0402481140e10400204000c111408192003d60303074116002801e00b001c010581c4100300c0c454101961064802e003c2c0010802c180c03503030200f201d01c251018090500e007003d9500c0d490107800e0600000d81c2042c03c2c428005025070b80803a010180d82801c400d1141c1c501c2c03030403d01e07094140c0c2040750040d40e681c0901c022101c400f2031900440d0882c0c4020f21110b112080b04545071903520f5900030708040048082804440203400c040c001c8000b0240b0a9080841c90100a020301240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 184050305 1250 184049055 184049057
    0x10203060a0909030207061421091e1b28080c06190c14060a02071104050903040b0c12070b07030513080306060705010e060a0c0f1809090212060a0606 66
    0x2401e000648401c0600904480d03a8164000d041d002d8035101c0d0036100721031605050b21404108102d44000031908000381150041843e50414103881d1000440b0f10300424003041c00707860b200c8100ca0243c94000001c5682d20154845060510f074500c0030041020700141d4000307102038074a0500c0308608405502206070880c0c1030b240848221900c01424030210380716540e881c138010714000c50800d10003405100030480c55845031450a64240c6d41305500c904001d01a180d983c08a0380025103003040c80040170811080c051304890802190030700c042165070f41d02c600c0c0b1070220415008500325072004030500c000b150020049402e10b50302c1072985130054003000c0488807500420310385804a000d0701310751803110102c158800c9140b4a943c82e800b04100e1903400c201001c0310190740310500a0410101844031602035043c110020a00085c01e041c00b85c03c807a4109103c908010342441614400c2c041e102d0003404982c00d40c1800150701da003d001246000840802441c0d640c80f82600b803004410856100d10b0485e091 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 184051555 1250 184050305 184050319
    0x80d170f06150309031306020714060c070e060303210f0f040309030206130807030f0303140c030a09080f0a0c140307020609041a09010807090c0f050a03050901110c01020306 76
    0x2802040250440152126500a0980304074000c8100c2c00300000d5130045082422a41464515462401c01810b947c21034401604204000c010813000103044d00148101219003d04142031881865581c11882c070074540301d2800740011884a407414400c945400008500088161110745180c00c1941000d44100c1c0004400c2000640303a54546480903010300c0d4991b44550146245800700115504801c0f04683c428014402c0060704100c104046801503108680d001c810000e1030501404490161822561741c1c100d00781048a103c0c411011a6440304a910380000d1800c201e0610300100c0c0912004203229030000920071690302d42110040c446640b0820891001e03084102101d07490380a43e0800941059080c040c2071070619060304244c1e503900001e20450345003d400310015040c2030080c1d0000070300342c001d902c1c18089003456028203441d01c0c80605141c250000300c4007000b405442582c4452080544c1d072008160119400c0d00325604000000c5800c546850050720442d0003035106548030303803107004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 184052805 1250 184051555 184051561
    0x130b0316051f030f0609051602030301030f120203070c090509160b0f07050307060219030509060103030503040201030c1205150f031504081e0a0f02061f060513080d17 73
    0xd0001944800e680c0040c11032103a0a6034a040419825480145034042c036441d101e840e02024603e00c5142c00422841d400402c0f0fa00780308104040d2100300c42520021904100300500229014188221040b58040e00b4190507490307418003241980110070008103c43c2058500199048403a040103001d40303101020303500740302005013003058543e89521907801d50240602501c01c2403031495000c1c000250244045d41e1070111641e0b108802c80e4060039102d0002c6001240c0501600d41c140304199104105600030701581d4115140a8035900001700024100350321041c8240550b40b251a62900c80034101c0c0042c052410281c0781140d550301e807001030f10f0080303640e492244032901c0c1c0041c0b005a8120015410400d945498980c00019800310b00c815214484290359000c003030300c0250080a00ea00b00d691220210018140000c0c01e145010b400d040c42a1000711303110060074040060281160101d05181e0368658003a46ca0006211495000b8034103806003204850140c6d81250040c05100d1050f108491f040d9 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 184054055 1250 184052805 184052833
    0x7050a03112a0f01050705120301061d1c06140c0a02010f060f0611031903090605060301020325030b0a08030a0206010b03090d080c0403020d05010b040c03090b06190302130b03 77
    0xb100d8003502110305640900c2c1503080381800c111a00b140f11061606070314010b0075407913851501c444002d01822848000004122030380c0e1003144105c64100c0300605055003880900002c5100106000b891060302181d85080e0400480750710192810000e564000c0c0c0324030b0300d070305c0078542500030200500140d400e003c8840442c1c04c80780300f12802e0700c001140308030005007002000c980c00144210000181d2004121036a200d10104138040d0203070f203040d81c1c0480c80c147c40d85070413802c3d1040604090f0090f8014000d10410465122140c4043c1c4800c0040d504a07080500c0700301c0240c40d04c06c1990750004811140400c41e502d002c0020030f045076403902150f0541e40c0e1101e2142c1ca41c8021600c800c0c40d50003540042c80d03054030035a0b1240e0070103000301d001c03400e081c0c994002511001017000216940c1e0356582110f4403a0800303008100040302142010007070706035580ca64240c8440002c0c007181c80307241914000b403181d425507012100555009019030707064502d0748510100070200000340600c203206c0c11034100002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 184055305 1250 184054055 184054093
    0x52a0706112b0c0507093602040509030d14040204140402090a0905120a0f020d020c1806030a08190e0f0d081b030a050a1701030c0e040807050a0311 65
    0x448406540c1c4402e581d030020400300e0014000c40804108040410b024010038003c010140180070590400103001d6030041c080c144218081c1e0a103002c810720304d50142e00004008014a110300c1d0140c8021440e6900e99002c981544202200f00b00000d2815120009425006107000c2c170491080d034081040d290388800101c2d40a1741140c0003503002100074000340c1c5510310f03a00019601c910407000c4607105080f581c030044503600400c2c031540c0010300c9400c900307002c198104880440c4044500140071403909080101e41c060220340740c2001d15036152804104152030400044180d243c016040c90380b034040008912240408400c0260b0006118842050301454800903040c5a514020400c41c90303c006c40d0303100340207504921100706001001c00d84581c60280140000d0035030403180d5860f180c0d11200140003605d01c083c00101d248801c4002801400052500e204000a60780d40a184001c42d40d12441c115626108000b0300400d1406072514001c10990012200056035800c401a510f607d95400360150030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 184056555 1250 184055305 184055323
    0x905030a0b16090e0c090108070f020c0609030c06070c03020909060105030a0201030c030e060903030a0f1e050408130e0106080a150303030506060c010e0f1c080601052a070611 77
    0x110815180459002d20b407400c0c000c50104101d0403c2c0c1103241c1e80d0304910122080031140841e9034100069051015a400b16601b94010190306045030344d07200200000303554030384055515000d01d0b0000342c24821650104218000014002c003150359407007440c07610040944507840f04a00a04960700499200000031884034160761000c1c000304000300d401e0b00114054000c01c0d400e42c0600d6960b21003010103e1050200500c6103004100555407400c0501181c8115021442da200e00350340382c08081c003550141c0521150804240c01c1011400340c40741d0820001500c40c00303542c41c648019950f80028000e2201c0842c80c12201a901c41483c1580d0f02600e17102501d0582031507050607800281d0a10009000e54841d5070403c8019140e2420241c24101c0e403401c64034544004822603208280c3c15001e032104115901341d405000e00d0300d141c00490104058012000540038a0500402041308d520b50811501c28200000d16120b805800000002081d91280000e0003080c0c005948582c2ca4103190500066000c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 184057805 1250 184056555 184056563
    0x204081b01020d1e180b190f1b080714031306120b1c0602041e03110d050709050a0207080d02070201030f05061507020409082208011b0e040e0601060f0905030a 70
    0x741c0881390507003126034070f040c146030000050105c1008282c0c40c40410283c421a0010318419001085101003d005805c40e405540d007009005002c4000070742040000941c0070754840301141e120805481c00140b68900c0321001ca00512002c900d0110103980c452690301218415160200e5000200610301c0c00c0e01c2e94081926040b00000305c2c00110b074690141848180c030b004060050505890b60f42d03420300900c2800c80601a00681c3c0000c1c4180144e6200c404040d402c216802401a04030307070782d402c0d1901130510800541c2665100060b00e440d40b140c0450f107400c1d0744080c410350fa8143c002c200e20025040311a00364002850305002100080841c40fa5500440c00100315405100700441d1100842d0b00c4050120b801c20b803038100060000308107001a001582e544002e4003083c16400e4204810007810750300400f0103a0400200c004414081e5165039000492450110300c441c05603000f14000d80042c07103140031035221350030002400660000b80e40c1120038003991007200b015580c0c02095a00c00011070040c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 184059055 1250 184057805 184057847
    0x1002030d2a050c07030b070e0415120b0901091a011d010b09060f040302040213030227040209131401050108010f0e060619030803090a020103110703020601050907030204081b01020d 79
    0x101c0c1c25000e900070b02600400300c821514030584a644440c007122050300c0750030110328600e0110203a40f80c40c0c007402044003000100d21009a02c1c0104030a000c02d0b0410020f0030a44968000c9401c0c807400307401008401d03401c11400306a8400c072060101d0b0f01002403150b40203200364003100d20601c02c01d15860174101c4042ca801141007401c0902000015485801c01000d14001007000000580381e80c009003480c403140e222480c46552039801071211421442c5100d07074841d0500c0001c1c0041e44841ca42d00340d0010380503520300364a1f5444c10569454420324540c041c00c0f098003800720000701e050540240b030507604010001d100140c6010800c0c01980c00d500c6c080942904100c000985a003000e2400c0001075905444407490f642e52a211400700d5482641d401c007a9070804c894103000d40d6007600800802081c030096840c9808501c2c0c80003902c43c2410b0107000d11130000750021031401c84c403d070140c4026010300740540d000112a01c02c9000c101000c214040d015014140c040c4401030700404c41429803160000000e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 184060305 1250 184059055 184059131
    0x51305181801020405190801060e040f110136120c03080a020c061303030801050d0209041101110706020c0a08060f0c0306062808010503010c0507030503040f021002030d 74
    0x80da262400d42011254990f500748000115581c4003004442c00d850303002c0c003010005003400075440c00d441e010340005c0c040103070642c144000252a2f50b612400d80d80c00100300710b100a51080102c5200e01d00029200c0102d444400001c0410155420480506a0010740d506026515040c00503072007503906010701401d401000400c0071441071801080d41140502c180c81010300c0b100001201a04440040341c013801c040b0005001301608102c11f42c0c05803104980d90707400c1120355030000326500c0004000410400f080e170400d5000c0d034006c580300240244d102058601c160340b5004002c2d40c9246188000d0302c200c2c0c0a5000180028000c00c0a40c041d01c2440c2d0301c1c0049a9540134141010760014003903a40141c01008820b4254a50b12800b400d442c0b540551401c9007084240000c00020046c0c10581c480d0349802200c1c140a41c202048403042079150406a0300d0342d1791400c0c03900004a941a01a40100f03403509010042e903800703c024800708110072000c20081009000005407883c2c01d50302d50700c06080782444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 184061555 1250 184060305 184060321
    0x60907050d06020313081303060609020f0409090303110c03070203100203040f02010c0f0501090809040518030423090c0a1103090a1202030a12030203190218010c020a1505130518 78
    0x31540514842104842554586e032000c107540e004100400410034500c4041c410410309010764401801c0010066090201682980c0c2d114400c62103a02070b240ea44540c648201400303034008010300c2602000c8241c1f034482045440e5204d0b8403511040741b03c0c1c052590b0608180016100b9a0f0143d50801201c483d1503280360f0064403900702070b01301030b10450b00322002d00d4005074007405038240e098800d003c400d0b285d014103018801520703000392090703031038064100700c009603a00004241e41c111101d144a070b0301d1440414107024a40401c00c83c0003504038000d00200480994090f00030a94020380c2d0341c40c030041e400d11080003a1640100040540e0011105c1d01c200680700c90000c601c2003003070004054400c06825a41d03441c9a1960380b20324540829004070420004c6000600c8004910828039800c2d487e14015880d03260568408485081c18024661032210540d10b4a44803000a44521116a0702e0b801a001d009007440c2c0250440310110408104040ba442c200429005454040c05200000607100c0c800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 184062805 1250 184061555 184061557
    0x1a0301020f04171c0f1103120712180605060a17030d021b062e0609091812270605190210061d070305011a0d110a11060907050d0602 58
    0x11108105100e00414030800c50b030320703840c079074004c5001c1e480700704980c80440c4002c0c1c0710701c2c0c3c1c181d4065456001842428400b4014403034403a8404100d00d1720074000d42d00018600002c04c6101ca0754800300302c81079024020494194032007401240116569604d465595540c2364400600c0d860152841d00240184902c104064010300003460011100405d480401051207240c00000c44801c28080e40040451040d04200140c0e0030301c1040900d5007407415418000c3c0a0718012a501ca009202503413510f059a0b8040b21b2030468901d80c0e4480601c0251002a0000405000128903c03180d60b64001b903110076400d1424054900700d130955100c03241000c100c01100700344104106412425805101002051000c091240c100902408403070710000c2041200c003980e41d160000c1104040c546841c0040c4480711b5049205881d807202016030b195034004103203948015000c42d0035051a0080c02284404685070040301041c4c00c0200f02044840c15941e8180071541d5400030300c00c85400c103114a42c004040366050f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 184064055 1250 184062805 184062839
    0xb0604030311010902121006080c100c110307150305060117011e0b0316021501060c120212030a02090319032114070203090a0e0c0a08150d061a0301020f04 68
    0xb400000e900390301500442c440112020075a800d40d0803003500103402d03041030f00c14034001c0e00f8035500405210b120980400c807925130b41900745003804411036042c030410035410462045014080d05544001e41d40b01b4040d40341a010040303500c0840c2c142000146a54030030540c000d0b00031246007401207540d2034020744a95000143c2e401c2d00c011410400f001c02c10f4002d4500070350080001d02d81140b1003941c00140241080031215120010410f01e1004200082d840f03034001e0b40c659049695a81100080c0380280d103040c030039085101d1104804010400303004440c0e40a03100402040d01520001c0181c1140c1c07011002000b44024045030b0205d80c0486054030b5007062600241c081c40002882c80b84c0d0400508500004403032100040e4030029002040b03060080c1c03210f00604c0e80c00030b070300b08034208010031001f84cbc050303c6a041c082040c1d4900003992840408040710708a00302901702c1c2c00c0d400060401401503d404030740f1242c000098a0340408604052003100c01007500c41d03413020300f0141040f0f16458400501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 184065305 1250 184064055 184064087
    0xf0e0102010b0d030513120b012709061b05070b010b03090115140406050607030219020406030212160b0f070204021b06010905041203060305060406050907150302070b0a0b06040303 79
    0x125031046450301c8103482c1c070243ca4000e4030741c0d944400d50309810f0303030040c81e0a0f04025101241c00203203000007803002e680a81501c04920525992010b01c608404441841c441101c014a041c503a80c1401e01500d5408518901d403c60408030f40c2081c045001c2c0c07140d204d220b40003401241e89000401c95070028001554010504400101d0b403884070621003500c26080d40c03ca0b01c10f4468400000740c09142c1441064024007064a02e1814803a041d02e000e0340b5601c40500070041c90003240a03410841d903c65100e20f0103160300070b07d5040c0142c12621b00681e01e0056050a4080800604011410219a105a5600b201c94a69a03850003c5a500f400040e4101c1241c070302d0390101303290401205400621003a400780a150310700090620f42414015400b14400c09824180340c030308101800801c0c0003150050780282c02600110f5075880d207601891601040703900c200216030021022190056041e00240f401e00c2c040e0301300300c00580f20084040101c80ca01a2042c4d8480010401040002c0c00b072284c10200e0074035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 184066555 1250 184065305 184065311
    0xc0f0e0c071b050604060201050a06060f0203030a0203190f1a19031103070f08030a021002040b0304080c0f010c030b01270e0c0c06100801180818060c0a03051314010f0e010201 77
    0x26880104d0f0403504903800c5040543d44407020000744070010702c50100180068502039030030701a81b0201a48034400a0710081c003d540000000c0d9803030b040b0704154180d90494030000c0252100040c178210080c0b89854103a22030300b02d0a284400607141401141803d0021390f1a01004507185544180c010f00303111104d5a014051440c00181c40304030300e24050010002340340a90341e186030030600241401110400402e00a105010502403101c2c0304d426039a10542c00450503507a03060194405140503041e0383c40444641c00c08010302c2c40d007541908142003412081c4c9414040003c1c2c0c4520b90607903015000d56000e4464210410031180088259098112100410003868802e000c03030941d0805d42d04486040f00c10b00848001c1020710801d1103a980318041440d000c170540000c60381c80c038105200d8001e00030355200c0c0300d2061561a80c3e030b82c0d0458414070591005ca4603000c5c0705140150590308640200320708242007000000b80f1076000e40440d003090b40141e40d80d650154007040d044c2c41285031383c10141d046640e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 184067805 1250 184066555 184066559
    0xa080606040c14030f0702160e060105070203030c011505120c03030304060504020a12051e06100b0901020106050a030b0406180f0305031005100309140a1509030c020d0c0f0e0c071b 79
    0x3802c18001e45c010740d040c0d0744211181c03500c1b29000c0d00d811541664001060318240c420000e0302c1c020795020340c2007038091030199035031001400001d15501880000c92050b500c4d20744101070740100081000304964003a50310f0510110303101c20303140d1500c0317007020801d4150b0410000640020259841160b00501c000c107040c030465291030b084107064031000022155030384111503050f42c00f11404d51000d00c03024130704000e026605d40540522800308846c071170307010300c504007280c1904180e00030b401c480d01070a0064030f0024410760b01d0800300c1e0041010755040e140e461a0060617940c0d01014240c0b2201e050b04a801c4501c4c4009541d8119060307480104040d24071503100202040a6030b503138440454048082d80c012400600e58100b501642c0c50110814001d54451212100026068104103005801025001840302154103050343d40084a00c0002d5110206128500130040c43c0303500b0f84251012260304402094450403074095111096400000c04e607014001c05001990b1041090400301030700d010030400036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 184069055 1250 184067805 184067837
    0x705041808030c040501030f0b18060406170c150901210209040c03050603010e30040b16050f060708060904050a0623100b03070f0e03120304060b0a080606040c 70
    0x14000b030f2680700d102100020104920760341070045028002400030208910221500000c0815440d513000c2d050050780400040c1240d611070f4400e5005060700b00a5403144107290505644039200c00c0e20340c0348070b40e44a401e4800425404001e40304241810b07150008801000c6149888840a205040e2078164003000451819101d500171401d4507a295280460303941001420107007501c00c0030301c458507254401141e60208804014840300000303000509484010320100310750f03205200d07079042000c81c040005140f4080513414904e11b00d84278000c00c140c0704d1040c199407500e62502400d03603107180001c8004c80401c9541c5000602c3d540c02900c039504a9002d12102d0303a0b054141c6669280700340d4190002500b024100302c1c0e9040699201a0424940e0311480c01e04402c20350501014006004002c3ca01914064050280103921451200241100c594076000200d40800d58000c41c0c044a0031030615505907000e0038400c6580702030300c2842d805003545980b0700c01884020000042000100032481c10195248 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 184070305 1250 184069055 184069057
    0xa0e0d05120a0507060f090b1902040906060804020a0603020406021c1e051c0b090c031b04030b070906022a180f0f13051c17071706040c020705041808 66
    0xb055507140c0c10303151142400c215080f188000ba07a04011801c4c20f03100b10004000c03494040d44179407040c090800142c545140000203024981041c00600c1c0384c5034000c0b804c150002095845240300300d904900c00c81c3c962804405901807885914056030143c0c44134040303482c5058461101311101e1405c800c04440040280c4488600e01c2c201101040000500c803610000380090700740304100f0746030203014648000d030110701c0c032043c010b003541c4603250080049408009404100d544078940c00c411543c4031522803c200d40d80b4842911200d020503100d64000550600204031490942100020708419405203c1a09076240d149801d09501600754500c0c14200700f0100c05d0700c4d01441c102c0d01f000d4460318208000300c0c071044001d08182e9400e0b10400d10003002580008140440401100308108510007021043e6103401c104000d50141c034405004020308143d12030080004042c1c0c8a902419036140c02051104541d140481c1400507008200c040c811360900d03402130080c0103509501c2c502c1c0840151105951 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 184071555 1250 184070305 184070317
    0x20d0f080d050103051903051602040b091e070305090309010c060b0303070c050f01020105100b090103060b070b07140c03072d12090605040f1502010b040204080a0203070b0a0e0d0512 80
    0x49640d880e4011300c1400401c101c020000d40c90510941190221900c015109024140c0002c0003201c4400c030302401c644170707074200d0040140040c1100c00c103810407014040d0204044520080d03400a81000030b541d80f48207000e150b000306030f050051841c04050340700450b1802c04152050351610744230300700c480f010b0b1020001011500e01a10540c000c2c44e0400e03040191314102c3c0b0185034111380c100020b104000d100882480e0486c1d4500c103c03180e4841d4000c1c01a00606040d51040700740c9400424100281b0500b40c0c03403a4031644c101c0e40d405900e030341c0d1607416460724041c208244916900a01084001076000a203514801e00944001c86103148008203d229000c89034208a0f107003c41c41c14100e00b580d402c80341c002c0c017800701400c0603410a810003000550403103039881940702003030041c1040b41c81e0398000c0d403040160000182c41956660744494004d9603445444404070b0091090010000c0c00c00c80309411340b140000d05030760380a2a50006020407044a0000d1003d88550240b031001c0040e4131130b060000c01c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 184072805 1250 184071555 184071577
    0x403110703051608060a1104120f06060308030a050709150f02070b0a02030c1005040323070c0801020414090603060f0405120703090603050903090306191e02040302090c16020d0f08 79
    0xf129051075011424042c0103403c10560a003403504034043c40c2c6500c0103a80581d200034444103015002420101405007003504098105843c01c100803061150040081d84030310f402020900298907101011123951000d8450042103001480d004075559115109410100030360380b0454101ca51030342a4031805900c40c490780c1c0003503400001c490440c10000c1c0b01003d11000100c00030003180c6800d8a02401a80305401149410001882011800a10382d000d80d400c4980180d9000c00003500c48203202e000f544980505110140100c00182e0145065074410b4803400e00035000e42180d4450005aa844400142c01100d032401074a0001d00103018000180c44014080d554114000c0d103010805002c90b800546444082c1c1c00400142d00707a610001103d68001a0210400301000892101c18009002d01c001043c210b4440703403520940d4412030b802800c1a2070080b01d002c10f03140c0354803141494602c01d0107403000c640c140c0c3c10800400f40c50102803010106000d4140c1d14180303070071581c0f860300540c4801e4400b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 184074055 1250 184072805 184072843
    0x203010b071b030b0f2707080606030102180f0609131506050c0a0311071203090e0c090a060c08091c0c1502030d05060a0b0309032101050603040311070305 68
    0x34051100c0504180698103240c1d40b0b070240e240c21500c5014002c00c004080b080014100e00109504504503100c201080e030584070f1801006080d6180c15846540798414a640c0d4070600c4082090ba28061003110280442319040b00c854003a40c00c01d001001385d20001d0194000014841e401403900c0f02d880007001c407030007408000b45805c82000c17075481598458010004000c401c0c800c2c1480e042c8000740c002000fa401d4140040507003440b1042e640741c00e945401510940742e10600d41002c141d04034884000f9186020f80d00d96040d41d42d080c10204030b000b0303040420750011013010100700c528010400d812042d405420402e14140240000c100e8007100340c51001d0700404203031200030900030000241c2002c0c0c07505181c142d25100048a00969a01601e0741c0c080c84203030b5941c0455401e41c1d079914401c2c024180c43c0403641d100e01d840a1100e171250084044103000000102b007910b010340d00740c0801c605a0b280100240c1c21038a407514100c0c3c0d000c0718101405074520411030702201045040010001041a0707103580 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 184075305 1250 184074055 184074067
    0x1005040803010f0806040b130c08070f0905180a0311030f190e011e030c0e03060103050d020f0d080c1b1005010501020c091303051e0313120e030c0603060604090203010b 74
    0x51421403c1a80f007514a50001401c2c0000100710461031904448811905a0302c000d190501c0ca408a416500c012030f10711441d81c1c001642010803c882c0110b84840d00c04206642e0744030b410a00080b003641d90740801e03401203100800064064403004c0d03140340701c101c205d80c1410f01c1110969115403140c0c0c0000d486e0030341c20f449810b2840c2d004240c40b001880c2841c01c01000b030740c4007000c080508842140041815103c02c0c05441107882185402c850080007000c40c3c07025652800c0c5961035001c01d0001074018094160240005040082d06030f260303042c1541c0e06011a9650407041c0a50f0f003004002c0c800c0009030071403c40810008215042924246080c0090654908400a13280c089095009402110260100540140750820039202c81c1c1c0c00d0b04007140e440b002800140c1c8007000c07540c2d410078203603000f1083c0420031500320300240e03200e403003824003002001401d1002c0c5c4506c3e444110300381d450391001c582c60801d428070f8800745030400d501600c001d007480e840d500344e0390581e0000d800800700e0507000305d03007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 184076555 1250 184075305 184075319
    0x1505090909010b090103060c140d0b0901050604081f020408030a091e053604060b09010501030504111011070801021305090609070518041e050f0606070f0203100504080301 75
    0x160304469801d0082118900903400b04501c850140f00140c4001d0b900d05817405200d002d10401321118400288140c3d817007280c0d602180040003140140750207440807600208a42c1001d00403034050300c0805008015203030889500c90b81001d962041070031199001d210000d03002c84100064103103140b4940f20000350034203021103a83e9070014058609000040034208105079168030309034a0520201401c0d890001c1d0249002440d0b04048040044100f01010200824408180c2c85000c000b01d080700c14605590742c5a0045090360300070f17034000e4810200c1c00011400307032401d2030004500c83c90b1070504080002c109028a070510b4140e40c0010030b41d940001c5c1030383c1c03c0200c1c206004090901200c8189050a0900204030300310401051030043c4003000a0408155150000e08419660006c0080c40000e10542c01c1400e8055010a018049410200801ea01001907441d0714821240541424140121521100c0e10920322050513070305800b980d880c4485560180c0034191040d0302a0002650325454201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 184077805 1250 184076555 184076569
    0xa030b070e030606010e040207111504030309050f1c02031515011b0c1e120606080c040903080c090a031401091502070305070b061818101506050a09150509 68
    0x200703480b9801c071000308151a81c00848200e4504e6084c2c60058441c0341c5843c004004440b41117090b035024402810103101d00008034000d02c142c07480780d40c80203540c5641e6800d001040c0f0b241600b0560100768034a4032080b445000b51045501400207049500e01040b02d0403030034141000303540e840303d56000031038004e5181d6048801d19041d540f018107449444003d944580c80303040e09074016100400720090728818100b40b180200c0c0040c1840e61000c0b007810749070f40b5103000240100c3c820305465026a50710700c94145814800c0c0c1104030740644840d5010342e00d0400e120300d1035008031103696000c208040c0200100705100060880f007204a00005112001800d283c0e04148901501440c074500402c040b0001a6021060b5281c4941c0504990400e1312000b001983d844082d0124840c4802d6540801080c8490140ba0380c0e000100360b01560300c0001d40d036240d14150750280311032401c201e04000c410414184550700410801c6090301d00400090b8450b0300000c02140d0440b0001c000440c04503d000f06032810312 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 184079055 1250 184077805 184077827
    0xa0b120c0406050924030a14010906050609090706050a0311040801060611070602030a0c0807020405040501090c050301020c0c271e180a26070f050606030a03020615030c0a030b07 78
    0x907980e400c1407400300c0c40c1c1003a80250b0075000040748004485c10303115031010405000150340c004580751300300255880e542d00074022042d05480c03142c10640840c0303240c00c041002a0007600280b0240110a0034070400ba11280d01401c100e500301941d554460050400d0032000d44003800c0d5140020841c24075050004042c09902038560700150001041042016000000c0300e5000c0214242420b040700a800d11255030701802c01c01035045820700c4104003c010041d030084a0040c8a0b10200c10480d80300c0b000e1500700d00030010b80840c503a000003c07a0046207401100d0843c0c900000425040c600480b40400c02d03140c40c1600e01c1008a0540d1294682c0e106e1a400f030640d2011411246110501d0304510b05650745000c044050402c1203820421100d0400442d06070181c003070311802c0350f540c4201701d1400c1c0d0305a150084050f81c0c0380c020380c0b0110b155842c1c04101c411006030140c2c010016a20303000450b00003414098419a8984143d41c81042d0907100c099403d0000e5000380b5071128107162105e8040d1041c1c20f00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 184080305 1250 184079055 184079059
    0x405060109021c0e19080c06070207050d06050a0b0303360906010804050106170705151812070305010c0c0203060a0915020a05090a15090e0c120a0b120c040605 70
    0x144040003448424014040d09407101c440082241d05090703140340d0509040e48040110304c1013a00345d500500c1001c000400c46032140d07100b02c490981d25454200c3e11010300e03004190780008604c01c51000700d421a0055904042000c90000d84030300800002071459100700c00d09000703042c1010400251410300c031006840560200c6c582c40d8202c001d00002801e294006007018144044a4089401c1c810301b54480f20140681000a01c448100c54000c140c0d120b41911660340308030448007150304404a41c0043d29425103440da9917003d00b140c214100100e120100100c28500d118408000003ca00c1c2402030500c00122601d991220020b940107050800d407004050140b160300b08a450b00c0011040c600b0700600d8a401140142c407020080c408039000d02c626110580d000e080450b000c251051a0048180d10117044d03145d000026903205c2201060100494201190072001e10098021000017407420f13078400d0700075100007001c1c1d0b0313401c0010b500c03c1c07403d203485620b42d4095a11118103041510407207001c0c0000b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 184081555 1250 184080305 184080307
    0xe0601120e030409020309100903081519062d17150108060405130507030804082a041109060d060801050603031e070c080f10052d09030d02040b03040506010902 70
    0x11040d0340607503e01c114440c40c800780b94000009907a076070042c800240301410800c4140802040c0b030400405001d420f44400000c50b001200c42d0006280c0340e52400c0d0144081c09840789286c3c5050025104c2c1d4148a00048481880c451500004d58400036003101c03e09d000c1c3c5841551803801081a456007034001c108148964050f0b01c0e9101d140e8200501591010088901080554540084000103030465800030301a1040d043c4c0801044001c2c00035205030b407038600c11501c1b014441c0c0d05405801a9400c113694888090b00500c00c401d040075005031049520100340185440c02d10b1020407241d03806958160701c00d5a54a01c117001349202805400d4012404074021030401110f600d010340110111014603203141c40000c6c0078010041e1400300715000704031130740035596284444aa1103440300360880031209041d24150001c0d049038588541c68036041904406e803802e46001d0240c0c44042000070f000c1500d0341c1b10038801c1c40421003144c001400a011045605601d0b420305142203460f265041c2c01414800d40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 184082805 1250 184081555 184081571
    0x105070203060604200a120c0504030b0411180a050402120c0109050f1f0f0207050a06090302011107090507050406031404020904080307090902280207060f0302090303040f0e060112 79
    0x9000180b0681000040358000f5582140c3da01c0d200d40800d201e042c2c4203040c4008075284c3c1c83c81c0c3d001030281c0c84520000384140100900d4560450b420f00c180d0100414034141c07503010070b0101d5103c50b224109808080d1011030700c0050418040340300f0204035110342007251240200700840c20407a2510b0701c008060740040c01d0180040b400648031040728000d02d0300619090740d21030f02c2c540d5103e0482460030041310303540801780c141000040130400031074042000742c031510030001454149043c82c0030460f01310703595400c41d0070b065500445502c5c818964203200761141441c00309944540d0300c103090083d1429103031181d13918902000a8145c40c20100700054a1181c90208805a2209843c96601c036070300030f085560720390303c40c40243e918820b0707034220308440c0d48081411030181030001444030b41a030341c11405005020054400b2a07813068903000f0000000c0307400c00300410060003500a0403828200400780c07401c203038a481c061415405181d0140840d1040c40044c00400e5810520000e041d0103184001d003c01c0c1c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 184084055 1250 184082805 184082809
    0x105160f020115060c050102130f03020a08070806010e27060105210703120203041a0d1a030d030c090b0d23090a08030402011b060b0307060c02012312090f010b01050702 74
    0x3110302c0c801c4d03000303003c041c4010b6403c01038203604075030b049090b426000544503220095403400c85260300040340190070f01c00c4d01003074000e00010f110044865002c010302c0e841c1e003404111480e0040142c20360040c0301d403038000403c8038884120b074a0f4184612100419040d07142c00100300383c4a0f030310640c00c0c1c1c085c54402c0704640c40752400b081c548140c1e500701070030301c40203000d81d00c0480c514803850303208990b44c00858044a2604482038004c0450402c0c03148280003603071441c1c2c43c0d5403c0421030407001d0381c103900100305041e50b01c0c002d4004800b04107007800e1440d1826660000e099003540807100090540c0c2d42c0388190511141c0da103c03c0c2f1130702c91409501100b2072501ca4100c503603910300c00f0005080030801000080031a84a1102101c2000740c080031300c003841065141c840c01401070301c0741030b501c41d0050304408640302c2d205050308450755030141d4450f41c0713400384900b0555658041c500c0c4007014031400c1140d40787c05a007035600c8a0044000400a140040d41d860440d421a040c080c1603504111040043c1340242e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 184085305 1250 184084055 184084091
    0x723060a140c070302031201060c0302010606032304210c050f07050112020309070504022205030c010e09040221151006080a1805010608030a170907120f050105160f0201 74
    0x8450028000b03540c40d01c150405030300e035008500c42842c902c44c0403000803450650140025225900c0713a0000c1c00740c43c2d16003006a0a0390f40c070403c080341d0280c42c5044980002d0342c05c4d090320781180c011a011030b1600d1440401100010a044001000c90b0032601020b0030020100703c0c2000c580c141c0d20140c44c169040c500020f01001803034444a0911390048040382e0540028085080103000051007190b90742c014541d01e03949a02c08542240e02000c80f4940007445003004144095612416503c1e41a96400c100801a16000250090340c01460f0303101012a544642503504002d002c0d40d00080141c0122503a980c0e150120082c80d031900101000700030040305801014150f000005690f01142a500e1542c0e11440403203149406040c0d9800c2000c0003440840200003001c0076281c035a900da085290700c00880b20441c500b550012143c2e0312004041119041b83d4620b40840e0b84515401d0300348a4654849909681080d00c0c00e245801030820750808860300100d10001c1c09280d13000a00150038156008950 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 184086555 1250 184085305 184085311
    0x2040c1d0603090a0803071205010f05190605030a150305190507061403040809010c24060f0b180d080c030307080108010b0a06030e0a05060a0c0206071809110723060a14 74
    0x64600200124051138010140c00f4008e000301c2104101540c6e594100c0e00503403c00348030300340c0181c035540d10600c282003800203c0780640e03004e0b4541600e5601c3d450020700051500c003046070425010000301000081c1d090002c0500c8000841d02684c9004035424030300c2c141106075018005001c0207a82c09041c003a001c0c020b4a0f8080d41210480e500ca030107000058aa0704011540105641040b000c0710340f035040c1040d00c550081d130821008001c1140c60740a11760754400d590013040303041e00051020112121841c00c409602d0302d0003500c0007a103650117940e4155540c200d2203020341716800102c1004242d80c1d000c0450b50041039000000d12801c10130b1004221440024000c01c404c0545500081c07050740300800c030180c2440d61000c03c895640c502807203d0001094100b1240005014800c00300301058800d0350740c103407042c0300400542c500303d14000e1060001d111543c3c040078011402d0044001180010108045400201c00710380740300a9800151410000010203454a00e483c02e0305084c0d010140242c00c0d58 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 184087805 1250 184086555 184086563
    0xd051006060e033403050604120e0a080a1515080c03010c09120212010615021e0708070b090319030e040605040204080c04050606070c030c1a0a0f0f03060302040c1d0603090a 76
    0x10110000708813600a01e2000d405c00f914910901d81480100030035602c1c2c0008100180e80d90141c40702c151010012600c0545c81148a030b94051911100030800d10141ca0300d00c0721010b034002416031440d0611034400074184d84414502d41003690f00e030a560900f800780058100452910071080f0707050645424110148003c082d00681c1d065040300f107449001d5015002400840c2c902220f0f2000e098402550b802000781c01200205141012070580c1c08001800000d13106502c0290088134104101ca10300d82d0081c9224a030b06109044043e440d00b40c0c0100048110f90085e96003080c0d981a0740705100c02d88040364003140c000c9104000c204031102c0d0205556140da4003c130b4011802e43c44d800c000458900480074068860031006000008011040c0d003890200d514080482d07160307058202080c0a140911440800031600090580c0e18180c800c48407103a64201d1400c0028039691a90045011690142c0308a404654a218403819207800464140074401040740d80502d146070122901351924900c4400074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 184089055 1250 184087805 184087873
    0x1805060a060e0a05042408030f0f0307020a0f0f031b120f12050f0702061f03020f0112060f060e1219080c0102130306050a090c03110d051006060e03 65
    0x31150382c3c5034048030006043c0204140900c2c032083d100b00301e05402e02140040c10b100e007190005035603170300801941c0c001c00c10111043d05004c407402c046d074010303400205003100714041c100e078101c00113140c203841c1041d8a000340401c0d01203103400d16001e003060706e076600203091460281e42814006048170381110081d0b0f13003524204001c5054020155014401e81800a40c40341c10070041164140f49501010b01c140071903801c480d1181ca8400c9886041a0301c2d81100389000d42c2c200e4140054181502000740061040c903000c3c96500c1c0c0c40802c041200c50b03d800c60310b0044c080785010851a544501505da4052046411614459401103069030301d1340a0350324801c0f00301c400300200302404095815580b42040c444000e554a0b1440d494014040c1400e00044550901d0107011402c00e072018440c80c0c8406d5031005000e03c07818116142c1c0c05881d1484480954441c081008a000181301880365a5242403101400b242c442c0c20503801034800411b1610705800395100c2640d003c007000c1d509040300c1c14080120340300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 184090305 1250 184089055 184089077
    0xe090d120e06090102090108070c031b030504080a03022109090f100302060408070501030609020c0d0806132306010507121407081c140108030a03110c0a0b011805060a06 74
    0x2020140501c0d02030000c00b030090000b040320091040d00188030082090b038480840303568540003034a1204034060040e000400205d110b0741c00201c5000001e00e0103009081c01030916079103403112443c020218400700c0045e008007400314220740e24401d4140d0404d01a810341402e0540704400714440400003444002102212404141c0b0408550152000f441d00a8842e0303945585402600340e8548003441403e0001c0d143c008009540055071007524074035400c000150031118201c100c22150603801400d1154040355081100b000c070081441020100a0070640020050506c601c02c0c00c2c0c615801001d40b81800002c2100c1d10003e1b01004445140d468a030411081038100b003a0380c40028096680d004140460005074605400501c0c3e2800009030000f070b5080c0044210201040322007030080c400c40030a90300500422002c0c034083e42001e900129240302031420080c94a100500d03180d6110301c00d4415070054001800407414140d602d9041d5038a0315003c0c021170604600ac00c442042502c9031b402002440440c2d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 184091555 1250 184090305 184090337
    0x30804141501030c06140702091e1017060f0f0c0403060606050c0c030a020102030405041806021603020d02061501050a200304080c09010b09090603070b030f0a060e090d 74
    0x4218040e44036104841d01071400ca01a61091102070100b52543d1506802c0021104c0c03155407101501c800d00315009042038000d5090054040001e041c2c1404a420038a040400c1c403010608a84104d211404e198409450000c00c02c044903080000c4481540090041003060042e06407601e4003e42d00c0000d8400903651140c41414501a40cac1000740001e0600300d000801962140160a8049080041e1400c0e4941e150805582d0800c04a000303000d030300144020406481c0c540c0c000600c0c800704580300710391600380c1d51701c01c0c0883c0d0040c01c1030100100650111010305904110000ca9a1040c0c0004c0140d800c0402684008010940c401c0381084400a4010502d0380301d43e01c12602980110b03500c0104110f910115600e940190040c2c00e40d500c2007604026241c0341c40301410b170488401a0300c171132405e5079035001d00000c410014007e54162207020790024003103d4200c02540f04002900344c07440b450404001d29426151540d1108c2002e1140c0800c0c0095890003042c2031001909500300b075010886d04003c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 184092805 1250 184091555 184091573
    0x70f0507081f060803070c1403010f060b0703080106170415091401061a0f0d050a06050306041b05040501060e04050621030904050f01060f26040f15020f07030804 71
    0x3016000340030703000010b039040d061042c816000c02e04810040c400942c86245841c0c2c1d0340680440648540b500074408c00280d100140f0401d80e4590140021030002010040801940c485074014520101c0001e008002c0c2f5034440c074080d025180c00c1c40d1151150b405034841200103c806880608181e060814801441c001c0d540310010141d4001814102c8000e104019030007450213210314004172076120600c1c1410141c0b141104c40b4104a0a05582403001900c0c40b000140402851005490780e01c400224169074104207140c0f18510a40420812034806985801c1c0c44550350b10450107582004010b004168122284511102d000d403400038440d0b03220400107890400700148a01d4071b030a400c034100d40b4804040000e000c07510003601e0620640c0c8600f43c4040d4140c030244101000100c00180700410310b0310503641031441124122199800003035039400c5980389902a5012605140d01c0d000503420801d655410f10b000c52814101182030030544110410980300703040b8028108460f040016081110480e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 184094055 1250 184092805 184092809
    0xf07030e10020a05160503032a16050c180a0c020a0c030816200102010b190b0c15010b0409150524040e04050303181f020a12050a06060f05030c070f0507 67
    0x103117a10100e01604041792264429074244519025411525103000c4401d40e40c40440600400c50f1440e001300380000c0b00200710f4100c0c0440b1180a2003542e02015a6000307132042d02c01c0640c154152140c10099480340441c1c162280d40b5080d90000c925460200d40044075540c1100c0d00310a0041d40d40146215180c140c0c2402400108460110300844d000241c01480d2140303141c10a0b00200709010501e01080118078032060110887d14140400f03008208940c4081e200b40d2183c603003107501c00c00c3d8034214001d602c0c00c00d80040020001c0032604100180f594002c41e0070070101c00c14980703425414040864a0a01d00b034002c2c1c80a040844520818080f42074120790081072000ca01111605103890000c1e226841900c04585042d0201c40311001c190b00441c01403d24008082d07200b003021075203210760010750441c01c0401d040c040581c0701c44100001038054144508008440001e0490501201500029a01c00e01608200d4141308020342c1e5100801101c6049030440442c0d0035690251034a14036140640d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 184095305 1250 184094055 184094077
    0x604210507140606041404080a0e0d060e2103040c0b0c07050d0b040317011202090c2a07271805030a05040302131407080603190305030f07030e10020a05 67
    0x20b4042e401e90108089580d5004400c219020f00080c402c02e101c1e401003400549001d08110820418903004034090001120942c1000d0488c0350380031042d03101c02084a1400c04102c50039004001e000c0e81c02d107003014190b1401ca50101030036042d403c0c5034a038181010220302402241d40e000150495403890304100b0280101001826102c0804c96032411400c003960a84003100450002184d8440c245c80045615068840c4151a0868198980c0800414100261150408800030000e8105d0702e19a0600305a8003501301142015610904c0c0b00b55140074500d500c8020005481d8151192180000300c40c00c0207410380d10408100182c1040740ca8084903035003c001007061100003002d03a50260800042d0040f24000c5910320b081d0060084404295290101c882944101d00000120600c0c020f044407034002e140a801c6030b04100d080d407130112102c4407200c000d501088000c410004030454407614150b02c0034942c6814406400c2d03101d02140e0340d03400c541c0c0c48682203401080c580b207064800c0303050762100584 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 184096555 1250 184095305 184095323
    0x3180118061106070203070305030a0b180c2a07030f0503040819050d02030418180c080a11120303240306100510140904090311060f0601020d020604210507 68
    0x181e1a0702510309800a40124801e001d0100010244c03400072003a224966051f4585618660f11842d80c44010920f21800d40d84c480c2000d024050704c41d40308010f9500c0351103002406a40c40c1480804428244060124809044c0000b40d192031000c42c042501422240e102c406c9800207506071501c1800e600039900024414401d00e05425003a40c440118000d81500481c01d458000c1601041240c82e840303140074000c04940115000d0110513141e60102581418401003009079800075502c88103506803507488608998081034104050107078000007c001084216030410124040340c0b0000c0d140d0000070999050000505112480f4401010034120b41c018020159040f51070103145405091506004842c00707403c682c0c51142d0414020161082a1400c0361035003070400402c9001c20016125495007141004644803800d8620002000a28051403040101e80140e1402c1c000091a021518003035078115448141840041010b40400c02040304554810001414281c0b4042d142441041001861144 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 184097805 1250 184096555 184096559
    0x60f060303091201021603080f1e0105120312010306021e07023109030512090327041107060506042022051801030b01121a0615040305010f0501050d0503180118 70
    0x940f10700494480c0c1c80f00c561109064480341502c0e01c1030322b070b0202c20100c00c126800041c00140b4000c030503103507083c080c02d04603440d040e416a01c9500240c400e17841260103907004140031040303c4c2140c1c07010702805c8041100c5414110140c00181e5401c038075410f00180e080f070700501c0d854000366035240120b071041241020f00c07030703c0c8207490b004200e60301c1001c0b054269440000802e506503404030480381c1608050210301203503481d01d208100083e2090489552044c0c3c1c0d1526016007043c86006800514002e03100090940350450510058401a41c0300c80758194940c9200d8505000c0754003a2154540d4042c04c50408000c02030340030307030540740c03903000b0640c07240f407601c407000d1540e4100f10340c281624491100161140d80e0b80002c3c4050340a1046d004041280700c506040e42c074031280d035100d61302c44001045100d513614a9116040203601940084d2400c1c1d46500c62201800801d01030907006010590350b4948412043e1502034481c000c481068905203040300034005140e11075002180404800100c0c000096 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 184099055 1250 184097805 184097807
    0x9120303061517060d050d0f02030d0606080402030c0609010801060503060f0d08030703060608130b19061203020d02070f0e0a060504020a2c21070f0e060102060f060303091201021603 80
    0x1000441030892074183e035000081c058101035017042031141e0700400802061998250540d14883c00c0b40030301e402c52009001c25030124800d4010100205030a1316500c550b41018011701d4140f454203043e0074003502d010050805666030060040703044801c01c0c50515100c0e00c1e1722000036058100300c410540c3c011b08a041c07200034461020000c5001d54a1520100300d0150b40307400655030300b1404c850000400945c0003195000c280850245c0754403200e102d01d02c0b40c800d024010100c00315012a002403001d034400e41100d500301501081040800007142c00105981441c2548105110301603006a0451140c0700c2d0200342484080d030481006003000500070341d00d895050000a041d0405c1c0d0b0161080060900048008400c060101c201d030f064000d4001020218024007140c405503243c10141d00b1803041850011340740d40304910301c50140c205149441020309200c0d0009181060107801c40b0315103104182481010741c0c0001c1110269113042d601068664a02a8140d00900800e50042c01d42c04c61401980201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 184100305 1250 184099055 184099067
    0x60203010e0a0605090a09020a080d0c0c08030909010303031116081903060506090105070c030c030302010c0806091006030e031c2a05070f0f120f0e01050703091203030615 75
    0x622916429040c00d50b035041401010ba41c6280700390b40e000500768020903414a81a000852058005415040141e0782c03410042e181030010503c041c001540c032440c135010808102040801000140300450030554084001429290184801014035035a03c1541c0c0d400c0055a05890040110b209851242c03012410300f0000303503010100d0301602c410641040c400c068008d11804043e1500600154184868540191515809680182c5079103198103030020002d039184142c41c0145100e41c0c00803030300d010340c2e83e40609800790180034544075241d04010071092070401d07440c0c40100c44240c940442c5481844030b4450651107003141a0a41c4903c0e8404107040840c240c1045680f94801c0c035030360072180034141110301c0b1407820320850000204100b188a01190300c030740c0550300f0640618004c24010040e070360f0310101030700c1010540f8046040c00c0703c80d80f110303070b00700048040c4081c081c00d2a0746044607075600242102540d009012001c40c20f0146042498401d610480281000400004850f66603100107880 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 184101555 1250 184100305 184100309
    0x9010c0b0a0510080a260903061e1302010c120e0d14060a050f130c0b0a020a02040c02030f0d050c0c0a050f0706030b2d1e0a050603010312080405070e010306020301 72
    0x20710300074250008107058000340000e00c0d1a0040313102d0b0000b144407443d080d803c1018000000b0440b00c00d2120048a07582440003e0042c0c10060103e20040012b41c604110500d0081a0f106031400e074030260340150745c20076041026a13500424880b404003802600f0360704c0d521401403a6800c030300038880c130208020610f05928852204180ac8944ca0f6030b60240714401c1d9541101d2140f9072000840c08070740d88020500091503a02e22078145d00d94000e8543c0c40845e1a0342142003e000141e100889607410340c03c0c1885640780c0f004441c80514500f861143d14800a885403507040301c100303603450000649500c4410207032188c1074001c070143c175001d4038242081c541d691001c80401c1c41c140070b1205c1c0000c6aa01900c40d900c05188094800c071686c04019203440541e07a0003500c0e89110641c80034030b491580e40c031110840303448441d001c07103010520506410b000d0891400e40107a401202c003040144040340d00940fa40701f0181951600460701d40d9145001828060035a0144150b03500304000030041040760707005141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 184102805 1250 184101555 184101571
    0x80d09170105072007081f050907080c010f020114070c1407050d0204020702040f1409070603020f04030611210105010e0609010c150216080d1b080c09010c0b0a05 71
    0x3440031652a0a422180251900c002080c000ba180007055041c00c004c1800d5004500b00751202d0f2a85c1d05905801c04080301030950503100002400940c0105600c14290040e8450f00241892070410803025070b00da01940001c1e0500c07000c0b08008881601c03d4110401180032850302d071050781030085001e4550a00000100d400301441d05c07000002000c0051388c603040390030082000c241e1202c0b50b02404000d501c00041641c103c0d0300c2c0d008019800050340141c51080c81c2c040240c221528220000c242004042d801c4041018010403010503115403140a45003503030f40080d0006070920706140c00e16084c0c45840100c2003a8400000d14070355000c03201140d24100c540a0700d40e42084034200c000c102c03007441054000c6010512003911350380481c0c40b100e0715102d80c030502d5074010b1400e1500105014048000c00089a601c100000c065001111501803c012200d07814584062212a200301070010b01005054000e441c0d80460a4182ca070322906000c0e29541e00000300001d41c0c00c01c0c1c03007040050178013118002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 184104055 1250 184102805 184102829
    0x3080f070302060708040b0403210e0d0e0307050609041a130207060507080f0403030c0905040e030309010f0504050307080f070807060b0901060801060215040c0312020601141509010315080d09 84
    0x542550003007410900c1147d0044031903050303540300d41d02911455688400c448401007940b03411140011303144203101003d564a00204894078210344010408803200040074001c0d00000010022611081c040e01c0100d4004c45003c00c401019a107101c60200003600550307405040b01d0000110f400300c550040c00628064a0f09100d0365999010a0328200d01c10395402c02c0c820f15600026010038420752010846034400d00e49801581d55a000040503a2030181c00900c0d039810000500039500824829066000b814483c24006442c2548a560b128042c2c6000509040000654580003c00000032100d102c0e80c040802134942804d41040e038000d02d1202c1c0054001d90000b0004a0468000c881940c12178203540c0c0180815500084210090f0070090003c489171003c0d0a4080000307042c1903810b0b840d0340c0341c940c0200b149616214080036201e80e640b1f002c9005d046d0001060710242c1c07000301280d803200300070300b0082502c0041c450000d25000c1941c1c0b001c5100c0c0a80c0001c144e8480c0d20400c4481261501c0587c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 184105305 1250 184104055 184104061
    0x120108010f090201050d2309011401050f010f0c0c050a0b04030515040b0703090201020c03010905030c070f06020606060306011b0b1905060d120c1a04020a17100203090703080f07030206 81
    0x2120489840c2e2001a01051041c0000d0a030b40401d07402041c0c03840241c500070040100030074251002c00c04280e6407001940d44078640800003a6103481154014201200c120381d500307035400c00107440030200003207080800100c00c84490034050f42090300c0000b8130f4043d0a682c0c080340d540300d10390529009400112018043e441032115032072000f0b01050b01454028000503195180c8020603001005184030490560091013080d203a1a9000e00c18004403600804c007170741d0f03144815007207181007101d2a0002c150a034000601880344540c0080c0c0c4683c0000c00b555083d83d40c1c0c8403000180e40d941459141e01100c4800c0d4004e03d41088410300708580550096460500110807000d8114140c40d0101c0f4519006940541c8040105807404002c45a0031041d0820300030241c1c8030b8036440d00c4910b03850086080d00d04070708240f20450034040c40500040c4401c24042484860105065840c2e40900314500c80d4580c012010031001141448044c009560020b0001c3c0c2c1c4008028184003241c1004006070090301490b000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 184106555 1250 184105305 184105331
    0x30c0606050f0a0506210a06030c150215060a0902070c0806060a05090c22060c05060610050d0b010504050307030b1806100b03090703020d0305030a0e07122612010801 73
    0x1164451002c01003035551803d0070407050000e01d410803903014030051020700d00340280c1a4030140e05401064903580c00305e03459045045c0114000e050b94004080a21803443c0360b501c542d80815076908400300b01c56001001d884460018a04441c141c00c0140914030024240041041402e040b8048480300c41c16a00316944a008101400c0da1034032134140c200b0002000180d29600a00c020020007419000da0013000c2d80114001c4c08003810380c2c00010105204c00e05038070501c581081003580c000000c0b6800c2010908030030f4000c160340100070300b1100035a00c95513140d080b40c1c0500161405004082c04031800341d542d900300700719401000c0e03070708840c4411f01000607513007500c000c51914400c004042e08400c2c0c2d5841c15406880075480102101c0c560b0081c000b0201c0140e40300750221004e20302075075513140c4034241f000034142191a001010141c03644a11010410a0504001e40701015084215030003120720b500da80003a08111080c041e0b45010300000e9011018039095800790681d91150000c020405842c2c0c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 184107805 1250 184106555 184106569
    0xa02030703110f09090c070803130c091e150503030d0b09060307060c0f060b04020a120f05040b180a060e0a05100203091002030a0e1f0f150911040b0403030c060605 72
    0x500e01c1c0a40300f040000c1c0510703003061140c1c80d820654180070f942c60303e0050784070003032281c01c180c0d8141c203032081024205040c40403c04120b0090702c01c0308803c1100f07034078540040e03260056a07250500c070702d80c0b280c90503024000e0140d50000100b0300603043d07075a00d070b1049101000504c1d20142691282d458070000c1742950070005010310554200b40c6442e042c103022620380391490120100d00703e0381151904080010703625180003802e003101d01501c911a00c034142c0300250b4141d40100141c0607030280391000f00800300e0500d86115400c905185c00d002141107030142071034104030304000064102401c20b030102e51015000607400c6181c0e0b0007203064031084020030100900768482540c512001c4e62190f4554202c16411703030300840d0000f242680001d614543d0800440c101128610014840707524112245100521802251249021210100030306002d501070030f2078403003031801150b16466842c1d0215000030750707000c2100c0141c07030703409000760701e0f50f699150091003484140021038a071401d1010014807824410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 184109055 1250 184107805 184107817
    0x705030f0a0510111306020114074d0c240307120b090406093e0102010b1e1005040e1f0909080c060108060601050313030c02090a0203070311 62
    0x10700980107a02c1c5404140004c2c0c94007184080c0c41540c1000800e079840305660101008100c0c903000841d4800068076503020703550005081400384007030304103800f070450181052540c0d1507400d80b445d0000c0809681642480b183e410740c0301005440c07032407005d68072050b001910f0040003504882242c2000042e080e10114000240c5800c8025402032010621841c050004c0745090b800c00d590015451040c0f40000340d1200041d1020350b1150340c2c400c03001d03003806134200564820540c1c608071000d00420344030061000e58010500803400c40300548284003c0ea100f900201072a21004001158203618a01171040030700360310703009038403c1310361a00b98035280d80110b007614102d61016203e00001d588041041e120010038406da00501c141100010400e84810701c201010b10b4062402c0d075445070040300d2560710b004070680290429030b0001e0200b000c03980c0e00c50201e81d84107810f4441c06000320290719058980e1002a48c00079030040b588020801c07080f04075070107184220034503503091010581890005003588038003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 184110305 1250 184109055 184109063
    0x4081b0102010c320d0b150c030405010818010204230306010f030b1009020d02040501090e0f04021e09040b07230f0c0c0301060602010606090905070519110a050705030f0a 75
    0xc050040308001070058400480c2c0100056840d44042c01c0a0020703540e417081c01014a00d076910a40004c00b800c010b8013500c000754405029601d403011075041070741e80e40100d01c103484c10013030700800107013170340ba08020281c1300c55806000a6444a84480d4984801413409282e072081e01d400400160301e5280000358641210404400981ca26040d500c0300010301d0030003011f2480052224a0005078806248001c1450165800300103840301c2c2444001460794590341c0c4010001820441800248a00e4100c00c94000743c0c101c80121106c0c040f84482c00308541c101071f2a540c014040c004000078440c0f009003580c8500416525814000c60b0001c4110a03a03880b110a841c25401c103000c1107141c4203070b100041200101c6027080f104482001c0c0700003406d5540c20317042200140d4490404010030350700b002c034400143c0f110381411b02c9686020035008007907004e004110301340c40d07200e0621510102c0c010034000050740114029507120841c60709000760354124510440b070081c42841e07006001464081a050f907402e0b40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 184111555 1250 184110305 184110317
    0xa14181e091308070506010609050a0501020a0b0606070507150e010e06030702120d02070c03110a080601230105360d03080402120127030216030203150702070b04081b0102010c 77
    0x2d0914100c40c01000410700311000901000030b03001080d0f0420400303000340910354502c0049400c0c0010b0040b10241540500e05540c4260315640000c2c0034150001c0d84140241c0f40325072030b0401403c00c00d24101071544000c40d03070141700900d11b05c082da211030701034081d0001381c0701c0d040380c528401e09110f02844107d41900058002000100c0000107800042090010108016042204a444103904521180d004440400c5821071300281801c0c031401030340003016850050b050725807400d00d507051a01c50580c1c504c100440c1618921145a000b0825070781201e04542001d4240503902000151026040300d50622102c0c0c81d09540a043c50166110b903001c0b13038036a0b11010340307440303035820302000c0c00c541d16480c074280d52075146166002a4441c03c4242e810302c51500c04042008034100031b400c1c9103000c078045405954400c03003403015880028a4094941403000302c003010342c2da1484c0803030500070250403610782000c0c00074000410070b0000070100c4117130322141d04407a80c0001e01c00040e822900240013000211b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 184112805 1250 184111555 184111561
    0x80102030a060b070816110a0f0801050c071e0515130204150609050f03030417030a0f1d0603042303120a091a0408090312030a0c0f05040b0a14181e09 66
    0x1c801d8445c140d034034850540301c44040c0c3c41350000703141e00b10303032782c00003801415510001c006201c024010103802502d0178445a1401764140c0750418044e0344800360100000e00c2129040400400708001440c0312140442107001e0b0a0018112000c51071070701c8260300ca175003080e214a807030644140c0d82000f140d034240c48200c0001c0c1b4000a1000c1d094038940e40c0c540c140028407000032a444443d03491400c81c100100a15512400d6580140001d281c441010040000003c01521100d2411803034210701c2001302c47c45038482e0740310304c0d04014141d0303101200d0440286604511000103400000b900d94101080c03461111a03903141c0350f030411582c09000203401103950046201c0320b401131151064200d406030602078a4030389903001282c904158a000502c10102c004100010443d40c2d1081c003129003050b181039440d010003003000a1850046014010900d03a0000e0b0f10510303580644030000c0f078030107440c40081e22034807006d80f0b000c10250078200440c01442c3c0783c102e240f80701500e041410403c2070010000243c81e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 184114055 1250 184112805 184112827
    0x6090a05091015030f030203040e31080c0a030f031103090a0204090c0906030b040b07030e150603070f0305060f010b031312050f0c0c03010f0b091302010513080102030a060b0708 78
    0x41a403494944219039014004800301e0101c17540300c81424041d8004503a198500b90302c81404107002011b5802c0e90000103000d40c0c0685005010310409820040300c020814050f003080722091049100080c014412407415804064201d2600140400a5202000407941c2104076072101d01c412201e04e034081d00134006500052420794071075580c1d03030701464886a8540d192111401120345a800940f02c5a00b18020001040201009107078880001d20b01440328040a00383c903607403035100003c5403440707400000004d03080b03881c10007000c0001c006029030244132503544c0c2050380d180c44081c0c0c1d043d4090100400045800f11148040342e00495039031900190350b54068540c0b0600007402d149680801000f0412541d40c00c040d000503000c12041c04c0b02401600c40420105400c640e580c0381c012541c0317400d1550f03d210300d545800880341d00c01c410702040241d171001d5100480b0030384640000c127040322540d844045a48481507020b107119a510b08030811000c0d0b183c005000d030a0180e0fa000403c40c1c80100072030010702c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 184115305 1250 184114055 184114061
    0xb03120304061407051305010c030206151c0807120c0305040611010f05190b15090f0d0b04080a031104030807060e1e010207060b09090d0c030e0904030806090a050910 73
    0x30500514000866000f0071100d07071180f00707007965850005940420b0040140300314400d144000d00303090803e181c0340c01ca107540103908c812000b0300c20310b69405550702c911041d841d02c42c0103540c1c103080c840b89128141c1d41440d0251541d00300980c10303600911502d98a01030f82c0c2c0076141010009416890b8141058035050089030031849c00d4600304619500c071000194604c0e40b81c01078900a503e0b40c9421801d0380389103103005042707a01c1580c50754440c46410001c22010b040c040220b8a0720307103050741c2e13030181d070540a000320340100b25450700201701030074003003c0200303021013070001e414400710b655402c0c00450990034011b6110b002d40d0002805000c0308200040001310a0740c8040d0701c001004060341c0c0d1710003200071101c0020000c01d6114643d6500010750004104481c850180c0702074044400c0901c0e070400540303042e078030000e010b2000d00f03010564604409060050f4469401208001c2c4904458945171600074034002046d100c00e4014484040403d52104072401240d10030183e4200800c210f080905001002d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 184116555 1250 184115305 184115311
    0x1109060307020f0712051005071d060705070e09060c0406051b010914010614061303030e03030706050a0902120607020604030f0918060806060d080405060304060609020a09080f010b031203 82
    0x354450b00203040741804042c40914000c00c00c06a81014441041c2406400c00c00545070b507e0149107400104500b07990003d100300d581c1c0d40044036490384038014201141c004e00c40c4240190580c451a1000141088442c1c220b0307128580703500990b00c0304d0320b45801d018594066405082c005c9581401540d131410480c10490f00c00003404c6002082d03200c1282c076182c0d1400385a80b00d000099450b544144a5040405c82e0f00c071000d1400c4c2e401c83d24044001c514031810b034145000081c1008000c40d00b150043d60108191041240c220f0000c01c801d0900d12080d41c028000c01c1d00c100e000d904c40741d0324000e01e004c0120701c03d48a403111350040c00103991540d904894583c0700c00d01e21414000002c0c00810010604c40b03c1a0100d0302040001502d07504140900d485c1940041416100d60f040048010000da450015a4101e81c41034442d503480781c90354506580903011980010482900c04510b12490542c0040e1150031140001c0030740744c106001c11300e0103080c0d03044154540c2d0140e10607401c2ca00171100c0400103640c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 184117805 1250 184116555 184116557
    0xb030112080f0d051005030c09060d1b120312020a1209031b060e0111090d060c030f09030309030906050c0c0d15050906070f0f0801050f0301090203060c07060b03011109060307 77
    0x40b400c07220348070106007a044500005641503594042001c640007089a100240000f28000d1044441d68400140e500348024101e41c018030743c0d031040204100c8442c840b1401069203207420800962540f2204800e0002002c06900003a005007144070854a0341c821a0310310300090b03035486030303138000289908080c00c400903044040028a2000300480701c55075040600d19807189030081030b41189140003500b511031201c00100d1a100820000000f41e4410900147d11940800b0208512061110a6004286441600400300d0400c0244810142d150b44504400c610a0f01c541c0c01054032038074116814046e14400d44c0190f070040881171580d152689040b400b0a200c2e4458001c0440d8400b503540c2503527402e0b01c2e040980c1e403100d0f0a001c041504000051400b03000d905e000c0400b10400c00008081000610845009105c556102c04c1076032001c1d080f2104880d005002ca46e210b0901103522810740c1d0040764180c2d5401d240c40c02c145c006281c180112980c440c103c8820078181249601004110390001d00100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 184119055 1250 184117805 184117807
    0x20105070f02060301092a1e0318121b030e0402070c03060906020703110c01021c180807170106080d0e0a08010f05390c0304080f0f0d02070b03011208 66
    0x1001039070b52000940c0030f0110030070007082c0447d8155041c1c5d54181003510f411007890b5202484180d66501c650b141ca0205650030700d0924400f1207640c1a0014070f01c07100d0111104941060b4541400043c2100703001070069550750f9011075a1843c6031024400c001c900080014215598440e0f403031038250007521400d40140180d4920541d07a545902c01c1703540c607000031900c02d41c0102e44901419003009524101c80c06100161807000c5061000035290b5043d160302066510700300180a2510740714400b180101050000b000b140d9030b8940c040e0a030b0f150540c5c8500c4941c401d04040c09643c02c0c0f018000c02c030855001c06d000307065200d0780d800180c1f01001c4101030540c201c1100000014503080034000c110700402c00c000b002604d030030700442070301052030001c0f02d151200410401c1b6458602021048060b100300d00c081340c4ea1a5440054818190300c0340303074800401c1c0c0c0b16145455080e16808202e050040700f07040201c980d07284904900780d8a88107242304144950b14140010022000031030304502205100c0c810746 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 184120305 1250 184119055 184119083
    0x1106040c180e0703060c02060105030303040b010b03040809040e0f01110708040e062407170301050306070309050340080303070e03150c070b06041e020f1b060906010b1602010507 78
    0x142d480c0100a5000791080c80d00c030090341507a507805000c0540503220130b401561130f40c500f070b4880e18a030354010b05c50034801000010001d03003485521026201d528070300501c03e002054104200513541d8500c3c0f84a07124552070030312009080001d0f1801c0321a510340c441c070082d0030b161402d4560045404001d00700e941000c00c5100082c182c41130304807022080903903803420070780350100c90924090003400629842c0e1a601d0800040c00656400554254840c0f40c9180218040b003092801c42e00b1070040e00300b5030b24590030006501d07a1046a1040c1000700140d81703001d04d45030700840d880c21810224984641501d641040010a05172072044922140200c4068200c40700e0030081440200a40400c50741c5440b01c1c2008030381002000081001c4640090003118180403400310307101840a0414882c901e0b044440d40020302442d6242d10f181501c2e2000c0b0141d10700014448050540c84c1c4032502101d040146004403000414424400e806a0700c2d07a003040041e004206003542d0041d00c182d4000b01041e20f1035600d809071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 184121555 1250 184120305 184120331
    0x810090c0302060f0a030b040902131e0f020414030a0b180c09070509030f0f070b07030c081908070807020c0d150f0b1e030c061b0a050606011106040c18 67
    0x13088850b100d580c1c056540c991455008045030024418a8410f50501840c1405603942030443c000030810180c000481ca00c40d85030302410200714411901c207841c2410340d40c0e15240101d502a2003116510480b0881c1400c00703504140d203c54207503000800c080c4491000c500041d0f4810640585007080340121032110b102d540c0050042c0303404a90443c005000016010b03031505042c00084400c00c1c0360001028001136003492503032030744460702034480c8400b0080307121020316114a0103803080d660040000c40e945c1880c11412075070b02e000940814049113000004ca01c0c01d52069210360320602040d40034225440c5110100161000d80c044145e862544d00c02501d0006009032003544101d0b1152100000d03001c800c81d06103c100b880c491203107000503084d0158610a40c4012481c018900d1086036450707520030403001d074650405400504121a48130307003030340201006800a040b034001d900c26203d41c6810351442440542d19241281c0050151440200405c56085030303e5809401000007a40401c02011440c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 184122805 1250 184121555 184121557
    0x110d0f03150b0c300903030d050a06031e051b03030d09060e060f010b0a08070e040e0a150c1209031e050301050a1224062309070305220804050402070809040b0301060810090c030206 79
    0x50ac1c210040c4d030354181001041490f4140030066840f0001c50608401c07941c56898642c0e400c00009401e0048141150225a405000300d420b8245841c0703040081c04041d0408034010038a08031803004512400300171450315495601114100d0302c81030310081c82d05101c40411101100090311950034071001d14803800465440740a01c101c20507503003000340044116810b203060350440304095040762030300c0c2007540c0341440c0c0c0c03116280140840d40000405d103622107140c1200e071107410320400044187d0703080190b031420764058021030484000b02d4420310705545900362003500039111a0000c040350b509082c2c100210039040020800ca074a8031000081d41503036403a00b1005907038282245503409510a005080c3c41c90000d0403280c0003006850104140d00d401c04100d80c49108000f0001d10440584035070703a0800400c04111030240034090019911403415140c541495000a0690383c03180f42000c02e201c8142c141482044210f81d44403005120100c4c18060b00c500801e0030b00415a40d4002a00e00800980ca0350341c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 184124055 1250 184122805 184122811
    0x30219030b1306080a050105010608060a0501030504170703080f0c0a050715092021190c1d010303030b0103090201050a050c010603021206070f110d0f03150b0c300903030d05 76
    0x980402c0da2649429421201c8c1600714200b8000c1c01e0003804240d84800403640d050320800e08002849456504180c220400c80b0a6421a22000010500105940100a580956040101c00040da1551040c4030720324000c03074441c6000200e040c41280041800940348a02e012429040018496042c0d280e44515003c5000744659402031000600303540d080c0400d010a00008826280c0044110f540382c1d01d40b81c12489001507d40f86081c0311003000c4c04007080c1e4940080000c044020098044a0714030b2400c2e100911041d00440d2030419a40c01c254003d0140c2c0140e554140e403201e103080e41c030690a0b109500083c003015459075a035100440145c8072040d402c181098060018422031a0800c0300410344080c40c0000001c01c505080030580b510000140b0258140d42800e250110b450a014120024141c90702c0c44a04070540c000300040d4102004c00406080580e03106442080ca03911410000800d0712080894100b0015042043d40c100031601512070420001c0a03a80381400c000d26070230a440c0b041d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 184125305 1250 184124055 184124069
    0x40b1305011b1706060706020a11010c03090311031305130b060f030402040e070e010b09180415050109151e0807060e130b0f1011030d020316030219030b1306 69
    0x41e8101400035a001028828100030f1070301959010325054010501901910341c2c000c00c8642c000c600e070000540501c84051803d012040200510620078000402418004600b60042002412080800304000c02254041030f4008800c40080349440c2c00d01450081a03504003280d1035849070620101c0d03407504001c2055010800103261030342028010801180c2c1880c42c0b011660740809401c2119141624401e411141c0d80d808260300c4200f544041032600e100c4a40020081c0360038801c110070401a00ca80354050f0711b505400b0031041c0e81b180200c204541c14030001400c8807040d01002c00906c42d8031842c0d07041d14104504880a090340da600d60780d262030100d42140c40402d002682c0490503042800c0e150040840700358041c0045c1d0070000109410341100300c001805402c01e5601050507070b010711001c04080038518100d0359602d2000301c0b0440250021340e41c1a500741c6003029564000c42c800c1c020780b01555030341c0e2088880180303001800c0e00241114105180c10107084418070006d9611403050750014410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 184126555 1250 184125305 184125341
    0x16020f0a0b0916120602090d3503010f0b030414120301060210090309171c020a030306090903080c0a211b0215160512040804050907080103020306040b130501 69
    0xc682056400c010319100c0001d80c0c8610202c04100c00602132088402064001c200140d91782408800708000307045c0c00703030090045c40d10a0b140801d50343e4108250500003503200c94003400140144d6120070103110078452540b2116045034248010b006039401140c0140c4a48030071030020a55154141c04c1130002c10b80c008004101000401155030103100c1d0700300020b0103c1040281e401c269074090040982ca000b07540c503035103406400d022450406c01c03c0000c01c42002c0841c442d20145400c00a40d108440401100001c0c00c1c1000020410014000c00d4200c82c3d00d51a403031000e0760354004501842d000041c0190070440c540300342101e290401c40b4000940c2d00f06940100d040341100103003100705030202542408541c040e00b940e8650040c82c03440c3d260440c5982204074880a42144203e8460151000c4030300e01414034002e02003002038000c024021180141c440344150b5035000415100e0000911029406070031600000300000c000b2030b40305520010000c3c0c13801116285843c2c003400c540d040c150f00206400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 184127805 1250 184126555 184126561
    0x80106120e0709240b0301051507020a09090201020a0b07020304060815010c021203040b1605010e070803030c0a0c120c051c05270d05010c080601030b060316020f0a0b 73
    0x5440003006514001480381800380310980007865545041c1c0307119a1400310340d80c1840d00514034002000014802c100a103010325251102540e6415034820f104440c0f160202402c0119a0308018007944c0c0e42c41e0b0028404034020303140c0b401141c00b428240f40101e046020b140f020000082d090b5a04501800541c1c0c001d40d1501d09100f00038180c4a03001e428a0100301c084285038005a900400c1442d501ea410f031411141c1c02d44c8000d55600c0c5024942000c0150310010482610000c0d000c400c0e901c036540590000d000003405544071039160403003809002003a8008200240300200c0550040c0b5081440c0e2801010000e0b0944030440c00148230a100c40c00161000210b009005c4200100710640b0340cac843e60701c0c00c21400480007078810300c902c01d204038503800c41117143c1d1007914100100c0101e0b2100607140204608151070903d00070000d14020201103502180810309075440b902c5055038480300075041310b1842c1ca42c02c01c40f4000d00380000404045100f084607942c60100700703101140d51980b2681304402103003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 184129055 1250 184127805 184127807
    0xe010f0b0f24070c060806040209030c010c06110c0a1a060604060e030304090513110f031005040507080d050d0f09081206040605060a050a0801051c0b0a111605060f06030c2707080106 80
    0x80d42c09802944509e0051008510b1344e81c011038070280100307090a141e803500c0e081c3d1808034041c2190701c410810014002c01c0020361340c0c1010500c0c0c002c0038410b0400342118906800030303201440c41940d4035600711400707020510000d4000da4500c80303103220040445e4100343d900c881c3c01c01615001c0710b0020701c1c0010390003001c0401541c2c030000505040c08940b402c010080d4803000c289c0c3c0d040c2101061350b100d0f8480020409100c0c050080101514008041c0c0da04144000400340043d03100c0c80080310b4991078048007412044491094170040d40c0d02c003184c2403801c110070355404030a44000c1d0100743c2c49945c4500010700b50790f03203038024510b400160310341da074030b860180360003502c40d0405a010310b0003400620f440c50310400b21000c0b04030300158000501e100300d86644102c4801080e140d45070035040f01d80000d401d0b50440012012103030142c0b1800841d07803581e981c001c1c56240c000c016514150558004800c2c0784062404400d0381c000d5400c000d4030322581d0300342000054ac01c46030541d1540081403c200c0180225 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 184130305 1250 184129055 184129067
    0x906190212040303061707080c100c1a070f090b03010512190c15050c032203080708031009020702031c17040f060608030c0303041b05090a0e010f0b0f24070c06 70
    0x104c41000050260180743c10045c03a11202014180391052b80a01f206088080c09182a040d131140c1200708203041003820340c40400407030401d0316880f02140701b0b551000d0780548100c000790300740d40d02c0988142c10741c0d107082c045c840014501c1c003444285014032880d204510440c0d902100c4a14041c08180443d14600164203548001d161540c2c01000030800890460075000012a00c01d032030301c508441c008050741c0f84000e025034801d800049c074105000562805104ca00006140950141c8590b0051a55240003680480c1319820bc02034041d01300c1d1200b0300001880401d400380e442d80e20304001c2c104900344199241c8030401140c040300c42c0b4080d18808803d00915119210152094000071854054460011030752404020b000402680317204c82003005540c0d6001c180c000801000d852030800d410203000c10005081c1d801600c071129880c060b98000c95004602a01400e12805403141400750660000e0150100202005a000406070850400d035820302074001e001d09401a03600200390303824240001c0032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 184131555 1250 184130305 184130339
    0x7080601090501031503260415030606110a060c0201062d120b01030f03020307141e060601050f180a03140c01032c100606200303090619021204030306 66
    0x41502d440054000d12088862413400c0e0394004840b8031f2800d8006504d046800019602c00c2d100980118001443c0404c20280a080c4070454a0500039507880d810225840c00e00700c034540081c0c0e0f10006444011810b291b0014a140c0e400c1d100200f0b041d078858105034030003840d4045035008864880e00c044041c80a25640c04003411075003160f03520205031500c0d00c034141001804058800b001c00d030400c4040500070021512081e41c46041c0329840005108103545603007900503401144400080c0542142d44045401c41c4681d005031196404e0510004400d443c2341c21269481d10301c0a0007958012181d51000d00341c500031441400f02c03007100d4018038401801c0500b00b0154606142c1460b43d10a4040039685c4aca24180c41007010031b003004440d00c20f80303a2402801c0f81c00724501d280307041404a8401d60100c030a0582e03811483c0180c0e04080580043c0c1e54901c03088580002c07a401800c0401e025400c003000280503903103040c0c0c000d41400800c4649a809960695044010039510401004060b4030b007456440 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 184132805 1250 184131555 184131557
    0x6090204050306191503080301090509070812091903050321160e061c02130e040b010302091023012705010e01030207060f54080307080601090501 64
    0x1003000c0c980800b1030368854001c0d00c071400e5401d55503600c20900c4000d40c40381e03005040901c003c0e0040341d5241450704d0329134428015240d2440c1010b0000308104400640f500031204a0402418209050860344516070002c401d107550109210113501d02d021070941c401809140140051681c441300d12101141c420300c4201424603609001040148038050000f680382c0030202402c240400c19140ca0014025100c2c030f01100c200304280140b000405801540034080311641d00888100154032051003000f020307412140203200c0035071600103200505021800355000700c4200465007030b40703071906140c6084008200740c41c120504810084419981d0204c0034040b1001f8094022001c0d100c2116000d50682c0e0b01cac00303460b050103511469040c1e240d10a504581d811a0440820400e404c50b0034800c101030059514040040b921040c0c004550a01807150310107101c058880b406610800d2601d40da461028060111026100c1c6031091404030b42448000d510480769642c4010007443d00d40000740c002906600701d14 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 184134055 1250 184132805 184132807
    0x10050a0f0c09060509060f0d15031401020418020a03060b12070e0906031b010909060e01030b060909031213020a060206060a08061005010c060b04060e0703060504021602040f090c0605070204060902 86
    0x11403144c0001c201c0301000d0065543c0c59443c02c181440c00c43d948101c00c80e42910618008a242149283c00b8040043d40e2180070010300320480d4104041c284c2c0664001c02c032405211a0b40d00c01084551360003041800700606007c00d04d29902c0c20b5003a07813030700300e01d44a0729184890400c005030b607640994a0310310288226a0340409080c4031001c031356100f031500c072802420100c04e0045542680a082d014000b820281800c0c00501c4d103411888800b540203220031102c0030000404540b0350302d000e401251280203c0f01c0214209043c1400925040c1000340c40016034210305c0380c1c50805619000e5800000d041d1540050403541400400c1c03050402e07441d0300c01505500100c00f400004504c0126607000c4441c2460300001c0b0904034140900107109900016034818501640010390003800052248550040d4504000440d615000e10060b4441c5400c0c0000f00581e500c050001450b041d800a11241c00740c9800284030680c0d079a40c643c5500e0640c00860102d40701103800d60451400380211406001945025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 184135305 1250 184134055 184134059
    0x60302101205160815011403090d030605040507051606090c030804080d03090c06210213081902011205040609050105010b1806040f060e130c0302071103060f061210050a0f0c09 77
    0x40c544140684980d2504444060502e0f080c0e100700f80000844612a80c025540d05250502c40d072b950b0b01814031030000c6030a0050002d0241b4061048501c41c10756500d407540b502e0042e45911388c1c6414a12001c0f03079030650351001e110220306581008400b4500c540c407481c2c5c1c2c0324103108485180c010341721110404c0600f4402843c0024080328503110803205d850900c80004040d1407a00040208490340e407528180c400f141c1c030242010369a00060480308081e0540d1110390214506c02c00302501400c029011810b01250a40400040d41c0019030042c020b1400040d40d081c0d0b07565142c00c0d100280c1c480e9405800108484e1050351040c00d07920310b10501120102d1504e46803800500c2100803520400c010700c0940401503400303865103000c469010060080c01c10150900030b0000d8000d400c407903c16540c0071848a600ca416080c009203080c052011100a41282d950700c004101e04800543c0301900c1900441c0418151301c1558003440f80654442080454003102c5840c00310202c441500545017005818182 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 184136555 1250 184135305 184135307
    0xf0209090d0e091305010e030703141306050a05070501090b04050705041e050c0c0708010c080601050304030e040f0e011806140103021f2003090901080303090304060e030106030210120516 82
    0x1c10703100681c10359800030a036407138010610b29207520080143c0035509005560a00d503601100a01c50a8400c0e00c40c00002072028403041c0030341c040d00785040c03503040550005100e0b03a80030b00080d18200c1c40d1031814074600580c80d40c841c0e00317645442c041140c9404c112818031041190501030703000035200c00d4508101038610000d0100c22100f6602145a030195200d020a12504991044418002c100812584540e40d90042c603030090540e0350403480065040350214040c4d40c42102141e0250f82c043e518241c104e05900104001030210845280003160307500d0658408810a0080b14006105d12240031100a464103112080e50403952540204c0c8100a0040c001030344d403112009c0741e503900700d201002e10381604c0308296250443c3c81500c402000700071111810801c400801083d1040095800d4141ca90f40c620703565540c1d02040c0c400e103200d50002d10051140c1403085034500d50182e002030001c1000e95036900407540d805410700503100010701c04070304462914458007030150480d02e04e1314060b0007004070b440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 184137805 1250 184136555 184136567
    0x10506010f14030402060403240b0105090d060509070312030f180b0106080714030a0b011d0306060f030102040b04080601080706050307090306050408070204050f0a0608070308031303140301030f0209090d 89
    0x4202da409080400890203548070704c01503030065032307210b01c40f081c280301c10080451040c48803444100c801e604060200955521030001d980c081c000c0070300380035030755644d99541d40c000e404014480300030b9124045001000c285100ca00030b0200e00c86850010302000e4200e0b418013610584040b01d18074000c100c12900000711340b440d087e4112211840c040710903844000040780d0306100841c4144c800c08000c010b0010501869201e00180c0b00b00f600e80e220b21800165842c080fa1b10740794801d81c0d0541003c40041d0140c102560001d11000004000500c0c00391200e032a007500b500300307400a080b180d000800500c800307401008000040c0525050660840c80d0002001300310046901004040301e41300d00105081290a500b03840c0116802003040c07065140a035a032100c4240300701c58114246080c01000111943c0100301c881c1a00e4004020742d00e590f4801010001480c1c04a2049080149c5038070316091160307140014501a6105a600a91030b01140c010851500030190411415801c40f0307c1d103285003500a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 184139055 1250 184137805 184137827
    0x306040e07030f170706020d0b0a090e07170a05070e010608060306091b01170f07030605061e0702031908040f060e010807030e01270c09050601051b0106150c05010506010f 75
    0x4000b4080302c12444004d03542c07600900d84024200d0b40045042c8600060541020039121030030b8038980c0380c1c260f40c0c810050554000c10180e800c1c5070030403003007409079189805014101a050100b102c0b440e01ca07981e0b030ba5243c140980e0000c51782000c000d005111260380141080d402c694110002d0286083c1510b500b51205030000c29138200c047d40900c1ba14440e4020900c0d4440c8022051400e07000d4641a188500b14020403038541c00060724000b004a180d00e410b80503240e10441000c401c0b10b4921000c030b041c451941c020101071741d1500c1010111008141034803070000b904ca100f04031440e180d520340303a24800210303255085031051009a51030810320703036804080b03168042100d240228540c083ca0300000d00501740c190032180b0f48680c002900c41c400740c07c4041546201d10850403448880da1f501c4890301140d03820303944c190000d0002c00090172464211140455100c03241800010800d03031790007003545415090248207002c500c00301c1001041c00401e11034164460001c0c02d0801640e0b041040c01032036842c04d6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 184140305 1250 184139055 184139063
    0x80301060c0c0306020c0607081006140906040909030c140102040302183d080604020f0130091101020c06090d031806090315230403030209090a020306040e07030f 71
    0x1102501042c0b0084001407001190441011581c480c2c0502c1314940b40c0b2821505280070401220100e541c0308030f1821a0012207120b0781e02c010b40700510381194880d6074800c0f58a0303039100c003060001148140f054480c0040c094400d844031b4051030701c14500f150440b0084058151940d04c148800c00140e2620341c2060b0320380c100c03428001900d036103102e0590fa4458201071030a9005134401100400e44004110906081455080140e50300e9a50b4a559035030b007004031030094001e01402403515032940a0400c942228070170344981c5e01400e080c0755540440c1d0400c800b200303a420344c451750b066090250f003c0303030900400001e00c040e0400d0390259000c50080d1099400c454040e254120450040c90f10841000901c0c0f901d0310703e480322040e65100001c00003030f228001030b605401c545014500d03580e1180f0483c04610010b00409500c6000d20510380031620005000742c00741602080121911344d60382c02810b00c100c4900da801a00d81c00c0000921040720800c1480c0403256200030b2003800401c03080c180c0036040340d0740 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 184141555 1250 184140305 184140317
    0x114031303030f0e16172a120a03020d03050f06090103030e0301060504050405060103051213090b220501030c0906030b0c0a020c0306010305030304050d03060617060303040f1412060408030106 84
    0x149000f15004207050a040c84050003403040c0620309a5405e00c6400071110195940440e5403c4001d0050301c0d4174401e0200000d0700c01041d6051488560783c0e40600e44141d004203100900700042d05040d051018598080b0f006030881c16000712000d4040c8205600195680c5114060386000404610a0315042c080501070040382e080000450307500350090006008050010b22041c00c5c28502555074070000e0204071098002c102006200341040e106840d0081d0580702c0d800d81d031510300304802006104ca0344070f1503089403000001e40722200180001c40e048003200c41e4001032541c0345040c6503a00d840309400840c0e00c81c1c03c1403801c00120741c04026403500318ac03004554036070b10040000181d02d4407102c0c0c0100c80c0c0501031a400003042c440c01002941c0716030700070003ea896494154030700328125611801000042411100d000c6a11100754034119446280036084919280d103410004c0c1c0d4001e880e5020044162511031840c0050900300b002d4142110024000d03e52070519950390f40c140d010500a1004000d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 184142805 1250 184141555 184141571
    0x11805031c0e0a05010501090e010203130b07090905180c060412030518030f1605100504060804030e090c131a16150203070504150806150c010b0406090b011403130303 73
    0x1c03254020300d075241054045900340c102034500280079020034410912140d250134840c3e283d411341802268400c91240040c140c10510940d90b5001c4801c0107000c1d8010000e00c03d0000c28000214425503008450000e8103150f4050600303a0b00b80303000240c0ca6094010030051100300710609a6401e0401000c0d4036051694617610031880380004c00c2c810a00c400d0b4948901c8525000d045000f00b001c800f036000c0c0c2c2e01c0600f04151100d0620a07100100c10205c1d00040e070030041008194032650500340c1151203840c0400040c00c0020000b09a03a0040c0e8407280100400503503081840d11411134400204022006400041e4041c003c0f0620360145500080c0708400000715081000005003040d070050b2100f1504544034100720900829a800900585004003882c0080f040c2003800350014500c900c50042402e481080b14603001c1401d500240c0760745030290340341d86160308036903154020710018100f4500c0008519504000061081c5003140c0d140d0503043c001c00601000b1820f95080c2880c0c40c0d05800c0c00b02d8800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 184144055 1250 184142805 184142857
    0x50a11030702060304030324050306130203011b020d0906030e060c0f04030b0c0403110906130e0717030c0c0a0317030c0906030a060f090c0203031501090302060d05010801180503 78
    0x72081000c0207520500000030041003540651100000e001c044005840c508040c44040040000e54042d65601d07502440004003640544d1182d59941d61000e00081407500f0780300007418001c82451b91007009a080014210031181c3e0100c2403100804440c6400d22080081427062034030744c0740150016403d1307040041c1c50001c50340b0340e004440c011640460013800300c0c50000304900d02904240012601c01c0081c8611a000349007118006010b0f0310028003d15256980c0710146008003007005510205000780d042c00540c0081c00d101413001401080d000e155520400e0445505152000075001e11640942c03505002003403074078280c0403c3c2c4a08500e4140d80340c41c3c21240d18a107001e80c05245510a00000800c840c0808c2900800c1c1150410f00501d0149511403035440151002001d19900680c000e200042108105a24103140010103040110f1455242d03004904150b2182c0c100c0d81c8401e031104010808003209100344111050304080c10942a44c427a0759498403442030f40b038040c81e10500707807070443c000c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 184145305 1250 184144055 184144057
    0x10e060105071704030c0b030c0a0c11040c030905010605150a0f090e01180509071a0306040605060705030711030c0a0603050916080c0109300f0209040309150f050a1103 74
    0x298110300358541c00000034000c050b280e4064081111101c0941400150000b031040590b802740c107908840314206142041c0880710000740daa810713208050080303c680c10f1a01c0d2071040380408030491b0780201e9100312506190303094405e5036109902605044204c054001212019600980b140707290042d070348021a001182d0303420140e0031140d030b0303c081c010000412141c41084800c83d11690403050007140e9403000c03030544404441c45070100403201e12490200c0b22600c1401158040030043c0300049954441d4003040c0c0c250447d0388200c80d02e80c0002001014851a21303484001504100d0080408072103020100d40ca400c154444c16090548a0000c100b40352400d019900d901480314562076800750b510300f03250780c1d146034200010740402c900c1c160114141103036000c02104100301144405011558501900e100205088240c03410840c1c540300b1001640c9000100e802980242c0d034011030b540c1001e0800c68409882c06611050210b1310780c6c0559140d4002e4182c0e819403040741004409000c0c103920007411 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 184146555 1250 184145305 184145317
    0x5060316030209100c030807080606030105150403051005060312090d081b1036110109031e0b01090e060612070f03080406111605130e03030f0a23010e060105 69
    0x8412810000071300b40651003060050810700031b81d2214035540f544001641c2220041d5034483d00903208100600030390914800110b040e03901516800e240c17582e0b036180d050070320700325405400e01c15859909000c0030b0300e8108028480024002d000d40d01e40052840017900aa6541c00006c00c240d130041242c210300b034450700000e8100e02c503040031740b0508a00004080010304250b0103ca9072001351400b1403031007404104200c0708000a226040041d034020342c8405844003101c80c0854108001c49002100050003a01004400250100702e04450703c00b62600f9580706130141c004100d00e61030708540940d515800200e81d03410040640c2c411034600480011031307040c20b820b50800d17000d0300100301d0700004219543d4000d0080b521035994201054103640c801d140c484042a8200720f207032540c2d03030090106182225904210a094060014524800e10010f506640084030700c074203281414010420503402c01c1c0100320400702108843c4040103810040300ca8101c80c107014051104081c40d0004840d64040d5044030a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 184147805 1250 184146555 184146559
    0x10908030a0318050d0c1509020a23100201060e220f02450c18010c0204060602030a0906050f041a0904020301080604170711040507020a080c0706031505060316030209 73
    0x280c06404841e0280484501d02401c840c6841d80c00025016040c0070300c90310301209c1c2e00802d01404246030401400d0100f084509203c046130046962034100d07a14400382c070050742010b4001081480c505000784841d4180140460243c5140c426080c070402410444a200b40d0b43c4002c02c0c0800320000e0000c54050481c143c100c00d008081082518018299075240c0d41d6443c4051008100c0c180891a8201d25250b05071707001100c00c0340030f0003481e440c1c160b10b030b001002251041c9440e443d0f602a507000501603413515481100075070000241d5541c1c2541c00080e581c00303040e260030003d1405d070803050324250300d104038491204103101c1f504008000d10700c8041102c1e0804d000400642d12035844003c2c5a440309420b030b400321480040300b81c80d44c10000e00981a03d00c1d05030042c101000340c0c016501481f001c2c00004203100b0450080910003400540c10402401103200000300801286050000140850b600300d0304000c00d4980d034442c2044195200012030303030f00c221004003044001c00306200540107409a941c08039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 184149055 1250 184147805 184147813
    0x1e0c0f0d0309020405061c020d0f0c0306050a050a0b06180301020714071809110409030c05070b18030c0a050402070222140705120601230d021305010908030a031805 72
    0xc00040d034190004065203000f210100020384907882013103403048031038801b0403100801e042182e01510780640c14107880c0d4045c2d4a903041103031030b903902d4035045020703500708a030401c2d521001c0c0180120280f161071390005a06404012080c829000202c81d0f019a00000140600c81c42c103107143c40e1400c3d0151543c6a5100300c1554400d200b52000130f4984403a4050202c1814107001c49420000c260300505040303071742101100c158607440006000252412490a9041c01214003140300041c41c204510310080086558003922115500745103056051142c0f141031003544202100b211a070b0340e80e003c8d5030441d82c0480d00165240c0c102d1002c150200b0200185600e40d40141030600b00c44601c0d80c120202900c500080d482d4566266501031340c4a000708006000b06032010340c00aa0f965004154030700e980c2002190b5040043c034019507040705039024003240600d00b600440c01c40c4009082d00c07556006000c003400e003921410308111002e80c0e40d000c0c1c0045c540030140c56910b941035900615030101d265035000b0b402d0b9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 184150305 1250 184149055 184149073
    0x8190605030f0309040c17060607030e061908011a030f06010c080c060712020705060a0504110a17100c0f1b020607030e1e010c030e03030c0d0c0b010b1e0c0f 69
    0xb29129044446124095418240720948140c03140410b41002c002d14034481541c4d458500601805420080044007806007000c55403142e03503251009400c61509843c2d803200ca006060750028103001c0d0607403202c010381e5162592108082d84000903031380e00c0000c0c4d241c0a0010365486004071000c01101c40301030b0110000080243c3c0020000c12030501c110319a88681d038604000085400c1284220000944540c00075070204001c201650800b6820602030504100d15a9040c03001440e0000c656101004c01c0c041000d804540a40078007180385140d03c0701c0e02c00c0101541c001d00143c049081c2004020420215108020900c2d020340c2d10b88800c250094002c0ba100c50340e914003d03041446200003180b1882560407861900340e40001c0070004120306039248a1049202d49d4141c404044203192145d250106101002c4201404c215500c0740c011943e4500c82c00514601f00b0034202401a04000d10b51007040107204400d08010f98170104070b0b095441d4065403124400802414100c00120003000c90280700c1c3c00c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 184151555 1250 184150305 184150333
    0x50d0603080f07120206040f0b06040b1504051c0203060601080c0d02030109020a08130c06180812030402090a050402030a08030a020c0f06090c041427010204080d09050d02010819060503 81
    0x782000c244241c810144444c403080040e644d44400300d5000b4000c2541c92602e000080700f1580c6e13650041805040800d0402c082c100242004510881d4005500380100c0c0410880c030b002c3d0504028402921080e041e01d41040e0080307511030300001c18141c14800000c001c903051a40c10343c1252103810140398110b4030b95840f80b4509010358032940084000400703041c0801e0815002500030341091340c2c8240c1151240e8500001550724a00c0d05040003807050002c0e02c009051482030150720314280000d0011603403031405104000c046040644000c0400b860320081200507200020320400440e08008016100d0b55406003210288c840c051440c0700d1402003070381d0b900c2c208030300191240c0901d84200030b03103802036044d10074401120003410351425043c090300041002040380d1000710340c0060328080d1080741d12160303030317101400c1ea80a0b520042c2070341d1001890807015a406030901020344011a88401510703501d0300002e00b00030000d0b00e154142c0e00d000702e12449220303040d0b1012000301005000d0b6400c1c0201c03800c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 184152805 1250 184151555 184151557
    0xc0c0b061516110a0605030603100507111501061404140f220903122009030f03130501140c030915092e0906020d110a0803010e1501020c060703050d0603080f 69
    0x8001801504044404a0051b00030b4040d00e102d1080600100301806118031a800a0400580701c0c3e014040b1004070840782080510a9001030320410b00b1a800c2545002c100030704143e0a1150064140010b020a110710680d4005640488908072001c001c4452250000396603c00952503040a030740e40e540d01000c002426070001c40c0c0050080e1a4030324162000150380d01a2264034031603054401e00c071a4541d203510100ca015060721040902210b014000d81ca0845145501850b1a0070504544000400182d0fa00003036624480c220045200e0800c20713800455683c1303000300d0706814415003600c0d07a100790110940381035820004005000b0b02410309410121500c0030103054404d4110f58401c0c00340240700d07029111900460701d0980c02080c01072070740b940071030300b0700d03040c2100402e03902a0100c09404a620440954081c01800c0883d54050400c2e076080c08050a6103044d003030540d00b110503010069034501d800d407613116400d4188682c0d50343d178401400b4001e00c110342009085030b0000c60240040061a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 184154055 1250 184152805 184152833
    0x8040606050405040b10150f081308030408030a0e0a030c110d08040611190201080103140a1a0123090a11040b03010305010e1b030709020d0216060f0c0c0b061516 71
    0x35094511b46842d082008600201000e00704041071403c241e11602c1031003a0700d0b1a40c801300000c11040001c900c2da5a011480d1710944047c0d074121004014080317815005c0c8580030031140007400606d18203c0da980c01510701204242e020b058140308082000c4a0340350300046042481d448401142d45d20745501001d054101c40216115181c842d43e0b60086d0030004510241c9038443c0c0503154010aa80303150348400c4104202c54002a00d80608011800082c103540e221032800024036840b219150f04040382c02090300403a140c00c06908001850716061921140a903503009042040c3c0800c030b6086803c501c0c12107111360782c00b00040f8080007000000740300301980004140c012001c20b5601035402c044207120103090303450074254142c111190800011401c0d034010b10951100810260034500000360280c0c1404001c0c1081c0c41103620b690020001c501d80748240c2001140d5801c0440c082c5e412a02e0741600d800c4014034490007100840d904201000110080c0e8a001080d5119040c08a245145c81c0c0d203044242 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 184155305 1250 184154055 184154071
    0x180c0e0a0605151e19081501020d090e0a14040804050f090c04230d050c0102060a0204080a0f06090510020c010501060f0c0615081603110a0b0a08040606050405040b 72
    0xca64040b8892401600740c00041c1101c982c03040c00c3c084460305208418198100007426144100152204030341c1c1810302000100b9251100240d5140180700e462039400211041c60464100d07440200c1c056812840d49019a44900300b2181c007903891400081c020100c07400c2605480381c13180100010045103400400c00c0c0d60f02500c0c00720301c507000c14050201c107510585210701e43c1c12090200340400800c3c5070300050310203105007507182e102c010031000c03900402110380280c80f1a00702c2e40c65010300c2d5804000190308800d00d010210710306807420300082d850f00c00d451030042c6685032541d0322009208641c0c1110802a0700300c0243e90024040c00790f140c000f540004030b0b90300f065007045c0c000582c0c94011a8041404036150b1138a41c6d140200b580c5020050001840c40b0720040c048107004141507100700311300c203003c03156550540400c9082d428100c20070411320156610480c81030340180f20841020082c0e5a003e14141046e45440e221883d005010b020180c000030340081c0b030003042006210b0000044c60080c160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 184156555 1250 184155305 184155311
    0x41b0f090b0406090b01080f07030f090b151c030c05030d02030f0403090b030f040f02030a0803010b0903010608010603081606110f0414030106030308010b0c070512010209010f051c180c0e0a 83
    0x2a41d0065802d0310542c5c520703030b800701d2200302c001181d02c100c1c2a00d01d5803140300c600d0b002400b129000405821604900303000d88401084608010001017040700b90600d9003421681c00210500703c100010b81940500c2004003000001c0450300100b120420070b0b99120403801c0000c0d0b40740e2914108801041c841243c0503000164907035000119403160100310ba010301d05074201909683d5076529403032414002c191089806100f070103c0c0d80302080d61800a94040d0152045103940c92103880201401c2d00c845401401e0305074503200c41000001c690a0071035102c4000005c000d0040c864904000004000c403201d01c4218040000340c0e140140071020040041d02e82d00d0780305460085c0104241400c0311294000280400d102c0c400612084249501804040b1071041c03c440d2202d0f203400c04200014070410803845260b4021a07040c0d0f0b01d40e0401076800003205185411420b2150303c0301d071114042c501640b02d0143d103a4601b8186d804031450302d41c0380c0c046a0801052040541e0780d003016401440111560558246 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 184157805 1250 184156555 184156559
    0x11010215040b01120f06111e1603030902060403061401031a06090a02090d0203120c070e0415090317091509010b0a0b13030c030c081c0206041b0f090b0406 68
    0x24100602a0046400080c4110541e0030401ca5500380c074654038081d501744945d07800704000a0300b00c1c064401402030300e0700c13150340791160301d4090800c903044100c04070500701c07042c07182190301c114004085800302d4042c0b5001c1103c80507800443c0c82d03031041c0e8002078002820841c0398081d81d42d00c405400d04031792240c0f54103000701c50203110b500c165070b42c25107016a224401201142e030500080d0050880c444004111140076445940068540b02c02604402e1000b000070903044503032502440042e004110341608100d1601e0150303503200d4048680750032180c075030b640c0308040024036205c1c0c03000000100011004040c2400d00c1d2150303c0d91203403055903600c04890018002000150103000d0641e4401015201612031410281c5010300341d04145003508103649003107000000300d01038403c0c01c0c0056000d030403007106a90400e012241404000c402c04401c00c2500a003c0c80241e0b4001201907110350020b40030074110f8404200781c0d850021030b80c8038243c100850200400c2e04c00c810b50280302c1034081102d041003620307 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 184159055 1250 184157805 184157833
    0x50604110901031a310606050102010903171e01080619060605090103020f0c300301030206040902071104050a150e09070b0c01060302030d050c011a060405040f0e0703110102 76
    0x4a4240001400a004800600d00c0041544404c80d00022000304900c0b0405181d50326041080200c003d2400415500300c1c07070801d01c50244102005000d00b0b20003400fa03007a81c0d45005e000c5140c00d11544000d1388100002400303508554801d41c01121007c8000e41483d40d541450075035031751007070b5034030300000302140c40c1400200058481c040c121001911100d0500d034080006400a410417410f8115000c0100101442a20b0a20a00820200000680c408d8401d10400e80c4a098140fa15070003c0e8202000184007582d00c030016181291800c150159854070a440d001c611700001e1f48506e900942004240302400d200741c3c0101112100418903503081580d204501d05040d503040d94083c000e0f4010310700901c0f402c01031130024214410200000b2030071903580e0340420716040e5041040400500301040c0704807803040030700940e071100c9213480080500b4210040014040d10940c81394a1046680301c3c41c5602e60207254202081e1045c0000aa50700113542e4100100140001050940140103c0240d60003403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 184160305 1250 184159055 184159069
    0x90105100603020d0605030604050f0706030509060604020c0307020a06030615050304120f18060f030b01050a09150e0a0305060108121201051509040c0207060806010f0804020405070c0b010305060411 87
    0x98080d84102140451400310298001e50040300b00383c400036100c1e03001050984007003004a0290f4410001020304840c402401ca08018058004a08060404060010f45403000803001c2c3c003c0d40444006a94040d0091078a10310301c119074000750080072001d400078034903405a1101c4122081c804140c901c9014038041140e140c401107230028000c030102c0c4980b0307001c14414180910781c1c00503030502040000345400403401e1081c56602a40004001111000080758940100742000100382011420b004191601a1030a016070046506071502981500b4a0510881800c81480d002900c1a640540c890500688400c000d0040b01076510900c060014840e451404540b0307191020a074101c020b174200420404240c801d01843c4661140c18003a40071a41d13a00d1241100d9100f498009008543c9051406080a0380040c84c503030600c0b00c0d00c0c02080840e90410740541c1d026a0480707001496642c0c0d504103582c80076104070050007042c40f900c004410000002034041c01a030140008000610000e010000c034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 184161555 1250 184160305 184160311
    0xf010b0307050613031e0807060902130b090a1a040c0905040e0a0206160203030d021206150a140d02130b04030302150c040303031e0f0c0e03071d0711060703090605090105 75
    0x402c21a4070001c202041e041b03402d5015041d45181c40c2c1008140503203a0048a80094000381e4007141d89000150851404844034400c0c45104032061002e50761160008464200081c03640081c1c6441c3e20070407903050035040035224056002481000f0080b001d0760003e1503248140542e50150346050f4032051041c41c0042c07204990381e801040b00303241c6500c00c0103030701c480c46541c80100c0e0188010722260a060300640098502002c1081d00d040c010f00d00b10042203030200d100c044034014980e04000c0300d08200d5204145000c0d8181c040d045a40ea03ca4100810000703124240010700d403070080900106540ca046801042181d02070ba00302c4030740104904400070340d051305030340040030f42408110800c0040e0094010300410301801c2c4d4003152020103a013240c0b0645034082c000704406951441c800300051780181506039008410381c010426107041c00d281128a8098000302d1030704450040004080510580c4c20751045280711050342c14504190b200500a03101c2c03198122425400c040004030581014800d4601c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 184162805 1250 184161555 184161577
    0x708150a0219110a1208091b1c021c060504031d030a020f0d0b100602071406030708090709230c070b0103060f0204080f0d031503050a230f010b03070506 67
    0x340007140300c0043d1180078256605080a006a0308400045810700310113207800613850300d031000c135884c00104241c188030703149488040105c45104120902d8441064045803107050524491382003010b400000c0c0071140b41000141e101c840034840904100203608500e019502c2521100b8040448600c2d0080b0794140fa178100360944d001d4030031170f4003600c2e044400002e070400240056808440680322483c4208080300e41500e059a00d0104110281e8100482d030b0082880c060942c0c2d8030b10010001070700511001d4102403c0110183c0130034608074051008000926000c0401c01c40100c1320345030b803804500d58944880c2c0d200020f8000130100c000200443e82040d5004840c46081c0c0c4c21a601d00004104414003048150343c00d01000c64003402c00c014101803406150024659029a050000c040c1d600515141c44c1d200d0858008200060000070300c5442d03507600c0851000c40c0c02c2041e0080c0d1041d200701c401d031681807186070100c2c258500d042d031041c040c0e000b0a400b030b140c140741ca1b401400071074400d550201d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 184164055 1250 184162805 184162837
    0x3070b010e13020103090c091a0123040e1506070b010e130b07030e070b130e060111100203070311030a09110919020304081306020312010503070608040308180708150a02 74
    0x80c015032090344181d425903c1147d10001164444481c14110b0f06841142c49000c403501d601c0d10441d41e0018113911078142040103908500070380701c407499454056445078400388641c0e0404144441f4001b42002280c4002134016134071840d03c0d08081040300802c4c03145401503020500804c040100040d1101d40040c1c204480f66901e4817440e03400c600030801324944c0000c2c0e014060300032601900d418018140705001d141040441d43c1405603040c0c030309102921060500c1b50f4000c84005036000401c140950328030b013110050f103a80c0c890780282c0113080030055011050000208000e450000d031ba006c46122030103a0081050710015009009543c1015220001c4540c01102003100440031500190391092040521509003c401c0000300a0b05155401070f00c05071f000440c0019030343c07004160303103401408220700a18805162480103004918054005800c101740c400000b1075812800000b84601e1482004030792038a551510955142c207038507054072a115007030f80007003103408a15000782c4404c0e00b0403007421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 184165305 1250 184164055 184164091
    0xc030d2102070b04030f140406050c10061202101b08030a0b0f03101503050114010608070201110a0302090d0507090615050405030705060919090504121b14010b060c03070b010e 77
    0xb5290b4104101c81b880401040640c120307103640284014200410080c1c0303403242c41e103150742c1d14a030418040c3c0c1c003031200f0146000c0c1c0c10407242c0d101010601c825901990f0602000d0f800c1401110059a01d100602807000c044091004210009006610414440400300036540e407200410040400c445003042e4103a000031000d14030705895500001a00e031840542011182d03681d0b584a0a480141c3e10108072030340c1d81001085030301e406c004e230154012644d10007040540380c40364094031603000b034450741d1003003540c04a59a10341d40c542500c0340c1141600401102d0107290b40c0d803401005400c09009015542c1100314004409901a000703847c2a00c8004025002c41400c0c1001c0c0540e98101e41030703056002903490005c800c4034020616510160584010101d03035407a00b8201101290182e16002d800c22280c1104919010a1030b0623054407141d010060100d45510b00010030f01500900c0401c81d88030000081003820b0600001c001c1031410f104520700100d6aaa6005c01e01c44070100302c4644800c06034807045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 184166555 1250 184165305 184165307
    0x40e010b011710030f050604030f050a1413031b050f040605030601290705011a012d050c07060e090105030712060903030f0924050601020a020607050c030d2102070b0403 74
    0x42903010080b0710180120755561780303c0d40712040d462001500e00d50021030070f01c028941c2c0070b840c00d401c0170a14280240f9005424600a0014000f5803c407aa140b40218030913005040b9405610002e40c1c0001d2104c07180b0716145021711442d503c600c070303c5215140020b40d00c035180c2407902800f001c40d4001005040107078a00b64a0901c3c2c04019102d00040090040c50340620600c1c80c0054200303076000380f000040101240c00c440c003060301c0358281d49050040e685a4901c0030500b0000c04020100f82c6665107460020004050301d0b1030080641c2c0d20700a02a651001c10b50070392054807803080f40b074215140d584990303885c002c1c15110b0805000d80c0400400010035640814000d0300281e81c00b5200c1d290001b240425880d00a0031180454012200c4104e0480c1012030098002e0002030350fa128102c08005038141800040c0d0345010090f8004c1c01480040b40d403c051080c140701054820304007800b81c07001d407103281000504041c4589081c214140c241002c41c1280881d070300c00e4500082c5e004a92900e90748451310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 184167805 1250 184166555 184166597
    0x60c09120a0812070305011e031b08120903060a0b18070e0907090305010506030c010806150d0c05070203070806010b1605160611010e0a050d05031b070c05040e010b01 73
    0x6140080c62007407102070000944000c0040c070880d0141d000b010440c0c10304060003029204180d0202140b10100c141c10421182c1c0200c03458110396210290003000003000403113031004080b59000314141d01501101032401d08042000b022186001c5060b280503940e151446411150b4004910360040c805191442040b40d00d0b5002a401c01c400382043d40303142c400300c4001166564102c0340301e00000c2c03504400300208542409407503001041180030f4080240b1540c002080300c030b4001d01851059042d4540034164010400490301e048280c40d5040c0306646541d1405842d079400801d04034064800c000000400d41c0c2c0200d0501e0503140e40c41c400340d18040211248900c0e010400400341c942d8080d1310b03940c5c0081c0003001c0700c0c1310081045848910aa2051540c010300b100c0c0f240007000850b4025084e010000303200420301807024100d50038010340300d0311005c1111404807c2d0320030ba42031b02c04002230b4000602c8030343c0309804200c800444043c4034049614406034281c4036405841404140000310f0612004401c407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 184169055 1250 184167805 184167829
    0x201303061e06030c180203090607050a0e090406050709060206010b030a2d090c090e031b0106030210020a0c090209100f0210060f031109190e01061a0c0c03060c09 71
    0xc140140400c0400c01d0904468103544101d81007200e065040041c094605010b0510a43c07000d02141503141c606146030310341070001e0a04040044c0020090391386806101d46451254000c0d10055052506162000c014030090b50f0460200e40020000164148000780f13290603600700001180c1940c85201041d0f010f4000342d2084109140554050f901d00c0341b175403000c0302500840000220f0b480019042051600109410980c44d0904020361a2030301c070400001c4411390b01441c01c4484070500b089841600504031500001c0d8002c401254000718168005601c3c0310150090280b182c13034a40e2070100304102d10522040d01d4001c203485000c280482d0080c0e00d000c030f0365a81801603542000c0710b01e42e44402c483d0541c100c10004c00c1c1d004e9081c030500c40980b44054500134180e072081200e0411440d15088069810380080300661600c0343c0000e0ad00003034201100a00101d840ba843c5541e02c1c3c0c00c09245a0011280d09501e0320a100001e200c41c80c00003940c5000d141d08456207480d009460085c400010645 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 184170305 1250 184169055 184169081
    0xc0a061109100f090923100302150c060708011203050a0207080105092401120b0c0d0c050a030c020c010801050103020a03020c0717060a090b2d0a20130306 68
    0x500100c00c242e2034070b01850080301d6040d550701494500181000e018181941c0024514920b014028482821a42000319400940315034881030b40e690400400c00c50406134000a4200f10072a00d004070107015200548200810041520040d5458210813915140d00740b0030209c0c085140d0680c4408203002d80002c04004c0e4051058803010780c1c4441c401c600750342080d0354002c8594040e03107952054101d20050602c007205008503804543d4540b81e0811030707100b0300c00300181c251105080441c441d1a1040c0494000d02c070820014805043c0f5030300041d0098010407034440100c0d0404003070340344251010030107803010f031016195480a642841d0044000b5003050a40c00c083c540d00f0000456109010082e8000500e03002c1c5122041502e14011385040803409001c16420500302a42c5c600003891540986501c240e140341d4100b07034045042800d0540c44114442030320301000f05030030702001c06015046441d0121804120080380c00d000011115584102e00741d549a00300c07486400e000207041508115100c90b55 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 184171555 1250 184170305 184170307
    0xb01051302070b09071a0c0303060f1305070507060f1e0b010302070605040f02010201060f0e01031e200307060203070201140c0a020303040e040b070905030c010c0813090609110c0a0611 81
    0x6280d8907014403030015140400d01e40c2c0010717010840072030488000b06050344c4000c141c904098805c04001c0d034038007010708000c1c07240e500009a0344403602c03040103103400c60829220600040c00c1881001d04a03038011a000e8400c54102a00100210b0b180c1c01070206484000c0344506040c1100c034800f40c028090307461107904060f0201301c090701080440c000c280c0a0390007070b602a800300800c2e1001900b1181d459101031000f0076400001c1101c82c0c07410100310304590300510000c0e50807403e000c0030b0309007100300000200440c0c0201c1c0c2c0401c403400e03500b5092102040c10380071140b5091304c45c24183e030360b4000e0601c020300160b0041c5004000080010150400058240c21100c20408a500090441c0c00c56040303070428400801c204414001c1c8000c9860b00305002c3d061240001d42010007207502c0340c1d00000d03000e05000b0202421300401410508803030856284040740a06161034500050113401e0070f01c0b0f40b201c0306081c101d140148200079000c41e061407071100000d148181d01956107d000e841c10310513075981028 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 184172661 1106 184171555 184171567
    0x80103030507020303040b040e0615041a0904090f0b0a060e0c0f0a09080106080106050102150606091c051f050f010302031f020903010204030b0709120b01051302 71
    0x240525000e82c2c0d599050000c68030303602c1640c0c40b41f001c0b4a400580020585401c2c0c15050190750f04940c030102408002c0c0c0b822034940901e004105850b14110101d00c2d80030024001004001c40281c40800e16048a889449140c000c0680949140080004102d00700c103407881920080c200400c00c0f01810304240080343c2c03c6000e00302d588403858500160490307480d40100e02c078900a0039400000d0150340c1d200e10095001e01680c1c4034480c0980b0407076441040222010000512540020300814100000e410030040c1480c1c00d40807140d1400e01c894150008030754244011010414a44150044441c00980d10011184014400c90b10350b0300c15001400140d8020605206566441034514071490300c0340c0c80080284200100d1540c99840001c00200704100610f602d84141030584400c070215540f151100c441e4801042d0013401c9803130020040c041d5140040c02d100321080c0da0f00c8010304001c = true := by decide +kernel

theorem cover : BRFrame.Cov 183992805 184172661 := by
  have h0 := BRFrame.cov_init 183992805
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 183992805 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 183992805 ≤ n) (h2 : n < 184172661) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
