-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0477
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:00:34.705352+00:00
-- url     : https://prove2.me/submissions/25c048d5-fd8c-4b89-a137-b3cf28583f3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 85611511 ≤ n < 85791368 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 85612761 1250 85611511 85611523
    0x3052a0402070222021e04080f032d0d02070f1203090f230d03020d05060a05031f020906041805010605070b012c0106020102030708180304050d080702090c030103030e0102 75
    0x303500b10101c1d0301000e800b000c1d40e803040e0801e200c45010050400214400d0703d1b148004000c415000c4440c0090148010f4000708080740d040031030500191b1902c54184da02c4504e410450340600c3e1f4681000d01d0112010b1151800e8a1030103a11a01c1103444184500b04031038081450f050954443d4091480380084920a000c0d21074081c0e003280140f558054030769076190041d800e8219204500c81c40c01c18062a5010a0103441c41c0d444059401584030803441110000311400a00001d2203601d08200401080e1404074211100220459015642c5192042075102070f205552506505c05400500480c889011b191002025a42070304208083c4ea03d590040d03420b480381c454050400101d00c0c00400c40c4144c5807d20400490360030500d201709603a844003c07010150b00b85c0090000d030750007204115040e035102c0380340c548c80104142c040c052714070b110345130545034130079802983d0140e00c14000c5001070140d07040031a1002503020b0030488503803810511800042d04203000840000324603c074902011340c400201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 85614011 1250 85612761 85612763
    0x40c0504080703081e120a1802010903081e0d090303050906100509150301090804090c08012304090203070b090102070b0f0a08040201030e0d020d0e1207050f0a03052a040207 76
    0x1004218110b444682c0c0b10b4012803000c16140400d2614070050701210b10107414072120f0001b507402281041301c071010595402c0310a450303c8160300160440540e91101541c01265044401d6965901e84034203500d01c000d000d10580c084041000400440000700e99005041142c000c2c2e80c200b0041d11141041c0c1d44443c403d848942c0440d151800c03c7c412460027010386900046c9061360000480b0030702c4042403e60301214030a031030016020070b01304404038460140100c82038240c54454855070425007844110044c04091200384030308002045142d0715160b0001341c116400804480c0f020759a09205121075008546890040c0120440002d904401c8815680b0035544079001038202110010215404e0100800c00e90400d500c958060b14118020720001c030100a09502902e841c0300c81030000b038426504100d016010b10000e4000c222100c4000c92490156002160702c401c6c001315410004201400c6a04050682e004101a0b00324444a1034455483e0101400b4442000c3c018a0108070403030050140c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 85615261 1250 85614011 85614013
    0x160e010b040311010908160f090b152109030a020c010507030f0c0609060f09020916121d03030108010203070201060504020403120806041d0714120a080c1c020c040c050408 75
    0x2030002038258461000800c030103152002c0d05d160b403811158500215042051414407112000340681c08928044101400c003807042401001c1c40003006c2b401101000141804180d0041140310448003640408a0205144001d4080e1400c3c085034450701d0b9030245840308050711503811240c420b94090300541c5c1040da0183c4881e04030082201042d1014082243d0884849a1304d58031200018418403440c8428020b201c000220042c142c4180000f42501038441500300301030b1220300102c65480311440c03492004401d8041151300005290080107030300351071900340c0c5020100010170f264105602842c420110355000784800c60341c51051008906c503a01014000d442c50310341b0503103100c0c0280300701500104042d00002d0520b0381c0f07035003890030100c584031a5665070300001c0c3d0400070309110340101d00c00c07598202e8140115442920001d640c410a2800003081c1c88008588039110039402d2020240c80c0308240140103585a404000039115002188610300c00c0c0d1601940c1403485210304107079000e41b01e00c41c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 85616511 1250 85615261 85615267
    0x50601060f02150403030207050f03030c0706020903070b0f03250503070e120d05040e0105090c04180b0d0b060306070c1e020406030c0803120c07020603011203020a050f160e010b 78
    0x69800c652000c0c001d40c034001584569883d0301c14404541c0d0750795200c0e034043e0f50016100c260914046060400005001107182c0c42030062004032010790044510080e401040187e540c011400407034201683d0741c0c0b003000d000c10040b0b035000036600190002e610075640c880814200e80501c05a44045c840300300c1482000070b9041c000664407038060b00c0c28100440c03000300600304040c1c4580209150040044502d0000f401c0854104680b05591031414090308007111001c403585400c0303402d0b110034000c070702c80c0003107122103d0f1816001001541c007254079000043c050018080d1341c0c1c2010314180034142e03980d902901c695000100348903c90100c038001e147d880703490811034072075450000301e030700140e11010f0360b00c5070303980e80008000341c04148a2801401c8840c0a15260301404d0701d00b02107841c000b030a0281c203900800903000180e40740800c42c4c0c1500e0b07103102d0410300303442141800c901d07100c6042402045882214402e980301000025290720000690294021040c1ca80c00d0440040c40203100d10150441c080c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 85617761 1250 85616511 85616519
    0x60a05040809040222090618020c0a03050702060f070606170f0604020907090e010e062e0f0e060c0a060b0d110f0303121003031d0f040b03011506050c0105010e04050601 74
    0x140d001010090304425504031288004c4a1140c2e11403170316804031034003e030b950000700111414034544504942c038010045042c481180c0266441c0d800c8403900600700300002641c0b0045580d11002d8801d003000e0140c0c10b5882c1c00c0245003000c014400350103680d14500c010801d07022044c100146110343c44800c40040d04103a00c0e150300b40a81958007800b444d00f03221102c50041a1521000d007218000e00d10701d03600704564100401440001001e0302440f040c1e06d1100d1855407a440e1003004000701603502d03880d1001c0c103010410003c5804d40c0c0540030070b81c1e102e031000414610004000402c006614000c813001c000d00640708080242207889800000d02c038000c508600d2140c2d15259413680d808803009801d40c0c0c80c0100940003034241010131215110782c0800c0040a10a055110b0386001c0034250004a482c40142c4840c0000d0070b861448100b140f149444a1042c425a1400e40041069984200c100103006071039260240a50304000810901503203810000207201000c10800350245420101621007a420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 85619011 1250 85617761 85617769
    0x2040605070f1509030e040c0203042304110406050316050301051003020d181208061509040e0a021c03120606080606070602070c0605070b0906010e0612010b0303120405060a05040809 80
    0x1078507090f118181192107045040c0c1079409001c3c06a4420755030207003404651800c2200301c401038420b4000310340c030a010601441c44890716505120392030105119244a124000a001d40100c032240100800007160020752990001d01a41c010350101c49501c101d401100d00496507800240304860307110703100202811410f40603500501c28440f1510000c0350900c1c04d00c424a590681d03c40c01141e01007040800c00c9045944201220f4201400700e882c5600141280342c00d0100d400b8103411140700c0e507600c5403180c49122003084001c5020b80e019226890360310444440b045a2200c0410960101d20b508072282d000c62a04c0c03044600381d404603100c4040c0ca4030341105010035904900011079051307600b00400030204100d40d4889008060315602c0982e00d150034a81b00060220280242c0c10381e0340407100500c80b602001c0711041e032241044e03840c0c508081160407030501500c507181e0701c95018000016015007969500452520550160080312029142c44100c2c10850318211005451140140030300d075141d1030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 85620261 1250 85619011 85619033
    0x1406030c060a1119050304030203100e0a02040e150405010b030c010e09040b04020a0f090b011202070203060402090a020f0f07050c0d081206042304051902090103080f040e090106180204060507 84
    0xc07101c3c0849142e28044414048922140c40c02179032035600c0802c0030400c42c43c1c200140c1c0803180d842481440160300921941c0d6940c400902c0003032040b5101e0301007484003d070030000c1c00e505400101145200d070425040550003054145d982500901428010101c2e41d402021000c40501c00030303019039402c5d0b6403a12a4036040f0409030040f030340174003140c00c0000c1c0d81801001c0d82d0040c0849020001d900051040050445030310020000340305801848628056035021030307810750098040c0c9a070001075451000c884000c0c0700308030a2209110000c0b1b0000320052442c0068001c80e48154112110740d856501040740c59000c070200281070042c1001150701c5070f0003505c440c54008001070404078002451104010050490350f160364452a00801000248081003244407200d040d0402200c80310815500440d0b1400414007015005010005035241e51f500b84c107045500420030f5003003010701802c010b10329601812a5200e02c0c1014114680800000100e6100f140c3c129425500c2c0c2c0c61030015583d9520800345 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 85621511 1250 85620261 85620287
    0x90105130201080115090b1b0c010c1a06060d022a06090709090317070c020405010509060307050904050307060c09060801060302090a050f040608120c060114010f1b050a061406030c060a 81
    0x443e00c01c0008508a401c00038100310700d4528a480503118400408d076140c020a00d0310541000403805030900420b0038009100c80c444500d8400110315910000401c459200b160910700c203a610029444090355a002059141007081010180702c0c400d421807038599400d0290380b1001c00e03030405e0380d00304000700c85948007194191080c20400d1817060392101c21400c0300400c41b90603020680c0c6180c0101140f46c01d11a41d4094941100e48203c20308001000c241e84a8130340c050b1600611080c0e0104d4103020f000c20549104aa00c41003e0010400c10103009000724810320480d400704044000200c0c0440c060300036102c0d2924060800030300985086d0410200c190400c07a003580003680c1c0c0c10040f51003103042c4071011140f0448a070b0f03281c3d05d908100303149143c07540590003154032191188511401c1c2e81d0101e49900c424200b468003850003280385600c03203042c1c132001c60020142e1241017001340801180d6003103108001d419500c0103050b5503a00301072540b1814180c2c0301c95400a41005600d1419008042c40200c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 85622761 1250 85621511 85621517
    0x32009060d030c0512091c03020309190807030f02090a020403020f130f0e01020a110c060a03020705030409060e0a050708130803150a031a0105030a030903120e060a08090105130201080115 82
    0x742c0c509840d410f0814042c1720601410b9107001500d002c0d83d0070104c2900c1010021a40c0d0b040782610a030303c00a4480c040c0d00030281c400c0d03a4415003130102804070003201000e85040019100001d541e8035000c44130212006040340101084000207410300c43c41d100ba038044035009400c0a0746201840c041048460420039036100300c0356108240c0d92400700e644603140b28030311004001079844c046108050085407090350f1185980d0301011600c041a111901a03951480d034900300541c40e105149480c50650285402c801c25030b9150200015444090704249401440110010031954482c80f508aa900808940d42c6051618288000c000200c03aa0002c560058131516804c2c44640c0e1170000800300c9400703a009885900302591003103010240408400d0040c08c04034003d2440d44174580c0c020b418580c0500c400b0342003d4092076000206405071036007000714140144050703501e0114510142440c0420350705c120480d881e10f0000b941c075014014200c00d28540584500000d60b10300704d1509008182000b441c410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 85624011 1250 85622761 85622777
    0x10501030923060106022a06033c0a020a0e0d0201090f030b190605010206070309050a0609030c0507050f2b08040b0307080609010f060305060409020a0b04032009060d03 74
    0x854044608002c0c454445a0003401840d45040002440d142c0b0a0303500d03040303050070090302902c1060303402880201c480c8155211a160365540c9801d468400300d003105524049120b4114403440c0381180d810584400a40207502019242d11203064120300943c221500805c0c02000036102d1440e04d81c07803200c42288149022440d91b510341c40c4402c413201031359100b147c0c02a9000c3c203005031124501040404500005c1d0201700e214a0300000030b6842d07074040c14403418550380d86000018400c050011700c28107074100d0000d01c080070452500825842c0383c070806640d40d014103080801c2a190091050301540c3c4014040c000340070402c00c0101b0460079207541e0616115040f10b03000c0006201704060401803114800c143d0b2a4a002000941051700040095100358207620041c0450042c2c00d603007106030b030168500002d45960324001f1400030700074440040d601220107400000e868042c88020020b5034812510300c580d07044200a144910000c0c0100c4680c004164000103089007000f0100c410329034042e20704081 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 85625261 1250 85624011 85624043
    0x3e04090b19060201020c010f020a020c0d14151e0606090609030304082e0b03060f04080c07090b01031103130f0c09050703050406060e0403020a080915040806011a0309060105010309 79
    0x1110809076010ba40981d401244443d0b6240b001c1c40750703071905807030100300354500540000c000b074403504c0c0030b50035074421511034001106102c644200007001401c04401c0b12041c8000e00340360303415408221400c42d20500d025407585081614801d50602031080a88440c1c1001c030200204070854000030246034140c4030a0100040310842000300d60000001301103000003038a14a4405803441205500d00d507030203400c0c2414080b8a450000d105a80300961b05216401030b100da01d0528558880c003e05c5003107601c100a000302d111140e0b03074003401103104241c0b020419030051000340c0c10180821200d28801250042e400c0e8046021600d01c0d0880511038000801000e4071003a9810440c2c0c0c0c15940b210009941c0d104000030410684207220180003c0144080185480c0c1d60082d60f420f08080000c0241c4004290b002654036003a05600b818614081c9450303c07a42c0728221103651700070910030701001012001512501c032902c03500303d13401a105a00500116800c040c015409084904001c6031b0607000c9440c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 85626511 1250 85625261 85625299
    0x90109020a0f1406070c03020d0303020c01140718050d080c010605091905070309082d040611071202060d02030705130305060604050702010e030a0e06070203013e04090b 74
    0x3001e840c00b141c07800d000b40e041080e850b400d40041010b035070041c0402c003ca0000b1400c07440c00300d001c4035812a1200c458104a10f021030183c015055501800d60a04c00134028110703d0040841c810070f510b80e10840c20140c20840d10703d15801d05e1160740d400030300e001030480100d41614010440e0f480000c0c000b19025550b2004295101021590b0b817030b104c801c2000c400c034444868007410780c0050091a0901c006c040c1303070312102c01d94403a8282c140c00012500605906011320342208140c507828101c00c0a85556451074050074000c190f2002041501802d00045209603c20322400a030580280c180d500304014078004400a500180035081800300030302200c160711041c80300308405503118902816040c2403c500780801d981c0b0207003c400c03e6904220440d0491940001500c0e05011640b400030034005ca00740114a4074805e096001e5010750801410203140110070290300c40300741450322800c1d8920640c02c218152134500840e0340300b80d260b0070041008040013603000600909401450350076103035503180c844 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 85627761 1250 85626511 85626529
    0x915240a0f0e100e0f0a050a0f060b1b0109080a05070303061a0a0210091e03110105040302010b10020606010f030b030c040e0106180e0309041e020a080f01050d030f0809010902 77
    0x5a0300c260410040040300981400b1800c0142130303660f00103c25042900c404110401e0042c8010b6074a5651000602c4103a41604001c0c020900f6580801c0016111700070710400e60300600366082180c1d12140b4a8000c814144a240c2c8115040300307146041201c585001c41e030a5111502c04d804058450348046080411001e0702d10300ea6041d22130713003691003540312400b03400d01e0f008a4032203000c1442c0ca4030501c08101103c28490261a40948000c8190b01c03a00d010350341003000c0c24040c02550310700710030041050380550140710202d030100c0e607800c00e18503d204100d03540c040440b041c030300107424200d099030054040e0b004080103150060955203038080345008a000c80d00311160901c0980e44944007080281000d0f40074441d252401c0009000b03012850214581c1c9200e0540042e0096a44404100032145101e60303200018941034000d541d070794a0014010000d10003642d02c075800320030b844000561483c03c060459542a03064039100c0d0b0182807900289c90800005000d16038035505c0b0034a100c0140d9880186c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 85629011 1250 85627761 85627769
    0x7110105090304300311030c031b01060803041d040201030902060a08010e06010903170306010306030209101d070c06050403051303060e0c030d090b07080405040204030b0915240a0f 79
    0x216116850500f1000c0319500c3c004008801651302851058a9031604410030340e42030305400c0801081d00c801118501c1c1d8403030b68146982c3c501021880d182c6401d0782c00707202030b0b0100c41c480003409100d450b0840c0c00e44a10503441500d101d403440104181080042c1c05065030b03c18014140020003540303a03004260380364000c1080c580041c43c558014030813003041c010b14581141d02842e004480c80e0441d41c500407801c204032012200707900c011000a420303030f12980100300613540c0075042e001d15003040c201002e44024280107052002d90860035805080d851341742154814003142c1c1d80c0d40b0400c03115440384002040090019001c0000400c001000401211088401144181000904400340940042c00c001c0344542c907610a07003003c1c2d01e14030100da00a004c881510010700c0c40343e560391303d0b614001080f80300320b90009802c1400880d00009102071103145520440d48c1070241d072403040700c840c1c1e0f00ca1080c200300c50b841d910907142400008510074180d64950810f80162407915925100c0c000c240d50742c0c4540d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 85630261 1250 85629011 85629013
    0x4031401051008060c070209100f272007050a0203060c040807140a03030f030b0301140702011d071404020c0303130309060c0512030408090904030914030609060705030711010509 78
    0x180410346a03407202c8800201001d1018125506001d462881c0780e114520f00a40704100510100c0d44403400809410010a800e000c003554481c0d0350328420f40b104c80c0c03504e11001580c0c0c0c00c81c88010902030314090010034050810384d142841c0000d43c14a4000c1d084250155100d204d1f42001400503202080014002c69001c8121612649840b00c4603243c05004c2d0850900c3c0702140d01304c9882500e550031908240d80d810f0401c58180c11100008400803c601300f2260360540c00c040b84854641110200c3d20b00035409a40288070551f0044903c203001c00c1c080914000795406070004010288a00c040a4074900e0000d2000d4507149000000c14916081641d034004032080c0c80c0107100806400080789001410079003040c941d0f4403416220152200c0001c0d1301c000d0301c0e090001c00141044000c0003107031207038000208200b403a400c280c00e00030608040b900505102c42c14075010900716103400a05103100b445e5541c020a041d41e900c100c11139030b68102910341d100f4008488454108401c007805142e1183c9032482c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 85631511 1250 85630261 85630271
    0x406051006020109050d0509120d0f090b0901090902030601050706050c18030a0f0204050c0705030a020c0301050106020106080c042715050a020403030e090417040801050603010f0605030d110304031401 88
    0x200000c00040480d4448000d5a02d00030014001640101d4001c0d01c0314400c1c01d140e0349644101011030000812089001d11070300505024103800c0307802082c000101d0b41c2d9a41c075210400d0300d5503c600013520651456501254007030504201c0c84c074558000310341c0504107242035801c064060f6a03120503100b069403112410075001c5013003a0382d4141e900b40c04801b014200e0080000e01c48d070f900c402440c0b001d10b1300003031f00803a200c41c00140000702d00e40488528a40c4402160350b1980c204100035140c5c0046a01a0f01c41d50820000080780c5205001da03106403402400500700360305002c01000010a201102050280b03460380401d08072545110030303010b0281c02115800d0f8152200d0300090204d41004081c0d0101c9441404180301282d4480316002c003508007500c94441640300c5080080e81c030611111201c07550880000c01241201041d04514010320b0190000c1c08181e1000518070709a80241c001c803034069100e92044032005102d1414911112000e034182c85c5090384075201c01131803030701c0001c0c0785219a460f2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 85632761 1250 85631511 85631521
    0x5040b0703050405120304050105120601140c011d030a021b0a030203010c320301030308182e09261935070f17010303080402120613060e03090306040605 67
    0x30171426000c0303c0010040e51034a418880064403c0c050440301d510b20000020010305940d00a82031803020200d808a136640302c3c0350b81c40f6040d0181c903e070014850744025800400181c1031000050b22442d0303c80b0b0b0003030096410000c02411a61030000e9440c1d511140080c4c0020150300c0030320960b9a401011b60f1440f4603855000c115080e180d092a0411291081000a04c03000121110989054039414a805280d0f0b80b541c10b4102c13080c1d1101c0c0d16407091402440c9016a07044070640590f15014211550001c0d103031040c0195204442c4558000703000c1c0c3d03081c0245144000c4101400c030f103440034400056030070403118507102e100c2400007502c000045414a03840051840d240c041c04100d925090102d0325141c54041c1e420625035070090003400502216041030006070340280c0108898a20303a00c810f0b00c0d90340e50790500401ca00c0302a035042e8018220f011440520000100340144103070b202901e0810b0040003944d4500c0100074045408455000c01d1040c800c055034140202400395002c1d6001140900703003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 85634011 1250 85632761 85632769
    0xc0105040c0803040609030305090301142d0408120601090902040e0a0b06070c14010504031b0905090721021f0e01030b040606091404060512060702010b040501080c090705040b0703050405 82
    0x115400c1030b0841d60090008002c0c10768424001000d49600d40703401e81d100d201c24004603014110010f1301d80c3e6540900c0c0c0800c1074032134020b03103010750342685041c00e0700404000c000441038020f002c0e94081e1150000304003280800400d00c1145411100614020b10120f41d2002c031203040b0782003034200901800254091150900e154022042c1020085841c01e241226564a1000411903803052460311540c094003150300fa13000d00c068900031a009440800d101170701a1804820380203900070000c2c0d1510f0400407882d507440c0011030005494503c02203400f0041e06100d07101c203c5440ea54100d9011402e000030a03040b0440542c4031407403003416200d2040e401c5c503880004d0203039807003100c02c0c500503440d103403042000b42d0384510200b080381c0284403000d50220300c100201d40030304010341000ea080b280510012004403800900c070361043c0300030703402003020181000c20402030711000c0c465660070781d02220249465142c8910201d4100c0c1050800b189440e66801c1d01c00640e0708800001e501140c4c005c1030070401818 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 85635261 1250 85634011 85634033
    0xd0609030f260603030c07060c0b07050412080711060a110f0d1d060d050103051612020d080d1508030a02100501240e0a0f05030f0f0c0d170c010504 65
    0xe0360801001c0c409800442c00d00305180450006100d9101c0c5001c41c07403546007802101c0b00c00030740702c00399508661100c2010f40810400802154504004000542d40c45c1c4110281e0b003e490381e44581c60b450000799107400105411862060ba80000c03a2444120240d40310002403a1200b00c40d01e4101c0c4200000130f80e41c0c04c1c40c120041044031038100c0c50700c100303000c0d034002b000046141c1d840582e070342c10005840104d052409603000c0c4851040c038040002c0144840018195802c29104505c11901c0791039515000410341095002500041c0701071256001420141c040e00160134950000900c42c0d10320078103071070074080c1075202c1b290903000003c490b84019070620507149142c02c40c82d01403005502d00b40c80d85425201032003000741074403040d0003c10500c0e8071504400056000090a41030030343e80741e003084000000c03a0306c90a8400c0c884d0004003800c695005c1040e480d82d9842030080c080100c0c80c407044c0000005803e03822528200e85031540c15102078402c001d405004407800000480d03203402e03c1e20b01e0801d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 85636511 1250 85635261 85635287
    0x5040f05090613030509100e0a0609050108071d19050114070203060105010c150e01020a20062215050f010807030f06020a0e03190c0621020306010504050d060903 71
    0x5040a0420007200800100c0c95007100ca090007920303a12009007411540b81c06500e0500758454181c3d040c40114035400100098103100482e01030a050f56100000e5403044507510406001c1551080000d150320700a00391311f10743c2b111007170040e24958214400500d0910349002206044844560240a82e591000d0300c000000b054554140c81c0c42d0150b00040c0e501c00d01403203040d04016000c1c1c034000800c0480540e619203a41401418095444451026030203500704031001c5001070b4003400740c004005603c91214041200f00805400261505c4040004040d010911400100405403100700061000140b900d8500d0041800140758244101d0f5091440c0c0107902481e0705a10001092010070141043c0622150740301c80016520001c8110546800e0081c40c03c41e681360042e00000c1e9040e004081850003550320a418221032a51200c405131280c085800d006c2d040d040e0700703200b0030300c004180368015500100141011ba0a00359100001510640d0051044541a03180c840e8030080640010350f5a50704 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 85637761 1250 85636511 85636541
    0x6030b10030507051201180302011410030b06100306150305010f0e060105030112020f150903100203070e061b01050403090f2c07031512050f07030807080a03020f12010504 75
    0x3140c55030300d0b01980e07180f040c080e5521a41d841548000310b04800d500980f442039038440f1031000c1da030721800d001e0300800b00c0c001c0c02c2c9280300d01c48002820720341442c6d0518058a5000c0c10100c01c84e22180180302541c600d615411082c1552210041002c08503241d40c1000600a035801241660401840c401020001e030303c0744503d09901014004aaa04002030724306442c58525151f00e2001c5500005044480c4c0c0300c5c04603000404060f1851140d00d040c030081205003025400c8620000b1441050022071008a035203100094150205468600c5c01100500340084000516850381c05418009421a00d044c1e0313080300860013442d02000340c101c6201640d0001c2c02400000d00c180e80790a00e035a02a0017602c0c210380900f200120018903124026804002e42083c544800205580c83e01901c182d18a0044400e031090b2240c40704807207501200013400c0382a80c0e8800788240c28840b04d0760f0307917460980004482d14249502800b8168a601005002c0d00c01002e181028924551410061004440c222607031700f030031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 85639011 1250 85637761 85637791
    0x5030d0219170403030306140306102603030f0612070f0b07081204080a0e0a360e010902010801090506011707210b030d0c1205030c040305010c0306030b 67
    0x280d401280103101c82482120745461004035150044648081140d81e120000c404240031081c140c0c154003a6007035560a08805c61150301c1ca2041568401c4202d03440c0c6040c0b070f0001011301c9151800d205142403800710f01080b048145c1400c0005013160001c45080c2400340032101044000c0c41c05d028200c0200981d20b0203800b04d03a04004400080c40340318007d03103403d00c03c0004c001040207009401c1351005101d40d070f84400c0c9800e06142840c402da01c00e602d9200014280c010121071881c044190200311131007119854038151400e003d2120340380c00c61103180c3d800380a200c0e00080100b29400b41d805045001800051504018030000d4142041a000645158a410204480c0782d820841c840b881c85860000c56219135146034086802d4070401c048000828520100040700c206903820020000d2003c41c251506c884801408580855003c10301034405c060079008a42000c1c026001982c02846411880e49401c1d240d842c1e26094034040c1c0004400642c1d00d031030800901c909800c0c000e802020700c00000c50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 85640261 1250 85639011 85639033
    0x100506030c0409090c0503010e0c010306090606200106080d080105240d110c010207080d0c020d0219020f120607030b10090e090a0f081e03130b0403090302041508070503 74
    0xa00c038000d90003000348060b0340c0e400c1103041c4048045e040c001040d0003402401142504814117480301009604d40d40400d08200c00800d402d0290f00a250545201c3c1d0b880846a43c41c0d0404507800c0400f00d41040384a550311400454000e4007403102c143c2d8515151114240c951410080c0181800750489100d03060320090b000d44201d0741c4a00442d100e0811100d80071425405040b400c2000384110145040c4542c400141002000a11405410f2100b88084200945101528141e07202c44031003d9000041e0441d190303540212243d44550a071650014000400c0811007001048140741001c00d1011594402e030100b1051940c58011105120000c0c0e0b1402e81d1040341080c003501d441440e00545400142c03c600280260000f00001c80c0a5900072039007845440d45030a0000103a4810b0300c40015040f5501240d0400a0b103c508490144440c40c070190528152512400d2907254064011000c1094080c1c0c0040540d40314025103446600c417196107403501d4502943c00e4581b503210352115020b5040411282c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 85641511 1250 85640261 85640281
    0x3020307080c0a180f0305010b090106140c070e07050d0b0117070f030e0d0903021807120903020a0f1103070f0f03110604030501090c09050a0203090a020609180a0510050603 76
    0x35000340340da40b035594907494905010380300032581d880b881100d00d074920340000340b034115418101c089a000710000c0144030316800511050510901801c404941207410700044c004044004100e000200f0080c0c03405180c03651800322072500c040e52130500245000c99401c4064015204181040200742406803a07640c0807240f4070484a001406441481840020208210700a0304800010000b41c0103540e28a4181d0101404501a43c042640181190408100445010300c0c20b503001d2a001d4685a0719242920304020140c110040c0c11021402034811400000b07503000e030020713081841201d03042d8a580c083d078203040c41d1100990003a0300b2003068500030003a81d850516240143c82e0402d1080c1755902070f01020401d01c0c49a5400104150320b00f10703020741481032100558090b20001041405603480315142032040c1c0c04180c0742c200c665041103400c500145080001441d0040001c1e2100c8050108a0b0107010320030340840301480900e440ba41001a00503d10581c5d001030101208c80310b0860600c18068 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 85642761 1250 85641511 85641527
    0xa050a1209050703030813021c06050106090803040b070f080d0504060c0201020f03060402030405010b060310090507080103110d06060f030b06090c1312030e1003020c0c040204050f010302090a1e0e060103020307 92
    0x6000d06c84900041150540307800030040e02281c01802c10b2050701c0c0812000e40341c401d4036a005444241c500350000c14611700c500702d800e0444504030011800c1c90308140c540c1d1103507030103101d080f100310070001030030400961008041d081c092580c01001400b49020308004059502c440e00c3c08085900c108010221080d00c0b4040da5000603042e80d0050f01d030b940d1803a0603030060072b40042c56980000b000c0700b0407410903030301200c40c02910b50205007889542c50303080003504c0103139007800004c0030b0305180c2d2601c60840c20040b240303c1142d4019040071070520b40e82c1091001008180c1c00c2590310402640c10000c090620b40011034105040c2c21449141450303403070801241010744c3c0961003800c20740000c0745061602c08d4101100d070b88001010000d135240c05403006002076001280d1080c0c2809641d5013039103d4a894402c1c3d508445004d0110302050500070011002540091172950740032413180008030f03500c880d406040030b448505d0301c4442400341c1441c40303c0350015802454941010300400801c00d40550008074 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 85644011 1250 85642761 85642763
    0xc0a110304150c05070503030c06040606061d0d03030b120a02041506050324090c0408010e07150f110a0b06011b020d020f01110f071505031017070305030a050a1209050703 75
    0x40543d0700e6451a065040c00e8075130380516814440402d0a0342d0003807002c101300d1b0044d48160401c004040e0380d000140e0305010300e1511030401c20b900c42106d440303505042c02c00c10010307031180c580003803120791400001d0100410b4440d0b002e801e50114084c401142400d1050002607001c910b4900304031844c0081c0102130303100050018201c4501119150b940e200480740041d244c40e00108141c040e803610f2180004590000d1064100640c240307228020b0004001c142c43c025282c4080f2406c1824400a0003501c40000b07980c0f01d04100581c14900c07100c454003d006101d82c1c2132090504040d2418110300040489002c00118881e07119817070f15890044e80c2e01c2106140196040d500c5a10308690b070300042c1c0e0f4004074121a60211700400307130010380c01040450f60b481583c2c100999608054000642180c0b81e001c201ca510740004400361082c0060030301030400b02d400103900303800c1700d000507101c1d0f3b10282160080800036001c04c1c0c000c0b0380d90107903d4100c3e000c82070210901c41304220210117500c40d0f50761111140b02c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 85645261 1250 85644011 85644017
    0x50a031505130c180b03041110020d181e031109091b0d2001030609090c05090c0c0a030203030106020c0409030c0201030b010e0a030f021008010806010e1e0c0a11030415 74
    0x10145480c50701440c0f2161303101d891400301070000c95694040b10200d60003201c0454480f0b0800310508030b50f241c20b005201a880341c0c0e41c000c3c00300070b07030010041e164903003000c010803034030361503c007001800c2d00144240500c403007540403800300c440346180741604020002c2c0c2440c510540030303001002290f10000500554000381406585049942d07e0003040c9020b0305843d010f00b00b00f6880f03001c010300c4100c800c04a584100c00380e8041080079034412580c0c0071126200c400038400c2c521048100b2140c64284111034003e03030002e0034503190040800850b0702e010034050044000da0004001008082c0e0113000010440c24103688c00d01004065070f5009100c4006010000e0500d5601d51020006921a202d410318801d0080e0454080e0358690401022241c00488100d08c208010740310240a984100c51040c101ca100070700501c2075034202481c801c1c0d04003008102d0488008202c030700b0300502d00030340d4089020b03d000030303421a5102c1d0301d0400288407000302000204264403c120800102004032181d0f0080d1200d45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 85646511 1250 85645261 85645271
    0x2060406090c0b0c0f06060405150d020a05030d1d0901061416080c0c1c0803060607060b09010e01030219060e040b030319090608090604020d020d05010209030706050a03150513 77
    0x210380300c0307070b405003a401080e14884086084050b913240020740100e000f51600807030781d00b60380301010403003900d0084074a44010103074036030407482904206402e11481071004010600858842c030219141140308a601000904040704003444418810460390b65948150741654480d1304240000d0b0080318408003500b19141c0c001550246902280a1100615800388020f60380b060400c80d06a55009000705051141350818203908202e8a00c6078204101e03540410703001e003181d850100b000f5090b0442c64041d00d0a40e1118502402c541c0e800d0441030181030f040983e00e503d941107005114a419815680a1410000100503c822508640c400d01c052004403000b240d880e0b000d07000719056000d10a042d44403000e030402c4076141c05070030680b0032094425550f24500c69544114801e07640d030b0001d540207034200080e84069000b500780a1404143c51340160000361500f0303005004245402401e0340540c00007040820940f860991500072812a4521815201001410200055840d1031004548442c080e034072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 85647761 1250 85646511 85646513
    0xb1006030c1b030c0c0e01090621080c0a0b0115030606020102071110050c07140102010c0f0806040f020906070c030312020406020c0d0204090c09021c05010b03040f050c0301020f070b010609060206040609 89
    0x40301040c0501e030317014041c8980b140e5503c40c0c8001090082c024601060308208010451148149603400c4c010310415240742d86c081551075060159101d41d45a1a843c000e0400c9100404c50329090341d4000c080103585101c0020b401c00c4001e00701c0c1c0300341d0415021a40104042c03404601004091149554101d034002c0440c0c33160f4005031071300e11070500109620302540d000003607440c02045100460070002c1e0020f108002807198115070b50350082d41864085060500481d0050801c0e500c41d44c01c008407000018a440c15a00025545410044003195402850681030041551018411b0040d01841d402541081d06088019451704448030a20380a50f29030a0050155901d541000d602260000a501511515455540060f50219140c0c502289000000044a030300c0d0740716650403102d41603040d509603140ea1703484181203604110117542034441c0c404074000c135507070070b2004044212071481d880d6906e400c0d5140141000700164813800500624020030004a500131450b03071313807103a40800c0002d0503a01c1c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 85649011 1250 85647761 85647767
    0x40b0102010b10051e040b0d020307050d090b070306170c09061f080f060a1a0d0902061812070501080f0907030605070903050f061902070203030d02070b1006030c1b03 73
    0x100c024001e90020f0016494080c003038210000f410030174454a043c08268202036508207003485903108506240c1400c2181100801e80355025680000007484c0c110b1800ba8040d05500540e41140d0043d034403841c180c000c2c08006600341c451503004000540d0500e44001c3c1000090751914107512201e401908000d00140d0a0740c2d4200c1e8101c010444032900b1a480580110018204c8078119410410700c08034001040b1070b8507220000b0710031203080004005055801c801c0c071510340e0f0011103441680d00d13201c100b070b400160795200103890903191030a1100c594801007420400f03150440c4c402224282c020f4241800540da01c04c0300c59900451450701d46146449a82200740f81800690000e081640303403405003c5000e40c403e8801c8c0480380904101d0700c98036084806a51681010b8074250003401510076000031940c40e43c0c0103482c2040c0000c2c15607040400c00c1c00741c034041e60302c08502241c5e1240003c04028054210301c10b1980038080511b0104180718400d84083d201d521601c18921594100b4a00c0e8020548 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 85650261 1250 85649011 85649021
    0x307051009170106030506150d0f03020c10020105070311190c030903050a051005070302130e09031c050103032c09040f020d12020f0c130c02030c030f07032c040b010201 74
    0x50382c000d04032004460342034403c0c002c1c441800111054000c020210f101001704681f60300d0001c1c401080032401c0011039468502c12015901c00b00d055001c0c414a1100c16901c081418211100e1500049214500403000400721094083c407490607000c2800804030031540d08080b221010a641400f440e074541905080c0c841e8602644014071a201d4070a0b418108800032400b21100c600f11542070140c0e80740c0110a5090340181e204000304904031840422004c00e0f09401e07142c01445040079280f40c140583ca1007274080750040d03082d51030140c9a400410402d94421a000010102c0e5020124804200301c5030b515403070580109280b080741c030800072a0502007005c0703d92030401d034010304150b1150003900e0400c00c0d054503001604050302602e01d04601c04038021a517418500b40c02015205200e002490490061016419960842c40107000c008840182000146000102021126201c02691400800041010525050041d4400c4032000c145081209a2074041400c9902040642d280710040780100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 85651511 1250 85650261 85650269
    0x9030503030114010509150405031603080901080a020d060e160302030c0a0c020f06160314090d150204090905030c011a060316030902091003150606080f040c03051615020c0307051009 80
    0x40c81681e9a07c172207410890061040b102e003a810340328906a0036507500440e050300d10020304100c1d000c1008084561013034000c10b610415500b03006040c400400c04240c2210500d801194421407158107000b105081500e1001070109c4519040d450b62603c9519291140101803c81c0b0910ec0e180a90364110b54604400d008072030703805080e080d1244014080038510080e00303041039002c140078403200742c441183e520440f08801d801418014041d003460b62014104144c003943c2040040c2d003440082102081400784800450082000319200c8000082c10b40c02c44510410014070a0410114000d00c0d80381d000582c0c4d4400c5411065244008a28005802400008200075071204103a01001491440300d02c1940643c1d00409003c003214a02040c0c1c0e07030880701c3d18051400404d03905e400044c0724110004840d6072161007a140402a5592503440502d049901d0303503a5004519406400d010203210604d115180f4140c9100403c1d0a6801101007034a45905000b024000d4800d521120112070080714030b08002c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 85652761 1250 85651511 85651519
    0xc0d020a051210150e090d021f0b0301060305070617010f0308030603010f29011803060b0a030b070309020906090403200102122a0703050f030a0905060a0902090709030503030114010509 81
    0xd010168800b80011080c09044285e4801c00042082c0e03682c0007800e40c001e0310494005003039140c0840d18101d82c2a007004245204c0301e031650300103449078600f800343c240294425002031007220b040481c0a009030344544000c005130740401d801007040320309c0da02c40c0030120703500200d40d1907403602c58501003409008180306148885051001c1c0c00304590070042070f5001c140140c112603940c00721140c01165002151503500c0152540c0000500102c1c100b0760002d1a0b01400130002d9400710307501c2d513808030380c071104598500220f40d031001b00c50194100000640c2d4895011111b03d503891505580c00740c1015048003a074662034655118004078410254121844528040c241c081145040046610900c807149409002c8030040e1a9154040c4000c10a03140515415241c103403c15519035642c1c00180c0004000d407110300d858400420101e04c0900009004200c41f007804500c881070707070040c4486844003910710030810415242c1000072842c08820340381034448405c54200000050001203469006218a507584 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 85654011 1250 85652761 85652771
    0x30622050421110c0f04060807120c0b04081c03021b0604050f030c060114010306030602211005030a0303050406091209060f080c0703121e0603050c0d020a051210 71
    0xb440404032401c2c98610301542606002c0500c2e19045980d2900c03568001c0d81680a03140d414a5480c21500550350028090000100d25036628100e919000c0b1a0340b0a5500c042c410b00514244154950140084c080d6011428601498091001d42d10074601880c01c10800190300c0340391040f8401d40403200481494480341d8949116130291944821056a003180c42c2d10403604a0b0243c4c100100c20fa0b084041620050a0642c4c601800e4020a503101e03001e140c1010344d568070202c0040c0705440540000c03c09a803200c4982001031554a1507000e01501d54180030500400c10031050f503000070701803e819414500403616440d40e280c42006412050341c01080701c840412170300305d03003075204400c9001c580296480204000d038010051350060001c0d101c010085d41c1c00c200c40c00200b40503183c4014101301400c00007400c1005034000b2002c0b403201200c07802210b03490324010400d01004200d203080c008400c880c5030315030f10040c0d4002002c80f80580300f100e0040480000d035242c40340d030500c201a5004110304082c85 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 85655261 1250 85654011 85654013
    0x6040905120c06060f0904030f0903050105010603021c050c04060e0f03060a0b0307120804030f050c0901060302190201060f0905100b070308060114070c0e0c04080708070311150306220504 82
    0x360480042c1c0d004501ca6900080d00d01e1a00441d0a5400c0c2d5026004503456112510f048030403032820b130300d424140f0601c9400040090001d00c1860700030000c50b0740050301d03180e000345050796512000ac181c41d001c0341000300340013940c1080012682228891300740140e5282c1c026010401d114101c9180716494011402044001e042580102c04d0540f02103082d1a40b603a00d80e455400f20304042e1070003501a0005100074800121880700b20342509005108030303810903149000090545000341c025130b0009402045004040e24000072000d0340340049d00007448018140011100032031010301c43c01921a499034049031040d2182d0649001800c050a0901c2d6921024140070307182030380980d091350004000300708001900b0a4007060b540020340c840ca600101602e4054582c094400c080c00601d0f42c1d0504000000d11203108011400041015a000d4a0054510b0600382074113920070320a00d0107031074509104490b0090706800c0700d0340000e003122800d20300b11a848070f4201245c1d090910b00b14032032400c81844 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 85656511 1250 85655261 85655293
    0xa0e07240806030304060c0206030c090916021e0604080f070503040b04140603060904231504050c0105070c090213030204110702030609010e0c010309020f090103080a08070306030804090506040905 86
    0x1020280c859203a28409403a01d0040c035070743e40300383d00c500380000300000000c00040c81d00780000c50304030740a80036860030a9400d85c00580b202000380d90490150740c66004841f90f007901403058010300760b0110031a00544032803140780c1e603c0d0100180f00614120380003810384845003a40c3c060702c40140e005012207403200d4841d004200c4580c0a80920300c000e10203e50420b25600d000000c41e4881c40000d00414407136247e56603082d00d106100c0d051000c0301c0041c10841c4010090400c42c1c50509078008400200c0740c101414068101109007040d54100402004110702007084032000004940900c2c1006aaa030581c2c1060329040907542c20095202e81044030440c42a015031018100b03050007141610040e0b150503154a080752a400141e00054111001d1038a1a6010340e22440340b45001400300030902c2c90780300001e0040c1209810440d40c0803c003091041000340d004a07150b901042c2400d040000904540b600b1401c0e0140c4d00c984914542c440c0c000134010b8503260094542103600400322580300c0d40c081070301 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 85657761 1250 85656511 85656569
    0x10e151f17010e0105010b0a03020c010b060c0114060906060a050f0d181a040b1303030207020607050a031409210118060b04150b030403080601021c08060f01030509060a0e07 76
    0x100d54150f08116841907000d01c1880745034100c0e100315008514100c2030b13100c264060b400216026000c0c0d50307a07110030781171074035000000e045001c1d40d1400021440c0554845520b2100c2c080c200750b014201220030400561103009c110784140c070705410016200d203410f0242032100d1194141400c0c100d81000700144041d4414100070403101c1c070441680120141c11651044100e1003101c014241030644c00102c2d0900302e11155052109001c1d280140c40d007041500481c44540c800b00f012110769010300350742c3e418180e04c000403058a80780014114034003088040012130041000031645c0104a0070585081c03040c03825440f14055013000240310107420120b0408000400009580ca03000d1414400c0c8540e0300700080110000782c0e9a030f0b800c00c5045454030b0710203e0310502c00920042c191b108411562806000700603402c003402c442d55980030308518102d405d00a07413188001c0c44d03505040c1800140a0200404070729540e00400b98000090413030504c081c0c80c5d141ca90f195009005001510395004151a001510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 85659011 1250 85657761 85657799
    0xc04240801060315050f0301061e080d021b0f040b0910031203090503070b091204030c090f02031608060307090c0809011506140a09260d02010e151f 65
    0x68008542c1c0e0340c000c107038161640362a0303a4081c1884101c05001e01e140c03404c0d03418080c08000c0e00004000352681d06045891052511020141c1244d150400200394200189011040d107032001e094001d5900011110700c4244d200c900b0f04c030380511001c404050710750b5070020214003030062103000e02c2c0c1480f0f600c018000e5014001514030041c4600e000444d14000d001e07d1070241e03030020003140381042e55101c1f9103200b64058956503180c01741d000c10710320a24880e005000594010440c0c480383c2d40c500001c510072141b040001d80e001c03600500800120850448088290703240504000401c4d583d0000001d003040c4094010403105840c004501035981d07800030801b0310866940008200000a4034882c2019010354852080014070720b081038021405c00b107010704101810741c1481d068003134079103541702c00307070426416078800b0024400401400304604120800c100c885a0000300411a1040f003100e484003400100110b81d50521400714462003130001d007100e00c106049000042454883c1c000c481d40c2d01001c24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 85660261 1250 85659011 85659017
    0x110a030c0807080603070603091103010204170f0a1502070510020f04030302071d07120e0307080a02061302090705090112020d05010609060311030f04020102030c010c03020307110102040e07080c0424 87
    0x1034202030141140b40e000f8900140185401803401604401a01c90000203c4081111361045c6000d40c0700dd0010380081c040010000600c1007007051518949121543d20001ca03500c50711040c07000c921041c0c1c128560a07844040075a43e864241001840c00400c9103400d0701e490b02c0010300c00a10b8460704c0281065038483d601751500a651000007024900644185003a0000c4440c042840c0d10700450b88802c0c3c2203000700000c5210440c400d20319095800c1b914041e52803000004039a0703042d960604c0281d074000c210a00d40c45d081402c58000c1191401c0040c48da078140040000c802200c0d0380955202040c9080a250943da14420403010b600a00820320500000c1650020013150720f0303000740512503a401c21403001c00c0c00c1d0b030303a41102c241c444a070241003030741580020010180006400c2c01107202d0400d07075031005030344c03414001d40c002e205140484115030030ba48144400d101030044410ba9a80058851608281c1d9444110550b400c62103154400540c3e11107014100000351110102440203241ca92 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 85661511 1250 85660261 85660277
    0x1b030c03010501051f0212030702030d0b2d0109030605010f090b0907020a060b010e09070809060109150e04020117040c0302011b050613050102040807140a05220203040501110a030c 79
    0x1a06060a9400078050550302c0103140d10601640405402d0030703080c44441d44100c40c030480c91141c04028951050343c620005070000601c00d04191010f0081c820851002d50b0640600c00034080b0701e00750a810400705c50011009011041c10680c404e6800c14040d41d0408020031595035a207100001c0074841b441000d0300c007403d003000d81c0302c00d1500c21520343c421800c1e500604480721087d60b695000b030078020a00c2e41401404842c854146d194180428820601a25000d0242c2082d58000b8503040c01680500001410700312400d00004948000d0f81c03c46a05041a01d480e480f184010ba40016058206a84081048080101f8806101035400c11203000381ca0341c400d111540568540220b0100070050090760050000c211040800035100b2503040c0503800041c1042d442e003905606000003036000308214410281a11018034000841400400c01140d205000141c54940500c41035500c0e0022030300076501000040a001080d0003c0300c0c0b401480c0e0125554410035040034000700001c2141d000081d84030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 85662761 1250 85661511 85661533
    0x100e0705040f0917070f1103120a02010507030e0304081e031b1c0c0f0b04060e060702010603150507020d1107050405010603050a050a061a070c0302030601030b0412140d1802031b03 79
    0x80003220350b4a904900790b09000306c0c8035201c00781c11420070701c0c2443c2c041c401c40d01c00d011001c2c0c0e150080d080d9001c569001040d141451035000342503c884075074440c2c10781c00411080117a00c1001500c0506407440c2031204a0700302080d018582503004000e041100076050400d40c0501034000702d5094420030000b40000c5c00b03034103031800480b019124107800401c8605510346407008208448086944544100c101203580c5480b075100c10f0414400740d50603030241c2e4403444140b0400c100c18100324102055034608201d01e140c178240003980ea068000602c0e0038400c50001400b0700000900829000e014040d006001039652510020001e240c2103c00c448028981008922401c400e03001d14401c40d100b0400091040440001e4100301c1d82c4a0902140d400502480000c01030320305018071402140100084001e91402e1700b010841610070203c080200700c1c00d00c410800c0d103c0d0358020350b01301c1e8541d41000911160055440c04000030b44400203036141c42142400d141d0a0f10035190741c40e0500302582078509242c0b071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 85664011 1250 85662761 85662803
    0xe030c0a08031b010e120c1e010605040e03090616170304030e040c020f0c04020a0e0306040b040b070228150f0e16050109090203061c1209120302100e0705040f09 71
    0x4905030034050740c1201d000000d0040101011f02180e07810242034680d0070b13111098030f07c009208920041d03007503511134a04010300c0c0ba040c0326159014580130090b500e003602031b01c0018018031840b100e003501c40c0c580c101540203100f04079044000c89007070600000c3d505d09050602815040801d48620f204a05040f10055000d02c0070942ca40d20759200b038001e002c12094101040040c1d02b000ae00c40d001c124800038000e01507541004024001c50050410801c1030074103043c0460a050014401c40a40d4003820080415031600a1211500c1d1210501c05007404075a2a0490001a01d03103c181006802c1c02154603190240e54000c10b01d00300288200e2b0078148803201c41fa90035001e039100f620701040d520001042940741c0e580041d40d024400400a2400d5508500c90040d00322441c10700b9030b0300c510f8205940325055004181e52015112005081c2d40c84113199600954034800310349040c640540303179004203045507403c00c081c901600c00100705001c04c10f50102c0c45001007950703440a4403200601030125400c906 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 85665261 1250 85664011 85664021
    0x5010609060c06050601230c0d030b0604090e0c041a0316080c0105070204021b100501080309060301050f240a090e010f03030f020a020301050a05340e030c0a08031b01 73
    0x480382d1100c20a5107540c0e11142c00500c03008282506206280c07200840d110002c06100d0f002c0326640c000a43c49081301c100180c94007072110282418145007101e008010760301d0500381c4003101c400700700120326141c480300c4490078684440c46003504181040000b0001c2c1500c4c080110702c1800540803544000201131303600640c4a01c5104070011904406030a51075948144010140e03907002801c050300d01241d903540180102500c400804080d005222070001c1440503018032030042207007200440c14100b400b13002501c1c1340b0061054a00c03c62586c40340e034005444075207a081d860007210000003121605191132000d6544003890100000d03d01032008140c11101110050680710702d40b03040e50a003825070750203440f01150a000c00055101e00b4040f0350040c2d0b03003409214451258410045000c5c2480d441c18660444040c09a081c6e080c0c2001c09580786904400022080310341c0791070082080d19040c0c0c0481c2c14002403001264010011f01000318000070f000004041514074261003550007060301450b10300700c40b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 85666511 1250 85665261 85665269
    0x1203091512061801050409030e0d120f020c06090d020f100504050310061410120c0c020a060804030806011d0603130b060d0305041e080607030c031a06030610170406020d05010609 78
    0x103002c3c030014003841c2850342c84020346a1181c1801d080910122001481850888508440454400ca0682000e60b40808001d4041a0174002032400b000c01c00002030305401850001401600341e05810703c01e558509004c1c0e40c0c00c0c00003809410f5504440140100345500901541b4020b00c950030504401034000d220f010100d0702c0d4082040c582c224100c08010111081104110070060506500100491180701d0340e40541d199885601c0e10703100d184140000b103402540110180100e100811001c40d4000010343d030710000919045040500001c109500201d2125046410280c040208041c9010401031250164064503003162141e40320402c01c50340c80c46158000b80014414801040250200000d4002ca100903c202c1681e064a0346541442c0600456051000a4488980c01c5803035405204554141d420340b11590f03140040c0d07801144aa210141030323140900c00c0032000b00c0c20184108650701749006510100d50071400c1078200b510107504001200d29070586085c00000d6514007404041c8215 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 85667761 1250 85666511 85666549
    0x3060f1b120c0527010c020901090b090703060e0a0e16030609060e012009060403020409110405070e010f110304210c05030a020f0103050a1103070203040905101202120309151206 78
    0x114242150000302045510b004c039040c0000303080c200e00140d070b510080c0d80c040e0040e43c0340043c01002440c20444501e0015013a002814075109090145039821b20b01caa51040c070149011a10103290b5203228a8800b100d0b4038811a4994600044104101508507a540900851040c800200b800c80158221580c4104442e05210301b03184009448400501400c1e00080c02400c0381d00701962500442e041d209050011101010418600c14042c82c180c400d6a400a15a2401250316508100064104002101c0c0441031080d5503480c80c01c501001c2044030090a200c003c000c10303980080d0480f82c84081038000446c2e005c561007101103202d0800144140003076400034010a502c0e11450010760060201900090303035191900c41d02c3c10034110401c02103001e000d560380119601c510303103031030340c03048070f1003e01440e40c80c1809050030480000012092003032690103c88501107090048140c5107144524407074250801051502d031620780490f031001e032625101181004c211032790750760100070b900e010010802c603039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 85669011 1250 85667761 85667797
    0x80d08010608190903080406150e010b0906041d091e03030f0405030d0c05031509010503060402090c22050405070e0108180307210e03070e0103060f1b120c05 69
    0x100324401c0c900b40d50480319a00400b002110288429401d0f90200141500461034a80c1030004106080c80f40c440500c2a490400e0802410000c00f841c2602d0103224103851441c010810705404c1e6110800c50340280140b582d02c00c102034040300f5001c10240101c480780c4803405030f55194541c1407481c0601c400071022050246246a4403084002c0c00280058070075501440144030314a000a1036100e40791003212a512025101e252020301c4520308c1101c00d8032940603260210040000b134130001181500103604031102d000d01e0b9220403a0442c5402442c00c056041c034000d081c00d00c02131558540aa09444050f201400103984462065452052481d552400036a503580040c03d0004034505000d0313030a0f1198252413411b01142c0760201e00320503002c0d00718038402c641e980c0820380c0b64000d454001e0f0801c0c1540542111440c00710502c6890703405200240910340c40e00900202c40c038007940038459a00c080214140280c41d69040280000380010349003010034544205104900d0003041940c01d001c26008241701 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 85670261 1250 85669011 85669019
    0x8090304140402030a0902030d020606040509010c080a1107021c060c03020a020a02010e030111040f1502010606020a080c0106030f12170c090d1509081806030f16020715020c0307080d0801 82
    0x13544000d0401445594801d0024010f99091096204032044c5900402d807506040041004840d8040c1861590381c0c90700800b108290303007002c102c035072184c400c5000052640c83c80508580c60b100768070000f0341c4407500015404800300419001034905002e252304001070441201c2c19400c030321a6070341210143e440f0350180c03401988202010b1100000c00703000400c0b12008002c122003150001d070455208140411428485058428060402c03c1c2140c8000d0182501d460000b039124441e070f55003d4400b02001611001a103c25040400250346c484542c202c3c0a501c0d06000c0440244905c4050014007003500e80c16804034003412250182d2103c0c0c00d014a004610307401c0201201c3c8014088500e100c2882602082000900c18031a4003401030016540d1010304c482e411083c003070070035060340c40f0b101e0500a1111001420000c0303580300c1d91215070081601034224060346444096800031039102d004401d884804c6601140c0000011000d03001c441030395403560101d94032480e01c003030070b07500090301800100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 85671511 1250 85670261 85670269
    0x111903090b06131d011e0908040509040501020c100207020315060a060f0905060318070815060f040f050c040f0806040210200316020f0603060a05010323040506070809030414 76
    0x18511280180020301d42e00c60603000c4d00100021132101c20503596842c00b54542010303032541c9640103110150400545269541c3c0c0f0019021743d0040342c1c01559908006001c100f42541101e54000c3c002045031101c000060000c0302130760120808a0090090a0480901482500101d4020700c00203204110450419034220342070000d80700300104001002c00001160b13140d6100441c011001e203001c0741c446803c0e181d001032400180342d2180790250703c4000500000d16007001410f8200508541c00da51003201c50f000500689040b900d250503c52408007800381d0748550030018403c54030602c00c10840c0c6655208840c0e1518022140a90400c40542c0c0c890103403441510812070340403024080350749101c0175044191454124801c0c24501c0a5101120801d610303040b10081c1070712908039421461482c0a03004201003509501c01c0905064131141040d00d42960000c0340e00c0b08480000d2074070703000d00d0b150410564502064440c42c0c0454000004113540001c0071007200c05036120380b401201068400c20902c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 85672761 1250 85671511 85671529
    0x30a1e05070f05090d0b010305030406110d020304051c0213050603010b0409030806060a030e0a0303060915080d08040c050423180d0c05070504110d0605040c0207050f0d0204111903090b06 82
    0x14680c4203400c0100e80000800ba8002140230b14000c1004580b03541c00c008000e03020314a0407400480d681c1c404107a41030030582c000100c0d001c0c1d0f1070940c0d2280740280220040d000b540e10f031110081d4005640e8104d6040501c0c0f0303074801441440110000d001c0004444180000c4544d402c80140000c0d03202c900040d258140500204000d8149260000f440400e08054600b84442110101c001985801003040003122078091100880c00ca9880e60491614204200f41e44d400c00c400f5103000c1c862104000780522508400980040074083c1080c803040c504000c140c249403104010005c41c1c1e44885003c42c2d00b660403d016114607001080042c45641900413044c1c41400409d842202c0c0791081807004a42920340703002e00961141010394250300d5100c00c5104206841c13142d04554051490002c10840c1c055001501504484c42074400b400c100c0e071b40c080480d070001e402c210040e40041c00c02c4607140000c032131000201084040c000701c101001c5a01c000c21408e03101004000341040300c854001c102145460029 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 85674011 1250 85672761 85672777
    0x80309030708030c1206090c04060810051509030106090507050702060c100f0c1d091902071707050d051c05060111010603061a090c030a020717030a1e05070f05 70
    0x4407814070005558005450740b0032685000818804511140034802d641c6001d80c02560803101340010349009100d43c0c1141c0624403400040122803804240503a401000103405400094a0202045800100d4400641c080342005009618100303000481001600c03580780206a1503a0b0300385040c00607020850150050400118140139258450111403a2407289004051090a02040342460720b0400390021030390142c220016400c1494002c030a03a00d10307120680c0300c500211003982c4001c1000001d0020702520800820517807044200c0380d02021803c0144c0303141c0f4802c60880d402c202c0c0440d0116118014007079074000c25203600240c000310086c2d0b44c1041c1d0340210185084548645030700c40e21801d5916039402541d805a032141c40340504406680780044c0d0700415078080c40030303091180c440015440b004015200640e80415032404111031030300a10982801c1100e415181d00b0109003440042500082d1641303a074802c80399000481c001d600a503885000b25440301a142418160141c036a90f0016031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 85675261 1250 85674011 85674013
    0x8100903050c010c2a02010e011b050f010e1e0a02040b060d1506030506030f1504020303070b160801050409110915030714090a050103050706141209160f12080309 71
    0x49007102c072007441050031050042d80c0e2401400c00b41101e00c001c03446000082600341000c01d02d0000940d8200080301c00c000c000b0321b0b180502c450901c820316050001d40000502502812031110b08805054014691101244055803030703d030b00304480360040d003000103080501034000d40c1941d00036203000d511601d1140c9003c0c0109244c862000c9034542200c080800039a090348005409003c8158144121640400150024400c050400a185036244c2c0440c8500b4481e1840c0c00c0042c0842d03c0074025201d0060f84402001142c0c10610846a1840124001d407000030b40c001d000080d80b41b07454003c3c2124160406c96207a500c2ea80e400a00c0440c40b4000e02031709010524a001144e80e071070400c2035400500d2208140c1c0d03003a8404100300009001c0103050340c9500c1d81040c0042c0041b441c00710307880e0211401420440041c2d003000ca00d80d2850b008816000002055070030400c0b07410030001ca0450500507001010a00c11921485503010042140c00740d600d422004005510000d0130050081d0303000be038094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 85676511 1250 85675261 85675267
    0xf0a15050d06140601081311030a02030a03050309060f1308090a23010305010909020604181e0b01020d11030f0a05160503040608010b0307020d030f0207020406030c0612060810090305 80
    0xc0003040140400410881c2c80c00c3e0b42e001c01c2c421600e948180a07070001424600703000340341824000c080009101c948082e100c20041c81d0071410759907082194107092907020b0240c5204504a0602520035001100c00c03400314007030b540c009000910080c1800e80305a1421415005501440e121440385403c00145141c10106e1000041000c0c0c20342c0b400301154004c203204150303149003000001020754406a0007051420b003401c0d00c40005030f9905050b030301034411007003282e9040000068000054105e180c02c9038014541c004c07001180704100d4120001c040400c0e000c6480c0703801040402c4410020040300110140c00070b00200c4623082400009010700300651a1481c240345c02c0c09100c1c0d207d082c5064048074a41d0000408000c6250019401801046002e800c241140f90549020b0345980025202004042d907030100c044400a240c4d0585006980150003000384c15100e1805154104090040c40080785411314800b00c4502180501c0c004d503a045c10181070f0041c1d039003001034050001035100301d050040174 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 85677761 1250 85676511 85676519
    0x70c03050a110601170f06090a0209060114120103061a090105100c020307080609060709060912140f0a1401061208031b0a030b0a090204030f11031c05031e0f0a15 71
    0x70060f0714041c00403448120304803180078002510b0300300051100d1000d80c004d9810490f1141000c05c00601c0c00e501541c0404803562640c0040320180308000f02540d400d00c000c120b41c0b401069401c800c074103991280404015a460500411104030519910580c1c403040d100010320050606000310b6100c003987d0308000340015165030001e802c212180d002a12643d01900800410030707020090940c010609040144209041800c018809000ba010702c041d5070100441d1a0100b00e040d01081c0010f58408060b00c681103042040e0035111b0344584015a4880a010194400302d0381c184242400c40c0d039a01c418440d86141c69481440c00d400c02854020030f040d480001182c4001c414009004840d80380e03071f0024103100c1c1181004031400c401c1d081080324520500050000403150417a80b925181c12146407441c03040c100700000d240a000c000c15220702a0703100c041c1c51030940c019000d14010312030100c1000354a8007030885110748031030850b0440300c0c645010300450790081050303100d03840c000c1101812282007510703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 85679011 1250 85677761 85677763
    0xf020a0b120609011202010206071404051f030f0e0c01080a0f020a1707080c090607110a080c0f0405060907050705010b030717060a05070f030b040612080c070e070c03050a11 76
    0x10000607022020080c80400c801c902d00318031624050840500461107035000b94000035501c450091000d000d10001c402c44202e2070031620107032030040400030032201c2c89040d001084c035030000c2d600c41c0000200342080305c80e0b1640c0099000b981e040c070f407c0d030004011680940d401104c44035009004090340700e50b10103081c120042180010640c20b007541d203850380c0341c1550864040da2440700070001c1c010014104203020034000c1e0141102c0207813404691083d10340080381040a00244145030065105564403c00198800080f07284a0802c204940c13081130f4012650510055840458200b03a116011100240481d0301541c05042c440340510000181440b4100100346000072035001180c0115951240c001c0d250000c004c0c91b94002a40c400a008134108110060080c034070b8007600707105161b16a0801c0103d51a03039802103008010004440c0841e1907a03041c6020660302c41c031041060ba008005000ca413845203450f849010742125501c0075150526a1400c03101500482d0be80b10422688007206035040b14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 85680261 1250 85679011 85679017
    0xd0e010f1818020c25091d0708010605040f0905030304060c0504080102070c17010b0307030224040e0a060b03011202131d1c090501050d09030905030607021006050406050d0f020a0b 79
    0x1960740740c010b941364280e9100383c0c13500d504000040143c0603401420001820038046400440e0070840002c1901c5841d0150300c100601d08111451640c40f81c40000a02608150400b004840c8241ca0804c080e210720861a02920710021000e002588100f000c00c00081031940010341403620303460b001c0d007426102e040a900b6030f8050441640d800140e03500501c1042c82c400007004450382600001c1006c4624103001c02e45500031440064811000380c115000c04244c040084400380c1030110145990f241c4031031169071400c1040d40c290078164070f0440301181e40c011043c02ca0741030350304085101011601d81d9080041e80042c001007508119100e1103070080d01c1040060854408894002501281c440403501c806414040d506007000c02001100400c996604542100d20105c00d080340420004803c0c1400d603a084001da2043d5018800d079002c00c04220790204680c508074841c64010310401c0d545000f00002c1d40c805000381540000340060f40c4000400700c0c4036100b06648007505841803199038040c2011103070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 85681511 1250 85680261 85680299
    0x81c02071a0405120322020111100e070503160902030405010207060e030a120b060d020306041b080f0a2a020a0b100806131e0c0b07140d0e010f18 64
    0x81c1c003040a01c41004000d02840000010052003a815480c2101001c02d050100c0740300607002001010b81841564071070030054580f20400c00c1202c0521702c3c40c3c82d1800041641188601d064000c00d4400b00b0780c0d24000c15100001e0700e02190031607070f07642003a40100080d400074104540a6500304513a13000101c03e80690000e02c0c147d80040c5465000b101c6014101201c82c1e40302c441c0c0c0e5480c0c440540da50390b448805032403850b2403076100141c0381d90325140070500070322050384401040b136079612840101d80c0c1d01403400b51064500419940c89901c60020b6281621074000d10300d01c00150030000300042d40c04000c80048241c540f0310484107801020380f41c080810b6820768001b088824004801d0010711400c1010540101e5030790303044001d02c1c0741c80e1034151030162218a0601e480100c0d01110091141252050000c0e20344444403a0303440005150100340c01d400f020b0340000f1805502e42c50031704c1d07500405140f094000c042c0c5810a442c2c0c2c079003808407107480d181c614a1405002d02040406d88810488980001d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 85682761 1250 85681511 85681553
    0x4030f0c06030c11060703090f0b0901060501260106050723010f0606050c0304060e0607080a03050402040612020d1218080c03010b030d0507080a030603050a0501050103060b0607081c0207 82
    0x1a0070280010b041c3c03030391914000c0c00d0040c43c1d21001030320900014116405080c520b80000c001919107001c2c400d8100b030102c0500b00c110903100f44000300c801903220104031503007600c90405682d11100d00750301c2226508040c0c2600c80440004214280c0148003d00c00c051284465035092900c80301070b0421100f408921040707036956822044d1501c4541d1150f00060701c00d07410b00d80d041650120000d5601d00c1035010303050400c00c3c04100200c05031150015150740c03e610170800c0f03441e01c00a01c40100200740c11201a8413132414004005090303440710303030288504c9401601000003804c2d980c407010f4525003070000d14000c100c190802c9180e400c1c03110300c1920241024101901d0400b20b0541098203403180010298403d0300403a10000180c1d0f000001c0b02c894551102c24103840c1e02d00c82006400500f02c40e4070107002800380c021240c0c00c20070198400d6060700d2142c0000c0200940d85414170145002e400001010040c0410100c00440d464031011130124801c1030303015107002c00a40c0c60b03400541d10f16052000ca = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 85684011 1250 85682761 85682783
    0x180303010b090f0909070e1807140a080d0509010909050601020a02010804080c01090c08060a0204050306150d06051806070207210203010b0d120306090203060616020f0402180111030903030a1404030f 87
    0x5004004403540d0b0042032380e900101c020440e245510b03844085038415420310b021100107812290300c4951801000308040780656114801c42500609594051035285000407080e00002c2a80d46c0e40b4480c540c024203041e8002d1069507125401501d059401401c10b607032050051001d03600c41e0400340a0f0100e030354411a0342043c002d182c00c041a2401902a02800d90300340140f20501264400146266008030480d0002c414040b001000c10300500101201800321410700c010030400107001ca0543c809294503c2c104e400c103540b18142280c95038010300900c600070100740804070040d660380c42e00408e154001000020300c1010000002d83c020007064003101e8050030702d19040149070b010321894008100000055103146488800220300e0301c2041d114081da0514210f07900250b4031404036003816020083c0c411580e540e04612000148081c000c5444d0002d00107402c91100380b10080300751070184402034021400c103d9100015100c181c941180886007036018000080400c0040f140e441c1e20f64001d00d21401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 85685261 1250 85684011 85684019
    0xa0302010516141605070f0311090c090d0c050d06151409070507050120040503010f0212130206070609060f060e07080c090105041a04080105180303010b090f090907 72
    0x1007510001001e012040740da40c605005001d40061030400346502d80781c40d042d40c1c0c503285000d8059502900c50064503a114400c3c02140c0f0100305030701e49059034003c80140040d1841102044103ca004403251585008140840495401c01c01c0c018400c281c821161600d101e03498030003152196501403416190240c0702c1440303030142140b05141d54041c241c02165442c11910302d4000c54030140d000781890302013002c0010f40c0028002c00b075000d003d542440ca2960700c4980c5811600a03c5074015020b158460352a000c1500303505903042c070072268001c0381e00041e0180c660f1010710500c01d0149044080e40c1140c0104805400178010381f0500c181e0f188076000010300c40720a440510200d80303458004184540ca000c003407240301a003246040f45d2000113404004d82d610041ca004803411f0040b079018000490700d106c0a000d01000c074202405c00c0da50004020032071680e840000c0103404c9024100004a42c104000602c0009500c500400c0c0c4550080c00f0341e07518002250100e02e4410085515034050340005030140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 85686511 1250 85685261 85685263
    0xe04140a06081b01050f07020d030206160e03060a0e07050303040b03010906050d0b060d021504171002030403051204020315040f0605010603021c15030b040c080607020111041202010905030304080a0302 88
    0xa0064040b07000146081c0072800d20146408501d44806414001d000c6012401b10700e8403c200e031600c0d64050610b480390f000e2854003030343d11a130684042085028649499030040d01c44c85040400c040c0080c0202aa5141e44c00580010a40a111035295008804000c551038504000601c020022811010ba5940c0341203c0c030300880382c90350400ca228800b601c110b100401c00800703000d50440411520b07050100c00c18400100342c1042d034440185090800300c0d0000e800c44e840041401501110341c2501c0e00074521088000c00c0b40b10444008010403024001b4010820560204941c403c0c8050100e40014843c80300880240c1c0017158100d40f41c920078141c01081026a000d000e004155a08041d82071420340300c240f00e42c0040c00c1100c184400d40c6d550041c3e81e01440c1c03441040041d07030880c107001030324100b034104003529044500543d102d9110f1180031401880c0b0500c40c1004106010b08214242404c26a80e4000401120401c0e41044001040807071159018002071000f012a5001001c90322407a103006 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 85687761 1250 85686511 85686521
    0x2007032a060504080c09060105071e02040507020a0201031d0d081807032003210c03040312020309180402010f081302041d1908030609190c0f09090e0c100e04140a 71
    0x2c1801b03860114140a801d0742c100050780c0c58a68004016100c40e80c4401c18814200d031181e00296209007001c003030005250f0046008440d150003070342e05002544100c0040820a00160381d0802c44e60302c5000c0b904005440b03204000e8008403110140c6580c40420410b042c40c150890f0015a18840c4603803001c0d42c1c49000298a200c441800e8000d449800c904214030400c55041c02411601020300081d982d10b01003051084401450f801440c11014401d40c400c02035807900300d030b84894001ea42441e10a48280041c0c103005103da5816542c06003000c00e030381310460340c104000c2c00c4004810b4000b018100103a4660069004441000d0103581d020820304800c10325102c000c180a01000300c3c40c1c0b079101d001c58584011294801400e43e001c0740251a40c3c00c02c4045c0211000c14001d4480c82c10036805000b66000d0b003902074a013000d0f03171405202a11614101c0440b80c005c541060598010320706018181450042c404400c0581d051643e1058107850200303094607032400040c2d0456040c0d2081117040d000324031074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 85689011 1250 85687761 85687783
    0x10311040606020606090c0d1e0f05070c0f0204022512030606090302030a0f02031204081b18060103051f14150901080705030606070204020406030c2007032a06050408 73
    0x1080780d402c1171004650030203005041804c3c003100c0029030000200e400e400241e45800c1c0e88520649210035182e5181c0208840a03200b00fa00b41490b012a070303800d00c11151520030780d41102038180000c201d80d00308002540724000d110b05088110907408484032020314100c044502690a602ca0b444041d84001d08803881a0022810f02000e04400c1c03000d40c40001c0c60401c841e030300c191905031904140c0002450702480317003030009035004001000709542002181202c41440e1103500c0000848a0700108031242d506590300414074000313070001646641c46908080e0700011942192440000c04818824402102d600208800d03864488481e00c28200846c60440c0d41c215040503900300300d55400001c01c9480c01400135400c016000c0041562992030008031b075003066004104560f100d540d000050060095000c07088082200e0401c1030700b001041c0d590104242c0300e500040c081d202d08503954030015035142844940141c5400b503450280b038400a200c2c9000d04602d03200e05880c0c0b85030414262401100003d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 85690261 1250 85689011 85689013
    0x6030b070c0605071407060207060b03071203020706020d08060913021002030a090b04030f120327020906010903020619020102090315040506100605090d020301181203110306030a06020f1201031104060602 89
    0x9401c0020085c80241d03402c0725071105007d81c0d62001e0b814000060714281d41915454000d40c240081c0c0c40006508842803a4800d40a454442e07039224001c1e07803554100a400400304040070000350941c9000c201c09640035651b0113079040404034a80200c0c003840c01511440c40940c1c40090f101701d80c580c00c83c80c004010300104404a1810b403d55a075442c1c2c100146000800318107038508106d010030300a81003515515171000e80c01000c3c0400c0c07000c44640030751580d0700303074003e00702c00020075029442914407401b038980140001d031038842da02c2440060300d88450790600840d5070a11a4120b2130b035042c8460841801c0f0701c45281d08901b0329081681c01e1950140c645e1f2209400b203174040184540180c00c0c0c81604000321803c0c140d82c00140003181c0034011441040312a28500240307101000420041813140b842581d500300300781c0c0200070158482c0e21099621583c11750004c030b8940002407140d00108049041d0125003030900c145d14140640e41482a00300b00c403503090641c00d0012904251107100e0040503644 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 85691511 1250 85690261 85690277
    0x30a08220c0b03270c010c0c08060a0603060c021606080603030702120d0912150b1302030405160f14150c07120b0a0c3c0e040f02120f040606030b070c060507 69
    0x1c0d041960b8451701450039060210034403500083c4100a090800144090801d8a07030b42d2030001c500340000d0005000442d4008c0c41c3c040003c400500c0000e02580074640207081043d41400c128050760211001000e05030b0500c0704012800050f160014000c404000000040c80106d010480182c00c070712a9400128078414810148400704500c3d545080c002e92000c600010000c01682c08034018417440d080c0c060f07401e4000030034030081041c0007860f200e510084604244190752140020b80a0516510908038055200e602040036172400c007507a080d600c0c6004100504d007014000c1000c3c14807480f5404241e40a202400d11000d100c40c5150295120410080c10400c081c00110b02802c0c0e0703030070b2458041040e22603004a040c0508480c00b0603032a0151046d030300600744040d0f8401041c141c51421124081e900700802c60424149034000e81d28600010b07912450345542c0d0070844080130800030301c15940e654603810000041410064018000c100981c9d0310f11003414907040c40d4041d80c001801000c02c0211003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 85692761 1250 85691511 85691581
    0x9140709050f011e0b030c090a0e061305060f0a230117010303030506030f0303011413020310122135010902070515090303060a08030a08220c0b03 64
    0x200b8043c1500c0100c140006121400c01c010131103075070150401e614081001041c8488120008050011064211200d14025442d03001604007000c0c10b50741190460f07000300c9a01c681c08056000f00c0d5000c1c001900e180f10320f01214000036400e42942d40444100080c0600a001410741701340c0801030b081c02801e0004280003000700c1070800d91030510000c0c6c100355462021460f603a40a014102d0900c0001d0700720b0f910f07035841e0380c040300110030400b101d01e114044000d0400c80e505410300980e40b041c1e01c3e90042441086ca00b1001c4001101d143c0d4007181d52183d040340703845080c1d010807808014450117a076541c1c16800701286000c100d110300622240c5040414a0074402d00c1d0280b110207040d00e00a08000d230300d9205078500107143c40d00b00000100003885600c1000258000040a544104811104150700954036a6101d4136446600c1c13140000a008034000345a10844003428403c00e451211020741880e8281c503200807a00c070340d070041c075542c0100100340060300d081107104000c0501c0072001d00c0b10580c0c40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 85694011 1250 85692761 85692781
    0x60c040806100501050a050c0c0a030b070f0314010311010c08040b090418020a090f020403080705101b0c081b06091e0c0105030103021311030901050405070e010509060910090914070905 81
    0x2e00046c5000c00c00b00054900205030103000061038120003400b45160b454036842c10240c1280200d80c00800243c0c2542c0e804802c034802c0c0200301d500000380b481490540d003580c607841c01c150b00e481076003030601800b4a41a800241010024070090400c094400c2d164581c4404200c00c0d1004045811888042c0120303d0003d6034802c95650101e442002002800c3c040f1501c40102a00407540050f18800d008590141407100100d281031002c6d0b040001000858201190f5040b40d5818100890014003c41318a6002440340c0300206a000180410b41306070360769031381300c0c81d00c0c2c21030856135455281c004006d81d04043c0c002e0709090310005101c00141c000b160007840002e16030f000502c4040e00c9009900121620900c541c2d00030411400d011008607500d280c40c20100d07001c0c4c001a170301114184515040050103507101c1c8041030680c1c1c00146a030519031030b0344041041410005d0010340c0c20017540d01b000a80009030380b04100207980300300300c002030306524940001d003060002c0c2d2081808a040401300070340103203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 85695261 1250 85694011 85694017
    0x21c0503070f031e0203040506070504181e0612020f010201020c030f0d06050a030c060e0a260f07081f05090a0320030a030203041e0510020d0b03060c04080610050105 73
    0x90701e190072480c400149030202c010b001080c1012103490701c81400303412007883c25001544a0760064049807c603440301c990440e0640f0440c800e0101110384400040303c5240d10ba000182003032600c18080305030348070303e0300c01d941210b946501102c80b29450074400c40440c10300710005130f0116400d000031802c000209584a81b2403150202c03015400c1da0015022221002c6580280701400340602810806512454004030040d000d0040c280820380c10030f400b21241c40c04020784004d880c40180111011003195181d5109400d002443e1104d83c02501010426580100310703210017001210300400c00210454000740cc446443c2c60002040e82c14802002103541001541c00b1a41c0e41c14507010904090a88100315100112840c0d01c09034000042d840c00c00c41d625802071401207018407804421081d01d005460b41906800b1001002c2d40c1040603441d0122400390f0241030b00c50503800000c10b50071034000000307060404c211115002010302050600a0540070000c15500180d04101603140908040001c2c1c5180 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 85696511 1250 85695261 85695271
    0x1090309090e071d0f0c0403020a03080f0702030109061a030309030607110a0c06020604060e0f0a020114040801020409021b06070c0213020d0c020c010f0f080a0c02031b060106021c0503 81
    0x41e110500740181d201c081040000802c400040210301402c0264402004d4400f035445107450f03c81d001c080341c00d0700980c0c3c4c02c0301c0c01c0341d60040085080a01c0c55a40c04080c0c0c00072503091002c580140440e4015803021700580c80180d2044500003096155900102030003040c1c280a103000c2d40c0180044c8a842d2030000341c02c1e42281c4581800c8920f401c817200d0079807601000780e200522001c40c8600c001411500001d5583c003492090b003090140e0380d20b40c82c2242c1d5641000000001c01c2d813120719640051b5002c0e90494a007a40903000040c502500c0c0c03210142a68026804062041d074009603100080d480762144410803c41000600590308044000030150008510082d20410041c582c0c60103a007401e41c110f4448003541c140034406d9a600f1100652600c090b8103440303002c11102c01e0120350451103880c002480c40145e450b00d1802d074070789080e048020f1400d809010250b03c82000812140c07065103903071101d401e44c0d01c001807107298100580227040c44d0b16800c13a100c0d561a100103580b40303942c005081e00c0d842 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 85697761 1250 85696511 85696529
    0xe01031403070203030c150703020c0d0807020c041425050403080a030216150e030a090603270b041202010c0806010315030b09010906060e060a2d15020f01090309 71
    0x910300300441030071445a004020741c50f20000905940141c0c2c00f00342010700000c0e000481045542c0c1d44d2054080e441410201c3c000ea0b000000c020841c0c60181d400f040c0c210203948121480e100792240840c0488d0160019104115811010092400b8495401c0f5080035840a60410a104d240c6000783c600e0045000050014a000c2030b043d00c018030030b0f8140c0d60585446100054642a14200110010500746104a080e4180399615030412800400c40d4038007040c0d581c1d1243c2c050300c2d0041c01c40c001d04038250644440c035408650002c9414210fa140305090f4000c2d8080c5407141402d00e8000b80c06c0c1704003007c1ea800e690400420400140c0c009c0e90040d0b0000080c00d001c1124508241940381ca0021500010a10718007035060040c0c0c0c08055021086a51140c10104100360b11081d180310419812511980d004450500a028002c90210178101417038400074440a0540c4160020032180c8031a000302c1c4501c0201034005641c01d5040003010000131814000b0480c403016a20b000b800d840203401001c1c0a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 85699011 1250 85697761 85697783
    0x1e270106170112020a2904090617010b091f0b040b090a090603120c020d05010911120c0a061107150314060d0b06090c0c10050402030c01090605030f0606070602070308010f0605040e0103 81
    0x61b8044003408100c014040303580596265100c042820082000b4059154180c00c10720760003d0b101d4052098002c1401c00030310350394a0303a0790310700d40031440a4a0307904030401c40001200021140d80e284081c10181c50400d024548801c181c3c8180200182264403c905031414144200302040c20051781c950403100a2030035600d80d030018004070755110541c2000511039031800ea1010148103502e030403070010130310840e5120829460f84074900d0392030700ba00c500303590310a0380c0030001c02003180551040300c22010707400c0c140e40307005648281954100c904000890b001c643c40d00301800011856000b403c2d48180c00b03e80401090303859898050341070600a1105000e080303a140130031448100a020384080391400c2c41294034504007200030401500341518203e019101e00c2e010035003158060449207003921140c2d45c1c0c142c2503582c1c1004050790a00c000c0c0099801c82020054000425480c2c0010300b03241d4040e8664a400c2d5151100c0920001c1d010350003202001824030040c010b0720040f02d503d5044070303004070b401c3d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 85700261 1250 85699011 85699049
    0x7090b0d021909030606050402090102060a090c0e0403050403030305010b030c0a031a10120605030111030408071e0308070f08090c01080402040212040b010f051e270106170112020a 79
    0x910844940c4500c502c001c0148001d00c0b40c0c010b03688000d03030f48a91000d1000300e41d12802e1100b07a00034403001c6c80c0942c100e80e00180004c2122f0f8048010309010700d0303000c81c070140c0e564806800781c501910140e0011700300080900c00c1c15058011503005041d0580c44615510304654000c000340112482c500030552184145144505264075038848200d00030410008254045005428050b9801000c85810700303148001907103103030600ca510003011041d48201d1455903543d403464000e500240b41211903107613040400600d1103421200000c007600c81d840b000a02c1c100048040c0c01110400321803010419580104502c040e030125004810750400e0034200c4c0b241e2203510008000c0c0c042d0280200b01c4d40304034000c02c024004004641d5048508140304a001c2c0d40c1c50f2010302c05591100d03129001c020350480f00b00d107154104903510b07249e01d46905003800310102400c0356800d0b440340c0a07031061001590f510410191010300040e920f0050014050505400c00140c1c0403840d450083c0c45811102846549140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 85701511 1250 85700261 85700287
    0x9030206090d0c09061a0f0912070e0103080d2a18170a140303100510030906050c03070311090a090216050106120b0105040e060406020a26070e010807090b 68
    0x44035a5403054002500d41d0701c030032184e4010b0055120f10b0204184100304460402c8150048548100700c40b044036150001c014180f10000c214141c1ca555988121600090039101c0382c1d4141c0e001c0e52159214582d034000100d0b0f200300f0f980780201e000764502869048400d000141c004070b285068906d0800c2955640401105000c00318940e002c0c02c4d1981074402248103005000c15158801071081d0074030a414182002c40c0c50b130700d000032625082c021642500c10b0000740b40c40c403c003508445175483c02040b9840305960710810340c1e5082e1b484005940c4040180a88113415015001203485082096400d00303440400141c00360100d8442c404040d940020100c103a2242c43e02c2c0301c0741003904174000f444951b60703070740140d200b241c0500c0c015940341100c000041141d02c3d10b80549001c09058800a09490b181c5c0e4440340000c2d840b0003413030070511407185038280d880c0320000c0146141003075080030410640307444800030380240c410300c000604002c0f83e81d00f0096001d030415500001e840d03220342c1d40394548950424030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 85702761 1250 85701511 85701529
    0xa0b1305040f020c0f03040509090d12110c01140a0605040b0d0b100302030d0f030c0c051005092508060603010509061f1a09040b06040605040e2203020a14060402010903020609 77
    0x1350254082e0800e51440204000300800c2100d40035201d5121941d10341000e140c85d9801a03420b0000501062003c40c404c00464010000569603040450320307100d146030b009801c5401040c54100f0b0b103103000c1c1c1081007a0b031192040b2002080305450501c081c0c6a1a00010501d440013a802000c0d030300164007240c2000100780d0500c018650240481d9007000d180e11024100d00d0303403150040c0000c3e041c901e001013034501c50590360090395405001040c3c3d1184500c00900603050080c102c0440380b252031205840a50b0350414022804000d4466034502810502c0007810401d0050420303000e40e0403d03090058884000401aa11000c0080f112a5200c050309000000002c01e5202c104221040c440310101da0305000c0c0101030303010342180c080094a98100901c14580620301c80ca8002c10001c0c04104400018070100f50b0740041c684108101080381c071801c1c8416942480c0050b00141e0140381044100100706121010810583c0700501080c50140d000a00708840d07400300900410700410740038081d45510002c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 85704011 1250 85702761 85702777
    0xc070602031f0503070e010303121506030204030605130f02100e030d050301170a05030d0f06050d0f120509032a1002010e101104061803051203060a0b1305040f02 71
    0x1080d0350328100750003960501c89001a020303203440080c1c44001420700d070001c0c1a104507403a01014800c143c3c610b45050318100320348030038485415241c0e08a07140000c50490201c0140c100741d1001030320341c0d046003080012600b00500050002240d2854000400c6407603082501140d030407508040f4150b0311440c00c80b681003100c055290580300d420011100e5a030000007440c160b0f86100c80300d41442b0590b0061583d01c0c2e841c00000382c8160004c11040c0f44010b110303000410030a8004c10082101d5907103402240c4400b440440583c2c8441e5082494800c11400884d901c0d058030583c540241041403280000b42c55107225001000c074500401c141490802c1642c7d0803154910700107180304030819481001070b020380200f00468809001d000c001d80d080d2081d0748112582452224011400c0a05008041c3c1d01ca00100318514407000c000f00c1c000002800810a5403c1c502c610004141c0303d04002d8180041054541c021055061041c072407400d00400b85141d44d01140c3c03080b41c0108188054240c004000d11448407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 85705261 1250 85704011 85704023
    0xa0602130807030b1e0403080c090102070b030a09061d0706051c0504050c010207090e03070212070812090108150f1009080a060b15030f0c031009020301060e0301060e070c06050c07 79
    0x10b00003040c0076013a10b10350b11450155114103140d01842c0e5001d007110f03504503402804584403501080319210984044c02b0102c40600403140d00940302c466078032846d0001c580c41c03140180c41d075844800700b24040c024180196451101480e12035044041035803100e40f00c1c0111400c0000c08640b8481115646040c091008181801040181050305103030313445406e420031060261180c8040094280714a03c140039884810324041c50604006600300541c86600800d00f038894800d000010840003803d01c040d44081041a001d1603a90104038005840814001c002e80c0842c0d0014801140686805044074401401210201400b4001c0312064588813942c0c1c001c402e0a220300200030b0f0030006a0351060b000d00004480c450054018200b00c8984d034030040701d42d02d500c006c206010403003402d0441e0185803c21080e404541c11252980200412030304241d01c01c000080c411031000c03201e820203110301c00180148003002c0b0000e260085000d807140ca0410402440a40e41d88001191421003006032100194004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 85706511 1250 85705261 85705273
    0x209040c0f03140705042306030c040801060e040b0c2206020106050a050904082704140106080a0608060c090f0901030606171c050d02090d14100e0a06021308 69
    0x160300108141d255411080c0880d1074010b112100a603100882c03489800e507941d96030300e842d007800002114459032805089400d289000a2002580d481000e0f61143c0b13280341c26203072907600e4548543d081d10443d41c000d14104440c0414400850380030300081d6400282c203010f4659400c400c8200b900c0d03000c0e0403242030135064840301d0f01040d0298190032040c2114805c0303d104c1103164449003004642d11040c0d0300241641c01c00c108070300301000150a001e40c8080194010000000c107000403406a44124041642c0900043d005109031078001e0b00d55500500c40580410080b4201000703195104009007004803100800b045006090ba900f084151546030701070061101c0d075a4030315052014041c01e000d400191000035525540301c3d20b00280400683e494030446948561a03100e0070303907141c2e001b250b10310100c40d004c000c110380317075100c0a9103007004501c10b00b24480d03054407082c8004e00f041040441d8405103800d010181005400006030303145203e42014005a88000c5071404152420071a448070005000f80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 85707761 1250 85706511 85706531
    0x70f180305030c0f03190e0a0906120b070c0b15060c011b03180b1603091a09010506010c0c0312031b020102343c0c05010309030f0c030201020904 64
    0x12014081c40b008000131a140c0340202140c0c50f40303030300901c54050b800c1501c1e600b843d50341034030940c0c003007aa1002c00342180350030944a5a2450a656481d001101071410000100f02000b5083d151554000403a141103c042d00c1c0c565540310088601511404c0541c5040840f0b450540d500000c0340c0c06840980020411040511185802e8240141d6048042403400c600100031030f10000c910400389034014442d50036941c4145500b506415444030035010195140b2040c400299603c03000c5001d071501104464052030085851030941e030000341079604004008510900094a0020304420303a6801000803c0340042060301f1402410000140d40c030100b2124140c84220350190300034180c04420262404840800000514030030035030720383c610b660a0b195880c0d1800310304046a00c11300c02d292910300c5102010710301800d1703400d514a0803298400c8150360300218100121100e0500003000300382030500080c1e20b81d89001d410201201c410b0010b1003282880d4a003007620030b41c11a0440c00006208020008030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 85709011 1250 85707761 85707763
    0x180307090c08161403011e0b0d09050d11070e0405010e01051e01050406030b190605030f07091406030604030f0c020904031101050a0e1b010c060906021c0b0306070f180305 75
    0x1076403c2c01110110b41c540244003841105540103a40380051001e24513482c2c030700b2481043c5071154028600780641e080200b011101d100040c2407800d074903600400d440406090007400c01040580c40d40900040c062154010000030030313800b0403110440002d50303075075441e4148140500382803400022035500e00720400c442a850702c030408051f010340b86142c1c0034517a02e90701404211180d078000070749001000000114840d8131210b61807840310000c2070108181e40d0741c00100746480c401c1c414401c030a403c560070a1214540c240316564500d230550740c4e8403080b400c1240100e81c5901c000340c0007070108000000c9010b40c0c28010b4000c2800217502400311006031a181c02c0040508840c4c50100c1d41300d5003480d01140d400c03501401800c602e450504082e03c200604450009070411000013090b0502804080c400d0100d1381a1240c00c41140c002c0c07501507a240d40254911000c0816034503882d2180d131516441c00c0007901c000407202d5006d042c03402c2200003000842000c1d908500702030991070f1901c06000020041206c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 85710261 1250 85709011 85709027
    0xc0304030c1205120c07210b0f090d030b1c0206160809010f08040515130c080303060a05030712080f0910020d030c1d0d11030601230a0b180307090c 65
    0x3000380c1c213841c0d206044c01400c030414800c240004499600165051105403800188110b0b0007035140344440305501280d8401c1c2d4010130894420030302c180080308001035003c0a200800300c42d0741515042000d01c28900001c3c66069910540b0b100d1b070400d052040c800c5450380390031220030200d07601402605071002d14003607005500400500b1300040d4410b486008444c0196007460113240d01001510341001c5884001d6004c1c80300801c82b04100508031111004038060300700101c051b01b84e010107503070340346000c500384043c0c82a03640c0060b000e64810581000b1821040b021640c44a5000b020030f44c0e80c14854404004501449003641d0741301c0c0104405c442040c4d00001c1103541c2e00b0341d42d1420310199020303000994004100140c5c0314028055510b046006140406004403124461958002c000b28580701292602d0b03000d0b04130010005002c407044102c0f001d40702c05418161002c40301010401e08081805030a80070f101181f0304041c11101484a59507000d002c500b01400b01c440041021080b0981c004001c12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 85711511 1250 85710261 85710263
    0xb0c010203061801081009051204080a021c0506070c020d060f0203040c0b0f09010c050a0b011710020313030309020d0618020901090209060901110a02060301090603030807031e020c0304030c12 84
    0x201d8410f004003100e4005a040f20b048030a282c010300b42034030072502400003030320940104864038000c1008406806000c90090310290401700300030010f0b55960320501a01c644915040d08a8801202135a400a580016a0782d031100c000d143c4108807009a2000c6207030741c09800c4008201a0600210809440307895001d14440c500551019040303a075681080a807500c900200c018250a0800400d5600d502940c10b801d1018403e10440d007001c0d203079488110240e0021f805c580110ec1d803103103a040c00f030081040141c2d07065842c84811031542c14000036018410b0050940201811b865071813240640d6581442404480c0d0861010b1020481c41e400c4509030701c2400b2000c07440b40034088004109210213100350342040001a1416140410003030040d582c809441c80c9107002441020031180050b141c4401550081c8000b41c4049040e07401c51401600300e4400400c0d2204040c60300c00804462080000c20100c0b04810110041e07445030940c18076801c5204a820142c040c4103171000c000b40c00300d00301e14088506 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 85712761 1250 85711511 85711519
    0x1171f0f0b0a030b070e0d06020c0705031204290c011a0307090b0d1b03120c020406090b090103060213230913031e09180b0f06070201081f0b0c01020306 67
    0x226540c107082091000140c00b0190001500c3c00000f4035142c00780e2403110241c0300040c6001907000c00c2d6900d103010b83e80007210034460780c4c211800410007810100b122000b01803601c040c2d0f90405003000700301d250000305c05100010320515098a101041e0180303048440b0b41010400a00c40e03100c9040c590303e520150502580d001c0e100702c001c00510001c1c1d5101e0b8000340d40e40100000c40040040e200c0300301d21000411280340581c501c04001001590b1201c92104074201501c480d03000e07a03075134010001107030826030180c034440c3d0420056078010350f10f40c010342c1d054a60060005807101c040c5980303a1a0300390705c4d0700200c015a0542c040100c9100008401e4140309004850103030f801e56030341c1d11030006216820002000724403030b607580220a4120b0801d5035240180e9141092031182c1d43d914048407100003109408295588070035281d039500f00907a0749201c03c14240c403018035002c440d6000070600c41c0028101880c240442c1c000f44503186007262254020440380307426540b0b901a041c8180e0003035106894252003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 85714011 1250 85712761 85712771
    0x7080c0d020c04061d250c1106030c071203060909080301030c0602010b01020307061109061206090f0910021612090806090604020a060f02010b040e07030311031201171f0f 75
    0x20380f81c240908001e07607401806130803d030300c148805e018403140e010380b1064000c1c50409804c084000600071450300d5161659421403152124204068407003a00c8034080d0165108004018107821154100c3c3c903c0c40d0310450380c8080c090704a00c200d00030312154100d402d902e41000040c0e41030117080405181600e0141d00c0d039800c010366610f0246d0072103034012542400f40e00140802c0d404210203910002c422218041083d16001e00d490000b2f015070700084d8001c1062880c8001c1c010182070105505600c803424040384d450303505140c000c0340d03903072041121280c18064000410703442d003550300c1000c1ca03d07030307a841640d100340e04515204c05400f5100320b001c0c1d015144129030000d0882d92002510740c0c05560050700c0b40b01114103010003110f00c0600390f1091020347d0b40701c542c6003074161220300c40c07000344000e000c010348103190031854020108008205154566030050189411500c03100da50340341160564440c18103410485c1002c981011642001c5000b501c64860b000000c82e1507540203842556940d40c01000307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 85715261 1250 85714011 85714033
    0x506060d0c05060304060905060a0516080402091906080304030b04031101090201080606030a021204050d0306050406030b01050409051c1e0c030819110d0204051503010308030f060607080c0d02 84
    0x208140304003a010303040c0c8000140810250500700d0007150014081d500c041400440e980381c0c039183c020155000c0e900c490f030b1842000300114800d00480c00384940d5142503a0b0380d007800e400258401f02c02401c2c40000d101c4101d0a24052101540400000d050080643e600c0d55030343d090441c078448084400341c0102d882e1900c3e0340306090040c82092019130b0b058648800580f04e20003480419000101540001e50b401c00c0300070301c0e8951004c0051302c0303a8810001002d5903400750500074256085075006034040c0d801c143c0e050001900825405054071001e440010381d827105810921b180210300198001c5a0b2890b020501c0f41c650b000c00d50142200458070300c081c0f0b0910b1040100c1c1c03d210f1002000d400121801c0114940800003500116442d00340341011402d5003201901da0000e83c081d10b88031070841d030300180030001400c00c0d8200803202003541460758295803440c1c940782d00d1f80c80010060301100104000043c0c090f6260810f503061650450360450302c95801100c07440e030710804680c4400c00751043d008000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 85716511 1250 85715261 85715269
    0x708030904180b010e070905180105011206140409050114010f0503011b02060403080601180e04150e1b03011104030503070b060f0f2707020d09140d03050715060b07050606 75
    0x3440256000c00e46080f00d80c0780042045200b41c000c0c010500b00300840200145541c1da6403071541120341c61902201880d4541400900050b20065408011904202041200032004405e524124005580104a10701d5914000d03004254110117186190560000031070001140b5052606444094000b00440b403080c450a80b1900903298a180060b8007241c00180000d204030541c0fa00701e030040c1010040554544000400e0103280d4110201c1031000504000900441e005030794031500340e0590812000a0400c00e568490b481c00380140018069000f05210b140c500b5440804110401e4030b686403910744a180a030384907440a40151030418007200464a2807a04ac40c05034103100000300350b080c1c0b12035508103012441c05000580c0d0003454201c4c801d56514a00700110903c11a03d80e800751094a18054014086240e0740d009402412200310000009440e13012661450300d4050071304680b940f481f880e05032001d03c400c00c50030424038241040000c085d45d1100107003001512072003d845407aa5048144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 85717761 1250 85716511 85716551
    0x20d021203060d05150702010e15090a030f09080607031a030c060414010519090f1e060503090c040e070501030b011b0209090a050109030e0a0b0a0f031104080708030904 74
    0x3612000400c20100b0035500e020198012032502c00d900380e807044281c0c06103640e0001d90441c2c5040240c0d46442c600c0c030064005100b515521341001000d140b4504242810a0340d4903000c9000905100302c07400e03081112406903000500400b102c00480e401403501c0030004018081090120b200000b11800e000c0e20352070042290002010058001420240b4000d2850074160f01d40003160f0500c070041029214034021812000151007007a1503d80d401480c0c85020605030300d00341e0124942d440f0740ea4248032600f00e03050b0100100c03027a51800c10745070b480e4600074a0928441c0006543e0141c82c0004188000602050104c1256002d07201040007400b0100159240400310520310300380c92171500700700c0042c5840c0864030f40045003042110001c1d801981c8050841c2c058200c160f0106d03460318401929807505020003000f8003032199502d070401c040311a0161000c0c40d165100341c10305803119003c0101401c01030a86000b8000b0104454084d80c4c1c0700c03017140d16a80001d001e80c0c062418005041d0100b0407602807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 85719011 1250 85717761 85717783
    0x90302030901111506060d0e060406020909010509010e0406020325022118090915011211040c02030a08090f0a23030405031f060302100527010c0f05070e09030307020d02 74
    0x1301800c550360202000481d0b8412450120210798501d140c501c108820000701307200f00e00c280300040e5242d64207420003245880590101d4401c651200041c07000302c041043d0306070400d5025801503100e4603400c0b0742000a10300d03810110f10322140800003c409560010701c1105580c0c41d1000d40d0720035900344101407041c2c07003850b40c11405e1090000c2d020080c3e003030004845500894100c16101184442c030161a1422020b911002c0c1c002961a8180184982d5031510441000103e6003003145002c480b501075100d010701003120091004260004840c40c9051008400c10030b140000d6901303034916031405807500349a8088035040440c0140720200010800800c840039075000400a04862900c50503880c0d803000d0100300c002c0c3d05502c0d0030300040140c8410f600300500c81c0c6180c450b81e8550718445035001038130141d02980701000007102d00446a5076040204403a000d40c004042030113100c01030030312900c2c002c42d60740702921810011013002801503001c00658040c0c44d41d5801c0c1e4940d9400020101c2c0c1d20507074050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 85720261 1250 85719011 85719043
    0x307090503061b0c01020c07030c060201060503010204030f0b07020708061602060903130b130906150206071403010b0f0c030304030e100305070801210f05011a0a0f0509060d0609030203090111 84
    0x34040b418586404044c15102d944540003503e04181c603010b15041213030319441103c030000044014000d940d028090700001e07200640013141024916101c414068114010160450005a0118811520910004005d8001d5004440d000d0604041c1208400d0464065500500032079004c40c00d085c00200884440540c40d280c2c42400c5c07030520882001940c00941c1c0240c00c0c4040510010b0340c514507014400c001c00f11001e110040d1a0051030190808000a00b150204459540d4040b9201d138400c0039281520010b1803400c0d1070300c0395804111228410b500c200c194078400171041008240c0d0020f40341d9050070381542e9a03030340380310560829000e070742040d9070000109198100600c00d1070001c0505009940c0200c0d211058a02c80d510350f409028803001c42074806035103400100040d0301030402503640b4194213170b40c901d000324500344e0212042c0c030145c06603503c034040100114030036075030712a16274a41030740000c4100322200c024500a0750b03940c4040c1382940481d00c110703650740c0840d074042542c0041014440c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 85721511 1250 85720261 85720291
    0x9030a0b01061d150d1503150f0b010c0c1701020405060301080a0501110c060109111b0c010224011e05030d05030603010b040209030c010e03011d0a11030304031703090c040f02030709050306 83
    0x40c903214042c00c060b0151042c14001e01c6e40c000003055202c0559102510305010000301c182e940118541030300c5801074840e06000381941071000148102d03141d007048482c80350170030707170f1500c1001c0c001c82c060f219a030b22040e48500003100120b9040303c0032580420f13452160008200d03203504d15911051030b000c2c2801203c0d03182c00c444010003040c1200d8000c080f1039106d42051074031300741c4c6d000c0f0203054001c14020b4a441030b90102d80200f10300d5130100481d1072080c010303400c8580a0035031040c0d01d00c040c40050044445400b0074101040b80500c0400c0c80d40064440203044c2c88184144807001031050f00304561040c4a9820f041c441c5169085c20310841c0c05001c0e014001c0c007080c1e428003005580400756001d902c1d8056580344549018481e071a900c0100c2d405a1394091b2014542600f8000034004082075402d1082c2c1003000100000351840c0012150790105108264595407004007203400c01e0461a0380750b03006400c2c2544020b1050711035009520485441d141d0b144265201d005040d07450350f0031100b81c41c140c101c41c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 85722761 1250 85721511 85721527
    0xb1009030206160203010209060d021b0c060a0e0d050703030c0b010f2114060a06140301060f0e04030504150c140601031e0203030d11030f0714090609030a0b01061d15 73
    0xf10401c0e12a01d0b0025002500c2c04c982c00000c5103040c0d120a0360010b5150340415101c005240f1801d68100868400000386a414807100c00115180b040c030383d07050103008105480c48070b1070300c1e0307840a072902941120984681a5980c1805809d889540008464050500001051140c1107684400c2942d44131100c10342c0720100c00700d000c5174040c1040b000391501c0324894444600c00030308100310ba126107042c1ca0082452882c00a0100041302020301d801c0c8a641052824071102c250021100c0854014103024401901c0d941070075200361145402010350410b990403e0024a50000d1004280c2440ba46d03000007112103070500d0f692610350030b0000400700f00c417001c050f0000d144a84480d0f22600d00003000c0d6890982400b0003802205e41784400c031540010b0100c10032050341102212181d021400e414070001d00007a01c00a843c4501c114804030f403040030040350380c0419403020001d107803032283d01c403000e2815541c444a0143c041803110405807038a07a0741c10003000b024140074480e40da4111500c0c20079810150340f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 85724011 1250 85722761 85722787
    0xb220305030403021005090f010b040504080313020112110a090b0c0a020613050904150510060906260a06080705061813090b040b0609060d030c0b04030e06040303030b1009030206 78
    0x4042c005400f18411a0000400c452051043d0390064000728010700003500f15040981c00d46a4544040380714502e001c00704408502c6d9007003200d40c80210480c00140200041c401aa010f0804c04401601e4034074056800c50740c1c03c0b443c4001c0c1b0140c4501d03125402c400f5610440c440c1d00b40301350b2000d0000c0e0b4208204c440300604094000e0000c40c8500e262480603107407100c0205916000488040d940030a0340340c500b1880340058802d10380c004400003032904c456810100094a980428840c0100300403251500202407200032004a17040d400407e80ca00f0107061604003603001d442c050191600c41d0007451070000f4a40b07020340840d14501160f03407048941110000c10040c0c0500ca0100d54410284c55101c058006003a000c1803e2049204101e0030040d4102203051010b0400c0c014560b5010300c3c15160395001203038106240442c0b0741d80c4405e41d2403140d55940360446031000400320990b00400c2c041004010160035401801d680e82d4261089030041500800890748190b091002030f4002034204843d003c072090b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 85725261 1250 85724011 85724017
    0x90f0204020d02281d1f0e03150a1505030618030702060304030c0507080313060e04090506070518091b09012a0213050f16110703030806030c01021b0112110d0203040b220305 76
    0x801030806420355048200405d040101c2150a4001d8042480412012200b180f050040003000c0c0e8460007802401c20cc0072940d21100507143c010f41c2004070b401d06440c8041042100c45603503014100702c3c0c6a0400b440c000d0290503002c1c9c401c50701c03401543d0005c12900000000e0b41c2d6682028204580ca80c5d2801100741c4244003980c0c262904540c8500c12400030910810030540110595643d480d0760700344107040c002041544240041c404c001440c1849810404148030603180110100c41c0e03a940c8030050010b0300d1602d90303041c0c000c0b5102401d03d2800030f0007542c0d044001c0003d00a881c1158185440c102203011508101e9003184455200408505a000b108820003072840017403e00e10600d00c80e60140500d0501161720850004450f802040102e0a0600901808140a00081804060461f01088054440c2ca6498100040302c00c06000210098004101000366000d4031550760b00b089500d80080d5000f00c805407071000402010a200714569540142506180c841c1d041000b002e6681c121443e078 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 85726511 1250 85725261 85725319
    0x1020601090b030c03010507020610170a1e02100305011502070509070c03020708030301080307020a060c0201080606030c07060203040605071803030801180f1d010e01090f0204020d02281d 82
    0x845050f90b03039134890b1000d02c9198043c0d41c054004000911300503807125418945904042c40300d408a80741d65003ca4400151040110380c041c2c0300070410034002d81524806112218065442038043c7c0c07c1103503040d0541d1117a8140e90f4000c0042c0790317480102c1c90a036901c0c43d05111300d5420010180c0050f51817407048a0707144201e0312030f2069451260391041481d142d50000e030040b13200c50b000011454114a0201129401030285003000241d4981da0340000e07200704401001d95002d0703000040042c18102da036604484130180c0c02130f030454690401c0d00701103000309021209003000c41c0d500c034009500700b0b2101c0c00c400e04599050756681d06c1c681c249159540540b80d01c0c0800c03848540c80708030601450616004816100c0f0121800005c1e48806141490a458000b44c441310303c1c0c1d250400c1d450128410180d41541c01c0e40641740903035a61541820f00d0b000303200b00080b008101c00800c080480911442c03e050340300310312070307940c001345140c148440703010301a000044a40d10050201d411443d092808480340307006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 85727761 1250 85726511 85726513
    0x12060c030b0a03030f1b151a060705060105040f060506040b070201050d060b030702070b130504110909040f0501050705160609020409020604061106010b0a020703020910120602180f01020601090b03 86
    0x558040008140315110303d410807030101d400704905032107080e40083c0c032110f04201030319168002c03600e5498018018009240b89281192941c3d468007880c900d5202c2c00c03003003000c0501180ea841205003070161311600c082c09084d1040781044101c0580c8a080c2c0200000d40ba80142000c0c0307000d1420311501650b07800008120f051200900180c0e8241c03040f48130382c0c1d000b04460f5400503078902d81200c000341070031a00c2d084900315030002d0094440d00c84038035484106544045c3c60018590070310704107618590051442c05540103412004210801421390203140f1190300c104000e01894444030700989142c090a000f02e0602345e144c0740100c000c940a034002400840c0041d00000344208640c01041d25a4456001803002c11141c0c55001881d4404101050040040c094114140805440000d4607074003503100191080000341c01007460038a00304113880c01458a50a4550500c4145c5801c9010350414242002d4051340d5000d09106408c0006c0e00e1004544164040c00040e0300304440b41c0c3c02001552881c1da01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 85729011 1250 85727761 85727771
    0x90f0510081f0b03180106060206060d0f0803090703120801050102060406091a041415040503090907020f030a0f0e06090d080f040b030a0f0c020f0307031b020415030b0a0612060c03 79
    0x203540d1034680d80d0740030f00b0144101554a1a05211804152030300c81d100c50f195078074081d810042c29a020407982d4204004071610034840d0410300b41030702e003510000c20180003540000706011a41700005503840840c1d214240c400281e00300c101080c3d440d54001d00c5900d02503003000000400048081d03001c00d850030f101d02120307141c64090f6000032070707990002ca03411a2402c0c40c1c00340000075540100428042c2222404240f11360340340c40e541d143d4482c094102d08900540740403011401c0e550080c04001200102d80301204c1d115068204020145059403060102144174440c00b20307a242456002c50355204000b404003040701801c0d039640002c543c440403142c11050814800440c0292807480198014014482c020801c0c5088000c60300880d04811203103010741d0700c05160905a0351010050340d2845405003002d00380c164905060001d0498031410081d4010b16254000c4c200c40c0280701480c083d00d0060707124030596914001c010303040701e505000344083e10304682d10070400200580c02070100c0000398580491 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 85730261 1250 85729011 85729051
    0xe0108130f030201090c140607120903020306070216060e0906010c0303020f0a0801050a060302121915030506150a05031510050a03050a032d030911061306090f051008 73
    0x720394003204600b200103035181d4031584180007000f07100341c000d404640780f002c558030030000000b0320310702c503607580204152039449070130207250b0165492100550b0042c0c2941d07210300e01118001c2d16000003c511a21a0400c4580800e02612541c40d00044d1640030f8000a004d45480340151014448241c04608054007000200c8185210102520031407441c3c1e203602c242541030200304900766040c0d40015003050700c10301c500760001c51702420f201d401403143c1038000040b43c036201c1044042d0602c60b140030b500d40c209ca107000040050006066200d038040f545030000302d45c200410020307115a1480340c1681548804116203c0304094580940c020158000400586641e43c01142d8410103540c81500c441e0000c030400c40501d0f401c8511481440e030404031100d0b400340ca040005648040413085e103410140d071a90343d0b40c1002440001101d91042c0142080d44411b40d0b1701e4403002441c01800380c0000169480130000d45c08502c444001f003900c0d4018407400031200380e2141181d5080c8014030301e042441409280c14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 85731511 1250 85730261 85730273
    0x1b0c020d0c090c050901020f03030606070312200309010506100816120908070b0a05010b030a1d1614090c03010b030c1b0c04050708040b070e0303091c030905060a0e010813 75
    0x5500d015160725015245c101c1d45001a06041424803024190b030010070402c07400b555100c046501c00b650500f400b0014406803074138a03004000c540c040c054151816101c040041070424040d46c800c1031058020b01103551000240061200c2881c400d201141032440800d00691391034480b04480c61303040c601034200081c500d80c80070a07100d2081054611000006016042c8a0607081d4550320944900051055500d0440c40c03800610006204800695603070744100003026100d00ca0199503403121040b100c94910142c43c2e64005c0d44a4411405180c0c1075541d5070345075050102196206010340401241580e1030112007018940c40145000e01100c0308000485041e0501481c2017000300c000c500500d80207010707205100444a014100d4010f1204c94820080040d00c8410403e60000b00f43c980300009201c0700d00400e146020b0914919401248584084a070484140c18403900b5402942c8100383d0a8ad2601030000501c14000d40000060090000100319400703aa070072a04a6002444910303203103c0c9032503131 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 85732761 1250 85731511 85731521
    0xa0519050909101410060516030f031103040b010e010503010c05070f05070803130e13050a060908040902160c0b0906030703050907090e0c01030e030f07030309060b0303030f01030302011b0c020d0c09 87
    0x30a8480b0008024060645405d61450000d032035581491840c0c9643c2c03070007280c01e24a0200000b8200401400c841c800f4510075005854070301702807802a5101d0405281c030348a440c409000708000c181c01c040000510f4681401103038102103043d19480d242c0241d50321810b210134507400301075a503445112030000702c400c0104014261050380035071641109040c1b040001140c00080c1001080c408980703200c0c0040b800124820f049550301050020b0303214490b01d0310002e00d001e244c3c0901003c40c401310305070040540740303c10108120b110f48002c2c042152250602c100078040c201417650400b07c180f0016100f54040d070301654020040500700d5800b07540d982c0a06064424842903d6104d802c042c0200c8115605402010009000c0201842c05d1180704d0319180e000703001d110006070400d0749541c541c0c8180401c030b50185141c0d40b0041c0030f9a40ea4a081d110000316110f085c4000c900540c40d11258580c0700d00040300c8480d40040da036407000001e00c819020030410f500035003803d541c00c060005001401401070f12070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 85734011 1250 85732761 85732781
    0x3060504020303090916020d0207050f01050c2a09010807061b08040308070609060b0108010b0d020a030f140115110705060a02010b03010c08271002030c0c0109050c0a051905090910 79
    0x4130400403000d25170003820008c06050000a551002034240156501c080c0b80108019083c64001d0300c410328455060b01e0030f001c6481d0030311030a01e5500044042c0000c0300c2d0f90b00201005540500d0981d90341d64440707950310154441c00c0000b410044024800c42e40c03040180c1c109602600d0480e040c02e0300d0b43c80d40010750f1321040d8202c959039034840019040084c1805040f410b2042400c06181c0c540c50071a107141103110f0481f0150301543d000800c0d050301c0740290b10000c03c002c1072002c01c00c03400a50000321b00402c94280150300e2550f03080c000ea25440c601c170303940c5802100c980380003810b2083c2c941010300c0703801e0300203840030015952100c0100702691024862080d1009a9940344600c1d801d00344e440140c8a00c50400b080c03078944a040c045402d440300003450303138142002c40303000503581e655240000036a8003030140311030441e500b0040054244880007441d68034944048070805504c03035840040040508070003200201c2c0c0043d05c00100014a07001001583c40013204044c3c4e80b0140340e081d4108222500012 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 85735261 1250 85734011 85734031
    0xd0207050904080703260f060d02030d110a1a040c1a040303050f0d0207060c0806060c21070503040902090f180604050703020d020d02030a110406140a200606040e070f030605040203030909 82
    0x30032920b541ea1f50600381d0400e0040da44c07082007145680110f620790080049480074811840800f281040041040c10129030f04080f045001c40340d4405c24545210041c1d600340d446075280400804c5038044140c1c0c0008441c40b10f2140c9241a02d507960030741d91504800500301d1031140130700041107075103070600090660070302c20000080e030010243e00c05070800c82c3c041c1c48940200800d0220401c4100700140d6004050408510b5400c60140320408070100d02c2400740c020298040810000b80c0101c0c1a0050718814008645d41d02c007141c4501e042c0f003215801021f1500da240d80010100300f043c1401d40c80706402040511b400341c07500450175680d170240c1e0b10900c0b84201c001c1c0c0c008100a0160024450800324070481218149040d1402c0b2008200681c440c088520a240c0050003c002c5800303840200040d001501c0e02c4200d61808000b400d480b10403c4070228050742c00c001d0307100794201d00402c0003001d0314002c180044405081d500d0365801400300802c100d070940320401c03e0b40d4450303641610b0b1501c42c2e01064 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 85736511 1250 85735261 85735337
    0x7170712060b07020a060e010e06070c0803070503041a16060b010c020a0f05010e040605060304120e03060f07020f060106120b040f0504050c0109090203040c051c02040501080f0d0207050904080703 86
    0x210500542900c5ca5004000f046401c00c1080e050f42e0380031100805007141210380c1511242c050815820100d40351f07110369803901c800030385176041105c040041c01c216030401d4078a20341c101404289070701d18412014403145c003c070120220800128944e104c039140308010700d400e01900e0080d03030215240120981110506a174401001c00580d0ba00c186c81c0210741c40c003903030140243c900d4080441c05900014000070202980d001c030a200e2a449030701e2418403000d0040803101c60b4100482c80b46c540d03200540341100140200b076284104410b0001e000f6040381d445585201004001281490050800007002035000d86c41e00100120f9480d1409070602450050004d8850750502400140140030760354490400b545c0140100808030f43c14444020444109071400d24000842c40c07902c042c01802d4130f00003035005150000100ba0b40c031000807043c480e0020306081324480b104510050f40e44640a00c90503500a451307900040c002107985002d444168403d081590841c0b00380500c140d42e100c140504c011040700c0300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 85737761 1250 85736511 85736513
    0x309010b06190c05030d0908130909030e0405090708010e062703031b04080d02010504061d0604020d03020f0f0d0201060b04050d140f0d030209030607030507170712060b07 75
    0x80c410445440c0040703032910314012a40010306001ca20119010b0180681c0ba201201030150603c2110341104a43e2401c10414445191410341a00410298596071583c000c1c0411082418441c20101642581303031800840c40880801014200013040b90000740501c600000d03c2c00424015400800581c3c0c000d89410300e80103617010355104010079038080282c030341004180181008400c40b60000031902c600d0343c64210001c0c50401038420343d0f00c00d8040344940c4000d0581c4a60662016014520421341440401d0301c690710b504c0d0b0100002c00003c1d45070040700101c0c00500e03000c250000343c0340c480d00540b80c0b803184512409003072064401500f40e0303d8000440380c0030740650a105800c09440ca06401c0c500381800c19001c0303070139001840340081155000a6030003900410030460200005500002ca48410300c45942c018041c2d01302d000a85d00034810355000c110134070300902a6500c900c04d9a0f50b40c50360a402e00c034a441000c00c0140204003403000504020318581e80c90701442000c0e10000d54555550415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 85739011 1250 85737761 85737763
    0x312110c010b010f09030809030304120f0506071107050402031e01030f030e0604060e090712020c0a0b0c160b0408120403050c1b0906010e01020304091a1002120306010c1b0801020309 80
    0x40b4040d030034100300c80f42d07120743d006641040640c41904e81080c0d42c01d45a40f45800420310758840c0b82c116100302350794181158200070075074106060700741c8103c051f03851076250b07000b094624210000340c06555801101040c40181000e5014507806881010b88c1d0f021252400c200d02d60b0b500e801e030402c0d962940b6480091040c1038100d4941c440440e4284d441e2860180380550060112009480481c450380015011641d0540b28a001c1d0004a002201c2150b07905880300300c05071366404d001021901110846c0001c2c2c0c0c2414440c096400740c0f1000781106003144070640d03403809a0303900188111000d18060140031505029541024441c1e4801c1d00c0ba01d540c4e00456101900c4e0000207101c010050310401001c81710394441c2c9201d07a030400020b080c0951862018030040c0d056000f40c0e007194140314075003000e00361540148000f00b42840f50a89880004030003401d003c9031121018510364542d03080400100c0d02179407240034000d8645003d28004e425800550482c0c24001121354081c0840340c2d0080180007010700 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 85740261 1250 85739011 85739021
    0x5010b040f0b01021902031b12010507120605010309050601060507080403080301030f0308061e0f060c0f010b010f020a05070b07020d0501020a020f07080a0506060d141c260f040312110c01 82
    0xc1d2141817028055070301c2c0d0000b903950810881100300800481c4290003591207036012590311142200080c000d910b0b0018008120707880b0402c0c0464514104080001e4070350281c45841c2040c1d40007000790150303a0a20f4030070399899102107000c0b658903008000000102d0f0042e00a103020718030480d04182d1a144604005040010280c0058803900b0a15039080c2c610245007051034911105544143d0281420000918240a010340001c2c180c01100d01e50b807562041035029561000c4240c94105800520050880e03580c0d409000081803507000080c18807100b440c1d040601010b6200809180320114030740e0b0f690303081e80c002401040c090380c810240000c03204801c1c0698000391040030000c0c40140784a8480658402018243e207000e106c80c84450b600340951001140c1c4500a203000305c6920301e4804002689504266100c1000520044c0202a0020203142100c20070301c8200207003440c5072180b4504000c0d000c0058030032028070003160841600ca5295000c1d9020b07103445892203540b40d442440d00142591 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 85741511 1250 85740261 85740283
    0x604060c060f0e03072301060602061812040e0901060504060305010203180c03030708210c0a0f090608071d090c0409051006140c121902100c091205010b040f0b0102 72
    0x250400c4030700c041c500400070070b81712880e40001c44001c10350360648100702c07a10140c25015201d9420710b9000303d825a000510a4003400c80d0592149205031220359294403080c213803c00f503001000410041011203829100303144c000c041d4000000b00b06a960b00001c003110354076130007180d483e5000f2041000796690821201828110040030b003030f05d070401d403000a4403449003a80c01400c6210100d207440698441c26a807040803605605401c41509140a4880b017540001e1200d01c002903601d090061318522a40300030f41100e400b512000c8203a2034542040e100d081022040c004440648081c0c03207a03e58641c80000e0050325903640d42a661403d110b402c105885000b0b0130310695001881c401c11901d0f6002c0300d4180c0c1d8030315004d02680c40d40340c070842c0e050401a5042d403c100b4260301040103100140c1c06504149800010b8003103940300804104208191040d49029001040800301e0400c070500fa003d0160001a1040e000040c00c04691000101240d070003505102481d5505c04601c052940c0412121801c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 85742761 1250 85741511 85741541
    0xc0905090a0b030c010c08070f030e0909032d0c101a0609030d030e1f020a080108010b0f1909020d06080d080123040209060a0c111005030c180604060c06 67
    0x407425003070101c0d0340d5131048010706040060868900d4144040034051b1140f281d0700500c201c403286140e0034002c240d0044801058800c80c0c1180c042803044500204a03080c041e01d43d940030011000442e00180c1f1000030b1010505150340c1080b00003400c007000d0001c040d40034151f910020390700e2881e8014407188101d004000340501000c001c036590a640000d039500b440551707441d0105180c01040311460074034140801c0760f06002c40d2400c502100c1c0e1301d1900a0001c40f01140d4803017899030b990341e2070f050982d01c0d40303049103400a101111007803442c180760300241c0810940450000c0942c1c0e680d0284412680240142c1045c075544180602c21582c040c0200780c00c2004900d08641c481d41020559061030014031411032052012003500000e030784544d010f035004598010005600c0d41c501d0302e4050800071407261708a815080d04100d940320303460709001c00301c600d000316903603541143e81b03e4200d44401d5210308075001c403c0e61342541c000d40c16690400100044d190036a00c4034840c0c0803914000056035400046030800e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 85744011 1250 85742761 85742771
    0xa1b020d02070b0901090e040302100513030503040609020f12030304150203060604150309020d0809041104140607050a020d050714010201020715090204090b09150a05060603010501080702100c0905090a 88
    0xc19500252200035a0340c8001180c0d07440f00f0000060303850070038070307408802d13100c00d004200410326402141181800445580900031035841c03078569020311038540c00003408070310103001140108006611816003644090014000420600c001801d498000340f14840b440d0b1000082000300151682c02850081c1c80980960650030100700007084c5000e2400354040032b9040707a80b22010f4500c82e800928071150007800600740c40040d400c00c543c06a111040460203181442c2d4041c104030000c400302c13011079100c00c081300440800002000a103910042c01542e2030320600003840c1c05a5607100503014a40c1c81080284007080ca002d94842007000c1d400e1006065920602c502004a4481184024009404a00000c8a106030b00c002001040792401c0508012140000c00500d41000206010801c20905c130008165840000240c117941c1c08071100781e0007640610040080c4d502484141303401019500558406001d2454107100720b40340c06036440c0020b4960314040286041130031505822070003400050007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 85745261 1250 85744011 85744033
    0x30c03060103030e010809030d0c0c062901050f070b0901020703021b0109030206030a0f0e010f0605040b2103190f0806030d170601020c041104080c06120109110c060a1b02 75
    0x101c11214903011505100c01b080004101c10390900480c0c1e0800716050040029500e01000241054a0304004503000d40c0303403a03d032070000804c08500c00b205002038100881c017500c203000111510707004006003401c030010a01c9000000340d1120322040c4035850160005803140414207000380750001611031380c10200c08130b400c6103416903801860603041d42c1e01541d445540351240c01c0c849004005a46103516014034203402d00741c00040c190004100c004801400b44001a01c501c01c100444840d41c9100d42c1c050781402c0c1c4000c0c01030101003520301c890031241c04c0d039080c40e52040240ca8111001d6681d0000a01c45000300e42c462500400c103540c004405500800c0c2c00048804c01800c1c0c1b42810810400d074005800014955a03c204450346280d10060300c14480341003104803036080c64101d4025528540501034070321489040240503500d130b03100d0034490301d0016441c1401041c000e140e500489045404104040206000c003000054050444850700040711a4103401c038050200d4540118400c541141d403c042c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 85746511 1250 85745261 85745267
    0x30a03061703040303080601110a0c03121d1e030d050403050601061e1808030d0f050702010b130203041719020f0f03040e0c0405030106080601080c19091a0604080c030c0306010303 79
    0x9060f60392500340b80d400780d100c031401a103075005844640030191082c4040e0000b00040700c0c01702f2080b03c1c458913000f500740078400300c01d0715000600010410811040c5110700f61603d030250f80c1048000450a00b03c01642003640800d0406401c01301040101c0d500040820401504010850061560389040b20481941c070400c4003000105985401c10003501300d0000c0b140d07414480050004014000850790740e5400301940c04003030405880103004103403800e130000700800d0060041c190b611100030941e0716a200d0502c50b00f0001c0d00054000e80d103d02499510511020680b4010462604070400301c100c241c003424002441c1851880b2004425003141645040d80e13580001924240d80002c1c03106110f541e54080000f02c06d024503405143c9c103609148000a01180c0842c07000d060300d0440b001d5a0f4142808014003690341c40403052074440040b00c541c05c201c50703903951348058480a415a00340414058a00000d0072030341082d0490080b0360089001d00c038031440c08205c1041c1d10181075002d80300540c035584001d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 85747761 1250 85746511 85746517
    0x110405130305180a15080a0b061c060b1602041518020a031103040b06033d020c07060e010e01140702010804030c0501090c0302090a02121801090b09030a03061703 71
    0x20184180440e40c20b10f64081c08000c1000c1c14030180c01c14030f445a54000344000c42407010705d6207000c10003a102113880c0c50311038011221480c001500042c43c1265244018203a5240483c900b0000c644d10740022451490ba44006c10250398503100e90740c5004250300410040340c44c00034650482000c465010030078010501d0f16000004240100181c441500140c00c3c0c001d80412621010b07484070000820080128041c181402580f0030b50850781400440072031800c1c03000414400c00c0210030782d035070440c14035004405230080002c00c0000160610341942c0d28607203410071035003200c408181e10100e0300041d5603012107400b4620b0742c01d01c5d090422140d0f2120f550b4a900c20b01d031029040005007000242410f000b01b4064050981c440000c20103000700b8104524031400c28001244600002000315a0707014040c001e030f49060109031402e02c0d9980f184c01103950700b6121305500313281035522502c80b10041186030100521070b0f210400510b90ba840959801011101ca0f500000c440b0680c074180170712844030000c25 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 85749011 1250 85747761 85747763
    0x80105040c05070503070f14031e03071b0507090f0c122708030901050a05190e161d06010201150605030c07080a0e01020d030b0d030e130c0c11040513 66
    0x40d03504600e41c4100c03810301ca4407801400391303c00081c2410030001c0400f4030102c0c40303002e6a84400a600c0c2010000d80301e21600c135200780303a12004180c1480140c80b035001036810120038106012104021029500001c4c0080f0090340e01d50040c0d6020007180c1514000c407000324040c103c0400c41c4110a00d0060500281180500803480d6113041c4540540700d44042441d68a105021881952b40c0ca4038140d000d980c422910174086508000100c1c001008034040c4034004e007031902044003451050100781c0c00500018441441c20b10542d40c256181c05041403641001d000b000e8919201800300040d02195040f000c0c10050440e858036400b04600a24003083c0800d6034018a4880d40d80e44800c0403503107141c040c07000c001e81081c00c005006140305070030a0804480340790a03000d0b1a40d50311108401e60840c0c01a8080c56001001020280000781c0314640d48001054010311480c1d5040400d95404111503c0001c1c020101c1d015407030240a210700c1d04c0e50300c1100fa5085a081c0458a49810301401610304a44 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 85750261 1250 85749011 85749019
    0xf090b0c0c060c0313140612151903060e1504080309010207081606050f0f010b070201110307060605120d090e0702010207050114190203090c060708041d0103030f020607080105 77
    0x20a100c8004003400401103901004200e5611500320003a50313902c035030110304254410f01d0000000180c0c19074004904441401c001c00c21810418040b04000c0c075903100800307010350611010b194260300c0c2d9910004003036501d00c2d40c41085c0c0ea142181703410401c403410308041258a5020800e01030511441550490b8495401500c0b02c0d03c0384c8942d01040d0181c09500d20040540d0380c007080c860003810740c060034207542a006400910450f01c2c0c201c08083c0d4418156205540d41e41d8020041c0440c0582d0f00c0100802c603c185404c0703640d404404413490464102c888226146e0380c5911003007200d03150000c146090a100e00c1c0140c4142480554041c26080c95071040340c468130540070000720030320f0003036050b91076040d0804028482044060071440c5084400c03208241442c1905080d00303100c1c040c038804d07244924200001801c040212200300400368000b00800c0b1642401000041000c5840c20340c100f140700c40c03c408041841d419450081c2c94403801d00d0f55201154401e20800100540c08202d803411607100b03031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 85751511 1250 85750261 85750267
    0x2011e0c0c05030c01140f101a04030f0b010f1a09010807090e0a05071206030818040902030a030503060f1206070c0804090e0307020a060c021e18040809010f0f090b 72
    0xd001624520081c0c08080c000b40804500d04280e60b9040d04030302c070b010700d4282d040611559440400f081c241815114140c484c403189500388244e1a024520480b8400303908801400c0a640c0d0b6110980041500030456082400c04010051040b00c44440c60188c1034441d90030103864401c42c8001318500030131210743c0c1042400404146418014418040a444018804a0280340c046001c03005000b0580fa01d4000401c11a01c0c0440000d007485030320292940940b075103260000c0700490f00c044030001140983e000323070b541d4401c400584e010842d800c48544640c80b42500c07403821008004804402513001801028985507180d1084404180f85031300c4200380c20900100401410800e2040c0110340000041030315150441601c040000b000d003520718070840350021a96180e43c400c54640b4881c020003500103180e01d040c0203100c0203100200c28901e01c041c00526490f6003050080424110695060300e070204c0026141ca440e5912248404039140b840c1059880d1241c0d404009101c403e19114018a0003004 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 85752761 1250 85751511 85751531
    0xf03031805010c02120307090608180304060804110402070f1e0510150503210f0903060406050103150b150f09090903030117070602120f1303060b0a0602011e 69
    0x240d11011000503110412100d620007454428001d0041a04040141c450101905500e501080c04c6901c1107400340d4550f071601e0f181c000c05680501001c4c04040103400d5014040010650800141000b082907948582d22402c2c00e050a039100a10a51381c82c2c0198010001030b80407481a861100103d9400040241c0b0544009a80d00001101c220010458021708495103e51f0040d60400782020602084514416a45d4010107030b845801c4d0006185c040496000c847e04012280c0240060084022000c0c1c541860000000d0805070120f41c101e41d00d60750384006105004000d002000e20200400041004c05114800521110481c1401441c0b1503000034000a1285120381600c15105018140d0707455420200c2009449030805d00601c0d60500c1501c40c5030708481d0b00012a242116480d070050304048400c0400c3c085594481180f8030b480c208200103d20340341c64101c164000441c0078590004020440000b004840c10050348444116810198118018a01c003000241c0f01c0144c031100103070440072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 85754011 1250 85752761 85752767
    0x506070201052214040b010806030a020d0f08121501110c100302040302130209040e0703110906040204080d0c03030f020406050d051008030a02010c02061305060a0903120c09030203070b0a0c0f03 85
    0x14403005003c0c5601a03500003843e10180c0a03034203071500c0300303c0e024440311a10000448030520125191981035001d1032483e03000d81069000710500c1c1d4020343d03402115829685561100c0e600c40301094441b016030908112550546400c00107064900346051602e001e50240703599500d42d031307184c41580700719208042400d08a010798121802140c0c0a41062081ca00c80301e1008025041445428012428036800e0103944d90041400020f50b40e100541d03003c8103000c50103000c20644010302c0700d41c03c503900700804210541c04201a036906003507035840300d50360f10b403500d401415100003103002c420071030040c4018445c1030342000c2540d84030b0414440026884d51034804e0601404030f6a481801c05000004d8240902c40d8103402c418800c2959408031011500d81000c040c0c100c9031113a0015005030018004500b00042c142c01c502481c90280c078201001754041e026120848032290b1042000c590180410070031800c060000c030380202081c2800310b04121840c1030152040c001ca400007071513144001d03810402c02d40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 85755261 1250 85754011 85754047
    0x605070b0a0f0608070e060111060c090f04090f050d0906051c09020a0803121005011b02040b0a1e08010b010504030f030309050703030e1908030d020c0703020d0506070f020601050607020105 83
    0x181c10b080c00a071356a031265a89030707800b9000380340d00981e49000040065020f0341900389401242c400804103691490020303041500103410265019003204051086951240581c0b040705008801c4007038003001ea0310f070651400c210380c65100d050100364882044001d070018140c400c810760800303005200181c4010368500600460200a42c02142030401141c00c0e8000400b5000400d0150102e00c2191501403601c0304104042c070549002422b42142184d40c00d203c802c4108450f03201070070200302e1220f4000029842c072001d400072a222200a8010700c4040039600d01c42c001054010001c001030302d0079100003802403140b40809407400101507081c0e07040512a904c08003030305401c401500e42081c0c0745d1900424031101059014440c08070f4409480760403080c101590b00720341800005524040c0040d0f0000c0c0650000554043d1500524000101507160342c0c0d1051050380c441d2001d003a0514000c4000703070042d40071300c2c044130442d48117100511240c0ca03018106e8040580900f416034031101e01c1c0c0d40d8050404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 85756511 1250 85755261 85755281
    0x504021c02130903080730020d0e1f14130b0601050d0513030306050603062b080c0609010e0a11010302131e03060e0a03080a0f1107030801030b010b040605070b0a 71
    0x40c1c030f014001418540e0040c803076070091401d039541071760020a4151900d04002c582d80080b40004402840341000c0300a58010b1464404801020408000709100c460902030031b5075094070310110041050303108003201e1248490000d688105082e10b0308140c520701c8072001c0d4030344000304580b00c00303008202c0d580c5c02101a03540c20500c081c401d000c140703420441d1b801500c2c05541c0c120046810480049104c2c0b46c07034002d4074490030b0003401c0040c000c0318070310b1403490303d095401c600400040c090680350003244894004020303102c01d03d0b000308543d040480c2c400b401c440f480642c50025420416222000841c0003408403a20b501c2441e004d03888107070441901c540c27188175074000f6103141c5038245070840700031501c00c1000807039000703030810000d040d003140b01c2c00e80740e9120201c0140002c3c03503440041e07245517103580700c2d00700d0890940c1c0c00110782c0e02d44048200103034800003040d0080f400700e00040080107000340100b03016140b48404981068541400980315001e5102c0c02000c440c0e10800080981c40d450344651214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 85757761 1250 85756511 85756549
    0xc0c0803010f050102060606180f04021b01150801050907090b040605091602150106090306150306141605041a0309010b060a030614040203070c0b04050703200907030504021c02 77
    0x81d594894010b21040e40c1c42c070030540580602c3c1c00060362480c044058036141115000103991085111040020b9801c40c0c4c60116170281c0c1c00e110344400440c2c03a90f142401c6251080c000120400450400121a660782d80031b01c101c1d070705010820016403000300e500811210aa5408240250b000d00024042c00350f85e0056074008001d001042004484001510144109902074030210f031410074440080c51824081c501c040345110408000280b461391104441d106080d8950444a0710380e40c5900507039000b094421403c4009030203000e00c5024081280c01c0807e01c45c10180d2400b850700c00024138501195503040950b0300c01000155541c0400e4001c082c0c00070380281900c0e03481d0f0340d0300d201a005020340d01130500c850b26030b0801c00c001400d052003160700a001c80d8452415001c1076944a840c2c011340200100d8050054007000800039020703850f1008020803519031400d0f026071000500010303d1004003450205400c0105010258440c0390303001e0110040303116184400b02050000c0303401140440f42031040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 85759011 1250 85757761 85757767
    0x1b0213050610030c0806060a05070605090102070210030c090605030402030a0506090f0d0e0d060903020f070b040e07020114010308031e0a020304170403080d02030a110a0e040b120c040c0c08 83
    0x44181154045407280000b00e810039900468414100d0490313050f5011880410030401c0030410301d1401501038142103820380343c0645401456914502a0750301aa1013400c1a074022400004514004d241c1d01c2003c80c940c07404020346040d81c40c0003011030b401c602c10207041c8440000400c0540d107041c40381c5040346030400129003160030030b00c02c0f0383c0e0758032001c0c2401c0e10b0700e0041ea0040500c11b81f1400d4541c1e030300304c03005141800f035003a81d8903002c0c000d1040450403815881180c80542c107044d4103204a10007080c42801640d02d0b641351a1a108000c00700409070b0085900d000c00c0074100101c0c02c4d80f001d040d40d070400b0340e8503282d07518000c400e030708046011a03032062243f45a0800c840d03008030790006c500c20b0748590000010490007011070310050042d400700401e610818410f00041c950f690740510382c000c24240000c2040707500f020402c01030398885a404030002d1168110821182860701882143d280113540e4020001c030304c1c900b0640c036000706214151290340c540ca004910507114000018109070405440e9503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 85760261 1250 85759011 85759039
    0x305030711040b060705120d09021008010602012007031103090402070b1e0103050d0c1707120306050f0f060706060308120f01060f05030a0504020d0b09010c0305251b02 74
    0x8141c504040101e440b8600384011903100b41095410781d102650f10200800704804904000c0d0300c6604065a41d43c111aa41c0d0b181602698410030a0a8404007a880381400b40d4103042c0c00a0175550250b0f001004084d00003140f100a080c2c0030119084c0380e400d0315096a208080054403411481402c8405500034008144030080c40780d9541001e0180303407001c0a43c00c00020000170051040782c01d2101400300e4002e0400314061b2800744550ba440c10344070b81540700b103031045a10150041e81015401340c0360194480000d80040c0c2e094402c54010b80012200a0440c441c01d10004e0443c071044007100d4015980440d0304410007085803c100043d42c1c0c001001610740d600300c208504640e80c00c032104000f62a11900001d2b50030f0151410b0703819a05d4944d501c518580da403055000250501030012a0082101d44c4180301241861074014026640c000010414510809004040d150060b0400320408200c100c0000303480d5074540316001002041c1010356501211181e424400705040c4000f0350032040800c1c50310 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 85761511 1250 85760261 85760273
    0x60a030f1104050414070203091c05010204230301090b070c050f0304121208010e01090b010c1401020a030e070503070e060d05010e010605041103060a0605030a0e161d07080109051003050307 83
    0x4402c3d9441900c04000d09004400382d0483c40c42c082e40c1503005604100400c02107800c06007151030146104004181d1a0700c60f1b9036605007264096480700004205051241c600141c90740841200c9002c00c80003071010912070b403100c050701a030151142c4140801040d110b000c101040c4545200500c03400f081d0780e151666510500006540100200c981d804841340211040d4001c9071500d05136503440c82920016800c00b02c40000400a1600e900e06008119080708005040e0455a1601c140001c0c000350700d8900c090740203020f131102c0c0940707403003d6040120180704586002a4040448014009a42c2d0a4440e1004507103d8180c01e1400703401542060507202088105411074000c655042d1804c014040303aa094900050005841959101041901c100142ca00c10b801541c0c01c5040000000758003103e22803503d2402409418200b028460070f6020050520b03400300c0d00c2c080c096242d4511180c4c1c030700701d003000303103d10300c1406a804802e5544020652482051141401071680710081302d69580385401d1030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 85762761 1250 85761511 85761517
    0x606080307050609150105010315050913020f03070b18120a0f12080108030d0c052505011808040e040c091e0e010c020a020d2d2108010302060a030f11 66
    0x19502c074402c41001c144003a4001590300f091a201c422a40050b07428000110088c184c40319501050180810380450381d9070356509100e0244800140754940304000740b05012114400f15003141c841e410941041000303483d258120fa040411384500c190200c00c0380303800240407540101032540da900ca030301d660200308036143d03c401c0b40a50081020703036100080c42c80111110303031003401119020740051011401105040c3c221080c0311086050050400f03010403108640c4840b40d500740c0140141c6600754100f40326081c031400d1030400d400040340c1180c1d0160344604240d403140e445650101c3c018000050280655041c203100501080700c001d00034101c13012030200a002407800d000c416146000565107408105102e494a2401c60790080c0112051517002c0040031500c14a0a8a03c0003600c0d861713802240380720400244011424a110160300f80d281001c03052014800c40e40c01c0c0c07000740c1d03141c0000e01c1a00000020b0450b80d04450701640c0c1c910000c41100900702d0824018480c03400e0100000340b08034141e000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 85764011 1250 85762761 85762763
    0x50a0f0903170a0b01120c020705091501080105040506090610020c06070b0f07110709240b130e0405060103140c040f05011a0712080c0712020c010809030a081807030606080307 77
    0x22482072610f40c0c2941c041200e14002d0114089299002111412900d03a04103502054507401a269102e54a40c00306e01075800c204c4a50040800c0001c41810668214000b030380944010380341009541b9011010441c2424040c0c5441d02c40c6000024803541d00340708000e580340d040005001182c840800340b501621000701603481044041d500ca00042045108040019000d00140c005140c09880c01d1200001081040d001c001c070010714111800110043c4403022000b071060620040e07448c1c12503400c05c0c261504a80068584003c0c94080c400400c82c0003c030036040d643c000c80a07000761502d07c1310b080d2901041076403068015081102c4040000d802c0c0c1c0c40181298a42001845600d2007424131005070310030b00c0c2c1c009001c81d402d00c1c111801c071440b8945507030f030090108411520780324041d02c1c0d042d1003901d0081c010700107034000b0401c071240d56404030350f09030054400b000841c2041c0d20800302a1410714024026403034020f00c2013000f8500e03641000540300071900040700b0050300e5150100e864480d40400c070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 85765261 1250 85764011 85764047
    0x1b050316020f04020a020a0605070c020901030803040303060602071a0310120c030c06110a11150d0605040b01050403020f041509020406050316090f17070b0f2101080c0103050a0f0903 80
    0xb010035440e0405008541303400b4840d5000d44003400030340c1d0340c21004100c050300a10822140c11016001a1510303c2000d01850081a10549070326262070018240c44a5401820454201c41e8003080511141c1002d1048400c0c01601c45403650b5541c4684c1c18050190342c4a85901c10320b540c0c0007020b001004013444141d034002d040103901e040e200d80c0c00780d8061011442d4200d5981c42114080d001c2009203950340f0803444000e1501050f121010b031498411b420440c00b42100c0e0380d5491080055180a2080c02e074421020b0800c941401d245800103408407040495040c0a0f548403401c001403e0781d505011070190044203021500daa0721401300030405d03041156009080e0401c0103003940c0003401101c14004581d0b543c50280821030a248048815404801010400f84207400010407000c40c2c000c09488981c2e1510710803500d82c03001c620520100c4110380440020010a400140f20828012038074402c0b4007000e01b00400c0c2500e370f41f2040c0c0000e00d002122044901d10b80850002010380c4008007061640c0018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 85766511 1250 85765261 85765279
    0x3050a020106060504061b11150a030b030a020901060815102f0604080a05130e070e01080108030d02070309050a0b03010e0109060b07200301111b07151b05031602 71
    0x14100303130755a02c503900850020a0040c000d54602041000d20021604d10480000c028284540082075584241c40e010712000303000452600d0312903502d480344a640d000201c008143d49aa0307074000c9200b928043c0078241c2048510301c00101040a40c0103025a03986020745503115036100b807080103020b40b1241e80160b5007040045501403002d00400300004201c2c181740041c0c121619582e403554004e520410a00041c40400c2c42440b42c4040c20404c0340c0001c0000e00b40c0b03c5258540584020440311030441d4640c1804802c600502c6107402c00020758000e120f052000680e226420b0501307032003a13034480c5c0c072182c1c1c0b04403070f5880401c3c08468100514100c4000600d81c00490b44ca90031000180d804601404400032401c2c0903190114019030701c4403074174040c04c001d009017090f41000403c0c251014000c04502c00d0a00243c04a4500d002c003c1311032507240f6200180200c0350406490758030182d240d113504010400c3c20a0b001d01ca02c1c1c1d5071200c2c0710710b0651000480356105d6a0200050191400d150243e00c224180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 85767761 1250 85766511 85766519
    0x102031e01031502090112090f020a0501030e1c05090604091b050703050a05030402011106160210020406091203090e15030c010504050907030911030304141207060c0312150303050a020106 82
    0xc514118103883e481800702005181034803003c0000c2d0421280c90b070402880c155400c10070305d40d901c51044031070f020702d04c2892064654014842e00800d180d00c090704140c680111030f081b070540030078980000070302d00000340001003c0031411185e500442c0034465124100141c0046c2040217644074000701d800c0c0070f030001010541c41e030303054807a1b010303880c00a008640300308152180c41b48544001c6500900c14140b000200c0081e0100302d03d0040d041302c1280944903482620745038117404100615a120711142c2c1907107005c0c10315000911824030341c46a041050b204101c1c4c1800c1501900c9603801810502c0b0481410303240c01813410051948a4040c54000c1c09642c0112110394842c03404c4405442029041a00d10348964004400a00c0700c0c250039900813440ca04503410956061008100900c401e0041c0005040140e080207158605030303407420700941c402d2004004c01d80d00000a80c03000c0f500350a2400e030807410f02c0302c08000381410b080a0b002d03402505401000f090b0704200a00303014501640208607258803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 85769011 1250 85767761 85767811
    0x114010b040312110a0606030605040c091505040914010e0615010305070906320a11010b010c0807060f060e07170601020601050f030f01151809020603040f0f050f010203 74
    0x1c50002821089800e140e4030550b43c01007001c2c00c2080c11210454000c42e03160b407116001c480c0f00750800c0301d4007621075041c4810700480402c1c200282615070020001920518801400c407480c0d0b103d46405075846d1044001803100307500705002100c0a9900a2200c210710200d02501c4030800c98008461400c1411840e0865100e03114052103449551038164440d400c0c02019142040c850a000b030031081d070692840e200319820308521011503a040a4181c0760390414102420300c0c001c004100220360315244014015a0744041c094004035000001c540c0c0d202581d0408001400140012800203800d004000480c0d400c0074901e00d224a68558917180404602d010307091801e6010344d0440c0c010790010700148030b540340000300c01503203003401002c0720813008903100c44500f560500c01c603410a00018030b800300010302c10722142d500d00340115541002002d03010750003d00540405080500504440f1500c08100170ba5440c5100c1c0494002c01206d4101c4090749009c1d011b075000315009101c400c41085603080c1005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 85770261 1250 85769011 85769017
    0x90309080c09070c050316030203030108120705150606042102010f030c0c140106030c090e12040806010b0904020403060203040f1b0821090a170c09060603040b0a0e0f0114010b 77
    0x10002c144034002d495083c0f0440300e440443d002500c542c00b08002101c00c451031200c5d58114188641c02a545a40c50040f800e401c00c4100c0d00d44042e09001001200f00080003c156103640c42c0092060032655261200810a640a035400641802140d40d800c0d00050481c44001915140300742d0382d6103800c0b560044201c0566038400c82040100c0c04a540f00e600248012240c101490140c03000000c0841e83c0703445880d11607069071300440680d6030351130000c1c0c40002c082c00211001c00303c94652038603041c90b05540a55a520503c02c2400d00b00010940d0b016039036031601140d00035500480c0554032401c050410b038101d410005000c45054038141990403c0c0c003051300d846401c4941c0c600203001e00700324180a4401f0103540904403100342c081004010352030b03910f200300c0c1d00190800300c410405540000c0e61030b80c07074903c64606003481641c196040091580e41c52048950081e40708a80300f55a071916a80318015052401112806001e0a82d10b032a51030310551251b100d02c01e207042c107042c450340e0316104494544 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 85771511 1250 85770261 85770283
    0xc0605090904020103090213020a03063602070201020307060218011e12050402120a05060702061b0702010309020d0203060a09020916020c2403040c030302060603070f05280909030908 80
    0x2250071000200507600170b6000c02c494600103403a0845540ba950828000ca07440180958086a51810144142e052241c42c2c820004038a4048a0b43c203404a119040c0300c410030325001da50540c0005065003164404e205440040b80e00100039504c1d0b00045142e600c0d54a03e95210600040c1e000503600d112400c3d084080c0c0b51043c0e5911110030260403c0709950182c5002081660041040150f80f101d0170742c10001041e00c2c40c0601c014180600b80610700904049002c1c1801d150401d103203c0c2030304000105800c4500484d42402e000030705407914400f02d00f50070300255020354540070b02d404000c90012540c01061016100315000281580c072850a226015905646200141e021940c2c030015420b004141441c615502c24403c0c00d04840190780c0e0740c1030740c0219400c0f642814069010010581c041013840c1e00705408801500c4040c0c1000e44611a1444510400b07200305222081c40380c50300c4450300000000c8240090044a0b01d448500d80310243c41c0140040300003030302c0d10a0008130290046500060a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 85772761 1250 85771511 85771519
    0x809190e01060c240203160509031504030c120806040b12060c071b090c110d080c03070909090f0308060d0f080f0d020d0902010e030304030224091003090c060509 71
    0x16900301078040b5018185107500711132103040c11154500144d04240c003d40c144240300da002d80c0d07a181400420745140a0881c404080c004140840c91895501159005000c42c9501c90b914a42e907541c242140c0c02248820041c002e4614054101c2400754071a40580c4208000d075170501517880c42e5018842e06030303a80c0c04140755580046020074a941c1080008050250058070152080d0004c80310721085104580d01a4608030380c1c0e420410078803031704242c00307a082040c084040c04100d000100041e011140c000c00c0c1ca4a040000000a0081d5014907092800380010030381c1000b5990840c601004c04003e161015408039074060001076842c607025918040b0907a00039121a81c3c060142d6038100c41e030b0070050300c14086080174031042c0e1404116101038412201000004258507489000251030028441d000a010b504204001d00241e01c1d01c01d058000c031801d0125804461110511041c0c1c40e0164420480d84101c24100f6000038941c16044008214020a00c00b80481e42c0c0e00400e032228450064082c0d08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 85774011 1250 85772761 85772789
    0x70806010909031809140f04020904020103050403180f050321070f0f0218041502030105010f1d09040f0308061e060d06091d0609151303120207080919 66
    0x51607115420001c00c00e4401d00345000304441140540c01c03014400c1e0400b070150b03076441042415149032031010030b401c0f840600c09410142025000319401c0c1400510203410700d03444401180405110b203108040210b488402e101304035031550200c4e5080041841040d200e03220707880d0260000c0070503502c0c0d40d500084c521040c0e440c00500b80d03119115100c20042c04c0d207079801001c02d0000961185101a001c2040c040314000552400e807032701104103500d8030901040c0520500051001d030340c10600c02341c4002036500b17081140b072003166100b0006c1d80b280c98110390050001c00074801044401604800414070070b40740c8480c10b40e00d200078403c50704480001c1034000300c0030000755009818208010505400e0030b0380003055264440c407070ba000b40c840c01c0041016000d0ba82811071141d040a0003400d030440001000f0f04000319485e0150b844112003d0640c009090341030108004050140070b181540260b69101503494800500788140c568100505c0349004440011080750072405100020301582d0000d404076070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 85775261 1250 85774011 85774019
    0x50307030222050c030910061401031109120609060108060c0a031d0a030f0e01020705090406020f0c060a06051c0201020709110903010f02070201090605030c0403031d10020c100207080601 82
    0x103007503002c011090400c0715400906504031500c0c020240300302c11040c400d60b96401c0c406545c81c503104402c681c2c83c54051510700113211311462900b400d071454200740380210714000160900c0d850b611a8909a59101c00d002042aa44200202e0707414842c4200b081a01e11580c1c0e034400c9103480d05c40849000c0320b12901003060492250003580301d445058040c600528450b060381c844149840c600b003802742c000c2112100c8500405a02107582000e1007420f101809034546850046107041801400c024000e0fa00854212102900300060f10400c0144100b00c900d01d0034203c0081c801040f02d40142d5014070503200c4c1ca5032286461071001a1700c43c0d8180c0c000d0010520341a459001003012161045114000f00442c1405a40034024001b41c0c40d02d01e000166240c10a10014084011981c880e40034000c0620400c4151111740003528101e03071301400e0200280c610012819a140781c1c1e0212140d01c1000c420003540719950000300000c10040a6481c050020181081a0394600e143e12074400b4030750003040140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 85776511 1250 85775261 85775269
    0x409020703031b0c0204050c040602031803030c100501080706030203010302011b030201110d020c0705040902031c12020417070b0c0d0c0804050324061c0b071403090106030b0c03010503070302 84
    0x30490a001c0d20b0b00181d00c06041100c103204040c3c0410140024039801c01820652a05128243c0c10030107201e1128509031400c03602a441e17024440381e030111410340352440c08050f1014030485000030140810755a21120491128005160070700a458092150310300200c1d21502a1080341d0680c3d4050312a032605c22410300f0808000913880404400715521502030088800c229030140450706508100135856600580e140c900c1d0025503070010344103505020400c00582c4003c24140741c40041e82031008841140c003d0f042c0e566480711070118949a02c000b600156202100703442201d4100d114050350400c0303543c5d5140881d9030140143c8a01203400803140c0f40c00c0e40c0c1c01400c8000010340328410580c10140d0303c0e0006810f00380c4801505c4003c0b000340b94164003942c1c0092181e0390200c0304444050400304090b44949244400740401051160705c0e101003083e482c043c10701c040581c03452024040d41d034074080130300318080c0140788030449100c2440800f08080408110550717058a0300a0001c007195482e5400b08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 85777761 1250 85776511 85776517
    0x73209060706150b0a020f0a0308060d060209091003141b1c1e020102061003080f0c16030c14061606090f06020403060b1315091d030705010c080609040305040902 71
    0x1121455034800742c0c0c3c0315203114480d030350000b0b003d9141d07519110341d00c089010381440b40500018041d600003d000d40d0010b9001880150842400e480145040c0d2403458404001e00c15410215404144402006000600c0300e00d020150307441080c11500d0130700382c5031810f036a8491000d07203004d80602450703490a884c01c090b12202e03e44125000c0d03040941b61192282003034203042c0c82441c5060000c0c40c07016025940c041001035001000b03034000c00826403850b140c0303980034042d081e4144290760001070964208001000b1030140c0e120300400b4440310690b00e1400b40d001070300c07a00c10800720340c0260303a0302007040c6400170544d90079000b00128020240841d540303980091641e07a20845620b90740d10303050f00c04904244003420286d0721130400006c0204880040003141021044002c8665042048000901688403408002c40c1c14000c8013046003104448900145255010024043e110119070042070000540011100244c240c50312561a2643c1c41070000c400340403180031b00401c50401c420010703c1b60a50003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 85779011 1250 85777761 85777763
    0x10110d0c021c030c05120f040c080304030f06090c0e0a060e06010c1109040f1e0606050904022409120c0906030d0203040b0a090b030405060601030b011d15070b0732090607 75
    0x34542000314450800c0e06c50140d410900b050026410482040307a001c2c2080b02030f0440e8001103007480d1650f0344800029504120040100e41c5882c035101c01c001c0b08020005c050301a60302001000d24103140100010142d40c030a10845081d0040420701c154092000c4100680c0c128242002c00c001d031b40184103440001401c12603101a40c1040040802c52000c801001e8220002111f6446080c03401c0000945e0b110360071540c45800f0301018030005079540780211103480e050049140d0768007000008042c150151065032604000c2c04541005140c90101d400202c0800c202d5086629440b01d00c18190360f100704044142c00741e44100024000c4001140240001700c40d10302d00a841507844290303a03009508180d0301120590310620602a071036800d4092a10000001c0c60b1841c0d0f410040b20040151002c080c0f800707801010f1880030940c40340b5000045440303554002c54485518101131200502484c03006d05030142904c150019035048448140d14426600385248407107040201d000104102d80e480914 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 85780261 1250 85779011 85779017
    0x70e010e1504121b0816050d0303090b0a060305070e1303081812030a050a0e06070f031409060414030f04091107020a06020c010306080105040b010b030910110d0c021c030c 75
    0x10000d45604011402810b413403088007200c400f0810801c0d01803034902c15030025581e540040035402c9071030b00111010012103030125484018031490f401e065008001422000d04203818600030000c01c003d05070084012a44140102c49086658104001a03500f0a640b022803a18240c42440042803245c02e0040c0c0000303008921883c2e0030444002c1c0c91402c042644031007641c88011007006140c00c0e81e84920b990145003000207000001ca030900594480900038082d40622120a65000b5810310070380c410f0100002642010340c803030a00101841c0e9450040345d08480c0c04005000056400c003011050364904c0a0f5248083d040c54104000c40703001d860300d5007410419034030501840c2c01603601c1c4400702008114540148c007548803210001402d0359420382201035103a04080500c80058442c850503811660303010341ca161030740c070342d00080ca0070711103140c103a10580d504180d114802c40e01580c008114180300100100902c881054041c3c1e07c40ba103240d503803883c10251200c3c42030614000e170049501c80201d45 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 85781511 1250 85780261 85780267
    0x30c03040f2109180905150702010f060f031e03080f0606120703050901200414120a030201050618150f0a091a041a0904060f060909031205070e010e15 66
    0x51a031011400c4140b8010001d02844001c1003d081441d070951081110f880090007660410303101d9175501c007070300780c2d001a1300121040001c0c0000c1c030030342c051280c9800540c400d00072140c1c0d82030061814402400152219440c0300c60180c45142190b0a80e10b8040c1d164480301034640c0ea809404500307890040505030019070401c007040c80d0f550300c421607511034111524001030a0526407155421600c40366240c00110060000c6d07082601914001e450844007001442c0fa40012408007046994031074401003c054030856040e102010780641040d44980815501081101e8083c0c074282502142a41d440300842c481521012450034031410031208400040d081c0a0b801c1d6440d10900c00b00c0d016400c41540102e001d01c03c49030700c0e2429004400100ba000300e2948907071035003400014562040904002c10f000d03900c0c4044210454190840c40050101c121b040104907c2030901809a80000f0304a501161402d03000600c11409850811504c02c0706070349200c0000314840601c600000385110109a403c800c3c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 85782761 1250 85781511 85781543
    0x612020c010908070525230d020303130303030c05030105060307120e0708070f08010911120106080607080f06040515040209010207080d0203040503060a06050108040f020612072102030c03040f 84
    0x5000105513243c8110020074410360359400b0181d585100040d0015441c010400c10841e044210390f40d45224610070f0303a0300d000007001c140054541204050029010b005c08290500300e02c900e8080c3c413040320300a4406000b0341c40e40c05800c98183c4024001e1541c412002e0002c28040e034416040da060300c0001040c0007440000d111120340c60b0a0f8981d210041315406404c06001d4548071400e0b0380010801d24009003c88000d0381d4810200d10302c040982c0780590807845066000c00000d4200000900e00d034801c3c1c507403500305148001c1c2102d5049440592207004d5401040b280e007080e00c1114820180c00000100000000d0108000383d0300119441e411446400f0004c1240141030002141004668008580e12072500302810306040300201280080c0d841c0000822059810440145d4001ea00c0001ca0303503000c030a440040c035075000f4922214208218441002a00b6804c1f6005020140240540d00101a0b0802020080c0d11086920300400b180c24400b280003e042c500c003205070035100d0021602e000d0301c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 85784011 1250 85782761 85782773
    0x6060310180c091a0117010e10030c0b03070813050c060a0e120328020601060e0d050d0906020118032007120f060b040605090f0705041a07020f0405010612020c0109 72
    0x10b1500000007550340e810700f418400f01e5030103c00c400d03124282804a00301c4440e403440c0c0500c81c014400e40101444410004504c80143d02e03200c000745900c00b48109000d03855072451001a0401c0325450041803a00740800c05020001e0b180542580d800401007848566010a1165640181d0a0001842610352042080f9a00e04d42440c031946603c500942c1c403a81820841d02c4128101c0c5c110b01c014104502c20b4041890340491800c2c155440c0c0d042c41e005401902c0042030300c0e5101064050300500070290803007481079200c052142100c1c410781c001d020301201070400d00561035036440000c0c049480803100c19001030322640c100c0024101c40e42911102d035524514101074480380c1c10f044440c1050b05611b2010060f0f0f501c11004405016502045014104008030b01d0048000d4440d95000f001c2000044800f8850f2049402414143c00e60b0140c034120f0b04036a0016400c110402c0344910041c00c030a82040c1440d1003004d0488030385035201741000d401d440c4424000d43c0f140300030351415500c8900034404100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 85785261 1250 85784011 85784033
    0x7080706030e190f03050306061c0507020730060b04050f012309070c02040f0e0a0303060902090d140307050304180c030c2a15021b0606031018 63
    0x6a1008146621a80202810400100e80d940242100c481003c030101d80d800c2c0d05a8001541400d02c9650303515920006002401015800d0002d02c129100c2600b040700c0307a41106000f01040d40840d90207a03110880004c44603000e41001c1c001d01e010801018010486034003a05d01c8501a650010f0140030a901113401e0381c07411200c840280e10400010080d001c0b4800003a520028403103845400350f581540050300d51503014000208002504004005560351a0301c161007003400b03003408000070a03200112940b943d5040d0415008039290000010340c1440d80e00840d4880e401c001d1031001c1b045810b5a411302d58001d0f0100c03481803823005200800008d241000200080c0142402507103403a02903061003c2039903400e100005c01c15041107940780340306c0d82100c1c503143c1c510302c0a50002c0c91004031781c6016642110b0b40c0009000c550441104c0308000c50310350300a004c2003400c04052114a452b5941e1340d640d0700015103006800d98402c07e504c0512075020303849038a000c40d2140d18031505880b130781c5801401d66 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 85786511 1250 85785261 85785269
    0x3031b0d0e0f0f07050a0513021314150306100f02120423030a02131107060f0f060608040503090103050705040b03090f0601050a030c0e040501091205070b0f09030a11070807 76
    0x2030310541207030b014484100418585040c001004202c0d203420800403503e240402c1c843c81d4040e4070003c3e500035600101e5015280b40b001c80809148813259544070180c1203040d004200c0d030051030401411450228142c0459220303a07000780c50b4400307031140c408089031210018901c072807c41c040c2407010501d029041004000a14600001c424604e80e604074843c0d40070f0003c41100e21941c40a003d00d80161075105121700d0a01202d00c000820508105020899208040d00205111328102510614006070741c0165013101c103d020404c281070700d070041642c0444040e64040c205a00a001082842d88250400c6038800c2d03072843e19504155840f20090b0711a0410340b400075035a00300200991407030404104a5004110803a00000c20700e00d55203602c00450744134080c0b0a0808081070000707041c46800d4000348252a4401000101c59610480080194200404c03c0300c440c1442c502140480e040316010038000c0c151071014525100300c640050f14150054a400324030b42c00390060018401d80e05001c404020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 85787761 1250 85786511 85786513
    0xa020a05071202032a2b0503070b0a0c080a0b011209080a080a050c070f02030a0209240103060e070f020109050d02010c120501030807020d11040203011401020d0201050903031b0d0e 79
    0xb980842c0304040c1003600f0010b00d401d030101c40000c2001c1e00034844911140c090f5064404488540481160070440c442d400502e041c032504410504003040710000c010440c8501880092800d84c61385031554043d94030401c940000074844402050401c04142d105a210807014102072905001c61140c21040e1500c0140a8601c41c002154104055420001d03003030388100150810000c61503c412040414000c1302c0002c0c00c910807100343c0f8011503c2c1003080144503900100080703071924044040174135540300d080700d8045450054100116550280c00b604003074900f807101a0740310340e44000045540c0300c8649071a4086640300c203c0300011481c240150040c00381a64004a070000719014090025409007245000e1581340030010008200b10a0658000385d80c1182c0510b55400a82011000c00046200043c1e11a1002000203811001c100005c0c40142083c0c00781c03034008090b040c0580c00c8a80c1111100c141c0e4008200050801d8080c51085140d41c050020850a069407001064101c0300c981c0d840030f0103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 85789011 1250 85787761 85787789
    0x9050a140c030606010f0509120303090c0a090b030703020f04090f030305070314150603190e0c040507020607120b13090503040905091f0b0a03080a030603030e0a030c03080a020a0507 80
    0x2003a0040c4003106405809400400143c01c01e000001c0c4a41e6003840498200320020540384080d980e00740c40c107080d11174034200716603e034140200c00e00d84881071154443c2c441c8818100008e0500340d580190031602c40010040c00c02c0b9484c41d001d0040b40c00d1941d1226520a41d60403d21002403001c03100c80000c50300940e00042c4030300c0c0c5504081c04a8400c41d40b2590f00040ba070701001150480c55042e10458103054407103030b450303480d54a64007007039018002e9560541810280b18805412000800708004501110306001a448100050740c4504d020754007200015040194072841c134459400413505614068240515942103080c504121050a0821241a000050108203038140e90250759000310344080508560914604e01c003102065156414516688802c21070341d882ea10400c04500840d0000402c540da41d5003940020010300d000c0c0400c1700824107070740e4240d00c0c0d4240720715007400b81ca900c020568084c3e400d545034401d294000c24402c030210f1055044500c00900f050000000410540d202111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 85790261 1250 85789011 85789043
    0x305040209090106030f020d06090b010b0901120614040c0207051c050106060e010507150b1216081204290f04140103020a0504090b1f0e091e0606030a09050a 69
    0x40c12260140200d54144c0c14850203001140001000d8202c899040b40c0309000e0321a0b520f801e2000d030000d0040503164244d001e000042a40c00c01008003111030b803d0b0713141601c40114001c000b045400c40c3c081c4d00c81c4098003107402d04890401c3e50100c5a030b804680100e07035180b9070702c00009104580031b58400c140310b502c2c071741c1c0501000424004c86000c0e0009042000509000d500006d19034003e006001d400f640c20419084001c080a0f80400d40031040642416001020850915643ca852841000d541c0c0d101c0130300025030f03000c0030494180c1011412585850140b502c002907540007005a1b41c00121610410400d0320803d00200403c0f400030800030351a00c542c540700704403098103945818641858010442c3d0500d0325888402c03141620045e1000103854003404010821000c041c4450140c0c80301801000600d103504118280d02010048509404c29500c51710b409008007084203034000c0d40d144680100303900e840e0000c05035900c031590400008040000d501c40300c1c0350641f0040d09590202d05122160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 85791368 1107 85790261 85790269
    0x7050409030206060607260307020d03140a0906060b031303080c040e010902031801110c0c01090e04170c1002042c06060306030c0307030c0501020d0206010602070608070c0602030703050402 83
    0x5454002e0300c7e1035203480e5030042d0703941e20161140c0308554540d41d00c240180300c5d402402200340e01d0141c40700b03442c400181040003400c889075500c9410114141c10520065032180c0a0410742003503001c0c0c9804c2c064049007020f0303c0400c001000300802d114042d0a520001d0440d49840c41c0140c1d41e60b40e01d08480740250101d1096040c6500300503082c84040c6004000d41500742c4041d06581d42d1503000300c0159480c410b24456003141440030fa0005001c21400038040320000032a002003468050041da446040c00b000c010009106179001c1070601280170182c0e1591400d801440300b034200d0b010a4584603031491402000144556400030004070103031401e00081d0b0703000c0343c06400c9030360303583d00c0c2e240c180540280d902502e0f00510408040d545a44e00c002481c3d4101c460a4014044003400d24008560021004000c1c07000c0c070581101c005d0028490740300071489110320381e50000d5941040d20400c = true := by decide +kernel

theorem cover : BRFrame.Cov 85611511 85791368 := by
  have h0 := BRFrame.cov_init 85611511
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85611511 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 85611511 ≤ n) (h2 : n < 85791368) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
