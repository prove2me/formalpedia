-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:26:16.722466+00:00
-- url     : https://prove2.me/submissions/0a76140c-e397-449e-a4ff-2ed3bf5ed7d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 205755395 ≤ n < 205935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 205756645 1250 205755395 205755413
    0x7021e03090a18150e190c0206161403010e10060c030909051e010b181206040f050a050609071809150f1508100e0a11041104120c0e0709050d 62
    0x1003401c0340c440d80c5130a62038000b00d080240b10010080d00d0325503c01405c1c5001441ca003400d0030240f81520303508010b4207159a590020301c0c25802804c8844920b12425090f004841203200d150000b0031075500800003040c4518200f0a05000300000c1140341e0503036541d401c09450456200310060007203100d00c10100485080fa4010030342c002811095821000380c007159081c420070f030030703000b0305011000400c004000d028082164080c00c03d0031208682c0c01c45c041d051403940c0b00b100400c01040b0b0841c540120041140801007001015413020503038403a8541442d405a80e0444e503ca0704604080a510b03850701840c0310312030f001503181c0010010405895104074040682990440604003542d01e04160b07001070b9100c0e481c4806012102c0203001000451003100c8c00341c0323444034030525594000315100740019104440140c0d621105172404108100daa003d1500280640c1c2c1c0301b0b0001705402c445100810000c0d107903200540b80d11108041840d11062000c907091380b0980200d941103541c0e1029800883c030402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 205757895 1250 205756645 205756679
    0x1a070b0c0a0225030312020f1801090506070b060409030e100305061323040c0b04090506040501080304050a060e010203070b070806031018060908040308120a0b0105030411011808030307021e03090a 86
    0x1210143c138120b81c01c2000600c0f603000400f2010500c0b60110500c820b50b90024092f0001d00c0211440c5040084907142c003030000001801d440c2c41b881c1e541c00503900301801500381c1c04181c94000e0110314103805404025026050880351544140c00c2c1c200c0d030301c1e402819072050f20040240c880440c0e088182030b0340b02c2e4156000c064015201d07214803c034006903440d0210010401742c040c440f804515400d2a100740001da6030107810501464106010034000c54803580484d42c121f070030754031300301e0840d90304030740180d00b18480e80e80064440d101e13907410080d0300c44e006504680100410740c12100b881d0441280181107929a00e407629007058100e0200700814210340000e42000d00492020f407510369265100ba640d50310884140103000c00d01ca08115800e0951311622020220a00f406403952030242e070303818801c00d00002c0035410310406150f90340c04007003204c0c07600c00074048440480b6070ba400c1602d0042d60312060301c8440c0303041c6495a035155010710b00c08001d0f038401490160000c01140d00748030390507110450748 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 205759145 1250 205757895 205757927
    0x70905030303070c1b03080f0c011802030a02100315031103060a0c140f120f04050f030304030807120b0405012303070b0427061508150a1a070b0c0a02250303 69
    0x4c140044041a0b03400024101041c04804e4140d550314400c1094ac00c1d1aa0b0b0503444545a54a207011005a1404107000041d10303411200c0e24072842c013414095000344689000d414410740c4c0c00b9008020011000f14890304844200c0880c1c015542c0c2440c030b0010b030303803541e41c0c54400980c800410410154002e00034001c01c504078140203080142e6841404803009085400c040c07083c01e03420922003072020900c114200b80010a000c0c42c0707186071030344001c1d0401002901c0d000420244440c4946081d81d42c0c2d010550b281d000410a0080c2e50350b82040b2407240b007181e20880c40c0000d2001d1050010b14001450104a40b04918802c1c101413604540105025105510203900317001d60a40c0002c513042c034891000608075404140c440866040401004010001c002081030044038420403100e5940c04a03078005c5460500c40c92165241c0240c4950160181c0781000386098020000d021040750080c010740003403c1264201d80c029410f0341004401d0701c4e02c8881c900028002860b052000c68072810080071480ca40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 205760395 1250 205759145 205759193
    0x18020a030b0901140901050f070f1407030905060a020105041103030408070315060302090f010810020a0e0d050106080111030108010c0203070222061a030a050a02041401031a1503070905030303070c 86
    0x1281030013002903100f1254095103941d01c004014034008644d00160300000940b4201030b06500f2a80f0142003c88100c00e080d40d19100400c11b4820984034400144c007612018111940310901110064043c000039030b0200d5000007030381000ca07458100001600d0441e2403c1005110705461034848280c54046a4007140503c1d84411012000d41c42e00303207a5a00421114211011640c076050381541408400034403003c1c01030041001608c0107601036050f002c80d800c22580800700c13414601c0c1c55030043c821980850959400c0c00d00c1c0865185100fc0954100c80089000340401d9800400483e128850814002d40c80a0000040300340d0b1000110f005441c8d00c444000000c40644680c541710880c102081d9600000800100b000705076259405465040202c0c802c2c02c3d0b08103803c00b450040e002041c07000b030a0401d0b80d80c0700c4070695481c50070740704040c08401509061078040d00000b0104954003c40716a0b021440c95040081d079410004100d910480c40c503034503055048016514001c0101d28252007101e002c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 205761645 1250 205760395 205760411
    0x40b040209060a020703060506180c030a09051905070e04052d10020702100201050c0307120f020703020a03111911030102190504050a240809120a0c0618020a030b0901 73
    0x220100104101400c3c3d400800800745140f9240090f120f0081c1000e00034040000303403a5203030b6542601581c008020b1150b42d926686ca030b90494008002c400c002604621805c104125400b41034404880154007070001d54540c203807104c1865000071410f80e0010305640c001c61072014100541c1c94084004000c0032210714042d01e104240c1c0345012242800b440b51564000b0b1018218a462400d804081801e03000a02480c680300c0c401c210503010040401040c40180c01c1003440d9070040350301095030a4000380046440b0080303414029071701d0301030346403c030041801c11038020302d000307000905140c005808480f003072100d00c2030345c1d0340c1000c0818062103140c0664082c8100030012040a644581084150ba55030792207519040c10001c4d60780d000c0c1d115003080d610a11403100c12085541c441d115290303003420000701031344840250510300172203030100c4030600c0d5010440c1d6244076402001d0350008c500501080c40420441d0088284406116100952000700f200d030400028850003c03087d4480420000024110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 205762895 1250 205761645 205761649
    0x1090c021c02060f090a020d1104060305120301030302010501080303090c0d030512040f050607050901050f09010207080d030905060708070c0f06060f0321111504021c050c010201240302040b040209 86
    0x84241c18055001d030308102e0400c0141d8400a03145680030440000130000d910454000c2286050385d10000f07425070000202c62202a00e494102030001d65201040360b01420581070602c180b50020300088006509000c000200c2c480700005980c000c8a00c0805401402d161701c08102000c041c0e200224140482441102031622400103000c1c41280507501c42c1c450300166207000d81c00c5c03003c018807200a004082c0705403199070b64008151021501d0503e016a520304040e00145e00d0314500c2e80c0600320600c0f5003202b0311181070341504135100d4948607208944650301c41c001d060700d140c2d034200c40100c00108610040e0f000305100c2815903176198081d505c0046c010392602917080e06241c1540040d030750103e20400d4603130311050321042040c900740f061070303c038030480c1500001c55112118041e50704802d02002000c10295030700e42d625810007140d4121401c414454502d880c03900e6061080344180076501c0d180c0c0401250395004c41c03422141c2c50386540b0403442401c3d9400c00004102c2185441c1d0000c6d82030250203256 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 205764145 1250 205762895 205762933
    0x60f09191b0602030d0605100c03030b030114040813060903080702010c1703180c040b090c030a0e0307060501081603030f05130b160507060e150307020307050115060e0402030103050601090c02 84
    0x7038200e540c040d503900c41c1a81000300c2546c8955000b24060700100800401582e840290008069410310340407440f140c2900c002030150210070f090801078000d0b03400b48400c1050b9500140142c03580004542c040070f80c0d4201c1907400e0440c0c0d1001802024080000304010740c03041c45020100c0b48a4802040c0940c050050205160004c0310a85103d60720003c00642c0c8460030405000d01d0b140442d07062095448410100d260780d480500400c00b1034502201091100500741c0000078940d0701042101d40755005401c002c0c000e03003004c0c82426040e01404140403001e581c0404030034296034240d143d0814038030015004540c40c0d0300041495104c00075000c00440d800251000030314110f250242c00114040603401d059042c0307490f540c449000c8c8000f859124281c2e0f03c0f280d5464650103121800d27240c0329520450140d00314492400000e00301d51a2040030325031400c103503e1a10a4446a558480541c04401c042c04221311007800050709070b0784584010490700000e0303045000014194419204c1c0040c0241e400085 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 205765395 1250 205764145 205764149
    0x3050c070602070614160809010212160b060906092a070803040c0803071e0c030605100e0c0f09120a0c030606090b0a0302220e1e060f09191b 62
    0x1038000d2103003009000d03400f405d1072082c81d9003140801d1070181b4080206944203c408001010104041403c1010343e009000c10b01c0000090900c1c142e464007030700b0130100d1040050740200c1ea0201c20801155080c00c00580303ca1080c60040c110080c80d403203c00ca001c01111546900c0d4052401854041c02400a203601501300d091150700e00c15201e0500e49407080514401e60084d5045500c14400c03c401b0a8030308444205254075000c82042c990a1030030701100380906900041e000501f05030510841c0c000082040c0204e41c00345441c500c0d00c0e00c6085000c1c40610540c0e011b28401d00301400442c0d842d00d0200c100c90740c0301d820001141e0905245540740d914440050b402038070310b199180e07010050140103001c2c408100c442110582812070a541c0020050340c00c14144502d0703142d9000140001b2a0b09174040412451002d003211500b5852582907116070406580040c0b81e80100008912500e1001003103074003070110b01025100c8800c80f01400c40311001e00002c207a4420301305051641c584440030319403c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 205766645 1250 205765395 205765397
    0x150409090b0a0617060109020d02090a150e04021c051302030f030307180302210a1502090a090203060a0b070807150605090f0705030112020103020903070608061306050d0204020703050c0706 83
    0x941031400224180840d0f40b56801584802d4148603250300184020810a045d555141d00068440f0050740c4240004d010b000f604503000100800041110025071403e5036008be51b540d00c0c00c0f10807182c40d041c44203034000d115100ca189003060b0101705007003101d50801d030390080041c031240011440300d0300000d252104000341c0310500d41002050145041d803290035120580000200001c071203240d640801c944070800d000e00642400f901c0d0704c0c20400c50b010f1241900150b00704c011900300041031080d1000a510084032640f04140109001500c021613009a13481100b000f003901c1c010503d4a01d0024441e40403850445840340f08200d40f1002421841000740d0034001203200040a03410601130100301c40002d4a084844080c2c101000401c980c440c00312819125058441d0111500d5071005a001e8028540010b13414020080081459030f0322072004e41c800c840840303031041035103400038400302211a035000b460b8100620758080c03009814680c006000341846131514901e02420608a98141240313030700104 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 205767895 1250 205766645 205766663
    0xd0c020a1703240d02011116030503031609030f08070f0609050c12010504020f0f0a0f030602190f09031709060a0804030e06040e1902040b0c0d030f050c030615040909 73
    0x40b00703c50032280005000204001034030301c0307840707031100080c01c00081410007410000b9416001500070380c14850486214550815041020349074948152203800c108c640f04002140b0318022031040c4c4c8103040800071250041d4100d080a00941c40b10700300740d4040c143c01d50303020284034803540000b0104e00c56203490034081c102501c00c0750792640c108000c80da002081258180e040005110169440b80d44481c8006000c031a43e041d00585980440d10740c0c0740320381c011200080071520002c02d11402e03400501c5100722b1048030161286500105403844000001d8910000381044000c2c40096400c0814640100c1e0b0650482d00f840030035400140310394484485100011054401d010415420000294012004480c9581003900340b12085c104020000c0451a104003e900d007010f1440c030741e504545c0581800541c00c0e5071a141080c401c1c0d591800301340d035940000e207010b4040b030740d42d60f01d803041d035000c4c46401d200940f86480e6803081048064400800402d10030301013100080112103407040007038140c803640543c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 205769145 1250 205767895 205767901
    0x303010906030b0a050402011b0201020c1005070212150408031b0f120609360d0c03020d080c18030709060f0e0f060913060b150d1b02030d0c020a1703 66
    0x69401c503d8003404a600303a605200c20b1100507030708150100308a00c0c1c0c0120304011442507000403480c203242c2c446000c0d000507144002c9261241d2241c0206045402501d0301302050845007002a942d074001d1480010484800c0c0200b40011100e07002150003190f42d940024450040c51200440c40c0d0041c3c03100c01030480c0002d842c420745000499001e070700c454116085003543c90000f1200700140f403002d0500c40180b4540c0030084030040c5d01006038601c0505c080403180368510a00c0050201c200e0101c0c103a0151040941c201010780c810483d40340b0480c400b40403076042181150a107000030441c40c108c640d15020758040032500f200320340300d844000c0940140c24244107203040004901078401600d00c0707031603d040f03008004541c1c58402040b600310031651707886002e070619030528070000d00c1c0702641ca41e44040100300c109840c12600703001d4808200d500108201c00e41070354607980682d003043d1441e40b0260b04248121000f0108503400039460401c0c038019a0307078403062581d41c01d11000d510900180400c0c80070080c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 205770395 1250 205769145 205769153
    0x5060c0415021209040b011209050303040b090109020a0303030902060702040c2102090306061c0b0405010f0c020102190e04021318110c071809020904031e020a0b0606030a0b03030301090603 83
    0x18404940019002800f0043c070341c0140702c9442d11a07540414026070712101803444691007508a100f000802110402035440c3c0d600d03210392a07500503241660b41c400c00d8800300c0d62079103061148044459000b001104200d141d03135016809402c054200340c6e8416028044c0c207025032114062800c55058070354551448040340394100c0080450310036140c00c3c685c8140f040c006581c4001800c29008a0112170441007502d02c981c1c04107502c00b0500000f04a1500c1030140010400c05401082d035400300007009200510800c0412400c0340200e0840030421100b12960940d0b0602610f8002611032003d40090f140034007160080384c0c0055103a1103062805204404248525400e11030b451101c6404201c6a281000ca0300f07000f0b1f40d40d1040d0150714220101c003402c4d54a03004550b400304031060b9001d4201720040c5054180500b2051000990400c060b21800105205910214018600d1039010002514544698040c000107400c01400da01c0415514103206070079a41c10400785000b0601c940012407800d0035450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 205771645 1250 205770395 205770419
    0x10206070903020a0b09030f0d03020a0905010305042001030e07140f060f0a0503060a03020405040305130f0605041403070503120a0207080c060d1802060d0f061505030c0309070305060c04 82
    0x400380e030030440340540500040c1d40d6000c4038070403501c076901000e40302c007803060000b400d00440d01154845031264100c8266031340c0c4c044d006000080d01c0d68840883d00b655440041d410340740100d40051038403c0100203100202c5055840c542c1c81403040c500016140d0382500481c1c030300b00761a0028020b81c1d4102d10312450a1410920444212605442203402c008000b030390030b581030080c0540c94040c02004000a6001d13101c554085009513001003040c009802c042c2400f52040d030040c101e203a080300021101258504c9a1041c8100b16107603981c9061800d40b51080c002c20214a03010366641c103011b4800c2c0000e851f60700f00300c50080d8050b80b8052540d1585501000383c0380026aa00202c0769030051241c031040d55071880c5c00c6e02c180600661010404000040c241c16121012010007544445d01051060700406c00768401071040030100030801110fa21040741052014810510078002002000040c040016810156401000b24000c80c0c811036100c0c0e580314200002110322400700322010804100840390700e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 205772895 1250 205771645 205771651
    0x60509090724090608070203070f06020d29040221041208181c020307150e010605220b061b1f0c0915021f0e01150608010302130f0507020606010206 65
    0x10b160580b0301980311000f80c603180a6108400601202e900041c028500910844602a5100324500e00b24000c502c0d064009401c500c0301003117020302c1d141900c4201102c008000b440144041a11640e50f2203030010403001c0c2d40b000c0c1e441051040366100c414010041021081d010f82d1040d8043c0044a42413200209880e4004120340a14080c440c4d10607101c00b00411101562184a0000102d40c07155000c240e20310b02c40d60000070710084001000d150074500340d61040a1880e880002401840d50350400c01092060ba24114850f40c04041c80c2c0a2203d0702560141d84c2152019044c01c2c1000303074201c6141d49902c0100c23002661034008500d00580790f030604070380c01004800d626080108021345a00200000413030300940780404505880ca180c071350700800c0148108131058a4a0510f4450081403030082c00d02c3c030000711240d42c24a840c070a140312032240000c050754103640c1c50f08400da207940c00b000544240c0c2080015080c1d40c07034000a403005001c0c0602441400075400809460820200081c0383c02c20007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 205774145 1250 205772895 205772939
    0x50a09150203062805010804060e060f07020c0a0806190b0a12031205090d0309080d06060203071505010506030712020f0a0302120c2703010b03030a1d0a060c08030a0605090907 77
    0x2054070b01c1d802c90711204d20f201526030a1902a000d80d032549024801000c3c4100d45d100e151045000b0409148640048540314483c00c4d42030f035442c2065181808540c14150240303003c141c0141002a0310340c040700000244445006902282e0303035811101280c144c5a19411054840c0030206180c030a150300b20420740220000e00904000a00e003d15160b503c1d02d00c2e2598000805444071f110406000c40d00040d01c00c08200100300700541540c0b4600a55207601504044588040c0d144008034509030521406042301c2d00505454030b0760343c07030001c1185d00e18801008004040e9090240105031901b450103010100d00c103440059507016000d1403031546010003031402c050348030304121108602000b040505490030300c0404800016610a0001303015100600c400c680521000c90342000302c6900c00c0054442452405044e07542004035030501181800754003c0c4404180c5a50074680054400c03402103500c04c0141c040011407544400c000b8401882c166445959a401a0000e00c031900e80c1140c581050b10386 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 205775395 1250 205774145 205774189
    0x8010e070e06090a0b060315090a06080a080309030c1005071803110d050102092809140f190c0e01110c0d020f0d05030d0c03060503150a050a0915020306 67
    0x6072091101c100c00000705528018540c1c040801d180e1141e1750400d8132109001004c1d0794a80c609400c41e1203c0c560100c040b0380c0b0540040700416051040c0d0712030401520050f0014001514043d141e60401e6480582480101c5c40104480007074904140410105581e0910000c521804d03c088000d103410721400901c00d10784030003c010030000305035500d0284110425116014500d481d81059402030295402d0707950428841c0840c86e0004000c0040d00a81c02074146207040c2c041d03261061481180c007480c40012507005283e01003045919084480fa90200a05031a14120020461a48240c60308840c850300070806007110780803590307001110340c00200d15210082c000481036170002814528a40ca010b4043c0302c05000303039082c1d612429803101c6882d4000040300d0b03540131505004002480c0342d240c03002c0024900030b00400c80b0314002c02c40d100b581003030034803800864546030040c1000740000341c2002c103215540c030b84220005603c10b000007070030403c3c0d0500581780d2800320240950f06041644400125207 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 205776645 1250 205775395 205775399
    0x3030201090c33090806012c040302030d0203060a05030a0c08061602030d0b040b060a05180a0e04030815130501080712080703122706060b2a030d09080408010e07 71
    0x7440c1c1c07a8040c050880c90640c10045495a0401d41e04d40d5550f4000348540c0c0200e80010901401d0880046042e5114280c40b031501c41c0700642c0c1c1822035005540090058200b040921084c807156009150008001840e0324100c65940000070300d1f2068140c0f040b10050305000041041403c248111940711940181609001c400341c0030003510b80c4610300d5110341083e0b0b00c185440e5251525071158640560240070a550340c009102c0250054010201c020024448110304074080d05280c1418001c403001d60f06468100c0d11141c1e0240c685007802421034803400c01e495000b40256840c18108a1162000700d00015a9410251294100b420039080384c003036542d210404100180548007140c000c15058640341107803004034100d1501512060350302c1007801c2008401041c000b1041082103035454031034041000400d941d215154204e000c6c5090b904034a09a03070440c0d84408101c100c80541c4203a5907401d4034901101c07440c0c42800c5510301142a10721108c00314041c0074510003440b030412405d181d82c004140d154 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 205777895 1250 205776645 205776689
    0x110d050120130b0d20040305070b1305090a09050106060c020906150306011808071d13021c020f1831030e0103090611090f0d0804030206070807080403030201090c 71
    0x1501031003620303a1100f000582040141d900c2d80440d02e0880d20b804481d034038000c141c0300904c10b500140020f40303444c01655000514054a90110750700d2184110720341c16914540b500b08517641100500c51121640c90b001008005182885228090001912441d03103c100a0051040070800208074030301485560110242103802201036941c048400d180c003601c0c06441c0c0304460240740856024071101d108032070020881d0340c41c0342060b046c905d045d020300019a0b66003880b42c070480042d03400043d4100c0e0004440d03180b11b81030031881240d03050000c1d2120102d0710492000c5030310300e10303100311000505c0b12800501c00101401050040c0d0000c2000705000d901d51000c104107113420224900600380004609440c0059009800040d0300903008882000003580030045031105611a4506c144501c8600680756001d1030089444004603410041040c00c2a003076500740400c2c2d6000000590318100140a800002541c100091000e10310983c000b02d0300030340300e02d040071807031046400030450002c04c0c2c3c8a5007481 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 205779145 1250 205777895 205777927
    0x501030c0306020a110604151103070903020103020c030f210106020a0302100b0a150917010e1b0409200a0504020901020309042703050909160912110d050120 69
    0x10360b41040e801030b41c49080c0842507610001c203c0c0d01460034020101000148880540c50030384240050100b4814103072500d105861600c0708440380d40c00b01d031b42d0540a0026510071b0f806449400390040849280074074205034000c0d030f500a0105004584a4480121f203140128880b0030b00514540c00207120f80485503402940b614100640c06403025500c000714070701e40c1d880e1007102c00145500c204010050310310300001403051040c0e025003140081041254011005c05100e00c0c0862040403024003074206501d80599021007a0310b1481e40e1003600d41ca0650701042d10203c1040e846400b85043c010710403006402d000c1c4500459002a01c584e2040c81610206d9801004842d9815400c84000032a6004c407404c0c0b104203542482c2d03a4910300c0e9100c07801d00030142c020000b0602020103c030003c802d03a60f03040c030003901100d004400000054143c04100300c2d6140710540d450a0301e1141500344841c0d00044082140e00e4000c030410341e86030b0744604082d04000b1415800300391403404c1071041ca10301800d0385050468 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 205780395 1250 205779145 205779149
    0x2a0d050f04030b09010b0405010b07031e050d020d0e03030115030605030105150906010c08130302090c09031e0708011e0b09040c0510020307020d0606051201090b0a09050c0307030b0a0e010501030c 86
    0x48a14440300080700a813080d07002d2107500314010020041541c496104400355040311500318003050628002d981000001c0d0f034141400d4046644051920710300c00041d001a400c00001c8026140d01d0710201040c000c070910103107000e0040c00c2e00e0306000340c10b50440201a50700c00d90110340642d00d0001880b2086181d100100c4000c5410b60b11120551a14030048648400050001c3e00940002c00e074080c007404101070700000c0364000c588040c4c035034071049a14280e0b07114410301c16505500000b00703031052000100d0580140c2405809562955548100103400e455101c00303e02012162040c8006001a00b4031802e107182d6402d50740c83e01980b40c503a90b084a01c981d9406181d209448a032038810b080b5108008842049030702400c44144110549400300c050075003409554440c0c003074500cac0c4140240051240d000c090390400e07401451622020b1101000780600202a10303140212213014a4a40702080424010751141031a00321902d40b40c0401811030302503950040c03250341000e0041011034000c007140c8003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 205781645 1250 205780395 205780403
    0x1311070201110a020405040b100605090303090d0c030b070203031603020903101503081804061d071b0b0411040605100c020f06130f080c0103020a170c2a0d050f0403 72
    0x624800303100d0b01c080c03400c02c407210001e605c1420201007000308890003685900480c681c0c064200440c0c0c40b0ba5095845015604070207405a0051200001c00d10b031081010403507030b014456500469071284c41c2c1480e409412919100964400014094814943d021450030550145421820101488002601d91002c50091130344140c4900340c0745050050600220003c5074030110080c0c0c0d40b004c0d240080102510354400030300c207501e00080081c0501111020705501421001f5003103165455040552354501690a68000e9a03408185100090f01407800d590169006420010000010b04100020b82c2d1560300003030f0049010b05601c040c5180c0142c10320000c40d904a44c2e183c0d0343e00606000c525540036800094401200300c0d000000c01d6100040d01c0400d4640c02010b540710005c4660054050744103000d141d80010b003c1660354050b40c41e540b2a13181c0c0001442105074541b0101c074101a00500100080c800f03084200740000445940c204501e040401d0641090340c01c1c1000e007044018075024a00c0f001d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 205782895 1250 205781645 205781657
    0x10c020d0809060c070806070302031e0403050715090212071206020d0f092d02060318010e0708011a04090c12050c0303030f01050f041109010c060e06090c1311070201 73
    0x300400592106503000008041c114640755140c100c4d9044d074800c2980300f14180e83c050300c070200b54103d21a0003220f104251040c0b270100740c200d450b0180e0b000c0c04001041502040310034003c00001030b1903d0b07807510039111040390100c0c2c01c0e1614010041d5050308a100405254406442040440c070800780b4401c2086d042640143c0754481030a045c030141414404030b003035091406461004200e200c1400141031105c4130a00d1004d200d03044a5298003001041c0040c0d4884001d00016078181e04200100503140b10000000c00c00c0c2821451007890003070a60003142c60360351500d8582e0b00c8004601c80d46209010100c40901c5001d40545401d8080d6002d402000341040e80d840c070790b80501c0360411224a4408002d000c0320380d00e14201200d107841c0b000a00826101d581010b002d00740c2c900d00f03809a451b03c50703000501c5514000c07901c8015602440306c000110f4445841d42080343c10418140410ba1103011410040c1820a501d6070403c4904d074402507030642000d2a00d03181c0e2055160381c8081e6804594282800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 205784145 1250 205782895 205782919
    0x4051527070810050907080c0604150e090a0e0d03020f04060e06040b0408070e13050714010c050114220c1a040801020a180807030f0b0c090a0b070c09050105010c02 72
    0x450030507145030410340651054030603c0104101c00e0f44002c1c841c4008601303496009440d0601c160300c0b941480401a400380040c40140800496851003800c200c54a0a00c0500c04490300041003900c90101c64032a80155070380c0a1240c8183c043c0132002d88040c0c00e1504501d04807504026100310b0089004c0e007010410702e03000c3c641e465264130080303801414081604e40e07117507070b0340d040320665440d00c60090b40407580500b404240c034041070081c0c900c01c5c42d034444003404030320b4100302c601901f2100d04014681081000712452021070030030321800d0f500d040400000c02c00da2800c80e0741450a110711088040c00c0c244800c000d50041151070340604180c070540740c40c40c5c10031036910700ca41c5440c1c025900481c40952001440d1521150004003561451003442c030201445652030048070749407030140c0710180030301c0c0d82940182c000940540c03104d44d1010030013001c0350401d00c0446c007140d9074110303642000c8081c01d0700080321014040c450302d480000303020040c0244195030400b4002002c01040c0900207000d404a4550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 205785395 1250 205784145 205784221
    0xc0c1214060c0c010606050c150601091a030907050a03050616030b060c010507020d0f050f030a061208030a140411010e01020a0219061205010e0403180902040608040515 74
    0x1180014401c5901030b0404010001955103d00c0003401e680d841c10100066041c012002c2d039004820b180e01030081c82c011009031020401e0028282410132100030404103c119410700c04000e4500c01c2401d86842c0c0c901408410300d400c150780c000e1840384c1d0000008100007040010301036807140e000c0340300c0d103050428032b001600900511900143c1c8070101280b000303020501584054410300e23141d400c40f808001c03507107000c5d6000345085200300d000030000c02a10010720903281c01150000d0344800002082c664401c014241d90448000442c0c03088000000d01102c6034460050440a003610300e8012501d05103507480d001c2030340900d1071450602140391000450b40c0e0003404001e0440e0b40107402c11343d060030b62011808214400d0b00428001c11114400b4444000d05c501c01e40d4143c0340e040402d010700e51035503101a03402d040f02c11425148095010808510340503140058401005151184034050a00345000f9081800729203064400d89900c0c401c000780b04151070800030b4080d261030b2400362111101c107d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 205786645 1250 205785395 205785413
    0x30903210f030c071a070519020c060c01021c0204060516020f030f060a0c17151f0c03141201060e04060f031202160b030f0a0b0d05011505010c0c12 65
    0xc040140745030003004019062540c600100f2040d0711030032062408150310301c00841014000c0e1125070002d60107008a442800d0080c442c0620000c65004480d180e560140014809600118841006940103e00c3c03030003115071031011030703e280381e008025414103003009802007450040c28400d42c109030030483d031a010340d20381070245804d40b03401a050f103144180d800509030362031106940e0b015889186c0207204400f1486111031500c0200400f0348440c20361a2864822801a8401d12040e84400520074030760f481e9602200650403a441070b1921000008141000b415807803100090a040c1c6c5801c02600090a0811009605503051f90420300040750181d004540203001681183c225040350440c040240054203680d451022541d90031116410b114803140740485001d4401e580c4020f41c00d0010800c01c4071040741a03680302e00d220000140c150030410000350712002c0b0103003d0350b40d40d640f540ba00c00d50345161f09841c0081c2000b0700b010244020303550790b0008210034a204040480e4481c20340e079010031061301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 205787895 1250 205786645 205786657
    0x120a0903020310060816081b060f13030b0f150904050304090204030602090f030d080408030717070c0204050711100207020a0503010207080d05010e2403120a030204080601050303090321 81
    0xb6044035100c140311000c480c0101100d015a00f01481040103107402211844142003e640c1200050305130f4015580a07400850700041d4190703840324084c0301c0d034818040c80c14082d0100704c500c520340f004010310754209804014000342921040c1c0e48900204400c03202008984041c2420540313504440d82e84c2c0e81080ca0440c001c54004e420314500002e03000003403044030b40240001c41000c50745482c0341c501c1c407002c03d03a9690b24400ca6070302040004c1d000030041501c4001955100f1842d041690b041e22541d40002c20b41c6c082110000081400c41d45900c06605042c0301d038a40c8858182060f01e0090090300301d490b40c500c03d00d140f105c0980e070001a204111341b2a180780d14000c02002d0025900c0300c01924040d4803582110143d08152840d0200002c2e052100c09032203400380c1d540c80340c040301d000d100180010000c0081c2030705c0c98051150f1b200150302c00c403c040050005802c0c5940061325681440125803c180041e4003062007075000340642140b542d00462160035603c480d240700b4070441281080844640560 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 205789145 1250 205787895 205787899
    0x402090403201b10020c1012020d0606021027020a0e0112050f0d0923130c02010f050c12040c090501180e0318040203060d02030604050c0f0909120a090302 68
    0xa009000301200026400d80300070071840e0141400f03a0070414030500c0c0b0901210701c40140d01002c044041d500304004036075440c0c90305180001d440c1d41e240f580381c0c003660311580c443e06030166100c000301b090942c10320001000501c0c110301482203101040030070441000c4921300300441000185c84500310354817440700200806050804102540e5034046240140c00f1070442558940a0301c0241e0882813000318040300a050340da00c940316510b04110041c41c000010380d25103004030248070b0489135107a48854061507100d0861102092032180f2078002425250f00e110007100030740c00c02003440300c14200d107000e80705450340d94414882e03d90380b5400d10301904029a80460240ca20386000810351510914100c1d00000329101d091082c841c8400145a8910941c800581d000d04c410040b4007140c905500150f41001004280d1010180d00b500082c1c01c018080e142181d060b40b04070345e6100709090151203406440c80454078943c441c58907419107901c0c3c5c0041081801110b00018100d54882d02440e41c0002031500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 205790395 1250 205789145 205789187
    0x70905180f0604020306060303040e01060302030601110105092a0105030a0207110a03081201060f0e0411090a06050705100605010f030902041107051006050f0105070b10170a0c05090c030402090403 86
    0x1c18032000b92600400d8505074003c0c0600000222541000030849044450200310454180e1800d1000c070b00075000980313014100070502c280000c1a1000b4020300340103c034980302030002c0082d5001c10301031b070355269001b06a0300c10f00c0140a9070140e070410203403580905a00742c096a65030032441c000c940c0520b40c0d440302c0e51140380050040107201c0381d10050424500f45441c1c008042e40c03540000d86045204203141d2000443c218840c3c409810203400505405140180203400c0010510008180c0820f9400c80b20000301c001c500c14061240c10012031403d040020000c108031381c20140000e007100f6825542c481810b0b161035000c3c045440e0f42c2e01010740000c1c0040c4081e162441e614141c2d44584040d00800366040c01d10401003494a0300d6201c1841c0c01005840e003501d006020b03076515000f500001c050300100b01c1000400102c0b00340201001524071540000340003d84070a24000b03c403600290003560148224008100300d40703a51030300b1240c002d50100c0704120b00e0b070b880e80760449010007124824108501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 205791645 1250 205790395 205790413
    0xf0c030507140402070209040210111e1b030604020904080c0d050702041a0a06030e100207080a020f060c0f0f09180108010b01050c120a270f0603090507090518 70
    0x400450301c0c0d010b98411a540b14444102401007000340e000b244406580841c1000c0461f0052400441f100d5021078181005004041000c91080c1803c290020703d181080c1c040c44032130010300040c000152070301d20390030354020780c0c07440003001c01d54a0703900a10080c000d200c101c0208043c8001d410944a680050320b04640c001c68090700010103d800c5144128002c1d814500d818030a07a5980c0d04041e03c0c0351000d000c1c84100e81c6000d03021006000303034441c0048140160b004d204080d01d242e000400c1800d02540496540300c82d1010000e00d400d0045e10001d00d240c002c101400303108201d032002c482e4070081d807032400d42e180c411900001489200ea824400e51041e550321421051a4100039100d0403241580020002005040300640e0988542c03421082e4030b0b040b11804902c1500340c0d0020342020140c62801c544002890b81c01d075804d0700891450140485c524420420400c0392410110016241c1850248005059940c0b00c940d42d00c0e00e4000d8011554442e00021303449190344017502d5a880c003100803103e41c02c5d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 205792895 1250 205791645 205791653
    0x3070b0703020a120e120d09050a081e0c0c10090503031201051302090f10020118030c060b0a21080906130f06021212100504020c0c0103050105040605060d02070f0c03 73
    0x76120ba4003840205891303200800c6071010741d104040750148904003070440c2c514000072940150f44a03082091800355540d102c8400f1034002c00c88000070500c10351841381c1d40c40121009038122180103242242440003040005502d071400700f2b4071304500d031099800e800c15a660300000e90301c0c0f0290380c000e0341d0103100108066035100804a0210304941c015200b042d282110400d04a06a1207002c4800b0342041d2072083d00c00c0c00d41428481d0204c590420320000a80004c04081d8a0308840014401d50000d690030f50700f0000e20070144500601e10404441c0213030800d150180f4080114204440d20503400d80e11903100081c094440100e90701e00790028800c50b07850025910b808580402030140b005001400100400c10a0000a1350b032802c0e55280e0403241031000e8001c06246a0400074040c901c0d51442150014440e11f65002400000324250050104446820001411a00164030a52096061500420032a2100e0b030448000e880221005681c950103800c2520180342a078100034030180030014004240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 205794145 1250 205792895 205792897
    0x90304180c090605180904020414010620061302091b0f04031104020403020a0302100c080a050703030506012f031b0606030d030905120d1410060207080f031b03070b070302 75
    0x40c41592a040c80c00c60700c03020104e40c1c03030180d00c60b80381d10408024554240c52801c82c0b00d07690f000d031008001254103420a580122074400c203a00c03c00104441c04c60ba002d076008041040c41000042e41c0090001c1d161690b10180ba0710381d4554041e0246d1645400700c1e03203c12942c008507200c00c4040c40b040c2d50750005003110040f07aa110307110030340d0f00e160b5052801d081e40c030300360007110212600180304d000424110380800040715650303030605003440307224028040060510f101904003010035855658840300c40d41405026101c00030403150402003041c60041070b0b05d140c7d14000303518907802000900002d011000c8070303107540310769824102d07140214180a01d20f030030001280c910038002a0241e908580700f413071051301135170161440100303148c001c2e41001c0728019512002d0818550024008540c000c03146404041030b42c000d40716000700c034010340810701071944c0400a00b00202803203002840120203465910b40ca80c002c4144088004000c0c20f201b010b154001c00c20707103843c2500414000c48608101d1400390003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 205795395 1250 205794145 205794161
    0x6220602071e15201902040506011715010c080c01090c0f03050703020d0816060f050903070b0609040809031b031b030d0e1c0b010812190809030418 65
    0x818211194040700d041c0c0e1800714001290790800c031080500c1c1d244070040c1c80044250390002c1e4041c0c91500c07007183d14401084814801c407103000175a81181241e0060009503400240264148182482d810b412443c080130840c0d480110000010840da00e03c1004032200e40c0e02020103051150b010440c031080110661103001c40c18807030020900850354454020120201d42c1c0300c0a4403a4014036410000340c2050851f00d560203100d140050301e002c071840307040841c0701c0b03034204140c5410743d031013000d200d246503d40f0505030403050fa80001d5060450a81c0d4440444000410503409240c40c14040b404102c0030005840d44c1b03900003410340d001d8100c1442030705400c050740c01c8103038030138424048600e0b5100000ca240000c44100a009003c1c03030a0f000c54240d805081112120790031020070858422100090007541290324402c92031a511549850f1090b407034000000c6205810100c100103010100060545003172031000310381411403584d034541c00c0d0382c0d082d030190b90b0003030100042025800000461903449192 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 205796645 1250 205795395 205795409
    0x3072d0503070302031c02070b0703020a0b0912070222090f12170a020306030709020408030408070b0c060f070201110d0c080717060f19120c0b0a020304050622060207 73
    0x1200690310030415540306014030010b501604400e42e8541e00442018603186800600d004488043da9103079050344071507021001c10380c016080a0443e8040003040440950850b0301c0c54000d100c104d03a410012507240c403550740e0003072241d50340a4141c1000080074030184460448110200700840141c1081ea1500c92100310450703110031440800400c1030301a07c50b4201c504044c01c0208020b50701d44588038001e50000d80855450b20444200003070388029400104045d241480c0030390b4859140c203c0062510713140e41c102c40c2110401f40a650f00c1c41e1130004010358400b40c1090180007070744a528040e4014090b0340104000c1e0000000c3c05007110070b840d0020310305450f003a47c40c0010f0340c1d0b4083c0100d403040c90200ca240341d0480018040382c80d0b45030030f210103044807500820041c210082a0f4822292415503800700004141030782c9588184032508905034010182d0032401481c004480d18006c1d100d02c1103014480c4648000304d082c04d998091051081030300742e408240028030f251a440042d595040a1040c0c078 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 205797895 1250 205796645 205796729
    0xa0b030403090f150e040e011416020d0203190c08120f01030c06051303030f1b0b010608060a0308030103020409080913090b220803060118090b130c0203070308060307 73
    0x1380d510444024004504040c0d41d52200e802c002400c00000c4c040400c0210615922144003400c241210203106010b20280b103594030a0b01c0c01450042d0900c200142c040003950030901c4181c65000e03200044501d0903030030341345c5000800c40300d140c04415401003c0c12001103050074002c01000c58aa4016a8166400340d00b00d50305499a480c41120700d48101281c00b0070700c42d010300d02000000d000b424ad403510005241410190001168410240c09070302010585042e84400c00403c98160440d050640100b41a60007401071421a01c0b5969541b00600c0024040c40c0d840008909201c1140700f40e034168000181221505203040841d0405001903032000d0300d5001e030384004500c21650b40c03100e540c0c9401080c445046800401d803208401508007d100d039051201e80e41030a13482800d01540203029150314400002c10b800f101091092442d10300d0261004285403003044401c05800205950005074907207081511030303888038042818180580c1c092901400c61801e00103103900d05625401030190380034020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 205799145 1250 205797895 205797899
    0x902040302041104061e090803070b0609060612150a0b04090912051608071704080f060f070e300d030540050d0f030c020c010906030b0a0b030403090f 66
    0x10100910a91003079034003107106603858000c0c001c05504d01c41b0b108420303401c0400c00c007542d0340c00c3d85056900505048031038a03040002c0003903628025100315000041a00d8403030424803400344102c401c06010700800038502203031110701175960b1401041c00c00380156450090b20346a45000300005480420340c2182e00c1c2540706008040765200748242d45204541c4051081480442c0c0c9030050181e000c0074090b10f584446030540e0200201200007400101002c1d402403140074488441c4c50304211010703040310b01006090007800110307507210700f81d0a4084421030b002901601540c4d00c0c100000010004041a0780c20b41410014559020134280035400568409201540d0751583d401080d20b9000500070700c5074030507030394100708020480013160240c030b625650925a07003e544885140101440300c0500052036040070144040e40f601500064081070b0005210a100d03000003c0d0400d500e601a00040541d0b0310140c40b82651003240020041600c00340c100d669050600300144461514000c9061411444c200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 205800395 1250 205799145 205799171
    0x5160510141302030d050706111209071d010e0c0c0d1e09050a03110d0b091f02070f02010f0c0b0c0406021e030909060d02180a0c0906080f040303110301090204030204 73
    0xc850040740d8020094403440720780314000d41b90344c4c00000055803160340d10351003149010860343c010302000703101602d0744801c0d2802407807032403400005403c5410030f854480b5030000b100000500144c150f4408440751007241e6510040b10480e401a071100c00030601c6643c48502480c2e0b00441104a1000d5a902606403820f1500048d5032511041c4100341e04010740800c104080b1721044501284008020110100041d0513103454000310350a4480703107e00c3d04059942c01c107020854903003500201e811603080d4184032290b2501d05181c410084040d0603c00c0c849006d9040078441c00409292075442400705100c0e0414030195880784c0c01c02e0081002511810608176242407680c0b27084400345500d00011032400e44c501d004d0084909000d040c1c6d50300309105001d100016600e000003944e0300840b000c44151076140c0381103010709442c010343d011020300c08c4565051000681c403c4800740d111700040008892510b442c40c040300245591800051444408400480c51180f982c008100300c0b40200c2d418014900f100d04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 205801645 1250 205800395 205800421
    0x50307060207090c020c1216060c050604170f0a030e07050105040f06140d1a040b0f0d020d02062514010203010f030f2105042105030a0516051014 64
    0x15050141e44036a0b41041259000d4100410b07030300c20744c03044d50b03102100d16003c20715590902030740000356080261201c0244920b0746014004141d9454080c41c0b4026a0321440e03101e00300540050200a000400b0211402000084039002c1c0c048014039a901d000840c0000e004201042103614140101e440c0002d280d0302c18020340e13044c2c0b4803141c003469001d8a00482555014104a0300080b00f840a100441408202e441502d40d0341c04560360790742d641e652000400c021078051902d841d2207030914124414094486d400e11170401c59060307a44510280d124000192580540003104003000c01400300f1190509400e12100506c40c810040ea80d004840000c1c03050a030b0009028422a9951050042000c6600b0400c03803c1d25034020f050340c1024902c0495201d5003455004040400b0450018007081344044200c0300c0e131404428084400c0302c440440c3e407040d4480c0300b503019103c100400402c9051552104140e140078580d030140071075011840c2c2e5403040020b801801d580c030403100300704d10020303404140200c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 205802895 1250 205801645 205801649
    0x10509070527030a030905040c03110d1a060c0c010f0305010608060f0d05060906070f030e0c0411120a05071218030f051b15010b120f0a0b040c030c0306050307 70
    0x501c40c14100309680c05064440741180d4044098003031860303882d00c040c0d20140215800a4000d50321420034905140c00e0000791295080328008151410025940317590f441c00550341e44020340340300070030741c100210744070100c10301c040316070603881540011086040c03079001503011260802078a0328901030850307010540c100c1303409114000110b0840b00008015140c0400807070244200103000d03910346c51003034466916103001202e681d00c10b030b800141800010740d0402d5290310030700b03003901d814002c281611003450b480b01c012030740460245880c0d4200c940e52262940559051506034407502c1d00d546841070038a005002c01792460008101c0c1d002c0e90a121450034051503043c00411141c400200e005581c0490302050703c0c0800c041044000d0184202c280c141c1c04441007440c5102000701113003003046901c0d0340c0556060740704080c5400704002d05109030b0f1484031078944c460200c9440c2c44150f60b4081611014002d45904035078007500e040c0c11088140d400d68001180392596540c1041800c0d26072050640e210954 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 205804145 1250 205802895 205802897
    0xe03030f03011a030903043302010614031b040917030f010504060b07020105030403110106080f07180b1c050316030815010305011a090307050306280c0f110c0901120b01050907 77
    0x1f008103010300e06080d0384581d22032034143e41c0c0c822050b1042c180c84503003070451160400183d456003801c200c04540c1805903115414100c018251040c1000c5800d0103809440d03101601071364861122900b070000c0d120f5180b5a00e14000d080760f0b0781e4604035150800c01c117000d0268902c42c3d8900500440d034112044195481ca5a06071030780c92450b1910f440030b46406e0030490104440350740392040441e05080c01e01c481d1403c00c44a000404101303080442c0032108810001042048038030306000e502d0540d80307800f4007260207400c0201108891450f03051075410340c413890454155401c500166002010360011b134140c8903a80c2100588072015080004509886080c4959a0f4aa21000000d00149030305e038010039031414003c04031034410b982c4002090810504a03001507565805c0840ad040446800032750311441d01502c034003004800103400018001c000032200440400003a02c101070510202081304944804004090541540c4c3d0ba545d03145503044890400c851f070304030240c00040c06003080707103503140074040c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 205805395 1250 205804145 205804147
    0x70609051606020a0b07031a10050c0c04051b03040c0312091401020a0203100e030403170a080702160e07200c030d050301030f1106190206010501081e0c0a0e03030f03011a030903 78
    0x2d4001b084001d400c1c120b0403020420304407074075464640d44010150300c442c1c85548800b5100c0021a80d46800c0200038141c103401075051008010740d11404c4400e50110b91107894409071030384c5540c2000090640d09806c001d00e518419040342120701c4d001401e8404a4a504074118501e6180900483c0c98026440b0003c3d0107038008941c0301c03a03a03401a084107400d072010300100da04090f90b0f903e0b00f0410f000050031500314500000f13a00c090185e4820125940403402d80028074061400345c0c5450051810b501c41c10107044000b0000c07808085c0301d110708002e0300c118031104150b42203403144259240c0052491180c402e1180601004000340201d003076a04981d088240c17100005581d8440d10009550310418550000041040902d610f1207510f45107000f030b1207503000700259030400d4009842c41d8000340141c40b0403005000d0406072446114003540e0311880b004a4103844d5034990009444807440741c01c2280c2d03d40800f01e540040d2448090144d412200201009050b00440d100e011a10b03102c140c0c1c01d4a11508 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 205806645 1250 205805395 205805401
    0x1080a05151f0b0a03150f090b0103060e0f091006050f10051303030804050705011407030e0f0a030506100f1a0f040302130c081605090411070609051606020a0b 70
    0x412406181c1c0d20402803005012103a81a040c1e05502c2405600b061902d114041040c070758060389032048080e11a1315000030300380ca50070f050303403100d041d2414800c0c40000d5444200d85039003a44079405c000000d00e00ca003a191213500b80f003610000c000d80c04441c200341e503100f032584001140314503004043c2250790103041600d24946107800e015012040c01045000c0c071404004503450900030129250045010b9600c002c0a0b060510b806400c240c51644110304024420300e5066a003407281c82100e08140d072500b40b030010401000040f0706500301e0a10060303070003000710a0000610a010840300e01c1071824200d95811184ca40344d200c0b10025a901451462110340d8901001900c003850041141420a20304941000c0e52070303002076242070212002d03481c450345515103249811b421204c502d4001507005a040742d10190306000030114094004410b12072078948002c1c07170030069036038101c401050300000e091143c4076281c00c0881d928000c0b0040b0b03880058075444005072031031001c540d1071817141d0301480e80e4440791 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 205807895 1250 205806645 205806673
    0x10c11061908240f0d0c08120409060b04031205090a08010c02030d0f050103110607050c0a170c0f13110c01020f04150c020102120a0210060801050a1109090105040903050c0d1701080a05 81
    0xc0d00c0b10b0802c9402c0346c60003102080c1c0603400c0042c2d4540661110200c1d603103e0400028909480942c1d101c0c406041c424031003440015014120344501c0d540074a00503880390b00d203900141a000141d441000d00303519146045603203e40c084014100c010000b02d0034460084003e01c03000c2228802d102c040d08166210103050403034a407010042c8100d034022001c480410030303154000340c0d00d80303207e80c45184d6148480c40d082262400921076818074010481300314801040c040c012545944006410011b015a40d0300000d52110140080e82c00c04040c0700001c544440d500800031455a0090241003074182c1000d0f6142c1490384682d05005c03d031507044e8094010801c152a03031004c150070030420305e01503008002c0c4c507613086c580d10b1154400401c544000406c2d241480c0fa10070341125603c070607100b034400d01004000100e03210b50791400d04550f0103640010300c2424908007214503000706ca031000b40e10b001d80c4c90b0211507203a0045c800034010b036100c40c1007115a6643d0003840d6440c03221150040481d00000c0c0108030745 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 205809145 1250 205807895 205807909
    0x40f3b011d06060751051501050d020f072a080a290405060103110d0c05090a2702011e0c02040504030905031002130503030702010c11061908240f 64
    0x75040006003802c0740012400182c0300741c0810720f07110041c14078000061216845c10711500c2c21071142820800050030610008031046035481400c40c140180020140d0310920240c1c121041c451020f04c0303441c1c80310100d103000380c070b00c0d05030f14502203004a2031242c400b01c0303070380c4200c241040344e0300710004240f110002d5888245000300d000801241582e2407800d1a403050110f18410720492041d8050300443d810340ca80b07541c044000401e0f06014440000c4a540042d2240f07500b2015140103c420200a6880403110405000320103040e5404843c0f90301001c910210701c04080034018800d80751254203290170726040d030038804205810701c00a0420b100180240c181030340f100760030501900e8041c44298892004c2440c0190500340d014215500094015441001d00e6400020b8101200511700d8194141c0009055090400f40a40040341900140045a070354004941762084200d41c000d04607080650b0290800e14101c45440e5440105901070421108044403500f08810051001814000503010310180d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 205810395 1250 205809145 205809173
    0x6060408030406180e1e092b0f0e06040506221205060703020310050405040f06020a11070503060405030a1808070b090301050601090806070e0409061803090605040f3b011d060607 78
    0x7440c080e081c00c038402007520082046410303000507101c0d0340923840f140d0000c05640d250100d0720704006c40c610241c1020740e141c4040340c086032803c40b070031b586031072080c407132000502080f410000440908460010720b0f100100844c911280c012000d550055031050401d6040c1e06c421641c0041080c6d10303070820f014501d81944081c0e0014007400704d100801500c0d90715081242e004074016004181481c0320030041100420142000c0d00c0700303a001d0316039802d095490036501e025900c45e100c24061442e014558001c1d040110708010099001250744a550310380000a1580c0040d59440c004e50074440050303e15406562044200c862107c0100785d1a62200300480c0da0301c1444d041c06d54400e481c0d49500c000311303d00e4001c0d0368424040c0402c4080820091401528070b500716071005c4107012050108004440e021202d140494a040224200140085140442026110b0058180502510706c0c9480e01c4c0b0601316038074140c8486070b503542c00c0320414050740740c0802c0045684a40c01042000441c0000e01800f405501c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 205811645 1250 205810395 205810411
    0xc0d030c0c050a08091e09180a050a060c03050c03070e060306010513090f0c0809060406051306050405010e06010b0c0c060d150b03041e120806060408030406180e1e 72
    0x1590702d50b140c0b0b09208080400b65944000801e02c42e0741c514107481d035000c0040520324021a0000d041b40800e032904d20041018440c00d10314a03000001120601200341036940c4801a500542c08920385840246140c119450002e858000010140111141224014042074990709a154840d004010752070784010030b1507040003405d001000010203074913440401350400e000d01103a03180d088050442114402c6100303008004800c010320080000101e032081c2c20a41160b0007003001d41c0c3e500b002c804082008a8000c05c203503d04000c21040c840194440a466410002901d07020f0f45d0703c8040a220f40521044802c0e0343d007000c88007541034a0140024410a299104003103121500c00c000d10719080c1d01035000c2c0e22007210010400c000c00070300c0c8110703906980ca40c28062203281865105d6003400d44014101c242400f00c2040400c41c0d5681e00002e6400604003042101d0f0303030300d4643c40020301c0c8402c0120301c0084904050008500d00a00000551240e0540b0a90300c0c1e44004112200d540c09401820203a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 205812895 1250 205811645 205811657
    0x11202061603120c0908100204032301090206070b090d02060108101a040e0d0f1809020d11160b09060c0f0a09030219051201060f05101e090501140c0d030c 68
    0x18503c46424001c610106003145c03502000c082c03a0082c0a030401040d6015400102c0c810082403000421070306042e140250382001c003906404070b0004113401400c450001950040b000b0803030404104498140922803000c403015590000d107059003e036520f540a0140c0519070b00201410340407041035a10000c048416402040c1c08050300300d0209049681c0480041d1a03074000341e8401e401a50020408202141d9614050000d502031030982c058100403402119401c60300018200110502034026840040060900039914032240c602c0c600c0310843c11804603440440340b40040c481d5030010415501c1400c241c1d400720303e001c000046106048d0b021b001448103000041101102684a014010802e01458001d100312141083c04010429002070752400d51a0f040c40414070011045481b641d0444809941201c41c0201c401d9090b0b600407400c00714880e16000b03180c034006045a121a540c000c9580a0b20740700c0720410503a40b8084ca600c142072007085194000014156101d10a5003c0314a8515600d082 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 205814145 1250 205812895 205812917
    0xf010e0c12071703030f1510080916080319050906031807030c030503130801020a020c040f0b030111190c030816110610080115140d0809091e011202061603 68
    0x2222032036045090f407825070001c0100b14806060120054008007408001c403c0c8103c1d450001e4006610500d261003040f10207408124801c104001e07030305001e941aa09000b8043d100c1d003c655490300200181c2c8492003aa0381904003e50007a001c07201d0f03650300a80500c3c51030b92a080e4243c00c000c62041c4826071442403c000001040b0040300c0e40000d54031036005182d813009000d100043c01042500b001c261030748104001d4107480d800040c01c0c4a80c40c016240030511200111210004065408603030b501942020b1004444c600280c00030300801c032600303084003031118416208440a04900b440103010403108804600310006641248580e001c051904181c2183c05420250801070162060440a14007031030070f206800085c040c0f009032940c2c1110043c01c4500d0003886503010014284058024807440b501c01e024030a254007150b08600025015a555040c415142038624424107101c940c4400200300100c1c0c242c0d101c040754110141c000b4020340c1004464101000441d080710b42c2202404614841 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 205815395 1250 205814145 205814159
    0x31a040804050d0b09060709051f030b03150405010f0902090f04020d0c0e0612030a0522050901030321020f040311131e05010f050307061427030f010e0c1207 69
    0x40f01e0b05072181d0940d01842c10600c220030b2901e180035102c401803100824080c0615214400690407042442001039503068800c2000d074000c2045c1812240c02d4000c81840c42d03440700e80b41e40c90074003441c410030003002505000795842080b1a0a940b00945c041d4002003ca41d502003019001600140010300f08001100c60382c1e5208180d80e030710f03031106058079404010030901c1e241a2a0302c041c1c4500000c003551900b0100ca070700070858468020205070300640b0810031854403030815840d0000e441c0140260513a943c40b41400f402e0907031242980e408026030302403100708420760f500030340b510107042c0007407581014295552004501c0440480540000c4600e0310301155090500405c0c114201c50100e5052034070500da0400240e0740145c02c02c043c40d40d55114108903c2d100011a582100c10707600d440c402d01580961601e00720307c144510422a080c400200030354500d201d900000300c0742d004030200c50a08c40c440d02241d00340c82140c0c203030607940d400c01c14040f080740c01c0000c0c60358880746808081d54185d41d103510b1703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 205816645 1250 205815395 205815409
    0x60c140102090d06050402120d050927010e0f0c09090a09080712050d0e160b0306030f0708070527010b16020315070305010509040b0a0f06090207110f0406031a04080405 74
    0xf0544400d5101d070140425818400c001e502c000c0b821074090426003150150143c02403003010b40710341c0507101d2002c080f1070b50300100001c8003210b100000c5660035540d682c617680381e100b0800e4882070301101400c40822142c001801c111070480002410254240e5100b04840c001003030150419100310004100c810000780e5013143c1c0381070b00940b5440300740d03d583c0094200e00440d000b141d1200e52543c81a2002102001440c4c0c04e08200c41e210160a656507a804000ca82404948a000301c01441403e1000c00c080c1008a4518162501034035071650f04103a442925454480808455003c40d00100052141082c2480182030740380402c02c814881031150b502082c41c12000d000c4000e1540c0740c8000b40000e0301d80c14080d10340103060459011806007003a844580000d0703006400c11004540c1c2c1d050301850441d240e04114001d00035110110f40300c1c1c2207820103240700300b4140143d5100d00440754020600e46000e11170744003640d4205072501d01c030f6184001c0ba5a00050082c0007618006810301001500c2d03900c2c04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 205817895 1250 205816645 205816669
    0x1509050f010504050d0c02030c040207021503090c1915120e070305060105090a0608033007050a1205010803040902070212010606050c0f150a0504030e100507140601060c14010209 78
    0x140c00020b0074501814618103050740d041a6100f040500c0905502503640001c0c0c13a030060004450060b560015417000800489102ca525040b806001c130400000b800d0110b0103031040d11040c3e851880a52502d80e1303498a1a4041c0100c0200200f00c02c419500720f4481c1000c0c20402540c6140010b84481c0d49880c10f14009195201b21404d0b070104006102505181c03450380e4200004072020322109041031401b948038005c4091408481e0240c4007008400008180c04480120032000c3c0032610341023a640040550340895195004074000d0340129001809c40d1003503904846900000e182480d0500028034080c0d031007014166482090803034400c070995428807070b01005114a483d4599104d225214050500410743c40590b1160048031000001030040c3c0301c015405051618002425a954541907404100d00d0003043d80040070500c8004c0c91075004030080446034010010507204100140c100d0303640300024010040017454859242c000118240042c00741000c0190000d400c1c110381c88003056440c4501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 205819145 1250 205817895 205817923
    0x120601090c11010605012c0402030f0106110604020a150201020c01020307090f090203040804031130160305030403030503071218020108070e01080c0309070905041a070c0b04150905 79
    0x1c0c0c984101c4a940002c180412058001c0092003c0c900d0100040c05c00402254178030015512403021864005404041090540c4020030441d103d003089018024401800d0088801280d1602071074452500006200c6200d19801401e85401d0303070401d524444000400c2c960324003559000c1c406400105c40030300241d48641280e6407076040d202e01e45004000010301c5a4818080d143c810010300011070a00400c417400da030340101c898100d240800e40465002d5901313030884a1324450610300c030104900020030b5a441c9000d0101203a645c2e010503409803181000f503200090650784108000c10011f07000d08091544044581400d404000c54803010000355084aa4410039a0a055421504642e0089800d5030070010f18031348884003c2803400041d11451002d010403498078004000501200d108002c1c82c005001039510038441030415182180811140c040c070105480110400240d80d2489800d00090300d030342005241d4250f40b215118002900c0c010111b0800311600e910052010032070400c00300c4010b110b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 205820395 1250 205819145 205819151
    0xf0b090f150f030f09160312030b1c050d2703020d03030b120d021e0303060f120a0303050105040b0909030a0f09030b0123031603061107020d051f0203040c090b12060109 74
    0x411000390b030904140444100360804811814000f081e031062841200c0115270600040021001c0e001480c8007401e11140030b5280300100d10f020030408003013034507042000540c4038100e003d51100c01c2d0041d22207100200109412046100304050316040b04100c5001e400b0b810001180301c4c030316000c150002150a0802080d90100991b160002d0341048250800c03280100b803505001181211580c50b0f01c809083c0394130804898544000c55901c1082c540d4055842408440110076140350280140c402482403d100b2490403030740054505150308e8080c4204141c0300a1172a0100f18074090701c416051031004410041d4030200800000c1198030510302074035980002d549544000203c000d0010110750072070b8040c1d00f1680c07121403880011806603050b80da0290300810881c2202070400e00f07900a01c00041c0d4802e003000b100d24140000885e030603009540409140c2c1840f1440000e030002ea00c01560001d18589040030b0402c101d90340d6a000003841440184810000450301703013010316050080c0c00111213955 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 205821645 1250 205820395 205820401
    0x6090504051b040902010c12271d0105030d0518031209040c09030503090d08091e0307080606010e0922060c090819080915040806010f0b090f150f030f 66
    0x9070720b4010740c105004503400e20a5400b00d40c0000c0001c40da9107001001c07000c40b40c180030f01c0175014544c078660400780b04581c0407039400880400e5206040d141308810a01000d141030f00070041b04003409a0584202030b004000584107d02c00300c40b81d500241100311b03241940f42800300c0310394041c4491103144e003c1100d401d031208209403c20040760994036003502800520801080003903c01b0051700c600c003078200c0d21842a9011800d001206119802405034449840c0780c51320132080703004226070f0750504243d0403941c1d401d407110396182d521300c002e44416000c40c1c4110101c812501d8103140c810b510015421240760800304c000041c8810000742402203982d0740c0c4601402000552014040b03004160364001801d400c04c41d0342e076042807000005805003000c0f10014090780d003900d55441150b0070080c0e440c0e140d603440741e480c40080d485840078001c420b19003c400500140c54440751064900e4520001d109502c040e1015041280c01850a80101c1411409000084a00c00360801461081c0c1110090074101d20b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 205822895 1250 205821645 205821673
    0x1e0f0705070e07030e03091518090c2a03040b0a09080307060609051302010c2604080a03020c04060b090108090705040612051504030c1212050a140c1903050a0609050405 74
    0x40078803050312202d46c802d110010156448003081e9480b10000711143c2d90710f03040d156071350210015041c14960030219100621030300c15081c20041400501d00c440b0406102e048242c1c85103242002140840701d0b80c420301c01400026608001440742000c1070510742c0c1d1a42e51000c00381d04607003080405a038100c0e41c0c1c0c8801c00041da8103003c0e05500854810400c2c4541a035540040e180c1ca0b2107900c041c0c08100c1c00c0e0300100040080c0c0494640880441a650b500e40c0e6943c0e4031140d8541401d402280140030300c5405c65800d081c14020107058884d0044e80302d0a01d6001b0f4011100c204008180312628458038000040702e884078802c4a001e07000200ca501c0b100c01d11818014601400320890040f0b0544140c2040042a888140c06141c90ba1121845150b5000b45070103d418202c88c00c0d0100325549000f0507c04c04070a00d41c0310590810702d00d200a0302980d0b9042d11544140980741e03080001036460565400510721070350000c0d03031000c40d0040000340c0a4443c0307080c808030b61040b03c045420364080d01096640c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 205824145 1250 205822895 205822901
    0x290f07090e01050a090e0106080601080d0906030b010f0f030618090303060b25030207030501020310030b07020609060a180f0602040e010b04031e02011727031e0f0705070e0703 77
    0x781c82501081d10095240c5804510861458452411404da540c854a00c0b10602904902d008141500403508a035071142c41c00b036183d0404841d10030100d880c02000160f006e020f0302484443d510161107512030b9481d1580d082c0c03612612444d249080580c5c90b200425031403024000368050040c9a90009550b541c6842e02074101c0b145038005900f07070300091040030000948417010380140340e40c0d0285034204100920b801d0f45402c62a82006005500102c1044601c000c030751415002c41c2d005040c0c0045544524900b66152041598a00b1481d0030580c0041c11440d141c7e00482c1e115034400105c00700a00941e122480080f040c1305040700c3e031a0700050200414083c4c8400c071405050240d1000d172400d49180ea504906841c1c4510440d0100d102c260440c055a00486240440c41c207662000c42c034500e81042c45130301d407440d42032640c0414070040991132a41080002a6801c100b207064180b4200d8010301e0040449801c403072600c1040328401c20071b000000d0000d200d10700007040e00c40c04002060501d40c0002c4d0903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 205825395 1250 205824145 205824149
    0x30a05070f06110609061803072405010501030b0927150103030822060f0204090e1005071103030112020d050a08030a060605070203030901120b0604180b010201060e0103290f0709 78
    0x190307031300c0441401050303000411050b4211510001d0002a0b10080e12080e0560164060107030407400c9441001341d90000a8090080303040d0842410002030785c84100543c1168802c4202da50040c24500001700c00203c030480d4003403078840402d58172020304100c080040c500400041c0c003000f0040d10000400800d604800116082000e148440d05440c9080001e1146000603c501030011a00d903101520703102c3e5950704503030180c10301120502c44902c0201106541e0901d0b0081c0c105950301c0c000006100340c1c0b00c0c41d2035403000444440a0b51550740b03880e90392007101c680020306aa02203906451140020010408050710306d1069040c0d50b2a8906000050102c07034403a400300d018440100300e03000c01070b0340100403a4100c02003400c00544d40d0700780d5034104008000c540c1c4440c0d082280001c000c80c85507003807215075440341101d40d01070008802e04001207003603804510a103030851201500510000d440b0080a686c114460201c0039840140040100e4215105590540c83e180580003400034442d840520303100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 205826645 1250 205825395 205825427
    0x803130812031b0f0d14010602010b060403020405060310090b090d0c02131a0406120606140f01080c071b17010903050a030902040e010204090b181014030a05070f06 72
    0x300da01031424840320144070040c400d0810640c0080200401030f403403010380e407144868802c1e01c0d440e0b44541d95094001c155034690f8412045002000080c11841400381d01d2074204046e1000741402d180d9070a210113044003601080c0d01d40035aa0190392184000d01c6a003102c81c0c01001000503038100303c000d840c1440c604811140c104500e84943c94096283c1d0814005e1489404400141d4242d0748821128401d00c40f400282c2e2103070911100040200c000c201c5489085d01031071040081c0784d80d450030b04801d010000c07800b070780100c24001245681d41c01409100c6d40410841c1030903252844aa0b980400048507084c2000115507000040c040c9541055072510000740c04002089040011307180604203000d030b500000300302754a5030740e02c40c21902c85800020600346110f0080d5140c45c0c9410b5080050004181e590740500344102c94002208182441c2a02641008100791410303810041701d251000c40b110000b60309071040401200c0081c4040103a60300030030a900d000440f41c0e0070071800420510342c1441c400f03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 205827895 1250 205826645 205826653
    0x60a1e030203090a020f01201b04020405150c0304090504080a0e0303070b04060b03030405041a010e240d14070906120605010822080a030504020a0f0b03041b0b0408031308 75
    0x40f45900001648800841d01100e000b02e068803000c00481e842c3ca200c855413000340c141901621a804000240c000c0b81c9001a940d10396005d549030300f84400ca0195104155111511001088420000780f00400700070032054280d82c40d09482c1c2c00742809403001034a04803644640021030102c1d0726441204910040012400340d0318000c40340d00c4031003400742d024202910071070b0740700c8a01031580d808008680041c20041d006100c03040440c1031103003001d0102e410003030106005c00352864041c60440c546444075502280d1103021005010f615040741d801005000c09c03081c0c0d880400300c8145451382c00c85440307070042d03030f41c2c500358170f81015030060010102200188032181002c1d4180010382e0006444c1d80d028079203122503050020700b240389000d0b0035a80300c1c024114820004800358401d5058000718071450003540d0b407040580e80c946803c10801e855100300d40c3c07081c000b8800b0400040c54151a81c0c40b4030224540e0354a183d490300032100080e4096407040040d50300000d43d031101c07a545a54008000d0004074064 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 205829145 1250 205827895 205827901
    0xb040503061b19050405220506030a020607030e0607140102090307090e150a02070b01030b01150801230f040e15061905121501030308071106250c02060a1e030203 71
    0x1051450080110441ca00d240014440000f03a2081042e900204401000b1b10007141d02c00c040d04443c0391000300c01d030350540e00b03000004299060004140c0b44495004c4c013a54070b8840c0c42c2d01c086840c0c40c3c2a80680754081010440d0801080441015072a424074010005030b403034011508040c580707141d0740d0101d105030342444156220700c0c0c0b0200b241001344482954020181e07813140300c4000284503480d80100403c907004008010700c01d5215515050702c03480520b4861628616400f07031140b4009100b0200c0441c12081c00184208400c803104030954409440003080c1714001c0c0008080d103082165190075075000078a081c440303480b0301c0541a0400c8087d241200c2c0d0280070b40070300c00d02c044e460090500990b0041d2440c0c054210801c0700c1d80344000c107001407510301d5842e850000c04582c41550681e00041c880041020740c0e00b03005c280c0f1030090b03e01d9402411402600e00c2042d000420b04034284023407007003078514600903840b142e0041121044a5840444001a040011010184804503042014814410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 205830395 1250 205829145 205829191
    0x604140f0109120c0317100806150303030a1a0a08010c0f05090a050d0807080f07030807020321101809050106060c0f03030515030307030c031d010801031214040b04050306 75
    0x6100c0442000d00d002010420355040c03e91b9002005080c1641141d980c008110500005040c004162800c2c1015200d10b5294240b2000c05441002c130042d0381074004001107207a41c1c0950780079040f0003041d40c161000c628041c50019444680ba948801c04903516072042d0911250301008200d5142c5041c240766041440754001700398980521f0185034000e0071030305042c50512203003c0a1f07415680e800281c1030354460760415200c01680014100300c000c60880004500c2c06800401554030784c0c2c4255840015600e1400d00740c821820014200658680000e84d0101c0d0000038402544420815814003081c0000545000c3e401c440d01a406082000600d03441100026076400188070070503014580498139840c1c202210f02580080c4544d95410310002600d01304060b000041c0d45d0310980262030361101d41d603488000c111074005844030940099108001400004c4010f1840310f0100300d58600b1208189132022030010340d5200e5080300b0000b620102d0100058030b802c110341350340300e05140a0030311135040100b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 205831645 1250 205830395 205830413
    0x6060f020703121808100c1b150b030d030501170a050607032004060e01090b030105060f0c030c01051018060e04030e0f1507060605090702060718080604140f0109 71
    0x10040c031840d01e0031121001540304200e105000c04101c1c4132851007640c1d44654650700d041d468503080310710307007070501c0b0b6040c0c280902c000591034000601c060318200701035602c1a04c0840303c100c01803005913130340ba01e4078200c0c0c504004101c0404016100012254142030001807409070400d40145664030040c0e004001034008113416400403524100883d506c41e260008100050020542d445008008280051a20340c48030300408481005c0c0c0321a8bca03103450701030400061100340206038102400300301500c0380c2100c5000901108284105880c1005505c44466007510b40c00e503461601c504942d801032004900c1e03106225060085201c1c108015807501d07034480070f01d100090000d02071110840760350300241c1382d8001c103074100140101402480211a0b480041c00c2c0c10648042c0c07060f910f01400414141403001c0e41170b010f205150000c0400c0d40c1c80000440d540d60303400d80c01e5140104a06800180403008200550040780320300b01400c4120800c9494600c0c180c1c40c03d400c085242e04245100c004180000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 205832895 1250 205831645 205831649
    0xa090b010f114605030901180f080f1005010305070e060619020616031802061b01020d05040b060d0c05150c0303010b090a0e0f0f04060f050708010906060f0207 70
    0x3042082ca20365000221504062101c400c0142c0c06056040702010054001d802c010400360031102100000180350210303400708090180140f45074030411145810758081d034400703038181c3e840351500100035448441d0803403140c010703901400390365005c41d06100c0316540038001b001e80aa5000c008002943c5141c6580347d07990350611400313a00d480031401081c0651960b40031900c130703040d44d80c000b02c414007041d01c2d00070f648807012103920a913030380035549107030041d4424040c140701c000303c9650584254081d13408000107548040346c1c0c2c4008104201c800381d03c0c0c0c10280090200a00c0c61a800945840c00d401c0004c0c5006004005522550a00d801a0b0020300e042e90000f0603124241c800e00381d22603254401c0700340361203400d1400c0c0841c840070000140704800b00c1d0081000907016144070800c207a5503c412902e801041c0c036440000c1c00c520340000c94400100c000700b07610a0140c030340492003458010004c812130b14240d80601c0010344103401030240001d14010344004010380e01c0c0c0f106056100c190000d4803801c2034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 205834145 1250 205832895 205832897
    0x7080901031a180609012c070219030e0109050a060f2f100c05090d03140906030a0203040209090606010c0f0c15110105060f0a15020a06050112020a090b010f 69
    0x40c4aa0110140c040c8400e164050b102824600703201c0358803080c1041e0014112038951141c50300400108a18071281590703155001d680034101c02c041040b201140b492800100384500b1403003031402c0390000666103132400070f43c580030b602c0d85440f213140480014444800c54124a000d141b102d03c1c05c2115a6120798040c0c110465407510262005486402000e4001e002c2000005034104a0913008010404036840c6908540003001f0000c0417014403058400340642050154440d01880c0c0d98000b0a004da0800c1e051841d401d05ca10703142c0030321800000d8090f002a20034480385940030080008504203034050f250401d0114004092520704113000030104201c071440149440c000684003401c0022140d0b5100107044000101052003414800050403840500c040c0e010960800d030100c1c1c5c00781868a40e440ca0350b0000f90050a44a003085e0340e1124010303404502d0340c2140701c3c0300c0010010590510400d8042d00c1c0c0b032030803003030b162205004005007501281c1041e04018074024219510703130780201125080c8001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 205835395 1250 205834145 205834151
    0xa110c04060f030f020d0c060e01031515120f050a050603010b0103052a0910020c130b0102101a090403180803120a0504080412080423090c0d0f0f06030501110708090103 74
    0x22034400b00710440d2511100410900301e0b81e001203080b52704006002d02040e8280e0301003212454508401c0300c08905031160080346400c1d5a80c40103410300c03d19185800000500000c0307010152400d00d070007281d008039a840b02d2540c1d03910900c030291500303001d0318030030710001d207404d0040e03040803107441085084010104c402000c030403c0d81010314841009640c5081001020f0f2040050a00000b9403a001b90100103403240e81e04a40c100003001c0c0e9880fa880c0b0040c8103070f000741603070700c55032003401c000f8010b20308500e40500c002c1014079406e5a81801182c440c6100340d8a0410b4910072383c100e0012115503422a0540d030b0010300c0980d141c0014116400da00c02c2c1c07490008502512a428142c42e40e100c0da401140c1e0078081c00c0743c04c100303114160340103000300c0d4418018050b100e2207003286e0340080302100c00e02e15405914040440c0c0e5695100b0040e200c298080b00300047c58040c4282031104441002c0e039940303c500e03122042001031100a20811030444441540306e85404130300d81c1c07100c2c290300c00d06a8a42c14995 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 205836645 1250 205835395 205835423
    0x6050c060601050c190c0914040804030209071b1203150e0a091a010f0812030606090d112e030b060d050907030b0c0c1c090611120a110c04060f03 64
    0x340810554240ca098444840501c178420708180750080038074001c0800c0281068043c003100001b26010030b10903904402c9003820310f070966080249411024000b6401c2007002c103107000101840034003071406a8814560007828004009000d010b95101003041141000100d400300800c5040d81615640820400000507641c032062038915080e808420020300c190703006800104241882071008d406480203841260b0841c3e4036052008a42d2000305c81c1a900a40705100d401203d06004032180c4505104004401e272070401c01010130000569410700303d019140010219118502d500d00c060001461460144200006500480c80c0c600c5140216644190f07940c0010303068a100380203580c0510341c003041c03200c09420300b035840c003202d078103c400c2858941c040c0700000c0c404907400c911394015003441e58507901d240306e1500740140c400003041006410360340140009c001c0180740000c010f01c612081a1200040c4030004904c07589491256291507010301d140480a20441d5203000c401e4080325840389000310400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 205837895 1250 205836645 205836667
    0x2010c0203010e0d08010614070816020d020402030c210915090c13020702010e0103050f1306020c06070c03090b030907150201020c150105010f030b0d080307021e0703030906050c06060105 82
    0x2800c080211001d02a000c05404c0c07072548104e00340d04844043d40d410300046d619064519191003407c1c00104003110030415205004054030107050340a000400280f0040820303008030f02643d000301c4203528414400a001000c20f0b1845a0329480c1e40f203800c68407101ca10f404800a5078507a080641c201c50341c5169800550005000c2100f07900040d00a8034403a03600055a030302901941040100f01d000c0340000c006103550354482e10404d44508400828400c154485507618189036034ac0640507502d560b02008401444103080081c94014621a42d500c59902c6003810000c00d602e581d50800c070791030b04041007030241c1705c0d40009100c1c0641d5100e4000c0c2c103510b030700140181c0c024440c1b03070030300f00543c043d00d81c1401c4410120505241220001e80391452009401d504c2281158290f010943d4030820381c100b071501081c2ca44010350f0303006032540100d070300c1181134074102d00d032807850014082241e42c00024107004056208400d240109041d0038a5400c00c0442a48181c0b0741c5c500412584c10400b001c16050125 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 205839145 1250 205837895 205837901
    0x12090a1b1d15190906030812010b03160e0f090c1225050a110a05060a050702120f1e0408030703031109012c061201090b030c01080f130209090c1f0c02010c020301 71
    0x50136411010016280c0d6031912240603000200368034209400c00000050804414003101d108403d8a004c00002001401d01944c082040005032608000c10b0304c01541c0715250b1140741c0b4055200395416a0303c410300c0100ea000142c400a00305543c0400015002842e24172030351205601c1d08040c108161203044181041310b207c11060010300240c070542d90058180300303002c20b1041c0940171030b030814041a83c802c807003039a5410a085c0408c2c8a0903041040b20000049a00600412506844040c0d860102c40064140c2078209402c6411070790000150300d400c0540502c5403029555071280514280612100060326000b200d043c0d982a844080700e0b00340020490950a5046003001064180ca0f5120707a5039080d440482401500c00e800d141102c400410f01d40052804100801651003120b0b5903250728441c1e5843d030001d850031044404100c0c81e0740060303403043c40141c46403100c00001c080c1d25100d001005905a414103020440800030143c00e400c03664171100c0d02640c01d80a0911204941051000c6401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 205840395 1250 205839145 205839149
    0xd03050d0f150e0402010e030d0c0f06020f0703021b0a060c02100e040e0f01060b0f0f16051905010f05040b1503030712020604020a08030c0312090a1b1d1519 69
    0x146003100201040841d4440310f40b502440c000eaa9a419a403000410325a440588000b44004103a0030a003034000951440b4007a080ba074420000541410922840c1401a4001000481c00760304100e9541c41a8034150a614001030400c8032818442c1e4544100546440c039444400303401075008074a500b00c45805900340006544016208204a02c404990f564030346e41070890082980d4200900003800d201f14409403494050007200d420b127010903905034090700f0307406228031001030b040b41e803290030216806000420030002c907000310700c00e0200185800c50848040d8a6007411640c6041d0600c00840d01c02003140390312014071001c0980e070841e0800000d03d5401201002480070048000e2402c440350b01080d0140183c1c400d0b602194419194000700351a8054a01904960790040c40014490620012201e403caa80641507810006140e240c400820740d1031403001e0780200ca00e04003000a0702c0c0302a44a1810388950102003a1420314080c45c004c4c05000245540c0702da08006030050880054400c8080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 205841645 1250 205840395 205840421
    0xc0d0e2d0316050f09010e0624030708010905061009060809030f0c01060504110c030901140f0315030d020c030a0b04030311040920070f030c060e010c0306140d03050d0f 74
    0x1455011000d10a415201036004040c01341c0303810b00070703110702d8105022194181c45034400580d0050340c034402803202c481d80c0440352091200d2513021418240809900075805a49039590310f504a605149030981030390380c082d000a01800d85030340010344255001103800701346c41e0149006105901d80c803080d01d155004801d0b40d00c1c4200f01c00694200350380b174154010340803540162000d210480e04545010400d000b44015420b4642042100c61055845822041694040110107a0818034000003c038020340089807d100e182d81402000500c40c501080701c1100e564641c03004001c1e1401d41004240c80703132200c1c1001008544c07100c020030101402608003098402980d0b6030b01d610340d40e13581c14400203802c90306801d4160700c5616508004102e2000101c44016810030500034101c00141d80848890700e009006940c85a9601003100c2ca0760b00078051408000c0a541d0045400380c10082500c0d000300300b83e5402403055480d038031103e000a4008007a10300c0b644003d000012010b0000450101802d04048518 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 205842895 1250 205841645 205841653
    0x1a370b0a0306170d05042705130b010e0601050406050306040b1206071205040803070503090a02030f0a03020c040606090b07080702040606032a2a050708030c0d0e2d03 73
    0x541240e850340c000c10880300040c40e0824a800980007154458a001070300c4d000181041100b441001001c007642c040414403c03044010707071070400401034100c2d4800c0c1c5410303051010081007070302807006203d007050140a81c07900d0540380e0b080c40340c0060068441e81c840c07001840b0b00440088c0440da11940900d11402c0060003401805c41881e00300c42e141c01040303034404042103043e01c0080641e0003500c81d4034411030384201e00320302c2e41c6c0301c2c00000d441310380004003000f220303100340800d410068509006611040d001300c00203096018007803901034244445c480e0828048c03803804000300701482d401240f2008171600c0c81c04080e5031b160b07d418444000d22a600000c1d401908080001418035850741c03148001c50100180700c102c001c03003441650081d02030b0349030740c0e40010000b032b00c030a285007400e840c180c0040c0d0403488004401c044503070360181130a110703a1240301903030004504a001d2003403d101e5440120010f15041c90102d0885000890055410304545000d540e00245074090707170712a130000c00304000700408803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 205844145 1250 205842895 205842907
    0x5011b03050f101406030411040e010606092301030506030a050d02031206040b0901050108070909150504050c0c1506060c0f330a150b0d1a370b 63
    0x9005000c094803040105001580010103d00350b08450406582c0b0020074080400206070030495a50406041501c81040f000050032441c1da80c2c4c0325003003110b4400310001c2005031034a0b1020744101e02c940c3c010742c3c03d0030000c0070032100c0d25800d0300c1502c0908024200092180c8560022a02e410301d60b0500400511518610040041d0000050000b0580c40d07070360120665500018081944d2100b4041508214800c0042c002903000d1805541e001403540b41036145640c0e030358462419540c40905422100c08450f00a000e203041c80c0c05429030040704d4600e50780c5040c0130101619600c5c46000404041803200760081665555400100c0b8440d440801c21180c2c1d15000152550320b0341d03200304894182c0b540049442340480c0340c0b010310001840183c1d0003403441d41d8400034614040c02455400c600c102d6540c400c0480d01c00d22000141c00303003c040c51400250210385020420420320001407152048001100b0b5142510703020b52030400e041d04103140183c46c40c1203a0440c0c1c0700c80c2c080d84c0210690303140110f41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 205845395 1250 205844145 205844147
    0xb04030210050c0a020d030e01020f0f040f060302030103020907050a020c0405160206010f080c09061507050601140a0b0301060f0e22060e06030319020a080d0501090b01020c0306070c05011b 83
    0x40c070007180720000007044241c4070408000741e00c0c40f80b0b00225000d60006402109128080da00022040c143d4500140c44e0680c050701540d542d610291130f009880b1004603050000a038036a140901600c440c0c24114034550454000a580d80c80041c280c078104480052201525032007400b03441000d5002a1062001d0300b0f2010071000d00c2d60300f800ca00c1d40144900c0f00000781d188200c0302e119089401d00c0b80900f900d0180700b028001d4003080180415084040c11110420700d040c40c20080980c103000d580549004e505120081d002100b840301032502c1025103000c18080d8002d108112811a1044d080c000e06003c01d0444c180c4521317040742101980440002c0040182c501800308150b0365038042c0f0820041140c03a40107004c1094000e48000360103078018040500440c0543c0280c4400c645a401110070203681c40c0e94140391944080c0c0000002900c50004000003e07040c05416110842400544860045103022a5544600504e090704008513501c180043c82021751191034003410202c0c1c0c40c10443c20f541c0d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 205846645 1250 205845395 205845403
    0x913061a070204201801110304080f0d020a02060f160b0123010c0b06011103130b1306050316050904060308030103080309070519030611160309050a0501020102040303081b070b040302 80
    0x1c107902403410501400c8001d00c0300d0131449000307030516000f2030412801000303426040c00030b00c1c0f40c2e9040c081040c011700c0314008108040c1005145880081810400300c1400303d04007d1300f2101c1500350350200c0084401070b82c1b08420341b4500e888c80c0714103e0703d80700c06031500005941262009040c3e0b1650740c00200c6c80781c51403480312041900069040034150507442c01100c402c8080d280c05484808403101281e035540c030030300844582d0140c110071a400c00d010145ca1600d01c00c1a50702002c441900000d031315140e01240841c60004090b181401420b51070100007002104018041143c00c0040000d00f103001170741c5550158018540110f00203850750384a00d00b4940075442a07406a080344503080f0300140611f0220705502c40032446002c5080000d1856a03071002603d034401031050705c034070248441c1d21141401b03003407003070030600a035a2507080500d03000131b1000d00c640300d1700704904690040005101090300680b92503001030f00840400040540c03464201c0160103005802000414004244400d040c0d00007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 205847895 1250 205846645 205846657
    0x1140a0804020a06051309050402030a0206120f060904031b0602040b0a2c011b110d0302060a0e012705010e03070804090506010801120b10051c060b0909030913061a 72
    0x65014542c45807222000c0c1c0c0c841c0542d5864003070401c030243e801d07c08202c05801081e005403018046510b42c059560018032302d50445408610048210b034100119a000805126000001900d4103c61801d190300c00500f040c140c21204915100764040c05020085180d0440b0b0007480d481401135110401c0c008000c000040d40200c0300c00c02c00b401070b90701408581c8104c230f0315980d14050b150300c44410b031881610b444014003850305480310b82800c0310f826034a8880d1034050441a02c294050700a034540701d0308040440e0301402c0ca56915a00d8803c5100f00326010040400e2440b64040101d040c102e400d103440d0307016026201c4a1041d0b0300004c0b07100000c2100280181050391031100c024000d0742d5802c0c00442d81e004007440b030002042e01c9400c00e800414100c00082c1c2e08144c0300c40802616a0300d0300c010400c03040c2000904541c040044100c103080c009a482003501041d421902540241420701d4100c1e580e00031032a2a0384561304042c0c0084814009502120050046e580b440101e4a540c000000040e0406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 205849145 1250 205847895 205847899
    0x201020c0c0a05091611030f0316030e0c1c061b0f02010c0c08070819050309010c02060105060a03050c1903090303050906040c03110102070308071202070510050f0901140a080402 78
    0x2403444003a500d0b20400003000c1e514080c140b05480c0da944076400c0701d00866102c0b84018000380184c403803910741b400d00040034a88480f03120f080d900d00300a0a0319403072200803005802098075002c1c01301048203000c00c1061801c1011038070314000188050107000e00140d1140b000340300d14070b0140d080c0c2d01104282c4030002c428180740c5400c610000f02c22000e90030786090f00355000000302c10040303030700000fa56203001d000060b000e884d205041145811781064500903420f6104007042002c010400448800d002d203050724405440a0701841d45080041051402080104414140c0f100001002900c08400b61082107200040c00c00c203c89070880050010103001c03000350b0000c0e040000141c001c202c000b444500a580c400c4500c07002602d140c07508854841c4506056046000b4840b0010208440030040d2103800d01610701d000c5407013401400031b49805166031000380917500e964000c864441e007010a40d92035120b00f000d030580c4d81c10102d00498040354104000e00d000346010032208080c1e0b0344101c8481c840d40c07007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 205850395 1250 205849145 205849153
    0x2006091e0705090c04031509060501090911062107050309070906050105030414030c010911130923070e01060f02010f0e03180f0402031f0b07030c0b15100201020c 71
    0x1148206840e03200808105a5940001ea08100e10300300002d030b1551184012003820b080c81e4907541c5512040542c20788140c111030712841c11605100b12840303014018600300c4070130400c280450307841c0040074400000b420700c40c00d008110b41c0800a403801c0e80962100111251040505e0500c1014220750000d8500301c2d00b52041040c0800c050142d40310b09002c0d90816162941941d881daa80ca031a082401170281285001c10310100c042c0100c07d00960000c90b10585051840041e808107020700200007a600c01603d50900360048049024200500000c00c000f510701600f040e41c042d1098074282700f41e44203003041b10743c0c24000500e056000b100c100c42c10a4903802405103203414903245080d50b003070112640e19504200700a810300440c462001c40049405403880013042c101c00000b4049820442d042c500b03480743c2142101c80c100c0c1207040c1385c01800e180c1001508014598400a00b44010013034000c0c19114030790049002c00384500500d6480c000000d20104282444d00d40083c040c3d0000380a4034201c0c86 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 205851645 1250 205850395 205850413
    0x31008060703050708041e120906021212040b09010b10031b0315090c02100f090203121c020c0f0f010606020f070515130807060206060a0603140115200609 68
    0x31003030049901401d429542e00b101ca48031034850380307010001a01d8100c0308850a2147c000098a00440400c01c40c481e900e512090301d01e03011000e4207080041444aa19030803c02c41d82d1905040e5903c2542c005412a031074160075a10214801c2c014084d51850a50209022150030400c980c5600000c242d400e480d0b0015546850f000004e07002c4d541404d5402150445120041c411045c030380d80540038140d6548100c1d4843d07101000d00400722401890a818000d0b00c4001c0303002541030400c07540c1c902c5205000034501d4a0740b12035648003001c50500c4059680c40d00000c4610f10100208040b9211440800c10340e005059104500f038000c00325881450054040c0a2000515a0000c600301d4100d40020b024404075000c00650700049a2120a5142c054005140003090103d001c0001c00c02070300081d00106068103200b010480c0313103206517014508142c01c3c0440c010000000981e0701e41103484a03058040940320091041d142402280d140a40d2108000781050340a000041c1e094010f4111070b09951100e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 205852895 1250 205851645 205851647
    0x203041e020f130b04060b0901020d050a0f140909070c061802060d0b0102010e1504060b090105031908041d1611030a0809030f070302030315030304050307051c0501020310080607 78
    0x2058503035010358408041180b08020381031000761859000d2078410700250350440100018201ca08540201d0039000700428406030f1560108588003514a41341050f0707040c510350079030003482e0010b81003807502000030030540d6903003c2c402501a00c00d09880100744000760702e05000300030100d551080060b650b29007402811101007280c12421101c4640140c9414544000c182c2908060013110401034115036079401c1003445c40c2001d1012030042c220912945c2c405081c6414030b4401d070390265200610940e031140042003260790000b05081000321000714061201c2460401542900880e4444440383c03a9401c00e8884600d005803823244516841302c0b4128800311140c404540154132500254910f034400c0203913090b03590103a500701303030310a0004048a00e010040c070010b44554020031000c1b00542d0000c030a00240074024009070030041003d40040d4202854040002c1c0c0d500110301c286070149107001d00341c0a906840c00713110850360790844001c0d035413400d007004050300000a40c81440a54002c0c000800c03441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 205854145 1250 205852895 205852943
    0x504060b0a0f05061c090308070e04060609061107050604121b03030804150603060216030815010f0e0105130303320706020d02071b0f090638030a020304 67
    0x15502e400000400c031070402c0c050103140da01040c200060340c1069410346010700e031a030240701602c5202ea0345860135800c024038050100131021f40407504c2103042c42020707c00140d004480301d007101c1d00c41c40c3c030b055103926400c07901c1c1c101285500720303a41001000901185020151010141c418454820380420350442c615902117101d2a01006000400030404603000c40c02e04420112400b0b444107002034030035641e03034882c42207070311140d01c141380304d503240b401501856002083d059022aa002c907980c0301001c00b4000030145590000c050090040c071480711405e1723910460965a4007040c43d001410500d8482c20050500da001003e042e003d25032442c008010b00c2c03400444100140d03003095000341003195541d2640007a400544480500725424800d5401041598011580124481c0445a006070420414404200041d00a864418101035082081003814181c4003045040e0a05000c00f207015415140141440b00040d41200e2201100f84618840c0a50003540114480c2d8901414090524909495 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 205855395 1250 205854145 205854149
    0xf060504080c150105090c0a3606020f2a180a060b1905070201050d050a0b0306160c1205090a0303030204062a120e0a08010b0301050a02120c0702220504060b0a 70
    0x52941b43c00b00d2442c40c0408060680401c5a00b003600854540804541609038020640320310819680040307010f0902d40012a0040e200e40d1014002c200c071102d05917556603400c1940038100010700d80074480c189c02d8840b200304154030010101c04080d0300a802286000c0d1090740c2245480f840c04da8000307452034050f4110341c82c0c0012014042e00386501848142d4039904412030a9052003401c11101c0342c0c1038018031455200c3c000c5481c4c00101c0104e0201850300e032200041071242144074003c08140c0d001c1d00007145ca624258400d040c0107000c4a10b04044030a4041d204e05140c03c0300300402c02108254150f0041d00035101c10f0b580e00b8003616400c003071502c0035000402800c1215540c12420002140000300011000c1ca000d050ad600c10b00c01400115024100561000089965a0510141340d240a004040e00071020610940c1005d42c3d40042c020080000382601c2c164030741c0041e003442152280c02c4c4d14030b00c0e142daa03407014481801d0b4180810240604560854200707140400c814200c0c039102c2c0285007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 205856645 1250 205855395 205855399
    0x6020d0c080112030f030f020a170105030d120518150411010504032111030a110601050603040b06010f0c02030106032909060c0913180b010e010e0a090f060504080c150105 75
    0x3d00d00c0254034243c070066003401c05101055120040c00280000070300007416a200242d4030811038001d140d00d480c60444d0b0613000944a42c016400c40301d81a070380000500c403d907031511030000b107684821034a0800204954002030f02401440c21344100003000c107000740d10860050343c841080d01c903134a0046a60344914080103103036101c220b150b2001c03200d0180c10b80ea40e1051508084e68044018510140b468000780040400036044002c0790f621950144031250040c40103513200c034110308090380c80e0b1004200c014480380c1080480c0d0075249500344940d2101d001075030080d00130440b50751a0304003440501d03240012040140f1030300c5008030404d0048800d0a1050841101820842d1140400303003050754040240300303078468446550354421000714400c420000035050010040c8103a10300d03000204000582c05000d5103030014004005540920070f400d03030f01c091180030000c0c00702c0451905050700a4001000b070030f030620700b008100030441d00c00010201d0389100003c4500506000c249401954001d0103119 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 205857895 1250 205856645 205856669
    0x9030a050d020a032004170604050a141006080d11060403080103110d0602131418041b03140106230d23030d060f0e040f0209040602090d06020d0c0801 66
    0x345204007070350151000440d03901d000309140c1c0c1942c80c9059402c10076840c00080d0707000004c0811025503072142c60007481c200c090140102c2d1920381c852903100c00704001c0151042140c0900c108000c0414040856602d06524040012a85030054507944400d103600060201e001c01c2000703070b4161000a096485207070b143c0c0e501e080680c01e5035200f4117031403500c181c801c1c1c01a070b1003580c1c20000380003400508405d41c820200c40380c0103854201e075112022070114406005d04149819242c0c002028640940d21507003004ca04203074503520781d101059aa04680c0090902a00400255124007041d0006421540300d103802c0c0c0c0c00340041d01041601d4030710b00d00352150b0020742e00030000001000e108400c4082101410142d4480c201d56074500d0a41e40141c84500410307589040a0054206203501c0c1c0000d080c01d0803500c11640b80a6840d201d400c0810701000e0f10500c4c242c0e001178100811a0120b684005000d800c01031040301c2c0f482d00c41d02035001051001e0005003000c0d1990700492042c60b04074101d07189030400c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 205859145 1250 205857895 205857907
    0x6060904020d0210093309050907050f04030f050a02030105060411160206090901030b010807080102030c0d1a030706031d060601020a0803071205040804030201021b01080c0a0c050a061409030a05 85
    0x1221042503010701040c0041807030f00044001ba02032807060700d483d0342c9007594400483c070700d1405400301c0100903010030310518690078050b039118241401e0b84500c41b42007407691000c01d070301c020b045030145910040c81070020444c040d08008021658460b840d201b6002071100c0c0c0c607800104815500140c4c0c0ca1601ca02d414040401990400201601250300252849103000356850209191a800360410783e02441518010803040008000c040000d200d094000c50440c100446030350103510489030309280031600c45011000d06448009601d00044005040310724140e911030010700a4010f003400c40154039040031000070317407800c04907001d446918168050540989240d50300c090070741002d42180c08005220311081d8151a151042e6030099000b04801c544032441c602c00203207010011626016030404003c807400950744c2169603642c10800300c0f060140c45042c0b24004403903c8030245c0c4094a44e128842421040c802a40d1213100040014003a9440c079a49110140e941ea129440c00302c000510300b0450 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 205860395 1250 205859145 205859149
    0x81c020d030b0406030b0f060306091c110f01050a0c110c0604030204020a050c010504080702040b033705030f070302010605010516020f1206150906030109030905100e0a0605040806060904020d02 85
    0x6481d0b2018000c10000308a601e0740c0302d2000c101011240a40c00001480911025240800c411503100104030014961081c1c08070b12001180040d1082500348101d9901c00d80c1050307000d122108060304800000c00c55450100e0b1024050141e50b298100420f03030070450b098000b0030100e0111003600b00a000d007482d00707182d617080c04000d50044445008022041c4512a4550001c2c0681c60046014011039601d9a40c2c90042004451001c6503840c40b90740b003c410800e101004500300071704983c8201e4100e100c3d100d014400360010340c0f0b00b04000c1c00c0d8000025890103a5143d0005050894000d0b0f0007000741d00d407140c005590504c5601c00800c040202000c00c5401441e108030724000b003840103406048240d1480003900e1070079805850f8499002e02c80c050261403410501c0145501030401c400900400221b5280604545068000c40707006a444200203a8000d01482c3c2d20801210701030141d107403880d61600020001e40150046c0c0c60a4000c40011480900d40148000e000300c1e001849102c0780211130782 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 205861645 1250 205860395 205860401
    0x2010e09091509070e191b020705041401030f120203090307060914010c0b0c0703020a0b07200102190e030c090f0a0c1d060a0c0611040e0105090103050a08070c0b04060306081c020d03 80
    0x70108174007d44494241c48070020054003001c01e00c0b040d400a090090900c4100000d4881c280400414076443c40c004001007000401080155500702080003103010f0002e40c22401c40c8036a0854680501c10020300040107a48603100604a4880886407031030070007000c00466803104054405005000054003084e55400ca40c0014a80301d403080c01203e00c0e0f41810360b280300c0c1440044074443c2c04100f524190f540303141407903400e280b12005140000c614100c0b101c2c0301084031030301e00501c4004220740b403229078070b0079102040035988400009090064914029840d00b0301c8440c120354031102281843c84056900d40150303544c2284000b0700107180501b0720b1300c0060082075004000034004002800000b1000f0504901c1524602060150f0b9290ba9900309101028900b0041c0d000601541e505001000400e1010884503130701070340405080e9550f2642d08090b481540341d50810000704000250000b50f19030036610080841e81241d00b921101e002440e0b0f0020128139241201c005a040350340d1a8501d184213074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 205862895 1250 205861645 205861681
    0x150801031209050a0b04060806040b01080106180e040609050f060f04030509010c120915180618030507090f06050102010b090604021b07030f032304050d02010e09091509070e 76
    0x454100c001d20b03580d80020f41c8104c01c0e980100340201001500340400d9500070205a0f01800a85040c818001c0100000b03187c00c034140714100c2000300100d50b00d011043c60010800c024062001d10183c64105818050000c021502040324188035811503100c41050115985100d680e14040c0c00403240d031940c4040e100e69104072540d80c10012400c3c1d281c0005400c0d140d0094401e8030559500350b895003071811620302e03805500c041d1418040e200c007010010390b90542c008810744800b8902041500d50320000040c90304080e400c028454000c49401003000170b1107600038141d2104041d002e0010079511001a0700722007071548010340040c0c804000401c40d013416001480c1000103200356140d00c002c465107090610141d40c00490703042808000c914241a0302013401d00c104103030b0f00400d802d00d400103034040d00d05114512440f070041030302c2c200000c190380c00360350306038060300000d44080000d00d0040c040c1511074000c01503500c014021170010588040000030581d09480d0b401407c4070302d0381c407014240c4c10740304241 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 205864145 1250 205862895 205862897
    0x90f010b0d09140604030215070504030b01051315090203061e01050313050f010903180905060a030f0c0e04080903160513150f030b0108010f05071202030604200d061508010312 77
    0x3c40007807000e43c030304009803442640260b02410050031000300800c0708100260140c81004800c0c40140b000c14542020340741115421180341c00340720b2480c2c002d007025110b12120703a52404e001003000940e942d02d54000b50b1107601c0846603500c40580841c82c032400c0700c41c000041341c0054401c1c0005a0641c8001c20072040c4140a00100c58400c03c04821240c00d488103035600300c002540300214409910101c2d510f56010700680310b001d000da0301d8821302040c0c0d0429103101c0034000380462a425418842c0240c4600054126003200c0c18052500e410089030550007000c0e460b0013031055118440b4507080d6243c0c140103035100200040141202101d00780040c2140507401280070400707207c0003400038010110b0000540c81480300c000c00790716102070f40d801c4440c0d00313890100281c10030080100081c0d11005040c0010641c40005031280c84020104000305102c1043c0c00f44450080c0c0000800442c101c05405521808282803040c40e0715611030011a15902c4e40c100003003002900144006000907000700c04010007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 205865395 1250 205864145 205864163
    0x50d0b010201020a0e040b011808011d0d020a08031e010609060e030a0c060e0f0307080109030f02060103050c040c0e040e0106181104050616080a050702041d1c050d020711090f010b0d09 81
    0x84140c400d50541c0c4154085160bd07035642254100074140c609403451454a210081c1c0b0520f0b54842000e9203442581a00130b00d081000400500c15040da03108800d2907900c41000300210b581c4030800a0300f03000710340c02803102240780d44050094919000915000c1c60354043ca541442c20b107040010744050180e145116404002c181c40e100d00c075201001901d0007404040c002181801060a0243c1101c0019071540c00b150000001030020900c001903070400c45e10140c500090f403c0500004441c15a000c85d1038540c854144450329100c40340540000d0223445040c1a10504400c6802d6800c0c1140d4185041503142002031008202615102014200d50103c410314501104000c1d611104541d00600d080307030100b00003141d114103508141c0301d10107000028100c031380e40000448034043e6a4105040400090800300c0180c00300301c902c22402e07164001ca02c40c2e0159210300c00c92070f010200c4c0010103202800385908130006404004003100c518100c0c1c00c9142c10604e020040d2040c2c0f0b014014580c0140c5d45090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 205866645 1250 205865395 205865417
    0x200a12050f0f070501020403020a08060f0c0d230f0907080a0f0215160c0b12061e0d03030f0b03030412060b04020412060b0a080f0c01081b0a050d0b010201020a0e040b01 74
    0x101d60802041118411390005982c0d0307045204004040080d40c00c01990740d8841c1040148a48000c801d540c5c000030321300c0f00710303480d0a180105c60015146240b40012100c240c80319001828002d030003524040d00b00b450794039055680e1203280c55500c078403920490b4980c0c2e201000e80c3c4082060400000011800944480c40030603d030400d00200394070540c003090070725006611030000d00c0001d098902c058038642c0221850b1003051036444484103006040c45208041291030311a81540031440e4464030b00d030180007c900c050345414060000c04c000c00310392401ca0b081100c4090799203804800c503070030f580300700044034070038401600d80c800103000280f4a00d40107a802c20022030400ba10394a0305030030a20916000c00d84100f61424000c61190319031000e081d5501a90034003289036004142c200b01d440e000e280c1510150f032161030700d8145400d015100400300c034000401c440c02541c0b0200801c8020302d462000c2c003090060b400120300b01e01c504105000000c0c0349845828480c40e0941181130201e405141041c0001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 205867895 1250 205866645 205866667
    0xf090c0d05070816080c180a05210c2b0305040905010b0901030e0c090606070204061502010b01090b03060102101a130c0e060309151b0307200a12050f 66
    0x9681902d044002c41c40351401c1144100c000d0b49104845080b6150054490a220a642059018114411254250807450002a5107601202a008020040150031883c0003d0b06401a2410f01e24094407a0301503c0112101030034405071240a403890742c2d075285400005008200c00c02100b100040703007000001c0200082481090295a0181a6600010303550b01140d0002408981034556004600e40200c0e00400e45581e802c100035520210690340240d440d03581380300050041009070405403018440c54a04603429071f0550040780350580030b88800d5100b54860400114601042380c5030b90041e84800e07144821b403240d42d000b034045801900f1410102c034981d800041c404c2c16200c40d40240380d954404109003025800103400b504504141e8140d032440c145080340036120160200c0003666050039002103045000840100394103814070046c0c280d240c0c2424600181038100c0106a1100e4140b21108140ca440c00840c160074280e40c03040426031008525007040d215a04a001e11080c6030605000302d180403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 205869145 1250 205867895 205867901
    0x10c0c0e04080307031409070510020c03030d0b041503121b0b0906040b1b040506030402011809020310051e01030c0e030d020601090c030b01050406030b04090c120b060f0f090c0d 78
    0x20314442c000c2252646842d50000701110508580403601d10521000d02419000105200054030415240c060f4500c0e002d0a081e40f4148403c28000c1d010f00c0300003001c00180105a018140c501c004030b070244411200070200c0025070003103003c050040808074070141400b901500714414814001e4590001c1c0f00c441e900e55002d40c4c081160700314455003241d02000108240d07144803030703130020011100c6412940e08200301e10307543c043e80c02094080d00b40000131400390ba0013494040d0321100c420009808164480000e0701c080e4005540001b0340029002000c103c0d4a052112014240058044039000c40b41490044028007104180d030810312104081d9332605032014031031141108420b40003004c0e80d5141503081e81c02c65403840003141c101450f000a5070416a4000212000c640c0f49140c0030650001d4400010010948050002d0003040ea0300e10010300820016210700c6414004d00c00800d540d0ba0306400d10240446c040d01a0754003a06400012050380b40c45d401c1035810103180d0161a05103408103526800b2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 205870395 1250 205869145 205869151
    0x1e0403030c05010c1d01030906020c010207080a030c0309020105091c020306090d09080303010308072613031505010f091d0d0201061e0b030a0b0103090203060a0b011b050c010c0c0e 79
    0x101e003440a20180107090107400c030031564a2921500200d003d0301c0b0340483c04031840b0340701c2c1050b855401140c180309040d0192100092880000c5542d540075282500042d841200c101700400c0c00c0c00e1031884030a0181c031030300c2c481d03a0301070b16042e1401a000040190300109060200c0c0c2c140e02d030800030000350300c0c02c00405124180480003031030340e190889001340054405a018101c1070b4010401440003c8204086c0c5080d13030784c03015240840740c420040072801007511400c0c10303440b000041000f06c0040000003110044901482030200502500960b800a680c0c00f40076130813101c81d481c1401c000701045603010304034401e54207030358a03200c0c0c602b100c5840c1020012400080142e450796001e101081441401e01040c80421030b885d030751285021400344031808001c01d580c200d140e503401d80f07154a0f4042c4e00f00f621407d9009041c0c41e43c0d40761080203000104000c1503c00d001a2034099088030051001c0055040a90400001c1040304100d5004444002203050120750303034000e400002500400654182d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 205871645 1250 205870395 205870397
    0xe04091209051e03250b0a09060e040c090e06060906120a062111130906050901060f0b1218030301060e011d09042a06030f0b18010b1e040303 62
    0x40500d1074031040084103c03c0700c050782002c0c481d29100c0c560740c0c1e03000030740004d505183c0d84484240c0286800c01c41e507800c030383d03501400c020301000500301d22041d4032505450a0700c0325134454a024a201c80c081c0022608444840d902080003030300d09200586503100700c41e80c400401005c03503140405240c0411407941101c000f244900600000780040241107001c0c1c0c201408460300680300311007100b111203000b089014405050050320210520990300c4031000361807100c002c2c20040c000210301c0d203000c10041108580f88440d952074000f01040c8060200d4000e41100d104072541410400c500c044400d82c1c11019250070300a21520124040030031043c0055030081030b85841d20b403042062a03001621851440c0129000401820a00c901981d05d040c4450740003038000d06d04102a5410385102001091041c540003080180401c0002c1e03580e9242e0810900903d801500340083e144903410300800710a001c07040704c880c20a00c0d005104a0400101030700c40340d41c03d0103070102c140c01c603003605849070350003500b080e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 205872895 1250 205871645 205871657
    0x6020f130f05010311030f150d200108090a0b0c190c0b070507020a090b0f03010e01060810050c04060507080403021008070818100e2103010302100206070206070e040912 74
    0x5103401078040c2100400003070070148900c0b44500d81000712071100400800c05000a100410380d007980100103204000009001d0a41c2c8641904209000307003a0402100010101c01140741000d51081c0f56403401107108200400107110380d603880488501006200d407000400c2440144850419144001483c0d9150340382c007a072101003410014181c1380c00a06c940103000040050100607142e034980340040750448400000c01c00510300003d02c0781800e40f00c1e03456240d800d20521070b440072030660050085507149030496001801400c030f10401c1d81c03012284d84100d05c4040c0000c110850003003004001161048001c00d2400d0f4880c1e0020703c540300035154007400941d0030310070444215007200030550000108a00d0381d05100020411540c1c6a81181c1008015030f110003d080342002c0030440410007001526002013107110b208207002064000344001d070321804c0c40b440754000702030010071014001c0c00c0d40e5001d45081d66036080180c502c029440d4800790410343d22050800490000c51031401603d03141e80d03500d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 205874145 1250 205872895 205872899
    0xf0e030d021317100e010207060911040e0105150f0d0812150303130b0d0b12011b1b0b04020111030d0506010f0201020f0d0e1507020c0306100b030f0406020f13 70
    0x10100c6141c0c1c64110039940602c940583c010004001290100000510000305501101002c9280a40180315009180c41c3c10720b40729200b00103503209201190038040d2810054540055078a509842c41070b01c074030124414850118040d810b044100c0800c00002400000029286580b04c000560103012550310345820081801103201500300c003c1c104010860042d4140801da01301d0098650310380c844c01d0f404400014513582c1c0081c1942111070b1400e80146020408012940b1040c0038042c0f440c420020301d840b103815145c4c1035015808122954403004200039414a03150b840ca01004001780c000d9061201c1070f00045603400d410002480114140c000100d098144400050072403600307038503020f0941e401070101102072005c0070151980b1000f402c078045941da034002c0c030b514100800c50400515482c84030041020070b0742c00280c0881030000540445d0b00355680c04c108150b05500c2d0b801607407c0c159080000c110900501e0303c040d50014000d074001440d00c407070050840c4150b8429039554075040204801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 205875395 1250 205874145 205874167
    0x1101052104060c0c02130e010b0d0804091107050d08070201090828030e030a180801050705031f0e040305220602070504050a05130f0311150406050907030201080a0f0e030d02 76
    0x10360b00602918106010740821950000d01901d1a01503804000e0b0f51341c22401307c2802094229a4400c0c3c4094000301401800f0b051004440e84a4000c0d0303603400d030402c200c04a80d00b0301501250300454004001d40305132841c0300e0013140c45d0b13500070f000282190b4071003c440022075800001820030a40d880070700c002504203041d40d05280c0c02c801580b04180351a001c4c4028a4034404803c4860b08046850522102c0c01d20034040a01410940c019568030343ca00310801c850940c0000c001c5016100301c0d50102c000302059040b032040b0001c1c6000d034103060031076440445c000070b01a40241410f90412003c0302464200c0d01444110030046600040c0140d0003900200003a003010b1103100e23000420354405200e1840d1a440340501c59800f502c0003002c4101c00c0c220300092510948414038881c43d002c06170703061079a00301f2000c09548020744080d40c0440c644404074060042c0090a0421654183c44214840d42e8100354403000702100c40101c8130311030301d9080c108005041400107041c400080030005850ba0b0300548 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 205876645 1250 205875395 205875401
    0xc05150a02040e06031c0c1a0f101509060305220309060e0a05030a120203040803030705070c081b01030e030702060c01020c0c10050301090903140c07061404030807110105210406 78
    0x2e00c034000d81041c808480b02001b011010445205a4105241d026001e1304e045114071110488003541c5200103024000e007880522102e038024402241c0481c091901c0c1c0c000c407031807080031145440101c2d0b00700100304400c42c043d0304279560051743ca02d0b0f980404207040d100d020301c01c03182110440026510300410b0245540080070004011030542d40c1101160070316002ca0394070350b141032000d003945100e00c0075044618420000c0794050700300d1409503600ca0404040c0500b0b00e800940c0101c03115100114042800d540c0001c0315181e00c00d85280c80d000620900c80154010040205609041c1c0410411040561541e9004102943d0a50700040e41d03407031660f014500f0001c24906c0207214120312280780e1042c07940b02c41a07905440c40745000003411406494140c48894a8070000c5042c6072021407a440d1603440480c84000319000303520b41d6505007000e4680c16440d8847e0340001012041c00307000240c007080c0d0b4215a4401890181841031500010400e00d414052100c08840d1400180c0c104000070001180 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 205877895 1250 205876645 205876651
    0x714010c2028091113030507061b050309090c090406060504030c0e0405060f0c07240e010509070b0c01020405032b020102030f0f04060b0613061b120c05150a02040e 72
    0x9400b251101402500c00040c030703501445900c08860b00c0313001c280103101016040701c11481e25a00326010300e40d52440c02d90386500880c0708103808640361018242c030b0846511b18400f10305a015010310325221014080280040c005407140c20401c00c144440602502c0e030b0300c100d202400843e02c40984462a40c5080450600c0c0b94010b1303411126603005020014074002a507507003200081d80d021000d42da0700e65014106020b0079501402240407190404950220507900300c02c0559100820710207184442a11400c0e1141a5000680b0350300100f8200b0488074001c024044034007010001500e85961070000904d4890001c0707003d10315142c40c0081d00f1003024440310142800119000950562800c2c07443c2c407400700d0004000280d082c001c80e0000c0c081014640c080d0400010003442d85441d01c48240c400b9800c06224003502022504000000010301990700300c1d044802e91203585213000000d01c00c030032a000001c00350200c07054410300014044142d0900e0000313100c0c941e40c0030011303142c620f40004040350b08d0020f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 205879145 1250 205877895 205877929
    0xc040c020712030c0f0602180109030209011e0b04091d1506130f0507081519270e0109171c0b0a0806100602060106110714010c20 57
    0x4a5000148150041000720444091540b051906411030405484003404000001c0c8020115910f080c10820594040d0111040002c035408464119400640ba291800e00000c0d41c88280f01d4010400d952034259010f48500c81d410142010b1035461b00c11580c0d9810130b8021045d8151104150110f83c1c00c08030350f81c0c90f15118940105415800c1810450032140301030b000c03502034421100f0200001c24107400c4840e41081d2000300300014600f05800402915081d180c00c100c40b04941684070461030024182c0030009500c440744000c5070310f4081c503104004121031340207140048800c11f45140000501c208810b0700310050002c1a10442481c1c040064031582c0300108280d00e051100c00c02260440d02d4810f255102c0000015503d484007001500e0071100f0f40c480c03040b07072080804014a421451070740f0800c48109400b01c071440d0b44c0300e410030359003c030000c040155554040402082558600c4c40c0602c41031030107050a440074007460312191403030220400030307508400051418107410300301003c80e042d1840032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 205880395 1250 205879145 205879151
    0xb1306031a15010e010e060304061d0706080a020304020301090b0906160f0e011d0604030303200f0d0b0f130e28110315090a05010b030102070b0f040f020604170c04 72
    0x407910b442c51180780031128108207402d4120480c0342d0090414a00c2c001004244507140d10705490100c025182c10170120005000c2e001545103005800543d000c1034608940720003116903518030400000303420013801130780e141d074a80250802064600360080d001e548260b018142918001038202c0c00382c000c6071042030401c001c050703a5101f07280d40044100381d038030002d02c2c080e030324281c400580f80300744030b0b0031100140d000303030002000810503415030700c0041c0e50f0800d00507400161410310302200190203002c0c1c03004002c0310304010440b10042c0035400180c6000004120415103822040071400020300340f01c000484d5940c9441883c0c2d00c07481001380c2d092443c108100791034030450086d00d07000010700c208001007840303138064011880d0340c1d401d008103000d48520801c001d48505d001220241c0d61600000b050f03506510b40b070001c1c180c0b42018001c58541740d0b00650390203195110690307110203607400100140d03681d680aa81c0100141d42c0e80c80100000e080b800c003c0104404043c1d0609e003400e90300c041d01445186 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 205881645 1250 205880395 205880401
    0xd08010609061206030c080c030111030105060921011407030b030a021c141902010f09031106030414060a0203010f0f0e04060c0203040f0905011404050f190b1306031a 73
    0x140c44028101681c0861404030f8501491901400250140340c000922801c040000401c2244001030b09040e03050b03084000703000c9c42d030404100594034070080c044c0c581c010a0404c01c00245081640c011054600002e10030340854028046550031a406032000c0c8201004071414001036680c140560400d0550440107461480744540c0000c2010b05101d100c1100c201c241c844100500c504501300e80f40500e00c513401c0d5a4140310300c074101100503080b9002240850101980340c54594400e420380d0090307a0784070402820311015001045230729000200100c0f01481d000b0b58070010b1a01c103001e1540180c1a088003d40c0703a50606c1c82c1070b902c04880382c00c4500c490940c840104140842440e00a80054100500198903540508128254800e64100c14601982000000340b5985a58842c0b4104e484c0c00f21050b4960940104110035030300c0c2941d4044401c07080700041003c0c40d00d84c9550101012901000003010413118010942c0c0041c004200984a951000d040082c00100d441034408180d41c0714034040c0780d203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 205882895 1250 205881645 205881647
    0x20f190303051e070f022e050f010602060c070819090e060414060427050706021606020309040b1c050f061315090c030c030b0933060406050d0c080d080106 68
    0x2c00c000c000c102005613501709200700500900060360141b81d0718413110061035809840c9031103600d01240b40c4602524040c005501e49040d2254581038070f42c1ca0b8058991522a140500c10642000c2c0f000c1da072810040080907001031600c0c100400341c80203922802c500614103c10030342e1f01000244014000d81c240f90b0070017441c40c0f105101d5540180210303000985c0c4041ca407404407500c0e9880c9590381c00c190440c6204070138440b000510728100e850a500301d03803038040f03003038240f41d90410140700d1440564418001414186055007050345100f45c094014030200f000c0c841e4648050b22403c20a507540c3d0018803110451401c02d01407503502546d0b40c20400b41a96480c0c3d250801d01003101804405960b6400f10101081002c40044d00150380040d00074908a440e0b04098021541c159020155841000c0b02000c0d80d5592428092035042c01391307010810a035255a1800031031400a0900b9841940c03000f02042559920400c000564000e002a110342801d00d040300b031902d40d100d0302c0078040c8006400100142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 205884145 1250 205882895 205882951
    0x50a05090f06011214030d0c082d01050607030e0402160213061a0a02010b130c020c0f090c0f0f0a0c0b0c030c074d09041e03020f19030305 61
    0x26a505c40f10220341400300800030341c154005e0152501030a400c1110f1000000d910819440c042e4203040ea15180040c1c1c22080b1a080080b4601000000000000108100e14100c8094800180203080c4030684031502c02c002000c1b40d01030000010450044940e080c02d508040a03080402d00d8449020814a806d026542000b4810034543e800d1480c00003404002180c401e4001c01c50305030018003141c0000c00302207842c5000d4603008445400510030b94086e804685017520805603030f407a0290002c0c20031b40303502e00031020b59409074140f0650140d0401082069040040041c07840034515034400b0070b44102458941e6054002909a80d001e4200b1b1013032040100a90301101d4410364400c10761402c0c070410255080d06e002d03c0030698a0080001716035444080c0301ea15848090182c1000c80c000011083d10801c04000e40c2941e01410401000182414045050f40b420b860f05003e40112240601416100707442e1220b0043c1094058074205070241c00c140e0140503a503006258a01d000030400e40840d605414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 205885395 1250 205884145 205884179
    0xc050906160302030f030109060e09011802060a02160305030304050106080609150a06031401060503010605100512100b0703020c0405010906061b02040204090e0307140c010c03050c10050a05090f0601 87
    0x410380030030090003098000c108940d001c1030001103064403503030f60703808c00340003846144245040b004040c40001c50001040c8a41d401c0d60070001094001c001c200d4007030001903040040e0003015441001c0650201110340703000342000f14401c0c3c008550b41e1910b40340c001d0965107143d10440d9540d2101040c40600d80d00441c080004003152008131b441a0351742e00500c0e0182c0010350000c0c0035110803100f074802900d0f064010b83c05450090f8001c5c8003048d0384000f4851362030f8004101380300083d0240071009110141050198120001036105050305440700310140b40d40e8030a003021000b507801121304c4042130500d1b006640c01004018810408140b40c040058000138dd800d00d1801c2849100032090f00b156034540c10f44024200c4c1d420100805541441d0385940c990101506440b04a03010240031583c4a00140d0b075683d049045c0d40c0c0300c4458445540c1995990010080c90303070540540d045030781000c0100d00c10103109801c0c00a02041906040810320b0810000fa441c20078581c0184005000b94140361041d400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 205886645 1250 205885395 205885417
    0x3020703080a1404060e03060c0f0702060706090611070c08030f03071b39030503040501080415050703090b0603070303050418021c0b0a0e04020a12140105070908010c050906 76
    0x240d11405082c040701da10442448220002001007000304091382c3c00744041701c80c12803d03404c030b030b4154440c483c0410f02801000941c980341c100c10808039005080c807501601c603261113094041120b5915984020a0b0b41c5810007241c0c0020700407480e07200b48882c1032901c030020100c983c0138501c0d180e20014880180d203c014420814091410fa004181b61012040da003141500801c050142d4580071154680d07880341030302180c12005014a40380c200c011845111400c40790f11100451a01d4130b00b80041d503055400401c1030700c481440030382d61031441c2c156000d0180716420550340000c540d922490808084e12014000d17a001c0e81c49039005000081c0c00000b12015292854681c0341c0411322018103802901c40c40001100000c2c061032004d4032016982c0050624100031140300d2021611007400489240c030444001e5030000a0b00c50411401c0003007103d242a29010f45043c001d1949240f0555017540c80c15291000024070302c0301e0400c09681d0038410007030080400d140861400c65507000107175050003104960301d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 205887895 1250 205886645 205886647
    0x906042c010b090d020409020d0c081e01110414010207030803040501060e0703050f0403030509101d010e15040b0a020c1b03011a0918010e0d05041a040506070605040c0b0d09060e0601030302070308 86
    0x1f05642e2000038050601d03074072100000361242c450030f03040e0320381c42d44007903959041c141c0e04c8400500f240180a0039950740003103244141010b00e0803035401c8e10a000c413990141036004080011020990f04001180705034055400407035140d10380841c4041800000f803040c410585400e09220302c0a401f52041740d00320750585030200342511410380c01c0b42424079180300410319500d05240810300100d200c40240d042e21354040200801c07410000d00c03544409142c2040040b1015480c00100090104240d46800280c2c07403100500f002c0e08541000e150200300403a88103207900c10300700101180750034010800e6101c1c60070305e51400394450070045243d40b2405040030000040c480c001c89080d100c02d501c0302820303c0d0005d003154040364180801a000398070a010350542100c052440e50350f40f80800c4102c8049a074041c0c03241b4540030003a01c60344001c060182040700c0022210f0000120080b202028142114243c400090320708001d14043c4101d803881d510f9010036421940041001c03e40105030041141d070450002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 205889145 1250 205887895 205887911
    0xf0806091e2706040b07050c0d03020c16060203030604060f1a031905011217030130080f0d15080d08070203120f0604050703061a0906042c010b090d0204 67
    0x1051810300b05201400c0501030303030200c6403695100014200c3c0958000c6400124585501300c0840d20307803041c0c14408041d40e11800420106600c40d50081c0355110100055907a1011101588691030165500c8000144c2c408002d0000c18681440303482c00401f211820114840d01d0441320140e00b00c2c1c000c00c40340902402000049284011055004e2001c941c3c0808100c19038564a41c0001d04c11b48074025030b8040c0c4041003102d5140086001c44c0e0507510101000602c08800390f0340d03c1c1c032040040303080d030101c2010b0500700390006001030050f01c0d40d441c00100d01500e4480e924005000c80740f0716001d1000907080351104210780100030504a02c2240c251a00360076075681c00c8000c0c0c2c17641c0b041c1b0f001c1a922038512810803841d58a09414180030701c10031107040c4003a803241d0700d00301c060703510502a03111800000710100345040c0e0008010161200064501e038107140c1e59030758400c1400c042c0061401c494819544603002003544c164214003618100e0051424092080b01080410010301c0f8002e000715030311084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 205890395 1250 205889145 205889161
    0xc08070e041a0603010902070b07020c0109050d020d140601050f03011b0318050d080601110a0c0506090109080f0705120f0a03030207060b0904061b0207060806090c190f0806091e 78
    0x903402c00540083c101c1590b0f5603540105030020350000c01d0031b4407405201004151a10310100f40071560320416514003490a00341000c00201c2402e51000301d80c4220104210f0340025005140404120118409043d50350f1400c41031004140008000c2ea01c6a4906514101a03e02c822100a60349038640384c000b404802c0025000400386841901802e40d00c146104c5405081e400710380c8038400c08080ea202c03440000300503d441d0742c0d40c120502c010102c032103088040c0320908281740079020541d01494802103007a91480b8490900308100d40300e0400390003108050195003803988010666842c0d503801424000880030310a0b0b141c03291180010200344d00003c000c000e2104075000032052800c020440e0120781018a400c40c01850040b011181a20040d07440808450010500c40c0884410f0b403501d0b0141d580d244208803000d100206841181001406210681c000c18a2401c1d0b200f10940c85031105540440f5024004500003018039220790305000400480c40d40448107034070700100f080000e00551702c80c46c00b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 205891645 1250 205890395 205890431
    0x108041101030605030a080403030306050109030506041401020f160506060102060106090e04020103091709010815030a24060b0406030608060c0a0516080a031a03030c0a230601030b0a0c08070e04 85
    0x400541c3c907104c1c01046c901401902c0700100b040742d00ca40c808018590366400103540383c2403c0c0c400a44160002000100800d100b00e105803200e140c0700000516001c9000300d40030050f00149032592020070b041c0894410800308010f0740e81c01810034002010300750b1504070014107900250048800c0300c0004000b2a0440e4001c1d04a540c1403a0702c801842c00108841d03401116581109184600280220000c2109005803032580032014101070090301d100400346c0c844501a039011400d4860200301100407001c2d05002d4070400d0050084154066030311442d02030010140c9140ba008550903812000c140860b642020080380c1014001d130409644404610038242d41c5080c810002508411001903150340c542c0d403592007400b803017181c00c004001000300942403580d85d0042c500001042c3d440445444003180382c0440d4107440c00c1d40d060700d0440104207000114200700d0207130701c03c849034003504062104030416401480741502070b901d44021549400d2000070a088016081540074a50390a480b00ea00c00d0040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 205892895 1250 205891645 205891649
    0x60702060901300b130e0d0e0a0b0307020307050d050307020601030f08130b091801140910120515070c05060c13120503040816060522050904050c010f0e01080411010306 74
    0x721404481c00f81c8a6800400350085600302489140c180708265103032400e601c03c06002031044c034001c2020100d07042c8140c46069200785403580c4012102400102410b40900541c03244d0500e07030282d03456403220718000786000c44140810007441024000c00035007660004071141166040912025400003030f003045d00d1903101d40494215401085207010600800c40801411000c2003910500102c4d44240403500f2648400c0c052441c0d500013032040e500e0030386400610507030855250030b40c61101c1c0b03942d07050b80c400b5103200034000c6501d50050100310f0319070395940f100760394080201c0c104210390080a50320140c07100c500800b200c1034000c010902d01690130002c2d040e0800740000140b0790740d1600c5141001c1e60340f40c10078803c0c89400e03c03961650520341c0400c0c264610071503806071122418004000c4001c3c15001c1c12018020340c0001058000442e503543d14a000d0144e0b0065000c4c089c0e05c4000000100500300f401d000c1c2c424828034901d06910b90b641f2000305a4065004200080d0444e00e143c012005441e4035 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 205894145 1250 205892895 205892957
    0x303020d0f0506010801050105040b090904030e03060703050f060d150504050c03010e06040507080c0d0f06152402031603031a0a03050d080a06050d020607110901150905060702060901 80
    0x31003040d40ca104250301c0180503082c2600d451085c1d0380e0300c02c01118a481240910000301105112038091400d00c04030b241e070014428104001c01c9012440403034503150b405c44418001031380b901c044c06803100490003003e40101d015210f20301c10b0109600c030340382041d019554808950b82d03200006010300000f4001100c480c14020024442007007035450403640d506056800b5945405081800100d0080c0044c83c80400301c00902003070b60480d15a250000206e02108069482ca1703150070741142c040e4500c60300704001e0500083e2410101549241080400710903503604c00645d88204040e154048411122070800766151602013002c0520824006059580c8210391f038201d800f440d408400c0103400302c2c04102c50b90072642d07218030355541e038514181a141c44d403049a0300710f01c03005098409410840002c200c440d004800220503a4143c2d400704600d03400c260b1048a42500c0f180540c074078294004290801400120780342818851aa0006a032610821240170b060044690458000b1185201e1450701c0c0c01034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 205895395 1250 205894145 205894151
    0x90d0c03060c0c0302010b030a02090c0c0703061b0f110c1504050a090207050f061303030908090d1511040308030112021507081207080f0703180c1206110309060a05040303020d 77
    0x90118050315100f03650030114095420901d40c81c0b040c0c01d00140c19030300241c0041510f11f854460540c00b03e06507000c80c1102d80c541c0103028010020035064000c00081d0022800030070610704140000038598201c0e001c01000f00010b003441092916400114070500e4081114504a21182c3c2d40140308984200c3e84030580286011200140b1500b06a010b070518034011001c0d5030007060320b6290651941ca0032190710102c9900e0544550110f48254004100c1c1481210810316000e40840010302e500c603000000c80b2031740b00100e8842c061a2150207144409001815000e08040c210340d1340705d1550005009409001c000c40807a4015959250100c0890340c1e0044403540d642d4001e03052600480c0e02001c90b42c2c0c0c0440d40f000200f95400d00c81c000b15440f4401c90301401c10071f619a02401c03406001d202da400814010141800004555140804401007544201502c480925032407c1e00070b880403040301e21203007502842046020b24010980c6c0e030703000c50740b00c100041d980c0d5180380540007801510340b0903101601e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 205896645 1250 205895395 205895411
    0xf030a0b0405010b0f06130b0f0c0109111906021002130b0432030c0108100f08010501090507081303050c120403080304060b45040503032406090d0c0306 67
    0x72066100004c510340564500811042000a00030345100d20490700c110100107281c1004901d1624002e4100790302c001481e00e1a0044441c081070030354226503c00d40d00c3ca48403c402c130341c0c2c034a0a9038054a407022402280f08441d490000085e480c0d035241080100a01e80009443c886e0245460100f005001442125619281c0f0781417004440b4024008004100d0310340d105008000804030301041c00c038080180107141e80030004004684000003d045401401c0c1c00c0179010a01103d0100054060036841000007090361404414106440010385014140070004062190501070105406095505420816920344070300722164075002f440d6040c1c6002d064085000f00400c100e60740114011401480d09110301c20803541002541c20401441c62402000ea002c807144052400300e02c0303c03e40c01c130180c610f07a441d449401259280201160101c546400000c20000c0303c061070904c1c01100e0b6400e80046030b0158009002c41d03107503c12100030781d02c121f011168503400c110039103107000007555000c0020300c4004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 205897895 1250 205896645 205896653
    0xb03100314100c03050402091302120d11070f0503030403020111030d1b03050619050d020105070f0507050111150109270302010c020d03091703040201020a0b09060f0601030903020c0f030a0b04 84
    0x1025220003102c1c00c0c1428040e204144c400e0088078099500140a0342c8640c4505950451400d040281281c0050084100d222146808d00a0584a100c1074494039428440085007608100d0f0075002801d5890090b01d0500554600000381c8065980c207090104a40300a010401c0c9035014944846054505080c44092400c00f21502c00404143e030b80c40c01d2180c0d8848408006046050300300001014800ea80100940c1ca000291080e800380181005440c28420b03803540408206400816221079100300c4040082796442089003903210441b8010704840041da8020090008042c8a80a201d40c1c940030007403084022080c07441140d440d583c180d2103411043e460302034043c141041044d00580901c4100d48a01c60080c0500d07800c10703900c000d18090b0326100300b10940460704040c00681c114807174014490b0010310b039459498040e1246100420b090b283c070705000b600c640b0b001401d0304c1c101400d1680c00000240c00043c2015480780c115600d60300700401c00302280c0342554060001e0f00350415401488188 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 205899145 1250 205897895 205897903
    0xf0204022508042c060103021b0613120504150309171620010903260301090603060605060a0806010806010e100306050a0602120706110403020904061e0c090b03100314 73
    0x210103603140c41c0e210312600c2c00c410f9541c4c20450107009218180c0000140345600c40e900078400f44011040940c03d809840500c1c81c50b0007812100810080c2054001c8414032181c04401901c6800c5403411a10745030529241c054481c0c1d92400381014144c42d10103603820412200000f110102e5150506034640e4102e4003018062140d504058038170070190819110030b815000058007a03943e040c0c4032903480602d9603a48600380500d40c5000c20042e0071000e2a058100d001c0e40c01980207044406012030103a046040010803185186c0c0020312403401000b0500c007203a0003c00450340280b003403c0c000d84683c1c07900d0050754240b20120800383c3c040c07811401c0741c90080c0c02d030348030100303444003996030640f0903440f840140d81d0340000e20750b1440713001e4040c4100300004e10103801032030b8000960300310b00b41481d0ba41c0d800f0810300482507404030703002a15038440d00031040b44107800c101c10990107003040c40481062040a010304d141402a88c041d094000006050350004079040002103905c410104c0300507229a03500707501c1e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 205900395 1250 205899145 205899149
    0xa1b12080a05150609090910051006030f060518100801020d0903091d0c030c0409020d0b0420090d060b0d0b010f0915050105030a0e0109050318030601030f020402250804 74
    0xe020b2411012405240350a401c1e590074840c0070b080c5500c4c140715142041407000004101070f0741c03842001c64080000707946010f0940961345c072740244e20026041002c083c042e6020a01d90b0014285004c0d030030030050fa2412070500d00e080c0303041d0b11800d69445504000310310030880e80004501f58000101d80801d51016401000ba05001c0d80d03e1a042680301d244070242f01803416040004210f1510210703020361600d400464022510004040c0340540d80e48642050b40c000e120121481940c641007501d607801c04c1d015564415400303506903605100c0c0c02c510900b6031b001c5c4851341405200040345d24801c2000a6010308a0200010b103204d5178114103190407680108240141d000342c0700702d1600050700ca00350780500c2c1039007154944480c110b0b030b082200440d290b410040881b00b89684030081007003005c1c428449d004645014030040c681c1e48894403c41c100750804840130b01d0003a40581c00410115602a80070000258103e0340903a40f030104681e18140440450450500300c50809218000c000d540001001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 205901645 1250 205900395 205900411
    0xa03031808010209090403030203060d0c1508060d0203100e010209090118110309031e0921010c11060a090609021503010e060f09040f081309091e080a1b1208 69
    0x1800075140c0c00c0003400e034001d52411981094503030001c034000a000350041d5600000190120180100988035003800100300d40c030200842010000c0308020940c003050b4664450390640d40700d030b80c40a01d540440c4c0d545403040e1241d03150720ba595141d010703603c100390119921190b006082d200740d540c69030780501075080d94070901c000b01850014144080316106094034440c116042c05581030100c00a000f608000d0701e9921010f0100c410010b144035a40c0f007614003082c06034400d2041c20162281142903084a40384203100e010700544a14480300144006a080e911030b2460b480800e0451444c54141c02801551030000d50084081501484500c0c031280954100d50850140740b07541d031580d60500c407440c00d08820880e00440c2400c00100807588241a10120038465420f051401d0010f90148202a00e43d40102ca00715860b82c90400900418800da1603513825042d6005c2170410699542411510550601da002d22241390011100414120081c1046d260030284003850005080001400ba11040383c03008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 205902895 1250 205901645 205901687
    0x30f060321020a0312050403120f020d060b19050c101d0105151309020d0c080a15060806011205030d1404230c0111030c0a050606030d03140106030b03010b0a0303 71
    0x5480c1d510020309811142c0d05519280700407542c06074010f01a000080041e0240800311003201d21204851003030b0b0070710701c40c0190010b850340d0b10b042440056501943c046958000188803003260445021030034403403410380342451940c0d0040e480d00a810800503174140030515217008800300070380007c00804608103002c04001c116a59801a4582c861a103403900d00340c0007480d4003a03950000d005075211a403050300041010b00416415612000b2441980d0007520064000c100008200700d8070540b112804120030314103000007810101000d0f1754170414401c0a4081d15001403d4040c40800d00031619600404c0c3d205100c0100f40c40d114090701c01003958111000e075115203035001d003c10101c90041178000e0180203404041041c6004494130002d9042180281c0803c0002d00d080e400200705805100b03101d84040e00591a1410801d4100f20209190303000780b600b0040305580090122100c14155102400c00107608910140483d00511101c05441d03045100302001206040c2c004d0101c131060700402080c4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 205904145 1250 205902895 205902953
    0x1c03080415020403051504150906020c010e0a0f03030506061204080414040e070303050a12050f0108190c0b030403120e0601032d14010e070e09160321030f0603 70
    0x81c008074402c81c0720150058001e05070700d0090f40300114900f130304503000303072180350900c6410740b2035804803450b41f10101c0e42c0d640d0014015060b001c0030b0150300c109110890140c410302d6281d840f01840400c034104010101580d41c4000350250740d9000507600940b4200070390320014074082c5054405603101e409840740c1005e50008a0b0458985030103400c210083d9100030b481c0c4a0728542d000d035015006490a9020300480c2031099200500c20320400c1e1003035203800d00d01c0b52554501501581458541082c1c1c1e01042e0034195510041803400600104446608071030a5680c0d41c0c6050881d0100080450b40900c40e003496803510b0260800501c07903040e603026010b1074545200b022100d130002401c5410541054280c0322001307011030355072421004a400c89800208500905144080c20700c40242c12046981055800380440c5000812030364a045c50380c1d00506001c03a06584421030014200d10484c00020541c02d02c4030840f40c0700380c001d1400c0203c0701d0701c14000d05860b0315002803800c6d40d41c1050300841c42c0a9030744c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 205905395 1250 205904145 205904183
    0x1009050c060c0d030b0310110702090708010509041e200a0b18060d02070b010605040609091107060b040b04110d050c190c030318060204030203010f0c0e0f1c030804 72
    0x1c40b200c0e48103903401004810103034102900074004e405c1340282e05009500307020051a80c6402a03100284e0a542042c3d501e42c01441040300102d0003405010810120b08018090b0380c49444685412035080700d91071601141005401c8503007d00c0d100000d2040054103140014200341c20b846121840703040b00d29940e241e0710307515508024000c0c1c21250702050340420200c4a242802c000405031054203131005440e161081d2206115028280d000f42d0001d44001070812240e41e02140d0036001c1c0080c600140000d011b10303004500c19020700300025245a0381c0301c10603802030381c9a500030b84101001820a100b19800180d0902c2660001582001d200781460300064601840340e003240e00d078069180807100c04128402080760103001480084061541e03500840c50700560400041d01c030503200f4800503a507541544103141c2036480e00d89428810070300304a9120303282c90304000b801d072403e807041e90001001c620075400209000314030b42d106235a0b0001419408141540806240c2c811400f4001000d40c00c070f01200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 205906645 1250 205905395 205905397
    0x501091a09071d030f0d080c0a02030d0c05090d03030507123e040e010501120b091503100608161a090103020f09041506020c01020309180405030c1009050c06 69
    0x21001da204003a507001507041402821218110f02c0f00105003c11070381500701203031504001c000610703c4c43d4006400245c2041c3c0c000c0310b4942c860300e03e00d141801c01c0300c0c00358041d54902805244200c0c103511003014914151183c4141c0e00c159030014860041202e850401900802c025521200040c6018000c840c82014900448030701d4421000c0c202440e85201604904241c0c1707503005452408408110040030b49440c1c4068070103001d42e0301075400c0551520001400c0c040100742c848080c01d08281c1c80c000c06550b5031102a038080151601c2c07881090010340041d0410b440800c0804600c4e04c0e0400105100c50002500d10b184c0c05002d0304c004106031624440150f01c80f00c0804041c1d000400c21010f45954429000360001c220180c00c62803c1c0542140040c09850108003540780c0c00c40284000c010f0590304100369898610f003070000e585004100008030340413034810b180c950242d400780e0b00800c0420104000312800b4100850540d0909144801468050620f09009840610454041d08040e00e0020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 205907895 1250 205906645 205906691
    0xf060a030215070302010e0a030833041d0d03050a0b040e03030711030403140a0302013b070b070c1806051804030c020603011806090908071407030213050109 69
    0x3070644109260590300b0100541c01028210115501e40b0a18600040f0810651000c41d1080c1ca440c1c0c0c440c0391a2400e0019224030000c03e44521300a844109681d5100103946003480c00b05070341c00318405051a8010314050742c0640050051310501d41c011240310340c140d00982c000d5042c20401e010b1500e980d4208000d41e0251b460881d5581c00800103c0c1c1d01d14094000009110081e00c190fa060941c0d0303454280f41d09400000c4c0d01d4a542100700b45101b0140e0a00c00d591081d11440c041ea40e566090071020601000700025201c12003030040e441000c50315041100200030000050190760760040b078900006001e42d03d1003800700882e4012000c840d01c0b0003901a8200741c5a01805c2002a02d82120310300075505d80151050b0140102c4801e03c00158584800179030103885040fa280e03c0f00c15642c002c0c0030403501ca641c040303203c161403c60084000380345030044a04054000d44e0742e90382443c4103018242000000d50000350f100040c04001000304202d900900d04a55660f402040020030341c101062524101e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 205909145 1250 205907895 205907899
    0x801170607120603050a150506041a0105160b070309020a290f092d1504120510020304060b0f0303031e0a1409060916080a0b0a0b06120f060a0302 64
    0x80000400d842e209007401c01c1c2005610740c0c0421843c3d03580e102c072424003e814205407203405030740c00d0070301440324540941c2da0000c8060f1403c2250040290711503c0c03004c2c140c0410350400400107201001101001c40449580c4d4000040d5201030a100101500511030007500300c0c080c030441080026100c0018609024032005586081801d05240340e81129990003800c10709680301e01032091540310348405600005a9a47c0c1503148485000d110030302440324541146c2c544140d40001002180640c00403e071003c84134540e1807000d40a010745412401c0480c00c1c4010003907144088204001d1000cac0d0b80080140741811350350351000b900104241500c80c44101c940c41120751258020007210028407115a6010300007000000b02003031002c00c0641a1801941ca4900507072148061210590003071100307a0324181980c0c10b01d00003510300540300d41c40324444800a4800c50400c0c1c00603442d00a00e400404d12000010002c51352010100c03294001e101081d00d40e5100e1420020018501d400c1451480080c1c07600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 205910395 1250 205909145 205909153
    0x50912010e06062205070c0f050c0108090106030201090b032706070906030212160905031009021c0b0a0e01110c0f0708010209030a02090603210406080f040c1511030a0f080117 77
    0x1840b20408017401000c2d040c502001015041400482c035088413000b482881503003d807000c1403040c0e000400300c02001c2c214032074507450082c0c1040144e812503141d008543d81d06120548a0343d912296104500344d074000b60b40e0440049001e40030104c0d001c1001c40c8a081d079903d030030522684940c03007103049006041540c030082141d0808a0f400004071340c2405108003891400420107515800824241900074030142d1102d51900021402c601c0d0011000504003100c0c44040400c400948452052040151280920382d507290201c0c49606400c0d001402e0001075808816541c05403019110360300d080905000303c0324003e481003c1400601030003142c6548100a00400014515800f000442c1c2d40182c40c043d450312440b00c1c115122108204d61a039004054001107450324600a40075001001c000d180d20150725045c01003000140a10203468192003612a0705410010811b400b6240403142c510030070503e2101107490364610703070700440c03140c1451582d0380d0703800e40b03641c0e01c0d4520141d1054451007854a504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 205911645 1250 205910395 205910449
    0xa020d14070608041a060a14121209010905060f0702010813050703080d0e0a030e040e0c031209030d0203070c0b0c010207170310060507020a09180f1209050f0a15050912010e0606 78
    0x42049988c0355100146001202c490000702140f522a00c1c1c541c50196520100c1c100c141d135a0010b510074003c00090740c0c2245440020200c26146104004009050100e0714010459140d0b0f00d02105c043c95074080e04840000391603040c0100e90b600580480d020b100d041040f881010200460380a850b26450380b0341003245481c0382c0400000d40b400071420181482201003240e00f541d030420a5501c0c10b50b408002940c0d0751008010b2609000c424114201990700c100b15400014450308c40074411a204804035585a0011980007400380c424048080e180c0141c01026181410b05c11009500038502540e640f40c0041d52060b090750710340108034000c4c0d0f020f03402c52401c0014a0306a00a000b00d212410300081d0034400c16503a059600340d000f1019505800b00c006202c0106402080c10302c0607140407600d012134950b000c000115a452540166080e041c0256440c02000d8000c20a8480038100100341084540d00211868020304801806103a94815500414800e0800380f1111040d0103603154964040d10b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 205912895 1250 205911645 205911659
    0x7180609141602030c060f01061106130312060b03041407050a03210207030804061809062601380f011209031b151b020a020d14070608041a060a 63
    0x640b46801c6005500040099100c810011b04c9035034411a546035440740c46504040d0010000302200718415555070004091020511150340c4000c20320303600d46094400c1d10609950030000d09070660003607140c24004402d0004001c144144d41c9400d2a4417821105910f540c0c0303007040455041c0c3d00c000b50115811303030240c05405403006034401a001c658012144101e940385c1d111140f50344507038403800000303400c0140d528030518031040c050000c1c41c1804090143d603080c2500140c0b08041144995800d00d045440007240c84020f4001559242c20301d403980b00161902041604d003240e4181d244008030300d48074104045071421665401ca040c030180d50380c807210350480604500402400c1c0040e02031141400f941c6844000d4039000400c0c86100740303074564403902490355210030340f4044503210f480800d513282c000000075030004445d0071403a01125081000340c40e1b814000d4200c0800740e40031406000300100407cbc81078015030b110740228440c442d1a2060420142080c0c107891056603520f50015481004000302 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 205914145 1250 205912895 205912921
    0x21040612021201030b0a05070e0f04050702010e0601060315120b010e190c03091202060708240d061b08060a120602090d030801060e0603040b060607140718060914 71
    0xc05488000185000ca07030361440700d075104090b4001ca070010b1391102042403d62450140542045450820205040c0000009001c0615911000780a255107200240b440c4e40b0075005281c00007034400c2a69005d5850311070013006018a800c600c0c824003c2b2501c00101a01000d100f1014160000710096969003498401000824007805d0402c02d0044400405424038031441491302d40c182e140c400141d41c4442d8031307040008036510010f000c255045481003044198010034055817101045403101c110607030f40b0600600710f89080c4081a00180940c1240007008019030184100800c4605807000d20040c40c1000c944016080366036a400c0302c503026040001041490746c5d1322200b44070364405070a000b003203030100790106d2115109400280e0013100400c2225000307082c0c1100f1003425035800e0300d50f19040e107d1120100025202c0f038004c440000d0507005000701c00300b4640900c1c400c60103489a40b0342d07610f05403074010f51102160324554941540014080b01900ca00c58404142c1d200d10f0300150307545500541c42d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 205915395 1250 205914145 205914167
    0x11d0705091002210d1a130222060512090a0f0204050a1518051f0302010c0804090213090c0215011e15030f0b0604180902040612061d2122120302210406 67
    0x2802d09c4030a11480342401c00b080e1b02010304260740c0c4154445142010500140401404410164000c00141d10106a80c03910910999406031000710740c07900d0b604021002490070b540303840c020740604240410300001440003090742404488090201d61181c00f51b40d1524070b042082c40140402d414001c0006500542c2c0c030b086003d0190428038100796032200960140e0340b01d05600b5620450300301c0140003200c042d205800c088005880109056074030203101650ba04018003c45d480200c03001c1440c3c0040403807203640400382c01d034540314414001c1000000f402410784509910400c41c2001314110f070f00d041060a03202103c82c0c00d580e00382d0291310700010344010800002d041c0d03001743c0c982502103511200c82110400c000d100d1031000880c10030f0300891200500d0705046800c0c0c540c03c580d4420042840014940042400526080341d03034000e24020411380d2200c01c02101e071441468640066840b08100e41c510160b402a02501c8140241030030010004804915200500300d0610050000318410f1954290b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 205916645 1250 205915395 205915417
    0x81306050a0b0405041112121804020c0d02100b0303030402060703080601020709020c0d020c0f0f090a0b0d030f11070e010b070203071805011d0705091002210d1a1302 73
    0x240d907003240002c60309984c0c00300d0702035031441c0c5c1500d0b50100b01d003841e13158408030400c0e405c0505036004d0621844242449510b2600b50000c0040c400100c0694a941c103d8070b45100c030208407480041c00d0301d40079403034030340c820340d41c0303003010316000e54010386050100482e031149500070611407030030160340c0e8161840d101c003400d8181140301d412408a0103603038602c01400500040c078020090842ca2600c0240740c030340d200c1c1d26a4080c080130561445141c07540f0f40c0c8074840c0d02048881c0d0203e0381d00c2001d00d00c01040c4c5105c1041e40542d80ea000e050074140c00034440d035508001b0395980a03041402c062500e94894035482150314040c0d0741c03401041130340b0341310700508205803006080e640c0082da07504050210048441c0714000fa103940b240100114245010380310224100403500c49407514002102400310302403071000c0c0d4060000f805044604910034000d25490103c1803450103001c0b000d0080072034250300721110600e489440c012004800504c0004217001c1030100901e5000e01d80842c1460f00040d4010105001c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 205917895 1250 205916645 205916651
    0x60c04180c18081605040b0a141306030c0302090703050402010c060b0a0f08030904051b09010e010309021002100b030102040f150915080402150c1e0309100507060c081306050a 77
    0xb071400070b00e011004000d00920004040c01418403248135405291540241e102d289030101040898445d240c003903080300c0c4000068040d50841c4c402089075403107080d80200b6080c0c5840b102000700514820f4002c2681c2c0252500125540d6a100c16021039000703540182c0441e007061415070014445801408803850040e0522400ca950f801ca045c4140c8015045850580c00100348a001d6080034400d02e0b50105542f128280c0703021341d03034010401358454012202d04000e201c020320b03100c5d80d000e03030000402c8680c05442c04400e036128640094451411301d4640c9400f50400704529018901402500c0980b030700f40140c1d14503145030050302001c0b0201007000d44284015103400148600d04440d1075501d014058490031014541841080310754515800400708402041c04030b20070b04403000170881c01c0207110b035511241003050440c2880c50740c000d80c00301a902c14403251681ca8815445070180c6262840717a80140710b0040402c1050b540e1000480e040400c04a01e90112070108550390040750300486020000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 205919145 1250 205917895 205917917
    0x1e0c02150904020708180616080d11040303050a030c0810141302130806010510050d0903031e06060e0612071b020406120b1609050607020303041d0603060c04180c 71
    0x100b0141d80194400f5140c007400820612455882d60030007448800f0308071307100740c6410f082c004603501000c42c01c240907001d11750102d184c070002c4000c1c0c1d010684001c1404520703070b203403541ca180042c05039220404200000e410030162801d120300aa043e1801180f0700040343c07011074200340c4005120002922050741c010401c40e90307101986141c0c4001e1165156042220b0074103414131960303c2c0b03000d0040c3d0005008055214080d20b102e6400001d448410600b4000030401e900c141c10110007820202c80682002d911094a09140c1d032855800b12040fa25030340c450810f802c40e604100121401058580171440900e500020500303803242c52502c0d48079104449e60034000803d9004141140e442c0c3d00903214044d59058940180100e20078802e6004042a40c1000c1d413614a40000b841c01ca91031003550b001d5000400c103101150f0781071081c1c902500c0303440d000d520619892089000e03a4807003540c50754068002d070320100c1c0d2840c485000305e03029221244404601411042d00c0e24008258075200041002031a00603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 205920395 1250 205919145 205919149
    0x60c02010c05092710050916020307060c0c150c111504021011030c030a0314060f09090102071a010f060207080d0c020a080a060f060501030b150a05040f03050d1e0c021509 75
    0x115002c5e14510b09907421403401d00091117903c40f03003e0015455450b0f4a0400d40740300d9800401c075624154010f10101e9080b000c0407080c2d604800c0c0ea131004001181d13100d518100a1a00da000481c8030700d460313a4615541071281d00107500c40420b885a40c0164061078006409402c22038203d040c85103203494843d010042840409095420000200050781c00c00134440c40710f55450b0041400822035010740c61a241090b4ac0010001c07044600e9084c0a03401304400035061b1a0f00b0b40c103461a054001c5012403040b0008001303050410000d00444a50700520130300410301030700c00542d00b0143d8042c600104081054118151402d4560078003c03a4001c43c04280490300e848203100d191000d038458000852104802d00702401941c07100c0c0c0099041504d08440d014480d5640c1d0a03019100240d60282e84d91007080440031100c6206580084244001444002040020000741412060007542e00e849201455111904d0390310b4519040c80e00280303101c0321040c09440c1030506816046000c4110320300e85000840 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 205921645 1250 205920395 205920469
    0x302010c11211b0a0b0306090a020d090c03021903080a03180807050303151c0f060b0d0c090e0712020f010908010f020702040605030a020105071203060e0a09060c02010c0509 76
    0x11200c00c19003000b038004444140280f426020f1140c216240300d000790070410f904d0030034003004141512402054012424100941d4101c8007507101046003403003042170509045011480b2031004a00800c40200c58900694140030101c080c0d80c1e000600614000000100310080c0c8082c500708410039840d169124002002203000340652441080a151039240c0f648984098010b44004a4042c002c101480888500d241107002030f0a07a105031815900b000d2400c01c94010302d02400020b800c030b842502c6030310501c259103400c0c40071600914400c0c0414141d4003070642e20750740c20340318030385001d8400c04840005143c030707010001d17007564185401c062450b980d841003030940300c0e40009003030119070001d803990a40c1013900034403015103020340040c4180b5505600082540c810441d000e8131a075150081c40207824800e0b00908000c20046000007680c2c2040d401d007070004c00030007804949a030324051942c1001401801001450042d94903030f0b41c11700701c11400380407090007410750040040d20b6184800ca0190b503114 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 205922895 1250 205921645 205921699
    0x30a0809011839060809010b0a15050409090303050415020403030c0221070e0912030402030a060209150307020105061305070f0f020705030f070f050105070c0b1b0609010e0111040302010c11 83
    0xd1900f80b4014038103080985802000341c684c11441c2d04007030003804c0d50f8945681034030440304851102501060101411540ca0080b6000280801e040800c0d540a040c2d060308450f010f0750043c00035820b10501a6903a60480c4120301c4020045140001d1881c00341c40c2c00c888100c80d91069180c440b28a0350210181d5003004c0564000c40e001084400c00c0c00440719081100901181e0b0704a03605185040a4001075070744c1c1c1d000c14004040b1034001030140c0c4d03640c0341c5e501c001c00620b9400c403810f42c407401d20030006406004c040321018095040301101c056001c00c14000d4a016004648441031000040c5108039468034901111106500c642c803400120380c2c070308000841c448a0202e004d0504c03207003449000708400c8860b600160401005001d000081591000794608031204d090405645030780441c103191300107000130f490494500804042144824042d0440810b10030294020028103204808241090045006c00703800074071500030460024000414000289200a043c0920b1403a40340c00c01484641030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 205924145 1250 205922895 205922993
    0x3280b0c090612010824190213080a06050f07050306040c03022203061109010503131109071d1507030e0d050604030c0506010803070f0209060a05040e030a08090118 72
    0x180f004001c001c0040c46880d002c1c01003250340d000c41074202e100030110894003410407800c013240300b00900d80c0915140c0c100c071105008214140b1402c0d075941d12441c1c580501e006d050b0740700303800c0c0400a44001100030b8103512650417a1100790a586418007031200500040d5820014158208041e10000b6180c5000f2440d03a001015042441c8e0b0451800f4401c0c0c44007403d030b95001707800a00981c09075a8201003030781d91003000d50aa9400881c1c1a08041420100440141c0c0d0003083c00702c24001080d51011502400094007920880392000c03030300a0200d1040441c02030070722504180b000d040028400c08003013022410052000256a050b81c0300d044c28507806440440205010310820301c208042480283c1c010031040300503500384150b64840c902e00583d842f0b0300912588030703880000ca030381e40c0ba000003501502d0041d01c02c00015568006140e40e0741d0201c59010042030340c04000400091701400f5010b0381007890001c111461049954440750300799800941c0c1000e98540649100d01c07400c54080018640e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 205925395 1250 205924145 205924177
    0xa0b1314061302030f0601030308071b06020a0509010f0c03090b0f1306030207121e050c1606030e1501030812130812011703070317100503010608010b03280b0c0906 72
    0x30380304051408000341d40d05d00740c42c1c1204c0010008a5001503a4a5010140c3c0c2440413100e04409400d0000b40c20701c181c004e0072030b03101244200740d8680c42400b0305056002a2900b078030000312000c040c0c8990109080007000912030b494207120b50040b6801601c0100c80c1c1035401420008500c1c0084902c81881d000000020b034081401400d1010340a521494a402810014244048180c542c07010981e4003400105014002485a292410030071140c1c50f0703d0100f00c0e80c014010344568005026003440000b0b0307020b920440f4203840304001c94002580c100c9030321820f803602d03000c0ca40503243c030501c000400540b081c5002d00742c1c101c081140d0200800f005400d242c034509242d03040900c455100b44002d011915294000c0c46104000b90300031090b100c01c0000703100c0011180c1c2e00d00d0210481088a900f100b81c065081000005814005410984012000f141502c3c44419071291602030f40180942110b440b0036202c42420100302d510788440d8200201c0803083c0c0c642150600451507a40c040c4910300340724a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 205926645 1250 205925395 205925431
    0xa0e1b09010c151406060316030908091009060305070e031b0d0b0a0506130506010203090d050c0a0b03100b190503090c040614030606060a09050405060604091b09080a0b131406 77
    0x5060442c4c944d11200440e070080c21820241c0d5036507080c0d12450041002d041d521500b20f005d111008003a60724031340008000c0070403440c04500c01040700724680324110206e8209004070761114021030080c100350001400a0081242050b00c00101b81505000c10760050301c100058070200700c6a4141c10301c41c4034040300200e81c0e030802d84244142d21500c228880682e42c03414003070203c0303a0b0b40803040b24407006e030448184581d84442c3c05d00505049076038440591250b108400000d500c1c9108000e98826500800600e814a555100310031443c42020850f01c5841701d0381c41c9400c5090701650107160822444412502d000c82d9050100b000c81c2d025401500d00d1052112810300390789020014140c0c040800c0d50318074105846201d0242000c0d80b04d009140c0b166031940c1c00a0441c0e1203c0094a008242682c0107103c400441c04221003100b45000400c00091800000401c480400060001540360b100640c52150703507443d0b47c4160380c003907045400c03510b01e200310301242d065020800c41d443c020044d0210070072043c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 205927895 1250 205926645 205926671
    0xa020603060a091b180605030f040c0b04080a05010e011418120315100e060d0903050d24080c03060a0c03020c07060201050a060e041a06060f1303020a0e1b09010c15 72
    0x108204441185da24038405090003116404030903603820010185007003c00d0b885038a081c00e03800c40749030010501d04402040c0080d2001000402458907806100200443c0440060031802e03500c0f10709a110880500c1c0340400c003502044080c0c544000d4845080d41c440c00034120100107a640141c0d012030802d0020300d10500c246c6406030300710000ca443ca04200c0200d1001d6004101e0303034000d03c895010415900c1c46220141406201214551482140f0410000c2c100400c40014000f514903a000841c1401ea404941c02000140f060b401080080041009e6505c19100d4030191481c0812041050780911038061499010410440500201e40000c5801d00d411510700742241c1c0c20380d11840d0010715450a0001140c07611200c2c00c410001c40010b0400369403880d000c11041d12a40a083d003d50704000364a401103440355400000f646d20071140040c8469441d07880780500542a64500c10000d44814004c40090302c4500800c10b424060406c0014100f554850780022420301032030315030182c0c6402c0c0c650a04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 205929145 1250 205927895 205927907
    0x11b1e0201080f0f01050103021617040905100b03040609061e1406030d0c0b07051b030a0806040e06070c030e10030e16080703080307140703021f020901020a020603060a091b 76
    0xa40740807103d4036160341c070004e2154040c070540b41459800940240050800800c2c0c4540e90780191035000e4080b80f248421100c1c0c0d0061007040061403078070000c9000400114555002c46662a6200f070464a8944074171004040c90301007100ea15640e00300300c2080720759a13429448441c400b9040014400c080c60503480000c1d000031709003442600807403150102940c0064900c9101504048408042e9440d14000d45483c410414100a070400f040c0410301c8901000004120700030240da6141c005441d103106003c00d0718400840c1907001c1c1c101c2c50000c0c2d000391003003000704c0078030f80285445d481090070500410b40c030003a40d44d030080019844402001c03a0107400c114154000c0b82464400c40c016103001a440e0f1030382c5240c0001003804100202180e4101e20510030072004001e151040b50740d0320b003c0e16001e5035030030380140303da038280081031102c40c000e013007034401d448884030180c02501f0a41c4499007000105e910003807400744e00c0107510300042007031811440ba40d042d400b020040054002c0035401c0144c89 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 205930395 1250 205929145 205929151
    0xe15090603010b060a0c06060f0f03120509060d0b0301060b03150a05030c0109060f050706140a180804060f030f050106080105010809030715050603100c030204090608120405011b1e020108 82
    0x40c1c1e040640c4464940c8854085800042c5da916000301d29034807515108000d040694804c460340c0c1006940802c200e0360079920312b4201e91051000c0703c1036612041c8107581c18000c041c0025030080080c042c0f1015074140390001c81c81040d00400003d48070303031580c004c0341003a00165031400700d0b007034405449003031030908220f51000350100b02d00811000700103000003000b5010702e01450041101c03551021070070350701401c10317035945a40c030540902c140320018070200c8001c041118640e0390304e070500040c4404840e1500030100380e03941100f039091809013041015208110f03401240c20405680303214250880e4410700c101c41c042d06140d9154266945041c00050075000301401c10301c000d400c1006a44002610700c11613103503040384208040f4460fa01c850000b814908203400740309401d82840300070146540d140d0b00600c00d40310128404c000b00c86d15414469520406031103200302c0898208018469580211706202900e1645d1104c6511810703250345544505802c1e04186100e48006202c100840d81c2003005143c4c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 205931645 1250 205930395 205930399
    0x27050403050301080d050309030901110f060702030a03050c03041a100308040806060a05090c03060d0f051509070f06020c0603060a0b130e13050604170f0417190b1503070e150906 78
    0x810350030040750f643d4603031103068046414000d10166020000340304dc0580400e00c0d503140c050320000d24010030060744036407000c0601800a03150600140b43c400c0d01e00203407802960080300203003802942d81001040500094030480c2c10031103541c00000050480001000a070220001618031800d0410600400701d805030031581c032031300e8580c0802c083d1401d01e03001e4a600640484041c600354206003020f4030090b40346031002c0c0150003589803280e11081918902c60082e00e040b41142e5140c0e0307581760111480d032041d01940e40141c00ca88400c1e4403034034020000d10b8001c2c000034000c1121959482c0c4100155100126548001041290401504c0b04a82e02aa0b2003a202495840014290341c0c03403a8980400030002071100031082840b0340c8288551003078503516100d602d2600d03603c60300c941810a90140203041c14031075105020041d01c03140440f51100c41c15581c084400c1d021a01d840300352841204801c8281905845200c0c0000b50250650344403034002c50050800501c2641401d007070096808000302840c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 205932895 1250 205931645 205931647
    0x12041e0905040b0c0306013c0801120b060a090c0804030e0105030c0901081b0d0b0310090812090a0c06090e060901080d0c02030c04050103052406090127050403050301080d05 76
    0x1241c01d0151107613000854400b44c0b5501e0340c803000103880d2003030a25591442c81d403140104110714035081510001d0545041e950009422442008849554090003480c084408015806c800505000c0059420840003000c003690310f0b40700d020443c200d0b103400c1500400990000305202c14140c00100b00303080001300b880c0584c80c40c5400c00003c0d5140c03085a0550f03040110510001e0004484500440b4003120040b1000c0d6440b42902c4001029000c0302c05401c2c400e000c0d21800d04005030380d0740308039000f10ba40070302c0b049c0c01d20580c580d4407000d8040003400c0c071029000d8103200c400002c0b440082e01d0080c0009480d840d8003107040018025200030001e080038012100d0400503c090100040c0d070b825055072500e001c1038400290310200e41030465000c074080e005810b110010082050224440319003501f8558102c4014041700d500b1030344d050054030500d0308091260018800d0543c1d8910184040701441c2c0c200101104424006d011600c0807107040c1c0018070040010701c40c07008103001e02e07034081e00580740c21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 205934145 1250 205932895 205932901
    0x50306060a0c02010e090f060a0b0c0705010c0c03061e0b0f0a09020307142106030622020a03080d0e0f030913050a15080309040b0108070807080912041e0905 69
    0x85245807184900520900031464004011684142c0d103d0f42085405040c44040f42044440032020140560b401031142107554408190800e014081c0d1703039004400d00013404442e180100560360701850840940e111460014040041440340c0070f03030b2075488480c181e92030b000e2001000040031160345822092203a00d15007000ba60655626401c20250381075240016580d0320b48010079182204100c810350403200001c211a41c9240c06901d04011700d65004001200d1640c3d62403c058864800321407800328403520f01e01292183d6000400840d510784003515111119440c1e403a0744d1056040a100e00041907280c8100c90030140c01481080f00c0c80d40300d01c00540c101641c40340000c82842408085ca07000c01d0780c0790f00040c1c283da0f540e0400c104030060140207801c05519603850707a07220340c81041c419000d10305021503084a540706901c142c0c0704500c01d0380d44183d952a00780d0100c4400b40060100205072055060423070a02800b1002400103202c2c4501040d440b0142c4404c1c02c110840b0741c0e0154841368501410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 205935251 1106 205934145 205934149
    0x7050c1209030d05070804170a0f050f100c02070b030a0213060804060b0306010e0c03100e010b0706110405010507080d020c010f0f0f0b0f010c0609050313060f050306 73
    0xd0f034840090070401940c01d07100380b1070010030400301004100404e000449101001c0c1284138181d0746107031f1150303c0c1d82d017010038051410b56851300014140c040d0440e01304020301442211803001d110309003060f60082d40744e02052113140d00110002000418408c1d00b64100c80c2c10f07a01d450007412123251501002864400102c80c102c131242d14014030a034180c40c0029400d8100c5061100700b196554406604082980000d0801c02c080e21000b000842d22243d042c00c002e001e016000311543d294503590070030509807525841001c8040c030041000340800e0340c1c40b03021100071503040707104071b82d4420900c030f0442c00a1107650f8045905510300150030600c048c0e030789c05c030150180d01840240030b44250a0591000c44c0c84040071554480c2d50440886130550240c95411200350298134002a10403094403480d003141d01054904a512403041e400f840403981020342082c5540301071800f2421407a085d40 = true := by decide +kernel

theorem cover : BRFrame.Cov 205755395 205935251 := by
  have h0 := BRFrame.cov_init 205755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 205755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 205755395 ≤ n) (h2 : n < 205935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
