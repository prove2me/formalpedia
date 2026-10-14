-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:53:26.559337+00:00
-- url     : https://prove2.me/submissions/d42afc94-6c90-46cf-b3e8-3ca5040ed439

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 19604322 ≤ n < 19784179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 19605572 1250 19604322 19604327
    0x70c060f0b010e10140309030414030a05030304030c0807020913030f09030b130309050301020304080406080a060e0c03060f090a0b0109081504080a0c0515070f0305041101110c060403060c0807 84
    0x701c41c20080c040356041a0783c110600300140c0300300d685803481c0303401200b50104c002e001480c2d0380107588860300c1c0d5102150502c8000320307442c502c00c50f01200710000c10859140b0b40d501626800018070150070b02c100300301101c1c140801c0710100d0310510760040c4021402d107003503c4000d103420b800c034000340c000400c401b4514a00d0303402064800113490300049003404070390ba9105480b4030480d0016044040043c0894000b40300d032002d001031801188660400341c0c40b00d00b00701006100a60062140010b141003030000c0010300440d958098120704c05500c80d6990340e07581800708030348581c466019600080035104100140c14203a00c0154040c4099941c0700c100c9070354000300c0340d958410004003403400c1ca07104085800071342e02e00c0c01842800710b14108800c89000d980c8880382000f00345c1c90b51201c2c48001c4400c0040899000040d0114115582007c014a0425844038030300880100303055414420002442648403500704042415000c006001c150b80300d4492501d240500003509041010540304408030301d01070f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 19606822 1250 19605572 19605581
    0x3080c0a090b130e090309100f090303030902010e09040c0503060109090201021506030f0304030b01060210050106020a12090504020414090c25080904050f09070602030406121112070c060f 82
    0x355561020203a80c1030006240c0c5690007500b00c806000150500082c0d8900300708121442004528055501caa2000080c0054210301c1103010017000342d100072203902d840e0408890000c0d2601803400040c0c5080520058410100d50100d0340d40c0106500104020403110591140a58005800f82c6005036a05c030300d520195034454000902681101c074507c1901c0e0480302415500c070000074115042101c1b000325050443d40076800584180c0d0039100140502501000b40380d01103089076408200941c50014003d40b43c0c0d00c050310003008482d00d200ca80030354038450100c50000d054024030441d030319a079421895603904d45c2c1c0d0101501600280c0c000804402203041600d400d00244512074803184080d100c2905004034400d01116218010300005160b9110381c454a48515842480c612490130b101003124034000081c1c0c488021503204000c103001c4547d00c01c0e0904100d00110b400400c0c5001280b0072a00380303000303599482c7d500c2d02c0080b00300401d240c2e0220000182c94041c80781040046100114103060300c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 19608072 1250 19606822 19606837
    0x2090102070501030e010b0a0b0c070819060507110102030c040302040b0f090402091b03070c140601150f020705040207080319051b090105070c0602010501080f06040507090509070b03100303080c 85
    0x60300800410002c0d075000780c04c8408000c8140c0e0000591015035000600440c02541055040750808a000804c480041040c80040c1c100140207281442d180b4004c81e583e04017019000300440d844c0d201088003540141d090070780b809000c000964a903d8201c012405603003240c80147d01c07030f5040a025008508200c0581405000040c0a03008039984075000e104644d88042c203452649550500004891025840618040d21442e41d85009414036420700d0240c502e000900e60147e90000801003054110714002c001900340503052078060704814140582c2494000c1d0b02440e082800050030004029040c00118821451000800d24030b58400302d000048a8003102d11082c0000381c108003a503a90517020150100050516140380790150980d600c000c3c01e2030b194054400b6039100c0c001441032074000d1040710f0200341804001c0a10380781c2603c41c0f035a125114401c0c10322080da200e0201b0300c06542809214040c08424050660f00e04200c40010103007a094401940099800000f10314000100000c5600c5d2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 19609322 1250 19608072 19608077
    0xa020f0d1406240301050d2f10030b030d120902030307120305090703080414210d02010b030d0c020405040203031204030518010302070506060112020d0903050c06060105040509070c1a15040c0201020901 88
    0x42da070806d01030250700c80e2111300a8601c860b070074103100310754440b110843c0b0b04402014801d903200c401c54810f01204a8003e0075a5062600300a03000d10640c90010f1715203c9d6040790318001f121851900e1020707004005105001c1d415000000f00b103414410442500002c8030302c10340d4200031070380e2103c0700745032680d20070f02004004040400c400c02444c042d0f54280300840d034009001040005c1c001200300c44070040510054200e40000b0221251141c0a20070180c898030300f9800381c411400b18910040811a00d004002d1041d0303a10004501991410416a003014604040c088664100744c20050899009208140c11708441510320f001c00e5440b0740280c9100f070b54000014801500c818006541000d445402c1c010b140f5400c0c0b21064480039540241041c0310300135283c031586c1e40a100b1096080100080907039040c01802c010030003c580b20030b107c0c641e000d69685800510b15030300c3e01e02707402c2410f40600c01c0b00805a180c1e0500c00103880d10b120703030600340300200c401700300ea60040e5405034240e0040030f40003800f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 19610572 1250 19609322 19609327
    0x5060904060e010605090a090203010615052b0c020616021f05070c02060d0e07090b0f06070503070c060e01020d110304060e010c0b0103060c090b040302090a020f0d140624 75
    0x100c1c5074110844403000c0301c0c00810301c00c0d145c101007194014101e4800c8445a01c038489030095050a2145101130805403880c01c0407584035101c050214858249504440f692104a0707140f81100c282c074050042c441010300384245c040c002f4000b07694000948a181c034440000065080750740c00010f40741c03000143c0803494411520061000c00003808010551402d0018405800380143e0307544006041424000ca0001507407640a90028034044a54200b04c1c0800c5c0351000201e46942c0322555640f1541d002c4134502e965800c039190a90440c01002001031060034445400720b02250405014241100c0030f0382111402011031400f191410507644402d5083d410401043c08180d03c204200c1b01032280605004444029559541e01d00c0030b02644142c42d040d40d907441e0150310907071060740000103104240350359040c941550001042d4905c0901150000ca6000031441d9103c0103003000c1d40c2024005d41e60400c0486580012009110821124a8410314490f10501d11882c920b4803000780764008000e280d030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 19611822 1250 19610572 19610581
    0x509090127030e031608010b03061905060102030d09060c0305060301052a040807170d0507052805011e0b0307030308040b1b0406050d0c05030103050c041505040c0302030415050609 79
    0xd503000050000d804204012044500c140c90402600e41c98042a01c1007584036858404494212340e000c8030700a11035040341c02071080d0380001c6a0040d1855401010004030ba88400b00182d103188601c85c2c60151890400e0400820b00c8903d44c002c11071124661400d110603684c8e001094200c840484081002c046008415481d60001c11112407881400500382c1e854281c841001520f412640d1344031f000807500d4107901c001e002000344290703803001c480c1d401e2050070b0000d00e550f205e444d450f0710010b60400380b043e00442a0640c03202ca0860002c1a04840200041c0c984040c000d140d041049000e1682e050524074080c46a042c0018220b08413905a80d4807120f03500c6035130740c800c4020b10240c054040e8901c2581154940602480104010019501e420703aa4220048042081d2018004c04d282400010700041002c92004603c5540e00b01c02114009402c2e0184082c0248441c081e4100542241c0790200704a410b941550040d400b56000b400c00000d0001c1045400094603011141c042c0c1055441d030105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 19613072 1250 19611822 19611881
    0x5010e0f0a0f11070f0c08150718030606030f060c051603050903010b0a0e01060e010203030705030105060d0617240915040f12121a10050a0306080a0c05090901 70
    0x1480d8502c15100c001c2030516070503a48030078036001030702d05954200c2c040603600f040103041c4464600408407d0064103040320341c41d05615050000070105400c1c40020f6486000012141d24510083e590006013000030f280c43e070402d1880d05070203000403911245000312001c8558020710586280f80a0100c1421000103103550131521b5030418000303146c1540d03c6100e104800c1d6110120300c005042240c00317600941d85440c00c014408440c505003281950001c0051182c07550348541103074103440c2d040c0c45859442e000d840c00900208410380c040e88250141342220442c0c15004580c88044528414619014404c030302212101c21409849440c001d61243c0040b45000f981e01c051254400d000d680400740304809a2200d01d21481c10240e0540003030490b1005032241010b40c0700301d9041c50322007503030554854070903808920300164070610307002480000702e0904012482030300028050280307042500c070139207402d290204000b202401480d12849080340046d041c203c0511512401c0d40c0803441c80f1780549900e5011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 19614322 1250 19613072 19613081
    0x606020c0904170705030d0501030b0402100e060711060d090507060f1701030204110c011b0807030507090311120f10060b07080306010311090607030e010906020a030e06030a0612120305010e0f0a 85
    0x1c9172035010a000500c42c0c5441442124020350207100d0811b079a16040c410061800c00d802228814010880d00380041c584038041a0b03064185d004410701c030aa00c401e400281140103000c1c003a508c03d418940c003001000400704081c411070307009807148404540280801d4807498582d07450051424074450040003d440c107508245c0c1400c80e5428070307078900b880c004600350940d000c2285600d030030500700c0300600d1020391101e038642d8400d19a25041106050034100100a40d2451201074000440c2c10310001d4a42d40f002c800c102242080021100c2125000c10b4091b200c4114a40c80c40520740f6014000480181d03038003c441d0300690240b503042c51a500d800042d0f000301022000003840080a120340111500d800300200145406500c40e80380307a9680100042150340c84d07402100c04c43d00b090380f40c00c0000b0380000c02d64103050f10481e062626591a814041c005045036881035113959072503a92441400000d8101e0002c4070642c1c0c2d01401140e807204540e2001100c180c5600c01d00d2843c80700000c0061049030702 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 19615572 1250 19614322 19614337
    0x8030d0c050405061303020a09140f07140d0608120c031b070e040609060f06060203070b0603030d050403080f070f0801060507020111030a03021308060705070b0406110d0606020c090417 81
    0x502604094451020841603001505d140b02041d41120041c801d500d44080410010014038000740404c004100038180041d0010301040684080c450200712028024056076031768002c14011152601d10040c01400504200e00c90807001d030080040d12640b10600000700d81000062400451600c440d0050072109501151004103080c00380300008140345030000c107818000c0307000d440082161040e41c2884400c40b0018122200c80c0c07413920034100f0040b82c000c0240c0e00b506400101e64080765403400301090861007640c00d800d88180c9404104400c058101281a016045d0080000421ba03a1050196001e0511444200110303a0325030041001c0b511600c02002c4803803041c036204883c1080d000300c592440c0c0000c0603c03c0840e0f0007084c0e41c90700f25011810303440149403180040400e8189010081c04ca88281e03107010703054070200c000050911240e50010703d00c2d03c7d60351b400b40c2d039a07a0101e03140e2030040032540180350050046514481c640d24211a5860149811000c020b40c030a01c503000684040c0c4c2700da00e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 19616822 1250 19615572 19615577
    0x90b0f0d050c0d0308060102010c090302090c090d0501020307080403020d0306140d1a070203041806140405181504030801050d1104020c01060f0b070c06180e0a0603080307020c040501080708030d0c 86
    0x458684190b250851a03c03219842030711104091300301000060b00b52040090241c2c2000510141000940d48019405410010210345103a4484000001c203191000b40791000d8515800002449081a3701c03120252040f0300030b509440c50036104400c2281550941d11503121100041e094001031403410030441081c0d24070802c880801d4030104844c0b07010a8100301c55060240c0c1000c101000509040b250f148000c5204910070800582041d6a10f20f00c270180c10320350750040c0d58070710005500c1203640c0401c01c0e500b1003840c122060000c54240404003554121800c4001605d52400042c280c285202d828414545c0314403001c004410102c24000290007102d030744202503403684030000d1400c0c415201c079005468840c20752903541e83e0500306a01ca09109500440030410403481203170700c106454860400b52480819200001d4844c540c820001d00742c02d40016103034840001c103128503075400040070108032740d00390f6050205070b81e2000c425883d101a4440e0652a81041019012900d02988818085002e03070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 19618072 1250 19616822 19616833
    0x4020705010c021c020a0510020903070503060f1b0306010507030804050c0d0320030a200106090f02030402030607030b010c06090c030b0708010806010b030606071e0204020d02090109090b0f0d05 85
    0x1034546034207481e00780c004640543c010482014070901e10303140101a03100a03000400d0810295030b44c2540e940b401d0342c0145c502940c0800c1c1814140e400303001f205d0040c40c00034225882800c290510081c20f60b42a2741900d20340c06491241c40c010b031010010b881c404c0300141c413002d040c0802c6403001c0d20710b404024000c407043d0180410000303096664191100300d06010750b42d0003c6904040440c20007080030740c02c1c0c1c60f03802e03031080c400c50290740e030711100031801c20b18051840f6014400e06040300c2d01404070b98201181803070501d00c1c0f80381e400e519075001c2d510840c0220212200354407824819030403502c2900500307000400c0c801805000c5943c41e00800035251040d8000300d5240d0b940e44680000301c600b61005000110080c2c01004040710411005001d030800c110701d03d00d50300b0080c00003944c80c8190340004112103082a03850618441030301030401c2c0c0a030007500940d0b8420b841000c1d07400031760024541d1404140710807004a0000c00511841204540c090044000006410104901c0da80c00c130000710303030030300c40c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 19619322 1250 19618072 19618087
    0x4020910081902090901020301050a0501110f03030a0c020d09150309080c030301031a01061b030309050313030303020d0608010203010f12020a090207060504120e090c0c011508030301060306050a030b0a0203060402 93
    0x4001c050b0607210140c80381416000b052040050406003e001e6003510303070042c0018082070ba1140000320850308242040301c20400003810660410b09510b94000032404044200980460190071440c0c0e166019400da4149000002081d24101054013807140c0b20560f280410200301d020303030300819200c0d0103041043d0074134408400d400c3c91580260012a501e8482d41295020404a000807a02601c003904111000d4a00301c40c0c1030389002c00c80390001d000c1548030550300c82840818011100c0381c1c4000305010340b80e1030b00c03410090041e511100d10311160501c1d06070005200302c018420360b41601c0c1c5c29504a03414515106e41c0d031250081070403003664080d80e425000074044840c1d01c001c1842c42d218082c00b140750b10741400c20600d00d007116040c50090000d01c0742660065513034076120035417118464030031300d4030b40502003d65401010103403990150644004e102180c0e101000000e981202c0f003d40d002e010b030340e03207800a02c0490040d0740300050400728240046410700c40e00da0040c2d40e021001a000600b000e25 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 19620572 1250 19619322 19619339
    0x311070803010f06080912090118030203011d060c0906040311040e07030c031b05010806130b06040f0305061503030714030f0f0a080105040b060703031e02040807090501090603030804020910 83
    0x42a4008040c45401030400c02c070b102d81105c04280e00c082e420001e80054240c205210b0040d102c1c1c503090720304101c82c01201041c8010300074070041c05543c019008100502d125001c1c21b0b21540c420010755003501c20400005c6020001008607450018050002d90034203146954082e280340e10002407541c4541c90381d489041c800401c101140c003c500a991603400c1c11b20350b060410341d814aa0718000c4496a00341028030569800040c01900400c0a40310000c0080308a440807004100c8915120781c4001c0004000031450051203c00007900e00400079240341e61141c440c01d01c251440e40036202c0e010307002800140c0c0855419942c9421266900040d00d241000c0602103a4076a80010b0483c50000000726013078021a41c484015030240038182e404020f4091035900044043c0600c400c01410191544100d2488082c000700090306204110415901d56440300c1c1c034075481d03507100e00606c01014600000041ea1104600408044a030503440780001074a99400717101031900010078604403c0d0a20600250850 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 19621822 1250 19620572 19620577
    0xc010203070c030e030a0b01060c110a120201080a05101203051612110d0e0d02040204030210030c0219080a03020306010203161209060e0603060f120604110a0519050103110708 77
    0x1e00b5941c0107104038551030040d14244d03e03100320314002e6000900c017074009131001480606403955410a074859018a02d00403036150136a0107010342040002c01d0002c1c0e00e5039010414003a8620036252803585c0d0f6180d1030600308a50040b02e0005001a0307002040000020301030359048458060301c1c00c43d24040e01c810520804a44001048604c041055005080c1130740c0700a03402e5001d0841006400351520310b48008143c0104c55104510403442c4010400465846034100c1e8011640500100303c070404880c070140041c40d18281d202d000d4002c030031512004401d1011002d050a40c480003c89c14054446d00c120020f41000b04518150300c02044000e0300f858100d0b01c5103447c58032607a2442c0c1180005000285484c40b50317400707881400320780c030340107440c56607241c0c156540090280c0e40c012100780c00c1d01c0013360841d220500300117a4014201030006100031306540d070301100c0003680c60b0542c59a64106108030010300780c4541020800703411040c000c0358800d4010300200503500340d842d07050140b29112003d035036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 19623072 1250 19621822 19621831
    0x1415190903240e010b090a0c12050c030108010c0203120703020a030605030f010606090b0a05040b0306040b12010c02060106050705030909180706090905130507030f03030f020a031a030d021209060c010203 89
    0x1040310b034001840309803180c042d04022518140003400001280008200802009420900e825845001a402c1c2031b03c00e0b61034041c4820f0700d40042c001c0703007400700c2e04d16540d900c2800f80100070b509041c0350181c400d00000441e0348184422004001603616100d00b18029044030f054107040607118a80042e85035010450031001d10010000020001d00d4003201411004580c0d0002c1c86142040c00850f42d0f0a03080003d9404580302c00a40d176540e5038903200042c004102042d105540100d0300f084290070310300150300400c100b06541d000c540c880d03602e42c0400c0d143c2d0700900c04010402e5000b0031000703085003400c15066810047c03000c6842017400c1d00c8000300d03040401581040000481201c01003242c0305403030061a030024169403005244415907100c1c0c50301d841c03180c00094668402910b0f00010144a5400b007107a10415650071501c41d004c00f0702c014081c101c184101451800621070140d83d40c9000b00c0c030002c2e0802160003c0c003d0035003d0050080c5078110301103d540c4035200340288840c2e1030083c0000d5105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 19624322 1250 19623072 19623113
    0x209010b0c010b010f020309011202120108070e0702030f030103020d0303110a0c02010e0906032e060906030302010b090906180a0c0608091603080a0c080702040908041415190903 78
    0x120070301a4421800c54a14148480c100030095202442e001c1c0c0220450b044640c0c2803a01c8040802075540e803502030f201d180c0c0840c0041c844440001001c60380414048140c0b0072a0880300c3d9540c071801c02c00c0303940f4000c0c2c05407500d89241c00c00c01040103280030b00c246003080d482800c001ca56548001b20004154001200100c00b044040d0a00c00031503070302400e440008501202d103c642c2e424000080380c1d41da81d502f4841d041c8030360b0a450841c0d00038417044c80861440a001d80c20301040341c8950046018000034401240558200003254000c0e02e00788209611415250b0002c1c04684d80d90450f20348000088440c0303141d2402406c64890104036018400000350489440300307000b504000d41c0b030600e409506480441c03848460f00007440004c1411046070404a041e25203210000020b013040c5010384122400294030924103807400f0100302414020f4002c82e0701c01c111660032517240c0d0b0b0510013440d0440ca01c04407000001c00070825000040c4040e01c42880b4903140030a0015281e55910030b030801e01300000b912 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 19625572 1250 19624322 19624327
    0x4030806031203010e071116080304091a0f090606040f0b040602060705070c06030506012001060801150602031c02040e15040c09030308070807120204060c0507050d0b0118090209010b 80
    0x803181410001858004035007407585181d9807604542d007003508400751100040040721f50706120900010400144007040644607940705650310302915a1700d43c031600c01e90200c541400310302d05031851201a04a200038015140c105101612410046001b00082ca600da1141c024840483c0c0b03681c2c0c500c01c082c090301284018a070ba403810500068902040100311908001082002070000382905120004485040c240880c0c0390712041c0040c2c642040310185060b03400c0303c1700045100b801c81500039030201c0b0f4000c0f00030840c0400e000c2c40c099a0610b54014840560310410214840c510500318030145c80d256100018100350300c8550001e110b190590700340707801455210084080f4641441002011240350401d038841c00d146a9015161000c02413a800501c44000c0004960f03d0044081260840141d1000c542d030740d4660b2400b406080100e401036801740300c1e0a0010803a81454a21644425000426143c03540c2c41d000c140f100d80001402005003850b00c0303600b40c0f00113031642c0004502801c0411051034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 19626822 1250 19625572 19625581
    0x30504061503080d060b0307120e01020912010c0315081b03010608030c070f090207020a090e120307020d0809010501080613030201090c0e06040b040903090b0a020109170403050d050406120209030c09040308 90
    0x30140c940d5900901b000903400c1003030000058100c1c1c8403000140155201240b840f003400c3c4564024051800119003014003540c04014503c0306600c401d43d02d00054030100705680890100c1130300241d141c050b4008035801170251005290201100340c054110080000c07807043e8036144100d00f103400050440406030700100782031000050610f1401d0283c518414114245581900080c042817014401c04030f0ba40d556182100e5950401c1c001d0b2101584800215543c81c02c0640e0003c0d0340740c070b02d03c210800080604002c112410f6040c02100e0403503880c3c600400442d222944e4599507501c0d1420124195941d6055420010b04400400c90040184054105092038048180000e480382810054400e0385850b4409002a030840c0f00401520969120f00307460301c4d02102c1c2a401822200c03000741042080c04182c02c6090943c000501c1600d1144040e1418100d40f404140d94901440c0544804501044c060015400f51039026201901c4000c0845180c0408580030494074101900e0550000d0a544c0401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 19628072 1250 19626822 19626847
    0x207030803181c020102030f070e0102031b1504080c0c01050c100e1005010906090c0309170a0c060603060207060b0303040e0c0f0d020a080402040e0307020f090a0603020604060206040b0f010503030a03050406150308 94
    0x8c50340000142402c04120b548100000d40360700c1800d00c007280e20f5090764040c060285080100700d44222070a903d00b0306a0810341004004ea801c003805001c180e124140e80186c69501c0b460650b10480c0308071005111240642940401409d40301800a0440c4196840b0032890b0003d0300a480c028410742d20000741c2c903401d0810701d40940ba4040b980009041c1802c01020005441d07502110b400c0560741c5000381c03a00340314442114000c20140c0c0103031030142008c80c0841440305690040c501da40c401d09003000304c0a140020f15031203009512034145911008400140ca0810303d000074501c4941903c14a89441142e00e043e42c1203070040102d03e00000c460004000031820a8401c03070510407c003100560034500c1907400501c02c0110a50a54042c0302040301041c00070282c3e800c8000a544e000b450300d40c4075600c5c1c1000955490040380c1c2540c1040c103e401080b2001100100203058800207400380d441c0501c900340c203401400300a401110420759900c0c900c04c00314240281c0b58080d52150310013658400308001c15 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 19629322 1250 19628072 19628101
    0x204050c03070c11011b030801050405100302030601030b04170315010e150405060c0a050d020d03060b03040c170a061a01080c0903030a1809020706020403060c0207030803181c02010203 81
    0x92200c0c058040090145040d0400282d51050ba800810104812068401210503121030701c0008401c0d1515200e4800301900580024140c071400c5e03500304510350b1904c0c103002c244e06036888040d40580240c1e00610110b0303484c98003a6406409524401242c1040000c000e00b5075008640e40c82044030200d02e0440c032580d1100b030b50404c0303580464a02c2c02c80c2c0e400d2510381043d480740344a130a210706e80000391004040d605204030071045410200342c2d404c2409131403029403104c0c0c0e4405000b001030315010300458640b0000c01902d010b1500420340c03280d214180344034043d030203003203003014007207845001201e400080d002e010b0084280740d4800e00441121540340050b0440c540a4400003c943c0140700a15542e20b000066621f040c2961500c0e1040c0441541000c088017159000f100c90709000243c2c3d0400e2200c15001003040720320910040180c9648103100302d848200070300000f003082c03900f0008a1540780104041c5054070300c002d4203407041d018042c180d1000c440b00d070803c020050303500441003040d46982d0315407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 19630572 1250 19629322 19629331
    0x120506010219030909090503030609070c0308060103020714010606020304081e1b0d0501020a0206010f09140604020903030c0109140f210315030d0c0c0803180f0105160b04020405 78
    0x140014205200081d468a003010310b078240c1c005401d00c051061500c00ca01c550014a516001080a00344c2800c01e84d840b64000c40b40140200c10310000b180340e840c41034490440344c540641d910202c035140e0000441c043c0d44800002d94548001c1f9030b1140480e00207200d20350040c800c035001140d480d80340404040c01d01e01000390122001c3ea0320380b03000340326510104000c440b80300e106428041c00036086001412403410048003605540c808281042d016400040c818180c41500c0703c0000c0c01551142000241d8030468550f0082000d000045813085c1003d8015007580b5500a09807424410070400303281c01c480c80d80d0070a0ba08140200c5101c01100c0b0213000b4449244140000f07403c0741d403101c0e806403107016400c8142ca44a1070001001902c40348850741c1c800c208107402020303175000301a920700082c4a80342e07096040d9014180c40b100020062000411104000c0c4074011140496501034100b180c021001c200c8541405010444881c81c1c522903001040140d00c10000951141014010b001c111100200b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 19631822 1250 19630572 19630607
    0x106050406050604140d0b0703060501090f080d030c05043606030c060806010504030624060801050f0f0406031e05010e0105040f020f0a051c0611040f0e040501020403020d0b07 77
    0x81c0180620707120442103400361040b1968580c000b105650105182640b0700c070015140e20402c2c4280b04804e90316030420001c54800740d03180440a43c0b1401004075403041c078400e595441c1e00c07808540c60701500035004240300c40024140982055a1812100c0707041e00f002140768481c1c4001c10300c00c1c25003c04039003d505010031034042004036a0550f991368072103130007501501c0c09000804001a40603072081c001c5501a560054082c040035001d28a510b00c0010100618509941c602c080811a50f11460074141241c000078941e640196048080c00340c1c4250702004960400d89600010000c01d41030001100030603600c05940610800c2130610900311601481e0070030469051000384804150b030080b88010098040380c405841840e001d00140300c81440303510450f08207a80418410a40701554000258280a24030a00400414528800b158880c40c042d6031546050030030284125415000410360241c4070310001860b0079103d40001e0311003440304038121000118003080091055000303182490015481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 19633072 1250 19631822 19631831
    0xf010b01020105090d090b0f1c020304140a02031f060806011212020601060906030f1d1605030109020d080708040902041203140313112103090906090106090603021602060c0a0501060504 81
    0x10000100400c6e1b5505c603d416400004c0341019613803084604031881907203260403846441560440c4140607400468082e20420b4426403001e81c0020f0101c0c400340520b6006010f000034000340400d240301c00c5800706102541030354418020815540812045000c1d22100c60000303804c40c072900e00405203800902403007045401000040000e2900500c0d85000e0342c0c014107001c68207080ca400100010410340481722201c165041c290410900c020840c111001c0e508007102c04e546031030f4010726080e940c490100030f4014142e4620000402d1b100400380c01d10314804c01141d458640d80364000c0d070a0343c005402820580010b015158205034005891742914400000420f00314504103032540c0508002c110082e04c1c0203c007008000c141e40d1952102a1000880800d81c0100c50074804807070758940008800601074040c840100b401454103030b002d0303412a44983c0c1c60020031818400118081c0d006508600c1d062145400c820f00180d4680025000254200740200080769440c00d200f4251541d40e0711140c015440e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 19634322 1250 19633072 19633093
    0x906100f03080d0c030912120608010207020117040201020102070f050309090a06060804030c0201050d060905090d0207030206031f0e040302060405012004121703010f090b010203130608040f050f010b0102010509 92
    0x700706552903030001c103800084c0c04003400e000390080c10b00c018001f0030f1000c1000c034a5403802d401080d05080034200031401c02c0580e864100b42ca01301d21501c40084e005c100f01c0c2520180101c030f050302d0310741c0c024410310016003000c080d6601e41c0c6401d59080741c00c0750190000f095042140c240350300d81d1a48100542ca052126a01d0000094540c0c3d40140c000740c1002103410f0150b0139640180221501030b607103103d08000d4155a8184413000746025070f2040a14000c12500c920a14800151030080d2500100414070750344410802005c4403210001e542c0d150309801c440001c40384111102c8600c01c5000740c0182c2018985842d22034211140b02007020341d641c1d4540301144c00324612005039815551a490105000d500307500348440702c40f020f801194a030300300003c00880c13543d81070105801201c07a00c0d4018080030740c8200040e81c0360700400d80c440404980c08072003001094401c004498005001e400b004500500c242c580600f8650240c074500856074458032884880d5909110303040d0310110070742c040d0210302e09 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 19635572 1250 19634322 19634333
    0x1050f040b15180a06030803151203070b07110109080a17090607020c01050c010209030a140d0807120203040206090d0524090d051c021204030e1915170906100f03 71
    0x900412204141c900f4400500e007074032140c0c030410165802c62903a075224075040c903414411150206004d4043c41c0048008140700d440041a01d0060b130340540c1c0301c050f50b6140c1100321085010908445103035901c54441e00c0200f86604000d2102d11410b940c0c0700000f86040103809000c05018140c00c106a11603c1041401c0368082550050310703d0074a040340e6552010b040c01c0380a4081c4558565060140010290404c2089010703c110078003c0c0e8251103109031640c03815659908125074070004074181120100c3e8007049a4000c6920901c000c10b0303207081c0300c00d40d000305420b40c240d098129629440581c0c0c24005001402c09441c140b150100740c5d55140c945420655120410440194203110340810444120107064a0820b00c20004203011900c1e143c0300188040351640c00e40d802e0303000c203112040540300b40c2481d02000407505424080c07601000d1078030500c82c04034441100703040200049844169503411200c49203d0250130140c0090215003800d054021041501d68003805041030104410070000300c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 19636822 1250 19635572 19635589
    0x1a01080f06070f022a0406060503070504060513080607031401121707141006030b01060f020c010f021e0102031008060f0a0c020a0c0b0c060601090807050f0a050301050f040b15 77
    0x720702e85040c0030801c1c582c1d0816407501c51282c4544c00341000796224525000c0814980b5095988211010711025544170310540c2e03d8070040d103100c000168104414002d40340108000d020300d02c5409451041d5655412a590a002d003c2c1d5603080000d032134152001608100100140c05010100f40e00b411510b52170740c079980c059010000c0c000401c100420100144240740181c001508080b000703441b607080c1e0084001d0f0007446140000c4030180c00c80300011410b98400d41440791103201c150001c00d162010103005440b0741d8081031700b0100310700c1a085141c4080009088142d2860320340400503071241413206136001500300503000000705074484020001200c0d0f0800f8800d42008031b00e400010901544201241028484c00c000317050308250100000702c0080b6000180081102c090a503100344e22048011183c818080c810007040d0b501020061002d03242140d040364603400005c1c0000ea4550ba103a000c2400d4410445584001c290120304100034013054128880d4810003000620810b004030360000368082 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 19638072 1250 19636822 19636831
    0x9030c0114070909050a0e0304030302100c0201150605030a0b04020406170c07020117190504120e0a0e01090b0301020d0c0801030506010605130e040201030b0909010b18100909050313031a01080f06 86
    0x20394481d17002c40c0048200703034000004615444280c81c2e40301c0e00e03418065500c040001a0304081403510b03c80c41304151061041030100b202e00300c1c103c2c2c40341d443d2901c01c4605030005400252680c0e0b59840819035a9070300e00c010300040c6001c0d00d603103044601e00801e01e804094020200710390200e0820000006030780c0440111140142d407646403101d5100c0c04e561240003107400758240a080e14020500c018042035441600d0300c9240c1c1d5807124007540198083c41a4000da51003525442e40000d00144404083c1c0c2c0c1040182001c041c0005007000a14101c40050301c000a680c500030503401e2006209000081c00307114054003640c01d0a0b0319000b00c10201041543e210702c980c1d054060501c0c042030031688280c110185481c0c005002028a003001e4282070700804407040c0c1c0a1140d0078200380891740f020641403c511451307092000c0040320707141c500400003a004215040f100c5000400c814022584803039130390b0028501902001d50400008107a10300440c1c010b03081030015512440e440100c41c1c80c00900d00c0c0c3d02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 19639322 1250 19638072 19638089
    0x1020d0306260304080a08090f03010c1218020613090b01050c0304030209130f060c02061501050301050d0807080a030b040f11030402011d0409211106070507020102070b0309030c01140709 82
    0x14802c2c002d040e00d0441c02150000307000c50064101c2d40080c420502e003d498500b5044800320b41580380c0c00101422569034005000108242411140c0b603450198000118000d00e4106007944481e1030380001c0705548000d640312060900c0c450f041c054100c003031088191940003130070410703e044060a02143c0c3c0e0f001d075100c003d2141c41c0080026009943c4c031040148215800207540c00380480c2440d0001c00341041829030b0005105103c0007a01c202602005000d6211068550070710b1a401c01d4103100440c4031805064527a0f00041004c0c40016003414001c0855141c05d560026542e40d5403002c00094a038034819003401c043c10100030a070722501d940104d94000f642420405041007801e0080c214040c00d005509a01618096202042c001810104114070700d80082c200868140b80d01c040e684001e600815a519038411000181454050310050603210f005004840400d50b407880d1340e00f01d944c0300b02c0da810029040440d070900c041d0424011070800c42002030100c0c3c0341d4940070200912002092280000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 19640572 1250 19639322 19639379
    0xf08070503040b0301060e03060603011509050406020c06071e0507022b050706050403030e0402030412080c120103030314060109031104020d0207050607020304050a140f2206060206010501020d0306 86
    0x42140c01c004541c0204540c508040d2a5a0740725009019850380d11a6580a4007900300094480d10b4103104581a0707001c5000800027950814040741c0061100402c2101c2442c1d0030090000d400d40100000f52003141140e4070011100c4540c51a1041101d0380040c0c0e0051000a01600c801641c2d40d450701202d1070341c80c1070041c01020b815100da1180010000000c5c206014034007002c031303086c1d0f8040c1c0200107481c040d856000442c8980390500081f44400c403805480c202030030302e0b5080300501c544885900b0000c44c0305403500f0510065203503111003100703034002c402003a5500e500102240101c006a5407160b07003400c200202a00d03607140e40e5007030820b84400520841e40022104c50604056040e202030b95000300889060349030868010b035483c0d100c0d00540e445200580c600107412000f140c100c40c03d900d0b000d41034034503100798541841481140010b098a0045100d6862800803403144141760041546c1e03801071960354074100019040000410110040608040040c002000041c107002c8100400101c8000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 19641822 1250 19640572 19640587
    0xd090302010e0d1a0703020309010606020307021c0f150501050a1401092603030405060708090a030507061a13060302010f0c030e06090111030d0c020706030903020d0e03030405040e030705060901090f08 88
    0x111107094040301d8505203510441400485c41d4543c0c0503500c540f10400082141d07a0300e400302a030b66030250100095000106240b050001c40400041d00c0781d041c481c00c03405240c00704955421b0000e8032021600c200380d980e41c02c0108410300e003da00100c01400c80420141500d6880400202038035010301801d034141030204460410f00320010242c0031019001001c2c5c036280c0c2024540184c540000f65007110018076818046004c4400c0450141800c40c1e058031036504e031045a42d10350029044040f0f42c200c0001148004203616100c000e00d01c4164401d1000000b041404c43c400905055a04c40790201081000c10300100001e0304014404105001200c003d0740b68860080101c1d0b82e0901b25400b90f1541c00081346949030180c0a40019010058036000d54800030348a82084048070f100840c0900141e00c440d40605004d4020105407031100009400c3e0f03072070941c0f118003003416103408150200c0c1d03d510004180341801341c140076540d0071110b03007802804071035502d40790800c1d9500c0780d1702c028044400009866 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 19643072 1250 19641822 19641833
    0xb01050c010f0504110a0f0e06010c020406030b24030309060d0908040303090303020d170c0306030709050c130f0b030c0d02270918060c0f0d09060e0d090302010e0d 72
    0x540140c4098002880309000d80000e4030003815003910105c2d1213008540c8011494504074004100340d42052a0502d0140e00d02907510721502405410b55051243c0d40200c1e10142c5c68a014100c003640c000d0140d240c0908180900c0c403c86031100c04000c060380383c20310308480309a40110494102c070400b110071a86500345544401e00a00d039580004000300400100041010b40180940f0200c9001e60203603100b5aa40300e40c10f1380d245100501080c0c1100ba008009181840460003444c2c03c03d90240494000c41c1e11030070218125101074a000605600105d214407003070f42c0404014010b0881c02005003891460704c580704585020140c1000000280444c580000061907815596210110261014040d420215505101d030100200c0d900910004002564007402e581350041004d290381c00406da0383e03803070a09100080e00080180c003100231003001004186062745c019101d42500841d400035400a0854106142600c1198640c0910041050400140c1c1e0440a8003108040640b41c0b04004285450103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 19644322 1250 19643072 19643077
    0x801150c031d06040521070b03040b011214160906140307030b330405090c030a0318090f0c020708070b0a0c060b0d060504020a080a2402090603011202031902010c060b0105 75
    0xc3d4000c4100710712042004066000f0b44000e11b20141500c01042e191038456035588003c440141100d208900104039404481840c00c0000b8012030407803050038500700016041207074042864418541d00041400b045805200c1e4100403e003501c6040310150001c4042600c4603100d10000e020031581c1d00c0000c1d1000c00069442007010a44d41461421116244900c1c00c01c1f03d10f43d81d1140101d1030500001c100b408005440c800e100c80003030080c404080f82d42c2d0101c80d00c29444c501c0105044682500181d01d4a103401041800c4407401c03c00301d960000000d0003881c0c040340d41d10980c4942c4c84001d04000c845818000ca411590703603490010b040114904114000d00740483c03041d030304200a880c14205001c1c00390300c028021482220444119a55030b0469070751452011005401d00100890803058104a00b06101c142000504003504000c01d080c005a590b4009a02c00c2540c451041182d50843c41c00f40206070030401032a444100c00303e55034000030000d0403c888010201035858110b55240d0f07010300c09 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 19645572 1250 19644322 19644329
    0x1a0306010c050d0809010f050c07110f0307030b0609061008010909020a050907030b040e0303160c05010e010e0a050607050a1409010201060f090f050105041b050d0b060a0801150c031d0604 82
    0x440f000988007420091040314100c4005a4130b520b041171103c4ca0f0700320360203aa4000d250280c034403414040300d41c03144a400304250400c01c0d4010140e00088555403014414000194000c84500b9038500d404010b2140512000b00724038401d100b00555030a002c2d41058a06040d215446000a03a00c017407480410051030380c2d5003100e9071081185003001522945038000c0e8080603c25201400249088800079a407404156856079501220b510f544000b94481c0c00380c80601030196001003170b514444c4a1072401c46000481008040d081005a8400d00008000e11608a0b2051420510704020307002c0c01071128071494503048503004001104400c980c401d41080c0080c01c0005002101c45a030369113040c00a041c1594018119802d2500020b01e500c0c1034810300c1c440704803c580b032402c2c2158190088800343d001140070384e00300c0d66455289640d903c80202a1405822a40303400c040ba50610758450384181c151400c01c81082824a1500000303a0f002200c0140304070041070f6041c0c030012020006682d03014580 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 19646822 1250 19645572 19645583
    0x403050f0706020409180803060d060204030c03111206100e090f1b0114090604060305130b070503070e03010e0a020907020f010f1b0206011d040311010207060501031101091a0306010c 80
    0x10410240705a0380c2c004c204442d0b03d080e040140074084241100c554143c1800640100011710015000d41801c3e018030141d1841602c006140603180d5035503404a201942080d00d0030204420507140d05c0c10700056520120755104001c0005180c030403000d8280c0e403014001e6541e1f254900c00418a0080700300070f400000360155040d2041200c09400b9001510814414540003d130441e451520401000044504000018102c0351505081080543c041d10014094a030001c41c613014400100f000e45c1303500c03030180000f50341e215681e0400000050588240607480c0b8820b901d04094007000d080c000910aa40c50342c141c8a031a4240d441041c04c0e400c00412000d141299403c003564004440700760f5200704070340701c2d03c0728170541036003581c21049035a14424058110a8180c000b5040d20600120818070b40c410721078030f007085807040c00304501c50130b903000300340b0454030191244018410083d0b405081e807520302080c07030316000c00c9140c00b504e000c0705082015810000304001021440c140d220382d00740d00b907642d0080f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 19648072 1250 19646822 19646827
    0x30c020603090d180b030f0405070e0c040608010b03010803030403080402060d06060203070203010501151b1e14060106050a050901111213140316030303020c2505030c0607020a06080403050f 83
    0x7546515100c0c1c80142030b10f0300050140038042d0819000ea01e2031815181c45c00512800c0d9a9001440d1034541405030007503030b00d0300c6a4034002440d0b00d02414268896100c002c40300340c545142c00c0c0701a02d2500103820000220344180014421518000162548190149010000c131744a900200c1c1051191200c8400524205107011a040d50000b008080da14420780003001580c4c1d99081101c0e5075801d140c451000204a122409022050300e0400300e0102d00401420315a8403581e00914024566602e04503984d524031b040540d4601018801e4500410079420130070324142040000520620840311402e041c020400e1038500703041002c001c0e00b06807100c103801d02c0b56203687c0c20480c001c005403a8824500135903140341905403e41000f10702c518400506013081807a40b41141e5055002e50010071042c01d0a210f6400354503414202c0150280c4144250000380d480d15041100b4142041da099903114058041000b4031801a101c20100804a0b4810300e0640f81640341c3d0700d4203e489205504007280a100e02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 19649322 1250 19648072 19648081
    0x105010b0405090a05090601270f05010501030c03050705031f080109050a0210031e020711030d03020d0b03030f120705121527150f041a010906050301030f02010c030c020603 76
    0x403000140240c410454000700340b90785407031003801900c5040740c242d103181c5c0214004104a04440d0380012401d0300002e000791011a0f5044070303104a85440c02000c10139a210703c010800c1d542c0503c41c2c0d001100e40c2d0b00d002c0c413203413511000281c4a4400584804410401d0300030046014000800701809440303101c00a12001c26076040172917891904c1c02c03059124450030296542180d02030b2241d1f4058103012051002070110b5040c0703503002900030000941e00d640491344005110382e010300c03400364001850f40380141c441c1440480340c4219038100848a0003a4001c1218500018140303043e240c2d41d40c40280c03c2002550303a28400c654a01449040340b082c08103400900003221a0022030800c40d040c00e0f074920100400081d40c082c1800c1c2003036030360000460150081600c1040b07005014030403c1003d00304000c4100c0140200c0c04840002c884403030003188821896082d036900a041034000d182c1c900e0100d0855040d5100c0440c000120b1200a041c0b0a40341c10301002c040c041c00c02c826900750014091512842c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 19650572 1250 19649322 19649339
    0x60f020c1c11030601120201030c0c020d031106150112020f1e07120f0804110a05030d021b0102030a0f030b130204090207030e04020a020709050907030f05031308010c0f030207020a08010501 83
    0x102040b03603005119210520700e4240082d074030f4100c40002440d4000e804482e001500207101c60700c9900704028418140001603100e111010040c00d102e0703a2419110144222003070701300040600b21a61038007a0100480705a0390100301807030048041382c0300503954000126402050300c00e1710b114202d00c0a102003041c030407104001c054140d560107484039584081c8840c000701c47c02e50005e080c00e8041803100300400e0224241c0c0c2c01c1d0000c2041c010301b100c405d0030748034800241ba2811039580080141d05c0049229102c3c0c40050748408500401e0006506240148102420142d82d040400e410541e480341200c0166461115810f4030b240c2c4c00c0390865546403100191006580502416008156400c0300d1680d80d040074400c48609284950151001a083c000103101a200c0500107034218401c3c101d01001103183c986001c2007080c4294015540c460341c6141d0700000b9840d0b84e00116540c1d01d0705006801098003c42080d4003075149240042e610305a030f10004000104903000404590710307210010500ca007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 19651822 1250 19650572 19650619
    0x60d06031a150303030f0103060e0f030408030c010b03010506010c0f050c060d0605010e01021615020a0b0c04030c0e07360602010b03010b0f060a03020a1103070c030b06030a030207060f020c 83
    0x9901840201000b5165020316550748429155155000a51401000400d085500c0080c44c10010003c6d58a5084c070520160f0be150025000044150070000302d5400c8411b091043d0f107100b04098000b8415460203400280c4410908140606514004118107040000c24001d01c003e15200910301a100d401070410304005101c10702426000c50b21008200c4295800003454806110b0348801e010000c0f07082c140400044080000312106500c929042d49001a140340703a41d44c402c0200c0002f0f80e03111451030529100b41c001642c0700390005c141c014107000403030303900140e246002c00484000d03420100465450301001104180310b00d081d0050494003003110b40d4190850098444210700a00c044081503080042c200c0d40c0003559a81b2502c00c225804030039029401522041c8201c3c2002c000c4100004d24481c00c65002c00e100701c41030030b80d0080134420403a850014135001b440c00d134028140054540c0d0007031750f658414014032040c8025580400d0b00c5034420425190200710180c000303c3c04940b2800000c4849 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 19653072 1250 19651822 19651831
    0x705071e020a140d1e0204050c0309010c0c050c010c111002060a060b0901090312030605060c0c0307090e03070611090a091b02011b03051504021603030506060a0e060d06031a 76
    0xb00001d500018200107084005064103000030040340b61241c2940e2582d4080204007030815000e68a02143e41c05642c4520401e40300364101d003440c3d40d4901e0701165450031942c0e480f00200600c2441450313400441c07400110007014801c2800c0040e0300084500b010402e0002c40d80086c0c0e8840540700303042c406568049186030040c5040d00080c02200c1e00d469050650b4085d11501c4c0f80041c0141500304046080d50407000b14a15840c180002c0098648000c01d041d0350001070824056485400c07940741c941010407100c2c000b031000090401c08100030002d0a51039200d0104003030100ba48501d104120300070f4000c00c03140c1c200c00050940340c18603650010310024007001c1e4a070020180601e41b00207446401801010700007494011610542002548141c00910300603162250282d0142d8409200b5100d610007803a803040d03d09100309501d92503103001000e072000180494003031001880403200740d0383c100041c0b00001c07400301e49040d200e540c1d10b80c42d200200440d900c06890940e280b44004862403021f1407540c0074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 19654322 1250 19653072 19653079
    0x3070c020102062805190501030f03020601060507020a050607050c040f0c02010b06030f010608070909060611100e0d03020702010c020307060305060312070c0b0c010212041104060914040206030705071e02 89
    0x80340d442c41c4e4040150180c800c0e00948039424010000404241603010035400080d00341d101041c007036065012400c8840980003280c0c21100030080c101850303010000940144110b181943c580724003980400c0380c4840e03500c1040c1c0203110100e4410200042804000ea09081c0035104100d02c680680e04000504950242ca0b0095442c2c19020398060511000700c03131082c0f8500305043c20503440c1c1642280d00000040c00c040c10001d034190041100030042c018540100f41d04e41e540c0b100c1c14030910b015030401c03051100c136010640c6085402080a2000300f80f80c04084240d00340161900c54078001a6580804000001d506014244c1d001c540b258042d0301c42809041c06604682c4104003c0c4c40360100b52080900103004602003200400401d1460302c001e02c12010302200150800350010b42c0001c0d0b240302070328110794600c00e02150150300d040501c500c0004002041090140e40d5045480c02000c1c2c0020b040640034880000001d020035000d0400c1342c10103a4000e1049110032001c0c0891034008070840b000302d10 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 19655572 1250 19654322 19654333
    0x60f1608010302100c1a0406020d06060f0f0509031006080304080606060304030903060b0604090f0b0f040b0622030b0103080a020d0801051e01140a030b0a080607050706150b03070c020102 82
    0x6510551140d416254041c00d05800c11180c03036003e4a00c004507000c03c80c5e084071000c000d11003055250144038004c501ca600c0150300c0c0e51b604603960b4169075803900904100504c95455240066201c07d90003110707070f01030902543d10100c0901107820040041883e810700b9051510001d00950000001c1045900e0602035541c0d603140e00d02044802e11082d28041c0020b40c0d4441e041c0040b45166000c0c0d030303140b88014001450135507213000c44019a090303220112500c80e541c03540c41d401c0c1e00b020030540401c490103d03410071800c8403060003d205806200a0100c80494034a101041e94105c442c404000c2d40d008040000d1940e036034900440107074415202c110040c014500d800700306900800805042e074400510007842001c04c03411130942907800c01007241c100301103510000f155034581801018400348a960200c0d41d950340206000880005a05c40101c0c6d50040d000c0003800c1707a1010980c0d8249600010209503c0010b0b40b034000007201940225010030400414040c2c0540c002841c4640c2c140b00380c00b13071030307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 19656822 1250 19655572 19655611
    0x9090c090d1b060c03120209180c0c060906100e06030a050a260306060409020702031507020106080f03070b0f0702010905010c030207030e0d020105030a0903050415020c03100605060a0c05030c060f 86
    0x8450112802e001030104042ca6106e60031041560007410701184080c2c1000d030002c50580800c00c810509907900105450300081065240e241800005da010800c24010308850424414201d010035603031180c1501c89007440041a0160760034403c0c41c241d80d0704901194a980c001e4205054102c03014240401c5400c0c01880c121401da5801c0162849003600501e051b04061504c83c0d26406507000d00c10490340743c0a244105060b010216170854004c02003540009600c50420203024600343e6018246c00d2140e106002c6e410006002c3c05400d0b03441a80c01401ea4203944600c00281d02410400b50010720b99401c1800d0301c03111308c0d4558081c014072406581d580b01843c1a040600c080d0303548100e80a400603500f000018140e0f032140d0468100d0a2103842d02c3c1d03240035912140040d2503109018400d0040c3c20500900815207410840780c0110080040c08021140c64000015070620800f08240300b403058111400302408414025202c0754408001503c0306454141d02a00340841e0440e014070015404500d10b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 19658072 1250 19656822 19656827
    0xb01170607031e09031b080405030f010509100902010203040b03070302030a0c0e0d030516020607080903010b100e310603030f050a020601090216020a08010912031109090c090d1b06 79
    0x200643e45485203184480c80c0d00030f0869000d4a82c0f0402603003813001c0c00300308070f5804030b01aa64034a0b0034003c500c50707a219800c0c00101410300f4410b4201807910707070400051244147e0702048100d6540001d070400190b540da07900c0140d05500666121401c041c0020040bc4911038050300118071030203403a90108902c8540c1142528060000503a05401c09018810000040c3c060b000800a111305200e042ca6009030581c0016000c0d445204226828a404218240c2ca402d0074081d00102c504225240460030300d21080003441c408a400c0124403607000f420742050282614482e42d5a91030f840c180c00d503903003040840b05901a141a120071000074200c0040e0110322032145058600008095024040d03691070b02c00301d000a508000c2601604805840706d48005945010446000b08000701c000308007a14141003c00003030010a01d0041818200340c050340d119845081110420b100455a003003140d00ca501c0d0680d43da0048490071504070700380c1c90b001400e20103a042d441303400d24128a036080303050f9200c0004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 19659322 1250 19658072 19658081
    0x30302030a080702010e0f0f0c01140a0522031212020f04090207050c090f010e06030c0105070303051302030f16081605010f0311070309090b04060b0f07020d0b0117060703 75
    0x14006800501164a0841c4560100c5030088550b20001c6a683c040300031281c207207140802104c52503809086600410030013806408a00c1500742442c0400d141d230076026200798860920010300300310002071000f03660301d41e19907045181c40301c945a808406481c4c0c58410300721900c0d8500c04010840d4102d00d800c2604260003107a161952559115052524100c2020041d401403a411075803805a4882c00031181c40e410205071240c00700ea1800051945006000105a030b0082d003400d0003a04007607000c61250340c0080407182096850720b8002450340d1030354014168040320b0720000758180510303002074800c2030001804900c180d031251040203813940d80c5c00c451943c0d101d00400a004100100358100842e60090003082c09003066814007040b942c4000c5420451039120440c200c012883c807502c00e02640020b441103104454040d18100403250401d00d080700540110507180c00c1d4100c001816a04640b40e82e0003220840340e00c02c2c40c49209503180c505800706030f816014400258419200000c42c614442d006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 19660572 1250 19659322 19659329
    0xc040504081806040b03090102030f0c07110603061207030309081009050a110111060703020706060b0c060103080d110f03060909150106180509090d030e0a02011205070329030115 78
    0x3040b881c02510050346085400e840481c00c1d80103000340400180070b41580001d500c11210400010f80e03a241c11413050f49402d5024003805151030f0203001c2200001e0740108c2d0b910f980c803800c44143e41c0702c0d40c90500052800250280d010790314003510200004158211182105454205054070728a01001e83c0c68801c8443c4000e02518951140e003c00001c60700651000c84400e006141000407615a00078540c40c0030780940f4400c00003035000911409204180c0b14940180c40035111180c540381c210302d855a40c2d100180130203003500d103001943c0145481d41d98004c0c03030800c03600c84200b521a008640600b41c56001244c850f80140310f07003000212010703000f088a4901100c040744164441e424660108d8224101d10900903611180550104a580c4c1c0d040480703104440750002071410700d6108100400b0f480c20113000304c8169100035014401030fa0020b001401c481c100080018a695444108802410502c01c80180c0440e28003004200401c809004d01a9440260000e01604501c0700103050000c44520 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 19661822 1250 19660572 19660583
    0xf0117010909030e030a030801030b0c030412270902030414070302010f0e1c0503070210020d23091c05011503020603040204050402010e03070b0c010501080304030305090910030c0909050c040504 85
    0x5001507149584440340081c041c2c0303000381c064800080420302e024845a4194042459200100302301f00c4080c44050b8030840711400b1a041d41806d5440ca43c00020039640e03230307040c03280c01d8052100f8075540182c0002039800d086200d00000e5512800000254402c0d80d060f929544000350400600340001040c8080b603074181d4540c00d1a0f001000c0440d01c0b45d0214550310f80c440c8a0000c00b03080e40c500307060404256400b4001540e69000b10744104161058031241e24011b541002445807207a5070094034000001c1e030f80300d0b0091068042541e51216900c90818850750101d1140039080301d0a0b58105c01d040c42c0391143d8001c11840ca51608940b030940306512009610080c10030005005091035040706402c01d1060610f2944001c90100203428031106401000d102c500218245812140900409004000b500059480c140c1540c4000b40140305101010b406507281201103a050981491110010341e0840710311507002c0d0f102c80620002e400e4003042038540c0e110f0300031101a103151510a59010b84c0d80030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 19663072 1250 19661822 19661867
    0xc0c04020f1c020408150a0b09060a0b070305040812031f03051f0b040501030506060f040614010f200102070308070806010801050f01050403080f0a091208030411130e07050f01 77
    0x1001c0d0b10700c1516440c1121215581c090100040340001000503103561601381010030f89901c3e03c2103a850456181c801e40901c07034040001030190720707120440c561044e00c1c05094000e81d9062582030503030302482a68000c1c021881075006100c030484601c005940910303504070360380c681810401030140d00756695010140464001d2804805042c42509504540c4030008401080d01411217001134103c400c02d034001e0b500f41c2c02160422046c0d00d270142e50b080c01200701301c50801c01c0c0e909211441300e28003584400705040c0308550b000d5141b03c6001d034006040f010f01003171040c0c01c0c01001002d014040c0d0030440046002c1408100400d001600400d0300512444c0181e5a0104c246c1c41c21081000c1e085085c001d49040c482c5c10400400455460390040c109007800402003035450058000040c62501960311900c2111a24080280000c44243c2120703006a003000441d074040c1c4801000a100500d0103601c4002c0c81d18010351034403404000b2030040201d42c0121010302c06002d41600541d0784240a03900c000d02c04030384 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 19664322 1250 19663072 19663087
    0x606030c150822020904030c1103010204120b0a091b03020103050106032a05160b01080c0307051305060406050907031e06051003091704031a090d08060108130203010c050c0c04020f 79
    0xc0240403640000900c0d43c03622441554002ca076115a09071015400039030064400014404540c44103c50f0085c1500214a42898502e200c0fa041c05e00c00d400918140c440c1f8003041696500760495541160001059184110705040b40002c0801030702c4200e000c0390070030000080041c003a118265114210a025800c480d800040d641c52443c0c03c0354110040c0b080034002c0444486108030904030380340c400d10070080c0c654100b4507158506060440310510981c01a10144101d41703800c101001c095a856001144548400e00054040c2816422854001c903c080800850560581014031045006444200320b03940382c0c0c0e0800309480301c4d03000d82604413107081c151a1800303100340e0017448043d0007450148003070b2508103a501410b510913401a03030341c080c14020980ea04c80221441c42c0c0c01c0a000302c01041214024030b0013070005d500003845141070001200006d11052400c049244110358020000c2045410020018007103400c00e040700c1085c1e01c030300c41c806403080c2098801c40b100d000083d031a182c02c240341c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 19665572 1250 19664322 19664341
    0xc0d0206040b04030807090806090a0c0b091c0501020f03070804030f0c05070b07080910030903020f030715020c0c030a060e1b130b0d050f01020904050a0212010504020c030906070606030c1508 84
    0x100940007501f0800d90740c2001421010601034640506946c1024154641084c201404104515040490080801c00c18000203598850309504010240c141c48000300400b0300303086009010314400580c00c40c800004102d0340c15440307440c407403240c0e11039281d9050b042c8110f101140c01c1285c40e10300030610360105906000800e621001b400603113100303030016860428031401003014010451883c1e400300707441d02802002c054040c00108402406500110700b009942d4891800b04042c283c15803100c1031b40000c81d4081c4000610840b61440c0c809000c807042c8104500d404401840c41c0116070880d030041150f1080101c1410003141d0200e84018610003205007000140001401100002079100001d01900030000d4818000016070710005000140c45001180501064502c02444410040d20401400c030040c0750b4411014150f034019035005840d4007480c1032403840c41c410b2044181d400341002c140e403400c001c5103800010a88e40308419100f03603990b484c2c04d1002c003000d4690503440071410741c0000690006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 19666822 1250 19665572 19665587
    0x12040206090a0503070803130e09060402040207030909020307081503070b03160c1202030409060902040303050d0519060803030109060603090201051e090406060314010b040510081504050c0c0d0206040b0403 90
    0x101c01002c044806555600084c50040c071507100b49100c6e080410b440c07902200c0550741c00002c0080e40b01131000e51414400460f124540180007e02c60750740410054103061094038600054031007184119520f041c4140090541003044034502000244d0001855040c280800c00800300c0780084100c83c00c58407900c1c0030404010403850700c2c0701000740646204001c94100c054000b07100f00c09401469440c1c0c1444000300c151166030300001c8030103004020401c000381c0d001d02102ca81d180e071024000780b036455041c4000c0e01010b240000d0b085071410000c0110340441c02200840c100c0c1c1000c05d04000c0141d5454003502038481405019003c1402070010083e00b401c518031011503a075401d181c0030b1404980f28006412180a80c00c4480025564001c8003071805800b0302e00e41c00b510740d01091174109880e1000080002c1410103104040003c81804556000d84010b0301184500008005000310318100150383e5158108601100441c071074050107402a500101d4042d0142d0f03004065100380d560703a40c40544070036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 19668072 1250 19666822 19666837
    0x10614100e0f04020403030503040b0105090712050403020708060703020405031501030c03080f2808090a02030d0e031009080307020709090b04020d080903010606020f100e07260105090c01110312040206 88
    0xd0b203001c500c01e145503103e10081c4040c6109846042d16030406080c44021060142c03c502d00825104081c80209600304502d0341c0c98440f0701a0102d804d90315480c0c00c90030114294821101446030034184040710f034260300540144d0300103404030342d03c0d55410041c4100b0342d00c1c2884060000000d012061000c280810010a40711941d0100c4a25180003101c51540d100c0004640c820a5645002d21107101d03940030110700d40004003600202021040e0383c001036250b4200624003000d2024960b000652500c0c18020011040b43d080020000032040703040840580d403046a01c500180144000850b01802d14440d900110703070442e9021002d03640740e500340821111030312010b031098201440078646a0b502401404040c1c480750b03003d00f020881100060b03107809138210b201090b03a424805072110248000a5540c2210300e140a071042038050b40c504003800d201c101000400b03d5003070500b007082c040c40000d0024070030282a07850006440721100703016242e000f405a48540014030b0004900507150140140491 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 19669322 1250 19668072 19668079
    0x1409061b0708030a0905040608031c0203060411190201050108030a090b0702061b07030204050604090201020606040c0c0b010611070b0906090103050402060f0403050105090610080a17070b0108010e010614100e 91
    0x1040e8542e0399491a680012030b0354130000d80520760500040c20180902801040340c040110f0603c1d1008038001080309401d20010070307443d4084000b0b15680c1c0c564000580406d182d600c1c890307071401540d5040c1e00d1032040640180140d07003030030300000e2588400030440d4120000d90361280091070500d0030940c070545c8100340607a484542031020441d04d8600c134645405441a000041c0700e03251a51041c001641c1004110602c00d40c41c1070030060140c0d8001c42c5441e800322049400041940a5071800e4600481c6d501003d00b010312a40e00201c0d10390b4008400b2010014540d080b43c81c0a80c1c0c5081e00c070000c0c03041c00300c09500702900b4800390702d81394000e4000d0f5400c284001e007601e0a014000d495072038550400d500903159a9102e4080c02480103050210503048010102240300060501c92a1683d414268000a0072944180403106943e6204000d844095611811084595075604040d902820495444458552900000080034203a4029003c201e07500a01842180508984c003580c1c112128180703181c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 19670572 1250 19669322 19669333
    0xb0106052214030d03060b0f03100e07080403020106050609060f03070309050f0321010e0c0a050d0903090e0601021b1903170a080f061c051e0303071409061b 69
    0x41000c03101d1000d102902d4814100d210386a441001c140c50080013084e42024103141c04000e201c000e40650488078400003120307a0390fa40e500c44041e4212680342683c88005a25895070500079895170200c40140690302a500901c01c82d9104d800b0884c0a07c0384849499100c5000c01400074002000300245a1000150500041141c0191691800c28003200205481e5405c002501c2108600d02c09c0c2c90010045410008800c03581841c4c0c44185155001c0d06550040c0d9010401e03d031750600c00c80848260307254a40c1d00780500b010a113030280c8810440d0142190611280f0001a1994030014090500221110b5480a108039003004e02200d040040f4659041c003d4481300070002c154001544000c07030b00c080c191030b5590485c481b401040100041d00380111740180c4001c5c003c0c0c80d170312100d009802003009410356128044901d0310602c0c08031407408000d00c440c0e6940e281e040c40c01c800300241d84142c4454135580c0700b0110700070940e4480d10a082c3c400e5404001409041172910b0b060410880c601107000131984c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 19671822 1250 19670572 19670617
    0x1809050a050d02010501060908070f0902070503211015020c0405070c020a0e0106020d0203070804050603060604030209040c1511070e0705070503040e0603150708060f03030405060a020a05010b0d0b010605 89
    0x500345800355040b100543e45a01c0104181c0f82d1255040300105182409458001d00b451400b0342400114420603250316000320310201803190038404c984244005010081d641d58004003410b140400071255405002c0090200045403800302e0915403140c1c1316603024204012a04007044020034001c1d160304108110f80201c5001038a401203a0f601803d14003052880540c07622000a00d44244e101c0342e031003150000d00c60079002415800a071400d43d00215401600d9640c0c040c040307807440c001d6030f0002e540044902c05200034000d44100b2101640c0c11960241000940f0300300688030301d00000e9001c101640b16001c1040300e82d55030045c864108481d454254580b0f0500e8a80354a0350300301e03401c4282c4812240c0c060010524003080790003085000d0300a010710314604004080d100400040c1034074000d03410800c404030150380520881d0040c14008000b00d4071042d4041c002562441302090480d010344c40c06440710023901d04010b00a01255202e001c5242e039030300f03040081380c080d0841c4222002e801082c00c2c203036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 19673072 1250 19671822 19671833
    0x60504020a020106080d020705030601210614040203010606090b0901050313020927120a11010b0913020a05041104051e0306070e04051b0406031a0d0305070218011809050a 75
    0x700554406035002143d22800c0028041c189400148400c040d9070068100700044d88000c11a00d0440e5a0102d0301000c400c00c010920402618114000f1310b494a083e00700758502a08c914200d000e540260001c0100701e4480038107071248011b43c040c22811100a004040f203a42c4584001d61b8811485046180303507040540c0410701c112002d64042c0300748200d000202d043c801e102200c1849010b03003107004001070707205482100b00d14400c1045650421280144502005000f5002000100341c0035000392031038030b010000100d40d181c010f04100d00c5074141e100b0001d207515244c06030340452052861010f181500d420704008040c176100b4516440307d2410b1102d100a40d80504c1a94070800c480d0321a00030f41044803040000702c402c010400070032850811050418142001c05413416100c5600300084c000108076580c942d000035400744140d1008107880c5000425500c100030340030701d40c07082c0e8251071080350b580c1c40c212400382c00b40100006149a040800c0301d1000341e40201400d43c0c011029214403c00710b807a00e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 19674322 1250 19673072 19673077
    0x15051201060e10030519020618010219032307020306060f01090b040806061f09030221030301090f0c050a02030f03150402070f030e0f030307140c0a080d08010501030b0f040c0306050402 81
    0x3d12200c4443c202001804402d02400307100c0d0000c0c04210501d00b190307034000380140c09000951103038181c3d40d030107120303103039008202a18241180f0000040b00c40d00c40d24004141c684d0381402c25044800c160550007a803032641c8151001035900a01800f03031584c5d80014000c0001c940c0c11f07d14104000550f00103400050440180302600000000c0d10541c9000c0090003034642012000500350b8071090280840303d81d04c41c1292042d02d038111405901c250080d680b024410403640703400d8005000000001501d0f41d407692084a44401b107404c240030303407560300d0006e49060003410840e401607002040402d02c070341c1c41d040045500544047e000b83c0c51100903000300b01260442a002c0f205984608081d009054100360b003c0742c0d00c03408a4107c87c4908a200110340c0364096000c00800202218a8008103001309110a0076203000241800d01d00303584c3c86230b0040da2202020014000f0603105000840c50754840d016441003641b014103001c03000680c102c280300081034208101020165a91800308055445000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 19675572 1250 19674322 19674331
    0x5031c0605060d06060f1e080405030d020c01050405060603070f12030504031e020a0512031e09030f0d26060607020d06110c010b0604030201020c090a090b01060801080d020115051201060e 82
    0x10302a410002c002d0b20007100c0800b0502440b107140344150f00c455144250030031362185882d182070540c6560ad4418a1800342d9008001c0356800416107100a034015402640f145001d8012140562035034001d05441d03080d40d0107000d0060440810078018130b1a900d500059080c1720346022407510396070361a00710100c0b030b07400c1c6410410038645a101040d0300d407a12003900030b05002c558a00030f03888648801c41d600e120715045002c0d00300306400618150540b40082d18000d900c05010307200c2e1f2405100c0f031300307440d0320008000f100482c101180142500e10a80341c01ca6401e8807404010803591601410818a5003051340c0880c3c0c00110164540005040c41c050101ca0040007228140c803900d0f2150132909455440c5800744c00b800080c0810000343c0c0e030028a003c01e60b402a01d4201c0c00703459004900c0090002c03000003034114a1400000903d1690003403065040394801d80c00c0d00c100300b5407000c0407401da503251103460390b503a010b284081c003081c0b40c40c0000f82060341c8203100000b462582c0711800e9403803407422103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 19676822 1250 19675572 19675597
    0x90c15070b1605210601030b03010605060a0c060f0e061609050901120206071502032a030105090405030403060903020a020907020d080a0c0201021204050a0b090303041a0c0c061501110a05031c060506 87
    0x5d0103103650b0580106403106104070001c0c01568200000f040c003d0040d40d803004100320800485c0c40c240701c5142d0041408a10b2000c0901c6100124107442d41c0d102803d458400700040c85040e6a65503030300c6124a0003d4480050411000381d00e1710006800c3c1c0c8540180503640181d0802540c00040d10b0340412a07115000e0000c05616440c0001c0c029000b80e01001180c00c840040b880d101945c24051401c0f00d0640d81c044520700410f440390306000d03245000715000100190701d4103102d00c0906400286640300e2034402c442d00718003603039240002c9854165024807000480c181801240f1003c503503030862041c42c01c4500c001030812600c3c0500d682840c4090300d0a44260f0040b150402c04d12030081012580300605000441c034506140d0b41d502c0c01480c05d035225140c3d00b00d541003c101c2c40c1031000200e904110b0317417804440450a060b01d0346010100d84502d0305011541111f80a5090500451154000c640000140d802d10525035060740c8003414140b207039404107940340b00129541eaa03c5028003240d40d0541c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 19678072 1250 19676822 19676887
    0x90b0105010e030703150c0e06040602010209040b060406080402131803090807080105060306010b1309020403060e0601092d0b0a0b0403060605040506100302180405090c15070b1605 79
    0x500401410304041e0f000b500a43e03003d00210b09605006051a0a02e04000814920404048888610040071580c1c4100000f8001a00c1a41500540b9032060115420040700081004003c401e1003544501c1d000b01c0d03e001c00150151078826800604411003582c04503030004884e480484150344203400300e02151900c0b1080c40701c44001c00107500a40b41c2c450082045003403143c0000d640b40c0c0c052140451403580000e00100800b00314a1a200403c0300800554031184c591805d00d02612040e004002544103407400000c4000107401500c3c9840240c01410860014024980080c1405c40e800c400c2020b494490300c45c019145c40e010721002300300140001d600c0c0c41c01c510300b14040c2d400591100b4810350030301050045940d030f0b040d0300041b8942c0500b4010707600c16020300030411800720341c801e103a03010385072a00300803601201003001c05001710110b408171f0a0340694400b0049900070f0010141c50080100d00003240b80c0311001e5038050788022804c0403801d11400c0d107a0003802e1410440b4085405624 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 19679322 1250 19678072 19678079
    0x1f0902041a0313021306090203010f090b01082802070507080c030609210703031e0e07050d0b0103020402030c0d05070509100e091f0909060203041101090803030a02030a0f090b01 78
    0x86101491111004008051940c209500e0f60350080c2e55000029104003503080780c00d001c0600030b0380040b008000e076490945d2a983d59021000100d8054420408210b0404000c41d100c0c2d80b09006180c03140011004c0502800000440c42e000e1802c0591000030041d820030030000420b03400c100100042011800400041e401d0310181824004080c0482c4200d5000c0170042c0115003030010768120f84000c400803a5250000c5040072005001c088158011040300c20a034001d01b19a075400010360701c00c03a0800c48085c0d03507540d018095040841c03c0003901c220101c6006200500e40303a001035070000c00c03556603103052200d80c0b44680c088400c107030f8510300410400030f8042810304028000c45031900e200d00388040c8289080e00032441342c00d4000c041200505001034403034005403c3c4208000600400f0b041000100641c0c0b030018001d502c01c2d41c1c107071003092038400540c1e15503109041c20410b80d48040c0c0991700319207600c0d203a032002e5000076245c144000d49400585080b40908e200c0c40d500c41c3c0c0144007504130382d40b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 19680572 1250 19679322 19679339
    0x1a0d110307140a0806100e04090c0303090602071214010608061003050105010506031302010c0203120a020601030b060405010315020a020a02120a03080f100303140408060117010501060f171f090204 86
    0xc4019618100070003e02000c07000c15003216010340d11031015114482c11a1610000311204501d01c24015071103440d1200240034040c422054070156880703910381c841d08988a90059030744807024803440b5528980352120100141c801c245407031030260300e03400102d11a521041c810b400c21400329101c24080c0c3c4c1c103110820074402c09011741c40c0145004e440790703495410302400d900d000741c04500c0d02a0620407080081d10442d2030412800c46002c610340d030b081c1e4484000160094a0705400e1000340c3d0340c00925030110b041c900e441e10526041f43d0f03000560718800c01c0310241402c040c0d00405840320941c01110030b03840250302d03000e54407261000740d00c014080e10340851401403c03110016250240704c0490a0400130740c9044001c104003074035098200700c15620042c020b51011032090b81c00041d003034050b980c00000c80380b02040d81200c40d00c4c5800c000703010607030700c500044a149500401500c0001e04c040754444c0641c08407002550003268411404040d158050201000724003240c4c8411815940094200030141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 19681822 1250 19680572 19680587
    0x703080f0a031a09180a05100b010e04180308100803030112021801050609040e010e0307030302030601080c030603030403110f040c05030709060c0f0602090d0b091b0d0b011a0d110307 80
    0x2c1c07504903c00d100d4080c00812481c6000174000e4020b01800c07041c200d03070f0340d5040001031265903000f402c803840910300340038500107022004071a030301041d41004071141701e00c0d2078001e035851042e81d5402c0c2c807403044141c0c17000ca078100c001a1a200214444078404160104144003c6001e01200b040138142224544148010140c541059018400250b0014042c5075070b44411600d5482c4125404140c0c481000340c018010051003003010306500c4006001010550950051445094240c07200091540e440f40e032010a84030403a0080d034990020001840064000517001c0c24800014041038000f905900108003203d103880b0741c00b030210b00007008000360b45a000744404042d00c250710707014003d400c0b140c2d9200180369810000901e10350700070802c856280c46443c0d403c4100c039004008403d850900110060f00c44c00c1000c030207500d201c00c010754195070f4104982e40b03100040d801031b000d04d8143c1c030303042c1801064060342c0690244a00200015040d0f45107500800e03145142c2a90810781d2410105409080078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 19683072 1250 19681822 19681841
    0x30c08010203100303050a0203040f0909120903082208190605010b040302030a060504020114070b09010b09070c06090c170610090c0503070c0813030f050f03090f060702030703080f0a03 81
    0x680c010001c00460382211142c1c40c007220f40c10300704140c5a60300410143c0c11405a60040030b0001512f900003d940c40843d0450650b05004103030810f80f160060310115003c418901014081400802040304112000c004818160303100e40000e081840c3c50306001424500c00184008450300040e2000e410700c030312849041d0041208d001e1840c6010320310b07804a40c442e00590406800e00795214000380541e4021308419460b0146038150950b00c0d411490301c00d85940060b118401d00b03618015036000300e814000701d090700425080e14ac154144200365940c0010304040c0001f1a200e8915440004031a03022642c02d40c801c141d0b04011b88400c5c9815002c1041c80c002652040022504043c4031451954000d4100c2e42c09c0161480c0c0742c60981d1032400e1000c55803207115503c00c080c01e0440000070600400324084001948201e090318080d40d021500c50f5540d00035444070783d5000224020074051f600e4128001d104d6144041c1c142c4000940c2c9071261905504505401c0c0311289000424011803a410710500350324 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 19684322 1250 19683072 19683089
    0xf0909120e03120f0c070b1305040c052505010e0706030e0a0c0b0d0209060d0504030210090203060112111f110a081602010c0b0103060b12010e060705031003050f07030c 74
    0xc2802400002d41e645643e00c40300c2004100002c01120314412041200c001030700c0e4004440d030321950b840d50030001c2da01c040c0204203600c40c800d0002c691071400c1d02801c50800c0003a641d176800c1c80380104904090000f07071402c001c00441ca408622001030310038010b01c0c2c40c4102c1480075000c01d0303241c003401030152942001c02404075040040e03000002680c003020141039445104980d03807140210340b0014001d2041c188074681c04400880d4804640040303400544c031940c800d500f074a690381c031490124070545003400341c0203500d50480300c018044005c522040c0107441e0b002d0f410554000c01d0b80d901107036076014000801b00c01c0c003500010420a0b0f40d0812040365400d05418010049a81e041e00e0701c5071340b40182c0104202e0b000c510300b028820740e07200d110306c01d28660b00300012154a59403843c060340200041c0480c603000d4030b444084040200340610807107546a00980c09481548d4656104071a180e000811509c2100c0180c0030100109008001e60301001c00004000d015641c25401c20440700507860303204626 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 19685572 1250 19684322 19684337
    0x3090c030303060603040308090a080d0207061d0a0303020a021005090313050d050a120e030f0601080105070504080705100306081209090a0204050f0d05011b02010b0a080105060a0b030408040f090912 87
    0xf4540300d840449070301036090724101805459510301d11703007071013a5441c01405d000300108c0d5002c00e00189900a04040c0c0c410f5034104800c142240744080c55081c464892368982c0c200710035030004a8001d13002000070160324410b0b9521101d003018810104c91060f0342c15142035001041400281c0120003501000d08400c885003410403100307685e11617558002020080904c001c941c82201034901901e0104010500101035806c0c06c00d411101d00d80d40e01d024031a4010a43c2007401069440340607004071025074520742c02030944681004103001d01404460300500400d81e50754400900004c0900c2002081e055407840706581c5c0481c14100f02d9103820203020b10381070317502c100010000c5595040103081c0d249402d0b40d108074098418105075004210f04015229481005038004075182d0b410f42c044400400200e80e41000310fa101c07041103088880803107490340c20040862042c80755083c0f1001a40c0e110340702e000c56a1905443e081c003420b65410542c0000350242d2980420802c000f0315052110714203d00b45003852 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 19686822 1250 19685572 19685581
    0xa050d030501180b060702061b0705060c030a0e060408070303050309120414040506040b0405150a0e041a0912130e1303050409020904020409060e0105030708010615140c060c03090c030303 82
    0x310392400d03483c0c2420119a680c040c080071792610001d6030a016002400c0039264040d186042d10721040c200f801c50340c2ca00804202140c2e503d000d60036a500208004020f60812581000075610200d0010700b1384da016005000010b80211b040125070099032103691819120306049408a25102e040a401803070244140018841f1804445601e000400c0842e008106a1104404207009110340304005805c40d01f040f08100f60030341c203c41722084c400e40a840c1d070340b1116955800d03502001c4095034010704010204090752003140c4c0c12001d0507000b2401e141a40c1c04100c00d03455a98052b0302001e905031712404d400c0420001c14442e8200240d2100003507440040b034524507a4014001d11640c0030300315a103076000c12038051075107881d2b054501402000104010041c1c40341c10b84e110042c0244541c030303c284121030000c904502d0602454080396641c28003c240f55031404070580b035141c03180001501459040c4070b102c03ca800e003041250301a003249078450fa5203062020009044c410200d513024003d520800521 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 19688072 1250 19686822 19686839
    0x7030f030513060506130501030605060f03010509030a11031603020d0801081b010318060510140a080c0105070312140a0b0102030a020613060216030201020d0b0904020d061109120a050d030501 84
    0x5a1280f00080c280da10707000001d0320b54400352000e401d5146000c0020040129130340c0814011791048a102030f145d0000c804060030303982c040341c4032180d6400c14440e402c0d855014002c8441d407000f400e0309480c103008200c105415221050303803007640180d00c0307090703190402a00581c90602400420024191090300c04c001051a401d54101a40c10940e517080342c200300341c000c24140317540150f01250a1195042c400c940d40013415882c047c1101018038210007038050328159880400b1111118050458606054010340d00c0384c10601d400da06118445103d081820614450720540315015420000d50b4107020705a002203503800c2c0b0364075041d54010004650001e400041560344022880085001075030f152a081011303015151a211500e00312240c42410580c040d0064040a48a503030104a0342c0e050340c00300b000140c1c040d00c0c0a90044200d21048020440382d8100c483c52a249201c02413601c1c5401000c5041010940f0034080742d42c20030081c0c60200542800140101c250703514050056506001c3e05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 19689322 1250 19688072 19688101
    0x703080f0409200304031808010f061503050f0109021e0406020604140d120209030f0708060106080a060501080c0c0f0d050705070b03010b09061c06030c08150903090d0204090f0807030f0305 83
    0x160910000c00311034065204103034510006000c420000303000ac1410680143e0181c8464040c0c880c03c114100c40c624880e0f80300f03219180c454503d000e02c145090740781c110024000c0d40010712803003038410703a03035031521340482082c2c0140014601a4014200741c036090a11030384c403074401182901c42d40c0000c0449000c00d07a00125003d6010184080140c0e02c1d5600c2c40000d1900c00301003c0f601d25809140d400189445000c1000d5040340e041c1c1e00c4003036580da51000004200c0c2c90394021540031030f00440104d058440f2103800341045175070b03e47c2140c1c1d4034181010034500c0c00381c80514280010340005610800c0040601ca000006c0047c0011a41554103240320f2141c1c80c012185000d002d0203002c68115025250741d20661148609403100304111500c0c0d08041442e140280280f050710322401d0019040425040e00443c42504020050342c10640c001c030800407140040c100c20f030ba00617101c100d1280414503989902e021284900080ca5841d001c91602600b00d0501076142070030b2620300f2003040a00c0312070422 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 19690572 1250 19689322 19689331
    0x40c060e03060610110c040f0209011202090102030a0302030703090f05100f0e06010b030c0706060b040609080c0a0b0306030309060c030a020d0c0b0a020703050d18060501090207080f0306030703080f04092003 91
    0x21701200706611201c0c92031500010021082d4898106039500e40c0d0341040758000c01c0050001e0780c50541031000ba40c20130302644030b1041c1c05030040e402005401405803080d80a035810a1451401191394004d5440756600c0e122115425585a00f1200301100081c0b03039841a00d0388801c0448040c841803604a41060301c40c80d052190307030080705c000400070302c20305800c40c1129501039102c01d04112440d10755000e8070380c0e50054041c5a001c103180c84400301c3e06240004504c418074800520b91100c05040240000c0c0d1a0005000c0580610050121141555a41020b04042e840000065850b00741d1030100a15004901060b00309102c0b5440a0102203030344248400d0b48150512030260381d42c03c1c24a0200c0725131281c94100c266092a00310711070150900243d8004005004a1050241d6600c0d0381d00742d0100d02c2003040040119070104010800d0702180009940d000c80c0080a88508a07580c2c0c8400031303940d00080c0c03203030326614002070240100b0540f03110f15000c0800940803045604d4a2800148040c8000b90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 19691822 1250 19690572 19690577
    0x80304060e0604060c0801050405010e06130e0102160c15080c03100509040302061e13030c0c050a2601110a030f09020310090311010903050702011209060203040c060e03060610 77
    0x14103025864200140304041907007101c0551820381001d00042c0884c4001500040580f0f000180da413819000c1e890599071410039030020b60311000d04000483c6107032203007280501c0d1106402c4829007401c0c0702500408181013640e018141c680c5c9040000e0407060707048881e1b04c0c1076940815490603802102d0035407110b0f96100c400d5481d184c800440304462050b03031040d41e10281d440b04020405a01103035140c0107c1500329a240c000300750018502010720119540044181c5111141000c03038842d04a0082250042c0143c6038015219404140340c14001d4014200003070200764510185007030109070000002e0303008000c01110885015241c46072159944078003c01d030700c60041d0b10401c049a448265039a41c000c0441e4070080d1500003840c00f0b480b01a01c26001f0695146030280071035010300a00700e0b01c9034581c1d03d40c2e1030310509034015601030038141c5083c446c01e1ba888054900143c02d500c002c600641c0a000d8945066240a9004042c0c1160554245c002d400c0340f4244030003500d498030341d0702c074040303650 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 19693072 1250 19691822 19691827
    0xe0109050d0b160e03010204030309050102010c110c01141e19050708040e0901020d0603050c01090503120306060f0c010903020304050a050d02180a020d020f070b0609040c061202070602070501050619080a08 90
    0x94408442c9070b02020130b410740c1541700140002c100368000c2c00400469034207070020302202e00903003401d5030460707106e443d400c01c1d0350050780c0104d4640d07100e4400008044560460281071500050024550b6100029110300c441000900580448031503403803424a83da840c070789540b80c8031441e90b501c03869006a01c00c4840c000050f13008103848150079015640c08803003400042045070b6490901c9903860310100003450108890500108850401003040c0303801e00d0700782e032541d455034443c0801d0107420340c44070080024808051004030401034003030042000e040d000c0d41c001c5072283d09003000c00c445025258005840790a00b1070340c01d070050325000c2104401411604c5068620f585001040002e80b09122800801034030006010f01c1a090041c081c00d50300d0b00611610b0102e82d03400c420b101d854042950050300154050404002044c03140c015190808507140c00075043c500207540704416030b004828100c030942d459000700072607400e0280f0154051301c0702400f0001d0843c6400900c0c6c1c2c540400b00c4d000362030030200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 19694322 1250 19693072 19693111
    0x30315040504021305070201050a0506060702030a11030a0b07020705100f0206161b0c090e010c270e0406020309010506010206010605220b040b0310080d09061d0a060e0109050d0b 78
    0x420101c0c01c1c13a410b846405000514202600134000c01c0304843c040041403a100c0411000c2c14680245d45126074041c000380050b030525200c0ca0b100704130604caa10392621452501500103035401e141c0d51f02898003500104495070900302006055512941640304020080b684804c503164001000b035000b400c0c4000032000c4040c1c110713003201d041c0a82103000340d010380d0959502e0200080c03501c500b81103e655030b6003000514086454542030b2107800a201c030026490795a08203240403043d503c908024102038070300303618546d03510304510403072070444080d1445680441080503480003070286507800a0244040c115035030400801600724090400c0b0451214192240002d10341761900e0030324041c1c00c1c4856440e8645a4804001d00340d58002c032951401050341420010b8064400680368180300b0b03c0d900c03050000c2c0e040c120100c8960a20010007010100380052901d016203407a106200a06804d54a2401c008242400980f40980c154082c5008244603544400444d02007080d0680003c0703641c1c545444941c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 19695572 1250 19694322 19694329
    0x60503060112020f1b060103080702091e070503060306060405040302190c050d050307051204060504090c02100507080108010c0c02100e0a0803040b070606050f030a02060903010905031201080f03031504050402 91
    0x100702200b07140036440000c110f84110a4034000d071078245018884c04050400c515a0790b600c880c0300380300082449400780000c00051903c08040c0f64040d11400315035815102c024940401454250f4902c0b0102c0c4c400020310801d03090611003560703c040141c8081c052804c05550003903580c9002c0c407600101035000f05105080000704000309004250061a115980905080c03546d1240d00086048801d44205602c10400860300026141160250384440d0704103440c0084c0078000c3c01030201d0340421801101c28021541c400c900c00c45009000c240d4480300d8035810a00c80600316446222130806000054285074010fa07141007090500c90640e24003e1800f049031000f103500748616412401c5680408075000c80d51441c0003000c0c11b2002d00030a0140080303039640080c851000b4040d810b013905900008040400b50030400000c21032171902034000500d201c1c154440b0390944e04103092006407242c01c540100b048110070003c1491070801075025600c1c43c10a21842c0038030041d50121240a039449000060641d507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 19696822 1250 19695572 19695587
    0xb01020102131d01150e0607030e0d0b040b0a060e040807030c02030703031d040509030d0b15040305071502010b03060711190803060a060e0102030703030f150e040b0c03040209010605030601 83
    0x4003404515250a80307403d1900c4880c0944000703104110411000000c0d81182c0081d54411583d0075115601c0c841d450b04140501d66205a0045e01404a4ac0003c090300340c42e00e940b0280000d00035010080d1a08242c58960380b2010060065004a41000d1041c4200001840c0307898000e58840500d60ba105007501e000e4402012026010f0b42c10b00811400005040d0800900c921032171340301408170214100300040008903141a2807a40c843e91040c8070400343d1035020740c04040c045200410320310180c0c0305000d020041b640582c00840d65500841020424030411005501300340129000900c008184640420b96880340100404104102d40c100c82e01500001c1c02207950130541903541031700c80f91260506460a500a403001c1e03018603100740d03000a0310341c8926100304000354160301541c5406000c0d18214090001c141303210b0300040d80c03a0f401a00d102c0501c180e010040c6840303401d0729010f05e09030500d6015001c4c020408408414108200001a511400d40a0560b442e40c00c250361030b6110680129480d6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 19698072 1250 19696822 19696837
    0x50a05090d1a1f0605030a09060e01020a03150504050114060f0405060703030b01080709082d0a0302060402150304020d0210110607030e0709020705030406050307121a0915010207030201030b01020102 87
    0x3098031905485208201c1c1d80d51142015422043d55a00c07155240d01d01481c151180b5030010302c040c00861b555840640144292034010750002c21000f204031903003801ca81c4910302074030200b80d843c0d909441410600d20060300030700d0201d404101d00c0d80741004d0910001d030590340b603600c0399600241001c945281000bc1e14040e180107440f01e501c0e2106481d01034020101042c5d098081240071001a00e0076101d4070888080d05c030340c1c2015000094520300b0200c00e4203401800581c0c50305c203159807181c00003400c010003d50580668000e08603810140184408240d11880140e600d1004004210160f194001c80d0f03440c15605890044415418200444a14101c1011038901e40594801d10600c2a0305030800300c403513001d91081e203002680d0380c1544401c9118030500280150000d000410100d4000e001450780b00d0f4042c00c1007518015160381c00412520442c040c086115982c80e81c942c802d08200c6401584035201522a00000b41070500107541d4004030300c0000d041507200d000300300442e4406e4041d41c051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 19699322 1250 19698072 19698083
    0x9040e12030a02130902030403020d2a08040911040305030f0313141005070203090112050606090909070801060f0605090d0602040803040e0105030d08070c0308070c1e0c0603020406050a05090d 84
    0x12401c200c02c19030301960007040103580383c800c5988049110b0495108407806070354036400074581078105800a5607072040b032407040c907510b4988021a02622502200f4150228400d00285a0f00e60500c03400e00e04030795110340f01d280c0c0000140001d000241002040710780c00315503400c81a88981d074095210a0300c800ea950000d05000c50032420000e88540028001740c0001c44001c20701c125610414101e9484c0181c0c01e100e800101c2d161000d600f07951081d40aa608528044c002c24500050403001c01c00c8610140c464050303d40c1f0000d41004071180a01c00c3d030004d4041d00c001c3c544010301c0c05e0b1009040340600342200f80308560750540340040009a60403103008055810a4030748482d500d8903c0d510401b024442c05010b8040d10407160110303803051200904c5150291201c0c032403141c0540307084400d01d00007403c50f403e00c03480e000908040f50240c5a1422a80103070b480d0404908014685070b03141d5a00c6d54001d1050600501060001a801c6010f4940c4101d1528105807600302c8000010011400908003421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 19700572 1250 19699322 19699327
    0xf07081e07030806010813022b08030906090a031d130c0201020904060f12030f0509092409070206010506070602070c0608010501080c120118090c080303090d0206090309040e12 77
    0x80d10518002810049020f915a029142d6804005441a0388112810361000c403805840130010703d00b14040e4084601c540b080c040c0300011517810b210349a0210303030b01940c0c04003001c020004000020000d203540300040001403c0d0703101d4644e40180a000941c0c0310030040d004030034081c034031584982c10104070043c55100c0502440c00d9508020b4000c1d4003450000b4051070030700c1030110b4000850001502210142402804514402c1d1801c0b1103c880b410004010000e0801014426070f40b14040c01e80110031281d07203104001c444410803042c12407041030541c00780c00c0c1007007000000c60700490341c0c82c11145d06a07242503454031580303000b078024032400da802041c421b001040400c0c030301e500c1043c05059600c207885003802c0741c403440010162800341081e40240c009000005000b90050b44008001c1031342030001c0407a601425588882e40344085402c5102154004000c1140489041100c4010b0102500182c54035042c20003000f52a807103a102c1d024080d6498181c078143c2100100192551904021001c54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 19701822 1250 19700572 19700617
    0x40318090609060503010b100e01090e1603050906040b04030f02070801050901050109180b0601120b030a050a020312120f0402010908070f06020709050601020a0b06030c031002120901060302060f0708 87
    0x80080e4042c0300d84a0349004004039090505200b002e20154004090341c070802c1620384200c40710b0030000d013036a0412402180015181c02c000071001d0048150000c0d00d44078026030700c030040849200800702516035011030188000304014503c000e40007901854014000c49030401c00b6271502609602c0b22005600e003404000c814101980180d05a0301e040505002080d502c02d24190308800c551005403c41b0100e101040740f540c000d1508141c00824031001042c140310b5500000d0428072400810345850304040c01d00000c52405000000490320000c486034200075001c00705491210008000320488421200860156030240303088030001c00218040311202a1a1411807407100520b204a6001d8891301002040c0049103004d00741c0304031810381c001c1150034003944071501a65009030890743c03d4094012400150f450920900000c1c201458001d070b0f94104410304000700c0200140016100e0345044800d02c0141d460030704a8038441d003580c0003d80c484100f82484c16039132251183c3c0c0c03212a0401e41d1400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 19703072 1250 19701822 19701839
    0xd0203040203060106020705030d0f0c15090204050a02031009050a090203010c090e01060203250303060f29160b0a060905040c0501030c09060203030105190305060708061f0503040b040318 82
    0x210321651081e0103032011a641d8a500342c4e5101824040c007581500543d025030031180c403818803070160341d40910300350f00c013840c3d0781d2200c1d03035982e000c50701e10041280ca42d142e5000354100b030701030a900200302244c214075601d040d19030540034501d5401303801419610f8601040b00300380395070045c440036034000340200012018002d008c2c120301114400d039165003c010000013031060022040da50707200c004890300d201d002001c1c00b10010861842070200c062642c0c0703100208400c4400e64240010700170380b030b4190f066010340751242450300841c10002c50744502d0800180f04501000180340c080c00b0b61001c40f2414540f5603520200c05800340d6000010b02c0340c036002c100424401c240c46d400702180c00a803810440ca0b00010400c56880c4841e005020242e0f2003000100f00720b00745192040018100010f510107a16103a90702c00d424040191480800036400700e05100091400c034882c00e588100340500c4151143c50440060680c0c000240043c1c14458038130002014035005400381c107120706a80700c500b0030b180d8442824 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 19704322 1250 19703072 19703077
    0x9190b03010b03010302011704080d050603030d05151908070909170a03020307120504110907090b180102010e0601030c210204050f040b1008030d020705031903060305060703060303081603020c030d02 87
    0x11b030f000580740c10a0b51119a040c0b10740c58095600124564603021040c3c2c000000350501030442c9070103120400181544031200e2103201c1c0181c1c6007411007120444000c04100780005026040d0036061040401001440720010350201200d040007404101890181020b040c511b0850031b0b14803c2650004141d407016500d0340c000c510844440d00e803102100c070300301240400c1302d0080710010301c801e41400c02e04000e0b03d8070b051026404401b030301d07144180a0701c940c8201c0031030b0040c204149000150540c2140b071981c080c0106041a102c0303000400340c5614589910541600510034a12002100840500510005d90503a12200c0d005002403207a4186500070302c5401c0412101550841d079042c02058000004003600300813601040015418810f18520031402036001c10b108482c60701c010800040b031030940809602c0d051110342c40020b0300b5840c5041c160b05040e0024281c0003014540314051001a821001032900004624000340104003690000d81c000c3c4030b071041c441d0740f500c40440c3c90003525045400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 19705572 1250 19704322 19704329
    0x30f040e01030b0f09030a0c0213020d0911030d0834080f010b03060102030901031a0904030207030605100f03060e12160c140303030f090114190e0a0809190b03010b0301 74
    0x3000703980365482c0700d404c0000c81c006440902550704100108142e15214000e00490b0500040c8030031a1080025a220b00303c2e4858001c003002d494a4081c08020300c45008107100780d01c8800d5025080c4580126001040e1900040444e41420010121a92001a251900d0180040c0170618410740c003054000a403a0300401c807008058014000c0001c101d608444003078034003882040c1c000354102140a07006402900c1c41c1c03401c2c842032809120b061900c40e0340384c4486c40d0245000381c01401c031617801c42c2001c2084d03900081c13036842603000603081007018200030700320341007226081040094041ca00c482c8085c106940e8600100303207418080391420000810120581d41240f1071140343c05410380e03030440d401003d00c031015180c0d8146c01c188002071203050138250342c540c41000000002040349045440c0b2000b00c0050340c4200c0d82e01d450000302001c3c13080511503014441200401001440300b590740e803060301c0c890007840c02d00581358000040e1406854468403405010881f4503a9120341c0c6410704080d150b0801d20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 19706822 1250 19705572 19705583
    0xb10050a060e030606030109150b06160c03030f020601060207030b180f0c040c030501080a08090a030b0a02030f0a0902031c03060807030f060507090b030402041503050d090609080c010206011502030f040e0103 91
    0x104015146c140704403045140e00502c001000941b0030300c2c000040c0160003001d90001810000219901103500c200100203226a2034044000c0c19030400400d0030b05001d108400755400103005006458002070a04201c135840b084000b01960b48003400c010703503c28401c00304200e1042000000702d442c004500184058000eaa04012a1840c3d007000c41c15640700f80305404140d00001901d10108407044014441910040c00c1405215529610003105c2c03002120480b2000303901005200304024080502c503000450756405201d0002c054000948520303003211004024501000e04580340713400381d040800100208004c3c2c0311226524101810b030450110011503526260800103860b45010303600b00000d460192507841e0a690b525400c2c000100000810440c50075007001c400000610304100009400e6180e540c0e210101e8900f460103040791040d50085a05500074000c840076a9a0000c0c1150444201d040d08180341070b0010380690962040804400305080e0008001c40c2e07000074160b403141241e1085 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 19708072 1250 19706822 19706833
    0x30b030c06120a0b010e03060103060507030501050d11010c05071706010807061106160201021e120105030d0507030e040603141b0d0314030402030705120c12010504020d0b10050a060e03 81
    0x902081007500c58425200864110600810810f00c2c1036480803014003410704221420203800e000007807821109a0040301c400e03031182c0400c890160305000c0d942c01001d055803041a110040e5075000c4410301aa003400781000314083c052814008200001802440010b024183c42444442a5911030209025201291283c440700043c441d12030004003041c41c814501500d003584690103484d41d0022005010001c541d001c0c0468045400310201d00348100c0c0c6808003440e07030703200301d803010f6000002c0507840581301e43c00850100c0c40482c0c200084800c45940740c9824140e80c1c030780d030b4002002410720790000703480501d0011a00c02482000140c07a40e6444030154020340c40c1c074851080142d40c0d6181200200014601c3e100451007150401c095038005100500383c400301a111004200c1c6840340001484280d40000d0419800781404468480c00128190003841203180075004130303c041d1001c500040100c4080c1c40011701b88104010344c040074200080080281540e90140240310200150381540310b03000f079 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 19709322 1250 19708072 19708093
    0x8071409040b01060c0c08010507050a030b010e090c091305130201090f03050304060f0201020904111305010203130e060607060504050109060501050609090c031306110c070501080123061603030b03 86
    0x9203556034400c552082401c40d03240e091090132904803460200454820341640b02c040740118080c010142300d0001c0c2e07030711a511032582250080903200440d026070305205101a2000e031175250b00869590018169200f155210b18020110340080400042440060b18081c24424000c4502442e0900c03a4000d0fa29045440d46504e044a2a50050700c001455907004010030029280030701e840034412803445c00014140301c590400b01e000e4030400b414032580501700007807001c0d240d440d210f0300e40c002d80400c0c030055003005000c400c40500740c02c05002d0003241140510003d006942e9450440d28890b034810300500240c2860302d031150107448020804c0307480d00e04080011800341002001d81d006000002e01f881e0060701d518041c1036841d4001343c0300000d240b6119090700041107a5005104100b0320000c0d840356280b01d041c0c0d0440c01c0402c550070050421090500410409014a00c420f0a000e200034040800000450008403244540c00c0c0c40b0b040f104801c028601410f4040c0e1058090b07003410f8042d648904503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 19710572 1250 19709322 19709329
    0xe04060b031603060b0402041e03170a05030402040b03010618060503100b0d030f09080a051006050a0f0308030c0403020a08060709090506030d0c020f06070b1501020705150304020d06020301080714 86
    0x1c1989506640b600c05000c00104000d500102c00c4404040d00043ca41a2681c501c24441050f680690341c01c00b40651040042000c030744081040100c0c043c01c0c0905151030cc0400518070b200141019200300c0e02c40ca034446c0c5c141d4081d031201c0700400a00c54140382940d1041e4820300a03000ca44213a0f4401e018940f010503d40d456405091008280204903d40c40100740d82c00340c0c1e044001e03d859204008041c0e0010460f240d003080790030312450041000385145500d04c407100c402e407603080e0041030040211030020414005071080c1e288c156544840039540b25958034000f540540a00c1d40080d5101c2c51441e0000f41841d00801c511380501c0700e40e5184030181d034440003420180c40d000d41d00d4980582c80b200644512601c20070b4841c00d070510040c96a4102c07090103001034855000b900d0141e404030100d0060000000865098024451003800902000c0e0700d40b0f800540c0e003d9204286032a4400c0000000703045684141c1d0500e041544817204548030f507190290503a039003a1500541032800d4140c684c4042d5481c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 19711822 1250 19710572 19710583
    0x90b0604050105160c0308031806011e03020d08090a09020a08130201120b040209100504050108070f020703080c0c030a0302070918020604090c020a050102070605040201080c0a0e040507090306060e04060b03 90
    0x80040e110149425070b10400b0700101303407024038269849840c82c10080002134503800110700807000703207003859000c07000f000086040030350681c080c0c1d80001041a84d040e80e01c4081503054201c90b01180c2070400c0072450b00304190b0078032440c078060b9403108008030b002c40c1d003808036405031038014260360700c40005655a48401d1000044814041c0c042200e50840c0b603540e06050300898892140504091f04000c20100480d02d240c02000651011940106052100e541c3c84030b070312503000c0d9162520503400303542c0d0b02c00a0f407654550300018001e0500042c143d49520001c101c07040c01010081c040322104000e50600a45412090003554036490510848080c1d4400c9200840441900244250314081c9085007038801012030600e14401e40c0640054000810020320103041d9041c02503201003051f207801c0c8001005100010840c40502c58240b01481106a0010491180c5d03041607900007206d4485480a0300c5c010901e6000414183c00c1210110341256081820741c007991243c4024010200031804150321035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 19713072 1250 19711822 19711829
    0x8070303050a1e1a0a0906031b06051c06030506040c080c0103061406030405011812030b01030216020f0303090301020409060806180a0308130f0807030f0206012102041103070207090b0604 82
    0x3e144064040014441680000c01840c410000701e81030304ca0420104d0241002e5a01011071142d80300d80c100148040e0821521042d2020a10812810308005001d001e50117a19480d456500c0390300d40e8411007400a91001c0095030b000700840e2603038034103443e00401100c800d0103800310038005c140c000c0007694081d000d82d2007658503611020140385028814401143c02c010400da800c2d64030345040d0740c8600404100b010002d40208a046081c40d20750f64040e09641050f6002410144104000c49400000d01005a40c0c694101c40d00c01c003802440340000d1a600800c140c240d4035510010b0000303100c034010f92203182200d250405072071740c503583e04144098040d9480340c1e400c1e0b43d800c20003e01001a1180380344c16400799912140420502690700c41c041c00645000e4203c0703150310b0000e15481419084041c00741780300790a00c002c15a541c103011103040419080da040b02d0701d26100c8405c9204558417504840f1502550300e03600c2c6d440346000240290399101c54072440b84050320b00b655100d51424030b50700322000d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 19714322 1250 19713072 19713101
    0x1020307090e1b070c0504110403060c0c02010e04020d09060203091506060406090b030901060b040f050310060305120c0a021017070302030c12090c0a0602010c181211031908070303050a 81
    0x526240f0b1040c0301c0725901065003100c3d198031040001c03481e580c586c42109072a00300683c030180c44505500d00131007101e9803c4118403c1c031840f950141c0060703030704c4401d0210400c8140d6015840304140300484c4050141940c00910b05800401009002e6a00141580510305468216501030322028140001440750303000f44000203401729020f02c490082000299040b90102000041d4241ea03080028556042500800c000b00b400c0d200402c6140750030004030003803a0b6440d03810044c03246140e030754541e01e140c1c4500d00034806202292030f8034030041c18082030400a030060b0081803880090071000740b280828130b903810041300345172000c282841d03c24403d5074491419003000c240f50810030340611250810060102c4410310480e03140c95030b941c030b0b4135800300000d202940003c1842c800454024006003107010084c1a1149246420804610040f4600d140d9580020080d807803100b0f982c001c45d05000260340c0042c208503152141c6c07410081085c008000c0d0b140030703a50811107616200403072015154140e0190781c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 19715572 1250 19714322 19714351
    0x15050a140f040b0714041e0e131203020405180103170c0304050f120d0e0906060a0507080d0b12060402030105060607020d11120f03070c0b07080f0c0304050a0801020307090e 76
    0x1603021104103400c605203044c510740c808a090031004141d0301940110712078165100e600c6c0b03050352000c28444083c003081c116400c0c180ca001608042400527903640900f000700c081d040c840b152030095045a0140801915040e0940012081800e0241c02880102d4610700c0e501c40502c00c8800d514103849413419000059072902e0b16110410000050350940a41c1c44214041e295004110130444001800d805480d4880d22010020812184032401040a809007800b08450070200d40c4c0203044800150f4080801c58036140c030070480c0d800624046d10156004841d80f0011420760500048280c4903030f10071002072080e544d80d4001e00289018011000750044829055a40000c88086420003188009498200190b410ba540d0034900307420451106001d800020300042403021401030400600820300d003452400384559a182c4a5120b501c10140f948500800d0aa0320601c082c17048400622006203000304850300d41e5501c1d4002c1d40141c070084045101040001104260004400c0c41650010081031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 19716822 1250 19715572 19715581
    0x207210b0f0604060902030a0b010201051005420705071406031303020c030303010f0303110109110108041e080d0b03010c050301060c050a05070e040311010501050603060409050a15050a140f 83
    0x1584074102a0100da407150311080c0100f11303c809480610720551840c034000c5905c090798000682103400180080180c143e0740300050100392191002840f0440308068a503500050f641548200b020114030710501c00580788103d04004000400545601402001502c910641e10b001d00d91b441807031006110340280007407001800e02ea03100c00300b0302601402401603621a00c0c0e02c10010b401c540c400d030412004040340c44410b00625504c402c7c5044140c0c43c2c0b40081144035a29180e1141c0054002000e80c100100800080e042000708078690404100031028a50031402500c2d00c0c0000d50440f034601450039241201ca8500c0345414001e006048055860b140d1841c1d0800d0f508a4241e00d072030000303032010701c951011000000d03420420301005045c420b0003c00d10382414170b00280215001d00303400e06280c1c1808018003003651030b24203ca81000c0c1c11140000d4000c1146015400c01c159000040d00c40c1d030442c240ca2210792419000648a4104001c00300700f46071102c0d80820340c03841c0a032580700000301c0070400103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 19718072 1250 19716822 19716841
    0x70c03030b061308030301060f030504050705040b120a0809120a0201080c13050a030f020102010e07030b160903061811040c050706021b06040318050f0102060403180f03030207210b 79
    0x1c00e00301d80508a2440e00c05140d07040d100d0420030742e008100c59400000104000b5501c407100500401551405000301d0605445d60b0307a880006000302c0380715036030b101a40c40056860f040b081c6020004482920960042e42c1414116600030281d20350003002c0c1440f502d01200c0000c940820020360507115070304151140d6100c28a960044031441c0e60401c2e1131b48004c20141ea4207a02d0b00e00651042d2060360100c000742c400242900ea00300c4941c0510b0388580014000034582810055014102d200818606400810100c2d101c078002e0380080c00c114a45540b00100c40f040c070342c1d00303104035018141c14485640c2d180203010031207541e0891900001d13018441800002e615400410411030a019044601403680001c2e50800130185c1d0210301003060900820044a070b001921350040408840c652608120240080d4407001700410090804c52590540e2141c2d0303c0c60f88002d0060030702c0d4652410b45548134134000c1c2d55030099005092203a01c0c5507081e40d0344588040308118081e94002551009a120013016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 19719322 1250 19718072 19718081
    0x19030f080a0209041a0a060314040b090c04050711060105060f12060a0b190e060306010c020108040212010c09031a01050a05060705010608060a020414090106020d1214090a031403070c0303 82
    0x603103400310380802c0f65192030303911401804e0590160f4a8000d04062002c420006803d4196125206043c28400c01c0c44070000b0002d101c3d507001c1d800101e4601245c1c1c2c0c0e00961810900c026640070f038094500414828511741c400c20750001540d1800844e10b00d66290020000c407405005030404a90b81c0070820f142c2c403031000445040d000f00028102101c540e4a401030001e180c2c10101c0c10000c2d400514881c0c062440d84000c0e445030749001691a2495424003c0000300401c80b00d00e0080e05100c4040086030454840001420401703a01000821a031305610000a04510b95840190b9010403030550f2401019400c444080c1222001072007040f07650b00e458240f01e00750f00f06440035949075595000c00a03c0785403d204003441754030130010050307450703042001031103010318000c4c0c07200c1c05003180100500c061500001d01c08801c10050404090304c820800b074a4016100b071481503010f10708500103006100000062041c1142d10a888004d82c0b00114a183c040500045030040300050601641d50040b038001e910 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 19720572 1250 19719322 19719331
    0xf040b090a0903110a0303050601080106030216031b0609060b0f04020313020d020d080c0a03090b03270109020414040b0112080304031202040b03040528022107080613030219030f08 79
    0x3889a20107102c0f501041c00c1817080030003500070071780700c01c204100d0350390101032030b80904424101107040c2442d480c0c101040e00a20b0740001d00b40540c4604aa100e00804010041c14a9001109103d018850318120b8068040010428080c5041e2003d80c100c51506000343c03132203503c00e00084100020b035a020064106072844c000d83e08480b00201c41c10208103600010900140e600c0d0041108103543c0c80c0090400516074429006240c0c144180700c116400001640c041d62a04417080880c044060612401054921710007580986040e0751102d800c1080d0081070700c2140101d41d444000d030b030b03540c2d107610b42071003c5200206501c1040000400190140c2e885c3d0250b0307844075400505043d1a40040141e950040d1400d5801e9401511a0400d03030700d030b07001d4000c1025440c5030120841c0f1119404a141e090350b01040c0c41361409050200915004100504801008100119156428030401d010a0b03023040e040d0950041c00340091620341000c2007203008189542c15615050320290500040711079402c05003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 19721822 1250 19720572 19720577
    0xb040f0f02130501060206010b180d030504090207030c020f0301060b0a0f0c02092701060503030a03020705010b1009080c100c0201030c18060314130507150318110f040b090a0903 78
    0x101040c02588802070714035a50720030326000090315414010080c3c0f8190f030507400030103000c10810101c01150941c100b090101c08041c0c0b07a0020704074880ca0281c41038000e83d00114201407020942d0002d06a20000038010741e4001c0e600280e00138909001d250a0355864014000c01e00c000304010f01c2518030440f19440244054a0205004080c0da07000542d83c50042c1c0d003c5138280030002d240500342c01d822009070000700441c8000c112803441c00020a40303034000d0728140d40034954007051101c06d00030290004a80340100404640000c003030400c0160440b082406035444611078400c90306454100b61440c401c0f03c140c0f80d21603a84881150f030045010740603840c1c6080411050b1089600609042c0c020380b03015100c00e440c08a94042c0d030340307000d15401e20010301403800b40011540480c041500803901100361901d11420b103920440c0140c094010b49080e2207035484050070820a44280460b002181d0345603481210b0f0f403c001454641000240da900e1008650700c20320744030208032502003d62040c03510901c00d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 19723072 1250 19721822 19721843
    0x60a0908030d050a0f0b0f011214090708101404060e01090203060403110d0e0d060207030504080303090115090c081515071401060f0807030303020a111905070609030b040f 75
    0x20110941580c01440c0b01e00701d501c1d10303078050042003103241c080d5102d522a0094200310105180d000a14000605444241400440341c045010140c854001200d40500c1e024104030908180007601c0ea55491442400c42c02e000c3c85200449610340b900580301108485408441941c44075121140144200042010550b6841c0d031104010f0720144006031080c0d02139101c1c9003244413206c4500741404250001c1e0f00030450741e03c03014000c0743e0320484082c003402c0d040180140c42e000c4030300d4142c8461183d40c1002002c0d10011003002480441500118000400110020001035032400320805841c01d0302c19120100307554000060410034040182e412040e170061624405880c04084901076503c0340d201500c0c2c6403044080c81d11014024005c0310000c140166146134601d2428527281c0d01e55040e0b000040815400045080505100d4481c0d00070054410040d20100c1944a4110511700d06034041280c2502a4000005116000f03018890880350480c0208100c1c1d074665440081c2002448000c6982800d003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 19724322 1250 19723072 19723079
    0x501051b060a05011a09010c0611040f031b0b03150f0310060e0a0e0a1e0c030206160309050102071401050313080c0a06050604180210140c1b1005030105060a09 70
    0x1000341c90301a0502e00c0b800602941841c030011190400301180700c182950030004114103990005141c4000758010400146406041100e80b026204961180407030002d0144040148245030386c1000c142203001c00c800b0055580d9014503a11804200c03001d450442c81d402c0140305a0510110351900d409004054951210321084403408640a60704000c0710b981002c010801407207000d10550301c1c400500401801240032940d00c0400e81c0c228200c044001d0700e40c0390b610381e080103840042c0002455004080c5521601d459010304a19403a092040d4001030852400142c08d50000c2100002d40c3d00c20394110031780b603442c0001515103600141075054200e11410100e404281100d001d0540400034070f000e402604010b06004007612005041c95118915224009000705001c140c201011035040e16074a0300040200410340d0710400503070690340f2100001943c2600e0300b4021958485502c0c1c00d070015524810050107102c6e640041c4400f001c04540200010700407403501c48040d02120004d4600380844546 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 19725572 1250 19724322 19724377
    0x30f03092103180305060103031d0904110102060f0c0405010c0302030c011a0907031104090902011b0302010518030903030f030606130803090907030207020307060e04021303050c0102071e050105 85
    0x40040289001c5062030580c00105680b082651618009034140100800d0850312070756121601848014240143c20b840ba1940c180c04030401455001c0c01024410580340c5418220300224080c8100c5006018050005150111840195000302004400781e800c00742403074010749c0c6681e400c1d00c05409503c000d0100c004404024000c0100d41f0030030310800041c0b00350740818031040c1d100c042c2110081c181040b2160318441c401c001540c085a1105901140341c030b00703500060f1248180d0380d4032400c00b96107030f913181014950150003650184c202e0a4101160452803c0c603203840b806260762540d419002041a450f8900b10840a5600120000c00c1c0305d00d04000c1c03a4201e10110b5007a40884034681002c00c580400b45850100c0c3d541c80841401d055184ca00203a00184d1500c1460080c0d030700780803802071140a26151503065074940301000740c2d0307030b40c8198481c1003c0d503452502d1600c2e00d00511810318003103a00541e050800980075001c22007100c465040100650b03a0b50005090800490341202102031a1203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 19726822 1250 19725572 19725599
    0x5060f09040c05012a030507020d020405100f080c0915040b0d03030507090504020301050d030309031b0c0302030601050f03030301060f0216031505091204090f0204030501060e07030f06030309030f0309 88
    0x6202d084180b5060749082c0000d05018103110541d0005e6030161403480c2a240310030403281a0382c0e41032601c165941440d100280e2030304084003000c4d400618000820280009164156090368081c01c4811000303a501d005007079680051035503080c0c010300c1c990041601c2da10181804c44041d1801400420b2640c14940031403804002c103032041d0006510341c41030081c09900400c0203000b0701400d0307500b94a99030400300400e901d003a02e11b40043c00c05680b0036803801410302c07460440c800e180007150000c00700c02003800c1a00e050407003800140d00ca030151400000b02c503e440c1400000e2840007401660031607103800c2096800c40340030100d070300640c00303034a4210700002600c00300d120280d841200300b58003400340c40030304a04465008000c045294012109a030316a03440b05c043d10101d403602840442c218100303d0f03425001e801254001020743d030070500c01044101510300703024480e02a5513800c00480800e05404e0b42034481e540b2001d40810b0440b6014000300c3c03070466034400381c0c0780642413082d6640e039a10200158039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 19728072 1250 19726822 19726831
    0xb0d06020c1c1416170f04030204050c030112080304030302041517100e160207090609050412140706050c190315090203090606060307021006030f020a090c020a0605060f09 75
    0x3600048464281e040710b000440076141140d01d81800a85043c07000c0d928540b14141884880c1426110040d00b08a00380c10343c00540c24400c52402d48401060000d403806800c18042288524144000910780010140507603041390040c0c081d03d600c020440d117820105900c05030060b410107808100100341e2516000300c44401d401e0a64076a44070031007400d002d51362210064403138481032034a9441041800742c24001c50b41c015115008402c0004030b0004103034a0f02840c1d90080b0702050524600003192442940004d114a00480fa01c40f6240449031040b106007200025201c0d50003424400da0020840d564800381e4041c00d804d090900e4020743c455080869400d4071801303800a034803280100421988801d50358001c01c440c040540c00c40c10001d8820382c882d14000d10407070180b0404000075a14510801010300455540e01040001035120f0805d403036464110f02060340100c0f0290400036402490b842810240304456010780052400383da916005044068801036120b038442411907441d54448420ad40503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 19729322 1250 19728072 19728097
    0x30903020a0506070c060e06150f180c0307090602031c0b06070213050105030f0309090f0c0702060f220308030f04080c010f091707030906050f040f06030b0307080706120b0d0602 78
    0x52072051b24001050302e80395404540690420400d00c90030843c0c0204211110708111545980385a40e00d002c0791a2160001000d29045442010f125066900e1801075018000d17a0b40d808410716141d07602642d03030781300300c119100c0a020a024044213428080d4468a1205070040402e4a81401030b000141c60400a0b085e121070b66988030010405881d08100c05547c25100002540c24002c00c00c0006000040003070581d0415000a000907e0300da1000d01204e0001d83d000301103648580040342c04101540001d001040038003200b01c80a003800c0c40c403c5005084035400a44c1619654402d492903043c00300151040302c4050087c40144d0038950280107044400d040300b88005440313099810304a1080b0003044c014000c03407400f0003010010a60161001341515018202141d84844080b85030889100741d03030003c0340c040c1d46142d0200320503605070000c4500c0c910841c122014152203042c01511002c1030f100b0800840c01c000d095487c41003079900064810240100010b10841e410f40300d030410391740500c4e1040003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 19730572 1250 19729322 19729337
    0xe1f06050a02060708010b07080903010209030604050304090e0601050a0311040b120a1502030105090105100c050a030804050c01020f030405040903020319171005030709020f072406090b060a030903020a050607 91
    0x514650403c00a07031300100c40e00d40700910f175151190074142481083c1c005046180002080003e030749094040f6004841c001e030032221f1514043c240340ea00c07600140a003d01c4076081c00400c04900000144580c1601c0005010308101403859660203208034916014540264a40b82c000c180366580035030320f8401c0410000640300c0400e0902c0c014151b0083c0b400450b03292441440140403a0f02e07464521410340304140d0310003e80c02900e0314144c49c50040d6070401466803083c18420300c2010340c000182809944560b02f12040701070691b00680e15041e20107000c41c1c4981c420310040025180c107400c00c0d60005e000b40140c0b840d081d806a16813820161186551010942000d84c4141d6075811070102e40d4069031003c652a091814100042d44038050313440341044058010a2030044503100100f25218a40c0c0120101c07226000e401d60f040f52982101500c0e103545207003820001e03072400e40c0c0c0900002401c0040c4000d2614a81c0c1d0400c0c0c0080c101701c5000d030114480c80c04150001481084464042c2c0182e403110207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 19731822 1250 19730572 19730587
    0xf040f2d0b0301020712050c0307080304120905030a120f09030503030c030609100e0c0304031209030e0411071a0702070b0a08040611040b0904110c0a03030b040c0e0303040e1f0605 79
    0x8050711004100e041c040da2041081c240400c1c586a42941404010700d0300300d6641841d02d03540780c598002c03400e020303100580c00424030041000000c101c840072209601c8104c20250340c2e50403d911486115809040d400140c000759640c68490181c40c04d2445040c244850f0094490f12902d18513003080303d0140c070701c07400001408400c1c50260400c551010a1a010102d21400c000b0300d0f00460b48007a003801038414000c008141054084c510384c0708202c4c02d8200801a070b01003410010615414844154021840d000a511408640300103e644183d006072000c512805e86981c440b03101d0364000c1100b41140600040400e6803400e200040c008410700c4e0396403030400d06117420803404642d203615802c00c0c94401044208081c0e40b0030400c0e81d40300c4030226000200d404c40e02c14088a244205c180f864068000c0c007081404060b0507610018010a0a840400c0600348450341981e40d00c00c004100d82c0d0681c01400700700500300d40b0030142075010581d00782e0b00402e80707038103840101c0d9801d49070002001b043c008107040c1c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 19733072 1250 19731822 19731911
    0x91e030329061801090506070b0a050a0216080904020c011401060816080c030712050703021e04060503130501020c15041208010b0405010507050705091003050609030304020f040f 78
    0x101110202106504112800740042c94501c210f03400744001c48080d100c518a035138040c9054600410002d80100c1d6206940c2c5480141e04004980c0b02460f07900d031002103040040c051080d81e00d1464580700c28844012142c40d60181a0000c50245910035000c020b100c2450500b03009259824030080405110307541000c2000d040c0c0700c801003440e022503102c1d10307100785000c0d401106682c204035012591556506c2e8a4001c0350951210f155404000d801d020601030f216a0542c005c10740003502c185a5820140e061400500920840c0700f0314001460a10110f0134041d40d411140d40c4051207040018540354107071213028109500800c0070030115109900308414032501c0480205030408a00d0000125030615100081602590160030704011000c070742101007100c100070903005820002e14002262824061000c01030221780011078003400765802180000c0c0f800400d0700d010719801030912505406003402c0c440200901b81075101a95154400301015032940c074108800e442056440310301140024404 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 19734322 1250 19733072 19733111
    0x7020d05030705030a05070c060912020d0302040b0a0302300f06030c01021209061b0105100b07030f1b0b07030e010b010207050a0e090c0a06020d030510050112091e0303 74
    0x48240a41003041246180d44802260352028140100007451340780c0c03410880384120a080028000c501d0041c4510a00a9180302b41b03441000603402c542151140107412800ea018134890805041001c0c055801400d020390041c220212015013588110600c00003a50034059181510380700b044000421300420202c00721080d1f51150050300207040694901e40003d43e502806507030303150b00080c0410000040d40e54141254850a0000d07280d42c604002180362a0003044240d450201040080e940028001d9002068884caa41c00d0384500703d0041e21303008c041c1c0d94880385800d806c04c0c0c50070200c41c40d00001c8004032100d0041040c0c0d41d00098500a0100301d90845c0c1900c2112070656001910400030396460102c282d00b61400c001c04d24145440391070420b442c2c01501d507c003981c032040c07220000c1941d6500042c2c02907045942d95007402503482c0c4c140903007502c4800c3c0c007945001a0082c2c1103000e0b00303591a004001e02034410708050300442c503598551181c0000368001140000c2c0c460409030303c00d0020001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 19735572 1250 19734322 19734343
    0x40b0c090d08090306060d080306041a0a09051503010908120901060906030605040c1703071506030b0705070b0c0906090f01020a0b0a06050910120201120e03040902070b070801030203030d020f0906040e0702 90
    0x170740c3e8810810548031100d07680801801d192182d030300c0d03070320cc071480d0b0320702c1020542c49100151840658646a82c05040944821603010000e402c41c10401441d41c6414050320100ca5000411a841c142100c01d54992010000f4202d06196481c0c000006010100b0700c11030000b0340c0610360001d030078209403411403070811140c0d000e030203109010000b00b034250344040106c50016500445400c5a0b131090000d04010340340d07660015140040c903404009003182c000f001042c54a11443d05401183d407202d100040354003901c0001368000c0781c2840a41c48905200c200d800481e401401255103000075030760b42460800c0211403440d180341e1a00c0c4100b02604004c010a6007281241201c03e45031070803d8035468103000d043c00060f041004400a003515110141d102c00361a80907081603a940e80c2d2101071307100c06544000000c46814002c0d60010b5002c51054038100d0507607038000c0c081c5141644880c4420701940014000c0f04e00880304000c0c0c1080c540da1a4000c1004040500d00c461403890003100c060308040300102c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 19736822 1250 19735572 19735579
    0x5040e010b030304060302070303110c0105010608180717011b0f0f030501031703270610050f03060703050910020301030507050301060812070204110c0d02010f23040b0c090d0809030606 81
    0x141d9403091941d0210a69080d1411441c0040c3c5621aa00301100a4204032180140011000880c0000100190016816216261107010703985d2a202211003540b0009002c00d5444c2d040318406020000d0502c242c0201d0310715820010804104001000c01c0c94012050071030003007046246c806036029001130003401c2035020350804002561641d1140729001e5103a8030007881c151000000150501664450b071109480c204400301401c4c0c0311000d00d036036900d42c240c80c410800f01e5440000900b0b86840c003440c0b0107456002e00640303101c1d100d04906402518000e000c51b9454003804207040d01c003418520280d4001c41c0507000403e0034030700d088141400c443c0140c02140480d0068452014410314142c1200e40070755064400040720000e03561600c0342d60144032150f04050040070900030506605412030506110303208400c21010300014030400541e800c022045030000300c1c500000300450400c42e201076101002c3c02c50189080170150004030001078469040347c0403000481e550001c1d08041241951148040c1d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 19738072 1250 19736822 19736831
    0xa11070902040806130311030309030d060e09030d05040c1502100501090c020d0c021518090105060412030c0f020910030b0a060f03060e0106090203090102040812130519050310020405040e01 83
    0x40e41e1503541c010117050398500c9030704844080500c00c401c2d00c44c0044054050707903200d0414400141c5c495000d0303000c0c02400750070000041071584c1d2041f141400b61003250000d43c9402e0722441a90b024050060058400e81e05c0400000b882c1d03103000a085115440c29400341000706a0700d18108110741041e007160b01c0340c43c070740501b84181c00d4001882180b40d256a040400e00504035200280d0341c032441c940f038110809404100200c00c046a9003c04904070030071901d82074aa82c8507414840c4502841c032400ca0311040f04107040700424020303d01d08903030b10700605d6034940c0c1240540101d401148280c444c40303828a03407240c04000380100040b0080e000006c0a809216444c94148001a0425980000b5001f00e039540d03440840342d0800d6001030001c01311680195181c3c41c080381200d000350040e2007407000501070b2040d1a180c850450301155852825190f01c200001c1c180828002c200516031201516801045004103440c0e84c1080b12401c170704101d010241e84c441c1401d090105941001c501026140e041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 19739322 1250 19738072 19738079
    0xf0f05040b0c0f070611041809120507020609060703050c0f0109050a15020c0601080c1801120803100305010e01020304060605010c0b01090f090c03050705011403101404110a1107090204 81
    0x1008a264000c2e019400041d1a41e54103000c04000344507442d0010803103840e00121242c903690f140302410032611442d1740b6020142e40b800b03841e416038491100050a203480d0718144000341d070081c00074025090000c2d041750304181c042c401007a49580406019404214080f40c4840b11040810941c00e0b2442100001d000c41d0240796141d0f6560840e292004113190140c041c203415011855068603200c09440c0c08079003180d6550f008250b118014483c14500405808006000204d1804000c0d03040365603111500010710010744541c1010303080035004c5018041c0d07000c4000041a42409501c110380000300005940741031030f140001c11244a54800b40c14000f9500030b40c8045a12646802d0440d1015107000c5000100060f0442c0142a6141e000303001404901e0040184280081c5000030740c1c60071389a441c01c00a03c88404a80d42c0011524071010301103441c0c051140e9010601d40c0445014013a2002c0344054001c414012583c0040d00b900700000d140d10701d801030004003080100010300800100314602400c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 19740572 1250 19739322 19739333
    0x90c07080921010915050109140103060209030a0f030305010f050103090302030a03051b16050601050105090a06030b01020102090d060203040614130201140f0f040e060303040e0106030c030b12010f0f0504 89
    0x1c080305a4803600710195141840340e042810500401c0c8100c008101002903803904040600110a0302201070b072078000041440581c600c5102c0310a40e241100d002d03141e00e140d031424003070340c00000d1058050094400000001720500d03030040071117100e40c801290560514890a2045045601c0b1504041c140b0040b1b802003038000c81120a070408601d0302207101d6881c0440e0b402102e000c1490101003e200080b00b164040c0384d030b200805014820410345142d642d07101d004640b0760140d10a43e50344002d40340f038108030081c00795020751102c600c18000035017811104030002c0c04400d1082000d45400b42c0000c10001048040c1c40340020342c103000c591a0300d0354104860096007a01070400000d051200300480c0340c14400750035003030356400364400ea001552001c4407000d404158006115980180203a000450000d20700842980e027500c1600e05007119607071030120101d0145c2280460a400d00d942c40144042d00d4443c80d0105040049942c000b26541c482d05d85003408803803e01c6ca030b12655601c1c0c401440005071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 19741822 1250 19740572 19740577
    0x703090506030603011d030a0306050406032a08060403030c030e06040b160e0301051602070f050607060f0209041b0f0309020904061119020a0b010b03070816030204030503030c030402090c0708 84
    0x10030648500380c0340d6450354013103401007070256001c90b00b4181400c0d0910002800100500700700901c0d40e8140217031a900d00c24001546c43d5400014070303212805620814000001819107040f0b070603031808543c031541e41e42c0c0040c100340b230540c0c05400003a2980b22911aa42e0103014100c480c8000307600900e0030385455140d0007012000600b889038100b0720307801c4282410b80308901d6202c1400c4000e0082040e0f050400101d810040e04040080c0540902100084c080c80c0c440301000c212a03000d0f090600c0c2c20155564100103001c04062079210540c2841480c2051301c482c4502d0800c5030200c4802039003c030703682401502e07906540c00c0c08000c00d0304101c06100162984400c0c1c0340c1241c0c0c0110042075400044001c10762602807200c080c00380301e5010300c0d1882d42a074001004da403030600506040956980f0b880704e01604d13100448802e00411071712004200303880c191a4540700440141e00e00142003507182e5030760303d06652040c0c075400c001c0d110220034001907150010f04a900000258a140c2c80c001160780c5005050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 19743072 1250 19741822 19741829
    0x5091b060a0203040302030106120501140103030203091c05060f010602011503030c0b10051503040c150c020906150f1803150c03070c060e010917090114070203010908040806160203070309 82
    0x10103020804400050003001610083d5034004e000388041603c84541d600b244a8020080c4c0300b643c06d1131034840c03407403051920240c16241c040d809940392034404003e00c0040d8540c032042c4000d40c8c010321104404a4070174442c86d801200c082810208951400c2c030000d0031345041c0c10080c14450401c80040000940181403191140da1240d500080741d980c4184d8068642a294044d0b031301b02c20841c01d028003084001e0000d510a078882d58006500d00e0700c034a1b8402d50340881e00c0705100800c10101d509409480c1c03424090341d01c100d0041000954007560b0000e4011a000301c1c081c108618008a00c800b81d00b002c69442c40042b201c00e6000707041c070300c1000a010111090181828100c01c2000010a8441d48510b4000c2d4000c0d400c64001d001104050495074002c1c8010746050b5280460480308618050b41c102c103d419000e0140e41d070348141408803500c0c0111350301907442280e0541d030342c0c6003050000b02908041c00c02403040d030b409042d103481d1000160050803ca10546030454004010f440c000035008052801038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 19744322 1250 19743072 19743079
    0x12070b04060b04051303081506030402041d030d0603030801140a1502010b0307030f030806012d050909010303030603020109060206010b0d020f0903070b0406201203070c0f030c02010305091b 83
    0x95490300c1c2006002407402e81e0880790460300b050100f0480e12a4401440034061003541d5091044d55402c000e141041600351080768420707001c0001c0f5000d0710740f6030000c030000328007517404000034110b03c5440c40c03a6030b009005c07000d243c6403504001c00505801020060040c01d020310380b41c0d01c101034500054080c4200340901005145800c100f9110341f40300b54014045440042e084503145526420240001c03580b0410403400980c0050005509506c654904803002c840d02045003070450030281c00800800700941410100b103030038400d040d040d07500c0c8080d0500071030080d20001260b6045000050034030170113030490003d40d48241c004004038800102200c07000110110010384449404480e91403500c07801c0e4a04d030341842800030101d41e9807019002403080300c040d42c41c0c25500d507403a0380f80c0310042c500c1d00e00001000c0c0c00c46003070303941034003a44c0c0000c5a0110040c0303000881907103d17580d14603020384403420030350018000080320011941c041c40b4458020035103000808007180400c0d16501404a42d41d4034600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 19745572 1250 19744322 19744343
    0xc0a0803041704031a070203070f031d0d06020901030b090f0103020d150e070906090e060a020304030509090921030f15040608010f0b040c0509030d0c0515012301021207 74
    0x2845652442030380400b1042400c1640c43e542c0c5e081c4510002d000402c0040b4484040001c602c05500000886100b103510200411020903651400d603024150103409500d0388903540300e4140d8070f41da5051491001d5214400050701c81000718001011a2503002200740280030150501820910b5401e4480c112541201c070001c2c117109034a80324030120320301d10710010801d08000342100080000724000c0f01780d903c0c454080002c02e948034007060640c1c204c0712003885150442d4001c51a1234405400440c1d103d8080c0c1440d52034100030002144003888100c9141d280394102284d80c40082c058185d052040d100040422419400c020b541c44590780c401424030034441c0c20000102d800d54649802070350050440070002c000342c00c440701c40b00028011034595148102d141ca6410140b66014205503040c526020300242100c4011240640b1003030300f440ba0035a80d500c2080070a03030350035103454889406440c8240c80c103d00c1078134408039a501d01c01000c600d84d0641d000081c160f00c5641805040e140616008902c602 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 19746822 1250 19745572 19745581
    0x6060a15020a060203040b0a1407050a0806060c0a0b0106030606140307030903020f0d0905030c030706020606010503041e060b010806150306011b0512030103050706020106060905040209030c0310060503010f020c0a0803 95
    0x28a0a030310b03a200141114004000c0206119000304602e2060034003100a100d403803001c5d041c43c10300900413214100410005d002c030340c008902c6000c940e680031401816862400c044024620301c0d01e01d000701d0480c0c03440c81131001400102d07458040d500c002c0910b0300704015010340c1c08010800740e0000030420810150782c1e0103803c040c940700b0455184d5110702001a40c68440350aa0b0041c0710005a0207814001d10408801e0441400d0000b400c20440e035403540681200d803182001118585e00290040e14044e00d80741703c501d40e0369160520440d10510441c070006860642d90b00150005034000d000d103205605030901c050010404804807903102c03c1c2460811880906000d610034044042840501188107915100f15030000704030085050b40e001e9421910b110740d40e59000c03400c0e1680c41c01131a0014548500070441814580c0162034000c000906990b1004a0040800d26150900044d1820305440e1402000903040a105005414100b0841035140070000e0350010340d00c09008600409113140000082c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 19748072 1250 19746822 19746827
    0x30b0403140c0712050102130906060306050118030204050403020f16050108061e01050a0908030409020c010b270a020403150b0406060311070b04050304030206070311101802011110020f040e0906060a15 88
    0x1907868500080c100c681c23040e280c0c403040000740b88030f00640d00800e140c40d1000c65150b00440740c800b403d9192a8030a400b40f0b0a40d42030001030309010303100300d09600c94a48490002481070141c0e148034006100d100094912b05400180344a00160015000d52500b05003044441034407099980300300c000782029a6100600002180c00c007545600108584c00003003004500030f08035400600388162041c00a02154289a04201c1a01c100103212000345050241e50b0014140d2100c07807076031019084d40014142952911001441030005a24441a681e1000061102d240038031a0380c0151401d071800b00310340145030b82075117064410044040c11401e0b003c0002020001d0401c102d50207550301034000d0391154560b28003c0c003036050041000c100c0b4081c5039407904568074244110201000303038840c020b1858115030019942c20724200291411409144101d0040c02c1c0a40014945203000000301a56145081020003071030101800415243d0400c0c0140040d6980d45000d40090352503803c00d1a10000c0141d905 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 19749322 1250 19748072 19748077
    0x70e01020303180717060a05060f0306011203021006080f060906100608060f060406120501080607080103020607030903051207061d0303010b0c0a020306150405070806130f060f030b0403140c0712050102 88
    0x18510341400c00200140c600c07006c29010f0059142410501c020f85401d01002804010320381c803035400d6401003004004009446441540d500e004e401611800010440c41c501510768540002045078010b4410b060900b03001c00c48281c0c0b02405001425817800c11104c006044100f43c441d0f01c007049440c0c4045001d680e64182140c03a040c400400c6a90340702e5681001800304d46503041982d04880c0f0f00400050f203118040707a0709204039026504c0c08c003160300b907908010355504a80b000380c0812003448400b200203081000303401d44013400044115200d42144c60310130250340c100400307150101c0641e4581c009a4100006590640b80740001c41034a40d00200070f0a880c010003c1070195244c0310f03001c05c0c0039803c40c84403081090b4807400d039030900c50b954a1150640c1c0440003034840b81d40280121807441090f0901340d0080300d405865440216800b69215007400b043c0a0740e401c2580c0740000d4400748020980c00412445e46040035020081c00c0c03401600d940d42d00c1f071489114459142c4402d1400b002000001e604 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 19750572 1250 19749322 19749329
    0x1005091e03010e0d0206100317030a0f0603050f010b031c050a021c0801090c0c0506040605061903050c010305060d030905090c0d020a090801050c07020d02100c080f07030206070e010203031807 84
    0xc001540f003011150b60f60340704041d0080e01600550780440d921041000441c0c0607207030440144034130792030003000c140d0307066000030880441660740300e0725420741c03007d50b0160100440c02900100340702000405404d003140c92100100b0300c654007034480e00c9500e0405c18103c01041c0014100b148c2c883d0305136081641010041600304110030000c80480c180c0307079001201c0b641a6610303110100304030f80744200d0907150950f0b06600904a9408200050300040c4141c024982c02003000d0302170445081800400c1c04440029082101c050b0070081c034101d043c2d42c3c18444c00703174044411288071104009a4031b000e020314045024181c080c0000800140410380303c02c049804800e4071510841d500e4001c506e004009030402d00804181b0750070702c1c01107800e90a08506880b40c082d00282000b60b424199420000307000001000e84007408081c0312508003190f00d080240208000d038405041d5203881ca8a0000d0410b0300c0100030400380100441d19131890b9900100740c0b80d0000a21008807403108a41899518094061b030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 19751822 1250 19750572 19750579
    0x3050c0f0f030f0718020304030203091002010209270604020304021c03090e070c0311010515010c0606030803010314011b0c0305090d0b01080114090a030f0f031112151005091e 77
    0x288504052040019541c04555040320b85030401c0c03103001d82c007500340d110948e409801a40184500d040d0f034035083c14180381c11083d5000051400c4403000c04191910000404800100c10400e921149006010709299108008403801c40c43c514250b0300007803006400039407001c28140180d41210400d8051007158001e030216031101c1d410b61030608070050aa0b40415400c0740001d00d00e49034009080da05000d0039001e03407658000b007810324515100444070504c8400c07003a01c1c0350b82c41d0310000000c04c51710001580694041c00030150790358050841a8255446603104440150441d03c00094032980045001040d55052600c90f03507800041000491380000c4131005024111000c00000320040154808001d1b0b0380003091480c810394a080003d5100c440106029004c02c02007000d1000b9540b0507000d10020822a0600040e4201000740010207034000c01000030342d882104050084079508560b02c42800301c01200c1c40c2042e000403039401007040c0a80348149005410000c07004d1000502c13400e040070402c038040d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 19753072 1250 19751822 19751833
    0x608010f0204060e04050723070602042d0302090c030405010b09010e091603050d080702071802090108010503030a09050f0a0902030901050114010203040b0a120612030e040507050403050c0f0f03 85
    0x8040e0402544588540008a81c40c840c95103590308080c0034092242850341c40b07140f90020b0a05402e220300c8146200340f1468401000800300080051000d8005840401407503909059000010403000c1e59016544100d140f10800800050366403005480c0c1c84070340841c0d0562240c8413403921501612544a03416030002c0c401c4c00218210020381c0380f140c400c4040c50100c4096600c007640704441f03d00240000b40c402e800508980002e5030041600ea600300d00e852044510156840794070030300e011241101e1480c904d4001864000a603440703100c050250200b00d020f1450040f075590080c04980042c82028041d4400c03200300026640c0d14019000248400c907000d6589182c00c0490f14000c010034066440100d0004892240c554030020030340e800d80e05040583d40ca0000c0051301510314045141e01c80d0b08040d201e0b18085041e50b5a40840c5001c4c0b0311030707181e4680d0303c80b80c0000c020503a00014042c2003088811320080011401c000b40c0300d110b0940030344400c000116244082048100031126003034144c0f10b10b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 19754322 1250 19753072 19753091
    0x6010e040b100c02011d010909020a0e0306040f0c0f060806010e060c010606080105090c03010317070507030c03080c0d030c0e04020f090901030f060c0c020904060b0307180b010306050f03060712060801 88
    0x322502070107051003603848611442c02c4040d00f8000b980b1b1604440d00140703401d1420b00501140e0b40c001c0400d18a1414400c500303104420020346010f07402c031030071501512480030410803c19031046000c06444001c004600072418840d004009510050000317040040c1c03840b0301c130106c0d2618801c441034616510028081c2544414014108400c20702c03901c5d010302a5480021000c104100980341605d50105081d10103d10405c01c0c050035800c0f400050760580281c0e60000001030a00419070019482154820f0320340480c110300c50300f402c44500901d02458148074417407a00a506c0030044d00707503210450b0016243c42032003150310798900659454031b0f000900c01001006000144070210615842203a040c0100c0003244011101d1401c2214025002003c41c4040340c0042c52a0708203040350706018045820704c0e5034401d00d00300da902c0111144082d680d65414200000d51b80350046402420f015075400c010043c0c01004282d60356001041e0380100801124944c0b10712308150000402091b080b0001d0111406 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 19755572 1250 19754322 19754327
    0xd050424080c16051b0f09130f080c061504050603060603060601030c0201020d0e010e060a110723010c030f0c0903050d030c02030f070614060103051009050604090b100e06120606010e040b10 83
    0x2074440451046c01d10b1408001c0b1880c0140380c061241002c02d01130102804942d513070141c8a10030031000c0710080024826202884400c0085072320034950b04a000740c4280c80d4500b40300485070050250381c000d0b0405000c000741a14000f80c000e80207102840c00003802c442c50745c0304a0081c080d10380094007160400c25800d1030240c054000c00c02d129543ca041e41d050341c0340c90500a0031541c4103030360408942c8007401684085803084101e812003403075000d08001c64040031078000d402c40303550029a1020950751040796246903914800ca800711545070800d00102130468031241d82c1d8082c517a4100d820151505141c3d5400380c800d00075a0850300310600c20a4a500c0d0a181c814040d01100150400902090300000c88a40c4603014030744c00340c0455920025051b06150002e8050b10380117000503000f0f0f8541310084d00007442005164070821402c4890842c2e107040c8000d00c000803901804d040e00c140115000080204d0b4046241d80e00031b88242402d680c140d000308080b4003d0441b0716a1640d201c40b445a000c10387d00d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 19756822 1250 19755572 19755613
    0x4050c0903010c020f0a060209060408150405100603050309060702040603020d0503180a03020d0b0702070b040905100602031312020d0f0501020d05090304080316020f030d050424080c1605 82
    0x314100c00030f21007500c800c0c00407a61a81c4103042e003049a4808404840485c481d98004c003038000020340160306d42915010941e141c0085000440e81403458501000140038061021035410690300d10103108851454890990740c1c00b580101c80c2c0b1070000021148210b5070760303511240007543c0c0600303070000c107040d241400b5803241c0190801e80c901c0c031100c800d0780c50a0300c0c3c40c0d100d003000c1c5c07a8000c1c04076401640750f40314080700c1e5800501980c10743c0704400010540207042001b0700020140301401040e00e00e0002c03c01d03c03207000d07258850b01c1998070030300041201503c9481d81009440c8411640c1c18500301c9400025000500c8800180c41c1c42c900d40c2d441028040190002c2c000d030b0400000901041c0c031450195a074030312582c441e41d01c6a81044c003650700403180c402894110355000a0150388241040000079080102010b03170040442c0380090100102e80c1c4086410b80c10904002c2094542c4921041c00381114800030035140b0014000240300c3e541c00444501c0248071070b041000c9441d080009401e00d801b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 19758072 1250 19756822 19756837
    0x302090f0a0506010305070c0305031906120302070b0a090308070314070303020c0d0207180b010507050d050418180f0213060611070506070507060c03111203060906060724090204050c 80
    0x2030b414400020555406409668001d000d5036991040110072910100d84503000681620301c1c11101c088c0c19410303074040f0b0250b42c0140900f60200000d445075442c0103440c10a256201c002004028000c8080340c0b908821750508483e080744c030f4180d541c3c02510341116400c40440c00f0105c0044042a2102850b90503030242c00c40c01500411151421000d007010b030f03076a019512540001c201013407884c1504400300c1d04580480070042c140315040c610329a03211410000a603582a002030070104007001041b407041c00e041c6510a4100040000b0584085841000c10708164080c0c070545005e04d0275411511031a0b40c6516072100700004014003515000018540d002c16000c1340300c24440c84201158030711b04070303088030350283e84030300105904d80c80c1c0304050340c00d0b034150300003075050080d1803031081c41c0380505100306152080070340c1c4410740c3c0b0310b0554100440070801500460080100384007400028401034010f40c105c44406501951410804004101400f18044000d411604160034008940b48820281185 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 19759322 1250 19758072 19758091
    0x120203070806041a33040305150106090b0708070215071104060819062a0801090c030209060306010e040e030d0e0123010308090a030606060e150405010504140a0302090f 74
    0x43c141d00360860f00780b040809541c2c1d64442c0a00c482980c6454558a85d01d10f5000b0301c41084203078555100d1305004035000b030b40c001eaa03036401c103004401c0f16060602d8200d0250115007805c00f070550070008032200364042c1d01002000e00000040a5007950303108c0d0341402a02100c40d282681da414680741c8002e58000a100403030041d0b0400d41c01083d081c1d03020580b140c640b440010f8080c1041c845456030000f400040b131404406a4041d1450208806c0c8215800c8024100751100141545400502002c40e400d944000d020580305201342c0403180c0d0f400041b2a003002d02441d03d55036026018000a0050440d15090401407000152005203100c9607040780500f840d03000001c00c6101d0309180d0034101c1d0010782d00d00c030701c544000700c005100088084000c1c1061800180420071125141e45e90b0804803201c40d044400840d40804680615180c9001c260612403500d03650f560400d441d00001a003940558029401c0b4441d410041d03104a4070341888403002903400501262150a24074541a41184190f134507000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 19760572 1250 19759322 19759331
    0x509010b10030c2a02040c02030a0206090c0a090b0109150207050307090510030201080411030d0c02130c0203030604090809040501030602030106120504030c03050c0a0203250e0c030606070312020307080604 90
    0x214042c1c402d800c00d110703d81d221400c040040100301c698000d00c4c0a0038040480c00003040002684840c42114081299074000b590b0740d41c01100041d240000050210440341e05c12100c2000b15150040d40c201113980d44000802d0701005900144c64011654000c050b490303042c01c2c44d0104d10346d2700042000403035030141d081e40c409036154a8104103954003110740c0112081e4003c4100015480b40312580d9105000341c0c282104034011000003410303c10401e0f188000a0409000031040d468024105031486030303540c204024000c1d42d5100651203000040825205035540c42e00803003030003c0ca0040310740003440200200265038491600300d00942080c00341d0340000c0c41440c072100d089481c6125060107a9096161401291147c0e541202c44d41c0c4081080b52890048507840b50042e00c04102040c0c44600c0039044454103500c01e0b07401c83c152501c5600900c00c0c03514003420710004070000701c03c40e0341010341a03e10542c0c41f1600c1c103055405071440226000050710020400002640c0600017a00900c4122070a10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 19761822 1250 19760572 19760599
    0x90d120209030a0b09030f040915050d15050903070503220602031c050408090d0b0403080606040f0b070215031003051506090a1a0d0501090c0602010504030807030e030d0509010b 78
    0x10100d001d0700600980580c00f1001c0c0340041245004a280c0c050244800c49186c00d036441e44284440e00300d80c1c020245c50b600c4001102066480f0000c82c401713801e003540c0400c8241100d07180d9201000d00c20000c6400342d0758500100710100403d00071149a26040749c06c5903547c008a2194901c6003210719007101686c090700c500450b1a41c408002c0302d510311000189092102c601c1c200c102d008050250080301c00700030030480e643d00f9440c0c45440c0c5258a0048800e000545414240070701039100041c101d0303100710340401c02400581d54003041d540c2911806241c0d00c1e100c040c02e202107034102130b0f00c440b0300409032008010030a852125100400580384a0340568028140115103012030b054144c0c0c455610000640000c3d1040032135601050003100003000c014642003186000c0348107207054160960340c594403181d211082c82000400c030801802d503440200304a10b0f00383c07401041110050021402c150311403034044400c080c104244c85150b002c84508000d14144054503d0082116600b502c0c054510195940d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 19763072 1250 19761822 19761857
    0x120a061d041203060510030f0b04020906120901020909040b01031101020303010b1b0106090216110303030105090619050301060b0a02010c11030301060f0207091404051b030c010807020a0b090d 84
    0x2041040d500011400d06031181d95810402d85009110141050f56803100040e440c1d0340c1040192030341c60315407030019440c40b2560029050701c0c90602101d002e5401084081126142e41003102c00c61170711040001425298102201c0c0648101c8008543c007a0241c0107010a01c0090b480744c0c0c1c1201d2042034451101c40e400401661240800d100781c0481010601103804090f80c290100c1008030452000002d200d600ca00040f0201e8014588500040001c041144c040252130084290b40340d03011001542958906400100c422034010615405001c40749a0540d43c0021032401ca0040c1c41c004000f484401d0b202e10489606400c4083c000c03005600780041003101d64020b0004102000c15400514910707801c203541607642e03141c2002890704612684500240c1c0710814496251a90f41e0450a450305061a0511501e070040e14109125810200078003400da584c2e0025044203800001e00382044142e460341e406038100084510050314122564082203e6032401160b0311601191540307610310070510789000e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 19764322 1250 19763072 19763099
    0x17010603021f021507050702100e04050906090c010306081902060d05070509040b0607020108040210050c03030c09010e09090604020415030b0703090c14060904050411030706090602010515010c150b06120a06 90
    0x4040215070204003000143c10250fa650110740b089d42440810119480e02080c212041100e03c1c2d00c1e10b4004c231040c408000818044a00c100b0750929003400b52034140b18207103480745001e504186070b90104520034011501d0b03e1040d50b105011441041019280848014000d54010804144154944198040c1f40c2c90101d068907406da0701a502d108480d40d5035030034040a1040804c080301440028001c0d004941402c00c010f40c4600358010704a03440358034000000d005240384070200c5d07109520031410030146540000350154001c2d0101c0b00820110714a90100700c000c011600041d1159030f40204122005405800a1800503c900760051810f552212483c9402d910300c1480d40c0e0020003000b8404451a180d044590070034007440b4003100c0c0317100010010b85003023505d911840110311202c6040101580a101c1c550313110b00501c7c0040e22094a010008000c03a4200f28000e09005000c00d40456a94440c0d100c011301181c040c0105607078490740401c22101240445181c100142481000300c1c40c085004070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 19765572 1250 19764322 19764331
    0xc0901030b06040c0e030d03090c1a190e1206040c0503061005040f0b0a030f0c08010c09030f0c050402041e0b040302030622080d060311030705060417010603021f0215 73
    0x1000740254885100700000f80098001800402ca1118800485550240034a19250381182c4002030483c40501c0d00d28024a030350303401032081e8040301654103a000315100458294481204400c0701c0c2c00c003860760545002d9500d004103038102029080040011400140f0345000714014040c00c940c40b517130b44040656030601100e03805004140f00d10308015604180d0081e130351030070350604042034030640d05000c2620f03001140d00584d410f81c03d01041e141401040420700001d0151500244600802c400c8080c0942a0511000f0f140c00c00c0d005004042c0606024000c018140050095680c3c82e41c40030b041c985291244007080c0491712004002640c9080f590444003101d82c043c0203401d03035582d296596800c074200145802c1100b45c80440c070030001842d2100629440030341c40300004070b103421401c2242c50b004110782854040d500110342032245a071071005075012500b4640030100c440a4500c000f41c0500a1070788000d40069000b8402a1801050320a641c840840399003100c0d1045000c4002103025581035a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 19766822 1250 19765572 19765583
    0x9040c1d010e1f1e0302060a170a060509060603040305070c151d03100207080408010203010305060703140601020a061508030309030a17150402070309031208010806060a0305030d0b01021c020606030c090103 90
    0x441044188082d2004c0078001011408181080e170384d0340c022404640c014204c800000d02e0010110070308a1180c440c00380c014103003840c10001542002c011035a032800142c0b54a110b0300d404400141050320540895140300c0c0d01c402e10b0719142e9a00d56000d60a04c080c0c02502d0082a04502ca000800158401521480c0c07801001001c05503050b06140d802540006010f036404c40c01000042001c0000740011402940324030b0040c08035280c4090000c04582074104203441200b02c50091020750381e800603842007510f40181001810301e0601180541f04d00d0140c0c07041c03203140004030411205410100c007030036035280c00e41c4030307080701038505a41d81c0c003182011910b4031501c2082c0c1000300710500705940941401031103030030002c1c100741d100d8a4407a804c411090b429070006802038014008208240802074000d20b042e0350f020b03001411503548540744d0240c81048404240e49414081041e1710800c10662003001142440b000040d0b4494025120321080364954040c5c4100141034415040140519040380e8108 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 19768072 1250 19766822 19766881
    0x70e0607150504020a030f03020706030b040204080319020f0d0503180303010803071518150c0e0609060309160608071106010303050a030b03070b0309010209040501120305070209040c1d010e 83
    0x103072414008010280c010f81e0407440c29070021000951091220440718000d070010500149464801410340365141c1c00f1900403401030008006000d000429544889030150004c61940c00c00e50080380f4040501e010300131240304120110300c003643c1001c000c602844280c511140c10030701e401c000a6503480b084c4541e001590082001c44007040104002d40c231405500407010980d001e40359500800d80144510564501d40012400a40100e0314450702d40050100c2c10035651000b800d0001a90754041c0d14003841c0a20000000030b0301c4c4100500003041c01d1b42d030640304c0d07040c4c00d41c0341d03c80100301c0038084982c100850700c0300f99071403000c2c44d0014410b41243c3e450707507900307181c012141401c4015040c42c10440e030301880b030440d011801a030481e000e50302c1080a48001a00d6221510800c0141c89041e4041095104000325600100740d00004440501d5010364107844262501c1c5001b040c204113a502000b4a00e1b415401c80d250304081e02d80c600d04807801c000c155441500c802c0310004050a035014060988043d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 19769322 1250 19768072 19768103
    0x30b04020c0a031b06050a06051e03060601030209300d080903040303120209030714010210021303020d0305040e040f020906121f020903070902070303050f1005040207060209030114070e0607 83
    0x84d0708495000030b4807200654100556907a20016180305903100a84162141001d01c0141000708084620160300c02d0304429400c241170100e07484443c0504250b04140e00000c4050080c0c45500504540f41c0041c1c50487c20126080030000c11403109108559142c09003c0c0f6060905219110943c054483c1c140a14074203807450b902542c042d0000d4411802c415001c1c03042c28016070701402040700915103814080b00160101000904081c481c0105801aa106211160505204114070800d49070b055070345172080a942e0034203a400740610740c081c100e0040f51004100800000810600d5214404e5442640c151a802d0802c907600e0070004d000000745d4810f42d00490518040c051030345803220031a00061902500002103800c01e025900440388954000409404042d85480791640c4492100c4a918030b90628290300300e0348040902c50a40309507004a4500140b1840354125503400000500070003181e902d13005422003a041c02c58007100840c64032921043c403803e000b0112000345600aa6080300c0007071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 19770572 1250 19769322 19769327
    0x50414040c0b09010324080d0f020303040f0212030307110c0a060503060f01110f010510060801050307060503072a02090106030509150903040305010608100e01020406090b0d0b060d0903030b04020c0a03 88
    0x14050f070038101a1102220002e8132000610101c2c204100c4a0032001d0700e05007007910349401704034560030b41003008420f031000d030441e804400c0d250025442049500d15214034000980c1d0380b850816400502e01000050000305070300a04a0060360f1752007401c0da410103080000304030b5841518841d00000c11003c00004802c2e2800c80f6050204881c1414030254040c60325104514006004007481081d0b036480f01071041300303100030b003a400051030390b440d1030180c5d13604103800f0a44446e281d1056509008021001c924800d009611065004d40c01a03450351614403a80c00c1d0b12003180c4020001d90103041c01c0c00010800718440d000c2c01e807090040038010401f90074001155026028010885403c0d80410701c07010001070000e00a10f0001d09030000102454141d045000c0708032918516004000d80c030400003080b9640e0440300800072250070040d9030340c5881141c3c5068000e0701c030132608160b01c01c1d4000380c0e044540710281c1c060f20b1054003030f54040014000754002d2008900c1419040c00e81540160700d00c500007032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 19771822 1250 19770572 19770577
    0x6050f130e0a0506070c020a090b0d0206030a0e0d0c02010809121e0705010f020301050306150d0308060d0f0b011a04080c0907050d0213050f1012020306010203070c030507050414040c0b 81
    0x15080c2220010b44481e03c507a0b040c00e10960340c07580003030100320525056140408a00000e0100800b04101c0c806004000031200703120440028000c541c00b20006603001d80300d501510b441c480740801d41c4c0c13046c1c10301d0400808841d203100c7c080b80402d1849010400081c800208016410000ca04032483c01555100b0702d18401d403401c0145407904400c21854000800078010300d07070a1801d440c40507849504210805003414802030031034800d14220b200002da07990f03485003240169074060030032520b5600c48a010403112503446802819200107010460100b00a00e6100f0707040f116080c001d010b1a0428100b4480e1611440c4100d00483d44032030038200790351600015880c0c00000b903003015464920380303490700402d0341c01c110015141101071040070803050520780c1070f0308402c00c02140c805c0942104860040e0200c5030030600302c0c003816800f100007001039000f082150850382d08028039120142d541c1c41c050750346c2c0001d4000c6500503401c0c120040d0250505a8556000b079501c003100c0310105040403a04081038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 19773072 1250 19771822 19771841
    0x50a050708010b0f0906160b060102060405030702010305180604050601360203060f13020408070902250c23040e0102120703090201050706180228060507021503010b07030306050f13 79
    0x400300700c80702d05c2e036130340d48024404640b29000680010361582450405981c000380f941d0b06540040d8104000280080110342c103050f824200019a5100d00d804240c00500d008039814440c42900d0030b210500c0b4000a02d58100d0b062002008149030401900668001c020320035440f000c265003404c2c2c1d075800000d03005150302c45030280c1101c591b0741c0100300040c000040113100d0301040340d0014007071028003400e10481c40075000d101c5041d40342c01c003c051100500f0303200384050200c0c1c82050300520100212841200c009000c1204440111a13500748a9402c3d05041c2e068035104510740440703007034014011700942e6050700030b404242c0d0642d03586403025400352501540490403c20700300010000101c05220300c0780201d070829039518500342944180819020b80c5420a50702400721f40c18031081012030208082951854a03059031210214030200d9200c404040d02034031009004800803a000050710003a080b8503002e56003e004e200c0c0e035003041c8825040544c2c002034014103642d500b449500715503041020700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 19774322 1250 19773072 19773097
    0xf03100e0111040315060501030b090604020703030b03030a03290108010312020a050703080304021e03060105040b060f040311030d090f06050a050909010b040501030f0b060a031104030606080307020103050a050708010b 95
    0x10410458840b100c6030744241c03c100c0303e07000d000980850000031442260003800003800c0400100c0c4544000982001001b8070080c40b4540001c3c180d001c0600c82d42210740d54240280c2201c0c3c039040c1c2c006000e00500070001094503200b008100c42090701a00b031600206503041a1280c0102e6400c54841601022984080d1019845071a04920004e90108a91401035009181c241d031242807620401c41c0d00c0e440821410f1190100e00396518003a6004183d0604403502100d00048141202d404604a40540301c545610701c81c0214001041c003140000c0310000100407015500858001c03c03042d01c9a208070b01030420400e02003070041c01a140180020401000d1906200c2d04290350700e4005078242c10240c0200305051000724040005507014090712502401014052011000100115920340110701c03842c020184c907000d00b058010b4008044402958001e801804100c0d02c85030b0042e6030350b20410040340000e281c8000907a001003940300b054000c2401d942c55001c16464400c0e0002a6080054110711 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 19775572 1250 19774322 19774331
    0xf0b040c0e180c0f071b09020711091e06040906020f04050405061008040215090d120306050301020c0a0b150d1a0a0506012304090e011d010b03060103060203090703060e0105040b060f03100e01 84
    0x9820f500ca15910040141e03131002359030f0328914902000218110807900b8010351015040c000000c2c6c02170840b40d560070300031810341c0e0290380d914009000342c0345110001c0c010038400240c071a10040001c000b402550400d44040c08540c43d40301c2030010b442003516001000484a401040042c6000301d891942e6011501c0f0080c2012000d81c0014540840c1c40310031188100340302d111141058050003494001c0c441140210305090064600a450b10404100100b000024600280b05200d820400c15025034002d840c404003540c05140085140d400d000c181308488040707a000851a41a0f401862b10504043e5113082088041c140d84c403925003842c901c2c6e810185018071021403125907c0c40381070010f9201900100d81c60b2020342421030b00004440c0c568000b42d0501d041e0307a085440004009046036404800141c8e242e84031248242452003980009040500b04040d40d152258150031150140e406200c05001944410303041010240c0300186580e015004120140c0340c0342403550061038400141000883e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 19776822 1250 19775572 19775603
    0x703090b0f0d0c1407060e071e29040909050a0501180c090603170c01060803030c120a06050112021803060108070f0b030c04090f0b040c0e180c0f07 65
    0x2031168029003018100d5060104101460200502650340d03030b0305482c1041d0707848800703000c01055203101d03c1c80050724190321007041140503802003282030002c01510758040c84114480304960343e280e50500c1000d071160824030642d221910090030401d6605450020a468546004055030240c0780b4a03409a5040c012201e601c0c0102d5000e00641000351240700080700d03244a01e10380550940c2d002d82203688e502d442c00000b48000307102c0c1d58901c0400c0203c200101c2c2c03241d0a40d03007424003600342c54000c00050300020050044c2c829510014046629241100ca0329580d40e428a41080b03402601c00c0e240080d1032440c1c0084411a07a60050041c0c05c0340c03080350111403451001180c0341110a83c044800c0b54007200c401c101c2307030298500441c050000145c2141c13860800d0114000359008602600b820151344410301c1e003001603d076000809991014000b4447c00241420142030527250000444c020014240802540b101615425109500a00c6940d0070255281d1401d006a000b04404903400500b49402c3d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 19778072 1250 19776822 19776839
    0x203090f13050906071214070e0607050a0515060d0201020a080306010909060f0603050708091507171303020c010c1e080705060103110a09050108030904110409091406010506030f040602070309 84
    0x58442c00d00f0b040100914109000000c040c5046440500c810515084070a41146000f60b001da03005506454001c5000001d50001140d502c00c0c41c0005106201d04a10107040040101c0d0485c6400e0b01d8412104031a61101c0510003568191240240142c01c080a2900010402405034ad044032042c540103020b02d850754000c01c100d6040c2d070811210030f0007808041100d0b40d85401042c0d07000341030340350105580c146031003442d0b5a0f02c902a08410510f603040002003800703100c0d031030311184207081321301004050600308008030ba10700799403100760014007440690741c034294014107006428607840081c0d07000b481b40c256801c40b0480d04401080f1801902048407901140c020000940a23500440c106401e0011510410143c4a4a64000c044283c14400100022840882540c082d420240d5003c1041389003a00d10b01c20034401e0350000e11006107014030110a00c00c0482c4041491182032007140c41e640d80700e004104030b901044418881440c2d9040002e000501150060003001d4441c1c18408805500c0b2040ca = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 19779322 1250 19778072 19778081
    0x30f06060507060c0908030703050c01020909010312080105010908071a0d090503030a060e070e01050306030124030201080c0315060703020c090103060905061806070516080304050609070b04060203090f13 89
    0x2040c0003610125000c81403000c2d911421080c500b0b1401e20300b00031854149290740b40d016000016050250120300510076103001e40444108650081000c900c035a12880d0540c40041a00030304d2002a6240f40007145a500503c550000e50320b0060040145a01e0010f1006543c031a000f0884002503050186a029410718020200107a101c2e9010703584070300d001a4000201d81081d0300400013042c0b40010b010070746812801846400000b0700e003031aa640e0314a00424007500c810f20320054060f40c0c00400340517908200b00d07200140c0b4800d81c1c6901c040d0720303039a841c130300d4a0205a401c406564902c0e001009203251110003020000c0c824010744540301c101d800040c0700c20340245c0c0240c030066207929024041080a200d140c0d442008180824000d000e91070320355648010046c000c0050003400140110501c01d91005c14500e241c1c012201c60b90381c82d103450410784070b030020741e0041030510401b0400f0450203426016182070f1840e6900441c1407000c1401000b540c1c1c40d00003902500810380f540078a030424518041c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 19780572 1250 19779322 19779329
    0x70501020f0912030405010f030203070314010905160c0c062105010608100803070b06040b1212090f0d050613060e0303040f0215040f03080a020316060603051525030f06 74
    0x6071500c440201062008046250000180f981c0041005015580c1c01c10103a000c80d0f2164600141c803555520010f90081c01c2c03000d044013003640550b0001a001506030026845460400301d003680881410405030b0b054110f6001c010184007801d5400d2104510482200701d2013807125030a000800c010401d600125802a0040303000603020750300f080008600000000c00030a1405c1c011464103d003900e84e00e90121018041d94031075a29070b032100180f03070b44207040d00941e407040381e0039114001c0400100c42a0b40d4403100006003d2140500d5413100361404000420007140c011020f0803442d42d031607000040b58a00000d085843c56503558480c10440c40400141d0320513441507902483c40303411401000603458410041d514085810030061007060103c0c11140b0440343c0c41f0a0068032000040c03001e9045001c0c40001d1942407401e021840b05000c5540c0040080301d0041044e200500c81c9044044091642125503c42c90b96150091103001054095540d21100b600d10300003c0303106404d2041001c1e07822950 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 19781822 1250 19780572 19780597
    0x1f140906101211090a1d01020306090f040201020a08030618041a0115020a1113020304031206080c0f01050c0f0607030e01060b07031704081c0f0c110705100507050102 73
    0x1008205000ca28204002d09080b140003018070a6079030711195006520b2011074041e504040100e00d4240300780e000b500f200800c0b40d00e4640d04800d400c0c00a4000d400458513940301c6c428440202e039401e000b52214501803a0181d020f0031f40004182c03682d140543c806060300c0d0f0020b004500c14613032054240d5045000e60f218907101803502d003007102403c484a5040c1c02c00040264440d078154101a000034120141075232000c10a0459000000028014030511940d80151400002084101b544c08a000e0806445440c0100f29458481d42180d655440c1007201e5600b1181016480500358082d001805910722950f0450f40071010f204212400c001e8142c2d01c0383c020a0310b40c2c880b141046000e0041c00c01602500d050700303050000d0703500c009040d5824424012500701c80d5902240c10701084504445d1500e01005c981d15000e01c0c110886002400300a0300204240c1c94150800f06041c03040200da50008000001865068100750400c0300d0030840382c2884080c072108005880c000750081c0040e103c80040407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 19783072 1250 19781822 19781833
    0xe24090106120b01030c020705010c0201030e07061115060307060e03010f060303030b120a0203070306020a1107060207090501081b09070909140601020c1c0803060f120106030201030b0103060302031f1409 89
    0x204241c2c403d88210074110380c1450301708811580f56560003ea58800c031030091801624003c0c1600058000740741e02c51003091540541c039070205400d504406028080e190a40c1142e01d18105592004c0340d950090b200941e01d500407500030880703c0e02c140a22810740c18001c0c0000751111240f1552011075040b0f500450209840300c44d0901145400c0400103100b02000e07010380900155940001d0300ca0130203020040940341c0c00f00c2c00e1452584220f09150f81745070800100c03a681c60316848080c0d03481142e441401704090900c0004034501c03c0104000304800d81c10300c420441114118100540060010014020405410400101c5400e0b03406480c00d03c04108000900504207640024200011142280d02031410715801c11200600007400c94441d6800c040c0b1140c5a071500b400041c0c1501c00c2c0b640b0b0903400440700c25030340d994450640c04031086070b100b48c03410845a45018015811b8940302c0c0b2001e035040d0420224010500e024500040040030442c00025000c40320030004050860b003a20300b801d031070340308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 19784179 1107 19783072 19783097
    0x120201081b040806070c050607031a0123070c05040b030102090105030a0e01110c0607030b09060303040e04050a08030906011505070c0302100e15120a060e24090106 72
    0x1050301602d844d820210740003041240780c00c8041e1000d010f0380000c00c2c4418003070320406501181d8510032100d144203120040d111014088000850155100320314200484540c0c01080054402c0351800c00050424052204454403082040d0290f8410001c841c0e070b603a04107007a42d0b400601540c01003226038070100100d000d07120000e60703043c2c032040109503511724400204540348070324140e54040011403041d80030400000341c1915010b405800402050020304410f40c04c03198482d000e8001c44820049030340daa10600c0c2c0c02141c2e00c43c001c3e00300707000600003100c014000c21305403001440e1460504c1301c284c48a40450903984130003849a2a6900300100f10b80c015841c12800a00003043c20945500307103088100d0a600070040d07080714020360740004240b1b1009124403815207880201c0300d6155626801140d113441c5c240c180a0b40b901080c02019010365440842c1c1340d02078002c1c4da40b000c040251 = true := by decide +kernel

theorem cover : BRFrame.Cov 19604322 19784179 := by
  have h0 := BRFrame.cov_init 19604322
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 19604322 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 19604322 ≤ n) (h2 : n < 19784179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
