-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4334
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:17:14.371905+00:00
-- url     : https://prove2.me/submissions/dbd9dfa8-68b0-41a2-8717-e8f0663c300d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 779316546 ≤ n < 779496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 779317796 1250 779316546 779316553
    0xf060723030a0213080a030c08390115030b0c0c070e04030903200a03150b1e010f1d060a0309050102130503060a0e0601120309050a083a0f090f08 64
    0x16102800c0c01e41c40c40c0760405c1c519507000c10b00e5140406e92002d41c0f404000e400c0b081040c2d541e499400c48200c04440364814220002c0e00c0c100d000f034079091143c505a82888214020452942900b40c9101d41079504c1c1b00181c42414190041480003100c00020282009042d08440c14603980b20544e1002e07040480742070300803403501072082040c4030441e06070301805032143c104d008203251040d00040410310b4074040070388000041086410003400c2644291f0841d240101503a26000031600c42100e9030101c1080c0034000ba80d1802c21084050141c11180c043d52040c5c1c5145101b030b088082800380740d40000c22400b0415848213000404100288002c001403c4c00044a54400e410001031600d00301c000340028452a2800700d40f01030700100070400d80c3c10354200c856101407080543c04c044410700003903044642d1001c80d10340300050080300019401140101b203551040c24184030508103901102c0100d0700600318542a48244032988181003151524410381407002540740c07034014428030050650802c0c000b550 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 779319046 1250 779317796 779317807
    0x30b01120b0705040303020d08071428020c100e0f0402181005090307120f1b15051806090114030c041a0702010c170d0c120e0f060723030a02 62
    0x401e28010991003055414414500781c6180c1c3e00940c0c4251940c0c0d108100100040401e00c02c910907008140742d0501c0d000c3c840e440322132060360361a21001361004219145c0106941106950011071046040c140c028440f00d082c2d41d1001701170300d00000d9409156403020b02c0e00510419641c4920240c03a1800300d036010001d81146e48010300c021860b810200800f404014080c2c0b42d1240d4000138040151002d1200340030048030540b5265004d401c4c002c80040c80d8000c0d0046001d403c0703046030224011030724141082d130755260440348155082d10484003074441118150300d5807022400d002c0010b000b826010301d0030040032890b0000100090700305480c40c041180700000c040000110071401d5101c8820004e9010385040d100e5800a4121140724100800d80281864180001560700c0281c90441e4015201401b4003099400010680110499018100f40c80c11647d250200d0300082d000043c00d8400000744000c1c0c481d1401512000c421034408a00440003821280c610300c0f0030006140984080000561200c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 779320296 1250 779319046 779319053
    0x3090904110411180a270207050d022404051e0a021e0a050a08060103020907170702010522240204030602071b170604020d060e0a0f0b0109060b0405120304030b0112 72
    0x4007115100c051180480f0b034001e002d00c0d48080b00e02c4003800715100c0701b10316003010040d40101034000d0384000f0341103004034420200810303000b01b0755200da001c140d18082d04103078018050454420043d54058a00e602c82e4400d10116181c0050000401c1101422201110220360010381201d04840e440041c9070b14000a803e0741d42031400740000681780403540d01c1c80355428074240c59a540e10510019100300414400304801d14058545209500c85420ce21462484c188401030301034101500c40300074021903003881d010890304810a024400b030340048180c028180c03011000151045407001c08039440e500300b0000001a01d98801007440500c1522690b1001101d0100c64200c0c003c2603104031501d0702d454101103901d98011400350b500a0b0704840400880a0b6400d18000618004031114128854041240240001c8202051499102c0d00c0d1440740750707072504c4a00b01610900d1003941010007041c4001d0107185008618030640f183e52404980c1815500d441d4414041c1e420390111448500c400c0c894001d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 779321546 1250 779320296 779320327
    0x30c0306050f010c111c0f030e0d0308130212010e0625020d03051003060501080606130c170405280c050d0308010e18070605130905070203090904110411 67
    0x107180488904107038492480010742072076807400c801803225030120007400c66599801c1300d2242500c090940c1c402d50010b07514001000b50489034003900460010391003003070345151036240081826410380d5480c000b911420b48144001c40c3c1503508990041c0c1184850020403024498050408003080041450b810441c1560344c10b07890720070010f2002c1600c000300c040d4003074002030a111010202e19000881e81d84444081086100582000342658101b1000141c00c01000400b9809400104c40307050361444442039030012264030200e6000401c06a001405101000850b1103500600034000d5504290a948445801d80300303c69907251070410711190001489402c81d20788005c2c01e0190741c80146080d850f200903001d204140f1603904003890030000515000d01d056030112000c0800c104a9040940302d2401a182da000341e912110403400c045000504420180285030003218150059440c00080d50203102c0040c000030030940d40c0306007a601c43c041c41c0d1900c1c07007950202c8083c8039003251074100c1500c00306803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 779322796 1250 779321546 779321549
    0x605031020040b030c0a020a0206040b0315010914302d0601090b03030c0109051e1f0b0a082401090b1e0a05090103080310050907050d0203041110030c0306 68
    0x1c1184148403e018118070f900c200e80d080115480720640b83c0c0350031300c3d04a02e0000c003403c00a4224a02103800504a00340001550145110b10038120586003004011100150745200342d02c40310702a21286480c90504051501c0b0f40c00d035204c00e028040d13608004001e110302c9041091941c60740100c1c181d21902c031200080405240604809100d81c081c1442c40039552a0180107155940f81d81d0091708400d540c04004131030440e45030340001d02c4081028101240c58442820200084003044003004020030000f0841c0c040c01c50101903240c0c0380c00703000003ea0004180a001d03050704140000d10105500d1810489084413003689404000d02d01c95160f410304403024181d10001c099810005403000301d5440443c1039042a175001e031100e25928040300000c40d075850952140d504150010004820702c04008001c42c400c150110805100a58070018418041801c4411744005403040c0035030035009107103400131070300039005018018040c8216400900e0f024001005c88000c00d5403255010746090300342c001c600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 779324046 1250 779322796 779322851
    0x415020604080a080c09180a23010909060e120307031a0f09093906250204020d1e0c02061005060f0f0417010506090403050906030a06050310 62
    0x1040382025500e85030b0034095180410306200500001840c541202e0040e2210010010051100103003010f031003c0d454502a0744d0700300700c40e0400c2c0482c001526a0441c0180d0113008144000c41030b0320700b221000051000c244100d55507507c0701040e404621080008002c8000c0107001582d880c01e00c40c20140407980401d91178200000c500c04800e24503610400161200c100541d0713807804c81d07640c46241724103000101540d441000c4043d080508601c800d10303034140d0798001c045401550100d141081250500840c0600014880c09241d02d40600c1c10407070001c10034910103072000d0f0400f444003c4000c1030b100312401040b1f41585854039000701041d1402070f001200205d00103070105080000000e01440d80c18040c040c0038003400100306100b01101d40845204601942c207030740d00c590700d0300c0c03401d2110410b05104550640c00c0c040402c1c4c0d2032800140c40343c05580c0c59100c95207880c1a600c02e006c0143c2005007100e04281c1d4031040007586031824051254460402180016140c6a02b1248501c2d01101140d99 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 779325296 1250 779324046 779324053
    0x6020d081b070201030b060a0c140a0506010501200a060207030e041a060c0304210b011509091107050d081609080a0201081b040f06031b02070501031e0e03041502 71
    0x4425064441c0ca800032840506800556403445800160050019806010f800c15800190003170201e81c81540c13009500d200d404110450703003e10305202d80e100100100500107401c8500100001e60042c0540f01c0c40c106601d02070801801e08190381c1c0e0804080020a44e0001e40024007001090743c402c07c070b002008411101002210000001b0344003c2d00806100e9004860010300000800c0d01002901d00811300e548203100b5442e84082880101c4494110440b80c0c03961072000491000072003034071144c4000090b81c0d101442d41c541160345010f80303590a0032080e00e542c100511030106205005041c00c891043e110040075041032058801d00740484980401008178083e024412000d005c07649650035a024178103805240c8988015492140300f03080303000e005210000340040c40041c50020501103403a96241002413210009950981c81c1140c2d98140050304481c205214030341c066800300b240c17a0044d5500602c1150407440c140121903240410211540c0080f408201d400f44004698010041c40e1024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 779326546 1250 779325296 779325301
    0x5070611031e0313080f090f0604030f080a0c06150f150509040e0705130b030123060915030703110906150f03040807210228140f150106020d08 63
    0x2d02c0c944100d004050141040040441d000d00c0348103894020031a04680e140707546001082c480c0d0a16804001500d01418203400c00000516052003520100c80c0c01118401d8007080550f20f0032400e6008400c258140098400d05d20301250b81c52007400259065028842c1d10513040c2158038003810003561242181c1c4809240380c00342d5541c00401d5030b07104ca8094a0100c0d03010b41e481d40041c2803103102c0d00080c1d000003c1d05a203a24100da140c008883c240402d40080003c0b1204004c69003594081c7c0004540c0c201200c0040741c03003030a0001d00d8940c0020b40c50b040c1d030a81c03c110304c002420000c1c41c0e80191020440200403804c140703010711109070803e004951180381d030206514501040c2c083c0c04048440e251000c00014103211080c021503000d00d600410341c3c81070020f240900191800e2000f00400184141450f42850281a011208102066170014040d0000c40d0759201c0e05021264200c2485000d120141c04604a0030000184034080300000d10a0a604084009141503811110802002140d109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 779327796 1250 779326546 779326567
    0x30421021b0402270d12091404061203050304060b0a06020f01060b0a090302010c050705030109060e0d020105092508030c011b08010308090607031b052109060301060c0f05010501030507061103 84
    0x1d000a5403c5810030804100713290f0030002c1e00380621a0300c003a000341d000c01a00c218042d0b001542006403002c0d20010826a0780350700601c01103c0e4035000d001030040420001c0d501180c010000385521901c42d54020517800c1b800b801003460510300d58046400b582c4541d000e0600c17000c080c0034130800351041d038182504050189400500d0b240c84c0d0b1001906200300102a030051010034000c1902a103c003400034001c01d0142d01d80310700201038074040c40e6004d00a1000409a00b0310602502d400341e410080141500700b20310380a1401400c1082108001c4030380301c800007541a10610140c0100304201000084030149074001c29485220203100000300801d602c010b000240840080e151440b0055518170b84600b8280380c01e0b41e190025600148840c20a0001a401c0080001d0078a0200543c400b6400da031100e000068071480c0200c01e540c0380e1281c010310040c04214401c0010015840c0100415490220780f621403500711102a0819107440d042064107000c4c040e049800b061200640d60001e51a0030b52180c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 779329046 1250 779327796 779327827
    0x510030b10180806010e0114040b03100b03151501020f0604031209030e03031b28020d0c05130905240a052e030215130308030421021b0402 61
    0x200ca801c24460a010321103003241d1440c03414000703003c0301c004940482d43c503001c589800c1e08091103024006040c441e044645810540290b011825015000741400088940403401801c2c0c524082a050702c04e02413242c91020382da990485c0500c81000c20880d00790300c0306000a0520000a00890f081d500110600001942c0a9040b12a40c1c001c0d503030003d1400303441d00d400c49030b008810120760380c144808284070469a40c03021089282c0c0d1810b03c1240d90040000e07a21941498021550311b00c4807036030003569400340c20002010380e411841401c3c05025540c803100011111114540c0d100c507501c2d540d40c500400c100c420820701c00c0100d9007460351140088941490384068a0003030104000c680c0b11408542c13404500c8071030300c40041000c5411004001100c20105d2845443d20040c4d105184a41c4004040c5618a080f41d414030b0922003034282817802e640714034040f544040c1c002c0301c00b82d80e00da240107001d0f14a0200c10f104e510941d030140c031600d401345600913155014020b0280c0706030300c10000c0400c1d40d113040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 779330296 1250 779329046 779329069
    0xc021503061c080d0e03270d0213112101050102010b09071d0a0b0d1805070e090c060f04090f0b241303110307060509030a080d02130e010510030b 64
    0x341c81240300e0b0401440d1080301801010564512103003014844000b01c0d42c00310241c0661440c950200110001002401410501d44041742d50407440c2c90b032584015040007141280c0c08684004040383d441103140f85110240e00c016006094400c0c48080034600903224080140101000d1009102c01d0000307800082c0080405080720341030214000c100341420030070b450010b500410041000e90144c0c2c0e182c810004982c4542c0d17011714510702d000750000d4138200f0050207400540d0041c008007071250401610106644010300681401c0c4203086845a0b650345100c000c2204414400c1a83e0301c0c1c40c0b9080c10101600d00031103030743c0f0703100e8208030600c07070551201c00798910118040381440c00d0442141402c40754502c50080c501520010000000c0b0a000a1003042c10809c0c13015002c40b40304030707502c4500f190240981926558075030000f2100d4008118a20050921000092001468022480e089034164995030384400d1174000b000700100582c1c5011b21044103802c40c41d0600f4424001140002668030300709 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 779331546 1250 779330296 779330329
    0xf1b010c0f0e1804060b1201020d0f06030f030f1407050a02120a15020a0306120f050c060a0c11120d031410050a030b070c12020c0a050103020a17250c02150306 70
    0x1003000134180a45034019560107100031706803100d2000e864034214040d50203407110001e41403c0c1003440c140c00d11180f2410f82204e41111001d0a85807441e50111007150000d49481c007000000b503103007900a941d00c8020f041d06031081c00241070511a40c03050015442c2e41085941c010b4002c0300032a40031609003a4070580108417801d00507a04c084c5950140c00405141d0400b1115040c0c030504002004403040301c000e4401d0182040b503841140300410800725104265000340080c004100e50f07030005030400e001e100da9910052007004204003101486203000045814240060b845152003030302045200c69503604801a01c0412600a0511000c241140c0140c4002003050780d42030300241d1107500c500e100d06040c60707016829020505e0340b050020360783c040c11319800c0e00c1545103100004066009100700e130600c400039101c20107000440d800010300c000000740079019891500c2100c807080711114000d12000c4180781c48450f00c0d80d0306401800b1010203000700c0e1418500c0304005102c060760f1070030603100040b2103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 779332796 1250 779331546 779331589
    0xa0606021b010207150e03070803030c0d0c0c080f03070e0603010b0a08040c0509040c091b0801050d1a07090612180b0a02040b0414100201060f0b0f1b010c0f0e 70
    0x5040004070310b01816603000034006000c801c0c0e007091169000c041100340600887c125540c503920b80040391b4484c4000c0e24400b1814030708115601c00b203c03841c0c03c45034a49216080c05049a0320b02d0b160000954802c0d600b48104180020070000d50075000030340600d03201e009440c01030466050080c090190300c40d510b4840c00348080e0314000703030030005120388410103010013901502d95414036250002c9800050b009d0142d080d42032440c2078440b2000300070034801400a583d101d44082c3d01c3e000601c41c992a1061003610745803407169110396134840750081c26015403400e99034402da141c60480c0050280165031100c444a80c00d0100c000507404030205224141c1303800005120054480d509054000e200d80c0e408007140c15030101d00001d01d0380d24180301c0700c8d4101c001d540d8802d03030704242c0c4001c0b401c075200350042c019403201403003050114042c19400381c40a1b4480d16030301450f00c1c02c4412800000106003000e10526915107140702e018640c0940c07a00202030306030921a01c90041c3c1000260404a45802c00e0305109 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 779334046 1250 779332796 779332843
    0x117150f1902040503010e070f0605090123072f0f15130305070b071e15020d02131e0501020303093d0c080108120d0e0a020a0807030b0a060602 63
    0x54440c2e04840081070014000c20042c1044042103440321054440c014a0707504c1104009200d9015104a1303d14100503520868372540340b0115210000b0440c90f21070001c81d050100400060b05052007140b43c214100301044080182660050101860003515011300401890246252034100b000706942c400a410745490340c1c1301c2c40c0070b480f54100c25031001c1e205229140c1c00144c5211903000514069000d9142d100072800101c503a22045807104000170b10360748600744d01c10203011107a0702503e030340c1c84203000240c500040074031054216080c40d001703400c03400b0b00c141543c01c0c810301b0666014000c0c0002c1c00910308500e000b0562546a400c0c190b0240420a0381c03d4003248403200740391843c007030005403407450413031110fa41004d50014a1440f200101003603003c00085422100002c40d00c010100700421a072400089000c024007502c0d0400808545110310b4903460016507540c550100a0165000141466451402c001c040c0c87e40142081080d40c0c64500c05124442d404180301101c540360039120001c91 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 779335296 1250 779334046 779334091
    0x803060f0315011a0403080a0e0402090d0606080f011103040b06030304030c060f0806150706180c08100c050301051e0a03080a05310e130503030117150f 67
    0x306400c14040e503140c0030b20349210710120240d16849068441c0100801d040745a01d603880e030710500ca94000602400d005003e5072800c94851700f00900904800740025003040084400304200c242411011104161504400e10070311400700324424803540558020f01c68000d80c00804410351001520241007100c4040010702c09441c100203d400459100803038054081d5244001020140c2055034140010721107001705030503180003900380c40700e2128403c8071841d2a0150f07440100600d412041c2200700d08840c00014003107034483c01001d00400b00e600c080c0085121340c002c224220344040064500780902800180402d4075140b102c43d0301c0c0c03042104030b808403850300300006417160025840280b20400001c0c0d9100c81e030b6807010180c040701c814800314030307003001000c2c0f000c5110003080342190b885001303040020800700010003943da0b0002c0f0413540c1d0315a0080140c581e1801c50703100360001802000304441441e030301041000603083e166814803909450781081c44613034410403009441c4403014a996001060203 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 779336546 1250 779335296 779335309
    0x41103061c0f080a09030b1602030a050d0603021002072603030105010c0201031b030b010909110a03240b130503030705100221010e0103050609060f19022104021516080306 75
    0x2071a40001c0059100c0c000440001c1210605020496403081f035a0003050700940b844403940205402d030f401842c14806910300803030b1a500104040025a40c86020000158039002c58000c0301000c2d0b6409070060f0341c01c040d42940305096203050f0400f189680311312415800000300660381592800d2803c0c828010660004038090032940c8607001e15010751400c00000c0d960183e00110320018203032251031800e980c0b440694102c8900071880030854030700b0040c64181c02d101c1d50010044c1e0003080b003010004550000d0034080d15070a6004400c1c4613100103032401d27440c2142810b81006100442c0210300d400c4c0c49a072141d4841203450303d228402c81c4c0100b062114852a203862011326181039109440c5582d482c01452404d000a201c11b9500380100c4010038003681000c10300c540700e02da0300488900306440e4540313203022547c030303140c4a6400d1680c04d122036414805c4510b01203660b40d070b60b200890b44908181c01004525540402005200041002103161010315030300001422900400502d840f60b8816020820 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 779337796 1250 779336546 779336573
    0xa0201081b030f040b15090f1305030304141207050c010f0e0409030215090c010f0f05071505070908010e0d030e07080105130b07030902281a09041103061c 68
    0x41c003801200f0450003150403001188507a0041d00451015101c1d0754104154010b0041c0194020140c0c4000480f462003230740ca50744d04400b240301c07521104003d58030380341d065400540301240e00191000c0d020074080700c10840b0310b26032442c4e2071901b0721300282956600e03a1405d400a8030360500c03040c1010900c125004482240032800054020310505401b4a002911251050714220680c4039240218400450024026140d420103840c1c015900d0315107803046e81c4915115000404000041000e04006a0050300d249240c0b501441c022859040060004c1d00550081d00103c00c2d41c2e140804444843c8070010700d0904886a5080c0003910701800e410039400c044d11608620419800c1c00244a485820f215010f0b0b030349406104e002030345464028088003611070714900603502c0320691425091007030707028490195964010724a08a035650351254a99103020651601c041c0d00c2000c5400540c0d03040c00d005107a010500d00d407216165181190005600030108551121403c2a64620204015416846a4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 779339046 1250 779337796 779337841
    0x12191109282a02060c12240a060804030f020d021f020405090f01060909150608091911190b0d02090303040305121c0b010c0b060a050d060e0105180a020108 68
    0x35151440146948108880100380400511904c0000350310a4140425624090740801c061102610b9003441d03091035488005206148094000b070402042c0c0c0c50901c1c100c01004a602c3d50b10f410711b42800d01409a01d10421108155000118192281507000c42d6403036019071030928850314103040c01013000003070060350481c80e00b24907003030203011034102001c0195040b01c031540d90b819030362519030a24400f5910720b03581c42c43c0000c0c2070b504184107103405601c41c15440700c244022030f45400d06180600c16012210030007991030844045542c109400c240f004032101001c1007079080069840c11100c421103200c0d540070044003a03408039070009a40d40c284116801507030082c0031200307003600012480c03180798040202e1100443c28140110440c81c03040c068980301f8501612221056039143d03c5100d81d08d04010151076120301c41c82c001141039540d4004e1200303286c2c007032170b000103002400302085170071600094108130079070401460b0700c12483c4e8005107010700c140e4286029607594544c400d84400a000212500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 779340296 1250 779339046 779339081
    0x90711070509090304150219060c1103070609110105040501170403110304090506130e0606040e010609060e060a080f0a1709040203042a1a03061219110928 68
    0x80f03611800009441540c408400e151310342040f0a03003ea0355032000d40e1101100403000d207034180114106500c000d441003514180000e600222001c060b05543c030465040f121281d84c0e05100c03045c0000750340700d070b182032900b8240b040c5090704100c0040c0101d005806420b540340c2490000408040c896441c2c040b112991200300d98495403510000c0b80584003c44071580140160091042110700034024400c440605401a08007a00d8110602002d000f046021894642d00c41034001482101c0788600030080240304294103890130042c1c01c011200a0750741c007200c0c0b00e074810f4180c0810700f0340c04a02511a590300840806000408404285581c002c02007003a0b80144003001f00810b221180f068007442c900c1440e04800c10903402c109102c80d01c01d59005120300224400d941885d0300a1150003142c0010f0010003c07082da4068440345894280300d290b500112421b240d10010801504105625580f103040b0360203c25890304d0a03610409800b200c2ea40c051a03242a9003412400742140d01101103a007205811 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 779341546 1250 779340296 779340301
    0x303090a060215092d010632060a17040609050d050403150507080105120304120807020a06050405012f15070f08061c0228060e030309090711070509 65
    0x1039142e07050100d00f0300284980390000340c142e003408140010314a02c483e000a50424084042504840c45610b203046075651b100404a0000b46c00002070508144006008440710601c0c2e54100203001c050014a004a8082c407440c1e22040e003111924811500994003800542d0b01ca040c40005024810400b40c040d0251110941c03449a10030700400650303008994008000c4d6030312107140c04440085401c2c0c400204002d00600203464103c0d07180418502c90340c2201d0400d900d80a56100050344980c0c01c854001c0005100800c500b0302d0301142d0020302080c203045d42414540400a0046040311308c80c04051030710301e00600035042c03290241261090702c2038100c90082004480882c86c0030350948848010905c003403000b1220b02d200d100b59503c6101e0152080401e444c04801242140182100c126444120b41d0410342051a0070303248001c02400301c81d031700c03002030f80782410203811080014075540c0290000c0182203455140c10f0483e603000301480c9420303403000350340c00c00c020304101690300b1580c0c0c0202d40405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 779342796 1250 779341546 779341559
    0xd090803040b090303240a0315020d14100b13030b0a050f1f0326190806060403020f090a061e150e0a0e0a022b1422020303090a 56
    0x24500c40c070b21445204880b0345a03a10080e503a40001c648480c070702d00d07442da0398481d072140f8800c1418a42001515110000342ca0b03a03100b100ca81402556080c4580d80860640302d000040d02035140c1050588140c14406e01f001d145600703c0b902c0078010079102c80400a40380e0310101c00200004001d6400c442620420300380068404040c240503204c6e025884100c402040101c66040140307400d5044c5120b406401a08c0c0d6079030380440c0c0d0640308022548000c4001002403400c0d04030700401c4584144603811402030054080035144250142185020300800d10007400141c5030051201c500c45001c68495003e07554041201d0040c0042d5040728000030043c2c4c082ca0300151420000c00203851208040701802c41340003a044070914900703803903240d10210b4840b00b04210035485862582062080001500c0c1c00301c00005c2040e114030150f440708051034600c1000035661320305d10a038400d11945130b41c107860343d0a10011840501403656003260f05945080128021554100100c6900c0329002d4980200c040c0d0300c2d003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 779344046 1250 779342796 779342813
    0x3060315200301081e010b0607031b02090403050c010509010510060c061b0e1206090d05160f0f0506090a051b0102160311090109291c0b0115050c10050403050d09 71
    0x801ca0a0044117041c104031280c0418064603201e106c02502c01401d0084a46045900c0040e40c40c4031021246d0100700c213000b40c2c403015030b024480c6000e5160300c1c0d6a01c600100160031100010414100c60f4541024000002c6200d510300c0d003240c04501e0440304102c0c050402400030501c1c4030a4580780001090300a501c640c011800c2589044100d420009610b182d051468a40c9402c444500e00c0d5004030182e80c1c011809403018060090011600311411503095070b411802d01c00c90f00090710308035400302ca41d0003007080421050f80c0c40204c01000e4282a9010381e6100d40d84d543c005940c1010001400709803216910230401c60034201030b2118101c03043d940d43e0500c8140c5074040d80205000f0b003040e40c00450000007501858600c2c140c0c0003080130081d41001012001d080c45500c1c50b03588141c080300b0740c0210308590103101c11b4050041c00d0a80300d9515114a00d000c8c800405400d00c10300505000b520703401880400d0400b0100d042010100c0d03142d03a41d140c00c40f07407442242501070100b49044000700c180f08014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 779345296 1250 779344046 779344063
    0x1015031103030c06072307050606240408011e1a12010b15070c0b2b0603020405070233010b0c071a0a12020f070f0203010236010306031520030108 64
    0x6e01100890041c90445421144600c2070060010b5200f1008500305007007000b23021108007841f151320b1071489400c2d030750249984e020340d010812a80d12200341d581d0090008100d80c49404a420040154a1140e00644030800b08400036170303c01d00d00301801c5007844000b03410920b0b48260042c20514600c3c40e103801405540c00c0214195000c2c5817948c404228154440d04440c90240c440702032002c0c1c940b03805442010303406400c00300c0307800c941c0f90040000140c0b10790181d9800f031a4140c028000c004e00040850200c1900c45007040950103919554400c402c00301c49103181911a030f000132990724092201814139002042c1d000390b00302c0c4407a401c05418511001c1c05000c01c1c10481c3d0b105150890325940710b406a00618161107080b2104100d40c0b00051a40300003400201d1002d0009070805200b514a060146010325084400c0f40d9400501c0360140c580301014046442c00f420b04102150842d00e8060400d403000c9450251280d59005860810b0599803002d4214030940a50658941e12280d02d1902c41444 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 779346546 1250 779345296 779345327
    0x207090e2a010c0f020d0b04080702090f011404020306031c1805151602010e1306051513121b09060e0702121801110d0509031015031103030c0607 64
    0x1a40c0c0e501c1110800040d0610800142c0d2030018015032600c075185010100e41c0d0485c0d002d0103402c0d8243c001004503054600c214002d807138941d260328990050090f8180300500840344e5800500040c407210741407205002c01040280c5e00141c0382c1c0c0d14030000c00d2030403a2443c2140c4003c469440f62800082d400b007004451298000d031406000d9503980700780004103414404c000c00001052102414512000c070b01002e03100e00505d4480010800c0102055084100381ca03652210758880300c061100d42460000c0fa034000b0392200440740351948040c20000c642c12940104290b0507000c03268841485610b989801029100010f02280355558692071030040840c0e02ca0785242c110700034000784001d0700210346072080c4aa105030a510303100d9054000e4498410410186050100003c00c0f03840d80b803030802900c0030403003142d210380d81e130790f030070202058070302441c1d65000500c035400c0060349443e000181021600712988a0021418880040002400d50281c200d0b02c0059118220411900e142e0140d142e9190140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 779347796 1250 779346546 779346583
    0x120408130608040f0201052a01020409062718060524061216090b211b0a12110705010c080a020a140705240109050f04150504030207090e 60
    0x581e0002500d0300b0008681c00741008211810000155000b10020052800400c00844040c0840e82814071304100d01e403821085030b035020a0a1203142018400d48011340783c3c80c031104143d1078412201a1596104400715040c0a445038458903208840c0e0603101400381d0701000c1801107140c40800e200f090302030640e0b254100380c5292107015650518104403040040c41c003040c40151341e00c171240e00901c3d0000c14524000c010a189000805c501900050722002004e0200b080b02e60502c0f48142a544502400000c440c00d03142d02d40d541e00c12303111030480301304500702e00f00780c0f07210301600f001940244014110300740c29250008500013001300650004901c03441e2900c03100f00c00d885070707408a0224000c0040304000324521441102d1001400030182141510031030445108040b800e9080c01000148030440040000c00d10040c05590000e0240715030001c19000c44c01c0da9880e00d6220ba5114590010752129216690800704042c940b003400880c0152a0f084001e00902e0f14415580740c1d00c080c01c8429404540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 779349046 1250 779347796 779347799
    0x5030d140a0e0309040c09170304080c0406050a090e0c0d0809032b0804020a0308071209060c030c11040b03060c0403030e03060702210d050c0307030e2d0312040813 72
    0x1e240e44201ca1541c21600c0c0150709112182c402e100040ca0311071541010301a08a1001440781c0c2c404450411a51100c00555119880c00c3d0741da602d440d96031034030284201e0030300c01c0501141d140d2400000441d941d48802044150071a07800a080040e5440e5060704500300b403040c0d0701030181d440018101540160112081030b210000c240d8004107041d40310690181002292441003846620f0894020380010700d9020b84907503968a500e016442542c08071006004c1c900000c3d542504220040c0041400c1d040100d640740641d90018160082880d004090200280b40c01c40c183e2100d50010540032000380494007203040c03002c80c8000701c0d00b1a11040740003941505c02d18a01e03041c0410018010305440d001404c403802c1d00740c0080c0306049001c58403030700307100c061100002044d802d00441e03004120000d0103503500e040c03c010050588605600307640e034590000c0c04900d00e000b400e8034802201c00e185040c0044c826210503010303007184200101403102d20700d03203400d010500003650020a102003420041c0b44025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 779350296 1250 779349046 779349061
    0x4050102100501050f21240c070c03080a0219050313121e0311030706060303080a0234020301060e250906030b1c1202010f0e030301050f0a0305030d14 66
    0x1030300240a499002801da6503078003070504100500410b0b100c020f806c400e00b1000131581480c070308400da40e1100c06100410040d04607203580c0d80c400750742040c24050300d0751505140e925881070f50605803200602c160f40008403002424401e0041042a44030040019402c42c4c150510750b50365000100008801c1d2900c2e0070000b000ea80b45e0254642c042d5004500481081c0220184110701024032000d03018403030003a442041d00e0900744001c0c095540704540010b4224114100102289402402c035005180b0400908600c0070300c942c50b50094040c1ea40001d03810b1405005201e0045980c006c0c000e4056090000100350340610308102c0307114429000d14a0020303c4180111621088101c41c11400724031811340c14804148250010a0b20b44006072140304002c10341507090301000080042a03600d4025405403014007503081c0541c082403031000318240301c44e038080e1403002c0d02c80c8810b2007124400c0002ca200c0c90056100d00729617400840c2c0201c1900d4680f840100181e0141c4081e90302400c03000300c0c0703070009002c0303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 779351546 1250 779350296 779350301
    0x7110627010309171303021801090506040203091e030d0606031406060a0f0f0309020d060b040b0102010b030718110301170114010f0e06040e030a0f0e03010b0904150b040c050405010210 81
    0x103507a0800c240b41c41004d402e4482c80f4140c3d02100611800400004000c000f51303d0b1181c101c04a143d80d455420300070340c500f10b114401c58001425041c0300e42c2c01002401180100052007610341c00138070304d0241c4100301d0600400c2c80c2d842071a40d26040e00e07062000c00a1520382540c4100c00c00802c12501004c240d84a004000d5030b0300c241e415200c080303504000c90320000c51250b420705078800c039a41000180c5805580010303595030b2408034110360702d036110a01138089040038012500070407020b00003071096044010000e0340323403c0b582c00340c1c0b0701640104903007501107400c0b600086c101c001c01c4100310380d0760750311090120400c040441e0003680940c20041c4603081d400282d21540d0490ba0700701020344816060100a2021800103030845900c6a16549003006024042c0001c056002680d103030054080c0e2074140c0074000420070781c0007d10a915080703602013140c4803181c0c925440b590180881494040503419580142454003180e5001883c0c00359060032190005e00030070907208241c01316402c1d0040e08e03a401d4107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 779352796 1250 779351546 779351561
    0x9010c0806150301061b05010614011d1003090302010b0a080604050601060c0b1302180a0b0a08010603110d0f1208070809030306010c1b080303040c03020f01110d05071106270103 78
    0xb03401c18200300420a5a01c20800302d07419a02518443c40c0300c8042d5241c0c20700b980d81642000f078101c03881100b02c1e1015a0417807101e45001a6000322981080107982c00950843e000000c0039003415156441d40c0101031003903011035210303000244801c20035900c1381e001c40e50310a8221001c40c2d05200c0d90300085840f50040005151840e44041c0703511040d502e0120b0190144543d06c0100c1c0c1014a1541107504440316040ba81d100f262603100000d4a2084141004085112580101c00503450400300b440801c1038091040d12818003030782c40d00b002440516041c02c84000c40364000e040450642400c0c0641d07548000700c64018500c583d50385030700d500c941010301d49910042e21a1808200c2c0da112200024410b0074960112030444011060140d0351200f4036030940d8011542201c80b255409000d000314a0a51000c4145510030301c0d100010606400403555604e800d52042d009001c0081013050400c042031107208400039015250320b4a80c4180d50112402c000100e0940700364420340002456030394031a106182 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 779354046 1250 779352796 779352829
    0x2060910110424091211040c0e09070905041103130b043306210303090203070f0602010e0601090c170c040f0b27060304020603130b09010c0806 63
    0x35520400c00300e40000700030003840789101400074040001d0800d04205a5140c01840091416440c25140d00c010000040360b04424060000d461203003001c1000b5a040c0c0d0010003041d240000c4044c0b20301000d5070342101d0002c1c0e181d4010b800b1010400041d03480001c881c129101070701c084c0803042d0140c11002050000311a0510940100d42ca0f00c40484c0f4081c500c0c940040c0903102500d405460202c9240e2a11603d049265240b101d0350031801e034a440e00e1040000a102c0c89407000107c01c540c0703590b0360a801c000c070360160425448080c100250358050152000900c180c2c103040c44155030360a0b001e0f02078001c494440320b15008135400050044070500071062010641c0c3c0c0d03515044a180380104c0d41e10000601041c1d003400701404007094006004108001034900c14443e1a2549000d41032200100220002680c440005c18400304103501d0385829242c11540c101d8606481c1d0342c80c580d94809101e20740c03001500c00c0c0403c906000300e48006500c0300c04410f501c0d82d5500c481e5070350b480a00a100201c4244803 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 779355296 1250 779354046 779354053
    0x101a040f0e1e0718121a012414040f03110a050906060a032c064006050a0f200d0c020a0b100f060f09031e0b010e060a0501020609 57
    0x1003451102a0003050380f00d102c50820300c0a2840c250108009480720741c2290a8800801207203205010340b0403d01858a040030071000601c0d0b051035118215954207102c20b00d4400021301d0410002800f9618154104440140050300c4503540c00301101c62620b40d00c01030701c4144441c0310304056402e2003600039080c1c600c064031a188646854060140c0c41d40301c041400205039507010170312040e801502038a11100304080807410f00c01b145139030003420400c0141900c900d0503104e11015000d0001c0c003110820701c44e0f0003503050740b140005640c121414440703860002e00701d920b0401080180708140d0f100459020320f2900401c05104101c040042199503041c0c00c41c81e0711000e100030004692144c001c01041100391042e9100140309075549040c0c141c0030ba500d4000c1c528885011301c03800035088002c1008080500d4980b007041c0c3d044e00d02410f200b446000243c0401c29140d030402c10003550080e241c5c0400e9221301d03000e103107694030a50100c126005039001c40c82407155210004043d840003841501901c12440035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 779356546 1250 779355296 779355331
    0x504032a0b010e0604060b0f030103051e060103330c0e03070518061516020f0109050f040903051c1d01062106110a030b090702070b12101a040f0e 64
    0x1c07a00c03e00c0b0040c115a800364443d07501150307a2006401500181e45007181254403075055203011400c09010b0540c9403540e112542c03100e9070085002030054116900260410f01807484501e8041040c50b40c201482c660900c4c610a8424400041c1e008146103511652004440749441d400c15450340c0c404d11a5903481565884518121408030b00c1040d000240106428840390401000c0503142d000810030f2403400610300c0c0c2d400c3c25414449a500055413007440c180070b8a50a02000502d6070b40010790383c1e4000c036a150381010815010764200e0ba45010007a803421042860b450754600a01202402c14245000790100000c56900502641d401e6412840410443c03145041180d01034034800c8805984041d207850440295503000c00042017201d20964000c69a03a090100b404051100500040115440250100810402401910039400c407100000d0001e0301c0d840301c8502d115800350070901081c00005940381020480c040103004030340d230710900704003195640c1004099561085840e0848078400080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 779357796 1250 779356546 779356559
    0x150c1309021b0d120e01020a05030708060a050406171b0f01050d020f030705090f010f02100f090b01060216080a1e08070c0806060418081b0f010504032a0b01 69
    0x203812846102210031841c000a080e03110b280152494000d004101d4038800141c004c2503130b025040220071000029850f26120300c100a11610008000008100d017200200303020707649081c4000000d0100074001c2c0300c3c49803944c010001c41200c02d1840c07c501c1c0b25a075514171040c418103590307080d07800303004240c80b44000d00000152003035400118461300c60b40d420080041e030380a4000165004441c1942d50585510401c400c1c0400810f80c911744905004982149820f4680c0c00600b1503c401e502050114100129413460000f03495170316002413201d07081b20000300c3c5180e80002c2e1056080080c0c05071718503d50340c2d10100c6444032203084002d032042030702900310000c1e20100d1560715000c9120726800d40c03602c1002e40380c4001000450b0403002aa80001092010ba45003d000744006004041060a59094203036141c0c10719204e805808101d581c0143e1180300c6554040c000c24414081c1c074402130107585800c0c80d00800220500d041c000c1c2c2184040c2400408046082d1a4114698400e01004840e405c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 779359046 1250 779357796 779357801
    0x1050f060921010c0e04090b18070305060c030403020607082217070f02010f0e0604030f050f1f0c14030f090106170c030c090c0301120303110c150c1309 67
    0x50303219002500d00d011124864207042d070901e00003101800000e81d060078200002c001c1c14184440f144a07609003c40d04000c00d041130003031030f009200d90f03c2c2c200760324001c01050740c1880d41c264000f034910300030001049136107000b00b002148910f2003542a11420342c0c99440c00e8902c03480942d91044940309a07260034010746010522000c1d50340c0211450380000d0448d0400d0078899200c42001c40324480c040882a0855030030007a010041c0b842810440b03c811910408504280030341e200180040e814221783d40c05000040c005060407203d05000d850102d8202d10140b5002a240c0080c450180d24052020240c10310407498160001c005200e150301d07540f03900080c0410304401902411255580310700001d518030704800304500b0001a000038156001c4090209414100721590315400dc08034081080828540c81048a06403940c00d0b804c18180012030400301c00400da0300002600c402d4001460300d41e4010b0026040900d00a8441440f07015906d8588401c00c42c06010204d40c51f40c030051702d00748031055003034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 779360296 1250 779359046 779359057
    0xd0f0302030603210a110303011820130f12030c02040c11030a020703030806040e0c0904050114010b09100c02030607270605030708010f06050a2a030201020306031501050f06 76
    0x1001c8864030b844041420b0441d4003131a03000405420006402070049400a25030340480101c0009581550700d402d90301d10000c020442d0f584030003540c940d901250b402d41c6580035101c500240010f00c2d100c030500d4080310b07401e00d10b5024003180100100800141c1071130929242c0281a81903070740f001004a03035030910010700301088045060020528a880680404201401001c0d0080d4000c2106600d1424041c040c041c004e40b0301c5004504240150b1003144c000980e80f40b1041c000d90710682c480da543e0500c640100013100804040c0b20f8800700008000190700c0191a142d82c08072503140a4098070320b801c0c4c3c0c1c0030003582da00a41580004000480d501d015003211051508580c6061082040303018881e1004010354111002260340441480800ca52001c0b19a01500c4007400c034110450902c0740203001401405600010130461315582440c80d500d001200484610b401030002800d2482d18002e4040d4000316030711402842503180c6201815001c07003d180c1226009132103520b0000072041840700c00d9115 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 779361546 1250 779360296 779360299
    0x304051003110c060a0f0b040b03030415090f0f0302010909020306090a0203180105040b041b0b0403080307050c10050103030305150f0d021804050604050c090106050a0f1e051201080d0f03020306 85
    0xc3c405407a00600502c4450701c41d81c40d20000045c0c0c0c1d6500301e1910f0031140085040d0f4043d078501042444540c9002086405a42c00010b10400e8421015001c0703030b001205401c00c414503440d280c030002e02405298484000e070380c800d0300c07a40015a1a001010128001181d03c1c6512800020100d024084d0740e0b1300940c0c0081000b8180ea42c0700c6840300c209400c0d650150390407106904810100800e2048a0000c040e280d002401c80000f403515010040c0c05500442c0800740139107500001050096006200b00c0b2184040b44e010f1301c5071003401d14919401008248410750102c0d0800780064a10f03001c504003035030740001c01014800450301c440180440c6612505040703801c10080d001480b200c00707200315200e00c583e2103400149601d1400f45000e0341880c11031010030b801540000e006000040d00301042d00c40402c094a070030845101440000c070740c01c4245010101d1682e110388241c0c0f82182d44103000380502c40c1c09040c18010b40c0d80ea034a030355507681410700c2c1c5400003982c41c0c10440340b5a031180d001550041030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 779362796 1250 779361546 779361581
    0x60206012402061614040b030f0f091203060d2102010e0d021203090109140a050d03020702010507030c050a080408070905090f03160f0606091d0105060108151516140304051003 77
    0x21706003c030200c2603100d60807024408101208001a80c0140010b0b19404040c00c40c0401d090f0425031000780c0c0d00c02d24080704901d024004800149141c407184100100540c0001c40c050400c0d82c0301da8060319007044145088015420309915403402d031000100b0342c440c6941640103002003101c00201e00207a40001d40055400c2d500e0702c40d08400b060003000c44905031507418000d003e141d945494414540305280000c2028107006200341d00c0036030703040b20680300da40740c241c10840403940e12891b0950401c125900d000b0710801d0042008180c4a0f00004c52406031001041c08200a440f4003001545d1a144c034040c01a89510401500698500106504030000d1060441d803007502800d03602c1e0b1007661903642040c20590b0b90355101000d1218000890300544004100801807402c0000000b4850503000302594110041c80c1d014145a895850300f0100d600070722410240c8941400c0c13940910b021100c00309503000451450304640791000403044608854009085c0540e03c01d00201c107802074200341401011080 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 779364046 1250 779362796 779362817
    0x903020c0307080312092425020606041d030d0b0a090e0a150e0a02093d0509010609050d0623010f0b0c0a060209190602060124020616 59
    0x4400b005610050b240c43c2c4083e60320b891518410b50034414004054209680c0701400c03541c020000751051f0b071a449070b015251340c01aa81d500c000174039482410007002e00c000d0007800c481003070317980802c2c1903001c0e8500300c0d0309006000102006604044040c5000c020a400c2040f80264107151a88581d040c0b0801800401d103096580d15034001311240c41c4140002500f005404504210003d072020500b245940c100f000349091484515540e05d00300d51009015946940c08641c886044014600312040e00754030070740c2205c690000b00c80c40d9513080c02c04200312011008003c1200d180c2040303c241a243c2965900410b18035210401c22003105140c0c0a5420554034811900e0444101e0440c410b070401c8800c820b161545404262035090710194402c5481003010b10013132594903404100900301d60b800c07010158517024540009956032911004044c1d50558460b8000340791500460282e0480b600e0030f1031000c51300c0d0b0907008138006c22094000c0c20010f8018000050b019601160051000c82e01446c2101151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 779365296 1250 779364046 779364049
    0xf0c0c031803010b12010c03050c160f061d0c0307060809030313170d0b090c0a050405060d020c0a0f031b03090303080a06080d020304051e010818010e030a030e010b0d080d0903020c 79
    0x242581703085800d65140c1c0682140a43c050003103e80100818007000c0c54402c2401c030706041d079018010300600e09400c04605400740049500603100045490f02c0400010100c030b00d03490364885522000b0360080c059000c0c00503209000da81502d1061071104091480c658072840c91845842001c20200c6a0b00c28500c691140341411030082c0c45100064840080e89400c08810404410401000001d1900c010084070000301c4d480342c240e0f000c0303e0003510300a8640d03501130b0009010b4020340d8071070101c61048420701c10502040d44880c4440034082d0301c41d0080c28840d100001410700001d003014011504091040000030b204c0c545d050390112058500140d141c0c1c1380c00080341020315002c441c00041e440441e0a10243c5802800b10b071210f4031121091a91a2005001922050000308071003010113500c248103001c144290042c603040d03a140d01c103580d80c9990745800500180344041c5006255860680da655940c20403580c0c0c102000d070807444a5050035442c1001d03402070080c002044085000b99001e03110f1a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 779366546 1250 779365296 779365309
    0x313080c0a060c030e3904020d09020108100503032a070608070905010c1e05030415021005060609090a0e030702090f07270603110712080f0c0c031803010b 68
    0x1c0c0c415000030540710701550b002002e840c148004440c450300b003024000d404090445078a0480e44140b2100790803205d02c02c102000481c000e59007241c21900008107440050550b601040d841d038401d8030340c00015120016925407a4a0310301803103406510401410803003003164682c81a4400c01c2c240032844d48240c0d038000b58204030359540070b0b1020400c03c0702402041600034250901404083c40d1801c04031a1540341c14441c8950710000100e2611145201c50511900380101c03800b034504002e4200c0c02c80d5540000039900d00e0710b01444542c092920000c0780f40386c070300700d0212645408014200101a112400907900415400a04000500c410860f0340016140c1004551241001d0b207005416803070071040181107040d164034103980c0801084070192441c07240d1282d80050303960700e281c0010301e510b10307407001c00a0344215040601000391130704041010640c01481140318440c0c3c0101d104c05030321400e9031801d250080f4a402e1143d900140000c04a026917441070b102050030040010070181001004a4075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 779367796 1250 779366546 779366563
    0x2160f050a0209060f09010909020a030c0f090605010c05060708101a0403060c1719060306050916080319080a180524070504030b07030f0c02010609060509010b0313080c 74
    0x140c41c1c124902400030742c5881c01040303501c0306081d21100411681d4400080c243c040500454800c95940e070091410f5440300414080956400450640c0d00c40d180c405003e541801e910905421038101100403946501c02c000d410324155109004080070340b41d01c1d805540500c00108041607101d000240040c0c0c4c60009140341c9180ca103004401d598490641c01c012098640c040c2c80c00d41480026052540d049205800c2c2c1c0380d000d101c60422180486a60040a016200030741c00a0071803424041800342c41d001c0031454012a05800d90040b0145958032a60b83d1280119480c0014084260491126040c00b4482c50f651001c0760b554001501182c3c80314800f00109202c1c410744140d0701440203032500401c61501c021118211541c1096a40751541d8010500c0c8254000104908400d00101d650340d03009030840043d40b07142070414042d400e05031500030700030655445144043c074145040041d10781401c2c000d0303a05a07481424190f1550f039804e040d8012006001004403400c80d0100091008164203101500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 779369046 1250 779367796 779367803
    0x1605180a240909030314090703170705030706051801140105060c0307020405070e012d030c020a05060115141305270406060302040b0f0d140c0307030804090c0f0f0302160f 75
    0x1102520b609004040b41c0e010303040c1804403006c6105000c075203400000c10a0480380d000880e580c0c200d101e045003601d14042d01c00e000f0131320f10001ca00c0d2010080241c215522170103d0403410300d5450b00140303025080e80d00c01250708201c881c0000040c009410000002c00941d0002c5044900d4651240c0c00b00341160700c00c94561000405a210305082903038070801a541c1c9180d1f0341208188041010418092149074901050905656850001c0c245009004e0184115041000d82da030030341e910034211196194850b0a41d001588031a180d4a04c0c2c000a010340e0245035414644540e51800c04061160a40d40c6001c004401140035498000140101070881c0c4964400c2c400424803914500c140000c0e40c0c840480107108100c01310301003043d0b48071555025401030b040020f03501040009103143d030600c0d001024442d0140141580030040c0004040207000f2940c1c801c40400552207440c0c001c480000300c0415900000d402180800300c020710a4018044051400b44804140b40c1a80d82d41c0044842108084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 779370296 1250 779369046 779369051
    0x3082208040f050a0b030604020304020a12050f060c04030b0f0703151707060f0c06050c1e0c070f0602060708190203041101120c200106171605180a2409 67
    0x501450525100c41402003c0954101050905140c0f6420711404005e14040c001d6501000190079135449444620007001440d030480075100071814810b03102d103050319507140c003881600c2c08600050148001c0300c08407500282d01c0821900d801d0039110a846003d44480e0406886030000c4511700408003140000748121010392032030190301c0c00800e04000301944440248540c080300e0729082c0350001c1c91840191340c0510001030540d503d28050707689020351001c5041c40c00c0c02411041c0300d0b03e140d60003054589000c204485030a540c60301a180d00f42124021440160052030109034030038001c840712508008101a9040109103001d0607404a800858054868040c02e802503181940c20580c040704070480040e05002c8141c4d018805043d200d9003042014001d038035448c4805079410f00f0351000f000303803a01c41d02c03032030301c04105424459540908280455010074049400202031610300202901c18080700104c3c0746035511000c28000401844041d1703d041381000000640c20310026807400080c5c00460f100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 779371546 1250 779370296 779370299
    0xd0e0604052b030c020115080717061b0705030c01110d0507110705120a0203060f061003020301150e0301140c040f140f190e0f041101030c0c0308220804 67
    0x1249030070b4a107201041a030044003010103501c0e040900c8082d40d0500e030300700890a400d003400b0882c01800d20344504058504c01c6600403901c04d402044400031510240614030485640c0d44565446d140c0aa6840c0c0c20418000c0d14100c010a481007d8240140104141c03414200001445801c0d1046805e001d00311100c00a40c540302110507200701c40e04041a86803550450900110b45a51401e40c2c0c09040c0c0f19079030350100e03010b048501304414011980d010b01030751864189512a00c24981c6c050310440e10a600d000f04410546202c1e10907241221800248862007001d109400e448800103211415050f540b11138a10704810003802855000d00c042a0907250788919204015070320086e6038100091a41140180900a03601c00b60100d5629000b00c0d0801606850320050008071200c070f038030801d2404000801c0000001007001d81d0b502c03640c01241384001c0d1540500045080320807448401020806803130040011038401e402107a40b00860740b54200d449900313048000a2880005d0341101c0d80000085c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 779372796 1250 779371546 779371553
    0xd0c030807050705100e0a06051615020703030b060703050720040203130209010603060e0606130f0306020d05010902030708150324010302120f0a20150d0b0105030112060b04020d0e0604 81
    0xd0345c8001071050300e00064020700c144001030b0661600d1089400700080483d0201451242200211310140d214884019440c1201c240901a401c07104007500800e243c401c400300f090615030110b8000b1580b595602e413421340385544042010085101c20443c1150700c021568443d2100d10003540a441c1c1396100ea041d0031510f204100c400303001600b0030020181081000c10403070001850f541d811040403140c5075151154524a02c48160460780000101401c0190002c10b210042c3c3c0202444441c6060600140c0e07200c1035202c080e840141c400307000141c203540000e0b8640002e200008041c072001410f4800100b0030002038034408840305006401b180000c0d0042046292a076000c000d03801c100d0024000c02c82880700d40b6138452000c04e401400d008449803088070007000050b600380c0d41d5000244046900600b8071004a41508240e82c03092059251400d01d151560044041d00c0c1261207040341e0444070032540d641c05019100c4214503070b411580074051600c1e58003603402031200c5401d03914000d1419207420306 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 779374046 1250 779372796 779372809
    0x30b04050312151c0501091712070513060c020409020406060905030f0606060a080709080601060f1b02061e0418020304021509010228020d03020c030d0207140d0c030807050705 77
    0x500c2d04002ca07640303c0c018096519001d500e4040078000000500741c240d130302d04019024013000c1100406500700091191030810405014045100c0c3da1503c42c40a41e81e0f05109076024440c5040c1c0d8a8600d210b5202040002d125505a10480c3e2003c0c00c0030452080e281e0100302524000d42101010404100e01071115003010030190900141c1c0d10f005003001d00345903002c2152441070b41841020028030a002440305806410084000c0c0b401d04100c498545c0c0d40c900c000c1006840c0c02d100d038009644032400300e0405440c405022041a00140704900e806042d00c1004906034680040c540612030900c03001820803040c1f40461031540c0031610250340c0340303418410051030b0031496500c0145c1110600c0906885d9a00049001141d40c4155482c2c121481c2c0b11003072035410468880c000e41c001e00da1801201010b40c00b04042a41201c25000c0324041d0203050303010f98440d0030300d000d01d0a08400d08496865207141002c1501c03000c50281c2009212079469844020007030b07104034030a49041e401340c08100603a0030100b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 779375296 1250 779374046 779374051
    0x5030c01020601120305070c080304140f090601092303061503012702040902220e0c10081605070f030819060b073201051b04030506010618030b04050312 67
    0x74405098a90304200c81800000f00d0340d00f02070104007000c070f0180308005c40b44420a0103400b500040320346681c3d449003248101c440b00d0204501031200600d0803041c0c0d0811032201e901501e4140c454010440c1086500803c401e400300c1044951324400500e4402a1000d0203a140111501441843c011400000341030039140d001c0620882d41030600c240803414510582c88030703491b075411203001c9140c014500004402d43e05441c0d00221401c144400080280516800040d02182080c140c074140456041000f0f035849203130018002141484001a2b100c40d04003400c1180715055041850920103181c54224400740d24032001c5020490300d2040c04401d104c030011103a0300849038038060040a0810116445a014040008080d681101a2100507118045c0f45100c4104c0780c5054000c50301054800b140130741429240c102d0721003051040022080b0880040302d06603508100107140d664070301201202c109103150030034000701310a1030000c000103034030700d4405004602580003140c40b00003c2204801f0703031102 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779376546 1250 779375296 779375299
    0x60609270a05011a100e0301060506220501020c03030f0918011d09070302010903060c0c1b03060e01020315190b0a050a1d100509010509120703380903071b05030c 71
    0x10f09480d0502c0d514024203868103103070343c035006d81e0541844002c00e014203035542106500c02d40c00300302a84050300c0101308489186040000d00c600750f50307c01c010390b1161092504d0540581040054410300701056001b421507110141103c80c03490028001f0a2040c0e10a80050150103030448010b28030f844008610f54000c64200c010380103072460341c1d0020b00301d603429100040010303848000422038103005480c01e025145e08003e40b1014072a880d240310300013900342d00040b1142440c1007865107180380305109072071149a101f80c10018080e0303198100f042c41e02400001c5460103800400102d409010100900306050781903d402c0e4683c0c4020201400e83c2200d030940100035403070181301c020560352385e03124070581c94440d040c500e0380d400354000100c52a10401522a0700081c070070301c604101101c0014030707004603070083c04544848402c5242c1490a0005e81f01c0502025000843c0c0c4070300c1d403803c100443d410040f00d804507850040f2664030450400c0305034014040940d56050104403d05091160a561110 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 779377796 1250 779376546 779376581
    0xf16050303060126062107090615361508010905010509040201082806030c0603270b06010e030d0f020706051c02030403050705100504020a0b0c060609270a0501 70
    0x403540080c0c1e1440c00000c000510a400b00c3c034402090761b2000750780d04551660f031003d0390740c1c0360784407805c0d02c1c0901414440d4140e45c05000c61440140b91068144501420720100310002e01041650603103010301180100c25421000c0c60740010f804124403243c14030b89000c40d110505558035040301ba00407123070142d1040303000700c40110401c00180c1e8420800c0b6806004ca0b002140300c0040343c00114041d003500080300540516005000c0103000c481c81116003103070b0560382c0500888689100000c4000780030f030807543c1d000c410600c803c000140042d0110b40c1c84a01854424405000040041c4c505119154403802080140c0403006049a0501c17480380500a5401c104e481c00d40c2c844001150444a83c0c40b8011441d03021020030200f5101d4401c883d90b0326005412500b01c814400800c1c2e0003400151070403886110f4031080000ca040c4688180c0d01c10b840d034600548020b5844070180300c45a00c0082440035202284001c0d1103801491090f001402c002c010010000b81c5400d2400d10b0848950140d090314294 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 779379046 1250 779377796 779377847
    0x41809110f0d0b07020c06070c03060b040c090e06010311070b1008030306010e0103180803090601082512020a0510020304050120060c1b1506130b01080a020f160503030601 75
    0xc41c2e8001842c0b040364840402c2c042995800310881c105900d81d030109500c9000050000140401000f0440640f8018582001494044070822045803594020540402d506440400410680303034600342d4401418140030078011a50210341c0c910354800c0c5800c4804502020a1152441559441001820840700103500c1d608181c0c0c00a095040c0d20394005041648441c400c99042c903440310850700c110783c400c1820f40c413400c0c2106056202d02d02409141e00d54814031851102da00415440303195000402030a2215841c100700300508a2002e42501340c1e002803c4810004d080d031202c601070400640590301940d03c440c180800184400100314181080441251404046c410041021a00903100715803840c0d407100da044803040c204900303412400c1180904c0717160034540c625400b038075803241c4021600901c01c4c030520200c0e40308440d01c4d001e81900252100001400c00c80d183d5008200d01c01b4412840c03800c2803c102200d005030ba480c02c100f154940c00110601c6910750308200826528407801c910448200d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 779380296 1250 779379046 779379049
    0x90616050f0a11040e07030b160248120105060a050a080d0c031e0801210c1a04030209160e180a05100e040f05060a060803071106041809110f 62
    0x507003080c83c2d554480d0341d5404041d001ca8404100801c011580003140c5c201900d0680d2445013552012040040036003d00003842c005d4400d4541004000d80d8100140d0141d4010043e00204004c1584c81643c0000b51b0350151300801e9581600d10180c104c0c00400229151603d0418402c010f003440e0b0005000e001180c40903c03da030400701d0400031451030b0789404501c94040c0c0c10216007140c402c030004400444c84100025051340c0c0512040d0503141e6802e86031483c03450f00c007401c4041442c040c2c0040c01d00c20000e903042c000080e0b010b0184200c000030760f031303454103160b140d40000c0d10009083d16442d40c07000684081045054101d4804440e0350b5044407203403081d4100300c0700343c0700d0086c0040c4038030001c6030343d88001912800e01c0803095000e00344459a4070300d540307498074001d6210b058621301500c4034840c0d90b00041d1407040b18024070050341c401d240035600300b20240da10400310310481c10b50154000000c0c440416054641068060781020300d51001c543d42801e8185402072181800045024007075a0540b4101d6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 779381546 1250 779380296 779380313
    0x2010b03012304050327010e0d02030a02100908030a030501080609010903020a0605071b0501050a0518070605070c0801140106180b030601050c1c030c090e04020f0603040305090616050f0a 82
    0x5205a42c004022a50f40d24503010b0304505c207820074031601004101c10720800c2603402d02c0c80300c0c0c0186c0a80396903518a0740304081004100b0640c0000750725502030042e140050910351102640300481342483d030019a00c0701c4403541035400c82c000e84e0740026a035600400c0110400c1010680004046008020b03095031900c0007510703111070000140c400e80d1241302149415200d00518014900c2d44107003a811080c241c80c1c0b450282c40c080d510030440900308000701c4c810720000701c1d1404050312010010034895140020541c0c003170f08103072400d88000001410020b0271401c207004481e41d0503201c401071380d40c541c1000001350801501a40501606454200510524a0303e900322500400e0908040d41c4400c00e0056981c40d1141d000208a0301040c0315011020701a0150051200d1000030b0301e0306c90ac2d0503102e16003100341c01421034020350f115464800c40600350230801c0c02190068041d250641c9091085004101a54401e0072050b00704d0400e08080c4040c00401d04c080480c16510002400d41d004450700d0303000c1e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 779382796 1250 779381546 779381591
    0x3090a1703071e111f140603030901030e010f020703030b1302042610110d060b030912090d0507030506040209010e1005040b01090801060f140603160302310602010b0301 74
    0x185450039100d000c40e0f450180c03800d8001141118201d03441c050042090070710310f0314403421840341541004900005c04101485481c403401d40a0000c508010005c40114080c1c151103a41070079655030b801c0d01910110381800141806802620b0102e06da43c502170070b01c0140d4034002d00e6041750600c1400280440b1660341c5451103042c200b050200b007400b500e023501d50306120b0303041291002c003864280b1041c0b00d45020400350101054086040103503e640e8640d40d03040f41b10441c0da01c0e41e640c0200341281120300160001e444d04440c05810760f80030b900550398451800210347c0041d180350b03011002b04000c51801040041c050620400410140c0c100001c2441c4d010312280216482162100420b1043e86d00c2000e613003000b07288034002485401c0c1d8400d85c000030030301d0034003c4c0e007a6012410846101d40c1408803c4a000e030224804685001e00c41e580110000e4001c40740704c200e068613232910020044290000040d840c40c401003141d01d01440d040c0003070308607620a10701901990501c1407203501c500440d001101d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 779384046 1250 779382796 779382827
    0x12315130b0a0305010c170403020714060d0e060709060509011416050d020f0645120318011404060e0a0605180601060f05040509041505090a0c0e04020a091d010203090a170307 77
    0x1d4800100300000d37030319004411b00341d0b0b40c00d0700d001540c182c02500044c8080c0100380548552000320745a8038119018030442900c41d02041c4111502c0580800c6030b0003c040c07074010452040c4844a0070b5441d2803c0c0901003800c000181d20260301e5000258040c00101c6d000340c1401140d01d40041c80c030044d01030702107141002c0d081584000c102e1502c4140c09091400c804010002034401640c0000d04071165a08240c5151410003040741c0802c00c00d0a0510880118004d5240c860489507256070303d00003d42183c03002c1000e21f02034505104001110384c010706d8000c951500d21200f51807103102c1d0740382ca800c10580c0000c0030444245c0403010305a4200c8101d4007501e03015a40c03c800341d0b80341d040084112a4280403145040c1c07415081011010012a400340c50300e2103801e02581d129034400080c4c440e020155400b950006c500c11003080710103d20b5200d140e0301d29000407a0210039404007495070890f041200ca00596400c0089204100203840d5001d02481341906180d50031400c050f00c006100511946650 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 779385296 1250 779384046 779384069
    0x206061807030b2e080f070522030204060e18010b090606250b1611030409020c0a023105191d030705012315130b0a0305010c1704030207 60
    0xe070703c1c0e02d8984a1044071000c0240d49002c080501c414921000c0340343d80c550b00060818000b28007a1400400b1441c09015280d940c01d040c0030211520988110b40300d2400407100300030100010043e2154000d002c000c10001c4a85900c5103051205114001c04000c00c1c540e840e4502810155155174a10351640c0000f81034441503140c41c4c0d10011045840d0504d4a00c22850944280740e20400045291043c4140e105c0c18501052107074030320341924948191019480e1a400912042c06903080d1a07000c0c0031580e00c0c060458807003025a4020810481120526160201c04003040c41058141303c4c01e82103a40c4441e00d010021803078806100390040f804002d8140225450b26150f1052030402c80d079010040c4000f6003a44d41e5004540740c01c034024519240490764080207400c140f852500c203204403512591030522207072048036613030381000b040b1403004915000c0c0a0f916290b054154684e40500c8000e5445100000360341c1441d14000343c59400c0a4004e00c00c6060741000b04800643d000c1a020201c800c8006039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 779386546 1250 779385296 779385311
    0x16080307211209120228080a27060f0f021506041b0509040f0612020d08040b22050a0f0306090503071205090a0b030105010c0809060c0d02060106020606180703 70
    0x210b0381c0750303940c11505880e01e04002c0020b05108001d0f6604540101c26001c5840446800c0804000074001c4040312003142060b40009021030f081c20001c0c144820386141501c4c035403106002d402da0300246a0a0280c400704c01c61818045250016919820500241000c0d403a89510240003913503000d148854150301181040808d540e9203480d04040000120300794242c1c212440c2c002e00402e1034101402c0030b1700c01c83c24649072202c042d40d10710a00050b214240984040d0380368907001c1c811742004520741151820b17800c020010700008203001400303414040d44041e00e1000807402c035420450030700e500003e224003400082040103481c000e180b40201c03035002c2c0700481c140c440c81c00c14a040d402041d0000d820181e16103106c03c1e142da4410700400a00c402180d03184903454450508080320b0000340a9107001c61544100b104c046500310001d0045041c1c001e007501d01d05400d40044a0524103103201d100c015921150040c460342ea01800701a600c4001a500d07c12880e84640461007009030107000f04052507514020b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 779387796 1250 779386546 779386613
    0xf05010c0f02060c0a03030b04180b1e0c0c1c390c03051009170c01091403120a0207051c030212270c0604030b0717040516080307 57
    0x6200550540080c407413911a1840d48120340c448200700c9089001a141040300a800c1c80d15119040c81a1480d043e003e00b13400d4036a0b00c08081d140080d04521460084061030320300451340d24030306407181d000e4954035503d4a0303408400b50312b000c440002000d2424036a403010441c0940c8210f0402c50f200460300060320301c00a440d56101c1d04070000d041c1130b10314094070400106114801f240076003100c0c803035030480b03040750094a0000c0884400e901c00605043d13030300c0e44100e00905084098120b60000da0000285446a940c8115074001886501456608086102451140c10030b28007503000311409419803411085a079125181c00700219000c4c52030750100c464080c1f4034400d0741940c200580d0402c0c020f149081000c040c92100c8000d4000d5060b00540c0ca000d002c01c2d443c082009540310402800e4281014213650710103102c410010640b504000710200d8241045081e42c00c018025406507010700300c89607101080280002003030300010301940c400c002010004e1451036220300520800c00d000d41c5035800110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 779389046 1250 779387796 779387813
    0x1a030606090c2a01060312030c1d030c12060403081b0a0309080412060e060903070b04120201093c051f0204091508010510030506130f080301080619060f05010c 70
    0x18155a0101c00350343c3c100701d4500055100e079042d24003c21103503144070040d500460a803481c1c0041000000c0d00440c1d032082200c1d01841e004c041c0d82008099501111403900415402010b001c107090866024105020134540c1213400542c2100c051034510310015181c0e0880141440380310380301ca08059440365450140041c42040c0c601410341072241e040c0201003401e01d10007511403c010401b0f80e019100215559000002c2113652880c1d00c035500251a80c3e541e22004400d1042902e00401c1d952948298400a9000e8030102962511420100180a2400f0001c80044d420402480d0032441000e00100450b100181f2045001010380000c044015004410f801a0043d980302c001c12504140c0840340c07410100e900708046e80d210354000c0100740d60343c00c48014502981c3c400a000c58102d500415a089580200401c0c1e480c0502401803000c222070b41d61514550090380001c246070003020030300400102049001a42101802052000c0c0f810506040c0200b052803042c1410300140346a14401c009262 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 779390296 1250 779389046 779389087
    0x90307061b0609051f0e0705010302091f090801050106050906070602070f050d2001091a0705040e0f0f0906090d030b010210020f040e130f02011d090106031a030606090c 74
    0x51800c0c44100f007589003040d41c2d104452440c0c00c070b802c0c40701d040c102c81e00301a00c90f10a21107a484000c1c450365240400641c001d51040328016008441d5541a0040409245810701c4824a69541103002454601c25a003116011781045040040400400c41c4030398840c0151020150002801a620000c52400902c00e14854800030320368050304280d0051030341c000004411b0340d480e10521030349105001d06410708941e0f805d0001841142c0360800d1200001159040b158020010b040003131400f03031100d126500401c0d0403200c140e00d10681c2c0040014068409200a40108400d4024a50b90600328455030301e1b8000c42048070704140e0f03908083d02c0581c0c4204020581c18020060440d90b650328000d00c44003076441401185a0031541030081501f40743c041100b100c0c4079401803280101c0c0f4649500440303443c1d4140782c01c41241e818200d45001e0681e101c4000e14000c10040c0c40c00100c1031041c0310f02d80c400b403800d0a203592294026204200d1162202c5140c19881400000410b0380d607410550000b0228060 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 779391546 1250 779390296 779390303
    0x10150512030d05010603021308010e0d0f02070f08100f0203040321061a03010503010c0908030d150510270e0f06040e06040507030b0c03041e021f180506090307061b 72
    0xc3c400006029074240e402804403516880c0700036802901c594003d8280c581494810880398440c0a46803c0e003841035040343c10070031451040d1802170390744006030302c41500c01e50404d5450380c1050b002d1800160040c8210981054080019810361610742c038003038419000c4560144918000320b80114650a195001002034002c0c0400f025405100400f02d5a40303400901038540250300e008403c0b5a40f80c06071412004a50009000b54076107120f203d2188017510801100c1d401007007001c040481c440e9074840710144c032404c07140d940c203004600d18180c550006e50b085040c0ca8400090320410711845081030a80e40e4000c501c2006440252102c40110700100103172210b100b03043c0105000c0c88204039000c030348001224080c5889102580310480100c0e19488140c81c0108035000c0c5481544484080c425034000c014002801d0038031800ca041c0700382840d42c03000d6407480300103400c0300c0030b2205581081c03804001602099a2a40c100710251020030390b6a02240a440d05104000180c04104000c0c0143c18044030b03030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 779392796 1250 779391546 779391551
    0x40e0403081f4a0a0b0d02100c2303181c14030409060806011d060607141501150318121b060f050f07020d23120f04020310150512030d 59
    0x42829043c406101e0036202d4401d002e00b070003452040c0b4a4100c0c2d42540803134004101c0540308480150980745500c00d010201c601240c04000401891100004500d05044034800303169034034617040c4520b00c0010010340310b038481c0d642100d201084a60a000c00400241d10500108000010010181c90342c0255403000704c1c0d81e07091540202c1c40220100304203048601030b0060341c075410807440d240e0441c01c2e07040b107000da040795051140d800826220985203402d0405501070b0f505240c4845460280038909800030207402840b04407005005a15200c0d4040e03084980040840003006036580400c10001c1c0404041000482e4020f40030b96612840784808403680401c0070803030301c290078007150040c0604441c0c09021240302000105802d0000c140d000311904c0540d950000c269652000304c1581d0204401550301e94400d0007083c0103103042c0c04c03080303004000c030b441e01541e10315052040618100c2092121a107545c1440c3d03080708e0381580b00d01d84805a0f8001c4407101c501d48400707652149180140e203803207400300c1d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 779394046 1250 779392796 779392919
    0x70c0c0e010b1308010c080609190c050a170402031b060c010c17060613091a060417120a090b0d020c0d0810090b03030702060f040e0403081f 62
    0x102403a0060035943e141442c0c2203a01030307456081600701c0301da507500c200228401c180066200d1410300100e95100305241030680c1c01220030b240701004c81d8410886000451000103008001940000012400781d5109441d40d00354070b41940480d48489461403414244007650000742165640c10b82583c281d031260310001c10007101e5940008042c2c40c48401881c8641e0144000f1494604050040b01d440b139902103002e00f0020320307080304070005140250005015010702a280f401e25903410000703100030304000050000202c91400020305206140010280301c0070200451015180c1001100e03040750824042161990002c03421403000c0c1c807074901001064099010191000d0307401c4450280602c4101d500c400f070882d22141c06208441c14103100030351690042c8003a20062800c00d00400c2d821404076441d500f031640e111412151400103684c01c4002c00c01541c208040751850904d00381401e03103001c40032600d003440c140924440360900081c2c11504e25003e06410004407072403284521103240c0703080d06040103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 779395296 1250 779394046 779394059
    0x60b0a051201050d080909091e01060f060e1e01140a120b04200d18080c0f0303040b0c03100e09100608070b0307050706060503030720010314070c0c0e01 67
    0x1d9019010360326a051400001040604201d40b00c569250340c015403503490400c0300010413400910080241c5480d11500d004410002c078181074041000004030b00108115003001c121960100c5290040d50820001000b609459661682d440e04141404007002d0410303040c060048034001c007226440c440020000401440b560b42c44160442c2280c03520307000300000c403110340800041d91620028620318070038810b070040e04000c19500400c018441c0c0c800004461b10100702e000c08203c0d2081e003d94440501180c4840c141c11705105500c010f1040001035499880c0c40c1d51111540c2e003024080400042000c0001604002915044005480311900d60213583c90403028250380e03441000d00b0302c50064100040003c58980014002040d90804d82c0f02e03504544e03800404640355045440c0558009440740d174005000c1d1014001061000d01641c0c40d00301310342c008500007030300829288600381014909000804001e083c031b2000c0303821010900c1c00b241075561340d003042e1a4402d066009000366035400b90000414 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 779396546 1250 779395296 779395307
    0xf0c0c090f090c0d0c0b251b09020304020a060e0f03160f05040905060f0601020a0c0e01140d020a030b13021c02030d0908030d0b0d051603150903170a060b0a 69
    0xe40000b208642c0e0850702c480c20300200f0001d00c0802090308032107180621650750000081c04007101902c025420045410343ca2441d1116414420359040d10f0f807e03011a060b405003009034004e8103c000041d8070f1801e196010900d803d00612070f0030104201c80700d0052240c0e580b2004400703158401422034105d5103081d001c09500c05242d208200d40b07500e00003000656410a40501b994958124000d81400d0b038844004142c61000280300a0443c09800050800a070301200141c0c05841d08045084e01d642c14415006080d1020040c0c0d244900d201c80200801030782c0300006c00b000d90754003080c4518a600c0d50400410131544032580203501c20301c40e18083d241d040c5410f035048002c0d80220212a0222840501a10342d01c1240c010782c83c046d04200404a84240d154124404002c00030700380201c510400e4640c54100214104001e48003000c0c3e0900b00306100d50404103268020754208100300c40f081c0c980d07001d0058086104800c4075141c1540014805615aa1007031004004002481c0c3c2e80b40b04c5001d00910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 779397796 1250 779396546 779396551
    0x31505070306140a1715100602060c040e0417041802030a05180a141204090e0114070f180e04152d0f200403050615060f0c0c090f 57
    0xe03250200c0081c1e540c1c3c0d0f414400c22241c0c00030340003c030b04074100341200d43c40b40207210a68010f4440c40390100841e60709041c03030a124488030400420346070b042c414028140f01c0040d0802080a0b014013091241c15040b0301c01d0381c1c100c2d07481400f601040a400e21040c07114040e50303000001c07101e801a280c142c109219001140306041c000000c005590b80e40a410504c2044038031008500c0c0d100c40900c8002070040310140004888280c00c50f0781d40c4e031300c0711b20400d9194000e4125400c0c0d551100c0211020000900858000740c0d2861000c40441c5007850004154015219104042001004440503c224034180000181c00da03402c100707100e0710b000d040141a80640c03d5090002524240510450441c428010703410003182c601c3c3e10020392a81c02d85180904010422522a43c2c0c1c4c440e031003040f128001041d0b00c042e002c03040c000c5450781d00d1810715078144100104802240c42080c0707008140c503500d5804a032580301500411544984a9440c0c3c01d01c1c005103031000c1508081c0b840c0511010051496001d0b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 779399046 1250 779397796 779397811
    0x102100c02160f0b0f0c100207060605030d0311091009090204060203030106200d05030a0f0c0f030e01050c030604090311011e06120b0c0c12040e090c0109030f0803040309031505 78
    0x40d191035448a40c0f540000607481003030900d801c10f01ca155441c0c01400c00410070300c12441d0442e09a00000c00b544001caa01041c0115407440d56010700700404d040510903000d0300d020301d0a0400c01010044103c40c0144141401c1c1e52150f5030501c5007460907401058000e003d080c0c101c00840d01c030b0f0703119000659654000e00580010580081c1c240b4030995903544041100e5801401412801a000710709039000d420180900d01041d4803862803c00c401070704d107d0001c01c800da5584003900c007000004040d088a50450340e022440c0d04040811804003e100100ca811102c06d07207000071081e009080850710005d4407802c0030030650a111104040d20180d81400754101080c0d03c04000f0b4031350b01c4400c03c0c0e640b410b40a009084501c000c0c0012000f61504001c0d1000800b08000e942001012070321044460b84650028111503134060240701e54600f0401c20704044110030300340000d00b01d04540310441c1c01151140c004140030070000005040600c01c21a07100211350152082890200c13000400b40900f030201c4080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 779400296 1250 779399046 779399083
    0x2070804050f060703120f0605090a2403050c152b06050f010e040f1b0c050709051306020708131805090105010b070f02030102090907020d0f09060504140102100c02 72
    0x81c2e80c9850030004070307800d80364991100c52a10300c0d132140300805041074404550704255200f2001803541c444e032600e030380b00c0d100c030040000d0000e9004201540d410140e0510408001019405000181f0005014030007584100e032603000590702c0265070352a038420316403100684458a001d0320400d40113030266401c000c03180002404050389a0040c0300081c0e081c00700c020300041e02200c408104d4140381d803040810800c0c1e0103022031008407000e50300c0c180410301840000014101c1410000b804418040340e0041c0c01560410701003800c208000d420414034221000c4c1c916039000802400b00107244003110314003c0d4404211218954a0300080b003021040f0342007114160520340080c0440006200e01c90580703202d27440305414860b0380d032100c0382d0b40303c0030000490305598200003025540da83c280031981700764015401854042e08000c0c0041c580110b02c0f00502c00c1c00464001802026003205c01c1e102502d240c04040103c0c072014200403441c2070480c100c040c42d8180391121035883c80750302043c4c0c1050948600040b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 779401546 1250 779400296 779400319
    0x206040e040b130b070c02150408070314030703050712050909251e030903050d020304111302040b070b0603011e0c030606021c0c022b0b01081b0f0111010207080405 72
    0xe103280b4036683c100051014500d100052100350250005112290002e0300031410186a410b8280050703006030040621903019640402c1040ba07410304203000d052044001e1418141c0640c2c0251940c041c0900007488030b1850040c4d9010300b4807038000e640f444071000300359511034241000c26030300507a1503034041d80380483d4414440c60064026240800c0c038481500c4100112454540c041700145414a012402c020341001003214150460010f0740c0a1801810340e000700070303000030400200103103625881d50400d0050108020000e5000c0a5824450708030b003015000b03a4402002a00520215109440c0041e0094801c04040215840175440d4186914200b1040c1e845000a981d46c080d50500c41405000c6000a010124403400c0d011090900c0500410040301844101c8890000721300d00700180120142a008144625006903900500c45840685411003008184d40300c0c600305c1407001c134001c0c010203101d102241d12810500d045070021000842d21580d092170100220351241c13184078820340280d02c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 779402796 1250 779401546 779401561
    0x40b0103090308060f01030603060e0708070608040f030c2d0203070512100207031418011404050607022b03120e07050a0e060d0c030302010c0906091d040503070206040e040b 76
    0x4001e4802d401d83c40e4020981e42d410200040800c00080850415880740400030006044d40030f0401c0c40c0060102400501e42012005171801d1070940c01502001641c40a0102140d80c0c2c0020610b801d41500d440d0303901c00e020341040c84504030403802c01c03ea404050100c20003405086c04007080307424821811b50b4840c6540d4010403c18010041c0e800b0703900d410194501c144240e40e03034020220305e4420b080c84100349045000200301608800344602020a4040c4840704560b8801c00080e80c2c05a0303240d8090500d418140495054003034044024011481481391005400c0f070416001003640c001d00c00807414038010300c3c000f08100c0b20701998009650500c0c2c4041030055005c500c207829181c5c06020b40b00f44510308101322001c4a030180c40742e904280d1040850340440d080300340b5200034600136000400e941a031094007c0c84001994043c00401062340f009100d00c1d550580300501040f49404d00400b1501c2d03908126040d0b10074807500a51103240002c0c00211500000c54542c4100d0090030038607019600c80c2d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 779404046 1250 779402796 779402801
    0x1409030a0509010e0f0a030c0608010b0f071401240906140d0201230a09030311072106060f140102070806090601060c0302150f0a0c02030f1818010e0105040b0103 71
    0x404980422001d205528071548900e498840c0720070010801a160341c01500850013064036504140e07410700882c4814401150816030f0ac41c01050042d141628181c05d62a6220481c02a407030000d001c0e04807410103100c0f4043c25000724480030821668460464114040705c0d405410300e1103003138210303400c121002807241c03840c510700d849100015041415070f420355801156421210032640300002c000945407600e80700c2503406070205408030341303420588d01d046040213801c904000052a005901100e828840d10f0783d565910078101e80e50405012885c101460060040d0034960000c14458030381910001c0c00000340d1942c201c1c1c1803404c1e02030310036941d1186032807511400c0071260b0b403e0b103902610040181600c52102458498046c0c03043e103460012400800c42001c10540f14042c0825004091040c034582c40c0c4250780003010940025841c100d0703070031071946a500801280c2c0c14009000c8603008280d4484c0f021468842c80300c074000700007540c4c54260080e0744030401e01419000d545003000b03100c51540a031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 779405296 1250 779404046 779404057
    0xb040f09080409090c0b0a0807031409150a0605030307110907080f010b1c0e07030c0b0918070306053109020d120216080a020907050a05030114040605090901140903 72
    0x207141a4034280c01c144240740544a07010084034224944d040000e8004800c9004c1c0c1000c00c80c80c1c0c1c500c1443e00700100c2c01002d0314808407408046071440e0051103400c13030001405000700d083d014040c4103030343d0340c1860038030080079658085600341c040010201d0030402c140d80c5080d0441000c482d1654144c980c618100d850b600708840101d885120100148644100507010b00806100c41080300d90b0050a40800300a880d0301902030240756000407010300400079080c402d04098005648524280640c030740000b6803034a164420300c1c400030004004103400754401d8000c000901000381c4120300c402642c81e40810707500a0340800f22422400180c02a0171071000b401240d510907001441088051050346174201020440300f4420f041d481504100351840241070408001004c0000140c14000d85500622425580007081101040010046040300c190428196810360700c009140303040340000300c8045070040009811a44d40016a1010490300040c150000030025034a092480c1040d12001071095480c001c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 779406546 1250 779405296 779405303
    0x70b04091a090a0f0213120203121602012607091503050402061c0f18060b060a0207210203070e06041b02280b1602190f12050c100b040f09 61
    0x1104003043d070b42419504101c3d01c3d841100d50040c608404184103502a43e00c0e54082410303402c90f4100c140640c9410300030319491082a00b0030318a0001c42d28108000b04103e840001e05220784d030f80900c04a41c1c1c03141c084140c01c003941c2020b40c1207424070240203040e610140c41030401c4c10350207061101040f0300c01c0c01410301655009c0d19079070078441c6880c0c00c80a0812020a00c1f079481da500d20001100c42120f006084c01400240051990340c0301c5410101d041d51580e220341030140c4000c10105101903070002e06242141c02c92029203043d044003100d003401800703240e40040e525108084000c1442207640b6016402094204c804200100441044101c0b000c0c01a810b1400358011b140b5010810060154607100400259190605440d4076690800c150009503600410305501c01300b80d160040d0108000800c5031507460b15441f6000315035482c503c0078555100001c00c2c144840c4812005940968181c40c0100580c60a507410504c0202e0200c000300b12840d262171040e410008501000030b1144100e0a400f0341 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 779407796 1250 779406546 779406559
    0x303041203020909010303030606090801090b16020709050a021902063d08061e04110f060d0518070f0b040b090109180902241614070b04091a 62
    0x45544544041110019100041c103400b0400b4a060741c0e500440079002e18429140011002d080800080c6508034542105009a25205542c0045242c040700d01e40c0c00804c075400500c0004258000700d041c03e00c594820384400b402c00d018000c1c1909560098500c0d0480700280789105071b9900401c07030380c80c00103a13010f00000c845c2d03c1c0140b01d031324080c013481400d0f2203034945044070518000160340c004409561000d411b50f0042c00c2400310908164180050000c10708010b8504d509164030744140444072460102c0c415034510003655060340724030058070b0504518000410507840c1c0140045404904040c4c01d09a0b070080c07450109070031900d0140213042d01c02c41e003080c80c207180c20462100000e920014030a41845074800001450100c440b40c54070449d200c0071004902000d81388103002e10206500d401c00200166084812040c0c00d042c015074030490042100d841032449142840300b000a10a01d02401c24007036104c0c049603056058005104880b900c801c10461180d00d2101c5c0b0151501e6484816031008 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 779409046 1250 779407796 779407801
    0x3040f02130b060f1306050405150a14070b09070602011a12030424030c0309110f0a08010501120b0c070b0612010e030a030c0e03010905280206210702010e0303 70
    0x34015900c20070014a590700242d0103010384001200c81d0060340c2c0c03c41c10504005000ca60003103130004014010700c541c1c14040e0610703051100154074640b6846503c09855800700d03d410350a482403410442c2030035603803169641c0302c0f070506040d0003c4000716200882ea01c1180c1001602e64414424102a9040001c1d01503005400d14100f082c0311a608912400620040c8004614000d000c01180b03c1c0c0148c41c1440481001800000b805880031482c1c5502071524103201c0310040340e42d04410704a004011112240c08040441c000385185002e90001c204641c40c000020034482105c4d5801c00c5124003504080d180e5a5541801e08200d1140700001440ca03110700003c1907483c1005006640d042184100200c9e41c20b4000701420324680040c5407040000307840d170160520050f04007000742e041b0b2000360003d021080640e2181c2d07644030f10250030440c0106040d20400780428a0070702083c1c5080c3d00400255441c00301c86044240a1503d1007202c0c01d0324420000b058006005200b0f010505000001450031075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 779410296 1250 779409046 779409049
    0x8040519141606050f07050a0501140717010605041703070c0e1506090307050f011407030e010e040c0807050903030d0212271c1e02071e122d030503040b060603040f02 73
    0x42c2c110075021900e521810305402c0004100307015098003100c2c01e031820307802d43c581420008e00402c1280b40c0c4413710032600d0010301c10f07503900000303d07000c0d9405c041022041c018510342491444c480e10001500e9418442c2e80445d03114030744208a40612488204040f8400084c82080b10034440c03441401d500d0b6006210400c5141040c4c1e69800c0c05a2050418a03806030305070003007183c10390242c501100055400c102682c1c072586c000e2690b001c0b01c08140c904003da00011000605a400e010304418140a80440c1200050360200100d030f0340c41c980c1c08002d41d01c546040b01021441c01080e603049444001b02140c000c183e141c420741d4000000c00e1000184400401e0344031030f1a0500d05101340704104441c04940415020215600342c030141c2403907000b0f10720341b86031000e20741e42e00c054040b10303100f86400010200310905440043c5514950820001c900c200c441884101d8503113110b01c503500e4000c4a92000006264201d0055403083c0d006509441e010350300d0004116162004440007005d1400c40c01038000075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 779411546 1250 779410296 779410327
    0x70306320307030212010605030601140306040f0c17010b040b0d05030a0c03410301060f123803030405090a1d1207061505010504060804051914160605 66
    0x10100d0150540358000c1c0c403900801c44011150582014581d106c1c003040040b424100550b500418900e071318038482c0c0502400217511401c0c094405009140046000000c3c01010030b800c20083c249200790700c030303201c084a20860183c4041c0307001510640c43d0415820040c10503001d000781e0756038824041c51404008100560f00c14039001400c0d802c01100e040c3c60360302d400ca50300d00c03001040c11482d03400d2028010301c00c16070076540300340718a00d580080600041000541180150240d248142454402e005031100b1b110018085d009441c0101050f00074603d10318070001024a201441b2012498091404502410f90341c0c8214890f032900041c0c003c00180b0303c142d2036400a0b98210004001079100d19090003818a44400455400491b100000721f05042000501c1613203134241240170094071841c82c0c0030002e8458055846000203010355880040d080007003e20214000010b81e030a680c11112007400e000102c2020b80c6c0c828000c901c141d16180f0303120300180050b00c044840c1a03031094039102c406000c40c2c99 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 779412796 1250 779411546 779411639
    0x61006140c0a020d0f0605061905040c0507230d0201050118050403030e060f011d27030d0603050309090a0510140d05010501090504110a030b040f140d08070306 70
    0x1e40c01001c01c500c00590342c15501200c82c9011740c110410210305400d11404442d00079007070511401c880e03904e620420707000c0f41d052000c13240102e50000750120f66000590b618420b0b000010310502442da011101d403815481d035401980d0880c0100c03010300154003002d9080380c070f0038083e68920340c81c103410b2070380c0240b029081160300500ca45400714690303406800041c0b60200994251000e078a02c40700500070005403e19031000f1111001d0010b44c1410000e00b007a480a02180c01e143c555500070102d062607490800807129102c003d20400c2050316030b030741080385d12500440c00d502d2056400c4408a6207104241c002e441c05400c3d04403030030032058609a141800810014507041d04842070100ca8404607a0a201c0c80d8002c0c00b90000100c0c40e0f250625203940013008140410788102c50484050021450401c21075601c0369002400203903034000c900b8800c50500b07400c107000c401889014000f0405641c4044040e02404c0c66440600c9090703100c44850006076200320311400b582000c01031010140d402c864140d030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 779414046 1250 779412796 779412817
    0x709150e1903050102120601020c061c050403051317010b060306012007150801290a0e0616080a120506030c040915060308071104051009020304030306050415050306100614 75
    0xd0606070b8030340c0c07142d003a40c0042444041d101498000c1020741d58040c001807410a000701d6aa900d010882d20b0701c50b9a002900e00c1c04d004660b95000081c08240c01002118000442c00031064642903482c41144425410441c10f00030030750074a401200d003801d103401503e00469050311404c200282c060075000005442030040784891042c4007000814010980421080707405582e228a0385606014030103210100030701d61007036032040da680082c21240b0301d1700c2070f6003003000c051034901041d0301d0103400261a4081d80b428a1017040403101c4210800252100130300c408401d03501c41c69040f83d2090000011950111990786d00b50308550800e010380d140590008454034861070019580f100c03000c01c0c0e0301c12158a500101c407c070350009210f005000030400c40c0088100121014007140c90004890007079500c1d240b2520310019000f2011800b05402600300f00c0181c41d0140c000c01880e0414900342d00026002c0c4a1b40e80240540700124140c5141551080281d440c10b48808030006540203800d4000e500041221 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 779415296 1250 779414046 779414089
    0xa030c09230d080a0f0e060f03180a1220071a0901030e07030506180c01090b0a030e0d18050a120f02030f0a08041a0a020c010e15030c030709150e 64
    0x10b00003d40e400001e040d05940036681e051041561a5000c0c2201207065039181c0701d01410700125103d18051021a84e00840058000c00c59411340f00c0364610301152440000d080300031500380c85405503030146143d6107010200d08a00c0c120303244104034030786484540c01504a4481d0700c180401280e40d0400060110600624001401903032040c2c0706421300900390800c60b0303e500f002d024080500c10b40c030390062801d105600603151000729040042c026920521840088003404034028490600a078000b0200022800c1910085216220000c1c8005115100f032000e80b82040004100d5041403096807082e1a50422152a5201d1136150307809a04c081980499040c130940c0c8490054100a1040c6001c4501c80e00070141c0795800d09101c07840160951071650480303102444901071960b800540384440d15030030f01f030841c4402000c0d0007203003185092140541245030b0010900035a2a01d0074001c41c41000c0340d03984c54503c03030340307500340c04402c003c2041c0090005081c045800c1d5052400540c0c6004d8488101c440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 779416546 1250 779415296 779415319
    0x40b0a0b0307050d0f050610020304271b0c1e0201020604080f091f0f0c0201021903020f011104140405070c0b070e0d110111070b0a230f0a030c0923 65
    0xb0341e000c3d20700c8013940003680ca480706c09005407420030300022420381c1114009141840d05004043c142d02001340000307001c50000b000c4074408401d4a40c0841000520025000861040d18030040d01403c410041140c07a10703a40e0080d2005043d401d0155500c1980c164050001a1155110700c105500421901c001802041190300701c680c0c1c44403141103000c0d000880c000b141c9010b13050050040b405503880c550034001103a261600507a0301240e507059032440d43c004d545940b042d90130224034001d40b120a0410640c41c0004581000940b4806003088480034003281071400700c5d010900c01601c00650712007010819154405000803002c020072030b40240c10746000d504403010400050340d0465000000e6488507808040c40e03505503880300300303c26600c155100420b422850416808400d2203041c4090003000b032050200e19066139500c100f0a04030400000c40e54070b881c03204092503000c0c0c2c400400710010034038141c2d510021034005c00548040724070120080100c14280d900343d560301340c003032580546e000c2028940e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 779417796 1250 779416546 779416567
    0x2b0e0a1703150637090509041203020307030603020a0f081c0504030818090403210c08150a0510030606020f0d0203040302060f13030602040810140a110706020301080318040b0a0b030705 81
    0x50030705a440300480c4813680010303901a120000e10707004140195401001c010105e400400d800440790384510300144d80795101c040031001000e076504000d5001e41c00881c0010b60008501c80c4005491440040d98060031325072191088004400c0031441c0441c4050000300301107154070300a0444002207104040d444160000003c500c0303002100c0c111f01040c0d007030000107400604889428201200a5401c201340c032104c0300041e20304840100058003102c80c01d40b4011b02501c402034900002d010151038400040881e40025002e858503006000c0107125000031155160340000d03403800c0b1881c140d009075250a00359000d0184603070201d540c1444404040241c0e0425041d01c1d100368005600440c40141c84500b881415800c0c00807003180c00100d00c2c100484080d074814007a508982284006c9030001e80045480240c0581d406422000b520407840800000f90421003c0000c202550005400849801042c0100421070718401500c94000d052810140b001c030041038000c50300b251850a209080c440f5041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 779419046 1250 779417796 779417857
    0x180e03040f05060903120a051e032e08030d0b030114130303020d020903030313060c170f0709030b0906090c09070c0b0601020c0409030c0c0f03082b0e0a17031506 71
    0xc0c80600004c00004015441618440b8550100d484d4489c5151070360928008091442602d900c54090301950160308139a02d400311241103009069000690352500692171148004140441c0d03007078084e5003800103900382c06100018042c490244480c240c0003086003510708034020f420110004070802d500b00700950680c0e500304080c61103544500300d0721303840280c5451f08900707407840b903803245040c0700c41150944803805903043c0507076004040d102c0c05041d544d9141d0048510703114a80c4060031003072080c018020941c10200319075101d229007000b200c12940883c0180714645078111403840c002010194030300c1c0000c00264800b500b1440500c1144c0210395100c0004040341d4230120200c2c00309a248180c0c2c0b041100701141e1500070540d81001040b080e01d1a219550039100c1c40304982c0d8a800030310080301003a41401529103002e0754400d004c0040d1000c81c2c01040d580c414543d81500c0c28031644012102002d00d0600700d0f8482c0c071001d60b4002e4100d0440d0207002e45c58200764546505050341d00d2035a040b1545a6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 779420296 1250 779419046 779419057
    0x1170103050a0c090e0d050c10110c06010803090d0b0a0b060307051b06060a0e0406110403060204170a02210a02041a01181401120213180e03040f0506090312 69
    0x100040c2100903410701d0003841558913644401025400c20440101c80d1201040c1c0d40741d08921410060350301c4c4104129282860006a40584c40d00e1401c0c290b058107108140c090420706000000300c031500c0c0d88500c89541e81c4d000b1900990761000b0203150860014550b4440b245d001f8005210210b20082042c0004d0000e800c02c5076032400084022403400015005020500780030060000076040c1410f0080110346145560f0240c4521416142e0100e804c01060383e00000d6980320114005440382e03103034507000c8080e520501c10f03207606c2e2024826038206a00081541118039500a0038003242c0300c034240140f0410020621002c0e0140501184200582c9940c050003041e840c03030080c50100b06c00c00034005042c02402e03886002c0f020a504000b817000c144402d0180c000c0315000d090140b20041001621b4002c3c2c810061481c0d2000d4800b03c0000e0340e02e8099003540c103508581c0c174007400f1078402c2042c419a640202e208107034041811010800c22424080002c0c800c00c4405015900410010b819208a176400f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 779421546 1250 779420296 779420303
    0x7051302091005030919050a08030403020f10090b090c0a14060409020705010b03060c030c0f03060607140106092301140d02091e0115120f15140a12020105030f0601170103 75
    0x4c100072405070240014030b6128604080c901034400241c075507940d84c600765400100450000000b240c28103000300010484681c20030102c0f40404140f003002009040d1518048030b440c07400302c1c08109682000310301075805160107071005a4043c60404032a2000152403c400e4103c0004c001c0411a60f00500052042901941c000f040d094415810306140a1009020f114450f10500501400302c0382070003240c07003140201e1506500e945503100060110303c150071005004006201c020004160b047d00490112009003c04100f0200c2d0b140c0801d03407000102e2500c008000300c0340010300402c0300c039404982d0000342c0609103000d010f00d5540400c0c600c1ca001d652203601000300401c0071402a444e92011405001645442d0f25180f000050151140070403025522440c0c1d21082a11509d10260340140c1080e2208000304d00313195940c1c1186103000300d0140d1414050100e0380004100a00403d44420035a5810307941c603803440e5143c9440c20700708100035290700d0400412407851200074035003c4545004c0c602 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 779422796 1250 779421546 779421557
    0x20c0c150d23090d0f030e2803030c0f0504030605040c0b0c0708010c02011107030c02010c1b1802040b04030b041b0e091b01140708130b0301050114030108070513020910 74
    0x402c400b0102100310003041c861076035012001c182903140d44107540e000c40c500c850a02184980000820f1418000560b02038a214010300c062208184010030b070507001207000746c45c10810300384240b2040720b442e015402800c002c181c0400007003000030040d81c04254060b001340034407400143c031010580580c1d0f1080a0702030003503204120a1140e0302c0300384280002c0406c140006c018520301d8003034200507070058a10107000d201000d0200c005690240c5030300c60080c1d5125060740e4001d185840e125503088994000c02c07681121001301e40b48018000e00c00c980a50321810035890610f031441c0c0d1a521b100b40000c008841000b821084080c0044210001d44052b044404c060000d0745080030b001454948448181c0100280050305202240d030401101018040c554100c103584080c1c41c1052900c5209506020305003000e032420001d100c805460103103058403800d1303a0f4039080504003180b860350b40c0400c0c01210381c80d0304114000c02c0145402851009100c0182c1805820807103070f040001c14079800c5088001c0405d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 779424046 1250 779422796 779422841
    0x70f0527150a23040c1704050105011d010e0c130b130501030f051003020603070e2e02120f031005090f010501030f060305071503090b07050405040c03020c0c150d 71
    0x94284245000703000700441140c8140d0694602500310f6100c2c240590040303907078a101c00c043c1031283c01c0040044412458a41039800c0501c1c1c4140204030034419034404900107022043c211a911040c181200c40d0045000c0784ea8840082c01c402d564000650340c4011050500c0000320074a401015108880081c110156194909000582034428401d802d1202a29010410100750b011400d86402c2eaa0180c561688940d1500710a43c0d1011400015a07881a42220001602d10a0718898045a03943c1c0d104c2c0700390f100160360103a03960b081415108540c2841880f8120f9441e10076030103558050b520340202040965150040b45c5004030944000b4410500000184010350b0580203001a0560829042004a2a40d00d1f460b4a03035603030380510038404900c02005101284650001a6600e4014002e0989410418800b07025581b0500c505030180d03080c502d01c075002e940039109807088441c000d00036242400005080011200f01d0521041003100c00b40002c0111201a101f000c3d03042e01c0d0283c0803209003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 779425296 1250 779424046 779424049
    0x90109051815100518010504230f01020a0b01030b07120608060a0e070f03030e0607020613080f0d1b0312061404110301050f060d0207060906090311070f052715 70
    0x840c10391040b60302412a907501d41c214a0707400400c5030044800c031840c10007811101c40c0101c0c0d40b48076550003007500082e440048101200c1c141c01030020780004842a085844440d001a44c441317285505c05884080327040c00400104401075025a0b1280702441c02205c0b10401e1601e140c00ca5085802c504143c0e07201c0801c0004100052144d20600311500004040700d40c47d2200410707003818103003c01010044001c180c18a2901c0c0d10007550b08440e40142002d0f16415a04015a0041c04a110f5401a03201e900d507502c0741c10324041501100b45900d56101400c980c0c07010008000f409134403008900300f0800740805040c010b064407600c0007a1079621900b400e1421140c0030070055440a1580174a500c00c200010055552202c40507030403c20261202a10b404246220300020300400030301804803400c141e50202000101d501c80c14400380321307448a0303011003039128940d583da5031140a2544d1800d5422010300c518a03000300d4076040b84500c40f0a00100d80800128003250000a403803541c0e9a1000100f0201603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 779426546 1250 779425296 779425321
    0x60f17220f080a0f021e1213090608160f080607030e1c1805060f030621010203150a080a150b040603020d050d2a061104121401180b0c0901090518 64
    0x8000200d161307811b03041130503030682d00d9222072881c1000213031000a07085030014500c16071100400a00f6030800c41e1551762a0b00715203441c0500c110381c240401c1d8079800303d503044982d01c5e0403042e81e003400c0007070415582d00301e000c1d001031000c10300e01041d6105a01c400f480e421403c00001c020140e960b695044001084217550461100c503400c110b201b400d00340090f0030728480c4001a0390b80498200ca405070780c0305026803030f25240780900190625550000080250520b01c01002085c1e2030070035548614882e5640c4d15043e210052841c00800c01031805004001c15403450b00b00c100d164034024000210300760780b90b00244a407a010f0b18111020340008804a07440742e0030041c0811005110102c0c0c2d1014490b8400d002501e0101e41001010503650319001101c40b9540001d0310b003d00040c013404510a01103080411404012140c00c904940c00c100c600e41c00961b0034080521400d131b02a290320f02945803d00b9000c09078200000131030400000f07030030028050b954441d6031952241400160005030900d07400a011 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 779427796 1250 779426546 779426563
    0x3030c02030a0509091f03030324080606090a0b03030d0b04050a061a0c0a080a031e02040b12041a0f090714010c060f1401060f17220f080a0f02 63
    0x540d0418480361000035000b10488440d0340c0c4c11103034101c140d07454851001c1c04650200d42c0490000c0081d401100b05074041c0d203d141c83c41c0460030b80c521900e004603407015500f0143d02440e0002c0e080721011440608100101603080001c0c550040340a00540010900d5a00200c80c174100c2c1580b1404606400d08140c4035485e0848540c070814050241030803d6203501c071b4114031461000b010000351000071504140702d4152041d82c00741130f0503520780c18104000c3c017030648aa183c90f0b0071500c40c407082c20b000500d442100c1c119008803000a0901400c080c045a40003c003c2099451484000d2043c48170005055401d214160710000d04203607003400303103500c1d2411809800c2040c410b0078030394540e075041e0382081103020b203203500400224100f140d40100c0c1001d00316408c0c9041000e240c400012075107a030400100c0c000d0114595860907211001e0b8405e44490005644007190785106000f501d203070b19504c1c40803045941c06101d000e03248141590310710f101d5034482403041700082c0d029501600040c0d0305000918 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 779429046 1250 779427796 779427821
    0x52a010906180f030c0f051e0f0604050d1d04050412080c07020315061903140f0c0a050105070f08040308030f0c070312180512070303270204090206071407030303 71
    0x112000c060752010301008201c00041d080c0101884800304010a40d040c954400c0e0b0712505448d80f82040d0001a5200902080106214014645486003805002030400d00c1395400ca80285401600510241cad0812140c1c410b00b10342c2c400000010885031603038003695000c0c0b0b201e514440c8080d410780b100140440009082c00850180030041240913070780000d00b06034440c12a407034211003925820001842c03681e004002c500c0c0b2864102d0b000040c8511021040741d6080110b054421010b80310300e00325101c0243c8940d0562084003d0402e010b603502c60400340086c90710606054203c4407154941046d180c20540c1b0489150900204200d06401881c20080e0400d101482c805d0400c800742e54086c140028403540e66000b0303544c4200894a1a425a080700c0340140c010b420b4480032141d104031140b1642c4020801d4000c00d090030b07082e22a03001c810080081c03009038030301c013009040131950801002d8001684103981c0810240442b0010644d10200c0c12070304c04a2200030910140f8516025041d5009d20a084 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 779430296 1250 779429046 779429081
    0x80d020c0a06050d021803010c021506011b0f02061b0705011b150b040f02041805060f010804030f120c0509010914060d0203060d060c0c1a07050406052a010906 70
    0x40002d82d802100751101482880c2c2c0240c2c5482c60055880440c00c2c500c040c59a05600b030614400d00c02c0d40110310b5043c07450890b0507030f1002d55111320054501081018428101144503411540030488100c0140602032004241616005444d00300036071040c43c4620200d01c54008120402c521741c1c0105d00c060041c40d13006907245d6050700c0c944800306c6020401040d00c031941d032a4010803000c0d0740c4c1d81c5c1c0b18030050410444215212611500c9640c0402c16200341a4142c03890171b8085840d501c1c02e02150083e80304140d40365405965103541c01c032182c0e540d08580c00140710000c04013014082280c014060324140980da02ca842c0e444280005044400c1750b0b10040300095000926070031034a4032011141248503240016a80c1d4854101107401621007400143c030304d0b441c041408100304d51090091011900892401000d04c0c601200340c8000402a203401c030200b10708000c1004128020000380c404500d0800c10703088510201f0007004c2152200988495580e5500c840c2442044050322801d03460b50750a001d40d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 779431546 1250 779430296 779430299
    0xa050718110307030b0310020f071103070806160216060507050d08011a160605010608040b1012061d0607030e100603050d0c0222020a0905010e3304080d020c0a 70
    0x29154034440505203c0425845040b4109075407010404a0b10240700b404046565960b014071f03640550300200411101748038006818907041ca000186031080c0d408074406818a61942ca4602d040c004480000c84258010080c040404e541d600b0b09040003001ca0b5161595204814500641003044841c0c06805204460005006810b0488623a00b03401c4242401580d8031950071042201210882c9801841316051000108aa56002d5441ca001e944111500040c0351140d00c9001c203800c1550041c00950101c1d141c5101c085642d50700501c656580403900c1420240c164000142441070032500540403a8403904070020105040103060b5400c00720302800c12800d420340e80d03050b031942c803015603180803c880110304409640c1d480254901c8440c05d1000700f00c9070003420b10082c2c040d4002e080b8010205440c0c4c54002401d5000d582078030391000000748511001c0340c5402c401c50344020440303129200d5201c107000455400550000070000f43c10114010180c11002420081c901078a1415443c000c0051040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 779432796 1250 779431546 779431571
    0xb0711090f160f02030f04081011070b060103020304060e0a03032406090504050a020c060717070e010e0d06180f060b030705100807121b092c0c07050a050718 69
    0x7000d60400d002c80c074201c0e0019041e076030200c0c698043c0741c251604020000800040000c000a00020120013400081c071009140030300785480c40c05030500c054a000c0c2000d0020302c8030b40c460b03401594803d00c11000021714607a1445864034002810b074044002c41e6494135506c0c40c154040e6000c00308030320001400f09656041c0702c1c009000b51401d2062501464890000c60801c1c20a84c058409110305d27841110740520340340300700903c600300705000e0b403c02d00010000b00b08541d03c134580c40111a401a11000d051403614000d0111402500d10142c1f2070303541c1e0700488200e040350b03602c06801c2580075a21010721801c003400c011044610104482c2d200750b100306410041500c515080c64140c41d02401d08540c80d03a14104103a0700784142c030041c81c541901d00200203010410550340780c407695040360307107001030591542203020071f4803900c507000300983c1ea91701860b010000300310340020b82c000e510408103070800c08175655880c64200d44a10807078290f0070a02052022982d07644100700c200b10009814442e191030b000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 779434046 1250 779432796 779432821
    0x2010e09010b070f06020403170301170303011a07050a02150909130203250b0304060906050708040c1e170721110f1c0506010501020c04021e130b0711090f 68
    0x400401c0c030140413a50206000455060b2001140c0190120304201c509042d60f21196000340511080c001d801c483c286000b100000a49042e0342107000050f4800301c41044000480e04103110495a91040e6410540182c032201e4010494a228140103030b2502c0d080020480c400310018800005403080c8020781c0e0140e41c2c0000c000c81d00081c03803081c8070061205c409488030700c0411908860343c030540000034001004210f40c02010114028442000306032510f45040f100c41405884c00380240107119009d000d0f1210340d0700300c0030584159182004600d03581c2d0066081307001c1d142102e1460313074201201c00c0000310001000749c04818100459042d113010140e6079109201d2408070750300c1c013070340290550300c405132503001784185030401302501124007000700e10301181e503080309010300350040c0980401a000c504050003550380002c0300740300444961031515605669a040405480b6004000600000348010414020485540a00c204c2c44024541c481444400140a08440760003802042000003405492 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 779435296 1250 779434046 779434057
    0x60f080c090c0f131203021014040b011a041701020d050c070c14041d062e140f06070614130b0a0506030c040f05010f06090806011202150309010902010e09010b 70
    0x710f4607004c82248003819040d030f0307800044005171106802e409164002400186003002c00c08148407248040c0c803913225006054a00070690101c11005020030182c0003200c6c403950000c400d04604280d07680006a04d040d903040c2c103880e5945d5000405650802c0e0341e0150503401030800c0b5035545000e0055403807944a117007501c94680b2880d051a62100c160b91550800046d102c14103020009403006402c0682d00d0740d1054070b090f000c000700e413120b18020f000401001016449501c0c00034842d2440e00c801440c86078000c00004c0c2e441b403602c40685009a0b01c50300904a020b000b200001040d0140801051180380d0141c9941d541c40e824815031000542104209940a103001c0c10200d000e86130000400d1406c07004c0c101c4540d205042c907001c0511002c042e4001812a0700d0101000d0082d47e0f03070b0700281e4000255002d071401a4001e42c0051241d80c01200e0000c10883c4050918443d02c20180587c910940081d04e90000a94644404901355a48499948489242260880019454841508050b00c40c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 779436546 1250 779435296 779435317
    0x15030605180706051c09060b04050604061d0405250303090e3d0b090301060e060616030e0901090c030c020f072102090c070317010e0403051606060f080c090c 69
    0x10300c148048140e0017010b1007081c0d0301001401900340500e00342c0007415001d10018001e920300000242c051905000c0d14007207500100d0361805070754001d003502034068801481a42c0501c1000c000071901d55200c1101ca010403d406400e411441c00d51070300400b088a140c1c0b00007070851203882801541c0906407090000c081e0b01c40d1912075101882603408400c0322100700c40340170308010503900058060b6a00014041c8a50480c0204185900c078440b5110b400f20507540d180d0801002d0105ca51600c0c0c100020269050090500314051002203001030f8045000360001024262a005040c1c1e04a0b01805141450072113070000e4000c030200740040c16500c42092089500e19819030142104200c41c030011060026000f034000303d41403030300c00d121944540c0605001c60004800d008101d811090b800e51560503038042a002c07480d2030701c0350746003242e582d04680001460180d401c5040303400180b607441072000400340b614021914600d0a00e5050400b5a600e44203409851000c04120000340d0300d4040315580e919 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 779437796 1250 779436546 779436557
    0x5040305031311031b01021218091806070e150c0d030c090515040602160b0a0302070201120203090c0108060d030e060706090203030309061f032001021015030605180706 74
    0x109400c100804000c06443e841d05400b8504c0b00b01028400b107540d203141c085003a000c036200f100312003c044e404c911592220805103a2100c08082007441c120b5038480e08400100c1400e06401d81184541c0d0604005032000b4000c681d00c600c80c0c00d010f081c0340141032080100e018010307003810030821005803208070300d0078030404150303075503400b040118040d01c25031025040182c00200350310407009112240d503100740104030152046410602008028800c0c94040d03c0030440030500346030740040d064020b504a414100c0c18041042100e040400c228400b81d44240180b02c0240444001c04001500c1c0b20b074098070130340c0225089006140802d800c80411580d8000c190f84d00c1c0d075210443d050913801001000e000951601001051200004000640340e0280c0340c090040c1424080307000e0101256045440010600c508e400c806119604013100d55200094060041d41c004903861181d200480d007885040d0401101510720901c24021907115555000060341d0700402026441c2c007405d40d4400d43c600c0380004011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 779439046 1250 779437796 779437831
    0xc090f011803060906151203030506011b0b040b0a0506060406180906080f01051302010806100c050f0d17010e280c0c02030c0a06090515040e010b13090504030503 71
    0x24400c40201c500005424440041c4544900e440400b500104a0544034141407550280408009091b02001c5407140c035410070080c4c4240d074003034020b043c00030f1685050020600300405d041c0301c14846140d03001c1c460600c4480e14074040c50001c0e090200070705802e104514000410072a40c880404403416a9034904041814005030355410040c2041c0d50007010505082c0040080c4403140001e600103210304400c000d21580d90b8000c1c807402040d40540020b80010414004170b171690500e0304c004900502c440c9403200105c03215442d2140383c21a0806082e41550041c210481e025a200c251000388081071100100c1c0f0754500184400c201c1c1000e00344000c05e0b414046d030386104204060304840d5040c43d09809100c0f6120b040000380024401b820264060b0080d2009426646002c13420107090303541540350480c01900781010300011011519032100e801000300800f041c140711201140c4e00800d44001a00d42d51000c11055040d60041d81c0c1c8129a0b4508140034000001d800c0820340703500c100c0211200c0e5044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 779440296 1250 779439046 779439049
    0x503180708010c0e1203031306020c030c010603050d140f040e1e0708010e18060a05090304051507110604030f0b041a0708061011100207031809020309070e0c090f 71
    0x403240d940101029072820381d035600c18540010504140540846000c10f100b80152501e580340d1104440c00d08040c0f119890140c0001c07255400344c815182008212801c0030440c4042c10300311005900140c5160340052410f0381f1680d4484002601124100150790604148140c0494207004602034506070101410000d40c1c0c182000c100c01540c414605030f0f6070341504080a0107003540a080c014040b080014000040010074280000150107042c02c005000b030343d42c1c4405140050402904078281c90208020001d03040c0c0d10904109001036104144507a1040b461400c440c40c541040d83c10f9018000500042000c070b08600195002250400f075410042c2c2d0b100e10309600030112254218000c1c0107004d0520a000340d0201c60217215090943d0400c034061406d4200380c9128014a00c440c1c0c003588000c0201e0400d19454000d00f81081c401c2c201148c1440126804010240e0075801144016501004000c4e81c10303001c014042c02400000c6868140f0705002c8090110381c42500500c030301030104805244000e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 779441546 1250 779440296 779440303
    0x8011b020c120c21060f070516030e04060b0d1d030301030615090f020318030c0c060d090c1509120206070b0405162312030436020d0c02010c050318 65
    0x110880209181184c19816140c403042c10070741080300f5818454003000031800d021100e8524040d0042da114142000041c040c00b9070315400042040b010004c1b001d00710740c07090715a8082d150240c02c08007030741512014200c00a004813004039540c80c9286944c01c84402c100d80740481280e054981000c000325074840345010842911034981e0103000484c0c0380c0350074019010107650246000d5071000c50200400b0700140c01c080d0387ca000c0c0d442240c682e034002c400050214980f0b8001040e9200c0380b00740115034030349182c40d044400c7d011907108800d103155800c40025016401117034140030300540569000281c1680e00032a1980c0a0400002c0c910310500d00442c0500101300b04280054101e01282d140041d26041c505110601591001c111400d100e802c1035110300d070036680442c403030f400c140055050a1030500d0f807421000310035a040b107402042001840c49503000130441400c64108400250b942c08046004104507100410050110f901d4404801d1000da80401104d422001100c600c4103070100300c00c1901d05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 779442796 1250 779441546 779441563
    0x303040c0b18031603020102060a0b09070509010e03011b0809070f060503090a061a12010e0a030503060a030f03020a0309140a06050a02010e1506030f12070f06060b120108011b020c12 80
    0x90520810b410b12040784004c2e0004010f0383d1013a426a041c3e0b0b2107200b0010141d0b50380148150b0310007000301c00280201e1290025281d00001494035000b03202840f03000c40d08540244412102840904544000245d008500c0e260030280c1c1c2002890b0b01480d245540024183c64040d4808101d0004045405000100400081e05401c080b0422610301e03030f0480300d030044400044107800740d40d04001c1c2c6421401e040c415500322008038006031107041d40a5808a400391710003081964081c010344c80100110380284d81d5400868800d4004141c524424103000e448800aa4000081b0301c0301449501c03450380302c12440404a8919082585d114100d22200364090409040b44500078440d2086803560303424003c50560103144c1c01e90989154410b442c0e602900d076180d001e61140d110b08100a0f00002030700741501c0c854458043c1d80c0000e00c0781c1c0c95440c1d0320360f030f6840805100f4509516070014030284030284a04007404c2100540114080442c100203526000240320720351082075250000c4084441c240090342 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 779444046 1250 779442796 779442799
    0xa1d04020a030c0e030c0901030605060103090812041a160f140a180504020306091302041515021513061505040903110606060423040605060f070b090303040c0b18 71
    0x40d115800418018014505802c103c80014600004a01c050074041200380c1c1040f4041d10001c000c2c0c0c01c42c0c80c0c4001510028010078105581d40c440d06012800c0390000c2d00c000c1c04040746501140c101410940d148040c00411102408412404c3c04468550750345455250086420100c50081c485c00084d100e044d55940002c00c020300c002a40520035030f0213001038403e15240100c0e02c1c061600c42c0207000403800103d801c0394000c1300c60008161640303080241e40303080610007000440e0030449d9036038960100039103a005801d600311001c034512450307406000049441c5048c001210321440d00702c01845008411480c003914099a8005548080040c54410000b422014100713104889980c58000d181511000b00b10303465008110126500c0d21300002220704685080c4003825003c13500c0588000000c10700900340da0721542d1000d00250545030300c0040c0c811155110f03540383c2c584402e07083c07110b440a401040c50906402c02c00401c00061121241d15050720b6600c2e0055840c1c0c038655a1212803083c0c010302c0703613 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 779445296 1250 779444046 779444051
    0x916210c0905090c030906130602041d06130921030603021507020a0e06130b01030209040501090e07060302120c031807030506070329010f0306090e01020a0917030a1d04 74
    0x104880c0c0e00800c0c51000ca50382500d14030200da840f92205102400150758510894101d54045000503010045201009004040042c6029600d002e4030500725035000d00425510030600c2040f02918080001c080201559081403011018a581d04500e2941200070003001d680c101c080300c5010741c0301c0e910a030702031a13001d09600784142900340785041b16042b90008900c154148640402c079500810211801628040e1001c41d89134140c10458004e001c0c24009941055400d0040384400c0d5200c0c01264002e04443c00005605107804e44c03150f081c84580e4000f40180b5004008580300760030402100c0313500200001149403641c40d00301030540042d00e0284112400e104000022050000200e44140515103548007003008442d603414050750001a451880403404001300e0146042d40244811300701040d0b6441c0000b0007c1e00c1d0030f032007421203507d0420203515079404a08000942e40042031803016250768000d05414103161030030780f95280710329a804810400300c0054159051b4640030b07825407400f0000c00130b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 779446546 1250 779445296 779445311
    0x504050a031406071d09060105070506100810060e011e03120e010216261603030e09090105010f1403030403080a18141302090a0b19020c091621 63
    0x141c0c0c80d94072031024040d1240101c01c0410820350090002e100d910985c8500500d003030028104001000700c008100300c1c1072045c02c02440c2c1c00610180002c4d88120026000120101e0070000c900d490107014100308085030b807a15806014200941840318116442e01c0030760786000400c02074641c400300095100401b070b80d0385002c40042c25500503440d000350150a90840b00080138855404000095030710461901d9020014180300018819a4600e00701c040013040310328503440680072801c0d0007500e500560014003111040301c2240742010107580c0007a0310000900070341d4144078604030201d26138403c1849100741450389400c40c6c0c8060050b6070045802407016a1500b103414800381ca40023100300c41c1d100d080c0d5043c40c0070404010a14465101d0b900107043c010888101316444402540007088695110300846000a06800040000c01103200a5000090500945003010340340004045030503200f10303024001c20000c0307001c9045002544940e403508114400d00c400030188883d43e000318103d0040d0a0150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 779447796 1250 779446546 779446553
    0x21509010f0203101809030503010302040c020a0203070f06030501080102090306011e0317031501021c110a0b01030f0b1012030c020d020d0b090f0a0503092b03120c0203090a03120504050a03 83
    0x81c1c1307204541c01640c00c009440346140f041c004440d107089008010600034001070001d810b00c0d500070b01003021940101c03502d0401680001e8a090f0865201180d0101404824810303950300d0301175140140321070002541043c69600009499100500803152181c440700056841c00e00c1002c0810011a0800107044106010007040f1001e60302c1290701032800d00c030303030400c80e4240e500c00a02190303d8448001c0c20301454a1080c0111250030341038200700030612481c058200031500280d03129000f584158100100c0346082e203014840c07035074014075030181c402c8040c1c0100541e4003400b1100a4095151401c4120600c1078400112003d48040c0e000c0c2d081030481d10003500300220740410034080c810040481e02d1040c2100611a6545c000e40c2c0e00415030340040c04041941d0400300c41c00312500540200141801204a154001e0380d6400c05055000424248a184428095201d0805100e8003407024510b001d138044045076281d09944002000c2c1c81c0c1c034024000d9141d120303070300f41d4000d480010507480c1d00c1035590a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 779449046 1250 779447796 779447821
    0x112110301030c05010c0302060714090405090a0b01061107030807060e010e0d091505040e090109050a05010504021906050315011206080a053c0a080714070b0a021509010f0203 77
    0x2c1210841c0e1111800b154039805040010506907150f402002c003591500001c403450f606820189a0400c410b200c0074980d640c5a008051040203400000c1034200101c1c103160010071170603400181404050b00207102c03180d001040b2481900d4100c14450765441075443c090780249201c01c2003003101c4d440d241c0554007050000c6009140c1d030360035a0322110003544640889074202c020740c480d400816820401004100019800103901420500000943c0c491580b82d0f14200440c0d4441280c4070b0b599a0108001c602d0840310b035000c4401c3e4400150b140501b41103003e0580d120160642e510104042d0300c080340340e032055034218007880041c94207110044d07560302056035418100c40200c0d42030240c031070462014440135004800c0a088403030800c406d50711028021202d0100407220065a00030014004080b843c100b00500103903200303042d07507180800440320007420602540c00010600c0003c0200c2c4106580c0090f0288940040a04284040c3c5441c40141d00500100c101400042c1c0044100480c6c6007049 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 779450296 1250 779449046 779449049
    0x50c04090c180f080304030f05070b0f0301030c0b07170c0f070f06022a12010f020f040503010506031c030c180303030e1e06040305071e080904180b0402010e0112110301 74
    0x401c412038265200d443ca40c1c2d0036852405015101d0344140f00c20004184d809030070102060080c81521410380c2c07180351012850344010910300401030008010020000290850b0009003002c4142e00c3c02d20341c065862400700e0741400d000c82180780d8086640c040011003800f0907800e022016044810726a5500c0c803404203030002c1e1040e2805800744082032103102000031405803d009000b0304060403050007208201c004401285c5111056581d11625900d480d00c9200901c08200713042906ca842e80e242404050a540c0c00900c064000d401520200210010030203144c610700d0400c3c14045001d0b54900004c481066402840040100c856103000051581650081b2000710ae610305990070000d00c51242c40c052042d100580c0c441e9800040042c5c0802e03c1040a001d602d0300c43c0400d0364500c2c148041890700103480640588580500140c0350005140034071541008402801c0d401c0d42c41c1e1000e85807251004d40c014806070520140403002400c03a88618174000c06610030b2041008681c2c514150300c13000790400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 779451546 1250 779450296 779450327
    0xc0a0b070e030105041101030c110712021c0b0a020c010f022703070303090e070e1806101d06030c190207151103031504060b1606200d050c04090c 64
    0x41550981c103042c011301d48204d03040351800e048204132130300441c0146a20aa050100034181c034256200b0041444404001e2107a80380700c1040f000c140c010000c118440e07112110441d40100716000002c1c00010245a00020343c040040c0c466002143c500d0141c150184118201c0348009203107110b030481c0d501d0a50701e20100108030f445001c20070301403550f1582c45000140209040504c10044000c611244603440b43c0ca500e000b486400405010401ca007034009681b8090350103100030008241011200c0111165891412a00c00058600001080d0602c0310056000744030000c005544d5003a08401c0f0303503041d00015401c0da417100940c48001e4884100340280040300b1180c01c100d4403128030035401e03030f264a0401c0010314607544542ca01d441450f1001c14030300350030640315240055401500030140c80041032103646584641c0d100e141410443c1e00300206007849540015201c0f103001d03403110584072100a4040700044903200d1403218581c034020790b481860603605000c3c8001c40968000011201c40c540c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 779452796 1250 779451546 779451557
    0x50d0b09120a1d0d082710170405190b192702030708070605040623070f0609050d030207030314091f02070b0a15060f0819020c0a0b07 59
    0x8000d614000344601c11050000540070b9111490f00506074410340309842e00200f60461000d02a556400c0c150404140d1855030490040c1140ca440708402c01c070410b8010441e44d41e40c2100711040060300c07605440000c29401c1c2d5a0758001402c0105c2044180502442c800070321000081d039140001401004a0350050310584045160304010701c24043c140d403020070400614680c4000403900c43c001c1e4000035040c1d030b02d48103402000608100601809029040342d035201c2e81d03a90300704400079140b41103000c000050126414030714111501d4040540f86215481103d05900c9066030a0a0001c1c00d004407028140e03010b42095038407000d8059000300036091194500740300208501c0c0c1041090101143c4003d0b05030402d480c032010700c0450380002210f0312205c01c401414410903454080090f602220000610b50791444480c038031444001c90f80004060924160400c9000781e01d00800c41e03d006070600207081e820504241c40e80001d0b4040e01c1584442d002100c02000300c5051000d5505c0341912402c01255 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 779454046 1250 779452796 779452813
    0x14031015030507051206010c0f080904060605030c04030602031b0409050703060b031b0903120d09030809070f0e1909031815050301030215130e07021b0f0d0804050d0b09 74
    0x140280991885031507541c50f01400c000e6000317402c95180c4001014141000344068803000021012540f8070a10342c0201c2d202902c0d4101d00c42800101c400369002441804401d00401100c00d1504084405481c0c1c82580980c480d00e40146686038005441030820360002d0120b00032840c0f082d40e0713000e070f032085031945d406201c500d658510790310440c441900c200a0400c061200903010000100042002001c054101c9400003810202c0400070b8000c1900304050a0326405008281903210052a801203281c0700503050709403518640441100c841e100701c551401c20000061808000c50441a02d094408842030101400380d00c1c000300b10014220242c0d5980112a0300030803207218003010f506c81404151515483e59080d41c00700b20107400c2102c08101d02210401450b260a50440d8909000301a12401078500e42030000000e0b060001025200100214224003006070343c0d40d030400b410750100c00740e4510040b000c26080901c50341c030032600003540241040e07c400c000c001c000c1381458030403c4000140c42c0c896 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 779455296 1250 779454046 779454089
    0xf1a090d17070f110c0d140c09070203120c0d14060406090b030a0818060a020a05101518090b100f081b090a020c060a09031106091c140310 61
    0x1030741034441c4000640c072988403082c11400b45290520342400c0d4811903c942090200040103070b8492002214403c40b0b1300e4802e07500000400440000c164115002e56032442c210400940d680549281c80c1d150410b610040f8040d400c950044420b00340c2c0b040002e01040f0a500d86010504d4010380d540d0340614500703400003a03820102d101d080140c02004000d8072080181d901d994020b50040195880c00c44560401030b0110341d10000100410325030354016207948030182c1444d60504001d6000b80c5100c40c202200300308030200d02d1003481c007aa1880360039201140e0914039218020010300d500284071504803020312400540d4070000780215000c40e16801304041e100c4002d40d80f5000c041768080b10050b1500c010789094608038542075882031400e000103045c264100e115915110041d41c0100b400d81d038450381001419403100700c100d030010051004051781e041c0380d01000c0c0d8400005441e100d00107031032a802c40c2c5840c42066140c203003880341441c150b101d040240d94100414124800c17079104104c5800e0000c3e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 779456546 1250 779455296 779455337
    0x40302041812020a082205040f0c0f050f040501111f05060f0316050f031204031a0a1e110d06030803060103152103090305101d010908070f1a090d 64
    0x280355103c0702031400c128203006046d00b82091807616008030461900041095119440785400c0501c40390303004150ba42103842d02814010001d0407800c10804200540500c000d039620444048600030710701143c0b030b05001e28103603041c00601210702900390824100c00581c0d00c4c1c21740055000356400c076000c4129007420410540c2c0c40e40744c03040e03500c01e560962004000c1c1d0f10b07140d154100c9000010f01560142c0d28520010441948030307800c02c555078030700c4c82c001141ca500300d03050560b0700036800c2104108451400058003a8180c51190541c6041d0b1520243c0034001003c000740c076004e41e0442c209100c083c0e102c0c42c000c0c0068008030786d150300003450402080d8019020b0340d0500101d540e00d400091003400c030900c0010241c40d03842802d9051228507500040060030030000c40750004402600003c6202011041211841d01c242c5115290f80c107150051010503604c9003180c642d10750012462101c4402c92608207510840b0007000c0100d0140ca03400c0150741c0d200850822204c12441c0d407404040900d20124801 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 779457796 1250 779456546 779456563
    0x31722091d0a061a180a0c03021804090c05060f04080f012a050f030106050a030b0906100507051e03071a1003060906060b0d02070b1b0f0a0504030204181202 69
    0x216808503a03070764040b078804c0d44031007000380c0000d050800003112000420204101d180e90804040520020404044000d110f103c000000929055180034805600a42950310014049105940d608403860030004c01444100c01000c1c043c10064940d070441480d00d00d5600b040c03140d0202c901540700e18150706a8188120b1400c00c4401d0304460a070200c0300303500c200c190403c40040f82884401c100d000000084407010b14002c100c1d5030764030b9680f1030b00298000d0603107424050b654002c50700c40703046c04440d035a07401d0f1030203200269281c815150322403414520300e0130401201d083d00c40c1d50340056403140d008004c0000c1c00c2080c003800400115808101d10011801c10494025030b0040403c035050001603840d41143d03c10a02928011030050b4640d00301100340c1c5c3c0800030100506070300080d15010441241030b040c2d444100540407281154181d0f07610355080c46000d40c0121801c0001600b101c02c3c600410548000d9900504104207501c8110a0144481c3d40c15800b0386501d1081300400180e544000358441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 779459046 1250 779457796 779457851
    0xc0b010f0b0f0a1101020d06080c010908030d1e061d0c0403050618210310060203030606030105120a0605070309060b100e0405090a0503030a090b061903172209 70
    0x510700b01c8266003004440e005440c00b40300300100014a0b2000074401d0002d0b10000c1c0d610400000d03410700e0214100d2500302d030102d03854140005080108245400841a80e41d403040480011404103c6201d20044d0038550624203d100303842d0a0780170480c8080c031060110081d120302c0405d4480c0e160544040f01c6030003140305c002c0c265030050300000d44003218103031003407a1700044800302c0f05e2445110350703401055000c090100ca480d920220800030f0029090303420f030004213941d00180d41fa604100c400b01308c0e207200500560b401800e0550207403014540801c049100640c01040411440c100900c00901811215405445047c07c05050040a250185c0c00000e0142e003601d507820b20705041c005020103080020301c000414040c816843c1c0120340d00344000c500c28503001a000400c003c040c5881480103c01810890241013003440141084e505c02c1c2a4100742d98202e0290001c0303a40d1400300c1c094900c00c07020b0390820140140d45c85030481d40400058420b94070b0360017040c030000e0244040098071501c02407902 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 779460296 1250 779459046 779459069
    0x2130510081c2703030c0c050d0308090c01090602060112050a120c03030f11070303110c0a05010b0a1202011b050c060711030c151c11120115020a20041b0c0b010f 71
    0x4100080c041c6203204081d5104aa10f6000d07a48c4e03c100052070000b442200b50041441d0303608000080509011106080009007490303020030f810100029130f40e420501400c90561030045d20801402010810310803100c1c0c0c03044406049400081004245e84202d0501310082810302c60701d040314030309134011001010100e6140e1401c1a5050700d084000d01161000c040384581e0800c0003000300700091002c410414029400400c21414000c28040c0e07550499110103100c010070092180180c0e444244070603003010030907000140100e50304155091540c0c800440e40e2200c400a031444c2040f07000d4200406200c0124152081c4000340c6043c080b12602c5074203900307007080e420070944074805025008808040c40c0d030a80041c507003145946480c070f5a400008030a40700c86180004200340000802640848203c80c805000c105100b60744038080c80c450041c0250103110b00402d840183c2e210307548800c010380340714100c8040112041c00060103881405c041500c12611400000c120070204000c00720844200841d40e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 779461546 1250 779460296 779460299
    0x70c1401170f07110105130b010503070f0312050910090e180304090c05040503010c17090109110906180a0e15190b010215010b04051c02130510081c27 66
    0x808407208020300f660244807440c4000341207110240f140520409a480c0401e480e04060b00300308111100c140e0205111358401d0741c003482003007802000070040325403050303622a06541e116025206401071500385600300d0780d580210582d9540c00000c02084551954502d43c0946038044003094a05118041d5181680108010070501d0841d610080c0c58070b490385030140c10b09842c1c000090960b0701c410880b10015a194017000001c4843d1131042d0b40104a06002300042d0810341c0e14019030741001d0101c0383c030034000d060010f03110342c440c215120340341240c8000c441803d140102c08d110041c0f80f01c0314052084d2007001414180c406800709514003804100c51215000000748540c8800b400030f0302c411a0450289a0300b410380c1c01507038111140600f000412082e1100e00b8041030200b07100002c2c051b0521000407502e00b00240e02c42100c03151704040326a00101380c60340e60200046510803641c1c0802c10b54840c0c0040c81d030b401080c240300c600a441c03040c0da401601d4a44020904010031001c440c90114100f90f010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 779462796 1250 779461546 779461561
    0x1b010203041212290418110f0f0409030c05010b01020f03031f0506040b1905040e060d050106080f01020d050f0403023019170c0d0b06070206070c140117 67
    0xc40e8948201d940707404501104c0f4003625002040c02034442c0004418030f080000c50380d15050003074011040100500b140840400c0c3c030f40002c000d18982680c1d00450a600e01d4603101d407200364031240c0100e0701410511101202d450700030104151803006407525460116402100e610101c0c103144121090001503041d030b290088510744104048409085001d032111000071192581805003000b009610035598403072000a0b44c613081c152444c2001c6041100401080c4407013072403540d1064120070203403451030841c88a490003d0040205421541c0188a002803284422405400400c404d1241d81300c140081c0d1100c20313508868642c1981d004001d81c21003421541e0b04402c160343e558600309a950070101041840550400a601000e01c10441e09142c0b5111882d2030381041c1d48041109800810740711600d4071480d05520b50003a19140d0329101c0d241c802d411041c4d40e9010075203018a400400b02503880000349028640000320348100ca80c6403414541420980d07004403501a0203030540a4801d510317603100e40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 779464046 1250 779462796 779462807
    0x6011805060a0305131b031a010b0a1b0606180e010605010f110c0604030804141509040f2304140604120c020d0609031d04110702010e13020a02031b0102030412 70
    0xc2254403a81c1c5c01c0a200c4006c00c142d17451031005034298140381400c0d203045040121001700d0310352900b410350803244010441c160b500021510402c20510341848800e50903403030100c001c024040c015045030305104006c41c0304007040848121400112800300200002c0c5101a42070701d0039071250030301080d000381c0c03403010a0780508025982101240c0940703142c000c0490019413a5007090304140d90740800810107014000302c610410311311440464030803c7d54003000031268518818403240c00c1c091500e445d45900c482085800011027030142828003031418481c205900c131044800c4a0a454441c00305901c05509040443c03514082ca07008440301c22124040d0f64265000640f19408a070021070004120b4003148092241c0900544260345030b001d8140000b0118003207041d1a0182e078481c1d0301d4001502102e16408c82284c030620750a00f0004a800c65035000a0284501d9044010b03115000240550b520b03507012008107030403c0c1c084031101029200c4e00c400c60803408101d6004083c9030710b003405800440d0044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 779465296 1250 779464046 779464051
    0x92102010b01172d07021b030f0a0210020f071502010605180c07140a060e01060b090303041403030c070b070201020610051c14010f05090613030f0503040201030914030306011805060a0305 82
    0x2c11584c2d0940c40d080f00e49184019007100c8580040e0000d5171030b0180801224056400c4080c120010200c0b1140824080c0e200c8405020091143d8440103002640500a11040d40740c1d07054102911040b07039458041c080c80964205101c401940b804030045894548540c0d007801c0c07048414031404c041d9803412906140340d80104019503060782440000740c04414100a00c0c0f404c81c4c4035030804140346c603402e018242500c0e19a04488200ba41c00c0c040202c0684002054404846100d20348008040410021908511561080070b03c680a140b40110300c001e4011300600e01c0900c02e07401c80d0f100d40c0e50b02d4041580c145681c0580342c0c0c08908840715103824415000d9447c003141c001c00000c3c005400c03090b41c8508503501070210010544d25003040259200003888050740c4440380c0b824408100400784c2c0c00600000d181000003043c440044080780941e4404c0d8024102da691008841c00310201815225a40303810448000b800900313a0001000c284201c0000c5030104c0300045c1c01d260502c09160030550140800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 779466546 1250 779465296 779465341
    0x130f02010c121106090d050f0d0b0306010e07020c032b030b210714030c010807050c060133140d020702040204030606051c0b040213092102010b0117 65
    0x144122035002c9040c80000303004074000c0d91181c1c407014070394081d050705050000700a003140b034100d0b45030003003255049011908010100928140c3e50803003040c2ca80c0c0102041500c0c250144980f10001c54010f5142c4070682c00344569408682d01c4d44103075020581d50b1810000100183c402c01802c1d43c01c0d84000300070701c1001d101c0c1418045006811240403030b000050400a00110030401c1541007104042841004c0141002c01340084403201440c0c007084d41da100e040140c1c1c0c100415140000ea0052060050715841c0c01c95000752039103541d6810503045200c0c0406445841e49501040040810034080a00403440b40c05440c0c40301c400c1403981c5150072076080081100d02d003a40800089006a840b4030041000c0c41c03099200041c1c52741801c007489a456040c010050302d0304400000c0101041040405a510550440b043c044d05100e002c02d26020b080540c8008002c0046e54441c248900040c0030080240790b442c2c2c0c02084490010b00c0110390a010800c1c008105910000200d44034a5240c2c400c20420b421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 779467796 1250 779466546 779466557
    0x302090705160305090103060f030b06210a050303060406060c0f1707061112100311060315060d050702060a0c09140d050703050114010f14040b0301240914130f0201 72
    0x20030800b0846200c0c960101c000540000d01d0000039a05840b80c41c1c050140d40b02d210f15003508559034040c089101a019901c0b540b881c280041d10750341c4100e400c001c088001c0b0251003110100e40780150307598105071041303842241400c1e804540248142c0c60f1047d01d94010320549140d081c1030311211b040000e4803041c0c40301881d0401c00000814168050321116004208195035110341078145408803200151140c403800030341c404100041601c242a80c0381e00030b0110742c1540e0b6900c0c0e424a91030039007102008190028030114100840328080d9020310f110702c1c01902600e1b1036680742138235101200c0300769600101140b13040038188a009810481c500d808034000d0000030390402541c8840f482c3c131040e46c0c000c90320b5a45076080d22018403070304c6240c64010481c00d02035504250400d41458201c000343c070341c03082c040d550343e82c44510256008d40219809000d8592188104411880f943d40301600ea03010340042a41000d070410100312920034a10b00c00e0242d00c015100c42403a50380d51800e03844101170182d04100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 779469046 1250 779467796 779467807
    0x160b010b03061320040b120702030a021f0b12060702070b0c03071b1e0f060203130e040f0b0106020a020906091e04080f0f0306120105010303020c0f1c0320160302090705 74
    0x303641c0040014001950300162184600010080d012000501808c04c54000707004564100703400003001070041d408070445182480e9166009802800703000c0a03070350b1081410708056501c035008100d403405011541d0035511501e40303c511240031441003803840c8499520402004010555403039000c00110b026285c1081847d41d02c0c140a015592481e048056a10700e2050400c981c07200f80b40700318000c1005002840c02e02000103070b407522061032481409003031400e44002800308a10240c01e50140ca5010003404515611814025070700c4400c2c00040340901d454501203162481c05021061042c07c0381c500321401e0000c1300d51000a881c00180080350803803000e00003c80461a00c0001c0e16042820369040e58803450f05500704004100f000c410380c881c0d6490500148046603001c83d8008600e01d0682d100d241550003100403c07282c400711000400c0030800c00003c4800c01d540462650000c1d0141c2070200141c6c402d20311045e46540d907034944184216003160301000141401c07056a54000e403181071071170404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 779470296 1250 779469046 779469101
    0x906061c0510020c03091e010203030a0507020f0d03050601090605030603060c0c16030f382d0106090506030f24220609060e04170906160b010b030613 66
    0x3a000301342e50060a03000840d0720f000e203090052a00d0007000410b1811440c416004d40040c0d16840064208081151560f0015030f44a00070000b48003010f40300c100f2208a44c00039070005009001c05d695444c0060004d1740b000412501c20380640cae00a00000780a03119035200c80c40040c0f00b07540329032198507a40c080c018a91510300c6540d0038103001503001e00b80719591030300d00e46403250040c140c14080d07c00780355085280302030069608192050102f0804101d074115100c007002107442d034640802c0004440d510300c0000301501c5a84078000d048910944030038082644440402045010032600740c01c440c45039030300140d00201600311822401d0300c40741210b100c00000402090501c80980c142c41e0200940d0750031060050458407909004210b925002c2012508260803082990b401500c0030300802c240c000d0302142070514034101c0d008a00010201070341c400d001a464114070070ba80ea4180c030400d8560700002103550b040b1080b03078807894000b062440702540034100700006054080785d00384445819400c2c103030320 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 779471546 1250 779470296 779470301
    0x417120d0203073b0102100c030f05062202070f1401020a020606010504080a0b0618012310090306021303140a020915060703111204060302120906061c0510 68
    0x1000001502503941e2030308060150210070458603580403c408070718850004d036444005104085521000c600440d0b403c000100d240040d044e10440740d56180c000550b60664040d400151084000d580900840d40c0707103810014400245641d104414140040c611035104041c0d00608000e4800c64404091a18a4803410880d00d2914407456581e0740c0003440c400d1440c3c0402107241d001409103012844c00d81048103d43c2c8401400310000d1003d10700c000803c0ca65500e1403100b041600000c4000c400079a03503100f1291049002000204090340c0c0080300c0000360420302c0444403024010789034101040d11355076800f170003036002d131750320749150500014080300040c906858003030b0700c0e540ca00061803120401c3c0100030a09201902c02d000c44074108440c1801d41d00c800e015180030f41d400d03041407160802d203001c102c0e09006a05407a0140994005004941190194081c04904590820050040e40e0b00b090322130b543caa042d180642c0c4011254492007480c543c4180800389180b06005650b010740c18007042109 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 779472796 1250 779471546 779471557
    0x140a090f181802033309060103031101021914120406020a0311030f0103030f1707090f080d090326131a190c020f1804030f030204030503041712 63
    0x40c40810081c03900d01040041c050055424410220308101c030400d6400283c2e41c2d141e095001805a10003010031892401c4009001c1200c5044044c0e2943c91800420f45a00c030b607000d00080300070450000e400d0600410502c2070740c00d007a07611081d008500407201c00c2661420021400129541020040001e48400d00030300507000300e210300340160b102e000044010b016203e07250101561090240f0070850507c0d072007491941120b800d42071081c4082100700313089030000d03061014602e486500c0c0091180c0e4951006a070b504442101e81c0f20a8490b4850f81459120340420506a00142d9103a00c2880401d1045180c1050f03110b81d0081e07070700ca8100c40c1105510070740040c1104840051444010001c41c01410502849481441030607442c0c0200d030000c10b68645400314041e41084500c41d42c40d411900c441414101e04100144101a013229542e0014000d120448003100020003600c00064a58082c3c0240c0b010303640d01c04003641c2050b0400034075118041c1945480900c030700c00c002d10442c465244000414 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 779474046 1250 779472796 779472809
    0x2060604150b0d0510141f030e03040602070302040f0603020915011107060306050a0602070f0308090d0c09020304060b040606050409090c0902030106020a050c060322051c0905030f0c01140a090f 85
    0xc1c2c41d1510048010810400380d020307000010401b0601042c41e45d031400ca4051a00240401001020b41c24004400a24100c09030140a2200040c04031b40a40c0018032807040741d200712028800312540c00145801e0702c40612000307401000700c6006c06c0310140101000b920340c041c1890240c03030744480660294a0408903a00030000301c1d90350350050295060001c0c481010301340c88c0c0020481c091a18580b05000a151f21000e44000780200704c1c0d0884d544c8001070503004640100005850076110b00b4110001e50080c2d07401c84504e803900880c00000d0030680a0001150700c035450705404c19207412000c1c0c001d0610004221751042c00200d0100b1036114a10155019040310390040003582c20138900540343c04440c150542c0b080030184108103030055822001440d8400d803440901c2054854070f0800e20740b40c41441c00c0d11520000710000c030030160303100a007901241d00c00c5013110400d900c084103130780c2c6a007840c120250018601c0070480000100c0b610060907905810701d045200c0994600c4411842251a005034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 779475296 1250 779474046 779474051
    0x503060f03070f053f0309130507180e06060918181209130c030209100e130212070309030c050703051c02030306010e151b0307030906020d02060604150b0d 68
    0xd028504050005e1032024002c0c5410944c900030150482e011084458400710158011090f036800d007440900507a00301e540041c2181ca01c41c5054141711014040484000300080d180c42c3c0400000e9442208120071254080c030014519184d16091001c291300c40c030380301c81c0c0080d4442e410b11024030507000007501c02d140e4030403819080084003040504156148801c0d6594101c02e0001c400386589160354490780300e0030540c0008544400e200150082e0003101100c40d40000c1c40c040303007451150000c01d48031220504460700000b0180c0710005604a02548092002d0b0031006c0c2c0c000b82d481c0e806940942d110758024200b80f111141c6541e525440c05440340c208565a422625242080c1a00301100c90050121360014600794a42900000d04407001d950220b0f224002031100c02050000c40c0b0119040b03c01d06c24401e50380f0060041d45a0343d01e50203810b044000a4130500d000a0240c8041810031a000da0799010300600d44075a402c0002034604140c034400c0f000e2032008002038140148000b41a0100c544401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 779476546 1250 779475296 779475299
    0x20d1e17180f1b031c0e0111010e0d0e04150311030111031e0a060311040515060a0302090307050604030b011502011b020a0209011421071707180218010503060f03070f 73
    0x881095043c0e0082d22406548008450036407450102c00324003e100b03030341c5004414006400c00490702126640c00c1541c603540303070036100010000c0124540c000780e01c140c4c6400512903115010b100440b55603004855002213901000d000080ca586111507001c02c00078000f250382d0900104600d40e0b03510586070a851103440d052800448240c50000d80c0c0d001d600c0385001c00c070991458035035040307902016010900c42c40d91100000c0c4800810400e440203034601a02464803054005c10180095000854141c4648180c1000040c1c0b4541317401181e003580d6104400b00c0441c1d03e04810b188401c46181d44000a40d5283c406141410220101204100080b0380c0208a840110300502a0104c0c040e00600c030b070f070300e0300b01d410f01c0307064855140074584030015403100176204809a24140c01c020185d004441d030012490600d6031000800610304e800e88109c1c4041c0c0c544c2c1380d5500990005c0344200900ea5421529000700f104030383d03001e103015503440400a084a00e000c1d506400107030502c501c9400044a40241440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 779477796 1250 779476546 779476573
    0xc132409150506580e0c10020a0b0c0319060302010816090e18100b10050a021504200f0f0d0309030c06020d1e17180f 52
    0x5810035007940a1004880d031801c0502003900791007511076840042c549019000c1d8500c45060314410248110307150f120f1041300e02c00f1085156803030f101420034000301041c032a400441c41441004981000715009140213800c01d4240011089803402100c1580120041500800d6115810b24807864030303014615aa840c040881007403522400c00e0105200b860100180b0060b40c110140640000c449400701b030703068400110031030703032402c00d9088641d0307003543c0d1418002d4410148590f031003900403040941d500058000c0d0008210b5022039145c40d403007403c800703126003030a00601c01019502c8461040e20400c110416860590010560b42120a440c0c84100d100340405c0309035a50301d07c504100c0381e0501030710000c80010a40300d090000d0501c2400d5100540e410140103400390401103a1050700b01e1072030303556080040e413104005200c41000c900c00d207101d002c4210b92075003000a405415100d50080c02c400e40084440940c00030300022400403001401d06d04040d00308051005071000000820100a0100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 779479046 1250 779477796 779477801
    0x30807140c01150b1207082814071b0213061e17031608090f03100f050c040303170711010905010213050a080604060c020a0b0403081e090c132409 64
    0x1344402186402404000b0f484c440b4070103c503030812841c0c94109002c0d00c44055440100ea0748038951802c405244003080346100781038210640e0604504624051036075020300907220712880225131100701c0090201840186450107482d0f02150091400103031158035101206011f4010755007541420041020810091414048506401c244035025604100c2c1d4610007030101070524800801d4240c0c04035015602d6216114003090070b40c0001d08a40c0c1d603402d03510f42c220040524105920300141002c0001d250980000200c0d0122035065807410303103245007282410340050001d4021810007811482d00210b80000340610100f4a008000060340d4541c0802e0a103032400095100078080c090341c0d00e04100201c408101c581c0c0c0181c22440104d0144601c0e10100d0030700010100c01030040001d6000c0c00141603210004501c20803072003d03802c8036180c942d194059045001c03240072205a01c40142484982020804100c041d401202c002c81c00d052800061040c41c000e55450015002514100b0880b40c503807070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 779480296 1250 779479046 779479049
    0x3150d15110a050f220e0108070603051308030a0915020406030e01090203030a11010f151d0c09010c050715030b2b02010e0d0212010b01170112030807140c0115 70
    0x20307a00c1d01d04000504040c0c42030141d9040030101c01c00118079800020380700c80800d8000b07060381180c441c116449070a6426401420302804282d44a588408131f0b13018024400d160180c1c01c8009601c515a0050307588940395400240124902a114088100007a010004c5c010320402007510268440d03040009c0102210225480c9500c2a81420000800342e00c01000721409000703a031400c82c10383c550401406000d80b000c84070605206190100c00407003130380d06205000651340307510034004040303000c641064881001590401400340c1700300000ca06540c0614010800d040c812010b403800306a4914908040c0d0140e1001c3c103020a4440114007401e2804040d00e5500e07503006d0025818442500454041301d04282a000341880041000b0410598518081101d860f90050011014002110712140030b04a1a52240d020440000104241c0d02c4041411070584140d5200c40c5000010758a080b2002c000c00f0f0a040c0c05d001c00d030310059565401e440004c2400c2641c800000c01c1741d001c410b00c1460301418a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 779481546 1250 779480296 779480321
    0x602010b01020d0c1205030408280f0e151c050c030f06190b09121f0f0b130504080903150610030207030509010c05070b040806063303150d15 62
    0x440106400900051150100f1603a9868010781f2035482c4e18005525228088075241040c0d011002001e4011030040401da8400850741c500e841c001107080280c811265017407241d40d104145800d48035011820038090900c400c9200c20409100810029042c2282d10503070301400307075400c000108458451030035041d40d0090340070b584c4d0742c602458a03003910040418600424080b902d002a8040704c80c2e8032488403414085042055440904d40645e030030754907005281030034a041d401c1c1007100192001078425034260240c05848061001ca44c518890002c0400800840c0c0e454000e0280485685003001034810268031000c00d507034241040010000170b4610060410b007098010020480040c2e4044c064410040c000c0c00c1c5a44d03265031a00e0320905040685d04070b4100c1e0080454009051200014410f004400070784010350030301e491340041011160558100501c0564007007030b800d42c2d105288000c3d50712802c0c00200007040003122000030124000c460080d0b03000030030018081d194500510071403c41508 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 779482796 1250 779481546 779481557
    0x2070f0b0403020a17120903150a09030206090102090105070b0405070b03160201180c090903020c1201020d1b020705010c110913061b091403010e0d0203071a0403020307140f070602010b01020d 84
    0x4040072141c0d40b1030546c2004210028081122811a1000c00c01c08412040049440a651509602e4800105002c441c10703401840b42c1d00100340b170002e06208440d01c600043e959149040803544601d1134014003d4400c035048e01c07400a001580324110406980103004900304c0c0c0325a02c042c014020309483d0711481031302440c0308140340c40340010070400780e4100b101c00200001c544841c840c203080e800c003182c0202254110100c58440d4804070b6040d4010020200001e00802a07894a2001c0001c0341001d100081c015a001040900866010300707240186540f00b141d41d29407208210001c28030300d500c02e03105640221088940c000c00c018503801600c101c0c0e00d2503903000c0300742c0310241c20040003410244140032040003262054401a20290415030100708070000702c0e152540b100350025a20b90280703401b80c3d04245403070a5020074908010100d4091ba402d03500650510009494480815a45205640c000e100381704440480c00010b00990380100754036000006d46203070034400a0b08012078218903000700301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 779484046 1250 779482796 779482829
    0x10c0909060b030609040204020d0c050a030c0e090106032012040c05040506090a1a060412020a170304050105130305060f10050d20010e1903030f0503151002070f0b0403020a 76
    0x12103507400e991348a0b50840d510a401d45071800410002e1003521081702c8c0301d5091070b640c03400d400d800c0b1000744003001481e903041000c251080030840d064140c82c14019802043c1c5001003107264800d0304494280031a50702c0342e039401c02ca20302211440754402d1015803034041a0808200510500b180c0120042030196410700003442c1c40f0001601d031081c01845481074623a10380341102e1240c0003c9161204c0d12000c0c00c0c0554580d211440407030050380a1808038811108450b0102e100b151403030056041c6104100203504150800c00192280e03001031500410629180c030002010580070400341d4003c20550092a0880c1014000364500400c180c2105008001d00d1300300c00c0004200006010f040c1d00c00c2c8508406003000e541c0129408c4040030107036540035411036004000e0624051105007180d1290301c80e107011310100c1a00ba6003030b000440300a411a444541d00d04102e0400c5001d45400440600c19101d0741d03915280d9142100e400341e00719031480d17a00880d081c411410651000006403e40d110380c0c41a41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 779485296 1250 779484046 779484059
    0xe0a09090c09061d0c090a03050a0b061005030721050a0b0406081b06030a02070506090304060809010627060306051005031204030203060c0d18140d080106050313170408010c090906 79
    0x21322034405100c000716110700040c100c494208191102d5200c0104400e0141d540e0303003045035503036030440030580d000b01145000c201c083c43c0462210500305615243c42e400e60b41c03050400e40c1c03456040c1103160030001100c55060000181071003420f00c10410881c001400c000c0800038441280c0898000c412598401c480c103902403004c0741c0586941080c11116140d0300d40d20b4001840c040c1c040c443c00145144030f05020701801440c04405002540c416680340f4400756200d902c02400d0f10b1844c49050155840321084503405402d0164811000b008080c020924550304c2e0f4400085a20840e840303000801311500074441440c090140c840c00505804415043c41c2c1150000394a0324409000340c034002200040040700702c9115005844404102207440701501c000d424444002c600304a14044140983c1d2400c1760081c3c014501c8a060f200c003950ba00b410742c1c1c0c42c442e255484102c0042e081d01c51075020410095001102d07401480070300700c0c40001041440c0c800c02c0240c0400c045030040810581070140a00c0603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 779486546 1250 779485296 779485319
    0x5030d0e060f06150a0903020310060608360c030d0809151e071211030a1d1f060e04080912031602060708071506181a100e0a09090c0906 60
    0x80c0c0100d1651317030050f244142c40402896000940501a00d900c4e681341c8902d640c41101140c40b252500301440c3d0f64803091108110b110424800c00f02c41200e06000549178251000c00d4034a000e008031100d80200a0000f881c0489105041000841d00020003801d284180134080c1c0410240c0c81c41031041c1000c02081e0310070b80300b001c00b0050314105013002407403184c4202880716085035882400c110001040111541d50b81c400c030f9510f40024105441a40b5100400f902c01c001d4400c81400703010450f0f4074032145400d00110188024640d5250709012035500101c0101d24001c510441910342e5600d050001e10680a4244010b0340c2c064106015030440295054417a861050f412242309660f180380d480c104045004800018040f0b440c2aa0b038910148001d50069081d501c2000c202d0002aa1583e0440309803614107103200500726040950028605040a0020142a50b8141a0b03c1c0c0560b12012440c0d40e00e95a2120784069250241c680a020900800f500a01001c1405010050800c02c01111 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 779487796 1250 779486546 779486569
    0x201020c0c100c020a030b070306060e1f180e150105070c1505040b030112030e0a05030c0f040b090c0a080609070e0d03110709061404020921070305030d0e060f06 71
    0x4400d9030009520982c842c0f00c00c0004140e00900b440162034490800001c2038034100c41c05408240340c0715002c940280600c2441c1c600783c20003400403601031080c3c1d0300302c24a801800300c071f10706001185004039020000051000060701d4540c83d0002c291034504c0c108841565402c0406050250400454020038507202c59001605c280c180f1840200c0f481102c1101c3e00c3c8110380c8844040c030000b000100c2d000600d4502c1c403c0803402542e17507111500c561000c000c1c00400b40e04c21254154800b441445040c2040110f543c00088000d0001841d00403203004a20180c00450780162a0500003889461807504180c04580004055900052510301b004010300700c400c4401d0114841d542c2042c9030002c0501c80c2c0c1c1007840308003a26042e40c485a650380915000f030501401010301080300403c035031081d0704251003514204a0007c00c00d0345009c10301d0f14030383c5000404003a08281c6000d20030010012540400042400400c1103000203201942d5460460600c03001500171010380c407040c401d005040d510401e1184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 779489046 1250 779487796 779487799
    0xe0607170c101d0f1b0411071406010302090f0601020c12010b04090b01060306061d060c030c0a08090a090c1d0a05271609060e04020412060b030d0201020c0c 69
    0x1c0c0d40e07048000c689841c01056016802040f400c02c44450192810120301420000c0004100c4241080d9210241d071105884044081107502100f0700b81d01915154100c102c91f030314141400d41c58071081e0380b20301c00c804101b50360f00c1c1c235107901401c010411801e0903441940d10254103090b00b412410407c0000b52540079610103944688215100a00200020350000d400480c00800410101c43c0518054101403000d104802c0884d241c1003001410074050002440c144401070703030103440c8a20200400c07070302c0d400c5000a160710b403000780110310100f001007011030300b42405649012346900051042162034809504070607100c40c1484001d602194000482d2018030382400100515180c541e0003051019195902c21070748001d841c3d840d002c242d4520070b0400304c0341c801e01203061171565801701c00a1001d103064080400088171120204401441600358071010a0010005031803d5a103200c03045840c1d4230750708140c4d070050b603030303e41e94a892508002601481c0c445000940c1001940b00d4090340710704510081a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 779490296 1250 779489046 779489093
    0x2030c0d210905010e0c03010b0a0b03130b090304090605040e030a030e1c1e030504022103131806050a060e0d020406081203091212010303030b030a080a050702010e0607 74
    0x45090707480385200140d0152601004000000040c18554068480012200e210f4024404940c40c181010700450b5190040a4803181113646440c2011100303500040c0003070320120890700b40300c000440c0160624010444040116103c0d41005800320841703100390300c07480c41030b4500b091480351024044251a2414010304002940041800c8080e04240b800305002e106403062202009a850300038041e101000341490504091110300541642120801c3d14080e60100350710b80921640c40c00025420303000e20904054034103151000c1d00d4900d4400305034010b42e40704e00c0059481184034005110b43d900401e003ca5061001514000c2d01526400700084283d0040c600c04e4264015501c803500200010300d0800304803440000c103101e042031150403c1d18100d185028a5100440d0741c03031440c0984100b4402200a1070711a440d50390184c00414801c242d2940500a10701c0030381c00310b130000000d41040d00c2c0c540c546a42e80c80720f610004000c1d0361081000c911920050080c1e10116400c10f00f548484201070301c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 779491546 1250 779490296 779490317
    0xe0d03090512030a090e060604050603041104110d050f0615090a0e01030c0317030403020d1d090702030c0f03041208160b011401080c07050d230d06080d02030c0d 71
    0xc40361801203400594100d01d0b50700300c41c0c00d2400000004d00511140e50380b035608854031030f0000c843c481e206992a84d80100103000c14800c6142c00700055400902c500040032031141100e011500362145020740e4002048007007410003d881d042d02800342d010010117a41401894800000307050304c00a80119600350402045c1207410f6112640454060540001030400b5581d5038072303060071002c666000481d240030004105c0d1400b03007d0303e403d41e8000ca41c9a0080c01d060002d060003152038000045816245481c10304096425480d61051240500c40942c003442c1d444151040c01e82c581124144461720039070040000b0004050781c4603004280a0744401032658803920600710701d40c804203001c0e000d010b1004072000040d0301c0e40140c02c00b10601c2000c0e210b030491507a0384018103400e4069010098516000000d0000c4542d11640c0e0039000403640039040b19280e944003103009003175040a000c0f6000c05940b0407040c0b00c40d607002c21044003000540d10003545065070b2703203c5e01901c40c09401614030078006000782 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 779492796 1250 779491546 779491553
    0x6090902013b060f0309070602070807030807031b080d05040b090f030d0207210203090f0a05010c170d140f011e0611011b0e2b030c02030c04090302071e03030e0d 71
    0x300c03490421200c4c0703500c0e100d052013010152941141c0c0304500c098030803841c0018003001c0100703a940807aa081210a400c040743d6480c00e80c2e0700304500200c410007440c4e14920f0f5000910345006000c222400b000002038900d03041c5094440318002804481c0749a12840310080d605030000200c41b01810340a4000d629200b1074580082202094100414443e00d5002e00404440d130010213402c14040440361502050010400c0c4059200b184c0a1035000500e0320b4440b00100304041d00f400c1541824188052526600b040801c0c00c913400001c410b46a020b01d5824008440602d40d41c0314050107420b003584013440788120755070f201c01c149486100240001d84801102e00d01c801e40c401c000408800e03113400211800d50700c00030700c031060800754a0b10840304140251004401300d503403403010300322060060100020740d031020368414011520490389031040080c150116111802110307410342c400e03001412038904003408202d5074250b1079080c49100140403402c102103030303003d2015510a1001d80d00080840742505 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 779494046 1250 779492796 779492809
    0xb0d06080d02100f020f030402010309020a03080a0e0a050303180d050f2e05061c0204090f240c05121f15030623100504080106090902013b 61
    0x240288154020001e40310a9150082514900e00d145520704000755406a41d83c0c5080740640b40d1a44000e0301e041c00041c0065010b40c1c051a86070740010800e040540da40c1d500d010140c0d108000c40310000300741d04544e80c0e0314200088107401401040b4091814042e0601000a40b60100114584a0000743d01c001d001d000007484045524445001034840090100da0f00780b80c024078169140c1c0e1039a95040c00c2c130081c808a0700c1001d010740001011201d0a601d10b4980030950003200b0801e03030f170103035440e6045000259000440d14955109507100d400705480400044000d0382820042d80c03025042c0b007100310009521000301d4840b941c12130101d40c401d03204c50821540860440c0c900302c00c096842500031480700500440c2c03144007441983c061004d01e072100000c10605510b61158041c00690400d8811140b80039601c0c4d00044060340780c00d90829a4514404d07081d00e601b130380030040301035855224005550703204401d50b9080d0403954610305400800b10507500005042c505512001400b1501540d0030303620325 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 779495296 1250 779494046 779494049
    0x30a06091403030f1e060d120201111b0607050a0c0b040f0206120609060105070201020a080a0513060c020f0411091005090a0303181a030a0509010f0603050115050405100b0d06 77
    0x407049a0f1a458a07402a110060003030300d101a51202d001c03980c005011054030a00d1140c0006004020344650903902c003002800d090745214190754a4170b02d500254901310010b8030145a1b03104030211400080b80e4407600740103020345050f003085420420a10000c0d040324031174103800d500003e80106942d0b1030a118908065040c0b000758800c0c800034105050510700304940f07018a1045800c2205a184d2000540f03032882040c030000c0c0585c010100303200210394100c02070001440c80d8284607180100007210640c5030340e050303009a008600f504080c9000d41c00c200b650450f000b4001d6500300320b2000d07901e42d944107501405c4811031049540c0a40312060f14403c6003691203e02c80a0003013624291a46030140c000e0401080c000c44400344010006003201629640070104000f5018085c550b448020030f40001d4080200311000715900e4030a0400401110f1180b90000c600407800010b40101c40c82c0084810b60f807a43c007240c41907042000b0300040306010b40e5554115a040207100d0354810001c0c00350405402103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 779496402 1106 779495296 779495333
    0x60a0f0510030e011503140f0a17160c0f05030f0105130212030702101215060801060c150e0616050a021f1d01020a09050a05030a0609 59
    0xf980100d48942c80c4000110301305030891a40c5488202d00c2e80215800400d0889240c4109428000d13a0050003902010b001d04400c1a19185180310413081c0c070000120000a40f00e4513040c4d100501a05507902510007078007140d80d1074a0035468011031158a01a01410903007210a0006110304d034070613828401e941181c0b8500b034007840448030304104c203035a60b1b1000704400ca0140c6e0710206080294107981c0e4614103d0803000d12560309403a40d80340d000c9400c2c040c1040500c10340d5049803229065514034a0584a403c00e5400c02000d07407480901400b050a00e05409998042030114403688514809c605007042a04074180c02c176820b2244410680050b0408054200d8802039507403072924089903140007060881001240c0c84800200201800302690b0000d0030030411a0808800c0d001002e00716406400d542c600741c046604c442242c00001c000310350382c07030b0b0201c20040b80e62039006600a4 = true := by decide +kernel

theorem cover : BRFrame.Cov 779316546 779496402 := by
  have h0 := BRFrame.cov_init 779316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 779316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 779316546 ≤ n) (h2 : n < 779496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
