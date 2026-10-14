-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0603
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:41:11.689647+00:00
-- url     : https://prove2.me/submissions/b9cbda08-bdfa-48ff-8901-7dec45b41f0d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 108273381 ≤ n < 108453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 108274631 1250 108273381 108273401
    0x90a1104060614070c18020d0b0d020f0d05010f06060f020d02030903030304021c050105180f0c090a0902010c0503030c1b011506050a050702180402040b01051c0b010c050f0c0a08071404 81
    0x11089150211b00010b11842225040358170f000056129405090007070f0840d104614817a10948110050364016240d04565104608048405404166071801d2850140c4510501c08a0b040e1400001080302600810304c0d003407103030003a130803074080c05103404050340d90b0700c110f80403541c0c96401400020018540100481e8050f04c4802885c40b08070b05603610709094400a6a840ba4482811112041d160800b0086881442d03103400086ca032001000d4049500341c1c40c081c119050a5440b071401d04156402205140c50f4264050101c07540c130701c2c141c9110f110503040f08507200200c0c410202c00d00e901a105021f030100c4040c0740040490000c3c50080290340c02e500050006041c80001d1000c503000da620a0300d18420f400d0f0b191b018500910301481000100c0d00600411418010207001002c684010100c502254800c0703544002120b143c16070040e609e82285d03010082c02e034410318002c801e50400210b1400054501038400700b000540b070740d040704d44801c0c40d401440100e8404148a50480c5415000081d040f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 108275881 1250 108274631 108274643
    0x1021902060304060f0c02011a030a02010c0206070204090209130506130201050a08041509060f05010e010605030109020913051501020d0f02031804060504021b0709110a26090a110406061407 83
    0x1844021740c0c40030340340d0a40024000d40d54901001005540d941c1003200c0303041c02240074000200190740044c0440f082d4900103800f40f2030101d004811500c86600501d01950000d200a00903c0c10780c400d000d030901d440104071014025000841d401c84c00b00ca00402140e581615624208541488100c0e03480000420a0fa54800c0c0d211818841d01020311aa03c43e1038018500410408101180503060356410b238025100c0d20010001003121343e5010041c2c1e03054519000d4003507070b258a03100000b15140d1036152402c0c0260300c0c1100340043c440b084022038514160a800743c03844154480d500f40c0391703403403007404400c0980c1080201900911651486005084c001000000c16940785e201150403604071516001c40425640002d840c440410011007000703240b10310090000100c0f49580170b0b15400380741d030103c007807029400300c005000d0701311003000034003c02c4501408554504444400d03541c0701d071000c058035001640038050740b0343c0c2064001e45050390196150920030b4100c104100310940e0080703038180e40c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 108277131 1250 108275881 108275891
    0x106030317190608100e06010b04051002030906040f090f050408160507080d03060305120f0906070201171501030605010e0a0e04030207032a0501110c2403010e07020105060102190206030406 83
    0xc4581e60f114450240030b4943c010080c030b4110103038100444014416012142d0f005100400012340c010088400381c1d40150f030b11441c0f0320280f01050b842c0d809801c12183d80300a02280110300c0c100c8050025048031a98101808101d5440da002c408a03082034401804490041004192124681504648451080d000c807884256a2480d40d4240085102d26000091b25400104144201005000c2110065980051500000c50111852841800c1c8524002c050110340e8a055a014113201c2d03901c4045403150702c1d55840c104040910103580c0310301179404240b40071000708055214102c0016a504040c061001650514030600304a02e0f0081c41181103101e0a400800040c59185071000b00d05860300400c10300c445810380308a50340c1d80035040030f41000380031800a099141e001480840740304060300e502010b02c1c0c40594909181855400ca0f42140400000004021119441d0280310340d55541c000c000e103480b400c00481c0c450211207101d1107a01c20701581c0f00058944100195006842441e00081d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 108278381 1250 108277131 108277171
    0x30f0303010905040507080d02070509040c05030d0c0b0c071e0602090d0602210c1b1c05070b0a0e100b040b09160f021212151518030106030317 63
    0x21656200760041c5524944410500081201c10030684020340001005003203410000780d40250b407403019201c0e4a100b400418007150510941c2c41d03900300a46005025078040c20036801010f02000d4100404840c003001010010b00080382440c142e41a0940c00055030980b0106800c03000f010030412601910240c4d400c00c00c9640585e191841c10b01508d1040e4409615500e101c4940802000359000d1564084919801c100c44170035a0f400f12071016028481c0c0d8840031035034a80b6607144c032281781c0c8808040410b10202c104219000f20140252900c41c0d40d6200840e5154110071741524892000b490665000515141d11a20b881d040001c1008001c1c0c000a8610040400100502c005640c80600c0043d00700036440c0d90b607440044c954503a40540002c148041207900180e1851040b074040024400c2480046001c51109607a080c8103014020207806528115010309089035020349001c0240c400c481c401408141418081c3d0812281c02d0713207032001c0703141d19248600810b44005203a07420b8961780035100e034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 108279631 1250 108278381 108278383
    0x20c040b1513090f050105060f1809010605180a030c060c05031c09030305060306060a290409020a110a030206040b13020415050f0f090711070315050a060605070b04030e030f 76
    0x122500e40d41000448410749030030f441004662a1408404c1d15900b03000040c06030380c07101e004440035100204240c981d41c440101250a07034648080d1140d034002071610002842e10f600070054904942c0c0070134210340e004007a43c01c00070002000c0c400144a01c07001501001118022003182034041d000e1401d484c030388210170341e408804020325850f42e021655501103400600d50725226a6602880681c01080341d410408005005891300b0712403815054800ca481010304107030288201c03140c00b560030403030741c8503070b03d586514010b0f40248078480c00040b0b480050414100e00000c00054864240d0040d011030f440701d8561b4818408003d00c1015100744100e14600142c444d40301d00f103602c0749584c04909185042c08200b226001c02c2ca40701d68030480c010780341d1a0743d070758881c2c00c00340d0001c249060410860605e8029141040030a41c000b401c1051800040c0d031074911075422051041c00c0a65040081075241c9805039842c0c040e600029101130030050000340028064102e2180250005080790843d6049840b45 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 108280881 1250 108279631 108279637
    0x310090504120305060d020d080901020a02040e06011a030c0a03110408100509250939090501090803090103050a020d1802130209030a060b0d230d0807020c040b15 71
    0x488840c01181c038002c680551511032203801200031074540c0810612034001503000c072682e542c09000c4000005060025038004c1280403400c0c0c0e4081c2041c0158803110041a4844100340704141d610814511085019900e28045034032901140c0001400d00d03000190880c0104811240c60103801c0c803c000210f0405002c104c0041d60030100c8a01003810b01e06280c07014140401150f0300c4100010a080c100301801801c005481501e1000c100040c07145840c03101c5950303203c46803040e1402040d5031000f02c00d2100d0a180d003001503048607184c0e0040c0c6a56000115900c160303d100b4403d00e50018800e02095620a40180760040c14200e4058103000f00c0300071400403164001c680c154420380003804ca00860409240b50001d1f0b101d2454214240b007488800b0070349914032468002c0205a0300c0c1000c101945e5500c000e2110b41d6048007000c0002d45003607807103101d404503100303080d1007a200e140020150702e4800c0c0100ca100e120250f000d041a0300c0c541050101401800400b690b01c01035103030b5078040c1d20a6040c05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 108282131 1250 108280881 108280883
    0x9080309010e07050102070810050604140c040608070e01050301033201060906050a0305030910090e0106120e06090d0e0a090203090105100603090f0807062019030b0a0b0310090504 79
    0xb00030001e00c0d041490080b05900480c19900007180800c0120008906550b118844040203d42e44d611200010b006191503d101c0b0000b95500043c4030702c1d4000000074000391103164960040c0c40c0c503011020b03129905202c801a000036400c200510008880501a04101c8002c020600340e090384d114584000c4070049040c400703169914542080311524501807030004010540b00300d20745a041d501e58980700d106424641d1302884c1d44100780340c04188a02400f00c01070250300c0c2c82085550310b94074002c0c032075003024502c0c00c44e06041c0072846118040c0070441a000354003510080414840c1395806841840e6421f0803554000d4203002d0010309003e0500081d032060118000006136840e1020a500c1d281506400142c1050329000080c00042c090840c140880764001a080c0e49415403890698082c000300200c12203011000803241390498034110140ca0030160150302400e14840241044040b00d072541c040a030300c40e01140040001c007100790015034002a0842902d40b00e2030301d03544920140c55040e10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 108283381 1250 108282131 108282133
    0x9070201050601141207030b0102030c0a060203010f0b0910031d01021201060801080a030f05070809040f200901050f0306010c0507030f0309060518010e0a1d010e1003080d0506030109080309 83
    0x42080b10340c0e108000d80042d88080e4030490a002c0100085145940300400721010703d0b9407901500e000fa80204265195101c4400803201826550316026002c1e4001303114400d840c85a8030300100e06042800181c410300741d0003802c0084140c0208a00320040c040120701e10380500130010440d01c08034003c1c0014410514040310302c1c50341d545002c2004103c144164422121342c0c003d1010720001a5114024205805051601c1d9803614600c0c00d1160b0240310300718902d54458500440700700384500a4100760a04000400c0310b45803544201c40090691044100300c1d40000c1082180c14103d1514030041c507000281850901221070342a9511031a0030900e800c00ea0b241d0841103540410543c2c091a108060302c0f0618009080100e070702200c45009075a80c151031305200e804180341ca4540c0342c041207000144401402045d100c248a0900e0000760000e020340e0360068180c0001507102140784c1c038190f0440e0f40c480c0c40e0501d44840b20b207044000f0070f030151500e90305548942c0002c2c04259241c0181d40101c0e0118 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 108284631 1250 108283381 108283391
    0x150b01140d0501150513090c0909050411010216060e01180503030705030403170909012601020a2a0308190902031002090108060406050f01050708040803030103031806050f0d1a09070201 81
    0x390b1300c554040c031240030b4101000002c2041d00d0f4201c01c0b03c800f4000301c0e0001000482c4c81681142e041c0c0304e44083d80c01800350070b032070541044140058500c60513070440082e000c0c2c9520b29443c00e201441d1556034041c070300204100050348031165104035184c3c03040c10320346002500302648440c002400c56004440c16501640081800d005104001c501e4441000824049a1030700e0110404a10851300500c108c0d0780180117a44038134100000e0720580d03902040c244c03000f199075500110011308401841000880c5080c0c030844801483c0c0304c0d051080000300e406440d180f00e95540e1040800740c22404203850f804141d1a00c0c400001600c0401072042021006100583c642010400040285400030040d922982c1803c03c02c01650711890b0580b42c0c240f82c2883c0483da40c80c4a4200101144103e50250607070788400030000050607071000c110b103c03041d402080009500c0d174450b0100c656002c0c1800c26070040340c0c1001070803c0581701d41c0c4500090000d00380440b00900b40b150000f07072980d004454140141c0d444e4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 108285881 1250 108284631 108284639
    0x60507031701050a030b04081303030914010302040f050906010507050d0203180f100809010b0a030507051908120d0908030a200406020c060c01060b0703020a05010f050103150b01140d0501 82
    0x6201291049400d40c41c00792561400707000854592440c800500081c01c800042010b00000c581152403c0040c42e400b411100c0c2c1d20715000701808030503c20244030400300c510b440141c0d8485d0081310110b132400c041c40f020050130070382001f043e48405014141800000c000709000944180014a640310b40c54000e150cc031407840c003045031240d03000074526100b1190440ca2050998030b080d10080d13942103d140004484e551120054010501e042200740c0c00000005c00108001d400901e80081c2c3e40d00340e8a0308002c600006043d40c170310249000d6031403140c2102c41c00e10707403c031480d0024008804031000e000c035000c0199111702c0c0d4ac80e0700c103880050b565a03d80c4201e52481003802d0b0511602040c0c0344146207030078901007000b500ca6000110041c441c080c0000d1000044609400400c0907280c011755060307445416150195540002d504103d0b2554200109110200c406202da03038104c0360403d03a174841400351085100002d108020a141c1400400f00380c2845120310200500802e6903103080000300c1e5410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 108287131 1250 108285881 108285887
    0xa0804050102100c0f0c06180b01080d0e030601140411120405070b090f040e03120705070b01050108040c050d0303140109091b0b07141c030f051b03240a06050703 71
    0x6031141c0a0101410100c540806545c000c14031010f00c4610320300040360741081c1c905880640000d11a00085071256200e800c24042d84500d0241201d5161b0212003181c0c09140003038030607190b40c0403090352681102c0010804007100344049040460001d000080c0100d40000640b400e411501c40b090f0b41003107800c100801c02104110b400301404108150b02e0820407244000b507500b40c0100d04803070041c0d864400b00c8030942c40400a5440b024140d9414010078588400020140c0c0c000504c280c1c0c52842c1e480c00090a540134459947c040d98201e00075096240c10401408000e40b00d40004400305550790f814031780988a205901806082c490703d010802410310f003404038558500c0c08402500601c0c2c10740800c4036000107412036014680c0884003032070850000c14a142003480380c0340d203c3c9142c08a040708005483d45a8080661500107004c1000b95072544040b620701d410a054130000050420004260401c020b0f00c14182c1207202264005442d543c988082000b88400c0d0f0300000100780041030310001c00d50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 108288381 1250 108287131 108287143
    0xc060301030609050f060f130c0914040201090b0c070501030504050f070b2208060a0b0d061e05070302070b150d0203071205071203090e1308070c050306090f0c150c0a0804050102 78
    0x2440006d110f14140342e01c0c00b055005001d80540390400962011408002d018070040000302103a11081101c000001d003071159088040307600701e000968480c0003140050030003050354802070008005104e41410580150300802000d4030a40300380c0b16010385400308481c100540c401400503e990541c0301c214a90a85c04d0340c6141e000ea19041c40500361003031080070030000d52907a00891680d00806c41c015402c000c15030003144400b000d04040e06051840c40c2c1d640351108030039140703090301c1001c1206540d2482c1c12012401021001099200c03820089208069910861441003000420355200e000c41540000e1030014580c1c4643c0d455194010040c042c80828070985001303014901c1280d561544d29600200601745900403024542040d102182c0307554071002d1200d6070356500205880d1785407440c0c10000c50b80d20141c46841c0c403070306c5403a00282075500042052541884404c0090001003580c404228000c0d140d100c01c071660031403d100f1780640041c100400d003891800f03000490f41d40c134101000241000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 108289631 1250 108288381 108288403
    0xc19060c020304120b04081209030903100606080414030d0608062712031b0c01020903100c0c080315030a0b0a05100b0703030507120c020106081506030a140c06030103060905 76
    0x34005002c100088660081075003840d5520185c110825655443c003002240558146092000d00f10000c210b2180c00000c0100b10611040301100c00000c5500c49000035910745000d80380001d540c180110380011000c40d0f400689000307980c1034909103050b5081c43c104840300ca0380100c8441d03102200380000d0301103248005d0f1101c680041c50044030007110503102e54070089015000f40800000000038040301c4110080c04004650340407550386c039500c04d06828081d420a901643c464014000d601185100c036220740e084458040d140c8180803079994885040c1504000e04204043c0201e00c016180ca640500c0100b008512400c56071400b42050902c400840f500149207201c9088054024042e034500902074030052641840c01180503600c403075040707032109904085090b000e0704148540380e41c1c80d0103401074000d0790807810490b10000c0c4011401d0202c100140c507080d030980c110490381004115056100c15001e03429004031161001c0ea000401d060758000d92068600c1c0d5900c1743e440042201c203000441c012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 108290881 1250 108289631 108289633
    0x10050405090907080601060809030405040501030c030b15030d0507020604030f030315060807080f04030c020925050327070f09020d06050d1101030c020a020406080610050307060c15020c19060c02 85
    0xc3d03040c8108903942d03640600541003404400b900250103900b04100b1140036004c06007050103503503900c3c50413668483c00d03030004481114898002580141c000400c071a1340303944c02001042ca1204400341a22140c1c4509800e9810800401000c130119070b07034000350f12800e84655030010b20515600000340a0349050341204d4204003004c1c062010855000300c0e200c3d0042800001c4c40b85507161480d0a0700d07440001d202c000d4006080c441008828150403280140c001003000c0703400902141d4a0003200ca0f80b100b161048003401e010b0a8180d02900544028540c041e0080100c035903058540c01003800781d049590014044a8000030000001c0000d802801c00800c003c0e1600089094a9030720601d8544021100300d04140e540c3c0c800810840c4200040d020030703078000c0c0080100c90344500c4881c0e00c90800b16165111890040d00010307040c240004c80070304a8945650740785054103a552203028002e0b4052003001e0482c0c09001ca03410300f14042c003100c1c0c052000c0d400d100c200c0702160300d00b034001d8031014440034044d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 108292131 1250 108290881 108290893
    0x309161205030a053402030606030705030a080d020f04030c09060906051807030f02070b160519080603160b0a080f010f060309080f12041103011e0f0902100504050909 73
    0x140000003512091038150130115203e140ca2641c90300c5c41c4403003407001c42c000c03003400040c0034a071071010b803801030310900940c00d0b01e82a42d10710081c1552075240d4818a901035001200f4a40411402c1010f050324000d699005850801800051007480c0c01a41054940103101c0c1420403201c0014131620005000040702884000d00c0c010000d8485521a40d03250074002da00c1001620300c511030b903c40c000e105803d5000715200d103800d05003410002c0c0211410746001c10410802c0601c24052801d642c40d04411a0707010300022031108cc00c680100029050302e415109161003801414401c070031580c05400f00d00e900e1a10f0704030203074009103034801c040e2102d49048007180041c480300e58541007a0301960114140401e2540f114508042c49120382d5074440703011000418041014107030150b03142d02513802107004000d240140c00425080762100e0070044450301e1800000d5021040f1500706e0360202e4406800084c82d00002c1e00403840003101c81680200007071001400b40000d1030300380092a0400031070001820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 108293381 1250 108292131 108292133
    0x2030c010f0606120c140a0908010b03010603050303180c030601060c05060a060308043b06030d020102160b07020f0609011b1701033002010902041b020a02060d0f0203091612 76
    0x84080740e4004c2800740c3c5c0d114401004800c2c0100e0000c2151840f4008580e0f4451307880380000d200b1082c1c0d0080030019403c3c14440503070b80c1360500882e000d803074100b40654a9920b90119440440288400782c8445004114026429960038018103000700902d86480211203450701e465420510010091141c03917141007030900100d0315110a035002d96107040c4140f00321120718000003910440078a02c80324018602440314018440c0c00180c01e0040700190220fa01580590700141d00340e000300306034600240032901103080412484000160000b400e0b00566070030050036907002c0e080102c1140c0140042e9141c030700d031394808003201d8400ca18601c40d51806200c548401182618102d8040c8005843d1010006211840d07002d5401c3c40404200e8658a81e4001c18121101a01a202015043e44101d10301079a8018014500d92522480e6038154090a140b22569081004980102250340902e5a030761080d0f030141d4240e480114055080c082c001c10440c906c3d1109060203c0080d001000d40c4421212040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 108294631 1250 108293381 108293387
    0x5031501050108072a050d050f030a020d0605030f07030b0114060f1b030a03090c14031908160c1a07080d020315090c031b090a0308030606130602030c010f0606 70
    0x941514001d192961941d00d5038041113990182081c0c0c036244040084400011607140420603200c22072040c400e4a003243c5201030706945070b0240c81221400c000040000079411010303603009101c41250140002956615180032130301d40303400020120b8080c2d1058900740240304008130b1407401445003482100c40012148041400c501806c8a402e04421010400e500b038019143c004521210b8110201d0b074507580c02c1c050041c090002c0300800d40f4240304040c0c1c040b8002c0d02c1c1020306c5101e180301a0007010b802c01100c02001d0103500c0b03030342c06403801102072044001d401da010400c1150f0303034050f888800403103041480101c110417217000c1c0304401603800c00441c00040d0300e000c181c58130103205000058907a80c4214400c0341c841036280351103600456500400c81c031400c207000a107008011400001000414a5644070803900c80c0c0b40c070803075100403119400c0002481031030045a1080c0007610071750409580f94030043d481d40050300f08101581010645241100c424416840d82103484001401400e217810340203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 108295881 1250 108294631 108294673
    0xf13050f130203040c05030d02030415030204140112110315010801080115031b08060406021c0e0601090c120204060503011802071e020409140303010504150e061c0b1608010503 77
    0x51089141c0103c000740900c83e10303801281c003d080140503a480b089400c0307802074995100f40a010341e1441d51500003405144603200b0341d41a03500e035201c03003207074003503110015102850000391032914261074400c1110f048808074055030240483c4440040cc803243c420001d403864030140c110f003101c2e03031405205030074074505440f1700d07800c03240c010302c02c1090480c42c14088640700405810001062040300203200400810303900070010a00d8028841c070782d84003450141000e03645030200c02e400715031011006120415070780c1e2001200d4845400c06200e404401e00b0070100341e0300554450340204401000402070b550040d0341040c88007802400451a104040d601c6000f900c0002c10070540c218a00702c511002c45d1129030080000740d4010a000e48040d20a03d0b500da620782c42409664010741c1400b40000c903400340d6419440a0b00c10303443c3c050013030341d07500d1060206171513032104008070005540044101260b0107d020300c2c090070f29410302ca1801040303a0800f401452041c0c3c080d9020b5401044014904c189450b01 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 108297131 1250 108295881 108295909
    0x90f0606030903071b0302041a10030e0c030709051509040c1202060c06180d020d0e060f190503070306050604080d030b1215041203110d0c090306020f13050f 69
    0xd54498503a0401d00d0310754041e0301d0004100702c1ca40c1c0600034000004d0410042101c1c82118140600c91703a00c00d626842140300d0840c1500318003d419413024190103034100604003c0c44000702c0d43c4d40540980080d00e031160b568070500d180b60b501e100b03000d01b000742400400d41c402c03810f840c40451810965900003d003905441040f80c00c00c128408007046507202e00841e40d484006d01e08569043c10038038004106071100905180c1c2c18841c1030144207000d800803902441c44280303502c0e400410301c0c5d00030034441c1d168881840003020316000c000c140300300001c4560350410039020341d880ea43ca902e003900018084414a03000103114a60034842003082d00300024448501c010186000b1804032404c5000c80d5810002d010107000138004c02000880102c0040b003914806c501400004607122002d0b0015412034400c4904110358042c200080300042c48241c0162041c202d00d80303003a410003542c90b2120310803a003003400c0e0200c2e0074200040108240c04030902e0b0a01914045864401d95048400010703d41808000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 108298381 1250 108297131 108297139
    0x504060516020a0b03091b0114160503220e01080c0906040903031103070f0e060405150307050f0a030c030f0e030904090f020a0b0703081302030d0309061b090f05090f06 74
    0x201140031915007029840003840c13882080707500da050482e2025140d04d0300070442c0902c440c98440090b12580318034080100c001340c0d00041032030b0010703560042b0b03a00140c40b10300341d60900c01086464030303038440800400e40c0c400307070340c6030b40b103242418040352944200040e84041c03902d500a0105402c2070f907500580c10f8000004880c000b50070061460283e015144000011a401c18040100103a00b0b400006024240b04d03256694420003095004000040c0914020a074024150b8150b00301c2d032040200041d41c10039928241603003000b040050340145640308010b124000b903129050031020a80500850070090346407017040c03040000c02090199280550f00c800c900c61500c4510010500400e0000e0b1001d0b950041c150313200b0191204c400c031074560302c10318085002440110018032004c0106032240b2800303030b00a024002e0700d501031100b04c024204049090382c11960300e82e80300f01400c0138041d007a0012285a1159120145040e10107805613680c0c0e400140201080f06c100040000e08500d080e5002c2d00c122 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 108299631 1250 108298381 108298417
    0x1e060402181f06120b010504150c0201121a1201020a02061603060b04260a03140d06050d050703030f1d0d05030f040f08101103060906010e0d200105040605 68
    0x31140c07880c0703078003500b400c91042910440101d080703648555540144800c84005000c0d20342d103600111194402c41c400c81d070a04481c070508c2c0301090300c075001c400303a1035005240800c100c0704031700c40400c1144c413100c812004034400c0e45c24a0b526824222038195958812100840c28640210310207502c43d20003d0a140d042070109241d00396042c001da000a004d0a45060190b40311a166a801c050000038000b0180303c0080d00210044030120000c4c84004890303040c2c0d25455001c500c0c407840c0803103402400c4510882c0340c6800010030381e5101c150540081500903030041001524504001e0070200f000c054450401c56141d00751080f080c10010070f810000d90640b1800042c01c40703030030124214024209001c0e030b80d100003d0002003044440b00c003901030710a6002500c3c001c0c0200450f810031900560024445641c040c000200185400c0c001154859010304269070b07400d1400c1d0008440001e0040126280785000d40070b0700c600d1129011035240582c0a08017540b8141c2400409441402400e90702c0e05285128 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 108300881 1250 108299631 108299641
    0x3091101031d03040602060f06060c0d1202091c06150f030206030402060c010606050711090f0402010804020d2301050a050103030203030f04080409150302041505010504090c0309050a051e06040218 86
    0x71521169040d003042c2501e8896484050080d240d580a95840005039000380200b0340d107151070002c90b030080715424014106002156400e40d0030f402c10742c80207506180d0912003041580c503001c4401c0710008003c00008200c3d10b080c50180101c8a480c03540280741622400107100030204070480d00240d035011241292203949520015506204940300120302e9400e1060005040390000301074204684078109605034200d01c0024001c044604035a480240b588000c0803c016500442100381c000e070020f0b100000306241a240d40781c14400306281d000314003a2066400d81000800c3c420940c212103580c13018001c552440d14000c0d40d80c000075204814250710741c00880c0801030047c003100c0082030f00c808244034104021040410f08500c51005a01407410201001d003103100c0000d4034406c0e00c0050f1241402c3c9030412400100030f1008c03000c0c900a140e99000c0a0005c540100704003e50540f0610041c10404a44c485102060603105160310455002800b4400103a841e001041070741140030703031004499511 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 108302131 1250 108300881 108300911
    0x80c0d0e03120f07081603080a05160f03090c0803040614090303040e0702030403120c0c0803031b0a2f1501060203030c091f0c03030c0f02031c060513020904050105010309110103 78
    0x9603440201090340004080142890000b13481b0320980c080e4403400c0c176641d21103070f48400740c0c0c00813a60000120130002c0b4510900b40651920b0b59124030510300084c6210030303940d524629000a80040a05a2000c00d082016035803044008110341ca50350330b0942069044400710381d40340258014a80301503903d03000616064402c100b0349001b95000701c0c03420030100c0ca0300d10190072a110bc103001c1e566002d0540c00422020b400004480c0110035864805a480a00108104030307600100841000c104036508610a00c80031580140c0c88454204da203800072611054151345803191501c5091000780c92400100215500801683d41c8050010782c05507583d85107030300181003814000190302c81d00704124020f1614951080c9490b8604c3c1c400d4508100d5986407000c1540c0b9001e86846260040c1d10401c078024501343c1c04005a00401c08400d80492141c2e01d450002d0100c2c1182d43d402001580d01155217443c41c0b40c9401400c0c01007a083c2410491031034603444040c0203081c10300645041c117849503a240c4050700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 108303381 1250 108302131 108302137
    0x9050705070c060e01180e1503070b0c0309100c0203030d0b06070b0702150108010e0a030c1e0f031206050a090b01090801050c07060605090c121f03080c0d0e03120f 72
    0x1510103010780c10991200c00103419a960710084c140059a0782d01c40f44c103c0401c0040c01d0f0103440310b036500c54a81c0d5442a01004003180c2c4014010703003501402c0400181c001010b8060903c00c0d203601c018503115140c0406000c00245421401002c0010f1000083e02584010081760314008a907a404680d1080c2140400c005200b00440200902590720030045506d60200e0740798030401100b42400ca460b6a0340500c01d090360400c0c4120003280d0407510300300303000034001d04080e803000d0310980e20f4800c0340310000c10500303144042100c00ea038403030301041c680b0082540c010401d0010100d074180400040703003840f011400d00d000340d004450f5100d6a036a040d41b4581c0c0240508802800404c000303000b51300e4101154801504075800850700030741804800b0501d40742a920243c411000294540d003444940c1d50021000b090180400c1200c0200389841d4407466000300d8a136002c5d6001d000b0141d0317694980740f421881c2c081841044410800741c044421100d41d00800c0c448410301e42ca00343c0640300c115540c58044184 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 108304631 1250 108303381 108303383
    0x60c07050607060207030305060a060e120f0f160b0406020c121005150301061208030a050403090305070308120906070905040b0307090f0c0206130c0509130f150506010c0209010905070507 82
    0x240401c0001c10803e050f0020001903210340c1d014001c0e61106024090007401e45e02800c1c000c0341400303010201e141440e00e0054844061001111841144c900c0e102d414003420620070301c281e2708102440c04d0504104a860401024044a00d900c0c2500e0444002c2d01c500b13450106a2040e041c401480ca2040d004200c554004019020100140e040c01c413900e25001c1c0500d21900d020754280a0001484820482c400480c1900490010b10b1540d07088100c40040c04001c108900340810000f000c0301081d070401509020703502c50340710b90303a071140ea10b80c2c920714103613004240d094030348e000c1400c000a0690000302d01c3e08070f80040e540401c0294040c000641080d140d9044412814640f421080604115821800700302a0a8086d43c480741ca61010b5082000c000c0c4002421402032900708203c1803c000c2c14030f6600c030b440042000b103c0300055039803c4490764168001c0d100d0840032518001a40c08a109203500020b00742492455608179030b0100c0c4400e8414404c0c04a00c42d502c0001890660140701102d10b81c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 108305881 1250 108304631 108304639
    0xc0c090a020c0114010303030b0616062403050c011701050f150f0c1b03010501030317040c030f050d0f0828150f0e0a150312030b030313080f06070509060c0705 70
    0x540c00d111104184c01c00344425000a428500404120708200c401c9801a071030203003850741e010805490b0000a05440d01c1c1076412420b40441240c01c80510300c540f6006103109130040c00b102104e100c00140a5a02c02d64009010f015500040086036104044803030031810035186601a10585468410a40100810444081c0000030380d111540385c017058019440f84031041c0c503680c041d84c0505050032141d007400b0044c0032810303c184280c01514078158665101e482203415910440d1a0b0380d60041450459004a40d0f40d88040308221041da0440c6241d981c1d601c0c285040c409501d000078842040030fa0074095641910401c0314469800c43e0950800004a2101d21918259580c0ca000305000241144106036004440c440841c1c40c4001c94003e06041081d040810700d04507095490702243c40080600b050185940e540391000f0b1034505201510284c004500c55082d1b8914045a690038118228001e80c9981c210404200680c1e03009000d8034425401039490681fa4504240a5840c02806403c02544 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 108307131 1250 108305881 108305891
    0xe011419060905010908010e03071511040303030605120c010e01050903070b12010e0a06031101030b01020a0611030613091a040f05030414010e0103090302060a110d29060c0c090a020c01 81
    0x101d0740d00319a400003201e1080e80e070392a840d03035284025822130300480400d854903001000f1540c00f062140120194003d6208000244408038650340001540680d104401181c3c5800c820000d6140c061301d00e10a0200807806004000c120500080038500322805003414090003188812450701c040113240b002d0000716003c00ea64240c0e01e0b580c0d00035090300b4490b4128010500c800584440f07003d00404040b0303603100120030404403c400041d0094829888000d0444c86400002808920340d800b41c4100d280d03544502554a081010901181c1494215031901c01130070060000001115007520340c0003003010304030b02041926a413404503041560541c014289210119001c110b4090120250110318403d0301c40301c0044403208015010f640c100350014003d40c2202c0d000a28000f440c0e0451681500302d0414545850718413103025040b100d90700c04004144601c034400031545c1c0c0c40d4888541c40890106d90349401c01000c103280d11703542c03692030f02c840d8000c1442001050b000a41a0140e0b6401e0b042d110082c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 108308381 1250 108307131 108307139
    0x2101030f140d0207090c0e091303020c010e010e0d0512030910060e04240b031002210f0103080c03090a030b0601140307020d0c0c0504090302030301060e0a0e011419 72
    0x36610101030050340c0038100e0103004010580005161828911142c02070071041307281c100381100400310b415092050107144120000c290796200300e40c5100d05520728416040340e101d410003e1500d480d031700c070090502c20b0702c8078203510f241e0f041502140017050844112903003558624050341030a02082000300b9100c03010043c0701c605503010554482d01c00c64600208602607513240805852181580c014241c698481d1600404000c0034002c41140400004080340c40b0301d001010900c0e1203250f48020203656404209907a4035542000c1d520b000400003000c2c0c036a1400d0405400651100610000301203c000290241034450140250b808802004240c1c80c0320300d035641840c403500003040b65001d0000d002d1161306403030f00300554160703401140141d00821149110640503140d40380d2010041d00d800080d888005201d40e1136000703084581e480381c0e000d15100e500d0208080c2040614000301807207024417220034440c0d070449a14542c1107a220040c0c0c44581c400180205c0c00d0340480d00188040c1804900000c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 108309631 1250 108308381 108308393
    0x4030b040b04050f070e0c030a140709090506030d0f050d1401030b0114030114061903140106080601060309200607050d02010501050f1c03050306031c120c0f1202210103 74
    0xe100c2e0340a04299103440440740005034490060307010b900724035113803c070110307050078040030140d54026150341000800d080040a10310461104031400d000141e00c64105024800c0130740111900301c00700364000c040c0030348000c07805400b0346102c1c0244020410302280a54090001350009841060900513508a55840703050001d0319120034001c083d000e10f070000320300426090500c107607111035400c070300c0d090130a41710101004209440c04070382c00ca004070407110210100341499241e0340380009510000412f68a000c04050a020b41640030f203080c0351912a10002040c0900200403e00c0c11040b10807101805030400544c0c28014490054818030502d641419801d4056000c0342c10b881d8120b40000303822a44504205003405042c26a20510300d920031a01c0001e07004401a5070028002801d8490000c500c1c4400d51040340b11001c071000186209445d1070094071148034001511760640343c48603545010318401f0340000e41c8480c128113000e03400541a40300104542c0740ea1002c40407848081c1c0156580d0401d9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 108310881 1250 108309631 108309653
    0xc120103060f050c0306090a0209030106030602030f070305010b0c0601140105160f030216140405090a050607180e090303060f1309300813050109140307030305150a0308070804030b04 80
    0xc60b03807070785840e02040c04809000e050b648502001031031180390b543c520422201035001325205641540d00c0d1140480000c80a002952245a401e2000240f901c0c1c82c031801806d507907040c0d110f4002e80c8410041c920b20ac001c00720f980d6041d15003580c4900c980c00203500c0100c529105220000c84481008040e0404010740d000080018a001341d0032182c281521310480b10039400c892142c0f000ea4101408841000d0a003600955800313008a0705680344085d4649409080101c22514040000ca55040d20f440c40642c0076101c5c030240400300e0443c0d90714a0107181c1143c0e00d200c00750080c2c1c0315540101044400e50f0300e0814044c40b14220750014004040342c2c0c0b0380b00d0501c4494100f145000704a81c2443c40d10141c0040664911044c0f59a44000d241c03a100040b590394500c128050f5041c0d501d405800c0082826007070703010300f045a2200119980d403943d0400408880c2d020300028855011505084c0705562510300900549822908003950cd1443d0710784410944110b52000713103845100c100b0002480702c08888 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 108312131 1250 108310881 108310901
    0x90315070201023103060f020f031009050901020307120b1203040618050d0302070e0406110a090302040c2d1206060819020a05070f0809040608010203100501080417030c12010306 78
    0xc10603131800ca00940100c0c00300c0d04a040303803149003800720800209050350441100300c03440d0701c80145003d4444c0401d8501d40e0044030203a503040b045030b10800c04803c49201c0c03107900c0081c4900850560a0a803401010952042c080011598a446948440740c2d913182d01c1c0301080d036440c001c0300e69840d560391025001d81c500086030308200095910002e1682031001c2d0340e0100b1a40341c1e01a105550a2904082038040042c0050360a2580e851940e403036050003000030081e0141c5030715401d50044c61481040b09988540c035402c001c112000f47c003902c01c2d00c24a1120300204c0421182000e03141c0c4032060444801c1c0b05c070161071166a041060002d221608914400d00400c1caa901020900d64a602030009038410003070001c001840410000300800e1354102461441b070320411041e8a49010100054107031a6240c214900c82d075400018414409031020702d101c0100003e0078043c1043c6400d850300300d02c0084000030b00070700d4ad07000400100703030080300001c03215104501c1c00700e060341d941c40f418400000c140f2210 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 108313381 1250 108312131 108312157
    0x190606021f021606090c0504060b21070210060e0103020909070311131d06011415030103021201060e010b0a0f08090c040b01020f1002091806060a0509031507020102 72
    0x101090192010850107a15007018200303a46240300002000000d5000c05840d0402c01044001500001e03291700501c0503e0303010300c0d0711581c0e89041808000c100d862030740c0107074a141d00822441c121106c0c88a04800c540321f0304e0a074440075980c0c8a1050b0305100c50506040389607480d01070041616100282c846040c0d070b00a454103c02ca0351090305031951141c0394000500714490861070b1501074908020004114444607a0120b000c1c200d5500340304401200104241c51030308a42c006101e20034400ba185007500204454094984000d060300c0c442074441070101030b0040c450000101150340302504400002d02410b58040015a503a9401d001d0540150102d000005ea403107802c0f855161242204074003078150b03500a480ca1094001c10040140503844003035055005500d11006421401e00440c40340b06103080d00540d54000040800c001d0f0b90070728280d405006490024018582c8841c0b0079505032680354240b0507507c80b81000003910380440348a5090001c02c8110030840103a40c10f401a2104e40d170285 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 108314631 1250 108313381 108313391
    0x6050607200103140f04020307051f080702070f060509040603023003120c0309010f02040801020424050306011b020604062106140d03030b0d0501061514040302060703020c03010519 79
    0x74011003d41e0509500d4440026801000c0744c11030a41701c5201c0d4205100808131110982c0c0c500128110321a5803244000140e0003003e04e002c1e5a07008034505900589900c00f90072610700b4030b141c1144812840c0215400c1100202e08074502d80c88551050000c0d540042c000c030002c503128075801d101d810150840c040d031000d60700300b4062034038400820740e00c121086903d46410742e50b44031a00c0c4250303000244401ca0075909d580b91075900c41000e10050010f081c4610015988506044001c694404e0358a000340d2070191954401300c11030307808010761340c0000092801b08000d007100c2c03852070050001e82c1d0001c6c1d405a400030700000d00306d4000e801341e00814002c81c03c0b00780b10529059038404503a103500c034865400d49e002608094034600032490f0f40c2400d10a007400903910b0082c42c00316100d40500582114160366805081c00707140e80d03004200a1388003451410441a02c0711149201e201d000f1440000d028142c041401d0301014000d200c0d40400d03101c081e000b0051440c8c982c80200060011110151607140780c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 108315881 1250 108314631 108314693
    0x5181b010210151a07020d080c0c0a090c09050108100b0708040815010302010306050907091a07051b19080d0c060204050d06060f05030327010c02090c040e010e1e0402010306050607 79
    0x400240e0f1241a00100701f500c10111940302d40c08240d00100a06281c1c0c002c04001c03103601d991ba00500c40c05002c2e507070b01c005241503c49138083e140e02420341085050020304820031a0b289400d540040c19100d9000309142c480702e9901e000f0071180143c1e001800356000715400c03551146c180c403180d1070480b8002d03031781800b215075a0f02c240092428240c2d03652000400c800c0040c04031980480001520a000441c814070b400b0300351301c42c6402d21225400003c1192401c03680705000740b0b440750100140100b1104c512914516002c0302c5680d40503c1a00324050250203410310051016641c10b07a00142005400c1140c02c82492504000a10240c004d02140f034840300e0010500b0b007000010f42d00305880c1001c3c003110b10881c10301d0b4050344141c024103136030422081c000032100680f9081c6846008400d84011103032600d0030056120080708050b0404010b40ca6482c0401030340342104030384401d54400c0070280c55440e480394001207001d0165600400d401800000324001044814211407080110f9100c441c0c14500c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 108317131 1250 108315881 108315929
    0x80a030b091311210703030c11030304242001091b080c01050c0c030a0803040b06010c080702120c0405010b070303060503120f0c070315020a020105181b01021015 71
    0x14000010700040d1403521085014200b580d1a072a0582510b2040745094801c070313640926001281e0422400112031089000400c040405c0e41c41202d1030442c007450500c0d0070800490b0034400b000003101c0740d0003021321083c41c029002d2f0329800c027130000307250038a00c00780080d6441030301a260b0000e088403410079403102840250390600907a0140da0310390f0040c0100d1100c0800454940d00042a214984d0040e020060300a82c1c0c200054040b4610132200542c481c43c15045c00d03024020000e10b06410b003c442e10032240015100c4040702d1031f91780c1c1100c0c6103600f40310400909203060014051140c10034980800440c521001c1d501500e0000c1c400d80d4180b000c19152803d00d607d4146901d0000041c040501005814001c1100500b051265443c125024150742c0e0b1141303581209140358110300c20741d0004a0a55455083c00341e10351105084a90914000c2c4015a01d07a948212910954031500c1d0070104801c580e100f4444000f4602c0c041e4024000300c5003840704451140c3d000d1040407403001c003030148000300601d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 108318381 1250 108317131 108317161
    0x3030902011b0305030c070203010209040903020a0b0108070e010302091f2603090607060b0d080a0e120309010c06051b0304080c071a040501030209061b0f062202100c080a030b09 78
    0x2905550300c1703040d92104840030200380c2209508980c15502400260501d4842d8401ca601840c02035005080700641ba007070500700d010060b0480c4d80e154000e2942031059490a48810b811079905803629240740d0b581703190104c10a0008000e80500351000f083c00640f051210206c100c4081c2ea0134450b070000050301c1011513981c8141d0408135000f450900100300070a80542c0900503081e800f400c1c2e108079102a95840c46603901003041c89001c50042040e02d03055041500c1911719071b682c500700651401c020036001074225400b0000051016484900148061542142000c80c2d49401030101d91241000e1400012a410140e01e110304ca1082c54000075078009800c03601d028880f04182c08905c1e040c20100110069800040304542101c010800c1c203030000000b0070003100503035100c4080c05400d051301c50010b040101c007800c42d00303400700c208035034412a82a120b81104600e0781200c0702620071003000b0b000d81322404080340107001d140000c0703050070201c0d8154020140441c0106c840390660354924004d104034503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 108319631 1250 108318381 108318383
    0x618210203100f050a090b1b210405120304050a24020c03070b09161203020c10020c030601230d060912080a060f0609060e030c030708030405190302090c0307051603030902011b 77
    0x21031f15001090329000c4401401c081c0840302c003645454140181c61124010078444001a140c10350601000300b4031100340821105505085111b51460038580c58160b03444040d064081c2013261071a084100000900c0d54080c641202000c095440b024100490b50b242d4108050035100741a000001a00352a000b1030700800c100b0303d0824480000d800c248600680d020186003c5042d845150030400842d034416043ea0f03840503141d4020294144004149400c040e410307442081d2480b16044050a007001402000050b100c041e02c1122060b500c40c10f096014001c1210094500c0e04207445501a890303020030b141344201c01011060024940d0398600b894800110b101d4980002d04840080c81510300c1680c04440c0c00344010f0444804049040000c0d050015951140b1516400018100110306110003910f20745d54901124803100d902d5500494a401d0340249002d18031100000080c804074002c80c1928101c403541c90625600740340600d03014000784541c000580c040360703224a030661140386c40f00104a0003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 108320881 1250 108319631 108319643
    0x210f060e07141602031506011806020c10030f021b0d020f0a020f0f100305010609090501080319020709090b0402011403072307050f03040608010618210203100f050a09 73
    0xd00000c4001c0581c0d0083c2c8a40307400358080c03a81c3d000150b5400c00c12040d03041240e04400ca09400e000c4005841e803490300a622080d02c4803010100001034012985030400c07030094440c4d050700c0544200c1280100650710600700810320110f9000401d40880000010010078001164512000744009a0b6540c10711444032541350301c00d90440d801410803440006c008800076104805415403080041e12034600b4000100010751b80f8001004103940c0040c00704028468034a040080707505280c002d80e203904c1400c1c4514004184010a2459103100f045620b004141034001004044658a014500000e0545040c1d000446604030300c11642407030b404680c0900700541790300c1c1240b040e100000d9000d030b041c1d103844881c590052140b50085034080c00150030488444020b56943c608002c4090300040061b04824100541006500c003030455468410041d1114941309622480c1180700c503032010ac10225000b0740501401045c01480d1110346c10078151003880b0007051000d65030b40c00c3c0180445003080005003903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 108322131 1250 108320881 108320897
    0x2a03030b060903010207050a050105160c0b091c12060f0e0f070509030f0c090f09030409050c090402040605070606090b061206040207080703020601030311060403050a0e01210f060e07 80
    0x68000c0e44052100400034060380d04200180001a0880c2c20804046d0380a400c400000f000704039080c811a50b200700315041044024281403070090107010400f0f4028054241240811000b4101300042070260760043d40170924907855030002488030a806401a140505002d0089a0b400b400300e004001d44804044001c001e5440d070285911882024290a0a0100c00c21040c001601c040c014100d59103040801024200c100b9010300200040084c142840c0410003410b00c644c0c0800403081303404481070f151010515448111061050f40306004001da8800e1001500180c40c580020203050400d00950042000ca0355541c9000b0507104140c0f1400e40c060307000c101c00302c500d03000d1950150300040090b0006052440e42d07a00e010f81c0780d1080b8003c3d000b590064004008240d40700540034400b02e914005401e036820250380151842c0aa92260b405100d0035042001d03440c0d03c2100c000c506031084401d1001c4c0d0210389542c00e8000d000c0140c80c03806150030548086100140c44112900680b815554085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 108323381 1250 108322131 108322133
    0x702090127060e13030905090a230f060d24060e070c24020d090501020924030a1805070e07030b12030904020a0507050706080601080f070903080903031201080606012a 73
    0x30001e0b0081d1308905100d40d0010110386500e4100c020383c810036a404000418900c1814115800e509001d044d50f16910040c00300001e04404560403504038105030b486041d00085803038801070032001c07100f28110002c0c81c884a0340185440350001000c54115800810440d100c4250484000444410140c40a00701008c09603140c00c0c2d00303541d003116443d0000c00500300441003030404140e4040030f03800d590503034004c5408242c03803030003600003400702c5800c4000440c0031984000c0b002c41c0c0d020040c1082101583e454600d08000d07070700d4240054140c2c5c4142a2407400d41c44880d18644007600390789190001e8600141d42d8001c2c14a040c442c2c4541440100950030030b00e4900810000c0d43c4404100c0c1e04104081c8015400550104014000380081d40c44071041d5140c03040004080306001001c242401a0ad070060080381c540065280c401c3e030740c0007908203a8131400342c0d020918610804555040c20030806000286c800d03008102e06004a9007665042400249041030ba19004988030f08040210b0728000014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 108324631 1250 108323381 108323401
    0x906010807050a0e040f02070b060a0609090c0908010c0210271b0b0d020702150f07060902040213030c05030c0603091009060f020703050a0905031c0806060702090127060e 75
    0x44005030b01c6240c1252000c2801e00885c064401503844d20004036008900758003081b40e20b0810070b51040c0191811800070345401c6000780250721910509010907915000986240c3c4603400d1680508060700081c80701008011000307560318805800c695a19141015020112801c2045a40c1131000c102c0750a8540a072900c8035010008000103070180b12903c40c100152a09204020700a001105840141c480c841401441303e00006a0703248400c02c0400c001080c0c15003680021b8171401a000b42c40041c4045440c800b25000b8410381c402080d9442003400f00004024000c81c2d01800c2c0c071819000c1e10f03425a602c0003071050031700003034446421344d4010001207540303042c69a00551025000e048045a02000c100701c07502261700c128001e4001500c0007a540c01d905802c10510340040c44168020300b41030b6008011000c04000541d0a582003183c044081101640c807441910310054001b0501a82035035969240f0300305104003440c0540300c0403d030b030305081120124403078007048558511200c015940c03504022 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 108325881 1250 108324631 108324637
    0xa090501061d120a1a090a0c0e041106030a0207061103040c060f020a120302040501030509120a050a0c0c0f0815010323031e0310230118080f010911090601080705 71
    0x42c0d4020032401e400c4141c00c00c04000300d21a02d801429440469500c03e0502411190010103412030340d440100769400140c4031010b00c100300c2d1740e0f070100400e9a45840c54850142d0250b9480190300c44000300510035500c540740d00412109218070810001e11503200300d060b10602040360060400300c42c80e50700b0055140103107a14100c8011501c141c0d000401c00d0f644078000d0465070340c0c0480011340d011900b806196090700c107190f080550b04e0020070b4081c0100c400c01040b480b405560104000f004620b0780182d500a00b10100c0151307010610000309504d8034144084241c2610610300148100325210760003079024180315040e20780000c03c42d140c1d100da800144400105186051419210401042d5040c5640c10768800b4410048000340e5941c3c00c091520ac0c0700b68a01f40c00c00c1d241040d11964500a80240c9080445066801c3c05c0030402c04408402a5a800406501044540c0107900701da10049006501082000344034072140c0b0400380c0360000380305000f001102d10502080d84400440c40c403a0150010f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 108327131 1250 108325881 108325937
    0x30606060d0b120f030702120604050706120605031c080f04110f01140c0d02070504060f0504050a021e0d0f0b01080a09020a1d010510020102030609150607200a09050106 74
    0x7000d5074105440311280384c04008620528150800320f01d5901310311b01307840c4480090304610000e000d40c0c20982c46240c1c4600c940d2050314103015582e240d000c6a00c456402c80c1004020003801d031046000140325180d0200c24001c1c20700c000989040015072254014194103000d01c2d0016100c0181d8220b00091002040e01e4100090602201d103404845021034070340107000c184011405000100101d100107450803041c0c0d08407511890801c5401c2c49803a400045440c00c4030400c441c045101e80340c81c184000240300d00e407107002d601054802ca40814061040c018840b803441b0030010000c0110304070307003402160440f80c071550004080340701103845042c06405c580117884c0000c1003103030b00d03ea640702001805801e8251140f003c0c1d21303038001002240307002444d00c0d0600045000940c55403a00c0070000b050300d9002442102e078007011090180440e25010141e40889502801c00c2c604907041d91a1105040c50180c0aa841119003880c08242100c050285504845198440b940040c6120010912001711400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 108328381 1250 108327131 108327139
    0x1518050903040e181c121a1008150103060f0306091401020c07051c020d020607030c0804090515040603051b15040303031e06030803160e0301090c05040605030606060d0b 74
    0x88007054216201e5001030040741d01c0c001c084100d01d044203200d81840000c000c0200400d00d00b5560041840d0031201c00c0d0303090810b50b0350001c1c0c01ea8544071106031444022480c2c82d00621030180741d42300c0940224a2901650b03201240700144d5802030300445c00d840311409050942c0c2c425134001c100103169a08800f150903c50403008800c45241c0f0003150880e000303080b0012281c0e1040004102505145d61301380440900c45541c03003558419500071070705001e10b00300000d000d03d60005990052512402c2c0300d0b0346895001f030a1a990b10742e83c04e00300000c0c0100380d4002c6080800054902107070b00c6c052207020101c0768050064031800d032842e07404038206644131311260b070483c84845042d010301504000901c042d501c40e8400044034002d0503000160001c900501c1081ca034038005007400866801e40540b5031028861513070307203801018000d0859030144150f054030f40540c00d111681c000c01215642010980300142c60400105aa480406598882c291241e6800c000204038016a90ae1a90482240c01070094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 108329631 1250 108328381 108328387
    0x60c0203071b0501030b0613050d05100c020d2006160c02040219030b030706050301030b130614182d030405100309050c010c150905160b0304061518050903 68
    0x3480b280c402c02c000c0003802c040ca00c494407050241c2e40e014801e404039403a080d1000d40c10714a02c40f403692940c014a0041510030742038070b081c8604200c001c000d8001c501414480c1440300a104402c0650b0780ea0301c80200b480440c412001b80c10b1618050300b00741d2503900c1001d000788641d4a460303c070314140300c0740880e0800070071130030034000405a11540010005141d00501d0400101e4048a0060448080c03101c52446038000c114200081d40d80034007a64152a0450800d030890b480e15405030f000511841c50050600d0304048000c0e0340c178002200340e544600f00c05042c12503c603d007440c01039160880b480900002e030544182c0100c03142150700317004a032040403004492506444500040881941210000000780c40c1c50311c04c0c2c00c2002c10b21008042e03000030f08013098141619540d1400b040c818401110406035145c0040003031203410401e00000da844400c00204150710307203413000b0030355104940070344410f42441e50004400380d4232218503046945031020040c06a5404600001810001d030500c0c00e40e200c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 108330881 1250 108329631 108329633
    0x10030507081605040f170105010f030201050d051e09031206030f0d050723030a090501030b0a060309060b060d0212090705030303010303050309010609020f0903010c020d05031602011b0206240607060c020307 90
    0x100c1817102c040d181404007403200b0414949028295034050704a03920000006e8002c00c0142d0b0003d0544802c071480d030304045401d58403083c00c981201c0c03030412110140700300c03013050060301c050220043c1580c54007600313849026503904090641d141c1c10f4000d0742c005c650055240180851041d00501a06403203007108400d990b00c100c2c8106c2004528080c41540d07034100140040c662500101404000c00c000c0c2800d102000e0706000080c0b10616034480c5005040c1c503034007018100100c03030340300d000c451100410702511940388002510080d04440c90044070120002c003c101c0300800041e1080c100e6400400861a5a01b1a034040300c0f16003000d050720740345648031400400c1c82616400900300030866920115240c070160303000c00d82500e055419403800c2d504811032807640182d01c141261ba022031030303409407952010000000c0303005000d800759408603010700c64229410700e5400304501e8090444080c0b40c2c2000c0b020b41c4541c3d900581031000311684600c0c200206070008607d40c00c1440c1c00e00c00d500503281440340b9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 108332131 1250 108330881 108330899
    0x10b09040605070801060f050d020313061b110a0f02060903030c0a0b0a05010b0307020a020f03070f0f0e011a07110f12060a0e03130504090204021e04051003050708160504 75
    0x1a00e048a80540780c0040007143c641c01071603507005215030301d404018169084c40c0506540300c0c2c2c848226115400100040180354101c41c0c00081c2940000e042000420140d010710103110314801c0300f40018a5030388040760380324001a01c01d2001e43c103d0414000c03c0b480b64200716142c0c1c403020b107861701070100f800788261000080c045c41c0e02045c001c44c0326865610300012080c0c01c98505802941762aa000d000b40f04405078000307205002c00d42e041c6c0d040007080100b44e00003403400001c1c1d480500c04000f1800301050310000c5da00c05904443ca540030382e142c141d807213202c10110310102ea2030301c8400301024080c0c880401e865440c032a485141c0a45840498070901001c0703580c1c501c2403000b0301c91a61129042c07003500303000c81c0704548404409401544c189103000c4082e136948079480c400c09100b503445800c0c0c81c0c155640c43d41185c41503001d00010700b403c241c040c40c1c10b2182d0b8100740705013442844c01e4001411a1030083c0103041c85080a5a2050065038404840701590850440d001040180900011805800d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 108333381 1250 108332131 108332149
    0xb130f0f0905060409030f0c170f090f01020109201503130525030201080c130f08010f11030c0a1101020c030c07080a050604080f071703090d2a05010b 66
    0x35282000c08110308101d000000d403100a01801d00980c9441ca1400200303602034400c2c5203102081c603102d51010340c07a00b08160528026014031001c13a40c0000d06403607649450703000301245002540c0e00450b0090b150016401c07039030b85480240c01d07031041c0604060790400382c126200d03004c1002490f41c040d40001c0f90700c10040350403c86445900c000000c6a001c2800420007840c0003100300700750100000318081400e482008110712009052045040100d0f540641c400b0589525055156624031959522003440007843c1240c45000c0e0f082d4030740b01c0280042c18440c0a801d40d00300c848010603285442e050360310020b6901242505c0200580304419a61a800c00e00040844841c0907000710b03194500030300403d003403520b00e6122524030f500040501000030390100700c05602c40c3d00540c5150312503808680180c03052280c0350000b4545103200c43d190075107516010185008060046c00c035541030030703079800036141c501c2080416024180304080302100c43e0b52000d8480d003060721940010505e030030f20314003042040f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 108334631 1250 108333381 108333389
    0x1022a061b06010f05010e03010e030415030e0111030615030112020105070510090c0512060103050a020103020705120f041401020d120c030207021305010905090a0b0a05041106030403030c020f160b130f 88
    0x104c5008010300d6a110521000740c0404074000c1003407009003d012643ca01c2035200d155001c5000040d40340249001e5800441002041c400903c9415003c0e03800303170034551045604610410030718405072501101c00302564140c511080304801c0e040c0507500103540740c0d041414200c840c0e224007410743d1904049406502141c074407900020071501c2c101070810284542000c0c9030b807400c0d849034004002280001840e11100740c0c080c00c00680c1c1c0c0d140c9040440c1085030740f41b00e80c280d0355070024041180c0740010b0001e004440c80a9403442c280d00181004a854403e1007075500c0c0001c0191202c042c80101680c0100146034507810b006103052030075400300303052003031500703c02e03a02640d0b0b540104443c01c0107000b41c560068991014100c80625075541084070300c805480003002c3ca0342c1da0001401c2080c000500d450960008290580324a8a450b00801510741d4010703071030050148074400d15a01c1000103d03003214071190120a200c0508051003035840f0380084c0404447c6030a400c0c0c001401c4411112204060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 108335881 1250 108334631 108334649
    0x160c030815063601050a0509060304080906070510061202010806101e03060f0501090506041e05040203040501022d041a0918220206040302090a0e0105090a0201022a061b0601 76
    0xe50701003c145100300a00a5074941400800c000c00e148071948501214140d840848622b0344948450810300b550b4010300442ca83c1004001442d00c0500c2800110300300740228094081c0840c586840c850f441e40042000c00901150040703021030503c0c64201043c0440311624039242442038099a4803c410711518503441012a50341d400501c50801a0040c900c05464282400480a45001c0210351540308074415401074809000c560300c807030040c03412800004c0100500079502d9060170b0515134000d6001d200070303c8641d00d244076800031309080b402030480000212070706a07051a2904c15208100d01204440c0807448104100ea40c00700d07920042010500c40604c60036a81c645811160303041e10b160200c04010b840034085100b500141d035035204031019641e05448114058076581c4c40c0307601502c102520f401d1a0f50a110402001700300c001616003007a4000da08a400780740841c1118a0106010024803e05032580040060076081400c010210a83d003441e1501042c405002aa41003030300a070080180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 108337131 1250 108335881 108335947
    0x910060f080708010e19050f07061205180d030209010c0804031a070903020f0d020105210a18020306011a07060e0607030f140109150308070605160c03081506 69
    0x10380740003003240750050514507000b04141390381c982440ea655000c40e045079a0303800d81316002070100141032204001c10180030302100d088030384a8030003404043d80740d420802c0382032070040010b0075130b01469400111802d10002400249445078001c6001e90f029081240c140300281e101c4000040010000303200850040c0c0601181040c1c9200c40081c03280041d090b5010088202d900b8400f5030380d0000116500c030411038507400c0c01c12071480141c1e241e020700032407075020f40411061040811013120006118028850701000a010b2032001c00000c0c51b001103005e505030b80501c0060101d00c107184991100d801c0e82580c400d061110f01c0d512802905c0d003242d81c1280729080341041c420780c1e5803d40241c90f11041284028825180c070f10505000548051041d81d052940300c203800300c10083c000348103074065500158500c3d0760311494141503010b00001e50740d0030700b040f051428400c1020700c03070300c41c10400075416aa0000107442c2c40a405044001c9c04826503400b0b0b90400c80718060400c0103201c1d0480785418808112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 108338381 1250 108337131 108337139
    0x180a0b0315040507080a03050306040519050403021f020708040504050a110304080405090c030702100b0103020d02041d06040209060304060207060b10030c080906100e0a1b02060a0501050d1502030910060f 89
    0x414071310300381d100c0e0580e58070900103640069040740075240c0c803410a8800080c1c0d030742d40e41e800354041c50940c1000b904603480c080511060503400300d81000c00b20b0385141240f60902c10140f03020124461742c500030301820000c1c407040c00b051825400580e040021b0140218044460052248071940103890880d049180020104410b0401c0030510740d1042d06d03800c1c0241180b4006001948418010100b0609195281d906240a038001e505541c0c401c0c220990464607903484005259403548a080480e081c0d100e01400605246000c4c001c0f500e014801415003070071902c40741c2c0c42002940040f64101c035810b844000ac42c0d1b840c1c8030010712503c10741c00c941d404a0b02c0100c40901234a1003070090004040741d000081009011200303042c10400300c071100900c00c811580d43c28140c50082042000740c0c040c244002c80b040701e18990025006000ba003000c101041140da80d0300820640d1484501e005100a10342d09890410000071346c0070790f41c0100c10300c0a8070020107682201c00126101c1d504000b21502010f50184 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 108339631 1250 108338381 108338383
    0xf0406050c0f03190302091f050403031205040c0314151005040f0b010807110f0a0b010807090b01021005130204090c080d0e030705120703060614040c0e180a0b03150405 74
    0x410902d850302942c82c04010303007080d01c1c03c904500980828103070009111909a29200148044240612481103882100043c014850780c0b0a200c207800040340b1500740c2d5008043c03480b600780580e60000c0c0e410003103450740e82c0f044130311494184001c2c81c6000d40c506010288000420082c030034683c5400040d00241408200700c1214070503410311529500d4030541c082e443c0d03005195940c2100160802e003075881841903591345070110f10508409640540e044070010404003034100b5050b10881010b0300d540903182d080305404c59a0024130140140e02c16626207030b11030031aa1015422030141798110028080780d80200d0243c075903642046903541103004003004011002d02115041800c1e83c50081c90f00c49610002a0751480d250040070301c100d80c2d44504039030104003045000019035005009021241e0b0341c103c100001691050300ea03018031708141041000c1e0380710b02c1c140000c0200081941c1d00c00e00c0c01503002601e0581c0109203601b0f15170340b02c0c00c205050780c0c01c2060703c006100300081c0042c5884e15281813 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 108340881 1250 108339631 108339643
    0xf0204030b0f04020d0b060303040902070c0e180703060203070309140a0309050111031c0e0d030506010f0503010b0a0e130e070306060e240612040809010315051509060f0406050c 78
    0x110010320444424000103954041c4142c06686d08a03400f105661078800c002400c41c4a00d0384042c500510000e40300742000307810b803103080855404c03603a07810391075030703035203800c2444040c1d80c0c1a81c1070382d8108034814000510f940d40a5a00b010540c540007402070025921001c0c048140311880c07040b50300074025081015404480d90001c2d000a2034030350601c0080f081d00b00d582e07004400d0f5050b1842c03008154038010400300c0c0d102d000403c3e44170b400c40e80a08103040020780142400e440c11400540c04407080806640100b04030790480c1c0c22600310b903180a401581c03c540c200116a070306540100107210220148090f805004400328000303010301351144c40c2d072070224100d0303a450740265a184070741c90421884806500d21030700c0780c1c02c03201c0440c01486041030000c2d8080c419850042045103041013030100340304000c005031120305e4003030700d042200c0c04e94901c10701e403155420b2007001d43c0450305400b1034504941d0f0001800124030301030459800c2808006401d400390b0050b401c010005034000c40c1c0184460010456 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 108342131 1250 108340881 108340891
    0x11d04031403010e1f21052107060f09020d0b04020d080a02010f0f0b01050306060f090a03030903110a0311060c070b0c0322030203030f1c050c0d0b12060f190f0204030b 74
    0x591800d031440c00d030f403084d2016446c130001800f01d00c0b851070910a0142c1409940300d46c60003100794115003200003c10b500c03990015042540c001d8038005111902a01501c6142078042c3c00408813040031501d43d0703460340200750041c0102d0304000c1842103080069503000281414800315000440c4450b20b40061700c1c12680c1c0c000a03038034100d040400c402d140c0d1343c02c402100e0304407000380d03845984c501909070904043e1040b004000e4000d420014004203060340b14812100360392080955034400b140e03c1d002c01c40b104105010141c00c2c107805031108455440e001d4020000b41c0c0003030040d01c01140d07542c0e02e507a01c82d402000c0000d040c0e420002e18041c011404241500c130320308410341c0d641fa00a0540e004a5680c0c01020051004c03902c00284c010607214001d82c01096001e1801020303c124503100c5035058480d004080c0d00c5821a00781091402c0f10b01e82062270340e50320100750b0000c0c045541c501100114482010304003110b0f001c04131070300c1810f45400c3d0081001000e080c8c2e5015a40b40d1851402109160b80140 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 108343381 1250 108342131 108342181
    0x1060e0612040308070507080c07050901050d0c05040c0e090f0403080702120a0305190203040312050109060506120c040e0c220806271905070b03011d04031403010e 72
    0x300c0c0600040030700c1803640254040c134002c80c590b0703580741d01912203200b40000907011000c04240207040c000c0000c0c2e0442034900c16564003405036a94010f000010a035044000d0021503012020700080c1040c1d40580c91400705443e000014007040b0004c40c4c0c103403d040c1d40f400c290395001c2041000b410f8010094681000d0184000d107040e18011054a10a005102d407000030980c540000c00c00003148000700c1004801342c9101150360b1705040c5070144c071120f258030701c00034114240000061359058a10546003140c0014100c1441c111000d004041c452600a1440c802d002042c000410125444c0c2822403046045031303081c0c0d40d01c1110000c1d100b1030902c110480c80c1440d01081084c0501240803550b00d810490b00450100448842401003012000b80e4010414901c200030450b1012022002a042c120f4003402c186c401007504d8418034500c5100034020740c0f000494150022860240e8181c040b41d2240c000d207003420207100c2c0090150380a52003031748140d040d80c6900341400300310903d850303801040c082440303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 108344631 1250 108343381 108343387
    0x1805040e010615050307020303130804030206030702011401050f0303070308040c03060501030309061101020306011b0501091e0201120b0609060c0102040902040e091c0207090c020102040f03050106080601080703020108010302040b2701060e06 105
    0x4900255207200091100c0c0301c8580041e041d604004bc00000d4501075940200401d0300c910305401c0081c000d1002e9000c450b50002000c00008090603c071064066018016020f9071900c00b05807410b13901d42e08082c20880700070107200340010210b900c0d0320030389000e18849d03540c0f20b13945440c018004100503100701d0340d04640e034410410301041c0c4e0380007810000b00c11451045021941c141d030400380d004050160010304415030280105444440418041e00314a100340c0700d03102540743c1e4452040480341c15803002504140c040150500c1303458100b01801c000b1a200f0009446c0036100c808010998100b9400105901c0c412018420540703000e12540780c410a15914041e9150701c2c0303010003540e4600f01d2144141e1160707114803031544a17200303404075800341454404840c0070907560301c3d00d14002c1c40c0c284076011036400351100100e401e031000301340c0b0411280c05070340300d449030b0342184c0070030001706004403105600c500303801003100c6c006140b40700b958038041d004580b2090540c503010001e0004803444190621940c020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 108345881 1250 108344631 108344641
    0x3032c06151306030b10060206010e010b070c120302010f11130911040302041a030f0d0f031107020409030804060f060305122203050601090b010e030c011805040e0106150503 76
    0xd0140e030244615801034031442040e000300702440c440790189020941010400710074000400241401040030b201000e1150f695030b40c049803035403c207000d2006402400c40042141c0c0300388002130310a0f580502c0200400507600c0d0052061844000f0044015075100d203041e00150540d840b500500e500310f8404949841113510070714003500001c1c055418055038500711410840881c9090302c01841e0702903c03c20551000b600c0114081d000c1c00d42880c4030348910784500d01c503c800811100c400203150348070300104c005030000607070140c8121860003103c090244041c00250b80c40f80075031074846000381c85541c49800c25041860030303145104112020321b400d0820810024200042c0d403e0036020706e11845880f180042c3d001d00c469654003448a00c5800040c3d0044180580030503414101c4140000412144a0440c0156240b03074545150580c144c200400c426a035502400e211520081381103d540d824075102c40004040315043c88485003141c0d03403540103000c2a090074401d102e0a000c9070900604610308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 108347131 1250 108345881 108345883
    0xf0d020904021e06070305030108100c0f050703140a0503090f06101403032a2104090e01061802120a060b0405130609020304080901020d0c0b0a200703032c 68
    0x40500001c3c0211089004160ba803030042c04050000080180202d41c0c9916600b402040c80d0805e000d02507036406408406580c0c600c0c5441440d492021544855140142036a4282d590340c105403415804c1c01446804800c002c2a07003001000c401d81c864940381c0d00da007009061315150494000380000c080e8002d805108608800c407045100708c604c0c1c0142c9403c02c9150001090840c010000d290300300f1030310a83d01c0810f0702445064050081001c0049454480e5140b0544000b449503d1001c01010403c1209003e4001386800484004a400c800403850540c1e4031000c100a12008041714050340d0301142000e0400d080b80b62150b0090f1108806100041c1042000c1d88644118414280b0407449682c160750481c250b0340065004120a110031074032031a150809100982c80240c1450041c0503030080c0e9034056004402400c082074001c40141c0d0f45036110713196180205248407080d1108000349108040440542006007034080c480e130780105255881c64103506c007981207009424080e11a26560104040c0c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 108348381 1250 108347131 108347149
    0x18030302060a0b0a0504060623030c09040914060405060702100501080601171216020a050108130b090c0a0320220207060b04022d0a0203071103070e010905060f0d02 72
    0x4407000d000141c011a00f0b000079410f0340b442e44041c1d0000d0500000040c0c00c0c0d0800000611488050b80d14a48182c03c00401a240d2100b2501040825024029024182040d900c00e850b061b1041281d50490f85000c0361161510900312421030310395000c00c0802803606d0f814003c500c09190b0846051200b9410070407581c3c0c41e081c05006a0400c80341900c401c101c40d5404100c5d1a180180c0701d82025543c04042011030340301036140c0020382c0501000c01001a2a52103408864800e204200550742d0b07085580e5900c20030424090040b00981c46026407414007592961113403401540b080c8104500c502e00c7c0d0036120001000c12402c0d03445000035036065540f03029602d050400300c3c06840d000590f1040303a494094014071810b64195001440421585030014529a803400107002406004000400c0c006040082e4400c0c074240d03c0046c1c1091140b140003da442422415210001341074031011900c415401186c45426486401031503140d0301840034038101940740d401c40e150305403101520f1003625000300e45001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 108349631 1250 108348381 108348391
    0x1b010914010c0c020d031403010e01080c060405091305010e010e1e0109050d0f18060c05070509010605120c161b05010203030402060a0f0c020307080c0306060603010503060c0d0b06040909031803030206 88
    0x911700e80901d4040600c00d03120b40684604c5805850740f80d51f100c1c0c94590b0741d00e0382400b9403840d03071248485468503450110243c40c01c4403002020311080d80d43c0d0582021142c80c020501701c81c0c540d01c0b00220554804203002c1c1a2445844400924031600b1710301441d9102081521005d03111703403500f1054004600c004c664a15000c103a030501c0d03441039844032002c4946d02c0316200030f103080d51503194000c40c600d03a000b01c4e1016054051070803140d04c2a110810810b004000703110340b902240c410068a481141c03201000c0b130340100490030507400d000708900345024005082100f03c40d10110342c40030a90755490f080140303010304402e100031419460194089542d5110790081070082c880500740201603d480b0340100a403042c1d000d02550840317503445007401d42e246a500b042d0b0748280180400103125042c090292030403034000034000c0c11240c544811503160f65010b4201006004d495450365003031512450300810061080800c002605440d0b4100140b58441d508000c0c05150900c400c200301280e400255a6005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 108350881 1250 108349631 108349639
    0x40b180109021c0b0a1a04080106121a0106120c020f01140402131a0d2105030709050d08070f03050424080a090c0608100f0b0d0605030703030c060506061b010914010c0c02 75
    0x4001006d0080c0d1260040d0f6000e6001c0b982448400f01c1c0c0d0040f143c3c441030b00302d40b00311040500c60f449000d900010340310034061400002d602540255a81040b5046035544d500300e80142d0720111019180305094a0f1100b01184104402006000450a101284410702000c200040200512141e143e900c0300745a031241512030307103514100500303005806101d06d50701c8030070714001e0070101ea80360343c050040c0e0011281000801e00d405000203107030038421403240d801d0741c1c05011030345007020941d0340c11690300603c1c2040d020845d00b8407010822110a2104040c1500600103928206c40441e0780100544401031401100310308010355480082c500c41010700030707a1030f40d060601c038039030b513015045e00361220b20b03805110411150030000032004400801000c120079481400c1c01003039128814142d440d0420301c0000c0024100d004202d0105015034019078020340018120746c501801120400010102d40314071096595550f10000100100415131650b103a00040080c0300e41c2407025030150092241010103401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 108352131 1250 108350881 108350909
    0xc03050304020a0e0411040b040c0c020d0606080f03070605011517040201050c030a030501080106120f060b0f0a1508070e030703080309030c0d08040c1e05040b180109021c0b0a 77
    0xc41d43c456100341c0c01340146840c2ca00c42c928141c100344405041c0013800900552818a030f40307040e4241070060800c4140c0c6515031080744065513081c80200d1014102c1a51f00390394400001c00e40e460141300100031200400019900c40e44113060002c100c2d031040e4030100800904d0a1022043c50b08581d100300070100100c08841965903500040c0c4a6205618041849000c0002c00e056001d03095803249050740e10400c000c0141d213440c0c807558149182c401c40c1c083e0840c1071295106000440740d400c41e49204d50003502d00381600b034840004c54440c812075000004007038014204030020941c0203c040f50702850318500302c051a010100486d8590103980409404400000001503c1c81d01c01c20403500d500d0001c200715040803624207401441507805940450782d2002070000010018941e4100e0103c024448030800300080ca4081003100401a42c10140e030819850384a44081b0368041d00b50a00920040b040569660042003a81c1c1c0001e106440b0103a841d4070b0b1003401d000d2500c07074008003002e4501511542503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 108353381 1250 108352131 108352133
    0x3090d080c0a08030a1406040b01020a020d0309180e06100303050f0708091e090705071112100905010506010e0102070b03040f03050708030108032125030f0204150e100c03050304 78
    0x300349030b0381150140c40b5902c0002400052140c17a0710009040340c00f045540b4440d107500f01000280c90114641c1030040e401518404050b02d0407124010f01c0e40d10174109200301319610104007890041e00c8407100425a81c1d0210907148800038090b50358080500140c00c40d1030703815075401400c28080c032030002ea0b1410740440c0340030401004904030703011010f0042c00c0c03804084075003400c20301c0440b60001083c000c3e85424049205240101e054070000d980c803c0780425041c1c00e4005200803070903040e40c00501e601c03410010b14815500d5128100c0041d01130b0300040f5080c42d050001420403900b6035540d504560014108100420707905060300d070040d502c85020f40381100c250908950b0b03401404800342624030300000004022600000a001100394a035414462103010820402c60b21411180428034484505a40ca403102c150303114041440924240040c004a4061001049030051341210654000985a020340d21341c0000c00d91580c0c107400c075004441e07030900c1a801402c114441200409000020000c50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 108354631 1250 108353381 108353383
    0x1f120c051204060f0e070f09050717070216050d1502090609060f0705120f030601030e010e030403050c0307080f070e09100c030506010810081906090b041b0803090d080c 74
    0x52081480c2029004241040c0c2031900040c00c0c0458003080d05440c2c0580350780045c6000c07900c1340440d400000c25071001c03482d001214018040c01000041000214410000c482149081550064405900400e0300400041c0c64030031000454102c144100c1c2009451f0b400245910a280060820302e080540c40340403076030118506010340082c0c3c0c0d50104012501585101d006030182c40554058070464211500c0340c2a140e0140c0304158460b00b848400300300103401035020350000030000c07150b50000548504100859411078105400840b40780c0c004010031b002e60310b010044540030303040483c094085011401c8101d5034900c070358446c1c18441128580052803044040c0010304016000010910018400c00c2005009220450b24140880c11410115400f0020f521510f001e4410140c020300b03c5c5241d03002c02013400f00700e88408454064070780340c2c2c8000090f0070012807405140b00e188414120200c1e43c4400c0c2480070306800c26a4661700c184882e1000d07681d641101d0003415000350340150b9401d0288542c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 108355881 1250 108354631 108354637
    0xd0c0f05070305030d0b040506180723042d03030f121104150207150c1104020a020303040506090115031223090102070b03130b060a1809021f120c05 65
    0x103026030044010010a00c030b03010000749000c0381a20b10401400107001c042200f02d1343e0a0342c543c1d4019210b4017086410480c81c040141d00b04a40c2c1c00c0031450740c820300301414140c02c0c0e20f0000f07103e000c0000c14200202d044492050f0101d078178050346515004495a204d840001d00b621010b010044e140c0c8070792004c0c0307000e135003106000412502c09104214006500010541c031074400c03440104822100d84030254408958002074500c18034079041e00030345e4081c1c201c40c00020810141c65802c0c40e0740c1505080e03a228401044000b8072500603684074a001d042041c01c100c0700400300c1c421031f4101040700c15848110000a81601d50062840c091040c07450011100007008580b8035040d15a24400d0320701070711245002e00781800f0240d00b1640c540340c44d40c244103d1800b0565102040a50004682d80000e4041b02c84640c4404090842c4035040d40d034014480e01ca040c00007100400ca43c2d6030030900154103004c1c0e101d8030300c00070000c105800d55410000c001c100b8588401c5440516075244000d02d92240300f4011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 108357131 1250 108355881 108355883
    0x1050d02062b02040303080c1207050310092301050d080a03020f07020301050406050f1803032205070b042309060906030c0a170d090506030a090201030b130203090d030b030d0c0f 78
    0x180200d42c0072285000c80080d4030600064000c00e500700c002420b03164000c0101e4101d00c120f00b26011640d00c44407815143c60f040613046c003010380350200380450314031801d11031017859008c114000f42c0d4640005031203416103070381a040140070b41d03821000140410390020840c2c007445900d19006946071613a0803000054000c42d20000e50550800c42407106014040d00035038090408184c0c0b0b884580c40d40c5c030140c04e150303903081007841e0f880e0170620010745039403185101800c0c0d80b65103400f595180803a5a030390a003040015000005030100c0400e060102c21382c507030005a04210740003006244050a00001002044003c0906d4428078000300000d400b500c003407000610803003001d440c1c004201e845207407a00d126400c2d50700102141c0310720244188102c2c86000c1c9542140c0003d0545440c58440080e48005040200403e80c145900d40c007550606032140700101d4402200424010780781d081803d03080307060000706032403a400c0505202d4201c07100c0e68040750030644080c039403c04120100107898003010b90243e00340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 108358381 1250 108357131 108357187
    0x315030b06100f0e0108060a0308040b0a08010609050105040b0714010204060c050f0303060a26030d2702060d091b06020102090907080f07050f2206020c0901050d0206 73
    0x10020801800250035030041c4411203100c48201d81401d411203803c1c03000342c00d103000965425020a80395010303e1141d50055000707000d540c41c864407a256065a80d20691008121220004044081c6940030310304074090006480e00710000b502d0940020300ea80124090300391240c1001a00400b00f0480310f5000c081001514000c5d03480300d95548000e030040c3c450110a0382c980c0070391030802d682c01201004032841200010402d4507541d00700622038841c07c80c0510078042c0c122010031600c0c4504810800f501410040c80000300310321014804098102c1404050041c1d5940c00700d4050005941d10016522140085c002c005088011400c0c00302e4002c10f40c1c2e035007000c0c9800040000c9100e40d03040d001010b140300d05444140382625034402c01c441000301165403a11000305880442da840340314400600c405184c0030a5a070500400041042c0ca0200c1e90004406003d50143c041102c181c041c010507070035070400c071800e03440c82d031600b408500c11404440d00241b15102c002180c6103141041050726030b952040907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 108359631 1250 108358381 108358421
    0x61a0409030206010504061205070b0f0c030315100c030f050a0207030602181507030203030103030c08091f0206010812030118020f0a080103170906180109120501200903070e04020103 80
    0x420065201d500a0084500071411f010000c5400980750001c210040c0c0d00c80020081145400ca20008603040382e40d00014460041003124039904003040950700400342d2148407072001c24200100030801305a410700300d05010301d001079000030a400400068202c94281003c5a80b00c1c0e0700c0300f0407428080140c00082c2113034800301d0a510481e004407510510600e06940c5803182203c900c0d12402c0a0190150040051380100018400a4403803100c42c50428401c01003242040040000500c502412031040700304040000c02c0c80e08d140307504124442c010581c0001410340d005050300d00d41c4051105008400c1a58803500080000380d6081d0b04481a50344044804d98450761400030042c4048020700c0151080800b05482205d20348400044480500004244500c0d102d0000002040721a03540195030602c200207800242030041848582e4ac0035124000010700d01200c090b9403084150340c3d070f01e5030403024800d111858054900260201c240c400c0711410503400d607610300c0120080c11081c45080540c43c0d0b41 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 108360881 1250 108359631 108359633
    0xc150c030e0f010612290a090b060a0f06080c040b0318070e0105010503010306050402150f071505060603010501050c0c04020d0b040f11090609041d06160903020d061a0409 75
    0x540d00c201c00055058054401c4900d000c584942a6403042c02070714400703844085840001032a5114204910340c44015025035103c4030400408260821a01c030304c0460b0f102c450090401031580c5029910040458a4408090900c84490609800d40c02a00c0034404002c020078400031514007620000c180201800d81c0e03e14000d058980c0b0440e001c0da088803d40300341240401d41586e818001d9050390410780d40e00342560328603281d60028050240040c0d8000d5129809410b00155400003041088848008240c0d1030002d8503080a2600d0040304210481d480c0509000701c17030351080120303411600c003481c245031203006030b086440c1410515020b8681c40784c800030700c00460140030b4208484d0340404440030000100c0c10160902075940c140700304800d40b042000312000c5072401c4000340c00c05440c00740000030403004400703d2028805060010201c217500050411a00250800005421005900d001d605440c5075a0200e440801c0003030000b050755440e8070503c1c00b1620240241d211320b140051042c403100c1c150b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 108362131 1250 108360881 108360887
    0x10215041a0702060129090a0807140303070b0720010501060e0a061107030204020a031104091409030408060c21070815150d09020d020607050706020d0305090d0c150c 73
    0x460640003151103091400141c0d035500100d540c0707040720303051035001c191084006c0300d0246091a9200d00715610106100c401215210400c0b030300041d020090040101d2400e045401800c04080c6185038440c3d4010080040091086ca9100341c00403080e0038062014284486224000490760f0b000260790340c0f038031000140482d03200354010354850043c0c49150391252500c070101c540c0b244807202d1035110380c4401810070040c10305500510020101b494002840310380c4034000d928070340c0301c0e9112080d040d071281030f07190112803008856500318807078000841c90149421155615030300014260b103401500829422002e0110002d90b40f4010100300d040714152901202c0540b40305401d5455044500c001c84041059050042107001144260307480982001c2d040c2020354007030954000b040380c2180320203240c440140c485c90060013003a03118002504902c3e080c220020310341030080c0003560030181040c040c44000000800c500c1c05840b240c0c50b00c2d90259080741403840a0040750b41241e49024a816040000c485e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 108363381 1250 108362131 108362153
    0x60609030f0c0509163903091701050103060e070e0106050c0c0d0516080105090c0d11040204080d030c0903020901050d060605150c060603030a0f300903020d0c0809040b01021504 78
    0x261941c40f8030300d501c0b5841071800490400f070300740c5606c45208483c00c40d520141000341e800388280341035000d0f2900c03000138002d00760501c0421609070713442c0c81c014805c00080740905040070440c1c0008160740b0749003000280134040103104070803e10000103100ba10b02071040c004081120000b400300381131400240703805a9502800e001016407005454000b00d01c0e0030060240781d02034410b42005155103010501045980d07101e1303040c1195002c0c1071117600c20305501c0e1400900020400030000e01204c05004801038280c90690f500c0d03008021600c241800180ea4417060380d415100d0940b0f10569500551610750020082c6410071030b48003510028281e5088074000051061514403819200103031105010303da62405100003a2020902254005a049109002664072071011342001441008022140ca80030603448030200d0605803510418000d064040122058018440ca03103100301c07a0b92500e0350165400360762000340c13085450350702c001420780c820040c01c00b00c8019400b06000c1810146001c2c01041 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 108364631 1250 108363381 108363421
    0x70e010f0c06230f07051b0f060c070b180601091a0d080d11090d110a0e0705040303090e0403200a0804080a02090f07050d090807080a0206090f01060609030f0c0509 72
    0x2102d1180018130144c1c0742140b031030040145450b120300341180f0a5018102c10100880a5114820685035000501080040c1406144c00450031540d038541c90404140b69039008002c0d00119400e1440d0000b080e000041145c111031542d80000b83c448203081c46000806000882030b40e12210414041c000e0002400007400c5800d01007400f000030b03240c541210300e841c1c087c020103d58020714040c24900401e1155002c1003a01c1e4004000c81034013502d840045100780ea044c0c95010024170007040a004154011001300b0242803520815200d03490250b030004d14010204114035096000c00080ca12000020890401415400f07904251500e4450a034141d55402002041c0e1091000d0342c04502403128801c442c60251201c0e590701898000c01c045484050048024101da00c20000c00061022544030000b80c0b84207240c660140c916801c01c410000c0c84e0152001000c00980d1400300100300c10703a000500315044a500c4481e00261580508001c0d02c00820b07648800c0e0400141010094034041950f8a0710080c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 108365881 1250 108364631 108364691
    0x3180312020d0e15070b0a09050d120605010e06160305090a0311030c04020f03010b030405070306050c030402040c0f0c030806030709020703120c1b02130f0c02160806070e010f0c06 79
    0xf00311003400b001040041d4000300301c4241010007841000c1007510710455488003c211000c01c070100242c0e5500e00c0c040c089541361001450a0b00740322071602290045600410092914205204445000402921442d0304d50414501002c001c0020103004500742d803178880008000c0f56074a640e81c20704c0c800e45c6001c0d0001d02d00c28091003a680ca0685054400e0b1201c1c03411401d0003a0450b07007850488030596001070000d86051050002c0000024400d01400340309a0b0394102c965124201403041c030065607003480050702030211160402040035031001c0076480107900340c40c2200c02502c656000c00d043c098103070400001c203400001e0000506030440a6000240750701e200412081800704412200c580c4040307e140b0601c40c0002d00c07130003d450154440385c003c2e0300900c000640d901480d800035007210b5880e420b04000da08681c2d003140d01c9008200d00c2070000e2010401428140c5000a8024210041040c0700d5060080c480741581881d4480c070f100628156206104100b865200304421115580e640c0da00752034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 108367131 1250 108365881 108365897
    0x20c01020f0105090601050118080709090b0f190207030e1c1401020405100c03020115080609011a03030d092603060a05011e0e180f0103032a03180312020d 68
    0xd003074014032955200303a101d80c000d441580d08000044a074481c8611600d000103a1450010038004d00074071075140181294507000030541300501c1e02c000c00c514018940351000080f40e0030060813800044101003000c101c2c04005036a102249810354060804400d0150801480d20068204040c010007000c3e1003800f85103805a05e56000e500d241c2030b48164040c00390002030f24100d4000c075074040ea014481f560f20074000850070944288040305020b80310341c050245a400032041c00400f407030a01c81d40c0c800082076992200da100c1030002181d80c91149a12910509a88080407014482e0034007441c409030184040300c00c1c0500c41d45420b00816003050340c01d40c0c032030000100c0018003580540038851103032103450030003000504034000c2038509440031380f9015000440f4000c1100180000044544524400d044174100c550440c10010010721900c1003d01e001455010071903011080901624107c42d80352620020745040d1030011441c24845038001008010303000c400c41505500840c03000e5540f8699610068 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 108368381 1250 108367131 108367153
    0x9010212131208181f0605010203040f0b09010e030f010902030606010801030506071107090e0a0b01120215030c0d09050606030d0305100504050402060f0a121407050d1a03010606020c0102 82
    0x141c1c0030400100055165501007458600034000070b40d01407507044040098480728800c882c02d1401e40074100280d48001d10041d850210b503486070700040c00c0284010350411382440d10b611103080060080d1f0b24014404908030305903038400d02d403181c00310740003400340c90740c0c14400c00c0f45602800303419004030b11078007a000000300907520030f4801c181200d821400405298551a1042d640945010160507081c05030541c04030303000d00540101840013103110001d12480c10103040403072030340704c06070000c8100c400c9822240300580d54951800c034142c2c400142180d0790b91900c41c5084094030400000341c9000d420704100340280000880d81c6441480160250703181d84190000c11822580101d6650800380d640700360621050030142d200030b6210b44060142860302d11442100340c102e41100050740c0c0090f1210400c0d0078010454040c000103090030000740c68850a0418001c8c10500500c402407440c0c1342e4680c090f104d01c3c0c0c0a004030610010340075008019281d10394174000c0d15060b11008a5000d48280d50b0006 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 108369631 1250 108368381 108368401
    0x50103180c0e0a060603091505090f0d110115080c130f0501090606110d02060a2003100f230609060d05040c09111306081b120402010e03060708040201030b030a0b09010212 75
    0x1c119036501401c1d440079082d0308e8081100410300605030b06401d01c01e455994003403200c2040040c4441e100e41d114038030603c0440206500b541c0d900c64008030a1b87d2108802c102028000540c0140b00708100c40400101d040004140000c0804550221007103060600005034110a40d2080c8165038980d0364900610702c40c940741980c0e07070306402903210069000b80b0001c1e96101d0150700801068040356400c0c2440d040008011105802c00d41d000014541204e808202c40c1c1c003210008402801c203414598410816641c10200341c3e22020400d50042200184000e09951002c08031143c0040c1001c08200b5802c0c54103020400801074080e02c0490f0b403802c007110200b07041e84400c4c0c2d0041400380c01552281820100120362000c0c0241000240e855040c0d03006041025960240c407042100300074107416494280001000c51005a07004c600a421090074460a654402c901d01c1c0c0c4240c081c00e02240c1c210038440400c0c90320807003800c0940391001a1041c030200c40d80c19002070002c254514034030001629090351039 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 108370881 1250 108369631 108369641
    0x607120f021c0b0a05030105090304060f090b07151107110405010f05030601050d020f090703091505010b090108040c0527090d0f0809030412050c12010b0307050103180c0e0a060603 79
    0x2140b00c114030100c4540103240c0c01000d544500504004107081d601c1010901399001aa50305001c0c1e040494240515070713002d840494880102e1900700d40461070300002102500c40c800000c0d0001204506030314144119030415490202000402a51100742c0d00f0300e40ca0701d006900781c8600c50b500348000001d860007092072240079100000c0191400ea4a4070041010381d29001d007040383c000003944111036199481c0314509208500d180c0f004901703503810f494415842421300c080708100c1e91814005000c080d250f601504c48002080c21300301400c0d03d0701d06100c41e400c052944060f6100d0310b5925010f00c001c00756a0181c4050811311030300303c5107031036400c00580c64900200d0070100003511103105812652042501c241c10007035510aa03031a260701c07503818440c0d54803070310403d417072692200401030301a0509800051201d49940000c0003400c403a1341c0001d88480303592048a0416485a07007800080030140611810b0302d6200542a22030b60b81d0300e60786400b10508031071146606281c034400041d101d0181c029 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 108372131 1250 108370881 108370897
    0x10c020c0a0b0c0a020402071505010905130f150213060e03010608060408030421051206011d190f0f18020f03010608090f0706180906080715050c0607120f02 69
    0x8074016250400c224000c141e004803a9056252140d81000c10150301c0700d20080c800940035a407100302074420320500c442521010390112034154a040200300ca840799124081890350390003135503040081d0b12410300c095000d1654685281803840001d00e0f04810b1800c8201d5000c41c1e543d910b07840700301410072003018200c460900c50207100c2c1e0400400100018281801554030510688454442c0e41803010000d80d0320250f105444007203400060107400445034017100c150301c000300740b91501c8150309c080761401c0c2100010150502811a8134450000240309450700741c0a0071a00400040c0300d41d0f100000c0c1c11100c03640c0b0480103584295205607902c1d41c400c0c0200c503110500b2000349855a4a011411195100700504a168601600300880c40d002014021708005080130799031800314441078043c1e40c04d1482c5035441030303038030f01d00e0020100811000401c42004032002900c80280d0644481c00507100c034070541000b40a28010b000c10000300a0b084000d035031918107000010000d41d010200341e001240b1440030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 108373381 1250 108372131 108372139
    0x3030103080301060509060d060602030a08150f040b031504110a05010215060609061b0a020901141e0f0a0305211c0e0c03010906050405011103010b18030c1809010c020c 74
    0x60000f5030003200142a1b0380301c042c0c412403401c0100445002290702e00e400c9100182c00014100e8038241d400640c55402051089054501100c664001050800b0441010b8082ca85840c0e860806d80d074103000013080b005a14401c01c69501c1c061415940448520781c0700d038411200003c01280c1940300264408000d400c00d14031003120780352001003052540001170b69650003441004041c100c4564180ca54018040010003011402c901d4410070202d080142c1014040c1d200e0481c4144480da91100c014440d40d101c01d00c0c04907000140340c00700b2450200c2050094010750700da200042082b80000350304e00b4495642c1c010035015922004a040d003482443c001088444080743e03042c121000b6940000f8921010760100c400e08030310b000200f030940703000000a440c116501d0b010070040c03100038014111455401d1410526540c1840c1d09010b950050507403040131050020903040719910300b080004204107005186d65001020440c0000703041c201216400074550a02c3c8001603047e00001c0e8050302e00c0c038010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 108374631 1250 108373381 108373387
    0x60106020c010507030806030703020a08010b0406060f0906030b040b121e0703020a031b03061802031006030317100308040b0702010e1203030612010209040e03040e0c0f0702060313240e0303010308 86
    0x2d2000c4030102405442e07d41c0c18091601c000005030f603002400402000311000101d540641002000202c2c2c040741d1000702800a0010746100c1240c1c401e481900717844040c00d0004005103124042401083c1801d81aa009401c22943e0303500c00d040012000e40010b819100c0501e8140e40000780c1c2d0f00e54180c0d21000350400d04c101428400201d51180804202e0403c43c0640403c90307480d00c42d1070075281c0c55001c4001101c40404031500b58101480100c00d04c603070108040c84030b03601e9550300802c6010002d10040025503100d001c80c030104000c5460a006540040e00d9944480c0c503140110f1156010740b00481c0454506190303001142000949003008244a202550a55031040c0501000e0010241458204e5508200060041c0d8403031250301035070b0140b017004684450a007010980403640143c8800c003004001d10486030000302c020100e8400d07690649540751030740c450504100318400201001407503503480c0040c0d00041c2c2e41e44000c14240c111003000511018025a5059441344800e0102409020f020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 108375881 1250 108374631 108374633
    0x70e0a05010e04020d0903090501110a1502030c07060e060601030506040b011202030a0e0111030403020706020f1c050d09032c030a0602130e01030803010f140112240e0603060106020c010507 83
    0x1d42d03a42209520041c10140c0341030130000100c0116802c880045001c10302da441c0921003540c0c00980342c442030258900802081c80c441d1160304c4400000040c101c4071580010000d0080060740050316141580244103102018428420350348501c0116007081c0060302d080002445032800c0e020784e18510006071102142107440314481e2000e540010502000c554840340c070342203110300c244034201e0701d240d000180503102e0900d450b009040c0170721075011408541c0a8881c9a000f100c011440b66104a07420300500d1901c0c0048200303460902509a031143e15600e018803920602d0780020031920701844503001d1042410760320700c000071035142505c001a010360083c1d44280000302150b0080070f18190036a0407040036030741c1e01c15403958104260000c0390754120200042114a2074501e03088058102c00200c0c0078070070319400c0020566000b410031181480e40358000041c030076140038420505082c0092700e0704102901e954200c41060300030b4603094040d2040c0000008c0d094030100300800f0400050392a1481e010385 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 108377131 1250 108375881 108375887
    0x30c0309110f04060f0b1206030d02120c0106090e0a12030c020304050913080a0c1b03020603060103021e0a03020406180b1c06260c1207090f1b08040b070e0a0501 71
    0x12902c40c080d04540e03240400b00703602d0310341e0a4040c000d09150040990380c62031000b814925220103803926020340d01000741000941d070042540d10100c408010703107540303c402c688506030140441d0751204410615000e80e02e15004d8003c0343c3c80361010701550003442c084c0d030301480c00c0702250265818803006810034081440f003807402c4111650091270640c0041e040b1400c0d0b8545c641140c0c414042c0130040348006446d80200051148810800882c00000d00e5510f0320b56004602180301c01442c290406500048000003d880000701e9058040006d01c460f0b01c5215165010300290321500601021640f1040304040040b00916408151100c07808603508040c2000034294490300d031251400d10564550201180b1030b0303d0076027141c481c0d0b0301c1001807000200c0c0882c17105040030840d42d69240610030241c0404004400007c0c0001155004500080d2000408281d00020b001c400c0e8061082c3c0c000500302c01d0416031005215003d680100b040301201d0f00d80000035140c9003543c03140c00d504140c41c2e034400c000541c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 108378381 1250 108377131 108377149
    0x20705010e010909050702010506090907051c031b03090513020313170705120d06080307050c121504061506020307050715032310120b010509090c06041401030c030911 73
    0x7506040101045886060038070036194221a454010707952038041080510380314030304c1c0da00141001c0c0501038a60038500030a210608a140c1c0c542c014041005441c00c040c03062249030015071200c1d1481c01105900d207001880b1070000d02c80c06108180c2c211044002001d07074402c40c1d0191450191036040908141c0d80d0341080005060043d041d03100a010078008100305120014000004105c00c564a0304c4810324a400c88244e60490105a4010302c00800080c0000800c0c800040c3e0441d0090301103200000301e41e00c7c00b402210140340d0040198180410046140c0041e550141d4401140c030035151580c1c0203e90b40c1c000d444025106500069041141240300d01c1e2108420080b03140c0401c0b031034648180c0c03044416001c0f03950003964400504200d104003450040d00c02401b6004805070710680d1640b103c4207000e0040c005c2d24400c0c14080003040744140708100941c0b00a00151a0750307240e40c0d840c545000340014030880d0b43e001c00c0c203060b402000c03a8803902c40d044180d5031000d00d000c401c0741d900d001d20031006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 108379631 1250 108378381 108378407
    0x11403070e2b1b0308040605041805060f04090501020d0c050904060e1009020a1803051005060604121104020d09030c03030b190b0a0e15090126010b0c0109060f0902030d0c0302070501 80
    0x4181400040080780d03a0303100400240c0301f25180d0f2984c4900c1c208100400a60182c0c0304d2030719509c1e100900c5450356604002c0c045081c411a00031801d002e150403d240244542e07a407000b441d070f19001c40e10b501581c01c800a800040700840f4100903581d61a075000e8041f83d4200c9003000c0c43d030b15440c02030094401c99070203410071701000c1c80e02c0c02041c0c803d2096001e46042c030b6001900ca41c0d1003540400301001d00380c000c0a41c0500261a210305207483d00040a2203045031900082c40842c90303100a1259448a5050b80e44160158805004c3c0c00d01908025142d0700b40c6410980009050071120800703407c0070101403d0311080b81801401041c5020b0344030380310382c212904070300c1002810b04007600547c0d01c2c01010080030301810404d40d6200b50290000d4107045000d1845052800e400381407542e04000300d0965411148501f500c0340d900c8820b210881e00505030608001d0101c0c2c94980184a58000e42d488a20f0940c400c0d41100c2142d4081c0c64182c0e10b46804401c02030042c0d10005c0140120351007104179051034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 108380881 1250 108379631 108379673
    0xc0c01032a0f0c050a14063412050f01051009050609060702011106070f0e03060606090108040203030403060e031b0c0d1202070302030a12021c0503010311011403070e2b 74
    0x4050340d503a03142c1c00c5c1410444281c440070f0a0b800e550b00820070510000e80c0000c00c042d0103200810303100342c5401c440b0b940c140c2031002c20014410311203100c80c0a90140d030001080d50070100814500f03110364640404003030090030f00840c10f03042a0308486010320307189415a90010301060501810074100449988240012070411198a0614902c6482080310a006d042c03691260500720148940050401c15110309403417213036000b0000d02025403140310481e0480c400070b00c1d010a0955580c00032a1542c422a0b00040107603240c180070240c5130b4804809002540ba01c0c24001d42048035061015503501001d246095015520514243c0065040d030a07203504000c250068484183c2c0e641c00181c10b00e000c0900560300410106c080b080f181d5810302c1320103030700c03a00201c3c55900c0d03c5a0010081c254041400001c0600d540c103030055034a45c0c028112038051150000c060f503628540030800070052944a032440b80620b1580880395140718415130071b403995a5080400c911140426100c100000c18a52440030300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108382131 1250 108380881 108380897
    0x50904020f0d03110c040b0112110f040b0a0905040b090f0402040b030d050d1b020a12020102090a06020f010f05060303070305031312020a03090602070308120613020c0c01032a0f 78
    0xe074480b8520b6120a50080d00c078500b800900c4c02a45007440410b4446034032451a01c3d500000581c0c00c103145e51561100d0f01d200054a800b803c80c000480e2003126100c0500f42e4003c030700005d40701c201070f00500b480401075503036031525540c400510003580c1c4c1024102c1da106100070002201c0700b070800700c1154800d00051004c204001c600300802d05000c008108000001c00000c3c084084c1d2550340034080000484aa60b501c408103198402503c0c0c920700c8a000b440c004c05c0d0030403503045600c03d40655207a84002880c1d08241540c2c1c500107980d03003405090301102d9500300882c034401882a8861a0b02c214806405140750103507540d000c58282c1c0c070003807400c0028411183c400000c904200051219800303190020842003103542800380c1002c60310307403000c011940308080910020748100240c03404040d80c03825840a9841d03460000351840310b800d807000b440c2c92002c18098004880011b4003c2010001e0f2402c02404a410829000094005400041d400d4001d400d44600c5845491950403e200f0303442e200103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 108383381 1250 108382131 108382159
    0x403030902180a0f140c0f161205070302010e210c161d0c030702070e0c0c060c130812070b1f030602030417070308010501050c03070b01080a11010c03080105090402 72
    0x4016581503d070042e180d40d07650403100303200050307200f20002001c41c22021a441d18004208450354072410352502c1c14080e011910030f102194400800c0d80065001e5080b1515000250004000c0d4100f078070160015070030003028030366010010401010040328441860070034001c090703a940503503111032855260307803040301164600d41c4004005d21018250410400c005440390724092505048060020901c10b1000c00900850640010700352040760b51400c4000300c95916942900305074042e400768040303a07018640c01c2080992004000780418170800c80303a003000e113469a0b0603e03501c140502052800f444200f00c8000403500c0306109175409441c1440240300c1080300d40039462000007e60003110380940200c203100402103a4451052103140c000c88c5a410200643c0300103110000610405052003000100c1c2450440700b4000c40d004c0c1908002d0500080d69143c40d5940d40d11f04129080d104014400500800c962241c40e8003010203415a5892586034280010001c40d6040034104a92041554840c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 108384631 1250 108383381 108383419
    0xd0c050910080a060b030d080106051c0204050402121807030201020a140a0f0503040906092703020c030f070f091b140d0c080601032004090f0905010921090501080403030902 76
    0x654891180485c20a071080280f5191100711a03018052222800040c0314850307202c01514203a07011650314071401403080580400a00c00d07504181d80181c000550199140342d150f080a00840713a1480d00c4804401110034685c076803049020090050300980c4100380881c44800d11459420303030350002d03118012308a45d1a200700ca003100c0000c1f14035400c00304040028681900c100001405007080c1408058226061501c640700000401c1d070400814000603400c0c10b10800844928003005004c49907140c0d00700c80720742d5840e441d0384103511001d40e81c0c20300410183d2540c010703d0441c43d680300c1c4010044102140a840c024140070f4011200c2c1c00501000005940b50300450f41282100c0d00c8503121404c0c041c00060a542d100c0019064041e0a40400385540300e9800403075044685200c8009003000c000302c050742c090500c00202500729800c01c1c0c038003000c1c00581510548075403030181ca8200e8441c0c21500c10f40c0c0004d010701c2031724040740f5180002030110340a500b10042941c0b00821042d442d500c029102c1d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 108385881 1250 108384631 108384643
    0xb0f0d0f060b031209040905011e06090506060a09170a150204140d0209160905030111030619060807051c0609020a110a080a0c05100204090b09060d0c05091008 70
    0x6484000320618030406114582c072415518110981c054001c4140384820b1004170700c20f40d140507000750742d141ca280d02400429400694216800c4501000d008205e070002c0015114600600b000145410003148a40c5462030440d03030501e08070307151002c40519203090540b0000d003050300d80d60a40140d07200980007400001441800e0b0640ca80b005803140c1c140081c40d100504c04181040c041c441c0b0401c0d07000565644801c05901500c81101d51940100c1c100e811110071040f03900907a010341c02d2284079400f90320030001540c070030482500d0b40c00410050800005911140b44180f0000c0790f520004140c11611070703001050600b4411140b49800c10400110200b01d51b400d034807005185e640490f114011a03800349481d60000303001d40080803c03481c60789503140c80c1d104552008003801007144019003008410710000c8580c0307180203811500e0fa661103400b40d0190020200c00c911880040d00010164505a40804141600720301c051610a060805002800f90058002000f541c001800003904140800030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 108387131 1250 108385881 108385883
    0x5130b011101150603060503060f0a0b0102010213030c060e060304110904170d05010302090a0606090e070315030f020405060604030302060a0e01020d0603141c080c0a03060302060f03090708030315040b0f0d 90
    0x100030f956450008001e04943c45a0000380c469007218050002d00043d04070240d81203480740070001550341d46075005038024854941041c0101011860000600c54003010380700850305951a19241b5405800030008a44030850f002003a100300303068080518181101519071180c81504401003401800c01c2c400c480303400101d4104c4850741c50788014011828010b0606410091007a4140a40c509011000c1d001ca42580200407544040381c00040c4064804d8100403607080361200580d0300c0d2612401d03c0144041700300010b0b40184d0600001c80c1660a200c4200c40841390550f024001c0da8544203000e0000c1c2c075076101000740da076400b40046d800f615070350b110703650045111b890070040304038100d0180b40c1040c0c1140d0b001e9001c500745040907040070b9002580e81c1c0e0710003a00d00990382d40d110309160a400a010365000a034001e180480c1182c0071101440c01140160700341c00845d4644c654620685035240300440d10301500303e003411600f84103401c054000c4d28910500600016100c000200426514010307004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 108388381 1250 108387131 108387161
    0x20403050a060e0606030c040510030b010e100b0906090105070c03021507050105100509060108040f0512070201120509121b10020a081008060f0c090312130602010605130b011101 78
    0x210307941005802c2c803079a4203190050024200c01d1401c1400241ca404070440003501076a1517800080c0c1000340c4580c004051035208c001d58a5650319003180e2111480110346507002014900004940d0f8250700040c0c0f04250002070005203000d441c00011107003900241011111100102808130040c0d4512041d1002c4103000e0302320f680c0783c40c0d06040c81401d442025013124895001710b1401c0c006070b00c410f00342c3c5600080c00e00b0400241c0e192407800768a941d40301000601940198030a501b001da07170420040080741e000341d96141c88d1a0a40a8003800c8075001da41003412a401445a115a5513100016216507807540f2070044505600c200042e0a240801d0041d088081e8009443c040d140e0304844d80c540c014041d1f03007131082240d0a000304a42d552030003500c0c00c0c0308000004001401c401c8075408640c04c0c0f030405820b45001c1b8081d00c0d00b420711a0085624640075240210000c122644144120812100000c11000751819154861402406110701c0f150402050b1a00e5000d90751003402100e6001e41042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 108389631 1250 108388381 108388393
    0x507030506150604030f03080718030c05010e01050c0c240301080307061d030f25110132070201090509010b070b0105040b0f040e070503161a0a1403060d0602040305 72
    0x5010404082d0b0441e4800d11810b4180000c0c40410300c03080d0356116590b8075080c00340150700c640c00c0a542210301900803240c4030182c04004000c000c1c07030032100c400b11042a00c4a580f0440001d005540b0390107055807910150340042c2c0700380020700d08200100840316444103115013114400c051440c03194000d0700540b003642c6c000a00c40b0100f140780d106510182622040f01b0000c41c0c1e4461203036440b84640c10104124890107e00c04038003044200d80303052040c01da16041e403085059440c3c000f50039620703061282d0101d00d4424036201c60010221400c02100c3c14020718504140010241c65281d0b00424000d904100c540c11002c80c0507120081140d01a1072107000d00b80e101c00f880d20380320030810783c141c0010b80175905003880007040f6110102c48501d544006c4501007051060320254071b14058060b44081c0d81403243c0c82c1240c00d60321440d14444c042e600000781400c10a00c40b885c02000d20720070051004000740502030028482c00020002d03541010000340402c0726115161a03100c02c0e078005400503141ea4000d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 108390881 1250 108389631 108389641
    0x9020c031902010e06011203030605040207050d0f02030316050d091a0108010b0f0612061f05091c0807081b030a091707050f0409080c0a0609020306100506070312090507030506 77
    0x24103540058800910007800104e44025040c1e46480062152240c0810785e6007050007058001d8000d48007070711003d0300c11910b550113410110365a592002001010440100c49200010320100440b4400d10201c0f03040070010b101201c04030780952200c1c0c02c07007a4140e555031f100800548600744001c281050b401c001000d81d4103020846084609100300a44a0410020f0b89106600c0f420151514013100c4918481d26aa03030002064100300c8500c82d1032032424404590702a030607008000362a00440540b4080074003982d003d4807140300b01000f036002d03081007420f00038000068402c1d0010300403900801e103005144020100c4183c5145c005003120070100b85411428095414070b00c0280700b18154460050402d07614040200d45610039425206000d66207602019061014213022511841180b00407120a85210300303004004149902e0202d11074000d100c04104401200c12084040c0c07800201140d19200c041ea600341c6080e0045207100490700e480722018030200301c0510034180118041d80142190b0b20b80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 108392131 1250 108390881 108390907
    0x105010f0915050705010b0411030a1d03030402150409060602070306230105040c030e07031b05060a0e0108060a0806040f060609090503040b1e03010b041d0601020303040f0c09020c03 80
    0x30446000100301c0070701010400410165030700c250058450400707a82c3d840c9142800f0740501002c5810075001420704603e0b000213074050006604c0351144d0f038010400400b200030b05020507803901c43c0d824071030b078421700100d000344c0382440d07803806005403ca002c545410798981c3c40f48199515580300c00301503048281e040060007414000d50010b884000d16500c0c400340044090508440180a400c1c02240c0d2001c0a54800d03010b0382c0a51a1825903504071075010340d5900d445008001d81c9441440041144030001446d41014016280000c5042d1208000740580d040110750041004140c1544001c0c105000903040d0004c3c41980d01403401043d4a071101c155900700801950010341c0102c0c81e03246000303407443c00300b1808402d8906690b01d45030031a41d00c07c985201b0750031042d10b803c2c0c610f104260000000a00030000c0c8024001c40b000c00c40741c2c4c1c100d16580701031b407150042c2c11241d90b405a0070400c0060002545050403000d0a4854600080324a4036105208101e801031450000d140c0e0000481d1440c441c8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 108393381 1250 108392131 108392147
    0x9050108240a060918060302091602030c010e06090c0301060b180a0504050103050303040302160b07020607060f022b06050a0314070806150f090601050714010204091515081501050a1205010905010501 87
    0x2c4446021b00480349181c2c00f265004400804500c0c0718540c07412600261751081c0100c540e84842c4000030300103620880c202546450303040c0c441c44032920030400035031014203040c0180401c45450310022810205030036440484a213003408800e5001000310070204241d610b40c0301c2c1d64040c50041e0000c5840e8545850042d02d0002000c82903807103002c0383c1d40c0421000795050112206c0f40d80c152681900d8020a107084009801494059032007030f4008103c2c034040130511030750403800c590a1041148051180310300e00d02222038500034580c04c601800c40c01e002050400d602e40c499429000c00316284c1c507940d00007890410307505a401080c104030104044049140c5000040c17900c000840b240c41131390801e00e001030524071602030000c0022041c18200381400c0001c2d8191001007800c0d15051203011042441c0f41043e501c00d01030160b10300608202851214401c0c2d5040d442090812101400c00700e47d0401502c4c2a081900c01e203040101044011008102c030340910b600a10030b8000100f03003075060500140c0420 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 108394631 1250 108393381 108393419
    0x30501030318050906011d1203070c090e0c010c0201020312150307091103072015010e090102070507091806090c080106050d0c060309140102030702061609050108240a0609 75
    0x440d420b00c1400306a80e10b84080350812024200802c049104c1350f40e00030b6441d5030000341580640c00b480c00c0d054105d0044001d014141c403910303108400320388460880d41120080711041c88158071940c08000154003450349a40c1d1640140100c80c10100e0418100c1020308040700c040300d0344004e801c912250b030700342004281c010b014946024401041021310354502400001d04000401c90207c9461480d8942110b041010032417100549a0465800741c80d403031062020301c2002d400805810024203001010b100f5281c1ca658003101500c0541d1a01c20028003920203030b44000068003c14240c44005542351151040c0c1c20710800c80800c03124a8162124219000d0303a02c0b00f07020740038401d10324000441c0200100300b581d9035814002503600e05401c04080000402c0042400d40d8800030038000d0b1181c000030041d00c42c41480d840c20040101e080da048420144074890300d408660040d012540c01011411501d549581542c40300190b1446040081c0c1103082c66480314000c100306100c18458807407111034904e404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 108395881 1250 108394631 108394667
    0xb0a0902040302030309040f0e060c030f01060801051c1e1a0601020307030c15060e0403050912030408101107020a0b040306050f0621010e01050a0c0e030a0b010510030209100305010303 81
    0x400c2c03954001c070b03440b44a00c8040c684203542d9100040c01140d002c3d489442081140f00c00c40b0403510740f00440720b1043c2c1c0181c411441c002c03040e80000443d0751186a200e4181c9401510900d0030960740103116003500911035044803208a44172078004520b24611121030f500e80525280c405100c50f00c09140c03540c00001d024a41103410802c00140425000f114242409502083c801051104c42446400518031a04034034040c00c8058244401d0581c48005012541800c551024900c08002c815070703030764403461080c040030360810008151010304990260001c0f40b100391070140380445d15400a040d8410f80d4010303081ca120003140034403d0106920a180c1e10404911105146007821400038505051181c40560740c01659801100d0400e001c0d040548a1500b10009006504181c0d4440c0701500e18040207038006003512903062003031326001914607907050304908400c0700d070303402c1c042480001072481102d002495020131520500e5121107409800c0710706241d50000d0300b0750640c5001440e03040b07803550980c06 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 108397131 1250 108395881 108395887
    0x91f15020a12050f03070503180106060e01050901020703020d030801080f0118080a0509090108010b040f02070f020d1a0106020105220c1503090804030f02270112060603060f0b0a0902 80
    0x1056400007000001c25030080c81c0b20700400c20702c0324120b581e8404c200b4503a14100c000310a102c891030b04000654042c40c05c0e030a030030001c1c1e92001065800c944540c440c500000c1d0301d0f085071040b19406100100303441d100600c103441e055a10303074012400301081c0c5c0c4001c60014980740010041da200c01e04c80b4403103d55040000b440440c15402724a1070700b51000101902040e00060340501c400e004204950300c8030300207490110150b964220b418002c0121002c1e140c0903900705081c0700300405c104e00c00c660f005944400300d0142000b10b0f80a00c40c0d110380d089403c0342e00785019614401c0207580801c203030b4024082c65001043d5894825443e440140d081c44107000340708920421200040c04256240090b40c2090117000840c00a140c0218068041440f002e4505400010301100b4014184c2e07841d030b0000d000f41c5410228070030b1404900000c10011401084401801d0014010f040b22490090180c07030241101088150f1a0f46415040780c50307904140300c4540e642c4541d40030300c0c1450501c84004004000d03046007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 108398381 1250 108397131 108397169
    0xe040210140334020109030e010224060402090d051b0114030403030b06040b040801060503010b0105042306071218090c0e01030203041b030c0e09011b031a091f 70
    0x10942c0000b40c07480790000e051030000c5900511494a030b99080164454007856418080c402a00820040805400180105540381090b500001e002d500b6804042008101c0c0b014140f0001101c100c00380240398001c0c0c00b00002c44440e541c000c04030a5050142000c0c00c14803400000302c40001911024550510001800140d901c0e002c110a030ba5115803d0308022907109001400510184034580200580440101c1e010400d0340c0154002019101e00b40d00802408051030019100760059120700d0b0101c890b901080c00c03280440c080721038880750000e000e09003065900d035108203144602045000c000740d2150501c108580210382080020a4809400c0103060f00a200007041c80c0300d070501c42414960004041804c00880c20162804040700c040d10314031181e100d14001c214803081d40700d0400007030000030124044010610400b510501d01103100000541700302000e6001d044444500d000300240d40c2180b0384141c940d1043d480c400c4e038400c0803003804019518800f0040da400c58110044100c01075450305 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 108399631 1250 108398381 108398417
    0x123090c090c090402092808150402030a0213090206030a0c120b030318030a14030a0921110612090d030c050306091f0f0e01030618110603090c04060e040210 69
    0x5001440030780e00546d840038800085005542e074544500184031124880c114404481c41c0c080c402e888401040d11300c14103040740c0b850074400d4142c50203503160300044503010043ca404507180340c090301c1d14000841e2198141e0002103a9400407181000c070580ca40718510180e42d4001038191008222010400c00400070714007003552401182c40d802c4400a2081d6601902c1d90200b04021110741c0c03041400b010000000c11598503a00040d0b96400810b9407058080fa80c801e40407200344000c003055a01c12003080194540d903c4c02015a9000c40d0000c07410400044a002030000071445041c050004111072500035800030b00311104100507004014060061200d10307a14402641d03044640502120802c2e07071b0b82501000112540d0f0700080c0140700c605800038103c0641000c4a04a80c002c00080080d80b822a80020360124400001800d00e124a490141289002400703540c0100000c0c2c101e0b02003c0d000b030301290440b180d6400810000c40e03100c04120445c82c108154019409a5143c410380c0760082c04100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 108400881 1250 108399631 108399637
    0x10504030e0f060412060207060b0619030216120908060a0605180a110c011b050a050a0c0302030d090309140a050a030807110414040201020120070201110123090c090c 73
    0x10300c1191500c1e02c0c20129503d4000741c0b4040e1903007110001c2409217910b0210000c0d44070010441c0c1c050705013190174900d0300e088010f81c0d85204100200c0307590180b42e86400c030000d5001a001c034801c0c031403840b81007010848a28621400b8130322170326102d150505100f80c6520f09100204592a41410700344213016540b9241e47d000002c5850300404601500d609580b000501081460a128110042030080c459401500b0903824081d00c54001c11180681600803245440350407841000b044042085c1c0031194421401c5904450091041c0d038100803076801e03e242034510840040e80006c11403c400d00a42c007031000c0518100c0002c0f2564040c03a4030b030101042c90604a448054040030000c00d6040c02d00401e03845000322500c0082c02003018003816180f89032814000e80c4d0507401076280c4007400084115000c0308103e502400586a82803101c16401101c510f2415141c48515540395052803584060b0001c40359400505420706400034070707220305003900d024146010780744142c0c258030074010701544500807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 108402131 1250 108400881 108400907
    0x303182004020f1c0b0904050303040b010506190c020a050907020f070b0a020a0201081503120307030e01060305070b130b0408071e0e0a0f020c1c020f0a0816031e030f06050301050403 80
    0x31400d2169140a9001d0040400c0400107400c0403901b800c01c4100480400254400ca1040c1e00381c50042c0d80b243c0500140380140540d044856071100440c561690140348803c8040e0710040c0507600b07161711400403c00541c0151800303000350707000c3c20700e0381c00041e000d01582014203140c0540c80d0501c800c4100003035550002c00c00181c180a08035003c100e00d01c1c00038181d4000c500c4003400312018815035110003071240e4000c95801000901c1c00401c20b0b4080c9040c011a0112074100000700302d4107086c180c4007a002c1e0f00500c1c40a103440544c0300006041c08260000c0e000a0400030b0150030802c0c50b00c01c80c00d050364465031888a201c082030300140245960b2540807030704031090450010380c4520864181000b880740c00c03c64050740c8a0b098042a40e861013400c5001000120b900380d40c0d03400d00568203ea641c00d2403180081400e40b082c0a0b03d03256000d415000c24225010f480c2ca5048000d14401d80e402d84150040e00d0310009407646101c200040890044100601d4190001c010600c2c1c5610300030071950304600707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 108403381 1250 108402131 108402157
    0x130303080601091e051305091b03100510050a0b0c0d0c020103060503061f0b07020307050904020a030f03110d05090f0d060605040204090f0c05040305030f070303182004020f 76
    0x202040d003507441414003d02829015418035060307641c40e4210590740c2c1241c4509440f8400901c140581c4041d940120742c000c004041c0105500c84c0440e10510b80c01c005045100d40500c01c40300f0210b1544011b01580d8001d18404000c0c0108604001c14040200070395001919400000c1004201141c4001900c2444004c14644003602000c2c0c0e01c0100c2c05842c4642c03016506200304000c0c003a00310010007104141e21202d003800103d49540d0704440c0a02e008688010358507070861a002c00980c280301005079481440201240c107826269601c1c01c8131012070140982c00a2403107800f0190518081100c0f411501803414840c1c1444840350002d420481d214403018001c002d0a141c1500304105c0c2d030012000f0380401801907458a4540728110020001e0849403000541815511100c542c002d00859042c4c03074110010314039005038558490310940c0120b40840405542c1d0705540b0b1012611071680702268828440110b0201600b40d00e4842140d403d050303603100304d20400074456120100c00842c0d0100742ca81c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 108404631 1250 108403381 108403397
    0x8010e100c02070308180f010e0f01030203150303030c0c0607080609070c030c06020406020f010b0913020607331401080303060d1412090909060408160f15020306100203130303 77
    0x90002c90074001180e100414514020992401c40744021901c84107921301030340c103d10220603c100440710941c5010200b030300a504850540c02a500c40d030010740d8482e590b00d1030a446e1a04460200c1d1450b4002ca414045102020500c02248102800460b400251034540042e950500c140000e0801c1c2029242509208180a100c4201070154070341001050700124115116552988040c1d102d07103240113402407552030440709081510300498028000d004d07000c2c44070780365291035080c0030361640321100039038890ba44141e80d80d040b50f841c040503a44a200310700000c190300d14014010320640b07a0001c0252001e402da00c0c01480f1620b0000181d0380d2224003222510482c07003c504108422074450005038119002c0c0d411007013401400c00b0010608114296291145a03480880b000d0300c410b025100103061100c10000d183e02414890301000f81180544090b2480708125070300c480c0c014426011028035142c0110420266292403001c90b000038403036001540ca00640101c5c007421040d91401700405001e810 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 108405881 1250 108404631 108404651
    0x105030910060f060f03020c03030a0c11030301080102070201080f1306020d021b070815090c01030c0504211103070b070b091603080c01060b0a0203070f0204230402090108010e10 78
    0x1c00c0205041461400d040090b691208180c0000d41400e00075400402c188221000100d4402d1086540703010040029500f1a00d5640000015040c23581c401c000300505034010701a1880140006d5009041c00e5000507610002e5100242240c0001818100d82e40041c1042040400a20320009a0a40c0c1308900691300c5000d042e00f07600074000e0411000c01c0181380d2800404003000012130700141c1d43c0500c100c8220b000a2188076548a81c2110404155000003041c0f02165000307400180a00710036003051801c0540b03501907528516005d1001c500800000c61008041c0010204a401d2840060b40900300b020b051100c01c02d840d1050800c000c0c1114035520004070b04007801d01880000071002d40c0080c040943e00d003460003450304120701c10661340d440c0c0701000520041e02402c9a040c400950081d504000407610703a1b414800f00c0003016600030f51107500c210340c040b000c0c0c100403000c0031440c514007195050600501c040032005070004201d90785090150040d00c01c002800c0071800b9403600f0301003000c50395 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 108407131 1250 108405881 108405883
    0x2090d030c08040b0d061815060e01050f0327010b010c1e050105040305030a0606030b15030405070b0c010204180b0f10020f0114061f140a09030f0c0602070f0305030901050309 77
    0x103960103d40a5680400c000802c1c40040d0011b5003201d80e4031180d120040e6448a00310201e8400400000c030040c900502004820b000d000b04100400050604da82010101c038990640c60380210f50100b2070b0040d5144808a0303068000341d40b4146503084000300200003600300081e008100d0000c0241c0740120040e06110444141c0840000040c1d0280003400700d403d080c40c0103001034000313407900c6019070300304a0081a02482403060803854180244891421074561300928407a038005001911103009522011803840000c030018614018101c0005984134a00302c0248100d90120401c242c0850400c2d0002403a6a101c062246000c07400300d5140a003850421001c1e0303e003a8042d40d00d88919400c0480360b262030320286900a2007904c06407481c1503102c0403146c501c1003002100da058030100340008056600008400041e0202071400d003020310700c840d1a5169080d05100c000c404682c1a0030600050060b19814440800200108407404d81c00600b9a91480c4d01e0b1700545040904010000c4001602004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 108408381 1250 108407131 108407137
    0x304031a0711030702060304020f0117010e0702010f0b060d021b0109080301030b070503190c0c0c0b0d11071e02040f0e0708070b0a020a02120f120a030f02090d030c08 73
    0xe400180c06545000c8505228100201156040003040b0050703021500102c011003214911340e80101442c2c61940c0b507500300651621011000d034100981c00e942c2507066091070341c3c2d9502801e00d07181c4040d481d140c1403200a00351416000d204000342e00380090060691940800d803412600604405a150090802da000c42c1c25a0200460401d6080040840c14020b032000158140c9018400d2a0150f58590205a44c148800e41e0a20b5118402203d0145002c1c510b91100c08102403a00d402c24504115817030321a80800300d031700305178014800056092048001e0f4402c6400380c0d0754a1040c2e40c140001901c2e014640b910080340c030780000703030803250000855849500c40c80201500034000c1080500310403802e40e0322400b60056600c90f01c04d40364041000b08002041d0341c0803103000e90040c0f11f002000d41c02e0091400400c030100d01c0038410481e45440c04e00c0c091103003242c00000014000e482e0030380c8a0005050307800440e40407200c10710421400c29591215030010500760303014181245031640515085e681d904c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 108409631 1250 108408381 108408383
    0xe0402060c120706060509010315050c0c1f050105040b150d0f06080312101202040e031e0a03110406050307081005030313090b04060b0a141210080f06101205030403 72
    0xc092818000b00080051026209660044400300010b54441c414451841420f02000c0c2044402000404100845401556125100d00303113203418420002d0200d4a0000e8000b51180220110009403034001c2180c420580141000c48040c042d100a20011400c500207032039100301d01d440006010b1080e0716a41d04082c10381074400780200452031b541c1e400541c5940044204004580c3c45402081e4603a403969a0b0741c2c1901c58400f00110180515400c100003000ca801150040d400107100d03080d41d940400402420104680200315034641e0800c000804403040030040d05040e000030310050101580c403500352a4090014103001126031100341c4c640341c0c2802e080d4045a8544000640550450b03900703d205000c45403600c20901c040340c280f00801080d154240910008840207115006c4586d108000c010304c600315440c00b0624080d6055604107184800b1200300300140d41c0f00c90100320740d50341001a1060070710301902400d80d604040c0d49200324140d19108003401880d0340c0d00c0d000284101030003114021 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 108410881 1250 108409631 108409633
    0x121504020607031710030201081807090b04110403030305160207030f03030203060d0c031202070f0b1e0d06030609020a06030213030201140d06080c150a0504061d030a0501090210050909010e0402060c 87
    0x74179000c0001040c050250204034005a0040c0110b0000c226a1009000e08111507000c0c0099500b8100b000009003040b1704090390042d02c8894056061010200410145002e5980407034a0725180c058103d1413040b040d0103100b15481380780100b010413000755105620a50610740981d40f0340740e0a000900003907201c40c1c06480c84d083c04000204100c101294811411041c1d0251030101c0c0d520032082002d03400c14070a0020f40c3c3c1c01002000150941c013603040384994001540b060a060300509104110350f40380d0801c85007255207081e01e0041d441e16080c204002c0a0030302e03095181060f00710f42d211501c4440d103c000d0500450000800d20b00500105681407090b0f60381e001c22200750784d50703001580ca4010100c3c05000b40301c00c0051005da02d202404036160364010f51111883c152605100700e4526210481740703078016104000c0030009540a03c11020058052000898206500d0040010843c1c00d065050140101000700f05555110b580c1094111283c2c101828002e9407a80041034280c80760403401880c2e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 108412131 1250 108410881 108410927
    0x112020402031905090a110a1206020c010e060a0e0106050603070c1103010219050d0b010504060518061e0a030501051903260a0c0506010e1b0c0c1302070212150402060703 75
    0xc0001c000401921540c002c0d410003101941c0801802441142802a03e0034200e0081284001c078024be0001e00031070944c0e40c000200e8030b80e220005420a00191150b8050030b4840e0790b1900c0c0d00c1000d0042c14003170103040320a1861414000780c094036800c0c1080000b0495000180111600d540a40c10f07030320003c2454550349030004031940018131542c8103003c00782802e0f00d49480406954443d9082d2010f0707030059201c01789001248950a803407a458044640c0d40424200300301407188144d0111066102d1024058035200c460a540c09020f86105070000b0303014023000c20020300c4004103650320504894000701c01e141c100d0001da00c01c2c00c8240d50450490b50800c00001c0d914229680a506510340d14061406c0d22040d0740ca440c0e510b480300e8002d403101c0716200072541c3c65889a0313030414002d000480302801156a04405680480c44001011952280c03580c4d020440409601300460289541941e000c041d00c0d20700310004219550000281010740a084003081c174404042c050b070113480309100440e0b20044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 108413381 1250 108412131 108412141
    0x90b040611010e2103040f05030d020406030b030d02030a03020706090206030907030c06020f060f0603030702040906021909180b010c050f0703140a02011d04020409020c06011505030112020402031905 87
    0x59500580c0740314406602c0c014114042807404102145403071414209007550185400040c00f00d5000600b007612001c04044001c0b000800403c0144481d1204c24000343e115880c000006d0100c071248640030b8081e8209141150b0500d0303010080704d400c080e07503040050310b4a2690420342c0003040b1115000790814000030a00c65503c0340000c1c0c04044911502e8000482910f0340400c903100c614980f00009075511190108000610041e0aa0740c084000f400712070030701003207400180584205101c2610088d500250010501400040701e00c80401603003483c4410516009002c44c44556840d400310b0160340d2850403c4242e817056410201c81070300320040710248080b1304c08150701c070b11103803000312104100103c03000a8a4030218400b18801c0c4c0503141c6c0d000c0b4584134a045101c056a8006243d40700740d0030040070906070194030152000b14000c80003041c0720340c1041d0b03064072103041032000001071000c00d00c01006080c9140c803e242c3c0c0154159409601c0e40c9a00c0d0381072480c40d00e184d21000c20f0500b4001000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 108414631 1250 108413381 108413387
    0x807050d110d0501060215061005160f1b030b180304051003020d0b011d0f0111070602060103050706080408040b07020d0f06020d1401050d0b0c07050f1608031204030f090b0406 77
    0x102021016000c001503603a8445c1641d5480e0a524096107030090000081c94a00d0047c034500e1912046080c25403614254460304034201044082c11980c2c80f11203041641403115249a000904000c1a80b44001d9825501d5540307000000510368070020314440010700c002c0d4002d2042e203009002c0907058504480131444050701030b4020001f800300003032600100082c20342c070880d4040c480050406a00c0d0103595110140300065200340c00643c10710403490080c1c41405410001d82d0700038003503607024001d15419480c1c420b04282c0c0540c42242000a000148804a029442294101c61598922650b910858408102d24030303241c40d000b03840011102d08aa041c002d82d50020718070019000740c10050308000340483c04a10500780221a04a075044180b040040c030380703202003504950441d41040c2000300c40d959681c81e0605054040c4059040341074440c0794680c080300d0384c501400641c40a9420030074042e5220011100041000e4100146008025072190040c00c0c0640039248505000d5522a12280c000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 108415881 1250 108414631 108414637
    0xb0d03020f010c0306050f040e0106031e0317060105190c0807110906040c0206011503020c030d020a021c0c0b06122a031501030f080d0203010e04030306080d0f0807050d11 75
    0x840d07400d50804015072030b8a0f1082c03059000380c4030b0040030207803d00c26040900004013111400f04a03699038808002c0003140d00581042034480d44103c3c01c4640101c6464010201d02d1141e061141201180c010b010050fa044020f6541114844102401c40304105104a40340450b0b0080944041e8001420400384004406c52514141c07013074030981301c40d8440200f440704442c10301801400580168005000c29900c149801070100201d240241c10468041e01d44c3d820740c3e0154900716081a40016520161601030002256042d40c03c0308000002d8041500600882c0c403468000340351010100011b10f0543d2072130040c00390214250221124414840c414007052444001104070360140d000d95818280340029128084c058080082d154992940e0f684c24140015000200c8005c2014001d03080840e100c0d101540c020b0102401d00c0b50b480c101405c01038100d4950340c01803020740d0002c00d80402d4894000721014038030038a6140c104c011b5610310340300311214080c442c0d60500d500d08102c1c40b896489284009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 108417131 1250 108415881 108415903
    0x8030603031b03040905070206160513051c0c060801211416030c081b040f140f15060a02030a0f020304091806060b16080c0c060f0d0c0302040b0702040f0b0d0302 71
    0x802c11b0740c90300801030ba83d503101183c80001c60032981044d500980e204401803e5200007101ca0402216212000202001711030200c0c010071007030071035001d000e000303100300008002c003807600b0244010350525181000000000c2030103046400d00f11051020065416000d10b40030411000b641c071004002c0b080e0701d610000307600c0203580103940c1000204d134403000460140714030f0980341603004444080100340405481500384001c009660782c10440188806807022611441c20b07250b140c0503c0c0740c06080081004501d0f40d40d83e0141c101400100381c0c41d6000030490790340748241c0c103120015884040d4200d01c1c40c03145802046100741000b40580c92100183c1d0440c42c00c500c0b0700c5040c441031380c0b03505058002c0e0148a40424103075030319584c1c50010a0700c610052100303440c548151140c1c0c80032580445c029910240948070980c4000846242100c0c10784140001e0444504d0700351720300f41ca004401c100c1d6001e070040117849950365014400c240c000f07940c412656154054a242a075010f6810069283c0192400b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 108418381 1250 108417131 108417149
    0x30206060402130e0402130c11160b030f040f05010f0c080c120403080901020d0c0e040b0406030201020d0e0d06050406270506010905040809030f03130e0f0408030603031b0304 77
    0x10106400c0c1c50103000b40c0d2619140401c400032210318054424804020140003030385c200340c204450541051030340c0103121b0000942c2d1640b04800c100c41040c03074174121034440581030061940c4000d10100803410b08407a04821401c06c0010980c840d03003005880301c1d80f5100001c00540ca044407500103c0740503000042440c4081d100c580107551040040f1400784103210208000651007030019001a014098103900843c5240c001402c2401100e401c50440311160040c1001c1080e15014202070b1809004802000030142c034103201e40c51850340081c1d0b0380c40008807076009114005042804540b2000341881400d03420450034041d41c1824100000213090380300e00905003404640c0c0c21610034040c2e103084109540e0050091820380c3c40e02d00170b80d00400e400b80088030285c13010020a1440c0d6801c22440c007221303103904065552000c00080e40102c494499004030301610000742081000c16500e8201c40c0e110f900500400e80e40d64035000002e040d40310320300c1c0107000c00b41c51900140805100002400654102c54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 108419631 1250 108418381 108418393
    0x18160608090c09093c0c0f0105210c0913060f0e1012020a0e041b080f0601050d05011803031505010e061c0605220624050702010507060f02070302 64
    0x203402d101d0840c10880700b914540d40283c600e2141c0240312074064015145c0340c5020f122044003c00041a601e400d03481c0b0366015401800140d000d86468a00306040c01c600b401d1803441d10700b2041c003541c40b85484a52410303541240c00f000a41011400044520036000280700d00d518010800d18034000b0031690160726503e00013038102080100c11394080078003403094541485040342c03078142d8007a00100034020490b0003c81c0700c440001c1101c0610841c50180740320f0300341800310030402903180401c0c1d40a46e20054050f440070380c5102d264200031075100d0540300c09403800641030000d810700a024154240e408100c800603c01c000c1c0505515910054201d03c1c80801100003a0b6210011034a040784542c40590101b010030503640c2d114030501c9154400044400d020540700c0d5030314001049420b031040600401c0517584840680d4034024801d40000d002d948200400c00700403081108284a410404103081c044002620750030f6a004a0039030700110341c85682400b031030322689443c10203034206440480143c459a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 108420881 1250 108419631 108419653
    0x70c1707031e230d0f0203010308030f0c1623150a0e010c0e0f040b0405070f1803030504170709020a0c0210030c120b010c0602071a0115081816060809 66
    0x1480c3d01d8509402e03154101c02000030070000e445020360201396209110341d82c401d03083c800c109640c006180214042c0042c50b440c2d1900211710121712600034020320150038104048080b501c070304103000c4510b503000411840a200c3c80d0305820310711040c08440440700e100d1048088050300c80701002902c50300891500740010845026014280e841142c00390f40412040344000362541800703e040c100181009001283c2c0e2081c00021804035032096440c00c2c001244140176010b006e070400ba000e0900c0072b282c1c0080c7d5520b403450324010b045006602a00404454501096001ca042000380a0103010000e41c1107644807085a0040c007000d8007000202d00426119002c1c00c041030007442803a00018246d00c1c1c0702d21034004640c001c4004c22880007001d041c407500c0350102001c42d40380e01c090300920740f00d96000401120000c0c041426064141d20410742c0c04845200d00030740d10340c0076003001d030081680c1c003041100413101c00d101070600000c041042d2143c045801c0003d00e05d94040b1171903010703c241c2c0c010b03035492901c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 108422131 1250 108420881 108420887
    0x1a011106150d031704060b010e030a0c0902030405030706060b0904050106080f04060c0507051b040b0306090a06050a090b040b070e04060308090609032505030c09040209070c1707031e 80
    0x111108100091403101407009410319051142e10980b091800350018012840702c2d22003200305450988810341c0e17402c1100c2c0d455811403001101c00c84220000d113520301c601e03590301d2480070300d42c000c4202e03070354020012034200501002038031640e13680030f84140001510f602c420110740d04240780441c03103641804000503450b405000e45a018489840c107188041d0f4a98640c080030745403c040f034208021040195602007401804004e140451400303004081406400400054400c00601a0305c20340107042402460310340000c05078000c6a100700e0100306a664200401c0c014550000098141a440e201700000c00c1041c0180350302c10180c42d2100146540c0e001c00b80001c07554640801400d40f5401c0141c0310030b03458001c000e0a01c0e544000c04650f003070000c1182207410907a101600c0ca1181050050030302840c40d040c0440c003031101042d0348400c15494150001703200098044c0c9064180444a51594188481001341880d1407410b441016607540d42071a00508000508040d06059610f5280304041d2a04c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 108423381 1250 108422131 108422143
    0x10302010806360103051203130f02061c0902010207090506030c1908030408031c051003060b0a03020319030816020703030f090504140114011103040b0a0e041a0111 72
    0x90180d4455506640300310a0009006464862100318030b540c0c005150302c0201c4800c5924a540500c222481951440c03601c10315140d103c92094030740103410310400400c9260071903003c56035078100f4403441c59070500d800800c0084c4143c604000200780b01401c00264045e1540000c080f06100b03a08a07405940e45082e403200b11182640d2031903141e0418803071a12985411a4880c4a0b80200b00b0144443d82d41ca060552842d03205501c0402d05400c04140282c10686003403d0800407001004c050100c1d01e800070b02400e084650703000c010445550340b00180c90360b44807034403030101071640a0b04070390180d113001c60032122821058601318001200c0500140301e829420002c030f400420395800400ca964115501640c00000708403181c02040031104c00002d565580d07002d04500d10f040e402901509504106040850302625901c00d4144145103440c03051110000045a0072100c09a14003921010701580407a0031066102c412607000341868410528243d00e47c6c001c1e00d480717400340c0b82c841500c40305410301a1180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 108424631 1250 108423381 108423383
    0x301030b061e040b03010b091810020c060612010f051906122d0c12120f02070e100314010501050f0909150711031305040f02120a0b0604031703060114030103 69
    0x340081d42c42c491541800e030400070583c0300040020554505103804110410800c4a48412210880b5103000c8011000e1000083c0005503240075854187d0010050b80d40348800391404e4010f1540080d8581201c00170b50003012410390500d824482806c018000d0340740f0704a001e41d851201f6107407200010300341c25900d400d000c04a86c84081610b00044120300704120600c050300d400c2150703900c5614040040d22003401b610207000701c41e4400307c0702c1480d0f007080301c8410817181048051000b0f450496154580001d030180c116160910220250b684031214400031064591000702100944010190f01c0041034000301e0682d0000d40d5414002c80314001004880034082e250410140c0090892840702030400c28000c4e400025414401000d15440c0c00351461a8404807110040002e000c00074859860140104ae00004980c42e0a600f0000213403100e07210600064000703040203550706002003094603a42d042d80e008580041e5034000a205c84d698005c00c2e40d200f2542c072070000d2201011880b15400c07480a4034162 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 108425881 1250 108424631 108424669
    0x150917040317070c0f030807060b01170f0403050906070c0918020a0306020a0c021e030607020f030a1b05070b0304030305070815040e01110c010e0705310204090507050301030b06 78
    0x1449030040360342c41e07212103402c2d81c2e441c1007402e0100d0881e420113800e45c011485000001e507507130510b06058089503400416103040000441c501d020000c01c0402c000d403c101c00354009011a1a54601569244501e5072425023000010401d03905000ca50a041000c1715560042400142802442805041110b040080d40401410000c1c004240f40e0703409400008550700305250302c50401c0d0005480002d1506640c1010180e03103070749030150b080074056281c010b0400d000800398010440243d5072071380640c60110080000d10b89030840c400f89200040c240080d0804e09036401e0355118507c100c0700707500c1120300f0340c08a81001d0110383c00340d20500169100ba030751061880e1042901e0000c1001610300d02c421502150f40f502c100580d2040168000c2c01940080800010085040301c0c85505041c000e0703001502c9080d10240400400c6002c07140f80c00b4941803031010040c0300d40b60051040080c0140c1d0408045107141604200341070b40c0200085042c0c9010f000c00303140580e0b0f0748080081c0c803800c07450a480b203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 108427131 1250 108425881 108425903
    0x30703062105070f052107090501030b01031b03020303030c0702040b090112050d0206130f030e130608010c0203030603030307200709140c1e090f031009061410030308040804031509170403 82
    0x501b080e0000e8080341250600c082e1035415540308140c9003038501c00c1e007003a5501403205004104000a20020112100301801c020404170314540010380c136404010030030703410600001028000c660300c55100700103200006040440658560300b091104070596202214070b8401c40410f400603500000e1242d02c2108a4450000345a00b15a16940445c04031081281800381c0d01580b011150341310120104640d1584200250719440d1141441c2983c0803000004c007590010000d01c5180e8601104603170f13000344270307041002510340c0c01006c00c1c0b50040300c99030504880c0206840814036100c240c01c040403140c0c1240c0441001d44070194281c0c018410b045e0184000e00700700004205a041c500c000c0e1100c003100034085a510b0304400080ba082600130b42c03a525280c1d55401e442c0d0108402c0e44502d03030103c030300340c007080c00c0600c4c01c1c01058011a040d4000038091088038000107082005c0941110042c552201a110248804001d94400340c0804102201e00c0100c3e405040456028107081d941129009040019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 108428381 1250 108427131 108427159
    0xe0115120303021309020d09053c0307020306070201091109010510030506030118081201060c080a2304031406060909030d020304020a0503070308031506130b030703062105070f05 78
    0x1c000c1d4400030205440848210313000500b4111407014050300e41c401000031034414038070b00c1e1040c2071040b65105641d00c003500c5900d8181d0000c0d264032802c103c4560040c0c0c45e24141903583c2d43d0b49180145c0b030000354035100388010800005e5041d00306041c0c00d4030034002a415500783e2402c2140c022404d0250540064502c0070501c0e03110322031341086030402030150002a410a1001040041c1c1c28100c00581c3c0d01a000200640d5020f03040d08101d0041c441442d19a600040c07d540d405c90700c1c8102c2d080881000703220070030342c0d940060a100741c41200804545850340c540da41c0c40e2070500320380c800c80a03c200340a0080010346505054440c140700300f40b107001443c680114180200025000a0002d03a00101500404500d0b03403001c101820140d0b0048080c01e4580c03a020720003e1842e02c0f0383c6503241c02010b0921189402201c0c08410f041600e400325411a120b58030420120001c107020391098517442044040503407464410304190141d940030f44243c0da09280c4452401d4002141840390a40101b900d0350822 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 108429631 1250 108428381 108428387
    0x2030403120b0f03061611010204030c030b07020102040b07060506090f090606120c04050c041e0e0a02090105070f0303051501031503020d03210506041d0706050c0a0606090e01151203 80
    0x10b8000348000c011503403080207440882d03d014001c07075a42210341c04408000c08000d400c000b0710b0030f000540600079403409056a0b01c0c0703403241299200050412441c540401c440c41d0007901590301400303045014540f203011504000000c0c1c0015603000d07010f0003011000c51030300c0f140c082c4107911807003600006001070b0b03c641c010710210101c50410f42d04a80a82041c6080640e507a01a060141103401095a2500d0405040d60303510010403040d400800c3c000c9404108940b010304000e070380440d1b07102e80161100c111100507501c034804c56400602c84003404043e0020590198407681c016400401418031745000c0708010750440706103054008072442078078010001440e200c2102d0040ca442403606900004904040035410041c0c858102805515482040f0b4142400d125541e20906d0120090f0201a01d15003000c0e150001401540200000010618031000040110300706140e4003020800000313546a00c0d0600400300581c07400300ba942440d2010351303040b5546242c84241c03a202d44a20304071840d0b6580903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 108430881 1250 108429631 108429641
    0x6090f100504080a08040302010201141b0a030b0402160c140306040609020612240a0605090409030306170102030406060509010f0603051e0403050a0809010203010605181807120f0203040312 83
    0x1420070908220100e8001d00c10b00c5000461840307005c202c4d03100ca04500c0060700750303010820204115600e4004010742c01a004441041175481212403690740c80d0000411806481e02c0850540c00030b0000900404240c01c200c1d01c4030419010f03410503a9000e440f0b00c0300380412802e4030003caa141d80200e0100303010450703551000000f980b00801d140d291251081c4416290134045441d076040743d450700042d00a8000004521446440c100c1c0c0c4600b20b20305140020340340c1d0080d0746855001d41d80e5607140c101014042d6211744050003000c14030016148120000741d01075441154200c8849080500c0016039040819006068070914080703e010030f030803c2812001400001e08602203d00d4074030321100e000040b1000c06005c1c0e8000e59a4035030fa1301c4201703400741c0400006410742e002a881000100701495120041d140d82041d4601da10b049054071400143d088990305040c1418401d014090144071604500303041c01c001801d0350f060102e400c0c1c0c60140030407030004071000750200b00311680a14501d50b4617400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 108432131 1250 108430881 108430909
    0x308030603030d050c0301090b0f0d2603090d020c19121707080405030606090402031c02100c0807090f0e0403080a150303031d01050910020708040902130302010e06090f 74
    0x8030b9081807242d0501100b82c40e0292510014400000018400c0b4030303290241100745501500c0345020794000002040c646401c04401414400580181d0746800985200861404a04110042d10b0b070606c07286094039814140c2010000d4401d500d07081c50103081601142801440d00d09985005c0f91512120201154007a00d0460b03000840a05108070781c040340d00905403042c0110a01d41d121410f1105044c234110b0044e180921824801e03040000603a800100f000124400e0402103000da0039110050b031030000e1400b144030850f03060040c008012a804680f861140b02c0300d030b40f0405029520960022541c4a0b07000300c0042c01000d030000380c0444e01403241213421101a80e00028661241403000c520880d1a8008400180c0c03100802c0c01070721a00c80381001c003414440000c11182c107100400c1d0340d07a4401081044042500440c0c240300340320f659000c0d140282110f007000d40d61007142e44c1d4003440384d01882c0001c9003c103101000d8210f46041943c10344659020151041d51a05204401c1050990b07400301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 108433381 1250 108432131 108432133
    0x13241d0903040b160c05041b0f111c1b0503161e0302070603060f0e040b040f021c05060f0106120b0406081b040b031507050703023a0801050a0308030603 67
    0x1c0018078503c003034010440704540c1407012008804d1032074000918080c0b5032015114904107910120044407103107607140f100805041040d4182c11200041e60511015454441103002c0c4c014444c440d99411031040310300325056940d074200c400c00e81441201c825141400503295900612070075120390103240840d1551802214180c03001304114440c0f004510401d00110010f81140c07a003040040d40502401001c6c0040b030fa20b807811182881503003640a0300090000c0d03d100483c601241c2803020303040b403400200c3c0c0c02901240c003c1c01c8000e540c1b13240c2034041c44110b030148101c030002207148a020314094143c039556030710020144150f44074800a4160440c881754001c3d95100002440c40d02004a0b556841c0700f208103034050135164080204851580203c28000d400c96901500783e10312502103280e001c502d80c02d1080d1a19003509040f07261000000e80300ca402c407032269103412a9102c0415010280c9004081e0140182032a001110a1502071040c190808505082440050780c014040c550001d0090 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 108434631 1250 108433381 108433387
    0xf06010903120e04111e070c09020310170d140705150108010f15030809060d020d06060c0506130c05010c11040510061404051c02030c13241d0903 64
    0x7803522502c4905001000003c150546804412420503014840355a251030580070f081424208500a000155100701c1522200001700c0d003040000030b4042c2c0c000b030009507404544a1078248031401c9903031380ca030140490550b460b1411038102000020301c8a000103640d81d4689034a0800c280d40c40b0301d43c100510440c0c90f8000c0072584018030f100703407112500034132040d0000b0800148100c080d404850b40100c21b90031042e20b07103038280701143e08002120341454059811680d00d00d2030210120013401400f903140001801c14200045040d0301481660803240240162240d545604480301d80c004072110004261070205001001190b0040d040c904040b4004e842c08601c40301c0a0000031304907502101c0710f0b45c41c44400c080c20b00080b0392040344658540030040300030b440d0a0500300040c83c921001140d0520280305400103c04540b82406000710714140030345100e0048442203a4440946004c9040c0d00e0300d1992210134502c43c8010005010480d6200c40c0d11030341c600d102c0010610845001044044244410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 108435881 1250 108434631 108434633
    0x90203161b0b090601051003021201050f030a06060303080403080c07020117070c050106031a0702070e01031101030e1e06070311160201020712080c0111093a0501020702150c060f06010903 82
    0x1140c03840303104000b2080900705540c10a410020000d281d240306a04040c410f10024ad100380c600c100c1c0a064860072140131f01c0c03103600280081e280c8140940001c003103d003001400810550001219800740c2e1098480290560314081e20b41020300030407130040d0014072900c4400c1003803010b64003031a801071141d15101204004a440c0c2d142582c9080d44101d882d616044076800c04119014801d0303800866501c06060320b40d280031500c00d88000c06010140440a4503001000c99030b000e50320500c0001f1511080d81c2e02942c0560b17800403088a401c5045d02036000300c0c80040c403a2446403040d0300f0100b901c02007203802e03c9400d200b40c018410002d5822419881100d01c0412008803143e6400444c500c02d0b211250303181034441070142540d0040400044507034051103461410781c0c3d40588180002000070846450007a00b81c00c028920540d5600340c10500007030b001640034400190000c042c528000e03207140e400c0030300f0720b002840140b15001040604da008200800c9c0105013581020b0f030040814585118202d4903 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 108437131 1250 108435881 108435893
    0x402040503120d0e0606030d08070306150c0203010c0503070c08070804080304030f140a12030507121b020613020d020d0302010908031006020c0306060a06030b0103020c07090203010f090203161b 85
    0x350114a8001c1e45000c81c140c0103041c0303e406220611403624025282c0780c1060008a6500c101d00c110350005c0c0003950b03001902042c0300c0e91046d070080c907005035a404c00f807e02c0c1101900d80283c940050f4029401c060700d00d10403074024000c680c003a0003680d03101600030119032901d0360150842d9000700e611290400000880c03440030000303040036500034482c4140e824084e01d444c01c0249042d11010250b42c001c88405000b2030030558411500c43c1c0c80781004180c84c2d5980c00101d82c4107040c2d030204102580703006c021071818105090300701d145400d02d4084544035101c15a1408031411a070030020740c441003904101c0010b05041444000882c07090001280f601c0306035541c003805030011a441e0342c1070100003508021896040000c0504024180c01a141d9070500b013001c1a402c802c280240c0003490744030709100245901c01c0e4110f4003c52500810f80744401e0b00ea807648006580288a190004c0c800060003141a0345540f00301c9005854440700a1051a4840300035034000c2440241c40030000b080003100804248 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 108438381 1250 108437131 108437143
    0x10f1407050c0a090603020114031f150207090b060d09050a0b040f0c0905090a020132041a030c07030c02061c091e03050919031b0609091a010309020402040503 70
    0x11181000d40300100c0300c0c1083c01154000c0780d02c4008120704003038041001d42d801c149034503c0d4030f1165150b07956a40d110030740c001c040d02e003401410f00c0c2c0e82d10007140021016009400c86050444a074241d0f01d00310307904c50101e010368807030b500b440354840c504000c000b045492552044808622440988500e031140b070300e8148084204482c10740e034044200c2c18903070410007050311540251a10640800890806403807247e9269000400281442014425a09155200320690900312022281440310b0701d04011803420542080c400c81c814600c154207c092000d0040040e648119401501941401d080e920100c404612145040e82c00c42010000c1b05d41104000301c5c82e040601c001c00002c1035052a51400c0c030700c512404404010465151807a1600095100080f00c085010447d4540d85041800d1012001060a64001040f9440c0c0c1090010101d40c440300103c02c9411949807000c0059907022241c050700c4890b02c4c10a80e0443c2c8100d080705960003980204800c5001610041c1081d48660100303103012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 108439631 1250 108438381 108438383
    0x6140a0309140d0906030509060a0e1c0e031006050d082101090e1c05181c1b0819080a03060b0d0605040b0411070206030a09020315060316080705010f1407 68
    0x3400c4481c24001140d08961100c0c0117115900d4200b005207403074001c807521580d0151500301140e0f110845145c050300d080ac0050302c022401d1a081000320003400d00a411942840f201d14041d015444180e403514541d803258000f25580640744120001c615a00c140440e0312004003844003591000304c422000980a044078041c05492000003040020700c00143d24012035240c128018883c800d81c00c0c0f10269002050720804103015040b02c1000d1031203400074042c3c200481400032840a00b49105045c40440b0f241c0340001c1c0201305501c40340c9500c82a03101c0e03ca503000c819003000000c5c4c000c58240001e60700c0008108800311840d00180594441104800e180d010103580c4c00ea00742c58610a0007246814421040f01304000c0394100722604815900307132000c1c002c0040183c46405d000c40011003064a41d0442d014165006055904002540e84c0d140b5000d00143d84441c042d10548a840e00c25111151541c81540c04660040400c1ca00d030200440e900c1d080d20341d15404008a482d13100c1c2c0220300d1403001c0c2c1281 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 108440881 1250 108439631 108439633
    0xf061b050309010e07140609030106030203060a0219080c250c0e0717040507090506060d02070f06050609041110090509010306051506040f09090201030b0904050a0b0c0406140a030914 80
    0x1030b042a42003903095614003039060303c06402c00f0038100421454404402c416900a0300c044c0d8590b0302c000700107401001e441d0700103501809031004011800c001e69004020706800c0d4546070300140306040742100c030340d50f003101c64035a8400c003080340002d107039080680080024042e0745a020002d03c2641c680b2601c024039408450074040c0e1106114960350421200742d10440943c241d03521928041d1580e030b80e47d0203148610f8040c19610400304d4400c5d15403a044a0144003074a2040d07545010f07526044840d80100807094415a141401007640c070f141504c45580915000228000203401000c10084c80744c181100030801c3c4801d01c1c80014103a1108294a0300a41c01100009002d190580450140000307100f2000c1c4982d404001c10300c01c0110601f4200241c80300454001940d000c40d200503001820790b8904258801d090000308410008000740481070540f144c840384140751220781b1050800c0c05103010320b07000700303c0d00030720201405c4509004e001400400d140200b0b10b03000c0c607220305484000c0c0b00d03104001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 108442131 1250 108440881 108440887
    0x60506040509010c05070b0405280b07030902090415021b0123010302010818010b0d05160e01051309060b06040e01030b060102070b0405010e0409021005040e01050a060206040f061b05 80
    0x452034103214403a0300048810081c0048841100e0040851086034001001c0116020104091010030080d03205504e1900c84403034014902c01d01300c0044c00d2600b001c201d40e04030900d40002c101b503119001d11075401d940034000c1c540d50b0320303280d4500c260004020688580c9580c01d100c5800310303c4200e6152444071a0314000043c03e100001e1071124000d202d0202f1086d9841c0700c600400c0103036800360481c1c0d4010501f01d80c3c02013010b00480b00f54090800c0c007103041e0b030000c2e2448110702809804280081c07000640c210140c2803a03510842070130455424410b846e403108880305000d06400e142e4002c090380768400c5d9000908082c054001840c41d030071030381180880c28881401802042840f141c100c0e005542400103084c0d00380382c0791048000b03210300e000c1c40303041020002a140311520341d500034920156004001074589a08190700401a4116205521030880c0310070002660703041c0f0310290429144244e000e840103542d01e46541001d0407840e202254010b58407205200406c48a00d0270384181000e0380e54040d6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 108443381 1250 108442131 108442141
    0x3030f130506121f0b12090610030302030a0e061e030402090a05040804050409240c0207050d021305061305070c02130510050906040603060e03071205040605090415050d0605 76
    0x51200300a40010b4080c0d032003000109181d248840d101680700050036803031208a1049a20f480c03202006920428007043c0110300850011400e110061041e0703c11002c0342c80716070300c514207260008038a100c080c0141c2c10804c800c245040c803031152500b00d40c0015204901e0004d04004000740d2100c81c13400031413910341c007106100452801178203141c1c1000c0381d41024030260504e070b1210103185c400d511505200c1c550312808041000050403281e1b184d2111915010704140345610514050301200704410018050144042000e241c207032510405a500904444510030040d00e101c0020080904407940c04036080200703041603185400707002e00c14111a030700c030321140c640351052040765030302d5070030741d541850900041000c0110044800d0046500c2112801e215888040c0030600400b12030308003500981c18921081d100c108000010500c40d03108145480d003c50010400302c90600450064000003002000460180d1070300c1c0c2c2140b840d100e510380180c10f04035075400c000b480c402e0301c4a208481d0503854100b004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 108444631 1250 108443381 108443407
    0x100e0303160c0609032a030b0406090203190b040803090f03070606030308060105160b041403040305010b10031b050315090a0b0f040507020c0d213506100e03030f 71
    0xc4001d100f81d0810400e5641036075070b00150000c0d0f080240c903121168550950004500140090003150801c500800d141880c0c01d10a02030f001709032081e07002e403140f100189410010303142005809034210007030320b0403070300c8a82da850040d0f40080c04403c801e214007042104011000c0c401032000b1442040c0010b8500c0c59444c019005102c010a02c50520000348950402d40c48484043c02059034403c9080310395965501d442c40c5140c0d51072410a0305448041000f10801c00c05610041178103034111040c1100000b410002c0b030568203a40c5640010600008003c079a59004a01558101c01d07108103010b100e83c44000030135000741c012200c03e042d1030380b5400b5050203410302d00500300880c0016141400107292070100070350f4504114961390301424035001e11b031081c00011212106c0b980348a00104607001500c440041c64214000f0541a0b000d0140f00ba5203580a41a59003a01c044c02020810999503182c0041114459a034540c80f01030004145450816560a0000307000304580413903040d8a03900c588840b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 108445881 1250 108444631 108444653
    0x10602060417090604030f0c030602030924060f121005250905091b0f0403030f0f02060105030c060309030714030406020f070803070602160c0e0f061e100e030316 71
    0xc0700c0988041110700102d03183c1d130341180c046e2074100e03002d40c04081003850042c41416542c1d2014044034030101c2401440d0801140141001009007a012582c0415075809900c4d50419624150b00c6055104c0e40802803c0c070036500c1c002c0000c0c25050721420f00a01940d2000c3d0340040b62404501c1b031525070324100b8001200301d440c680c0b10003443c2142401d820a00030881501001d48009100741c07105801800301c0d00840c04880c4003c0442e0f02c019229075903860040c1414441c07015410200f51b084241000b06071001551604840340180100104403000040c803099074400340403045d032400100001c501050b42282e00c41d0882060130f00441c0e4451034401300038246526040c1c1421031b50003100080021110020540300c00d150840c00041e5a142c6868403040701100d42800280007080ea0140090703441e82d0004070500c42c070710481908600d82c2e10701d000c202850300982201900114418018080c42c01d004211000344900c0782000c0f40c40200c210b0001c2d20b0341d00007074030b50420038600c0411441000b50304140c0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 108447131 1250 108445881 108445913
    0x4170d050106090b07020a23060c0102040e0105090f010b1c020a081602030f0909131202011e110703030902030316111509091602010915020306030c010e060d0f060e0106020604 77
    0x11303403420145c0b1540051041200c2e481005452240c00301003942084041c035242c41039200080909644040881949010b90418401c4494102200e4000102c42c1001e0001d1840b40c416901840096800d1442c0b6204903000501c0f4030760302d080120300b0f41e5281c050030310040642d0196a00c600c0c0403890001e00c440042c07201155954115001404003c800c2049032003035404c6604c00702d414130070b140c1c0e500c001299502b003118400340103100d0200c501b04010b501076000ca01282d00c00403625120890401e501d00a943c0c04a4002200310010859200072038030a034451461144028140c0740742120038131103e020308800da0307402d0340c0001402201c200c141c0b4280540c9009100b40e07424140c1459241000102c10640040030444400701d1002101c3e0420f2007940f0400c181395015188080500c12018004004e4104071803840c0603200780c040341c0e0300640c0960241070003d8001003540e803070020481518005040400b41001015480d1240451703045c0031611118003a08055006150700d14050800c0c030611141c0c030302 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 108448381 1250 108447131 108447149
    0x603190e030c030403020418050102040b0c0607020309100305060406051207080f0c03070e070903051006080c010e100c0204090b0411011e0c02040c021f02090307062604170d05010609 80
    0x2c82c074038003140881030710100c0303030116400602d82e102c86484c0d14201d0200c0c40018125440050301141400140024003410811841220f02503501c500c8166920302c40d0651055100034000b0204000b01d20940007298081801307003000ca400e039030315400300d643c400a2105071403441c1c21400707052104d601c04104000c50300c00340f503000301050240c1901090715103880e40100d6098440060010f060207000304049001140e03c4011210104042001000244400c0c0039840f91409400b9541c4950740c030031040585000002010380b07110313618400054602142c1e60345c040341c2040d120344d408004528400d01191165005801240059203404001811180a41c080c0c021240c410300100b120359034000c44002c0303880c2d41902e000800e0301c6405000ea103000c8890108500008020510000b18445c039005001591825003c6484064547c1c01c1a5001624591140840c0c51083c040d5030b40700301071032010340c1c00030b00945500b04844d01d18002d04da1564043d600201c1d40c2502e4000412025920403807500040c19220 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 108449631 1250 108448381 108448387
    0x9031005010510140c03040602070e06090403020c041d0f0105060405010e0c1204020d120f08011401050f090406030804030f0507090203010305190512210a091a0c07020603190e03 78
    0x2c80081c104450940d40c1c08204078407690007906401e0030108442950100900700d03510390f5615003001707641e40f08902a103048011048042500307801d0800b4003500450707140e000b8080b181049400e000060000b520311340d8071a1040c000540e03110b00e00340900c2d644c18007040004141c2d440d000050000750359060b404001820410740420910710220400e84860702c50014041d8039a03241d03800003481c940828040503140c46a580901c0d1103440e04200c006103560250344500c10107a9071078100c0300180030403080b22804210104080c2206181c9a0020101e41303500400c001401c0791a6217030b5070702e65082500f0859810300140c4c076010074488100400402085451030a628560542e81c559803100116030080030512101c01c14002000401c0c42899014419041c207140c88117005141c0b2412030210310803c040c01030701c1001103240d29045004440401d07420941045d08040c4022039560500b5000f091600c062400303000140043e80d03070030020340c0201c0e20318202c00000724801d6003400444101c410300c02e4880c0d00070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 108450881 1250 108449631 108449639
    0x307180909150b060901050a0c0309210605061c0f0f0b07050703021504020f06090a030213020a111b060304150912030b09071d0a05060304030302040312020d0c0611160303020903100501 81
    0x300048908e001500d01c0d0050800000c3d05d019100c154194105249410003090110b010509008020b071806001e40300c1404540c89500a0101040005030420760b4140031520ad600401c400c0749081035034610901c100c200d4280070703440c0c40e8014041038a074071380001c4c00065000141070303040220303054070f680d030031001034403414554009170f508013101d078019004034000314000b102692042485801545c000d0031080341d2000b80300302c000c0254482c00c007080c046000441d07461801c0c680043c0d124100e83c0d09040410450803449c0c2040010b800c01042102d60302c0c0115028402258117001c0c0c1d24003a0310841451008010040b8054140da044d18652030003003070b400c401c103d000da078850001d041c5081c0d258074840f14102600041364140fa02c2d0341200ba08840000240f000705507260707005004983c01341e00085000c07560303510308903165110f04140e00001070040400c0f01c00300703101b5485254140e40d09009070b8684010f641c031a03c0d500000c09402e8011139408590910182001d2203805600549a42c04022641c18 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 108452131 1250 108450881 108450887
    0x20d0806011d030f0304050a080304080a03111011030a060617010611010f09080304020f092401090312031a010201060518130804030c140909030307180909150b060901 73
    0x18a00c0d8104603448601d00201111950061002c0e50040c013600c200c1801c00031401e84c2c0781c0c050b1103818002e00c0343d44400030700d141e004030569090700c1000f00600032901090b03c2c110f41c41c0d00c1b01c1c3d45140f13076401401d4412403002d15034400c1c21007440c80c1c9070100d42c507031800d40c0340c200482c1c400f64482414010f00c58420107000006918142c15580700c0e040144c0c202130414503250041c0141903455020380e00c0c100c5460240040c4074080e51003240708640c0c030140032500740c003841115002a00d0b5686901c240001081d03021013092031031000d141301850a032300d06030355903198400b520241210440c040395a80441c001c080110f43c41c101190002030000b4403049141c0710104c1d0500345084104ca980b44c81c25030111300d2a1300c4099219442d5600040b06944903503d90500d4107080c0c14078800c59074994444480c001c124241003011510a04041c8042c40c1075a49420044c0d41040c0c0b076101c500f1107141887e00114216120303105648102c0e028916070703504109448080c104540b58280740074810042030101056680e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 108453237 1106 108452131 108452147
    0x304081902100c081c14010b0304060b090601050904020d0204151709010501030308010b030402300105011403030f0a05070203030409241a0c0a0203010501080708060106020d 76
    0x510905440e10700807000014503280040c0101704145041d00050030422000360b1010a034034800100700c1c282610b00760484031b19000c010080c0000d02519100b480351007501981c1c480110308228001a00034000d0a96003403040f600000c1d6011a141745170140d5000300940d80e880e0200728040b800203011030001c80300580c044840d0300d00081c0ca50710b05001d4141201d403d0b858646042e42800c5017074009510041050b42c202110206482d0500d03868220706043d15105001c01180d40c2c0107860903825200183e1201001d49032240882540d59008022104003080035000640c0da05030141058489000d40c0070080d40c1404040380000e0100150b80100240508101c0f8003100c50081104500c0c12500501448454031500300031841d801c1c01e6240100031081405044034080b00890b0f000030309442007600055030f90b0308a000308004048081010320b024005500281141103904080100b21103 = true := by decide +kernel

theorem cover : BRFrame.Cov 108273381 108453237 := by
  have h0 := BRFrame.cov_init 108273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 108273381 ≤ n) (h2 : n < 108453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
