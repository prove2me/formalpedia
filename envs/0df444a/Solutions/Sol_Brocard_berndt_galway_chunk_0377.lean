-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0377
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:30:07.542959+00:00
-- url     : https://prove2.me/submissions/c51a82b3-e2c4-450c-b080-03c49393237c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 67625901 ≤ n < 67805757 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 67627151 1250 67625901 67625923
    0x80a060c02190b150306070c021c14010203010806011205100b0406090e0a0b070201140604051806040501061e03080702040b0a1206061a090306130203010f1815020c030409020310090e 80
    0xa030060104d40c1000502c85204800e035460340413815489800700010030700703244c02c00b0b0012000107031400c00003010020030a901181160000d0303100d5040c401503600b0500c0503004126407205c84448030740442d030001020202c10040c0d8500003680d0905c000450060a034607000944c840d070610706003402288002414884250081340c20350010746801004078240d915a083e140802450340c0d02151240c0740640c330164000c0c0c2420000002108407211403030800304115001d440d103075541c100411440720040c807046c43c017a8041040c0321181d4150303030703d60015018080029004540e240500b9130f150710f4042ca000064080e100941d0b0f20381388a403610102400d60b60250040c031a501d1403114118440d44400e45080900050140000b40c0d03402d6000d00540c1403100040c3d81c9907403146150b91019502d84203210803144240009001e000300c5007880b25003611212031143d01144108803001010a01100f56015900040805a41c80c1c032010002c29240200303030000720b00145040700d24100940300141b880700c54 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 67628401 1250 67627151 67627171
    0xf060b0a0809070f0311122505090f01210213060f0509060609150f12010302100f140a050909010b0702011812061e1a01030f06080a060c02190b 63
    0x42c1d4440c9001a16007079a44201c01d00c6502540381800006c0c4803191040708070742e015050407440c4001c0003800b40344c20340e040003030003910101e21050542c540701252a54090182079441e1201c0e42068608034062640c148642e0513502403060344200403d441101d2081c0084d00180409034042043c81d14000070112807050301200402c40e0300000780e40c2025041c852007108010f11540c1440e85010074008a51100f020080c00b01b002000035000c40d2164401030511600d0b020301c00d50742d960640c030600c007103045402558018030403984211101c0617442404089401901d929607034480818440a440a02418094a603c0031104001181c680d01013000342c080c86000740da41c1660005500180103e0a005001d40c9011200062941d40440c046811402c0b105600d110104007148881c640714003210b00d1030120420740381140c0a00c040940c0d00d8040c030f80504861050400a01e407815007001d550fa62452030052080c0d485003140d4100600a2190b00000d1402c04840c1d031402041c0d1800c3c029003c01141ca50b880 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 67629651 1250 67628401 67628417
    0x30f0e01030b1302030403121103060a0618090e0c040501080f12040e0403050a09050d060507030c020c030a02360702010c0302030106050a0305090709020c01021b16090903030f060b0a 80
    0x903507120b406401c1109202900b0104400d10700e54103d80a90f0000b40160280708407800091000e86a520070310000141c91010700c1e0305c9080041c00c0004501055100a0401c0480c500c000440311407880c0f00002c58480400014202510810302c6052143d080038040d4407604d4240005503400c0d020a200c1c1c0c401ca8110152041000325010904c241c1c05140101d2500c02c880c0e000050020340650f000b4112800e123424100b08440c0e9600004601d441000b00031500242c40368144035401341c0502603262103c207240090410814440c0c0429070303403154007401074440d200c0714400b40341134100503983c0d07806090140c402c09122100e807500c4901d04a02035420000540c6448040c0c20000e100b4429079058801666401d8900030040c20118054600500f46c030000e4041c4580000d01c5031114030041440800c440300142c1c5400c4440380c1405038400c80304c0c01e801260411001581960620300182042d07482c042c45c000780700c800300c2c14210028041210075807031541c17820380f0120b49104040050000444155613110b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 67630901 1250 67629651 67629677
    0x723071101080709090c0c02040903030b031203010506070305030615040e0919030801060f030608060a061d010e0105011209021804060516050901050d1107030915050403020f0904050a020a03030f 85
    0x41d080e400f19090800a60b441005001c001c0d01600b00403450a0301e85805612038402d0b4002808a6040740b00460200c0d9940d000e035001820305120103500b200800c0526421580740c000032034480e125074400242002000400203405583d0240c0c1c07610490041c68481c2d4a65449410244034802c09482142003446040c4000d051380c0301801100301c81951503a6800d400340d18018050711155100b01007901407545900d0042821502084014882d10701e980c0c0c0400c60503d841402c4071408045c0c0011007803410f80c1001401071040e00e000443c11900e080c42e06a11a02014490900408202d20000d40c00038044629100d24110050b840340102c0c065802000182c03544806804400c0340c412000e0040b0742d082c0316481d42503000d6805031003808441d10b40415070001e880301c0c1c80025400680102d0104000e00428010030b2074520085002d80303071500b440d0345094251707000190304085825130284a80c80c0c010005003000f0050000e40e400079400f83c440c000b1a916450040e20344900d50501c0300003d408040d401e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 67632151 1250 67630901 67630907
    0x20d0e030703091403071703190504140102010212040308180d0c030815010c350c07050303070f0b0411100c020126040b0a1e0b0406090507050306090723071101 70
    0x5208010050013010520300d01840d818881054404844031f5000c103000c8a45000418121040d1380b00b40ca80c2c9141d038807402c00802c0418000c203036030b5442c11a07206115010056428010b0b1070742281e01030806020a0b600d111128080307526031a010f05081c0542c1c09010395440d00080084286d44c4039445103016a40e5100c00e50307140f045150440341c00101c141d5014800b2804c1001d2270104c0c0380311424030f841e400b54140c5104210101d0103c03c80c030740000014841d11000000d0101e54051700003100918608181c46d1100500c00040d01800751608500c1750104040026028a0312071122010304014803c240409002c4d08005c0f42000030303404121480491400c0d403000d24101f41d03440c0c1040741240f070f150301c0700c1c5c079000d200390002003074215040e03a1402801500510400756070082d100000b408550142a0814081610115401048441c0c14001030000207a0010305403548000d05440510031030b0740f03596003109d100110585688221346440141050080310b02c00400c0e00c64002c1d806a5002c114204c011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 67633401 1250 67632151 67632179
    0xf010902090618030f0d081801020a0816171302040b090910180203070e01030c15050319060f0b0909090a03140703170a020c0129010e0301020d0e03070309 68
    0x2060b402802042914001c40324064070591000700602141c4114a01800b00c52404a5459131100841c407403408114000c4400c50f03443c114134403a10021340c14400d10a8002c0e00d0382c00041d001480d060b803120b0351070b003005116240c501c03006420b29176000d600b42003018896808031040201640035a04002803900305060501c0315030b000f0f0815030020305103010000c040c0b030001d16402103201c40b081c0c85d015401c005130340c007040940040c2103402d108900c0381d45140b4011084043c96442410344800750181d007180160031406580e402100c09840c009002c015022800c024440d5030400c0341004041500801d0308070740c2c5409410f084005a580500b01c2e15085a11503540c0d00c5c3c0703440203000503608180c0310240400c06018041143c070904080c0c03c028030071004020030840484000c1d4040c2e501148010b240607090048003d9280300b004500480d0b040c0250802c40a19858401810300c1b800b03200c9080c030b43c0c500b54111002160040130411007204000364503a100d1744031100584c001100a00e010412051075080 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 67634651 1250 67633401 67633417
    0x70b0406030903050405030d02010e06180c01050f210a0c0806030604030c02180f0411010e090106030c02070b030907060806150313020a03060905010608070b0a020601090b03120a080f010902 83
    0x10241000c0c58448114094000b03079004400304035060000080c40d0f2000c100702c070410030f01500040740241803881001d2400c103000b8078101c805902480064503980000c95031618428081c82c00c0d956030000b441c0c0c0524144a0503080e40c001c101401e40220307142040f1308181d030268429000601050301c40200072140751000b500e6580d8540c0001000c81d0000380141a070040061010f000f003c503c02c0a1004051114000c079804078410201d1401c00007080406100c0900d031701e4090a1501d80c428030f032004140690b205001d20303000d06580e1808080818005c01600b00200000342e142c9590745040c1110300d032105120301c66100482c43c7d48000c1415450803000c600d801d0180e103004581141c0c0c950824542807107030380e1810303a00142c00c3c81000c408200c0701e00441d0803440c090340c00072034810f00d040c441070315103a4980e00c5140c0700e50042c000e00b001d4a41c046107040c1160f20200010580c403000c9000241042c2a544000e2aa1440003c2c0980c0310780d00010810b1158103040740030300c056a640c107034001c02c1e845011b0b2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 67635901 1250 67634651 67634669
    0x3031b151802030a050d0905040207050a1205090a06050d05010f0b0f2101060e030c03120a0c170415030507030507051605070b04090902120d0c1e050303040303060602060907 76
    0x502140c004156031003108481c1d0002072010681000760007090070080e50040942c0d0a0300484100800385811400c450300402d0151011440c1c03030450389405884901d0704c000182149590302042e5000d80c40390081d110550b000800c50f10b015550791401400781e1f03000021400c07030a400c1c00f000240000461118001315000f000f00700d49080440310b034510b103503804880324242c0c1e040b0035054092200030058890b8043c004a851b01c0c00c006103240d042510f8840b410350810b100fa8440039540440e185004180d90400c2d1181c1449a13a84030b982c540605100c5051022801e00e480c0854009402c402e0707030f41c0e0921041c8154804100c2611124002c4080e903004640140100301c081180c100031100070b03a81c00e8496030081060303e102540310715420348c655100da4000d021f40758490301288150b103407080c445451084040000c00c1700740c0c60a80d020704800e2403034002804412080900782a81002120800c01c400d92042c10349980303240c0b91802400402d03450003800011310690f40001d2190310002103403020764003004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 67637151 1250 67635901 67635923
    0x5011104061b030504091103191a0105070c03080703020607090f05061207030b0d0501020a020c0102070e0c03070504080f100b0607020d11010e0a030609030e150702010c020607080d0603031b 83
    0x494039041d5206000b00450804c0403c100000700510607100c1ca00021802000542e620304040319800c401b04110700c169500c0e98a8690320b41c008854192100c01444e00a007030060f124141800c06046100c0144d002410707000000a0080826030b0104035503101340d034a82c54601505454400c105401503003801910f03040701040002c070301c0701c035000700d149135100040d4500418101c1c042d0300894840202884211020303034020a014001c240c0601c003034841890284010141d10749800c0402c000880c2c0903000501d1141d0001c0400c4003544280c04403000b40450a040740d030441c40f0014116a5140103100c4121850710301442801540743c045c2c11101c52a400030840030084415803112201c07810001c841a05004403946c200c0b40548504840100950061100042102c00d07424042c1c2240c4107582043d10608020002702a0024180e0640700c540b5028609134108600f60b1010550601c41e222000d40910404039101c40c460105820041c19a88030380d4070042540c040030244004948040c03c0184401c10003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 67638401 1250 67637151 67637177
    0x103020d021318020111010213050f0a1508010806010b0f070204051f030302060f0906010b12060609060706020d0e011802220203010b1210120b040f02030f0a0501110406 74
    0x40388508803a40001d000030144035140c64a541150540710400200f0803000c0c02980c25507800504544400203182d000391f14000550180f881009450b01502e0312820844045460540755050300c074000d025040c807000181d91a0203005441c90100344585901172013500000318220903110150780de68505403203202d0424116608000107000010007580f214405c980917140c4506154451500440c06034014000a0505a00b00c0180180080004403164010001007003a411180c007101d8404600c12403c0d02991112000510184a114001c50388940e01090110505c1000d50052030011b110310000c222703203841442c03c07600361906121203161004e070255182c80503007850540280d070543c0801c400030301440364040f48000ca8000380c0184036031340004503004c05d00000c418512500160801c22510760546041444403101820110040a99001102041c10807000c0000352800301c0c5d0040a441c03a481c02000110307903502c4485000d4400d5801c08030848040b10b01041102c0558000d50f403881801001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 67639651 1250 67638401 67638409
    0x8071b17030a0c060e010b03030a050706050a1b12060519060201140402090c0c0c04020c030403030906021c0509010201090c18060902070503070b07050c100911041509050a14010e04060e06010e010302 87
    0x610505d100645d5240d10100c00c10366800e02c0101005078168641c0d64903080903050200440b80020409441a46006820b81406520540c00c0c0c00001840ca403401440c0c529115907009011140c0c4540d407c0291008459024508058a14240c81e000d03802000303001d60b01c0010340c003c030f8015034001c0d411001d5240420340b240d9010000b002291030080031200c5524203c00460200d0384000c20003410754001003014010190f1141a4900904880c40240b0b10032594140f800401003a4820030b10503c140080e492501e64001e4110300ca101d500b240d1440315440c1c1c3c41d4040c1075a003111400030400030349405c00106050040d442a114020380100045044c0320b4142e03650888010050041418000140312015071a0000c014282d400345046001003008080751410040d02d2080e0041203108505014242d40048a0107542e081101d01c000c0e0b02044c01c0d21030112400041100c0f8080e000402c1e070940c008240041000c0c42e46004a00c0b802d410080c000904030101d4444200713001d5600d01c924014010009850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 67640901 1250 67639651 67639661
    0x601050a0e031603021801030515070c0503071b17191a04060906060b16170409020403030e0a05030106030308010b07110604080c010305090303070c0f08071b17030a0c06 74
    0x240380e0808505040000e030010f0301d041c1c074611080030b0072150a0300900850400740300c1d2201c8616408030f110001c1d415a960f2a4403104114001c40750081528002014284228004007840c0d0300481600d50ba4000c81c2019600b000540301c02ca108581c02540c009001d040d1103c545c8ac1c080c01603070181c140840402221800809100000d5400031356810f24003522103080303c449402648030f44000103036081c17a0f00d02601500c005030700c8a14115821303c1210a0502c41181c44040d03141d12000c88050209519a403c0c200d00440e01700d076200070710101d00402010340002c80310454440c120b441c682c0850341c540426099403c01e00000700002c0d050001000303030200e001c0180c410140704140f0028101042c4000c50002d03013140c2e2013505241e2000c60700f50801d582500c50190044554005145507141149000e080c214040000030002031050800e1414031403a90305407520607a01c0100110794071808602086d207040540103001c1e00c6580591580346409002046031101d500e1501c40c00c00d41c0009440e1200244 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 67642151 1250 67640901 67640917
    0x2a0b030411100c0302071e030204090302100507050a020f0c0109270207080d050a0e07060c02010c0b01060f0f05040305060106030203190501030b0109060902070b0606091201090308040308070305060108060105 91
    0x303507180381400329036466101c000d040740501e944000c0800c0700307414001d10741030655200c446141c100220070700f00769540f00f50000c140c07070301940d0103c0c1d8080310b4902240303030075900201c602403245008180140146d002d4010117414800b5400c8804d8100880c5100f9101c0c158061750ad408201d224000700050a2103a5201e2031400c008050b100428090210800507a40080412a01c3c5e400c001080d541d41c002e2032060365003040d0080803c0054070211601e10741d80380c50b10301456051112420100046a20800250024941c845804032240d40c5d20100541203d240715001d001003102c1040da09201407050f0155001c80c1d4100004150603464000290000e501c00351840d2000d41c0d041100700c200403501e000c3c040c000d5104000c9080658542203041080b51110381002001d1790041005101080c603000d00e41b82c000030700300c0d04155203125410000d2104c2d40a041e905006500300b240300d80900d44c11410311880f40c0d0207921240c0c0141c0c2ca52008500711501140c4141c040b8002d034000c185031394443c1000e06020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 67643401 1250 67642151 67642163
    0x70e01020a05060c13061b0204150f0807060e0d03020d0c0f050609060907080f1b0a030507090b03010b0a0e130303061d01170f0304090203060a0905010608042a0b0304 73
    0x1603109074840c0c2d820400c080791102d00110b070002d1064506895a130307081c0002c00561400340c0c500c4041c0814400d500c440d940e4040d11441e1036540814070b400080c035018000304181d00c14107480c0350759054129103d140c10320614021400d0980d0b03445090034040707910b954290303047c1e024101402102d00b0950341d91218100c1510300c0c0000301101c000250f01003001d54000c00d200c80082c1170a01d89129168509445c5800800542c4c000400320b00120100140401c2038100d01040660340304001030104662410b590300107451403103001c000145401140d8001c1c240150107800030302480788035000b0b00c11000e58500c948140e901401000829841c07502c0c0c002e202d6180720b85804101150758060b40c500c40e0902042c4184071401c0c80004214201f41e02c1e6080c03d0f5034003640003074038080c2c800c0250b4544078080c61007101076041c0c0000c0010030554949080d403000d000c2030300e0100001d5031034040003032804001300c0b000c88a80303405070030f03030070f1005003070030158400c402e07202101900c1707900700015500250400f900c21621 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 67644651 1250 67643401 67643413
    0x903050318031b0a050601080f0304090e0c040c180501030209130b010e060a0906020f01090305030c07060e01060308091e030c0d02130504030e0a0609080d0507030c05070608060423070e0102 83
    0x1110700030f507046072040c40002c01012070002d9070400030f04184042c1d008c01d909500c00000c000e01580d001c01a07800f1503c1100300000c040c4c0341290428140900c0e8803985600030318100c10a01c403260401c0385140d100c01c420071b40d580226100c2c001503040f481095115039004c01c0c0d5003107002c10354105810180c00501c0c103142002c2000000004104c15400008a280110791101003d100845d8100300030300e00451131500920103c1711071f03180a0b0540c40054150900000d0000d80c0b201440070030341120113115140002000996a0790400000a03006901414480d8190885451000b07070304a4120141f50001005020055001c9040082150742880101c0e0031040100740035192150074403440384510b000c0d03102c8030882d104050401101c0d04040d041507043c404550424890607000103201c00308804241001c65440985040a070380507038050302e006001d4403400801060043c0d0110740c1e68011071003070f0340510204a942d600790200c072651902031500c42c0100320004084500c0b6045140d4510818010f40d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 67645901 1250 67644651 67644667
    0x6100b0a051e1e18041a0d020303040b120601030501051f05090414010906080c03060f0106050901120e01060501090815060d020612010b03150411030f0a02040b13030b0109090305031803 81
    0x4640c000c0e50320240341c001c00800d00d140b00244444d010303518580700f280c04100000040a01100340d031011129030340500c0c52001c01c1e10454500300100c40142c50200c000945071540c01c080d203d1104000c0b0f44860000e410440005800d081c1003080380c02992400c1c01100581b14011000c880a410011080740c0c041e480e00c88c51011120340c2103038140038000c200004900c450402da0560329094a24658034020740c0444100a58000c100041d641941c01e14a013040d5200d07200702c012180c0280007080d012585290030b094180c03041c0305511520445500713803200c8440c150744000b0700c1e40340c401030005c440300c03480e80310009540c074a086d680140c0070350b200501103410040d001e850000e40010981100034000c0000040c81140c0c90412841c0d4807143c0203c40c01d002c280404040b14100b404007900720941000f005c40840e880002540641c2c015140c03182460391141c034448103220b0208040d00c01503c503072404100108420160740503075041d154154032504c1c95510740d03030504042c1750032295220400e40010310401d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 67647151 1250 67645901 67645927
    0x1051902070f17010c140a2304080606090f15010e1503070f180518090106080d0f08010806010503030304260703110f010b130c020712030206100b0a051e 67
    0x82c028014201040e40503e0106883c00d08440d1030007071800c103014200c45d15041441281c0101c2d1010f01c01454003580320386c0612a9040d0045005c142d140c11080d010401065203c00020038a00c141c1e8100d40ca8078542c0c44040e2449001d810030345002070b15291041c1d8108295003c1d5442c0e00310748a01900480c82034003080e4a02d50145c10907034030134000a01c20b448110800d54040c00782030401e042d508081c070f6180e24040005034204240c15042030311910040005d0001c4500798040c0c2e008064000a4951078480c01100038206500300c160003010076480e100205803450002003145c16100c02600a518503240c9864603d031a16240c40302500c035040c56060300da00320340c05030b001e000e019100380c4810701a00c0050301c00c00e0500c240319036804426890075220500035a11440d95000c60050624000b41a0a5a000c02c90401600360441c44985003031a80302c6040590000d4100c0c880d12500200021050301c400303509aa0380700d0000700f080001d0052060300e1341e42e902c25100100d6940704100c130a1528070184440c1e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 67648401 1250 67647151 67647179
    0x1509120d0801060e09040b130606060206090f0610050108090a060608010b0a05010c0201020706120e061e070c0305430311010603020d0809060702061c1a0105190207 72
    0x215003034200d1606414455001085540540810300388500c041070f4030f2003c105503050042000d08581c903e030000c0350500408004440407507030840b0382405199140c1002954400c400d0b81c0540c41440f8007050324400e5280403446500521501c06c2c2d840003907140100445000c04040c182c600c01d40680c180f08400942c151142d0001844503000200340b014140b000c01010101c2c0368011818001000c3e54200140e9000ca40c0704195201424007106090403109940010071441c0a81411881448148506001c80000240d11610101c2c0c04c0a42e940d180442141c4104080c0c40003000b0074028010040c28031a40031100802b680c0191000a25440320701048031041800c01c00d50b54502c9803400d05106055102d01002c0501da03400c0c0c000d01c001451540440c002c1055000c014010100100d400c030216035400c021640c0180d0014003a50f260b00070300720070060b00c1540180c640f1020745041101100451b07625548044010b05031076207410a070280a016200c440011a40d1007180201070010498179421490 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 67649651 1250 67648401 67648429
    0x50f0301091a031606021c02060601080403030b100504090e0304080a0308061c031116180b0f0303040b030a18170a0903020303210c0403170a0e090a0c0e010e010206061509 75
    0x3008044d032409034003905000c4071280b100707210356003964891300d000c3d000140507801600070b292143d404c1c1c0d600d04044000300410464540e00c0b005007220023910962040152060b12100d031401c1194680403500d42c2e80c2e0b031040e4070810800350003018109010074011a002540214090041d2207070081d00c5810000007142500100c000c039196400000c00726004201c1030350480c0c240c41040b84598284880040c003a9a51020f030030a541d21241c18088a4440101d1a40744040140489445030b0301c03021219030a0300200e03220115540752015000480b20074a44440310180c00c1000300c1075030400d04e410207035968030411282007404003400b00040140c0b4104001e0070031500308032603043d200b29280c1c6072801510000d0f00400c41005d06000c1800410040d41d15014001251450b203682c610f01500c041d22408255642541d1141e802010010002c100ba00321442005160740c80e4008021410015142a04c00d2150140180d10200009a440c00c100da41d00b036000300c054030700e40d06101d0980c000446440031030780 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 67650901 1250 67649651 67649683
    0x3040b0132060d0905010e0c011812060506040b13392f0a0303060902130302040b030106030f05010c0216030503030a020307030204080d0905090601050f0301091a03 72
    0x40212003194040c071600d212000c40040000e54040d08100c400000c80e80320310b840350200040c01e80d8001c0581c0d01a83d82a58084001e024069008000648811000800a007c10851701e40c5400000c0d0100c400e5007510103c280d80e401703641c81519008024403004004a421a5032076440c00f07000c0e512401401c0d81c0102c4c0010104100303114001401c4000c0282d40404a540300d11212041e074801c5c44288001c00058a04c1d0911060710714001e4a408000390085001001c41080c000805125010449107003560080d1814020385680b0329208040740700f1106035801d003c0701007105100520701900071410480340200003061494490300c0b1114000340c2003604232990f03176441c404880200d4062000c400120214a0b014030018516101c0b29202d110003440300c2100c65002000800c200d00903410b0703038068031001c0129104402081c20142480b011406807500c1645070700009081d40d0311a604890070790501030080c03821640b030b068011001d090210518069544c00c008480d080d030710104900310420810036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 67652151 1250 67650901 67650923
    0x504030b1302010e030d090506072604050a150e100521160c0201020312070201060e07030207060b0a05060d020306130e10050906071704050c090c0c0c0402130e0403140304 75
    0x110001d003145545903413441c080d400c01c002c2e18540c01d800440302c5089440c140c80d003030740d540d5103843c145000300c520800101c030041003d02c502c10f02d0038114001c1e20a50f24150b60014172691282d001c00b0f0000f07050440b4400007507030503503988414240702000c0c800b100f0700b500f410341c10310320803494a140700400942100c82610b03007541085198030880c0c159100d00c500f02c3c00e04c0ca13011b060640000351640301c1c0100480f800080100464011403003580001c005007201c0c1011681c03420a440014080e50041005449040c1409284019882e10b05595021500000c007070900d030248200d00d100294100519190788140400112180e0302868003820444408520140c0408410750700c0641c2201c0d03000c2c00e0700301c55a1000b010015104c0e009000c0c1b400c1d159042080d401c40b03554910f4401c0c68220310802840c3c03c040684107001149241c40064440400e911082e0b891505a0005010132800780490010180001e003104018540320415002e4005000c4e1034a010302403e2601440020307801a83d0071103e440c902 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 67653401 1250 67652151 67652153
    0x903050106090b0a09020901050708070c0312030e100c0905040e070801060303031e0c0507060218030109030305010512061014030f03040e04062301050609031e0a0b0f041703070504030b13 82
    0x40c580e40000380c61170715011401e0000560000348180a1164003c182030313000100b240a200880000700c0c01154007080b0704034500c9034204007e0150040d124820600d01c2040c0d4100c045a410b0301070200001c502d6611006541c0c90841041302610134060a940070707008420010840c24420b000e800301550180e100400e04180140170b64040180300a9622f0a840c90003c040c0d1590398424100c4909581081d0007503144d050112483c040d00180000060785907181c41c50030302c10941c042d00301034100c60048442151302c041080c0b038075440b04d4044403442c1100c56040018403101c0070010101e001a11301500710f800c842c50103d00f43d40345610a0308002c101d542c0310000c100820001c0c0c00703841381518090003090450130205035844407845c0180240b40c4240340c0801d00ca0001d0320100700d0300807190050f80001c0740c0d40c103034149065126007036050180c522207030900c00100c0c1001c1ca864680d000300d0344607034120040c00b00c1c2214031006400c0504082d0401c0400c000010200b41c0441005014041c005140c4000c00c00d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 67654651 1250 67653401 67653409
    0xa06031a0915010f090209040b030d03050a1b021e0c10020703120e06070f0302120708030a27030c080f042706120b060d0204020c07080f06061e010903050106090b 71
    0x802e020315040c1c80c103075000500c0f500c00c0e0040050f00b110440d5030003684500600700054058241030002c19018820307198040451756240e0080350007103c0204082105160405a0110f640c260a60000140c3d1041850304c443c681000100d038034003042138080e2001c0ba40a5000503e54800c41e44081c40103a210007400d000344003c1c7c1c3c0620300e0b20500c41c10410800b0034154041105400340820150148541c0304c0001c05050090143c0c1148280c221002581e9910b14070703100d00b00380c03c2074801e40c02a910f4900500004242c21001c0000f402d0725054114103e903071035030216066400390070100c03800c0c0018403e0010124580d00a40042d0801400c00354130140102c034520030402c508816459510f0901404100944102e0200004541c000c081394481d9613600c00402c2401d0b400f814001d400920000d0801e00e1043d001c100802501c070b03a202074800c4154038480d100d98880713003650b011b0340c8000050407050503020704040100c10542e040c1004403420b55607480d2603084600340d5008005841e01d4203004041890 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 67655901 1250 67654651 67654663
    0x72c01060315030221120703030e010b0d0f05031204110306061801060e0a0807080106031e0203030d021804050703060f170303070507020102030c0109060212010b0304030c0b0a06031a09 81
    0x11007458100000c046002400300b8003200b0b4800a8010380c4e80d21350316034030f07030a0300d00940745003060b904101c844d5003a001c001c40181e0792140409070000b0340340c076585801001044c0225640e05400904d0000d83c44a541c481640c0d90100982c104c4151108010000d00782c84c2d83c1050f030744654001c51011100f02120b400707040c2007500003402c02d842410600b228021001104c4095410758006150141c110b201d580041510b010464001030304c644544a000226401c2c15008242524440c0340418000c41201100750030740002100000d5154000388185403400800703502900d224034007081c010310403c14510103e0215030051b01d0300c90009807120020300103200e05043e04001401c20f61400480000000071158481c080540500100f107000140c0c03070107580c800c0064070450081c4000810044880e07241c424029802442c03014400201000001001524a02503a20460b0583c407a003c00c0032041c0d850307202d1003c0061100303030135540d5042e010005c2003036010440000c61070321100450718200f003031090385001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 67657151 1250 67655901 67655909
    0x504030b0109020724110c0703030e060f0d0506010314090a03080112020609090601050c070902040501020610270e01091a10030c06080403030908180a140f090603072c01 74
    0xa80104a01d0b0000f038030020011888050300300010504480c0040c05c00f02070048418170200c698004070300107240701400b03c0c0100407240301e6100e192100850009001e000e000e140b489441c1c05d903041c0a20007185030b140d00500d034454814540001d040c40080752203d40c00101703950714081b541c004d904000030182c1081e00c0c503014050f165440504c00400fa40029503911566420600815030000429101d9015105490581d030009047d14030164440700454002d41040c0b240c14010702c200c002044841050300c0c9000251401c0e4406200351071001040702d0600020404031011f8550307500740380c18080c0028421410842c0c4500b080d5103100c2d565280c1210002d01c050078000c001e040c03042c030030400501c1460000d0201c1c0c4403420a00c141d9542c508056000f0940400d02070480d000000c0d00350809140340c441404401d104541030402c460306d900c11581502d5510800c160002e5042c8a8109640780604106a00140080c02c46010315101c2234500c481d076081e0354248840780c8007503014080032140444018054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 67658401 1250 67657151 67657169
    0x402070302011d12180d02040c121b08151f090302030106050402040509061003020d0606090e160203090409060209030a0501050f090609070303030f0209030105070801062d0e030307050a030504030b01 87
    0x3031013102c82050320351250710b1801c14400c009914141d240d84800a00e041c1e0182c00030301c10001945213260261401c500fa1305141a0685010f40301c80b0f50301c001d80300c03c4044007501c0c0d0b1660a0b0f942c5e0300300d1140300b1500007038001c0d520002c40c948940d112800e0700c0340c080c0b840c059942c9ea004000d10b580306060958a80d500040c1c0f15500610051109403119114107502c100104c859020764484200164003c1c854200c0031207100c1d00b403100100703149810001c242d007190149101d24456558501005030032f04450314240d0300581007085000d90342d06e89130300714000b41805424018580250303040041d00d411410380c4211010f94403041000282c40511800552000c5a80044c24040c80c200a106858001c580401028150f03a0900494082d102d070b41520032081000d0300030011800d000401402042092080718001204c0d0215030400088000d2034007829a803881d101a2101c01d02c20082c1c1e030003600801c1240e0148401d01010b4042007081141041e60b81c06601c44d42c0d5540d0071801c1220350500141c0125400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 67659651 1250 67658401 67658413
    0x90902040b070308041e080405100203070507050432070e011724040203040506090d02030408070e06040905030d06030c0603092411072d0309031506050402070302011d 73
    0x120110785822541480e80c14500159190f80e00d181c24800e000c4080e050440d80f2469032010360402030a10700a1040d241d08a0b006043c41c0c00c40241240da0f40b24548009160303821040c42001744c0e00302030704a403c4090b04140b40ca640c1c803040450b1941130000c0c1607140d4400103001014014040e4121300c0c0e100c0301e41801e107132040a503002960009210791340508840e400c43c518200700559101c101c0034503c00c82c00c00070815503482c101828038596442d400e0b1000269070080c881885901400002100c0031100d41d0700c0a03001c1203150256401d80100000e0011303800c107445100950000cbca003400102480c0d9003800c40050820b08609202c1c0e111940e5800603010700d8a46440f14000c6214070050a00b908107a640f51407107201c1c408040d50151260400304040c107040030405804001c420403d81c11a2400090490001c02c000754110308007556484018010070170300c2c8003c0c408200306100e000c0303c1024485002c2815075985000c90226441381c0000d0380140d5681d00c10500b01e00310800e01c2c04a1204090003405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 67660901 1250 67659651 67659659
    0x20303060307031209030f1110050301050d030c02030f0f250e0c03060102010603021c02040e0a02060a0c0f12200105060a14030f01091406010b0414040905150c040609090204 76
    0x5602d020501000d814241c2103680a40b1040c420782e0018003440e40060300000d10582468182e40300606410340c036204108204079850814402c00c00d580c101c0e040109030f0702c1e01f0310b0726850507502c0840c03a23041030f0b03054000e10750780e80001042040741c014139401c600010b00c0000d4001040c901d51201c1c1d240b40d800c0740d101802c1c00308000d03144001400e420030b40891036540c0e0b03510b8200060307005221030b03400250030a1080480e4105464007810000700719000366004e00108405034503443c1c4803034641500a500210070f215100e00c09109590042c0c1147c40766070a02ca80d82c0003900d41c07080009440a8520005090180095041d08a100c11442d50b01550b0001d100300c0c1450b50016208920034021711401080340c07042055aa50200500b44039006808020020414203040c0075540d00701d090146001c030b00c40c9000008480010100325022920340302c003203038060790040c002c20018000c0e40c44155458428204070b2006142d44074a0725000f6141d4000c5c40765035503d0700101800c94509584880409441800200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 67662151 1250 67660901 67660903
    0x6130f170a0201030c111005061005040f0608060112181101020f0a02090615040f05010207080a051009080403061a0906030a03080c031008100f1b1e020304090e060f01060203030603 79
    0x7020351642420080307246803450307000711240c0241c9075099009108103032008100e82900d51055024640c140d88610021316070302e9060b100c1d803059109421400040c1307001000070600c07440300c1d107070040300c149428501840d0011608081d5490850401c0310240c54460340d00400c00200c00688000381e00307001520700f0003182a06591586800702d0f010b40100c040c00000f80e0030f5074410000c11901024043c070b590b202d039121020600e5100c0c49004190140c4200280414052000102e90f110103078480024186501078018900c0230703011034a4112a0381c101400302200140d01801400c0c0284244250016070b50301020421250000c054000b9009800001095011035400320340c141c0e000c0024080c83d5501d44400056040c0000c040d840015180218001c0701d410201c1600981c1c80290224801d204604002c2c074802c94400010240c20086140880c051186e02d91203580d240c10952a4010b40f8106913031880b8800030342d40301c240f820b080350300000200125090010405030142105100079070952910700042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 67663401 1250 67662151 67662163
    0x2221203030905030d0e0106050306010e0f15040902060703081510090501110a050604080301080d0503131b090f09021309020312130b0d020403050607080603120d060506130f17 77
    0x9001c040e1500350303070010703c0000c0086030440d45000f641040b001c99420000c9000f00194003c00740b10740a540c0c000203446031000c40e094010b04444880741c0e01c80c0c8404445c2145204180c00d0b03250040d469005100150359130700c003d422044e000391566140b0340350074000301c900d800e44c03042105c0c80303985403544100403194405d07409001e80d0820b080c4a01020508c3c036019140c2258010010128460002004104103940780a94101c8030144c040381c140150001e0280c0c0c003804102c0d52081202180c2d040c80e4085864a0342294160b4020000b101134292034080d0042920b14000b02d4141d090348034541501107050808505c0240700101c101004208056800a501c9041014000d201c041c0089400401402d81401160050a1420314242c0e83c080490602c8041d40003407005480d1405480e0005054500a242c49482506c0c011b01501c09141004000710017030308107118900440f66685404900c0340c6511004248170b80d800f0007480d034120310704030310600c000005801107807108601d40c541c00010040007800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 67664651 1250 67663401 67663403
    0x907060e040b04020403051009050607030b09130201120e0303090f0604020a050127030303090b071b060509190f02150a09050906060904050f0f010602030403050a061104050d030201022212 82
    0x40400c0401050b00001e01038050341e000035199008240e0300703000841496000d01c0b507003441141034a501780e94005007a0208d8002480c12500004400000341d46030525202c016090f1348141810801d01a504201c41c0440c1c29028100380350ba813000040c02041081005001349444c1c1d100000e12040ca081c0d408516084200d104141c14001003405a1080840c0301c90035010020b00e400000c0c0740a40d803410000c020340780506040d1842d0720140041580b007840748a40520004501000c01d120040032340d69440106001400c0f103038507014000d441014a0303056074a07007040500a0f05a540f100640b40100f01021104584169464408024081d000ca42201040f402c59004468203980d030750f640004038003603104800f812640540351104001c0248005051140100001c0c3c0f0034081c26270321030700e00b6a501d00c04d40c0005000c0e035000d0040380001038000d400c42903502114896036800c1c990790f8404148044003840003180586d402040c84a4030102a9084640d9180c00d05602100076240068041d02c1e10a441c00c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 67665901 1250 67664651 67664659
    0x4052104180207080315090f0601020c090601020709060f05040e030a0903081303060501030b1e060303161b0e0a0b040c0504090f06050a080f01061d060913020307090f050907060e 78
    0x1c00c1984480041d8103942515410501c40b03a07403443c1c00c006402c0c511521201c003611800640000c241812054025140f1465040e00202414044041008480080142028114400c600f80442c1c40c208500550004044005060903010300f0f0004202c2075070202c046801c42d9500c02c0c8084c819031036101421501f12508954090faa901c122170314654a40b08a8001130034241c2440000802c004c40e48840301c0c4641c040860a8107880c0e490440c401301c2c4d0f4815100d40d85d140d8424031005c0c0c41010050840780c80700c2d2042d508591181d210b2000c2100d02030b000d07401800100f51050410503c00302c2401500281d43c0211420030000d10b82c000d02400d103005900405c65195071728611613040810030f0780100c01421008012040780c1e43e5400e0142d40c0c5000643c0004555402c0100016081019590849024410300000d075459900c184c1071081c031017002049691441e003101104e00140e1024400c040140c19800c0c00402c0701711088281c030044d41d8001d0840c0d1480e900c0705d8010400c80d41e0291070082d494500711 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 67667151 1250 67665901 67665929
    0xf04231c0302070b03010605090f030a170d0219050714010615080702101a1002010203010e0402100207030f0515060303030405060103170403020a09051017030901030b12030c0604052104 81
    0x20404903d0201160002500080000008a101078000000d003003c2c03a800c41700030280c96108414503440b08100f0400030a102e1050600300141a00d81004c1e010051441d00700500700b85600664040c803070008072150000c50000501101401000b03059001e00c03502c080c000703015103450311070000002da4800701c0c04410800c0c041d000c10003080c4280b082e44241c600c16202400002510394404400b0800c240803180300701a1000805070050040c02543e040b5000c180c0c6c0c5003ca07030b44070780034494100b0950300040214040c1000100c001340f4071030340d00e592090099000b0301c1c40c481e070244080c0d0b079881c0160900380b0981c402d02c10000081d90015165041d030354080d0900e10a418004071450440c010750b0802588001c600c0d1010950b0140d41d44600d2003080300d0035046020750ba84070800d0090091030343d2140c034541c108114141640d40250411000c0900141420081d110340c1d903036990841e0013081a442c00b94004030140030522008001c0d2520440402001002101c404500040540f00f03621900030b000700341f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 67668401 1250 67667151 67667153
    0xb210703060302030a0b07030c180b09030a0b07051306050c0303040609020a080d1d0f0a030b060102120304050309131107030c110a1d0a0b090a020d0f020f04231c 71
    0x39410000c011607020b011075100007000d16240a091400301c2d2907900003858488403e407030912401070756000182d091108010141002e142640c00c0c0c1c4066200c50305407081500c01c60001d0740c50f0780c00610490b030079540c0648402a00c0902d41c81c051040e4010003c01100b80440c542c1100040110b94009034085000244002c41d0700c0403da84c1c0940f548142d0346800f403102c22485003034020300b44680002ca05801078020102070010030040b03002c500d40c40364000c00d5281007480000c0d25a0051078101c40c05004071078603001242449603465000f120101c54942010514407c2030030900140280032041e0102072001803032010503005640101c450203004c008407454a841800030501d09915100d42c06820071042c0d80e161114414000100c1d190301840d00e056500160038440d043c824001d0345c4400610190440d121100400007940100d0314080311950703107603840d0602080a100400303d000400e901c45032070f246000501001d084210301404035034151005041c0d0b081d07581544920404c02520030580d240a45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 67669651 1250 67668401 67668407
    0x3090b0c070b04060302120901090b160201020405030102070602040806161b0f05010203090601050108010b0a0915111b03100218220501080109020a06030207170c190f020a0b2107 78
    0x72a881448502c1000034080307001a0325800900700402c840b0900c60854480d003003007d0880d10514000b4002d90022000b00344041e140c0e000c1c0752580200d61001600b001d84650029007240e019810449501e070740050f0412040909100c140c0d0b006001c03042c01424800b021034040c0c0028544c1584c0401458035101c010100301100d125250a00c0c1c010f0000c54580c42c024420b140d40d05403e0243c123000c200c4450000a0240e10002114100002e5644804042d132520307010588d00802440c0140600c10003100110464404000525501c003070324260b804c51120000906040824005100607040e00401c1f01c400503010201740b14560010a444088640c842c29112400581c500e0201240d1a801c0c1400090720420540102d9440b43c000c44003c54111f90340d0500b501207108000000f080040b1021040146408501c040e1000c0c4080c002070752295041000f00044000c114081214440c05c50403000301541051202c40025101c0700c0007003842d140809012840c0d5401540b4101200400e01002803c4184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 67670901 1250 67669651 67669663
    0x80f040213180b04020405010503060c090108061804030206070e030a0302071202030309090f0106090e0f0601110f030403050106080f070614070309030209070807180f06080a060f121b0303090b0c 85
    0x30140e8200b200d01418034002903640001c0d00e060f80301e41e0410001040510307000c00c180e0300840314084800e207050068801551420001408039900440c0c100a6520070300c1202e1880d441071f44a980a440c051a042001a000200190805010380c0c40b0f9012400001e40004541c1c041d140156440d00f074a62561000914501c10076889a421103062014403d1005000780741e107049c0c03001d80d06c51040030b03501c2d90509107900d0401c884041002c03260301c01080c129401203043c1920010700320207989141409080035403569106620498450307648103010003502d0009d00c8000d10341500307500a000c0140c60002c0003403140c2ca2090b002ea11990000800c0001c25004a0584c1d00441d4043d0840d13000b8644200c0182214078126140b50101d9454000d42e801100b44030110416100741c141c41e4041319080120484800d000203001901071aa80d40010601a00030354549000706941c02c0041e031901c3c1c407031400d2040c440030b0402d01821103003904801d00c000303600704040c1416a10980691030716043e10705000c1745401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 67672151 1250 67670901 67670921
    0x1005060304051c02030a0206011d040b04020310150302041103010b0a0f05070c090507081003051009080708070f02100302030906010b070807021201020a18080a0305033c07080f040213 80
    0x118036422000640b44c3c0103c040e0400e10300359004e0b5070030b0340ea0702c0702010f0b2107420410b54055901010000100005e20700602150860b0000c0c048410380b60b06018200d04441c08400c20b02d810410034581001149040e000d8a4000380c0b50300d44090443d494009a61101c3c0140b00b030400501115410071603203a88601d05440000703811605091520b035907000040c000703080076181a0001490800042c42100c025030080381125407000041070761100c240b0100703000341000102113a07851341c00c000380d0005c90741d400050035100d070042d50b000200c40d0702d500c10070494129010403201854014400c0041640c00840e8950460301240989982d6121501e8440c0c0c1038403400b03070700a40c0f2100401c00c01d00074107030540c041c080034003154445c03000c99950b11801488186180c0300d0640030f90702100c0d1503000280b01d50051500980411241144030b407010400f401c40300c445003100040c840c0b0070700e6076030051011882481c0e0007070814200324000e4200b5140203003c0d0800180040e0050800d80c1c4032058101d4540c1c0110380704 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 67673401 1250 67672151 67672183
    0x50919051b0d1203050a0e01020901020a08030603031b01150510080103120909020a032f041505090603040311060705030f3c0405010c020f0601090f0b0d050604020315100506030405 79
    0x103c1003400050000d250070f0700c800707403100e02c1d00b0890707515a0014030840e13103003070b4058004180442003507481301419440100030070303010700040c000c40182d144080d14030422020301200115001c2c521460030300d00100d85a00c03840c0709030036040340c8290081d0089130341070559820402c80c10640144000980d80c0700031651000d15841e20000b0105080b0b9416880f200c02441c5069002803104a9440e03403ca001d40020020304800400300320400c0f60103180e5504003107500301c0d400d1050070a010b01c0002805034204071400d0300032a510000b101da03503500c1441410340c03145140c18003a0840c00e00300301700d843c0b244006005507503070040c24012104500103140000f00000398006201c10500441101d401c441900b954115001e41c28030300780a00c258008940b030783c1800d40d03c00041c0710756071134041144003030000c00108a000350741d00c04810065031205114820350344d01420041c201d500f06441803514004e1307441d0700d0010715140301c1c0500c0020f500c451140c904603881140c1143d241d07103070f5007485030610f03600c0c0b0000c041e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 67674651 1250 67673401 67673423
    0x1050a1a162003060907090506040905070b0403120c1101030e100216020a0506190804030c0204021206091501120209060c0a051507020d050706020705031309050919051b0d 75
    0x4000445207402080742e030700802d2500700ca854005056032244255004085a008900c041c4a5165140e102d03d0380074000400208003154241c8425041c104140c00c000c042c1c10000400384180303c0c2103424001c5085d860700d881c44511120fa01e60000710288981715074105916a501042d0f0340d0010804003031480e401400865030741388041c640d941e0103558000200d0017900d000c42c1c001054a03059050780d40d003800e010220b10440000501c02c581d11030b40104202c0601c4903c80c015030268940d4400340c0000c0c0252800103085062100030081030000c02016000c0c41c500c102c2201030244d80c40030b08032a907844c003a01c0141e16010341c20000b8a050140c0d240c02442485071280802c1440b80000300c5008010030080c1031480e40d114103c0480e01c0e48514010503011400411200c4000b507082e03401000400d0103041030741c0c24040003141c50401c82c086a8440950a6220000e00545000a00854945440c50a0b2031402c1c200700f6a20309480d00144800d03181da4840c550f0340540c45840d43c0e410880d02c40d81c00328070454 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 67675901 1250 67674651 67674653
    0x19150207110a24020303040c1a120c09011209020d0201030c0905030f0601031a01080c010c02010504080f0f10090308190b0607060f061205150a020405040e070801110301050a1a16 78
    0xf0304808040d615440c2c14460402d000702c80c4e0020013124000d42c0c00804848c0b0140c20420078000800140310f0305114244200442034001030980d040307500540e0002152076a030032107480010403030725035100c03540308151501c000000166170f681d003450ba03166420309000c1500103851600382c1d9004410b84c030854050140d441c00101000c07007c00c006058a204040c0500c603031101c80440001d140c03003400b513074500e540720791000d503039960285800c070080b9403051403d2881c081d100e80307a040c240540f540c1030303000380d0740a030b500411405014030401c40e07000504007082210300b0302600c0090104034041c00c8030080e10740d680d004100d201c01d15000705800040140480350391b20f1552500b0340042c03103150300700922289840c401284803850302803514415600b1400500c82011f54021101c01c40b0405071483c00400e5003000005800d498034080c01c7d40c001d280d800901120740c542041d040c00d41d00800401855000700304014030140d980d85100c20b090790306843c2d440d040f10b0000484841d0601c160b5070103801c44e42d0711081440c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 67677151 1250 67675901 67675919
    0x903040503330402060a1202090607030309030e060a0207090b0d0b010305071805060a05060a020a05060907030204060b0f0406050a020c09151c1112070b04030807030219150207110a 79
    0x1d20b201c0440c11019550020a0000310750b20003981e000394400400c12400c3c0a05210f58848510111824001890700190000081080d4803540040f000300351504100414150402403201e0224000d4901a1500901810080d1100c1850040030000741e40e80c0b548402684841c580d03031845960dc141c100e000d95861b4188982d41d08114441c2001025003882022080c00d82405030324040c0030083c008019a03410602080400e400c4092010114031504281c0c002181c003c002c418010510f400150a41e281940144002c0d00c0140d000606046010401680c143d140c06044908903006894420b40310032038418104e003001400303140b160380416250309000c40842c10780f0b201d01016170125924140245080c4804000c801e20503009020a103034904068654184a809800600c2d03501094490861320b8405000c003581090b00290740c402004901001056010803110f03c0300c0408176444800d42004c2d5070f500c5144107803548408110342c1c0100c3d00310100141d06200ca80f10300c82c020490392000d5241d00c0d0403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 67678401 1250 67677151 67677193
    0x40b011a0c010509160b09011d01030e0601030b090c0102012a020a210e0103090c0501030203061203030103150e0601030506040609150e010b090a0b09040602070c0b0a0503040218130b0903040503 85
    0x404440c41610000141d03246c1c445080316400001a1108140307800864601050200c0c40603049041c1900c0d104030603280c14003440801c0c0a14031030f110454060504d460021b20781600c089205065a1510005102445061204040c00780d803203000c141f4191201c1904a05058400900401506510b00c180c40301302d10703499500b004d00d0180c0e920400c5a1000d240118241c0b2060000035150341080351041c042948240c0080d607000d18040c151b0466070302080380d02c606e140d00076403040d1f80584030380300300f003090340028060703e101840d403000100f200f5411a1140703a02c0d0500500003d0003960faa0340c03908104040c80340345540442c0981000c01074960083c602e140a005180d441d24031400100000600380001445000c0d103601001c0c000c10110b582c0d660301c1900a41c0480c0f81681c03d8400d0707090015044000e03000070000c81449540b0310751030703050500c1031065030006000c48901c5440907404021103c405e80804501040e0040025110b5485a05005003148520380001e50140508a40c5401c8000c05c0e41031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 67679651 1250 67678401 67678423
    0x4150909110105040b1c1b0302030612010e060f040c150f09150f0318170d0b010305010317070201030e030c0f0606030601030f0212030f03101805040b011a0c010509 72
    0x301910070303484004450920460080d40312030701091082c0544009039074a42055628119000140ca04104800c0301c2000c29001450340000d40000801105040103917020304041d485030000d00c02d509184130324a80f2844000c00d015482c0410320700180030321160901480051125031380300c4008000211000b085803079940090b01c00f0403003112000501c81140d08140000c0c1328140e41d20703000c110301d81c1402c8000c0d0000c0b00d481d03201042081c0301c50700460b10a0030400020740703c080c0d030f4607035451503c0341013401d0340c08900b04581450310f0100104082020404e40080504420042550701c08503407005a0040c03840e449802054400842c0035007405200040c0706401103090f104480e1190340e008101a5903407024040144501c070f01c03444680040c24003016200c1001100c001350390070448806480c407007a030001c43e08907544484140c000c02411300464103111600b0f00d100320038403051520f0b84800c0149141071003a4030b03803008104026036103045038009039200c0d010604002c0c80356042014841e503640903071401d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 67680901 1250 67679651 67679663
    0x40909061406030a11010c030908070b0a02100c0503040209040203101a0a0f08030d02030711061f150e2112030f1003050607051e13081b03060f040204150909 69
    0x101040c2c01e8030307000410000b22540515a1000c007104400111810b04c0001c00072002d200e18298081152036090010501504032401c005d922800700034802854042c4c00910320070011320700300280e1500c84c5c3c00811298829010790342102c880e02d4500c0844d00c1c0400c10700e804210540340440d04514070416040600001c5d0041310f104203c00d40310100c100c0120034a100d04d40e0f2580c020060f050118402e6005168428514107010b4030b080c86074840c441c2001411035a05500e20800b0003100080680d41560710058400b0040c01c17000680390b80340207010100300481091007401c0d0309080b64004100103052640d000010002d0394203140d40350200400b0b540040d42c0c41c1200035034030030005904461000703401c811250003500030200741d02e070f0410070740c1c1a50015201c000f85807a01280b560101740e02c0340c01014614240d4140c0b034084c0e454410030600304040101100760310b00c0c41030001d032a607981c005000c42e00001c0104000c1e9094450b0300c00a00101070350949450788544040002948080681c030140289000b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 67682151 1250 67680901 67680941
    0xa0201091a12040501060e0c0a0201060603050f041506080307030c050f0a15050405160b0d1103091f02040e0c070b070e0d06050717100504060803070c0b07030504090906 74
    0x21019124486600181c0603240209100100e10800d48042464002d8020000060b43d40d8442c0758514a51004841c90215804005219106582d092107101d0081026140405c0903013401c2d00e207002c602c5400750016000c140001c4200741880c800ba44442d0003040c07903c08407a41c1d00f01924000d4040c0440507015101c900881540c1c20322a0404602403078220382c042c9561b22005410441c0400030030340070300159541d1044609035116460152000c070040d104c1d0134000364032201c840d00c40200f6508400c45032a030340034041c000d00005082c0018070300c070003030300c140b40c1d90b03800c08a03002c0104000d029951085d4108850340b4244091402d4440090800c0d9000e85041a45641c0d54001074404801504030b2030781044104104a0201d1015031007260001d08070724000c4140038149404108141c0143c0750320884010255013040f89181038400c010041a030719018504162a90315000c400041910402c040b402c0001403031410140b00710100d501031b01c04034a04001c80e01c15070414000806640d038101d44481c02032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 67683401 1250 67682151 67682159
    0x22505011b0f0b0a06090612021f05090d1b03060b011101140c030901140718050916080601020709020706060312030203100b090103020903010e1b0105030103050c04051003140a020109 80
    0x250001995480d00480b81003800c1c0855610350b40205001800034005559a40d0081241412409a54020164880d15406484090040146020003000c016401000d90420b145600b5000003c3d6602002c04407035540341454141000e00101c0031000f0320000b95005031402100300304441d40451401002170741e80c400d4060036041040d00b210042195a10040d086000095042030218004d40d400040714001107400d080000b0300c04401403003a03550502007103c040200110241603151300009060440ba440f0403800e001541c000b01c2400803074504104490100010311a9008004240060003040e80c11584c07a040d42c14000020010350204945034005043c0e6686003074800d00070b89010f50f0081c90b480f0308692902c0070343c07556940142101410f1640034403000300300366801c0c4100d007101056403010340004441000541c1c0521240304807641407100c11310051000c6480045d03640307075600080d2000242c94803020503510302001564402001450401d1090000140110394080341510030b0300d5a0f180300c0e440d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 67684651 1250 67683401 67683437
    0x718080a06150f030f030c05100e06060102242502031905071a061302180a090c050307031503060603030f0e01020f0a02090604020d0501081f0b0a0b030702250501 71
    0x65442100f0f90f203061818203002182d0707908209803035148079081485e00c40c0710640c1c03510700b4503a0000c0e2031092160748014030b6884001c207002e1b0783d034480024406030200c0c640240e080c0500210300700910301072140e000002804d04001c401c034100c59900166840c89403040e0f80c003009549038440500f032541d810301042ea0107441c0e4002c00903280c180340e00000015030f44c0c050300016980c1c0c420050031254000410032a81c0f0b00c6d00601d00c000c00c800d454410b045ca56030b050a4090003140b004560240795103034540310406150680c0070342540d42018107842e000c102590146a0070080303840641000c1c00d294549240082095080704000303205803440e458051000380c010b801a603c3d81140540324a098020030464001407400080d42c03030340064014801414859058601e00444000360030008050307101c107890070710340c4e83d888024005c0e10381080780c240a04119078002c203030740507445c5c4521688110048003003842c0d240203000c080208110702900d00d202d15041c20307200141c9120b2b44981d83c041207031840c5440f14942 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 67685901 1250 67684651 67684691
    0xd060f0302060901030903031b050a020c06030c0702060a210212060306010e0a111c0b0102100e030a0f0e090a0606180b0a05090a08010216060b06090a030b0718080a06 73
    0xd0000c1c01030f0300300308032440150082c0a10000c00c400300742d602d001c003040101c0001054a00000580d850984a880c0700b50b020b86800003010600c2e120701400d004012403400c140c000c07203c0d11623041cac40700398883c601858203562107103215a03981c4420f503d030a80c00701d103c6020f071302505c0ca110000071610fa96840301c1050540741c0d50207000700401c1400200005122580c070f07800601003030003e441402d107449a110000805a0b0180039002c0107907850b80a10030066a04000c17480c3ea80514000c00c01c10488620140e503601e106011070b100030300042860700c5060702d0040d0b041c082190b801400c604a20318105000f4070040280f4003c24001c506034200425655590740c1002c8103590750b61803443c1c038192400301d0070303100c0d0380148003aa64000e000d20404030b0515404c2c0007800c120f403400c80448155003120f00d4140261005840014060f0348240701c0303d02e043d603c9240034030869821200701d1003142c907080d8044a188444e00801e07030707410b0092200001d407440e0001305602d159002e0302c030821050100701e00c042030b000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 67687151 1250 67685901 67685903
    0xd18082b09030e0909150c0a03050f01080a030c150905061006020109030c020415051905040b0f010e04051b0406050309011803020a140a140c040f0605060d020d0902150d060f03 77
    0x181e042c4980c5441404c01841c030507000100002112016001c004840c0d61510003218a20500680480c08559940e01030003250340050340301c80442503079810310328071a0740d400000d50050300700000d40e107003082840360b00d5601c503070049803120003030210300b540b4140603030755010644220011240940700050218818810000066899039828000080315002c200280880004540c42c03601c00c0c00340050300d82c0c3c1e03801030031050344a6900b00400c802d02e4a400c100450315404801e600070300780400c1d10001030382c2c4200c0041007410308840024494950300070003a80011700320f520300c52103440050049003031a00000594420001c8400910545021a0910b864040e068000502613400703015500c0c00030301420381c070760750311100101210001c0102d0745402206011400f04004035402858000e00103080500544600c03d003800c000b40700c210b01c0d060101d42c0304c4c400c0c058001ea00303650114201107554010f81107000680c2d0002c00c0d22003080755481c0e00100300c1c0d0010720500c030501d01c1c080b0001f44102c4060388001c100c0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 67688401 1250 67687151 67687157
    0x60b01140915030603010b0d1a1003020a03030f0207080304060215011a0f03090a02041b0e03010e030306010e03010908030f060a081b10020109050a0308090709050c0d18082b0903 78
    0x300c02d140107000083d00043c15007a03040d5202c0c1007802464031015208103407a0f000b810440d41903441040300081180c000b51248428607041401070002d0303180c0c0600c0c0380071a0342c10b2501c1c101d42030904004a0a100e803030f81090026000002c1c000070300507400111501c020105021003115640e960b8810403170b80701c1094820100718014080e840040b00c03400007444e403122084041c1c9a68a006030b0000b800c6841601e050f0910303040340c201c03448800f50300c4040f805075500d00b940200142101600300a949020007064075040241080300121940c0f030a40000d002c00d80d1050301c543c0c880c241490300201d0380d007040360303030500640f1040000114410006415141c4101d000b80803500326000702d003030024000c0031043d600300359925110300e800058400c1040002c1107003c1d94a1200c1c6003410f04c0d0f03007810140198032044d2a203003060244911142c100080b10700d01c0c01c2e0210005404204d40c403001000520710000500a88404205149141c8140641c03241c0c40c6a05540c001c00c0150070900e090807950049030113000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 67689651 1250 67688401 67688419
    0x207120609030c06020c01140c070317060a0b12010801050601090e040303091707060f0b0a0501140705241605070b070c0c0503030f190804050a060f0b0a03060b011409 73
    0x3003400c651000c41054064a0034a0007030003161502c400b81ea01c819010130703541c0c3d915680205a20200c49025410082c2440d80c1480c00340d19850051540003d0740b07103038100188038400700d15140d41d242c1905000f01404000ea41c2c40f01c002c0c05a00341d8568091103003042550a01e40083d145620465100060740e50441d507000c1c0300d0b1142d071011001042030314070840b0706480c01203114880c04100c01c064101103100d80004510f50080e00d0040054480c0000118040c10300010180526a00260411a19805201d14548a01541c14018035007620100203510140080030140e043d4145918120311410848080703240c9483e05400460790381c412540060f11000e03003100458101f83c0700344001c01a01d030103801080c0d20079480d5400a800c642c03240d0004001c00c0400a0520550f204241d880b0007814902d0600402526181c2c8580d610350502c4407004003642e640e5941c80d0b20070615640102600703c0d02070990100d5540744d1811000608a00d020f03940804d80c00740200310380300c5803801221420b2a024045d518 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 67690901 1250 67689651 67689653
    0x51605030a03091e0f0305010203040204060b0f0409051b0a020f0d080106050426010501060c03030608030702010903120c060c050306130c02030a0309030e040203070903021806010c0b18060c0d0606020712 89
    0x1041d01c0002c4c1110300070722680c800041541c0c001071850701444c012400107949042c90701c100800c0b03601c983d2084030340f03000900070a000007201c4810398046400d2950085040d680b040714411003141c55aa00c102c01d0f4001182c04007413a580044e1000081b22100111703542d40c0704043d816102402d003485140c0c0092002c02c0b0901070f151140014036200c229140400c002c01841041d060b080d640b09030041e0340080c400010007003e0503031500562004180100c06149404c425400080c0b807400c05c0e000181c500008001d50b0704c6000d10800b0203e06003a0010802c00000080410061440c1c0c42990414803807101d5143c1c1c040d140c0d0f2240329400307101038150002d45c80c0110020065010340100e500030f6090000e81318030488151a50b0004600c00d80550b40c03608a401c0c294410406903c802c00c0001d05129180c204000c9c0743c0c0d800c0030351901c40707a0f002405a0710756540c10328030110402c00d0a02d10380d01402024148010400004060708002d5030208050144503102c4100300d9941000e48100d030548905008500 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 67692151 1250 67690901 67690919
    0x15020f0a110c030106090c090b070c060e0d120903060b0913030f050c0106090b040e07030803013b060420030420060f0702040f0b06090405070912051605030a0309 71
    0x711280d41c014055a0b49411100006800c4580d181e000c00b06c0103440b0000c000a1035840492640507120b6003440d94100502d40c3c480c212205032078010001440030262003807416940e408031200b01c2d150b20450300d001030007000340000e201b0500c81c44101d921900b4603020394842d1601c1140071b8070440e60640c2151103101035440480d0018210342c00c2c0344c24008104600d0070040020300490014100180d001310709a002e120601044488050010030399810004080c000035a10b041100e04480c4007419031008880607021000c2c2c2c02d46480040c002490440c010107010504802a00380700300c00495003000780707080314800d1a2058004410062104104100160010318401d0866036400303c04900c56502d0702412002c9803ea90103d488007122090101d104800c40c6000e001e034411105030030509121070030790780021032031500542ca0000c2c270482d03c41000941c4188074404800040000701000580017140d420030a03113481360340b641c10401c0c0c0030284000c205401c0024640c21001c0c0e0544c4c0c5c9080d546c0c60001d40e0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 67693401 1250 67692151 67692167
    0x150a060e03070b03130f14160f0801050103120f0203040b0a02010c080105040b060a210903050403150b06090105070f060204140301050f0f04080a0306030b01030605090105061f0f030212011215020f0a 87
    0x4c441400a280601d56054000c1002103230100d0341742d881c200c0e40b905149890b40d9412003035016888071780c105030040c00025202c816180c01c6011500b4084860640414240c1c154041c92700218a4100c0100d03684c044250305400821441180d03031200c4199036252002c0c001901c8052400980280d000c0101c800560710a5400d400c91601c1c503440e4090042103185003c040c2d40340c6050607000a4400706040c410700601800b01248140c00c00010409202c800020401500070210650f040c400f0101d0040c6c03d000190f9803000302998420002c41d942e540fa551001c2e02e0b6080c28000e03501039840c09002600c980c81c0c44c0c12060140340d1a03d4a541580d5442c0d0b1080080e5102c003c07403104040e00d4150010009003e550a039028511920b4003152504d01510b03c03e08541c0700415103442400626201020301c07001c3c1c0405044403400e4039109244800407801074001c0c3c0325603550301d00400741500c000034203401d980c920940d10620410041520308a03001c00c030030a9014109100b00007540402045803a20b00490003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 67694651 1250 67693401 67693403
    0x30406050f070c0303020a051b0901150201200414060408060109020c0a0b040305300c0d06170109061506050f0715140402010f020a05070e150a060e03070b03130f 71
    0x307810316182c500c1e5200001d40350164402c401580c051021101002824085840c010713000460004540d10343e040000c5050344103206001030f00c580601ca81e1080d41c800c2d0003440c105c180b008407244e009003168003e00407941c030607c05d6030813446107550060783e50314004046404440e4140000c2100c1d900f89141140294442041241288076003031041e00001c00705034409100d540641c68090f00e41c2c0b0421406207401c1410004a056100074100c4101e4950051000c0e641212040c041c4a4803400c50000b14002007c1c00d0f00092020914000842d070048415085120740c0d500c0b030035081c0040511480d040e0f109040a01905010032428040008503400355000b80c1103050003103820015080284102c0011a1000100540c0e4a52404108419075811845050314203006100410001245480d01c41d202c0e109805500c01c003003414400b1400c107025400c1885503589000706412680c035614070015024946050100d03000c2d000300340002038000410400d1342d2160504035030324001101d9554a0741d400345a4000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 67695901 1250 67694651 67694677
    0x504050a020412061505090105100e01020c04180218100902070303021303030e03011a0d030c05210301140d030c020105160b0a0b1f02070e040f0602030a050f07020f03040605 76
    0xb001482c000180010150326000340000555910440c1c2012800509504800d0160f4500c2004004903183d6550b5003404101d680352a0515120a000407420300300e00481c060760040c245142c500c00e0707414034003050045a1003116030101039600140da008040500301c444100d00e03c0344241c20408603c698009041e06882842c0052400c6100c0324407000c014419002580016402504100c2505007445000c51021201c0304105914244070006420090380805c0103080041d8201e408007008810000e0030b000c1c50040448900b20101148075000b1a002449280c4480643c2d607442146400c1c801001001c07070b0f0301650b400c0c0240764550010748035a8840c40a01c610080300855450108803e44070743d602803103c103000440e11158400402c42160403140701c940c840c03095001604180c1303800180742000c850081291030f181d83e5481c04d054614650400300940f607c0e00000070803150100c2944424810741c1d114510303805645442c0c2c0101da65091081c1d2a8006500400090007564041c101030515482c440c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 67697151 1250 67695901 67695907
    0x72a0201091a0705030a0806030f0106030503161b080c0a140306010302150d0507030c0906020c18060607050604050c2e05030c1e0c0106061b06090206070b040309060809010e070504050a02 82
    0x2030b4915146600910754800007c00c54000d22000c0d1a0a008003030882c0e54600083c000302d415070310b03403a44901ca2000039400740000314841c14204414922210000c1c0d0b010b0040c0e0901c10f40d600601902c0c1c2c0a60500d26101d01029640440c000d14a401c1000880030003400070a0281c0c20340d0309100b07040310300c100d40b040c0c5000c00f4444c0741d0340c7c40014001d50740f103240702e40d5011031411081c0c1c00241001c80d00b5085401550403d5080300b0840c2c45024a0241138030a00f9120221926603002040003440f41b003601404500808003004240040000e1103010098151900c0c076201046500800301140f800960400c071000d9103040d464a0f5110300c010b1030304500c282500d41c0c0b602e050b10307001e040411050406400c0071140490f206c1191042803280c00c005141a08103004001640205a01c02d120310910046c1090f03602c1c403040040d51078150940d02420703449040b12416083c1824064810601c03403243d10001810100042c51500341030062600e28140d40c0c00400313901d0300784030401010340402060803c880b039080c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 67698401 1250 67697151 67697153
    0x30b0f040509070303020d020c0d02060d0219030204080c01030c052205130e0601050604080d0807050d110c011b02070311031207080a020c0d0b010506030717072a0201091a07 76
    0x78416039000390403040080040a14501c0c001c0e0401403802c20728425034000300c100700c2d40303515030101ca00c0c0c41c40e604582c1035554a440004401c000d003c1c0550040401c584180d09442d0704d0b41542c0140700f9140400c0c2181c04031080c4400442c00d4444182d03407100050020300c0700c1a0750340c504240c40d014031044a015541c2d2161203d020941000403607502d040013944440d00f40d680d2403000e000090252405403881450241005255556a202140136104000380d540008a04502c03402c1581e410301c224402c2805a5440f00743c0214035504140c0b01d20324a075291a07030b1880307818200342007424001425001780401c0c51564a48541401010300c905030503004800003000740c4a0b0800003000c4441c40b0f280401e03200d90000400a21340301001d01980c3c041c8801401540c0400c9190825504450041740c0c4103503a648d80c840112040c0e070031802880c41411070f60003400720303550b0040c9000f16004082901c1c0884110f020f41c61046203c42080d0103808580c2042051201c0c9400351b405180c1e400070740080324580307822 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 67699651 1250 67698401 67698409
    0x1d0f03030a0c030813080901200601030807120306050f04090303060b0307020f0f0f0618030904090b01050f1c020f011e0e09070816110a0204060906050405100b030106030b0f 76
    0x4000e00c040d00040b2a210464209a04041850f40040a184801800240e02e5681c41a54485c4c00f55040c10b000b010743d400d210800800c0c84070035285d02d00c3c1c000e9905a503035a150140490f0484002250340c3d11181e5810240c2c41c0c442c0c400e07101220b10081c00c0030701c80c0500c2d0050000a18405d101907003050346465000c030307031000a04000c60007116039a0003440f000e42c11040c080e0a0502d041e00044440d00011a1605180c030b0003c1c1e0a504280081c00b0389045034580d210b83c905e980700740d2a03215002800c164102083c04941000641201c9003512808691041a02001605d424100302214051420300c10030380075040c0350307071803540100043c14400c038440222045ca40c1d40040d070b40d800c2000140d5020701c5200310f09107502d50a4011140e81010052801c00c1c00c52405070358005040c80041080051086800304000c008003521160003070800c0003c43d48580d6805e014004502896000d9030904000c50111440082a4000c8600000c001401d59080203422009056013641d119132003030103030010381e003640d83d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 67700901 1250 67699651 67699657
    0xb0d0204050d2102120d0c090312120c050a020a120c020a0b0301051f0206070e0a0513050907120c060806010504031a090615100c0215040b0a140a1d0f0303 68
    0x10043d04180b07405030305410b40440203e8481d070458110340104110a03e5031000e882903428405480b01301045410f0240402c0310b6107440e55001400b141a003e06600d0003503040362400c183c0d0101d00c00c0501c00600b10039000c0d02c4610510700710f140181d128074240c0300070500e80108095810804d141a040a441c035030001440140703250480040823000000400c42c9260840e005034103c2041031205280100041c8065194140204550300f4082c0d81c12100142c0d950310040030002d08070080500d00200524058100200002c80d010701007481485004101c140c0b02c44d10140d1500d0b441b0a406007035500b4080d08848176200504080c0c1400024000880014628004104103040b5a1f40311030b903070718010613441e1808002a0183c0c1006541120343d404640350400407003a81e110506103500b030540207202052052680d6104a1a00840414042540f00816009098943d09540e911300c89200c03c0d02c4040341442900103d00105400705084418085136102c04e041c41031002303107480c03060f030341280100341907038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 67702151 1250 67700901 67700903
    0x603030914040c05090607060915020c0c060405030604080c0109050a080304020102150606040b07050a0804030c080607030507120f0207050a061e0b09040803090f011406041a01090b0d0204050d 84
    0x6050312000303110805091004220380c01c4100c1d8240000307107080304040c002d80304000c14140111800200c0c9407d2104030703042080115807003000c4102d40403025240e140207412400e1481ea25000c0c1c070340c22000c54507220080d202900d000401901c1551210750301c0040c664008079144080d5500c80302c030003002c108248411a107181c018400d5903238900c0d10b03200090410310300000307159840c0d00c00c6040c04007a4507648243c0d401e440141000d02d50351281c5040c80d5107410b10302760008052900000e000f00812044030100c2c0212000182210400e8590070b5069094417012103c08000500d41190215258141d41040501e41a0b1020052030507159460741400c041c10240c044c1da20726143c80c140543c1c400080d003c041c4201e0308150800902c2c02980000e00306610141c0064440b683c040301013501c44400b400f54088d140a040e000b00101d083e02541913010310022908148101d10b02082200d50300e40101a81080520507911703c0300e04c0381005490121500706018003100191300b03000c08200c64854004501002d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 67703401 1250 67702151 67702157
    0xc0803160c060527030114012c040f02010c0317040b010609290a05040b030a0509011107020f09190e06040219030c06030b030313060c060507231b01060303 68
    0x15020301d00300a00031014550000b4100a01084201c102d0a844880c20100d0300075003c5101c1c0909034000041d015226840e01e9403120707011080006060f4107400c8003504040352410084529642880f840c0c0c501b0b810403180a0034002c00e0402c0c400066100d00303151940c040c80f0b0b052040804101108400c1c07034030f4089a046804e40e02401c0140242c0350805401c000800e0a40c804010810041000d50b01000301e000303088800c0038000c03a04402d41401802940c020f8801d203000c035a22494005640c030060002910302d541c482d4030304100707003030b00c0c03200741040b51300b910780150403020814040c070706110920030001d003c0406100300b910700c0382c0c0d248100e00910b55024420f000038003c0b403d05004012a010b03140c5044c20207138941500800004618498000c2114042d080c00601220040003003410b612a00e00c2130900c102480502080319a00800a40e179043d009450800c8239030740d0f000d82640c0e40c40d00c04248111005202000340642081b02005180307000b1a0700303008410282441440d42590042d40048003c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 67704651 1250 67703401 67703437
    0xb0a0306090e010209040e0f030706050a06030203010e06040c12021813120e030c03210d0204080a0c23030303010b0904060806010f06080901060e011401050c0d0917010b06030f040c0803 81
    0x42840d103405400e05420b41f25003c0c1010f1034512440075a02d1151010040003181ca8900194190045a100c00003c42d0090024460103e9101400351078100888007110f001800100100e90300e1500d100c0d403d0300d00c0c1e015043c3d01f045d881040c5141c01d400d00003004445003013095800c1e90001481c503181c176011100d5075203030311030716007082c004060800e00c0103c0000d00913401401148880b50741140c01500e02340342040040d80d0340034516000800383c401c03a002045284030709003200d010081050042c070201d8108101d0307001d0140841d00c038039812130360303261019034954020310040c8034518024004090000c8010000900c4556512066081c10001d03846410302a42a40040000a07045082181c0c402107850007007207805c2c2003522840b076003001030042560310030b1414881070741640901c08882c040b4904408580443c19100b4004100c00d0313050140d5001d04010031244260390105002c0c001c0c075004000d00783c6007150f5424001c1054100000c009889071160b41100141000003800208a82d4003040381b0420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 67705901 1250 67704651 67704667
    0x10c021309050d0318050316020303130303170a0209090411060d0f05010801050c04080d080c2203021c0201050301121106040b0304020a050d05030a0f020708010e03040e010608040c0b0a0306090e0102 87
    0x119521790071000007003000001d1a0300010008411910300d041000c002c0d55841c289030000c81d18501030041c41d08201001100040f05042e0071a421400d0280c2c0d40802c41c0041c0d0b143d0b10050305074003540c815580c11241d11004280003c80c1d120f032164203140090121800c10a00c0720000c419900300c0720010303461559500060080010a009065014128107d098903061a2600340da5444400381618800c100515000c9400c1d882030390111407460302840248090518540302c1205440280c1c03000720b100d14a464200c90b00364564140045045805855082c1140e207130440400070107842800c00c40301a600617280961550b01c913409007000d01000ba802c0c603141d28042c0705105c5050070130780105202c1c0c80000c4501000650000480b0600c2d5098941000700c58048003090786061821b4100000301d50138061803220f0f04000102410032945045009100c50360b903000c055035102404c0e90040d00c80200c864080c010003070050010005000e544c907000600c0c43c1e44601940072103880150f40100e0340d4002900310 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 67707151 1250 67705901 67705907
    0x316020a0608061309110d110307090e03041806030804080a0b060d110103020a0c0506070f021b100f020f0a06020d1b08160c05030304230c0d02010c021309050d 70
    0x34028001a0074503a6042c02c0120002e80791503c8001500303200c07a01c50b640ea2007000803800c600000c821014180b0410020107181c0440382c01414136400e0300038031440d03c00060003a0980164001f00a00c00042d618150400300004024507114140404158407504000002016600200020100f51014094118031858034100203140030f840144105819005500402d07485041804046406d09005039200d180c41401d58484020f14405002c50081c03100b000100350300100303200004002036099400c8015401c1e0040303942c1d640346801940101b1a0700301d40442c070380611400c0481400c1030045443d03d100c441d51180c68602e0b80c07403023140c1f00e54011814080d6980390707025040300504c020040d520382210ba10401016107000500482d5448004a0440c00141c000c41481c0042c94001c1300752a0b49117003504040011001d0510780d20f4088101415010f4644800303d1600d61078080140b101400b180300b0707001158400b503a118207907840407480c1c11424480845109080191348280003501d9801080c038006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 67708401 1250 67707151 67707169
    0x30c0608070203040f0608190f0209040f051b03060d051002040611030306090f13020904050a02010f0f050a26040c03110a03151109030d091505040305060f0a020903031602 75
    0x180042d54010700050024010366084141030710017034038107810640d239041244d43d1361a68250180046a01e4640c1e83c0b4500780080c1c000301820039054500b0302407030700c10803e01005c460382190380130320410451001004d003105083c01540c0001000b041500c1200d8540c0301c86007004940c1074010201c5500080c2040b58a030405000000f070301400e8003650443c40c1c0380380801c81000000b044048400d450340000b070241c1003088142480c1c5900034010405904e00b9103406e595408180900742d01185505030224061446030b100500c0b5000150f4510b41440300c080c0e001c3e07072550903401071580000c00030301d5007048462980e440300340306501854900310114694149001e00704400116079004021294041c00407034031252103203048034042040055030107010440513a031400b0380c110455150203000406082d056000484001f620915107100c1503820340382e07209540500c0703144002469038018100007800403803441c92070b9a100e5050b0001610b464950720003e41190301c03c0840b82c4035220300c0d21540040d0300781910a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 67709651 1250 67708401 67708411
    0x15010e0a0903120b12010207030201060f0803030103050a03030b0102070e130215092404050402160605130f0201110f030309160510020c1e06040e0f0a0b0a060c02010c0c030c0608 78
    0x4200141412030320b0092841c242d0048058040741c40310400c15003a01c0e45044582c0c254100e01c021901d40d1440d181c020702800796480703010a45002d42d00c0c089800000801224100d80d80100108105400c41d6016001391070b94403a42c506601890600082d50344044082c54401c0d2042541c50303000002c50b0ac10070654080038408541c6a0310180400d0107103403594881c4484039600d1501000c10b0352a19814020148641e400c8181c2142c00130420844118a0020610903588100000c2c440303640c50b485040c26281c18150041e2498840451030009540030390300014a0310768040580d4501410b01120b503140d98420766001c0c0103030f80100700012003101c5401060780500340440c0d8000c80c03401038950095440d0090a03200788255050079000d14042e91395800c07070034010710203890552555a502d0741d0003410748049544411014100c4001f50560759180304030241070400528841044c1e007070540c200d824018040c4102e05101d44400c44002054907200040011442040c0004150b810000d0081000c131028103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 67710901 1250 67709651 67709671
    0x608010c181406040b0c0105010510050f090112020904061403240708091e07030b0903070c0b03060a0306090b01030507060504060f050315100c0201020106050a030510050c070515010e 80
    0xc40d0112100304080034008507002100c03495035619040b00010280d03c55507200300c4040e1400600076000c20019013029049400071980c84240302e15028096507035200b0442030f146200000c1146811560155100031641c4100720f4005040641d100082000c4a00c20b0b044102d503490388424140061404002c80340c5010100c00c4100100007040c1c0401b010844090132074401c0c004813000048490504101e012031000d101c0380c20240b49900a54881d440c1d030858001520001400c0b400900c05034400012241c4843c0e00100c000d4440b80f5144840c1e003690006014241d00421900c4008045246401000d91650042246400315403440ca44a4580300032507020000380b040c2030004012880d0454071004460402d818001ea80c2d540e8004181280c48603d21400e80c0300120b04a2107810652104000d4400e40c800e80082009644500c100036541250f07101c014074580c49218108807860254008582000101201c2400c002d0030740d43e11400c0c400b100c0002c12207010750500400070a0300344501c2940298405c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 67712151 1250 67710901 67710917
    0x7021005010902040e04020d020105120c031b12070c020406090204170c010309020d060b0d020a0b0a110c060409020706060b1605010c030203040809040b03070902040801060f080106060503130609080d0608010c 91
    0x11641d0710f103205c00620181c81820903240c040c043da40200121510510300001e0350b00700d403034900d0f010700340d54005486864142d41c002612101d1001d44800715040d9805450722004140e50f014001c846408601c1030880c0c0150300d030207001450200713600280002e484220001d4040f9203003090114a0200703a031241904042c1840c645c50056118030584204854000b072010888200e5070300404c86040385140c000350421525140090b8282002c009010001c004d80c0c1d031002c8140700c415641c0c0d59422100c0301290b016074104420445807000741d0081ca0514405c039400301d50240e46140e10308094005680c0c01c0500b090944444041220a01c02c00900307080d581421411401c254903520a64000c113050140540c1da551a00d14040c3e400300f01d140d0040240c0d680075580c85840b0601c00d4044e09070b6102d2220488015200440c0e1803074103029802c01d07540c00d0703540c1c0c17419030f905c0c020301c1240b40d051020181c60841d0340d114454080380c40c2c01c00404008a00407004900140351801c25801c503201403604600f040401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 67713401 1250 67712151 67712159
    0x1d010c03140609060d0503210702100504080a030c091a040302030609011503060902240a020c09040b040602032e030c1d0a020a020f03070b040323090105030a0b0301050702100501090204 81
    0xa258013600003406468070305e00c011041c501945503100740520303922001e48803020540c3c2c43d450240350328821440c99003a5a002190306500d0400d0b24800e640c001c240b02014801500c1040c829481200400b002d45403a04900382d0b9a4220351420505c1d6460150100000070b080c015800c0410809800c20700e000000c10004008400f0039032005880d00004002c561030362405003d542e150390541039442d07035109440410074040004010030f44c2c800703140c240250084100b40d804c1c42c13405955003440b50340c01500c545440d65030307641c82d00001d502c01011000031001202c00c44103d412510807250701101038000e01e41d4000d00350706050300b1a000075403280d00c28000a10381c9001e1a003126440d940c01480410300581c40e040e0b0068280d007407030b2165040c01d1561001185280600c040d405555014600a440b000101d0b05d160f04820b040c40c401c107003c0c8003044410408446c6552003180196400180c004001130203000f5103002900b51802035903d00f0050b803100034444288120b601c2214010320000c0011841c007460 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 67714651 1250 67713401 67713409
    0x6020703060c05120f09010506030d08060f03190b040506060f061603051608130b12220b0406050f0606090a0302042a09030605220803040302011d010c031406 69
    0x165000040100da254100400002c1c040c50950300686070324104071905140034580508400411121013040390708140104003642804070312103042c8083c50399410700c2d035a00e40080c88036002c1c4184010350544188950070358121003181000101314403622043c00507041c0f0341042441e020b03014000e248640a16140c01405586600441e19581666458003040c0c10540c2000e40386401075980741c0c601d42000054079020044000010842c81c10038000074044c50307890390300045050003240740d000940f40d585800b142c5400708140101104405465a440380d0141c1c540e610301280401381c400700c41103a02c400c107000020b03c200715600e134440015100c00e42020b0011002640881a0b4072006e80601e5a030400d12450400f40311a21040940d196820b403451041c0d000d00600c0420b088c401503400900d8480070440d00e4010007009185441c50026024030540c0c1c03034a40b4000e5a02c0a0700031402c0d50b50729200003120051100040307800e454098000a84e500c1c0d00340e4040c042e06e0180c01d001029800c281b080002d0350342c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 67715901 1250 67714651 67714663
    0x609060a0303180f0609050301060902030106080f090309130b1e010801180b030319090b0903030301150509120105180a0816080d060e100b0a080c0d15030b0609010f0602 74
    0x1e014a031183e460903c82100c0b180152207074028500092085002144250b0010180404c8a0042d4020010155241c1c0386004a000a000d00400a80200e02142a0a0000141681000f030100950b0b00c3e02000a0001d500c01d820100441d0150740c81d81c1d004049864072109000c40c501c490b403035040010304041d000034480340c814010000d03110840d129001c85120a0fa01c44c0f0240f0340e002e400c42e42c1d2400c502d243c04d542c004052800303000284691f280032840d11446030603500c5200c0c003e80214196420800c15a030040314450214082200078070003210a0307910004805100b8044400010f0300e81080420041c55040440f442403c0381e010000410006420070301301c1c0c0000500841100004003d4a041d005a1185100b0301c030b01642081c40118088080d1000749008000ca0502d03840035036994008088a07005400d0800007140d01c04001500b0030040030028074027204610340010300550b13020030702c0001d5450364009590712040c00042000509210503041d015041c841440000c041c82c106000307655035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 67717151 1250 67715901 67715903
    0x60f0301020304021003020c07180213081c03020717120a0501080a08040e100f080105101703030406050402061b0307020909010b22060f090b01030b0a060903032d0503040b0609060a03 80
    0x951300103200401d236101408400d001d001550300001205196019000180d01710044c3d40c626010001c200285188001510858081c0f280902c20304004502c0c0040d002900701c81c13410740c0c69901a02080b01e40301102d5006000065000094030707018203158174240d0484905802051140d40320145100200f000c0c441500c00700e460a0b140d660b590b90710503100f40000300c51580000040700b00400003040d20b42064000a00c0307015840902c460662355840002102402403903802d08542040005c103011035080c0d0801540180081c003824986040402910341014080042d0799041d000450218114035008441a4000b01c00100901884540c030002440c00006440e5904ca030302a0b13000c2c0320300c401c1c0031030700540014418144102e82c5e2583d00e0301c3e40c0000c0c08804038898002407030408445511700c2e12100d040c4c00ea0306940d65003180d403810341e45d040e01c0282408a00039115444c0302c41406110746c2e81e00d1b80301140b42865540310340ba814030f03207048030716110080e0101d485078032044104a02511480d032a0021a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 67718401 1250 67717151 67717157
    0x12020a2c01120e070302090c03041e03210b031006030302150f01060c05150708010501021006030b010620070305070e0109020301060c080f0c0d0207180b03070b07020105160b060f03010203040210 85
    0x100d81c003c2c0e0081c1c83d04a842d030000350090203803410031182c04101005144140c1c003880a4841825011000e8103004600003c003d01227007020055445074240014488001000d0010000d224150031000038a0704010550036083c040e01d51100740109541413000001602c100e941030545814004555494030405020311001c024a43c0c01000c240300f420090000700000c91281c5450300d082084000300711000034080c071405441501d10954034500d881c41040200d03030300140c07000f00c140d08000c2e0441e030344001340090f400082d403c0c4251030014901400004021846000204006881e02d40101e04c10300703050344102d808074410b2004000d010b41180300c6c0304045034462030076540c4040e0b05443c0329040c00b40500400962180c0c5c202d222203a500041d00b4800d440c165806500301582040c5480b041c0c4a041c0e40701501a000400c0c200115006d14018102007881410710320300701141400c205003d130a8001003034504240c01d400f84901e50074501031003030b9603403030a400a620314542a0045001902002031030b60030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 67719651 1250 67718401 67718411
    0xa05030405090603150a0504030806030d0206041b0503030309010b032a0f06040905090d02011b020a0213060e0a050402010e010309051b13060b030603010c0e010906050a12020a2c0112 80
    0x306075814000071245c03d00d4000c0900541c00c1c02484400144030441c2c085002c89c1c0c2c920045070091130b000526141c400000d9005010f255110b0b9605000d81d10741403001d0b000b00101041c00f249994003400614803824514000240400c003c400305440c2804110307600a40003140c0b00b1a40441650780b0640c1c42029054034000710034000e680200c1e04074865980440a242d15140520100150201d81d110340240a94001d001c0c2d01000c0c0d0360007a823140e00c01811800b580c0800700001c010b080121012180360100500050f0b01640d89100d403a0748202110103108140c3c1c1c0c0e03000c002c115078100d500c0d840801c1d820702c0c0c10402c0642c680e407015594600003402d84249190030701144526504c8000801c5100b000b481e05110b41e079640d2200300e595800071380f4140d11079405c01d030b809481248562000c01c01d8000503502d19030107614041041e034040d808044444104486144040c0c02d07251035000801500c0082c1e52040741d0320f804800c0700d00214100b4010300b609280c6a200d01c2900340c0c3d1004c1e0300300c64081c0b01640094 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 67720901 1250 67719651 67719661
    0xd0b0a020a02030910080a0f0e030403020405040602090907021e0706080c07020328060b030a0209270d0512090706140a0e13060812030702030703030209180a0c0201060501020a0503040509 82
    0xc03650003924900340d44120000b44a46250341d00082c02130041f001d1080074445000c100c103e020070b031041c10899100c00d03801071008101514144d0005504240904c030018580740d1400f011030500c0c07404580134000b40c1c0c040c00f014168624424100c0c00501c000754044c05160b070a0481c000c00e8460042c0400101410214099055541c1840030103044144804901c414503001d891307000140b90001c406440c014a482c16000e4103040205120551540c0200034105a0382d48602e003001c11101c40e0304200da115065400301021803000c006400051700360b901d031035481e60301040d4411120407000b040030b00285c05c00007003004250b03009940c0129162081c0030441c1c0b2010203000c04c5440e2010100d181d5801510f2450f80e41910b0b8603a4050740613243c07a0429030308102c000344080324540c40142d0b108001640304001c1540484e01c20380c05850003982c02000c5519401c502554002c103802d09a4084942030750350741c1e0040400307409201d0203005200038009407101510680b07074581c403406944281401030304040005a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 67722151 1250 67720901 67720903
    0x804030206161205160e040b03100c120e0705090a0c09060509010201111303051c020705090604020408030c0606040b030118080307050f0403140111040b070f03020309060a1205060d0b0a020a02 84
    0x4143e020101040007145000a00f0518101c40d000700d03180802da2803400d6028600b06400341014500c000b4004000204403503000d000203100c1c00d1000010030040c080055a0417400e8081d00b808120034800810701281443e0411440d0b40d400382c01c10480707a15000e1001035184c0c000482101300c0d1303400d00304183c0f22440e120040c0d014142050408034101c030000742b0050b0112020b1042c9064a015404842544c030003002804e00c00c2c803003004008090391020f4404c118900d0306015040d0302013005000581026070f40c4410501e135400070384105249421041c01c108241c24544207002c0300c04021402407040310030070040442010321100025100010010000e05c1c054041d0003200c281c2c0b902c1c0b092160f601d55480c10700f00300248203006054040c2d400c00d080c50b11030064886c1a102525051401c0034a00359a541d00c1c40c001400c040f00803010350206004010302c95482030040c0244100544034113103e003070001c2c81142102d000400300f510448103c100080400e1640305d0296001d014940010b0780c03001c42500c1a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 67723401 1250 67722151 67722167
    0x30902030618120406110c010314160909020a02030702091005060715090b0702150a1b0c03020a021504080f060108031209010902090403030f0c09080c1302071a010312080403020616 79
    0x39074860014000905590010040504c81b40d181c050b01c194007407000045094070501209145409010408506c5d51580d0360812b81c084080e60501302800c81d1350f03a40340b0041c0d8004000510158001081e02c10940c00c100e24450360080c0740c2d00390280344030700b4100001c0d0765005009002d801c03115134032003411400700d40e0f9120000c0c1b16003003c41d01e006840d213034400075683d222079507491681d41c9540300400c4c801c40e040e00549941c0d2542c1f8040502c042440321007141c0381668a0b03c16021441428064005612568600108400083d80050b41c0d10f06102c1c1140c5801184d2400e448075600190040004074408015218451031040b8041210b4481e0400c0701d0140070450f0000c0c0d030009444061004040d010352110000e041d1928040c000b0800c101c4081d60001814440c003c0d00d0317003103801080c00c14035085c2c0010700a000c2128005007095107517258180f00e00c0703940d01b01508908907803005200344010031900c8a5081400d1415a07900d241c25039001f034560b54042c1880b04106284020400246e00620306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 67724651 1250 67723401 67723423
    0x70e181c081f050d0605090f060402010206160c150c090503070b0901050309030c2a030d120f023f010308070f020607020402130e010b0703022a0a0303120507030902030618 75
    0x20707000e400313016030400800034041035440d08024482c1035010342c0400004520284a2501600503104c00e640d4000007442400070103000004101c01c0c1e00d0f0200c0011051121650007a0303c410000074603076501d0700050705415407078200d14403c0e80000010407100d01c011086038074400084ca0406e440f9101d03100080c0c514000c03180000000d00400d801d500000e40068040f2400d084114198090b0300d014005064031010100311160010b140c420043c0428405070300100c0500c2c4d10140014904000070521900c250a241d40c2030481003a240c184040b030305641c0d803a0f100415903011200320a9491959041041e11403c00024040190030b041d440a640ea40d2042d5400c0d00d4000c3c0081d5525203180314454540c900038002c0441c0b000c00800003148440492055a0080f41e254004100c03070841743c0303600d550100907101c00c049210054541400d21707466050b035000c0250310a445128841c1003160101c3c082e210300601e480300b05403802c0d13620000b60b980020f4041e04603042404410340c1c0c074441c444160420060b80b40b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 67725901 1250 67724651 67724659
    0x19060608030a020a030306120803070c03090f03080301050909070501021e030d0609020904060602010507021002090d05070e0406050708060d060c2307020405010902070b18070e181c081f05 82
    0x80c805202a0081382542020748a90360070400340740c5030b04d044980d40414001c040e0805000740000b620b56030250844a6966010b8140200502d5941e9001e06140e0a9a0411258241c01100411403410b000c1c81c296000356512015084c01401c0130700013581c5130320350703a9000340c2101d200c2420443c00c0c00c2841211514019100b0a010050f01d07640c00c4400b952100c41840d0080340b80001c0012214818442c0724000d410984c06420030000350702414000e50485104d0a511407000f004460000b80100864002080c2c10401e1124901d000c0c01d0000407038034020200002d2045610030000181c1c1c4021034071000a82c0000001521241c114084841071350707408103080041028201c10400303e180b400600b41030340c82101c040c00706a1703c41540e1030980c011200300612590000340440d4010702c00310344c0d03103401c89516400c031400c0aa07106440c0655030001c0d1000c3c014003d405500b2010101d007480b508007140c942c17981407200c039180c40c003000300380d0000117000c1690046084106950740341c00d6030b0080001c140c024 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 67727151 1250 67725901 67725907
    0x60330040e01060f1101050105101110061d07020a05030306121c2c131e0906050402090f06090f0c0f0708030a060e010f0308030a0b03010c080414030c1906060803 71
    0xc082c0000b034070741002001144070b9000845d01c2d41c005004050581c0c0c1c01401d66900700b09505c034155801e44c920b101102481c050070f226080101c0c1c55210b0301009000030381d50b0f0707040d400b0300491607012000013804c1e040454000c1d444038000706000008594100300e0030755041e200442e0070340109081c40d80045404d074404030074001c1d0702808bd0340700303400c09000841c0300d0811030f1080c50382e00107280c00c030041d404594010702d103064500b940968a6005c207007814000b804010110786c4082001046030500306007100c0e241e80ea0f04c00d20082d41004c020003a4031900054107105282800740c00920380e840c0082601030f002118400090700040035000355081c0c040f1114500703403501914a000c514030707041280c1c03101d00285071a400080d00000e51055034100d0b0380d0b52040c10190742c2036440d8420a60b100401601029480d40c103401e02d43d071424801c207180043c8544da124080e04180c600364141b8020300d024622140d00a222500600e1808500d1500c5045040c459600033b1009152030350151020f41e2010100340004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 67728401 1250 67727151 67727159
    0x60905041110020c010801090b040207020d0f05011103040206030a050a060b1201080f0105010b12150d0809010207140a060309140a0506010e010f0f0e0709150f020105060330040e01 79
    0x28141da1400604a5245022080c000c500701d941c0c501104016001801c0500100700a0115034080944913502a0016240c419190080b6064104405040703505e1800d222000040c40400c0c861407180490200302107256003040c1c1c000408600024001058040e81c0b0004602114015804038000304132040503280c944d440c0001098403a01d0034880c2c00b90360b006042035440ba0704010320610b8180c9050300f0b151402e08514161220007054000c001c007100f010440006846030369407800000b503040c45080300305e507a200c950303000a00b4140c0035030044284d107e100406511681d124480340f02079032a03030701d00025000d565050003200382c034480c596140c1d030f03014000d814000d110010031054140d907113061041910340d90368061002e00314503a215810b0b1042d8803001c1801078442680c00c2ea9000320180c43d0040c4580e498842c805c0020f01d03101c82c02070104103140300d254812a028040d25602c140210098030f8541c90b145c410340040d80803091a801c0408460380c000d038113400180b043e10081c01c12050908139968507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 67729651 1250 67728401 67728413
    0x9090f0615030f06040209010b030703021e0c010e0c010e0d0c150905030d11030a030209010c020301151412030405010f050c0105010807030b012c0c0702040504050705210601030305070606090504 85
    0x10340852503000f40038460301d20858200000d5200d0280f580600303c1d00b40d9030701c0c0c00502d29068201411a204143d02000603600782512820641241802c2c000c1040d5034034110355184d800c45070301d40d4120b0880d130003803031003e06140e8000c8505940c041c003d54984100904614001e90203a8140e0403840c0d244079140425030859034132400c084140e0b00d007982169045a40c01d102611030150b1f128070320075103500800170b03210400c1c030030340107000102018100320b441d512603a40001d0948503044058540051050030401c00c007003401150304481c4c0000e407000c1d40ca00d103401c20aa91a845603018680c18007401010b8907089521030412103451440c0103008000d50350315407081070f2300d800c100e200c03e556080c410340011890310b600990003034030700e40c600b4040640d4010004211901403030090813410281018801200903071203c6c09001c2c89140310b000036040c0c160914041104003042c880403d02d6400300c00d40308007406000000d0340e50542c0c4d0142005500c2e2803d91404401810711904201e102d542407206100030485 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 67730901 1250 67729651 67729681
    0xa020a090515031b04120825030c1101030606050d0209030703080c060105010f0e010c020f120709020c16050d03080a020d0e0a120305060d020108131a0702070b04030b0609090f06 78
    0x82d80b941014140d51821820341031303a004038014545015640031541000620701001032194070090203030054220310b1004072000226a2100a80126004006100c1000007164591918034000d081c2082181d08294000b0310358000c2503034103621280d0004422215aa007001450700543c0d00c0b03040244d03940c284200054407110f01b0320515000c0f0f0380107201000c015004100c01446614180c2d101c2d65084115004c000c1c030010940314860300700d006450744a030000024003084d0041c111400c0007507038842064100910309010000c0645540c0c11004040c40f00b0354440349407003000c5406142807805a10340c1425200244500c2e040104914902441c04803604c00100d01007101a003e042200d000c2c11140070154103490048480a510040b46c0074880010360142c8409500034400d0a440d1400c3c20143d6101c041d1004103011251100840d8000c201d00c0d0b0380d0401481015003a5a50410306140c6035a80d2454840c0003e07207100d10480c801c10004681c40000c2081009c0007200034110707151801c0c01020450310b04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 67732151 1250 67730901 67730911
    0xb04121401050915060904110405040c0b030c070507140d03141c0c030b040e0601090906020702030d030618110a030203041e03030b211b01020a0506091509150a020a09051503 76
    0x44c0c0700000202c262810301e01e154440c540040c010003840c2d515400b04402850018021250a0240c08000c240c951040f0040c611801003411459580c0000b414064034040c290350269040d01d0406a200280780c0740e00001940045d4035090101c1886a03035a40c180e040d000c1c460100f001140441882c6200103280c2d00182200784103502c04108002c1e4900901041d01c0301500c15008070b0b03000c1d00041110b00c645070b1040ca411801000014104586d41d4006400c0281c2d00c001b080010352510300510045162103c1c00b80c1c1c10110840800a102c048421010240501e509078014542c0c00b01c00581405202d6113603121000000503d0b009026240c80c0c09002442d900c1d45844c01048010756100a80210740d0b550300320205458000c0003420f0b03664054040103500005014114007514800070f00250003000b69902824003d0091324411100e105803007030a2000030300f505155400100000d07443c4146003210ba40013105100d0269070b402c031a00e02650544210703072009070400601d003880006802054040d500131 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 67733401 1250 67732151 67732183
    0x100b04081228051201060201151e090603080903011d0709050402012001150803040513090c05030a050303060f0609010c0f02010522030c09020f1b0a0602030f0f01050301060b041214010509 82
    0x59803104007c0342201c0194407440000e40311b005041c0f140700482c0a003660014900380944d40e00503259089e04042e036009510455680c2e01c04142d40c04c0e185000e01a500e16090000c01003040410810741d10b0f03903200d91521072480410307070300d1020409692180700a014401c110040c40c00500c0e400103a01d80c020111040f4050480602d144003181d904c03004021181140c0000704030b940b205420346a0b00e4000d04a003041200c8142105800007100d440a100101185015030302031034891900c4000e110303a4010250729544220801c001d0900b850383c00407015551150441248068441c8500c016202841a804031080c3d5000b004c038111646040c5e542810103484c4250348801d03010765924242d0080e4002c217082c000004005000b8110601e01002c41c090340115007600303c959244c01901d0b500c080707900c1611440c521392808820050f1599a5503889401810213030020060380d4a007103050b242601540c060035100810664100c024068070052074102d0381d4000c07000304001d0034502d1005a40c0d400c041078141031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 67734651 1250 67733401 67733437
    0xa0c0212030c0c030c0109030b0606090a0e0f06040908040605031929031203010e091c0509040b1206010501030f0f050705070507150507030509030a0b040308100b0408122805 76
    0x189042c0443d91700b160000685954900900350741d500b112460b03000b010203402c1181440219603595801900c000101640e84540c449414251f262001000009007428001e5003080321074000940c2c202d040320212203807443c03d03e8030381e200e00c1d5101d00c087c0d144071b100910482c00c2c85500c0038170140241c151051100e85403585c42d0006100c0060603220214003c1603203c0000600040101c80902802c40d40d010003060141c1da0b003030030024100c0080555804840001400c046214129401c0078854a5050401104c500d090054a11782da01e5640e00140213040c1015103480410304071007481d4102001d0702d88015424003051600e500002e00c2c6404c480030642d42d0b03110301c07a0005200c010074540c2c06070030081e554455203441140d03241501d2075481000302c0c40d010300c07410030381b803000c00c0d541581e50340514800d5690380310a0400b06400d001a44042d084082c1d01c20341048100700c20031001408007040720304460001c2e1104602d0100c88200032042c92600b40c1101100d1031013000541c171000400440c100f0004500c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 67735901 1250 67734651 67734673
    0x1008070602060c16080d0509070509071d040c05090310090b070f020703080a09030b07020d02070b09031b04111c060e0c0d0905010f020a020a05010501051c080a0c0212030c 75
    0x1a40c2c200a48400340085400c200380001a80c600c6842c009503401a41340700d10b0140003081c600111042142d860450b03402c01c4100380600c0c982440107541010301031404500321525000104090344c1c2c202480ca1060b6036540300d510151b4018403c1c1c500140008043e200c80f608060b1104000d03042101007114400d000c800080c2c0450b0040d030f0300b1a00034045a0041044a05658810b0410781c4280d1400080c804c06000000000711208281031061140d42c0c040c041c94001004040d2820015400442d0616070521070f084944d20300081008241081c20012441028a0070100b002415207070310700510304000007200c0308403400d05030301034864012510382041265aa410101c101400a03a50302080e203008000741140541180c22a50100c0e000d00000075061921505640881c0d0020080780007503000340b44004180078003807280c580185000d4031811120310850760040080c49180100420700400440c0300fa000c1485501e05003a41d59010302650890351000300b015a482d000240d8141c0b942c8510204c0d04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 67737151 1250 67735901 67735903
    0x3904060c0506070302190503060315150306010e070219060f05010e0417030f01051905031605040e0303220c090203010b0904050702010e03030601030b180f0417070305070312141008070602 82
    0x1d9080c809522000c41d0340310070100841d840c0c0e001a004d0f40d45031003510a841c40e820b00100044cc06400e1224003110b00e004a001414200007059001d031f80b035001c500c0c04000c5825000700d6039042611003881c0203000100c0c545032002c001c1c0310a421401456182000100300320004454407801076014410320080090007510b10b500381e21040b500c0e9030280804500402050901c806051600640d8040808140362504082841c041c000d10f083c1101e5a46a0b4042005050070300c070358010244e60402a6240d0701e4006c0c0d41c44c10b889440750203d0701004807280701200380104112218060015000103550300d5a4849182c0e40079080f035030a16200c0c0b441c04000c51200d5005204e1004c49042d070030060b50944c1d55030001500100702149130b240d0425401c0e0b100e14049274003a9007243c45820004840390071030a06040c403e105500048040420f03120801c1005e000c240c100b41a120200e81c103203032444048060302e6001c8040c15840d504500010b050b502401054070014a02d10142d4159400700d5504c03a540794412 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 67738401 1250 67737151 67737157
    0x403300501030507171b060307110a06020d0b03072102010c05010c0302040609080615061614011a0a030305040506130b030403020f0c0103090c0b09010c08070302070510083904060c0506070302 84
    0x4050034802c04604100706041540145500403458140248c2184602b60320724101804080308494095001036070795034021442c401c2104590703042d030003011b10500300468801c1c02409650610300072104040e080086a201d0040b140309140d00100900030349124000c06000b03500607006080100d048940c001c2442a8005000c9100d00402c2203101d426441d07034001d2250300d074402e1403603044000051054201107640007104503e00744010f000041d0b61000800c0f00301e0280c54038550503205000c0d6038020008254070500392020b685080325070950351455042030100d812a1a40506003032a070100802061540116000350f4644080060350101c90450340110111011000000d003241c80201003406280c03102c402a254500040c1000f2800d124a47c50780c10142c0c100d92802c03801640820028031150801c04002c032682140c1d81031a40c4181004039010722402c841c8500203074001c50351000301440035501000300350b03a100d00e450116035880c0c8821000700207815001068485108440100d404e00d4442d2080f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 67739651 1250 67738401 67738423
    0x309050111030a0e06091203030a0e01150611011b0e09010806160302090d050303010b0d0b0f100503040201091503150509100506030903070605010f03050c0108040330050103050717 79
    0x3440c41d00580c440c0560f1031030135003229550009001c0c09003110365140d03c6040f03034220443c90020b40d00c170301d8441d21510944d14040080e034120b0741002e241031508160142c2041c01d0710100d00700151400001907407580144480d180340c060f0204114140306100713801c5254005015025560b580c426170b02d0300031041d40c1d03142c103403a44243e0945105080816501c43c1e07001d06440040200319660501464865134034541080c0c00502d10302200080c50000107069228a00040d20291454035075107203000300007647c40000c202103c0074414000001021a0b2041c890b0302c003c0d140180e0341201540e881940100144091030043d400360701c0e1008080340b1031801129291081030000c1c1c485050301d0074502444a40e400c050680c2e0f22510081c068500001c0550140030301034030100c00100d50051950030030905d000a1640000d050007030f06828040800c0c0c0c0101e030983c1e2ba00b0b0011085048a08200d48003ca120039001c00c038000e00d1030440040704018000c24070404403418860511303c220440315150b61104e013404c130 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 67740901 1250 67739651 67739653
    0x50106020c0a050a051215010807050a140306010e0604020903060f0603070608060a0308070c09050405010902040501120209011a07020d0b060307060503010b0415030e0102070c0602102f070f06090309050111 90
    0x4402c00c810b20b0502c4411000d180d0b080147c1e101d41000c04081e14110800323800c0620190080c000a1000741000a07000b002010701014004280d0a40c03004a600e81206000d290b2503441c0041c0021240e1701ea0b0b8040700d4001300d025044590381d103800248400401c5040d60030a210340948000004e20314805c5940e0f502030038000305150b44042c610f6540c240c0661040c04200c0ea520300e0180005601d20007880340ca0720540c040c600114dc601d03083d104000032110141c0002c0c4d602481403440d04c015032200c201040c15603502000c418261140c1d0745240100c0d004035000258000501c407141c03020030100b000098041da07402d40855060a0322948140e03120302090081094888003400104070040d8080c4a18990b0039641c100011a2070204440500ba40d008540070f482c04001c0d01800c120183e41000340f49088207045070b040102481034051586000f6807003030b40d015401050040000c0084a410845845a03800340355400040c2e030a00d4504081c1017601e10030f13404130380c52000024040d40500700c03084002000c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 67742151 1250 67740901 67740919
    0x501050909070216030506041208150f01030e1204051c0803040f06060b070506040c06090815090c04060320060703080f1f060504080c120a03081810050106020c0a05 72
    0x22051004541c0010400320442c414003040205207040c4100e550b02860290018246030b02e070a041090041a20410800803c901c400402048520382c0c5903840580c00c0464103480412070140040b00a061200d075800020b02501840c030b5194031040000340202d480545020061180d034076440000000303031071005000c0540c104000350020740d025405250b203903c1060005041a1140c440c50b005411034203089405900c640144418040d20483c2e41e8001c203610302d0615030036402c1c1580030361240040c0c41c01c0303000e00901d0008148400c5003404004a0701e54090400c010065880c1403000e003900711107045030704070f603807001c15004c25040c040102d915254142d01d4014058071000da24903a2010000d11411540e800014041c142007044041c502c010003203650742a1b161400d0480036800c04401408641c440c0c0141d04c41c5003800d0601043c440e01664241c2000c0300c0c180d95490340749600044180d2007411314001c85200510400d180d0740300b2416154668202d48501c5403810038401c18040500425a020f0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 67743401 1250 67742151 67742167
    0xc0703060b181807030b040f0b0906060a0b0f0903190b0f0606070209190f05070201060803070c06050306010c05010903030614011b2303040806011706040317040804030206070b07080c04050105 84
    0x80350000b010411000304403040242c2c5c949420004070745c155400c9550001d510580301c244071072520711940100d051005401181032081c0001c01070070842c030802210207808180117005120501c19194030480240644202056410010849503010b030007c0718080c0d454400300301da5028480581d4410000a0038851800c8402d8003000321581d002803841300c0191204a003000c0080c010300039140c1c0600d0701d0201040d0f6007041d0001a0039200c06030801d080a500502211011510b004641c02c2103c40e40c0c10090b581c1e0703c8041c0101c2e00302001a1003c4c3c20f82d828000e107001055451341c00802141c0726003101d4601c2030030b00d100440e44117005030340c10481805000000808a150021616103568001c01d2030b03018080449045420740d0800d501250300c94001c00700410900912110322801e080400e806029a031501d40c4e0081c0c4205812592564006031200000b0300700005001210301440e0014001130b100d00540c0340200d03030044200e030694001a003110100f28107004407015201036520507180e1a091240b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 67744651 1250 67743401 67743421
    0x70f0801090f02040306020a09030c080d080a0903090302090108070812040302010f0f0e180610020105060d030e0109030f05030912010c0512060613030c090b010804030807080a090501020c0703060b18 87
    0x30b81506a00c059820400040001c3c036920080c41c440e11262160f404451860400303120411886c3c0c000c440d00c0d0005401e021031300340d00040240d4495030500c1d0010f034160041c1001c40b812546900025040b10408001143c82000050b542c000c0750070000441d0405598120080c0443c0140e200082c08a00720002c200000c0c2d008010303641c0c110311a4502051508525000580e8a00e4000c101c6100511001300380015400c4c10300075030328064861f0000380264103080020810000c0707101006001c000aa1081500b107a00c03880e51500115013084d143e40381112030b8240507403a45d100301001c0c0d21039110390f581c19100d0081070140b1400e1032400d441d003e0425400c6041044425002042d40b9070100b010803503800428000303003400d809540290240c0b28014144401ca0045a20000d82c86041c0142c0070104130000b540b048809034410300783e00c0c001d906604d0341801203001c1e00700d04000420a5001040c44106c5240014001d03045a0140e10b00380020340709401031000d40f505e1f49410001060000740001d40100c0b03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 67745901 1250 67744651 67744661
    0x121803060911040f0b03061f030209040305040e0708010914040b010b0a020a050d08010f09140103170918150406150804080c010603060c030b060c0a0204150905130308070f080109 78
    0xc000d040c1d409084044100060450380b0a0802108285c0e03a9a042c400f00c3c103041019507485843c040c16551b002190018225005031603103c000c0c0f00c2c64042001904042c411010348004003006043d000b0b10742040c050191004109008000605251074104110103d000c12030303c2c002c03500201c801c021030342004403040896100e03e0313004055210302865280004d1040200c00034411107070303484001550409010141d201ca0f55404441501d0070101d0301c004100f07424510504403580003004114115210055181502030356691a611141c24810f03000c94022446000d0302c039043d514004610040504100302c00c0b80d5041c001c806450044070340592009000303010003900b060040c80d645091008814044d0300f0740d581600229140c42e150149000c05a8060240302d80001044440b9814101c0300311070241d5850481e0b03c0a4450340d142d1078201482c02c800c183e884060030300d1b142c003030140303180401c1c4200f607900d003110013240003d542d00000f924030380c0b241201a000712684c0e40c4010480e483c00641c5000f41c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 67747151 1250 67745901 67745903
    0x2121b01030f150e0109062301030203040f1b031202030a0e10050c0d120506060a050901080c0f0c01050f0c070b15041401091b020303061305090c030d020a1218030609 73
    0x1650f541840030b0100c01210300070020014044481400d43c1400400429500103078000d210f642e010000580010b81544c1c1c0c208800142031800580345e5540381480c0f00d601001480281c05000c86021440100b101081201c00392400b490000c0c1c3c4240c0d08081c100c0c5e86e44112100c0364000350a007402902d052505c00421b2820001600e05036090078800044981451001d0004c600403450401c0151400e907c1c500800354041d030202d400b142402d0100001908520801480314104900309000400350200401601c00149807080346580f079102c82001140248001d0f590f00d13018801540010700c107141014122044540d018260000b070b038541d40400c1800ca80070b5044654405c0d20740c0006011a40ba0505040c002c1c045200003051801114614040340040c1d540c1c04000c6400c00c0003008425110305002d4a0050104c050001d482e80d11b030740d40c0504040142d112158103006000002c1c1c3c0666000618190250162030803c2c2c1c0d01408050986580340e9814400b0283e1604450400106030141d024410341d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 67748401 1250 67747151 67747181
    0x906060409050f040308010803090901090b0102010f0608010903080a05151002010e0109031d0a061d0301090c151b020a12020301090f080307170f160507080f030402121b0103 76
    0xd445401c80001d40388100c0b00810020b1054081105040d80182e41c540109100d0018504e417141c0304010852100050040d0003090f5103038418107a0740e900c05d6000300d180c0c0c0c5141d1010812244c842607494043e10480328194005001d14011442c0042ca5100f0f40c0c3c0200c400b02e8081042224170b2090014074000c080800007555a107850400380040c0a002d51048079229985407220300712003403956820703118001140c90007101c9050007800840e410151211b84440c000c2441e00d9400b090744000303800341c00ca1100082a881e04003200161007015402c0810014013140ca408980032203841d03102500c80300724080a0350040115008104a080b1001c0b9012a20b0016001040e840c141da00e548802c11140c603800c8a00d40d4002003000f44403940000d07440c1842d5881d5014003410b04044008000a141c090700c1072000c3c01031111b4208509001d10110303402c10394008146030722840071007080a260f0300120303400c0e80a4541d40c1004580d001001c17500d540e2103a04050043c0d40008031600440040c03211007011010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 67749651 1250 67748401 67748407
    0xc0503040b030108150a151a0702030109080301090b01050c0705090604020409140f160915170c1804020313061109030109050109050c030f0d0c08120901020702120714090606 76
    0x10301e6010019406845600000c00540d4045502401c804000030701480a041c90900c2070345099003061000401c9419000d400701c0c01c040d030f0096440140c070034080002d505600e4001900100942e0f9000796040f00c0d0034090400c03032082c1800054a5030300c140e00c10525981c0111805104920700107100b10740102025000604054450070107038202e030004101030081400120030002594400c41030b040d4801d0303200301c81240c08445a00003a14a10301c0b4001c03081c109031503010740920383d4828017100c0d40006018408400310705004205001c943c0c07188020300c00c9014600d08004041c2481e0023164080c003501c02c034010f01c580785a11001c00900000e0326841e00c0e00010070000f13049540c24021290254080d100009503038101d0714015107800384000741c943c021b1300303d991681007445011440030f41500050414100032041891300140340d1151165143e181814a424800a0380d0154007400200f442920000003031100070000503545d0b0310610490399005c8c11030103066241d04003840142c0c5c110b94041e14183c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 67750901 1250 67749651 67749659
    0x11b0c110f010203121b0a03092303090904050f010c090e0906070e04020c101a040f0504020303070f030504051c05251404060b070303051605040b160515070201020d0b040203090304060c050304 84
    0x4165109608100000340c903105044248400c1e480cac2003103c03542c00400d1100880c1c0c10446140c4a004904945204180300340010b0240700082c450298500e4115000f004040310b0385c540130348105143d00070500801500350005940100000300203001e4011510743d01c01107030f14203041001a40c00303050701e1400307402441d500c2500c2d4501c6026500d17405041100c888200c1c0015010700040b6541600e605040758289001d002c0542c5000c021600c40a400c11094525400b0784d040c1a03038540703e10f502030384c0c1060207201c0a0880d924108556a0840e2041044e2140300c54078541d40e8a400b500b001c1e4540f000c0203030300800c11002e41305580c3c68110035006007000c54910351310a042040c076002244c2c1540402c2d1504100280086d08444480c21060700b42010380c14a820080160010300511290110901d404491101884400c000780c2c0014042d140c000e01d541d140081e0024081d40018a12000c21800c101102010349054020340c4e11881006c8000c40c00e042c50100c0c101c079504540101928680402c2001107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 67752151 1250 67750901 67750951
    0x60a0506011214061c0b04030302090a0b1303110105270d200a06020a0b010302010309061e091104090308161b120207140f12011b0c110f01020312 64
    0x54583d9070981c1207481c1e0780b40c00790034400482521031381c2000c85150b01c2c80c441c001881403c196a0403641500d0300603103030390741c92000c01c2d0321251039000920780c0c2901154550184a02c0180801600d00c03e800745208008194019100b5001d42c1b042c0040c8400030b06822040c40c0071001016444e940002e049048511050300e8814145000c10b04400c01040002c0b000101400c21100e0300000300304c24401049540c0c019124a08221018000241016140c11018041c0000c541000030402c1c00760103050201034003400f0314001004c40c1c9404a804688580ea91801460075108040305182c041d241d04a0990b900007258044d40d069130300c10014400c8c1400c0d4100500f602c1803440382124450140403115403480b21000c2d1802c44940c2c000060712001c043d6800c4141c0b07810307800a1100c5003d1f41c4222220f01000b116501500040c3e400c0208044140942c900e91a030148800016a01858044442c280050300f03120202043c00103060140e03108101d82d10b10454100321f4181c0c003215118510040e802d04000311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 67753401 1250 67752151 67752161
    0xb27010203130617060a0602060708090a0206040e04060501170d0507140106150206091209060c0c1e12031e0a0e10030c02060a0b1c02060f040b03090607030905060a05060112 76
    0x200091301800f482c02c18013007030549454008a08407108000a498842c2c02951010000e046030308104101c5c1c00310b00c031014100301c02464940d000f040c0648507511607514205420b8112015100c070b90801c1e000080c401000b80c07108401d02e80d400040d18100a40402c00c0c0e4031030b400340310100c40e850340841c0c040400f06802e00c1880e021703102210707243d1654020154001d00e8408050b10030183c54000c0c0f841118401c0c011800c03501052001c3d5a5551a086800d008a09000319029416007004081500302c8074010343c449480d0840d98201c03103804007802ca1213101d56890280c19560621100071107a40c0c41c003800c094000c2c01d480d001500e40b00701110344003c04038803060301408415000c01d85540180c5906074051280300e40c002c415103c104009145000001c40e1562520266403a0052a080400a540703601e000c5134140e000100034140e40b2507071200810055802202e0703d007031600507980810221071080c0a685a6250030800604903034480078407a50003003001801d06c034103000170300e2802a40204180a8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 67754651 1250 67753401 67753409
    0x11060a1205010603090b10061e11010c02010507020f01051009020f0d06080616020f06041709030703050d030b03030406080402061b011407030b0607081c09050f06010504060b2701020313 81
    0x304005c500c0c0d1038003085640002d030040301494080380d0103014556104150422001e4152254441c1c195250070940e504c9082c90480340b40c40d42003011b0038001540541100b80103103000c0d82204c4280340070f17071410707400c0340c0c400e40b80041702440c0300104010141c1c02d130b005130849018074100f051400f00c041060340704a843c2c90f84490701a400c50020040134543c03100d0084041c07016400501f0800c04101446130b00c07021700810050014080041800340401c1c803005650554a000d4121410a6201e040060f82d030811240703294006410901e641c041404c010045c0d40c00c681c21511b41c03086a0700c940d801c111103a00403085500030043d4a10030040d0848003402021002d000302030801e80241400f1038002e0a880c940500705000b48003c00400c0002240038046581030b21903c1307058844c0c011100014005051300740b078080d0039031113464001c206c00140411400c0c1217410880301044010f80c0c5071004200d500407402d8401c9000b0001401c00302080d10312480c15039107001441568a013042c501030a801c082140c1d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 67755901 1250 67754651 67754657
    0x30c0307030f0309050603190905030c0a0503070611090919090b01060e0a050109080a290708160305061023040909050c1507021009090c080a1811060a12050106 70
    0xb200c40103041d0807074080310243c00c0075100b1131b25603e01000c50380507052002c4032655030b8950302c0d0100014404140141d80c0c081c400d05e411b8803130103522800c00c00c2d03882c2c00034003040d1140d030b2a01d0b003110303040c02142c000c8403491100941007216603928403100c28100c1100b07103003034403040352101000b9001804544985011305025181e00701412903410a00c4840f80240e040a810b0080300b110a0041d001c0c0002c0d210700065100c03041c80920301c00700a8040c45400c56409144c0424410001e104100350000c0c080c5210705846145040e01d010300340c038200c0a5030030954505400034064090100414801e401034814000d951507203040c10350f920824003049510507844103c9450390382c0c5031481041024400a5a4440211003166296001d203491000740c0c41000f0f0000d120720b0441526218a40c0581c0040004003c4420104201f42c243d88000d0a2040304494400c299403803d02110010307100f0700110a2419000301100680d0302100003400b48a5001d069084240710300d190100740403984034007075940a014181d0f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 67757151 1250 67755901 67755923
    0x110607030606030e0a0b010b0c03040b1615050106050706020c010e0d020d0e0915060304020a0b03161e02070b030a0605060d0204091508100504020f090403020c0f04020a050d0b030c030703 82
    0x301c00182201d101300f0b00480581c00c11840c210224044941e0b07203055600e165112552004402c0320585544555404083c00c104042880c0c51110702056800e0143d44c041c0c40043c81e49250030043d04200c1d0424007490f004642e0074170252010030102da001c0c02c000200c100002510022100d0700038038166805081500580c06000380c2042107a128854207031b40314090300c00a0481c10913071041c802104120102134010344c0c0c08800101555030716154500140310f00d40d42c080d0740b0700f0501c074120120807a081c1c80d0000b00d00c00c554000b12690205101901c0416681c1c05009098206103101c0c0135540050101d0840a0b183c04021079560340d918010480d200600d0401030742d5919100e0341c40161341841c01484608007000204215044010481b02403280d4140300025640d84c5c2d07480022520200c0c1e019054201200a04202c20950001540b0307104000803200d07206104a0881000280e01c00c4000344070000d2020300c43d403400c0f010903400c80086000c0003020786481c41c0700000400e00e8a040d9510a4845c18005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 67758401 1250 67757151 67757159
    0xf120b1308070602030c0c1e0d03021206100903020d2108040203030d090c050303040801090c060908030f0a020703060203040b0f0a0203060f1203040e090303010f05030313030f0f141f061409071106070306 89
    0x1c100380c55a403030503410700f58103040400400c0d000453307004101c0d070b010348064000352801034400d510311005035900400102000f030490070450191184100c1c500a1740300381442042002d400760030054800e070382c020004d41c070b0010051031000c041c0c4060b000845c0d5140e0303600c07408070300c2c0e540c2800030b040070302082c0c0d000241e08080b42c01e007c41c0348006d55120b4000d000c0402c0382030007140000300880c0c050758200d81310075688447e001d00403890615a64400f52145101005020811082420090150907030070a186807a44600120f001248816203081e640700807042c00c417564501381501c800441c521844180c80c14a070343c84940c41006176040700d10000a8200200500210045400c000058007043d4000c41c146116241142c1c03403404c03980405403150744801d812408024660054070740c200e500132075650410303140482c129070303542d00310f900031040aa040010790011026807003a0401c5030103280c0d01c0e48101e0790040a12001c0318011f8030940801c5541d8001c14005c2c00108901400b801840d5800100d6a10b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 67759651 1250 67758401 67758403
    0xf0a030e09040209160509060d0f0c1701050d050a02100801081b10030f02071506080c0414040201030506060d1a01080612150703060f120b1308070602030c0c1e 70
    0x301040d09204a00200a0002507104c0003a041d17405800d074000b000d0840350f00312090312140035001280da40200002051100c41c0304a0b0014403d0a014820500caa185408001d40c1d022100480b40e07081005143c00401651914582c80b05800340900300380c400b07041003900460300042400d211a0040b420b840e004219046040161900d408410442a10300c84a40d00000358060f40c044584002c01d034a0b40c1c0840240d1446604940065611804492410078240242000f03031880d44503540050048401000103400c142c0960380c0c0a01118900c03041669450740107400802015080c4c5420003011f000d13100c1c02100522170b00c1c1d0425160a14561b540d02242c0004095041c01400580503d8150200c4150280d00180c2020728600018440460383d13154001103000301060750003642440040c00e400034a05400c5840b241286010340c2c0c3d54070b0346586809015010b065400310041c07180108000300c8002c501e1030390203150405540304129107411106050a440c0c0355442007507502e0964590000b42c00208 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 67760901 1250 67759651 67759667
    0x10806060d030c02100e0d031706010201090f1e0b010305010623060706050408090604030606090c0c0503030f060f0d12080901060f1403030408030408031b07030c0909060b030f0a03 79
    0x98211200141d2040903600180045002c250007801120410901c0001c5030144650741c0c00074001820401c0c0d412010304009061203d40481c410030308020b43c010a24551040c000d8202190f000058110040c20b2a69100b1660001c89510b80c0f41c0c003000759054002842c2081e1450085004000100d080c03410600010b4038032100354202e079101e007101e814040301500d5802c103541e04a5000030340010107580c4d50a1a010314801c062003a9406030000501108200e03655101d9030640d202e5070400c01049151f03032001c2d113000200c40d60182c100e07441400020f841090842e24107910020113020482c481c1040c10214050780803003401256591003544144604950181c005644000004000e10800d860b0024424020940d402140c403003225041c2da131a0141c8040084a00401140302280d90780d69071001c507240c80c0c0e0050310700c8a42c08078161038005014440001c41105417600a000e010100385041c0300c400007048840c0b000c035495611419107801c80e6500340f241c445c40302071180241c100000e00e4540100056 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 67762151 1250 67760901 67760911
    0xf030c050105090108060405060d080334081f0302042d09200105190206011d0403021218030a030203091914040b011716030f0b030607050a0c0515010806 67
    0x30b041c08942c019a9000603420b4014005070b800252544522004c54003c4154980241005400000707101c0302007601140c0c200061070356282980c07190310b041542c00c074409058441c040001c2d403e4011071400b1018101c503422611009641206850303482e804103041c0c9040016007040c2038450300da402140d412005c001c0700008403010040200c11095500e12081084151910006094101600041e0390280045454425408155001000e501c503002955030301c0174000c0d2030b8400c9145d1580151801d08101650040da41900075028080c084507180800d03030000084440d0740c200c911000d003140d440900c01c000501c1e004ea4080d40e40e45a003d03040c060110403404c4001b400340800001041a072040002400c4031030703402c640c0032071042d0714000100c85d005a0900b10351600803030340043c4103061704000c0c03549005242d5a04c042c4840f56242d00d0344030480c0d8a002c001d603016040900010040361043c0010090baa141c3d08042c1281d849030f880d103a28050030300d284044a100781c0801030000310307410401150b00c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 67763401 1250 67762151 67762157
    0x3150102030901020706052b0501050406050904080702010c080d0f0b010f0f05030f2502030a0201050a050106020606150f0a0917011b0e031203040b0711070503070e090f06010f030c0501 81
    0x6102100000d541300c6280c4100d0041100201c0e0003231018060f5030407546110142d150b869502c1d120340034464000c01c028460248500d1510000151302e04000100e10710454114086c0da007450015001540c403141004804c990702101000748800d295124824100301c0b081c801000225144040d00241a60420442c21000e1011310440d50301a0703680301044a510010313481c11007800e511070a03840524403c120327500c84050714420841d1b41c0c0d900d41c000054418010b013540284150346500d240101110000e00a9500681007100050303011304106d4600b0384041908000d441c50180403240c5035000380c1002c0c1707842d40020b0740e6000801554965200000c4807071801070080000107410b072000030403010380354511028002c1d49a8030034090740c0e060040e11101040d010800e40c0d245064640f006029400321030190104031000c0e007a015113a0b001450304107032a0040d00a01005090910f4411200d2005000b081c0500c14640a031050842c2400114001c0ca11b1510741e0185a0541c079154080701c484c0d411903810 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 67764651 1250 67763401 67763407
    0x903030b0306100303051305040204061e0309020d060b030f010e0a031404080d08090f06041109090d0912060216030207031202010b0a210501060b0c0705060412022b03050315010203 79
    0x803148000099000c90f031745410566070703401400d04828100600d981c4481e52007840400c00041e42c40e00070741201c0307880e420204041c11044680138298200d62803400040d401c42c01c056034080020b9001e900103810150f00504803400b121400311042c1c29502070000b40c940c1d5801440c506400c064003c0f00f207070070400040300018105400c0101c038946e0f580b00c1d015100d04020322040455110001400f030450300070203001c10b44405103010700f0400c2d00d808101c0b860a004001e010f00284c0c403030801280400410000c0d9540700c0300c032803400d00c025001c940410000e9414550812010600030700500600b146907100c0c1d00900010352039800c280d0111440f070103544065905100040c8859554114040c0c15078101201c020051203441101c01d42ca0707100240d005005618001000c9004800c1001411380b41100500300c412558558051100d01c3c0258451543d130740d070012a0010040c90608040c00c510650f00010200c40c012449880e882d410f01e404081d40451400014401754480110240842c440203000942c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 67765901 1250 67764651 67764661
    0x2160c08011d060f0f10080604030305010e0105061912060801060f090c020f06061309080a020618010c0206010506160b07030e070f0501020d0c03181805060301060b0f070213020309010903030b0306 86
    0x11300a000900c2ea2243c40105400600e5400340000503c0142424030304441c1245054940039006203000e00a04030004500000010549011402c071081103219400c003104170300745e200094601031001a00101c0c81c44c3c8603200429803020910502d00141061444040700610303002c9a18100c480c1450f0741011500080c1100148400000d05540c01c500f06480c2ea800560b9000400300040c005600018690700000450861140e40040e03410700511401c03507a4000c850803a28460300300d80c11000e0b942d0141e00258010400791402e107000d00211084d004014221070081e54401c0000d9200f1242c41000c2540c4040018880108000302c0015202160400c04010704200010f03555040c04e040a41c00c0021021200c01098421152109001e61a14115402c961540904004241b08001c4004814a4900010720515050090000b12803045810320726003c1c001c1c022084580c4841c005a82045200b0482c0c00030b100c1e01d10080d4407803a841e5000250f4440e0030700d00201541c2e48100024030a174040b6041c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 67767151 1250 67765901 67765921
    0xb01030603020307030809040b060a02160503062a0f070b040c050402040609050f030a120507052b050a09080a0b22030f05090a0e07050310060203070c050402160c08011d06 75
    0x10040d00c0e00191b03020741701c501a80015010b0502254001e03000503001c14a5203100d50002a0707103940700d003101c0c000d4003d01d8a40051587d6280101d9a601c00c120300004c10000092030725440c194411003000340a0b241c03600d06001034403a0780c82200d04944100c0e56008005c1403210012615000d410304403400c0d480d05180034401003110106010f241d00c00c441c0503200c10f031140d404200300c803103241d07000d540c1100b101500c11014106400211040d1480d004456000c0000003043c40c0c202d040a014580c5540a08142c0504482c0d170380001c0220002c2c01034140340882d03450002c00103085c54900ca001c54030054a0315034a030040800b84c1910400c0c4802c010382c0310000080e045500780254015900d08180c0310880003000402c3c1041580c40303030303425940300784c00d0100b1164404d00451054102c600e40320070042c1d0799007040b0791300d11031204043d19040200740b0501c4640344c550024008912400341c0ca403010009906c030102080210340c49048a03030354444090707200743c0d8001000b00c1680841ca01400349881c022100d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 67768401 1250 67767151 67767163
    0x712020d030605060315040212090c130204080d11150901020307030c0f090612060905090d0801060216051905060309010b01030507030204060c06050406021210050117070f120209060a03050a0b010306030203 90
    0x82c500d10a0340003880d9500c0e1242d50542718900000b54a120403410200e41c00c50321215000601801009503019500450f400d0707000300c0d42100e007102c00030b10144000300303011074494640110342e0240b07001d003940301031641c1d03200c4468501802c20700e40010f0740d80c02c2c5404081c6c1200d000c00e401405000e1364901807070f0000d406c2440c1e4012210b15040040303104280500c000c0003002c864010301e660901d00f405020028800040741001c40040b915125200e90322500140d907140c4d04085124644512603606101c58207105808845642d4140a0b1201480d210717070010b60150400ca56441d0940e658076038004166030705020311500455030703060440c03409080031401000c4841601c07003c0d150740c0c0c86002040811049504581c2020712040c8043e4480c00d00074400c100c048a28480c2500040b002002e003140182035425880c01484c2507100c400020080544c1038031014446a800d2a00c29406d00942c603181c0c0300c1500030704a001441c2e600062130b18203c010101120824141c480c101480c2440c00d10041e00c0c00100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 67769651 1250 67768401 67768411
    0x810140604050c0f0f07020a090e0a080d0207020409150c031a0f030304090908130806071d010908030406020d0801090e0304030222090b0103050d02161208070203030712020d0306050603 81
    0x4651a5a0801d5416003440350081100791248000703020441c5c42c443c400640302a13442142c8903408141d440c2505804d40d09005800b40081d0007034801c0c5000201400000d20803621805c6016007440c0542d00010102d80050a0a56414203041030000d040310a41c810003240f0b0002d41070821040d2071034002000c1400000234154021b50024070000c0099504100741d030000c011164052110090919006403244c104082a90300985000008180410b002c034041e8464010303903640c0001031078808528800b00b0b0b075404d205414441190000b14800c48240002c002a000c15001440c5a00c40d40c1030050200740160303c614040c41c07800d902c940b854075011084030203d031b40440e45107003c4444400c0e2101f4075240000e04013405032421040008001c219038034207040303a0080c6c0554044000c03500082e40c40d130b520322187c04030203403000700709100b42c0134a41d03030064101c5d0140404a081040950229246074015a000d8605514100354108225070401c510959001140340c184441c51501c000f00d0054040506 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 67770901 1250 67769651 67769659
    0x50603010f2022150909111204081207030b0f0306010f09021c1b11010207020906100909020d05011e0312050906070204090b06010201110906070213140a0608101406 72
    0x5030701d000106104403452601c203940324614401668900204c00d01c512001c0c0c142000c20400c2c440081e402a043c4602450903040c803954514004100000341d051440040003101c0800382030000110311030007880c0c1c4510a40d17031501c7c0022241e0280c001c1050f903424105c0079a11a0f80a10700500c14142c1c68900801100c0103140c0c0961180c4250304101ca00249036048440d040c0d140a500c425100b03000c160350354507103403140c40d00f59413008480c80d11401e038410348601a401c01503110106601e803c0c020301c00c01e203d40043c070740411720030b40b19610103061340e201d040588000c5450f60010f1211241b525981ea010034488403007100400d196030703219440d194001c02008140480482c90790080d8880008503610329900600801804e103071460040141d035000d40d44940103600c0e11409425507402e0790110f031400a401040e00307007084125420080d10480d40382c0806070385030b104c0d00200e10342e44601c031015025002c0f030302c00460341c42e003800107040c601103091210191440c10802060703604101c80407003e801801c159 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 67772151 1250 67770901 67770907
    0x3032a091807110a05030702040606030c0c1223120609010602060406200c03120604020c030d0f110f07060b0603040b0a09030e1011011515081503060109050603010f20 73
    0x4070054030815003010f01264030307000c2c50000004103c4d011006140c0248205e8040002540340c0c0c400300d00321100005140080740e150030308600450343e10320844500300e1310351400c010a06280c180203040c0c90380404006a5000d00405d07124080c002d2211050307071104007900c80b811558503080000755034000c068409400341d691031a074201000700c1d0f0b100203000b2080e18641c40340d99442e5446c45903030b03e41c0410f407a10040b0718840042002450715001b25262a00c0b100d00550901210390b2541000381000180c2d141781d070b0344d210107101900d920040a484200903181c03819840c2c2e10a800c1060a07208a0180b8921600b010400c0100042140341c105412804403130300010300102516060300d031200028200c90303003d8070030000c1814032a48071003401d4910311800000c0c00f80c0302c0b40c1c3c107541c00308945034011655440c042d1000c01c003c40d1720524107540c4c4054030040a107500e2990780d010905044080c1c003c01c03c6580c4030401c01010382824010a007400021140c02c200d0002c04003004000144a01e6801903804800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 67773401 1250 67772151 67772161
    0x8090a0807290c191e0b07030e161701020c0601270b010c080a020307050a061505060f04032d080310120b070e2106090601171506040e03032a0918 64
    0x1c42c0c21200d44011744038460030030292134100030015070710889001c3d000a040c60346070700343d0b42404901a148002002440c580c0e9a00f4290354452101c070300840407489650034004d00c1440d910400500d8000e1013100d00d0b601c801101c2180b084c14445421a5043d0380a040c9454240242d903c03085400c0720541056016031207800d501c071f0407411032003664005000c510490b00d0440a220050740300c0224000901c54003010b0907542c3c1c0502c0282e01a130000c0000c050014003081001c2038180c05a0603410300d481400300503030b00e4047d02da46c040c5000100c0544000e80040308115541a001e100d0300080d1298041c0005401d610342d44040c600c1800030000d07806c10a40040500c101d441d0035001d03502c0192402a1030007035080b00b800003079032007004861446035841500300001d1440140e0070200191781402c005050b044a050803880c033390785d5010302041e42082d6141880c0840980600286000f90b240380d0401c0890002d0081c0716003403682d102507030002502e0421264140713a4400342080740d25801325581050580e12 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 67774651 1250 67773401 67773413
    0x2010c0503030403030e06070e03100f14010905010603050c181203090402040306050a110c060a0b0d0f150b0f01050d150504091a07170408090a0807290c19 68
    0x208000040203031102205101c105034040c0c00007a0140a0901101c1740b41d40e5013281203410400210076036425401443c099070348200c440d046021520004000440e80880400d00b610300768034240e2000e40d40380d41d103d00600a841d490b020300c1c1d4110070900102402c1c0210103291081000c0104100391080c2c071404c1c03d00400711000e0045d01d2031108020402c64585549041c500701074141229110401d9190a240c652100d84100c01d40d0350500804000300207590f50885410000c000311040d043d0700c600c06016200000b000842c0c4140c44900c80d95070003074070300c8040d01c0d43d900b5160080c4d042c0e441030040e044d4101641c0d03400000d50f2041401c0f05030100781805428003219910300c0035048181c0181c01c0c0303000be106120f4508514240d0315407613261040143d41e1003030115000b4250907100e090300c01c3c7c0c41001c5030102d020500500341154005000718119680d03108540d145c8004c42d400303401320702c4c1502411098459100300042841400b400c2d0b1525006110119588482250301c1b1005402c19400340e480c00c0c000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 67775901 1250 67774651 67774667
    0x5061606060b0409061403060c030c03040c0e130302190201120b011101152c0406241e05010c05031219050c13081506090c09221103010605070f0201 65
    0xc0481501c0d0f03a2151180205805400700f8000e8119a04052a0500e903c1c100018018494409110942d0440d20b44040c1261607600180098403802c0000d0340c0491002140e9094a010f40140300c001550300800d442e0190612030030010720761650001c03640c10009030342c002900d0800f5001c4980002841e849560042c0c6511000780c1c0e08a04540c038002d00c88a0384081c3d070445100781e6a006000c046e2483d070507001803000000c2c80c2e820451101c03400c404074000400c99040940f800e444800440c0e80c00c2503070a0a140c40100035030005003100c00700c20340040c410700c180d00c00c0405000280703011101d6403115101c00d0350b02d1040c8941c2034070070b549000019030350442a40314512403c09030382041c01541042c14550045070401520380401080d030100001d0000320025880000b200f41c180b079190956502c60411695913002407004000c81c60404c51100c00c2d40d03e07000600b0302c05041008541101e40b107440360f0381c2233903544001d81c01c601c00d040006002c0c594004041d106800e62002c1001d44851591004a500103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 67777151 1250 67775901 67775909
    0x90702010c14030601021f06080115060504090203130b130b01090c1e090f08060712091220010c02030403062f030603100509010c02210412050a0227060405010506160606 74
    0x861618140000074055040070044270281d000904c000d2085c0107450b440c0c2412840b41e4004650200030070040c00c102d0707402035079120800c0394000301c0c600c00603103c9066044003107628074200b0740f070300741c1003400c1003140c08901d4058031100d54108403040c0702c81343c050190440154100c034002d0848000102032031107a10040060702415251500b01c0e0b940c0c41401d55500c01c181c91641c049250700311031054007440d51050300c21498011020b04a07801000a00750f50301b860491502041c04140010100007460074015094050310b20350065075250320351b00340703c5c1c111004130000601107a125161f84100c004400698170345003603c00650307a43c03511004002032800010200030706030b00313041c401000015401944240d40505698081d2020840000b40421044210420b030741e05525050000f4003115002c0321742004003030300c24000c4031105142074002403440340746401c900820600302200305e490001864025500b102c01074078103001550409000505c036001c1e17542c0766244032074006000350602a60707803c01c038014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 67778401 1250 67777151 67777183
    0x806330d030f0f020d0f030f09020a060207031a040503070b13060501240206010b0d020702120a0501090218070212030408070b0903030106090b030606090d0512040f05090702010c1403060102 83
    0x9900c29180180491889900000105040c001c0061500b8004980b48040e5403040d03803070b82c043d002c0c8000705600601c0324520302c0f45400c0d99a0b05200058035001030800240c06980c004018040c6180781003000380543c009520605000681840001a800019100429071002c15412560f40703050a00101c2c81030440064103281c104000010f038108030642600c00131040c8010079085411304201030f03980351406e10843c50001020842200004615406004091310080000b150682c0004001d40f0340304460f001510265590104207046181040fa030405410407140343c9041d91621100207900c46030714010310344144000100150800c508101210070f01580504213226500b0482c0c1074643e030f03400074001e800204414070000305610181c0e03019a48142c4000f84140c1c40c04440c0003d00c01510030100c4100d80c0c43c803901701d200f461640808040c002410707a1010340d4450a10f00b00400002242c042c01850a6902d0700c408140c0381c80e40401740407030580034202c00c1c66a940740c00700100c0c9802c0300d01e0064805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 67779651 1250 67778401 67778419
    0x1060f0f080a0b1b18010f050c0604021c020402030a02040906050d03050319090b04120e0f15070c030b1303030c0309050a1b090606110c030613030c0c0e0a0b0a080633 73
    0x700c1c00508417400345242039072090140c01040b54240c07040d204501109005d81e10010000d00140350202003c0711207440044065039510155012030140e800c2a00c80d150001d4001c0340902202c051031080c1c10040c4400c40c3e80441c03440c065180a0218403015000071040b007000880420b506c3c5c4d1980007001801e174042180601ca15103410119001c8210050250010380e034400b02c0803103407400b40300100311903100400151850300c0500c500b480aa004803021070368541e880b5000000304501e441001e1058030f4081e2000070203801440c1c020f0895464000b920203251401c120000404c0e00016000d4003c0d42c40300310708400000b117450180849020b5800011000c0c1417107004580e00c1d9004034201c43d40b07801d10781100c00c1c200f00481010303100c0748202c174040d810411031104030300400c1c4140c2c40f502c50f1a008913900c503040d41c0c072100c004048a00458001c1826a1102c00640d114284128240c00504211010301464240f0981e04224060348814020384606200310f000a00303591091010745a1100511503a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 67780901 1250 67779651 67779667
    0x1180c090f06050901021608030f1b060f040b07030c120207020a0302060a0917030703050f030a0906060e04050607020d0806130615080906010905070c02040c2001060f0f080a0b1b 78
    0xf080743d002050031401402091148103000f82c20005c1342c000c0c0c500c03403000303503081103e124a00c3d0a00c1e0400800d0000c8030302400214481a802402014018080504121305501d01b03070400703611120001d0140010180340503910516951300090007070590146200150f87c0c1c0000e4000160035881903000079600100014020300442e40004180c0c0849c0c00a16844c8900914201c0060710f9025034100a400700c1d00801c0000e840303012002c011030344030300c11240001e8002c4803500c540040301c03000d0b001401400400400c7c0418800708200a980c468020700c0102031a4140d80c1008016034400707840705000310490041c50041c50229000600a0908200606d105404000c0300400c01c800584520600e80208800031074122810702038240304001941b25044248100d5080c000102404d16980c3d040100c4001e4001140880010103c0d02d081c00c1030000ca56281042c4003075544007800d82c080c2c40b01141c0d001007003150f800041110718000350403800b0a03140da0340d0310400e01074260326448a50862080040c40d48 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 67782151 1250 67780901 67780907
    0x414010c0b0703060f060203190804030504030c0803090f030f0a080904140f0402040606050703090302060f0d0216230c090c0903030a031401050108070e0f010212120103050c030601180c090f06 84
    0x130210f40c04901c0450b50130369a02e00903610b0b441907a9034070781380e040f402411140c07442c001c0001d80c1c0c11070f2117480e10740c1c501030ba80d898000360740030f0b20307040301c0059040080c00000c1c40c80d00620340c02c002d0710110042c000090702089541e50b170b452070510041241d0804581c3e81c43c0c542d600d50140c42041c0880815000624241e410170980e003100311022031042e8503000000c0f031644c0c820401d41e031318254192903030110b0342d0640c0c00304001600010b21502c3c5000d401c01400a43c044903001803d81d80f00040c0c4100441b620031318000041e103120890541c58020000031103031100d5030008400e400041c0541d0301001c1da846031040d0039014454000c000d42c02d880005000240c0f294141d100b5001000f40010b40d0407940d80350001141e90038800d50f40900058071504100d04e0740d10341100350000704a8140111400c41100150361181600414640340e50b02000c88010018004244101d501000f01200503001940c14803902d03888500301d080c11681f070141c2c1d5000000700d91307010340030481c040c0c503103480450480f0303649940c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 67783401 1250 67782151 67782161
    0x1803090d11090705040f06111c0203070308181002070206070512030109060801060b030c0d1506051209060103050d08090703020303070b190902010504050f0307090509010c0f0804080414010c0b0703 86
    0x45010b0201d520014562921501c2501c3c10717070300d110341d541200d24507002c000c858000902060403014041c540512200c0d07001141107004e088140e40255486482c1c6080250040b10010701c00000703592024400200c80c070700452640701d4038421810047e203542850002c56201d000d510002405881601c1e440310141c41900c000d90704940400d402880155201c0414070300340c13242845010034596081c804100ca00c020300010700034041d400940041c18800c80c044c201c0714018a544080085500050310941e242e0340c180d4000e40c0051001d0040c41107500d10355034199900072170010340040111000225403240000e005c6000111b8004048035154422404d00e20360041040c0d5182901c844078840f08081448a40615543c0ca074050311080c0c2170a28040c244441c03070513001034203076150299407030114465909108943c0180050400001e06a0700c2d07240280c522000c0c41088400d0251480800c40010000c01c1181c0940701e800e81c0c140512016200141c42c050071081004014052450030400c6440c1d040e400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 67784651 1250 67783401 67783433
    0x2030108030c250303050a03020d2d110331050105060f0301150605130509040f030905010c0f1106070f030806030d0f0207030b0c0405060c010e01060e010503061803090d 74
    0x7503c010083c04001c100c503840b1410390860441c0c4109034100040390003440601584290f80c20003510b44001044004111601e4102c80003c0c15848580404582d185000b102d0442c0f10003103040041b20752003401c1c1c00250000400030710b8566007040300c6180c9040d12040b1417500e882c088031108a0501e0a1030218041c04044421900403218407012203804d15050064850303807000307020300d052600c0c200402140d043c0d0001c442d01000d15a0322500040756154402528450781c042d00d000a5820004d25001341440380c590700550410004000c0d1030302080090244a02903980080000716410203c400b0400501412801403c08050a00c40e0024107821214040c03251400328141e800b1607004400550300030031106000c20050b40416801d0000407942085250410f0310041510b0505580b400004c1243e030101c400710a003070b51140f06001544009000312000392420030503c504960500002ca940c0710002021800411000c540b4006035441c1402150b03440e40c3c1c050002c081107060f908000390601c0745114 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 67785901 1250 67784651 67784653
    0x6020106140f09070804020406051005040e0a020301180b030a081b060105042c01061509090608190b0703060905010909021503040206071b05090411030c0a0e19020c0102030108030c 79
    0x5075100041c40e0407110500c0300c0c40d00422002440e141c0e40701c101c0d06038100400c101c0e081b80d6590303008503c45c0c0d2103100c40b0400107125543d15a8560a26100070b005c202c01501700c807401c0e401403006001007140400c99405440c200c03840021651316640c002464400107100241c002c80c00092200400c50f107500400801c00d200d03004a5006907654018002268080b16600c000385c1c0c003070508220141800c4c898641044040c200100300d0755100e048140503441c41907100c1001c9444010108602d4485001d450010990900a000314100c12510740304041c4050300014450340180b4000b5486074080c3d070080018040c2008204159a101c092404c010540c0d41d205912030100019001010005002140d2089501600f000e00b0104540d48002c0030701803050544805988403140841c0e5030701c031002080e100c0c3d8000c044039507401000c030301418201550484100e0107002d031341e0014002c04030707440f41c181c2e0800781c2d94029100c03e082c0007002000900035042452070741c0d40000300010358510000040d000f541c3c0800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 67787151 1250 67785901 67785929
    0xb090307240b01080f0601120b040203010815090a02010c143904091703070c05030c03030a06060f210b0d2001050705060601030504030c0803100317071e0309030c06020106 75
    0xc011341c0e00d82001c81c0c1c0000311000000011358035501c80c526080080c02d900802040c004170303c20000c2c05a0700241c001d0710032035010b680c02e05580f0001a103629008800c00028003032126154000130036510710784401414100c0c03040080502840204562841d1607103c034400d000300841c1e0410682c4403030304009a061580080b071008000d520341f40c840c0701d60032980020301c0760210084c00344503245500010143c0b01800903202015010490510003408a1501c24010390f95070702d0103100100072107000e0740021042114064658400300d802c100c10310a4516a41c41001c103201800c0340b090080c04001c6400c54002107407031480004c0005411034031a0303030390f01d42d04818a1070840100441f101d004000b0068840d5001030702148055000780c2c00242c104d4002e00e03042002c5000d40d110302c00b140d8020303282150b451036a48010000e200310f01007100300c0e58200e6501680b800c182511a400390554425803440300310030001202082601640380040255800300c0b00b86603a9a54000107030017400b481c810301030034414007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 67788401 1250 67787151 67787171
    0x8040309060509030c3102070203010f0615120e12070507080604080703030504020a090501080307050c121005220302030c07050102030403020105030a200d0c120501050306040b09030724 81
    0xc20943c1c0803500c029000309000c40d82e2070200300c0701e80307a000c014684d40b000b034001410540c4940404070340d081d21818005a030380e10261040c103085a00600703000060a190610901040e0f42c581400520280b0a04d00f82090111825004d0014031100c092082240718101c0e200f5910f41c11031010340700480c01182950403580da0f4410140c1c486404450050283c0003c10110000038025400641c00c180054100c02215850700d03190801ca0304280c01c000c6683d0b2000c44d1410400c00200400c011040056035120303188202400140c0d9100f500a0782c02c0126038881000582d0203007098298443e5507002c0c2403907072440c14141406500c90f881a89208601d0040580105041d400042207404480e0b040c0c2d1168519914268410000d1042814528a0000306403240307100340e102502400e05d0440480000425520100010301102c1010b8039943d03609041800400c1a036038003155050784030307400c5100e01d01140d840a1071142584038144009107581c05030b11500322604000519600d0070800200c0420480b090 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 67789651 1250 67788401 67788407
    0xc0108150108011203050d1107140a0804050409030509040906020c0706080103052805010603032f0627030d05060112050f07050a03020906030a0906110f041509050405070804030906 79
    0x10a4402034041411400100300c0c913180c41510800d6a40203103000d40c1414000081401030307030510b0005003c0480c0126541c0b00780880c0582c444003159552005090b00050f80e40ca8511a028522504d44610703034920700e003001d01d030103602283d030704408c0100304009042d0300340f4123100203400c074140614032881203001c0411814042d904660589801c40020141024550016159485188440b214150502c4200c0300015400d02846002d584251203a8440300100c011108110381d1071031401d00c001c4030100c5803100480001c0b8091b42c2010050403101144010041000102031581d20a0100c520001400c0d040380c01c415070000e0b0082c40e00340e9501e08000800184841a50f0701036400842c4c64030010041211980078400901203014181401b41c00c003a80f003c0011140c0e08100c40044000f5141c0200104100d060310900300300e0b50174034001c64200f0883c0b00c0c18050b5030107540200105007003c00820704519014040c841e004040050040c0090300c0c0452005004038002d0320300300c0218052000110740b480c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 67790901 1250 67789651 67789681
    0x409050f04050c09011805060f180a050a1802190f030602090a0e15090601020c0a0305060f100f0b070615030609030212030106021f1401060503090f0601060c060e100203090c0108 78
    0x1035086c01c10601c201e0b81c040c0701001001d0180c0700607800b900d202030329000740d01d44400240b54900d0040220352030745030103412130702511801090703907103100e01e04542e80d20341040c1d03103c000030303000d2701950060503142d04811444841526038100008420710001d00204000b5103400070403203040181c900e0310003e07a4500d540059050161101e5014403161901c3e15424182054596840001481201c110b00711240104074860060b400555094100b03004201400d0404403100703802c05048106000710514001903040300321442d0040074001c6800281d8074080c1f1980740c22205014503040d0754514043d960b490000d00508070500c045025001e041d202290807851041130324101d48040d0080c06248070510440c0745180e00a03002c0001300e65880c41e914030050b06886106000e81026140c156603801d21741c0540d0300d00400200c0c3d004031a0710000c01800060303403103c80300d9511680581c1c003040259403035441904100c20b0f1080c3c101d410384040308000c040d40c400102c7c00050b000c03e803501071880c0c860344007111440c6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 67792151 1250 67790901 67790909
    0x40b0a020d030c091e180246050903070b0304030206060a030b0601110f07030c030b09030304082b140a1a10050c03070c080a02150c0a0311030409050f04050c0901 71
    0x84c60800c1c00f00b00d00300c1000b181c0b194070a070151040010503103034043d1503c1085100500b03507051f1780c0420200d9400f90b080000ba0780d01c50441441181a40c452005141c035001050410645000b00e0307118071204078080c1c4180c400c1a40c000301030f502c481740c65040440c45c40d0021101a80148506404500e4500b40956500192078002c2000d0601e40e590000645085d2041004545580308540c42c1c1003000314148a440301851149420081c0d2500e582004090b902c2c015201c0c0140390410024000000e0bc0f61046491039171a0181c4015081b4a86002000c885185101111450b0a142141e10104030b8070880c184a00581c5008110303000f40c01600c001e022000c0004580c10078802c00b0f412204034052005010520001c070100c0786807009a51382c58074041c031076070302c1030b03085038030004a0800b18038200c200c9070041119800034508003031021007556501c042590003e814000084101e100800c0c091044501404450400317005908160440b15082d540c100c070103a03024050070321500824031745200b10504032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 67793401 1250 67792151 67792157
    0x120f02160b060307170105060f0102060f07030c050c0616140a020a06050c07020310091e020d02120708030406181e090f06030c090e0d110d0302030405030c0102040b0a020d030c 77
    0x616501c0340e035107140152110b649441100000600f80f03a801c5d0100c0090903402c00003207514144402408001140482814150f41007070042145841e12580c0450344606140340102d54034514100c2584c2506c00c5050303072051800f460041040c00780000700303402e0141d442c0b41d031399082c1800d400b494030080c1d008034100180180c00940c1164041002a001140c2110b44081e0b5945025015400240f0b00116880c020f9030f02038031481514240002141c2144098175541c0d1040505074143d4001a80c014404100901c107150390510052800070030454100034006060803680c1d615210300300a005502c8594202c0391903154046c3c0481c00e2480f01a40140b0842c2e084103505816080080d6000600074a001c01a083c41d650200040401c5040c030f0b2000051406d804001408080004814145034550410209201041100801d0380320000340034410514549801612611036140c503a0442c407440c402010a980040760205000c071341d4400a00080741c071130f0202e9501d4043c080781a01503030701c0d03a0100004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 67794651 1250 67793401 67793437
    0x30d0f020727060611100605060910120e070e0606040f06050c010b0402040e07111b0f01020106030c0b031602010e0303040609390b04030b070507050a05030703120f02 73
    0x428040c071040a5103010140d00b550b0000541045200101c0300640d01c540c0002d0140d402012500505200320301c1d034143c400c00b042c0085414040491824821191182e0041c013103c2d0607c2d00c23140c400d104204100744000d4041c0004420341c544e0503921f064a00a0f00c0001100c5c40108070325190a4040328201c0716001809500c4510b0513030140c813071360030440d141c100315522205010084c1d03a071b910080001e00843c3c01d512110b402c1000d8001c00c11a10601c8030081d60340300380200000b5841e4005140240c280848d120010f407070302540100e024201d641c1c0010020202c440d400300304000074001442c030411700d0302c0e1007841226400d0012402e0740c2c1c0180711040642c0041000c070700850100c2d081014110b006140007410b0356800700103001503051540e124240000050314160602115088200040641c96103550800341103445080742e00038003070f041c64280080050740c0010014184520031001d84c00400340c98581c807040c1000b80c9644d0403001c00110040c80c0c10030907030f00503941c2c1c42595000241d00025080d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 67795901 1250 67794651 67794659
    0x51815040204090203330c0c0a060209060d050405030405010813030801050906120609060103020a08012304061506020a11150316020709110c010e0c0913020d0f0b0402030d0f0207 78
    0x4010726450500383d8042c003601107460740c161785000c400c1c044220b581b07441e0540007195001452860310f02a10b0800c00220410402c41002030004031040e545400510069407030300188001141403003102d15902c1ca01d0300b85800c21040c094044007070b004a8100b80c0700c03904690b0351103c0014030142603500c01030200350a00014042810700d80640b560100015010076162400048030a00e085001c4405447c0740c2d01c030700014021402d29071744080080c042003009100080040c19642c02c0e1000d01044241da9076025000034050040a41100503808240f1308501041d640b07030603000751520800030081ea0f00244001d8014960704040c04102d4030007090f1104241903448540380080448c01c820085804c6114000e07001c0b038902d140788940e0718820360b07800640d1343d40c820b45100d181c2914810701d100d940c0d40c1c004140d036003010b807038100c400c40d030202042090f41c04035251072000900c1c4440310300d03002e0300002a03111240200451014080d00030360003141143d242e082461022100e0000003266440140c0018400300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 67797151 1250 67795901 67795909
    0x305040c091806051f0e011802030408130305060106091508060103020901030b27010b09010905101202070303050f090a0203030a0f0207030206160c06090f060c0206090904060518150402 81
    0x8194480c1c040e5450b0409030070381c55140680d103084c1c0c1e03500b050100c5100d920070004149190800203041c540b04a12441d80b4240420260b0f9074080b00205c406900040003030300304002881211a4880601c5e0040710064590030804c1e0b64170003d000e51400701c1c03010a80458544124480307180566020355887e040c40d919800118045e400229a850505442d0404400d00c0c3c8e4440040304401c2c038030b20409000b8041c690745681c81c14a01a800001340350410003000b41180d9000ca5000103844003035078100181c14501c41c084460007200ca841807501c0d03102081400c10035038580c0200d07020307000f03501054100c2d403a0350030202c0c0c5400e40c46000070760541c000c006400c46030703000d42d00300b1041000178010340e40c020f80d0320b401103a03141d070102d51142c0e80c003041889203030204915049100080d05003450712000c501d04040b40d40e504905c0c1c5020780002c0c0030310000c1036011580c0300c41c00c41e003000602821a050900f45458041c01410041d16130b40d03c624000c14072406800000075083c4180020400e108801c3c2d11a41c00340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 67798401 1250 67797151 67797161
    0xc120c031e090901030b150f09070e130e01020712020c030705040b030709051302031c02030d09061b120c0f0519090b0a0203030402090105010516110a05040c0305060406060305040c09 80
    0x940d1081c441800110025600c01032014003e50052482035a1483c0c401d902108011005444610a0f03100044040b17040c1c540700384080c1c6c044058106070111003402000501034400b40d4442d28038503418420440300801043d005080351500c101320813005003c04010981e00c41159810b1590150301c40744040019181580080100d2840a03003501c00782c40e00c40360081c042c5e0340d0031580c00941d070b000d40c602442142001c000044114522042c40c041c0c013817059038002c0d00d0b88a01c1d210680c01c01e445001200500c41d8607440740d0041815141c016201085201020741500801c2109032480c525054400490b14058100380000401a0b990149080c3c410400f85180108401d119820030030346000201d600f040c1000244500311580e002191280307000e2041004c900c00503040981003000901a60203607200c1c1800c01c400080e400a05003500c0310041d408205045420341c403140d4041d06200dc0c08601035050740c04580103102c10b072014405240c5806069081d520103030f030010411003928108011030781552b809 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 67799651 1250 67798401 67798447
    0x1030e030315120d09050906040b01050301030623040b070f08060d02060c030f04180b030a0f121107060903110301090f120203071a01061b030206060d020307030c03080c120c03 77
    0x152043c0502e11411a46448010000b0700e000c280902c005008900e0b003205d801c0c1e40148116014800a40c0301c40c002011800180b000801041c2c41d02c84c50a00240500820308240703103908006041071600f414443d00e611015140b00c030100d6000c560081003d031082c4569449074502a0003821265040d9080c0442c1e035000d04040c51150100b444440c41100c0c0003002040201840c499010008400c402d0304000c47d00b444001d21301c240e01040302000040e0000304110316964001d10300c660b41c85410300c8281c0d0b03d10801182180e690040080c0801d04580103a4404140c0e0f0040d1090700b089074800c0141803c0720540d10004c0d200b00c5001140c100000c50180481da890440c51064030f052030580e44d5800e60244550b140018124201c40050010951002d0b40b00c0301c52066103000400d5800985000c1e4a480000e02841d010b0041e0040420540d181081840b005503401400d01d00b015a807802c04401c0b94001c25000b69940c0031382e0703410702c50206240054070b0140d844540a189004000a10b00c0c0b002106011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 67800901 1250 67799651 67799659
    0x160807111b010507170a110a03020c010c05010f0606081509040203030702060f0f0309010219020a020a03060f061701060911040f060f0e0301090b191a150c0304030c1401030e030315 79
    0x810780000f019440e00c0400c507401c0b681e0340e64a506c1c10003005880f141001103100c60b59800000d088000c6680099244011a400c0c280646801c030181001c3d40900840101c50207202e0508000003083c5a01412041c89111050103404148840004001c011101501c029515500c00c0c002d46001d89094001031041080b41056540343c074103030100002c415001101c50742c9240c1d601091661046c5120703142108240114400f40903c040240e00203000c4c8079490001a05e034550b1002a03c9a050b460381c0043c010b84040c07041c10700c0442c03800c81e0b194062318403030140090640c20452074810324030020055030187c81c1245903030000c0b5810088100c60007801d41c5050130410200c1034024009450a01c0b400d02d41c0342c044d01b00d1903028034040140c02e018294012090828138646089403c11008007104800107003002c0380c1e003c4a0b811403840c55030341c0f80507200103107500d800002070010400008030344100884410504600d00c0d40341180041d02125102c1d040c49000360030400009018091348d00e1242c0c41600010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 67802151 1250 67800901 67800907
    0x1e0408130e0103030221042115060909020a0501020c06070605060103090f03020109030e010f120905010f111e09010804060903090305030c0102040e01090c02070b03041703160807111b0105 82
    0x8a0704403124080e8015009a00003020482003002ea02011807000d00e000810b451801d4500380011a85460032111b45502030301c1c18540700c0170005c2503040c0c031010543c2003400340720312510341c108180200134070740e0128441c45014400146a500205450f070308144024110350601001e41c4800c000360900916290415079607610010024500e45010703a24140a580000380c00460741c036010f40841c1e10100c4007418032050595800700c4d194004640382c84600c0002c00400c0c0c1e9000c038a0b285000d400d4066401481609040385411032500c140c014007503a020960070500031507900084000b0900c41d175032060b4002010000003801050840d000b20458500c40d1901804482e0b0f00d44441c1c4c1142c1050384802c0240c0d400081c1080328442c1c1d21100e501501040c101080715924a0030b01070368a80c40341c8240b0044044c04030010b4203101d021600300e40c15001440300565240350401d030303012400290354004030104003020302203101d0728850050b20100840c140c0040c900110051780c0d081c07002c0300000180303041005c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 67803401 1250 67802151 67802159
    0xf04030c0602071e030e09090d11010e0703060e100b0609090603250807080708102c0c04180c0513090203030714120712050d0f0e0c01081e040813 64
    0x501c4c0c00c0c1c110044c1016084000842c516009001d00c084030718961089400b0000d20803020404a81c0010b8165103081c9003c1c0c0c40c240180d00b90160410748034007090b80c0a443c900105000c0a40c00088010104609550200451480b00e0040304c09050b080d68202c0c07070610131880700703090004c0740c16007141c0001c0071680d0650403900e00c8600709002451461810b22202c0c0b040081490811414025011100260078007a0911500683e56078800e800c440c06c0984840081843d40c500528400b1820303074030f04d40001d80b095603a202c941d50700200b200b1a802540380c5030082c640c66070551078041102e54850780341080e580c641070030806100d444135001d142c150b03a90b0505e800184d50800c01070100780d21640f54a41c15140b81c850003400d115489107429801c0c02c007041341500243d05c01c0340e020000c00140c14400d4071142010481c1000b4000983d44652141c80c0004114003042c000941c0010800242c0e50302d24650b980510380d00e05c00c500103e281001102120204e00040c1c8501e02500d0704481c001c0e4020182070396 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 67804651 1250 67803401 67803413
    0xc110409030c060b03010c0e0d03030b03060108030a09170c040e0127020307080a02100c150501081506100c02041d0303010e04050c0414010303080912030c0d0f050f04030c060207 78
    0x415103044010610944464040101c02c2c040c0012541c4101c00800c80148030607070140080c0d55000c2c600b03100705640d4032000c0401d4080d5104041d4010003900303c80441d0713191140941d0f65802000250f0200f92183e030001030381c00c01407058036908442100585000358004d01840040d020ba030000c540295290030984110103a08108c0089000004401805c6408a0300501d400c0c590150803003000c0360020082c1401607100c0c1981d0004a000340e20b000e80041840d4100080002d00200c0c1c01d41100e401c203000016002400140d140c03ca8200c0031082c00992a404100440381e541001803102040250400c140949415803005035006448050852484102c05005055034401d800401e10a0740070021300c403d11100704400b000d940c1041d902007042401400c40a031100505200040811411100003400d4110502560703640e54140d05406132241012140401d0b50b810400c025004a4904201c1640009450085500401ca034000d120190f0710380f03460071148001d60b48000d03654190204100e00024007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 67805757 1106 67804651 67804661
    0x228030b07020a0b07080405060f0601140d02041706010f1406070206030603010f15061107140d0201020f030403030305010f09050603070b03070c1b06030e060f06010c1104 75
    0x500c030700d01207251603886030b4010310319442c0300b042c8a01d982d040100e16000d83d10490a0390040d94849012540c13015040380c10a00007840d03052800c0c000401d03040185855107441c1005441d15440340c8410140b18002080d462095200e200100700318a1800361940113000001a142455840030000404138090358070701902c1403600101044a580d008d6118815a941e410024480b141401980c0050482d0320b201e0800441c402d00228240720201186e100d050f51017100700711030007181610a1000d4140c1d1240100e055102d95030150320b12842c100f028000440c402d6030089855818a801010718200d00c0e8441c081c1a401c2100303121003950041115820b40d4003030210252a580c41e603804546400d6400009020004003041c0c445840000354803a40c2a540d69413010f114035101031844664607001118148100505280421155840b4205a40380c040c001c1e500d0480c4200d181c0000b404442d = true := by decide +kernel

theorem cover : BRFrame.Cov 67625901 67805757 := by
  have h0 := BRFrame.cov_init 67625901
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 67625901 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 67625901 ≤ n) (h2 : n < 67805757) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
