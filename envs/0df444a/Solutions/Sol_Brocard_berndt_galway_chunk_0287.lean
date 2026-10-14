-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0287
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:58:33.767313+00:00
-- url     : https://prove2.me/submissions/076aa9d8-1c86-4885-a01e-47a53bc2d7e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 51438852 ≤ n < 51618708 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 51440102 1250 51438852 51438857
    0x1103040806010513060e0c0c010603060618060f0605091c06050117010e0a0b1306060e0a0204090b09010f0e090f0607110c010905100e15120f01060e060301060c110301050a06080d 78
    0x10340621816190100301b80c0c120500d540c00341c8d5a038060b070130858014112904010300c4a0309180c40021081060440503481408610040180f640d68000302c0c20700c04254813681c4007140b030920000c0c541e40360440705600381c109030761441e4000d039446651b080300f1a1000d8020721549500c0300300a101c048802d10501940c89020002822015825124030ba002c1d10010500942c1c410302080180c1006401c1d000031004000407054044903040c2402ca2728007030f400a0281c01c09662500c28150a1841e1031410701d8100e41c8903c1ea2400158141210765030204001449001c0300e216806000100b44020084144185015681c00f01d4014692070102d082c1403500e04185d0401c007041c00c080c05556260240d102040c141801e003018a40402404500078025803101d5840c4850042060502c4443c038000e5540300780c0384203840804580c0c0380c00040c0c42229520364125041b040500060003154040c0a6400050b03008140d0070041f10021320000b401c0d94421a01740f9901d85d182d074000c1200542c10841301110784203d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 51441352 1250 51440102 51440111
    0xc16031e050c0409050a05060412030e1204050d0203190b18030304030837090314030108070b030402060f0d0c03050601032901051603020606100c02030a0b071103040806010513 77
    0x240c881d1a9950300315507081d4820369070380482c40100f00b800c200c03180a0942c0001607032840e24041c1062210b15910001c000701103405c00d1401c0d56084c80200b030740000304a9007101c80781041c0c180007d00400002140040f60184500348007210000d00320139800c104a845040155801c0ca001d6100c12540e54001500c0d01e031641c018014000003e0304254070360750040e41001d03100d0200e1141701d0340c0d0f00000201401c010541e61a8040403080314056000038040030700a45420341c6020314404540f0b2644400d00c00c00c6903940010b101449040040310046070014002802c640c208021540c4510081e0300a04451030035958078442c0050381c036014010326a002ca0f003400c0811070a81200c0300e10700c10381044040341829030b8000010307081603070141c8107640402e4000d1000c0000641c0b24500a5038500f0143d61451146412440c1c10080d80d1242d4114640154003401902003102c0d580d8904241181c00303481c030414400607035003501c00101c040010304001c00d00400104020b5251405203c403411010190402c161f060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 51442602 1250 51441352 51441413
    0x6040b0603010308070222020417010b0114031305031c0e0c0613030f020a090203040807110f061801091503090b06040902030604021011010515030607081005010c03050c1603 76
    0x101400d40d124540c055903856011600b518110b0759a071f8840c004070021034030124002c100c2000c0c2c1e00030407100c0b8802d600200301b0381c00301000540303034032440d415a080c80300c0e0100001000320250160f07644456111f241100d003055503150b4041c41081d207071150b003100306170745100c800c880c0d09040111034a00c400968406262a4042d032010304c103451207000207042c41050144032030441d00e030b00907000004d0285030001c54032410b040c0b410680d1688041c07030075221034510400d84810b81c40d104001c00c6c0702c40ba000309035610308a2202c0f80c00b00c11308014944141808985480022158030b4440078807540a80c0e50340004420003145044000242e0150105000702d00e0000c0704030040e20b00141c69a0020380468406901f0000706004071825003446001d40c1c215400c2c41c061100000c811b0310300c0c070b401100403001e84205642c0c0040441d1901421503200d940c01d00400c404228a5020ba0a150481406490454074110f40d00f40c80d18034100c4002d150003850003030b084041040c000d0400300c40d0380303410010a881c4034075501c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 51443852 1250 51442602 51442613
    0x71512062d03020a03030c05060a05011202010c020117090f07081603031817061b03040f1e050a0b090c010c050601060318060c120e07081504020a0b1206040b06030103 73
    0x941602004001c540d98420303800160101400307500666000f003128503410b03221300d4000d20720182035804481600c90840800c413a0b0240f401164181c6800248000074043c09400445056129003400c0e414002106001811000710344107091255400000030000900994120380c030b4036141d503011001c541c000c0c1d640345112904014880382101e416107049100d03c0704200700581c0c902802d6000c42c00e100c819030a0b500843c0c00201d02c80707115100241500c2c44143c590200f154080c401250020800c40d84405408006084503c200000788035100428078201c1c0d440e5071b102d02d0030b1100039080e81c0000405003002110711040103020144d203030070b00c2c1040700048940d03140d50b41c40c0c20600034102032641f517100001c0c20500d0945c0040100b9080b81c070500c04103c40d804050119031481160940140c100405100b03005c0b00000e82108450100f0010030301e80340050742c01100004080d104036803144c2d1038080040c6500e112400341c501081695460859820000100001c46269041c0c603130181100344010000b061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 51445102 1250 51443852 51443879
    0x21040f140c060d0c0207050a1706060a030f02040504030509060a0503040b011a0d1a040204060e10092108070c0636170c1507030905030f030f1b07151206 67
    0xc08143c030100c0d250701c020f04140e06040c0c0750b80002e40c12016803440003030200d00129102009a0486040d0740ca65101d0781c0900c080c101c1c1900020349460800d01004005003002d90040c0e0380b26010749440c1d8207203c0400000365031075028024841c00600c020003848140942100150300418201495000e602441c100300c800d24040c80222043c1a907940c0e40310300c40584100c0b000c00c0140d500400c1103507100d8403185e001e0b01085c0d0f02680140035050000d840f400c2640100c0b807900940c0c0c40c6000b80400410310075148490b50400d82d40c111040d0006110020019450b50690009040143c0310780c12a1901510038025280c143c10807201d40111070b00c0f040070809040412078080d1401c840c035141a2011480d09132346000e80c0d22620503002070081040e4082e803034001d405862500d110b551041000e9694400305651742005a8000c01c10f50800c02c101d60000d1141070041c0355644500714901c04440308011018140146980890f950081c100c2d08846031a40c4440750b441c41c401d500d10100101d90804403084c4018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 51446352 1250 51445102 51445117
    0x5030c060703030b031501060e010e0a05060705070e01090e0f01140106111c050c0c0406030809010507150903021005060303030f070f05130801200708030a0221040f140c06 75
    0x300c800055201c01e1510a4102c4407540c4c0001d0111a281c40c240901440381c0035003446030b54006040c07404240c55662007207040100c0b1690003403640c80c480e81032000708103550b801800200c540c0d10070380200080030902541c00500034405540c0000b400341d2492895400e003242d2000050117a45080542440e40c0650744040b030542d81c0c68500ba10065100ca00c01b0b5240c483c80c1c07030070a101242c1071507201162070b038403400400c610003895060303a0206552000b440143c076520302004002403070070f2256a8032540b20b4400340503039500404900782c1a0443c4010356040f1541c002045d0016000b0500091104034180a40e03130300003206030f00540c42c520340710b070312000c140c103024024104021210400b503940c0c602c2802541c10040c00c0443c007408140d51180700500034021041a07a555078140303818412511740d11410f99010310382000d0161b01e1943c1703e1440000941c008546c0d010030704d54910789120702400c1c1e00035140c82644555803640f41d90089040421005007070240c445d1680d03120125403c0217403110810303aa2207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 51447602 1250 51446352 51446359
    0x10504060903111305040606081603031709010605060406020705101704060e030c030408011409030c03120603010609020c010f0b0f0105040b0d09061503030f080f01151205150a080705030c 82
    0x4100d00342c0006901c4100080c1c0d2104c103141054140400e03c1803e500c84421036040d0002c4903424525a03c0b944c0003095a48009404180030f000500c951540e9040f0b01d5900603640720000032520b8688000541a4205412000043e07211040c14445410045c05e031412905060405082c0c640d0200c92a1031102e2000f04001c2c4a10b89072151070034040020019520780d90850300070b498542d070304c4484640c001c0080c0001c9a8484900d0000b143d90110b0100460b40f24900c0c2c200610726002c8100d2281c1d040c600042c110315099980e88000003012801c500c05050786e103c00f0030000c0380c04100d0310b56840607118420f00051050144000c451056a0401c040b40d003250080c64a06880d030b40d85a20baa4020004030390040d0006040207030401c400c030b410b1524601aa8072903100c01ea848103030603500705d540350000c071140d06840729000c00520030240713030035400c5420340a14640b907030064403a60b9044050740d400303640005404d880a820203449181c00e401c040080c3c000301c0c0003003001501e40400a50384009007813000f400b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 51448852 1250 51447602 51447623
    0x3030f030902040609020c0c1507020108090705041d1e0706030908070501020301030302010203040b09010b01080106050d020c070902040524040303140d06060c030e180609090102130f0501020c010504060903 90
    0x6050194009102082d0014001c00c1130941e240440c102940c0850b0700c5000600410030728244624007102c42d0034105610081c07940c1403054560040d64080303406440e2110f00c1c403e04c58000360382d9884c0d00980c2c5003c7c0100c952100103d07554951103180c0203400c0845004c022100702c20440312071000070481b08840c06031030041840f06490074181c00900c20a02d028145500000000c003e242d01500114043c0b885010340020a81e1007001141c2240c262016040c0002e525000400440c1d1081c1c0240a0b84203030024014035103250342c0f1085203014260f5100300401c82c2c0106042003d4a48040d945d80d010f01c2c4000c5051080d02c3c4c952243e0810b10139400300405100b20340007119562040c0e00159886070038582070030840540c440c031001d00203e0040408400103020075610841d1410012060100100f800c0302c0b0702d1094130380b1005c002d030480300140609072540d820b10450025800b4040144002c1000b1f02d001e000503810320000900307269036099024103012040004004080e4450361020440b03401058203003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 51450102 1250 51448852 51448877
    0x16060e011218050307110312030906040b222a030b1303091703040e01091404030f0509041103010504140105060f0a0912080d0e011e020904060e07020d0e010309020a0303 74
    0x302e0111070140080d0040c40042202c80030803103c0c600e00d0303409443c00c03805c44d042d0042c001c00701000e51108480e1081281c00c64004100020724000819400140a40700e003c0d10000418200300c82c1064103000750b410b020580e4000103104401d4000d038092901510384405a582503445101c880305000d00b184070800100c40c1403400741441038841802030714000403201030000b00f448925603070f40c01c14003821080f01d0320107000041c401e80c4c034072823980c291850f1120520a6621510244d49602c00c1c10164000e1040130009007149640d284101e0888200707400302183ca950510301488103d503961244007032a800c1d400018440faa6440c0103551900010070740b051303a103400c019012160312070154006031300b01c640c0d001030750100703c0c030301011301104460b009041220401c0d0f80041401c2e542c1c050b1310400000081c80311071503a28400d400503c800a00900089081c07039562001246a04d021230b0f0788401070300f14005a01c6101e42c4581c55a0310100c007440e090101c9030540e000580d0910442c480102801400c06c00c41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 51451352 1250 51450102 51450131
    0x709141507050d0815011d01030e060c180909060c030c07050706082401080105010e0f0303030a020918010303020304060c0311010501061e081306090c08010e16060e0112 74
    0x41010800e00d10016207600035072804650303904002c5030000200d003043c0001400c4982c0040f03115000c0a059403850302c0007811042c403801c6c0b03070700941415040585440f004042950100091805801240420b1b56034650080714600c42900c0415014800c0c40c0d07082c141b119001300022a190000e100c2d070700b1941d807915282016900f0707104018005103e409041c5000901c036402c28007181c4a02c2203840c0342d00c0c000d1410100b109040d201c00c1c0d1103e0200c0e20b40401400b0b15480b80c9041c03120254081e0481d014100c5120020340703590422203410b40320540001d10340d0f0050a180c212184d24051089000c1d0241d411a50065128003c42c06520204522005003d09040c4511242415003200340c00800003943c4032040108000000c1402504d62918100d91141261041030340070b02c01c032808100b81c00e0300c541075503c2c1ca020b0480358030241c5d0072094201c404512940c0a206060409110030300a20070140c07003202f07049441c0601d0b071080d414404100380fa045541d8001204108422211000081c04088014407 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 51452602 1250 51451352 51451369
    0x1090512120c030c0703050c0111030715050604090503070c030c15120207061d070906060203091509060702060d0203100e0105130f060b0409091103120415050405040e060402090609070914 82
    0x130503090710400e0700000c1400000700f0003017100d03e03003039a506a04980080001c1c0d964032441c8801400fa0712054600d0480340c0e141e5000030b030001c500400205001c000ca4940b01c3ca541c0001000350b0301007121590402c01c00c440080c003400200422a411010502d0000c0c01034264030f14210600c40407500050b02c0c9080281302d44c0b2007100c01a80700000c0241000750000640e40749842d01501100900d410400301d6100d0001082e100d8480005001855000800b03015451035002030201541045c02401010016602c00c00a00185c0c3c498850040e22864000204d00102141754401e110280c0303201d00502c401d071942d1a0200c0f0b4281c0d60b61011500c5c1000140820080182c0e6005a41c0120045030100da0005650494520280074010380a4054500c1c010903848402040601e405008100010441814111040f0608800c00e05025041c035954401040070344da1806401d1030319402070300070441103207050382c00c0c0c541120059441d0809031034240c80250080000303003e5100100312003081000d042e0342c0e03000c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 51453852 1250 51452602 51452617
    0x302061513110702030f01050114060f0d05160f030b0105180a080f0a0308090601081c0908030f04061b03051602040204030f03030b090f0f0109021b01061401090512120c03 75
    0x4040042c0e800103800d0403002c1d000340608030320034080d20090705241b002c1402900e058543d040b006d4804280210201b000651003d0004642c444090020031540380c0503100b0315128961100c12180c402c1d940c85002099200d0014400052601d09070131064241d03800029940158105604000000e03c0324001403018040d590142d0b00303522907410f0424881002240f41e1002a00c40d80b82c1c0d600341e80f41c2650700f039200d403001d0041c1202580300d85038101101070041e1017591280d1540c142003841d41e8942e808ea9040d50320100c1500324540300020100312070b55005814101085127100e41c070781150243d580050603489110310b00c03903000806031035230b4066507141da04407402140d12110780c40c0f588900e85005009070511100c218801c03400c0800041501c08014100d030b200e00e5081c07081c2440b9038206081071009402840e1f5034244c01881842ea24206142403049101800d190300d0240c880c00040f030b00040001215070405e6004084101400c003e490b80052070000b0349800041d10350b2034120b00c403901c1346140584032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 51455102 1250 51453852 51453889
    0xc0c0907030614090c07020114071b050a060201021305120f0105040b040506010e04080d18080c0a0506010506090303070b0c07020d0c061b050a030c030e150d050a0903020615 76
    0x5003031184194041e4480750849031605841d00040300058200416041e046070480c4060f84d0030004800150300c520350801c01c400c841e80956080c2010340d03c840e8043c1208103400006015090740900103480e02c060004000c01c500c5c4000e5103006a10014200e2010f55445024000c10000d002008060303428001207400440f824001c011a00d005c0c18120a248001e840075196801150b0000c2513400280400030701c280e0f00040c003e441c000604013094000d044447c2200c441c0c2c42c1150354040020450001802d01c064140b009010400301400c2c401c0c100308041c2c0c00644603803c1080b18104944000c4141c500860304021200160b035100c60307181c5102d104480c0f0007940080040b01c1c41082200c00c880038030070794406948199822560f401d840054010843c00503020b0352140c40c00400007482504050300030b0348285007000600f64503c0c01304244c510022030f110003007100400ca8409050325803058a0b8480d203d010140820840e680300607403108170150001d8440c0100741b4000b0400d44a10310b090b0154004a0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 51456352 1250 51455102 51455119
    0x50c060403231c02011506050a02030406120b0a03030c0203060708060a06050d0b090c07050c0d02011e030b0603070203040801050907060c08030c071203050603100501030c0b1c0c020604030f0203031005060c0c 91
    0x890300074001c1150388641c2d4080c1b0410311004c5020340c8503906844075044250000e5180c903051803803d598030365450891561403510742241d0700154842d040c940d0010b43c442d40b03d50360188001c0c030416007030400080008081100f440708202071a920005000200e445600300b050703031001c0601550019000d814001600002c5000500a524803ca0028030308203001d1000c0d0345194000c0002c10500481605010340040c02c0d10900000d03140000c0c061300b44131000340c103001440034104c40220720f550308112003280c0541c2000c501002065028024140d1011003000071300b100905048000d8111130300303058060000c45010000494120402040f58025078000100d10145055480010090002103c1c42402400341c51140c0030728140901429058a130f00081e81101c1c2030034010305c030394560440c40800c40910b403425038000f82c400700b500c1001c0003801c0300d6010304281e14080c140545500c8421040300e04540c420000c025000c020802c1170030a03900d0480d03800e0b998004d800c140034503021101c0005940f103880c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 51457602 1250 51456352 51456403
    0x507090e0c0102060106052b0e01050a150f03080a030c02121306110d0e0103180c0b0306040c0804080a0c0c03081315091202090408160609050c06040323 67
    0x10303541c8110002642211050303038031220700f19442d004042c0c0c46c40d20452246080da242c01c0f440480030360000b444440009451200d21900c1d0700f0354205a500c44c0364070f1713030f03600100d0b510f4200c851411000d441c11100f00822140345a40301c1005108080e0f44104040c1e5420301080401d02c2804600002042d80c031445d80c84502d00c400f203505401a43c8641c80c0401c1c007900644440c10004070b0144000031464a54000c031070303598001500601111804a5207182900d2201000135080e10140009040740245c3c503034680c64000280402c0310003030642201400303090010080060803110480d0700084040c5800d001b4680249044415010b40c0c0d00001d00032071001c1904140c3c4000c50304801d00b100c80048114444010388841603c450fa014007840c00305800c3d032031800000d81060ba04071a0410310450341c4900c0d000e020100400307805083c600407964140c0342d0b203078802031007000c0141c4001c02c1800c030f624a24043c07455a4183c1e1143e8400c00895400e49140b000082011341400b41e4511820036003007000381c0301003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 51458852 1250 51457602 51457631
    0x7050d0302010e0c040c0c0f140a0c050411040509011202040204030b0f092112061311040e150d24050106030902150a0203030708180a060209040515030d0c050709 71
    0x3c003076120100380c0c410051400f20924181c000d00260715007a480300e0280c0d41e03c2c0c0d01c0318008480600c009484016400349220030108040121104142c005c0d01007152040c02e100420003500c1c8a4040001707240700c01d001c1800700c1d58540c003c0504444545800080c5d811131031002c00c0c00707801313035510142c0b0728441582040036200d05480c89920910511050f192400000c1c40710f0051034550511001000c00b00780301c0038203c442d103000d2064002c8802072806240d460001c00c8541590707458984104110004a01004441d001c1e460b5aa00812800c030035030000d41c1941d01040d909050098054050f1945940451042001e014181550f066410f4103111960310303210f028014102c0d54070224041c44072500c0c120304425008003503d4203079005038080c41c0f654a0702c03003003142c482c0030140040c9090b580355548404054000c04c50715218520940c4050b0315207588400304012503030000c003040354400f01ca503141c8000d941c022400a800d00d1036400c154901c896541055440c1107540c0d080840b410785881041d00b008107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 51460102 1250 51458852 51458861
    0xb0a08101b0206180f06040818030f060a022116093008270f121c020f03040e150d15050c090d26070b06061612030504060e030901090506070507050d030201 68
    0x51400c612710507101001020700d95a00c10000070041b00e90040400702e210095a07800800801100c40c10484840180064425403040c05454071000540070003140c05006170801034440090541c0040420b400c042012490f031461540d420116040c2281900f00c01008400801c2e01c0b05541c1350f80080c00a00300c1448143c0c10110f05000c002c0c0300301800d140c5050355240c074401c21282c0c0030301c0341c0140203c000141e150245c07000c0250500c00650040c40282600311900700091f0008150510114406062000003c540321040b00042401040d4080320100403c40c146440041e003000108001034607642c900d0181424002c01101680c084c007241c0d00395003448100e0102d1b4586101e86408190400070f0210340450508c950400140038040f48400642c503890300310003925600c95200703585c6100000700c0c0c1c1c4220070104174106442c0480e40d20f00502047c814140300e00d101314050310008501d8160032900180004545204032840341d0700014500c42000002d2140e0070041a01600803400d9065030300e8003a0190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 51461352 1250 51460102 51460117
    0x5010c12080a060e07020c04110426010e030d1512020102030319021303031814100c061104240f020c060309030d0501080a03080c0a0c0210030b0a08101b0206180f060408 74
    0xd49c01c0810284201c0007a90468007100c41442c080425406424441c0703144a1402424510715581c03060940404c40c024030040004800c008000521500b01d90b542140c1e64015400119071800045100c00040c1d0700042100d40001e400b03078906481800794000310b03000c1d03c2030440024010a0404002041607000740041281200e90150442c003c1e80310800901c40da942c2514240d4404250f2030300428960041c00c910a1050245c10b02007503401c0318104d5190700d0707840703980b204a1440107812904102e8078084111004941c846c540039020643e0300d58004d40c4c50b0242d11540307100d0300000001c00c0e903418080045a408420306c070b0041c8038540c1c4d5107540648030603060206801048902000070f1403908604100c80ea00071890300c488505400c0c035001e0050410810900400740366542040e00b06030360310004070100500807480200052010f800103042610040b000c60101c4010210440741c0164010807029071008210642c003400c1d0004040c2203144c42291500c42d01c2070300a00c410f1005100f03c200c000c3c5641c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 51462602 1250 51461352 51461359
    0xa120302130905040f03120204031b0e070201090b0114011101060f080d0309120804060b040504110f0402040e040b060118060306050f1903030e040e0609011505010c12080a060e07020c 80
    0x3820303a02c15400d0156402190000c060701514060780000a00841c0d4049045c0f90303001c0010306298803662022465201c0844040e654058040104000108610f200e540808544000e02c00128140d582c1100400d060082c90001540d02c4007400c1d680c0d200d251a24900041c2e60000d102c55946d45000d15403003100c2d4020300420340907500c50229001d020340910140300390311140401c46103900740000c41d5a0381d0003500441e101600d03418200c18a03581da00920740140d01640410b540021a10700304040401d0110501d401540140f0003040700c40307030000080b03500c260080f409110a56400c00102c480700103404004600c0092118082005941540100107a42c000e0364605c810664a504004421286480c0c125611b0600c10081c40042c1c40340b01041034544000c3c001003034038030a0712075590400004440f040d00603903403100f4038600c6210a152140081c0000e0070f000840c5551503c605105802d0810b095060084d4a400b003100e02d12140c0c885030080080d800c55007114200903200a40b140640c20a4610 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 51463852 1250 51462602 51462637
    0x302060609040308040b070504180c090f0b0306060a0509030f0c03120c100b0a0b0427110a0f0903021507060509030406020c0d020f040908041509051503090a120302 72
    0x31604103020000d014503015100d02000f075485a0b0f8640346e03030070004c000004000c018040003840864500c100c000d0840524004104c0740600440100310b415154004410103a003908100309035801303007084030303002181500d1103561001440016940e40c4542d11004d138040c4645042c0000c0b40d000880c1c010071030507044040d00c1050180385096032841c000c0041c118141d4004840114039000b040c0d10070144004050416010560303280900b502d1508194810720341740e004807000341c40b00c018422006100310404202040b0201c40441000c6c0035001c0e140f500001c0c01400111851440c9c082c036800c2d030045a00500c0c0300345588003803840030156027040030125507040c14803011a140e18400320640e41034a460b1341c02003200c00f143c6410040d44554080080e03030801c040d02c0680700c494070340b801140615401802c4060383da40ca4242c240c0015100703a018a02002071019007808a03603204483c4625802c1481009520380d15143c90769400c01c1840f400040178108100d03801c42003107030507030090701d69404001000315 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 51465102 1250 51463852 51463861
    0x1c05060106030209090f060d0c06030e01060b0f0a0c170307050702030606030f06130f060509030c12070c0e090f0d021b031203160203121005040b06070b1801020f0313030206 76
    0x1410b134014001c446510014010000b0036442c0880e40c05d651280c8020142d104d41c201c1b41d121614011003c1e000100001d0300e512a402c04050709004e080020005071101a241c140c445156115601076034240a0811100b04040300c01d111180044040d07600e82c03550000e40d0f90400d0320000d002036001c0c9100f24000d0203074400040c4546800300b001140c080815010b0b1804c1c0c0c1d80c0140720070003e0000281103825004445605011416500c1818480c4c820310b4010b40c0c0d51021140e2951602c0810002c1c3e01c02d2000802c0130310002030740d03810004c0440d00230100c60100d5072100120386060420525842480d0700c104408401101e03030004046070030703140c00c4c0340303014000150130709240e150074000b04180c2501d03c041020440c0c0c402c0c44045240c880382c00b4415203081500c00088000d100f841640c03682241c100d004800c1c0046e04c2d0610800710f0302c18040300c40e91300c0c04820baa03400403c41e900404594002c90480503101e4003c100b074040352680b00041c034290b540d03403500b606034035042c1414280a9005204442c0000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 51466352 1250 51465102 51465107
    0x30f080f190c03080f040b060420040f06180317070201050705010c0e091006091505070b1e0a061202010e19030308010306050601030903020a060c0c080301030b19060b0403020603040503091c05060106 87
    0x5d005a411483c481c03120383c0c6440610010340803441c000700d440340d42d4070402400d0181c20408bc1005d84004c81d1700300485454014014404184001c02c449844540501040010606440c0c0301002c00e40c0984540c0320501070006840c0c1c1e00527014090282d500740000503241aa0110712140c916104840c2501c1d01c0d1204d10510541c000d031401803001103480d1501c00e10500d010b845003080200000d01d03020b483d0000c159640400e28401340d52011004c42c9030184107400c000303107089e066400300201e8010403480d45001c80d84200d5000100020b07052001361103032482181c69030501000c82510401994031803d640785401007403641c09100546015203040c0210b207039907101e03009802c0c02d10340643c0102100309a5458070001072803040c12038000d00c82d40880410000b400480514021401410f4bc510b01d451700810a56503502c4a00807404010f2410400344081200c02042d50152601556417030b480f5a102c2c07801034030f14071550080303640c0441111007203d01c040624203242a0144514180d030721990b60349a0a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 51467602 1250 51466352 51466381
    0x15090f0d14040317040311010804200a091505120a08270901120b0714030115030216050d1106060609040203070c0b0403030c030605010504030f080f190c0308 69
    0x4511a00680c0316000614401c0c01851842110388480740d203003641d203966a00e2070030b8483c1444020f041e8007190400512200c242d04040d4001d0030f00b082841c9203800d51342d20601d240c0c903015114128040310001c82841d180d8814401c00b800e5001d008204801682c4c201007207561551088510400c0c00040c007041401011850a0105603c1090715040c003001110344502020158002c080b0941c5c009944620ba40c0e840f90840e00030480300c03008018021250402e0100c00030014180d20600c81d00201010200c10f1001c116411601c44400414640356115000c0b400f80c4038140107070f60402d40e402181000d00c2800315110741c03015003680b12550100d40e1800c0050b101c3e0811220a40d001c6024840f105550400360000c42c4d04c030b442454811075081c80356441640104042d10180c000a540c0d00790304081a400d03220b11406010700742407881c146465695503480310409003d00400c5180041401e01d181440402074500c003c0d0500a100202801d500b4003c01c151040001600000da182c0080303070501c95200c14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 51468852 1250 51467602 51467623
    0xc030b03190b06040e030d020409061410020601140406030b0907060906080c0403021e04050718050409022b051002070c0603020309030a180b0f03010305070504140412050d0207051509 80
    0x8500900d55034401c04c20004115466580c0303203074007041208150b4030070180b0080001d01129080010002d092501910f60f9607411940030340030780c40c6040484062074000624034111fa10441590b40d02642480128024007016072000300f003201c3c5402803051049020808000b59402e60b0b4552188641d12182283d40b85019140300445250411090015060000920012400000000d440034190401003011160129161070000302a041ea04900291801441000706001c82e401d0000100da900013803400f00d6088400c0080b2080c405501d8813a540b98a411004c041d080000c1d00d0000c90350b0380420f0080e500c1a002191451203540300407403018008d20a0341d0082d56628011418182d90200554072848100391f540c451141c036000004600c004d200081c090075000c5c0c180c039038482d4503614000c0d191400348d070440d9201c0c0e801c01c034504504c038510350003003a4003581181c4922640e00056800f80e403075104080030046818000a80b010502c14005014101d581101012003040c0d0380d4810262348603018281c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 51470102 1250 51468852 51468863
    0x9092a030b010c0f05011104120201020d0f2a050f03070b010503010c05030a020c0c032d0d05091e090c040e090a0203340e010e0703140a020c0f010c030b0319 69
    0x20f04041c045002000620701d1107119000024000034168400c140d16082980460202130710800000300b10350381072100900460b61350601d803140b01a03132103001c0c10507200c1000d001c1991204011990410395240070942c90282c10000780d8030420240000542c40c0c0e030207941c080d5442c080b44000004c05040520034a00780002a0380d0f10360654072040685006540160440c0710a403054101c11070842e5010f02603240842c15a0f180c185a1808884d031517990b61500c5100c45c601c50300100300f40d0401d00d0300841200c0c6480c00c12940130700c014100600710103000049185854100641e282000094203081004009a0f0802c69415482da43c94400c030940d11f00720094004d4150f0042849d910480d00680c00e214404008054003c41750060503c4190b8515074170391100b0000400e000040088680c20b140703079038200055150501400b081100950214003014001c1c80017558001a41041d0030740910004009144100080c020000c008130000c000d17001282cad01d24480d02404a03140000003000541030349195200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 51471352 1250 51470102 51470117
    0xf0702011407021906030c020c0f0103020f0403060507030603060506030a0f0201030b1c0b160206090c010c15021821060f0c070804030b09070501031802090709092a030b01 75
    0xa500468840740140703440c0d55519024008100140d0340d85626019034110702020140b8a4506000181595183c9506005540000c607902d034031516405c40d08910f40030f01382005659141e40c4404964039114661016042902d00720601c40045d605802040c00c4070300404082c0314588403c0704043d02c0314030380301c0010440f282065844006500a0708049012000100b034807402c1c054402010355021070301d09003210b10003115000c0084402621804001651161000340550300c1c0c01c422b44c030ba850300140940c0781031007840800c0c7c4042040290607400745800919080d500c0b14121540e00e00759800d00d85c401846421148541d0134485840d60140c40d4410000303005002c651070742c00114001d44805406c03940119410000900490901001000114030034454103505103010384000342410380d240c100d64109070518040b902100e14094524240540403504c2c040c03075465950341640c0c07262255100900980c24660b4000c80304981822007081d2140c00340c1c03017081245180d10100c045401404807a804500308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 51472602 1250 51471352 51471367
    0xf020d0e03030d1d0a060b0a0801050402030a061a04090602131a0d09140604050d080106091a090301060510020f0606040608031611040603060506010e0a030302030a0513030b0c030f0c0f 81
    0x13900001514150300c10300c03440360702c030703000400c0d0501039424000c0c2c1d039141e102d280003440d6003080c007082c400919646008104504056000030f4030748440365000391020f9281d0062500341941d42030700d0160500010030410100b0301e50b1410030069000503a103510243c000800016509600c2c4207034007840c80d41d00f60007038a03000d0702e4034000008006492003030303a2001130400c100d15415000c00c02d80303000b180603c0041030000c030701e010000e00e2410160400c00410904050810140c0a5447d0103100407143c2c50850351034210b0407000c40c1c0149420750000c1c2e0700a0340c1d1403a034030341e00d9008601d1014019001c41030322610354444060005691051142d0180b41d4000c211020031080c01d200d4a1701e509108161b09a00c100c2008001016500c0580051f50a181d4402c01c1c0111580c0111102615501c107403140c1881500d180c070040d440380a00180c1200f40540020039044150807410041c000d158400700c0e07030a46080ca050405801c0d0401c40e0440f440d0b020a03400b04103801401403d545811040202c00c501d05480d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 51473852 1250 51472602 51472627
    0x31507050415050c0102030c1b0102070807031d130509191109130c090b0406090902011713080403050c0405060105040803030105013b0906010309030c020909070f060f020d0e0303 78
    0x8054642d400c0000603c40450070003028002140104030b00c0e481540c46201c50565991001050700090203da88100030f220b00141214050360b91260705130800300c840d200e242428103001074610a041e60f0180d1140c100300905203881e48040d010764035810446038080340062015403940c8800d000640028075003000e05c85a840c24007611a8401908170740b02c1c01c00003441e500c020060b04144c01010101e904c1e0404c40c00c11b401c05102c0c5100402c8010000d0040595503000a0040003140f03d110480707412203c00248100c05482c0b4100350035a000e1241a030b6a50340b42003141d250740c5d882d80c500748640c0c1085c0122f00158480c105480a50340000061807440e46000e00548080c0c848081d170700da0700d10b42664030301580710b00c40682440c0c1791015807068401440b0003081240801d40208124185441e02d05444003007507000031800c1d541507041e80c170f50f1003e03243d00c0940b03450010aa8000c0c1d1280e0628030010078107030b52090044654a22a400710b84180710380b80d0068495101c030310282c80e019803060001c0c0c0c4140e01e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 51475102 1250 51473852 51473879
    0x905040509010b03060408070b070f08060906010203160606090605010203040f09020a030b04020c101118090903070501020c1b0919020703030f060617010806010806011a040e010f03020315070504 85
    0x2000000820040d80e83c08241410800c0318162841d03000031840105200001c400c0303640c08085407901c0450329122000c0a060340f1000341081c3d020350b00d0a800074078a64001c0007183c80b820b4600c100c552450f8458605000502403a00030861002e043c410005450750000007681d00340c5007030080c07020189091540100003500a00f071100101920f5007005021a01d492004040020059010f0310300501460320a000781d41c0700c8092588086010451000035040c1c1a520003c910f0045402007940c0e00c651810750b245000d000c401500c55440050b18a05040c0001010100c4604030741c1e80640c0d0590300c0041003040d13141162410300c501c600719032501c0310608035401081d210b88641400924280002003440c12290705408c400085640e5140c0d6100d1500c0703440c003070350042603000c005000b15818030301d1003074a0750018490702c1d110610500d0614004402002501c0261007078803480380b40d0391780d1000c000c680200e051100b030f4028020301101003107600d98100014172640c0300e80c0743c49141500c3c1ca8401103401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 51476352 1250 51475102 51475111
    0x10302010503221e11011e120204030c08070806010e040203030403060b011709010b0a0504060b16020a09090507170f0c061b061f080601141504050303070303050a0f06030309050405 79
    0x71129050721000613044124820850300c10040c0b20740405414074001c520480350015860601402080340c9102140a0507805903400d944e24020410001049508005c0d01650700021b10900440001040c081800200441150090000c480560740d807504031140700c20741a40c2c041d415400c00c00c030601c00700c0c031144c01034112440189411841d000e50241d50021601080c1e1300901e03565110800e219482c542000040003800088504010541c60403840c190280310302419912035401030245030065540d040e04200040041880c140081142c0d031500b541ca4203694018001d1541140500e15800b42001030240d01a1123400010a14400c21746d0030441300e0f0300f2402c040b4040d85160b01c92140340748000d105560085a0040d2469001d6410600d5083c0002003504282119802040100000143c010b41c1c1d800f00c0800740e982c0c03000e6a40800c5070250720322803034020b10b0b014400011000e040590540c00b851041e4007005c010030141d40d140c807000d4284c950903c03016001600100d818015854590305c541e030030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 51477602 1250 51476352 51476401
    0x1050f2505040509070201050402010f050a05040905061c06050604060902030c0a0c020609040e0109020a0602030a09090209010309021c0308060618040e0c0a06020724050d150302040609060305010f0203010302010503 94
    0x3443d035100b00182c2c1d8090103c0e40000180d449900340011540c01c098803000701003203800d2072401c00102c3c102c014000e0003103105031040c040d2548007007074180e2a0040103040ae2001c1c40c8104040e040d0b81e00b05903003d00800c0c3c4009008910304000061b114501c0d2090f2800358444814451400540741c01c110f4036099009000d90b8420810400c0d48160307640c1e4130030710402402c5040081244030550040268507100e65000c80c081d90420060301454941c81600201076501003140161284d03207581c01280200041200250030286040c2d000e1031074000408050302c054441c0d03a0f555060754a1006200150007154007000c05c80c403020303030911920b2500340c008a0902c051801103440d04c4844100080302641755600c440096000381e1000d00400c418001c07026000c2c44666100c1c540c0703400ca45c40052807482620030380c1070000d9648640d00c04000c04440d02000441d0020001c0c45451388a4141400525140c88200e940303600c0d02280000d4076030b0701e000f0f0728120798050711441e0950781c0d020085004001c003080032145 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 51478852 1250 51477602 51477607
    0x120204050a060b1c0f0212060d0c030f03050324090a02091302040e040209090a0209040f0602130f090c030e060f090a120c0b2a0c030c011a0301050f2505 67
    0x5120510201078250030542042904c405041c180501342124084076032400842e00404c2101d0709214003148054010300c041c2e413040d1803042c071410b098504202d036410050500303a440d44510141584140514001c5050602d0b08401443c3d00b18003401040b04c1480c03080d085000e801c0019000500d030750180508050103020010101c50006030181241d0194105e01c011448200a000550604640040d400824503000300400d0455400040111400420003840c0d41508480e0b070080062a40665580301c001c90601c1c00c14548680c1001c0740e00c2c80c50b00450040910f001c040c0c14010b03100340285000328170540043e2149844038160070000c580000d1141880b48039400c2c06100041c0490b015154090196843e071414a1652a180784807a10280c08074030154154914a07080c20850085080342460406440343e95a02e0144101e003180100e003c0610715502e8980c240262403449010a085080114020440d55851040301849581c042d202000525510122400f40f07500700c400005210704907003005030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 51480102 1250 51478852 51478859
    0x3020d08180703080414090108060406050606070b0a050f16050f030903070807050a0309090e060f041e15051008120c1009110310061401080a1503080a09050604120204050a06 76
    0x24a40160707a4011258104c0006080180481c0c010030710506107411140c2075025494003004640c0e925018001425155860000c41c406507545000c4072042684900e00d1001c910f0321580340c10040c03100b1612014070401d00320015111070854090391400040c242c131118100070302e01c054680340d50002004800c02d0720042081c00c0c081440f01e07010b4441ca034400c2005000806040c58000c08400546c0d0059140300d0500700e4644c3c400c0c1d00400e07903540c440c0b04031903280a81c0d074441c14428281c0603a8101e4106c0001c2030304c000d5060040902808840d0b500c40d0740e091203161101c110084d401b892610070030b075040d00802c003440403d48442c0014403991440c1c1003100c4601c2c030400d8002080720070709103086449070034140c10186141001e20008142080e17860301004942d19040f0040c0302c81e640c035658103040002010000b20600d0f260750144902c49425440c680c0c90303603180d250004441d07110041d0100420300d0003a00107030fa03107441c03c11a0107480d41c0b244208201c1501e80e09100c081c02d8013405510125480c0c05022 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 51481352 1250 51480102 51480151
    0x30c04230409300504030b0402010309020603180606030a020907050703020f0106090f0f0c050901031104090609021201080a020102070b030a0b040c0e0f03070f1401020307060903030603020a0803030403020d08 91
    0x55060a0103407200026541a10920825144a03c0021401c003095000152080c0d0f810005490480f80c21201c411000c3e5158130048000b44a0000c00075400301000c400d0081e86101d00b142c02c403c04104008590450315a001010380d14611034070000c1d031046070007000071181441800a030083c10b21900480380d54507a40340020782903031029003040403440d69030b071064001d07840c450180501d111440841001101441600103000340b01e0810380074107050722420f10401603c0f5420441d030003000e003001d04000346a10b50341141c0107548021a00c20792503a085002082242002c82c80d4a03500c4d034160014180706140c40398400d000e40009215008183d502c0d000c6200c1071f11076000c0c034100010310303542d02c0105141c00c40400585880c042501340c000e81c404103040c8203100614005e5407e6172064404c4220704041c40004038558480c881c0c0050008d81026120001c25806410940c20741e482120010802a00c9412030703540c9010840c2e0150040c0d0210151440840c09030000c560070602600c40c808042c1c010134000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 51482602 1250 51481352 51481361
    0x40b1b060a150b0a12240803070c080f031207090816050306010b2b020c0a080304020f0414040f23030304061b0c1502120408030604050c030c042304 65
    0x110804151522451002049101001e101803c40401442c2c101040d8140c0100381c44080000300a03c641c1c0c4400d0300d5040e22080280700500340120040400e40b684030080d05407240c05c9220100c1d00300220074004202968081040c130b20f00380c401c0c0c004500f000103020b82131300484030281004051012030240840e842c201404040c1c0011a91210031201d03604c2c01c024580380c10702c142d002c01500d41c4c2c107000c5014038490203074074080c0c881020b901c900d80c8510440c050b24020f115601b4410485d01c20140320004012101d03020303500c11030081362080e00c1400804240004e680c1038418041400742003900040004440140d00b409403030083e1001340c03161441802042c0c01400ca458030b00100e6001000b04410807081c1d004107000780c1c450403d2215130810106016148400e854801007003001d56100c16952903e0586c183c0c0d0f40f602d4100c05010b0603040074200044268000e48002e80158101800a0f040f61f840d0000c59020740e50030102036141a140150241d8100090084c054030f034013034602a03003641e07541c5028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 51483852 1250 51482602 51482611
    0x5070c05040204091407110a0305090303120f011706010b0304080c010603081c0b0d0305090907050c030a03090b16080a11040314071e03020310020c0a1a06030709050c040b1b06 77
    0x2c000780041071002c918003504c4c1c5c010440d80402409542c030309881e44d404104400c1c01541402c1103500c0c0c0d0002e00000c0c3c00e6010341400e240e07046900703000700840184007052240c122880030059504804003012015100e00090158140150302000800c0000364980020080c006030240000b41180c0c482c3c3d40c1030b40350f0f4004010105400310700760a03401c00e1901361140025006003100d00713400440e020f641c090928010820160b110350001c80015502c20300900072240c49a24a00589075117061401000d00280800501a68080e40b18000a1000440440181520420b42d1200110303503485003200c1c009000c0d0b0b0709085441140131302001000071440d07580031440c8a112005400c3d01030604402407940002851030404070307030000c035040016803030200e0105101c80c82100b02580d1008070340200c914000034180010405913071241074409880c0c203900040c0c02058110203842825540e8200c1e070741174071303010303202480085000c00c400c11107400305500400c208140081e01400c3e481c0e000b075405080145c200c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 51485102 1250 51483852 51483869
    0x5131404050304060e040603050706031104120503070b0c0909010b0d02040e010e04021804030806061303020d061a03070b090405040203150103060204060801051c03110309031e060a02160305070c05040204 89
    0x8082c13103001c0d040911400c84403016070f0208850361460320781c142d907210144601420b05588018452111031a8821100604400f5441c240d40300384500c1d10303079940c2d80015001c2d43d00c0f050b404c0c04a0094903144085607401c485c01000d4900603400c0c00c60440c51a40040000c505d116804c000000b020541101c6060003004240030742c00083c54140140865101c04c101110000504042008002500104400d80205044e505941c07100030314103408004840c01c0e00041d620000411024080000a400c400c108c22114a0510390b1301c0050003c3c9a55444107008803454007030148121441814075074809a842030005040719045469901c15240d880000c2e04250358023500020184542604071a846005280603148038140e082040d800c01c002c1082a0002030400601c403c003c0170010f0b082090318200c282c0102a00c0a031702e848950420440700d8100ca4082070301840d40007460a60b40751090b19003840760a03400c00c1c00c0840300d65088549521103c1c044031118542d410128083e00c0c1c51019202410000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 51486352 1250 51485102 51485107
    0x90c0e030106060c0b0f06040b04020f0a12050105030a2603040311070602030913020a020a0204020a12110307080c0a050d020d06052e3914010501030c051314040503 72
    0x10040c1400c0d035809400c06014400c0c44501c182c0060a24501980e1194103001280100c2e110880000d01409441c01139030f80c0700340049005000486110001c003808543c90b290016100801e9400f201990424030070f0940c10b4020381c0400000c01c000394121081c4d117402079030365501d080c080d0043d001c4941013582c00743c0001e02c550803c000459030811501028100c00d0005505006000c0002140c11040f00c0022101c241c001c1241d6010900800c06003180c0e0750b0060040d500d440d1907080041001544030b01c0700030f01c94248105404d415800310112800b0340502c1d40c4030811a030b9015034401c6a0741c803105001c2c04201c0c08014041d40c000c144e02c05000d1280b1452804101c840c80e00040155a4202c031940821740309128108001070030140090707100840d99070509003810280c040840304a01004d000103d0501c15000c10829004242e000600545201714003d808542713961482358200e40003400b0060803400025020311043c600000413403100361000c080401e03c0352214100809980042d03600b00c0709648003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 51487602 1250 51486352 51486377
    0x120f0d060b1b0118030509030a050d050903010b01030203041a100305070e0103060e0d0f080c0d020c1501060f0903020f150d0614220506040e030c0708150108060609060604090c 77
    0xc1c00900445082e81c20000d01007071884000082031405203031002824024001488202603e0500450300b0458200c001e51303d01100307060001d0155800103500301e100e5440c180c9681c81a60103442520b00540d042414900c8524615102c143c2144d0090944080c0d4401184000b0004104100c000c002c2c00941700520990351652034108141c0d103040380409000c0e080301c051280c0444c0c0c40f0300109201c040034500620151500805102544140242b4034400c600014482d00c94000c0000c9030f015014200110468507a03940c00c0c202c50240115070310100140540c1404c0001d032610804560f44682e00914580c08056840030030341e0264810510450000d49601c030030003002c86007440c4a0f007003460a440c2c0c0410b040c030b9654071070300f88000500540310040d656804128281c803903903c502d03105070040c1c08480c0d680c03104084003a034844541c0700b840481c2c42044030141030000348443c0c0758100c82800e001800161100790412188400060034540c00c5101400000b40d103580741c8c00f90114484168407500e00c0c118a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 51488852 1250 51487602 51487627
    0x1e020702211506010f0807030504060609020c0106080d0206010e150f09070e01030e0601050d141903020709061a03010303110c1e01021515060307020f06010b0a170108120f0d060b 78
    0x40041c070403410710010b00b5045d444641c21a0307540d940001c0742d1400103043d03651072820074011f200541206400c1031001c168045401c0c41507100f80c040d60039207411078000541c82041241e4801d401d0190882c112001c2010440e2040b400320b09800d00070b801030207201c4c5003001c80c011904401d801c450f4400001d0405011004c0d07560140b007005140124203014111642c104800700d4608809444000e044000355050340321000820703c02180c41203203a5955001422840c20b000b560780740c0394018124032510341100083c0b003114050025803065148040c2c1425030b031035600c0c1501e004048084541650254134481c2c0312503980d00007160400a0710003140303003100d20030600080c0742c202c2c9024008400002c41d400c1c0706460300d1402c02c01c1c00e20307602150301d50350300d568000c0120f081404d18600d8076240d20440001140313801c200c5026194100c00c558603101c89841c00301c58610200001c0c42a120f81e90081d0b030904c00242445402070400b03160700303143e01d4a080140307141c101c2214656131011000c42c001103200401c54a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 51490102 1250 51488852 51488893
    0x50109080a0305011404050402030d0c0303090206040303051308010b0d031b0f060510050405060a032a060504090b0402120c0a110f060601030c02030c0c010c0303110d09020a08011e02070221 83
    0x16040d902003060780b502d27a010a0ba1050f82c04140c40078000b007098000209440f1381c0014641c1940500729544560b17a034034015050b40c101001f048136a41c0c140e0f1012502031414425455180c0008106414082413602e040c0c0d110700c00701054030300c0242c6280c0b200340410024051000804d206450000e035520700303032500310035480c03403900110301c100d04210512010f0b0303440844400a4035000302c1009980e001c0e90340707000d0042c90f00e43c1c1010304a0030220720000c2c1840d08800600101d80441405128002c17401c4100300483c8600503d00410121401c00700b1010601d003805461507121a040c00c0c040040f6090040e0701d070405a110203051075200c2c50412455581c940034100d8000d40c180021820540c000d0171980d169900d1254050400030944004000e0603c00e8014226110f1003945030b55448006004441c0a00020388050340500c4800b040002c000c2014172801e14030312500000d1124410808401e0006035002c500180da00105200c6103070400234406584d040c00004520050030034010078120012a00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 51491352 1250 51490102 51490139
    0x310030209060123030702190b04110f091501050c0307050319051614100606031b020d0f030e15071701050d020901030204150e09030702091b04030f050109080a030501 73
    0x4295010b0303107195a580401c45028036074115415944a46c0c0e03080c0124541000131100802c0b00041c10702c0c00301800601c00c00c540c0164001d070105072900c15040c00380110060b01000894002c52500c00080b034800c80f002c1000c2d24050149131035807600710740c0f003d07107440c54100f01015109500b001422400000316584c2c0c40b500d000c2903060181c1400411144c0c0b00000070b010501030a00140034800704134225080c81001040080890700b08030480d211800203009050000d035100d40c0741300041116a07643d0001070341540f10003860340c1d8411501400e03030040b00a4015416040803600c118141004144400700384103106032101e51b10905009102d09601d4003110060348064040c83c241131110740540c80f8220a02d0560350165808941c10703100c1600820210754a40c460b203070611100d418801260b00100081070070900844034040262209040d08440c1001b8448031104a0b40801c0200002040c0c1501c0d440258000c2000003940c1a0700c1d166128240d10000596001075941d030014040206100e184400c035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 51492602 1250 51491352 51491357
    0x2060d0606120c0509010c0f02041806051503030a031802040c2a080304060218090903040501030e031303260d1d150c0306040b0d06090204060806090a0201050a0504090203100302090601 81
    0x4101d90036014007944110317040e1904000680030b45030140309064940400e0340c0c1d4094810010721002c46803103240090440350403200c081c180b4000c600071126884204107540c0006000d5450051114810303070040c8030741000b0203118001122000e025a031140700c0e51715107404503103480d003140025415401d5904607004210700907440c040781d5240490300510030307290701c01c0e4040320050740c0358405005241100c0341042983e07400154001004003440c0040084d004586080e201405904c5d8a03158803038803809002c07010390040c48844000c0000c01d18030200140850084c00c0031901040c9154248c60311540841134210019844900f01c0c5525403c250781003607141c50b108090855a1818002e000090202810b00d601028012010400340d940d15881070021000c024181050b031621032418038003800e0b041000341e1141d481c0500025001c40045443c030304c281c180314040c000e030b0107060f8019142d5400445c1c5090800c00c050101050030107403071000710701440151080c29000c511710300c10042c0040004111904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 51493852 1250 51492602 51492611
    0x60c03070813030c0809060c0a050a050610050f060702040b1f020d0302030403020c101b050c0405010803040302010c150f0e100606030e0706030e010e120d110a0c080901030902060d060612 82
    0x844d50021240c0c20710340e84945440e6940201a0015140c2d0040102c0004640141e060603405c0000c0010220900d40c850029101151b80d0505800fa1a1415100306a08541a44403014051424400500300c0c1c520040c00051b55800d284081542030007502c6240103e1800d00042d40000ca03010003800c06041c420f032909620350302c0c00f550000d4581040c070008034042c6c00078095401301a03001c0d0940f08080c0c0454082000d0183d06030910540c0c51340d141c000c075400340d4a00707000491840b6001c402c60381600d4040c0c40c0d403140c80500340d41e0303144900142e12014207401d43e55480302080c01d206020f0317207040e04019402800c8001e0480d04020889403564020014540361050344404803a02007808004c176142d44c200001c0d2561041e0313043c3d02403c080b10f02d500c818000e103031101c040e034240c0501034403210711070410420400790030503441c041a200d4402d039500800d06145822000070420002030406200c1854003051420981d80401e05580111415030052602c48005000c844d41c4041c0038050782140c018240b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 51495102 1250 51493852 51493891
    0x406050f0403091202010908010c02070614070309030308040303020c07090905010b18150301060305010c050a020d030204060503060607050a0605010311040b041a04150b180f0d020a0510020708060c030708 89
    0x7001689113100d44281d40c4020307004042568000d0b902d5034001d0003070304004e209108180100175140d4003203000c1e220200b0b50f10503100f4580445607054412440d8140c403070107400c50a584095030316503c0140304600305a02004006014803041c0520001032212000200d80c00c04103150280c2503c0541c441c0601030240c08056450449080429a4010000111407e861002407010902610301508040c02a60a200d40312402541c030400400c01c00440c0c0d800d403140300b50145000c8040c1d01ca588501c90000342c0910114038a032428100501107548503a040782c91441c00c0341d40309015610241d00603039051000d540c01200604041c0580307142c02508548c00c00c050041442804c200c921001c00e480d015555564100c2b0078841c111008101605000784280d84403083d04281501c80b5a4a041c42801420302208000441c1814810380328211350041c9054582c50400301402240b5008102c07003011072041d101d000484035014043c5038014811411219a80c1c078260501914401018261350311420070317440c244 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 51496352 1250 51495102 51495107
    0x9010501080f240d120f02070b0d0f06080609010f1a03030d0504020301060515090117060603060f030709020d06030611040803030705030406110c0f070b0c0307140106030b0f0406050f0403 82
    0x2c0c0e1007203200000d80d040f00c961212500c02480d40da00059004034084c07004605009641100c0498003000b03a5501c1c03502c0321451800c0341c0b02c03500b500c1105030307040007840740b64003528994210b101c000840c10f0000035402e0741ca50105141490690784c00a41d45d40d41c00c600404600940101840d00b41000403001c0c0241c2044046a96480ba02c0b00c560080c48d9254042003c42d030342904034900a0070010500503e041580194030119803107030b10011301040c09040c004c0010920000d1862003404010a9107045079608014031510300300380c0ca2804d1341401034820106136280381d80701500080b074205a00082a60440c07a0407005c440740000d24500506c81071004000001001040302e41c00341e051b1911a8807500c45151000150615076441d01c1c842e0b02c0420320030452100001d140d26455804011500d040b41c4c3e034a02c51906100d5101032200c1070b00304000c0c13000452011003021030100020030001420950307a84403144896000e50f0100c3c3c1e0386480030244000d100043c011990860908201e0f40c00c1c85c00c166801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 51497602 1250 51496352 51496381
    0x702060105060415051e03040821040b010509040609050106171908070f050705031b09070c0201090519050d1a090c0108060409020105120705130605030105240d060605090901050108 79
    0xa134410400000b035103039600e010003500034a401d288500345c140c50b41014a00a6416008100f034294000c2c582202e104101c8450b4000c140690b820000012032a42800c041c800071032001003041e15590b440e5286000041d0f002d12410005100034045c0c600c81010454446050040c03007802c81c104d1800c55460300d000700c0d440c20704071040a41e001d0310b8030121070424508642800f149500c4075905001d0000241001c511148a41030841e6084904540c40d41d65100d00380e440b51002035000c4d000484044082c0002d05101004810400c4c1c008040f00d0001d6540e8001009600700120480305042c00450411031011007a10081d00030141c1c402915a040c8400002011400c0c020700709441180c507001c01100b9640100202c42c02641c0f810303100081860100c002400540c802c44003078602ea100d4400004070644a182a213058485c01012100c04040c1c0402803400007600d00d4605040c02c074100700d011810385041c45440b00400d500d81f61184c461003040c0801c4003211050b0300c0203051000c002c0402c115051005074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 51498852 1250 51497602 51497639
    0x3150602010518121204031b0c0501030e06070210020918100504060e0f0610050d09110307050a0513050601021f0e0705010302030411010819140a0b010201020c0709091b03060507020601050604 84
    0x70305c00302d039a11420b080758004000c0c1d03c1001104066600304080c40840803050341552420380702403005c1040d440f40240e48107401c540380b0005801903c0f2a001111894005081d900d5000700880b8149003000c41014021070161100750260242d003100304060304290041000824652058481c9403030102448420300360001d100c2481507481c005850f1100b40580269080006580d10400c1241107524080107403d0340c071344a00c1d1191140c4c4000007103034a415803501040c1c0d84083e00300c582803c11101e1080190002404a078154095149440c43c445811a5a5021610481e0000c0b40852030103440500340f61032500b2090425004204100100350868400c929007082071800c10003540d21040503646140a120b500d2000d42c1c00c01c030700c1540c60034030001100d001d00e038407500130409a881900160300300d1151314044050390700549000c00485000358804000d5500032042824482082c090010b030420307041d0000c481d0f1076a52010300c44e4943d030401c0040e01601e819207440d403030141040400c000710b03030a600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 51500102 1250 51498852 51498877
    0x51504061707050417060601110303010815040c0b030f10150f120f0f06091112010e070e1305010e10030203070b0a0c02030d0201091208010b0f07030315060201051812 73
    0x3400b15a02c81d00ca20120b030018070794681c1c0800c001100c030391003d4941005950f61030025910711b81c010140d20f0040700b124100c58402c802081420302051024a400900400590383e03504a41c200140105100001714402d03c00920140085c2c5007582c0d0340b03401032034907800c44c24802c0e07104030f5554002a00f04206e05480c80113410311802c6c066051005c200139151072402005c0752414512071086a00480c0c01c254184c5494420622034808400d10001d003030b0040d80d06044401c2080d200400000d18440c48554000d0428900201018003440c041142281c0b4007000900c4030f6a0355004104410041440c1d64001d078050280180951450300000e0340da01c25030140c2c100040e40000c041c01010300034076806240680c06025600903c14401d00a070037845905025110703e4040c102544c245031050980a06a5160000613403c103140c0d0401100c40e0303040380000314181076039003800c4103d603001c80d6803150080202e03500204451510144490385842c5411a5866a0b440b0b4010140025503403000e60b6030265000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 51501352 1250 51500102 51500147
    0x1110c060a0e060d090b0105010207080115050609120102040f0e180c091008060928120305060d06090c0f080a03020309120c0603040302010b0102060105060a1b02150c030405150406 79
    0x81001803601d1294084196584c0c1c5001c40800070000c2017110300341250003d8080e10201603940702241e00340c400503892400e059030700c0fa1051209241c24400380003010005400001103141c0e03244a182240d001e50010390209030380303110130481d0300108441c455009504075281c066100f80c010809d03903034100319004a4800c0114800058191950000b0742d001800d0f1602118618202000925150800e500e500f0803040c8015424a04c100c01c0d21121061455012241c1e0210280d220021002820040c0c0704a600000c807484000120b881805002e1205005010001c01740c2c1c82c003521040c6c2d8003800d078000641c640020307091001180d004800d4449028081c1c841c0440308075400b02c11030400e510f1429060380180040140700030b0640c15801402030000c20380807201586d889004114041c0a4500b03507100103120723800c04505450686203100b6030148041c200106403148004044200c1c0c020b060000d03265400800e0030080380c80c252481c0c00d10014008070640c603040c18008010301c004004400800040f103030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 51502602 1250 51501352 51501377
    0x607050403020a150813170d0e1e03120403170408090108151503060a050d03080703060807030c06050c0a021c0201090e0103020913110402070f030206250f02030412030306030201110c060a 82
    0x310001000a07c80103c07050341c400240302c228004003240c00407080c180c803d001100f00c07028584c6041e8840c8911150042d41040308150b241c1c001500c0c010012420058010340c0003415000c40c0e1011f5003c1c83c49a1505512200e0b2040010401d9000070945618696203032040c10881c1c0380c4824102c82840c0c550400c603900e50701c00d13001c20710b212080d60009400496140490041c1a40241502c4c040c84032540d090001c256175015040e039400590001030200f400d0f0081c10021745000e01c0c0202281090f01e01500c0811070250002495100303180c80300300e403010148464108542e400b000c0704020b41803442c0c5484403941150045042190300801495145a00c0e845960902a11003004ca840c488010015503840d42c042c6070800c038000032a0300490162081313001003424000c606c0e103004440d898804204900f0f03d0005022908400724817000c034250b000811000c141c035029a04000c1880340a610f010481c54598800140100802c04080603581c000204100055460070225880d00b0180c1c038020011101 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 51503852 1250 51502602 51502613
    0x3021f020d02070e0a0c0309080406030501080d0207080c010c050a0c03140706050712080c040308070503070210020a021e0a0302030708060f060a06022a0d050105040501051003021f0207080607050403020a150813 92
    0x1000013012740b89441c041400110590f040d000036060300c0c1c1000980c1e20142d1000307001c0e80c0e1416540030b20300f001e030040c0b0841c0501c0c2d4890100d40800c00d006804407200c480d450744507152800300390b4000b03a40c003141400c4461000a000c10090008209138a8014a00072003900c500c00e0199141c81050f08201d10708000c140f0a4841383c0c02d1318082c0d03420042072941c6150300e281c01542c0340e11103581240640142000c81411500105d240d40c402900600f0741d07420a50b80b03c61031803e020400b818a544900c00200110240e1420885003025202000042039503080c10f400c4400020340050460703210f44a0000280704032a804200d000c13281d43d083c840045c0c0c0d8444181d0120108800410701e540000c801303002002442815000180514000c1d0020085274541100701d0440004a010203508002650500981020594940c41c0304031001e2040d1a400b9803075034405420800c00b5a001c50000d24040341c24000e40c640842200f000f03001d5103508400088406a01501c071000c000c1a27504600d00c000e02c003106000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 51505102 1250 51503852 51503861
    0x3021002070806010803040501030b0409081b01020d1a04050903040b0706020a210507080601110c09040f0602070317060a0f0603050402030a05030d0c091d130c03021f020d02070e0a0c03 81
    0x34041c010783d59203607140e200ca0307a03982e0064454680000e0408084081c0f81c18940301d005201504000e07020319000320458200120820401220500d41d8200b202d00003880051203007000380512074014100e0345041d82d08210603120301030300d01d01c156002000200480300320304040b1000258005405615078603490030030390704a0340d24480e40204182c010110041c951080d03101510a10054032110f449840f1400111062580c46035030480742e030b00c07046a821640c500803404075070203441a011100083c290742e903000141e0b01f2850b030440208880107a02d18809080c040c2c07069100000b510002c0c800c0b0722300b5a01144404840c41058142340c1c1d6000442c081d51030070b2004010240e005401c803981e0700c1d08446014005c1520300b402000050b40c1107408208420aa80c2101d0200c00c10b80b100500d58403041e41c078092420a0b0281145d104064401c00001a00c4201d04035404000711500f12000d0080f000340079003041004075042045400c05002400028481e503006c03504206400c500240c2c0807040f0b0320076001031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 51506352 1250 51505102 51505109
    0x30f0a06030c03030906020d030605060f090607020a0306051602010203090604110117072307201c0503030402180402031b01021002030a1d0a0308070c02060409020c1e0f070302100207 80
    0x1150040110138140c01481e01e030115082c981c22140f010300700e00f2013182145d5043c000c144d80300300b082102d104030784c000d040035148503503000b80043d20f0201684c0c0026202c00c2c0942c0116500342c0c031a01000020070390410743e80c05643c2d00f80000d5103507181503081c003500c902303005000424040006629a18a910501c2d513904120380b070520305003503810034034009000441c942d400c103421080c40094010400d40418195042d540c0c3c004803001120100c41001c50680c00d05400c1b03a81c110002a40d0b10b00011060a02d00c5140c03070003031018507030742e060a005101d688854180d01a111010090031301c00140c40000b04248045003002800300b030600b050700102d0074400e107101624011400130040c0100601107034040f580030304014108034032005481014035150581020081c01155081c1f0014800318056545800c0c01072000f07291600c5e20341c4808415081b80c0200c84905641d90240c41d0605040e86443d107141c84000f071807001001481000700202d651903009000c02800f4402c0d030300180a020f4002c10082000d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 51507602 1250 51506352 51506363
    0x80d050313060f0e061611030304080a050c0a06060305010c03020301080c0112020904091419080a030c020a08070609030e031207020f062116050301050d02041a21060a05010803030f0a0603 82
    0x1880094000c0340e50380c85e010b50307001050440d80031400449500850122104000da03001031825651031b502c2c0e0a2454005804a100b030101c20020315400a000b4440c8594940c41003000144003815030415a00b1a400c026840d410b143c4100010f00008100145000f09a802440d0908100d403107488000301900a1520990f0024181100b800400c402d011b074203603c1521050440700007601c107104540344641480c9000e44031000822000b0300081c400e80040104200500407164842d006540d41c0c3c105070321860b001d4503e940c0e07030203042082641c84200c1410301071040f07004055a030046c3e0804031403071050007070003442080400200c03010b80e1545403e40c0c0b500103002d0504404454204007001211a040700c560b84420700c840720080c030180c0500d040e6410307280d002d01603c09000190f800c5c0001015240803e0400f040500305e07095450351046600c0c0c8a00c60840d10200700507003044034091408201500c0c0001c080e08007030042c02103400000a0340e0b80450401801001500d562410000425403038001810 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 51508852 1250 51507602 51507611
    0x18010e041802040b0301050c160c18020a020c0411030601030f060b0403120210060f030b090a0605011e0504090503160f12031b03090203060703020c030405040e07050901080d050313060f 81
    0x5801c040c1d501640e000361000d00041c60f01404140c03c0b24011a10301a00300c200f40601900428075441180680d403003981550f0313280e610b80107101d206074010440c01c1d40381c5d0780015281030740d20340c1031108101d001020360b801c1c00b4090501350009120f00004007100d04143d52106c15028816050304100003d002044400390350702e450303050010190440b4003140c409440382c08031864202c68a071040b04202da15480303280ba00d042c00d50750355000c04080648018074521440603100b010480d2403050500034a0101084030588669481220b01c00c00150b221a100b645880980b401065001c0f00b2a1031000c540c040e668011100761030010704403190000d01502c1801c030300724a000c40c1e503010791140c2880ca030b402e2009c40c40400381d0305d0218161451140000d4168002c2d40c00300356100d000341c018001200c05502036a05150306c030008502210f035800c80441d640e9100303c100700300d203003081c005a0307015081c244007624a01181c140301406501c4081d00800050070b00307000b040280981680018001d082ca95014403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 51510102 1250 51508852 51508871
    0x1090e0304031a060103061205070501080a0e0105070c030801080102040b040e0c13060210050105040b1311160308010906140607080703050405090109020c0609190305090d020d0f060f020f18010e04 86
    0x30f5400c3d030865807640482d180200108060010740c821807107066220000740066400c2500441e805e900103401081016200c0c2d668035000d000030b0140510902c01c83e0b4514102c2a100c1c00d00400054040c0c0c0401c400c1d9104001c18031035a244d86080300d00341c41500010040d1307078460742c19400e403074411041681580200700e80086221940400c1a900d01451501c0c14017190341c079001000220f44609020582c462801e030900014101142c1100141440b03404940b4240105410421001000c089080340025500001448a030303585120f520f010b002041440f0358204004804210391348100c2c800903100403808640322041511500494019010140c400052541c3d13031948400a504080541d620f580603000c00a02000800200e10245440c81c001c0d060785440c06840c20380f803550007820295004100d000100700035890301d0580e08405449a020711542c0d4015080240450701009140410b0344d00400c016112a130200e41030f52189417424100380c406920020041c3c484a44656059412605004641 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 51511352 1250 51510102 51510143
    0x7050303010b120c0a0c02010f090807060c03120212010302280f08010b0d030203040501050d0902040c02030919180f18050706030b041103130302070905101508060901090e030403 78
    0x101510780c80f440e02c03541592920302250f281809150500000a000c100071100590720030250000011054103100f10b1154070b0744a0030381070094580201c0c0100c1c41c040361081c10154803440f20b601600e0685002c609240440c001401d842c0410f11020b44141d504801d0424029888100109541c0441034170030001c0342d445640107040000c034460030002d546031010034800d9003001060801c4565065000d503181c60304050054615411540380c20761a1035580e40c44400503100c07403191140ca480641c0045444032804000c2225484084d0900c049180700102c04010030071010b10918103c9a03240c2d008141c0c500303000c4540d0003d22080750704071510080c80e4440014404041035040596100366000d1164000e00030138802610080c82510340342c0c102c2080010b2080884100790040d440c40f0340b065403852030742c42116000382c640603105884c21003a6601c0c03c000c814120104e06000b61424201180140361a10015007950014401c8040701d0342c403a100310307000a200380100d40c059940100300c05000c42c084001e6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 51512602 1250 51511352 51511357
    0x1e012604030c020f030321100305030c030909090a110907111605100905010503011e0e011710090b0609071806020303040b181207030e090f0a0501060f05091507050303010b 75
    0x43c1c0c0038440401c41d00005003004012140d200725580f00c4c0303030245020000030209480c001045060031241504011001901c10700080a20f00101c0c0f0045888501c040100410700e40080d00085c0f417940464860350010340100141215100100c80b880315541d58030001f501c41c00c1071400546014003414020303a00380e005910540082c0c0b281a500e05c840e40e00c10140a5540810318041c041c042102400100003130111640b810050010004e01410001d0381c8035003180d4240000e0300a0210101c4800305440c407020200304000b40d5a07803128061229044507100d0041b90040075003014011007510000408690046100c02080c0c04a6942d00321240d0340c07450025120b810a4034212290540c12010905400030030341e1400f0701503151009030603c88840c40211429511040c011428000103405010700c554844040b130340301394031111220710b82e03262140c200e9040b1350f0305800510900007030307403940a00d95500030142c42c5c440909960425804590b403110a066000302d14004026210020001c114030703401001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 51513852 1250 51512602 51512627
    0x120e0a030b1303080f010602190c080f0703030e0405040b04020d321507020d18080a030e180709140406030206031003050610060f030b0105090a0603050907051e01260403 74
    0x98401254544417070144070014280709540050348802e041d13030745040b001c0051382800c602c2203003550285961407042c00e042070b08000c0d42f002150814201002495004411600030700030848040290789019036404280050280c4064003a0380c00445075410003800d410744034625903911404c007039052004022400c02c0514090907003c28010426141020812494068050442600505070391014001c0c00c40c0d40d10302d170302d40c0c6c80c1c102502004009249541030060080860013650703280d9540b00c02000307004d1034080360070b541503d24a00508005c8507640c03000403031003910305000002c0c0c0c40714481000900504140c0c1c1019601040020900000420910700d40086900c1031050b55001c2d46c62503030080700a902403203a2408030b030007203010300315051095104986107081418694100035811000c200074a8481d00030740003281da55000d019a0b007804220002c0200b8084408000102c1c1040100d020821040310b058180000740c2c100325800d010845030b60000b1a490700e201149868542402003240c1036854 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 51515102 1250 51513852 51513857
    0x6190f18020309030706050408211e061509030a0c090504060c0f0203030606070311030c010608010b0402070302100c031404080301060305180606090c0c0304080102040504050112120e0a030b1303 85
    0x5100280020060003583d1240c00008069410700107291105005041d00074021600b04608200350110803500055112100c0003800d1812414030344100c14882401c0107164030161070340c0080402c80c050b80c803120307240d410100c003042c03080d200c0364080c0110749802e0313014900030454942024041200340300c03580464400d82c005d400601100e00c6200051311242e80c9009014016041040050058242300c0024294107219140136210964040e01c0d8605581051188003156515018108410324090151140940045030110314040c0d0994001e1358036212860390003219030b260b0842c0e54115010740c4c130842e0b500401807070000d1240b516182520a5500034080d130b1010a00c0c180108280820401100740041c210f02c0042550784c81c0d6004000b00c010740100000c0130004108901d240e28082070024000404100002507107450401040200360789050300446051088a05500d0101e505040190020036503418060304040345080411900c903215007000e04130218040520a15812481141540c41d01a5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 51516352 1250 51515102 51515129
    0x1060803130509070804060519110a230703030e0304050307080a050607021b0904020a05040e010b01030b18070503090102040b040303080105030c040608060714120103061e060f0b0306190f 82
    0x260100070344814281c4030b510004105d100000c00003500b40d03205640003091210504080808a030f880d000b940e0058802210300080410710b180415000040c5107160501080c042ca001410004528280d0103a4035001e400c01d81c03030b0740440d4880c4d1070510071107000c0c10010381502c4c40c568903150300c1a500d007180c210481d400d00c611341c0094112407010444269034480a40050600c0e00c10740100192008040e0042c0d82c00382290b103001030981d0f113a108880807641d0580001c2200d580310300000d8221240396070140d000e00200d180c0c4001400d4144000da90155040c100140c90752901801c1034024083c582060400420004e408414590000e041a049072001c400319103000e0750b08800d00040d28002e01c9512915400301c004943c96501450a0356950340610f003507507003001864181d42d69484d0080e882070b56801e954802c01c01c3ea164140008100010300d820050180c0d80c50080b07400399408942c4101c0f0200f03c8040702284441d40c034101d143d000030020a1501c454242c55414400070042188904c030401c4010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 51517602 1250 51516352 51516359
    0x2150a08010b03130f06020d050703050a06081c08040c0e0a15090207021305060105070b040606030c0501020f1c05160b06030615060403060914070b04030b0a0612030c05010204080106080313 83
    0x350b070450384242e413000c0b004900045182d4907484542c58140049819075028000c401d0000050b100c0c041c40780c8010341c0d0204460500d01e03044011240180c01445071a0005c0240d4001004a8000c803000c0c04030794585040181c0ea1800c00485801c1a40c01642c0c10b9130107a000c5c845404126004036031400122032409415564512922040780b08400000350007820600d2200030702c1c43c1e140e100a13400303181810402d02d81446a038813180c042c04101d4048070032942e110070501c1441038506115014040a000500c60380f9070303454070b0f203607203052640718140f0070401a511820700ba0700c2070041e07410400101d14885109550f0780303030400e031248084072594040d1007041c0c002400c500212000c80c000090142006103824290384076000640321b17016003a540700d040c00f8590405020304212440c014501c44d4002170300e6034110701e002550b0002c05030112204900381081070010010800c0b40140403941420944042a0780d0f10303000340a030055034040a40e5510300310002508201c040014501a80d48022500b0680e44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 51518852 1250 51517602 51517619
    0x30c05070e041a0408040f060306140103020f04031101020705360601051b010e0703080a03150308090904020111030d0e1020030c0405030a08040e1510030b0d02150a0801 74
    0x7040750301518007402d001900c20820381c182d89a80d0480c3c010f01016141c5500c607100724254104030f0348814002a80d50f2810040c07101d1111941003103500928048d403a010030440d84014601490001a181e40d007025140d62050303008100c080700900c80500101015000b891640b40c24920f094200001c0403906032380d200c981c159403490180b00310816142c139820810058004880c17440c03541c1d0f044101c0e6582c3c610ba43d003008010801100154491280341e50343d014040070040698101c14001d03244804170303800074400550001c0c160386071240141c440804595890004032008131000b504000c00780000109000e500700c45800c1900040c42400031030300108031019000044030071552050385408640000803004079821401141c000311480481c60070661030302c0c0040c2c2004032002044800d410001010840302c000ca00000f0383c400b0000710848201c480c40c2021625008448004204240c0e03503941d801410394649a11049054000e0002d5002c22031000180c00154004816074002c5520400006035148 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 51520102 1250 51518852 51518879
    0x40902010219050f0604050307120c050d0c0206120109021b0c0d030c0c030c150906031404020906010504090608030d14010317030606070b0f04060c0c02030c06160b04030c0507 77
    0x56041c0c0c01007180005001502c6064011068215000d0254412080302c501e420032059000c0e600a0000e141c0c0c07540305142a4601109440c155410300c0540c5105d100403030000b080440c5040e0796420400d142c0d80461000402034494034000c04102e190342c6002140c03001580c3d02400848507803040d100402c4408020b0745d6902e111000251741e00907042e981c0b038000240300301d200c80591446201c02461154413030f522204125031340e401c0391420010284054400702c2d4003030400001448182405c10040010107400c0414580003040a80a07003215000320300b059214000303c1d40203101001d01000607039103070b807242a1a81c3c01a007000d03200703d0504030380441e80d40c2003144a0b41220f5201241410100c924402405c86410060101d0f40c440814004031010418280402e44a0b00035042d2547e803510301441d15108071029a80c200b070800c4913100142005071000200307a000181c0489090b07854041d02080c2300030070400d10400804403078680e4184020075800c0940850080d20880c266504141c84101801c80403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 51521352 1250 51520102 51520121
    0x5010302090f130b031b0406060801060f030b061c02120a0b0612090321070f0216210206162a14040608061003030801080d020307030f0e0a03060902040b04 68
    0x90400051032014500307000c06140184880f0404100f41c00c0880002e41040030341403080d181c6031a04004030740c0c54a020320949016200c00d06042d840365040c128002c2080c4100e00002c0181a0f4520603ca0703103644500c01d44198207898074601000010300501600650405c20b010a6440100004501c1c0c914050023141c00103103001c0c4c25181400b5028020004079200500a944140000c110001c6d660001d009150380c44481b01c510003146040c1503a000300403a081c81e4041c400c5422582c20000d03007021804038101252100c1025442d40d00303040c0e0440c1101c038008030000750300c10400120544007020440313103481502d0040500a0410148080d00007030004101d0503400d00d0803001005000045400321009000b080281000800d561603003500d43c5010fa0607500009680e4000808000f0141d00c116034038050a8510b000e4651f224210713802a5881c042c40600605000054490f1044903103c1c1c0c000c2901420020000320486590b401c0120040c40c000e00300f640101d00704540d200150030940182a40c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 51522602 1250 51521352 51521359
    0x60210060f0b0a260c04050f0f01080a0b01020304090e06060307060c030903060c120903030b0312070b0609040f17030412020105060d08181807020c0a0803030105010c0312020c0a0b010501030209 85
    0x30003221400c11118075078050b01308042149416425040804003900070340c45240c00c0089155101e04080402c01513602c200c1000c1d118000d006031504559900c01c0040341c0008510303102103060031514005030700398041e541011444034508401c142e86848006541130041d10150300ba108925100d242c02c0342c599600d0b82000d00882e40843d402c10000e0420780c03001e08243e1417482c0140c1d07003401c91402c0400342c89a00030b040e0f0001ea10380f102c52405182c01c1c000401040c4002c010640ba0803581d50310000c41101c0100f613a0b108200c40d01c000350a1065004040d04065031050756078510502614085e4081e4100b0745068440b001040200e0101c03d005220f41030140000070300b4040c410400e030341c4404842d0301942c8e02c030648402d02e012120468451a60030081d010b13034184141c8191822020080c0752074050742d81c442c400c0003046010051020044201c078155a02844e00d00044122410180d03211140d40c004621124800548160141d00c0441e1680c0030328403412001d18283d030786000441c10b0740544000b0f56131 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 51523852 1250 51522602 51522607
    0xc030e0a050604231c0912110603220b0108060606071e02060c010204060c020405090304050604151b03020c040f0507050904090507030c030f060e06010b0a0503150901060210060f0b 79
    0x4600c0a1072600680f91910002011303c1d00c28115640c00c3c410314410105092911490007241c0c42e81002104029100744102007050803240d0f00c0e03071400740301d80c2c25100340a4100040071910714401440c418000c0540505a134000300740a241a04075070f8805d00c81c4151f40d01500010507441d04d49101290721a40e0403026450b9065900e00142c20031825100080768007040c10071035030f15014000e002a00003001d840d20b81c190019070900500c0103030340005000c82d895070010001407009a9502098070162024010503050649410009a500b1191024001c0407550b403446036108043d4000303100100c0c05030594041c00b262030500c000784199007050364000007058052090301a01c2c20150701c5544100d000c2c0742242c0700c01f0b50340d864081c02c0c822030360420388a034203141000c10b0034020503010710154888414010511380d0b2400c0021140303409510004020401d0001c04103040743c4450f4008900c1e014000c00c8a00c0d2540d44003800307940c0b00800c48030f611005050410025010b4648040d0404450400320f8003071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 51525102 1250 51523852 51523861
    0x60602011b11070905090709060801020f1c0207020d06020304030e01020c090112050a150606020d080103020f041107021203090a0602060108070504050403050f27061608030901110d0c030e0a0506 85
    0x46400c0b0604402582c2c6115251000658151070b02810780512500805003007042d04180400d000e55600e5008810039078010006081d03540d1405040b5910481d90f052540c1d214880d800300c40c4081d118284001c1d60010000c0324660600a040d40154080c074401c0c1c481d00c5201b640d0f400107a071500d0049110551010482c1c0042019400c2001000b01040c03094040d66000c0301c0c81d5444202c08400c550003011081e40d00c140a00044c0d40401202c1c82e011810309001902c0d614642c00940d5455003480002d010f561601030604207640220290340d41c0980c001c0500960f1900403646540c0c0e82c00040445104009038100000c0d51400892514149d1b41440f01600c04141080b0074880681009403048080040400031880101c041c0806864408408035404549004c0a140a0f0200d120601c9075881740308108031104005010303c410180306a400f00e0f505441e5590014918014090b01c071050081c1d42e4005041400c21000da4003010a42ca03840d10100000220010a540d548080307080c0242150700500101c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 51526352 1250 51525102 51525107
    0xe101b032906091503100e0606040b090f0402070807030206060906040902030c090403110a0f020312030c0a030b0112020d0203100b040639050303040b01061d04150b040b040306060602011b 82
    0x43c80381c0030f0302404940c0200104440d00c074a6500841c0c01d02401c00700720a041c050301640c55002c07604034808403004d90410f030a00140054030320841700840e11403210381188503255151601500d0150743c122a405840c5c03081c50a0181d1500801c80f075140c4946a0040041e4a46c640351085208a4ec0c0280c0140b08580d00c0300184688200050030680c24407407409008d4400351803c03c890507030980b03d80312520b5020a00c1c411b0510345a94805210400034003031081055100700c10098800c039003a40d140125220201d80010f94005510b030718001000760000451044200740c40e0010b600074917030f88600c4040280d540351103141c1800f86000300000500f00800d11041d140340c15034003448104140b50300e00f000e00e048003d0b000c0d0003c0b10042c200c3d10381d00080108000d00042e07007a040d0051032903052420344081d0300220349084040c8000418480d80d600e0703448001c015000801e101c040c080c40c81c20386549584480424100b50824801280c0755405d00c2c0380441c0b114818082e441c8014100f40d280150301010500a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 51527602 1250 51526352 51526357
    0x7060207080712021f1404020904030314100305070b0c03121503030301090e150405061303030f050106090f0b1204020d0501180c06020f060c0703030e101b032906 71
    0x256007118040c0b0081012407640780c001030090b035141e0024400301400340d03442d0b4107440505148041c00d500c4c0008540940c15481e41c00c59009078100c1d20045d00e91b889142c141c0c02002c03240d074410441e0400030204108103170074460b2a410360b4060700482d8451541c5807000076080c03055582c07081083d0000d0054500761342c840750607e03030000001c000c030303100c81000500443d20b5a00268082108540c5603415090300d04c009011211344044981ca810703449161a48400e03585200c094614882c11202907405402d02d803080d8000184d604002c0c20501580d40d58900060407070145004e210744401e03820000007010030f0398070120341e1001c030303400800301d2140c0d10350b020403061010204045d01c5135502d810301c1222481d85003c1c0d11003020b00c101c4000b90f0190402100920b014500740c11050150f00543c11700601c00303019819200101c2e49442e010600c14902e800f80da0400d01820039079407145007426080d881181c0030550f444502c0c000c80c0e500300580300e05240d03104081600710321010040308a03c2500100c82c14107100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 51528852 1250 51527602 51527617
    0x504060b0414060c06070503071101050f16020a0501090b0610020601080604031b02040510030c0605090607021c0212060114040603030c0314090d050f0c09040506160c020402040602010f0606030c05070602 89
    0x103013810700480c0b62400c0c0c241842241c0450009400104100d8808e800200821207201d480008114602e0b21000c0c81c01cac6a2406000e0951420581c0210078150f4070030400c45444581c884000d20200140c2c0c03400814120043d500c8500c030708030014100035098800140d540c102c1f454840181140d450716141076074200c160305d00c8030719448108640003026031514050f032806801e10590f012451032540c100411045825000141040410414506584e035864141c0c1d80070303a01129411114000d950320391800b107184d050004d4100120340202040d955002c03801604035030207400c0d001001d401810800084071030314000100450800c1e130301000441c2c41154a854070f00703c5d50603a1860000238800240c42200814400c4034541d00c03640525188607410300880c15882e405884443c05410315903605030315000000c1c00c0214032079203044003e0205228040c078040c260b402a000710b5440d900c521009010b0020308072641ca080741007000014080f0320900c074901c4619000e075225070074040e4558800002e0f600480 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 51530102 1250 51528852 51528859
    0x30f0c03090319021f02030910020c0c041407090f03020a0306020c15100807090603080405060c030d020a0c2001090b0a12020a0915050310030b0402030a0f05010b0a0504060b0414 78
    0x10542d01c0f24090380100d40004122600200320ba1a1810803040f081c906024a070b500c2140140107000460300001406c81c0c0c5141c0c000360141c2c403842d611020134601200110400e03030082c1031804014481342d08010305801303606680e4800b42c4050311103a001903103e0003072000035040103e1400c1000801c650340d0190131001b0340c60042e1080300d8039103000d14402c00030581e10704c604120309000410443c2c1007003248000412300d1203424021203143da102c00d0041e004a00c1081d00850000034000c8280e50140f007100d00140c1c048101719154611040c000b80b9080c2810300c102e0b054001c0d1400902040300d01028214080c40507910650303800d00b080c1c00c1212075000002940b051060700502c1c84c50b01c0c0d0941c0060204110329554001c811458405240085100201c0150a10004009000340f103101031009030140ca401202c0080ca540726032011a181c0001d0a4000c0c001552a03600c00c41003000c190400c14813840d048a001d00c4c015140d00c01c000c01c84461344103809000c1c004100400030300349505442040341c00003d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 51531352 1250 51530102 51530107
    0x9030403030f0c0609210201110d0e0a05030403110906180403050c01060503030f0a090f080a020f010504050607050f0c100915021e07050a120201120b040e030403050601150302030f0c030903 83
    0x41d559071382510800d1900704c560903504c000480d10075600703414100b24031005100a0207420303e2030449100d98481d01c82e00c2800c6c191201d83c0003003000010400301700b03500d0f48507003100c2d9602d5807400c0c04001d401303010040c10300c83c004687c0451514604280003950480261001d030686403225502950a94402840e410310b07952a5440012181e80900242884001184003140d4403180b1400c001d10060481d005080d40605411081c400001c1c0000c0c1081c01d2541134601042c203c0b01440140c80c1c5000300c3d8046580604005801404c110011603541001c180d2107003104c1c0400140000c01c900c880074230b034440000403207458081040102d0307041e5001c07148545005451030b400c1844603510001c00e000a44141e40d520a102c100070342d04106d58100000d20188258180f6145030f81d00080002402c001809616a1a6940c1c040d0640e1030f40d21407503078070039440d080360364840d980c1c9070032501c2d02c0f003d100358003031640201c6004c40880d001c0d0084030310035640807030051140e50343d054001a81d0b0b0005041c24a00d40b205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 51532602 1250 51531352 51531377
    0xe0d11030d02030705070e0103030909050c1e070201030f0506130f020f03090303040b09060103030807030203090106170c0a170a120e060406031a0a0e070c05030702040903081e09030403030f 83
    0x2444004800740305503010b10354809050610a161000c2079120090074080f80c001000800c0e03003c6400c40940b40c022901003025107984000d103406005500024241041c081c09107a0080318480042190074806c2e00c05015460380845003004032102107409075005281c2c1d00030054480303c6580010000c080c4804018107240c0d088902810640040710300f0703040340d48000180024843d40c50520390f0b006511a0041c9415030469400500b000d902910801c02c2c160003101003881480207401042c0503002000c1710403984c0c1c041800e1a0341e01c045040b84e507401f450b550640030804e601c44140300c1c0a2400302a0051803800b015a4450b0400304611104604001c2500005041a0343e20310040c0000d00b4666000f1400110041c035103448001480101803203000c00580070001d010080b180c0d2a406001030401e00f0142e5040c3c10914214410007070004d5105281c0429001015040441c0078006e260f2410700d180c41c6000c100300300c12004070540b8018110342c4288030810000c0e200307501c3d401300d075401031038050f8a03000c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 51533852 1250 51532602 51532609
    0x6010f120507260717121602090903031504020405060a05070804090614010305011202030a0201080c04030606030c0e090f0304150311070c05100e09010b0f040810200301060e0d11 78
    0x10100e95003078003420803d1210381501e01001284054134040c414006820480880280e1351803590f10680004100801d0100c0008089040c00d85203035009880303803d00c0c0c949090400d44035031044510100c0e0b0040350315440890f007000e1090303800750b40018291526080d5000b10a50b15900280812982d10004102c045075190742400307041e00400358003010301180300300b0400150076180160420352540d010040d1100160b50001411004130785c0a09100015840b96119540b4601c115003014104c40d041c003000000f0008a102188101d4420200c50300054030b500f41d045480d43d98040e8801115801800300340301c01030801c441e84502041900340091310200940103541d158000c80001e507003400a0380300c10807141c02c042c0c41d11321401950345041c0d0914050000011070240041c0a2131408032400b007980303841e00a5050865020300404012038024244c01006100980061264001640b0f01030b041c95801c1c540f0403082c1c9050b03440e95110720200b100c901d0184240141e600f4002c0c1c50394581e0f000d40740700980303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 51535102 1250 51533852 51533879
    0x203090433060e01080402060d050c040503010c170609130303020f0403230106050418060203090a08070c15140a0e03011401120308090609120c010f0c0806030f06010f120507 76
    0x400e0070010071034003450003078083c0103503800f840010b0602c11304204200c010707901d0200f11000c1912401000895480303043c0d8003841c07405140c221a815610300940300010070381140f48001001c503003400c000c03551f5456009218400400f5290440202407207840000001d0003600a007070310312900000c49080603503a850b6094010650300c2c0d200041c0401c0c40d0321448980080c000c0c0c0e40038100c00d84061008d240e559004000304481404013428a6501101227600388100307003c3c5c904525004110180c07a050281048100001c01d0b00ca400386030030124001c00e00131401030b81100c54142d01c0038011414010188010344114030202d9a40798555a9011440b86020340090a50b006c3c241c0d1440600000010746005001d0301c0b0040c150544607400346040101c0c80800013102e0031002d01100300c09072070706c03403d0b501c1d9805002c200402c405260b0801c0524107405520605035440b07030500320116078900100c16042529200e00303001d230b00034156000d0000d00480b2a000744201060388141e040381e10b0103986008c0d405200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 51536352 1250 51535102 51535181
    0x90f0303071e0207080c010c02010c02040e01021201090e03040927050607030c050403020906010f11010612060f0e0d180b0c03071a0f011406070b072c0102030904 71
    0x2c0d140308804001e80b034600d0841d0852107610b00041c000c2c1c034180186182e5a41005c1202070401c0001d64442003164482c0b5030303500380d0aa01400512080080340c0b2014040c1d0048004030341100b01030000020001c08a0058500741d001c9040070f180382900f8500d4002c090560120b0f6031990080d003111080e540c1d0800c441006c0c1c85030151000c3d04541c01c0480b00103041c0c4034408900d00400c48184000c1c00035903140c1c03404981110007420100b660441901c415a00035a240340c142c201d0b540ba052001918007000001108610720805d0104054107507202c4c80d20031600f1442c3c0560039684910441002c9900070540c6601150740c000003226183d9807000c00d00070075031144e051f44645030030100b82c68041059000095044980070203050760a890704001000000c2414421405a44030f680400070b0300c1d0703c0e1030b0b08983c000c5400002d01c950504c0e0008000e40750209a440c030340c01004480c8942d118803500000d0841c072900050b409140392044040c200700261200d080c203075102c040d604010450b40c802c0003d41e038500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 51537602 1250 51536352 51536357
    0x6040507050a0b09090a0e1f0c0f030509060402040b0f030708011d0a1703060a0509010e100503030a211803020610090b0f12010b03030d090519021503090f030307 71
    0x68107180502010111607400b107004202c09000c1d0403080ea0315140103c1d4010fa1040d00001c40403031555142e4030b024070f074444120354050b17124003883c030780e810641003170343e2840960715070303411541810200310115070b82100c00300e1031070300102d0224006241a03003124001c075400411480d000d44030000068100b8240c1e5100034050b030b6503000101c4248000d812044183c1001c9009040c1c89052501c800d04904017600e24070010300c10000c0001e2060b540da0400401901000c0d040841542c0c440c420000140c4054943c41280700e03003010001003038030f40041124402d10180c5e0310144089041c50310b40007031a146191420249468005001e0f84200520442940c0790080d0700034103203401d00018045400000e500000202424034400403040e0f2100070440044041c107440502140700181d034010f0040041084159040c000042d8180d24101107400100c0054061801e070780b100071800780d003000c42100c04a002904102003821809010300014055a0b01500450a03107850718500310320b0600303551049522501 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 51538852 1250 51537602 51537613
    0x32f0706030b030c03031207110a0303050718180b0d0209090a0b07030e070e06063f0405070b031807030b0a0e0109020d080d0f02070804060e030d0c0609020f03060405 73
    0x10380e250040b04140700003500a04501815180407945070311a0313a458018070110000401d0501e80308103807401c007660183c0b041d15032203a602d01c0c2c028003412040d01c00000103282d804841a2555001c03d0901c1110280b40301c4600d1010816282c001405500c0e04696201c01440544009612041c80091141c0000406844040350380e10381104500703805090b5104140c40d0400260910070009064025116800f040c0d6000c0c1d41e43d00006001c9208004914806000030b84103440380e0706075190010420342c412500c0381e403800503410804e210200100d50291440d880482c0c1040f40485c4030f4029900990049540408080f0418040d850a601d5900449545400c0c004002c601409ca21070080c0c081040d42c0203202c074000e5500090b03108184020064080007000400051490942c1c0c00b204a04442c4d42081d5141c042d82c2c03c1c9402a40c100b841501d01040128020600905d000b15030350410365400d441d0b401c0220034640f140760060462601c100e130480040310345148955070800030244a80d11031b500816 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 51540102 1250 51538852 51538859
    0xb09010f141e04050303041707021207050102071d01120f0c060f0e0414040b0a0f090302061801020a05040b2101031110050f0702040221160806010f0903032f07 70
    0x440b56490301c28030500c189210240000540d0120480c0e40180c0c010281c0004024003071a00d00c0303944075911000794480088040003041800c045034503001c4076001d0f026114280e580702c490380f0101c9141101d1140550360080140841140316101c034031038500079038541d1680340044d65040d0513261940c010001140ca0140c00801159011040d0b6980c1c1c0c01c1603400f07000c50f0307a05851002030100050801410340c4054000281d0740a01644031080300031101030140b009200e1420043c1d1030340f10680c1d9000c0e50701001c4a0382c04801005000b20361010704242d442c2da00c1d103468022460f0319504850390700c4003e0f408200d140d030710075500100094040c6010b40c101c03441c5840650108501c80806224030024032a0070301c928021001004107840715590191400b69480d0200386000c08171015109418603100702100500a2507000121521045a0386480724010341d101c030703c01034605804011800c000a803142c0d0b001d100003441550300ba440c0d0345684201c1d825054070450302d0580248200541100c3d54003610041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 51541352 1250 51540102 51540121
    0xc040603140105250503040201111914070f031704030c1512090503030109090f0209010b19081303030e010219031a011706090c0f0a09140117040b09010f14 68
    0x50f00030300c81c020603010501424131558400c54100044205000b000f0001406590141040310301c8848440181c1c1c3c12624401c424080340c41d03140038251381800386019007001946000070300806403007408080c00034041c616500c00701c01c4420154002190901804000b00003140c1d074000d00301402c250706407510400c070255002030030a4018503c103242d40d42811290f2000c60710200c02c80b8152490110080345420040c10034001c1e542068800a4004a012000040500d80341010f8031005051070700c10986a00720000407540e1000945e0281c170310408112044000034000e0b8001c608001e00003002604088036034008005d22030015590401082c0c503106000d020105107150f01040810908001d400c4070100c5480c88005880101094010742103079001c108e0820300781c4241c4588102070301907503540d82d2190700000e0400075035100c1c00b00d4001494424180300e6000da00d20720380030b9010314545d0340241c1c0c076911600e603801c002504444903556034043e500503407030b543c1c00b4540800c00c80c4403c100090800f2000c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 51542602 1250 51541352 51541361
    0x509040209041a01090507140a121a03060c0d0501051002030d05060111011d0d03060803030423030a12060501050412060c180e01080c010216090e1204090f0b0609010e010c050c0406031401 82
    0x990040f10009c000145c03d45420403083d4081141004001440030341d03c01041c1a45d00b030381240241c0c14456602044002c1c08504000c0401c5940e0903414003040c0da90704184070030390707089002460146c3c2003881045080e1000351710151b0f1045051402a07200207a0000403800c558070f006c0c81c1e04441c8030310001c0b40d508503010040244812850314082100b24030345003241b622400081e00c010200e03202110084407011055400c12181c04181e0182d0355240d059590180c10000c1c01d1624041060500200040f01e41c007440694049500d01242d52043c2540d9566800c002c0807580101c80501841604108a40b82d00c4250580a0a02002d10041030f50508824034a02105494062704552021b010f51843d031100190b000111901200007240b4400d00ca10f00b9400c2ca11010414249130101141c001066011078000010601004038200100301c3d10700240652886a4240307140410300e0b0040000760341d4418071000500c1801001076403201880384001805541c6254404d8070740c00c0703074a02490341c8050f00707214 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 51543852 1250 51542602 51542627
    0x17040b0d1a0111070608040606081501080c040902011d0a03080a03150f03110105030702010b04020703030b04050702010924020408030d0501080d0206010e070807020109050a08031501090509040209041a01090507 92
    0x202403903d2040202c032190382d20258040c0404004003140401e04214540c0c0102e00900030f1042a00d001c540c01c1a4880c102e0102481041650320603040e41000e0340c1030610401002c15010b945503000c1310300310318a420041007101103d40e003010b011040000414110070181c18100c801740c0d80442d00c07a03c807281d514030f4442c660704403c034503900d0790300c0410000e018444601281e800a0a003541c89646940b0140d0041100700204c54005000182c2c820415504d0760001c000c0030000c583c2002aa29017132007ca00721003140700014500400350b044190340456540084403a200c0e40d020140c03070310351142c0c1d0035070940c1c0081d5a42100d0540720760043c400c520091021102c885c2051000b004070351302d800c13074101c0c00140181001080c000c180010580c00c138801e4020824850700101107a080031158079005405a20489045d40c202d10004e5402c03600d503101d10600d50031984000d10404aa44030b41c0c08100003c5400792049a503d59440e00488031120104211b0b4000e0803400720000e018030b085500070f0543c20071a607 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 51545102 1250 51543852 51543857
    0x13080105010807050f0321040e0c0901090504271b0503060c090603060f10090e06030a0807080906090d06020904050703110a0305061c0606090f090203060417040b0d1a01 74
    0xc005001d80d0400041181c2207071421141581c0384030114000c00e04147d44050404c0c690b4a88241181042803188000c00490b01c0196a030311f5140e4032110004400d008400c10180026420764013001589003c1c0c1151800c6080c452507002c000c210004481c02c610000201290b00c0c9143e00d03024801c8004c42c4018000801042d4003030000303440c5ca41c3c0c02c0d400601c40c6c800c8151003203401202044298031600489076035030b01c01234443e0380701d80e00b07410019001203068400e800242c015680002d44505010404002c9168440e1041741880106d036110744450700100032284d005082804040d50320b0b40d4044103007800600689006907120030600610094510040c5482c0905060032000c1034200e83c0c140c04c880c0c9041c00c0389400501f81d140d00001503003407c403400c803030320b03041d041c0e030400d5420b0090b0760340048115202c4030bc0810200300511040c4c0c09603081c2c8903002e54140c009000060210300b00000030700f030030108280410301d4240c03541440b54136500300d8940d06555696480781c0340d03404c000c1d00814200801c2d090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 51546352 1250 51545102 51545111
    0xc0210030203070f08090313080a0605090f0c041d0706050c06010b030708060d0c09020a030f05100b0304030f05040f0303050a02010f11030a0b0303090a0303080601020613030504050603070c0b010902130801 90
    0xb0f0409408011070540001c100004000082c141101c2403081e100c03100484a40200c11704e542d40d508a5450344042802ea44413440c2801042c0300410015540d031002c08004080d21001c00f000007084003c0141681c00e0750039a100824602d03100d42e09210071700150580b610744648400c0c0d1001001d1411105801c00d044094082042c80140794101d4070072607100800b1119040001e200d0b151a100c2d4440c3c07940304860722400420301520094160b0003070015041408030411250303681d0284908040404c2c0b00302c010300394080000c100402d00c03610f0b141341d4410090070103602c0c0954441d100841400b541e44260005078010640e0030002e54203018202c8010452103051065002915803543c10b4440507014a2001d03035240103044850724148256400d01c00c000b0400c1140c156203040103071280b4000c40340c060060049000040c150b11541e14000001d64040d5146800e080c1028140043d950016000e0000d1240411a040005591608a074040c040302500540c840b01e29414407055207a440d001044544d041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 51547602 1250 51546352 51546361
    0x20705010f1401180c08160201090c0609052d010c03020f0f070905131101030b0f06070506180a0f122030030402040209040204031407030201022a090a0e0d0c0210030203 74
    0x40010b42c01261180351f609500c00e070a641a030045c082d50500900f03602d542c2030700060264020044504482064901c0d43c00c0c100c00507500107031a0f2920030340304542c0650504040040d44a05002c1d480310b4801d00443d400007900009152500c110720036000c1c0c05601500c024800520300380100b50708410106038240d07490040d966203c5000320580503043c101603a44807000b4096651140606c610400541a5a0344202a040094940c0350840d0125050040150601d0b902400041c0c12000c554202d01d01000520480d40c400350090b000b437030314100b042101c940d410004050b0301522f50001e00340100802001441c0d6403c0c44120690140703e103a0714803480000910700406500300c0307902030360440700140c1c0c500d44200000c000b40256000940038410200d00c5c10481c13403000078094250781c000d03001c84017500c0300e091a0b06200310030f15102590300c000c0382d01c03400c0392400c2c4216070075084a20a103001c21025840540703d880d000014030341d20000b5401c1d06414083d0b0a00700084820080a46019271840c6003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 51548852 1250 51547602 51547607
    0xb09100c0e01080408090a0b250804030b090c060a0f080c03010609030803190c020703030e0904020a050d02031e0a0201090b03010303021203040c12060b041d0601050103020705010f1401180c 83
    0xa1181e4181c1803004080010301008914001c45e40c44800080451b040c6a4440483c1e0b8a640c001d826290300c6896281203001c01c00c241c04802000d40e50740821134038900f03800c5540d0741c0745000c40034120605a100d0180358031600c3d95400b000d800390385000e981d031610142490100510100d409030610300104003c10050000c5c552200403501a6508840c0076640c139191415040030111001c0c0c0b40c00754042c0b80c507002c061096400304134101180d0103a900e40784141d030654108003410200307640080d07000224050400c55810000c081000882c0001d040d10170300006c00b8000d560b03400760442d21815a03003051400c0b031f08568000c201403003c2e0000c04101419581036a60103581c0d01c81c07a001d004070050000c0f000504110400b89010701410314801160403d1107030f0310b0010045d000b1102d11a11860030080001e4110000315094502d03103140b4001023003c2c0c0d1900c0300650003944034031b41c280c1d0203540324404034440540034080ca41080c0852040d0210035850824011210300200b180960380e5030401070f0189100d40d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 51550102 1250 51548852 51548867
    0x60a090b03010b0309010b1e04090c0506040303180b09031009020102210a1d030712050304031a01091109031b040e031204030e090412050901120f0b010f0504050102060a110f070b09100c 81
    0x10035103000ad0703120f01d91306000407400090f501c0781c0d62200d4002004810507502c002078106007103010242d0740e0300c10344802914140c0d000c1d2154180d0036034050414248000055040a84441c5c0180103540c0e071903002d0404441894110030720210140c100141c03180895501c0a03452003000c654802c0d01213070b0b05004c0002074a40e903491040d510108014074120003482003e008540c0210b500419103c034030b41080e50181e101c07040034481c4880d201c2c58041000c02c41c43c0b0030822115840d00c000c010303202c0c00070a40032113588045101c00c0c0540150f40c984040c5031054040005100b0b41004042d04181450103140040c040d1500280c03043c0554013517414800001c40040d0003000c204414207000c0d44501c18200101d5034000c941e0b4211410604000700c404542c130455000c8501c100080e619220040303a028000d48081c411485820b0050388528001400025954450410200100515071501c0c0051002d61400c1e04800c801f81c44500008061121a5908000c004804143c06909004041c036000c4050b0140 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 51551352 1250 51550102 51550159
    0x4030804030f2301090b15030d0305070201060902270406030213091707140606220203060316030302061e01050a06181a0c0105010f05030705060a090b03010b0309010b 73
    0x602d89164600304205000040300382c141d03040c0c900c0e25070122107000503902070a01104145c96100c0380b6008114550303120007004540c69000303002002c480707409500403001400c00602d10001c41d5a204000310318060940014800b4103480c0c042c4600009180c4010150780c000790b59403510451074210200016190605117410300340619800203203003030345418070b0f030000d0003940c80c42e1500740000070b420801c10010b41b402c0341d802100070080380c04c40d43e111014030070761564800c0d1512465248031203000700d41605130004e6510000180c183c1e040d03000c43e045004490201a00b040340582c0107c000c000d8021f0000d100c1c7d200c2c080118103100c000e949010080303195991680158030030040c54801100640349440c0e503410017400e85422140081e03004411140b000d802180401c4619400c00000040d1410400f0418059400040180c8442458042080300c00e41c820b010300000d20400601c001100f00288020398020199600000d50f40d10b440407450f42110007030310403544291000c45610901803140301d44031981 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 51552602 1250 51551352 51551363
    0x20306010912030504050d0b010608090c01080112080f03010303320d1d0d020c0418021804050a050304090906060803070c0501080604090804080d020c0102061303050a0e041a03060c0403080403 84
    0x102c0c28101101c0600c00c0f50000c0d50005a405445070810000400c190b0403a01c0f079982d004503640307480694603203035020801c0b42800183c00d01d00610003002d5130028442e82e2071140c481e01c1c0c500a0030150080094000340d01c1900842d031140303140c06101560038080050f001403117030700400058021b840601240603061030f45071402ea0300d00344140401ca000c640311021182140442e180205100c0000b940d410010515500482c10a0718850092401510301550994024a0000703150101c41d41100c03000c0d0000c100f03503954400c10540d000403550074001000078255001d008114002d940c1403220a0740c1280e03001510369401004503501040310400e1220035035130240303041192520303002c0000d005842e0000014284c00400503000508441c001a5500d5a244a40940311500d03031a80069031680c00444540751800d4944d0307021000a8803d41c0180154480e9041076545191104081800c4404440300d6018284140d4031001a500e8108042540701a21000310303407800f41583d403004124003d501c0300501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 51553852 1250 51552602 51552629
    0x5030702071e030818010e010302040302031c02031b0706140403050c040f0204050418110d2409060c050d0f05060319021c200f060a050a03060503120d0b040203060109 73
    0x10741d003080c0c42e048801503400582480c0c48000d00616405070b400211034290110703400aa031040315501a0084d98102c0340c00030f01600030040d214080460112101c0048011400304000c0e524a00704080d04421030080000010450744d801c04c080a00072501020141040010030f03c010000544000f800c01c3c13461005039004100c9200140011020340600d810050348a0304046012040c0410283d400300902c3c0a00011002000080c052140305204030380041c1002d00d00100020342d0013180b0546111640786400e0000b40c5920700e485490496010003028030014400288244840820740140c0307258241848040255082c1a0b0010707548a00d4001c2403080c2400095442040d95240324516500b505180904ca89070b03022440c01c20316640f005500841c04210001c4642a0b41c100317065000d072107040281c411031610030741030f0042d01c044d00100c4a5100b05601c510000c5842e480501808030341000c540e072101c0c1c66541c2c84c5007140a9400e11081180110710510402c01d490ba40207034501c0032105070406281 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 51555102 1250 51553852 51553889
    0x10309080a030b03071527060504030f0c21051606090527010801020912060603060a020304140d0e030705040509030304020105071a01060906080f07080103080c0c0d0506090d0503070207 81
    0x905000460b1b0004221134040d4a41543c02c1e0f030400e10500c0c1804080c100407101003025602c0d00c0001d0b44901850300000c40600c41400044d010644c20008240102e0303111181c1951030600119240003014044c290074051101281003020400000201d90315000b1018002070400500038840d100c01d104041c8a40e4140b4044030300700320044401040400d000740c2e010051340e124191a0b000c2d40c00700a189014004103510140d00040105426000c3c100090140c511603e0700c0b00158080d40002e4401c1e50589140d1903600c80d40c001c20041c0d0007a449468076110f000140400800d0304100803036102c1800360b410070b006c002c9032002c0442103079401a42401c1c85510342c8054100f03117110511100c85000d9800407100042074460300400b8408c01ca6040c1d69800045a03201c070031003110500306a5030365001c10028070042c0009440d0078080c0011b030582c1320803102500305a0000911b035500410064400d904a0301c00e00c080c3d0f503070502c00c1c1c00d2200c485052003031030360608410082d80c510032440380240c40703040304000e507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 51556352 1250 51555102 51555109
    0x807031a010509130207050706020d020607021b0f030a05070906081b04050703090c0303050304121b030309061e050108010e06060108190b060706050708010f060c03140405120f010b010309080a030b 86
    0x80e013040020b50400c64903070b00c0350324201e40d03124000e0054101520804032034090f10752002a94030f00c113521550140c00c0b161851208000140e03050079280b648241054240761640c0c80c1000340002c464080c03c02440d0803803510090790100d4a40b90001290307900302d80c1800c001c0e00b110b481c0b2034000d80e200b510000382c0d039500c03940e0480c010150a0300081c850884000300005155014020354007a038021b420002c111a150310701a510032002e0000d41c00100300700920000440e00030b510500000d0702544d0041480641e01c501f0f550980d120070a0100500e076500c00500c00c0c4c180911541c0300c02000c5100401030f900b004000a4034a03240142031059020360140283d01c41d05d0141c0089041c2d10001e0112500e507009c80c68948090041144c84000003040c11000040c00d1001a40150448800741c0303441d402e40090381c4048680b48a183c094000c4010708000000e107a071034030040b5001c00c1c0900409804401c1c120b4000909540c3da805206040604240440c1c0214400c0e204445612055060001d1070a000c103011 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 51557602 1250 51556352 51556369
    0x3081305030406081503012702010915030f0b090c030105091009050414010c030c0e130e0601030503041e030201050409020a2319020a0b070813060903090302010807031a010509 77
    0x2800e07400003041c00520203803c0a19a8096082e01710480d00d213040071401d044c00c80c0d00c108201a100708070012006200442c192426840d1230041c90895101500c4d8655209200c62072821100026515180ca48030391090340b04240d040303c0c0444500b59141003248440126000600030180f0403641070000c2144903030400708200080646402c1486140303400c2c2450000f201000c1b00c000880d50900b416209414484e02c00d010300c00304952103040050f0f1101041c40f8152041d4544a0785040c0d0301d500c0008542000c0003807600071032080000303641c0c03030b03081250800d0104412614084e403201d0b0030a081c001030b170300902941d041c1c03000c0c03500040c1c85826580003100c0325030f40071042c2000c090070300c07820070003c03003a501c000c0a00e200c3c40c2081e05040c0c88801802c90b555040044003901020102c800301e58501e1050b09d10710b03000b603c011040049080c05071a4138040350a8540c084001c100718490400865170441207050780001d07a42010403c074025003142d02148514580c0d0941080310005003c8000e6864014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 51558852 1250 51557602 51557641
    0x60307030f0b10051206010605160c08060402030d02060106020714040b04050414120f0706020d090503030903030403020601050f0303070215300a0b010c110a0e071e020304120308 78
    0x1420704480a003010b40c1d082c2c00688001c1e06078403000002040c241040400104244582030042050341e10f4041c0072111500712189030a5080c0250b0601d40114403005c000001038a4014041c00850a152040600d4030000030480e00942d0024001084000d03008200714080795000300d5415046c003181d20004000309010050203900c64601b1083c001030100c02100f0705100e861800803110000c0343c4a00801c0180542c45034060300340d2040080b40002110b940242111070f41490300854403500a94505003141c10031070f503100c8258804800c000506604228850042000b620805819101280825207c1c4221034001c5e00a030ba00007002e0201c25207590071a0407200360504207040b4003480f0030145907411f008044d02110000d0304004200d50140e1032180010f171800507181c8900a03001561080d1003d103142c401c1e580e0010b440100001c0c0550310b101510303c95105540c460400301480d55100070103400c1c0041074000c540c420700c020300011402c140700c0c0d10300c942c0504040d05503a40300545011000c00914 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 51560102 1250 51558852 51558863
    0x3030212270718020c0312011e06080c03040b150307080c03330a09020411070605090d05042603040f05090114030a1e020301050103050d1202040e0f06030703 69
    0x42000250244550700d0041e001d040c0000c984101a41003010703548060b1401044002c440243c0c890b11440c4140d03005044804100003074a0a04c00d0500d207824000c8002d90140962040324000c2280c052a03100c0c004002e030149041c844054140310229000301c0c080108000e00041c885004224525030b01c00c44240c002170000c0071104941c0d110007042e9220080b01d11481d0080c0314005012208555414038421540000c0d10f408503604d110368190030488402921019049607160f6046001d44c0300d80c0112070199941c1d00090742c0d501c5451808000b15500100f900070a90000c1c0c017907100c5030368494200c8045442d8151030b841d0150b808100c04054080382e101001c41c41c840041c000500c101c4a0500034121002218104016a61000e0112890381400c1e0b5181e0715401100f102c00006a901e11894410107048003c2501c9503259400302c3d0842d00300ba0003e8603260312950240e0b402e103502c500a01c00705d10118100354149464050800066000a002070ba0704c250a20000303240c680f802c2102c2c4000b0740d00074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 51561352 1250 51560102 51560137
    0x60218030601030c0501030f05090303040f0201090801020307030221060108160e09090d0915140322050c0f0409020f040507020c0a0b030105010e0402090d02010e0a0b1c05090622030302 81
    0x81c41e15440503403185c0b15060100341031284480c0d010807544110343c4101d401c031014501e15911a91150401d100c80c0801300d041c8166000003285909007440990711464094070016524020801c100c24208821102800ca0313034554020042c099a000300004e4001d2002006c20040c0c030f01b2910300b40d540040d1a0400ba40240109081250380300000900b01030942c06502d4100409465186440c03a4181b02c90444000c0740003441d88502d1055103000442d44942c203c005461000c4410f0400b03007240301000d805a4907540594688011031a002021918540341205c04100c011140d0b400324000709000d42405204a903194000340046009220000d040c150003405000801e845480341c40503034000303010f01c0d0300190380045c0d80b07400c50074148216400b940d4000c1051881801d0799004441569034022020b0300000b042c40d000070b1841c1000d000d04924851910f101541440d0080c2c0e04046900003002e820385540a4030070302c00c1d040d80d500c255040e0360bd080c0d45400448003690600780c0180c0b2505210b2558003407003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 51562602 1250 51561352 51561359
    0x904120e03010f090b1905010e010e10050409060903171b0702060403050f060702010b09040c170c040204081b060403020d030f0314010603090302100e120a020c0301060602010b0910030b04060218030601 88
    0x458106500c00d176100d200c2080f9186445030054101d8071700340942413000344200018400101c0c0030024960089401c040c9030b040ccd940ba080481c0940300c036540101d0761503889065250405801c080e0f07030f185411541024244500e00704500344a0300744209080c140c40b000c0041e450096484480c00c484c00303190442c3c21200ca50440c8050580d07100c3c02142c42170b006510304005003146280c41d000b280e0056401640440d0b4403402c08204141ea611120b145954901c80d00107842030304c0e20390380041c200802c0c50b0f80240140e440c1501000301c0d808070100b0420700c5111300308014001a40d0f84254900b8881d0549040782010b0001c080903030062082400d1250340310340302070002828580c982c00000103244030340d0958854400e00f010601c1554107100451216170040384c461025550303000c1c00b034049240703644100c50f140355800010070b0031615140c01020060751980d6503100c1d64201810007540080707402d081c2c240340d145992036081180034054001400b0303a1300054441d80c11850116034900d440d1000302960701c40e5170f5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 51563852 1250 51562602 51562613
    0x3020a0302090a0e190203010509060f0d0b160f0201090206070b0702030d110706060503010213060e010203090a18050601020a170d0e030d060e070306061d0117240904120e03010f09 79
    0x1142d4610240c02c0052040321200986d000f6039048400281c0310003460b40341d002c20442c126000d601c0781034000c0d007805040804134040d801c0b01d0b401440d054980507085000c50320f00810000c015131134103041d68100044400140ca4100840f1105500125800c030503884a40040b03081d0701c18900c0c0c0414407070501d41a04200c4500c28001d2407144d101c2c807400c0044c159550241400e138060008040c0d030003000200c0c00c00c40d2a02441d400d4104c0503051060f2840c01020100060031158290000c01810170300110401d000030b840e01c50030750840024002032110301c141303036504000c01c1c101c103099401406001c182d0032001d40d880d80101e01c0b259100801da0341c42d041e0300c56604008200900c0f5904405001101050a46009204a20903941030703a60301610250102103c440341c0fa0a031401d5410403040d0850310b0310030100c0d261194000c215500400e10140301005202a00c500302e0b82406210722480d00500c00001d0104c01e860304042c110382040c0018132080e030700007401804910884030400e030600001004210 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 51565102 1250 51563852 51563879
    0x903091205070e0a0501031509020102010b040e030309010c050c07060e010c0c030609020a0608150913020604030b010807060203040b090405130203030301060906080112050d080406020702030a150515010f03020a0302090a 96
    0x43c040b40100d543c0b82ea40b2140041915020700c0b020b401b0b03220b042061000e204c05500038403403441c01800041240c90100c0082000c035100303000e00c031030990008814882c03145020b00606000065528015050590744600651595400c3c82481c0074000f0300b0030310410036405004803032000e030740003007040706426600d090103800f402c5200d00c200c0c4240340540d130110358140034010072401400f610340303180421a03500d420b0010051000d0501036109002d80280c8005a503460000d2001c2c51062191070095450162858a00702964020b6001c3d504140400c1c0700406180f800e6507a80d040440e404102c984510b000342000041041c4041d40501000001145c440c0c1c000003000120382082e6194032890781e0300d6010011980c00303503800402c00e40084110303280742440340c01075039040b45c040c150041c40d0141d17550000e4038280c09010120b89015000c080d4030310307101042c400c0da98003600c40b10310081801c40c2000028000040281520240b55000c10680c1e480751003a0b05490740440c0c054580204d05440b40107404900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 51566352 1250 51565102 51565109
    0xd1113030b061e0d020d061802130203070c0b071e0203090a080703120806060d0903030c080708060a1a04090e010605040e0f03030712020d020a0809060105030f10090309120507 77
    0x300c0342010400c40d041401011600748280070001e05805143d10400078070804060040e40d1140f06042c030040810003d21840c21125014140c90b075000a0b288140202c40d8008101144103d105000700701c00c040d040b045a054480d40050140300300e5541300d00644107100d00c2000f5155440070500030107000342d0004014100a101201d005185559413070b0800c2d44c030445400000c01105a1150519880d805203a841d508920020916402d0132000004e9004450795030000707030b00080e164410740b5001c2c4e8000300c51641006840c43c2001c4103142a80204d41c901d00c6038412030326211400071005000352511400c5e5406015248824860700000b104803901800103070007072920451178030b8030625400000245009610300000c020310300f196100e02c815900b110313042c0c1034010140c0e020849010344118510007494042c80c107480d0006c007410429030762458840e058000e1402a40030300740038950048006840000280500390115004586143c1140c01902031b61050304c07501ca0a5054108000300032610100350f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 51567602 1250 51566352 51566363
    0x2031e0a060f0512032217030a090501050301080d0c02040e030a0c0c08010615030b01020705040612150203070c060207021c0f05010c0807140901020703051204030203070e070f050d111303 82
    0x240b03621030040112084e0055081da040e03a1081104001c40c00904042180c0750341c4116614480c0c40d41c900c02c101102c9003024801105410014080e0b03c52900301d03644c1d8014100a00e0120300b15818940b1650307403071003409180d9040c040ca0340ae104045654a4020305050441d45060702c0c2c5030440b6010117444070340c810004441c55501100041920740051180b0310803140c1c0700403142c58001c5040c206900404503070801a04501400ba0042000d031180e0284000402401807182c160108505200c080203050650b022040b5004000340712100740c4c018400f4031703030325004800165102c086200140d205d010328000c514004565034021700174441b48140460798140030b031009000c0007035010381c11128410100d41c03001c08200b40241c2c4444582c0d005000c0d00c2e941700180100d03480240c882e100d01d07160400349d413011010b81400040600441c101400f99a0050803a03821503c82820710100c0a030a40c1c0280201d1000c1200210304d40d20003411a0f040024244480c1440030b40d02c0300c1c0306114000403006400161070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 51568852 1250 51567602 51567629
    0xb0d020a0915080f0405030d0c0e1003060b0a031a0301050106020606130506010801031103010e0f0d0905010201090b01090504020d0c06050702040c0e0a0b0a0203121003030e0a030f020402031e0a06 86
    0x103a04505111100144807199a00000f55450301d1032a01038030000742050703c0b40d100c02c1c080100308094a00c03d00100410540350b08055049520030000e02800408250041500b80b0780d04001e120f1a0b04203603401c1c010a828042100020700c0d034114031030020011802c0d411b6082c00000a1401e4000c2620703400348100b1350b5503005001c07050f0710600c25200251402c50000b61208010008a61020f03281302888130010b00224030803c16000b4185404074000080d0295006907000410726600500001c000b400203000138001c8004c19100d100540c04148240d0910a0700d81000404558901d80703124089039001540c86056a1a401e00601d29040024200d005501e07108035071212078011084040c41c7c07a001010140b0560406600d040b86412051a85040d44004d000d803c103c1c1148e2210b0601c202109a8041003480c80d5040051001d806610354500607012a8411b2002c01c4040205d0068107070140d5000d42d40b5120401183c0c8a00300791661002c54003043c809000c00011503402c03030b10848104200c9400c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 51570102 1250 51568852 51568859
    0x307080f0a0e010c080702060304060b03150105091003050c0d030c0203060a06030b0a0902090a0c0203040f03050609060c0406050403060b060d0c030f110c03090103180b0403050706051b0906090301060b0d020a09 92
    0x4031051130a03500604589000d0040c0e01c018034040b00115880761080707c010500030000000310346810640b050b07041c80040d20000520a50906840307880e40b0542803620b8145c410302d180c031009d80314200e502049004600340f5000000b414002c0b69858003041d070142c1121514905288010010314550004507410304000000c0b40c0d0415143c0942d92255400805ea03220a84550070b0010051683c14004c00641c001440006a80d00d074082e2240c2c0118011405040381c1e00d041e40229092100c01440824001c1c000d02c028001340d03511005490903603901c404000780c20001c0c0800107500d13000380e01429403800c2c00c110381e64481030380c90b41100ca50381d003d043c0213002608007e04801c113107001754008024654810b10860b0074541c0301e60030203a00c0740007000c400408050700d80c070760303c100c104101c81c241c02043d800a4540c0c20000c131880f40d103600540010008090210b0754034418410b2080b90320091044402140118184e0f800307604c02c070001c1c440400020b580c1c04001500002030b400002002010071801200003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 51571352 1250 51570102 51570107
    0x1b0807020a080601060201361103060a0b09061207051c0602031303020d03050105010219060905010f14070c0c060507060b0406030302010606020d0201021c0203090f030d052202090103080901020307080f0a0e01 91
    0x2031005030380241d903070b0403230b409000d001c2d04101c0794041040d03841d110041b00c204403035202484802d01840103805c02048000d18903007440050705000d000b041c003070301494120380d04000010840000340c0f2000c403a2030344500081c112200103c070810380d005d82501d00c00018400c1d5072203030104000304984a41c00b6902032805903c000e5086400c248101c0e8007581128142c80003c4800340c450642c114440e80000401d8085a21180d0841d0600c1211006071030380e40c83c1200d45160b501001c0c5501c00c002e032502e81d13408400d5680d5940f01c480144141001d102001c034085040103600c1d04a050071210140c0200140350f43c900b4020b018200c02d228410160103080c0300552058818000c440c09050a03109030000300b03880710342140080d0b000602512080c041c201710000350b114148000c2540400e03120b404203590820011201c070960b410034040d0b0710350b01c4c0080300c1c43c016141c1e0740e0201d0449400400440d225401c141c0184d08500c0b5995008010a10010300b8001003409034015000a01d015a24000d0803c183c0005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 51572602 1250 51571352 51571391
    0x1b06060a060c030801050f030f010f0218090103030507020d020a0801090c05210601030f020609130203270a032307080705010f0618020a0905120307030e030d1b0807020a080601060201 80
    0x780000e10b4003001804a41801f4060b90440b90703010b01280c03000d52202e91907030300f1104078038110000303e900051440340b0200380700c1c2e0500340010119030005055146507170281540c401c0800017030041c0680b040c010255074900250700014240c1800034011018240340540d484c648a0082038030448400b211b00783c0a840940b410400480c811005025903401d5860740c02c3c10034000c0000700da001d003080044050b05c0d04c95400d26204e070400714002585900b004d400e18075a1080c00010081c0d698501e000c0c10860140002d45da01500381c041c01c0407840003010901e50003008243c81c0310f802c000f5800040601c20018000001c00717119000744000c0140c01740c2c0d104034809440040c49400e09a6810070605081b0420750b078001c01c686001b900340f9600f01e80d510404680640845c0419a030590404985001890b0704a15440c42c4103008801a0840c900d06520141109000318451440304881144050030003889104980e1000d40040903d000940d5070361000b60b8980d07017409488015420440d006000d801928003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 51573852 1250 51572602 51572627
    0x60901050a02130513060b040e0702120a14071106031302010801080a2102010e010f02091e060409090206070501020c0604030908150c2b06141206010e0603031b06060a06 74
    0xb06600e0181c80d000420000d1401d101680746155031b1000c2c000f840040c2c11001b40010900700c0c600407543c1c0340291010342000b860015070303802d8a0040216404a6501c4120001200c4161a00c5030b00c81500b818132a01034901c00055907040030000052140d0f0008020800c080e15100b6603915038a0307030b2504c0710a41c54090540008110b5005c5601c5e61032914400e83d400c075244070380e9100000c0d04030f8414010341c1c00c0d101c845040c441d80640c00035110b80c442c104034000e01030302c042c80441510001ca000c0d021802901c900d100c1c0003080e0b9501c50306041103580e80001c803040326400034020340d221040c07401e006888182c1540c0841c08606a03002c0024103190108808254050401494040b80d8034803800035101d03440b01c0c448191940301298056a050081c4849944100106400280080c1015001d41d8441910000300e0b102d43c030402d0840e20641000140d081c19140101e568510980701c25003c079280d8014081049207084241d041203400c42030000744a8850349003101d034508000da03034402c1076584020100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 51575102 1250 51573852 51573877
    0xf040905071703071e060c050c06060609060906042d030305030a090201111504140309060d0b031509010e190b04020d05030c030f04051e01120c0309020d0302060901050a02 75
    0x9100304010b00100c0000410100036a041d245080c0303841d524031000440000305666000c0e40b05000c40180010792141d00710a0030b16040061500701e60740102135492030000c004a20a0900040c1c40650b07480e01400c2e00e041c258050300268032a034407000200450610210200c40c0740c4000c1c3c4400d0200b000313800412080313a0b0180c440a1035602c404c1c00003000313481010f03020384c14040211540341034401d0802c031105112001488041c400c1c2001d1516080c0715958040004031a8014402201d0607903c860413640540101c8030001601020000800c0c10001c485501080c020390b940100102040190880405540c80c041540c458602d618400740318a0300c816400340c8018011400500182445600325900b14011403c032420202a11082c5203142d01c01c09200100c40e40c045810401d6050101d20340c4d038070308010b51060083c6000440000c04000d6080145050140ca40074003400c0e0728003960040c2d03d015005441ca1021001c9410083d40d00d050a8450424030340c87e00300050b002a4151003034526000024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 51576352 1250 51575102 51575113
    0x9010303030509011104060e0a090c020705011110060308040e01060f080103080a0e090a0b0406120812180d030c17150f03010f0204030b041a1e0403030f1a0f040905 72
    0x140c40841c0101002864048150740e41c020310b141d41200100034100620580c1d650610907180c2c08107004521600d6440320026900740541320041350f4005c01e461052790001e107401d55824108414951408106240f41c41c5a685420320100601803c1b00003082665948520b08480d40d0b40e6023012120000100000b20018a0210060000a010400408141160b0700c0e01012120405001030441d101c1900d62540b811b82da096070700f4143c103241c000c604c018a0742e1034400ca2a016a52580300040c4525101000c08c0c00f180400217030070f10a202c0924000d42004003c40e5a1191000406001000c040c003414010844000c40240c000496543c040e20642d803004000c447c0060030428083d40614103000c03290f25540b00c0c0b41c8840351a1940c8041c0c0010740c014100c00305981404d040c6881c0b0f10241d09481b01034080303540100544a03848a520401d991050340107180d40c0c2e0b8803070600310b00501e1000c096030008d90810310300c0b07541c0c40d42191110340b45c0e400c00c0310304103100c0840c01c007040300700c0b504500020000d0304803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 51577602 1250 51576352 51576359
    0x10b030702031e0705070609050406120203062703040603050703050105040e0706030b010e090a0f1b09050904150e0601140409020f0f04020714061504060e280e030c0d08060901 77
    0x1e80804251006040c0c00c003030401d21035a85d000d041c150180c204c40c000440c8404200f0051a26015040c0144030448030503070312002c580c010944078000140880c1d04601000d102c240d603400d4400341c85c001044481e0549031907a40b00c060040c00ba000c1555508002410003002183c280b405101321080851480000e00c00f0b5443c14105074082d0060f0b012160500001420002490712007841b02c83c803032145460000b50588003d81d1080c01c0b5a80d1003c01c5961806030301c000e003100340c0c2041c0903809982d0100d50310201c42d503ea1620600d50800d4403450400305050400418029000140300c5050f01c441c601445584c041c108240320450303e41c5413000c6d42c49040e03650034076201d0410160b001146003001d48050326000d5551141c5d404040361003c5220740f9404401003111260040e00c80c03c0074010100c43c2480140e00d4403150000c0802e010b4803074807481d00241122291007640a6143d00300034803110f0180042480c10791101e4072a040341c0038460050092400119850703106400c050301c10707000203104410136402c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 51578852 1250 51577602 51577627
    0xf010e01021903050405060f0d0606050306011704050106031403030601030c020d05120603190503030a0b0406030b0103110d0c2309010602070e070201020d15090f090c0902070201030f0c0c020108010b03070203 91
    0xb8003209406010342007101281c0c070346070342c5c000701100c001341d0042e2951b50200d9104401210000d41c0490304108060046c4055681d014081c81012444520894010381b511300303000d401802c80d540010041560340c141c82c200e0030400b1010314820003090f2400c200d60705070242c00342c1e200d034501035482d40001c800704806801c40040c00e0015800c0200542103070580401c1d65542881292031103c2a00c981c5e0000c410010008005e0180c90f24551040d40d0500855156a44d208080e81c0d060100502940d03282802d000991a0001b45920503500203030940c080c0c5981d11003080d07900d146105411280307101d84081c0082802d110f08428100d0345258010013003649468072402801c080502020110354013040307003060740f0915018804250076441c90058082e4034080c0c0701d03012180014060b601c440d0820034102c01282c03090702c0100c00c07503940c0e075000b69890380030b840101c004007034102ca680f1105140c00160052107070b0040d401d540342c910070b0300c41c002103980f00c210038445800121441001a0300030803080e400102c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 51580102 1250 51578852 51578893
    0xa05090303061c0c06021c020304060906031a090114030d0c12110319030203180a02030a1101030b0a090209031513020105090406030503030a0b1c080711030f030a030b0f010e0102 78
    0x1402001d83c4200340c07826034031041200010b51010005074001d040468007015070354642a440107a900046240901e84032016103851070500c00d42c1c082c1582c91880b0601d09410a5071030701c42030300080c00c6088a603100d2a82c2c1d0410040342030000e00074861107041019160242c0034005206030403034200329100592910403102c1c0380c40558034020501040c4103103040c1101c4001440c0380341a603501e01507100c0c90000303510b030503104203075000030b245038000c40b20310015131004030340310b400540c1141203080c9c4d40703042d0380040c3c0280c101e0f6401650410303221500003420b0380c1aa030203800d96100171030507130b18500780840f1031580c812800d840c40c8250220003049140158044c000400340100054804240581c0d02d858480c2550800c07698080c03a00d84603c28001580b403c07001103d03402e104480003010705003503905c90589502490304020711500c003004100b4142d035002c2120441c50040b050403607558620300000280640078040070a8001c074242c1d035030801a0f41c00b818045001c1c2c50180e0041c0b2000901e1019189000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 51581352 1250 51580102 51580129
    0x20301020408030a090306230a0b0a17011b0302120c0715020412030809010608030a0e0415030503130503062202010309050d020708070b030601080402060c010b03010c170a0509030306 80
    0x15942004001074100e000d101400d003640e019185e15944d9890b500b070030419118000c112212452800c4d480c1c20492015204558111500d600d00050f400c0424000c290710f040b072034000c140070f10400080c0349070b40101504400e08000701030341040f4400e40c4c00c41095003640241d11048139000c1160380040c14140380c1002a21380940118042c0354070060701c070f04179401ca9200ba0030400c08a001008504141604200e04540089284008203c0c0d949840802522400750700c40302c208008414003580031030360300d039004000b03501c50071200d4800180d52441c14a60701e502c1003400048005441e80700150a1401041c403c1c0b04120f00340224240900c0f0a8985802121410040b810315555000400c00302e07008001013401c08002d03800400b4050704005000b440c0000c680e024540c0000b040081100380d0740c4c0720444c2a00680e056034203035105c04030984803d024201e0507006035090740c68000800e40017a44207022141030000442603a00d6a11003401800607214222030000035a0b00803c0402c140341030000110321507 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 51582602 1250 51581352 51581359
    0xf01060f050a15030b0402031303200c040c0c0210050c070605070809010309060207120801090b0402090315040309030602130515120615131d06030d0206040f14100c110a0f0f02 77
    0x5d4000c5800180072a0030560700c011021005e004100c0c10180c00c042e11801d9445c0d90241d1803001c2407654101c9c0e070b84a2902d10418051030312812030081c020300441807580240d60042140541401c0840300420342d0300040d103102c1080c459034070002081c90040c801c841ca0031380c10800f01442e081349000194040c142c0404101c078002e60030006000441c0c4c00518403055190196035459295160411040c29100301144140c0f0462042109240e181d50005450100480085d01c0100d6541d5a04080da0703200b00690014142c54000620301440142d02605d160960701c044428041c90303c00aa0068014000c0c21003014202a41f08040b0780e0902d03080301456916607900c6207451400b4551b0144080d42081ca40c005480c1010380340b0700c117101d2480360b403017544e1000d015030040c000c400c64603400079920300c00940043d000d00c640c0c145400c1480003842080f80412180004c4810160006800a0003855581c5488002038200c86a80c2c10400300805d441e07100340c2c1c1107140b407040f40ba56a1124035aa00794600e04980c0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 51583852 1250 51582602 51582611
    0x303051b0708032d0412051213030507020907030507021c12050c090d03030609050a090305300903090a0807060903080c030403061e0b040204030b0f07090e01080f01060f050a1503 78
    0x184d007002204030f207556100c9000c4034049820180703004c2c40701030b01140080040c0207041c000142d000004035140b40c0d10107009409103803035410710b060960b00ea2141e904040d402050314010006017a4164200c140107860302c1d400ca5408100b1002d42501c051542d42400c000107046541200140c0055000150444014105175280480d075500080c82104800d0b801c502007034840c0c0f010000d90780303148a4a03503c0210700b81c4c14404180c1642c7c00604038400d00e80c50b05031070311222100c1203654041c0104203040001c014400d01450410340751a681d43d4124041a501c50706e00c0710070203e80c074140032401100312107090b143c40704003d04583c3d40d8045600f04580f000d016100520000002c16035900a000202990150700c1c0482c07140b84c01c6841c00c0e44d81382061036025a004000800020348101002c50340900b55101c0c0c01c0441c1ca0300182100c120405600c8403a00d40c066800208003200302041500c4040c0c0c801c8000c20002d82e941b074096003800d1042c40781903400741004000704400300081982550b4003242d440e0009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 51585102 1250 51583852 51583891
    0x90108040c080616081b04050d0c0b07060204090b0f090c0702010c0b07080601140a0e0103090206160623010f050d080f0c030a110c0f040f0b03190303051b070803 71
    0xf45071150441d007290400740c5030218008010f4200c03c00d03d422000c2450880c012500c007603401c0c40c561140d441603078083c52183c031046091146d082c200401030041010140d550f010b55040c0384010b900f00b07001300e14401d80b902e13041c0e111a10701005185842a0040c00c41e080c255151108484d03641c10070310041e414001001410400610400819441080c440e103c001c00c81c1044400100685483c80341b0310706440c400c119495840780c100300d40c0d89942c3d02c01d00e4046203240c074510118000d40100c0c007084c8030f415035a00c3c01c103080044540244026524042c040c0c0a5029030311681450841b080c40340c1c00c4600003a10b010700003400c203c000c0314550750183c10f515150481c00e0000c1c14141d0b0101e03800c3d0003280c1002c107011074050b50155640c150364601c4001881c01040480005050140e41d164240c4250740d201411103540a00d904115052400182510340210302c80004070942040d6400c00c400080c580130020b401a42d01c40004901412041c0340141002416501c1d11215403001c3e0001107407818441007030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 51586352 1250 51585102 51585119
    0x110405090705010f110a0c1e0608010510090305010507170c040605090603150d03090f0608010602100e011506080901050a020c030a0804020a1a0a080c040b07060b0f0603010816120305090108040c 85
    0x5c0040d00c40c120b034100851400c4207039941e446a2300010a00e20346901003c000c01940041002c1c1034540480300b1191030302006c0300585201d0f84a90006016508100c00c10103002c2d009883c59204030b070035280c880301560b15124444010f21807400740e103000c603109105810b454205030025603030221001e00e00100744d41400b00012400f1080c45011130009044001c00c1c0400c1d0440c011000c01010b95061181403941008030281d202d100b4005610ba0702c503507a03540060019025000440ca440500b40000307036043d2520001071400300c040310010155820300e40810710001c9a40700f00c031120107820001e54100600700a040301d14440c068010b81e0300012499000c9a1212565100350803007000b1049580da44a40e00005404005e0052198040031814001000849841000c650810364417001c00917006c856a0001100380c4402c10195400101c00b200202d0f60503400100c940450004418000a00c0da99042d11408600d9003040280007030400c0c0006005135014080da160042d11865107021115101c0090 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 51587602 1250 51586352 51586363
    0x305040f0803010e09010e0703030e090405160b0406030e070303020606061b07180c030504020102120d021b0109051006060504140103020705060a06060e150711010203130b030103110405090705010f11 87
    0xc1c1c01c0101c03202d000e100751703103009200e01100046c81d00041c010203407a43c0c13809091300018101450150382c00b10300040c00c10400313210000c044a4180b800c881c00765110000000036030024010000844d1502c01300d980243c1c40010a0307402c4a900d41e00030030b042c0e03450505201d00c68102c1c0144d444034110750b1004602c0f00e00d051202030058041c0d2007080d010b88241c45140410b440c4c0500900041c1403a01080c4000350341c2c0070520300c801d00c162003d455600d440701c1105600a00c0307081045c86d0045461359880e000540190420f91505005000321900030f0381841c0400100c401034411140800c0e002c003c1003224550102404000142c14100181000c010740c85280c00c10404483c1c0165590399002c081c0440c80c0c1101400c0c1c64103100303641100da100030328200a2854440d91601070415080c607400e0108030ba10800485000103001e00500310b015680e800303100c2c4541c00070300084560076100512080c4508092007064402d584120041807414948801981c800302c1171740c144001c00c441c03140d10328900300b002c114 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 51588852 1250 51587602 51587609
    0x2071e030c170a032d0510080a0506040501050f010b030112021201020d0e0607051e0310120501140105040b0d03080415060e150103151e1a1305030c100305040f080301 73
    0x8036640c070f960f03e1400074111500e203400e422101d0441c483d02262030700170610b03d0700c205424030700004243c3c0b1911003003419040650f020b80481c5c468489034034200240030035540d014074442c000034001da0303c5d10200c0b21a81802401041030008043c00100480014165419001d60000d000c00b62410340c200c60090981c1d2141e101d1090302d640700c00341ca450150303080000c1c41d07210300305182c102d0a0100706803c03000c8843c41d554209401d0030b03010002c120381c42300003c041401011007440e14484e40016180140c0609041c50b80404890011400001d1608180c081d95041d484014503000200d4210395003a81c2c0716401070001d85807008070210020340b8840368402c04010741017032094075825180001a42a81110012070340c2d04240c1020310602e20500d41504000031b07a0014246a00c0d0041c1d0b2070311f800300e5140603501454078484115001ca407080c040c0b0000740380800d44255410451910788003030545d1000b5030134040e80c11010700190070b070b43d0a1281d4800398010f4030402600035007107040d4580000581082c0c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 51590102 1250 51588852 51588893
    0x70204020f1b0c010905030714040b0d0311010e061509040606090c180504061d1e0406020903011802060d0f0b0303070c05101e030203150901030606150302071e030c 72
    0x200680c088a070401096420f44403d20340101c0050030000400d846801d0381c4500d09074499003c849520350780d03441d0442d03019180041e2400c1089541c0303003001000d40d08001c803070802c2946081280c1144000114141d449641e01c1085129125404c4060045013600100700380d6402e9500c02000c40c0940d400e00940320a4003d994613070a00480d4219003001c4410035034050303403140b49020b9040040e24918004c002c44040e060050301d070161340d1000c065140366034903c0e1000c586501c6104002c1081000d50191004c040280c0017000448180c1060040800f40d40b140694410342c188000407910280790800c6c1400160b081020030380e01c0788600401e1654100d8002200c4015490704180460705100d01c00860300031180c500049078240141000e1000f001c030150b00da00b05a00000028180010b15405404404002c0c04401031507a5074201480100520301502402c1080c214240060520274002e0b222400e800ca08060403010410204c02c2001c040740300e085080c030480c20103650200301003004244544c0244d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 51591352 1250 51590102 51590137
    0x601170c0405030d0513030206091c0b010e0f1e06010e0d051509030a0f260f07111204090b030a021201051603020a080f07110d05040315090b0c070204020f 68
    0x10182400e03c0355108808010046c440b40d0f03141240c1072400401c403601503406650f42c01000c1c01140da402c41440e004d8140451505220b001c1144000c07000d8121580706c14240d03816100e01007191001c0e03405a400034610084039007044410b0124101c02c58019005042511080307060001081c0500c03505502501c0c280c00501c501c10107440e00030852980030901d18082c5141c00e8220b0009040d000b8400e170190104041040c0d00d418024a84040410744c00001c80469081c1c81c1c1500400e0458004440442c00140340c840025900c0c4000250782e4040c8440078010b03801d2904000325030000b810449242941841009a01c0025860b441008000b031008903001003414500314403014120305500c000c10080600c104010071802d58890b1407603400142c41c11505d401c2d0303115120300300c842d10902c40321504c50303000c0d1168075581d04c0d80100060044a00c260124401d011038114900115541124041d10400c49080000d2255400d04d00601465100400c010308000040c904071a454110181300c064181c100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 51592602 1250 51591352 51591359
    0xe03040e0109110c060a1104090f050a0f060501200c120a0c05010906050d0504050a080310030c05090f190902060a0201020d050a060b0f0a030905100c0813110f01050d020a0302040609090b0d02090601170c04 90
    0x40c00b40c00d041180383c140038053b0500d814002841c08010045000304a1074210708000d040c901402203000002000f451b09040e0301c5071030149501d417140074804a0701500340030300014055001d2039485040f901140c0f5820b041c1040045805d014240041c4200c131103009461814001840000c051406020050281d045050451408100310f803240e4201901c51100e0740c0820095601460640e0b034490700384080c1503128032200c80d0f40340107801d105800951044011520705007142d03055016041380f02030170b00240aa515544020300896400d40074468001c2400c01c006a003071480340d00200001d05003403400081031101070729000c0c144010032191964003034a400c00640c41580c003080b85500100060a1403114418591702e89110a0310b0400503801360b41c1c00d01031000507a02543c00da803540d0050440c10340d81e50040130402402940180a620045052881c000c1199201441606650500504115403200c410b408126a0aa004000c0c90400070000001d007a00410b104141d4013034500d94900707949590a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 51593852 1250 51592602 51592621
    0x90609010b0108010b090d080a0513060e090601030b01030b090a1a09060d060c0903060e03030a05090105090618070b07080a09170303010905130f060b01020d02150c0703030e03040e0109110c060a1104090f05 90
    0x2f5903200e0400c0040010894107180c1d07903e507070305800c4070302401c0c0010b8a000c03030030059024140108210358442d41000411541121a4001d40c1882c0919484492504440010005140307000d9039450341060100044400081450303001000e03000d20b5042c41a4a50398a1340e814090b00e11504501c1e65070b810100034011024007600031030b80c025543c000240158945030080c5540d40b200140b5280000c0d50310080408014801d2143d40043e0044c1c0511959903256414510510351280c660310000881e04a00040c4217019540b020013862041800f0314038503464400314002500d405050718100d4214501000c0005000c1d24000d00820f12502011403070007035140029082010050b1124155044115422846801d2010b466844030b404003a6945540c014142180101030b082a9a5110300c00024003003000d03240c0200540c1202ca1a5000741700c1e545601c14401d10502910400c030606900080100e95200c40356005104401102c0e000141000d0703550190106891a4070302540c4625540d90a0141010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 51595102 1250 51593852 51593887
    0x30c05060604090f170d09030c0b0609010503072d120302070e0c09090a180b1f0b03010512100f02070201080604110f0304051501060503090609010b0108010b090d080a05 74
    0x4003110b040008043c44d441c0d08440ca000361400030403c15500844c0c80c1422a00d074242d071040384848108000e51070381d614010780034503074425083c2ca0070525040056014a481c00210f8160b230400b40c09402d00710314100c3d20448080b84035081d440c1542c06960849802200c41c0032440c018852040000320b0034050f414040d04203419a00901d419a50803010028180c00078030469a00c040203407181500e560300c0244c1e000c000c143c03180c0508898030440c58440180010f5841c9180942110403400c92221421411f00e0310740d034111721840a40180178001080f00b0f14180d0704c0c1440500414041d0784189000d5624403007203031516a11903c1c041c2c2c0c04510441903503400034205a110b042901d040010341100540c1c560180581ca6096010400000c00101080000e008070b11000c500e8075401d42440d611a500035107030f601300f15120861846000000b5040d0321050180038803045040c1c4440301140d0901c10310380c1f16684050619a005500c01075040d0001380718200400103810030b0f56070b445e181c4048906841000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 51596352 1250 51595102 51595111
    0x3080708040206090105070501390509030c15070203060901020417070b03040209040807080a02010906051e040308060102010212090f0d020708060712060b0d05070f2a030905030307030c0506 83
    0x2100080070440140c4800049600c0758000342407041d01d803441854028090640b04400d0741199001420401e9500c80e44c031180c0f00608000e6030181c40140c41031204481900492421a82c90350000070146c00b54100105100b400396604c04902d40307040f05580200746810004e82d00392081d6980040c0070846c03150800540d4555841080260003110300e401d0316031180d80000703000607119034840c0010a0400030040111184603601001d0251552040000039000300b40b2103030705981307890800c400150716205400b8400342c190b0a10354800c10740d8680c0d4504075003003a4010121070643d0b600300306401c49070034000003692081c030181009000750502c0b0a6a035041c454450241c200350b500c4840b06000403003020501603405a21442d002c50310000140111020f8009503000010810001031540018800c03904503d100341c019842d00104180c0500c1d040f90300f1440380e20307400000e040c0c07002221040d40e000300316030310124024074091001c1515003002034111351081604402250404006901300a002d02044d41d01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 51597602 1250 51596352 51596357
    0x207062405031207110d0c0b0301030b010e01080307060b1201090b0108070b0703050a08060604030f03030506011701081e0708120a031a0a09021c05071808060408190c081303030807 79
    0x1140d9078002c10090b140510309009203566403582c0003000076161812030014564200c40c1e07038132800d48e41e440380c101e05134402c1c002542d1081400002003109840811902d040f140001c3c0207500d401c00c00d89448008002c400c2c1c0d81640a81d8541412481040c06d018241d5414001c9207655110f52409404501c5c00c12141d03c1007515140a1000c480800e4100c01a1504400e980c20103513811340d0740500040c0c0d00c0c403445c0c2004215010581c040c50905525501c0584034440a0300d610080300b01c00b00556001c14800d106d101036540c013915030fa1201d03c0d040780c0c2800d03504040e80b044824294480d07045d1030428401040003113400c4808603089150350fa260203403800c21500aa50840d265000750045044144d8500441c0000307500040c84071243c0ca089485a10074401001c801c2105083c2914010b1180c0340203100c00351800f9828102040880c00401c519000300c0c0d00c815060724162003110003190040781218050148400015000d01017002240103040100300215800e65060031460080c02001300648207004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 51598852 1250 51597602 51597613
    0x30105040305090d150c120b0a050319020604080303090a0203150105030a0b06010c05010c12060e06090105011b0602070f03030e060403230408010e01140601051c05040204020706240503 81
    0x880e81080c12100c083d00195031044c090049030502c4c0c003130020540c2e00c81c01e4461400e103c04940c940e110700641a400f81c021030500160489400f005840f2066024140c0e054010304a48640710140c0b00351140d2031480a040241007964030301c816800d40d00304070f9602c0070b030340c10030307040b030011490107200b000204403158020880b00d50604001caa5a540b403010004d00d08501d131000f16880b07078011103910150720343c801c000380003004805800409810344041062815803d100003c02d007a50480c80b000c1c03040c5005021040703160f21348001161181c03803802c01d10780c0541c1070148203000310390640000c1803158041c4401000c05200c5e484c2c000c00b141d28581e102ea5841c3c20080030700000a074040c80c45845003549040c41c144ac016007200c0f84046200d10343c4105210341c030b414007440500e207041d00a0b010a80300c51040c5407055581000640b07403845100f02a12004400074070ac011402a9980660b42050000d4001030500340c09680340400c41d0b81100800480c040c80c410b2810f041101d0070300c030343c002d403400364041c22 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 51600102 1250 51598852 51598861
    0x30115050117011404050403050f070f0c0501050c0312100302030609030418020f07060b03030405040606020610080105010e1f0b030408070c09020f090105090312030c180f0604060509040b0a081506030105 89
    0x50031031300b000215910a94032a004101850b00c0342e02501c8a42801c2d4580d5a5641c0c03407450700c2150325540319030883d084140310302c0c0000c4075030080c0f0644607140040400765142040402a144600c44c005101c1c8020903030090002c00549c404200c107520603c0b03614000c2d982d450400c420f4041400d14942442c01e42401007024040f20300c20041520b00300781d800030006c0380d000c3e03884000a06502030794004a41041c54210009040e0b64001603090180d100c1704484134216131200c2c0002c0c2070310001d000d60101d080f0721701d005c181004140e00000c08881740a0701914501921505109034552042e10b068915141c0850306105000400311481c0060000d0354045203400c550b42c01c00c600d40d0040485050600c0700201e218035540e1418482e1490400f550140c5540e00e01c0d02d08072058042c0c1255110800741c440b012600a0b080c24002c854604400004125500745841c181d8200c4281e072201103c5504076488600c06892a266850f00c000640314078405041885040064900b481c4001401c40e4482d0b8104810b01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 51601352 1250 51600102 51600119
    0x2061e04061b020105070602070c091a01031b020c060a050d0212060102190210050d0b13050405060106030c02060a0c0e0a03030e01030c0302040b03040809012109030e01021f05130203011505011701 86
    0x54a801f60b10181c0980c03540d00d030f400c00c4100343c103055012070038185c280003503c50414005040422040c000b40c07010815035015404031280a892403000e840076070700c01c40c0e19041e24038080029080f001c50340d103003041c07404800b4902003043c0c0e040401c44a81c10307031031130b002c0c841290307010700900548101c8064a0116022a42c00040074230344003422000a0010021f0381101c201002e402550420b0005030801140800301c2c0c50003001403c044805071141c0c000e1340f001156a912030701030070702c1d030b812036038010101038a8442d03901c001000010780180501ca04a404411513440fa504680004e50107902c803a01c00c1c5003800000340954110340041010103204100c1071020009400590b904207800c16121500e4024520058501c021640c4000e2000081760001801080040c0c000903050761099a8a8445028500059a4507940703030829031460f116400d00941d41d40100d9016590108485511926850840e00400d017111041c00c003503614046c10003c10312842d60455081c0301341c603007140851030a940c03601148 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 51602602 1250 51601352 51601357
    0x5030312010603180818040b0603070203040311010c02030d0c0203160f03060c0203120c0301050f01172e0801050919030f080a0906060e0907050301110403060902061e04061b020105 79
    0x100c0d02819503440805051041810001301a194000181c5540f948203032113600b1207996011a55202d5420906885554109903040d24015010303070b002981801e0856854242001810150f14108010b080c0f500015076400c1001a2900280e6140d90100b01c48034018141080700c10f004038445401111003c2007180303c61300882048a4002e440000c4420320504108e083d407007110304000c00e11000005020200b4140402107040b1101102c1201c8600e0a540c01036600300394a0907501c000500d100006880c1c1454201c01d40c1e044150b4060441d11040f440070420003884aa4200c0d4416a5540c002c012292034100f10049848080c08160f441c4d141007580d00400f054510a6181c00b00904107012480030401783c0c10100c05c0c1540200d05010f165299407450440403c200d4002c0340d41d100702040020ba5007018803e00078081c44030307814146032504503200c82c00601145c00f030407a0405820400c01586040004d00e04940450001c0000d507142e00c0e01c1c038010080c40e041004004c90071414004140140c2e0030804 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 51603852 1250 51602602 51602609
    0x5010e06090703020c1908070b010e0108070806010b0405120703020603090f010f0b0904080a231210030308012102060a03090b0c04060f0f0309060c0305060312040e0601031e020d150503031201 84
    0x10682c940e95a981f030038440728024000b000380400d62010000ca5803202d481e062906075500c1c241110b075002c2d078450300300b40c2e520000e00c04d0b0300b500581000240040c0c00c0c402420740c0c802451001302c0d40b0707442e600d1703000c035030a179104842000d05074210280c0e11098207000e0060145440d4255428400d06042d000043c80003580a40b00400c14070001072354201c4240501c27486400100d01ca640c01209548456014000342e00c5003d0850007010700c0400280030000900401c402c1d00e4160740c8000300e0b60308080600001c0c2c403203022240c51820180d042e040059451a00074440d01816940200342c08115103400752506401400700840c00f001403109100740c0da0b01a0068446c8041884c1ca00d0000c01800d00030b400500c0741d0107004d4041802c0640307040407550150000d5009010517411140c1c0a040102e122545000f24002c0c001224000c2c400301d0010340c4039400a181c40002005295410b80312038070440c4c100e900041c00c4001407074841d0413003001c83e041118010018042500030b07514000d55400e1a0400850500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 51605102 1250 51603852 51603883
    0x203100e040b220c0b0301030317151c021c0b0105030a0b070f0314040f03020606010e010903020909070b0309011509020306060a18050d051c02010905030313110405010e06090703020c 80
    0xd8041c041c203181c903140c183d0880d0300400008080da44400032144e440e4400d01040e80800ca88170f0741c80c80b9040b840306125101e01009000c02417008441030030414182c10729201e90a000303601001580140c4c0d030303028000340c541c00f00007080914440c60385001110181305a004522a4002d002c0e51408504c0d00b1030061350112542c6070010f4000410401500100100002a031000094104010400c81d081440310b09481c043c1c0c0031039185684410044a9000046405030b0015110290410041c100400c1564000d06550165600c1c5510794513581901d4104896440207a0744812841c940c0d034002442c4072000d07184880040d46507184c00d80c0892110f129040c882020000020045282440740d44010005048000c007080448090b6042581d9100e00244280c1d40381503041c1e4002c4083e0303005106000081d58848051811555010080c0310020503603042502e4000c0c01c024000c44d6540c07284a440e019181549a00f4954200300e42884500f0000074462002e241c4104203080389801c0c001860500400c91a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 51606352 1250 51605102 51605131
    0x20a08012003060310020304030c06050604050105130e0102220e01060509090c070309260c0a030f1b0801020706052d0109020c03090303040801140f0f01090209041b030203100e040b 79
    0x1011a01d4040025000d920441c1b0100038082003552040034072864500030801409a601d9031320030803044075428800c4540c0f04103011503010040385d054014001c43351603d4001420074103044130704000c490341807000612040d04441c09210720040711004074050096071a145043c080c110b0041850341202400c1d5141e0840045103070010144225481000360143c40c0340303844548209129620a0203801d1030002e034038054041032071018201000360b403040741d800c4861415500f43c5507d402c0c0c16210a01c502c0c903c10101403c01181d070000c240001d1280c0340c0b08000005007883e0100d4410541c550060020000c4804003129075501050b13660f945054510a08005958080c2c8200242c914851507040300d400d40008200000c0400c819400b51800c1103603214441e51950300d140301c80c0ca00d00002c03640d86000e80d001c040184403112155000c0d02440d140504001240c0d02c1da0a203003030b002080090054002a00001041a021110391015000b00340c0d02c00701c0700e100c2c24182d45442118900901004951015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 51607602 1250 51606352 51606361
    0x18090203101809120e03010e010506150310030b010602160905070906050a05070c030804031a041a0c04080f0705120a0f06110708030705031b07031d12010f0603020a08012003 76
    0x2076000c4010b095029144130500c03001481c2c090034a042030925203220f0752822000304841d10041c0107161151000410851000c0c0080090003c0e60b0000361596218244044010001a014030306c0c2a000c0c1c001600101581d0b251401c40384040040ca400406009040c542440b40b001e0b00161208181c655908109442c0c81d00761504036141d001d8118050151000100c0000900440500030b105407030060f80305452030036414101c044501c0058070000c0a111210380543d504040402d6081c3d04250250314051400d0754600c1164038100201942d901550440c9404120610b0b00160b5018407084020151800c141d10303407901c8002542a80c8084d24103621038000150710392000c0101d650321341d44003038040c1c1c490a00f00402452500202d49082e111088083d00d001c0107401203040d05d00c015411f640b012904007031011200035a00d0902d41994000784603502c1260046028081c0490550341311400240b680d20b9401084a00398556104074541d914082d070b41c0c4418032407410210220080a0141540c9448 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 51608852 1250 51607602 51607649
    0x30f10030b1b090d08070c050d0c12150c020303180d050a050903010207020406080a050c0a0e0a0b03010f05090f060a0e070614070203010c030218121c0215071809020310 74
    0xfa030850a039002c04003e0003102041244409010914081c0403030300b550540301c07018441c4000c19864090010800034004000046c20300c4002000203118003d005e0503c03c0c850b090f001600c0304030041ea40903070001300402480000000c107042c291034040c4010501c044031081c0240c01880341420800030481d00081c07420140d00c0075012030313004581c050820017a240c1c0d40c810264503141d1b5502c08a41c140500c0c20b0100c07062070300003045410b6400815100969403a402d4540300208086411240c055495401d1090500c510b071042c14440c1d010240981402081040d0190a2041c0104000e44040c40c05181c07010700b0380c0005d000000d03560207091804441e030400952400c980200398000b581903086c20400240268181c018048003108601c2e5490030b4412001004580c5840c1050040c0a43c02907a810800307500c40c54172181d4000242c01520310982050340101c0b50014100c0b2b00d00d005c501030101204d001150300b61000010803a11008505505190714002d00c100d001d4402c00c607034910616004c0e020740c00e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 51610102 1250 51608852 51608857
    0x18010507030902060318150c07031106060319050109060e07170303100303030c0c0803040606062607030b0a0902070c0e06060301030302071401050408011d0c0607020117151203030f10030b1b 83
    0x150002c600b85230102401007143c0c41200304800090081100c030941500c0098964040d940050140c0040d032419255001d100080c4070003907600e5922050050046403542c841c4604c10148400540390301070900408030030b5248201481c44899208104002c8141c1d80f658131a815030341d145c603010507030840081040b2200d10710f01c680078040020001c10f100802c041948503000b1200c440e20750440748485c5450407000391007115044400501c0010006440c00d00c02c0d48044207220740184280e0146440310360b28000c82c1c200b508202c40340540e200040c40540c5003000b400c0d0b070020049425510b1581035a4001752134040034810f201a40100307844c51125603000d0320540d03019088601c001c0125610340046180400fa22074290740b1a8007918142c502503080070811285015010703100c03842c1000382c59804e0300800704000d002244191041c07412400940d01c0c00350005141c4040d8000715141d04001812405600c0c1c040c2c942a216040181c0402c00a1502c01d071131903000801d40050101d603a1414024505807 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 51611352 1250 51610102 51610123
    0x509040f0602070b070203090406120308070f03060918020f0607050a060b04090f03031b081509040606030503190306050607030f0f030f052805010f0b0a11030318010507030902060318 80
    0x2a04000405c40e500f640003002d003551520461b0103101e031503034132244000312140e140d80180024000320300094000d409441c00b98003c07810791900149195440402804485000324a2000315005d210518254600f01c0c0034400400001c840c3c0300d28184440d9646a0760f1010401300074a15912080c1d80080d42c0c0d04c80e440059582d03000ac2c40301c644e0305020b140080040c401ca10880a92080f4034004040f110310402c016480360058211142e942c034000700812900000081049412a4540c180400090401d00150500e13611201c3c01d0462580807950203030a0341c0385074000790300410042c081040803e5003d0385990100140d41071100c00001010b500300d02500a4520300e941c51828842031010142e03105c03944180340c91424002514021400c4510401d0321000c0c820710f403d60441140603c00a100040289101c10090400342c2c00c800203100d202d41142c104aa46d0001494003d0003010300a80c01e004651303000f5954601000203042c01d900040700fa02028204294443e000080c40402c0c03101001200c088 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 51612602 1250 51611352 51611363
    0x3070e040f060f1409060c0405041a03010f020a02070b0703091a0c01090507080c0315040201080c0d150303030c03230c070803010b03060102160b090105030a1b030603060c090509040f060207 83
    0x7021022240c9019104070a4071604c0500000001010785501181036805080b07500d50240c070300340c54101000302600c6140c1810740317000006d00d8950b08a179424400c1c1c0c664039000341070141c1c41d4810004003a00f03040e21903014040e0f80d5020000c400010394804085002d44244005030981e102043c1b030900c5560064559101c019840c01c2544818010f0010b213000840342c83e50122a4034051043c00d060700d03680b08620455020401d6000b00d0019800f5419450740060b4201c00d10b424a0b40142010042e50040610083c5030f04040505000b810340c14002c40c01500c0c040e0509000588200d048500081c98810702c00f840d124140c000300b1600784451007160921504010302c039489503107d4020031600c6e4400c1e10302c5405840dc914180c40007132034030b803a01ca0403900000405400e000c0110015141644002d080500d403903034443c1a403000c0c4540c058032401c400c0c0140d0f000120503045180c040210380f02040d1b0841480039600003040103030b0360803d00c1e55225074000b41008000301d992404002901900340020310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 51613852 1250 51612602 51612611
    0x3030c01050109050c090306040f06110a08100e04080d0b060408030703020c18010b0403080c010212090a050d0318061104090204060c1a010b0a030b120f15010503070503070e040f06 79
    0x4909815000307281600ea51400412150301c40c203056152900c00d0107140c1e40c01d07230040000600132074007403900e46083c81d005ea013021825080100d18000343c0e601603550035010482074428031070034000c80d054000140c01c030f4140001550419403600c01c194010380d15902d2080391200744007055529030342c064500900d82402180e8586c8243e14010b0349811076518006c0c0030306091031760452442c824141d03050482d464054094903090568441180750303881501034080c9076408014806888503d001882c2c800c401150140a00340c03070502d4600e003004000901d01c010141084588908a100802e68012050f400b40002496001b1034607018820300441d40100801840483e000414036040621010301314801e01c80a1024404104003000449003230041004a40043c4102003201d40a548001c08169008101600a001a900e00351801500310205821a041002c0010310050040c8290307002d00001c50203020500c3c1450046540e03010180f08182400000f8004141800b16000d0b0703401c84a0b4100c02c0500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 51615102 1250 51613852 51613867
    0x10501060314060f0109060f0c020a0e0901050702010e0c0d0510020a03021902060f0a05150a031b0501080114040c12050403020a02010f080f04080a03020c06040b0609011d01230303 79
    0x8005141003070203100c0c2060042c0016829140c500139110b00500142c41d40030405040c200d0403106045030b01d600c24240000c0100300c0d00541c2d18401802c0c0141030414900455142c141e0041d805c2d5130000e440c10056a040428400c01440003088220300bc2c1c905076040b100140032801c4c0a440d007403903445411810351002602e0300368140c0c150020540c00d000d10148802000303859000302d80d80c100460310150f6038215100480c26403005030304040d410011301c190050843c0f0f441000a11058080c0d8001c07103030040345801e08035038245040c01400040c00300742048003841d0715180c209002c04840d02803991007241c0c0c82c2203050030075008030810081c900008600b0030061925140c065074031008900240d010aa05007044041d140c0b003101d805201d24420031010100784c5139583d07600071903000210b0f050141502030208945040c0c04200e09403189001e00303c42602c0c0c1c00c0400c103000340d851040e0000050308201e91000401a02c4c20b54500c0c0c111440b080c042c0d0790885030b0b0103040c43c4078619030402070fa040c080040e895 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 51616352 1250 51615102 51615107
    0x1c0501080a0209070c03120218040c020717070b071119060c0b0a0501060507030f050405031f050907081203040501060b1204050c0f13020c01060b070c17062e03020301050106 76
    0x40078640c825101c4001c03e860f1480700350341842c4448001000541241c110b022805060b40160407407552440c0d000d003920380c6000019007a50f078408018001607014030401c00010b00e2902c1c2d40c044d4594004041c1210b2420455a1401c500c51b48030040c161810602c1440d00c15259030744140e9115a103c5458a58141c581400500324901010155007074010080401c0b0307100c155120715812252036807030f01407070100b8540d002c0c0c030111038602c041400c1c0403007400000f8081e1000c0c440c218081e0708140700c0d09402e890702c020980445801034800902c5600c990000d0000c104002100c01c00214410410758580d40d0b1450401d0151a5a4012604a240108a41096100394481c0d2070280d840769003600d00c3c2c5060a801e0020204a08001032744c054200c120b1303801c400c0075913401450806044400410980d8480080c3d140d00e6001d41000c0320141e0303d04200b048450b584480341c041900e8004040c243c641080f0103441d500d0000c000d005e9400845050403903076100f49401c03040005541c00fa00900c515079551002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 51617602 1250 51616352 51616363
    0x50a0b0f0601080f220501020307030f1103040b0105010c06060504020f090319050309010f03060801020705070303020d0813060c02151515070c062a06020a14031b1c050108 75
    0x44025140344400412030700e6000b070400078401e038002d00460b20f2550300e0341d844006806003c0d003030505030302079400c401000c24000c0c0000c43c40f0701c0041c0c9003c100105184040001c8840c03100b95004025001c3c01440001100e90b0a1103044400c00d10b89009602d20b103040000040000703601541d4800d10019500942e80000c2010300b4407100e080301034600390305154003810303001c80c0c210710010300e540c00070000105030703600450081d030041519250010312140c8030707140142249c1c0129415141075015000c10420907074100304410151a107483c0620407828a510252035004207010002e00d1070740c0320101c0c40012442002030000d101100400d2580c3d80c108100c100d039004007610b155600400d0030700d410718070014061040f50315050380302111840462510384c0440b03d01c81010000e000040d002c50101a80c1d07060320203894a0540241d4005135120820303030011744070000110960386058024820803250846044124036a21419090203690f001031400e440805c01c3c6503520b0450262400d000071841c00d400169 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 51618708 1106 51617602 51617611
    0x112020d060801050c040f0f080604060c0e0d230316110a08060405010509070e0106051606061a03010302040e0604020616030507140c040c0e0f0418050a0b 68
    0x15050f00b580ca094440100009000c2014000c441840070480000d0096201c0038040ea40340205917a141c503001071010b00001c0d40c4000c80d1a41c0360041e0198030f0540001449030764401150b00d001e01c2d0b02d07001d00c5a640041e0706c41400646000000000b11282070441140d511002c1ca856520416001040d101040c0c0044800500180200301040564062031080002041c42d140c040170003450102594414038896a015004008080c2c000e003c480c40c1c20a2102042481006420044040e007140d5109040301041c0b4400d0040d401d81c101c01940c140da108031030902c0854041c1041d207039254800c0d00c02a510030030400100d48680900d803405000107100c1d04240d810012180c0b02c0f0280900d14a0300f10b043e98012903948045441c0c070b4460240c1c2a6001d0409492041c001400726401c1c00d92001610701550b81d403002544c0140d000120304c003a49910100301c030001e4800c2c2c680700380c030408240c0c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 51438852 51618708 := by
  have h0 := BRFrame.cov_init 51438852
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 51438852 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 51438852 ≤ n) (h2 : n < 51618708) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
