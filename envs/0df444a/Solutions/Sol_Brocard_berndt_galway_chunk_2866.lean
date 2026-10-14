-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2866
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:58:40.851425+00:00
-- url     : https://prove2.me/submissions/189753ab-4047-4bd7-88e6-490cff7252b6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 515287769 ≤ n < 515467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 515289019 1250 515287769 515287781
    0x61b07090219030e0a03080601022e180c09090f060e01150501090506040b0a032d0b0402030f0a1a030102071407060f020304090b01090914091b0d06090f06 68
    0x100200c056191081441000e5040d0700101c07604041c1407500b02030800d581004a0b140c803a054060500c40480d58940b0010b0782406e510484142c0301003147d4203c88050b04064001d03030340200400030200b0520b0708a542c201010401c41740060321641a04004002c56221070300710328413462052500d100007103995601c0d2007d551008842c81c00ca85d443d48084094081c1003080c81c00140710910300701255030b00d89030103c3c8a40c410b80c015002c89200002e048901c15010b60480c0d502d8520fd0350505c0b48410080020380c035810210b06075150140e00706a00210a45080d0080c0d901551200400400644940b0441030040c6401906807440b00000303114662a075400b031014080403805a1201d2019034078401c100340c2844080e0304220240328401910861565002040c1c1c5d0680da40c4460000d00e02c0c0540d40140e4248611f5032102d02ca4508110501c2100702180005a0085003040101c0d010402c1001a14000748111340045810480303428000300403c0d010b410440c0200c0c01000e6400150103035403122425034035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 515290269 1250 515289019 515289029
    0xc0a08010b1302090f09130f150501091407110c0405010b1b010c14030a11040f092d0915051e0f0c120402130f0b0a05031209061b07 58
    0x1649485400c05070420310705000c1c00c281070751421413900713001e8800500d40d0010800d0940c00b403030206c000141e1701d210961424000d5070304000740e940f081c000380c506141541d030000300c2480c0442c2428000078030b41c9a0382c042c2000d0140120000485a6101740007140c81042c2091401c50703c0c811341c485d0001c10b03110781c404c507406000700307182c0a030350b07401c11020039181c400c40103001800c0c03603145c81c030b0000c41103600044007400f5003080d000c0780d541c0b43c48070300b0804003400102d1540c904140c1300050000302c0218490b49201210620751061015104140d140501c1591115486500c594400102540e0101c0395100c1141e042c810f2404034285080c043c1c015044580c1112513140201c544400e0450000801c41940d5214490300c540c2441e61501e024480c005004120b400b060300c0180001090071940c40c048207541000d010603081006440d04d40301d4602410404d000d187c040e04013001c010038141000b041742b000c603004410b901b0307152401c0103050080980c012039981c1814001d40221a40040d000c0c8842c43c020a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 515291519 1250 515290269 515290271
    0xc01210510150c0506150d050316021f090312140403080403030314071403280c030c020c030a080309070f030c03020102010506040204180b0103020c0d080f0108010603230c0a0801 78
    0x60410714102e4120b400c642200052102111020002030000150f059001c454405014417001883c008105420a918801031490001080000110201c010315414485c000c58406c003c40c0c1c141e00c40b200110f40c40e1213501c00040c400141c10f10100315004040c42d500709482c03038140e01e00c255250102042d034005030811a511000010100140b41e0315008140d04407204030311441590401030b20107010315400d1142c0310042c64011000030182c41c90300b001c010a86411005a1110046001c401001000c000340c118022900d004c3c5e0341010f0510010340c500140c0c0000d0000c001e00e909039114004d4a170001001003042e0303c41c1c4030001c076505001c601120011032042c403843d44240d09520000e42503440060629014a09c14031082100d6a400300440816000c1c903800003070642020401200030f40b1822030744015038403072805542002ca501c80845032003000101c5200716280d80b5816440d00380d03009803002030200e041800c40c105549822003007174114940d9a004440e10749011101044148003d584485000d0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 515292769 1250 515291519 515291551
    0xe01022e0c0201060b041401020102041505070c080309061b1e0d0e03010510050103020304170c07050a090b010206040b10240807020a032a02060403140d03020406020c012105 76
    0xc000d06010740034001600d40000c4c4405402c01c0c01212050049115861065041c5405149242d00039411030703020740399894000500f00540ca80c050a00d82c0300c00b2013207828800d000c60004801c000801540c13040340c2c004042c103240011f60400300c0b880ca0b680001c1c0903200c0c01003e00c000200c10025400103003907580c1c0401782c4418030b00002c6c0074103ca29000d0fa105c0c0241d040c0400c20111025210143d01034400900b00161244c543c0c0c2010141e541035441032880d109400110505842da001515404440b0110b400035811901c408404042d03d1400041c180076034803041c08100040c0c0c14002065004003440d403901d82c3c0e0f60341c40c0c05c002c1c14451446015141078000e1880b4050781680000615071098050008103280720180d50003c003003c04520005241408441c511850190a60b1005800ca5001856261216128240464800c200c600014028132030050b54681d210b00030300949086604580103841c03d01e070514019650801c1c191401001414051010340311440c00d48200ca02030a000d030408040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 515294019 1250 515292769 515292853
    0x7180e0604050a0c140a0608151221040b03062704030504060906020f0622061118120a020402070215121603021206190803030112060609050103030f0e0102 68
    0x139003076054218580800440040030404d489000d05030301242c0d9140b0b04400725544800c0f01807c2c00c403052192550001c9070880e1640e0000c00014070154004101d00c8030308000c2245100c1d40011712a078494814001ea00b4400186945445801c404c5102000c0f80c1c50b071250001200c0040c8601001c840841c049000820f00307103d140e9020000d0000340046000400c1d108840700801541c83d5402070120450202a080707d841200d2410b10002d241603124405010419001c2000802c0e9042501003111101d2060b41146040c034001310204120301d1900c028100340100c036000c0c0b1010358044030b030903038214010a11071100d40085600801191403000c80040c41ca06080301041c04c403e1540020008150041c4545105540981185900000c00b15109084081010104501410070754010261800044000034242d218615030b10200c0b0302c0303448104402912403809000320317242808040d0014517404003164006000d84511808508140122103507407001c4002500900c05450b41c003148096884070803a8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 515295269 1250 515294019 515294033
    0x20a12050c04060b1b0115060908061621020f030a0b01110616110a0f080418060b030105040506011709030705010b0604030f15091505090d020d0207180e0604050a 71
    0x81e00c4008480c2030062500d010078160315401002d9040d21017010316984000050003d520032402d42c01e5500c0902031281c0d4a036030190040c16944500e000d24080d01c4002400c0882103285081c4c9100603403601908040707540903940059000808400040780d080000c070071411908030203907101e08000c1601141c1e0034007040004202f6039100803c030385168401c2e414040b28050202c0000d503e440b00d8030380030040ea80f82222040c41c021044c0409014031a04002c0d001c10320055100502c103644a040300d07d41000c102070007410032900c5c107104241201a0600051240346416007017150031034014580f071284060201c6480c40700410540d20740440c0d501c00112101040000c0c040c0c1e0320a00d5048422900f0b091550700c40705011510f00c038006009a8881c3da01010034441c03640821030041e084103a6044151b05c0f480381c034009100943e01c044451240b081505103051000030b10200d2102e00388e0140c0b031610718004d800495040000b118445003a1102c0c1c816215040411100740300798010b9005120482980c14110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 515296519 1250 515295269 515295283
    0x3130303030c0c0b13050a080c010504030f143f010612060f05040506010516120e041a06030a0207061a0f03071a0d06031248050a020a1205 61
    0x10b00b8010401c1045000c1018800481c0d40050200000b84101d101460001d00785081030b0f0008104e40c0d008211100c0c1000150b20080c4207a110340c031141d50a8090b201e050300d58405002e98071041240400000341e03411014120810840780300c0c03a040300c09c043c000f0200300e5025040085003203d282920700401000368030140700d0302d801807024400c01042e410440080350100d5140542402503460f140442d085911640c100d854101038a2140c960711540c9151406003002108000c400042180708403492a00c0d043c81686507004210a5504080000c8002c0c000703590001010b007000c050b0300340000808240b560060a03d804540301001a81c5a5054100203e9515a40e403183c00780c0d000040501c0f01d9244800c0124001542031102c2d9100c118900076440989400d0300000e0030594003080303e0000ca07402c60181840c1d98018400c00c078280f0700c14a440d89140004008002c04440503903498038031031010075408010280150140c4000c0006a00400c4000c006544124038201071206100c2c01e00800344140 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 515297769 1250 515296519 515296541
    0x17042904051c0306140405100b040e0609061f030b01050c0d020105010801270321090b0609071803030806030a0803072601052b05010e010902042316020f0313030303 72
    0x4200030390400070f00310820203101ca0345d5405503658034007060002c0d8020303902d1030050024041180d517480c2c440040745c240700820380740706010742d4105000c1810307481c1003240c4032801c00e0fa00c00004851004070408a0140005690300d60500008024030603524105120f044100c1c807003900081400e52501600d07608594666490b961500b80003015030b581d0b00244040302c80f08031b4040c071b0514020a242603841d889030b0100308040958506e030804c50b07820800880e030854030840f400c4403410507581e0381d01d40645158031a1089040700440702c00d02840000d0044513800e420002c050b00f10742215080c3c1e40c802050380c1c41601d02c140800c103020f450710b501380c500044d416007998070700c060f6203029494100402d07520f41d068035103040c1c032404600c600300d40e2158000880c500b0300e400000034089200d105107514001c05c20702d042a8000c0e400c03d035001d280085514544030b1840c501141d1400c055030f13442c801c1a002d40c6035000401c02c50040c032000b040414401c002607c1501084100101c1d400c1c5541b07030180c1199001ea842c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 515299019 1250 515297769 515297771
    0x60105090907030803190603030c060c230d02160605040b0c041505070821060f030313030f030917071d1317091309021017042904051c03 60
    0x1005041c56000c0342680450380e1142480b80c80e0b0319210182d681d101c022401c5c0d0311040746850400011b00d030340003080c051501c0c0901400c100f002407003d0110303641e00460710b0659043c0315280060101d0411900244050302c8900801420104400c103942c0424081c4201915100c6d1504148828083c4a0711520340107a95040602c0c0380038606414051402c400160700c40a000b0041901000e0050310300858044070f2082c0e061005000d00768200c140034410644032540103030b00c0600b0b0942c03a81000400c0301c802c10040540c3c0c800302d80c42c560714102c903c01030000460400007080340c0041c40c01000f034405a600012440509442411300b101c40300b44c1a02c400b0790205131800041800703a21900d0007501c0d034540341c00100e6500d904a2004c91f548003803040046075500076034515032110340e4051a40c00b40190601c00c9880003200030f0080d000b01c43c0480360091140301e00f089030010800203100145400017103098220300c42c1e14420b414041000c4114111016501c941002c0101611643c03a00a00d124500d440c3c20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 515300269 1250 515299019 515299021
    0x40914070b0c060a1806020c0f011802130f11030f0703141312021c0203130b1c2f030906061512090c040e03120603030f030a0b041d07050306010509 65
    0x101c0690b206005031008005070382e12000542c540740417005020302150000c8042d503880c0c400e1b00c0d0442d620340404c168500c55518100188842103d90070340360b4943c54004003c0f400110b080e0104c80024004d0002010038203503140d0143c0705540214000e144200000700080d03509142400018094490100002a000d1007450400403070b001060b100c4410145c100c000388a181c40c45440c16441e10307400341303d2141510380b08404144c40941c000f0081135400504081d072413010749d840c0c12000c02c40c0500d101125845054080399407080d01590f224480d460404011010149128000d1059903070100c400c0c4100000008200520750b801000711503000f000a68014162213441d070360304842c070300400c00030092240100c0003095020004000006ca4150018404c10500c0381d8009280d0b0359901004401d1510740c00c64000030418580401901c20300c40c200c0280c03e180d65a4121000c0003004100c01982d4440c1d560030a029a00881c0800e01c4000000100103009103420b0804151070b14030305900c4640300b418610 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 515301519 1250 515300269 515300287
    0xc1412090f0d080a1a0a06030905010902040203091b0a0b030609090715081f030c060e03030702031b330a0512010306061e1409180a0302010f0506060c150c040302040914070b 76
    0x141c0208107c070300602d00000e0400c078510b42a409054214000f0354018004010311014250100300108514082001e40003c50505810701c840100107200d0681442d00500000c1c00bc0d041164006611010b1038040d940f002e501c0c0c50b82c518200300b514400c8000a150b603020000302c0004141c40e5108861105060940245141e07910301490545000d40c2e41005007402005190ba101041070302c09250380182a600d9504202c00f440342c074000050319a6101300c500311503070404841e000405581da90a01122070110110b104000e4180c0d038098200c03c41004010040c40780e40680040300d1034044c6210ba00b02141452a00c005c00d106111460801c09011210081c01c10425100c3d41442c03004134010703140301c2010350b605090201000020301601c0030342d0185804e600d0801d030341036108481c010759521041100d40c0b5050217002080c0981c0420a5841d801120b00b18401040350304001d0b400f40064509520f02901c90780442c1c10340314200421983d00048000ca691030b044140100e0024003c860641303030500d070400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 515302769 1250 515301519 515301529
    0x90c110c0d03050a03060b0304060e2512080403120c0c050114040e0c1e03071704330c02070302040605042901050904020a120c1412090f0d080a1a 64
    0x340100605014001844c442c0841c000c0d04524010405492516182e180038100369004d00510070f443e84142c01440000e00d800c0b01c031410300c010904980541d01d0201c03828100c00544404c4203050580d1042c1003441b000000800304900110b102d021503075541c00309030140c50050001e148980101e0306000d540101c590415507600d007038404845803100d000c00c3d42d46641e04840603510492102e900c14642c45800741641888034001903000c0c800704ea56140c0c04800703031020103400c00c1040d0740c001c0400c1c0c1c0e0480c40c2c268011042403114114040843c0c802814646501c0c5482101c24800082d000358200d40f0081065250500c9000010304003581c003480304401d20310081500001040000440040c9001d420806074492000e9070086030010b00111b58030000480068041e2450000d44500303181000b0984102c03a200315080100c40c0f400294942c1040d10000300b9003100c40d40145000c103584200d4041d04a10041000701c20144022600c1d10751380c50030608801403d0700c40000703204007124280298000b103600d40d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 515304019 1250 515302769 515302789
    0x6020c0d0602040312090f05030312060907030b03240901020307021e0a0501090614060109050306180f06010b0301030318050105040302040e1e010c09080604020d03030507090e01090c110c 82
    0x1046031600c1695a1500d08a402405260005010403840e00c0b20f0354501070304108401e003a14410a02c001c0700c540d842c41016030705d00c610038124180b6090000451102d0600440b0544c05c1860b50070045034103103260380030a14000b003000a5002d01d84c1d84820841e4541103601c0c0e044d40100c0400029132852814900c0a550f0342360070300d906240e80004124405c10680b091080b1003405500900921140825080c018040d1800e000140100d1380d20740042078180d03020725001070071030710b020700a001e5981c2c0d04c00c0c2c01985442c01051383c244e640103040c3c02c040703403503004c0c0141c0f8041d0070603549d01901c9504600f8001d02c461140801103039814610b0206111a0b0307001019242180da04645c00304022011224050810490039000e034501030342c1641c4ec2000301410340001d009000c103a651040110b5070741c0069943d0b1b40c02500e000e50020354240f0300c5030110b403198000d00c1c1d210080382440f000003551510400304062090744090400e07940c6042840c2c0c440c0d0b01c0345c8813100740c10300d100080440100140001c0d6848078 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 515305269 1250 515304019 515304043
    0x30718080a0c030308180f1c0306141c06050702010614030f060c03130c0b030a05100b04030209071202030403021b030705010c06050402040e15040b060105030103051b040b0301090302030c01150b0301030b040204111809060105040602 101
    0x1040522451360a10b080d080700b0b4454dd407242d010b101c141404030f4082d000c0c04090280e42c000390700d105055802da08000400c154200100302c01880e00e504c40340111b4481c1e600141060000440012110000c03910707092800d40181141680d0030355034506050540c01f107a070050004084000c00f05000c00c00c0d24098401d443c2900d0b0112540040d584800a041d41c0e824000810303110500d001208010078542c0218000b2041c0c1036150150748000c89500406840d20351a000f540e020803060403910700031030125841503078424405040002c400329202070f000d240030050480040108001000c11003007060226078640c002c83c2c00e003440c03425035055503211600d8034043d407801040c03280c00150021541e0b03140e42000801c000c0190013000a04141c2c10002e4803584031603030b940c401d0740c01c2c50b07500d403140003080b0b900200b202d83c4109030504603425540e40010f042c4010304241c1c1c1c82501c40c990480310312401402001021800d9900000c108030000c00d002d403043e03000340030030f050102c248020002039401180040d0010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 515306519 1250 515305269 515305279
    0x4060e01020309120d030501140105040b0903070509041421070206130308040909110616031d06031005180f06150c03030718080a0c030308180f1c030614 67
    0x140940100d10314080e01e070030280c1c00324070040c0502c6a2000464280740f1905140d4050021380c2c0c99035007000c010703102642c0e040c0c000340c81000100301d0800301e0001340041080040035503401590340d000044000390161015201c0704c4203140d8100d0141010001a1703541034080103450748140d07401008400318082c4640282c01081d001030b600c00148101c82c110300103141d000c42c45070b403912b0312500c8000003010058070444040c80c00381f207003581d10300e41b04043c0c2d5586100d91100c09503801055070704640d0440010403c08000c552064070840c2d90391440081e501c81c0242c05061241140b40c03c0c200b001030080324042035950509401800b820301021200b06602c00020394010610851401c01c144051003205d21108007400044140076840d58800d840741c00003009016084005922407401c07a4a580b0680c000401d105014002040002c3c02942d040c2d41c4208481c8080020300d460003040307401c1c0a1a42a07455054001034140d4800405080e1012150b0115242c00c01c90103052200c0701c01d003a1800f070302440c851 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 515307769 1250 515306519 515306537
    0x70801090b06091f09020307020706020714190b04060509040606050715050903040b1207020f0303070c03030b0f04091101031811131b03051e090c041509110403020a1a0406 75
    0x195910001000c1d907180a0050038015540c0e880788138020340068600c82300500a0510010305144000f400c0400d440d15003a007010419040c8081103858203064140750100c804d018400602d40740b074403010708020300c181c0c0c5900741e55510860030441215171981120007804018055500402c007582c0091441840240002559480d200c82c441e1460003168805103c5000024007801c0c413100c0250602e020300c11a400300c611101c100d20542ea00d07800300300c81c0c01d0009a0b42c0c00303d90000c00e00c60341240900850141400d00e10900a10109043d68200c0390151245080d8108044643d681481051034510094400301400d0880381e071840520500c0d921520300c21013104c01c4503180d40c0e03104d502864503103529010710300505000c500090080d004c1200d19030303407441ca044803403007001c5551840284254210005012550f40c007904110051018a00a07502181c0c0d669000c205502144036450280d64460801a01c441ca148104a01594581c201060000381d428184c440544002e090754141c88030ba0810310f510b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 515309019 1250 515307769 515307781
    0x30403091a033907050105060a080d050313150504140303070c17090918060912040608100b040801020c0715050f030a0e01020a0503040203010c11060c0702010201230108070801090b0609 81
    0x71203e10090300105100b00000805540c4420002440300c54401c000900c02c6641d2801000140000ca2150f6201900070b0103406416500c103d0042d0350101e803103400e41c0181050398640080c24002001d03210803003a40c0700b0521052100200c80000030312440c41c01903103940741c880802030182c80c00e000001c0c000034262141c52380014442090700c80c0c1030005000a400d901c2c000d54480c00d81040089054000c0c059134001c44c111042c08070710b0b05441c80c001c41d080341c83d00d8a0200308884042e0001c246030b01051500001003054040f24001308002c004040001d40c4034420002564202007180d4030050007a03c8034019a0307200740c0c004040d60b2420341d403130a150b9101d50380c0e402d1510261802c400c0d034588039403001072400f107200d0708000614007480c001e4008009074900344c6019501c44400f0f44074240345501000016800100440080100b1881880040b900000e81e14401c410b942c005110b0060221008005100b4003030100301200007082200028448500c217901d9089004901501c041d000304114000688 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 515310269 1250 515309019 515309071
    0x4090e010b0d12110102180f060d0f0c020d111c0219050601150c0c150507020306010f0515191404080d0206010501031803080c0918010308030403091a03 67
    0x1a840d00c0241440345000e0b450700c0d185204012010b41c80700811050380b040c00030b0280510948008980b143d1034100d4071680c0c0d104101c00d0791658407600b51f011394108038421060b0300038001c20104940800340401c0c2c40c00c0d80c22000e4103010001c1c1070002004507040011154010006542d640b80307204d4051400700e0003040030102d050090410010002038800c0f800c00d0104400000d41c4e074100c1e808994500e402001e8004200e580082d5407001405011a0ba603060000300208460540c200c002400c2003840c000250b40802c5c01d11800f680559401d1015003000c01140c00d023201031031030800040d8201c915160912600c510b01140c584409810081050450040e0048600407a0003808100b002c4560010090f44000d40e246001d01442e070003e07007000c44001001d514009400210350b03154130745035050355610190228542060341c059500104440003402c6a98110301e1187c040d600513a07002e0b9482c50203007006080e40d9526807107c1c1c1c0008072420700ea0846515101a00d13000440c804084c2141d00d55a031040d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 515311519 1250 515310269 515310281
    0xc0e01020c04020a1403010b0a09120f110a0f080a0204050105030109021f050f0f0309071a0405060d06150c0605091b060306041e0209010e030c010221040e010e240604090e01 76
    0x200345c0000000420000280400f500820040d551110303a11034a849000c00d601071002c1c3c00821003581841000006885001c03600c0a500000d040e58211503070750b0095074603282480c1c0c002c51190300a101d204044d0306140c0180340c05480180c00a11110407a540031031a0b4203864160802c0148580308202d00c401d00c0f841c12240c6100e911203e8a0710345090035290380f00d507070040d20b19440522441100052065051070701d00d119940054145007420300e050144160399000c610260030780b41d0340781e1002c20f08207101c10001264940694903202208070900d0305508817080907150000d55808042449000c0051824000414900340c0e0255120b03110200820090b000140d02c146802c00d10b00c20250341098135030b0207044000300036600d0f050342e5080385040c1364407550703422038290068014040f01c076540a002c140040c2001c0036114100c0c0741c240d56441a182c405801c2c1c104001d003208400a01c01c83c00c1c2c0c1d4401021061034103249183d828110300000078401c2c07181d8400c40101948a1040c0801200203610203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 515312769 1250 515311519 515311547
    0x11061b0a060e190c060509030109060f020309120c03090d0f02090f090d050339130306060929010314010b07020907021612080d021c0c0e01020c04020a 66
    0x140c0081080385021800380900c901c0001c164850b080c081101d100c1100e10140360702d60081c1c040741000b81401c07400c0f91154440c0c410150035640795200300c0e00044481c0300b914a2304111003001a101c0c01c00306809030400100d105c4002c1e48041c2404050038007100401101c03603161040b41c0d014100c400d603107081d4054000843e4042e500441500070483e02c000b00c140c010b48121411000c0d651702e515110400c2d03400c1e00064950081007030404008a14213215200341070003644600340407030303020764128014100e0744c0c0c400329982904264030703103041003041444d0007200f000d4003850314140210b24000640040c07180c00b2400e500883c0201c4144001564025808850300c0004105150000d6071183c442c0d202d240d0040108034040c1d800407000480303070740c400f040c00c042e00c1031210700080440e460000310492001440c10241d0304100c08010061034038000d480201103210b880c0d400782c0c2c1c0040080010404452410540c00180310403080d807150507070f07404030f04d49450740b80844c0e0050310746038108012541c200e91541d138 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 515314019 1250 515312769 515312773
    0x6110d0c020d0f0804060e0a050d030605190e0609041b06020705031213030f02010525120e06070609061404080d0c090b0921120c0106050d11061b 64
    0xaa102485500400c4081405070202d0796040d5034250100c5014040108000c0066420300c04600014100c0d000b40d01c1e40f00c107040450b0b07610a0700e42c841c0c2d8246054010080c0c0400d603101c400300039a007040c1c0b510039031050300ca01003c40e1a91078505400b28191006080e01e1051160340d0000c0c0c208480c52501525a080424120700010740310000a03607500050701aa510a1080000c2e454100000000305c0300c01c06c408843c6401d284d031466a0f5200c0c5a0442a030803811711a0a1100e08103483c0c801d8001081410001c8403184844018140006003044101c000360801c841d503241c15513a0748910040714040c6074812030014211890b400c0600c000e04070303154800064401c023000d0109014164028207400b00103503800308000c010640040e2140d440314440c440040c0810310894210b07180211700344245001100000050032121100c480c00d01c01c00d5008564102c2d804150354034408070901c90701c0c000d40000d4561041d42c03600d6444911800c010011040d01c00d00340000c2c0008000785d204002c501c0041c01c801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 515315269 1250 515314019 515314027
    0x2303040b0c070f051011030d05040308190e3705030703080a02040e06091f0f0f0b1c02070503210618130b1f090c08010e0106090605070611 61
    0x1030550195409050061514401e080020804505101204040320401031103461152074440f400d458100c1c003030304200c0c020f010a10910101c01150f00070076208030302c80e0b5198613107490100c600c3c03071b00c0350b40c005142112145000680c0c01401380c0003504040341d11080d90408507501c00e106240340f21a92055074103900f0313901145410100400000a13040d0b03d840380d1610011559412012002c034041d6110702141100301c0004182c2c0750410303950403500300b08807d0301c2c4501031200420380c81e8410059030048500b0082c0c00801c200e451040d58402010f0850501414030b013a0aa503001580c0149120b03501800a6000840b0010000100201d400b0155819108510002520755490251b10101c400d030703007c0c0f2020355541c000440c801c0b400394803c9441d81803105505626403900c20001000414002c00000e1024403414034250390340003c401005254804603000700020340c0107280d03c0040c3d006400712801c5d000103220803a00084103c06981c7c0034504039407105024108200541b00f204401614020006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 515316519 1250 515315269 515315279
    0x10905010509011b140304031b0b04110a1211040603050f010506031903121512050619090c030f05070b040801020903070602071d0910020a39230304 65
    0x1d00224400e0603150001c21054011811141c0056604031aa90000c3c025003a02504225024013540c1c02c24040e150071001202c0780c1e11110701ca0710f8402000c1d00d194440100308002c20414040072980c54606494842d4901d2400300900b00000180200401200c0c503c030030b142042c0c030f807503000a00440e005000c40d00c11620042c59140202400d0301c0c0c00e8002d00501021145c82d98480300b0602e802581927541483d0380c0f503041440300c000c006c82c044100200c40410700024494040c0c0103641d4034140100054291410b0100b202541003542c00718081105041403103085c082580b0b00d9010b011690000303050404404545801030810500341c2292540303650228010801303600550282490501c250112940345403681002da9850030700d40b1620001403134000000c4042c0501e61001504500d40030101c8402d0380c101c400d400c00780d800080714180040c0c8250ba0f856807000c05a02240501c010b01d00e140005e4011461038010610a10080904a100403e0f0114245001308059420f9a5441002d403619541c8030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 515317769 1250 515316519 515316521
    0x50415050f0414030a0e04020a030e03030c1201090608030405090907080d0e01170906060d0312180209011a1206220608010b011b1122091a10050f03070801090501 71
    0x5440c10f41d103c552440b1904200b00700002200c800d062940c4031004000310203002c0002a42c0304418100c01c25441d20718440c0d03251170800156008424140c50320303403103843d6036032451a0044140e111403c140e003010010415103402100312025a88103803402441039075041f040c145007005a600030f1076184110090011803503840860300e0b90716042681c1d102c4020322404240713900390505582524164201901051507883c101001c0e0480b58481d00b845c0b0005144041007004071054142114035500c00200a0002c5151110170707140500100031103d9600001c3c14054001c2d400f42030034a11240200da40403802c07035941c0c401c80c0c551800c550700d610085459442d803844090310301ca1042100350340c00d1001508096002c0c0e17006400311401c41002411001c416115034041040788040d00e6040b442201900300070101c43d044032101740c0ea0107074020940c1a210700c1c0c90016000042d1241e00c1d566048000e00c184c0b03048071014101101c000715621611500c0c004002403c101d01680150f54a610340903880c07080083c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 515319019 1250 515317769 515317771
    0x11062106091602070b0a031509020306150c0706030b120f010b01080a270309081b030d0f0c0b0402060d0c1e140f0d02040b0f0702030706051c050415050f 67
    0x55550404a44480880c0d40070208a10140030160700036490a0000f0110300707006d001064214a008294244280202e5140c01d5164101d5442c0b942c00004010031030502c0b8900b0846070303211003212441c08190008007501c50300a80102030408d925812101429582c403200e40a2481020003564101040e01c01031134020841c030a8000c0c04100b0940000c1d20f405842c0c0f0034844640600e6034060001c80380000c54410b8443c03194412000c0c0002d005020829200802800800003030030101c501900c046541010b1034140103207444410440d8044004021661000c480404103a0200182c1e030aa156840010114050951440304072840d000201d50020742c407045404c6c081c42040003045418580080840e4850582c0d07042614100e410002d921400e40f5540051141c44d40c14074005051a1300c412812022342e0003040b030500752280c003042000a41c501408440000c0c803a41c00e1041c581101c00d042844400305095007000340582e640002010301c0900301000c50307070185040041005140c8441c0010390220 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 515320269 1250 515319019 515319031
    0x1f030507030f05070e01030b040e121225050904270b011d06090405010b130f0c0206100603110918160e1c021c05010c030b06070c03110621 61
    0x1041004102081c0600e03c1054000c030f5083d603854055581d00801035002d0843d607041142c2017580e800460540300c105110111902d0f040c801000d6850341040b403000c111440141c600018041d080b6003a2104052481291041d154141007603500c2d0100c0d480000c009004c01804031101c96980f06030104142104c41e00e80503007900c01c401c07050b01640c81d02280141c00c00b294130030400a0040e240410304034a0040a41c1e070f48544180004145044c9420100e0401e143e060079884c038441c1c485040c4800c050f21400342070b005480c144020065850305441c1d0740451070b201d04c00c0d41c042c581d8880c049143c6d54600400ca400c0303000b025110b0594030080c0c01030980d100c0030881d4034055103065100161022442260302c107011000090020f0350000a11000800c884480007040b41d00284030441e4031351000081250080c8280198000102c903c1e401a018090f10780700311586116441c10000000040c8a03040c4510589400c1242c00342d0048402c2d011520134070840300c040c04560a01401c0c1031102081500540c8180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 515321519 1250 515320269 515320271
    0x403020a050d020607260a050903390f10020c010609020c07210308040b0711101d0703020604030b06030f070311010e18042a0e1e071209021f03050703 66
    0x2e945420384007428211005002010506c600850308000b442e820180e08038601506881c038024040420107103407149000d07600c0c483c244985a40d00c40d6800e0a00243c80444100080c0148002001c07049860f900541d06001d04c55134042800041c0700025032005024105540007155512990640c1c296902000c0c45280081c0b68480300d1062010340410100c807215605072180f1129442d00e81c0c41d501030b003500800000c1000031401c103803140200c081044048034451450009890000039101a0503030420800c10700b11940100c070100010380300c2200f103408a9802c0525005251180000039040c41c544600703103005440b80c00d13404424090480031102d6031883c240c8403800400c010800744182084c186407000d080b0404100090049040000065081000c40c0c5144041d0140e803000d42a500da00d580000b090002a00c0c204a90380724a10703800700750407039240a00c1c100b5207000940248100e0502c07000318202c6440740000821912070502400305e50b1448642d900e0001d407040030081c002d240072201c080c002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 515322769 1250 515321519 515321537
    0xa0e06090a060602100c1701090b0f0321090d0c0b130f05130504060b04060b040503211b1606030c0e040b0603012603070c05011403060102150403020a050d020607 71
    0x101c0741d180314940468046401400180a04c1e0703855200a02800c0c507150203101810000310040c4000c1c0030498040c080d016400030b007100104e1305000000000d640d04074020351000d01c070042440c407000185003103c50245d4071180c0e160300c004007154603041360100040070341c91490740201b0035800340000707402c00740c0c0340c105400e088550750144408195038610074903070880b070302508400c040300b001d402a80d881405403601103900c90a4002240c115000d03a44000345414012800340100d190500045605084452540b406d107520107030129030b20b2181c4145881060320003444441080b800307100207402c5032031000b10082059643c08014010b0140343c1443d00c0000e09020102e0364619051248071600c40b400703407189046a080c0300030500324070505d6444075030b800c0894010f0a0301754400c00013081d581d0b00c5003042c02ea40500e4213001401080c107199140901000910402c44e03140d81c0090304c01d02d4600c03122058400b0f0b884600b0182e00384060702502502c240a404c84614000c2c1c1c00007582c80c000c024654529602d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 515324019 1250 515322769 515322781
    0x222050601121406040507110715120605150a0210020a050d06080a0f060b010507021314010e010b030403140705010c09061b150207020307120c050103050a0203090a031202090a0e0609 80
    0x2c0f02e8040e0000050f1141c1c01022801a0802c1c0e407040364441c00e40d00b0142d140f0422424214901001644001c43c1582c20800c1002840d910030704040903d10519400c0c4401c500f042c00054a5a4050305c24459113500802c01d081c49a20801c18810607040e5403c01b1591003603c880000c3c81a4442007020280900f85613000500f0100020340511103500304c804c5624014160740c0b100003404070a04c65a041040901ca0724025a03200514641c0d42d012522000941d2000907132401c2c2020016401030380c8800050004000ca50205821682d1140e4540303030100400500070382001660103629006001913183ca1418028140c00039951001e9404c0f03030316a9104551840b906418540c0b01c0100180803203019007144c1e24203000d42d009800120300c000c06a5899540b80e0003084805441013030145c9001004040030012540c05100340741d00034504240079842c5150065020759140800d400007020010094014580000c0a038181e488940e001070900c2d005ca940d5160031880a481a01c2291040040b40040f0300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 515325269 1250 515324019 515324021
    0x10f050a050f0f01030c030b150c0118080f03070504090e06040605010e09030a031806020a0221130e040c0302030303100303022a01080a06270b0901061407022205060112 74
    0x31800d02c009040e50304100500004401070100941d501040c540c0390a034a1040e0381c0d400c0c860345d04d566031000b081d070788a10154a085081d100380c4200882c3c8a00c003030600030003144202040f1164103480040d0b0f6640d03500c0728002200c032486983c1c402096185402a804103e4101180290189008031000d10003a40c8403418916054000c0e289036113940d0040005d8408240240c107c0e90300049420b400c3d4000250a0316640c060380d01a03042c2d8401030b08000b11100b40c440740200081150007071000d140e403e01c61040f501c801000081e000300c0e0f1340c0f000e051001400300701141010401031a0b014050303c1c5c481c1007a13140c0b84003280c01808100d0150180940c25810403070300e5800301c070080003002011500010382500544107080068045414541c8880002c5030b264403102440c1c4601c031b1694040681c2030000a001401c441900302d030340d44601c1d1744c8401005100ea2185070740c1004100b00d0b000990301ca5051001030408a007202c94071421074440c0c250303203811508583c4803038418003080c1c82e800e4140c5980d482900c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 515326519 1250 515325269 515325289
    0x504081608011b0509040f02040e04030203030405060c09090a0f24060f0c0206090d020d2f0d0c05040b01030f050408041a030405030421140d02010c1d0f0d0209010f050a05 75
    0x20300091014000181c3d03501d01900003802a411f0000c00500d400e40340c5c2e6040365410402c41c0e00783c01503440001170004000040020951101c0100d02c03181c1420724040000c0da00001c050300702c0101d16101d580151851410381d00150f0b5148020b074011100405194004000141612660000c00e1043c500e141841e4001e0540c059525070003004540740c41c0c2607004104280c40304007416a00903d1107080da0001521500c542c4241c110841c81c0d46083c280c8039001613580f11411040140170320820310030200000e031010b9908098820464020510108120041b00281900d1484e020418182810b10080c026040c0081054850180c43c0011340144003105041520058400400306d620070031040081049016400f9451204c0710590b031400f50407601d0702818070000c17404040954200800b40c0705e44580906c16407420800a007062040700e04040d68140781d08071500300c064060b0344072a40890042d500c10349895038440d40100f1194041d41c4610340d0561a52040c00b8036405509020307804205464076044da2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 515327769 1250 515326519 515326571
    0x2703020c030d1e0203040506120603100b010804060b03030904060609080705040603120f050d0504050309030114130201051e0c1609020306060a1b0c090b090a050f060d03050408160801 80
    0xf100207031401120340e50b015a6100f484411800140408900ca565000c010000d070301e01c1c02c1024800d4240724080505007407050300c0c110fa02e58a4210b400d61a0b90304081c049611079080b01c0c00280c50981040824210b00c20036800d654814505540410307102c1d08038440206848101d0111011380e921031061100320340650001030300404c1d80450784104144210401040a29207140c07ca040107100d410310015614140d60440382c2c1c3d00003203100140350900340f21f100741e00c5041c805036841c2070601a00c508000c0c42403000c081d04118000504140c51081180344a8503219000d030550790359442070103000d4a039001460410101d842c0281e0020740e45159000392409003038000c084500c0d0200550342a01c04011800fa081c1820507034414244c00b041c0d0b403020020080c5010180828000349203820051440c2000b0102c41034103140c6030500c0740036010900e00341e41c400c205550b040042c0c111414150340030301a69001618a2250089903071010810342c000c00102c4a0b034400a014580300d81030905040038010b121 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 515329019 1250 515327769 515327777
    0x20a03060b03010f181107080d1a0a090e0a1209050907020d050901050309010b0306040506150a03050c0609060712090f060e090a0c17040c0e0612030f0d2703020c030d 73
    0x1007030184205c218904044980b02c1074001402d0050401420001e03040090709455103140860504540c2c2d8032402500350b03046050055941000720318001584d0661a03000f0780035200c3e41c400350084001020010340f4070700358105007011100100c0102c010122440390041a028507185804114040c0c0001036200ba8035903992910ba080440003c01110280c100400384052503484002840c4c1e151802d20140380100d00440160507546004200001c0c06d0f0108001c89000714102c54041000c6440850251544407040b94000d0f9980400710000710540207890001c1c10742c06004200d21455a0040c0b040001c903440403810042103aa03031207054031414142107441e6000322104002070f11288407544040d481001600b80b2103081c400c1d56981600c14401280e00300c0d00790002d50303400d01075200d00103000345d844517007204c42d40814007043c04034517202d000da1600d11600007404691050512503642003502c0342440040132003022002d845082e03149480b215400d5015000f0228000f01d10309001c01ca40c1041540b40d15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 515330269 1250 515329019 515329049
    0xf0b160c0b1303090510020601050f0d020a030b100e013f0b0a020c0d031d120f070f02060c03031f0f0501050f040f151107050d080903150703020a03060b0301 69
    0x2100c0d0a94042d2940b0480130001d01c5100411240e554600c92100e01d8210340c006c0c00760350306000a20403031060800031244900104000100140d5035a500142940e9000240e08041d481d01d03080128107010981000300001503a50001c10040c000d0441c28580c0220808111007043c503030203c0840382d0b403803440005070b0010300811140214410b0f1103001e4001c42d0800c03005107006014441242021014404d1b400000d4441c0da581c1d40f02d459100d0b01c00302190100010305401942c0c0a11094280718420799103c50100c0401c2000600603400c174650415500a03104c03d0756a550011655240d0748110351640c08004c1c907100301c07112005200070f03680035140505400e0034481e0510f070054070b40d50001450000d21440402c03021813203c1e0180c1c2c03110003c0500440d051314041c203001c80980011030410b40c13508517500400d020002075545d0403070380c00002c0c0c000c1c09481e034030303081500401d0030a00074881684400150388203000d1401c0c2d140e8010b015079091643c0403c030403a210781084001d0b200a108804079055030322 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 515331519 1250 515330269 515330281
    0x90a050405130203010c0f09080609061807031e06180503040612020409060b03191107030c210905100903020d020108060102150c130524090307030f0b160c0b 69
    0x1602042c1c000721501c002d42580305650740001d003581c19032142000040d01c0407102003040d1350040881d00c080c1c04018054041e42c54180c1a0030354507000149008110107038070460340074090382440603902560304509066100080f2400c1d01450204401040714a40d10748000010b540c0d030407086400300321340d00c40083c0d071901d480e00400b03e42c14013604240b40c42e400d07400c00c00028044000e12804000389442e0403156124600048031040d0601d011100c0d90015042031714083c148a00741e02101c110300e6050500c407000c2c080030b04100c0c5000d1031201c82c0c40c010f40709400444007240e81002e2840101e82d0220b1b9000000841c05030121079241d85c03480001c0d000b20307404c030002c401076020b6565581c0c08101841103034013240c00c0915440c40b0310426568000c1201c40042c1c84030b072009042c16404064001603950300e01e4041a84000da245200300350b50b48090700d0020030010055601481802c0040da00451003402040507404c0c200d507150000e440702c000c0951840c104d00c003018010200c0380c80f140d8015111040c05e42d02d00b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 515332769 1250 515331519 515331521
    0x40819030c09180b060705010c02120403031b03030e030d09060b0f01120e031e09030c010f021f061802210609011e15021014010f09150302030d11010c05090a0504 71
    0xa0001c3c0e81d00e030703900d5640b8800744c1d48440d0003400016004100200f0f079404060006410945545940c0d551590104002c0c800f094003d036074400f8075900b0807112480b850701814210010400e000c0a00ca45000014040340c400d078460308600107142c018041007103952500410040c0100c01520300c00d010400361404100e5200749030740510298013640054a160a840c4002c458010f030a500c00d101014001191031031032810100403c400119080c2440680341c0703800342c4003a580e5403600e241c14843c084a507091010589031500b00e14001d144903802413078840da80761190f01c0a90054903c0c00d0707603400b0080040188560401415008003c0548002290b03402e14202c80d0000c00302040c1e01042a160300300001d500780e492041264600300b0359001c0c01401d050380e14124191745c05c1d01d00410094910700018403001001d540700da02152002240060024080c0c045090a050b640e407000e541401038820368854583c204d0b240d25541c2410400030801840040001e95203409620003180d003020a9100600960801d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 515334019 1250 515332769 515332799
    0x7120e030705030c070e010e071209031707050901030515010813051c05041e030b06010e0a150f08010602010507050f03041109012c040822090203040819030c09 70
    0x844103580c60300401d521403d103564010f1403082040e90000c2d03410000600c45c00413444c050f080700719003100700d82802c40b0003c212611419040360b0243d5a00c0710041094002c01e600d646151013045000b4051920841c0030302503401c18842c250104c0c1c01e0000140700440b008000d00c03800c1605844202e501d0700d4102e02211524128101100d10b445002c000d021341d50300d49450600d03c2d03483c540c0d5041d680e80c203040604480504450855084001c410000d20020344955101c1da480202803901b0010301e540480014040c581c00d600c0851000c07401d0700d40d4100e460303000301400702c108a5034071001002d0342da505040b800c8a004550013000550180041021690a6401140c00500074403003045560a01e20000342407038403e91207001c0100c01c4810540d419540d89002780300c0e25143e6600c1010300c1c9032985806040740f217401c05080701001c1c0e103208400100701e500b00c1c200c0903100840046440703182503e040c040702d0340010984031480000d603000b030035050701c64000d0410b09441e9583d05003c841c0741503114a09504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 515335269 1250 515334019 515334041
    0x7050715140d05011802091012060509040503070501050718090507090b0a17011401050301170708150a150503031b190b060411070c06120209101106060301050712 71
    0x5580d400750711071902409800c2d20030401c2c1c1c1c0080d80e07514120100c0410707003851403d030344640d005224200c41c903543d4440350a00c099450500310140030072041180000c0009802c825840300854080c0000d0010000140640b540314500810258580490a5440c140782c2480001c85a050010500440d000da802c0240c00000605080e42207548900b60881e4036001528100e00094074604145902c9581d020035a00401c18140c010010b0205c3d040000c1440c07005000b00002c818416428040008003084844001e1290300c0581d0280c28143c240301e00c94010584560301414201481c40100302c8120b00f1450848000030011031411201c60203215046610003c0d031842d44c00342c42d412510725001f03100d100b9003d511401400c2602d281800030001118951010900d4180e42400101c00041c4a50302020590f1180c2c101101e8010030300352810080d1189240058000c50041070011104c1d4004040c19611a0b030001561590fa0301c0d83c06150072140b0495400d8001112404641001e401541c00210311034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 515336519 1250 515335269 515335277
    0x2d0303050a0e120d02071a0403020613030204021b011401051f09080d030f06120206041a130311490f11090a020703080703020a0513230607050715 64
    0x40410b0000701241441c00c80103003250044240c51404076414002100500205001011900740754201900305005030301009014903400149a080c500c0c00b86800401581e005000390340e5482c1d18070307003030701070465050044083d58249a84040c4c6040d03011503550685270301516400040f5131f00400310784d405034100490f1062085080002c281860b05000381040008191404902210b00c1824841100d0680e44648000c41618072a41e0040c5d84950458040b102e0300e540740712180302d050030505050700c525044601c180c2010f034800002c02911941d07015250904a8104441011044a1621445104200c04172045208901380d1242008208900c50100030004c1508881c640e5a01d82840201a2000f940d000ca4042811140c0d403400d281010741c055040502903003442c0103940c1c0a80400da01030310f0402459008507816400d540b04805581c04c940e05070802d180c80759030b02e0031081c08007200d0002d80d940080e0034002440e558107040c001c80303074160ba200d0000c0c4015450070350b804107029811180d00f0204 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 515337769 1250 515336519 515336537
    0x917070b060f0409060f02131a03010905041704031b063914010501080f0a081c020d090308040b0c04080a080903030705061503150405100f020913062d0303050a 70
    0x4a403c030701c6802003e00031200010b0b23031560b094000520341c3c3c0255200c405064101d40e441c02d80d451856017580d044554581000c00e5646942c58100e00c14002e114085080b4000884d001050240e100a085400c10f0001d6120202944480088a10059440084041c1200248014829101080c1003a502800c01500c03110b0098280d5800c2d000e030003c8030356100540c1d1500018000010284006a210b102c10300041c4011000c65443c61228040c1c0b071060402c42280c01a80f080180c8a60100c901c082ca0108041100000c07624028145000540342525810440c0300010074079060b80e000c40c2c1c142c0e0403000040850040c1c0381c0e103405041c4d1020040c241c050000380b0449001410811103680038021040140c00d09509010a02d440c1c400e00d488600c2c075000c50342d02031201107500131a0007030003200130180114840e03941841910280c03244c03016840d040103c0d8540c0078120300582d80a0819a6000c081d01085550301940070300d00c110148071200c4981d66003c00410004c0d011740001e02060300d4905091140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 515339019 1250 515337769 515337773
    0x2010e01110417030703080708041e0605040c080106080309060d0609060312230a0f020f101401090207030806010804060f06030c140d03020c0f0604080d030917070b060f0409 76
    0x703480400c1c89401200901040c00d211141c0d00402841071450f030700000307504000c403a4070000c12066015103000c00b440a4180410188018141540412100d5055145418000346007140c0100021182a50b620010f50300200703500106010b8101201c003100000d601700400001003041c1c0d03600c80c010400c5025503070f4030b002602420501507000190f001e00501c40244803e80d0028201d80340901c00f0403024015a0742085205200030f064400441c09450554401d0810900582c5800420406014075220348a80610164003030381203180c41050049050003e0390380d40c2e140342d05a000b04400200800c40c03d000041d295485840b56980c01409241c021030341400c1c6841000807140d484d001510b1807001d901c018030940454010110032003000381d4080c03c6149142d1402502e802140380020304c210407118030000981c2e00e9500b603c0103400742400b85d50818640040103002443e4604044501b0020800b402d80b52183e15402c2c0c07803000307800409070f0307403107954101c100701d000250024155803150f40c42c211280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 515340269 1250 515339019 515339021
    0xf1419051201060c120e0d060e0f06190606091208031308041d0c0903120d020c03191404030b0c2808190209031c020c18010303090b0306010206061002010e01 69
    0x7000300381a40b0340001200c2d1508140c04170000c149920800e100842e103150415031503621307455103a55046580098024841d4076680d0030714500c416000d03028801c2030144411081c80681007031400c95420000c1210523035030391081e43c00c141248219601b800055444601142d95100150b602001d0803440c5518408141d0f40c2c5c4200d604580c000e40c0180c016a0844580032036071694641d0030000b145182da050180c2400000d030b441a094680d03c00c2c006001c58030102d0301d510750b010f035090140e0b00805d50f03407200504030745044003402e51190b40c000500c0c1e4a50401d2440050b404641c140da4021100c405c49a540400740c1c56260300182466000048801c1d81c41c60f002c0d81410301c81d0280300142d481c045142411040c15112901034508009c1080c4100b260b0310950760002210940c10f1203200c00c60140300102c460070ba040102101c1c0e0550440c098055901e045496800c2c0c603410317a4425221030004c56103490303030a00c090208443d003d0150b030003400416030303a1402200c3da0180d40502c1c03001140c82d0b441501c1e00340c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 515341519 1250 515340269 515340271
    0x100207050c03062a0304021f02010213140405150d0b04021903120f050a020703030804020a03020a030f2120070b040f090f0b0d08030910020a0f0f14190512 68
    0xe0703803062040300300c400741314290901015040e1314101c0c402c1c150f0a041e0000b0395090703489401c60242070034111001500714000c1d0181d0351070f0961035020722a4255100398940309107101c0240303540b065292500240710f5020340090511980c1c0c01402142203060700c0c2d42c41400301c5001400582e80f103140d080600345603c2041001e0009544590b000c08098050762001802c01504a4040c0301489428441200c6160b4001010800c40f9003503d4030800c69250340c0041810385819800c040e403c44c0340f620020082c400e40e5011480347e07612441c600208104904c2d080410070342c03400380010014404e0300803501c90079a2080c4102001d2440c0c1c050b600c4499a40d210000154000c1e841040c0c0c60040544c200309085031441144030075009002c3c04d00c03800003050700044102052030030062480340080045203459500b0412491a101c0c02c01e0115a07400a4040141c020102800c141c0300080801600161591044080d0b01007090740303048203420040c1da8084100440035914100c4c080210038414212030182e000030b41c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 515342769 1250 515341519 515341531
    0xc0310050409121d03030f09040b060d1b05070804052704140d03150b03130f111e0306040303021b1b0102010e1b0f01030b0904060f06080d02100207050c0306 69
    0x1a0200844040680f01d400032840442c00740380240580300c1071345c80200132500c9140409200513540c0341b0315130020b40184a4107c1c0f440d0410804941c200e00c2a00980c403c4000a4070b0344e105455000124800300c849105115004100600c140001c00c280d06100805c044010b1070341500a41140c8800b0a01d44280d02c110342c00d442a64881514600340c1c00d00340840781c0090014507040c8800c4200d0001d04030304140c144528603005000100051040e000c43c00d000e01c80300d03400399480044000900340b406400d141114402e200c1c084441c515184141c0e0703285100001d030300c044d002e0807159440340c40c190020341041c1d080c0956042168100740308180b00744031101081e081c80e10b6078081c4500a100090071100140c4524030f00350b0000480d00b45c080c085800d80a80c1c0380044403600e0b0b6200c40c3d03000403005042c441c2000b80c1c02030042400e1104024054000c100d01c800070711b01c100304132540c5488031643c40320000000c5001d0b801682050084098980080001030b014000300c800c4c2148600c003081c640030080b40c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 515344019 1250 515342769 515342783
    0x6040f05091c0309110f061201060801080c040c0e0f0f030f100c080403090b0a03140106050703030f020301050d08030c12010b030a0e060f07030c120507020d03060510080c0310050409 80
    0x540e0b9251204214000074140c1075207001c021300c1249a580b00381c561150300605118500204486101d031340c808084400709060f24a11040039656000d01502c0100c081c0100e05490040080b080080d003045c4c0308401105e6060f0303948054030002c403000d0010075495840b01541281000c0740d41d40042d00c0030003c0074412007c03440208020008000714604550002401030204003404080c000800d911400c014180d400181c0c5541c0d441442c0309041d80242214044041c3c040c00d0b07003000061150b0068003400ca12802500c2c01d001c00741d0401205801ca1000b402481d612034464039421000c9220103002d198022840b0200901e007028910011040042c01da1101c08240000000c100241d07606000d0742920003114401403a07141800320740c5c0c2070030060082041c410107989600c1c1162852046900c08081d9141d01c0c0d080205080120340251070b030348898041e1000ca4100700740040d441c20110311410300311440d03035101c9805464a01070b4040c0740d800034144810140080c20701080a585900c07030414858882c1e01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 515345269 1250 515344019 515344033
    0x110106060c06050a0501122004090c05090f01030c06050a0c0501050103230d050a03020f0d06060917031303060c0210230702150408032701050114030f0304030b06040f0509 75
    0x140240980d0f0005010981480c104401000340347c007089640c81206a0003400c6010802c41c2015807000c01c5005104681d11130b0a2030104414080c41c3c00341ca0080e141d05644410342507803a01134103c01d0240c2844014204041a001040040e100c2c1015040d050060300e00401c4222558842d942500d60a80060780e801c042008800e910040301809850300c5d0300b028010301a80707643c00c02c001d00980913070480c250900da00007800c51041d40000084900045825004001482d107907240204040030900400610404000003010741e01e00c00070942e40e481d200301c01d045400a0071641d411001d080702500c0001940b1030505c0c007101160207406101d001428105000079403400401407200d50300c40240c113803030079508119400da18174010b0f0101d4541c013a4201ca041d568940300e070b0b2000709000382400007552166440c500001c84908064002c03178100c0c0c202000b0406850840010191034002c0640c41810507482000208009210006102c0e80b06000400008a020108680c1d0040c0c030000c035401c0e4082d0b000b02e5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 515346519 1250 515345269 515345273
    0x606150d05041209170c01030203070c150f050901140402060702121c0e0406030b070305060a170c091b03340201142214010e0a0515090616030c110106060c 68
    0x11410004000301ea4101e020100ca005e0340c03d4481c0c0720340610038101600000051011400751245220f220b52014a031241144a400920010010080102c512604020210307600501c14003441c0f403855840000b41a66440f541c5c2003048540c0509000c9130803a041801144800d001489415505203501138410306000ea403000c028890300b101c1c80c0b61407040e41f8181003400429a8800784a81c0034807a410001000e8441c000001c0b003039281a841a481d12000300c9a00000c0840030510207101e100c255070a48054440c1c5040202c0c2200014460400e8141840000c0316a500b640300b000c4c101c2d101000c0000c1202c4203001c00c420002c0003440020150307441d0302e80c07070405662115030940e01c40e4406022a80c243c0140200580c4140b03010006441c0039031044801c1d070007a0342036001e01d0b2644121401c80b00c0c7c2d81581e160442d01d1f00151030410310751060312000920001c1011407001c0c070030200c40701c4280094000ba00280c00800d43e15041c1400c00c40b07841c11030000030109110b8400600765988843c481f201c003078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 515347769 1250 515346519 515346527
    0x101401150f120b01090f0b1803010605030a0f03261e0c040b0703050f03070e130504030f260c03090f01090215070305131401030c0c050606150d050412 66
    0x280d4041041144001c0d00407401944010742000501c6101c90114600c2d104000490b0022001d4001a2000f8051140007031010305400080c80d40044c0740c240d40101500c58030805081b42e1491040c1c1d6007580240c45420002400b54031821605446424160742540504061a1188506582e4120142700740d0b230600000b802185140c0001445100780d00115141800340d194441c015840703580d60104c0085140000c160043c800e0718080d4110055003078903441c0a45004000844c1203030560f000d69098580e1032496a518001c6a224a8058031000c903030b6038180c142140e001c0d51038241400702900d2201c054881d0f04480d00854095040c0c0107420741c80e0709001440328280100c103401e03c0c40a13072501000000584442800c0d01c19444034075031294940025042c0ac0d00c581c4684489100c003003424483c003060422071500000e4180b10284d03810040036510050507512407100b01070140031907014034006034462411032890103580441d64921411700ca450303225401590002c1e501240c0c810038010f903021001d584 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 515349019 1250 515347769 515347799
    0x131112190e0f070506030a450302150a0b060304140d0c030813050102160f290610300b010503010b030114030a1202030315040e070605070203101401 65
    0x114041d00c002c402042c0001d0340c1e58110f02c5814011540480018a0503440da4042d040101d0130b44803004501c680d8061001c0c81442d01ca1810001140307814209454040303040c00c0c40c0100d5491340040600c11428200c240202500400428030b164441039031030743d80e46401001e540603034400c036102c10b6a004100003450400910813442810804032025903c0404c4c1d002c03480c66081881112425a8503451303051807806403083c201109444e0300080310b00410440d0281ca0140301c0e50180c1c04022030984a002c0c20409811042e0080201451803c0403600d24901a4074000340340304581000c0d0846500700f0310300e540e0b450010007030031090901e2041402c203401c281e020780380c501d4109207011803856043c019a981180018050328002c0c03121041600e547e43c500b00420b400d51900300d11007c000184404000f5500da0040311807201c81c03484844c01d400c203801e0a0151441165100e8064035003141404c80490f52a009418166414401ca48039a41101018490126030310485182c185ca2581848034046031072034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 515350269 1250 515349019 515349041
    0x30503031b0319021b010c020307050f030414010e030721060e0c03031b01200d0b010201050105061b0c0d06050403020601080606030303060405040305070c06210b13111219 75
    0x108104440e0790360b00c1d001c0320503900042c400141c641c0040c0625501c2006100c0380b17600d26619000310700c1c03550343c3c000001c0c0c130045118804407412000b0244125031240141d10903003507080750b04186040c040d030040481000e2014080c0c200c96985650f0700780d0840042d000a4001030700710804038484288810b5015556045000c8070050415071103000201c0e6803441025000a00e010304c174800001241020b411035004401c1d05c0016103601529000d100302a907201c2035207071031414907220a2540650060040504036100100800e060400d0213802d02c501c010781826044003406101d4a00203aa40c60283c954007103409130070001414070700340c81d0182c90b02d04180c125214030b51001080120560300082280d50000c8142c42c04501622945000d841d0344c0034100300180b84c06400000454910340c005c82e00640044003220080c01ca403040052030703040f10f80c4d80c520305401c90b5404901442e48011600645c030441d4a6070320301d80c60300d00200d10121001c1010b54424488800c002158203d201a602038211421 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 515351519 1250 515350269 515350321
    0xc070605041503060e0c090d060c050a03050105010f02101104090603080703110a1e110405090f0d0e24040b120105130209090402010c1419050f0f10050a09020a03050303 74
    0x20300b01480381d550400010819240c06c10002841e54440d10350361845450030341d001c0c01c02d003e6120070800107003480c1c201d007182d180081d01d00000010158480e0402140d04d48003900946402902011704130080c1840416400e82d10800f00000262076105118200045d030240c901203442d220325250040600c440700d40c102401c0c0c5c6c04a039001020450307202e020510000f1810310f4000d501d0a6192071a0354103604440c140d4884e186ca01080803031140820940d4005149005a46c4c1141c2559001c0d24100d961f00c02c8d903904503d030750390050208911102110b0340c1c980a0032205040c180c6c1c1e0210200b860740b20300000c5468540c550010405400d0034802c440c0324010151080d0304108880e8003081407a08020800303030410400610700c4081c03040001d40f01041c0c24080c0140d42503c200203800351f4060101c0e03002150740703100c0c00104809100c03000c00e905c0855500180134252030041880d00d10301038440a444034032000c0d9506804001683d0f01090400110300c40e50107981c81b4a45000e03480024500010041114 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 515352769 1250 515351519 515351531
    0x503071a240a0b03150f100f0503060d080f070309050d020d0813050901080703140c0108071115040309140a06051e0c01060e0f07050a1d060c070605041503 68
    0x2424051006001005a424041c8030700060540041d400e000664001c4402281c00400d228111030340c14031090301358100f540c0141d01c48a0203410f00001d024100120f80010b40384c1000079180314401d070015034010700c0c0181091041441603d9070812381d032100b000000740010000c2e0341810141c10001500c001c1104072040c0701d41000d1900418210740c0803074401004004001404110b80c0728800b0703168090321000d07001154560f1180e80032a5102160b0100782d510311200001041039182c0002c6c00070420406940742010760f140e0481c151282813401502001070b0041c68426280680014101d5110f6400303560345074001da1400035803640100310b00c45868000c0721601014010144c101c411100c01c040c01d4030702a1840350045020382441e028442c06038820b07500300803001130b00c1c824141c0e1003030280c00c0784c120a80d110703211514141d40a10072040e2020109682041c4d4501008503204c615010b00e40140615142c140100303a10b5050440d150810404504e011409001590541c4d20b000c0300301d6543d00b010008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 515354019 1250 515352769 515352781
    0x1e0816050607060f0c021f09020a0905070c061814060f04151104030f02180f070509060d0e0a030e042901020309060310031505011d09010204120503071a 67
    0x224045600540d4041e48000546000b0031803203034040b5203c42100c1d01d00b04200780c10000c0003500d56114050010f480d05480b030250b14620b113507100d0740801d55030062900080e640350003400310203032000410b05c409012944101d0380101d1014061010b00700d007024420420303128689404446100300d41c1c820f2201c0e90002082054191030b911640d5003003031700400d10340715150340030003030304003914850542e58480c1d20f003c9000010010200440401c2d1071003240d410b40d4074075002242d811802c104035a408808900800442c205900410040c03580c0d00c000350900b0702c0c1624900c03a103000c3d10560107442105500504040c414542d2194000900000488051100712440c0315454052480d88541d10b02c601480d0415000c140e00810032100c00541c0039101503240d03e4240000c031004142c922041e160390340e100c10080350040703051041906035200c5010407030403003035030810701c1f072041c4130040003900559807c110108620ba85640064400c600c244021907907107500e45086900c0b5403101c0d0000c034541d078240e424054 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 515355269 1250 515354019 515354053
    0x30f13030c06052205101116080903010b0904080a02010c0203090f010e06212e21020910230a06080901060f0b03061801030201091403010905071e08 65
    0x3641c15000040443c054444a451513005800e12415840c00f1101c415a102049404252002014910482000104211241e00c1001e10504510512008580c3c102c040040c0024024201303085005d03000050808010f1b0109046901c1910b0507a1140c0000c241c000390507509000c7d4036210302891000d503041000002c081400441c520815a041c050345282c0340300c01c1d485200030341c0c50903021507103c0b00b040102c5850485154106484070401e204002000391881082c000c640c0301d0044804a2085a041c606001a02c58002c6c04032039a13110350110300300c1030160380c82c8140c0700d016104084402a02514290904130380415070481c80303004400902c603000044ea2041e0525013116007a0401481c182d54514143e0300401d025007264811402144000c074403a401100a0b601c612800e65140d1501d05283e0200801600c003448020300140780031000744902840e4041d41101c050001d0000303e54400349686040c00e00800d034001e400c0078032170030445600c854030062066000300340074006000d45024034031030b0745 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 515356519 1250 515355269 515355287
    0x90311010f2d0b04090f030f080714030a02070210030501090b041104031e062909161215030809010e060a120908160515010906060e100c17030f1303 65
    0x100a40802070301000341d02c21a421100c021100280308002c4a140c0b450541c5d5049541072080e40042c0c1ca0301002400e02303015500c0103000e03003a81c3e00c4000c00003032050700e02c0c01c655000902c04042c8640030310103500140c444003038618411100780c8000c40c00d5070402500304115081d407035445100745c1c2001a04095649444102d40a0701d4100e09601300700d40482d00c2d0340150803103008000700b11900e00318a03140c3c0b10784000043e9440700070030308410303121031154001c0120301e51040c0c1d448229408080018980f1a00800040e02503240000c00820b0514000b078000070100100d9105031900700b00010748682641c2c3c407419030b001140d0116503440c2020100b020051500c4428440f0b025650303940c3c68084240100c000956901c050700c880f0552140d4031610f012038441c40080c03101c15000f2280c600103d46654140502026911141d49404a03409c0310010000d400199141800c24401c951040c0404900d50405a00120f4503401c9196030383d080800203400d03180700003001c00c034201c40c40094403000690700091803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 515357769 1250 515356519 515356571
    0x12031b02030403020618010c0f080a090501080402010210050411030a03032403080d09060f020a05090907021b0f0d081201060f020307080919180e1b0607140f01090311010f 75
    0x21803c2e11b24400140d03800411000b000c0d244001c1014548100500e81d0002d100742c4030595101c0b41c00329070320001500d5940003510001d02581001c854510300f0102607101d00d600600a200481f00b80d004070700420b080c400300301c800390002078450011440c1c11160302c104812010003001d101030030034619124113031940604040643c42c1c5854045007000e00111b0b400952034040d041c681107580f0009200c008e0001d0b0311600340603025102030000590042e0000c150384880c103c503850031401c008512801c001c008009036041c0799000494407121000300b482000034100002c0d40403201c82d0107504003c4050b01404000d206c500031075204001c40d0300014203840603a294404240c8085c6640b440c0311146010300d64030764101c01c04044812610b41c00810454000448890f40341080d80d40c00d81c0b907070100d05641c0078540030f1203070090400c00c60b420005a0100e900d24111020340c0c1a2100184600000c90035110001c3c0e0aa0020f1060f140d020100e181c288107051b544060840c00f00000c0080c100d41d845540611551 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 515359019 1250 515357769 515357797
    0x2010c030f0203130e0105130e100b0d0f0302010605090a06031e02030a0213050a1113063c120c08040201030b0402070503030103200a03050c06070c0312031b020304030206 75
    0x10001c1074a000b00152698400d4008821000356200d80c44180106024892180301e0200c42c0c455410882c01e070310076028080c43c80005029550a031090300c1c00548595140240c0000d003040860380850000306141c040a0310076400410061b00d0101003010b00362019220541c02c9141c03000400000c0c034115003690034a140782426680c800258000a030612280220280d0040c52105d84082c9880c001d0b40654800d0146c860100b02400030106800401d005024168442045c0b40c8070600941d03000d0349510390354980c4900841c102c60b184800c2508202030600740280171803c0c6005010540c0e03002040752810b40e10302d00041041241010300204218005000070381810385d00c6100343c0054443c1d804a40c0e446030008200c2c6d07034030350303403891704c410344041400c016000100107018000d003e107040c10b05541100d801030000e28040e221841002104d520086040303540381a10500000060b5400401400741c4145440c0014405521000030500c60503d5550b40210b4008000500059407041c1c1a105503045002d5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 515360269 1250 515359019 515359037
    0x608030a020a03081902180307090608100b0a080307030c0b0f160c0203030c031201080c0103090b040809190902090f01080105030d0c0804050a030c1a03130b13060e03090102060f0402010c03 83
    0x800001c0a1760500c040702a02d8000100f40c80c4540840d607641320086010307012500020754070465001103518130b00910256401035103801c2c440100c290444186c1600003800d052001d0740d1114918956403008804502003900750710100c080c0040d071481075070f12019501110b00303103103046c0c0c8003280450b06421088007800110384140056450400c20b44030b040b2040000c4983c0d40f070507a902c00d40500c000348144503a51042507034483c03195109010300c2c041d02d640084000e0b11a20341d507442c0042908003641064200510190040c0c4a4110401d040024404960010b03a130f036580a0230f02c1a107141d00202d5605100c0140d00422003510000345d900392100b07062410500c01000e9140c00d01d805c2c45598003241d80422055404002d022070301400c9011520f52040c80c52030000142c0001106000c21a0440c0c201c43c082500080814590244298004e100810445424038140c1e112011501000a01c42c078991010031840000c0d40c0400409403c01c91000d452a12441d00754002060564051320040400c28500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 515361519 1250 515360269 515360281
    0xd030318080408010e060903071a041104061d060906010e0f010903060504050d021e0d050a0507050a140c0303030c07080903070f0801230405070918060e060a0608030a020a0308 77
    0x1052000241c0c1c0020040c2c0c1c0c907503982251038041d0010821005950003101c000c5528910300004030350740e03d0780c0440b040740800d0b08054501c00581e001403090b6944107210601d40498cd58504c03480c0007030050307003954a00d41082100700c2240c010000748464080ca0110041c80030980c1c0020110740208411209144070034000c0004071070000c040d610050030507007083c040c4030802001064000c280b1038075a00311043c401c80d603500305501e13481007400317084544c014000601802c1d00c20802081c1205941c07c2952030007242d6130300c440ca0070351000d03c2618015084031400c0c4c0b58a50034003041100c01400c40056086d030400004001d12449115030050500c5400150b54460313440c03d200a00040c00a0340429420a41c2d03201ca69000e00480381c001e41c82d503103014001c2c01c0d00d0b00c0442e440c00e000759040001040072504289294004003103102d500007000c1006018000000c00380d004500440e02c052010340140d0805c010101c051b200d1640001540307400500c4020341680d8002040b420950301803900603126102e007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 515362769 1250 515361519 515361551
    0xe01080d0e0402090d050334030806010828090203070803180d020307120b040203010b0d030f0c080405060c16090903140d0f1d0c150d240806100609050d0303 69
    0x4030002403c41c00049481c00c03181c2c01c0a0717140110fa1203181d800300c0c012341102444402c0001550001000b2640500c003064040d4412070034250720454510007800800c1c4e210304506003a64040c0400300449484280d0a402c500f01400158001d2160f10002d6082004015003032200d400c1101c80c0f18002e403906041e000070344d501008684010b01c415206034002000d98242450504000c0361305030302a6090000316103180c10700210040410340c15030b8641c10103842c0701800703e075419071090b010380348100c0074030001c150b03541c0d170318000c0c6070601c0c0400040005902422040c15000c03c15071000010b00d141025035402300e508000d050081c0e0308007a01165442c1041e0031003070000c204c04c1d45040142e900d001500c0000920b100d81220302d0300107142c101d03041010359004105401c0441882c00e15102810f2102c0103500406030000a0b00c0c1000c501a401c8904c10080b03202160328541c3c0c8030320041d0380280140083c0d05417603221080604524604194018108004580d0400751224024101070752927001e14001c05031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 515364019 1250 515362769 515362789
    0x90709060e1305090709050c040605070209060a090c020a1b27060807060905031c0f0e0d020303121006180312020a020a140301060b1602010e0102120f040e01080d0e040209 75
    0x100c8181040f081c100300d2000d95417100140600c0305441e180c000400d000e0108241520708480d0a41d0300c040c030b041c1884d401d000300d481002c2e06141d00181100703c00b05a9859034000ca0810798080d0f801062800c5840c11b0001c60702001c1c0610784640e0b11040c400380000c03560000110003d04154080c1590302c4100c40003140104199031002680c0e000720711000c5071041c0e10015510858504508072181502400705501d6110440c00c60107012036040e0f0b03010320210340564055500342000070510714401407141c02103401e41d4803000c05440815504c3d0100b000041c07050000310042d014a207000c0c0101c03082d01800703a40c20841404080d20b09082d400c003410045108100605509074081d0200c2c1e0724541d102542ea03110510003c3c0c1d144030707500f000d40c08640380071030340240e8084a0346101110700881c2c85400642c0c0c0000c0306007603035045001d5030111040f8100d418004000c0c801c100c0300d03000e170f845240450410707000d0b1f0180c222003500c1d001046640207840c3d0043c1d03240140c03801110f00599584c00c480000d1201c0031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 515365269 1250 515364019 515364049
    0x1112070e0703380f18041101110f2a0301180c051e04020d0204030f0c03050118051e100e06010e0c0c19030212190e090709060e 56
    0x5440010446407942c5500294a5940700525070b800d0703030402082ca100010340910140002501e800d8425455152100380181846006002c00035080c20940b43e1214031141250242c507400124048500c082d42c0c81035541185d80a860041d003081e00ca0443c001b92205034100c48100e44410408402c0340001100360300408004000300200000000c40440004030910742c80260f8050b215031500007298184040c550845402020f40040b040c01583d040100a4002000340710006070300344004000a40d0501c0c0080b4414007030914088180d18601c1d107107083d5442045c0004245020224400c0011000031b80b80184103045a030016a240282c00513501d4100f80945035040b1074142064905041b102144c8070741642c5410381485002da035800440480c5104050051006034846078407004060500c0090001a600c648103075444103c0b07244901e03515400000d844d0030b407811070040415207281c01035070565083d44241d5000c0000c0c03034400d90250958030139100341010b2020090310000507603209642d1100d1300e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 515366519 1250 515365269 515365289
    0x51504080d0912140a0e120a0b0705030f0a09030e0105030601141b07050a060c03051303150c080702062a0d06060e19051f03090b010602010e0c0904111207 68
    0x1561418031030724260321411083c1c049a409101c0c010402d0224003281c00708551501d84040d00034180050002c1040100140c003890b0180341402c03c0002c10b03e60025000c2c0c41e00e540c6a03902da08128008011118000d4200d42880349070080c00800a600324107030620022007404c0c0350b51255606001070715001c1d240200040c990200058011024849940c2081401085007c482c81704d600c500070300c0b030361058600031b800c0803901d14164038000900c030360010002e41511620106d0700e40c0d90f82d6100300c541081440b03a802820340b00c1104043ca681d0001c64a40c4c032010034802010316041090060007000700359031604920704102001a42030340c070a2411a489414104c408100041e9242c40060040e0110004a0310031140003d03c03004011000001d60150f0701d008040c0c440e408030582d0700c2c0c0d070224559803c0d4018140c40e44801d0b004181c07090152402040030b600041a803607c00b0f8400740c20104200c4249203c0c00881043c88049196241d849a00180a03a40e44402e076510081e0b0728500f0b44d90360702010f110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 515367769 1250 515366519 515366531
    0x50c061c060b0d0e06010302090c07170a02030d0f090b0103060b1212040f0e010b03010b03060111100b190f23090a09110916081005310603051504080d 66
    0x1c2d401800418240ca040f0a00300042e003941c0d06540d072641e400388001f075030140440000c00d40401c4510001c0c000144a00c2540c80d40300085801502c00c2d4000704c2404025070004203030604207031000e00401200e9900302c02e00300075202c842d50300c03030030810810701001e08899a101d00f4803209496040c103c411206242040f43d941e04511829182298018014011070505448001648011f815140b074162655001064103580c00d0624040580c1c000401ea1410810b86102d5081c000e5028801d411418489200c00702e01d4152071800d00201c10b023452200801c2c80c6440a00b0451010300442c0c803019514614100d001d6010407801210001c40701c400c54aa20580403028000c80020030750060500901c01c2109030101c4001d50200031001804940072a004008920507548040c03150b02c40c6940300c20700c0b40402c54201e84520128042d402000600c80d00041c600b117680001000350a50b100c20711b40b00c400b05102060650b5107807600c5520005c0c40c400d4a00080300841e080169003800c0d0b489400c0300130010020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 515369019 1250 515367769 515367779
    0x103110d050103110901030302030f070606030f140114070903020f0d020603160201050903090a0e07090e0a150b0c03041e1a03010303030b030601060e120109050d0e010906030603050c061c06 83
    0x8150a10086894050440340c0380014282035171180d0480f90150081c5003402040e41c02c4004c180c0c04010100c0d0456603030513000c000607074035102103a0003d0058020324007040c50a01e0707040c00c54503005000c9800101d104208010a54842d000768266981507501c01100c1e80c140f800700300007031100480254001c1010003040b40070ba0a04400140001d4258000c1c0000c0c1c440f030300c4a41d103034828400034940140d159203041c0030611106612540281c070914150074200ea0b21300c450127100e4030a81d0304a911507158010a01207469000b10301c0003030311920412a190407102003449549100c0e61065032140c02d040709030304011110111184008110211564040d03820010000c01658024007084020030f1804c1072040241c140040d5460507954a0f845480c40300303000e481003002c081c108403c494a43e40d21ba90706a00000c400780070800b400340030b03521030b0300800707c00c10009000895550000410589820f104002240002460031354600b4203881d0f4941c2e80c2c9150014450454145c103401802e90309107000000c3c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 515370269 1250 515369019 515369021
    0x201020d050c07020a06050405010518060c0a20120601091812020109170733060e01060e01050a05031b0c0d02060f0a0605133801120e030d0b0103110d 66
    0x2010134821201c1c8962261644410350782802180102c90000c2c5003403000b502403546da1480d181c27054030002e10780c0c0d00740115a1003452034038014000886284182c59800210490024041c800c00d030f508440351040c0007207203680340c0d0343d9220511036080320320344038001114441681480c5200c00e541190340119507001070140603009e031408004c21200c02d0190400000503005100c146d0380082d0340202da5140d60701c010441080700203180300c11044a41001d0a41d421006054072400f80103222005000c82c0b191301d4882c000d000700366100c01c03260500c0300810160503401d500c01c00b180e40c03082c410350803403446880b9504940800c2c01107082420880c400e009a07241925000900782d03102d020001071014203030fa1a05207040a0700c5082c424190001d0740d01c0303034012982d02140c10a21123041d0b040c1e41c0d5618400413400d07030310070107030b42c80e0243c0001f04a42c0003142884d41e0040d59000e104203084000d003c0c201c0c5200e040e596030f07c100100d2000090b83c41ca0f6001c2141e11a420004000c00c0c031740c6440d5210003190210354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 515371519 1250 515370269 515370277
    0x6070618030203030f07050a0e090712020403061a1903030c17040b0d05010b0c0c01210c121802090112021801080c03071409010b071b15030e0f070504020a0201020d050c 74
    0x600c400c0708560010302e165100c0c1088900383c106950f2109c0b10400c0c843e00340002c20201410300000e20940040811061781144054802036000e410003040411150400380240001c4d610320034040c01075211445041512544100d0403264940b90030043c0321410300303000382d6045e10304404411200d4001400286a0710035000b6109140390080204016661034592040601c5038900e0745849400035007aa11007507020300d80341c04050500712013590320001c405443c2c504445c4400b40003070202d0019121050007070898071411040f000e00303819104000c000c940024040180502c2405036a606012040d0219200c0380407400070b40c511250400200d5840390049621500030b520424001c0c85100c400041240341d0341c4103130340e802c80040d1000c1070a908007101444590f00100301911a4645045070203540411416000010100c0a0707031000f090060040003000d031203000d1031181e5981e0020314090305c8600042984000c03120222001644d0f20b40034802a40a03004913890000230701d20b85405c01c2501325241d4014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 515372769 1250 515371519 515371531
    0xc030409110904051f06050a090308070308270a0b0601030f09260f040501030b01020304080a080307030e0105060a0509130218060132070212030a0c0615140607061803020303 76
    0x80c000b9594408000c400701d00c884c5e20000401c00401c01c20810280128024100c00e1032078944035001903242d0b25450342c254400c910407000140031b802006045000c0780138040711040301d01b00c14403464a441d42203554070103030210040d06400d03846000c5041d0b0f80c042c0e0300201040441480600a22038107003803454075400c4808006d510f4118120100500300c44a1b000c6800760220010b0241c00d1a06120045000301004074505065203c01c00c80401c48240401148110b544220042d554030303e8240c000a058a107403100c54034103a81404144406035032421072040940d101034803180015a40c1d6002440242c01804019400080100b03800958442040c0003521443c02a22004a11541d280d1b0040010103c1c00b6450a400851900901c240764050000c006260006154050007900100042d04540c0001c90ba1030114003900402010480d050091950005094080b1700140d4641700720900e501e050304c80250301c20350b00091030104102c0e180e032014140c0c0c19017440e003006e544054a80030f03541e40d00c10303109 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 515374019 1250 515372769 515372771
    0x1f080d2c131407110312040203070e01030c06030c09030f0f02040b1302030406050606090102070605360f150a080c1b101808190215090c0111071202060c030409110904 73
    0x3c0e0565004014075030280035054011071030032541900562540c1c40c042e01c201da240c0103000300000c000f803114000c580038601608210303008514203c005070484d01c801700b016040c0b01400c0d000300003064070041380c41d2801e5082200450542c0c8548000b13401403918440710755204038035519091407042503501440c400c07480b8000801203500c8100c10021b507805042e20190040c3e00024081c01a02e100744091302030081020101c84400140c1c0c070840c0c02201c40d6080c40c0c41b48030b8103050158010b1400701c01c3c040c1051000d0f1000094410003980b56510b61268046200901503000d000c00c0c01c600c2c4d41011140c91518003900042c121b0388141076141c4946d1010240c3d074955051405c0301c2d0720b02241840b149a80c82d40500e81501d0031544d94220700c1c104134008401002d501415120139251003000382c01a10403070000c1d019160440d110030001d04043c564100b00c0020f41d0020900740581c410502c41140c000380c04580700c40c0c40380c4914042d1440c501c120741040c1c10040c00c1c40c0c40c40314120b08080c0540030225003118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 515375269 1250 515374019 515374021
    0x1209030213020c010f0506210f0a030f0206100e0a090c0506040305060103031412010302210601060f090e090705010c0c09020f0d0507210203100e1f080d2c1314 70
    0x7208030540c2c209a6040341d100000006c0d40c000c04c0008180f095892022406564000038049c0509042c150340d0707081600840e05608245510302d5050061036404140360022901007030034840400c100c040020551101240e840c1004000e000405207004003d110003820b0b03598480e183c0c6041c64072118207102c00c4000c542503103681c0100801a4043c0d411030b4a1111401d000d50f0300c1c0d9000c11040850690051180000310718908401140500885000c2c080640380c440d61414076013001446054694402031045040c402480301c1030a0104002c8102e4409192070840d1880c41d0903ca842102282d00c60702c81c062000903007044000d000000741800b060108000c100c1550380303070b0040e54200300680b8005501140100c040d01c121b041070303000d9504035130701140c0c9803500e0352580d103244d060110070f48001104518a060180040181014590290000c40c01034610041e03201c1002d032814509001d200041034004524108803a000001d0140d094001001004295014104d400050240c901031442d1418288 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 515376519 1250 515375269 515375291
    0x30a05101116030c0804050603160e0111120c030c06070c120e03032d071b06030c0c12021204270204050a0e04171b0f06060a031209030213020c01 64
    0x190907500c001d202c1d4107602201c080c2698048410303d04906040311640010310000c03982e5220103001d503200e41200c1c4242c102081c003409014100582c41e03000f16041000100315514030006c0072644102a00300c01e000380345c5495070218124103502503000d190f1024400d95003003103603042d48503500f042044d0084444035804040110100c4030251a180750325090303402000f041c904040c1021100a1131b03c961030340030201410b26019850142e0000d6825206e0308031554007030900e5062140154020400385c141084080e1444d003002d0a00081e8101c00303041003407000d041544950090200810b18105802c4c0c09990300e8641203c420040c0900030020788202c2d00038000300c404c00e10b5108483c1650700040800f03006c10710340100014101c0d401001104c0c90f5258141107100035848002a180d1581c0c8280130180404c00706103030318907052690042c032203940d00038420f0100c1611080c0e0b14100750f9800001c04405000b15680070364040886500094020341030034100071031450300f0b9010b403000d4503806000b8020506c03c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 515377769 1250 515376519 515376551
    0x30c1311130f0f0e070c060b2d09060d0305070302071d0a0e011104050d0203010b060d0b2d091509040c1a070c0510120e010204030b09010203090c100e030a0510 70
    0x940580b8941d402207102082030640100030070a40c4600c00d11f400b091045855010540d244070116403001c84044400750040c0c50012107422644580050390301000c14035142c0006002d103d5682000303070500c00e00180b26401c0c18030a000140103003030b81d8030710414a00c041c0250605420000c0354441200c6241140c0a00c21072018024041c000140c42100c074200740c144010050100e801d5001280e05641e61a02481280c5034000a440b03076130041c000005080f0118001e003c072109400070520b00654030450702007034031354840e958240490000d841103290742da120881300724101c40b901000fa9110100e10104420800745240b1030054a4100c0302c801564120b5002811440c01051402041c02c00c929505119600b8100081c0b001107135107140c510740c124484900e00d0111000c00c080d14520387d400080038000c2c440b986000640101180c0000c42c69458a0203801352903850b0608040d100d454a0391072544928031039440e403034a1081c020140c510300d88051900310b42e0303a1001103112031690304014410701e400040c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 515379019 1250 515377769 515377799
    0x190204180f17120c0702180f0703020f0403050102031303120c021f02090a08010b090105150d09020a15170f0105100e0a120803041709030c1311130f 65
    0x1c020704a81d0300444507621000b00500d00303024040d09841c00d0001c042d1001c2c0310360801c4d028100071034101d41e60350054018042007181040c0d1081c00070040d0024000e8640040355400d601058030300d0016200e019103410b00782c0b01d10640d840a4480d40c0007105024402404e2402207820922a458016404131102c3e541d00130b40d170444c01c01c0c02c0541c01a41d1441003d0300814541c0740418610280141b4141d02800058410080f42d00301c6105030b0766807a00705015040010210f0f001d040c045590780c03a8144c201e0707407a00d0755201d1020b403450955183c1c0030078001c649a2460f504007610040001403099440c134940100952a8030064600c030110b02c0000c00d1544420400480c1170b80ea0292440100c5921518141c4042109124050308490074175400501c200413035031001544d91054070b00d40d68906050604025104400210b202000310810200d121941c00082107111000251082403e1801155111008100c442c81c1041034038000a844c96418507450458802d84491000c0c015180343c03102c2d0203942d0707004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 515380269 1250 515379019 515379023
    0x905120703080c0f0d09181505040b0a051011060c09010f1b1b06021006081903140c0f06010e06090103020108132406060c080708090a0819020418 64
    0x25241071010840107402800000400300444a4422003007140b18070b08006a44818005051440c051001003154012020104140b00b81445624a800410600034031644a00b41c03044d80d45407450346490701d904071000b00900d002080118041c1003104068200c141c801da0544081c040d01000410b40c0050005a0703076001010303940c05038280601002a90303d00510404801d031686072461680000b14450000e07401c10790841040b003e0300b0300e03013240a81303003941c1d44100c3c2192605103c0d0901c000b5000113201d0381030418031b5070701c01d071144d0182c141071321a82d09051944418100000300094040030010311240d070300010200b104d00136a80c0b500d09888280c0c3c183d800903407100075000108090343c0b052002d03540003000c500100c890079030190390716410300307405414092140030140e9840400203694442c000c01044036052034280d0001c1c1e69500441d42c45200d00051880d0008107030390141d0744451301d03076101070301e80ca07421100c0c00c2242c9031540c03035540c6c0c000c1c10492145007040011405070603644403001c0c0f115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 515381519 1250 515380269 515380273
    0x1b050f0714040203014401090b01090b030604030f21060e07020a0f12050d18050111040303090315150f090b010e1305070201020d06170606030303040c120510020a03020a090512 77
    0x1c0e601d804c200030764020810040034181b03040400000c0c0c00040000c402c200c0080b0000502119903e003038014410164856002c02e80340c4941d201907500c000c83d00c158000e80c1403078014041a0414030544a400360409500d0034624000a05d40030104182c0c0607009882c056400480d6039a140c1608903600d241c0800d0081259900307280341400144071880d0f811400c02c03a414500d04014a811122048421032008042030006119111052281c203220780241c0c441d03a150454039040c11510702825041c128400245500d82c1601900007070364060b4850307180d2a810341c00b043d1340c0c00e070b0360181c800404400f0300500c3c4040b4500f48449a1540c01400314851030100901001110344c6442003910003050010000000d654081120241a035510b02c10b02c80500317015604054200115410245030110007400c9a0080d0310401c14007011881b41503000048031900c0b54241c00c5104246015030a04130f00e070582214150001c41c140070101e4150b0042e26454410741c0d1031001c411340e10340402c000601000f104120755 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 515382769 1250 515381519 515381549
    0x5160c0515030714462c0d02030f06010f0618151701180f180b1008010207061d010c230418140906060f011b050f071404020301 56
    0x6007541d001802410050807824040d204106000b41d44d003000401110080c0c0a030101415600b40301c1c0c2d408858005004c6ca04150302a014400400e4100a050b070000c1c42070b51508114201070740e40c4285182c0c8a40d01030b066030724401560101c10390300c08080c05180b0100e507542c034000c102c01340314501d40c0303800741282940c4510503441c05145051501c10884040c0c10000581c880d01702e80348009100d036000304419958601540c15501070b4000704c0d2850840c1007440390a2801e8070b4103100d400e101142c102500010401e03d292500e0203000307a1203880b03510410455002090750014092607074043c0301c440907a8125019861881c120940c201e620707106525003c02d05800c106010300c1040881404a11412104245015200c1440410341003003103001d4070103551a281040c400030301c110f01c056000040c4500404060800e0320015011340d86410046040121040800c840b85100d001d1164000e41c00405444843d00b1145806440700c2460140300140b441c401000702540c2050310841f4100c0c1d01c142108401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 515384019 1250 515382769 515382797
    0x50f070e040c09150b0714011a0a0e010f0b031e0712180201170603070504150603180b010b030a140406270317060f060a020312060906030c010f05160c05150307 70
    0x30b03a0807951056400383d86071900b6060031f8509116241c00000c85082181000304070b50100003041c0c02c142c100041c61041140104400c2001c002e000c02592800a610b40d16076440c442022243c0c040b0603520b494081c00c0b202071010041d000100010303545008282405818000410040d0115048a000340065440410859000d40d95900c0c560070040040a44550075611800902603401c082c00350003001b020084c0800c107141c0c0503ca066480850300c03903809281801170300d8402c040407052090081c0d1400000c0059540c03200e5034849130740c07a1134500084c1c115042c83d0811100502c241c10842c0c0f0780810031080750007403110300000816030945c0340c1d46050031070041030208207010301c020380011b8000b0901202d181c0079664650103416204455802140c0f00c11812104c00030000c000b405241c0108400c0701880510740380072a4014881101382040134800e00000000c44042c8541009040481215402d403400c00683d04c64040450704111840240271f40c0c10f0b02c1e400d0207440306440c088007080307007001c007460 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 515385269 1250 515384019 515384039
    0x902030c030621030c0609010506040b030a0b040c1205010c0806011425080a11060c09010c06202b0605010e010807020304090c0f1808070909050f070e040c0915 70
    0x30714000c94111190302d804540b01c0c031461508851520985d68001904008071110309200e2294400f5084805200c9044100d01003602e616490744041c04210078100000c0920080d020740c407001300180301c074220700280641801d0b80244007030440701c00010f19480129015601c1407030070154030140c035182180740021020b83d0205040640c490002900b4204a02c00042603e640c0641207244a90726170080521501c40c0d420704114004148e02d03020601404882c2c1142d034801224442a0f901100005449402c0008100040041c20100300328001c0050010440d140362042c0004008410b0541400650000e041c881074400c00e014407400101d60060401096210f00340c003d400c0f0109005891030303d62120001400d55418441c5a00414860403019043c40c0e4050000300c10461541c91083d40c4038140605183c5414580c441e07600810345031074010003803220501810454002080450310315a603602e154101101c403c80b02035a4103198504002291080f50181d446071440f21000c034490780d42002c42801c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 515386519 1250 515385269 515385289
    0x30d090b1b1005150108100617060102010f0c0201020903070e06091b12090703020a1217030c0405062a060103031209080909040b0105040c30090503030712060902030c0306 75
    0x100144646102c00303070121024441c1e980100078428011128030f0403640098640d202c06044403803008035985003001441d42c490018000c800e60568403220a40707404004034058181080c2d8052481c0c40c10a00e03140544d015402001017003015015520516039861b81015429400c854607034000780140700003203502c2ca014444500c1c207907aa07140340381032130034100380a41401300031511211154041e1106000758a41015103200030110507412945101c125540c480d000f140708400f0341120350012010a100304a16015200030700300250016440701c0042d41d0450140111070b40c00c400703443d0f800c0071020744040041010790583e605500c2e11410207070389a118600278010540255000b01c81804020255941c0104c0d641c051401400b001681c0e5050204110849141e01d20070018080700c1001c103d40b9404a0590001c5c24401115246012041c900303030b0806020180c1c4000c2c0a40000010000d89039080b030711329103140c1074a85082084030385426244080703110540381c000f00014280001070795850092a18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 515387769 1250 515386519 515386567
    0xd060c02031201290304030e1e13050f09070f0b090609040c030b090603160b0702060f0f030a060b13090f0e010f020705062a030a0b030d0905030d090b 66
    0x12441c0448980b0600d100420a803c03155541880b10f040251201601116242c0c0c0300f8800001403450030940d6002e403081041001c1d280c000c9504c9a42c46c00c0314500c0d41845403440070082c1c840750345055001c2c6960b005005c202ca01419030401040030601c242e500140542c1075a6214444450712030414401600d01c0d01b00b0f405060340a02c0c1000441c003580c4407801207188881080d1400700341050b40b8002c100311340c00c0041c040c600941c04500400ea003040b00707c1426080780c1c80c1340d804035559402800417400c2841412000c6140690009219000004500040d071003201190300410480d510b610700e10829100782e0006000f0482d100c501840843c001e64098000310b00311407000210800440403a81c00d4032110000955840c1d404105207003440018801d06a0148400d040100220079469038002c8a140c944040d48100d4004000900961540e034414034100354000c040f5800280000001428544680502402030041c008a208414082d100720025201240101800c0c00085290a08030a040b5011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 515389019 1250 515387769 515387773
    0xc17040314130b0f04090c031103160c060905150903182215051e031509030c0a0b070f050c0d030c0c060204091d06090a0807111309030311090d060c02 66
    0x2583c03120040101004101e001e003240d140c82c40c00341c13980c04840d026070103031050508206403d00361581c088103c4c0e030b020720500d246024400e9803000844d001213040300e0042c603040c501b4180c1424007100140d01c40e00c10300c4100b0700e40502d03903400c190302e41c50303008040b000382c0d200303100d0103170081e49280620907003405009402d20320051481680503a400d44030441c16090303812038802c0051104e820591501c080c00c4900103507041d6444805008242d4404480b84004402c40300100800c00b60f0005008075900440038000b03d0b08110340c5810464581d404c00e03030703003c8041020404001e809600840c1a81c90010540c80070b44031513280b1140a40142450b8200942080140d030408000030344035201620103880c01440014020240d221001d200d54280905644240d014800700403100200040d541ea026620840c00780d02c074030317480c6030002c10707981010804c59102880d02d096030b002d4601c9602c001c0303906020341d42c02c0c00f00d102d80d226004010310542960a0308400701440c0c01d00450074507008441034081c1481 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 515390269 1250 515389019 515389057
    0x1404060318021e1c1104050601091211010206250c0213020408031e090d0f081306050d06170304170304080607091401020303010506070b040f02060d0c17040314 70
    0x10005a60301d00c1001c0c070326108043e440074102181402c5121007041565100c0182150601d500c41c90021110400024403403521000041c400c0d9200301e845a00600910b070380394601e00e030185065503104070481c0c0000d00501c2800d000468040302c50110b0a00c0b03041c0b0040401c151921050100c6801c0d0040c0c405a800545000001030b00301000d100901c020440003020710b4603000c6540100d0483d8031904c1c001c90900406100410940c1d894441c0c403050140e1180003055500400e1914045900848444c2080d12440c24000500c984d000700c020413040068080070054036486440d41102c01d0110718400041d17a10030710040c030002c0a14403410302c4126203031040700d00380b40d550040315207080022105103001a80c174903001c00404520001e052800c00c0c1c24000365040d50f0504010600310f005243c0090540030328400401e0900c2600121100340e41e80203004e1940d1000920f5540d80948140940c03071000810340f481c148521802e0340000d0340982e40c141d41d40500310b031020240c0080da4200044e005003a41000d9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 515391519 1250 515390269 515390273
    0xa080a020418020c01111306090803071e060e030315040b03072306160f05070f0e07050714070b2a060705210103150501060c03020a0201110a060207050307121404060318 74
    0x40030f03000b103208031f0107a88020b84c2000401005039000d41e100c00000e60081c4007941c00550035403400c0700140394500d030900c0d03e50b40c0d6060400141c0304074100c45045000000502224100700395052007980d90035281070008410748410b155494006200303081150700c60500008a02c40c0b2100e02c140170b400e00030086070801d1229191900504201d000407030700307038a1440030801041410f1001c180140600ca180314156071818503041e80d121802070442c4100200040e4030010803219460801c403441080c803c4409490301c8180c448071a511960840c100b040e0741440540440307800c00008030032090320030050b000c1a12021800d8602d0707040251200304a8140c000d1071120385560070300d113900850140007188040d010855030407040326410b0304640100712108204001094001030350800f003a41c2171030720820600c03031101011b05140d00f40d0030051140c3c1c00080e10105000000018059240c010040140105665082500c528006e4100c103070b440c003424442008098001d07442041034954029200e1008082c41e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 515392769 1250 515391519 515391551
    0x2070c08012c0d120603120c03020c04060311120309031f0b0d050a0308090c0d0807050f0105010e04080a0c02091905010b090604170a050703080a080a020418020c01 72
    0x180c1114103140c0d92008a180c494a05039000165031201d841c40c51220380c61108541d0301e41014140d0107003031090184a1a20f814a140d0212000f55080301d2103920400c58410000d200c1e9401d003030181c005200d20311020803d860188075040071294881021071080140c01c00b4080386000d007003c245824081441841510340741400705035141401c8442c0c0e400d20088402c0382404460100b2013460041c0c40c1001c202000400c00181c0c6030b6960703003608010b00d8669a4510161800c4000101550800065404030b000c10a4038406418030510030000c2d54456001079903070500b00c503424820031000203040310104010a290782e005000f07143c100d05c1c15044108032070b000f1030142c2d00240c1c1c0701403144009040000c00035180c0e100f454050041854070070714168045001030750f030b8059030064002c1e4007009007080b00c08440400070000c00b580c0c07100985070502d0380c0b0b0402d10b00380e80080105d04080f0321144001828207000b4801c072000c1e52003000c800004d190038110070358000d410070000c2c90b0f819075841070108560061 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 515394019 1250 515392769 515392793
    0x438090f030426011401090911030f0705031011161403121905090c060c07052106070203070203031923040f1d160903080304050606040b0616150207 65
    0x1c3c52142c465401030780307000c02d0300800b00400040060b91600c6902814a903414020302d04440a000c0c1c0030030241000e0805200540380400c1e460342c107105a00c030145d0100801b00b41001250011801d540c1407064a50403081616100c118415054108000742d4201e0707031030340481ca180310380920040700c020100440820314641c019149042141e410000704aa40c140080d01c484034a11031000510213030800103102540c1d203680d07407040c61080307401090b401c1c1103c104001e20402040000c0181c100f00309a95120301e6509070350444402103018050024455600000407030b101d407035019008500d040f0b105a94034140b81d0b4030f040110200300200e44c0c00d10520010104160402c000101003039a15071800c810003001d9607840d4025040701030104c0180c0d0355000b0701d03e40c055001d04540b14028020460013011070741205190802080c2010110500c01400400180a44107400a45080101c91584400c1083c2802410840d91990300801441c000103a91149070000210280c240581001d2050351000c004d031070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 515395269 1250 515394019 515394029
    0x60d080c0d03061505090a06031a060313030e0d1e110d060f05151309020f150c0105010b0403050a140f0a0b0f06040e06011a070c09050438090f0304 65
    0x3d00c9007000d020580d492900810004030303a05140e45410951004103010107407611510040c0343d075800c018051259007041c026801d0f1802050a075032464890b05600b2041c80d02e42c016400914000b20820882c00c20488140c80c6940000000c0381501545540d019140310f4220100c1e03421111002404168a8001701041060310480c0003180142490a01d2401c9600c010864008028101c5181e1150384400203141b03072003020120041031451840c00819411446600341da81c2090300c3c4082191490441c1c00502890030b40000203010f640d0780c0782c4009403680620701018085030031000349900012a0701d224101c50403038420907900040f414242e03480c200203056400380d450b54021001c01c4110801c50010a91004040b1800c0250307014261529a84040c1400307651408650751429004440b40d4a0a031441540d00101c014030382c980362094000a040c4c16181200c00c01c1c10087c20125020f409441c03490000400219a44104540414101e8502c0040e00400c070741e010b0414081000841400100003800c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 515396519 1250 515395269 515395271
    0xa0c06080609070302030c0a030908040e102315160506190b060307020d0c030309170403020108070e033304030e01121515030b0d050601090f05060306060d080c0d03 72
    0x807034810140110080002c001d102010310400820904a5001090710710781180c07443d00290075000c40c64400803034030803500060109d101585c1080b108504003003002054076141241c4890174916465401d41903807603291038581c48104d8005204400503610f0290108107401518203400010307d0300c44600380351080c1c0d1103407160403108004030a802441d00076440c050500741c0d2113521b54500040000e40714202c041c0a4020000d8601e0307034006040c801c2d046800510b4124500214408007103080c0d4200d40c0c080d01c012408101000000b514690050310709110041029002d0300309102044402c0440303949030303100c14100a1400021040246800343d5840c0b103540710b0703194800c241c02c009002402c84940d10381c001808504040500d030f880c02c00911403404480044440401e44101580b0170ba01030884042c5054010300d00c00d58080902c000058218100e60f0f020b0410066040d040d50204103030368040f41c046800d50300042c0481e025040c4115010038040c06030080f2401d000c0d83c081102c1c200350310340444900003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 515397769 1250 515396519 515396521
    0xa1809020a1815050303030106140f0a0201020711040c0c0210030204080f07050a170a03080c0706020a020c010f0903053d0504030e060a1b020609060d1e0207020604170a0c0608 77
    0x14003843d101d1101a88485202c00541e245400002562071005026650402c08500d001140001c810300590f4034075140058506e841d0000404001e000b07412401c82514031003007850108803a07080c14030450140c4101a680c52000e03004036001c0c440030004950700c0c4401c1607820031000800b0741081c056070000060310000b03030102d18036010801c5469903072900a4031019900c4000b409003e0340000d103511080ea814281003482e641c0301c0307003001004d00816070003900c881c2c00056150743c10341d808181110011805d072108114811415402c644410030b50100034040c0e40251080042e00380d44142a01480010b0070105a5400100c0340340c101c00e2420058030304106850708240001c1540140c80600b4000042d21068102044488028040e0103040151002d0031090608070040d91128011540c08000c090852680c2d500c141180800070191106603405040140b101818403951078000c81c4c0b405034000302000d00707003400c00007851032030240c0b050740d600c1510420141400060151095800502e0141c86005203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 515399019 1250 515397769 515397809
    0x1b03030f0605030d0503151807050c010501091e0203040602090a0f08150609060f0d0c14040608031306141303150516090b0a2102070201110c0a1809020a 67
    0x15107038150045440ba422802c0c9001d0915881800d903035002d14020309100e00b00460300b01140048140c1d081010b103003c1802c1c2003051264100008012180c4204001c12181e0790305c1880d80e0484e005c852681c001000c2c110201500b40c0100d40246400038050500145400308000c00a03154551941c03100b22540e000d40410000c0310002e0100085801115104203010b1070044001128802c00421180c800d00d0020581c020f280c45008686003143e0b400341a5a00454607421450612214080c4a51182e8140400864085404020f0b5188030104a00703d04120703050070b03020340e02c100b200084003039a01c0c828410001080001911070004600a20000c0c1001c582c81c1c40410584038000c200071100b5080b03e070054007195024441804480c0044649030b00c0f926582c00446442294112205080d4000c0116400da01d1050b8000c00f0205c0c401d807140b40a24032440c56854927843c0c10500715a01140c0000304021051840c10140b00003440100002800a19540010791000d1107030400000b82c0950079806032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 515400269 1250 515399019 515399021
    0x5090403021e0604150f4706031501110114040317040c1517010f1d090c0904080c03070506060a09140103080a020c03190303051501020316031b03030f 66
    0xb500030558040d00c000d24160311280b5040000148031208540e4501200440079990782c092413001c240ca03100850701c1012401d961000e03000031040600c1d441d445c3c081c40300700c009144100c480d180c03002900702c5041d5a20622000c001d03080705042c00d4140000e00c1100340300c0c04002e1003414102e43c0c0c40c5000d00c1050500781001420b064061004500110820040c4800b0034803112100003143d150701c00c3c4160f445801d52003252200ba03c200900c0d4811325010010600d45a1440d401d0142c0380e80c3e420f55814100c044501003003034001a22a032000e03800841c00d07001c40c0d0030041e01041d403040c00360071038620348080502c54a2441e480004299615089482030100901c1d002c28908010010b14a00b031116814060705241d00240612009000800015012003041d0003030011040120004040d50500642048569500c0b5a800400c0780024034007000212015841036075003c40d1001079004509000803141703903017117031003950400780c0134041500c603604c4c42c80023195101991603211b0b07900452010b200b07a140c90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 515401519 1250 515400269 515400313
    0x1106240105030c120903040506120610140d0e120309030901080a0e030f0d1503050a1716020603060315010b040f0b071109150303030103060c08070c170a03060509040302 74
    0x1810068108140f0044440d104140d4aa1004141110030191242400580f40d0b11807a40002c2d0411404540c41844011a0300268420481550314014068182600b00c403039030903401130031640c2d11f03090100304400380f010f600000761026050100c8540791542203c802680d08200c400714402d91002500040d196400302d1001e8220307144180600907002c203444c401d5142d002d40034412114050110302c03503000c0045a0000c00c060702520500c22806904c03400c10680700c510080c0252140341e0280d2031598404021011103038264020712104506012a03401c2018030351025025680c18452400a4189001410300d014020030130008499982d914040c403140e254287c035806250400d500340006400714802d0003218103200700441e480e100645d10500c210110500d0082415098440807002000f000710950045205800d40d0315202c03815074a8a40442d04031a210000a00e601400c0002c000c81810000181c00c20013040d0401041c8130f0340780c2c0c006c43d03100e130f1080300c00b60010703032002044255906040c2c80c19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 515402769 1250 515401519 515401591
    0x2042102040b102a0c03050c03150f01060804030c0501142205120304140a0305070201093203190c1707120813090c0306090b010c1a071106 61
    0x20707400e0682c0010014001140140941340001100c024410700494090f101401065100701d80717002961b2607090643da41c0b03103030f50605402407159859500c40204034100140c400c03107010311111100c0e801c200040f02c02d102c020700120103100e06c4084c5040019400e00a02c42030198400e203003001d1345000c0c11320315509139074032142e050b1742155490368101080d0041045155180d1849251355292201c3c43c044c40000c0312404201840d004104518040550100042403942d0003680d0b1000e00d25192401c81c0040c1c0c001681c6640240300c1c01c1003c903400c074045045004102001401c0d03510307a90301008070610078070008000b2594180410741c14000110303065043c080542405008025003810325070b05c91760100c86050b0140050301d0100c0c07480054074155120070701820001c0b9091040006000000c2d000d041503001d54580307182405200b02c4a07500c00c11907076180c541c02c9aa520903607510f031205090741c200045c02800030082d051404c0003ca4104000c568081c41c5159806443c0c14500507031103891060a4081e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 515404019 1250 515402769 515402779
    0xa0605040b0105070f030e090903040501030c090e062e2606010c0f02060d020415030c030506030a02060d02040902161101081303030c090810020903010b04111c02042102040b 76
    0xd54007107640e1190641345200d82c0000f020340d40008a060548400451890542d1700015000030021400400700207402100e0342a01c041c8108a20050155030328110b42c0500000d0031200d900259032450030710b40205044007081180640c82a001c189140d0300700c4801c14581c0070582c02c44418002812504110b01514146642c0c07030018100720740020a100c054800c0034210403c2d0f0800c2e00159610300c0e08032120001a02003c44d503403595540303407a40c1492400203c5000c81d103020390b540c240a02a004441c414030004001d0300c2030070b40940c20401d0780d8104c007003400780b002d5080c000400c40704c1040c401000d88120f8202480710036400c0b89419000070081c031414504000908080c00f0300306110700f45200489600d402c011420382c01c40c04080303461062691114900d8441c04680701040b003001e50041c40c8500e4103600a00800d100c0340144000c0c1c2c2d0200c0780c440e800207803c100c01042880042e03620804040480005031070075550f09944c5607520706007103840c1110404001201d04500e058410310703400030016a2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 515405269 1250 515404019 515404031
    0xd0c09050406030809010c21082d070309170301080c0a1706012c010e060310050112080a1403010906150807170a06030512040f08160315061206050a060504 68
    0x504c42d90036019840003203052041c030b03c0024003007003003c440c1c01100712030101100108180c030500041c0f9111007a514800107407d0208490b1040c0400c800c58035501500c003441a566860780b2030304038010020780b14140c5011142d03152901c075070100c0200450082520600a04c012040c69080042102480d405140800c1000d040003d4071440030841c0c504585015003490318181550095480703d0b52007003130568149801c2000426007058640d005800703000103404940908503d01030700c2d01242e600b801400b48000f682043c070800156500020640c4404d0ba04d89444502448050322800da0800e0f0000075406807590b605118007084100021340920507454401414104200c02604e1041402064a900aa040000b882d00c485940006004603444800c94460103000301d40911a900940900603164040c2c181c001070320380000074000254956103010a20282c65691181003514610006084a0703842e0480040d004c0358000e0519061350180e60085202e2130b01c0b0186000f02e036020f81055201e90700c2c0c41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 515406519 1250 515405269 515405273
    0x1051305120f0702040216030206100501270e070e011e080727090b0319020a0b07050c04020c010b09010b04061b080903010905030a111c0f0905060d0c0905040603 71
    0x5030050403649441c0001d55140b50b1900024510711892901a41080c00043e1002005403070306061050f8a010f682a640d251325885248002c81c0720a128a5000658109901180080914072000c101070480e00b084000c56541c1040c9408003c00c5400501184900204880c1c13560070080c03c6a03801c0003808118003000311070a020308100009003002080003040341501c0380c403c8203051244621100c00400300e031850f030384400440281181882a40c000e00540081c0d010113907058000341d018582c0100fd00c5151801d0990441c0d190f00286420b5446100b0703100d800d007243c1c541d44002e08030340d91504000b1614050440a000c2035500c180e00481a02c0000c00041005540c007500d101d120750500304541c40344c1041c80c10103840340d0151300307002581540307000620000c001000004100780540e54854000341c00c0044501c2d5210109003103100b2604541444150505118542c81000c03196103081035801c0640319004603280750058400c6802c00c595880300800b4241e0801d02540c000c0c1412501485824116 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 515407769 1250 515406519 515406523
    0x32416090611010624030e0f03040b070f020a0f06020f0d02280203070b0705070b03040f0f1407031211011a010507020102101401030c140901290d0501060201051305 72
    0x1803041e0001c12103800100d4200980a4101d5030061013039400742080e0380303214450200314089034954500072a14019410041c80c1000c50550040c82c4598051400d062620810300e00711390107484100c032011160b00b90040169940d54044004d048002886000c0e10f00b4410003038507101c0e1300f88046150b581301b18640405142d002840c040e261080c45040601803000600d0390701c0000806400039454018408042940a00c25001e420014000e0301250566640d03030030020482d11042c3d6000d00300d130124150b03200101d407825164417100e40c40b42c1e600e6207426007413050960038854590012035020340381a14441410303900100006114004400030404e814405044202c455480c1001074144080818000d066a00910030854081790940d0b05100408031b103018201e0450090000300d42407030580380041064800115030107004c10018040002070b1b402d0200318998407005500300c51a82c0c1c0b40091001d03075444d2210151002040c50074003c45c640d41440c0001e0300795135004003a00320500030700e16031a000c5140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 515409019 1250 515407769 515407787
    0x41802010e0102031b01050a0b0604030f0803041401090311010c02011a040e150a060504050c04050d06050a06090e06010f0e070c033b040c030b030d120902032416 71
    0x20908001c03481da5203800041c0d0441c002c0c0c602d94071003140c502c1c114440041c4190031a61061101d4441040340081075820000540035a000203001481e54000080010f0319035002160064060040d580c4000c0c081142075007945c1c0d44440480019040070394a841d200001d000e8140e0300002400284a40303007800d51144989000d00703088a21454031070000e001c206009002050040242090403440d500d40b4425141c058a5288607107070145280c2400501c071504088142c1d400e480c0000d1441c01c4603d100d80318203014040c041c00c900c8823145c1d10600010902c0b5184942d240c1d4044280103000158036080a808000c4040c3d84201441d407407500401c02d070650f00442e8030303003800d0b41030070404480030030082d0800c0c0c41981c0078100003a0300460701d4041c0c5060f00040e07420740845403c85d018010004070740700c21010758947e02829501035101e02225101c03140a15440500421070305000a206001900081d00d4909010009440e42c0101d11002c00c03d07980b02003204d0360190000e480c0c8a0128401c480c014080c8030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 515410269 1250 515409019 515409023
    0x801020a121b081512250509010320090a0605090c0a020a0b0a06081e0c030f10091a040605061005090f09071e03020d0e1501030204020307050f1303110418 68
    0xc3d410001444d24043c40c1103e0319030190240c0300320f142080a4990582c3c038503003050b0740905107503201203078200070344107440807800d0f2100a03112410603440c41d5100d071458a03e18841140162217508610304984034451502d01c80c50f141c44010494a1400c020b0040041000e420191024001c0004894003500003c1210029920180d44040b130340e074451000001b081182c20860f00c602074000700350349540c01d03861100400040722080ea428015904209640e0f08007022005409810080303401c03202c0013495200141e0710707002e1000380a0942c500c0809440d50704c81281d08440740d07070396001400100e0403c162102102016424121706c4c00c1d1200b40010006004803008600c0750b8245d078001007101d840b0309141a0210516003480442088007900503000c0e400c03c1354615505480d142608c0020407001400c0003640103489180104c69003141c003800081d61009208009000c1e080140d40c60282542c8000c1c94003a1001150021aa007986000003c855082c22014030803030400b54222003130700c10f1a08546410b5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 515411519 1250 515410269 515410277
    0xc03010504180206070f0c1215051e04020111010b0604030609030809150109150504090c0314070612020c011d0601080c0f10030b01110f070302091e070507020f04060801020a121b 78
    0x402c0d140b51009205a075500b00d239091107040c09428040000c00e180c02c0341400c001900034402a681d0302d1102c507084601098042007003420001003400740d4060355580c90751154880c00410a501074034040b0b21580e00c2030f4422298180c4da052100309040d40000010341282c441c40c058501075110307110320764501006002c0c480e821641c0e40c060741d1403041d00010000080070003034018441c0c030305135081c05107001550344000c0c0d805e0340c3c5078404800d40f46070206100041e0341140d00e43d1410103041c0c00000000b90002040e9154030f41d605d035940d00001c202074040d10903005080004000540c10300840318140310091100600400100078070355040d0340c40f14220503040b240c2e03180001c1c200c01446c004032480c288141c0711109501401201c165003200110301e2000b66402a0350030403041c0c640402600c00403160074080c1601c48000008611403500c80d50007000464002400c08100700c16000000d0708803900d42c0c0c0036407981ea600188568003250840740503840d490a0810030021020301c1e2403031803484920f05103010100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 515412769 1250 515411519 515411543
    0x6050c031018090c06080f060402041206050a06032316060e04150e0901061403060408040e0903070b0124140405040b12010e0601050118030c051210050c0301050418020607 75
    0x800b401d5401031121035002009507581540d80c0c08040e18036041a5004d20304484000e0000300c4c1400e1178003c4404840600301c40b40815069519079000409000c3d1850f13803465100d075000070108140d10010718020b04080c500c20150080442c04500e41007003080c11900900030942d04001c9a03030044a40f00e2039800a0b00c02244040c50070b40c0340040e101d055001855016949014031020140c150b1080c01520b004040314074550400104040e6500c10850300141480d00c100018040403800c0340e5500c0d00820108102c03410566640d4035201401401d13000103610000413440d501d4091401403600e603185105044c220114010312003805400d105900881c1d0180303032500090541a26080d914038400425580200103595003800c8007611010284516800640184000d180240c480480c0500b01e079401825200c401e071600c1c05000c04d04806410009181c06018203a0a04127258040c0700d1003104211b403216600c0d8100b004100440b1640c0d02a1480c1000e080551401601e4401c1103c00e00394000914a0b0a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 515414019 1250 515412769 515412809
    0x8040b0c0339150a0b0319050a030f05030402090a1a040204090c0f090b0a080a090203100903021908030c0c0a0213090309090e0a110a0f06090306050c0310 68
    0xe980b00382891000d2080b02c142040000740d1074215212070081e01d0240c00001040e1400c4000c0d603901c403803419240b4a4900c10040380301e003441540082500c00c4040c003903035801d01c64a40103160381c6003c120700b502d00c1d82102e0406070805a10081c54140c40701c4c1400d01c1c50440c10180c0116030310b05401840c0580301c40c0da4144c0b059040b61003420450000b00005c00655403030741c4a201c0c0c0d101a02101c65500b000c81d082a0384042100d0050010740d042c1c590340800039081c00c003107603000c41d0360b003001130002460656520004005138400f484085540d0358007980c04112883c941c6002441d042c07851004150802c3c48040c400c00040c07100381100d41011026488079180c00e101407000c2c1c1050055400254003007110091600100690b403c940c0d00c0070b0090b1181d2000c25981d110050075201285002e0480b60003c82030540000d50544840340070f004081c0c21809a1501c8110315000c82e81c0b560000008160390520800800c1600c1c000c0a40c80800d900a42d41036017880703c0d090300202d101d40921001002500b0741012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 515415269 1250 515414019 515414023
    0x50a030309061116060609050603030a03110913050f0a0b06071b15080f0105031207020904030c0c060309060e01020901021f0906110d0c0908030306060c01020702090c190201050408040b0c 82
    0x44106030040050303a2984144c07010100d40c04040000c0314454140709000800a8451007082d2065801030061454161400740840c02011008100310700401d0900141c1101d865048980c20241d89014000985081500030492140802007640644a00301510300e0820340f0b603a41038651103940700130595200d9000800c0380150740204c1c0c03c8034121079890701209140540c0403c105004064070700c2021502c0c0d03240c506064076804000303821400c0c0b041c10003d0400604180401070f03070190213407804890015940ea64400090250380c0105c000988442291082c030000b449055009507408000b1448c0c444a1000030f52508854007243d40d00c540e00101d807020100b01500b21081c00c4c1d5003c0c008100754010011042c0340d0350803508408406901e03002c46084018000e12414090302c6485004608664a840c100840381e48555881d200554081c808240141c481201c8103000d12101a026a01e032600b951905040d404009551011681407900f4880032811050499040d1581902c1c415a20003604010354 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 515416519 1250 515415269 515415281
    0x7050405100201020c0604060605090903040f060819090302073303050c1306020d0905032a030a0b040b041e08040605032518150206160207030f1a07080103050a03030906 74
    0x1030b119000c0c6c5820042005a00d602071000e9510441f440031a5403107039944c941c2d680c01180581e2902010050f0b05101c4140984126540801c0b806204d480402500c040c0105544d9410002c80241c0d108100034040d020082c3c40e11404024100d40000312059031003030131100d0049c0f20421030141070382d510200301a91410021242075003401c0c1b4a076411190386920003551400c0640c201400100d070250003040030301d800b040078005650800440740081075903405501601c4d0300b00c03461940c103100e072182038000200d06c490070510841c01035079000001e281a0500c1c014ac031480070100e403c828030854582002814ad041941e09031401480c19135260f40d01c8207900f080c80240c00d1044800c407080e2000c0f0011055000e00b260101c007410607040740d022a83c2d5101d031481a50a440510090f070040d40000c0e10300071130814440034810755841115006940c0e40c0314664944c0745042d09030790034400020728031406000303541460380202541c600703400c2c03542c07440c0c4869440380d07c2c601008040645480c0c1d40c0c01407054680100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 515417769 1250 515416519 515416537
    0x50907170721080307030e0319031506020a120f0e1201020306030c011107170319020f0d14070602070606210c050d08030105130e1b040f050705040510020102 69
    0x18000000e090380d40d09035141c5051160507101030342000403242d51a0440b10245505a02441c0b850854507800c80c254003400c50108018098031086c8240301070840c1364498460104510b407400245081101d00c011561802d40c5c11450035035000381c544100142007000c4e88601800c06160203c80c01d954100d0032524070080c45c40480e40821515803040d5149010b42c000c40c0102c208030308981d81440c1c008019115045000248049130300f1150b4100035403a200040d400007a00c440058900d09840f450400304000304080740380c0016800100c0c500711a4408001c0860b462011341400300ba0301c081025030301c510b8850044014038980d0003080205c10800c4a410100c00f0f401403d545c034800c048481c6840043d0b040c0382405a40141ca1900c0c005a642840b907c80c420a40d0003c10f10741c5141c0c00c200c01c2c0130802100c890000c2e1219a1480b1b507800c02032051007405060032012203150342e100144030030402030700d4040440404661605c41400101d580080c2102c0450700d0070303604c01000c41c41f040c6007a0f00a0040d500b80e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 515419019 1250 515417769 515417789
    0x9010605030919110f09011401030e010e01060801050f0a09080301090b01030207020414061e1011070317070309060f080610050d090605160c080324030a0b071e12050907 74
    0x3004082001c81c0015208481c01503c4004100f1015000c02110a03800c3c401c007018076010b2042008d01d0b5201b500120890119000040703820b400c40d00d0500c0c01c4a803540e01c40e04081e55542c0600c00c0340890a02030719006184e00d0402c0c4149980343e29841e9643c8070620600c1e4046941d804091210790003601a64080c5800038810080000d42c050052080002280c1d03840c0b16034041c1c1c3d201e1103400f00c1a1048405541e024015610403040c1040513035042001420040b9113102e142c000100140e003056449003000242001399444075100d1038044e1170068190029070500c261200c0000130b040e40302e1843c42e0300510442d5161004031900006407014824000c5448080f81401051000e00000d60881070007000e800146040c00e401d00c07042142d1000f0042c00c001c00000b000c00125444038006024101c1c0740c02010304030004045000c0000b45400140f1004445008208041101050b044200c02c000b8182e6180340300c00e4090700c624024200c1003600c07002c24800e941e52011840c0c218041118001500c56030403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 515420269 1250 515419019 515419063
    0x8070305100e04061a0105130312050412030c120f0815041e020301050a0506040b040612020d09030c030f260c0d0c05280905040905011b0e011b02090106050309 70
    0x10480081c1c2054404422aa008800d1719215948594103c800100c21280b2200c10f990550351f4100d0490640384405040242c24480459240c3d0b524142d11706407842070f2034481d511076003803900881c58600c82103c401440032070304901030840c0c6c000c0300207a8420145044030b00309191100c0020000c0c103c0200ba82038071b95050400c0070140e003040c0c2c0118140c50049905070035140c1c2c0d039410803074540301d113000e900000c000c2844100310141c050003030821903420382c040c00350802c11500e4014088039004d4805030006034034800000241070300180031740d050700d01d00c0c40c1040c2c2c407240460034029003a4654103114600290100090380b501c60842c11f4600f402da22590520990700603860040842e0002c6543c1c02a17520b001c02c00400040c5203501e071006122594171003502c00752902c4100001000380d810b060701c195480b07480e525072040d42461108000c09442d12501510440f000004180d00040c501e03446211800e121030078053f0790b1f11400c450442d200b5203450741d034980d50441070034100f4100c1940c204040820403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 515421519 1250 515420269 515420273
    0xe070c0804290708190507170403031220071131060e04060b0f101d0411031f1505044707080318061608070305100e04 52
    0x2c4901c0351152001c5880569100c00103a0540300c2c82900380080c648601080b418181c8160340001106000306030603c0c600f0329103103403195001d444a08100084442d4006001d004050b0001c038403080ea0b40741c0f410204200045c0d41da1025588006123107a52200c00d020981a0820060310710140c540301000e032520003078400888c089064800082c4030031004200110b030b0190799004178810170040300c1d6034515440340c50300c60ba11204020410703090300e9900702e01071380300002d02601e8116018586010540e41d031904075a01440c0d8092100b03600442c5880740b403c0410742020049100243d03500700313828150f1914005203110203400498410b82c40000d030f010010f03c0c3c8404481e0440c2c080c4c82159540310480450300c0030300c0c0398a0040d8902a80718a40544120102034400680b10021050a401c1c02c038040c1c50203106031650f40b840d810450764a006106920080151100300344074240d000302c100302040085030084a0003401380c00b80240808101541c03500012981402c0c10300c3c9400078181800146140e003414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 515422769 1250 515421519 515421539
    0x90607080a020c060a021f06090c270806150604080703050c030c271906082b09031410020c0303040c0806060618040b0307081f0204050a0e070c0804 65
    0x1c01d81040503004900401c0c005080c20001c846000d05180d001c0d001d03445c03032280e04125001c0d000810070002c690f030301c00105140c000d0b071140440d4140144c81d00512002e910b081e42c4040f080c0b050b00e600303d10700500800c1000000009086801c01c0940300740d241c0650b0080b010401501807a03008a110740301d250000020300c500407c160f5a090700a030b0958942e03ca0381418080c02c0000050f0240420300c04440c0754158808407088a1b4000200300640954442d031a01d9030019551280c1080e8000d4125010110601d940d0180450f868090441d00c0c0701442c0c1c03070707400142040499210207843c8c0c0340c0c11072040b0303c040418800034410210900d021511520022181070380c907082101c04a441c0c0c10401b90100c0e062000041c110310602c0014182490301740901c1490034203800b0840600e41040d150441c10405981c280115000780c10360000400118500008168540034800030880c2c0080c81008244401c2e00e40380d1100041d03480e0304114030216111500308540313103200c0c0702c03014216420204010510840c0d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 515424019 1250 515422769 515422777
    0x4050a0b042303030c07030e03010e061005030714010c08070302120a0e031b0906060711060d05100b040f030b0c0702131a18070f020a21080c0c0601090f0209060708 72
    0x4a1810300c0800e00714244400d9803848285d070100f500704414401000024440c8803241e6a00ca4040c002045071310361400c2c40c614141003035510b00380b00001c1580c22311040c1410440000208034130061342084580140c0041c2000c0b034202ca01030f11101c0009008803d0500070440c814500d602d114103035564070840031000304510451a00750f8800c0c00350440386543e01c0f5489a215408100041191485403100e004100e040d600c410300c200c0b51003d80512515090703a41d10080c000d250140c81d400b15252400580103004160305811400c4c02d1081440b0902113601d603000da0307000340d80c3e10142001c0c0a4035280d00e5904a40901c140095002c006402142c80d82407994000b40d0314045420740e4500280e0085d000c00c040000e0140f980d01c0c9840d40b0380009036000f440b581000743c6d9291309005a0300e00341c5860319209540400e645a1500c1c100307a20000d5001c20b50302c00d8116610181d1628605c7c01e02403020081c03511a5010702c40d403805142c40340062064441c1d1075040391104540140f44550701c5001d440c0003601600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 515425269 1250 515424019 515424053
    0x7050103060603090510020c0f06130201090e01060807052104050703030306050406030b15180906090c09061e0a082a09011d04080909090f0705101704050a0b04 70
    0x1c2890000903515000e4090f4a0190784e01c00054000e071801540e0450094101c1c40d4111240c3c4074054400ca5400001d0003002d01441c9a410030b045100c003c4c0c0005048061b20b5030020442e9441a401008602c0c2c0c080d13642500300c2007038a059a0f40707a004145020320380303d0110b01070040942d11414082003101c00104581268481c0c0c40a00909650382c0c2044102c0c0c15603c805080034501c41d00040100b002034034640b050b100000c02d29803448240d180035410303c5408540f030b0000303a031011082c0881500100031124800000711010b15031850305402051020800005403000040642d501410719656802c5940240c05064102e074500805100c155256107500350024440d40060840301c0564180059001e0507202200e0208425011108004241c110b00500030303110644181305000c002e40d26040c0407070140ca4020002d040c000d40f18103000341050702c0303035020300e11078401c0004a0751450307041042d07100c0117085c2c0c40a4060b140c1c0e55041c10360515441020003441ea5842008110400c101c41c84001b40c080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 515426519 1250 515425269 515425271
    0x41a031605040501020a0615090908030a1107030e0405070314091b0f0d020d0309210b0f09061f03051e07080c092e06020102031e0f06191707050103 65
    0x1100ca4201900c091040340591401a045001d0181c0404d2850b0444481e0b4218090000c190640c0c8032045030403110406c0007145c0d10b090000c14403030414440d000702d6030f01400c855011440c060103590090710309001c1118250246489400040505000754086001150003001401c4a894400040f0340c90791100c3c0880000342c544503000448a0420303501c842c8150b400900512800031841d020040c40101e84d141c12010090390400210704000302031120406140281c241a07054000f614218400310710040554441c40704c13510402003810000a0f009030030161a001400c5080c811100044003120190000b0f0310900c0f500704901c04400c0c0315541c04010002c1081654556600e03007803240c1d140c0d25014240d41d0b20158420116201c940b60743d0000c00c0071140341000c0c00c001c420380000610345e401d582d4000009030b5804020080740c0e80200101c1d04070003014010500441c0380c1881e0f2841c0141303020701150300070b01c404400c40400c0e40031105240050060903403c14050040a640141c0c3d896190040a00007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 515427769 1250 515426519 515426551
    0xa0203060a0f0c0e09011716031104050601030207020a03080a0201181a0c0304030c03080711011a03070f05091b070206120108210d0b01090506040303030911061c0c05041a03 76
    0x1e60f10414015200160040902011b6480c1c140c06000041d007280d0a80c0c114000d0305096074881510103640b0740154032890000844205040412049641c018812814075004118000050f5651030260090300e602c11500350301c640da1540224010404045060110112084c0200c03d0000d404c030100035108038116151001e0317454042c651007501041c2d85c0200031409a010b0000041d000e985020340c000014541b100601481c030084070309558003481003c460507007a4041c6001ea050074001c00000d0094141001105407030103011685240004040003d07a103e10300d65080c000350b855049070101c0b90001d00280d2201507112400380d84001c20311990000d0f01c0764032004044c0c440c1c01c802180300d003090064080d042003915030409001c2c00c10200c01038100900e980d0040303016039610b005800694000c1d540001d0700d550724684960328201e240046441041d0502031407081c20006250315245060640c80850380d100403a600f42ca00740910380001624102144c507045071141810040c5100d080b441d5188210 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 515429019 1250 515427769 515427791
    0x714010f1a0901081f0b010c0b040303020d0c090602030a1b0c1d01093c0e151312050f0d0c0807030c0c0b061504090c0201090201090605090307090902030a0203060a0f 73
    0x7442d0305c0495503030b07011208406940805842c56100d01c10000c4c060412040842c40c0344c2d501104040211001c40c046030340841c92114070072961252080c1460a030400744415414000040d54900032044c4240400c84030161021060103484540303c40c945c0d0169030102d0300da44951400008003196101c1c500850707405c0c00000b9407030b40305d1b004031185251074143d400d0024a10440070b40203c00100428420800a00401480410148a141890b01c0000301400907800040d680c00d1a0f03010151070310800c2d4045202d5000810307000032258810381c03400c0c03c1150f40c07440c1911401c03405014480c02d1103000e600e803031a070524482d04159020b00c07840d00396404128581c10041e060700c0b0800100c0005d0000980304001840d01d0034403440d648504c4860451440c10039680d0984c11007a1042c90707516800513515412080115608144800041c209a0070590704196025001c81d13503d0700584107124049407076005507019502c00703000018645401070241c6005142c5000005d0191061a0500540300e14001c0c248203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 515430269 1250 515429019 515429023
    0x803040614040e0c0702030a050a05030a02210d021e040e04030f05160b060d0501060906030b010509240d050d02210403050c060304113102030c0714010f1a090108 71
    0xc140d400c4403480f411192250911010382c1e0308800001c03078252143c14118804140204a40c0c030005103c0c0703009603520020340d50020f05044014002107006c4000c01e6918108500c46000c3d100004040a0016101d0b0185a00080f04800d1200315500b83e050000b00455000c200304070040c85a40a0780b1140583d0203003800c121860b114244a0100000c0d010182c8000103c0c84a450343d00040f00400c6190f2040c2d641d2541804c54102c0d03030110360780c0f5a44040c20003c024840015074010001156104003d140c107401002140c0d00344800d120200007070503900d421660b80c1071010110b142d04403040b02c51440d000d94001e03580b480e00800c542c2c04002194414103060400c84c04980990343d000e40035019000021040c0b001030740000d002110800164950b4007125144c18100d40050350321100f03020020204445002a8962116003a00045004208009000c4140360496035a43da01c800c00700521000030814900420114407413008640c101000c217424450800501c072540e400886401c0b02c1ca9980d8510300f0703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 515431519 1250 515430269 515430277
    0x60105060304210203090604080c040b03010b090703090201050403330b010507061a1c1a0106090303050d0e01050703060501170906040314121608090c01080624040803040614 76
    0x28502548600403e100c4490541151070301c80141c0126402c01038910000b4042c0c1d0415080b006040e8030280888220f8a0b01c0d006110304064241d00800400400b00041840c502c001007040e024103868050220441e4883c41c11030f0025034000781e20b000070302d1404c0030301a403492101d0388407a08841c0e607020032641c400d024400d0340c0c3c1c2100140c641301d1401e0065500c00c00076008400004014420b811000c1d142074031082d041800402100b80904094203030303894220107100d02c15006000d200c10030300060003029000030f000025640c0505110b41c841031201001030180200310388090055082c101800000f541681040c003c2c2e4800342c0b21002d00603000c16186072486811912032445601c243d0100e40843d00a603c0b03410340301e040c20300661816800440a0b400c0080554240c2d42c4410b646403140c0000b580040c5c400c2d00302400c100038200400341d030700008180d13010142c600f0307200e29403804150504040400035400740b07491070f44001c3d031542c2c2e81ea54003584942146c4903c0e00031401c01484007049140c103030211 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 515432769 1250 515431519 515431523
    0xa0503010509181c1808030c071a040308090d020d032a150c02031e040e13030c0201050d020403020a0b0a0906020f1015030515101703120a09081308060105060304 71
    0x100f071400c00e40a801c0c4c0401850300009018004e904001609104840c1006006801540c005580e43d2105101c801d2074130040c1e511445441d1110313404200c680740c100c01200c044a400c41d0201d80c0303512942d8006101c1508151009511a2208e40300000705600410703d0034a0480409813001c074800700c800c0c440280080b0740c1c0001c2c14000402100034231100c280c0d102075140d0f601d62040342d0500458242d6a411810310f00d40002000001113800c21221030001c0700242e024250803c0320b030500702a45e40c0131301103020031200241441008030b07620303036845226030588000f550010807021015640d00d102501c00c0e840703009400d000a520170404914203000042110000c201107000b8154284015501c42c0288100440304884021040002001c00c80c2044210320752110f441500010307082411049000306039580c001040c070103c030220480b0b441d8000c030689851a4448080c0842a500d001c1141c00030001c51000920307082c0041031508503446401a4001074034104011242c0990304d400c10403186020403a40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 515434019 1250 515432769 515432773
    0x702010503180304031b05091015080411040f02090f0f2110050f070e03010b0609040e0304080304060810050d0c1e170a0203060604061a0f0904020a050301050918 71
    0xc40c1580211002810021101005981c04c06407656a500340ba05203000011003c0c00c8035003000e00c03441c039111141c16000031030540b900d18841d140c0740c03681d5502e8940000341418000004001803e000800030042c4401030002d00070403a00303841801d07800c000c0d0450407088d0f004541d0401100200d00701820b04c2c1042a030018688090801205862440403481c7c119814082c0202030304148902c100d4000e1074080c4103010584d80b428501524000c241941260400d886681407194007481c0e40c071454219144a54241d5011482d07101d5110140d2851107143c0c0410750794440040c0009200b50700c2140d59000e03106d4991096403a503542c004120703e40800000142c002a010308040200c400881c1290601100340080320100c642d940c0004a06101c50000d10902d5420852044086103030a111480c1c0c0118100c0742008003509100c5aa60201700000152504070000524006449190019605042e4005101f9941c0d00c000d128024050740080c8030303c60041c800880440d42030160025621044941000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 515435269 1250 515434019 515434021
    0x6050319020a0908010e0708070902040305151815090c01020105010e0a1a090c0909011e0b280f020f0313050118030f030302070c0801090f150e0a08030f0c070c06030c030b04140a0b060702010503 85
    0xe043f0b0039180003610050356040c1c5032002a141400610000003404260320b4418a186040c0d141207050485a43c600c0741164034181c01444040604c4031104c0d080074a504000458020108421000850703e12800b03910038050350030824800111402421081410f60341c002e41a40d03a2121006034103c108180a41c002040c141800b0070582d030740141403c551355030449000c88001495200080048035802d400288501051820142d0100310440060300c8503c0210b02d80030604a000801076201c0c000c09040002e01c14203003650400c1c1558a00183da04022040c0c2155001d2501130020b5208402c1226501d90000c000503c08506114041010b41c0010203244680322a6654203854a01c0c400c0640465507189003400ea00700c400c011164516214509a540c1c0381016490301042000080208070030b40c1701000020000b482210b089821240c0350304010412130790a590030790140102c011030b1500189410584c944905507800c040303010302100c070010440d04110b002489078a128202001c1d011400402c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 515436519 1250 515435269 515435293
    0x61b040b04030615120c050312133609030f050301030b0f0c0c0a03110c090106020d121803020d0e0108070509130f141006050319020a0908010e0708070902040305 71
    0xe041389081d684143c8440a2aa441d10b4168100180c007490646500250764000c1c0114101004042c0c7c5035200f004c0c08d5800d002c07118850444000c2c00b4003c072040b4448021160100424200ca01070210140b0030010902020042c29400202840d00c3c0c20b030001485000303000001400340b4122070582c8e40210081c0d00542d5001036042c4050409014010081c0080200f0040100b0512140584a1095403480710002066100c14070702015018603900c0380114500401c807031074000915080e0440305051008022100c182c8403402064450030081c2d1407007605440d0750030182d000c540b4404450b0162034118842c45140d00458120504070b940b02e000c00c2c004c004020291030008800000050204400f151059a0301d00c0300050b600801c003110141d15005090201603005440b41c0c00240004d4549241549001c0464141100904041d0907100781d00280e8035036064070422001c030107484a1030080c4810201b202a8070b035103105c2440f03044414040d007400403841a00a00071201260342140c01401c8901d914 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 515437769 1250 515436519 515436521
    0x801050f0d020301020a05040f09050f04030f030b030d080103120f14130305070605070215030402090a1a1504140a1401030507020a0f1a060102010524030a02060705061b040b040306 79
    0x200d4030154000c2248406000580d030900050003400d60303d030f559075191481c241c1451510788054106140844c00c16041203030040305035408651068140c0b42c034036465504044150b00401a030003510b90140110400d1507080ca400c0401e00d4100c0e8031a2400b891052040300c4100c0b440608001c81c1c40001d240c115146401014040c060089200c449440040803603684e9070711407030301100343c2c0040d02240012620721b0561618202c054418462542261318629103513000890524004150705242a0f40c0d81c0400b4607001c000a005411aa000c0c0000b00c2062810a54801a810505c1a01e16120f0143da502105041c004140d1080315689600307010304c10000001503000c0c100040a02c2c1c118071031440741801180301102603104403801000c0e59034144102c03103100b80b0b02c2d05008152031b0640e814001881041070915020784840fa0151003026010581c0301c001134144000603501960086d408030306503090110120b01d0600900d85184420310065218118011a00a034424054403000c107110803c080f0381c00e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 515439019 1250 515437769 515437789
    0x1101021204080c1006120507050a060503010909080c0604030c060608010b150703030e0607170f07120506040605032406010e1e0105040510180f0b0f1b010c18050108010303080105 78
    0x492425540c010084c410f040c4104c1d40680e0003c031203180d020741c0076024000d044c064003025040584d0031107407150820702c000c3c0240c8410700c241140039584444003400d1203005020382c0c02c9020100140c3e10b4500305401d00401c2040b6010055510034a071060000b0315100501c111100800702402c040c101c40900c0307480842c00d802c1071005070185603c540a40280da0340911215100c0d00d266110b1b01d1085600511100c00410300030140c009000c08541030121081e007002222070100c55031040400d299503140d0108000d02116889213400d842941c1d803076008440a5201101c0041c400d0700d40884603518080111220680740058980245030034506e039261040540b209007039200b06060440c41d11b541c4001003801c00d4103452241c00000c860994451482040d00b031110028250810b10380503407030401e5000c101d644100c801c5045001d00015040c41203881f950044180d41c41c17110300810000000c98801351228000520302d00304051425404100356004a00d0705059a401d07585072030441e07003040148840310003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 515440269 1250 515439019 515439037
    0xb010e01081003050a0b01230918010b0406090b1215131a070c03020c0108040c2702031f080d091703310807050310021309020316110102120408 63
    0x4100d84001c80844c5040107103400700c521034442002c1c81d62500c0b07854803000c0f01c242074007481500c010005000070303607e11486640207050604529171a200640c42c03280180607680b13040c0e401901700380780042c0c1201c06500c84094000c055442c54411113840f00c2d035035100d69a200c1e00100c0254590040313051103180d01c4c00c07041220300c201885032000d6058031001d07100f07000865000002405601090301015414404542600c1080c28911040c0c2450b40d10030302c044e051809001208084030141411142c1c025400da04c4e003045001085549003804200341c5c000c1400003148038440c400b0700000081030000041c1302e02c0003854554071101414140782d8528411040001e06840a110902004046220b401c10080303000030340700440f2200120301c44d06030303010365400d034494101508101000c000c56140403904a690b42100c01e00140d5860740318a85d51840c0f649908a582d000744003100300241d40104240c1d4149088058440500c0300e00802c4085081c0e11070b6400b42082d000586010400151601e8007030800f8039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 515441519 1250 515440269 515440291
    0xb0a030206070f050f03030a0203060a17150a1d070501030b03150406050c0c1b040606020a031e0203131203080a02030411090a0209131e020a0519031506031a040b010e0108 75
    0x401034649851461f08140c908942c0c4950010520886107400c8200c3c5c170080044060521485440080440d02c5070500c803010046034140100044107030f40b1030360041e41c403a5040040903500c0380d01c0c160102ea07103100d40e004043c007007860300c0881481c81c42d0028182444500b40c3c071040c0401d50325503507070001030703e00a030025103420018001041001d10602c401810610002d114041d4004084100800e0710b0040d4006025900015986408694414002113103245680580340300c8080c800412840d502c6010501c0d501040c2c2c0140200d041c013041d8642c00c00b4503000740d949801c030740c6504104a040744400d45e0000e02c0034030001800320f86070800305203443c3d1260400b400181490312603000b103001c030480c4510341c2d03881c0d80e030360400300384203507084044005425940c80d021414044040f5000e4520302c00c020140f05601c0701116403071402e0f80b00f034100c4010301d02d0810008408580c1c40c0000760103000d0406809158000c0040031a000341454401ca81e06e0b840d050b581c4000b6461138a005445415010381500040c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 515442769 1250 515441519 515441533
    0x10050f18010605040906050604050606161e050d0c1a0c09010e040914030403060f09020a06081513020a081501050301120f080a08011d3105070b0406030b0a030206070f05 74
    0x1036486201c0c00c031740319000700400b0815240c190200821182d0041c040c9114440600c000710b1429090003001d641a54800a0f15000d0b03a4180c003840003030241010000d1261081d190f402c0d441507400340d50702c0c0d585445850288002e000b001c5102c1c09002040341c50392010902400301c500950310231000010820070240c40003c0004207911005903840540c0c0c480e42581d400003404004028052080501c01c0100b50000c00080b070f92507000884821540c0b04800400240d0801310341c0f8030145400e520400c41d00140480020341d02010700c10041c0d04003003c3c50010406c0f25000400c10760b501700107241800416903036545160300f401c40c42991420385c0d070420b554030010420300000003144000144841207003a118400709603d02990545201c0d03003141143c401501c03c5080c01042c486c00c284d040e084c04400102d40c0c04420341300c646500d200f20902405005889003080016020603000e000304152400c03964280042d40c521018002c882c856880000d4000710200400700100e15400210000a44101c0544400b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 515444019 1250 515442769 515442779
    0x6090a02120901021305010216050d03020f030a12060e06010807140706140f07090311060a0e03030a0e1f090b070c1d01090b0906010206070f0908010603050a020310050f180106 77
    0x1d0681c00300d80d0404160750004040b03c500c00c042c5c01040050500344018680721002c0c400d515800011441924060111744881e4010140244a0502070400c0d5804480e11141c0c0e83d24000c0c03080d03900d078001c075910301c1c070b00400410b48100114241d8401c0d00c0607101d00840743c0f5500b01c2201d0021051083c00035248007409000c00089050090315030840400c42400001d0502c071003010712001e0058405424080d034a038041000854090b0485001c4104689640e26001d01c04010b95030001d61101d0207506010002c1d807204841c0d0050340c1c3c44010542502c9102e2203021300032090150682c1090760f40c0100c1d549035000c02c41190014014052107101d8400f1340c02041d610440f603541100074000f4803802200b039400503c0003000c80e10505041d1102215250030304e0074a81e0010b500c640c0003501c0c20301000490141d041c5414080c500e600018180c0b41e000300074441c1d80e8100b1544500c1540800c81c400d00503020128a100f1860041501502031180498001d448006101080c41e0020303419580700e540303407100060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 515445269 1250 515444019 515444047
    0x3030f04060b0d080301030c050f0a031101141207031a0d060b130608060106020105060301020a050406050306041506030204030b090a111011060a050a0e01050c0a050f040308070f121706090a02 84
    0x3c6800d00c80c2d14101d032a5411490104a00c24a1b07410141c007075920b0009201c0342e60395030303000442140e412000d6841ca01c180c940040b100307041020080c18441c6800184035180e6035120404030321942d15654100001e403848403034061202c6655440030b80c8400c07404007031400715015901040130640020002c00d00050a0105c5000b80e901c10f0703000d0080e6030883c0004112154080c02203030b42c086d000310000c614050961501501a0043e409080b0030480c0110001d912901d60741c0c4010035044003032403d61042a81c500d00200a51301c240001c80342090000041040c003440003480b880069071040c6a440012298001e0001c2541c00c100848100102204100011181800308074000c10200b100800e1701c0c50712050500c2510900034140000f07a140804020400298000340d80e0709034076519040341e60351503003030f2480d456028541000d413000c0d4002900a081100c00c02c540c100c0140714201786818803c0d8480152a201c010704042c000500c1e540c0009000c910700742464030b511040208006080c10740e842c251b12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 515446519 1250 515445269 515445289
    0x91a12030901020708030901020d0e0f0d050607030b01050c1b181e0106020318090907090510030b09060c09090a0603050d0906120b06180607050a060b0a12030203030f04060b 76
    0x2810a4100041024065a052040310007400d0084010f600e0006542c0000703680301c1810340e0800820040c2c52252056559421010008200c000d014907a6200300d4180580c94082c1600e28201007480c1c00c0c4032035602d5002d84299122410301071b01500704020110003541d80c42001e9042c45604c1441e041e4200c400402c2028010b001d140b400111040103000c400306c1401c2c503001a0080790640d130013030007090304014406540c0c600c1410300761003201c016181c80441503e041060f41100180705d09203401c00405c00d0750380000c103040381d02401c030004031a1213803940607403180340550745817107080f804000104e960300304000d0068000000721800514203582e5141c184c02c080450941000240b00e0301d000b0050540d00035280308490a403840b040199000040000c3c401d4458104040c09103050308401f88401d90b074140075100a1504402600e4101840d40703001001403114010562080c02401000700e00c40104850030300b40143e154008503d19155044c07100f87e401002003003205c00030f40390340c01283e4a4450792812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 515447769 1250 515446519 515446549
    0x2060c010203010302010e060f0a2f15010603060303020a060216150515010e031b0612010f061101050609040809030a0c08010e0f0a03020705100306090c0908010e120301091a 76
    0x680b25419440014030104080d1000c610134041408186081c407440c000300c0d040c60f907403814251409150840654881a070300c1d00004a4041d02d4440400480d6011540c031040034410408400d035683c842d84154111001030002a0040e44010300c80e00018119500401c00100000e10710440407943c0d40e650124003240861380400c4588540c144681f001746058544024482420700110850814005c04e50b01c0c6030944e02d60340c0307880381d1040800c6940c440314100c40e09440450147d520755a106c40341d455451020f44603040000355038441003000c00310f040c4036081c09414001c007442d1141d2141e071615000c0b90800181183d00d40501600036000801d000032900c01402100004140340d40d1034230041d42840d5001ca01402540c000c0740c80b080c0041e0340802c50300c0544a003140c08242c5207032074600c124002c10300c2d034101c40304080ca4540001c41103034004507558201c2d50032100a000c0100e42c20381054a501000d40110031607101840184006100c680001d0285c004510386502640340550000c0d15107040d0041c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 515449019 1250 515447769 515447771
    0x30406030905060a0b1012090f060b0319032f010608070518010510031e060e0415140606090f0a120b060306010e04020f010e120d02160609031e02060c01 67
    0x2402040140610820383d001903041300c10010304112a0204c0e541003010800d94041080b0965058200c400700d900203003881c2d40100250341c1c0480c503840c1a400030602c0e070203114441d202d034076041c0748100015800b4030055a4195a1240148044015800200704c3c8401100322007102c0410814081800d10440000f072400b4001048510300e05003d0004a07a0803a10020f82e061501d00180020707165072240800044591400107001855407001e41040d801e0000440811428031030002040005815113900032070040c9130743d895030421040303658100d0340c2c840c104450040c0034000041c1c6d1803a1200c0035121210002c1c0003100024420000038055501d141c020900310019407401c1400d005d40d03a092158060002d400601c02541800081c5201c1728004200030311500449030300111591046020440c08080074224803804803202400350307224200070014000501c24600d050386642406661901120429100d684009085440d007440c0c1d40c04607000003502241c040760110040e12440700500b040b13025640 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 515450269 1250 515449019 515449031
    0x313060909020c030405090a06050a080c092410030e070915120206041206020910030c08070906210b101d0a0f0e100305030c160f1a0c010e03040603 65
    0x640641880140e42210201502c14403036541c003e04008111400e07240100c54817803081da6481302020240009801494020590341d00006a030000001d0040c0c00321000c88040c18a6a80c11404132003401c130817114060940c000c2c6a80080c3c90420080390107142529150129a000181e0321031807500d4000d61141c46550b1742c4042003860b55132074048113400f90081241010b400c40441d00020541d01071409810590310a50708001c042080b00e904a510718070001e001a05400309040020340109055030260002ca0b01d5440081c00c107034403818118040c2c0e520340e11400da03124011480d400c6142c01034070522403003d43d503540200c410b55030340b48020440302d0035a480c0b2000007aa100414071000c10b04140034064038492105101c1c2050347c4a0b41001d5a03500000320803183d0f41c18502266001e21940090501e010002d0f40b54041030b0b0101c4c0c211000810002d100c5950b56403640e0f041d60000c0c20748a002e0190910240801120b1010002081c0700d005c000700100b80b01f010715112605651080d4005404642d40d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 515451519 1250 515450269 515450279
    0x30c120f0e03031219090c26070509070f050d091110022a0105120f010f050a12320102031e0403020d0e010c08030103120201061a0702090601050c0313 66
    0x2440000385000194007550070040403008000c04c903240600800e1104c0c1aa8680000100305030340843c92843d00b00140010703842d6203c1e10a031410050f03403414441441110306c0c040e40c540700080c00004941c00540114040d41c1c420104442840124601004100c010890705104400c00c0c00b400041d1401a0594900381241300c0820030f04102a104200c25500f08100c01ca0015140303540c954007080a008071106a03101c1c040040711030f0710030510030071403e82c6c0850504c4420250b0b00600d5041e1642c000c008080130341c4030804c20080901c40c1c4a90b1880207103510844000410036144a20108510b0111110181c03405509902c528001400307907030303145c0d4040304109050f040c00310824010f03810444031030005c0c10710b51002500d5200c10441d00b03060103a44280f00070344d64456010401243e411805d85903c9585903d44409080525034001d0015800c01401040065804500908143c040000e4515080740c0b0790078800c82079801800d40d8140f0800307102070503c803c02030005119401d4a164003a6150b070403c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 515452769 1250 515451519 515451527
    0x190501110f060103110604170708010c0c02150c0a12030f181104110903010e1c17041202010b0d081b070f031b05040c02060406060902030c090409030c120f 68
    0x2204001095104840c1607031010008907402d0f064030f401032090480401400042a090311582c0e12600f00104845a074512442000c07440800351003c1000074400d051285000f180c3d80d10038201c0195000b074a080c8001c2c040f081b046c0050041e00000000d0702c828100702d4540120814003d01100c0100f52581d4124802d101180300390460052008040100c40e45562032380b001c2a0040441c442c0507568403641e8803e254180d01c02e844600c10010000c0c0002294192801d0b2500303c0c002c9519940d4039070007900e0174040c1c01075031031401c1820740b03a010f040c0b141d1b21501d0703601c88100032404c4042995652906440076407146010b4420490003103c1881c1c1d030310103000c0d02160350303000042001620b4101140a001c203520f0b40c801001244d4000c0c0c00800445032090310b4036250310865000992151500c00b000e014250041840e41c801c50155500f00210396517a026a000d034072045071288801002003107e0f851919284d031001d403602c2d00a14291050000d5556800e119900f05607c4901042006603681c09039544 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 515454019 1250 515452769 515452787
    0x60a0e06010b030c03100305010507020d090b040803030c0d0920102d030e030c0a140703030c08212809020906090c0706050a0204050a06020c030607050a0e190501 71
    0x59401080c0a625220500d04103000142c8054894030000020074031044003034902d4000b641d0410020061070600c010069625a2000000e4000c206041000200c0e4600e4606460444500340099403443d613446420504075800800391240b250740e140980804070b88000104406180540d82480401010101700300c0c00d100e41d00004410440d280310941e01c50380110a4001c606844021800303030110b82680183d0144c145e03046112928400803510000c440c600165102c0e495000e00c0d40b01e5803140c3c1e0722100540b034807001c2c003000d008240f60429800011300c02c0702c005c011911014071450540d514404002d40200c1e4280d6a1402e43e01c440d00e001600c0c5500340070900343c44c04a1500c10010310700e803503000c00c0f11408018800b034403d40761103000861030241e05003292101c9600c54420441850982032043c02508039000340f50042001d60b001055003400000c900c4125100200141265521101c040b129a44108010402c00080040284040d01d8200114081d0103001205078040c070b04180c00103014006d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 515455269 1250 515454019 515454041
    0x8010f060b0a140c1504060c0305130533070c05060105030102270a2c07170f0604020903070801060503010f050c040902030a1d01050610140a050313020a030302060a 72
    0x104001542e0307150b0300009962a80c2d41c24000e01516260000b60160a00000200000c0d164605070100420406254000080400603807802c10454443c524464440c810081e0b00a2881c1c0c061011080042200c0c0c0c05120800309225005e505860a81502e031442c0d501600c03850041000a030401003003140600601d409841300358003c5040003e10854411440c14a40c10000c41100c0155504c034142c0356000403001925000d20b1070580e1a01c0da920001c81d00703030408032401b035984103040491a000e01c210340014401c206a00340034040e89400074000305031440a17000b00d500a03030801400c03075242c07000d20130300c0001c025490000440503d800241400d4841492980c80080c1ca0501000355800896017541c00741d80c0755200041c1ca0b503481c8a03081d00104250f0200c46203d0104442010507007005410043c401c0030709480b01c2008800c411000e80b10703107503080b500c020809030034070801c2031301d600c0380c00a1680118000c9019240c61540d401082843d49540c1083e401a08820100a407400d00c1f4050031404003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 515456519 1250 515455269 515455289
    0x60203450a0611120c0f06010f2310031d0f01060317090114070305040515030103021002010515191d100f0e22050601080c041104050d12051308010f06 66
    0x240703c035410140c030313030004c242c80448000012844035051241003109200c0c1c05210300444065585920f098114070305c50b4480d582c00143c9100500303031201340e00c031003158019001809400c1010020b03041900a8400102d01205007100c55a02e404081c900304004d5410200b05000094420300314206882181c0c50903030f82d0340c080c6004000180301643e1002c0c0146074407070450410b9881c1c1005160850300e42c0701e00e81c00603074043c0c6503440400020a00310011412607201b100c00340e82034103000e482030b400c1c3c4500701c3d080501c41c0700c0302424981e40e083c141005413024058084920003280c5070124400481c4200103203481c0b0110034420003101d17a114100710005440c0a10001c13100707503e0300b071010465000040c0441d00206a110380d049840855007283c10600d0781c403a06940d81581c4074081e0701d44c2c4010346180644100e0900c0c1800c06010600001c403000d490001e0001d40c1d2100c2151640c507640c00307031000c0c3c0c07004014040000c0080c80890841c80006007040318008903461005d0545801070b00c0c09500514900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 515457769 1250 515456519 515456537
    0x201060503060f041703010803180301090c0e0c0c0a05060601030c080c0406031d0a030c05010c0903020906100c0b1501080a050c03190b06040e04150204060203450a06 73
    0x69030006880c43c1c1c000e6a080201c04560756525080000380c421000f44140c2200220001c550450048050b01d0003065041100c8042c152401c100341c05c1c0d4107a07481c041c144414000c01445100c00074640031742d2102000c0e214910700f8258a026518006140d50180c549801130b405001d020341c0d240c00b94078600074031441c1503009800c1000e00704985110714400c00c1c043c165681240c40c80b074409000301d00501d001b10401c3d00c01160203800c0c0680601200d40d021500d5504c0c002400b80480e020300c600c00d05494015003a180c1d1642c8030011311404900401b201000d00044000010000c2c224800c0c03a0b11031400ca22074122503003442c0c000035010070f6000c2c0c4031440150524040181503400041a241d0040342035502c0302029000f5103079440142140820320703070480c00c002004180042d1140f42c8a002e90321034100948040740309002001240118041c4800680080254904007041c00029002c82650300105441c0311030182e080040b0b030f403011600e040c00b9200417050701d1118074102c2c0825000f40780340d00340300d600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 515459019 1250 515457769 515457779
    0x7061e1e03021309020c0111271f0201091a10060513091b021002090f31020a09080c0901030b0c0d06030b0610020c0a050607080d053108070305160b0a0e0706020106 72
    0x9a455050b0b02c1e140c1031090124100d030707101c1400c000c124203682c841c20703407441c42b1060080c080c0410b1a01615001140e4100401c0602c10b043c1d864420404a20070b060b034541400e104803244e602c40c144a6045266100d00440c040d0072910445120b451502003408a030700903543c3c040e09000d00901030421240c07060040500b15114200ca00300811404c80f4129942c00e9000c400f40310340c0058485180300200d071354400f0700d03c3c03a0720b03a8000c2040c0241500c60300d5003940c4e01c4601c150348001103525180c22034030100041000494400005800418440c601c0e8140b016442d81d910440b842da5000b030b1069420b02080c0102c6060032000440000d6241c80606420654800071031550000c0c0e10486009030350020703500c400d00082800382c41c101c45d03071a00f0502040c00c060080a84000030f5200340e42030582e911464140c140e03401ca003000002136120380e0282c10225551000e8920390020220740030703003aa020044400260080004030710407214030000095603241030781c1e0b0500d4111207070004011b580c5805800c0c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 515460269 1250 515459019 515459047
    0x4020604140616060c02070b0309030406081008031303060b0603060a0b0901020c191d0f1909051c0305060303070507030204020705030c0d0207061e1e03021309020c0111 74
    0xe40d400c81c041001c0c01150103022910b94410980303407400310700200e19104100300c115040721281c031186901311203400d40c89441e4100300c0d06c03040c2c60748030070f9a1081104012803030003883c00951050024800c026466690b4001724115804068010703010000c9100500812980d84107110318440d042d51014214505a00800c8411405000d9500c0203800800c00100c00e0780b00b041800c40c0820040c0c0300c143c5250320445e080c0074815041c06400101045000a4941e80e4010032102d442100946000b04080d110b0100f01006442803201c0c00c0802c0d5140c03041400850400c10000c51034003110800002c40c018102e5006040300e0020300340511a4008000303100c0400c00010b041815a40c04a40040c0c0d101e04500e09285544500d282c9000075010341c11003001025000b0808008540450701c46034080071406560080245443c003285c408a01c0c03808075400d0303e1034110303e4012210103c0c1001490503c0400c4801c00740411a4862181ca940002c1d6000a01000780036810302d80000f1030200b410641e8502c4041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 515461519 1250 515460269 515460277
    0x51005072f090406110409150b0738150102121c15030c08030307030c020d0f0804060f02040b04050a0504051302090a021c05061908210d02041d0f040206 67
    0x107124402c2007000c1018403500f80d00c42d08021403030301c04d0103030365950f28900354014004110407141d00c4051104000b68410710b0700211814903500c85010390060391540b21254036440d8004244a441040c80b003040c0e01c0c0c01800b81c0c12801030316a1604010240d920000087c5040c12a5000c205220b0061028100e120250304055924040381c0c440443d41880340c01407503400c801c0940c005481002003100000e40248003000035400b5216a507810721010001c800107a076500110044003001a880c81c1225070358a1064168542140c0f02d0300001c03035958002480003050fa00a608010048880000c0c10050303403400b966190010300051b50188440e150102c0703903046403c200300d006030040c06a0800a840300d90030350b040341c3c100c04075800c0101040740419000703401018200c032118000c03c410002c1ea8801117003041c0f5a0115510303031000348600180c0c2581240c4064035a04901d0f0350354418001c4507200030880c0080d002030080303002c0c04041d91803000c00b42c54480d900a44500802e540500c184005610340004071 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 515462769 1250 515461519 515461613
    0x231501140c1903030507080a0920041d061806010b09010507020a12050d14130b090a09060e0603210301031b0b130e0a0b0d06050a0605100507 62
    0x12500e40010000e01810200242c5402c044032a504581d036003090b81681c0001e020f5413080d07070707254241e1f5550612001218600070020b0080c414403d440020100030303801800c010b80c80a4030100380707152060080080b41c000b01100c142c1c1078004400704200000c94402004120034824001e100d1545020704106040c80b0340c010a904021f00000c070401552a1044500c008180f0075a02001464041c18030a80b0380040654020020750510341048940c841d0381300fa254011114145586040e20b0071800002d00d902850605070000c40300c140008400c1d0302c9214000081080d4515910603280c01d81c205400c21000800498220040d141e6401d00084040b00340c074196030b071040601c4040c0302c10f1688540064000d5204116640000a81e660b0160202d2003070000c44405d0079800015440b031105442c1520b43d011280394211042e0007280c0c01007103003504040d420400c952400101c854980e000b040c0e07200e240b00c1c0740102140b000502d002c00c00241202c00c40704040c94141244480c4803800c01d0b0701920494400d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 515464019 1250 515462769 515462807
    0x11010e0d140c090109020d0b100f080601140f0306100302070b0c07050127060c08090307060b06210f060d0c0b0c07230111030306011b050f01231501 65
    0x107514040c40100a042c4482000608a80407980d59080c10400382d8450a400c940440c1008600707445418041d01400010303003152030706464480c45007070407500001c00400d02410421308000301e0b80240249e03801007055111904440380e8074500001400314400180700303a0010180304001d0300012840e240c81c4140c200c1d404e5031440d0b60f00c03500c9007080c5024000c3c1070b201c0500325080101048000c2441c0318201001e0384512000e000b010581241952208001c84808445030410440807000030251b603c008154000100f40508003901d01c0854462604501c0d22080c0e100109020b21440c00d500304019039218404980180043c61955501d0040c2070080c40f84d00c03000d100100c0c65a0400c0808e00100d0007804403042400c0074400d95005500b03400b40014112808100c0140c007141c00131501004880c03055030103071101c0300101e0344105a0030581080100c00e0320940174110314891034403401c0c040c5104000340a0110941c1080700d407a41503060001a02c2044221550418000701e40d03044801043c1c403081d4840 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 515465269 1250 515464019 515464043
    0x90f080c09152115010b0301050f040e060c2d0a0f120c0221040b180a1809060f1a2412071704081206010306120b0411010e0d 55
    0x1d420342d201a8103071201030303100c0001c0032010703c0f24110040d101000b000306002c858403a0f55400f180031041600703006448100b1410001405541005a2030f403458071405000014140800301400f810488252006140c0200010340c0e02c0c9005400038010032042c04801042010a01c4001541014441c44c0d82d2001808051518640018010440c002c010407c07140700780090340049034029200d68032401d04842041c0a6201070200b1440030050700c003512014104180340030b6007503101012901c0d51149041d4030032107218000c00e10b03610040e4054500769410300042191103040c64a40180c0d0082407840a003282340c42c0b01d1034010a108041c411462000343c1c0c0a1444010b5002ca600ca0b210917115010f00444c400141c0c5011210b1025a080c1b05403c0d5940302410f03c1c2100140e40e4403103400743c1300a4060030092000c0b40c0d030030740e407010307805c1e000740e41410002030b40c90340ea201c0350b4203a689440050340d80344003000800050002661348078070501c80920f0721b46801c2d0105070000d020090403003000b5004001c0c202c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 515466519 1250 515465269 515465281
    0xc020f0d0c0c090e070801270b0405010213090b13090201050d1a0a1d01050d0b07080c27030d0813140114090307050c01140703110a150606090f080c09 66
    0x10340c0d6440039000c062018803241380544031542c0c0d201c8580c45a4021076103040300c4050700300400c48148400c0c1d100400910700e903c10341e40342d1201040700a0300c02ea9a5560800c406c440c288085000c0c1e00051000381c20105200441c10200b0142c05110102100c00e5424801407000603130b40132003140c2d10304043c882e00040d1021076813258000d010340c901d0040d410900380480850000e210301d003030b5100c07401e2105000c40300341e896100f80203407030920040c02000c8991010224030364501840c0f0181d8420fa4a04206040414580450302e2003840061441940d200003108140f19040034419000c0c10070705800e101040d41410300341142108403412000c0e01c01d00401d000030045800a40041c4c241c1c071500401c4484d1030801e142a147c0725800300c482210540f068440e885802d5018014460000c6007070200a410200039480c01c0d500880262000b2589000c0c6800780000901c5015808100000400e0700081c400c7c10b0220240050b0300f01d80142200401c3ea040800001400140b820545401680e41c403685850302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 515467625 1106 515466519 515466533
    0xf1709040609020c0d0c05010e072d0803190e0301020a050301051912080c0a0b0103081306020c030a06420e040b0106030b03030c01090c05040c020f0d0c 67
    0x516242c5c14000d0040c195651014000e03c000308070042a14103050074941d46401400400c0380c4242080c4070125071950f48104060f540391800e01072810200055505e00500048003030303102d200c0c02142452441000c0301058035201a000355201c0740011009802a0003d00569005021504010680b02035818241c001c5442c0c1c0d000d00b09009540782c0f90381c0344030f42c055003c400c403500c138400e040350001e41c81100541c000c4d80030382c0551b920740300d580b19200d459246541c05031003103503c007550007005944c2c0810002c0107a50310000000d21201c03021066801c4118882035581d54010344c1102694518420920000c118204c1e24682001034841208408849059602a10090390100140184c40c0264892222000010102da080809280d101801c0d20040c540c06c40c0c07145030010003080182401c0c000c40d0300c41c0ba828000b0703000480c2d01a1119954011448a6504101141c02c2e030304140005 = true := by decide +kernel

theorem cover : BRFrame.Cov 515287769 515467625 := by
  have h0 := BRFrame.cov_init 515287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 515287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 515287769 ≤ n) (h2 : n < 515467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
