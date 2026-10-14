-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0694
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:11:39.567636+00:00
-- url     : https://prove2.me/submissions/db7f4666-bb4f-407c-b65e-e71a6a83e67d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 124640287 ≤ n < 124820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 124641537 1250 124640287 124640291
    0xe0105040201030b0901051003020c01020d0e0a170909040b0603010b1903020909030f09150f040b04030320191a01030308040201200a02010f020a1b1d041101082206 72
    0x1210955a2600401003128010381d03000c03455514000200e048e40260080032010150301140c0340035810001e40446055400c0b2100500c035502d241c40319140c85240245007220102804819024121814029540c10300341c01041411250f5694a64140088000780030340d506540c0c4401000307090341d03104447d511000300300c01c07079903521411441480a40003010388000a154800d204c108041d840c2034080b40c500c01c0c010342c1c01540c3d00c006402401e01d540907030700403d11000400324000c80e101d0507080141c012207020b42e440090303205141c039410542114000601d0943d4000d4804000242c00b1100841d5485100b11915040340c0f001c0c88001000f0507003a00101c001070b501606100556900080100711008030035a264010204542c0203665070744901d50080c181311256003a403a6441c007d0085034505074105035480300802d0200a0340704411041e01980885032201880b550700700045507162403003607600a0150043d18041d030300540700260b0080107002c110b142000f00d030901070720150207011500d20841c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 124642787 1250 124641537 124641541
    0x3011806020918040c12050a0804150305181528090201031d061603060e100303020106090b15090a0f030b070306091b032021130b1909060e0105 63
    0x10042d60394507030044000b200c0e40d40d030140300c01708882c86800021542880300240301e021041c6040b41c00d1541840e4003828607900450700064110394414044030004543e6000c000554610140225118132000c180180340c1c4036041c3d0140240d84e0409040e00080d040c01d08100e01e0500c11100b03003420044110360155583c5030019102156090b0103800e61001c10004007012005107030580707c3ea07a44006090418411022150501480c00b0742d00280203003140040c914031070310b4281281583c001b220f05c8100c3c015840c05400080c4840b60740704415082030300815041ea07040e03855003100000d400400074150b10500c050703000a04c50102c0340d4908011407285100c451145810103014049420316403102244c2130900c02903440d0a070300c2003a81c0300c8084c082c0c00c00052204201c00d401078994010170300425400c0001034800205100c0c029408014031140100c5c85196a45064218491542c914001c202d40c400c8004038080f20007480c6c000241049031140007071201c0c1d03280c982d0310a4885094400300c2d01d95417282 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 124644037 1250 124642787 124642789
    0x2040602010e01061220010e040204031a07022a13060e0f06090103020a05040e07090509031c110f0d090b04030815040509190201020a0c060203130f03050a0f02030118060209 76
    0x10100200356002e0005c014206a80710b000524811081c6015034031224030054050f030f030203450550601c00014000315103e075203c0c82c1c2001503a41c0d1b803c0c519800c0007602c00050340c046c400982e2100348200e0400c1501002004801000e02a10240c04281d008054030130815480105208075001064640c1e03480c001c0b4108012032240c0c520019004a000d01401d100600c00b50b254401d0600c100d4a050f0f50005505d940740c00018100305480d04113520060815083c012002800000f03021030711021884400038494160b00d08044400e81d400008100105014110402d41040302a0003102d9071517002148078034030b0b0b07520304996400454086000c11240f80a00c142900040c1442070044004c3e50704101a0804c184421f6850300da11200c100e030690038103030860071a40309000a4407107a0307003d0411401e694072048060f440c1d0f042510b164082614281000501da9550052703817048076001009458425031980b10702e001c265a4101c181d8041d900d600342c40007090b490000c252030060183d600140c43c0d9180e04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 124645287 1250 124644037 124644041
    0x50418061506110d0c03140c16140102010e0a0f0201120f1d0102120109051b03040b0702010b031207120e1903030f020a02130903170406050115050403231002040602010e01 75
    0x1124422242d102c0720a1100309608858178041442d0141084818021003007400e19043c030850803001041e000301520621258009003050003602e0020255140e40e00035a401242210a249944655276010070324060101d042c5980050001340103151502c0100000e850240540b82e8014000200d1981da8051004e51404024200d8100740c86500961800c9015440c5584500041c01960300059444000c03452074284c409503510404602d45005441c0e01c1c103401c002c032a54204481880140d400d00300c0d00b4181c1d1030049880407911900c26000d80c2080c03016219100c0e5a1048250001400b0424011488a946111504949840d42100e0110b040d0540c03600500b03400500d035030034044d50b001e2000f120040e41d1341641001c260170750305000585c451190a080741c0c0c0c403508205143e00e81442001384030034020142c001505a07800605005014840082c08841c0c03445244030203824003004100a06401c8010003142c46241421b40c11181e40640f85041c0b103003207900c03a5100704050b039540d1001112224082c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 124646537 1250 124645287 124645307
    0x4030b0105100f0f0f090503150609090d050313020307120807020301060e0907050402090d0206120a0606020304030206030612010b150703140702180703061a030f090109020a050418061506 82
    0x80d241a040401503c04060500074990340d500c4280800343c004c0506581c070500889008010040c00c0700d0300000e240526000b0442d00382c541ea40a21a0740f00081d680e81d90008403200d4041203a91141c0ca56680c2d00d480244000003080e0487e4036001d40c4d640010021140f11000d172410713020305805951070426104150840305a80d100b40386204000082020034100450504100c42e0141c3e0003581d1a114480051404000000003c3d4800310201d100f050741c503891503a071403040070542e03010000e4035151841a60740c0c0c05140720095001000b040042c015061206503030010f10301000c008a6021100c000141900310000c01c2d2081445020902001385603003c41d1202035404100c201c03616010b00c58002c03420301c234040011308505001100200d0b07940e604c40e6101c08000e0800880101c0003501c10b210207039082c1d00170b81d10440442c0300f80d40400c00ca58018031480300e1316a40202180c4445161406000c00362415455102c0800f001c82502008114113003d58800481e4564007060344a06040c4054801108 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 124647787 1250 124646537 124646569
    0x15060801091a070e030c01050c030c06070207030c12080304060209030a02031b04061d0402102109020f0906130506031509030c060c070c090f06080f010c270905040204090804030b0105 80
    0x80c0801131010303103002c103014108420a113826030761550001941c0c0c0c611b114009864a85120382d0040120701d5a0200704181582d200303c040c2a01c0742d54804290820b1004400f01400150701000480c0018200b580141155540a410b5600e075904640001e4117003403880c80c0c0340d55040703410400405140b419106070400351642000080d864070800d00700f907480c200c3c010310080c050802c0035400200c42d806809849002089444401060181110786030080c0c02d44c80803c900403903031024449218a882010302d88246000740400382041517181c442c101410016004607018000c2800001c080d2400f114414410184207004599450304240114a040c20040612081c48400e00020000a4045484408507001260041a644080d040200090840b03a00c542624070580402c401c010394103400c1401e101c00d5545503100405000790a0250300c03505140c1c00004c5040302c1c0d0090014681e030f544130710740190024000141c80c113810b0b40c0300001030307010b80c1060b200400c0c40f80c0100850329141d5041001944 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 124649037 1250 124647787 124647797
    0x52d100507060e0307120221040602060402130e031602030c060316050a02120d090317060303071509020901030f0c080114040b0402030f0105100f1703040315060801091a07 75
    0x20414005210340a04540200380a803500d14900003031000300107444046401c20324121803241041c401070342d036140501120040c40c0e00c0703c003202c1020302e040040c0ca045650301d4002d4034450b03840d40c2c00c010304980c880f01c4440540365100103210a18200b0030140190405040c5080c5901c00341d0300401d80341c5509090b07003510814041041004070510318551030aa031030603042482d00c411040c0c03070907400d0080d6240003550784400402e800b8503800450304684c5101c0c2c000e40b03900000e13000c05a442c0355051400c503011500740d4400c02c01c040001c5d428074000111041c03031303180c0010000e00c0d40c0d00180c41014280d00984600d02168004424042d903040da40d0000c1c0f006100030081416048001028a0401000903000d04c0b9480000b90035920140325116242c445030000b00311502e44480041e00010360390140c0f00422504410110f4445103100980c180014494019410180785589000b10341c0f003a5045164a035440b280b0015819a09000b50301f440b51180a00100d500c00482001c03406500090036801080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 124650287 1250 124649037 124649059
    0x50c0409050703030507060f0911040515030c100509030d030c1b0b04020f03150f10080708100b120d02062418130506010f080d0504060e0118052d 64
    0x510700040d1082201d40c103041564641d90700f42803d400422840d600c0824140c01c0072380e420200b00025104001243d03085a080050b0f480d18000c0035441c00e081244660544e20030b004400d290b00d00110320000300d00780b9140c43e40c0f4240074480441d0609940c1e41c09000802e031525994941c0300c4d009160110310300c10010103103003a945103894000800c00701400107401350724038a4031100203032420701200c034003022420002802402c1c2046404414002214566001912103602154401c000700e48503045038203c1d8010f202004c1d069000e81c3c0141860306900794441a1200c0980e03401d181807091540310010368020700002e282108000840b40505540e07050841c00110704110156617104d03441440540e148283d000b0b0f65a4a044900740c41082c00024142d4411140005401841c4d0580c02c42511640000d440d101c200c11030068400303000700d00551000c14601e1780800c0e42c1e035114070380042e922105580f220b010a561000450161140c0d1689045844a80314611a03c41e4800100c000403040071b80b5151901 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 124651537 1250 124650287 124650293
    0xb04031406070518040209090403110115081c30110a0512040303061d01080c04091a0c0702130509010b030309010f230f07030f020a02090f1e0c0403050c0409 69
    0x51041c09072010301101381d0b81c0401d095484035030544080800c080c02080d4141001d04019026004190345da40007923003014181505032030a0390000c02120550b0000b81411361110844a44000e142d021400411040341d000396030200324140d204100c0440c004c048140c41c0d280311815001e4541e402d0103004062010070880510300c2c2e024007102c0703400140e07841e40407003a1650701d0120050000d0764080301c0f40c05040c00c3c18801026586900a04070341c8445d04880c603e050b40818041601ca401d440a42401d0202142c0c54503100414601a0700c07911603e0141e280030480c0c2c0c0054101440340030a5aa050317612005c02c410303d10b00340300f500d6a09108400660610300c028000070401e0309059070340300c10400e0100820198107a200040b40c0300304203180c0e2240e15030000006142041c0c11421040e00002c840342180f003201d5001040f07110034240c001d84180041c0d5111000091000d50107821592210300c0d00041e02424620706000d64040c44c504410596210f00e5400d050f40703031120b1903117414866440c0c18007800c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 124652787 1250 124651537 124651547
    0x1503050115050306094b010f050d0f05010507050301150c081b12070506060310021314010e090106030b0a06020106350303161b020901050103020f0903070b0403140607 73
    0xc09103007111911003d40e605070702c04c0f990b56240c0356801c0f440c2c00440160100704051102c01c111761b1009541d00480341602001003410240b087c482e00f1003041d0081410b211380c0c10000494030449020305807010410f6038a681d41030131118211040c100061002c80180903210350402c58100c0d0313000b580380c080079035040703502c0c6c8002906c650000860420040c1c1d8810084d000c0038444c0c8016401402580f91300c84040742000f948030720f81254114441e014410b42e60350108802d1090f210098002c0401468103030800303a00b0403071107540480f0705060050301c0c84814050364814070402c1c0078042581c0c000c1703507501c0e0300d00c20700c003a06100303030001c0f415641410303818400001d481024420b810f03034020080610b0003a84100070500ca02c1c2c440210b4441c0000000c010310a0901d01c2c0761075068a207641c0b102c44210144501d62481c0c2c1c1071200003580034000344d0040185600c60b4024000d00d180c0e44644030310700050440000d141815030742c044460341101140400034000051501c0e401103044402410451818a8000308 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 124654037 1250 124652787 124652791
    0xc0603140a0209040929070801120b0a0204030f0609120e0f0f0a03050706030b13020a051206120102210f0601080c220902070c080f0c090c090303030115030501150503 73
    0x20040c0d0100f104501965a500300310f0b00300307411503601c2c00c03207020744101d0729890812154042d03801d103007100c041603955200b184c10038125250310b03031038010300001e40c0c1e215a01c03030002800f03840c00070b90280004000708174012084400f072442020b0010310407007a440d1112056000c203002e00c080c03240d21040c3d00700b1a1200240111010003c5840f030301485611000109410315607000501688500389000c500a42c06910420840701c2c05c0381d01780510a600b52000059206200c42500050414408911240c03c8891172076000382c1d0091088070344c2110207880608a8104c2810321444072086494201d101e41001c890035001501490303000882c2c5402000601442806016540c1034000020703040d1601c1c990b82c481c0d140a03860b01c0c00310300d186590740440901941050070251080d50b215000025294800650441c01a2014000c1c1880010201c10465050340060140044400800041400713a60078001035010308090503082103052a0380030300804803038058001c401c1d81c112103050088020782141c1525 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 124655287 1250 124654037 124654051
    0x1c0e0c0f0603100b1201080c0f0d080901032703180e0117010b1905010e030d140c07090207060203010f0902030903040b0f07120206010528050d02060f040e040c060314 73
    0x1d542c0e8803061000742d440076541d44042150391001c6a8030f0740c0e4503d0300126034100e8000b181203070030700c400c244104007540388081801c503400101d0000d8035000400b9580601341000050500081407400307440e601e041b0898001905942da60021051000c241d08844680025080001100000c80c00c05841d0508114103000b214200e00d0b412249881003902500b0421080310090240e44880f10000c4404000e00701034000c0c10702044c44010841c4d807500f0700092a5400070704aaa4503900318a03107030b042d80c80c16070124260603000d001c1d0310f10104480255000900e200ca10448005a4a601d0851f149042e61515045103200900401c18009902c5002090314180d8150550003540c1702d03000c0850b01c180344100c01c4010040c114004040a1150300402d10318102d94080c4c9402041c246071030100d0030100509400c00880c20700f115018825410300303091450b40c0c84d10240c80680f402c0a0b82c3c000ca105900642d2004c0e011104250400c820003191901000c010305080c10144136a000c000c5150319085801041c1d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 124656537 1250 124655287 124655299
    0xb03011409040f0611040306050105030118141920010212030c0d060e070915090f14010c0b0a050402010f03050c070212030d091506051503070503090309061c0e0c0f 72
    0x81014000c245940c94800341d03000d0020040c04540380d03c0e84461790847c0c84103485062400b0000179130f82c2018001c50610f0800e00c1440c8281800310b54640b030440c00f40c0c3c0c11100e03880c0f2074940d081002d000f280d042c040d6a2401031021586600c07203101a0383d0840c0740010a2030440d04800c8130722540c001c030101030381e40000058801da9225000700e01f0741002441142d00c54464800305506120078950007041a000b42c8000e8000303403022500082055801070b242c1d120b44010401080d404110f8071082d441245080343d4140741c00c114250a64480701300c03c500c1906e45c02040c03a41d076018070086682000c004c03640c0b00c02c2d03820248428030300b030004c403461030140e020041d0203111b101702030f42480e2005100b00c403810010318074100902041d9042c6068070048000744c507415240780c040041214a401d0310410306003001484020310b10b965245d0216091380000c2d09800342c0f8841807102019554404010306001c001406800d100400d080704c0368001e40ba207110036940302da000384042901644580100100707109040d180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 124657787 1250 124656537 124656541
    0xa030605150d080703080a0b03101112180c0901030b01090b030f0d0914040e0d050c0106030609150c03110301050f0d020303070303090b0109140f040f02150409060b03011409 76
    0x2040c04501620001c0c59400b1050310b004000700211200078141c2c0c2402030303070340940581c0ca0381210030442d010000c8450381640040d40c5080344640b244c01c000c0e1442e040103c024101132820840c500e4500c406d444d1030308480d1110b940c41d81160001c00107905d8250303003141c410900e545075841d078280744001030144c003e8807a190640d0443c903490802907202d0680e0f69801b00c034050200b9441c0101045507501031b50303480c5503406504116915160007562080c18210001c5c0188110142040d585644400f00242c015521118000049040c900c03035125254000e484110240104074241802c480c904480c1109040c83c100d180500581c1001c1600d0554900361500094150b1100010701d00d6030031814001e5042c03000081c0c0000b00355054121507442441023400b803000303903210b03001541a984031200c110100599200083c01c0d0000c6002100e8016024003004445a80c050f004a010510503078200e01c1507041c005020401d20502d445804010f00030405407034215410319030303007681410b11100810300c1000d82c040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 124659037 1250 124657787 124657801
    0x7120203210a0f110d0b010c12030605040c050703170702070f0b1810080f040807020301050a15050319021207180e0c01050307050d0c0e0d05010605090c090a030605 72
    0x4100e45071540015100402825030200410796460308031180c0c01e01c18104400115882258010000c1d10000141a10305124a018404004000100200b81040095926240825800d030601101c8111030380c1d02066a0f82042c05200070f23a007140d0035072070412000700640804240d21040220380e480c014189445951034010049161120b640c2000010002d04103001420420310001403038400400c4990000c0c0c010040d080240c43c40400b200325021404a0780022003039144001075513480381c0b140e203149080480750f40110b07084820842d000604e055451010181400c0314101000080400701c00600030b01500507101d240070300d00868000e01511070fa000b40c800402041c0302c500040d29104034280e80c00d100c0d0701d248001500b10013203849518000c0c0c2c20000b415502c51001c0300c0c030411242d160507203044c0301c5821040003000c2d00141c0c00c0402104003001d40185c0c0e551902004840d00650020035084e05000c104056070784003402010994800300021015904c50116410071290001d00024240d95442 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 124660287 1250 124659037 124659043
    0x2090f0408190e0a0b0408030a0503040501020d0c021f0c02030a14070501090507440a05060703020c0106050d03020604120314070c110915040f06090911030607080606071202 76
    0x2e0840d81031014900407290314aa00c03052800c1c004104582107110a5969249248140309034064082c8039002040b41d000b005000300c00135034000d1b1043d0001460701141002c0441250300d4800703600010b81200415034041c04401c0c0035806000145442045001001c08001c0d42d01d21030f6024010600480e4555520300c440e0039020381e441c0c5030b00301000f804001070a140250700c81d819030044421786110324041e100c0e10040107504060201450060070490b105c15054607410070070001c50b03160544501443d51001a200707008050040d44140c40240c1c0321542d03a0021825039026402180c011007500180c0400f080e0300084c1142c01a800c281001c03030013199050114003400036510000d00c0d1035a06018054066807092032141e040d8020000e0046601c1000e0410011840a0724070340c000c003802643d0075080380360a603c000543d08451100195803651041e401041d00c1105200743c072640050f01c400d1159040074092141d11010030301d484c001d5840e00800007415030007055006056a0114030f440b58500d8020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 124661537 1250 124660287 124660297
    0x40b010509030f010207031d0f01050904090c0b03090c040e07052103030c19020f07180e12090a050118090213170c04110c06010b220b030601080f010302090f0408 71
    0x902551a801031203e02d142c040c1d800240120009005035204a1410800d40581400d16000810480b203105428004640035040303030ba46680c1c01540c403910364002601c220701c0c0600a2020780c0b0550340360301c5c001c1d134000d0a00040e03500c040d00aa081c40c2a4044a12000c06c400040d520105c422031010942000100c035003200001b2270a006100000c03e1000c401c11103000f6044021001000100c43c80400342d00302d0319450034001c9220103a004140501100441a0242c5400018407100141d1100c504031898038041800043d007001e2007000444046038200080c10038064942030030b0000f10030243c101c82c10714401c414440d181c8810750200308001c801a101c038981c80144105024030400d9400c1c006000c1d1644584403503144514609425085400c800100741c07418a00e240005d0b1030325031f1030441c1c404c1442c2e004d550b1a0010400311000901d5512000710f13810085d1a1443d05551686008130001d003052101030200541200d03101300410040ea514010150300ca054039045200c651228a000d80e078a02071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 124662787 1250 124661537 124661539
    0x2071d07030b1017060402160611220801050901051003120513060305190b010e010e19120308070206060d080a0c0602031302040f0506012f0a060501090c02070b09040b010509 76
    0x442c403103c0c030219910a000d04580c800c07140c0701c0d003031903110141040100e00c200050745072104019500074002c41d40039400020703404440e100d507502d0001040c0d244126080f107000d07000c07a08030240b0300c10300800c036091140a500c04800c000810250510f0035110038041c4841c48001c0003003103440007002c50b29214209850b0001c1c1d0004008581503283c0001801070201111180050841070b0f0080b0701400f8079000707403905004180c6a807203a512641004440e1700206052140e00201c0200300000814008009000244640549005580000c1c50020146030300030701040c2c11980041d041c820142c4d40c05a5244101e640058039558801d489403064031400700300d00019181c1840482003141d420850080d0004030351088404124580c18a400c0c0c50440d0700c203aa1150025a4144504150aa0700340329203d0004440c8210083d0000c4004800e14142c0407100c1142c0054682d001040000c450b070080312080c0b404c03030015000c81c9003042d091380f400d4010645203c1c49035407284490a41a4010401c840d04040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 124664037 1250 124662787 124662799
    0xf060f05091e0c0c0d030501060e0f0418060504140d020c041a040903050d0b2b02060c0f0304090c110d051309110406020d11030a030902010314040b06090702071d07030b 74
    0x143c2043c081520b0303040340940200301d01030112403111051003441208c1c1070b100107448205181c48d181090118888981e0030741c0d50004c0d07884000d80c84c2004500c102d511031b640715400129561800d0b14204061105903185010b00d1ba00c03045c070301d5101d140c000c902581c1e0110180e60001c2e00c8048203544101030ba40480c0890703001490810400c09042d8003034000c14001c00b00c1101807050645d4031080c440c040380c10240c046c001e03104102c034002201100409107600c103400200428140b031844450300d410403240c20522100c0780d00c0000c080190f002c981c01420380d801560f08110259018011042d078440c0040d603843d404010300002c1c030501da65410768440f400b4041c48002003111460300c040c0e002131030380140292005445206403483c5a14413481e0303402c182426107070256081501c0058150040c180c480c00403814592a8800c0c411405440a0604d00c82c50084443c45101c3c00c054041c010340c050081c04102c21500300c5842802000841c00405200c141e800701c002c8601c1d40e070318100b01e0041c0b03c10322480f58008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 124665287 1250 124664037 124664041
    0xd0204140105090702030c060a02070c050a09270201020a0b1f06020a061a030304060305090a080c030901110f03121003081b0705010f08040201180521010f060f05091e 73
    0x440c030640820305966094449a54948400c007050b41d0b00c1c0591071900c100707548200700041c1540b09603009464118072907000c2c1c46076281c459000411074580ca8110402c25503941401e1044032445403862144940c442030380194110054000039111120190050640401e200c0800d100420310000c0c0410b080c00900c555180585450000f0f407201c400b52002d40e0441d0901030b0204c4269001c00380400c8403c1d00070019450140703000b0040e00500310040c18006617001e50547c2c0804629800e000b0714138a201180656a5070f510312700050f00f000c0b40f45911000c039a0050720b001e50030036000030032610022003110410300b41755100c21503080e0144954000070b020901c0031400a100ca4004801030031400c226100303039a0159160001104e00442c85a0350500249900022030007550182c50f000030540d0380c081e58200010344a10202c1c014500198503e140011142d210340203040c400c0c421303900840a01c200500c0035900d419000010010a80225407141c020400400c560744c002d140c4d80c1340304120400c0404403078 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 124666537 1250 124665287 124665311
    0x110f030313030305180a0b070207052110110d020c12070b0906070503091b06160c050406061d040b1201050a06030c060507200402070204090f11030a0c0605090d0204 72
    0x41d104800d044000c6420300b0040b55000c44103644003038207410301e400104100b0a40e0b44400d503d0000c041e0080040d800780c05030101d2292692800c1750a0542da180ca815112000191550300d800b00303191091045034645000c0d05080b01100c0d046130381d0075041d0f10001d82c0700c7c403003062564103113074182d000007083d1000041c0720000c10100b200020b211303001841c1620519900c010003030310035101c12a50f001c204c1d0003402c95501004080001c00c6140b50014120358100f15106498036511102148103460442c030252080040b442c080c018100500202e2400c003580300242081401040d0550290901c1103813070301d02c0002c0e40d4440000c50f07602e03000e60b10024030441c10710b010a040140142e000030f4544121380d6802003019030040d401c80362400c7d440003040211001c0424642100b032461414680e00c00d07000c02c0381d040940d8039030007440b910501a10140803401c6007854034101c02c3c80b290045900a0300000d0210001c20300c85006c2200301c81860410036a20894000082c0c44a06503c0c0300030b610614007114540c034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 124667787 1250 124666537 124666561
    0x1311031005040c08060c0a08070c03030b09040b04060b06071511070b0a020a0201060603050606030609071112030a0609090b0705071e08090f090603120c070305030a020f010606080412110f0303 84
    0x4c030740700d06094a003551036445020341d80c1d201d4440c0300000b24840c41e009c1584240b180b038107c40300502916000880401c040c000520841d404c2c0da080c4c5454244000380000d0118034850303641030090894a031454200d06544290954400030070f100b4005e40e0314406105550711080448042640c841c00c0c40784c0d20318181c1c1d841c1009400050303841005610385203010400d41d0003885028001e0000034000f605690341c01007003018200d070040840e000c00030125074200c500601040700e440c0c000503003541d50380c4a1402c42c0030b0404988465018000c0c440c1001d000c180480c2c0030301c44403034201c140b6141036603071880603052100e131140084d2628158004000c50b01010306c6601c2c009483c42d40d03000c4480d9440f20315181d0801001c61400d0300c0e210746c55001090000060a950030090030f80480201c240c81e4012780d00e4a61900b107401c0007001d00090b070015a80d1904a500078071410016200ca410604a80d080a854090301200111160340512500c01d85601c0034040070840610340021031022643d803440c0548007001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 124669037 1250 124667787 124667789
    0x10e0d0207030c1a12070210021911070e0c0a02030918010305010c14090f04091a06130606020d03050910090606050118120206030c070f0b100e1311031005040c 70
    0x245030b40310f403400841c2c0c030146403004581040200c100f16041140c120540488201e002d00950306620032411003a50039002400900742c0f1038200d003442503403510481da02400502c05802601c6994000c150140a90314030792500540150709501a00e4803103a4040c402c1c0e24611600200c95440303044e4880c0e5000f2040000011410f0780d206500034085038109a44c1510340d80da02041d03c4e43e0101c424404c0c141c0506103424042d915540c020008284268540c40d00310441c113444e8441e03505c064a0b8410002181428170034001e40740c0206100300000c03032514800940303036001d04103c1030425031100003041c008030040020b036000d4241040100500350799460130000420326880b0301d0b8040740007031a0b8403050180300100001140d5050010400e5444540d0030041154070042402007076527410302007900800c500114210b6803a1146038070f485103007040c504c3c0140c2448213502820183d441c8030104194900b00b20162080750740c0c0001400101194040000d0601c1000c4140041440c5450b08210070b000c14108558 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 124670287 1250 124669037 124669043
    0x903030b03010b0a05010f02010b3303040803162d090f0509010b0706020403080d14062b0326061e060a050306150f03040c050108070e010c05010e0d020703 68
    0x25140580600d8203803403c0c0000a07074044400e6008008650103030306170b641c03104554800010140c02c950002001070441c103c0e56114007444050046291411001401c5010201e20720a401e521b0103a40c3c5407507a1000401c0c0b01c03450b2920500b4030304114081d1b0019080da08100461900071681e04081c200740c181d40010020000700720800c0050300500d2032541c00191040a0401d014580c04c01090021503406600c0c1146c409900b00300001c042019000a02012604941c02007000003112610000c00e00c2c010b0002c52003007914480d00030701991440840d08c11070903030002840c04140181800d4480a9915440c1c11700030040603c1124408841e400c4a13115890441d910075004602407044680c80c50801d06054100c5020004003c0344ea00800c050340e8481c100410340813043c05a50701358030088d04901c1c01030340074200200070f00c4200101c1c41d074a000a06820300e41a0114600070100900500c001150941405510700401e401d01c04203411503921034031824101c9001e01035804009640700b000d8802a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 124671537 1250 124670287 124670291
    0x1b010902090708040c0e0601050706050c0405030a0c06180e16030b030f0d170405072105010204030c051e01091203030605041112010f060c120c0515160519051e0409090303 75
    0x129103e10034240103402403206279075140c00d104840e40c40e840200070207804040d408106200014071907404001002942d403145049200c035621b08040a000d040071741c8200c40042102201c1800300842c99183c01d5827001081543c0381410201007829070040c140c0906454250191155034841013000040050580780d8940d43d418840790140210400c0030410340d03005015070400d1008014420700d82d040b00901d641300c0d10140140021541d07078142264401c0d80102c401e81b0038030320b080015213031402019200310360412401080441c14000245140500d0045580c0d0201c418603903c14944a81d112001404026008102c0e80b122209030080c0c40e0000c1852000c1c100da1480081110303401c0c01c002d02c044a0340e0b501d9001d4441d00d550707501408030030001980e104010b5014032400124008100b80000100583c501c22807608002c90100e91003402041a6014003504104c842062100344882000c0c40625203803032070719900c895201c0c1e191001d800000380340310100450049810b00159100c407107041d10075141 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 124672787 1250 124671537 124671539
    0x9090c0114070b0103141204081506060913050c07080408030306091e04020919050a05090c0103022d07080f030f0105010c0201120f0609090f020306100b1b010902090708040c 76
    0x1603041c0c24030034101e00a20491120f801000001d070281c2110803802c41307503020f4480d125054484519a6001640306460075841101161844c01403034054031b030000070554034179150035110030104130100813030303000000002c0da81c00014100b00401410b6032030031548009580c1d56207541e0240580d0700d8105135840d0f0b200b2101d00d0b0200300c0f00b0318a90184900070240e82c440312026611902081850440201400055900060341a0401e91a84a000d1040e01240300c0050f041c1050044c691801c60b03489000d505040c810091801558021100760f0341c114800b00c000e50800c1a04040d0314564011100010030000c004101c4038945141e03000a144a211103d5101199a03669001120719000c082d5001e404a0401c1d0390b4a14652665000400c20380c0340620701156640d0b540d80c8500c01c40340c02d4542515003a154031a40011450705208080d00000030940018030107050509048041c46016400700c0c460714000707207074151903030700303400590b00c29030002d01020340c900e401400908448001c460450700103202c080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 124674037 1250 124672787 124672817
    0x1806140d02030613150507030e070605040617100905190e120a05090d020a080a02040f050c03070f020a0f06061401030504030210020c01060e04030f02120f0913020909090c01 76
    0x81295000c5030018002e105a8a581c90301c0d403240c40511106840115155807100340c050000d01178540150100d64000550b16200680e050400603103401807800c0040c1000208403040e8001c11070f0340f44141020001d02982c071004001c2c0f0700b011480c0e11090a260408013000000c048544040030080b201010030301101e055078a402d9143c98a13207c0703058581c40180203501c20180710304068560030307001410583c54810250002010f0f00465401100307654060305c90729046040034098101800c0d1840c0d000c1c0014205041e110095000c010102c2017001490084900450710802a591010360080e800388154001c50130040c01400c0c0c070b40600c0c0706031740807205000d982e94442c6c4609881150954040d000e4ac081c50340e030a102940c0b100351027100541d200c24000c035200700600042c0307010360b1203030b1031b5441c0811070700102034148104004c0d40d500720042805004400e401140803104522000c4030062040056003010900034011840c10707a1b040000030b010440030f101d001a11042405003603c814a103544208 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 124675287 1250 124674037 124674049
    0x405030a0f0e060409231008010c0305010e0105010c051c02030406090e06030a020616020a08010f0b12070b030408040801021804060503030f040b130e090d0e0a23010207180614 77
    0x8a00350801e50402081200204980c0951088120080700701c140821b40c50a124001c3c0041d602030f0b040c82100481080440e40c03d100d100311801041c01c0c14005503250802d1004040b405108103418091041c10820400100344000d03860416556200302c2d50b04940c040c002d40e40e030494000c000c041059420049034000c0b01c1d02e207007445004002c004146004040c0c0c00d0020507001482400d4428107920700080060b6600c1c103200d0007070322801000180751030740c150943e01602c03005111f00380640181180d225101e100428000259180d5500303150703503a103444c50311040d140304903408102c2551000c54907034154984d19688907800300048400b400b51585400c105a224401c0c10300b00420080e04210070824810348a010380500803030a0f0b6105145642d49405038481c9004072010846078000e00c031164142604440000c0000d8004d1301c0c0e00d01c01c1c605000035a0150b004018035510085030840711141d642e803080000c6800307011401c540030680e04042180a014000342d01500c08280c60722814031605041c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 124676537 1250 124675287 124675307
    0xe06041b090501080316050f01020c15060901030b0703020a2f01060f0f03020d11101e030606140306122a04090203070b160209010b040e07020a030203031b0705060405030a0f 76
    0x206025619000b400c1b95100c14002c5100030407203040c000c0d201d46403c940c90030b20140c418a51514040c02c1d4a44120360071318071a0130000c114610070001c1f28014030105001501c40c2d540500300f420016903800301340006031400e5948100c81c0a6060710b440001c50f28800c080b0000301c8030140140248081c544614908000452501400607521440c00c81000580b030001d0201c00f1050180a060140c0300060f0041205601c00000c0100030504800c210414621850150524840c4514041000c98208200141080443c09401c0c0040c880440414603584e00c004021002d24082c5c0c04a0307640005444021044016140803249440107007404c10721141014000d03d01c130780703500901420003142000c515442c550003054140a0644030601d56400507154580300070302030704403000c03029140c80c40c00c0000c5402040060103003086403c46101c00000903000010b60307400c09582c3c5a581c1c045060090700361114001c1321320291803442454144414041c003c00144800c46031940c0b8039840301407200d02503c40c1020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 124677787 1250 124676537 124676549
    0x120604120c03050403060e010203011701090c17010b030715030c0201050606070b09070e0a06150c15180219050a080d02100b0418030207050f12060109050403030e06041b090501 77
    0x411569900c040780706000991415100b0b0800b00d04290f1251030b2101103500d45000307080c2c182e41c00030043c0030310700008625000b10240c083c002d000e500312030b03500c034103e00700144a5400042107240c9410b1800c14203402c2140404005811600c140d43d4409041c421f800207034a030040881e140c10021900c140c410300400d4418403001c0c2106127070114036903c800868030001d01403800c1e0301400c0d90100c1c052407a00c80303040c000c0780c428030049038040c200340c00c490b400120b4100c10000d1081560164000404001c60307149005403a43c80000c4c3c2101c8200f5147d0b00c2003425100070341c4400c41008040c40c0c20a4610201d003030314402c4d90103502044c1c4508102d641d03a5130001241025034011403201640d80025000386000c034101610219040007a805191103900d2051070031000350708886801d00060a107141300510346c030000c42d4600180b00d03010341c4072a01c6400600562007403644400c001400e241c0250411038820080f241207030960b18090610b1106280b07503100500240919503000284d42140380200da0688030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 124679037 1250 124677787 124677803
    0x6090606050d0335090a05100b010c020d030201020c01020a03060e0a0e10020304050a0c0b0a02120412030806180c0307020f01021c1509020301060207181103060d0c030507030f02120604 81
    0x2081c400180350042880076402000041e1141800c2c40d02c000490445c01481c1c100700a004024092504c24140080c00b1500c880d02481c240c98aa803a0380d00c00d500da4082501900c54100043c91814101e02a00c0b8003900040c966000003078804146905078844021902004c0c94540e00342c81d400d006500b03407800d2900da041180d200c8510458180425130041d07802ca4402d07000c4591191155a8000040d520b951011104a20101c2e02002050b010f110398200d030501c0c05052480d00b8100594500ca10910301d00c0a402c1190b0500050340e0303500d81e9102c140c1010742605901500346070202074201c050388200c40d81001802144e15100307030036805000361501c480072185020103220070b0600380c100400050010080c421002030700040d000e1258801540a416680d010300b404601703000e0300c0040d00c000700d40341d0b030300d140e03e00000c004100d46d81034240c075000f11b0110380700200707a003982c01d1080d01007241d504007500a0061003030020810406032408240c051003595001c000c0380d801c1c080305489010869024001c07507 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 124680287 1250 124679037 124679057
    0x30302190803041407051003020304020306090f03041811070f020a0b0310030206030c1c0e0c0603160f11100606170906070305070c0516030311030c030909060d080706090606050d03 79
    0x5000e03d2007113201c08a80804032940c81c0c0d980c5001583c2076110340d0302c10022079800030a1009500701400702c107900403940402080201d049600480e82c82c070603031054264640c00200d500c80030080d2900034450b034848000000da1a101c0c2030030072900b82c20100e801241b08040d07000d400641c0c40c1c450015070340700c0c8030400d10000d815031a507000e1081d80d1b03000611a840201c2c080248902207c4c9546954031001c9d00020005005011141e01900c0c0008580b1100d114210910401001400742202400480880d00d003804444820751002e0b00c290181c0807445800b405102a02805403000307a0004c0101c85d07142d56120a0342c00200040d00085030140c401441e075410050000d42010b00a80060b6004581d44c581584c180314642c541074102480010718410703046180e441003092541c8074244602c03910380c20f8003440c5070140300107402d40d403441401a4240260001d400048050fa030f031001940c0c2007a0080b0440742c0d500c01626001c0c009000da80703401c682c4280340c11800b00b21814141514400c0b1545030310358280c02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 124681537 1250 124680287 124680293
    0x1c0e0103020703050c19060b040908070809030a020604080a0b071409010e060f040f03050606040506060301170c0603070503061e0604091a030a0f030f020c0d030e03120c0703030219080304 82
    0x41d602c080d01c26070500c82e080000300e2028004202006102c1000c020500d00d0342054605030341950080c00500e40702d14200207802c2c020840403422501d6059011640a59604e60540400c0c00c2c1020110080d602503130120380064034880200b00725a02920540c2c024031076950f100310956a803e402004114600401c3c010010b035540a0031140043e0540201003d0504207091403142c0300b40d1182d0031082c501c2203d201c04100b04641040074a030840e0044a080c800e80c0703883c0000c182217000501c526a6204920744da40c08103250113104035110080040c224a540340f90246010b0072030750013540c6141c011040340c0c03c90403684441c1c4007040007215005100600d41440c00e44c406001e000e0b40d61074446060680c0103c01d0070fa036001c0100d5011140b0803050301034541072504020301000b001080000641d0400e41b103031030030355941340001244103a2608180818481017408030745031484e001c2d10214540030001c0c044041e020b000130008116880780e804c8031028080c50039a400365400350f4400815690041c0003207400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 124682787 1250 124681537 124681541
    0xc03040212010b0a0605091207062106090c030207050f060601050a030c051b0a02190506030402040207050312010816120b0115110106090b0909060723070f0506091c0e0103 75
    0x1e8030404002142c0d00300c04100240c1d8071040781c5d00101c003041c1c00040804040c284010b2141c22500408050000f4918000010384806c2501403001410007490f608511400318652140020384580b031070400c00105200e102400951280e1025107192244ca012203024000001e81d86214500c1a910107040c0030003288280c0141402e140420240403050005100500c42c0321460a0150742e9103000b800501c505006000300c82c520b054004184400181c8140300b161260002c41c2d0300140c0c152001a03594440b41091811409146080c2480d01c0703030b810000039203810014041e44080c155103d20b01003596210401c0d01d05101842d40204110805401005008106101c2c417120180c1130402110754030910503460f00311345654011010032641c4801c560741a00740413680030f600c694440002e0819003041c5d54081c0040d8840d41142d440001032280d6041c0d00c160714000c2c0c994441d801000c2428040c502d160064030b0b21000c440029603032007036480f5904e8007407011601040f40e1115445400b008940360b801100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 124684037 1250 124682787 124682809
    0x30c020f03010e2508060a06090b0102030a2a0f140c04231512010204080613111e040216021306060c0f0c0b2b05010819050f060f0403020609060c030402 67
    0x1d003502c4d00c0c900000b00c00c6418800a84031b4611924002542c1d0304100700701c801c0b200d80786500d50440d8004d01062800f141c01290003200324981115990007811040101c0503041e603030020041060318024245802c2000c0d0060a401c034440030300c140d4090101e020f00b0b00c000c644407403211842020f01c0c40d0210b54020100041c1540185198041410b4500c403540450395072100e0070a03402c0280e500080400240d8400d20200e60080450303001c802c0f070241a6100c000e00c072022081100d104000303010800c01c4084010303280030a8550003401c00c0d9221200d03061f017000391200c082000d90050144640c0303c0342919036803081209442d841e8403006101481612036080d0b21060f500300311041840c00c9004500100360f00080c11103014604200c0d484090310f00760100d8680014528240200c2c10200140300301100402c44da8100c45040c094500d010340d02e810094074000f050a50b1051500500c0c0034800c015658050b420312690003038007101c00c1925440d40c0d0540d504800c41c0d4500d15001c0c18004540185400c0441c82 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 124685287 1250 124684037 124684093
    0x5090d020406051804120513090203090a050d020705090112020904151104030b1608010602060c0a0c0c060203040303171003060903051207080106020708070806070f090b07030c020f03010e 82
    0xa0454072000800c10380c4c3c0c8900348407040400003030100700400145820810828095243c217500b4081904030603241444240101c00c0c005801100144e103900040008911090304442160901c0c0c45491000c0e403103134198007485000302d405000201d0008d41e640f0700c82488903801341640311582d4480e00e030b076454010200e040b80c1c0c90fa901d503412004080c0d11140544003030360044900c03d00600b13000f03111050f10014588403005000790030700100302041d004280c0395070283d500031a0950f540340c0ca84049501031008540103011340c0e0700e0740020808550000140059a209844180c160f074110314661070f881c4012036405241000107107003403000070516000f2a07a094800c0c1070681c28031440440000c01329404448040005480d0001000150380c1040808010030a100c058421b032030400d0390f2a911840001e00140a101548480c0c40981c0c0c4580e169030010802c8181241d10b0b0100ba1030700a205401406050307115000d070b210503005901e81131244208091101001303281101051041402d00304071600e0003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 124686537 1250 124685287 124685291
    0xb041803110a0b0a06060816020604140c04050a0501090605030a0b011806090c0c21170c0403080a1e030c020a11031207140709060807120c051e0a0509060105090d0204 73
    0x2c0c1c0000350719201d00ca800780120f540d0101c0e11704d0030030100600c800b0700184210b00449103410300e50f0490f900410816040b80d046071644551442d803036081c0385005c3c0f056034883d41145c644400c02680401592005058814180b0280005230340c0b402007603500e407168103014103014013041c0100a01c6c002d4040340d21814401f443c003c100d4503520700020b0704885280c0346000101d4000300d01e41c01000948005e8510342c2c1d000380e44c940007076000c4450040a038031007001150691620000030512190021341640c00031079100050607a110b80c2e0500c01070900000014000310303520701007418a40da50290240140f142d81c0b50380148040180c503154100151065020f10382c05000d00e082031700c18660040001d018660048007000701ca080450703000d91806d07030250f114445c242e02e0a00e0602c8800340204880d412154144940d101d003001508245000b02582d521895200d01000d142d25250300c2c40c0070290451003c2141e0800b10581e03140144184c0034400c51b40036002503c2041500860318240c00f10414880c0041c01c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 124687787 1250 124686537 124686553
    0xd0213050409050c010e011803030806180405160e0f0c0a03060902031003030e10021e07050d1415060306010b0703110307030513080d080a0b040b150c010b04180311 72
    0x41000c48034000b60644664010448060965030030008440c41c3c4c550038a000501c80128075001418041e090100800304400c50300420100c2c0d0302e00c5c600319058000c50816a0b03041c1000d162581d035800c405080703018411455440010098150351150348200d14100110466940d13500600350540d104000000915030394650203d0000006c3c400341d40f11315010030701104000e0440c04c001c0d01c80341e00e000207544a10a0b00b144031480603404a00d41c00318502039442d0b640181e01d441c0d000c1d420701c060345c0c00442e001049105040240085c55040054a510300f0081e101c2411311103e00100d4807004941958059015800400240c0104802002e280340030340741c040b8011565421917800c8d544084402d90003d4004501c501003100752040a20081001d800100068408540f0186c01030030b000b400c0131500c82c0d50f18505c07001502c03650018448403c0040c02c3c00f500360220b1410103210303003080403080d401e50320300031222640d8102407042d14002265080343c0414102c403a40c003211110f00000a0580501070840 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 124689037 1250 124687787 124687789
    0xb0402180106022811090403050f0c01021c09030e0105030703060f0b03010312051c0b04020702031f0b18061215010609030312050c1e04080f060402040e0f030d021305 73
    0x506074080e01c0941c0c00351480003c0038111354825030b9821500c1032004a00c9800c1d13000140351100040c400c0c4800e43e50920a0740d6542415100b0307004130088003490100000e174140480d001940240480c501c510540704812400c11442821903070341150003004900d061140300040d40c0108083c5500c0402450701060807034444040841d408441d40c40744010b04000710041c8200210040c2d4010311841502d80307030b07081019000034400c589502064801a1541e110244000340d22035404a0b8480b5801500301c1d5084405501e58060301803a12420a62180c900305030003c1500d0242ea000c48a4035040c62810300c09c2e1030b10703c20450703003214249040400e403146513520484550213080171130003084c6549486c01598518240580741e041c003100805a03040c50306080210000710481a2110040460542031500c0a0344c50f426103188660380084289104544013403080560005010344980d20a84007408034520030150160750b0070421900d541240c0040c85800c10380381281e409050b08821400d0b2201c0460b41d200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 124690287 1250 124689037 124689079
    0x30102180901050d150c0e0d0506040b060405070e15070c170f070f0b09010314270a0203031b010b15030906100302130b01020a020a0b040509010e0c04030b0402 70
    0x9250154020005100c11a0303840c01c06106401008103441194264103a1780d40c074450303500700c0384d540510035946680840711580b24071000c2142800c040c280c2c01014903942041655102d045904447d80b4101d140000d0541c01e280c042e044c00303050240c59024950030640d0410030019a4102520108101032200c50046035a5140d42c2c80100524110811818403450b107586c184207010302c058400f50710046c0100540c82420081a04540c140d0321616103a00030b820041b030285c4112154651000700c00c005115900c40c100e42c0305207140c200f502440c04000389450b41c01da02c0328032040780694980c0041c406000c8041da000c1d5000c550505030400041d43c1c030314040c0040c10244680e5050603420b2004802c00c800ca80c0f040102030b0700462480ea91100315891a4002100a085986440c450707584807451881680d0003000400341d0664000c0410b0003c1c0c0d102c07070344150150402d1041031b2182e81a003000280c5107440000a502403864101e08616090070740c0c40d558074010300a0001c80e0800c6c808000101c55070079030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 124691537 1250 124690287 124690297
    0x105070206070807031701051806030f07090b0102100b03070b03060d12020c09070806030706031104080a0f020405071b0609031115090d050a080a051b0f0a02010f0b0603041709030102 80
    0x150125640781c07a01360500502c0c91b48503800800088036030354010321180c2d40e8099070344044103010110046540d10980403a080a000001d11807040c42030344804911180141c00030046801c003079084840b010103254031601a80c1d030340e154441c1c140e00284130a11038040300c900116404003000e058400928200d640780400c5000121081d801a04205001680d03882c046844540100d581e00d03004506080090000307480e0481c03481032000340343d80ca40c0440c070a00d060805a0f001480c044050300c5489129092203c5d002c0e2144034106e204030314050014401a0080d0200f424510080c40c50065602040e901d00001307000310700f01501030090f0781c04035140c0300d00d0411101c060728243c0001900c1a05243c081c6d00c5ca03082d004035544051080500c007880d1600c0e40702e04210b40c4a0340001000c541611911040c1e1100c107140541c00341b040b440000c049868085e0240204802d800b00d5001300320120b039031000030742160b1300980060307030160080001c2008500c031a00005035042441110b01d18145c0c4220020b0300f26445 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 124692787 1250 124691537 124691543
    0x606060a09120503190e0901120201020c131808071202060c0d090f02220606091a0d090b040f0c06050a0509060703120203010807031112070611071e090b010c021e010507020607 77
    0x3441544051b5003000300c0c0d410300500703503a92040d1040303030261700103503c1c1c03d00c500d002070060420517000410705503550000e011261041401c0447c100ba241000030341a8000f0000761000040010000182440012014460200e650780a4140780414800402030314800800342c0d41d8a918030f010350050b984680040549819003420001c3c036482e18414a41074038455441030b814001112001c0000001aa5002c100711904003165a1354001c0c6080010080811b01c0c00034100d001c04d042040100505403210194850013441c800146a94846040b01d00e882030209001c000341041c80f0307141c1d60b42041c20103001802d101e03091902d04020a1a001003c0f0f8000b44e10100040c0e101400400a200b09070614041c0e03c20181d5104e2206141c3c1ca0320240d90301c000d4826601001819254035408050500c40440540007090502840c0021218900351340e803000d0150190751880d1940840380c0b0f42c0121361120703106a000d00b80040046040301c540d010000e681c0400740c103101007081403800617580e6500170201548 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 124694037 1250 124692787 124692797
    0x21c030e06010b09040f0902010909150909050c03060108010608031917040c06030f060509061c060915050c0a08010e0601120207050d0801060c08040306050411060c0106080606060a0912050319 84
    0x4203444c204001e941c0c98409850f00e07035141044110160340c1c0720950340c00782c0300540c00200f075800b44100300c44a4104640d010807292450a0900d000f049004602680f060700110226141d036601d8138017490803110140b0401e1500e5100b0803511410001d14680b080d0b081243e0300305564a00c4650351404c2d80c48c20100e404440c0c20600f2202400859014801c3c610140d0314500200641424040400c0140d04040e000334801c01e508402102951300903400f510059030304c507400b1b10103859203181c4804130341c0f0380c1340c0300d04c03c1c15040ca40040c4003103200c042512141c03160307540d03410080c1e4a001080307980e848020344843d040000030408a200e101c0346000410303541d4072442c0280118041014000c00d030310010b802039400c101042e40c021010940460580d000d8030340180002542d07403500c1c90a01c0200b5104020241c00500120715600c0000040d0301500c1114244016621150746002c108520fa01c18400107001286500d5014024001c107901d0108045101d10100e901c3c2a54889000003515043c4c0340043c0010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 124695287 1250 124694037 124694047
    0xc100507021011011512260f18011e12060b04060507050114190b010507023016091805120a18060c080304030e0a1503110307021c030e06010b 62
    0x2800074407801c1c0c0d808604070640044507040800c1e6203407070254203801801c2c1c0c56032041e80101c0100c0b03c60701c1e07201d0350903051f0030940e850b5000c1c0190b400503003000c04503070800c0311300003140702c001d5003c0c0321540c040c00c060a00580300854801e8042e10009000301c0704200681d81c7e03883c0403800d94085d10003000a4565500d415480c2c0d40103261440c2500c140345980316062001409000410808203480300c045401810081003402003a80103d6aa00540c00080d51100c40d90f041c2c02c6400c866091420022495076051170714100c0a0070207283d80d402821105e0f20078503201d6904010804055100b4180c030140b4090103a90090952101442e1034201c901d5903040c1140041d20329800f03604070001c1517403d100800100301040c9416006030002420f1000641050b10010000b41010300c100001640c29400600d04540c02d0f4a90036902100d4288030900e101003441c1c803800e080c00500c0902940c1c8903402c0369004020440e40150b10210030200c0304809801e0544503542030320981d07010b20000e4068488819069210 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 124696537 1250 124695287 124695317
    0x80a05010522021002030c01060906150201060b090609030703020603090d0807110312061201060603020301140402030115031d1504020108070f231309090b0c04080c1005070210 77
    0x40750060456507124060700d40012003400d41049401e6800d0701124811000c0e01c1c41c050581c29485007140200c02c0c1e500c0d0200100340b1040316840b0380d054848500b0701d0b59110301c09000580c2202c1c0c0a0081c6e003440c400500409030341c0d05d00600146011403002d001c0c6c0c1d41a40d0740390301045041e0016108007810348c020722030342d0404a42c40506a50f00c0b95040c60180c03084488d0fa280c240d00c0740700c1c45d05219a14400040002c8603515040000e10506854100800455507920343c000d00a40085c001c0246c1064007440640a918050090340c3c1662000403000b418920502c105400500014080c10320b4010710701c00d0000590414840e03210400314104503c000b0f0316091000505110004120005008200204c0c031101c5038840c1d91400340c0440c0940b038401207031400751200766a00507801e4004001c12640c00124040501c5c0d00300e025254032901080040752030384840b07108140128000c0b0040c40d84100130b840490714007025031400c841c02c01d0500914046054003c541340305113802c00301000c10f00c012000818 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 124697787 1250 124696537 124696541
    0x8030405011404030c0b060414100e06030109110409050c0a0306050901060b120708190c17090a0b15060904020304080a020607110d210203011e060801140118030804080a0501 76
    0x8601c80e603a20281003843c090f9005010100100c03409000c55a00d00d00150f01a00d450380181842d05120700c01407624034042c101c401d5501068090092602c04060205041d0308050140a4506600040d42e1501ca021402884002c0070a07101c01e4489101c0c44903d02c010b0f403030b80c1c83d8010155000f0f04000c00d10740b500d681c00900b5140c5644c41186883c4040000b91401c0b03d40c0c1480e0354021000345811442a180e100001d548900041c0040310b8a40c0ba00045205441e0040040c0d64030318000c46d003203211540c404400c16106c8018040207410344100340002030b04a0201403010110703400040c1b00d2070402d040e01c070103d0101d0b00212800c49459a00240b801d5070990104070240e40918140740a5020402109050351502d00c480144018842034000b039051070308000c03e0100700b8070100e1034219184d6070740e05e54440c50950000070281c10f182c10003201141c568400c0c03003024140c030680340303518450001c02801120510f010000143c1c202c262244048001484a80200010409880100700b140c0280c00e00b01d00f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 124699037 1250 124697787 124697801
    0x703060b090c1602010309140a03080c040302180703020f130e0a06081908070203030310030b07050a02150601270f081b04090311060c0a08070305090c06090103020c0106030803040501 80
    0xc890301c0400100030000b42800110b074024040c000d083c0100000510044c3d014000700d11005200c0c0350800300450340640d000944040f10380c0250b607171042c152035880b0300b00c4551045001c06500000350000340f4540e480d0860784150454590b140c01803038600858441035541e0010043c0130110500580d0801170034510110311a04007540d50310400c1b92610340060265651050816145103901c0d24403a4010b011011065420b01c0740c000d8182c0340d03a49010703180781200030f4440c0400c94201003100e01095466200d2020f413000c208868000303000c150201129040c1d1440020403480c104600842a03042d266021000d80360000000034540c85c0e02c60400a20111460b0250080550b40d40076002440d400f02401c82408018074081c2c43c00554044903084c12a8500c4604918003900d100f450140302484094034001c0c00056201e503a010307215111100308034250380d41529802800d0748041e0111005203401ea0040003c01e6050400515005030012002d0035a14594820b03101d9007000b00402080c4042070040d80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 124700287 1250 124699037 124699039
    0xe010f0f0501030b010c06050703180609061b082206230c0903070b032706040302010b01032d020408100e0d05090108070503040804030b090c0a06020c060703050c010f09050703060b 79
    0x800010044c6000030407400340f0200c081c0000707032a107001c104810300a501200f400140b0020014150100b030030300a02030500664200c070f105180c1194135001c00000145524100340580d41d02e203140d00c0321a89034141000003c6011082031058800900090040c0b140014400308609004240184d946000803031460007045e0b40b01d41c14040040c070500d41e5012884100f0380d202e494801b501d0f901d407c1d4501d40204c81080310200303400c16141c0e15030101800020348a100c1e900c2a8003c1c401d120700c020044054401100b01c4440100c0c00000003d1083c1c408800203160001c50203005041c140e0b5810100d00e01101120a900107035500d40d40d04081c41020b1003c034a04484c641001403906081c0800205484002820700d4100840400400e0420010703a0444008540040c41030800e420041c071425280c0d4080007a00d0b203c8ca1a10100103100360010032000c200103002425541040070f030b610242c829510091141080f55621503121802c014188a9120308900076001425054198038080045a951030320071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 124701537 1250 124700287 124700291
    0x601080702030906041806050d030c0b130c0603020901112401050d030512040c0b04180b0a080607110307020405131403030f0c0c1606031e02070b0604020a090e010f0f050103 76
    0x20b2403054039013004a40403107103034a2184d100c3ca205c01d0b041100030020b41c0c000036801400440d00c4030505034010101518a400b030035411800d03403111072488405503000c0c00c0050002d022080d003000707001d000c0d81c05054000b074181040c1841c0c51064a15906040038820760424be016138030a0003008001905130b441c0904010780d40c071428800c1e9924050280d0080c075a1000e64480c1d020b0003e42007200c8000c0c0c0c5001044003a25003500c55489000c040000b86802c4110b200709407601007243e58514240c56800100c92002010f4030f125146c0c0f44080b00c000d010a400c1441074403081104c000103131518031400748034900100401042100070325141840075450b003401440c551041c0144611200079900c1c040e000b00c414000c07a5580e607047d108403410200440b0b4504c0c88002902400a50705802d9000301450b00c0021030388400e0007403495900400c074018040041c29140d200d1001854908007903000301440c0600d420844e801c995110a4446140e0090b00f140404102001d001c110140600380c54201410003402c0c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 124702787 1250 124701537 124701547
    0x1006030c061409030a020d08210a0f02070b0105100504030218040326070e010c050313170f0303060d050312070507030207050f011e0e13140705070c09050a0204051305060108070203 79
    0x61340d05e00e40c07164040c0c420f19503110801d00300b007492030440d81c940380d0300b05005000684040c10b0584020007208c0124030207081c00010310001c4024803c8030900d84d1f00513404e6600d6400c203070a20103c2c94103024503205201d030410010000d030baa0003404504611b425007844900e45007500c0d0040000c0c141c5103107032941c0c500c541e60541e1600044521968400c21618200309100340b5500121a4101e40c188094018000002e464425001c1c24800c403003610702d2081b00e00b104004210501d0f41d66040c0c81d03803108040e0403d201041891405c0c0d40c400c03140d80e02403000c40e0b0406103038084080c0642003d40e0942d000c0340c0300207028010103406100c0c1a00400c0e08680b0400326024010020380480009104422507030b484900710b4540c01d009134000c4200b044080c0c03440d1040315144100c80c0050400750104c452500b41e040018103118802c2c002c4500071940b00700d002c411245440c6000019020103012240000c0d000e1201240344c2e03c95135200d0304d40d4400c070900850141040ca00140c1001c5000d42030601715001004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 124704037 1250 124702787 124702789
    0x4091104080706050d021201030302010e06060a080d050c0102040f0e04060506091308160606080304170f03040b0706090512181503060d06060302060c0304030309090603020a15021006030c061409 85
    0x2c00078100c512a00380260348030403010085000b48150600807807101e0300c44002100303042d170551003100488040340440d0400d40b80d10080040c0e94402d440b0f034004590107102003060080c440e0014000010754000054101a250405000440f40b5a001a5000000c040c01c0000b8001580607080d00501d040c0d803a02d656040c265100d05007800c0e2401c0103440c0c03010000c0d071080c000e0341040b11215016048001007140580f601200c0e5220350280c81261860801c0d40b0030a03a03044000314a10508980302001546003624202d04400c00c0d41250740c06650190340d03280e0410100d901806103460304a50100241e41c0d41e030012159504a80341d00d00c5150103100820042943c4400b41030499800c84000c40da070000688403450a94040c0c24a50030080d04650b000c1040403c0740e0f0000058800d582c407070340320205805d45403903d410445426100181d84076090180030003030344510074900d205254503481540c0c1800200c51540d000e43c0c69945c8110303404c0c1e40095041081d960f12610a4001c04503443c1200d180c119400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 124705287 1250 124704037 124704043
    0x140d021b060a050a0c0b070503090c0103051302090c040e0106020307060606020307030f03111315090e160804080f070c061812020405090f1903031a03060f09070504060801020409110408 81
    0x2003521002d00c0f00008204081d140160403804549500110f0111980707849500240f043d0020b4403000684d02c541c0020128030740c0240a00d074456686442070040c0d01005400b0042400b4005c3c00c482c0220004000c049030081e180c2055030702a180503001155500841d140250071203225600a40841d08280010400643d0000010071a44135610300482c0100440620784006e03c901140c92061840c080701c001031440343c148003c12032124030307190070340b0403a910f80d1035010003c0100c3e0101e0312413500c4c11800c555980144125a0498010794449041003045041e00200d0350214806903009c0c40c0c81c1d003003040070759480f80d10b403c44458001d8460b070700c4c0c624100c805900d580440340020710440d280c40000302d0b19030081210b000030201c00012205044644170080345503e601c4801640040e0400040002d21100e50646a00d4640c014004221580ea10a4041e0070250041c1c048000d5000d651800241941e45004034000340c0140e500050b40d4510700703840c1004842407001c0340708550ba01400104107101000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 124706537 1250 124705287 124705297
    0x10305090d110705030a0c05130209060a1d040501270204060c060e0309060f1207050304020607030c03091a130801050103020619020c040504060b031b03030a0f02030403140d021b06 79
    0x98180032540440600c2c1c890308020060308401d8051240160700424080c81c048403104807041134039655002d000c07144c0084140c5c1f1840340c219400c0311041100d1035110703200d182a94004480c40b4151401100b41ca400201a90340170b1f4841c0c483c0640ca049540804119041c0d251082c001c02c0404615091801c0c901504254618001802013a0fa8041c6449141c00030f104880b840c20000381110703500c007001151040c03144c00520403540e02d09103440003d80664065001ca80c01a50010000c0b410040b85560840d45141c001c0c10883c100041c400d8009280740d544560a40d40808128419403a40220382c105403440c8281c4e0700c0610168100401000542c4409003100c425000790080d6205032006079800307a18011480701d035544c005142c08208014015158400c1d20844400c40940703c120b69030503607110312000010f108070f605401c20090188942c1c000c100040382e400550040d07a041a59986641000e44003240ca0052580c01c00c075010200107906200002c0140300e12a41c00d400040c030040070607114018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 124707787 1250 124706537 124706563
    0xf0705010e060f131212020f10020c030d0603062403020f01050307020712111f17090f01020c01060504060b0301062a141606050705030d020304030e03030406090602070501030509 78
    0x400030f40b81181c90350000031103810101100708401c08a5845aa00c050b085543d9010364184165a5650051030703c0404c001864040a500504103640c4001d5844002d502104d4001c80a11081124821451060140400030b6000d02c1c170002d000e040b540342030148240c185ca610100148c02d03410600060ba501048504111000e04e00182c0341d07580c4050aa14180c07076030304942e5040c00d844480c00b0801180c00b100452201e416590070040c2420015400281d206104940c0041480c076181102040341d04d4422903809440c0404960311070390550085400c9a10400202980c0e9440f0841800141003a006000091060701d89540c03030356160090050040300c00c030b03266074940301502c0c0c4044c1442607001d039a00002600080303011103c407250300c141030b51703103103100d905d1030b008140340500042684c02001600e4050360850055403a02d06082c04040003580010300440a010b80ca90101a254508101030406440141c80c4c51b034070a800c003003001c0c1c90801568481c86c101420316040000410010900d0040818 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 124709037 1250 124707787 124707799
    0x90b0a02090a140301060f080a050111031510030b040204120c05010c030210051e0106030c09080f0a06050a020d060b0307020606040933150609150f0503071101050114030f0705010e 79
    0x2030780b00000c0c090656079000520103401c1c2e44d0041920790b801300327032480c1161080008104020060b2201107107030004880554241540382019030141c20015827940040405140c002990403c0400040407600150041c000b1403e402610404200c4a42c5025000e08000d090044089509580007035a44680c407200440c2c40d601c0c1c03408200110710040b0340c500c02c4100b2880f400003d68403554000c0003405125100400101090000503036150049038004880e4205406000000c609444410244c40050805c90342203608002450300380041d4400c0c4405840310701c00790340da0ba00304100020314080014000510461a082d658030000e00c520b9040100c0300250082204e4a202c04101c021000b1200044005058242100c022030704000d04180c400f0b680d01610742d400c1189d100d00404404c804e40300789101c00f05030710140a8610038080c00145600040c1031074502d61307031021600740900b500da080e40858072078003e80c0a84980e518040c0310a0310707148400002411242e15241c002000040140c8403030f13004070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 124710287 1250 124709037 124709069
    0x3010204080622120f02160506040915050409110a15170c16150c0801050904031818020d050a02090901170a0609050a03020c0315010603020a030f050a090b0a02090a 72
    0x5124425001050f5400c00c92141d0840445a0050010700088160500500070b03000f00b000b541501894050984102030314603428941060804001801e000303071400f20401300120005016912030144c4070156119a042040108062043c050ba103001d03500105081e00b5142c0e0002c00a40c0d20044404813540c0c40400d0000c20745884d07a0300c40407441020303003008185002c103000c03d06108846480a40341000003001708010070f09000111080e00b420b02415510840390008100400e1050f4034880c9100c0300d044a05c4038007542d480c403e500d40400c02e0908a0020340200360410200d880303104450b44088050820340c54403c0410014140e44014007941401c03445c2140d01c0114400104440c03a40a80d01c581d0810000c0d07851f08000d40c3d00c4100c4d41c0304030014802c50941d0001410f02245000c030031441c01354a80990790030890182d01a40019402c1e504040e41c0c0c2002c440e06140c0c5006681c09902c2c01000000c1d156528180f0100c440001407041001ba03004020001244e1580d00c080030031030300f00b02d070810343d62 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 124711537 1250 124710287 124710331
    0xa0b0f240a030210091a0403053301030308070216150809012702030d0f0f03051b03010e06030d0e010210020f0903150a0e0127060e1e0c030102040806 66
    0x241e00d00c2c0d04081d4012005075048109550080c800b14140e070000a00011600c1c1c0200c0c82060500c101e01004003941c0003e031440c0c101a01c16099809a00c1c00c078036941d840710310480d2075544418401d03132043e400100d89106000510760103008800d140e40107081468805814a1022030060740040559070410184c500003ca9400c801c0d03001002c880920103040802202000784c03143e0780c40441c10700b41d10a001e1503c541103450301909400610406030b440b02d04000038614030540c01800000d28094201850998003000c14114400540c041c00c0e4920111a90341000e80915107811110702441080c420f041240b074405a8000640303400111b0464030159503050107200004050060030f0f200c0c0d800d8840c124100d4800302280069920038200203c2c10064001c03440e61560980d08810001030034001d40e041e070074046400b4003155448580c0681c078049034205401003501d14040b520100300c0d001c001e02d19000c0300c000780140030780c60380d140c0210029410a824181c1403504e408001e01520006c2c14059961190 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 124712787 1250 124711537 124711549
    0x103091a15030f010209010908071a0c03190305070305130b1902040b0f0405360903090a0303090f0605030f0c070201020a06020706150803130b0c011d0a0b0f24 70
    0x720401c00703010303501c1100c040b0250350f02175001082c4503404100002c40c0851030060000f421011910003d03900290702c040c5024808480d44880d1030f016031400100004c0b000301c4a100e0028842c0c000c259000280c0d45015600201121406480000c501d0607483c6450301054200040c1c540140016078080703c490000e00130a402407007aa400307074840e50300105601c0c0042403d44042c3c400c5400c00d4170103110303d40c0f030404007001c810286110480718941102d400515141758019036540006824200c03850108802d0000784c0d4001668021070000d03507001e009008105621035058018405424900d0950420101d071040d015001032031544400c6c000700b1920250b82c0308000c103000c00c03500484115602c00a6042c410086c10640c030030038200c0508124002400c100c0002180e190b00300b120030040040d414103003044455031060400a8056403245502114080e503c190050920705001c02400001e60320f1604548010004020b01c0703031040c0303d0040083c40e250310321141c0c2d0b00c94021a0403190110f40030b400968 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 124714037 1250 124712787 124712821
    0x121b1002150f1602030a0203070f020a09020c060a060603020f030a0507051b060f010b07150915060902220f060c0204060e0c0315090c090114040503061608060103091a 73
    0x5021028006001038002003284050040382d080412500c2c2500c080f8060303999200d00511500141d104100350401b10f06004021004288002c00d41340f0f1441d0340720007481c00c1e60000c4045c508190094010300030190b025100301c00041c2500d0405500702803c504445015003c01800580001c0d210000114120300c294200c030310f8071000032640242d44002d03407606070b81c4400446189816032400c10010906040e41d100b40c50683d940141800110f60046c240326003d4514048100c51360302600961280b070300301d00c2c000c0b900500001c1c60016100c86002c0700ba0030b080009440c901d0f90044240209010b0032042c0201c5c20266820340c1800c1e00b0307640d018404079009243c0c580c008040481c00b003050001e0700f40c09000860060a0504070101161100d00c100004010283c808102e290400c1003110190350064007400c50206422400c0c0d4203165a4002083c10000101d829042c1c0304058804c1c94559078000c050184c202900303103410030070044d55a4400c01c281c4101d100d095409668580000d03408010598501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 124715287 1250 124714037 124714063
    0x1a04120c0b07030c0303150f06110c100c02030105060f0a030f080d09031d151905070c0803040f080712030507050a12050408100b0d060b01020307050d0806121b1002 72
    0x2940c2c61019090041c048910904111300003030406850840308003042d1101c5099407022418a42541e1404200303540b03c50b100b140302c0a96004070440c0c4e10a40d82d4018690118014a4a4a107404100c9104041c01c4602c020a400e1003502c10304010700c00e80c0c58052035081501d42c00f0342d520060030181d003010115400340c101c4411032141080508070405920082212141c640c0404005140c0c818008011141e251180780200505041c001c04001400c039103181c80c69000c090920a24040d8a42c5803100f0340300701c0340c101800035400040c0130414050584c22070002460500060210282405801444442c00e0100a41005030115a0600340081841401e03103441d4010280c5020001181010b005a0868410741d2820300a10784c0c045858240d44c062100903983c0184109100842d550320030005210309102c0ca41184018460480000c50420801d144c60803a500c4640703052601008000160070728480161603600110700d20062010712000900c000e50313044508804030268444c1c12490720708241020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 124716537 1250 124715287 124715309
    0x140c0d0c1b0515010602030306032d0f0c0906030d02030d0504030302090909060103020102010e0a0506010b0d060b0a080a060b04060e040506061908160c031209060b1003020a08011a04120c 82
    0x20710208500010042d58489040e00e4000c03850380d031108142d0b12030000321100754054112a001185e10883d64850101350a455484510280c0e10840400d20f0003209103007c840311f900c00755280c4194500b64442d02c2d0b1141d421001409000751120009440e0300031507005041094903800030804042c020b070150b80e010710f4040c4c00d00b80c051804c01c8800e03a80d05400e201c240e0141d4600103009403e481e010600c160101d400400500075a4a0405203a005900c64034200b100c40b41ea0b600f000c9490b00c8100c00400d91103104d0f03952004581400c404600480300580c0c019140090108020002d443c0c200740e101d40c4044c0112000990307981c8900c003160582c440c03464000d245200c541c0d282441c0c1c542000b0382c140941000c29031000b40e07a903c504261410302c86010701602055200014480d0100b144c0c01c03103c02c0510440340460300d18281e01c04100001c10780d80d400d0300401c1c0c000c10040101d41d4031642c07490040c10301303540d800042e500c0e8140303500080c403460007200f0b503240c2600490004d1100404101004006075498 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 124717787 1250 124716537 124716587
    0x71509080c160e0c160614040f030e0102070f0e0a1d0d09080c0612040804030b01030f02010f020d05030c090a030b0a060512010b03060a0b010c050709050a140c0d0c 72
    0x20054855035200342e1081c80c25184440469420b00c1d041034184550401404103180c010000304243e1102d1a0240480d0f0441d11030000303901e0001c00c3c0c15070a01413480795005003840e90780303031a000c0c0c801441c080102c1d045500c041010804244041d03550012690307010115080c0e81c83d10b840a0029003064090f10601551440354400348120000314030301d840003d581c3d0115420717228000d150f101c50712040c0d031903484403041c00f030004202808441d0030b4000c1d00c00c0e07041510f4079990b541d813890500c0099105482c0c0d90300e841b440b00e040d5600850000140411440904407034000d0800c060503038000600445241c000c045a9801d0307a031119240344000d1030704540301040c00d24140700000c0181125016090081174a800d84c1410101c0c140141403040708000c1c09800c250740c0701300c11b10303004007900f5030241e04211000000c000480c40611000c409442134100103d01c80c42c0007400c2d4030503202410342d8a054003003020100044010500140e60446023000c40208610000b024100c07184041c20107003088003c44218 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 124719037 1250 124717787 124717807
    0xe090d030e0a0b1005031002040b04030206090d0512040515120c090109090f020d0b091e15090a14060a03020303030c0a020717010b0307050d03050304060c1b050c030c06030403020307150908 83
    0x80400700f2160b00300c0072200e4402090350087e041e80158424a171001005210600041c40c0941c050720030703054050b000300c030303902a542c5905142100a654802484500040a011a050140c8a031441c10390381c080292820030628008200303039100510b070034901c640c0459882c00c81c0e8410101c920052001c200e050204602c8408484020b501c02040c00c0d40c0307079261001ca54011b0410122003407150300101c101d4042040219403e902d920001029070140c0000010b506c10540c5e1080501800340d0070101c0009031402d0440408081c1c0d0340040c01440c40340a04010410040c1d4001084aa119a9120001e80c640c00c0d0914284d241101c43c0d00038808103050754281520f442815440074184d20404c50440b40e60a0b41e44c828095800c1d815000600000c03030401c00030b03011502503008400000c03800d181a403800900400c0e203400c09a4400400c40d455005914049001d03d001c000d860030700d000407510645541030944c0c2c040c1d585d05c40c6010040620707004c0c803411212104140d0101c076826803c030080f15a1800511 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 124720287 1250 124719037 124719061
    0xf06030105030c010c060231080111190c080711240a0c050102120103030c0b160f0509030c030d0905030606060306060306190803070c0303030e06010302030304061101061d100e090d030e0a0b 83
    0x20b2110508103406070070008289d001402a007903c4043c0c02c407054a840254134101410b00c1d00000710700306000303441e010b00000800310300c0241101805041050070001c102800c008500019001c14082c03403140902180c0b042e00d02e141114135030711075420032801e84211850800e0190080c00100c014041c1742400000502d50000004524544901c1000540f03585403030100310745003c40103150001a6042d4603590301079005034011b10a00e203004044524075080b040019280c000803800960006a42c1542001542001c1201c640c0280c0f040301c14604602e0072002244c601c0c00f0081c06284545a443d103c0808010350010704000b50210100f03807030780c0c5c696604203c0008460351008400003071408140c102402c0000c07031007a060f42d80c0280a10b103030624145c011039019010800048c0913551703540c00010594601041344848840c250311081d01840c1c040340319078030041d9a5200701c0c640811102040b90140c00030030100280300d954100000c540302203104003403400410380c030700a011114400038004c03810a04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 124721537 1250 124720287 124720357
    0xf010c0c09061d0a0905060c0904020c010c03150f032d05032205010806130f0e1006060e030601032d1a01030b160c150e07030807020f06030105030c010c0602 69
    0x700028001c0b03490381304601007181c040d41c00141c000c0e040003000c50300300c060090061500490040026041c1418503601c5400c440c0c3d00707042800844c0d6209001e03c01003103241c1d81071000f000075140d035640d090b11b0b540350442d045001c01204803074105807240340c01d03644200c500030909150704482141e40f2044d00b5820509055101c44141c0750548100900144a40c82450351501c1400e0180425140791800d04100c800360130b40c80c0c215003201c0c0c0c8420381510800f004009141316103619441c04220149405805000000501d020030300a8003c000180049006070580140a500180d000300c5c035800d14107107440492280c8080146508000031051081512030b0f50034034180d901812186c45540c80d403560000304100380d804070034082182d0100c0c1b1000b281c00c40c80d90b2a030302c0b481400d0202d001c1a103150141d081c80070315001101e8580000c64003a06500740f000342981d1000d01034440501d107505080000f980e03503001407105030400166005602c108003182e01030782c0b2090800134651845030910b20030b55201080d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 124722787 1250 124721537 124721579
    0x40f0e070e0609010c0b04020102030c0a1a0109050123040b0406030311060a06120b04020f0d0506090f0606060d09170d02070605131119030c090203061e0f010c0c0906 73
    0x48004920591820404580ca80c3c0e40c1615242a1711409643e4035200d40300041059056010600c0582d2a505082c050845164801e2203100013645044900c0641ea00042c2c111400c0c961a080c014440c02c4000520300348911601c034603a002c42c0c8000c6001402419440003a660450b0405200204264000000010384000c1c88156892645c82c052000e044580901c100c0f0b072020107541410012940c0b40c540545c0050000c2e00e55030100d8a4140855610131903007000b20360781d0348480100003003440c060011000500704480a44442c0c2054000101180640700760303102e40a550b80101c1b030030407400d8402e044010805c441603035182c00c06408100d00a4000c01070a45005040c807000818a10781201d00b0480e1f40c0e8002d002c1d594607041803042c0401420030740c1d480f10301c08104410100200c0c40c400000002428503040169581c504441400568600103181201850060b80100d00a6a94010075048001c0a1074032140b90010703820030b40303644181c66100c0c4200a140410100b1613080ea14400445041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 124724037 1250 124722787 124722797
    0x1401050f01170c18040204080f100908041a0d0905211e0705030c010e01060f050f0904060b0d14010b0120030a030b011101020a110706030c140a05040f0e07 68
    0x1030031000540e02c1c150030700c032040e4580401c000081c4140c0050307809048150a04415400d6030765010703002c14101d90003a00b2082d1654401c000540707140c0c1007003160008200c0340520038400c200355542c0e01c8225001d140036030900e00c0111204070b07100750b00e0032060312a11201c4000600c910540e50030966104c052412186104c03059030804905404041801c03100341614980e210544255004d08110701c80c1c0003068100d6140c0000c20000349101400d000e44800c00c0c1404000003010b61420a07480d002111a90005001d01c00c1d030f0840051665411103035550240c0c0011010404804810009840b010118402050030107540f100140e4407405500c034915080c000e888144100c901ca40d0150203a82c1c079007055800c0c0341d100b086032245962190300b20100400042c1001200501c0740c164803030a80c0c10200740f280001d002c000500c61149010002800144107a0900308190107441d000144410140810a02e1102000584011452060040714018003001c000c107158039840c0c05200c54032031001d507603040000b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 124725287 1250 124724037 124724059
    0x5180d02070b180301140a0213061403040201320c060a060f030f1e05150a0b0303090411070c0605030703061d01330e0102011401060e0904080d140105 66
    0x3400001c140c0c007540d4400d68514240302a4000030b40d2000b0b01031040c150903540714101c02850358004403150340a8282e020300581c03180460294001d4860703050780180100805c03400c4d18506203210808494100c6d030207280203030061500021641c520002a00d50710b007c00414040003003180d403004007610b921460401a0340c09a1201602c4800707588440c011012072541e028020030020300104000c031100c03481000742403004244200d20519423a0240415612034200300385e140319030300e00710300709a510103003800d400c1001c4141e41e80407a6590040600b00c80c01b4030744c1d0301882d040c51810321044e5199150b200804848080c2c035010010300c5604161142c0b008030341041c1010800e40b0010a80c172a80c14049000056540e10b030645000942c8482201c0015002c00240e00c07407441d21701295040e54030800c0ced4561807240340c24003000a0869900b038044001003003081006000300c82c0e0101241d00e22207000c559441854031107060410301c900c0b0302c0422439900751a11003403491903801d4500e454120f94003110010602 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 124726537 1250 124725287 124725313
    0x10203120c2b271101080a06051903031106040c090b030c040e0705180403050a120e0f010209030c010809030304020402030c0d09050601050108071707050c0109060515041b05040b030c0d0518 83
    0x4880f440000a1004a0310f03003180c0f00781c0d4070500700160300072581100030401582c2d400114229210b9107500400c0f40c08244014400c0c1900001424404500a00141403c0ca4992180c80b0f51200710f010700715245440311058021540c0c1000340340d41d40c1d84024410064580343c140803680e01e808d90700c034042c0075842600c164480c01c3d501d01e804a214a4141e116103141111128085504500e0081402e8860359140b42c46105480d04100302d100c0e861442000680d1046d0490800d8580640c0c2d180303d44c1003044203810442c00d54004400e917034002c4c0d8147c402684030f850b183c0f020032041c01400b1030320340b10705e1600348034000380080000d03c03c1c100c1c3c0342038960341042d40395400c085030858284212450b00e0007228000c940214030990041c1501c4135604000250742c8541d0f031b6843d06070380056a0000c03117600c481c11901080e1800d403003425600c141c40c0740b5040b4035400c9014050041c0c05148260300500702c000c00013440c0081c4450480c0c22040c43c00b0700c200400d24280702c80e04509014400d00440511880c41c41c01c03a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 124727787 1250 124726537 124726601
    0x4050402041707170309100c0b0f040b0a02090105070609020a0b0c0a11011d09060f030f030306030d170f190504051b09060d0b0c0f0a020a060b010203120c2b 69
    0x10b0a01c50b413028510f08070200d01849481c146102800080214204039103011074506a82c1b28017585100c1030384a903509003400c040002c0741003c0d001140c10391041003514040c1e038100d004c85e00c01642c08000401c1102c818000580d0b1004942e001e00c1e442ca00008580c02d0348103020451000607031280c145400c41c15104c1004640d000c51700c044801c001c140c52056030030185420b080040c0e01001c0142000d010518090100e82040000d04100601d0b07071001c802d028442c5030070302c144000380d8050314008441d02a5106540142d14020340a41c41c042c41c1da402207420f024030201d9071036400542010134456401c0c11b1030300d50f07030310f1204d40301146c0d60001c030b14040801e80c500f201185000350802401c00030720341419140d180302d0381070250100c1e0b080001080540903005004c409440ba010968000d40044009424410180c1d2a4030324040d045401c10801d507088c11580c0f01003550091000c0424544440d00e410b00344031560500e18060f200d42240840c45544040f10707800103180b852110a0010140341030b0740c101e540c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 124729037 1250 124727787 124727819
    0x22b0f031b0f060509100c030b030618031b0f07060503060f0a2702090306040c06110f030a080402040b0a2606010506070204090819050307030606051201051504050402041707 76
    0x110310b051880d0700801084054022942001d0f16005481c0c2401a511040c801c03508801c0e458400b090b1548840354030303440d00b07002d51582306d1800c01d00456a11214940c0580360b200d0700c1c01e00c1e4003110702442504054101000701c04401c1c4200f0080310380d695260b01c00075103540c10031108a40f00d24a0410800c10381c4c18064542412645c00c00110019003c588080782c3c81111250418040d099081c0943c4006950801040c0c1c0070350702481c0301d03109030790804100400c4242043c1108505a001c0c20761045107030000021030380700c400a40740c020301c030b501da510014002d8803400407001c0d0f109102c494089503030044811102000d00500680740c0c00058a6802c0760307101e003400d1180c1d0740c0c80501800300f82c0250505401203048540304a01310791510195030707150f00f2046508504400060b50100c02c02000d160544101c10103018241049410002c10904034401d415050240074003030b180c8500d1110300c0c80c203194107490281c5801001992516140c00c1c3c0c0f081150032250604c0c0f52740c42480c200041004d51502c0901d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 124730287 1250 124729037 124729043
    0xa020a08212805060105070818120a031b03050d090309060905030d0207030f0215070b0f0c09100c030203270f1005030106050715230901060b07022b0f031b 68
    0x1d6a40d50b900070300c003002482c004220b241804010008000000d1a1100402800c207117101c08049080c1590140300c00170350041c5160030305600461102c40401c2d0440c03803030544090310384030b064500744062408542c103000302940b4007400c0d8200018481016040026031081d10400d0f60b1b20201c10f42d03140d080507620802010f0300300c00350b0401482480400e02d02c0d8280345d9028000741c4100d241140c030580c641c407298030550341600c806010405010b1400309600010f07400c40c1b2146e64550900e6008000100170790500030015040c030044002041c100b60082c01554580304940d8003c0d03020390018102040032401604c401440344c1280007945009282c10031081010aa86603915429603003090740c1035500b94848070041d24000d83c60002c0d0b44580074a80034038a448001540a0351020310203400c200203e01d0094011370444c2d042107403d01180311824180d1f80310b030341c049400ca05080c0c1d01d000c962042407003900c049904078004841031006c1c03140880d8904005071196640702410400d1501280c00d08090321801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 124731537 1250 124730287 124730341
    0x1030e0c010f0318050304060c0b060604031509140303090109020a08060c040513090204020f0409050a0b030c0d060204080d02070e090c06043003030617011b050a020a0821 75
    0x2d665039440b030b42c820040c8405480100d460035a0644603c0c1c6542c00652003000003d204050000070004445201a082003082c0c40c3c1a00f407505603581c84481c5c8d0a80c10400c68915540d10003081482510140c1080c106440070079a0b40d642060284940a0818002c2c186e00405510400155602d40007415a01c42c101c4a0131180c2014101410850b031070300781e840ea2020315512605424050ba03502e10041c0a035440502c0c4941d40e03145001195400c0d102c0042030001d911b403602d80300c0301d0941c8000c540c0740401e48048035003a0840d02d00f03140401c024003c075040304442c2e1061610a242c01900051002d01741d0300484c2d80405c2a50311012490342d9440400c030300301d40200003840200705010400e1641101280d4007030014150310140ca20504428000c03400540c0020b4544a00708412034030140c00540485a00000b03100c07020b009441d20041052810007141001000074a4130305c841e200340700340c0b44030a9010003110340c3d8115a001c514441940c0040c11540d0315641c00115003a02c141000780c0441810781d140c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 124732787 1250 124731537 124731557
    0x2107030804051014010e0603190201030f09170301030506091b01080601031e0b04060f030506061905090903210405150901270b07020106050d0602030604270201030e0c01 74
    0x11103540034090422074240c03050002070f07401d1449500450b4940f040007203c40b60709602d8811004120640501000d020f0b41005081018020311103d80b01c00382a028200800c4849000088200402c90240c0180c1011803000071403d203129240000d40c1200e010704112442c646130302c81a69124104c0143d444c0005130783d016907000e41d500032007829a2086e014100011800c840043c10503035176000c0b4203842641c580d201000a01803800b4441d02b40a0002078400345900790039595140e40c2d4002c05840944100b150076038110604414070040e10242c94082d201c2925403c24681c4259030780c100c124090041d11112513542130b06a503020300f0510640d0000d00900c0850040c181c2c5c01007004010348110b4040d5240e240b071381c1c00c85e12916849080c0240141d085a24140c01c2d0170800325468000e8652011a410101c080000380d840c5d000d03c1d40d540d40c00a80060340c2c0d49440c0e00040c001d0083c003544041e142d2441d0f0400c0300180c1003086d003140e0301d8000c0c1c0f000d0140140030a24503031036844000c0d00e94081040140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 124734037 1250 124732787 124732793
    0x1d0a05090118140906090d020105070e1908070303200604020a0303030c0306050916021b0f060d090204050f0402030606040501150c1716140106060f05091801172107 72
    0x1140070002c003811640000c40711109038805800ca801100c41c1d103c3c03584880140590208100010380280920344000c0189081c0080c00505c91200c001969100305040c10b01d9030000300c4d5001c0d110b0010000581240d5600c0d5682c6000b9051b800d9914000d0160780c80900320100d9150040b5840d4411a40103001d5010325007150380640061159100303072800c0565401e00810f00351101c80d000c6000e001409412001289100c0b4001e15145068600c0c2040f003a1a424100c00744d2900728400c841410111540c40d114080820313090700410b61064040d50050400060101c00c800c2d601c0b2690085000303038162102c81e03032a4070034007003603030000c2c403c0d030001500c03071701f108001c7c00e1080480795141442141d40c6c01c00b40b00c610403280019000016401c0042804081d04000c01c40750a0200c012103100303800074480545091702c0902a9458500184140711001568402940d41c40381c030800f00c032100c94800c00007940c491958003021100300701d0404041c46182805100b60000c07001106107944003c129030718102180d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 124735287 1250 124734037 124734059
    0xf0e01020a0b0703090b09070503010b010201020c0601050d2a03110405040b06060c0723040b01180306020a0905031f11090f0f0402040308070b04020108071e0e01020304151d0a050901 80
    0xc041008041d9a0030545c00000c40c00c5400c2409010500300400c0341900300b00c201401c6841c40340040c1e0542e8030401c22130b03249a0020880b141103071401c441d40c3c9030680240c28250864035600e400c1101a1002e208900c100059210508054034000e0604030b0f2803030604c4091100320b81003660058554110200080c1d02c07440c007000100b00c006001d4041d00c2030b01d96201030001c03224034040e92401e242042e00c040102c00341058803544101460920385884882001220008080c1d582d01002d0700b0103070009843d0384654003404520004103005400c888004c0115064000740d9a80c03414612803460410300c9506d629811031058907211180101900f02030070b50344081180706601180c45d140c0242e0244400400704d030105010300201d500400c400700c81d610345071000600011000f01414240440c040495504054003c1061140002c3e818a0081d45150b0740c0140d246000d140d10a020011003210043c80c283d03841590080214091151000d00191000c02c020b003941b020b000d107503000119140100a440030403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 124736537 1250 124735287 124735291
    0x70b0f070216030309090509030f0301030807060b1c050f010c021b0a0f3b04030503070c020603010b0c01061202030c19030206071a071106070f09080703120f0e01020a0b 74
    0x50040340c540806042004680b94050340c0158045101c61608000d400002d006da11751002510015604e00b81c0380b03145104030fa00041c0009425144003003000c0f0100800360b4003100d042c01c80180401410120041d00768036285a82104841a00a40e400e4078590030050180400711030694016012402080c04210170660301d104178240d20140c103050008100e207441e12a80c000d070444a0754180040c4904840d21426400c219071041c0760b9044041000c68070b00c1103018103800a50628007aa525155200c04540034404444069481000000002070800d0601c00030401310320a98000d0080d10b58440040903c0110800e01030b425803c91130380d24803140f41c00c4c01c80782c10105d4036101c100c1940386c581d00440e1079908080c00840b00c1e0920729031020100c1071138002685e840b803224500f07000c0f843c41c1d00140a441e00806040c85d0280030301046402a814080c406c60009070441800311000315030b4074101030015091407058640803d0b540484001c0c01442000f03007144960b0180c00038a07040c0c44903074411b0015200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 124737787 1250 124736537 124736551
    0x4051b07020409080a02010b0a0605040602060c07060902030f0610060c0b01090507020f12280c020609030f030c0703020a0e010e010b09040e0a050a03030f060e0f04060207080408011a0402070b0f 85
    0x5680741c3d0b04002205400030300859059940002420040d40060000e60b00e0306802a409104d0b0a11040040f9a800650503500c501114000381c4c5800349032609801a01681e503000b54140160b040c01000002c002401601c40c0d1001940714600d1540c4041c00d440890003600d01600c0740c8030140c01440800c0c41500b1064124211384100d80004083e2112181005a44e013001d000400380015601400c8500c0104c0e8140f00c071078618049002041000041d165580c2402c0c0207000c2c8401080141041da03043c80b4481c80340004005580c1d89a00802e002d6445210a00007248980c801103000304080341001d40c418182c40382d202220b003582e400c040121500d40c000076085580584c80302d00b8201c00e82c07414410283c186104400600e84000186405070030355100862903032166240103010800e0a0f0f102c02256003090010100b00c1541e115424900c01922805030041d03c801400680064100d00540c09400203910050515603214064001c100c241c0c420f501011748203e090380b001c030308020b11480c801c03500214 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 124739037 1250 124737787 124737791
    0x10f150e06270f04030f050901053403081806040312050406090f03081e070f050f0d020403080a0807020102070210180e0106020f060105181306200d0b04051b070204 72
    0x80da100e04040803941110301601440c10f510611040503008241074540f0041400d0084c203144000000070194044c580d504200b240d680c24403007035104160307a62440300d05500359958a038403009050151800b9000d03205640f41d0400c200f42d181c0300000c0814880d00460303242e03682d4111061800c8580001e420007400c20b603401a510014030001a0310320b0800b01c0d0381c81c4240c68281a602d0440403200d8501140b1540c000700c1201c5508020341d0aa011144030122a501c0c1082511082c040c62946007a002e004c64030922148000303808001e020844c00a0300381f01c020341d611800c044d501d00300220300340d024100000303400c0442104845106406a10320101c00104004400042c40c0e0b581441e143c140d1081e070054000da001768031106615002030200034003400b1b00f81c4025119169030540b890040314000e103c03400a52040b0241000c106c0d09401860348032010000c2c24504200403000400c80b80d001900400c0c41c0e524040050003141044e0103128481d003d240c01c141ca02c00282c0302c01240581c000c240482c0d0240e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 124740287 1250 124739037 124739089
    0x61d0c040f0603090201030506040911060f0921101418032116020c0d0303020f040902040303020714040e07030204180602040f0e060105040b03010501031a1002010f150e06 75
    0x1140041c00030050240c0d41d808107050f02c040c00090200c0d18040c01140c040d504241d08000412030400a561f061182903503d0740e0307a00c58603030b20400d40740908941e00d80c4c042c40f68040c00c080382404a01204010715248140d4091000c2e00500c041103c0191100a90b81c4bc000700000e000c40314090980d494100c48941034a01d4070295004c01c01c0d0481a40090503031038400c010a0080300704402c4048901c00c903003030000741040d016a100040303200c1480f0000600b0075400180300340ca02d2010b001902c0c01056841da0035034841da140d180103900c843c201e00844000e001c805907186214a403900543d01c90320070100160270f0403030071602800003504800d240d90701c011024090039400600207100901c010403c500007a059036040c00840030184070081c0105042000521050022401940889044500900703000034012611104182c8502d1804109a402141c0c4922030101070303010741143d0714400c0181000c01030070a1400b9540842c440c18010402c4440c001c0000034503e05190f01d0411a5000c0105030201d44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 124741537 1250 124740287 124740299
    0xc031103030a050a061205031206040b030d0512071b03112404050708060601021015090615030c030e0304050409170c1b0307051012090b0709031401061d0c04 69
    0x1540241c418000c0c0c1550b610030003c3d00748545c85000050f041d55020703a0301c0d001540e01c5103030b81d9018841c00e07887da8202c9400841c0c5140c1d16940710042e151009030544462003101d03800500942c019944506034098680e000503100b911070072080f01c4030000050065010000e940741100e00804694030302e9001c0c820a034107080c5d05541244080740d9213a0074010354546150a107041400d0000507801600264803210034403819a801041d060b10a880c0c06034000b6031800104103401030300303800d9842460158a000f101080f0f20360300082d9991007482545040c00140c0a030b180480484000118035100d940062000f80801d00d0b02d5040140082e00460f4240202500300040050f5a4088c008685540e84400310541480383c0c026441110044200c02034001a4035090200d05025803d1107a081040a05200c80072140807560005045c150040340110541c42d00b0710000e001c004641c0400e441c61a41000c290025060501800c800c1e5134582c040303c1d80206074904c000030b82d18809000d01c041e10000740004100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 124742787 1250 124741537 124741543
    0x7030909060b1b0105040201080c03070c080f0909151f0903060f050105100507080307050f1201060207050a08060103050c0d050718052205071e09180501060b0a0206070c0311 76
    0x10700030311060b03550380c3c0203c400494926040ca9090110b00d0b4109002c110150381c00c1010301c1d07440070310520070385d5a0340d0364000c1c101d40300001d41c02c00416100c000301e0042c614100080240c800c268090350b403100a6115202800c18094110040c035502251040086040c9100c1d040714590b0600c050a00340c10480c0c0b6039640c078043e80c900c90a0030b140746582d140104690b01d00008424501000d82c2080c91411b0030316200e0050a03c80100b015043c400002160803003000703001d049031780c44203140d1405062961900c0009440e210644a0350384110b903000b00102d100200414414101ca03032100040541110300da051140140c2c503108280c409005030302c0002614100e00c5240b944051004000040610740f22a500d0000003091031292000c5110b440720f0800510f0006260046d078499200f52000c0000d00217440114036406e421a04d2001e05125503044c0100d8201030b0084000d101d42c0007400000e464680080c03081c00380140100069000402040c00c840c040d04c0c06225481c064130307240c02603600c0360342d009107 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 124744037 1250 124742787 124742789
    0xa02010f1b080703020c091e060a1d010504060602030f090405070c0c09050121030503151f0306091802031507020a0605091b010908100b0f0405040f0c0501030b0108010b0703090906 79
    0x1400b07100040c0b920201035042c410403200b0001103544030720b0b5007084200185071001d4070503030303a02c0380208901180751940c40b4101500146142049802007013040380360301004101c01e12929005500f0207002007900f0b0b00200980e40c0c0c64054042450502c0d581204000140101901e410b09104038981040041052410750714042d02d1a03900c08502d6501d13222498071a581110070500814080c10808000a90300c082180e4200d1900c0800d940304032004400125040c4020442141ca50b000d144080c01554040c3c114104a030728100c3d0408c4507842882801c2c0550703582d00030080d45a0414054100c202c2c08a003c0d480d0024004d1040b00c0c50b40066650381d004440c8180c2c2d24000e10340c0400070302820b42c00c014410101c00d40003031800f035030958a001c810304c1da1440d0001403450416100c1d050550f66464100505500783d00082c0144182c2c2070905004040c000c0e4031106036680301c0e41c1030001c50303154002d02900d107681c18181c2d6002880d13071038080e88010300c0e088420210200069001c0008034440c00b801644 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 124745287 1250 124744037 124744043
    0x50618041b051201050105041d0a06050301150302150c0c0105030c0705010504030c050606040c02060106200601060c031112030a091103070329190207020105041a090f030606030a02010f1b 82
    0x1a5900d21004181c2c03d07040059114030b040000c100000c1c03100203000702c0040042c2d031480841c03003001c1d1201ca1404018040300e070040c603003540c0703001540d5022500e0b10000004980c02a034412109a0021034002528894800241c07919804510030800c10351284005541c0311011245c0141000210303a60785080d81c41c161000e50014204145407000d00c18284626038011000319002c0161803100710b4017a446800510851052041940361800c826030a01380d10741c5d124280c40d05442003907848480140c41c200302000700b5800261440b40c480c001100001c0e03605000018540c1a505642d1005601c1010308004d4000703c2c0d4030092100820015101045400095803142c5043d140701900683d45c80704040380c0d00010700744000e41e80c0500019203204d10050400e04820800076a8561240c001038980d4400c42d401504140c001c5210280741c003074040701400b00350f14215840036008001d08209a034505c4151801d0340d040d0010380700c540c019030007014009814429400c09000c00b0015103000309030007480074425 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 124746537 1250 124745287 124745297
    0xb0405100f051e060d0605060109030206040902030f16020604110f030d080703050a150b0a090b04080601050a0603020306220b12030c010e0a0f060e01111908070306050618041b 77
    0x80001c500d4080079200f85602e81403d03298107444d1100004141404441001d0301c2c082e41c0b4800300d541030b4401c0c1107840146401502c0540d540e42e4511116000394070031580362a104031142c02185004012500d42c01c80381074140d0040505845540b00c2000406040480c9503018a40c03030790903400c644080c4440d40c4827824940741c03040f051418100c05403e60b00300400c818a041c0c41c2200035059000601d08042c15500200c1d242d50b01d40b01d960350180d441d8401a004203c107500302160016030b031140000e280e03050303440a86139001c8083c2c0d180303006d030143c2c0410748155502180ca00f008005080a0702441c01030040c90b0640031030448003100200b0a00f41d6440300245458000042003105007600b4011060240d0340c0b00000d01c802541e40d26402030201e00e95000501c180d48030101e0700c07502d034001d420000c1c01c400212134281d980c07003520348036807a8604030440c00c402042500340011a031038003d00c6400103d980c00303800545007402c90044400c07036203082048998410741e20101c6c07040d035584641a0040304006520740c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 124747787 1250 124746537 124746541
    0x60303030c040e281a091006030b030307050601080d02120a0905010309020406030c06021014070f0503040c0e1602010e07060203030c07020301231f050612130b04050d110105130b0405100f05 83
    0x1e01004c45c8000284c0360f00440120040c40854144420000c2c1160820700c0d0005410040000113030542c0f25a400c0901903219203400414941e0000c50140c410301c03956000c44060955040e40f40b10940034001c00017010510640b0100403a5001380c0102c01441e100404c002180c64aa0351140544039260b00104010380c007030000e0300e605041074810382801e030303031881e050342e1061401802c010404840300b003a203400c018021001c54204501e000c103880161204030090744507403401035910004001c418072150b0040d0300300540c4002103000400ca50040e500c01d98003552a603682c900c08030400b0342c405102280c156607101400c000750030a018140d086c1464a1130741d00b403141440504507101880503214800c40301141c0d0801c110f50b55800c0100c400381152514114072907620101360300c85e1201180030103010f80024400704000c0060116030460384036141d0310f40c100300075416804907003212000c0701d429071080004017400300880e14490700164414410f2048400214503485e079241039a64079040c1d081400e0319030003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 124749037 1250 124747787 124747811
    0x2040e03070b0c03070f0201060305060402210601290306010c14120d0506120304120209040c030f1b0807080a0602030a0b03030406091d1e061c0305070b060303030c040e28 75
    0x1b0144002d000b035840203002845c190340f10251039402c0035100034402e040e604000c140c481c141c105001e5007005140300b074803840d681d282d0380811380d000f4002000074141091310802e108031400d507090305c0c0138072010b03511005250100d646006030300c042c0740c16480701d40c82000800c1d02d940304802c000300060108490040b0346800c100040c04514034807282e6110191308240800e200c00858988000c0c002070b011a4420031545803414407c0442e0016000500013001d07400c80762040c0103410405000801c282d19040c1011036072081020b4032202980141d608a07000b00e080d140201c0e0035900515002000c0c20000980054003400103843e50384660310503804640d0b03508040250108550005001706011004640e6510b000e0041fa4001247d0000100f00c000041c00464000d440e4100c1c281041c10915410844001150501801e079411480c012544c2c151542c000512600303000c41943d004040c00f400040c107150400500c922402001002040c3c1d40706041190f051f008000000a50303090442080022503980c504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 124750287 1250 124749037 124749047
    0x4031422080705010804030f050702011202070b060f040c0504090b0301061e0602150c091905060301120b0a020a0e0904060b03070f0303020d0903020604091116230109020d02040e03070b0c0307 84
    0xc1c0c000c134107001c0a078042001294004096460444840c1b81095640c4100e10058807280103d8011441491004c0344100805c02d14811f2240203c0e81103c021031081d88000c01c01040e602d090020900280040c8810006103401c1d400c01002000018000300d000c03604c0350400c4407403882100031000001c80600b01041503640520411410300c5a4141c0d903036613480d000311a41450b00c00e030740b1164041c001c0c88013110052041c40301d440016080042810791790f0350b5104184200703a4401c0000b510408940d1001c00c1d9072a2180c230840b400d408054071990806c124480402a080e0740c010403e40d40c0790303202d01c070010007950144588006081c240e041081c03045d08605000707250404220781c45e0180000584c0074401b581e1071100f0303202240c044903c003203040c403000820a1640e001d08420b240d03001c12080c4183d02040840b0983d003074017081c9000c0c5a840b05c62045605420703180a014003a41080c07884950301d001d828550400c0c61108414000c0b40c0c5010b089541e118190380088500d181004004028004190f81c48 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 124751537 1250 124750287 124750289
    0x12010509130f030807030e01060b03071103070b0c0318010c0c0c140916020708010905010608011103010b031b1b07081204050924060c0309100512040314220807 70
    0x1160074058080c050381e03040072000070414003405110381d100000f10700c0c0384660450b0020b00500c04c02840341c1c907516604006150403e680c034001003406504022042031000041e44d040035042410f014582d210707021003940540c00900416034415441c2001665880240103044810b07d280d52a510780d4001820140320014440d00710501a1160510001c0542c0d245014103400041c0011004449060b4400503454144d403948404082e500f0504d0603030034840f0640c0320a0440e4040f000138014051640d42c440441d100074050420000e00a0010540c20410380c94420f00076440941ca0f203241440348812100494030009001040d948050001d110340076050001e8400f2041c481c1c01c02c1d05040c24a00010b5201000900790b4020044848221414464103103804241d54805040b29540d000d00d48030450b117a5101d50803090140e01030003402c0a0080c4602c0c101c500c10010482945441d2322140c0d0100c2d00480c50040c0c0407440d85041c051419201103180c00c0b10003d0000c0c00d804203a051800381c0241c145006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 124752787 1250 124751537 124751551
    0x5011b0c1a0108031207020c0d0503040e09010c08070311120a0203040c06030b0f0d020301061d090601060903120e010917010207020a0e070c23070905060306090d0e01030f02070812010509 82
    0x40c0900400c2412000000e0f45d890680400100030207580304d80d0100e20b030804c00302e1659030200346040d0f002c0174040084002c3c41551a204d809007110358844903443e0a840c039498141c0e0004049800242c2828800c2c0d0089420300c84402c0303032600d05202461490709540c820303500c030400c1c194004248000c1101c0300d0740301070090515040511030341e40c070103000510040580312101e000e015560340010441d5821340c1302e0310141005000e608280402d14044260700042100d9200341446140c00200f50a40940c0d0380310100caa1004201a811030310380803c403401c01d455020319051014824000c1000d90008904000200300c1500042c1c4485d41707030040208078101036000012014006090045007580251000c1d18182c1200e45e142800c3d5104c00c01e80f00b224441c0f4140500b43c0100c0e03074040f500404540207240600412812294580c0304c00c12040d8607100e2007208100403416451075514154020741090300703020b4050700014101845c9407203036510fa5001c180c0b128103000b080c000601c5a4a070400c00c0d140c015074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 124754037 1250 124752787 124752833
    0x306061115010504020c030418090c0909050303160e0406140a09060b0304080906120c0a03062408060f0411070c120b04060203040f06090c05030c060c03090d05011b0c 73
    0x1650905890381c04106005007030050303400091940342ca40302041241c00504010305c0d03010003c003201504a00038071500c14102c4095141860000741c030342d00b502401405940010265180da258400c141b4a14500440094240b000c061042117090795140318a00c01000c4e42ea600c1100500340c0403c000b08a42c040d00300c401024a840424060200703081d090740e60083d40900d40c141c0d908a80400603030b0500800c1009140d89081c001001a0072030000c01419182e0283d031014040207848084401007108541c1c20b40012400001b22100d0141c41802d145410440c054180301d41000c0050101d02a10140401c00484003000526001044004810200100440c4464100d040b0090b0740f6041e100c503000e0030141c2034a030080041010b0084041c1200c81203940403004000d0001c1610b4104d860403028803a642c03181c01030320341140050420200321281680000003031443c107100d200422503010b111038010348140d90b9801c4200c0035203805a40e06201c182c05601c503640645610b2400c02000300d00d014180074841 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 124755287 1250 124754037 124754053
    0x801080d080c0702030102040302220606030203060d0209060a170303041b21081215010305060906010e09130206070308010801060501020325020f030601060f080906010806010308070804090c03060611 87
    0x80e8008111504070701c1c400c000c00d43d00d8195000090180c0655080694421007400c550025000703500050390007242ca815060007100d036502d81c15022408200c0e041038220000050140042c54400990303640103900402030360380329844042d4107803200b1075198040540c3d403000050201784144a040140c0440104040b196420f00789a00305003a400c030119080c0d0f89203078105100f0100708205080e9810340c2c0345401c0c582c0c9680341581c00c10151015000c04c0381d011924040104201c0e00303041030418840d1406840701ca005d904104180198017800038039001d10120651842001a69000700810b445802075032005ca030b035414003140c0d6007100c0c002c1d44642e056500800c0030044485104e401480913096600c0c2007100c40126001040b0384610480d00140d1602500002117011500f0003505d546511083d9034098190f51200000c0360b641c40c085c0111041035004c1c0c001000007074142001044a01c1c81801200c1c101650341d2038880941d40803045840100707461b518188100741d84031145d054000788400c010181c078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 124756537 1250 124755287 124755313
    0x30f060501050f03100e040f03030c1d060903010e030c03120106080402090c09031c0206070f05041211153411040e0309130f0e0708030d0513020d050d080108 69
    0x41c40744900c0c03115203c00100005256404008250005002c0409115840d1806140501a185038290120046440d1841030111035118500c00e80002c0d616400900306c1c02d0300710b001c009842d00400e5180d581992174819401003001d0500240400c038641800454a42d07054041c003240440c4140c0025040103008020403016944038699507412402c82d500c480e6a0b03500c1c1402180c18450213103000f4245d820600680790f506070f40080c02d140f00307645581e1807500c46400f827401243c0500c00c5100b4400450442130040021480d488000e88200000030040c95207042d8107044240c0ba07421007104843d042a110301e510b4000380d548040e81035801112400140700081c6030303407002d42e03581c40c02da456406581d840001310300c0c41c8020800c94030b001303000801000d4198118480e00e400303410805080c003030032824950301c1008038600080c00e40548803880081c0d800c0400c0492040c0040c074008090701c4102c803903080010007607243c850300b0343c0c139050051000e05500c08015401401046069028481503400503464085e4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 124757787 1250 124756537 124756547
    0x4051915020d0c03120603121119080f0d0204030c03050102040305060610080a1d1506040f021c0c0302040b0a0f1d01090e04060e030c0307051501300501061401030f060501 75
    0x100551605001800e2605c00c000b070030081041e82c100410500104821154154028015007402c415600894030940720000b418644070f141c8030f074020030018080c4a200b0044400780c0150980c40307443c6c4001820310b55241c552140a602c954015100e130b941c0040c0074000e01806000c1264803510580d4200d50080003210010140c4030000e01c401e0a01e541d554001c0c0b803040310000b04020702410003044803841c014070660241d01d204291403071881689403d124192a914900a407094844040c982d41003042e00c400350b54014104540002c030400d0303820880031840044501c0a444494525511000342020381c8001909510715600c1202d080b44140e54000c1c074aaa1000448068444200d480d0300d0a03100c519080014002030302c60300303c0c0c0d80404240c41c0c1d202c80d80003000d4602580a4400c6607000c40032181440c02c40a02800381314481c80c22400e001c81100041100311550748140c0c0c40740d004082d801d449090840b01d60343c2200c124041c5c8003884d400c0d1980d0501501d4284004080e040090364640800170380 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 124759037 1250 124757787 124757807
    0x8030a051204031707020705010806190605030901060801061203030c0306050a1202152206080906010504022b0c09080325021c030e04051807061404051915020d 70
    0x702400040002a003014400c450750400621200b540c18014100044041e484504a016107400900c015000a13180d151849100307114400084150115904200085805500c02032010400c0d41d01c1e60381c0010401c00034801d140007446460004400314a441c0f500400381d40c142a400300806080c20000d01c00c598a00c460a0300702c0d259421185051031543c40032400402d508142400707a000301241c0c00c0c4221402c13180841c589065940b400d8003060315400c00303451240c1c0035101c5514640c40240140500c0c05e2644c024400440f18804820034060b1098a604075520202980c48a050301d0781d000b410804d800c614084080c00022000c0c6051000d64101e0200130030420501c0a03581007403100c0601035440301d201d030742e0030b1954101007180e81c5455400d0240c0344050403070416004a251000003120350140b41c03080b000e0000c0b010060070310149454011074011004100d810750a54041000160590f10309182880e1561503000341d10300c991501c60500c003400c3c0d5011421040d034008517007015502d50300c004142 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 124760287 1250 124759037 124759057
    0x31605060306040b06040e0601020708060405030a0f050d020a17060103020403031b1b0306021213111306092903060702100509030d020304030c05010c0207050a1a0c030a051308030a05 80
    0x39141d0b0740d648009409411070092158005a0001b4081410800311050a10410707081e000c4a180300d80c0d0381d45c542d0351041c080390060318a8100b40948010300703204440ca142c01e030f581c0e07143c0b85080c00b012a0206040b40e02c81a507034000b04800c165508000704041000c0d56100900f400d003141000d1640c0c50143c51717042584850305036a041c00607208100050168900c0380040b030203480c90700781070f281e00e0140003e40c404000d09200850500000703e4510b00c01d98001c061640c46402c1d4400d051112040c03099100000c84040e18680e102c440c0800c86902a106010309110252040881c1f610301d11280e03144008007064a601035045042088501500000c403404041d0f013403400000e09580300101c0e1803e501030340e08100ba81c82d00000c00d0109041c2d000e0385e030f48420b0b400b50000701b011071140c50050342e5a1015114180c0c1007440d40703204210059105500c8001d4180100080b40b5103030311481c081d030443d40032408001c0422408241e90300c60030000240c2401408040008602c3e0144086e80900305000f108088 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 124761537 1250 124760287 124760299
    0x905060f120f0f032113061503061107110d050c040e0a0201080108030a0f14040b040603060315060305060c070203070f03031e1106060d030e03120d0c021b060a02071d07030605031605 80
    0x1b04140c083c07201c5049105c650090f00c104a024012071000c0400d5203188003d480050608100c3c1542200c000c0803103498550000c00c10100392080005d002c1c80208403482640c050080030014000e80c1c03141c0c00b802c001c080c82d08014021031030080c4005002e514040e000600c2681c802c0c00601741080c5c000501682c44845800c10f01e55800c441004542d4510541d040340001070804600003440542503006801941d204503041440442001c80c1c070402c482c0701e440080c2c29a440400803881c03400c40c0a008046180c0054140c0328001c0d02d80c00000d00300d001507401100003c1c01344603400d411260b02c5058460a2000c1e16051080054200a0654900010782010710901030701341c0c1401054090104111403840140035604880708078800c542031500700034100d455045c00c0c000c6803094640f001c101c103685002840380300c0034000703080c0007488500c5c2c000c2040c040c1584150007010940142440080400704200c152540711403610310402400e859140d80b0841c003a50002036412068440d0061100540d40c040da59 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 124762787 1250 124761537 124761541
    0x609070b091305040224120903130902030601030e0f1005060105030403020c010f05040321030e0703020102070905090c0604031203230403030f0209060c0106090e0a03090905060f120f0f0321 83
    0x2801c032040c58101a81080780d060715401c6c5040c0c1c1e48040e1606440300c099070801c40e0359011103141c4a205000c0b8181001d68222414828603c030303070b070207150040c00c1850001202c07880c0800c2d86141c00c1d2060705d08515540660038105691045010381544070303000780791042c01c43c02c1640d40650b0780d2101301c01060511107001d411002c03040c450b505840040d030700310204124484e03110070890f0f4040c0040010000081c10a082c100d0290000140036045983c103034000d280c0e192405281400820000d80407020b03900906081a42998600300038002442c00b03891010403e070a00c00004d0708840703012130300d1080c0c080307110f0340d84100018590001368040d801d8100801d40b040c0e10b04803c0700034410b000105a01040c007040082013040154043d806584580404000d06458420280d0f17652280040080005c0d4600710103000700e007900d4110a4210b000500b900c880300203d200010b50101c1469410002d41e40a6020b0f02221a400c0082c43d00c07498004010b18a4501e980c03000e0b140340e01a829030038801c0424900 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 124764037 1250 124762787 124762789
    0xb060a0e0112050a0b0a0503241306050702031309060605040e130c0602071d060d1203020c03070b2203050a031d06070201051602030a0909050a0b0d050609070b0913050402 75
    0x90b40c40981081c0360380810541c546444140018401042c6050060580031000300346410009108066010f41101c5510890f1820b0000071100000030f0a03405c1c0404483c40d00d1001800340d0158138018000760700990f48800b0000325803840d81320317281c5c0841070007400e0000400005404c00100c401744c40c04100d00d2100c0d6036074a120000070a00740c074402840100c22050010301c0541c0880c6010540d80744005404207500280032800000205444660744640c0d10f00200c4c3c00141500080d14110700d15043c094242072a28080f2800c54200311400d503132503488107013006202001111008505110101a2450320360140c03001000740c0559070194050503a901ca480304000c0300307000c152240b03c00391402c40e401403078000350090190805581c1880410108440b03420300790b00100907101040029a1004600b524101008000d01405422111041d80d1503c030203e182c0c5828500c184a180942c0083c145810145451031a101041d401007556000c2480494015030f80c90302c221804400c0c00c0404540c03511280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 124765287 1250 124764037 124764047
    0x10c05120a150b0a0f090e01150207090c0302071505130b09070506040b0a0f110303190e03180906010315120c05030a0c140d0b16140c010b03060106030b060a0e01 71
    0x401c1c442c24003100510005002c14a04010b0544046070b9a0340f0450602e00c080640350a020381c01401c2183d14000300600041d002c01101c1a207181c914412100d60350b503145003120807906415021400243c0008612061007050007849020145214040000d440d00048010106d6150440141100d07203500c0400d403c903070100410300c05011300825507030707907969103a45443c3c0780ea00c150800f0021a8800c030741c42c41214014508403503841741c1e81c00607501d0b40e0b44120707503501116481010303450140e07914482c40780701000820280480714046500030501f0104101000f603c0c4500810352070400d4103180001e4410361ba400c102e0f800b12006041c1d101c4a203100ca2905010902c4160091505803160500c268244a82000c0c0441141c0800105000c081050310501032001442900a42000e0342c45010540a036250309112040090310300c0c14104810040c4505d1010303030f008403030103d05a034442c0039061240c070307080c000540100b2503424100842c620141c0410480d01500622800b400b40320489010746900132 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 124766537 1250 124765287 124765301
    0x4031505041515090b03030301050d0b13290f0108071703070f0b01090605030102070305090f030111031303020c0f0a05010810050405100305011d1905030706090b0117010c05120a 78
    0x10b160240a128140c065092248605116484a01d4100700541c149800c001c01140c2c144c07a0f002e05103a40300d0807292205040020054a1707401e050088921800204401280160044031070141d9440c001d03100750881254010301400c00810001c1d01001048030510002e801c40c222000080000e603502c8041c04007504600440e038015004880b0245c0c480200000c4407600c9060b6107404004110341078403102450700f00e006820000f80030400810030840304e0315000d80380c1e5402c40d0004001043c1400c41440300303600340e042900d44087c1880c0680710081050340602070740d41d07154004d0b01c455101d800e5410005043c68524411307036051204c6440850f001d52941505a80075203c0a4024400c508189031004c40d4200c0c98481a01c0a52804048454803500c1c00e1038200d2800c0c100c0020400080c17100e0301d10351403415001c02120180310402802d0b002031480d008080540d402003802650341d40c5080000310341c0d80480034403401e6603403604039101c1002e034011041d164110a0724560000c50341c0c416000780018050 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 124767787 1250 124766537 124766573
    0xe030106090c0302040503100501050109050105090d05010617010e0a0b01270c090317030403091512150501021507140d18120906050f03011206020f1b0d050403150504 73
    0x1800c2c801c0110942540080048610640c01c031040101030042840c2159000c0c0a02c2d400245100701c1080309602c5100507040b01d460050511051242e2581c6107803c4904a500882c0c0c103104420550740110400c0c41134407000030020000d0b00950140e56202c40c10309005000e9403407440c2a13001d400c00002e50703d60f0400802d4100003030070041108082c4018000c0b40c214881104d115440300b200080107200c007030980e4061685074480704146d1f4244500084c0007891034101c04100143c031402c47d012000035001c0c40312900159640d82810702c0c140300009041070001680c0510704040101800115070b4494071035842c4031180360099890f980541058006001c0245043c41200706444025043c4070800300702d000440980c0c0c50f081110b0f0b554440903203403401000d2800301a5030091004000d00b0b00c601d15031001c1184139942c01032919240d0308507102c080d00261910b50b490b50b560b082c0f2200103802005040500d071400c1c201380c0d0525145030f0710980c070600f6540001044988032004a01007040c003505d80700980f04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 124769037 1250 124767787 124767791
    0x10e12030c07082104180f150f030b0a060b0a0f1709011409190213020403080c0607232505253c030204050703092f010e03010609 57
    0x80d44840c07490342c1c0c021035100143c441100c0c0910044c001d03140012142199145a07003440400600351032040141b020140c0d039210720780c0343d084070003494003140502c1001e4180d42c2c1094440c1400c41c100a00703802c2d0005d01c92040703286001c9041c070101d0020004c4c6e5079590501d1400c50781c01064840111112040c65407840e083d07918030000d001b449441900f0031103002280180400b4560b82c2d200005656078401d04004d56980246145d09000d1300b0070180688135001654405031504ea80d994400407264800f81c1e00902980021003807050507540014102e092155142901c180e000e191404501944191400001c50b9034541d80d002c58540c05207002081c00d190014165407400208001801c8500685e00f002d80358292072107008504059580c10445030130b028100785500074443c070400072807841c650380108640c2d04c4d100c80d40000145c1d01c5001e001d109111540d0f01041c0030106150075451169a4821030007551203280b00c031281010302c9100b11343c900c1824a0180c410118110100f07004203000d40008503124 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 124770287 1250 124769037 124769039
    0x4080102030f180109020907030c14180307140a0510020f010507050d200a080705070c0306090c0e06030a0b1f0e0103020a0b040803090402030606040e0406051b0405010e12030c07 78
    0x111882c24518495200703051401c0c540202001c18500300c86800000035888141140850a0684290300c940318407041410300d040c05103ca801c0d4503d160f040703001c810425103071410428803507040c10310800000380f600c00c02844850064000107150700390a400f42074002c1005200c000c5c081e0f40b007044030342d00c0c40b4200c4000304441d0901c04802000c0364410400c2c905043d0800059120700380300c41e8004915040d002c03003010b041c0024000111440c2c1006440c0b1810001e040c080880421400003000c030045214840000d600a00c5141001418085a002d8034112072648100102601d0204105440d542d1020800116550308101c1c1d2100c042c0c561800000d2190140d07000c03030007500245410703050b640222101440326a03240100c0b20300b842540505446600f0512004105013403e8000d590002c400034541030a068031450034440b5081c0458040d500162070b04144007410b0610500c4485007c1c2c56440f1615103400c020020b00700001b0340600e90301a4000e4144080340c40020300c1034801403080c0074240c4d81e003030b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 124771537 1250 124770287 124770301
    0x6020f0d050403030605090c0702030606040510240201270b0402030115030807060f05060d0b0402010e090708151e150f0403210807080c0c010e0106080304090605031b060706020408010203 82
    0x10a617a0281d680280c0c000d801140c10410308600b0307207520344e50060081050781c0e14442400040c26028003001226a002103002c15034000c42407404030844c0c066080e2084500300c0c00c100a09448c510025440302290002c1181a65178030540a0140c090b0030031503008403a102c920219004140e9035080706240c484284011080002c08402072001600030402409290690559030080301d00070b4071107941c001550417a0300005120f0580c20369000c3d0050400306c1c081c584e210040317441e2640840d8050700180001003004180800281c6d4442110402d5900f0f05041d0954a0302c461b580c0d00e01e85451340300d12190240c1c0c0711100046001c98030400d1510f02c1d81074945959207040c609190b10401140a45543d0341c0d100301810b03119900042c4030b003c043d41c03907140c19150060a454240c0c00031551080c107548581c1d202e03216440074040d500082654400542c0d0369441c04805808603106c3c5d400c4148660020240c1e04644a50f6802c62412100216202941d9000030b14281c1c000740301c0c0741d018024a500110400c000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 124772787 1250 124771537 124771541
    0x5070504110406170f0112030e1008061207060807140702100206061302030c0304060c020c0a080706110f0c010305250507030905030a050d050a0306080106030804050a06180306020f0d05040303 84
    0x1155581e807500704085418540308800010220713617181c0042c0041c801000000480d40740d0b403050b140641040f5042c0307008040892000f2002c1145c1c0d0b030100e00400103011039428100c1030f195414902c1c0024000860030144000c00414018101c0f004001c480c4955014902291040391096070f4000c0610508809041010792100d80840c0c009105e0014032100c0b02401308103000b100c4c030420302d075060780780355540700c0c0d990748024480c0b0141502103118a03101d6080607102d80c494000034200c6400244052450300303100604640d540074541d03010707801a24403540350707010000ea29801d585090801242a80c2c6456190182c425298a084042c1c0303481e440004c8056046001401844d00030713a81d6401140d190703c03d2660300d03264080000c010360300240c161148503119001a004480007482d001c514150341c0c862040c2954a9900701b56260080024100403526182400400410050400418440c040e0300361a0b120300039032001070701480d0005a03a0300340c08055800c0715400c01a0130f100300043c0c1064240100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 124774037 1250 124772787 124772789
    0x21b070306090b010e010f0b0f09180109050702030c0a02090705121906060302040b032712090f040e0706080c12090d02010e0303100303030b030109020a0608090706091202010309050705041104 84
    0x101811903c00101c2c3c0d030648010100d05a074801303400d902c501850664a010194030075400c4039203800003400244059901d2034a400f00301900c2d8640c081035541030000e21021100003804050565208010044044101050000c1015011610301c07034180d58409003542e0521400d0140c10703d001c041c10400c16003019000041c0d00d07a59440400300b0900381c48034001d50032403285000750b00004905100080006403e400391141642020740004170242c1401c03001894801c0380384c03441d00b1520021854066900700b10030034852a031030499051110704c0c2d00c1c00404d920f40600b40503043c10000800d0006001c00d500c0d0f02101c103914507203082015207103003603208541c41d440c002d22110019402d04501088040c00042902d00942001300401c5020b40b8540c2c05078001c1a4202016801d55290181c1401694078003640ca0010030b610b4440c08164980481400d0802990b6048001404042841400501c407d001c202c1003295080c01d00081090b483e0801924285481e0f00c600d07801410402088180421400900 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 124775287 1250 124774037 124774043
    0x3211b130608100b07060506030703060e0102090f04020f07030c050a050a061b08040c0521070608040c0902030f04080703110f0d020d02011a190b2a0c03060703021b07030609 76
    0x900940c583c41900e4404000621840040500c248910404200b20754012500880b0050072507141980d25980c0d001940c003004086410f603580403440b04070314140a40c165500c000704460840c0340c20300609000f6410b0184400203003c00c40c00f210540f0800130308200b4551990b4000c01106c001c0c1409141800180c06401d03c1004007040c0d5001c0202d580740211100b5000301d500085180c3ca840c181404c1c8900102c9000941c01d04034000310348603e0340d05007481004058100e075a15806a07140c0350a01a219a80d554488000c0c02d20400411541c03042500300c2d20380041c1c2c401d200342d036038241c030b81000ca07203103209850790780128094500c4000c454007000642042c003c5040d0203840300d81c0508030340bda00300c40a0021003000b0900520081d9001d1908141001c00380c04002e46a10140752074580343c10494100810640207c0009140e41684050700142030030072004020080440f04603c00200e510303588064644001d141d00850340c601e140c3d41000022498000410859181a80d2402c0c16005096141419 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 124776537 1250 124775287 124775297
    0x103080a09080a020a060f0e0a0806010608062d01140a0c020102061e0c03061f050304061409031215100210050708100e15060c0f0c0303211b1306 64
    0xe0700b51020480b4682c0c1d9800800245131240b41030400d81d02e8100c00d50002c801c00c90b64030001d121541e1110340391006054110024040303581444800303080c250001e0310321840307906011701101032014145040c07030b40c109540f01aa41108180c600607603040625505480a9040120710001d0719039005001c070700c0e140c0c000d0342182c80617101d01c00451101d8441d00140850009103000080400009500454010348050408168501d00108a08043c685424040c000450000500c0240226402111040c009586041001d802c0141e5a6580c070302c548000c0112107480740c000030b041c104541502c18000c15015000d94440c041004000f5102d0080d00e090404140c9040c2c0072818013480b034041c00e403043d00900701c80d04003942001c041440313450004021415000d10105200720ba51a0b9001600c2c0c00d00066000304100e006010000b814004900c1c1c850b400380d0300c20b000f800b0344000806154030464191481044868071034110303404180600610742000f01d9400500c0c41d0301c120400001800716039065840c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 124777787 1250 124776537 124776539
    0x4090e0615060f0d0504110402041508010902030106050315030a0506011e080106060503071404091d2512020a03020406060c0209011a030c0c011404030306090c020102190e180103080a09 81
    0x420110f801901e541040708a8240100341000714154040303500a8000d411003020032440d90b00280580c1e0198200080c2005031459044000e0b80040c446405003a0314082581558103115005000f400014031604803082c00801c0c0c0901c3d42c900740500f490160b004030503100c8a43e154a041c078501c1c4002c0b0031000d00c071203034800c000070780c5003040c4168410343e40c0e0b581c0d031149151281402160601102018003914040070040024810302611038048050b1000100010040d000303107200c2d040070ba04078100117001080001500d04510554980010740c4c0706c4161004961030b05002061104805803c001d411521b0001d003c140c80d030b041036209205074421140641641c3c1c847c4000140c034048140803008950080c4045902800040043c0ca4400c12400001400010710301da01009903100340c800b80c1c0480c2e501c1d0014002c1c079195020320003005015000940c98200c8001840840048410107101040750b4103540000742d644822000912291142d01e000055849003451841b642c4100300103c0400c6230124 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 124779037 1250 124777787 124777789
    0x90702010501050328030e1309110f0405060102060412020127021c170f0d020a030506090108070f050603070912060b010206010905190b060408011a0406080c03100c030204090e0615 79
    0x75000781201d40d1403c605c0d40240d43d40e41600d080d20b504090b1a4000d102d140e0304d440d0908548190703c8a10301070108480800940c0d01803114807201510090701507408d00f000c00c080390740c0004880743c11940c0001101c80201c03946404034011319070140d14011803201740030001814100b25180b650207a00850b200c840c4803c000503040010500b00e0001000c1240d25602c80b80744007800c1003d070000c4000c3d03034440b0349420703034030500301e0226408461441c01203030359082032100908150090501604400000300511410907031080504c0103144101407140c81c0020001701c030301e48a86e01f0800108080189054a0840c918000c0e0150052104990040c0f24910000491071542e018841c042c0030b08001c488606440600042d001d800e030003014640203001000b0020b18100240f1451402c1030b031600455120701c21207810001036030900d82c402070300d80c1e0103690307440429600807410454200040394001541c401050042c0d01a000702e034407004865181800c0f98281400204101f489102c420320f41d01c0d44c540040b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 124780287 1250 124779037 124779073
    0x30412020c0604091a190b03060303070204050a140a06210614090d0f1803020d0317101a210907080a12020105060108040c0b07030e0a0f081e15040f020907020105010503 74
    0x1d10025000742c440020003002c87c00030300950708560090b00303503441c2c00200e402080130345000ba6080082665140e2110320007443d0001e159410510280c002d0005d0703440d0001c041c0d00200218503081015168541d00c80400c0819448051003011060102e015880c01a05c80e5448171240b641d144042180f00d07200e00959807003001868981000000390300744203410b58084c00642032250030301310144001c02d0102c642d13504507692400d06c203480c10840b00c4140c030f0800414500c0005100c07804800004281f0404500303011039519010b002030580301e41c0c0300503583e124105103409460b500a0300c0d607018801c1480107004298807180503100c0e05800a100540308d49004441220044070080d02861000c0d505210404d103400003800074600038030b00420356444c0d02d00010311204250380120359510500744100101d040a1001481c0d01200c66268050016251580fa0321140c09180ca6084404110009400c02c0441c06400c41c485e03401038070001e034a10b003000e00680201802c0c040e01d8400d102d0650f071400350013012 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 124781537 1250 124780287 124780309
    0x90302011d070e0c07031715130603020303030a050907030b04050616021b061308060903040303020f071419120303090b01050f0a090b010201020910020102070b010e0606030412020c0604091a 83
    0x3420343c415207944031030b90074080b604840000c800300032103402d8070110402c0d10144140609010b40f104409505500204903403162494000c0421908140c07003003001d43d501206407948014081e03000309290780c4500700ca03030400f58540c000411400d010001c0c0b00911a0024003e48990410902c400c0e50b1a0700004c00c2e81d44911150b1140e44028007500382c409a0304104010301100f0041b16240c0c001c203a22060424108241168008202e5001040c10024960b040001e40c40310791003440600362050a0544c1c3c100307507003030319441c890040002046045005803000500e200815034801c80035500d070100d00c0c00070050b24203840301f41c0301c1c040242c0021802c5e14000c4a501440340004242d40d4860b8680500e08010b00080420203040d03541c01c4c40400d0058441c514103d0f4070b8181c0b0ba0006a9840301450803503003203903060704a1403a540b42e510420010b915154201c0c0e42141c0c0041720008001d03078010049241c911050782403908280c000c100080d580350039800040c4142c910f00c515814489612040c41940329003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 124782787 1250 124781537 124781549
    0x2a0c02040f1e0e100e150c0405060d0b0d080706020c0601152a0206070305130f051018030204020c0d0201180308070c110303040e0702010b030a0c0b0a0302040801090302011d07 77
    0x440b1400007400785240d4456041200141e068814504401c9007240845070b80c01d034030650503040b03050100400b502460301d032917000c10400c0300c1c030381003c0c01c00c0c010031030038040e61440328080c44c0c0d0380f84000403507034509920051040c0d00103032041d80d8120030b2501001035009200c049009104510011508000c103030754840360100155241c003d824608500c0c0d80c2c1e014518506515811a010b4030200542c42c0c2a0040031900c0c002d4440c1580c602501d03007000c240340c075a640112a0310701c00a009001d2a03450054036101ea9406282103290b002c8501c450f07032800003050f400254081d10014500c4041c0e000460201908400740d0020084200b2610894a46403440c1c42c00030f0000b182c000c00a182c0c6406642d2880d1124000d10000902c000c0c4039020901d103034096007165040103410410446010b0382405050648442a000303000400882c1e07956039402c0e00da0340260000c1000100f410a13559110b075056038000c140404c02803000751600c2c28003900070f0074805801c01c410259005a01c4141d6000141c0f4011108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 124784037 1250 124782787 124782821
    0xb0a0f0e09130206071406060907030908030402270709090b01020105060f04021e0d0f05070f0903080d020d0612060b0d0c090902011209110325092a0c02040f 69
    0x610304002201028141c48204d03405001400b9440c040b4140c00d51244040c00a80010146070030410108040c02c013000700789604040c01c20115000262100c4181ca0300164142c074001036407000d6804c007401549181d000c0824041e241800c01001341c3d4410420800c58a200c0010040001c030400128240c038021210503803c031301024041c8945040503802080c00c80076001c0f408941c070384000441d42407a840364030f19214441c0c030b0320088900c00c4190300c03802d900244281010340c140f91803004050800202d612015000341d03804200200385901c6a0103e0f803044d1088541000641d03110380d990001c81512003402c3c0c071020310b030031031a14550502c0b5088441c0b2a421609050b085440c010031500544a8114224100300305030314504940380079401210b01303840c40768088407071400c0010103040c42d00400400b80585600d80740100c0d1881c0b40c801880344140c995005020403201d160b400c0009007100401070010075044444074100c0141da104042c90600c43c800c9400740840e0340c0e066401c0c0c064900100c6071147c01340d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 124785287 1250 124784037 124784041
    0x3080a0e1209010c0b18070905040b0604051510050711030304033521060102190f02030c150a0e0307050a050112110f0d0b0402030405070b0c0a0503040b0a0f0e09 71
    0x1d501e0202038040c0400514140c04462400c0c2e41d1480300d0903054540044204445141070310702d000c2401101c0141410620400c03d40c5410344aa0074000c0d00074281500480c1e40760302240c0d1625414440c1d1410a9000d0188040309404240041565001c082c05407007010056400f44054900402110126a041942240580d4045201d00a00000c15503004030400e8040c0703149921400c00ba0107410410480b6107084038050100d104c404032068010071403411904550002843c4a411595503011950442c12800c6000c5080c404249441c140d0304405600c64400d010a5450307040b0000103002d004030565400c040100c1c0e070401e040d44c810440c010b00d54410001c4c00309201c594810707004842c40001c1c030840454951010603051010340d00142c800f05101d40001030100380c0003914050382881c080103403030452440c90681c175155140c0e01c240c0036804000030700280c106024401007003000303a042d41290a9a03030b03565680981c0ca84642c01040d4840128034100042910305001720115402c004010348810100e13 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 124786537 1250 124785287 124785313
    0xb0702061b010614040c020a0b220b10170706020304031205070606060503100e04020d03030e030d0c1724040b0d05070b09150403050a02090a062103080a0e 68
    0x3508580810550000640e01c0c0c058000c20034002c0c1c60040080302d0304106941c40200134802a1484a14090159400005003074009198041070640c440d404400110412100348082846201d00100c0074201c3c0d599001441a810103a1103201c0c11215070801040c016030b60680b5541d1268128481c802c05600240420404a6070003810740b0302c2e5032020b1070114a800d079036030345880458006400c418000b90001c01004110503038100340c000034001c41d0140820b10318143d80000e800b807404000040426031212005440c502701001030340c0b85000f805200703001429545500a261558903643ca02c03188202c10086045050345099900002d44c1154aa82240c800350042c04040e102d280002c5401c445144000c80c04500b0611624000e020304a003000e581d0b01f62b560403c203503c1604000462514000c010070800079000090a00c4401c0d8140c0c0c100341c09a5540c406031009050740d0f804400107040c00805040145404000c00682601c00c0d1070b00610750701d031401a5800c40c1e059545019550f4400c01d500948 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 124787787 1250 124786537 124786549
    0x606080f0a0f02011b05030c100f0e0a140102090a03060e0105070507030203030a050403090902040914010501050406050a030c030b090405010516020f0c060903101b02010b100e06090406081b04050a05010b0702 91
    0x5120102465081c5d076800369510b8915652002c2402a00364100c0d40040050080310300610031451030b902000d000900d944040162680756084c4014880541918410904c50080d0141c40203180300412150a143e038030700b003031000307490002100d55041d403070700001a0000c0d0041050718583ca805500a41c255981d030f000d52402404080c4c420340a02c156080c0024502203180028805003407401400b2803140c40005500382d4030641a005a8103001c4180014041e2661040540b65404058034000c9050340e0783c104190001e060002c01d0a4101c100c410401052241c15049a4090003c2031990340c140003a440c070403030315070002403410340403608001d90380d40940c90030300054023580100030161024688096031080c203c0d0700000510300c11003c018281e004c910380a100b0401c24040954201529807074090300206036003803000e0301038443c4001244c08083d83d1111f0b44840054440704044031030b4403c543c1880800e42d4030540c48280f00d40e04080c0050183c032198001e0f0b80c1200e0200d0241d9040c10255420070407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 124789037 1250 124787787 124787807
    0x90b07020f0114030a0b1e010c1b05130603021305010b0306010f03020f03040309060f030912052a0601050f04090b04060b011e0810060e090a0c030f05040606080f0a0f0201 75
    0x104000c080c0f5401e4030061458402507004034603902c40001c4107102c02e82803007910203031080c1c086102d20143c0c2041006e40d0f04480714041003680026003003044c120480801ca4124450f40010350815000300c10825081c41e164040011360740200c0d80e17001660000d403845001d07543c0900501030f80d0042440811070b954020104402030320001d007000741c01e040c41c2423090586ca4004650550010709103a900308600b90704066036444803c0580b8050101c9244c6480d581202245075400e081003100010350700420082480407019000c6032601801c03030030701d60003c10598403c001c0c015144103c4a981130702c8254a42481080700450381b202031220b05954944078200100b10705070300ca80c103100060380c020b4116202415072003e104101e441e02400c90822007207024403940582c0001d418881c85e03030000112a560401002e502158038800440c44407070076402240a0710900100c01c10311400c24041c0010080c0a0700440c0549003240211340740c0da000c240c19284d46003080344001c1d02c09105541d0040141d485005101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 124790287 1250 124789037 124789039
    0xe060a020102070f08070c05010c08041a1b07090506040e190206041203030204030b060d0317060a08070602070305150f150609060309250b040e0a0b040507110d090b07020f 75
    0x1420030f5100d40703c0304209a020041212200c0340081e0510800101e940c120010781001e20380711248041950360380e0300912882c003415490007000401c0d00c081c46510b0040700e04903d02e41e10352007040000c2c2e095140d0f80b07044500501e030030300e0f040000064060405100d00980f007a40040108010004504041515607a240043c0e03088101044045040ca4026400c5488140303c1d41e00184c5d03135855818811455840584040d100e400901226000300b42e101d690402c2d4400c2c1500ca40000d91101320006e403c1d21006c1c0e1000c4460f0250b0500050099000b06400b0226405441a100c00c001c4e5104e28000c041d030101c89103a0b840d108c130b00115138001095214034003007210203844186400c2410700000e903190000c44015403503900070080c4c401100e81045800c0d40b5400d5040501003250305145400c50107000d1401040d854050503000141c11165541040444410107041008107003800384004056400f1120912481d104110800d6a41486180b0200071280264445418010b1130380c2080b49000c900d121031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 124791537 1250 124790287 124790291
    0xb03161806120311240a020306130c021e0d02061902071506090f0c0f03020903101d070b04151103130611010b060c06060d0f0503040305060a0b0607030e060a0201 71
    0x2058040620074019849402504d440b002000303c049100c2c0303000032221020107070000d104100c1c0681c0038441200c0c0c5e08410400009600c0e40c0c0e030301010031480c41d00c10748104034040c10f0507600c04000b0b80105403801e00b091200c0d980342c02216044605a0343e044a20945c0c0b0040c0e10410010300c2c94603140400700f807034a20208016160110603100c07030b0032080c0c3d203204541ca02940c0d44401c00401010344104c0102c441c400b07030f040c00030031801f460103000f240404048000340340c0c0016462406075000d00103003040703880340503041040b000d80c180b1011191120781c100702401d210780080031926418660550f0222490190903841d40f000d180c1c001c4401d0641c2100c1c020b600e00c02840003402c0c1c680c03503880083c0540302aa0700d10411030b103080038907425107841010040c01031701c08000c00c0950030310105001e6400b800980b00590401a00c4c41d2601c4402100c401c080d045010115000c001c1000110789a4010094031600780158030600003040b901e4800d1f950014003203503e1041c4c001d1241010000ba01c01440d0034000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 124792787 1250 124791537 124791539
    0x91c0c090e0f010c02031b010902031b120a0501050f0601052d070b1510390209130510060612050406110c0a06050f07091707051003050405010b03161806 67
    0xe0780f42510612001503000d40c1000c101c48881c010254481c000000600009000c01c110700e4001c01e0702d641c2c185003503070410080d0803440250740d01d0b89100344921400203001c6824003d0142002802460140c4a01010388500c3c40030881c1c1d0b61040090396482c000d01c000303030a45014416403c000c2d912043c0210310f81d101d0184000400f0448001c0424420944032507429020800001007040340c0c0c50a80848040c0141d1040310518000101c2104c10003864408240307030100b1f40d191095a52540d203840007980014450304000c807091605811090007481841101d0607820904480d206441542c0501c9000880b401480a6405529000260418081c0d44001440141f0448825030780d40103905040c9290b0040c1d42d01810004944036880c0d008001d801e010645003018100140800d10030b22442e151014400d006811041051000c24002c00000781070006900140d5030180181108840580e90b035480d06a84802c1403c001c07a102c8401c8942040a401032420180c054000c5a8400681c0552076030f1850 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 124794037 1250 124792787 124792813
    0x180d1716020901080607080c0414060f040803040312111c05090a1703120a0621110405010e160c030e04020d0e0f010207050d020a03090311040212040602091c0c090e 72
    0x8505000c4d101c05406000706142162014200e0031016107082e507204405c000400c00090b1007003541543c0d00044030300940c1e4407080040e551071030007150080b1a90780400070b0000b0402600040d544600c0c0442c0c0c5802c0300c0180c0024560f6100c009032981c0803444456030481500c201e00c5480182a4540c1c014035024040e0349500680d0060302025040880d130350720000f25085400c0c3d13802c01c1181c1c42240090b0902041f424040c151810401411b0405070f02031040c00540104106804078106c0d150780617004200a42e0b65000301508401d0990703145104482c0c104100c98814822082c210700181c064481100400109003404004c0d440b15005900307880d503802c001c400140c4280501c6000d04016400980c6424150404c10b09015056030007006640c03010381000300081c0c005543c481100d801c526513403c0e030315080340828081d200f0105280032840c480c0e03081004001c110380c06080700160503503910b500c01003400403503400f59440c0140136040c4110301d031040204116541091040f1184841643c0e2007101c01c107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 124795287 1250 124794037 124794049
    0x8090109050a1e0507090507030b0306060a030f020324010518060306040b0a0f0f0902090f07080a020307140a1d03010207020a090e030f070c05011806170a0e070308180d171602 77
    0x20300000c90240d07d0b101844041c5505008200c1c52103011000707080e8504000b00010020241d5210083c03240030078000140640d901844031014038650800031150702104000741210064090040c1d07482084802071000e0781c1042000d01502c9400060300400c0c460300e403030312a00c0080c20006d14891546840e000030b0060301035540986c0c80e104502030000303c2c01600a06c108480c5007801071410485480340c030201b20b1841d42c0208200e40090306403400503940c0e00c0d0982d007110210700103001d00d03415080004040c50340d9035029140440c400e50700812140303000c4a0808040c01d03846500000b81d40070302c10007018054601e05a110004840304282142d01e0002d2444040d5883c0d0880701c010b076040c4200b16020003065810591541c0546d10401e580c00340c580c101040030300b4a800600a40500c145054001044bc2c0700550261944405820440e10100c0c1c2e41d2400009540c020908609548030000b00f03074000e0b00f000b007402c0100c40c2d4410490340e03030050240c2000f00725400c2035982c04881c20842044002617100c5e5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 124796537 1250 124795287 124795289
    0x1801020913050103060609050c041a1b1606020c0d0222110d050a05011805060a180903030b06031513090807080c0d021209010f02070b03150108090109050a1e0507 71
    0x100c1d002081c81d6156080c0a01140c1d15644050309407402c120800c00c9030a1104104c030f058405028110f6000300700000307072011a0158091000c1020305884413001c5603180010002c0500481c1c54581113120707200c42c0304030b03115403510094580000390321601c02c0041c40d2a0351613a8110500b240b0400e0114120140c01d82641c80c441c4001e00d0b9940001044007030101b282c024558840701071101480294580b10000c2d140c03038142070f1811001980d0301c020480542d40c7e010000010010301e445628030f2898041440f0040030507840c114040b07484d08032004218240401564850040820b1000203100745500388403520400c154110811682d542d03c0500240660300508400c80c040d600c01a01e800e2480d403400c1c034003145c1103d89410355001c4170031a4001140070080b550309007000e107040d08926000c0342d416864040d0759080500c500c5408020002c203840c00c55845c0c2d8004400342c0c3c69100700d840d4032940600b29002010080c1041e00010102130104603204d100181d030800303520f4500c0030301c115521524107054032 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 124797787 1250 124796537 124796569
    0x11e09030c081603020103021c090302031b1207120207080f0102040f05040207170906090405090307060c09030b0403050f07060e060907050f030307020f030109080301060e030601060c050618010209 86
    0x1950005106000d000007441d4080d0001800504107104461a00781c0100010311009040513000a140f103000d861024001001255070001400055010315002e51250003404002e40080d42e6800e0400b0b0000c00001d042c041e2070b86840096280081700e484240c2d42d460b05403446000d40c8035542001400810030825131942c580c00e05c00050312a810070180801000c02030b44054410f038010f00030700c0c3c0842d500f002c001c6403011658611a41c4c072003110002c290b89000d103a104a9205141508101e50140084000e040080c8102001c00c8107804190341a5504040707804040e0941d03100600081c00a8060300007070810407030320f05100b81803c1842d030307d001c290f602c0c2c030b00601d40c0350308203006100711800c00300304035805003802329281164a034a01012030390300c3c000c10f100680304916801283e8000c4d2020b500134000030341c120340d14954943e11480d018105682e0400c105000c5d1103880000154244507140d030000e60380c1d001c1c01500f02e94454001d00300c01e246c07201d01c5540c0f00d554200000c03110750340c60b0305032017401d4a5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 124799037 1250 124797787 124797797
    0x3060f0403030c030b0907110c03010c0302130504060312030b01140309030c0d020f0c1509040608031c0c0801030b060a050a150206160206040b0408070605070e120d090b09011e 77
    0x58907250050a4401c814001000d040c01c10b0041e01483c3e4036080b0700c69115a4504e407120f816a900000f070b62400070395040c4150554603200781c40c821260705400074440b0038030445aa0303501964600038401210014440900310840c1c403000c203050319200350850340b0004070500d401005000a02580c80c650781c01a035071514103a1000401c4032071800d007801703030140700c00560000d0850f200c480021b10fa1110a00040780d0300c030300d0000f42e074420b0103045071054508848018104006150305c0e40ca000b13550341d00a0b00f210340c80d400301d0b25990340746444030302032511140b590780d549101e1a441d40d0b403400b106000242c02254881400c2c81e0101d03041c0c0340c21900a00402c12100100000162010003906103480074111074011419982822512500015802c1e0000e52022103003082e6521824036144074003924070002c00441c10003040c400d8003a405100c02985403411501450a101e048400700e036103005044039540803800902c010003100d007480019002d01e800c103040c10744114071514a0001d8140c0403554403c0400c2d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 124800287 1250 124799037 124799041
    0x90f0312040b1510140c060a15140609040e030d0c0806040c05030c030c0a020a17032e09110d060e15010504030317040809120601030303051605030c0304020103060503060f 75
    0x1030402a60b6030000c03000032481510071010004150202c0804a402043c0100d9244000c54481d1003801c0f1a03417008080152419410b0072500d54004d0050484442d4085840c0d8078003250004024901c940c6445005080798500703100312061002404540088619602091005ea01d0005090091100d0034010750348141062034a18200700442d19050b50180c2040418801c000041d4903080407290030608540945881d5a91131600f04d19000d96418001c180003c002c40350801c054012002d54003411a189840256034104900e260801d01c0e07240c0001c0c0150305980040240e15900c1d800411129032807103141d0b15240307142440c10181d40180d03020007070401010040100850f074015400e07000900c2440d10b540340c45d01c0c40d10018000c4544407425100c988202011800b08000b404c2140c015a00182246165541080036240c0b110310920056001c20f04100c00540c0020b0038241e4008950300c0c64a4181c1076440c1c0c0c2c082410b294000400890606a452602041d1603400704002403003880c0c040c0c6c1503101c0d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 124801537 1250 124800287 124800293
    0xb040203011802010c0602030603070503030d0c0305070e10030c020c0a03051b09070c170d06080d080106020d050a05090a33020a030e0f0315010f0302010e1008010b03090f031204 78
    0x41c2c1c0200b0b41042022080c551140040c0c1e4488000c500442d000040583c403612500d0000b402e0610560040350f01d807000281c400344201c2c017034108000681d040d8504020a6a910310107903400c0095011180d4003020584200050380d000c0da014580ca01100e1040340c0380d500705440032a40350aa00d0304291416400030710700c0b20401944598860010300156040d0341d15040045d0701900d00001000014248048982c001405448900a0342d6116400c90701c00d001440d41d69011a80b42e440061800001904800011074a90300000b00b0544d4680540c6c1c565141c214139400c00c460f580c0240d2200c0358001c8280f08001140c6241d07010500c031100c00151003152820003c00c4100c10303402c12a0f40c01d015500508110381c00302c0d070800494802c0035015541c0f059203840742030009007010700c95050398001070080300000c03a040248100010a50703100703803201a0340300d0f4980d04015141c1340820180000403540001403215810300005590020098402c90b010903941c0c0005c41e080d50000c0b8283c0200206c03000c100414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 124802787 1250 124801537 124801541
    0xc100c210534080a03180b01030210020c03100c0e120327030c10050c01090b100801050f0a020c0a0804120b0c2805040e0907050a08060903160204060902070b04020301 73
    0xa0300da001d5540c2004000c1440680141140742c180140042c000440d0600855001c0d8000404010f289146901c4024840c03a022104c800203000c103030301550000400802c000c0c00040c5ca18400140100240b4410a11404110107000070304403050411035043e03d190455260114901c0b2054001009581c0314610150404003e000d2107039015406000015078464540f0082400b010052080d41c20529001a000060318584a034102454166190a40b028240002c642085003e80f620243c1c01d841d05944003902420f8520a40c1c55410203245030300403e64031030f020350041100d07170110800c1d0780045c3c1464036500c4481d003080d4021010380c0303080c1c01c000082000c03945e40c0310f034802843c0c0c40c00c60500010f5142d01e00e0080740f00c04801509080f1440f0f6620a50044003a50000d2030b100c440b941291810020f42601c0711447d210b858054501010086104030703010500724420030a2400843c1404c42803c00d6180042003041c081e03810980da044d0214903030032580000c000e203a006a80c0381c00f65003040e105140c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 124804037 1250 124802787 124802827
    0x3150a09061b120b0120070e0105030a0305041e050901060302371404080109111009120f060603080313030f0f0207091a030307051b030c100c2105 64
    0x1000c00b440404aa01203400420a44034480e000c10006101015040182c0e01e032a0300c1c116401002d0304030924007145280008103942501c6030002c044240d661ba51b018144d940d00d445000801041041c030091080c5480715100791140e4241c0400c49003515504c80c04140109020b030000800a9000030b4040910300d400e03d640e2b452110620b0f0f42c40980011110f14a103a454040301e0300080003407500300c2d40e030f0316504401600c0241c001100208044031040c43c1c009410940d00c4c1c9003d01490a6216200c0e80758001c3d940d10044818140c801d904c91080741d0307249403400d042d0001c1129020303605c09011000c502c0100240d4469170045812503014015420050540300806040c0e204101030710f4508010a907021804004a402c0f4030340105442c0c4140d10700031100b540602d8401e42500c00410f2038814440300141024013000240046031112200e64207041d02c2d41401048107030000d89411100c2074842c030641900d041d280c007409400700a00840008140e0748101c00c3e00c454000341022a00c2595400d00071203200c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 124805287 1250 124804037 124804061
    0xc06020c010815040b0301110a140304080a080406110409050117160b07050111070606030c0b040311090601030b040c0207151821050d03050a0b1c060b03150a0906 71
    0xc41003503040000c290344001040c50103106888030300780f002a02c07140c0003020304042c010f0007405803600c000c0f0704160a402c01206a8002407015030078122081046080b00d0045400c80032482c608104088203540d1000040d2040f1031180da21501300301323000c40c1040070f030000c2d10a162010906503d09468100c40da12007941781680382c0c05c41f01424441501e88aa0300c030450360520342042d104c004a00f0440e00600842801c0ea14440d00044e01c4402c10a0729800741081e2071041c6803981700d080e16500d440c2101d000b98000204007a030402640e902034604540305030303440700b03052501190100301c44021030290b81640d140e070805030b480410b0602c601d5500c03202c0d185e0101403900c1c05201c4000d41d40025920a03038a84900c40002c40d8144800c40c04e001d8138600c011005401c5421075400d40b08180004000f0324046960400d242d2600f20221624a090048803c5c001203098a40a00a05030349580004001c40303201d855240c0320328010481c42070210a909803081c02e91040001d03440c41076041c400d0585803a03008003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 124806537 1250 124805287 124805293
    0xc020105090c120304030f080405011e1b0602090409150c020118081605070e1b03060102030315120d200a05060f0c040e0c0c0708030f07060e1203040f0c0602 69
    0x86140d060000340902000401c030b0308406403a5050a2103400c602c111b0300090461000c0250a1303082c010b0b43c500034821113400b070ba200c002500c2002002c1c18451032090244000403070080300c1007103402c481c2003000c0380c41d801400d00502d8082940c2c0040c044404018040ba0400408a201c88085034a8810301031107000303d0009000300130001030b00010490081c0c01c0103000520200da84011181c0608203154a158801c01b1103400f02d840307090503807150000301e034007041401070a003400c94149035079400d40e030045206800444c21901c51030282d00c11480c02c08285a00f103840d4411481607140200221080c03158140c84d00441e40701740400d08100c030810464101c149610018461001450015145612004501074101f06850b0107201c1060f512455109004070170101c414000e2001c0010001c0c814120410112803025a4594819441e4018a1850181003c0a00c003800214006270400114001c2e0001940d00b800c80340080e501103a0801d41d400c0d40e420414110b14800c206002c006480500001c1c001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 124807787 1250 124806537 124806541
    0x10090303050906100b0703050304050307020d051b0301090c15031103131506030201020309010c050f160e0f010e01170f060114030d02010615050d1d030a0f050306060f131703030103060c020105 84
    0x11417081c4180743d4000d0810000000140a0150a10540c0c01c1294010000082c0c529a070400c40d40e41c0c545512036030700c48003050401500c036140510451090702c0d030144017001114988204c010f1407110179003105080c1341d00e541001c40c410030214004c44c4540c0010135003244981c46818440880d54072641c140003003910303091042c40580e030000103452442009180181e9400c05510344142014184103004082d4400c1400d4400070040fa030075440c007541d400380c000c5030056a40340c0300005040f800b0321604044641c40c50043c0040b0000d2102d41041003158011036016081c440009840d15009034080c1c90f044074842c0c0b45503160719080c400701081d910540300a010301420200d034055442128040783c0c0500400003481c84140c0055004540449010300100d1051810509920307141d5010b41c2c0c84ca0001070301c03c40014041405001502c0c092100034040034100740c0070403140107447e0f00068111080da0701070000010124100c0000b142c80f4443d10010395203c2d45145019401c2d241c05601c103000390790406007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 124809037 1250 124807787 124807799
    0x20d14040b070b1018061a03360709020904110f0d0515040e0d0818210c0601060306060315030209040f020105250506010f030b0c0a021009030305090610 67
    0x825607010b15000503a074045511400d11044414540d98020b10040c001c0540403a182c000c55841542114819000c6020381c610f40c2c40000c41c0c81c07100311140405002110060200707414001323082210000103484a9443d0f180710480f80e4a001c02c294002c0d003016800103850000740c205401140300001034640110704019001e041c000703080c01565540d650656844000078544980c1e81940300c4160b8025104200041402c2d5075541c980d41054007200218403400c01041940b0841300d85400041c605001074000c4078240c2c0c040c0407943da2800c620100d42c103c14462810f0209040c032a05d402002180c90008540380f41482c081c1c156650203170700c0d0418407001c010400140e210410030650240c1c2c00b003c1100039510f01d1005840a008070303000c00807030b8400c1d1031388250216102d5400e0202d85019008a407501d0b0303681c40f04000030400038000100308481850101d0a40d110400150525445d50700540d0790668494451000712100c408041e0000780e124400d0105440e42408401e401911030001c540d80c260a000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 124810287 1250 124809037 124809059
    0x4030519020d021309031409010f1d0a0e0106080a0507080c0a210605040b0306042414100608070f02030412030504170606030f032104020d020301060303020d1404 71
    0x96254040020494a01001c5540b90703060300c407103590f0081085040f124034002c040010004220100c0c046030021096400404c42c0c3e806988011a0583d03c106c2c4503402d00b501151100c920301c031b01d00d00c90b12403241212182c0e500c40c1400c50243c818180d86c0e0b00e4641c900300700103140d01006402045c11602e800280001594061191039100181d41002540d41c3c50700c10040300d4094030790f0060454038680b0301c509605907110742c110a04580c030440b02800068401f0301019281c40046c0c2d001846070211400d40241124180c0c1c83c8a510b0341040800108225020340349404400e00312000118048158000d008840d00041105e070404c51900e0921640809028065500d12440c01031080c004d03078100e5030404062180049402034180c10181200010442c00582d980c2c1e141990b0b824860b00030494864480e40b0000152149054204002050038030313203840d0f80460f8940680143e1308502130080803405600d09014020082d4842e43c01040400900c200007410f82482c0e54003041c07104020170007000340007014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 124811537 1250 124810287 124810303
    0x1302030115052a010f0c080c03060904020303120c0310080d0909020c01021c0902030705032e06030503070c0906050604080a060f1b050c06133203180a0b040305 70
    0x605001d0f981d0341c2c0600401e07000300a1464218001d101200d202e540400301074000c0c00202c10b40040600c10500d1010040d41e00701d10454405072200803e200003801c0303240904e100d6030498006030540707142195414000e14601011a603240c500c0c800001806440c0c4c0482d801c001c004c14441e00545200039a100008050f58051300c2106134075500030429040c40b4174203604403102d152542d04180194100f00410300041c00d00c08000f41c1c8a4050310300001203a040201e80002e100d640d141c0e281150b0300551b1322242280c1449200741062035503540300407000400c00c00003402000d01468016038840d00d480c4170201580e1980d0010760280c88280302c04c01081d00c2c0051808a440d6002e031003c140304407180e01001c0204640003001e4601e03031064a04102c8580c22078024504640034000303582803546c1c1d0070401a00281420401400e2254107403210440455014805120781880b04603000390f4004101e40b51700d5500718200300080314182c004d1240040c90010301c0c1744014403500d04d2050a1034515124a03880c2c0d958 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 124812787 1250 124811537 124811579
    0x51804200303040f0609080f06130f080f1602090105011d010503042105030103060c050415110c120102040906051008070804110405010e01051314070c02010504050307120213020301 79
    0xc98a851040d03079814000d54024107801c0c20b4005909a590074024a0304840e841985003600030210648060f000108009108003103000e150740d81a40b035070b61008904d8468600940d9407141c1481401d0450b2005001086100c2c11102080080c902c0c0d0300403c00344405c181d1106043c868241c8412031020a2198400e01c2c1c0c050900700700b500c0781e5903824500365010a40c03500d81001d00e00c3d80c0300d0840301900200614181c9001d5941044205d0130424199194800e901490802441c20710200080d1841004007041c1000040d05645402d00c0000128160202a03910b41c089a5000700342400500460300ca07400045c007084481c002400705140000d0302607030014015108010b40400050140041a1101c800802016000300615a55a01c50185c107460078028a0f2103095a00c0005140300142d000700324040c0c0306445a050583c45403042034590502d00d400c103d060100034040014a5501407200e8002040c1001a000364040d0600c10080751031301d0224192103246c4144014881c3c80c590700034111010603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 124814037 1250 124812787 124812833
    0x120e010215101707030b040605090708150103060c05090306070207060e22021b150709143709020702040b061201060c15050901090b0108070311130207050a0b01051804 73
    0x1240680840c1001d620385c2028012045142c00d0200b0412583d01030b512910045058801841d181c40d500c0d0340b1907208070062010b00400310014030100384940d000803022411404c08518021b005c0f80880d09000d41150700c480540c112900030000690415405d2403080c0f02114954099000760207130b90020074581030b00d2440c4590100d01c0d6040034030718280744901c01c0950000c881082e0505d102d2001d00342000c54401e00000c0c0c51040002d108842d11110310b5054030014002d80c40d803d480d8040c070603000c002503500628040e84810104580b0001e1706580301402100b6000742e51100725006010039034078480c01540c02900c08001e034440070502401c0940c155402840e041c4d544c2a0103042c0303d030311000748101e68180a481e25050001c2100154811880b051140071100e180b60303a9014206d07242c0d0803522021700000c00086500c401803510144403010043d038000c00500f0040b07241c80f4140361110012007225800b0300c590040c031581c5880c0d00010b0140088e1400202d0f185041c0da201d425040c0c100f824003a4200c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 124815287 1250 124814037 124814069
    0x1110a0516032709471002010501090e240405070504110306040606050a020a03081902030108061503011e050402010908010c020705040b0613030206070f120e01021510 73
    0x1885400c3d092420a034030b01c1c0d000343c0c410a503000103610b83c00a1041580721860302440c070321a80711100304103070106007016054030352507903038030904008035030300c0c40d52003001044440c2680c03490742e5900000010200315800011158140a12107084070500c50441c0142c0d402a0206990b090b041d80030b1030300700c804011003100d541d11649800e0b4a07000721900800d600c0742c00c211403501c1c4190340c000690712521045800340800c0740d86080603155441141e11040058005000c08008a8000c0c0712241c0c01010b160308070607429002c0b0820038200c0c0c0080e00030340d400707800840c1030000340d0480e00c2c001c10021300100c0003003108000f1000034100c0c00e50500c181c50840d0380c03078000180c103580c05a055a4014611080207020660300100001d4032803505010703441c41940307460349940490601e8400d40d0382d0360941e401405017080c00d40d020800c0b1504407210884542c041d07070a0740400901125440c808100058803901d001554207800a0b0030440c5404c0c03408400c00e13810042081c949843d0030440120f03419118503210390 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 124816537 1250 124815287 124815293
    0x4081b010b03060a0c030c03050c1603110d030227090106030e160f05010201180b07050f07060216170712080c0906040f0e1f0608061206070207060201110a0516 70
    0x94600204802e41c580140720030001e6107204d54000514240b4141d4080208002c54042a0111003040d100600c8050040c4850305055581000d940c007620b01a00380045200085034005151000d4044210000b9030045040e80b42031500024000d08d021401522103100c80c2c0d8000414401001403045004040e1107031540122000305004d000d01c04214454041ca94a884003840c1d40c0ca03107aa44a0540190301e04103a000d000542c620517105c4c0282e0000328241d40d83c07900c8800b11095004401e8002c0311290070012400052038a00c014050f031540b6a80b003102000c500e041000410905541c00a104601082160f00065042031040c0203410769040c01102c0d6220f0002d40c0129001e5868203c2d000340000401090703c5440e081b829040350a1080c03041d94a544412401036280301d4a5003c1d031083c2c1c24010f060104a01848019a2010000d0f1601c01a8a0325071022441c000d02a2120809030304100402e1024603030a029a5042403030041c1201d1a000132010020860300c940440c203807421548204041c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 124817787 1250 124816537 124816541
    0x15131b05060c01050108060c0f0f1e19120203040b04060c0e030106240528030b0409030507210e06070512030903040f05030714060702030a05030a050d1404081b01 71
    0x3900000e00455100d00e05100064020700080c0541d03d2144180b00c0086c00740003800c0c04640c8003074580001507003402c0c00400440c160b90411000da9001e00740340300b000981c031020b01d0068004e2054690200e00d03000e44c5610050020080300100314101c90040007040042076800021942155100784000383d805a8504101c643d4000c0300c030304503815404c0900c00103406410f5080b0152050440d42c018103070410840307040e541441010214815251458001c580920034039070b10000b0640b907400d01041c1c600b0f04000260440b410030108402003180071070080c09205906000b005100301445040003c0d89070400d01a115a01e00c0070614411100050400c04100d030600c02c0c4e803a0059100b00c915104e061094203a03440340c11501940980784ca590500298a1400107103110441d89031550b02c0000280c80400d02c00190312075481a07030913100e2220401c1c00290108010700384810343e41d403a13540303403809038407500300340e420310030340415404041c00a00c00400c96600480b403480311500d01c842e80003a80c2040580c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 124819037 1250 124817787 124817789
    0x105062803020d0e03131e03051207060506010809120705250806100b0f07020f100206070e0316051207080106060801060f020f0d0e060f070f0515131b 66
    0x150184a0840014650340580103403818400c000d03c148135096000b00c60300c0d40da01920701c40180c05004003a00b000803000c2c1050400c0e4004000b8042c3d110242c680c0c80300b07071410401c0d442c45070100900007400c000f0f00099214035600001c091074071082030700303021054a41d10304010310031740c40e4450001464010010b00f0424072100101d024a20b481440f035480f8aa040710701d40b48552100b41c007401d40012030600389007083c07809407504100c0c41d0341440c01412004101d0b81058400300d030010103000c071203030155560b000000520312031503006121520300a20014491001564864007991080100c903140c5007940e071002040d034030161000c071101c1000e030034690b14120707007617002110f5546843c8010417080e510501190603070f0301e59194403d0400d460581240d5a0340440300f0300301d030343d00000e506c00b4001d07228050700751b044038004010702e040c1000318001c000030b0350007180c0446460011100030000c00209100b00007515102ca40e40300b500e841d25242c0c4901140c0d106c0401401400110380d510a00d010b00000c0704 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 124820143 1106 124819037 124819087
    0xe060108091b0d06051006090801060b07021e0a14010e010f17090106082506020c0307030327031a09060601020a080f09030d120b090f010506 62
    0x90241d82e1030b0b50300141e02602c0c410100021031101c0c00f4242c06480c211301101009854040094040b002c0e50303000303030542d90500a0411007041d00105582d106c9405603601c1c3d03204a29400b00d411200c40300410303070b64808200000421a40090300c4e40c200070800a0b20f4221b060701240005640c120100200040062290400c0709900c118201c0001d0b00150500008030b00321340c89070300c40b84c2081c0381035600102042d80803004280001101e801e41008103681d0018143c0c11540c080400c0e12425203000180500c00b000c0c18042c102e5454148102000f0400481c151166440389410040c10060320b04102c0d401c4010404242515408544c0e20b0059105070010091403145640d481c00a411202850502200601c5104002c1c1c0f4284844002043c42e0707034480301107c40540301b10089604980700503009045c6201000340050342c021400b41924030498020340c4600c041c107175440c080c410140d001 = true := by decide +kernel

theorem cover : BRFrame.Cov 124640287 124820143 := by
  have h0 := BRFrame.cov_init 124640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 124640287 ≤ n) (h2 : n < 124820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
