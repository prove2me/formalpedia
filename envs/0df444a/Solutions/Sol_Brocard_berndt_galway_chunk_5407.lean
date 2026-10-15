-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5407
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:12.671126+00:00
-- url     : https://prove2.me/submissions/a5d1d8e8-5f4e-4195-8d03-0e86f0af9fc5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 972302158 ≤ n < 972482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 972303408 1250 972302158 972302173
    0x7050d390c02210a021f080703050705222d2c13021f03060b1801110705040908180402040e04080c07030c1511060606070f030e040f0c020f0105092a03 66
    0x620310715046d03e01d220b5a80c441203a41c440d1015400c5400684012020803c01d2000410040010130341007a032096608551108643d5131403a030408500210305d80c0078106920000d280070070701b682d03206d02c000d098020107505c2181d43c82c1911254034207180240e02d401c60988001420615410001e14031450b8090300200c00c0c0315648018440c020030105503100080e00b81000040c0007440041940c0780d668001c0c0704400000c0c010302c01540c00900c2020404203078080c80c040061155038610980c060140910a01e541c6c0f10798503402d00d040081041c0410307208600c14001806034201907803000ea44164440300d00e07680c51b425100c0d52458100180d0008110410380d80300030880019844101c5107403405c42d2520700c0d10703520f0f101c2950380f5000201d80b000c2d006036060021201044c0c002e03001010081c000d0030441b202c00108000b0406440700342c1001e000c45520303080a40c02d034560401c561000b4181c1c0300002c01481c20400e00d00b58589000320350517a55841c6000d102c11040b560034030a8003604034014122a100d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 972304658 1250 972303408 972303439
    0x607030c030206060a140d0f141e12030103020603090a02220b03070302030d03150906060c030e03061e070201140405060412080f07050d390c02210a02 66
    0x20004804001c03401802040041481800c0002d070510a0b1800e4003040d03d40f51a85500f40f1004200b0803400303a481095040c0000d0100314a4030354007244078105800340c140815000c1c5140b21107114040c8400c001ea20130414500c0400218043c1c0c0e05495040365407540c0c2c1c0d02c40413070291070610500c2c0003030762024204a00107900380c4285000000550007941c144961201102099203c01c010310011f5056000300c5403050300e03035210758081c81030200a41c201c0c0842d070340c03201d0380781d412030b011030b000613005c94414040c4c0024960000410404140100c00801c1f6515100d1002c6900803010740d00340704001415004125698000e4111040c8025400300100962805080c0141d4840050b1000d698844202070413080070740c82031010f0380c172800002b00340ca2029280c228080391305034840445000c00703903607400c020002a601c01869001002d10865200e00100700c2c444001e03d4024042500001d00004500e41c40060b264204503061035031840a803502026120310b04c00303060690310300b0001d52028942c82180701c0d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 972305908 1250 972304658 972304667
    0x41401050c161806030206041208041502100f05070c15110a08011a120f040302120f0c0709021e03060301150e0403030e0c0f0f1302030c0a1209020d0f11060703 70
    0xb15038483c000c00c3c20080000f51510f04544d958000a50440801c0005000800c41060181503151060000070b140560b544807890b201d0602e805490012f03080311500c0c1c0e400141c9030265042450726004108410b040007407010b800c0034101140186807008100c01c0703c0306c81e0400da009080450b0a5800740303035130345609040104403003000d014807a2120294054446203602480541d420001105100038140e150a034a02d07000c04401032089003103104d20301008601c40042c10107030524002054866442c0c0814002c820306107882504030024084c0705006154140e81c00c00115400c0e0060100c8255594440e83d000c2809407501c030030408071402c030640c03001595841c090505031045000b40c0c1c0c01c202500c40e264840c0c0c0c944003281601035000740040403041040c905804a0140403000800700c0041e040c0007d42071040c1c0c0c06c00c031903140c44144c01140c2000815049540e10008a5001030100002d000c42e500181c2004940400a000c400140d0b040308104940c442d0222002c550040084ad21102d0310300c0d0061 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 972307158 1250 972305908 972305953
    0xe010e030c070b041518081905010e010c0801120618050f150114100c1416080a020303030c0a0c05030f1c050609160c0602030f1515041401050c 63
    0x20760301c10071000280b004054400e480c1920403102003c1001c002c03804085890fa501000d12440030b07200d8a400013004030041090390040c1c044108010038081c1c2504000d801c440d421208030440703906180001d02840c2d0701c5400c1c241594403000b44860507030043d0410500600c035103001410660141d00103882403100000d410307050322044a003140c481c010b6640171603004080a21a188412511040300c09052410310754407040400da03407504020f203090b2910f40c0f204610b103143c42c81125030001c00c048451002200421b45c0584040f030010301c580d1050b036001c25524400140f8400700148081221004a403044aa200e0368032381050850307403280b84503041c0c1507060380604400700201490035100f0070300c904940185403103008002d040c1803a07640d0300d66170498030f05a00c1c01d0f10000c00c1402c1c6060030014072140301841c01002410340c01740b9549002c5071817084545003003498510402d40302100c031060801c0441218280c1f0749c0060700e20f40a41030a00140d03502d0080018004640c020314400401100304088100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 972308408 1250 972307158 972307177
    0x130e01090b2a07030f0e1c0b0a111b0c09160305070e0319020a090609050906061f0f02070f06170622150e040c150503070f080a0e010e03 60
    0x44090044960032a42510711607a10340702c000390502c62000460300079401c00000840c00c2c20815802c40c40c040000703c4c078040ea002c0d4480c007280d00341010f900b44515002d80036801040c0308800c200860700317032150345007501565188690284102d504e134030b145102800440c2500e070014100000a080c01c80740e4444041d14003034090300003031030400081c1035140300e00301382c041c0e0000140c042c2c1143c0d1b4505102c00f14168101c1000e03078104034055400a0f464509200d07a10007000000700014850505c1d012150034064040c0c1264414034000300a03400d508a05400300032210824180f0500808500078242e0408085520903a004a00031380001807164208194410b583c000358140ea2880d610b180402244444000682040c000324001c008001c600750b03032140741c85014141600364074540c0c480302c810361040111001c5078031100d5407104011300400908140c0502c4c050703041603800e52901030002031031020410800b000301304607c404a100ca01240e80105058802a0024407014482800460781c83e032100218 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 972309658 1250 972308408 972308431
    0xa061d03101b0206070e010e040f0e06150a141c0f0203190203010b030718020f272b080702010e0a0e07020d03051b130806040507050a0b120402130e01090b 68
    0x900a90f116141c1206c1c0c0ca50142c541c0c00f81d15040d2030a110007014035660001c5c210f907a954200d250600200002c91041041003030b019180703000e030f5090003030130000c070743c004800c01512070702c000c89075564191842142074032191001d94404840c102421000558000603406004118003200b184903040e040030b02c818001e4009025040c001014965540d8041c410611061070070401d61070020360640040c4440d45640300d140b420001080c14010703074070310b9039035040907a0302c03c0c05005541410400f1800104081b00060b07003803840724000e0386001c4030f10070b210001c0040741c001910004580c011140492400c5003e000915903d895981c24100594146c6007070303001d481040e03007030100c0300e11a008561083c90134509540801d80071181d0440b09030003a08004094030480031020405030001c000e264452801480289a85450071084c080e43c812660019020010300f04030b0030680b40c842c8030703405400c42d90585800000c50928a2054020401e040314017002c0e50800c04440305210200f0941806000f8a004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 972310908 1250 972309658 972309661
    0x1e0f0605070606140d080c0724020d05030408070b06010306030b04050f0c030c1f0c0203030a0807030c0903051c032309060a050702060708060105070c0e0a0b0a061d03101b0206 77
    0x80104004e441c6041d00d03038007100783e00b18500081e4858020304404903030b0700222003503651500c0d60540240045000c03440a00182205a40c8441e810040c0c50815611410500e1450030103880d0000c0c0d81c421201e000d40180c5030704000c6002a4401e601440c025508104a00028185880c00c06d80303030b9041046401c05d45c0310364a90a80c982ca004680e0455140c801000a035244010050304444080452010828080144103200141c1c4081c401003a0300401c5988030b951303901c1d0004014040790401c41c00ca0301040307401c3c0e00502c00983c0004e000002c40c05880b400d4405403040c071404501501e8030f0503507285200300301c0400b101d4900c51003410700e000c0c80124041da803c0b0f5448a00c100e0840d0400c0703610900590000c00402c107402e02950720160488010b00d000c40c0341c050710703480b143e40c00c0c0d41d40c2c0e00400c650003040080001a00e45031083c01d801040c1182c480300c0703840c81e006000b82081e100f005010031540d161180460140c0e420840c1d4100300215070424005a80642400a0305284040744000540a07560 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 972312158 1250 972310908 972310919
    0x34090b03060708010f090513051c0306080c09040602030a1512021c0507030f050321011503050907050402130e0403080403200d03020a020f2b021203011e0f0605070606 73
    0xc221906075a81a0b04910318240346c500ea00001d00006040b101d03988080c034521034041030f0113114400107040340f80180011100c22200060454880d60300c500c4290b04008401d40b5165038501240d81c00982103100076071291100d100c00383c028040e110341800d40007c043c1000841c0b2000300d840c000c80c40d0003251030040545801c8d0703c52a482c0070b140001000e03034000000c2030000a012050001c1614081c2c1e0850741020000c24951108800d0f5060380b0082004060041098030703114610700a000038149414440c0d800c2c82a00316a035190503000701440307a43c0201c2e590081d0184115544002c00140110070300f54201414042c00d010307004e40302070380003420b6001840004852100c02c418900b140100406c1802608402180250000d04c000c2c411802504000400201c0c1008088a011030710825884000700d0707043c085465851280094003950424040c51007080180703029281110207101c01c0350306050443c0f41100f81582d094001c41011a0a40310202d800c41e8004098a02039100b0300c410880b664884 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 972313408 1250 972312158 972312167
    0x1415011e050a0302041e0e010501030605090a03170c121509010f140f1201090c1502211605070618060804120309170a0c020f0d020334090b030607 64
    0x203000e2150400102c0c1c0e01000141080e80c029032a004018015051006404001d0402d440f5100072510050391114018401d0000714400c0c0c58200c401c807402014402c00c19a8054403668883c00441200390380e00000071340301c40284003101c0c82d0031045a400c0580340f401c400e01c1c2e60b02e4260500d209000d0803400340040380501010f0090340544042103040c4601803107000c00c000c600700201e54140c0c0c10000c22003511411120034014440c08070b200e0001d6030701e800c1c18032803404101078014003540119030003044099080981007070041c02e406031142c1490b0780c0303180f0001c580700b4001d0040300041484c8500000001d80950000c04108005d03641c8902c031705451350380d2204540e00755058034003400381d42e000000e41d02014000d41c00340c83c126214686034440710026120700300e5190070508000001c51a5080e4031011840d042d0b401404550049510404804654000c039030f0307038030081480700c00001401802003030920350035000140c80c2c26500da0f0310b501d6580318242e0501405403c42514000d11903400425011800b8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 972314658 1250 972313408 972313469
    0x140406150b21060a0b07060b0d06020703020c0301050703060b0403151b210614090402131107020135150907050912010c0e0415120c1505120f04141501 66
    0x945d0039050500f0456220745000f0000d000400b03902c65141c019120001d0360303130300280082a000e50003414041401009160030343e0402004c00f0105868500305101402001d0b09036401e8139000410111460543d0540300c00411202d0810780c40040a480600003084c0d1000e03840b000c80c50803841d03501c00099240200400d0318070714000c0c0c454003501e000d121411814481c4180303610600081011a01d0a4145c00369002c903521080d01c940024800140d1500b596048429220307408003094841421955040d0705807082c0c02180001084480800e010a5418207841002d0700200c00c01412110f850a1901740900301f0340c40055998000c642018640550070b40c18450b070154250b460b154030f001c1200010030040180703080b404410504601c00350100e8002100301d5864162032061021700d00d1542400c0c00ac2c1c0d100c580e0442c00c2410044201f0215005007031091032a5082130406181e10b0541e2030f41e280101d400841110180d5940c45240c0510304c180c204003c0081c103d84020000050300040d142c24080f49010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 972315908 1250 972314658 972314669
    0x60228200c010c110a140f1e0d0f06020f0d0509012a030204030c090e0c09221505091c110322120305040f0504140406150b21060a 57
    0x4407a101000a500030002e20040758811104002c9414000001034011105070304102540c4125800c0003480341032001840c0309881040f2011610a1000d10002044030b005256a50140900030005820030248c090201d460070350005056403a04416011501d4a8016590704450242404c0204800c040d0611825042001591420140e280a803d1200b0540e07046082d030410036908000000c00300302c4132542c00c4050b010056010644c0303110f1407001803804140c0f60405214040040c18001004960703c18000d5402580e400850810041c0c200702d5141600c04000800d81400d0600300f010440c00442e03240c031002c0c29518141d050041c2440101d80c0c1030250101001e441c0c2c01005204d003d00540b40b001d9460801c0d81c03507130202203038844114441c2a079803220200c01089010509010b08600d00c400a00a08030540d401c000c01d624031110341c1d0100c3c0002c0c101804903070b03684d1310010300c1c1045149480050100f80301d000b9034038101b4192100e4006886c660304d459403840031011450034501440d50004884 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 972317158 1250 972315908 972315913
    0x304032a0b1b0c030f060f100f1a041517160e0411250515220f020616060509010b06072009180105061f050706022820 52
    0x1c2c440e801030b2019a029684200703070f125820a45070107075070030804200d03030040c2040a008030f410010985000414058841840c080801105100c0c11a082da8540c04407000b003e2003140452001d9800704d110b201d1a0018028064006040c11f242900200d070840c48070403042030105c1e90b03a00d0f0311a941640904402c0d002c00524401d0401c10720385030a801020b1081c00701428103140c00a9941c0003100c4402041c6e1b2005202c28810066092003014000c00c00104e81103c48190140742101281e00d5803000c05d510360216040d030080a8041c41032240303014505540c040d20903603840948103c003d038845509081150203074100f10000300501c03c1070013080d0320103e000e000705040103102d64840c00129504840910788803403401c0c03550201d541d00c41a5a0151102003441c0c0203e542003c2d100b400e495008090380d004072644284107a01000c01850003440262500c0c220703884600c80c0c03802c1c00207480399005554008a440c0c480b82141036400b0256901034201d9101d021104050b0901c00011303910304070702178802d034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 972318408 1250 972317158 972317167
    0x120f1b12271c0306181e054c090b0105040e1b1c0c1220130b0c010b0405010501180b0a030605030307030201060f0b04030213020f0403050304032a0b 65
    0x82c41004076011880a0902180964850450022404068011a000ca82c907941d515200c01c52105c0c0a441160035400144210324000603141910300c5401c0401c2c0c00c8106143c20710301d03071112000130720302c0e05584075140303c4085410315800d400b0f000742d90241c0c20603545030001e01c3d69158043d508883c1140d0f50640d80d44950703035850042d640300e040401c00d000080c550402c604604849590041c144044000388001340040250400604498a81c0d030260340c40c525280c1c1c18003024a03282d995148511407080d290340e9510144000c0d07021208540c0c0000440100401e102d8244c500c1074100c1602200d081e1020082d582ea540011100a14181c2d0b40c0008800040c0c010310203240c40c04c00809101062b82404030340b036643c0d076002ca891544801c10540c0141d5640c01d0034000507504402c0700b4010110140d140d4200340c2075400140314608614071103240c0943c00100007420112f0002610011500801138a403116502d0420040748051691060700400d08002c004490a01400340d103010354401220440c00d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 972319658 1250 972318408 972318433
    0x30a0e060306120d0c06060b0301060c1202010209212401090b0301020f040b1305060307140d1b0f030606020d0504050103020c0a170c12120f1b1227 65
    0x25648080d1120390060200003a602c400710080041040148465172150b103655140c0c100002101d44540002000d1001080100070440e030000302403140300c2c0c11501c0088c84448a910590080c402c213001560040d1001500d1003204004200020b0411710050903521600703c2c407400c0d200c0000303a60f00d90310b180341c0151005100c0381000e90b010b682c4000c005000140707010480400000749400030761040c00301a40018448505187c80d504100041c6000c3d14004d040d400c00e00c0d0003070240742c02440540c0d01024081040f81e01d40c403194020305581300d03080c8003008035411036000041c64000d600804a000c01c1c200007000482c9403001815111404643d41c8460a1504180c0114041d40c04400040014440d01c0101000700d41c448009003942800c0000e0280d807030030840c105600b001d498030700c0040305070310520140c01c0001d00040429031000c01d203001e844e00c50b80e403c02c40034417449000300340c04030042d4003043c44403610700300f8880c2c580a62541d0485194204031658403022140c42c16003220980d82044851500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 972320908 1250 972319658 972319669
    0x1c170d0b040c08220b0f0910060303050a1d04090501090209010e0402060403060c120f021801020604080d151701230421030605031204051801150f1e020d0908030a0e 72
    0x30840d40c86010b5059007441e85e150302d04058800d55001d0544242001400203403201040281e5518903403050070b10806146440c007400c0c5004002c4100c040c00f440a03180f4a00b428041c4a0340c803d400002c10412008506050007070082c8404da80803030003120078000100d0154140b02250380314980c0104694540303800d60381d600b0f02403e80c070100203040c09415945800100b0b464000d83c4c4610765403450050b100c080302c1401c01d418410707100740581550006020710010440c02400c455800302c40050100f09020360042c0500302c840703140e12400c0d4401c034441011000300019000b1000c1d8203c5451042d040c60320556410400850030f4800074000710841066052400d8910f5081c00004007500f0f001910568403000300782042ca1348004520300c0751000505011926044822184152041c02c1c0d040842d070404002003030f03448404203600184824223840e132060910590303060306d04125200c40030590010f407020203503881048a0925002ca007503030f407011411403c00010f90302d010310a985d40300e5442424006220 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 972322158 1250 972320908 972320941
    0x409090515091902040f09020d38010329040b10170303060f040b0a0806010f090b0102030d090606030f080306030706050c190212011b02010c1404051c170d0b040c08 72
    0x3c06c40d50302d400c07000000d0303130391140d416440074059014041d40f48540f1508c01402e590140542d0800c00000501d0340c42c20f550024040d042d01e50001d2049004140c0c030b81d0400310000c001040c3d4a042c040702e0100705c01c00c84200481c0e802001005500d65603c1d450700351090b80540013982100076a4000d00c0020b0300b80c074002c6402ca03000c03030003c1c100045100701c001c08191000a2078106003a0f0384e00c414010440103032081c07c407800600e45d0003001c100c40885040000e442e0321075404101465520790340a5030501580794070004c01190710402c21044071242c0d24200019800172940745110380580c3d8000030b605400b07441211840043d00001c2e15910040191043c180074040205030b0300429048207180d10106d091145824070b01440c82270358079030f1100c6000242501c0540d0101c02c100002e0620f14a40c000030442942e041c0c0340121114065414101020700c0c5410005d000a0810343c00b02025031680300164008180c000080d690900c0340c104104107000036507011021107400124107100003030301213040c410900c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 972323408 1250 972322158 972322181
    0x60e0d03050d0932011109060f120a0603030e010207030213150e070509033a0c150501090623010804050a050a030905100c031202030c040909051509190204 68
    0x9044000c0e0303c6900b807a29005401544c1e540108403070a22000084150440f00c00b40d22000344964500740040100034001c02c00301c503004800200341c0c00405074040082c1c454030ad41d5180030034480c2c40d000c5041d0b006445a440f056010403844000c0b0100e82d440800c000c41540d0300a03110030004403682c10648011324000b840102c0300b50008002040d0309041c2c50081b8040d1302c4954480340c890f05031004140c1090690f40d041c29030b00c03007105401041a090043c04613241c0d0f0044805841c804011042500d0035840e019004145040c08032a4032000c3c1e00e1940201d0585e5000d03282040601d841e044850300283d20444405640140b480a007141907100340c00c4030750321921410503903481740c1a59950707529100880a04401192041005002c9030410038400110f444030b91402c0c500d0480141c402400c1c00041d40c03554182d040e00000021060418030003180d00400f4860300803c4085007034203086845180c1303002c69035111214080407521101300024011443e0105000800070040a6401c2100038074030310040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 972324658 1250 972323408 972323411
    0x100302130b06030c0c1c120911060307120507020106211a090102030402040b04091e0809060a02100e0723040605040218041104080a0f05010603050d0c0507060e0d03050d 74
    0x308411034503600d015500980c02031308481c0d141c00a2490150034500101049049021082c80c1c40e00d4a5600820511942c03000c80da001994265038207110300c80210904100da0402c000009000340d580d80400000065011a070042166481d0880c04a0980f0064418054035100b0b1115280300750720740140006150744158a6410021583d40000090600448007514142d5000c01008150b041900400c40000300031a0304128101c0542c0d04d028140d054140406000c0c007410315034608100d600030454082c0c540041031941ca910300e624000307540d00401041c45904d83d0502c02c0303082100000180150640780c56544030341c403542400d0000d0340b03001c482c0825983d01940f6000009001e40b618401805050620150600140004000d01040d11021580e407045100c04010400a09030041075442000d0390041d0300c06040402400c00074050650758101602a00440d00c0b103a00c09908080403a400d03034030a40a444901e59103d409803514030440d01605e4000e03008548000000e48981d008210000380d5940 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 972325908 1250 972324658 972324671
    0x308010918060213120c0e130803190f110706110c060f0a090c031109071403011202010e030708010e0610080304120302030c0111130f12022b2910030213 67
    0x1911030090f40760341810f686e040380c240e00c1440303581c503000310f820b9002c0c592054a59000303040e41c1c0d40800600c0000c03c600342281c1d0b10b11072095484c955800c850142c0d004541c0074800070300400000e001591080354103c1d40d552402010b80c6551218000380e0380000031031b0015102c40d42d103004d42d0844511008040704402a5107440e1140013544111907040a1401040303100c0d072401c55103040c005248405800001886000c1c0080c80440d13221504807415100d01e407103002411501480103903002944401d040d64103008214000c100420305500000c1418261804c4401c82d442d19240284049850b0159002c01e420401c4140040300403011000912031081c4100ea10b06850000d51900712034001c13403e600907080004000100b2030b00d03220060003170000021003203401450701d403030103203da0b1008600178083c40d8040c014080340000400014075404054003404150103561921040e049200b03030090840102040e45280b030b4110180f100d510440655005041c05801c540800003c1000038044641850321100c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 972327158 1250 972325908 972325919
    0x70201030e0a0c030c0e010b091f020a1a07201c09121103010f0b010203041202060c0d020c100504231201020d06050315060a170313120308010918060213 67
    0xd030034004c0d40504400303c502405c041092404081c180e010340540300090008500a0752408a5450411000c00108a0f00c68170a81e040c0c0c00c00d42c103213801424101414002c07401030400403400380d20a4056648220180c0d00141d14001d4032041c0405030380c025801142c0702c0c01c4600f01c10001c00c2d12082103050224034a50b41d80d0005050200c4e8075401c0380d07040b207600c8013821141400d00403050070704001c41050250400303400000350f41e4081c5101d101e4101940325814011f42d00e8520442d00382040b008150761030500003c3d07000e9954851880c100b40240b6440030050a5140308605480c00e03140c50f00001490b401100503c4500440c0010515900007800e440c000500304c0241b006003140003500c1c4007c1506031030a003c1600b0720781386401c0e0300d41d10b07034180c010416a0758a00840b4800d83e034801030342c94020740a45504609d14000d80d203c540504c00341d80c401164001405124445140c072a0f40e4082043c1e1301c882104059032180e442d4410f01e114075003401c00000d03810741c000c1d052190078004105005560341c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 972328408 1250 972327158 972327173
    0x40816020310020a0c0b070f02120310050d0506040312020708030a0914060726010e06100905090a0207140109030e0d05150c040816050a050f0612190b01030908070201030e0a 76
    0x10413213404544007a9a55080128081c401030744408a030400e82c036820300e020780194441490300c01c0007201d5000080010310088819140002920000e0702801d203981003850300540c2d400e0151015000f2840d10f28500340d4840c0c0314000c5903107880d031040c4040d08507214149030340003500f56034504840300390850240e003031001740411a01d44a1041555001c190901c500c0c4d064030310701302c10802070b442e030120a001404058901c036000c540115040d120354802e42d6130810b04541164a68100640c00f240d41c40034410648900d0300641417840c0100c850840c04402482502c0c00c03030340150740080c00304420048041c074601e400800041b083d07000c1c0050310740e4190244102100500221901603040d0303c007140034014410104918601070010320206011282008005402510548107640c821440c5040e0030b803c60301c0756400d6901004000140403402d06242590642c0c5138210032000307060070f2901180c0b214562090251800c080d0304124030a1421296030011005002c07449140d1049100e01c100707600008014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 972329658 1250 972328408 972328417
    0xc1701030c030f080d2d05090a0f031704060f0c020a0c032a03050703031b05060c030601110618160b030a0209040e0f0a12031b230703050903100504081602031002 71
    0x742001041c403100103400c04215001d0451311b02002c4c909000c0201d1100e000500d125455007010b482c0c4000c0c1d05c5807400b08d03200586040c5018030403125201344401c000d1103810691101041c81400e0010003000041280c0d50010b40c0c4025200e1070344010204007040d1195210032446030701c3c900b480040074003034500b405500700d10f52046543d5840b405080042c142d000c41d20007444078101242e0400b4040b1505c500d40c3e19000641050b420410010114100d81c5c05221074800c00d4600906641c01ca2401070200c040c43d10142d113150602c4c0c029480b4010203001c84010720030668908a41003800d41d191192104001c0d008131524940282c1d4603941c088600c601003068900c0c4002c150014111554140b074200c070b60001c0500d1680a01d410684480c0010440070300f005942c10300c1c0d04e8180030381044544095090074040c029440c09110001c1d803032061662010013089210030680880784007841c0b80302124101c5400301d8016240e41424400700d0454204001081e10707650000381107500b61001031075003900300d078072 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 972330908 1250 972329658 972329681
    0x151e0a1703131403060103060203190f090308060a1d040807050f06150612040206070c032001090b16080a02151504140106020d0c050a150c1701030c030f080d 69
    0x226032859100000d54844016240c00520f210240c0103140c0442c1d40c1c0ca0b410301000342172035004130005201d9680005510040c01d2182f906000900d0010780000c0101140f803c240c00088110000829a00b050881c1104a80b04400c0c41d0002e5030481d1441402c80030094012a0300e01020420100850000c0003084440c1d21600060710705410a490305941a4607900b070014044c1409110043d001d0350144110b0780d00c642c06540b13180e070342d001d01d140400b000c6d4420b401c000e00c09151016003aa511a00b540c12220f220801c0c2c0721050580d4a0307071420041801051558003140d200c05e02d550b400652501c000d00340d0121180122213007101c3e140261050410102c8401c0300c4000c0c40344c12101c407454280900404894092900c1c101da5040444c001e4441d05219540024050801c00d000c007084420070024a40701e40010a00000e1170404525501601e0203004000004420300750080c0110944a00309040302d03800b480c1854010324544e103852010045080c2503e103020140501400441c1300d0060b13070782c1d061 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 972332158 1250 972330908 972330913
    0x5210303010e2409010b2206030516020a02030c310b010e09042609040501031b05031c210f0b01080903090f04020702040e031c05151e0a17 61
    0x151000c81c01c1d400a51244041d4850044260390841d9901c0e81844503040d10352208040e0340d00c0141c1003412101080c1c3c2101b900329140800381c000f4000d40e1560042c0d00415a0400000c02d51090b0200cc0384d640d80c1904019600d50420b0461a48501d4008a40380207400800403400312612910000b408040341c16160003072661300c40c40f81d507000d9a4048a450002c6004a03200c0403142040d0311038a03102c0c0580c7c031403000e005030344500742a400e610080c20707541c40c0c2e0401402070100e5a140c0c9005440d040340c6038007961182e0f89520f008030b004d14011800d0f180390361060310202e2035980384400403030f0100f4030300c00034a030280c0401040c89001d8110380600c40102202100104000f040d0038001011140014030741c0342c081d01f0030700c80d03c02240e5542641c00c480c0b650841d80541c03940d03241d000150040070010240181884000388a2910340303e200105c00c00202c03030b0041042140d030740315506c00c1100c0c10940d040e684030761001140c024401e10707200b11282951021309050500b503162074001c03607000c515600400b140c0c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 972333408 1250 972332158 972332161
    0xa0e0a060f1202040e060103091407033005031b070f050a02011d010c03180e0106110c010c02060a030f0e06070201140627090a0206070803060414090705210303010e 72
    0x490700030700640c16286895108510706450503111805c0508040d03c001d04141d1981906014840e0b400c81c444030784010141078560166892400b114403541d111140c0d0010390350b80960000300061007441001c229029141c40e4910354840188040301420541403a1003500f080c0107040114904104501c00c02e40f007540144461b2089000240a0410300314004011301d00803844900700d41d03404201c203c0300b258541011041c00c1c1344400c074a101c41000b0b07041030003001c940034000a14143d0264203c959203a51005580302e030840c4d580111000e01140307101a4010034100101301000d40721b90f0107500c003038641c03880c0014515100c2c5000d9041c41d9050300d24600503915000c405220075100030005030060030440c3d0314a20b1001103401003c4030b211014815660380c010038000b80d41c80100344a000034440d030080805a40e0000d520b00031030b80307070804c0cbc400e280298a02845440d100c1112130307a490184083c1d100500f0094a40410004845007841901401c85c02400103034a801c1c2c01000950701900d0319400f00c103020f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 972334658 1250 972333408 972333437
    0x1052103030f2e060c0309090c081602070506030c09040b0a060e01030e0609070620070f03060f022a070506160201032004141c060c02070b070203120a0e0a06 69
    0x7840800304040e45903064038190f012808a04108981200c40c031307042c0f04110507800d00342034a0082d11a44400301c018104502c8540742a40075104c03070b02c00c1c0250841c56182d803d40d2042207a55842d1801540c3c1c0081041000c242056400c10141c00784490080000c2541c89200c804900900c034a03a10180c0820f644203850905582c050103108100f81104004220501d041c01d0000e9462200348102c03c203002c0c00620034110040c041c6040400c566480c1c048444a42c1e40300d4180505070060307c1b0542c1c2503031030b0406513045900c00e03000f20303419280c40e20030a42e070300900d40c5d60f0780c8901960010300b004680706048000030b403602c40902900c0c12440700c0f41e01c0000c1e0b041034000035040c0d52114482d01d41ca4242210705201f41207100c000d44040d00e81c0c0c8441c0182050314030010805034140c112a03000703103030403c5c43c00c0c40400c9015005440d14030a294292005c2e0742c1c0c3c50880000c94061950020740c5034012004100000c1c108a001d000d0b004000e1a2000c6401c0700480480d290101603040500040c1104900780f81 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 972335908 1250 972334658 972334681
    0x40902120609130f060c0509100801090c030c08040228090e010c0f050f160b240105030903090616020a0e1e0c07020d0f060e070f080c060301052103030f 67
    0x80c03242c1400001e020703d4a280c3d83d8000c0281c80c1d140e0090805541e8445002c20a20840689001c41c101801000c401c01c10100e0140c600002481164000303400c21000c44491071181c01102200c0700f0a48038044151030345d50803c512400d101801d56441045810701c50901c80c00d040d01c0c1e000402503040001800301d1540c2e582c1382921319001c1d070350007880200344e800c1d06460741c4007003160310a18442c06d42548800400181c100b6008054030040c0c00e81c1002801c1c03081030f24070202d00c0c40f441d16041d441071031242007801c0103584900044800c400540c01c144001200c906000e40101951000d803148807203021940c2e0b00040700540e071504940400e2201c50104140340450b000414803c501d042242d03451440c01a40740039543c816144000d005440b0710b80c1c1601040480d4000703582040c1d1110040c41000e002181d6503523101c460340300f0986102c1740504001011000855a00f54540c07026054030314680c00c020500000c08218007502c480c52203540002d0b4280c070000d0020b113010b14400c9074035a01500f0318200004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 972337158 1250 972335908 972335911
    0xf0117011401110d020618010917030a0e0a0206030a20040306140129090f1f0e120703031416060b040f02090f151210030308180312040206040902120609 67
    0x380e54010071400d042c0540004601f544684260403641240e1104420103000d051014002008080d0410713240144d014503030081e510423000510b041140c0d0985c400513659502091801a4000c40c080020400c9a113454101d004203240e9400305140c1036401d102915140d9100e030340300351703003041d6a2103001014034010385006004001032141040d80c103034444a00d0400312500c01080d00c02c1c19000801e61010b40b284a285800030340c00a00f50382110071203a04542c41044aa4040b0001518801e20f8104034a0014054a16074043c0c0005200300d600b5540c0a5880428040c040340d8405002e11007402c00b2a04590704021042c41210045094408038040c40103807042000042185030045c400803001d030300d03800218800c8039012074000d5541c04061031540124030494401c0c2c50036000200810104d032000d0703e0583e048a10955490395a95101c84519844120208511034150020410080d86008009c00a504580024001c0e80741590f505c007101c0c1240c1c460003000e0001d0f81d49504108884c80c20701c1281c3e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 972338408 1250 972337158 972337187
    0xc0302040507231c020a08091006060c021009031b14150d0510090204030521030903030a0b030c060a1d0102010c090e0a060305150f070f0c020f0117011401 68
    0x1c20384100c1820044030000c2d100c01c00b80140c038011500c5804503c800e090700103c0380f510383c01195a00c003c06e40042003207100b101c0c1e84d2030354411403c0011550500c1e120380d404a400310350355061000c10a508025800d080840413000f001180341c030220105012a00b03100c207904e00302203d01c6255141402c00c0703c0034142940c1c1343d0301c00c110704d44681182e441c101d02100c03038440100c0d4002805559040b42200c03a440329400501c50f41d440450040100a40060b43c0e203030341c400030600c0882021905042a03214441140d1084c55a00240003150032403106401081c400a80101602ca4481510001c00e100350403500415000490620090a1107115104403024811081c8000d0007000c5040e00301034080e42d01c40c80fa5203000c810fa50006a01a0400c0d40083c001d16130010558031a0705007410710031502d40d002d44085c0e403e0064030010514450080c640850310008a4a0b40c00d800159502040b0320715090084181c184500c0c10500443e016846018070301030702c00381e190343c2000c10146000500381241c06658 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 972339658 1250 972338408 972338417
    0x90d08010f0e101a0c01150f0312350708010308041502010b0301020c03190914060a0309020306181225051011070213090b072a0c0302040507 62
    0x140945149540d00c0000c2c0c9100d0030320280251203181895540c100e05601034081a040b1307101028446800c43e00421708104403000902010b0884c040280c02821144941c40410041102c100001106c00001e40801503042c20f000e010000041240e00848045d00181000d00320b4010303920408103081c40e00d2581242c800c0c81c01100c550306683c0c0300b071a40e1240e8022801c44800c81420801154801d4010307404001d0060020354503500505001c558940041000f4885804601c42c496501c521031b10f02c11080745c01080c1203140030000c0c0d4052011a52120300d80d60308040c3c07107400400c05600c00700403d501980c00c1078503451560b42c44007085404e010b104541e85d00000e6080051100781541ca1200c54030480c4d0003c03111005003190700d006803904400d240c0c903810341030800788006480d42110740904401c9000b500c5480820406111032011141a030030020f00303005100000c01c0c0480c1c801d209600014107201282d4032003620444261803c0910890101c0307035400281e50074070450401740100740e0445001e051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 972340908 1250 972339658 972339661
    0x4060510060f0c14121611010f09060503040602072406050f010903020f0303090d03030b040c09030b0a09081b03190c05070e0c19030e0714031b0301140c03090d08 71
    0x4020511104808054210210512181c44c0d411003808285103d0024000c41d03581c403518622465038000540d101524040109410f039682540190704c40000c0031115642d24003c80d08003001035901c1d8001510569195609000000006000910350215400201e6086090041c00081c400030346649400c0075005510290011035942d82040b5120143e030b80c1206c1c45400380e4544000320386035004200d11250300400c80300300c24050580550140da0308880a54090003200070180301501c4280c0703940300040c040c0c111800000e010100c2d40d03001c0e40041e03100d081031a2424486540200348000403c0e4074007e03682000418a64001c1c00e051207510000c5181000c0300701205c19150303592584c85c14811a41110014170000b85465452021618000049001e5a580c40440305004004050324044410703148240203010414025000140c008054020010004900160188120011038a03d803a805640360100c041d49520b02a042c43c0c49681c464044079102c0c41c010403d0f514009981d0300401c14000d2440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 972342158 1250 972340908 972340937
    0x1e030601080705010e060f160b0a0e1906020a020703080a12060e0c07150b09071d030a171305060403080715020f04120317191d1e0f060406051006 64
    0x110f0b4805c400d14100c5082d9156400900c11000c1c0d4424901e08000c004002001340b0100704100c005a4000c18014404201c6502c0d8000031560711510080c100c40000310120340300c070005955030014051a282803047da144030343d40341d941c44280e80102c98507401040700900c0300e01603941c4a1040000410014942d045c41d030911104110680c0b10b6504081c202182c440b821031215629500111801b0b41c0103030009842d0710300840001c107840d85100403e000c0d281e8404600e40790b80b0340001e0f03182d01c1e02c2c0c00c220346900c0d80010b003a02c84000c1c4e102005141143c40ca003240091035660322405400118000c03138600740c2d203145034a048551031141d144203805075481484908141c0031404117540a40b0101c44100303a00e10384078101602c4103900c0c8481042d980c1900010049031030041d16883e210030f04c04030740a0004c0300344030450800b4140c0155241c011540042c4c007400030700384040d00441c3c150351400295480319401039200c9040a10440f010790b00e40e5115014040c00d010755050400051034103250192940c2c0469 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 972343408 1250 972342158 972342167
    0x106050c010e01090c05011b0b0109060518040b06040b0f040e06010806010b0403030c020d02060d05090120123411070e0105010507060506060c030c060a0f1e050c091e03060108070501 80
    0x28006c050400c41e8111101100b544d44d20710007920650441d0004980390307504c00c41c00300541510b00070a4064024a00409021410f000340c40f03014a91065015040d55a40e005010041260b0b10391180d000c00d00180d0346880351240e00c10040c600d5440d2024108640c14a0f8000f4608841039004281c0c0380070400c03042001c6075200c1005510145d0440f0210550102c0c0c1c00021268001c002500c400140b07844c05201c42c0c8035055000034040c0030714860f156580086001c0443d254040e080f8001c6104034040b000a1856220a001c410b4200c041c6014a9200900d444850840040f280d0040081802e010302080b906104200c080c0007030000808180a540c180800242035000d054401801c42da11072004c6440c0750313605010b550b850319003181100c3d100e0714400c032019614541030759440e400728900b2166081d4804540102e4900d0000c00c0c01744110701e114420040001c1000034840010f5840c1840007003071950f9628200742c0e55480103a000441d0846032010581880700c107038010100c0750f100031030400190740c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 972344658 1250 972343408 972343433
    0x4120c080703030e210903061b09090c12010f030b09060115030504111e0108011d0403050703180f08161505160204060e0108060c0a0215040204090b0106050c010e0109 73
    0x52a02188131002d002e0104d180020510024080c0e40903020700310001a0b401c000b0b40080742e0f085013159440d44a400085001d075820050321f0100031420002000c01d030424542080d040080b03c803140303291031001c24013110115000c0e0031002c050000740d082001480490704600740c04c60210000f0703000d9540740262990182030008031050034107454a00103070070300450140c14880c18a002e03125211004690705240700110f007681c0c0183c045003120300081624590303003155944146180780366014a444071f40741036405800c06c0350b04508101881800241c4545502c0c0b0b170100420381036180320306860a00700e0103030401c642e2460b04030004031450000c01c10308920140c00c0904150500f401c0b65966a500100150841100b8020313402904000c00003440300740c103004d0036040380e503410306851280d00c400d004018a031080820320b9005030f00c0f02c4040c1c02003016200040f90480d100030000200c11a1603a50300780b101501740e0010b8085403020511104070182805510300280b400802006a08455544c1c03c020300b18 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 972345908 1250 972344658 972344663
    0x304031d03210706050f01081b100c1b03050a2306150414090604050d0206010806041b081014060102070305031902030c0a05010902030115060c060906020f07060504120c0807 76
    0xb034100444000400791002c0b41c40b540c0d04440184010318110080c030444620a206003038080c4103024081141028003019500038800c003c0c0034032540d00f001d207070440c0c05800d000010365488180c0c00080841034030428000e07009610900180805580c2030400500c8405182d02c190b80a800e400c02d407224904011a0440c1e04c10144440040c9002c90580810000c1c030626121b4080e45000d1170038008800c00000d44540708606c54001c94408490610040380c403660203120b20025a030001021400094142e54210b512503c2044801103c1d0f07640e440744e500d800c044001d608100f650390411240e90780041480d95a00401c02c1c0010a4024a903a42c0c250350b84c4070721085c89403542015240701061034800c1c411248a0111170301141d141003401c0c1000c50003810070800480c8a0f40c42e00380d80500600e110000a8200ea4190700c0f1115208800d49031103003c3c09034104120b4001351701304490904038102c10080d04410380600e01c000f50500c1c0c00c1ca007016000d100c540314a02841100001c800c0000c42d05011500e030107070b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 972347158 1250 972345908 972345943
    0xc040504080d270c0e010501050c0303070f120507030c170603070603020c0a0204050702100c030506060a0c0204242303060613060f0603230130170304031d03 69
    0x10006010f210f41e0f5070942588015400464203a80140568081e0560075108915286151666175000641d418424598a20a07175003007803000824082c020241d4181101c070354180003c3c2515a0f024030b00482c2c004950078808282d0b2000c420100c6640700c5664810401d01c2030801600b4102900087d5580c130a500c0744008142c0c00041110781c40000380100d280c40381d400303002440350303050600d400fa40301c01454502000c910700d440b4011403000d21901480b1302442c000390506e4504220700908031008d00030060181d03003180d1102c810000c0d81400f039404d03800100640c81e42e1108203060403641200f0b10039404044003158549e0304240c203c0d960111711250451421074543c005841c3c0645c0003800b5210700c0e480b09a400b00e503503030006049078140e0800402820a40744020030345041000066039400d0a003d5020814440380d14441036410f080700d03161541415490700210304546540d90711402d030a611416942e880048140020550072a103041420402003402032905640c05001c070b513540c200500d0309074680 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 972348408 1250 972347158 972347171
    0x4022b1103190e07060e1302091c08120106030c1103031e040512040603090b0f0f0712113f0c1305061201080601061b11012705030c040504080d 63
    0x80b560754000b8034800f03c140103030703a0704594990000d02048000c140650145404600400a02c2030a20840d4003034140102429056a0380858041c4003072501e89048440800c10000d0246032083c540806e0300074906a6000f03d224201070070014000301203081515403d500074020f01068075078180c205040603250900c0d941041e0385504100385000810722485a10100c0010080381007507040d007041c007640f030080501c4102521048030b907190b06002140c2c0c84108013410b00204098621682c040313000c54950b5480450949151600207100c0e0744245800c0a0600300c040794404041413103a00400c4100340078084018200e9051804255620002c000203d014400980c15003a02807100000011b01000341c03e0b240c8500ca12401c29188100a0080d4683e5200303040002840500c02c00d00c00040c2e000c24040c02c1107044a56640c5c4240241014460341801403c060080e80f9406c801214020f16484500b4030100a19200a06081199805000380075034202410040400c80c14002c94082d50761412000505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 972349658 1250 972348408 972348451
    0xa051813030522140907210209030106060203070506010605041203050f1c02072003100207020d02030609062202062502040f0b13050412080903040504022b1103 70
    0xd88540c0c060f0000d040c010010401d14108000090000c0c0d4070700b060f100741c4040441c03040103c1441c0494500c0c00003004400403a16924015440042d46604401d02500341750002d0006400d4a1190708030030016440031880364188041080f20303e00404160034441c0c41c1a080c14060f8011005090b806020b0000001d07990054803555021100f06c21510446002d80941d0045a60b01942c0040310a0390f00100801001c02d41c040ea075481c0fa4055a4001e004002c8141e012004a0181d00055401d0741d00031300264045000d41c600703102141c0324510381c1019051070b1030409201c91008405e80c1003102c88459070b40b450360040e00c89074210786200f412150402012010071861409400c101d40d0002e4006090400340040b2807002e4001c150b508030201c841092411003000307440111002100c0280c1808181c3c06400601402071a0b9950400c00580c142c0c0d1425840f02c02140c16644110030039945040b1003080d03800c40c0245051415240307108014140300c590159056020303140800707400940442c02551002c0b52 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 972350908 1250 972349658 972349667
    0x206100806040b04050a1a040210030605010f1b020d08121501080705030c0d3e04030206030c04080d0806090c03090d050d0612060c02070605030f1302010e0319020a05181303 76
    0x206e50790300c00710740e4003031b4a00c1c86607100d00c260040d101240a10820380c11044051b002c0d0140b501543e0060b940c00b0003544600c581150500c50703440c00c80140c0fa0f086c0002d80c000d07844002900341101d0003a040c2a0391880101030310500900300070314900680344040d040c405207a900182c450740040c030510380f1030f440340c0b00e90070350001c0b600c20180c1010956203081c41240440d0050b1312681894248200d2025121003c514040284040c404200b1540c2d541080203200510b80b590243d504403440e5410b8030b0402d41c9a51146160003000002d00c030104580e502000060714110b040305a20941c000a40750943c1050010303583e950741d0b03407801c41c01030020126460303641c10351031380c0100005c003805a911518001c0e5810800010301611403a0310050007010804207041340243c1c01c0305d020b800e500c518880380d40d8800c0a411403000509800703e0400c01e07054213040840e50200a9403070901100960104940d11a20400124000583c0080e0107120549000001c0780d4034007088a0740f00c80c08038840f01c01c280c4540340488 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 972352158 1250 972350908 972350923
    0x50103050c16030903050706020102120109020c0a05030a0309060507170f07030b0a06091404050412050904231e090a2612090105093403021f0206100806040b0405 71
    0xa07042c80c2e07000303030a0503806040d001c1164000c0d402c0d51141521404102d090742b149e0382801c6000c001c0940104145005640100070580c0014291080d40c559543c54501350783c040d200c000e00203a16090600c050014600c82c0c03d42102c00c6017400d00c4114035103245500350501c0180300c0040c0ca03030b50100280c1254046d4011904d840002001e1821042e02c4200182990625001c5d00102003496a540d2090781003510446010381d030003103462021315540a008030380e00d51100306083c0d00182c803030300384805080c040e0803144012410b4076040800c0e841c011a2103c4260485400b00c20041c0315002404400b5801252046545130022040150394134070f41c01445c0c48000904010480344400202d0f04000c01c10100290b0003152110008e20540d107619040583d01d400031000c01340c0c141c100c07400d4000c2c03c1c9903550069211620b0b6195881410341d580c2c00094002c0c6407000718002900242c3d0760200c0d15641401115070090f62801180b0b50b440c20304e4081d076541d140c028801000d841b00d103004502400010803500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 972353408 1250 972352158 972352177
    0xc080609062101020406030905060117031c02040b070f03030e16050d081b0604021002060103030f0516050f0c0f0103090507050418050304080706090b181c020d0b10170304050103050c 80
    0x2e542e45c076550a0020014070b19030b00b045c0e071140117440000c12650307403000b02501d407102e00100a600305940348004080c019440030004185960030013000500703480d042d001e00b281a0080d00807849449590070043e041d540c0b108a5102507401103602a020203040501c41415240141d4241d4440340d02c52418001d144034001141210845a01041030034100009602c0d114034400e580c040096550355000740eaa9080a0000801180303160041d0103569200f5800740000a078a48050301c9202295181c403802d150780400e08580c80d4200410003d0542405482204018000c2c44c00300b2442d40c042e119591150000d0040a1140f6101d246016441002042d500e6140390010243c9584668034203170035a0300c41c0b40340304020114400e0080040c00b0600d540070f0711460b9810100e0a0240d039203541c10061580380500403080c0c000c5400b0a540b000d40c0f9100d109901c1684120510102410320301250514444030b58841904a09054003401c1108070110a0318100c03075003800d0105041e210315001c40264058400d22 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 972354658 1250 972353408 972353411
    0x1c0f0c021e04060b0a050306041503231908040b090a0f0b04060906050c0c01030c2309030c0f06190521150a0602120c01060b03190c080609062101 64
    0x501082036000c81078918504801c99080082c50303540d0520300000d00405c1c003c3d10114205200007486070a058104900c004002d901240981d0346907910f8a00c14520364082180150000103181d118407020070603000e1442c49000c0701065a511542c9219661141c2d00500682800200e5106402e031900e981d2800501036040202007140d803202c601c0845e030b4006108003000114089400291130f40680219a016840301c40504400068407005401400d5011030450421000c00b2449c55182040000012034070b02034014980c0c2d40795070a08140c64841d03504001ea208210203440c038215a0351702400c6403006090b08122541202d00a03030143c996004100a8030325504250a81980c81107114519920800b501181c2200b01501c0e8000d004c030146890140301c0259100f02115032000caa040090000c660030b1380000300d040317515010f03500003942007034900c1e09482d0048041005481182d0140381c1206956282250756072600600080c4400f80c0908901d0003035003c44400b40058007441c8155280d80d410400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 972355908 1250 972354658 972354679
    0x403060e010e0f03180405010b030a0c0c02150406080907060923030304091b180504020f1903090201080901050702150411090f0a06140306070509031005041b081c0f0c02 74
    0x2640303991145c4d580000c10707601030f00300e4072242c9080d01c501e905039160f01d107000b825969a0071145004056100809080c055a11845030047c1d40c0c1d140d4108001001d00061522a4074042c00509200c03806094003039145c2041c8818010164003405400440c0c0d11400000e1922065000290384d560000010903054000040c000c1130141700c0350840c6403100d000c48071140190441032801c64004501174403038282c2d0071140d5803c00540c83c0c00e401034004440c214410385e05d4154050106040c44846d410207002207901c07092810255a040391030743c4d60090a04009206c0340c584903100940f60072540595407404c02c0c0090214090012181c10303444200030140000f1803906002c901101e80301d0342121003012090030b0800100704110300b400d401000000150040005846032202610f603a003125050320f4140c85100c03d61900b107416030080c140182e00840011052070300c801c050502d01c002c01e4102001c03d522420a49000d04a4540501c0805c29140361007140c4880104044034100341540004e03521045180c1c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 972357158 1250 972355908 972355933
    0x140604060c0815030d26010e101d3114070b07080904051803030c0403110f1c060e030d060f0e0106020706120b0a150f020c060403060e010e 61
    0x140404050360060720342403007a5490002c80c0c1099407440f100c40d609500249002c40c0818001c000c6403100100c07110b114003401c035145841c2d140010090344a465409200014466510304055003000076003003504100c5070050100030400c2c04200050903c598640110b002c801582c0a0300c0704d22000081031607031080e044000c0d800c260800c1a0510040320360313030007003080001341350360318004890f060707036011800c0345c10071218104003c02460000e107141000007100c610441c401c04240000c40c425100114860388460460070510700d62859084014040c42c1a83c0540348140c0d14807820605e01c3c2403600c18004012024a00312000c2c11074154006a988000702c4c0074002c0113840c0d000041603074405106400d10550b40d25000703800e090300b8483c640c0540c10549080c0002445116110700813054110049180e070126004a1040f1060303500503806a100c00c0034150702c0a500107000340400000784000c1192806040029506100b01e200c003d103100d0b580c2d0040420f4280a401620000700504103032032040e440701 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 972358408 1250 972357158 972357161
    0x150409080712080c090a1e05030123010504090c150215100e090d083903041e03080105040b03010f050c03090601080607020309011233090504080f0714060406 69
    0x54200843c0b14600060480d4180b901500c05240c0020b1801d5500c61a1040ca0306160204e80a010a074011404005c14103032401d00500b131034a40f03038620f03840c0c40d02d545600340b150125040e00028456030402071114046108502e01d881079820303643d030b0090060350070442645061030000040201c02e2415040145440c1d9100d000403c45d0b00c5180c1c00c40055940300e0025480f154624072090126801c1c40104000d454801034045003042c207000310b051800c1e03507000c151081150108022101400001c2040100a040c003546a02c030b60300000b19001c98623441d5400340041c3d4050203118002c030b55440c80d028007030750309401c0f0038010700183d80c081245080401d04071645a00c11640240140b2445d800000c0c8094000f07112071044505601450915080d6401164514488070031017443d9901c44035002d0a600005080155116801200380d000804585055201022690100f84c0325443c140400022507101000c580c1c455000d030a0240c0d031120945400300752001080c00b44403003849060100010070100303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 972359658 1250 972358408 972358433
    0x151d0102030f2b2f070b07021009080d11071703060d06020408010f05070f1704021f110d1110050901110406050d0b090124020f0a0305120c09091504090807 68
    0x14800384600c0481044c000c07078081c44290350810000010010000072820303140400e9008540c0344150781a03880c118603010700381c4003880401c3da041600010422400c40c4148034501140f16266882d80c20114191540580082d1042808218080000000b4034941c1c807100c003084442d610000440d150b40d102d8811f58001c0000461810f43d0fa481c0101080040e806402c001c61614001d550314102060309034209241c00d50301500072078010605d40603030b03201e40300d154032504c0c404c0103560382e2a0380001c0003c2c0d0303c42c42c0850b00742610b000c0c00210240181a0301000c1034040c000104100042040d4a6201d5030500400f0050400038502c40042000f04036541d01200600003084598006d00c0900c04140030010284c10a1003a125010241340c030032050756003180d40c0d8012018180c015907130003100403010a82000e00e040401c0b00012000920b5481c12030f030850170a90481d501d00e010504040b0001e000c100310401c00741802d0140b960010508a9a982c0c641107258035582c00514292681c00915061a40f03521 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 972360908 1250 972359658 972359681
    0xd030201020903150c180d0f050c180c090609150c0d03140106051206130501140a09050f060d110a030c03060c0e03030307110703020a151d0102030f2b 66
    0x5941100540d40c01300140c2500400350a07a0480c0307020308013008840880006c0001c50b40203401900c0c428045600005982c804d580504050141c0c0e00050b0108000084207000d070000f584000d40902c038480c9148004c0d40c140c40030503150150740b10031a01c0020000c14070f04281c90709111000414048110300411000010744264605105044a07002c111140031001d0088100141060100c03004c200c0500c40344640026020340580300d0b04200c019541e043d260260449030106074001e1007103005003812041d04000b011861810405810020b2070203081c0000549180e01c6011140b43e8101401220351a4014128006000010841c0c0d0391408a0780d400c0e03244000c1c0ca00303603d010310383c0e58003d004540502178100028095850759480402c01d80f2141e03440746191490348035011004c8016207403088880c0c040c00b4059041400c80f074800000411980e48820940d507410b01030196903046036000800d403502288052209070321081200e05005100c840300d46003840070034401d00600c6d01c0b030403613074440e403402031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 972362158 1250 972360908 972360913
    0x509032703010c1128110f090f011a07120809030d02040609031a0702101a040603060f1803080606070819090501090603020a08040206030a0e061e100602100e07050d030201020903 78
    0x15102d0300000c0c0f02c410080180001c0035114012000050606241d0b01e9020300d0080000303200107c180086200f81c041101c0745c3d4030b616003880045c00180e41803907540c10007104c00106d041c40c2000c182d5601d0b111410289a58052190b8132010414246050040d01e40920401034110340303035070382c0d601b0040c100d100d40d1200790b418228240c1d5910f011000324440398030a80d22a0020041c500c80245603100030300c03409405e1107901c04c10006050301c40e50365005500c000c50161401055070f1802403000c9040341c22a000081c50b0b03010200d21140001e40054605901c000100d40341c42e2660b89905200c3c44500c81c82030103520403010140e003e8811600b12032420103484080c0c0e142032040780c40d0301c01a8100c1c8a000b043d036021841c0b0f440000c0041c40d1460041d17922400020011070300c50800070001e0318010742030764a01c3c0b2003224400c50071b8510856141340c0b030740080000550781e40d5a04d01100692640000100317040b1305615800d02c002000010001c034002840c000c2d10b0f60001c9011820000d0003504584d000030710a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 972363408 1250 972362158 972362173
    0xf070b010510052704060803040906210b07030506010201021209060412180b070f02030618010e0c010c0305070201030605090a06030501060b280329040f0509032703010c11 75
    0x42c85502030710a41d02d206800811311203a43d01c00110341101d080d0f40706500c40e4403800c002c910181d052025100400388084040f44a9081036001182c4072810100207143c0c050003c000804103107881c517140d420412138180000d045c1c8507500101d01a100d030b503200c00c07a81289001880951200011003070300c03c0d4021000b91004203003400f0300321050340900803d071a0302c540056007404140c4c5c2c004020049240f1030301c0c4c0d2060641c850390110f810081d0464130300114401240741e49948210178001d001c4450038050241c00c2c280e15500002c0c0001801900260030008089040e5003164042e80c000c0c0c0103044001c002c40303294641984910050181740c00125059400c1401c00103009800c803050320603120303029418a422000e07403041c0381c00b01d80c41a16250f04158542c0d9032818a242030000b8401c41d4050404400c4408201d00f05100c00e40714a8526040544d103007804002d030754a0b0100c00c1d18082c1905d0078130105c0e21040e42c1c20724000c1100c403158069055180c0321740308e1001500a284c14060700e840c2401d81304503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 972364658 1250 972363408 972363439
    0x15130f06180608060111031b0703051905100504050a05010e03090111060c03010308130f06020c0411030f0a0c03090605090d02160308030708131e06050a200f0f070b0105 74
    0x51040364030460700030038030b900f0128185600440b208440040c618007180c0c1000d04510544402d41c0b00c1043c2000310b501b00a10500a01400b40403010703008203501681941e14009541c0d0650b1a00340b2018840c03030726500c03000308003000428003006801c140c003d00284945c600c1c0c1c0d41c03000d489a1040845d140410706021549504020202e0000d1080100308460790540e8a140c07600003895000d0751907020f200000a07400701e085042d0b00c0c1004041d0171182c0c0148008002c26040c0422100711031125602c0c0003041c410045415a1628055882a002000841d1904e01d4940640141608007402842c80313091504000c0c00c0d640011f80b42070542c040340d00300c0d4142c1801b600f89a8030b610301808082c060440400000703c40e240500002c0e6008440109003201c486000d8446940c84101400607d44000b6001240e00500c400c50041c43e410040c00203003000389038141c10a0400150405400d00404000030612401e601d03802802c0e01c8151140c5591a0b6403424145005030010109000d035034422414520f00400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 972365908 1250 972364658 972364697
    0x406030302031e13060801030605010e13020411091008090c06030601082e030b04050607050f07020114130b03070f030c09050418021002010c03061d040215130f06 71
    0x8690301a0059442c10014600396440b00402c2c06460030400010420445038034000c645031402000b403070743c550009504508e4054203172071042e03100500018110080c0b11a03405c2021176070b00110303030403100011300c002614180c07001c40c010b80c00002d600814011602e42c080d9000030740c00384941e209409503240c0141130301c200030060100b914002e0000302560b0014402500c1ea1000c0b01400e20851043c0b03507010b14840208425003d81c2d04220380c030040c44011310007008420007040350041001e00f0068240140d0745118049401351840180c100008292703607403105604001101c648490180c00306c0001c42e141c4401c8079240d1310554040c400140c3d034a848100c43e61007031094042001c0ca40d600c848155207010200f002034680e20214000c5403840c01403c1c001a6194850b81d03e04000c50340010a603149564006011101940d10200301c8003010700c12501c0000340740c0e07042076015a0481380056500c101c030054500328011001c5a5600d441713400380c04211545038030301c440f0842e200b60759490341891003041e5222 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 972367158 1250 972365908 972365921
    0x15050414040512130302030a080a0e012a060b0301020a03020712031503150f1a040b0d170f0f0a09030209010603200307031e0c020601053a0203010903030b090604 71
    0x5050b500190300841c010102d0300000c240f044903013408003008580303d030002805e09610303030403c440030140001d0905400e42c201c1d0020300c1500c07003420401802c440c108032052440c4003281000b5608900c1402601c2000302c1c0360300602c1011400347c02107444074440b14000d0002d40c03100ac0d054600c80c0c003403100d141e0401d00c07a0050307541c1c907010654129111881c0d641d039403200851b2420041052030311445042e000c00110310555441503041000c02d0b850303080f20014881211400003549010b050f440900c400428100d08041840b01c0308030f8016a5074512640b40b28505010b02110f0b5464000c00240c0320514aa00910b108180c038000c40350419280d0303940c0000d804840741800070850445a0b84001071031400d954014541c000c1c03060401240070702142d071030b5810400c0e0800c0360364a02540e86008800090381000b050f4050941a284221007141c04406000a0040c0355113180503140c10200c20b12044c044200000300c4194068000c1c40041031500c0d001d8080d0003008a0716000c0d070403e80000316942340600550 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 972368408 1250 972367158 972367163
    0x4090c1415040b190c080304030e0f0307030f02060c01150303051e0309150c0405060d0e010e06250e0916080c0a05161b0b0c0c03030301060e090711011505041404 71
    0x10b5140044941071340410319250804002400221000759010607078800055100364400e03581d141c44c140c441c00030421145040c030012030090317100700d0052000a0040e00e0540195404860040d1180d00302c60100380075003850882944440c078240c5001041540000140c9039141d010000c00403c115a200c181c0844c1c0003c45170b40f9429400040350100305611410101d4014883c014130510740380e166404103040754040d030000c00c802a0f840d070914a00300e4007031150310902c001368004cc1a1344d04080d1251650548195030a98480002c684c03100ba58034056401c181038018046c0036141c05203040d40003880c169400d07440c0e960110f42800001220398a00c501220000742c282d4491a041400281a440910382440c40072114403a81c0789170407240800744000f08008084012105580b0070700c860b02d1074145001c1201e124029481880140319090b000364030703c01b4500e41030700c02c0c0c1c521796219401212031f00745100c0383e040356503c0d02c0608074419550054050030b584043d41c0c188200310380d202c100d240d140c400702c0c0d01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 972369658 1250 972368408 972368429
    0x11062109120a180b0a0504140d020f130b04140703150302031b0d0212030403150618051513200f040605030403050d0f02120c0a0206041104090c141504 66
    0x7042c0026000d0b80c18660a4203100190740a03007078030740680d0032142e808900494042140450701304000b0701484100c825441013078881ca41d0344603869001c141940182c24840d807050201d075030f1006010f825580003030790095008005011002c448024000380f51026500c440020741001d45018005182d03101b031400300ea50103001088158002403490310b505500d20b4201c0da020807003c1c071071405039036074400107194168400091541c1f18590300d480c14500300746201264910341444c10030401108041c40d0408100c664810219950351440030007513085000c0010954016541404011018031540c01001c44108103a0300303011011050030790403824014000503c0807007404002c04d108407840f4201940e0414441e0400780e003090310145428080c0d81ca440703000380c402503001c100b40302c0314125208050f8001140c44600c901d090407544c0001c2d02c5a00043c4060140b0480c2c2c071424106807155072003803010b10740002210780700d1500c0c2d07001c50303401d100402602403159910900c00b0f048a540c01c0f00322011201c501e8107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 972370908 1250 972369658 972369667
    0xa24050112061803120203090a05030403320c010e04110310090f0b061902030f22060c08030a1505030d11011401051012060e430302071106210912 64
    0x801401a51000300a00c0e080e003d10440140052b208001400c0a140700c2d501c1c07000401c0300080c00e03429102041a00300103032018112802d14400000c550090150310030305e020245200524041409003120003004401003030300100304020241d00320b02050544528203002e0100c040d5109208054602c60349034140d10030410000012180c1c2c41405911441c2c001d030040d03c1c1008042807910301641c1146c0004450307420181400c3c1d649a0240c2c10042c040e0239542000600c40b90580c031282d4080c00300410142c0301559849500d4000461900c0e07000040034002d0403600f1144080c00001e100e080b42221003140b80d824184030400b502c0c403400000e4141d4101502e500d41e280d0090b1005c0700c0c801201c11030444510f98541000c59a07800810045100d1801100d0214040d01d03003648020301249150201c220388032019000d18010b2100600b201075400f881c0c900940c48080d10305000c0f13001440010a1544400001004800c81271000d247c080202142c00c5981d5480da642442c01d070312601d2001540308a03440800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 972372158 1250 972370908 972370937
    0x40506031509040503030a0c02030f03150102010f060f0303090905250c0609030c020310090b15030709060e1b03070c150b090403080610020c030a24050112061803 71
    0x8003a503441662990780ca0749100c00355012561000090354141d5a0350400410403050460501130103601d141035100441c5802000d03d00c0000f20302014101d12132000c3c00746440b044e00d83c800d40141da40d0711141e030010088140d5552101d20034040300c0c8001c4011030b220b20030010300752006200d400c0c40f070b01703105425400e15110500608202400c45440009101c0000881d00120f0184d2003514480303480398554641200c56401003500c0c11160140404d00c40b801c01690301c00284c1001c002d150401014115040c80f2800b080000f42840c6490704040c860300c0c6019000070380d12400165090085440c21a410381e800100424002c0a02c011a50100403865000c014800608809000c81c800403c0040006901c00d44100103000395809580070384c006003104080c0400307803a010f842c90a14810500040c1502c45800340400d46030003120f640600415140c41070301c02840c2c86442628904607500e00300300500c2d03846600b0f1048044081c0310030f44038070740343c0104085100300640c10100f00390b4064403550700140822 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 972373408 1250 972372158 972372169
    0x213030305030c1b10060b130e06030f011103010509010f03080f090604260c03030901080f040f0813142d0a0f08030c010b040501030f0303090318120b070905060405 72
    0x54400c2150850130024070003000c2c0c40c07001d08110101c10401401e00f041e00c6445150030b540180d0810010795104200c6040302545251160040301c0d00a4059a4199244c60011703080144c6504140c5a43d400c0840208401c890040158180c401c112004000361341c9070100c202c1407206602000300301e40e0003000750003529011003020b0500d48000a01e544e181c251030301300030840c3c60060900480303141d5050307a00520000e020300200207441c034150019401c2140d02c2000138091f040c040c00c1003400114200100b002d003c00520481c4489800011490f6034030070380c43c011140c80e00a4801c40ca14190502921040303880c1118815a031a00a03a50250661007561103100e00c03600090056079029001010001d1004d4042c410740c001486104080c40d1641c82d80000b03103094030410480588113519140040c030010f03c180c400c100c01f90f42c151400058071112440c0545031043c001d00c005210302c11210000401c0c2d1020403a13080140d00c10148a00c0c1070f10f4140090790b05150710b006031a44080c0502c0f082c045820a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 972374658 1250 972373408 972373411
    0x1c02040615171909050c030706140d09050f03030f1b1c020a020115261903052226010501050307090903020a150e070e0c0712020f0d02160801021303030503 68
    0x1000982c16000c041c49044403400d0f10308030741d170350850340100c5030501d014072204008180d01d0070000c12032850800600c02078803603019008551552040e80b60203100c01040044056084036080760b0390781c2040b12031441864400c48076075003200305060b01504449503202c00d0f11068011a92041c0745070341d40d8031850001c0d400c849042c0d400c5641e60110b202e50320b041100107200511458600078804003011501e000d062189895120617640302148a0b5152a000741d00080c81d10b82600d801c070f460300c000000d80980c200e44d044100403035151314180803500c0710824a802c0d075520305e00307100120f0024880c1d032610300340c88013441410380c96049508100204841e940001d81600c0c42481620500b00041e42c64403884c060754100c549841c0c0da44d5402c10f46d120300410014000e0130100102111500d001083d5078428410200021300040f082144184402e000f003005400c0c5103c0704003910121580c0d01d0000f07540d916501401c26038080d92407800100d05d02d0600c00c942d4403000d904021080c050568034252040c2e0710 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 972375908 1250 972374658 972374671
    0x90201110706091509050f19090608060114032a01050f12041208091b060705010203090c03061005060304060e0c0a030c060f2a0507051c0204061517 65
    0x4002258500148040c0300700806000a602c624042d1424002c001602415142001042c4008a5404e00ca155502001413503d500105d0f01d09561282d1001ea51000c0001513005008560500e14081990300c00400d0140c140d4141780c40407540451a101007640d0740b81b40e02800200100c000282100d9621030040304807410798103041c0b491401d45c0800403004103a02413003c441c0422201c8041c801007155011007400c8040302460852400c1c04d08003100754803141910041d010300d00c002140f43c8407a440f1203043e0703004150858021502c0e0b19180a03a2a224041280381603c80d00901002400d03c44800e00800b040d220081d010360304540c2c1d180d0b1800c2c01002c00b410000c625200f50500080640d9a0140340306c00f03503205180511415103058005007011000080201c00e20014040802c840e2040c0c144010415480c40c8040c420342d4400d0a01c1800c0141c0c039005150448500f400b03031920035030720007042c51816100b52020008256544400094007201ca08850001642e0000100b84195129100364103c40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 972377158 1250 972375908 972375917
    0x70204050912070507050f040e060c030a1404050a06050109020f040909060204030209160908011a0613080709060e150f011101150303120b090103171806040b191b06090201 75
    0x44800720700030642c2c3c1051108441560000703030207012504203210b901c1c010311030984050140c0700c9803141c480d4032188014141d10480a001c4005000e03111103420244005141402c803403218101800c4c426103c0b02c9409003034035070500781170000070f00145034802c4456480c0d454903d1810b040c01c0500e4072010304100041550f0703964003880301001607616a4041070003040c1d1070000310383e000342015016004015560061429900d000d90ba440360141c105941c4000084c1200c400d6540c0c64a0720104002c0004d9420aa0080c80b4240010800303c2150b8880c4080d5a016001034030355640d0401c0309810001e05000b116002586818a072003c0d5000c1d511030052040c4000010600450041c2e020088003842d500580001d21850503c503ea2581f6204411043c4002c0e42c1c004610743c19034075840c00202103644045101400007844004121181302c004140c08002090340c0d076241c2d40c0d1040802240c001e4001303001c4011803036450540f564011060300d402100203610300700c2d15403a00c0d1950070003040d81c21826810702 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 972378408 1250 972377158 972377173
    0x9071b080a05070b07020c0f221a010e040605102001020a0e090a0e061f2408010b07030e04090c080102030f01060806010e06180a0506070b0108120306060702040509 72
    0x80e1545018000d240300d40c1d0340b41900d0f5000d500709143d000030050b00440c19504200741d042101c0e11880580c8003010b109646980b0703808a03015184813266180c503030710800355281882d81d101c1140041198903004500740da1f0182c80d1800007080000b100c0ca03511805512000c1d64400302c3c8014003a0b40828480240c8001180385120940209030aa0340300c0d400d2900001c3c0f082c0001010b07850044c1540360425041707d001c2010030003070304015a032150064000008249441c9160a01038148107071000580a143d032348110540f1904424010110402894004545600300118200150744180c1c1c1c8480d03003551303904c48a122117805000060039040415910003900358408102140240000c5d8050308a540309181290314021004001c0d80d0090191070400c0040b441c0c10103070790360b0301c1c056034843c8070032400701100450b80c840052450720584d0320217034004c40e0224100050061101c0c9050403118500c1c20341e400003080c0085084c1503c4102c1d8055840041440f00f103025003002d070320440e44040e9000486006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 972379658 1250 972378408 972378413
    0x50f041127150403020103050f010b090910090603030507150c05040924140f030d020a150612080301031406040f0305210a09170a0804030f1704080408190209071b 71
    0x2882403002e0240001e4000a010030455903d4071503264030407690020600e081d41020000c4031544608401036200302d11403c0403c01601c0c0d542410002443d566104002050307891501510341d4001d00300594108040c00090000c58442d40580d52000d1902c0e0741c1c06180504003c6000c00400010140881c14024402806c040300c89110180001d0402c955003e80080c6601080214103090f02a5250186d0410622a180300c0d400068021721580e01c41f60712414408940307003100051040380e2103152001004003500c001d00c6005002141605c2c0a200f003002e095000594080d6100300545005000c410010314180110780314034041c0600f0113042c070041c09140500c003d110040d00c4140e0380070b1801982c505a843c00c20046402c002d40c440c03c411101420a06154006081480014005010300c026940242400b43c402d0303011600c810002480e00340e090034542001a02d54100380070310465440350004078040402da96003010400e550090044020390b550303c1040300c405c18500c1c210914503280c07007940d100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 972380908 1250 972379658 972379669
    0x1273b01050f09010b191802160615080d1202031e0405011b0206240315040803041112211c02070501060608040b01050103020f09060d06050f041127 65
    0x2640240342c0c1c00c14182882c01c025821100500321891080c4410f04800012109092002e01290114054401a80d2040494074007a101305c3c1c01c02d000002180ba04182001101c1d0300c4001c1000c5003041081001e83c44058050303480119200c4200854004050075035410842c1d00116409258981c9440b8041d80605405e2411281501d044a0503515181500074004900d03a0004400a641c8010040c908203652907100502c130a48183d550340c1401c010303502460310b040010030540718070b00340c0c802124035090a18101c036070004c0c0e900321940307039901d101d100c054944145802001c1c25098040c0000742c4403282c04202048120002d800c41d142d0902640c0b10101e41481d10012011000c10003580c0c88410f80350403403c41d003958002ca005d0100f01c1080c0400300303940c61945815030300203090060341d0300c1503540c80c41e510740105650aa0311080020700030464411a030860000c540301910300d4462500440e0070042035405ea803001440c6c4203020701000b40b0b0100b00c40c075007800c0002c000c0c980080745504c02000c1003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 972382158 1250 972380908 972380911
    0x10030f0c02060109050c04062001060509011d070507030203030f0709210c0b1e0a02070906080c101416140604050d091202090105010507020a090501273b0105 69
    0x30241e04500010881182c16019855008410103403891a140c20500c010f0600d000f0904400090b00f1104c01542d9004025030200001c2e2100400320081c030360790303202585400311001d0180700301c40078a01c01103500c4601a034103442c0c01e554150042c40c11039585410802c039508000703000310104845030b08001020040c4001800710400110705484254002c0d04201c090301981790700189101d03804124200e035440002c07282000c40003400302c4182d41c8004001c0200d01c0c0811a030400300e501031a00703000040320322000510309580c01090320b032580c0c84103c0240603100c401d9040340c441c854100810000c1651281c0381c01e0300c0c2055106d059454410051102e072146004002c41c0c0c00c4906911854480400c65000501e1304020080c0c00f0420070380c04d14684c00303c0e00c6454103102c0d00e4140302d00481c00b4011582c81500d41d0000d01049001006030307682d16042c1c061048030005030025004128603980c1a04001c83c020402e980074406249045900c2c20642d110b041845420354420615084070039910054081c007889 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 972383408 1250 972382158 972382181
    0x20603090309031501030f02100e031e010c080118020702010c1502071713090216060906060501030b0a14010f020f15100504052401090801020412060506090f01030210030f 75
    0x2581c03a404400281803070000702c82c4107113140801003401000010001411804016810380c3d208000100001003611518460340065901d8010803108026a01010441040a1030028000e200601001c201510000801c0c00340360101e07607802c0006a402c400a40013491018130601d440a000c00b0140c85103444803048004000400350002285000c3c05440c007804c41d84141000f11282c9441d0740d41003401002c45540c8103100100d038010844512400c200d000547c14190020f00a0110f030403d8500980105198020103020a252100221b0307036080159045094a0042c07200c0c00b0500002c0005582c0440c05150042c2144200354201e00650014003d4218489110000e040d0307500b0f080341c01c031300c5225550700164003c1c0e1a09003008801c0101e0341545104d40040c40315040010201d0004882c10010782d040610a90b0000134000360902c0b0700c0078040001b41c000d040802950302e51404000301000309543c2c0d01c3c81c030000200140b01500d000060724a00c4d01c10750500040a6441c4410302d000d442c40030049 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 972384658 1250 972383408 972383413
    0x14160201142a0c06041202130e0a0606030501060803041202040b060708190801062a1106130906050f0d0809060d0f0b040c02070614032a04090c02190b0a0902060309 72
    0x6008a03400b08008000101c044404c1313424a0f090030000f0201c0d0b982c1308000b9104000c20000c801c6010001c0d4400c82c50700a0580035601c1c070881d0f0742007003070241000344011201e82d0300c0c040000481c40e40c0442038400781c45401c4a0300326084d070300b6000c100140c0100f0062903070100d0308014410004084400410845081c4001001c0039a044203028041000591000d418408008100d081d280d420b080000c070078119071110340d4214225410080d00b01500801c07959085000083c107400400052a901800c43d4000881445425114400c0c4820040111807007500550f0103c013407000070720941c000e400a80b002410f501c0c1455041b01c201c50a442c04012a0400030303a0342c07800c1c03001509241c02140441c2c01070340000e20000d0302e0004010074222000c05010041c01010012555071170110b107401504a1011003d12402070423440b194000b5030282c81b8004600b442c3c5045200054004a0720704400443c450301ca084141c125114801c110100500c4000390940d240302d03000069440c1d0b170240d4003480c1000e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 972385908 1250 972384658 972384727
    0x501020903071d06010804020612042103020d1b0903080d1e0203220b0a020703050c0d090f061d09040305160503220e06010c080d06080d1416020114 65
    0x2243c808000c005041d5604028100d8104009616801c00310f4440b4001c1c1c1c40c82524659480c1400002841e6607940e540c4031142d002c0501c5202989a0090b0440c030f4100e04003000060011060030400c20811078003540407540100d01000030030044130140280c0494641e010850300111150800220b0864a2004030300d6800b01c280f180e494061618007444442d88100e000c3c09a82c0c0d41c441c1200d55800070051060342c3c0d000200d00f4100744c03144003030f600300b032940e41d0464055181c3d1080c00307840841035000301070710040c646100044a902c910305c400b0340c0e803540c03034a5080130000c15028480b07182002002a820b00400304129021440f0341d1607c0c1c440540514007640d04d607488243c04904000030102010f061085c1c3c0803003404001a2141100d801c03a00c2420181c0b035a480500c7c00034610b02032030b80000812460700c5400a14000081542c20041c2c5441e5654680b0079441103191040d800384181d11464500d40801c480b0043d40100d080c81c0c1c00e90f4044048a06050b841081d2440d02c03280d072400e195656280e0329 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 972387158 1250 972385908 972385949
    0x7030b01061b0312020903150a0606020f0a0305030609220b01140109060206150f0d062007050a110a0f0f030c150210020f040306020d0213050f0a12050102090307 71
    0x4880d41120b005103200380403480c0c01d03520024040103800d44807001150b03000600640316a41000014007610740e0320420701151400500190087c00c01c0e00c18070000d030250400080c1c068a010491200302e50345a1113190858a682e000c1c802c03000401446000144da00040034003044103695402080f1610a440180103503041265201c02061904019414042940b1040c804140c0103c0c0155210600b142440402e2f01c6050000e04404201c291551300242010b41a40501c00d6980202c401d06004011340c0035040000100322040c1d106080000c0c0c001e800c00300c140c0001038070100d000d0f40a03800c0103088004143e101d410894010340d659000200c09800f0705001c00800c200f0040d039200505104074a01078400c400e020203521006900785400220341e0026400950a10040607100038641002c011034568000c00c441340b000358451801444004140600000d283c1782403040c400c401b9001502c101802ea05d000c04410203907018900440b4255000e1042d0b141e16102000460700510041c805c1456000c41c0702d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 972388408 1250 972387158 972387167
    0xd021e01140a020a1401150f03060501060816120b03031b0f0604080306221b08060a05011e170907051002030a050a140702282c07090807030b0106 64
    0x21140740c1180030041c081e0070802e0b600481c0d01c00f42e003038110b0014103a10f907041034250300401100d894140c07480c02e0028003290b07112030303c0800c10541e40703e8101044240d80ba002c040d035204e41c1c11203440004030141480035100d144242e6030075905203e02e42004c52400c0c1d8800009007541c008184d1040392600c02400e901580b07004100403414107814901810090400351140c0d0080e00c8000c080f54000c03101c0549428100301404090021030220120400600614103048485d80c9152200b11001503400004190149008101038007200c0b016101d50181070300d02c1c0020f02071071310b40d821301005000125204803242002d07502e9580c460034000002e032400d9800d01080200c0c1900e00402c40c002c552045c403a81018980000489010001078240603c20341b210107003801c920302c50214000e4200d40210300001180d0080d25400008107540318200303002075145c048084050200c40000d0a2405001035000382c100c011405c00c03a00141c5c50310f80850360b00c0c0c0301c5089500e0003a190344202c172030301403240040003607a030303c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 972389658 1250 972388408 972388427
    0x1020714090103022407240c020c0405100503010e030306030d090e06010c0c0308270429060c0a080a1b02010816050405030f0c030d020307200d021e01 66
    0x28000e0603095500d05004103034441d0341400b00900070314504482c02810304206104039001c036082810380d0303a143c00601d069610840e050f8000301c0f02c50701850200130100054090804111510703802408a000c0a204110144c0406400180c80040b0311401080c0750700c0038050520300ca090340c40110f030b6906006c814540760424800d611402c1001d005802d103c02030b40d00f04055080031003440d040b1411031080c103082009001c07507031000340040c034000f462400d80244500340d00319074a010201b034101c0c0c3c2100d806000a0300c0d1302800d85034044001e12400803090860101807402c2d0000500b0042c1000c1a10200038642992800242c50084001c81d1501c101075221100a03050700c0ca400e491002079203242c2c0041d1107240c026082e81400015900140f84c950b2107802502c005250003422188200840d64045494050b40d80f0264084e00844014074516400081151070a0b603000030780b60902041c1c0e40100d502c11504540990340081c1c410300c49400740e580c40c4c45000c070310304040c807850311056603403400503225100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 972390908 1250 972389658 972389669
    0x60c03221205070b18060304030815031605130b0301051f0504110a0e030a1e02090901020a200307021503150315222a060207051e061b0309010207 64
    0x90003500140002c18400100c60002040c2519500001413445c4000050a107441e00002d010080105050380a980c090040d1030040340d000900d50800240750f107900c02000c0718602c1100740e640c00c10050402d02200c88080602c0c0000040000100c80041d00b510010f6803101100e0004421105124561241c0180145021a003c01c124200d04540003294050040b031101801040380649486403010b0103c1e04005a02c581216680c841c20b000e580804268004c042e8000c40d1458009417510505100307c1d010138036181c403035190101e902c43c1803014001c4140051070260205004007001a10380341c10341d80c000001c0a01041d141e2401f4680042175400c001c145c54442c0e030080c580300011080308004960800d038150365180c0d13100c441c1c2c96948003882058200034036942e12480000c41c9402480100003848204500b82d13941240d03181002c9940340000d02070160f014580030452180203445034a00a0031020241a00c2c0c20724604040c03c41c13800c8240b0070109810740000a0890300396a05110721005000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 972392158 1250 972390908 972390929
    0x30a0e091602060420031006090c0206010807030809060705010606020303011502010903170606040b19021504051f0f0905010b04200f0c0102070b0907032904060506060c0322 76
    0x100100a650b20b2002c0d1024082c445030144c2d22141c11255504105803180290440c1c04621400c12002e00230010b80c411180c41500e0a2004400d1900c00304a107412941e080d00101151800c5803600d141030f91046611540c098420000000011801e00881c0b0040c02d007a00650345a6142c404094040c142102052045900d040302000c0000d820507003503240402001d560101585d6081c0c04140944074940042c0c000340c2c07012078050303462a0b82c0303014004041030325402e4841141c1c80d001c0b200740070030081c6c9009101390801348030386040c40506180002895a0103401164031003005001c20101c0e0300d04d500035180d594590b440c20000341000d000d10007141d0380e4406002ca4688006000c1c90075805a90134040e51070b10300046078003010500f501079540c903e40242c6184050304111030a01d503941000c1c8001c58280c12078503081c000e44110712906d0021441c0a00d01c801503aa640c0d61501c009200c0240100d91080042c048100211001c002401300c04103406070b040610510446240d481c0da80c0b5a01003820034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 972393408 1250 972392158 972392191
    0x15080a020f030a0b0a0812092106011202030316260418020930010c0302390d0c0c0506070f080d060b0f0910020109110d080c030a0e09 59
    0x169100102c07640850040d000043c110700d0580000d0310600c859101107024420203064080c502c1245009101c0da4104455207040b681241d0041545480035115000391900b00d0801004050a07043c40205543c2c40102600d2400902400940d6256825441554040c0f091401009142c8909003504200608c0d0406513003418544000020036100c0000218210b507004030340380c5255120081ea46851659000d91242c0d451541c1c0e41150318041e1800c00001158244076814071028001e201301c0d200c400d40855810f007900e01182c138156040303c10580440456401040701130340300500740700494030040c036035407000f440b5a03050800300401942034101a200d400700304010b100156006102c1c841080d880340c28103403501c01171581b90b030043c02c00d80e009407040d85000401400c221810700c0100b441b83d01c1203a89000e10013580008030f080f94000c08000340340810110000c1c40a02d8280c00001e480c0d44650381d8249803543c0c0301c40c000d040d1303000410340380003003211511140e040d0f183c40c9240f0b13640191002c1054440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 972394658 1250 972393408 972393427
    0x1b0c060306080d032a020708010c111005040309060c05030c0a050d030606080112060509120d0c110c0f12120706140f2a040915060201150b0403060e031315080a02 71
    0x640c00401140c10b40171030038a4015880700d0081c840d240c018040c080080140340700003a0040d043c1120718403014080e02968110fa018040f10388501801260540c0e00c02090604000003a140030310ba05a091f1400d22042c400c860180800b0020307840c400344541d0181090711440304001c2d05603100781e00103005010750800188110083c801c0b2903080c1c2500714a0124a81e1240d4101e01e04001d80460318410317004000680c1d60214656411a100862040d92034401452441240b6a140c510034050f0540c000c001c0780310003110f8540702c0c1000c01403d1040090f52b0010a0550b04141e0540c000c400868406440b590400420120790243c1c940c0a4061400e054152400b0301185132604e01c40083c080d500401d00c20f0703c403500c130000700580b8040e00001c0320400800d1441d0404111b074548610480b0010f6080056035003065081c401c11a04540320410840d01742811613460f0800707801201c216400500c000d0090388141c81c866045603000340152035603840c038030340120002011414011302e030055850040260840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 972395908 1250 972394658 972394691
    0x3090f140603042105070c06030b0907030b13020d091a010b0a0f030b061204050105060307060c02090a0b09190b040902090703051506040b0a11070509071b0c060306080d03 75
    0xc441220701079540d82e030710300c2c2c0b001d0040c000720a00c8240d901380e0b004002d0002d0700300004180c098010f14000e40203d61302c280c2107041d9400c880c0c560703811642580100303009034000d410110315400000c02d80900c0c5000304150070124cc00400300503100d151240d038107409001e900020025828407200318100c2c80e60404142e40313058800c041003030080004504000f00824842ea200c02029100100351550314070030951841c04400055a040e80c540d481c00c400b00f402131800207010404c43d9501c0d01e500c54185410b40070801d201c5001464950305039203030005251213940c1c0e203410382c0c40f80e5081a0540d0130005204514402c640341c141450340034500d0040c10b030015a44012044d54016218680131a1941e60032141290003110300039000e400c0390010034081669903c000260616a04950720440d80c0522514856a51900341c0f06242e0025000b0000c40c1542d072003500064507440d08a01901d201c00c010759100300d03a0701499401100069a06c1c002840f1000d03080c003a050000040f03140034002d052020300c0200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 972397158 1250 972395908 972395939
    0x330309151103130602070209180606031c0f0302040906030614090601050a090e030c0a0302031e0301030b0f10030f05010c03050117061816150906020a05070e04080705030d0903090f 79
    0x2045035016040f500300b04252601110241c50340a00542202e0038801c07681038050000d40c1800e41240540000100c030340c20b00003941461030701101031040d034074503401d2815561100d806c10b8000426400b00404103001d4024001d140080d4440c10000400300760b08030b8440c1040700b001d02502d105401c1940100300300d42d2031254010030303990301d4680002d490301c0c0f00420307600c1c1d44580500d80c480c5004039043c003401d141e00440034218110000b040c04210001c092949440b80c402408014030852141c400710f041e42043c5441c89900003c5404502c0100d500ca072075020310381810260840740d5039140c4410b810159854000c0c10300400100c05c0800052050148207a111500180021404110714130001d0741c0c0c0000b000501a0804d2040d6252046600c51072200264a041c5a40b503010503c0c00800003030080c030006040d00d200d03410402420000381420785c102401c10003e4000d90744407400340000c0010541c18401080040107901000818515914018141d07080a1b030010000d100d450781d081106942000140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 972398408 1250 972397158 972397171
    0x6080c0711010c0b07090302040606020a03120f090206130810050915090316110307080c180402012615060f0a180f030302030a020f0313330309151103 66
    0x9a085045040102d401000f110340c081c020300d44507030512204c150000668001d5a000342e40903c220382d21a001680d54002241c4014002140c424126010100d01e61000c43c07940046540450724410310380020328a60080d00d98040c011004840400030752004002440d04242048020b000e24602842c54540310100c03054002c00f001c0384c03d40001c844500502c1140e070001009601140c514109040100b101101103071104d01034071601802203615240091f848103041c1005180701407084036921040c42d8204098801c90601079a900c94807643d07c5008080080300c800c01c03404800f14500300d0740d28603145403006161405180104444506109500100c9410501605007010742d03800c050300c41844044030358000b401c0e10b5000b4502204040e800700081c0003903901c56088400c200c030b00003519500e9114400c600c5440e00310641040114551024600c085c020b025202078034400e1070b40b00f10010401c010544903000a595441c03805c200180340140501614004000b0803844031003c03102e000c148006002c1e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 972399658 1250 972398408 972398423
    0xc031b100311030703090c08060f1810020304080c161811040803040f052b0f020d060c020618070b0a11190c06111605012a080c060106080c07 62
    0x11202081e000e6000350b8541414903422070b075640340c207804c024010450204116400b83c10f6403000a030458001801c207016034100400c0c000c00d85c4480502400205001601c5019405003861808a0f0440e81c0f01441c030660150300c202e5540d00108800d182030141d0070300000e0a2250150301881504020a032030201f01d1221600001d40741e0308441c000304d26004aa004102d144000140032030340d0318100a80d5821940280c03403203101d00d002e095210038041c00180b0343c050640003051245000c5006600c100421a001414103102c980c1a034603a1416a550340d2040c5002d80d2028051250b03034000004601c442620140250100b1800e1103140509403007068031180810003021501c582802c0188842045000302c0d5590030700ea0841440c000401d0f0115114110103d001c002042050401c0032602c500300c0584510b5529817a406c0070010b480401d554200f050044032038450400c40d03a540300141c0d10450b0f00078901079484105c89402d1500d0424141c00c60b9040014850900250344201030648401c01d601204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 972400908 1250 972399658 972399679
    0x1f0506030a0506092803050702040f02210103020319020d060510080304140102070f0501050706110c0118110a0515031312030c09080c06090108060a0b0f0a020c031b 72
    0xe850151041409405401020240b20780513070006a076000b00500303250906203540303072412200705203c841540600855000c003d004011b203002d5100b02d005400c803141c01070402503c80e44204040e042e42810707840419a1900500951408000341c90014010030010801d0301e4241d4003080d080a0700382c1d001094136844501103201c2007203400100b8040c107107400460352610360361864071050541c1000701c2400b50164401c081200820030442105840c410303150f492501d480c070f035510320003040c014024003000304050007000c62021084c095022100b0f2510b05898148495007040c010351098061450310400346030808000f151654802c9084004140c00580c0e102c1c0da075900c91100c010481e03003008105020440200d04580d4056004400720340403607484210b80c540350302c0e1003551501d0788500f0030307800f060900c4040c81c150702c03401019520140c080e0102026940d104c070a1120341d00a1404551a03003400308903c405150b040140441186040b0000c00e0324801590b03a810994034007180c0a80a0302c8a04c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 972402158 1250 972400908 972400921
    0x51005040b0f03010903050d06050a0515160507090b09010e0609040803070c020306040606030b0f0907090207170708030403110a020d0f06150b0d0609110a051608071110021f05 77
    0xb600c0c1445070b901030b00a100e080160715004003254021003078004581c0ca05400480c8a05024043c0401d4a102400d0320b000440c0c803001c5944d41e9044100c604a40040301c3c02400000b40060003800001c01da148804541c69841c00704010b0442416002021807002d030004012440e42c1d403544164100340c029554990f1f0f5280c0307880c00c0744c103840c1280b80070750944945401d00c800c000075a400f0741c046a00815040307030a91241c0e8400c15890600b0b0346e0050440c4e111000500c40880c142d401800140e11030220841c085111060408407500140001c5d100a40040300308003e160700410204c0c0c2091082002d0075401c0420350000d086524001c84c00740079114008000010800c080d404045201000130703c0c24400c2d0707034071941f601035948154589403d46007403050000f050181802040542c0114203207607410140b24080440c1c0d20b8001903243c0030110340c100900300c045406a4000c201241c00780c03012b00041010442030050b0a2402c80000d000c5500c802010103c2d40b19800c50003a2110705003001045070b072500f0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 972403408 1250 972402158 972402169
    0x9020c070510020a060e03090f030307150b0a0302090a050610050c030a1b020616170c0619060e0903030a1116020f0a17030309160617070504210302060a051005040b 72
    0x141c40141175501d84040398400700800406040220b008680e1044d0742d14008007415128020214000c1c62185294018420340110b034019040c2c91002a0244002664031303000100d61311170588840f8aa90380d076200380141c601300004c1100c090511400c0443c50144014185070352403040001c0300781080000303260180000c164507118400f041d002460a034940046400001c030940003a401150710020080e60f41599150980941d0000302002000c1c04e5907a48040f586142c00e00c2c600050076a259072180042600018208141d00900014005588925040b13900700119030000110750b104039014480014002c4100300c1d00c021644e4191501c1c3c5004242d00081105c0c860150410310349421070019920a4140001c0954440c0d0034460888030540d080c1550a14080c8182c0180300c0020078007010713902a500c15000940c0c01c403141e403829134900756440310b0b80c074122000507800c00507004044503180c040c1a410401c190f04000710540c01c0001e420111403441083c0c0c40c9125441c044c42c0c641c844003c841d6600c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 972404658 1250 972403408 972403423
    0x103030e01030f020a050309101109010323090f0c030a08180315070201090605010f060e060a0207080d091d090601180b060a0302041e0b0d09020d0c030303060f09020c07051002 77
    0x3c00c001991180e00e03034000500b0f56001150225100d21603940d01c0b08440360346004046410008001d56441e01200b0b0004601400c0104020500c900170212404545000ca100c2c00d480f654040000c0c1c042d82c0000740c2150b081051800d400d611940c8440e030301c00049181c4500b100c40b00c00b100018150300c00d0101010a003403001c51a08424034502c110104401c0d1074040d01701000c0503104040400c201c1ea200c112508400405015000000d0080058500e00342425001880c1c216100d0044440c4580d64450052030700741c4c0d4402003000600c4181080040a03c5000504540c0d01c1c1d00b4040310a915014001682d100014440e596800da180c040f0100040e50540c80311b080c1341401f0384605e590703000245006e00070f1b6105110300070b18203001e124885101840440d11105480b08201001d14203040c800304000036200a81090380e00c24620350612001402518005e0000c500c00c0d140407941d41d1403e41c091202c007007075600017601e07503004210000705510045208402e5450443c1c0e800100251100200d161980 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 972405908 1250 972404658 972404681
    0x100507140d0f0e310c0e1203040e070305040f0b04060606080a050609070e0a1e03140d08040206090a05033f070807080f0429071110021014040203070b0708030103030e0103 75
    0x85c000210901300e07804000859020303800e4449100031004100115a81c0c80349105080884070300d41d0200c0c06140c4280c01107500540a030424143c0c669558858034030000d010b17603085800950701c00c2c0c20002e00d900030005a0b44100702e1a001c105619103000411600080140711000708503140542182c582e548070310f5400500002c2c0d46a488a00980c0300600c554031031408103a42103e240440d170844030000248410001c0701641e1402c8298489030300f1301c452604400c841a40c009c1d80580c0c0450380d0b0f103040204640c0c00c0000a40c840281e26840421214440d0011001d01c0d03500c0d80081c401180a00307074003211009503101d18801c1e40c1c1d06041c14450414001c2e9034208032040000100041c01a0040c40d015a40e000c0f100001036441d520170300080c40b00d1052886c01020b40c10404001d95072481c1614031f4102640603030065901450341036003000f0860f03050601084041100406200c2541000c2214901403c68108d07520700c0c042c9207840e1002c8900052000504102d1908600d814591003504000103101 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 972407158 1250 972405908 972405911
    0x305150a0213091d0106060203120403020114041506231504050409030c0c0e010f06232706040e0c0c210d0506030105060609100507140d0f0e31 63
    0x10340701c1140d403004e4110340e404d0b041c0d0351039004080603c0d043c040c03040f1402c0702c2d210740003036140041950300785601500046c401d40c00d5560764034000c500522030400640c803c600c112441c1180c1d0b005400b81c40204d4449070401410020070303508140b052041e20301c0d030406051044170101500c20811a500406200b42e4100c42e80280c100310709d00302015081000c030702034903104d0310806210f01e4032126403040a1f2001d01c21824040140d810400ca03160103400a200e0304400780c500d080e100c4072001e520400c190701045400300e0128500044080b204080203404401081c129401450580f0380641c0408031040600f048030307600c100058000c2c55410400c4041040d41080c5d6000c8a441501003203001030b038004160b492000341c00c101c0000c540d450f061203420f2040e400240540e007010000f10030303c02e036452425100021720004000354404550200004589000c8a000070a03240f810b080c0000c00d40314404504600748050740e0000c48544d982c100d030140c05801e15403003500401c91708070b10b8120700a00481520f51b046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 972408408 1250 972407158 972407197
    0xc0f0609040207150c1e0e1507060c050306011b0803010509090a120201090b06010305060d140705091501030c020d0c060203070306090921140f0c07170105010905100305150a02 77
    0x16861500286489602c2c0d0300c600c243c44c00d0102c490b0440d80d0030310f80843d0000f40044000c490303500c0d0100500c01d01c418040701230380c00c0101c250342d0401100e40c440c0117940818004401c2103103a40e0300001402c9404c602901002c004102665410b00601042c001e031481040c0400004031040004c0148070207554005491142807a00700b44060300a03c0f0150056a0301e84807040010300d40c1d4003d001e01801004c002d0700e5207200102c591219480010780722840c00082c003421200081a5a410f42143d0042343c08480c1c19640c00365032400501102e0042d004002075400c400140401c03a90480840c41030381d030f0802e5000d603580da90003404a00070903054202c003042e07502e411220302c00c1c81a55404200f400701514401c44000081e41c1d03080c0c43c4141c200401c0529868200400c0c2c0117520b10401a00c0c0c0c4282600848038655201c01c441c0d41c1d105410001030035680c0d584c00c01009a40824011280c000d070126900c0018241551182601e903030400d1106660a04054003080592126504550f181c1c1c0e0046a0005017 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 972409658 1250 972408408 972408443
    0x29010507020a0e071b0506041410142d150a0e04060b0a0608090d180b07050d030b010e0f010c030c06050c0a030509010209010504061103120103230c0f0609040207 71
    0x103a42c2550000e00050b41da0b640122040502001d4480103a00440100b603d666227988285c008881e000c06040d00e4004c090b104a0800c1a500526100f01c0d007051048003241f50407080d0021082104040e44052208842031f440007556034030000d0f400c000437800c216615103890700800d003880640e5001011401340502088244282988110700c0a0002c43d41c1210260351480d0072113005600380c0d44040030303411900c2529030850141d2603007041410513484410a80e030340c80e4030141560304041d00c02d84103608026180450981d1610071183c6a403000d087c0000c2460ba0301d0042210010407880d5076050002e410f103a034080c94002e0030b00300071b45030384a003041c08a441e1030101b46010f50490400342011038104400b241c00c00e001030094aa0050381a52540d003040c1c5007140444086e182c0111103443c1e4041000010020726054a080380618081d94100d03101001d41c0350001c100424001c182242034102040000103a915040b00450f4440120350143e100c01000c0000f034000e2103085002401d01c1b0790481d00000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 972410908 1250 972409658 972409679
    0x9090f06070507110a050102030f0d0b0607050105101d040803190c0f09120f081b03070f23061b0c07180605120c040207140316140129010507020a 64
    0x140c40c0f140c0466011180661300740501800c4502610380540c00a00802c00c8805145001d000044001400441c1d0704080c60003144081d8000c42c415290399460f0320030080b40c00314000003034008100e071101c22044007812181c2c80c01c0500003c2c10042c030100000020070b8441035003030112680d0645049082102001004014103061603100104000c5030300880c1c0062000d003a14800c52440d034100000e0010040c41d541c4003080c641c4a0304a4140c21030488014584c1a941040948081486002c0707824940b03500b0b0a01211480390301d07800c002051180001c4840540001c9810341d040700740c00150391040401b01500003071a0040f800410340d41d100711100054110040b10805840031040742c0104040e039214000d0011044000266809035404201d0000c00ba050650081c4417280c000c80107a1014209000c0107030071903000b0781010800301840c1100d1420310680c0310260418a06100007002005035040030406180c0e500c24003004c503060000300e0f2004a07400b9004442c40168000d04c00d03221591600800e50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 972412158 1250 972410908 972410917
    0xc0f060c0b061816081e16140706020408071a0d1a061315030c1d0a0f1212031a010e15070507080c0604030213051009061d0a091109090f060705 63
    0x50000e00b02c0e401044900b601c1000f1a0101d2a09059001440c0e43d0b4021001500240d40540c20408c40e0160619540b42c100310003800714103219a10141e80c982c03505004c1840c04d08560071001d0010002c01000204c140d0071012602c82e00200500441d0440c001c09501000007080c003401c40d001385000034902511018070b502d44044c0c0315080c1007040b801c00c0b80d480840403591226502c101144182d903928201da60310480d11059098020b18100c00c20340c4526000e0060394056000020000c2901c2c3c04104000c1c2480340135440d500303189001c02c4441c405030741507807103921030601803410702c1102072580c040c91710340d010170304040b1000f90040c076502c026901d0190f03039411151107000c109000700303242c2c80c44924003071003150102c0790002c061030504032139075007090000c1c83c0140c01c3d06015400d82e0b000003440d011900a0720002c003445103032180c04030040511440d40900041025941d6403801c011940000e03c915400800315030156900074548e51083c00d0b0624000340140381c0012341c4100d00c200001075034400b00a2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 972413408 1250 972412158 972412201
    0x301080307230c0d170a0512090127061d0606030601080f03030a0c0c06060311011d0a350c0a05040507090905060a0b0f070c0f060c0b0618 61
    0xb01061448081039402d11021210100300d55084611144114500314405150082c040c4c52801203003000c1500c3d1140e10f501c110780e0320700401e40200f40041a8040e101e88a81e01144900c02400f980401d1151800c440f00500b0030241500344d180d100006001d115880b00f04407031003800310b861000c00d0058103a03555100484c0e045100c0d00c02c0038004508502e0104401c003403501a18011030031600d80c0890040501070020360802044108a80340d00072a2480c002c1030010341c007232410495140c0b2a5000141413010001c003d000900910603002920740701c0604641c04c03201c001c0e108403111421450486110440d400b1080c090070701220b07070080341c288040380c50410f10b80100c6208500c690f460091106442c8102d9010b80400c1e00b030203003003000d4801e940100ba407000c40188001400ca8980091082d40c2e000305200f000d00c1c040110300c00c1c0c10002c000c0482030241c8000004098540d1404000815141c008280103002200d40000704a031912031007842c81099072003652110b52480d1249160381030702950b1541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 972414658 1250 972413408 972413423
    0x40801050a0e240406050403030905030703030f0b0406060c06111314010f0c2307180b12070f360b0f0a061704050a0506010f09060503071220060301080307 68
    0x1070194902d039180d03040c00302003110304900f426659103486880040c40020001d41c01c0c95110070180d030005205000400d4890b1090318001600d2a101c2c641400316450109940d00036031400c04244105904148680c24540e484107001c1514002c002c0c180c6020300421040d807108900b00007002c01d00310036103074806420030313001e03071750b001083c0301b06807045400d07c05502015090303d0f00031107041282400d641140d0030009071401160031480e030b241480b078040c01b40c01107000c522950322001c41700b683c504441404203401004000b420380d0b82c14064000b000b000c0070310808a001c0400701200740021002c80d001c808031000d03d03c907228100704091819000e05181221207110383c2c0014036003241352803c0110032090f00ca80c1d541b4050454220030705c0364080500a0010742e920310030761500c0b900191003001050302900c886003000c1503a524001102c01954559002903100e0b80103024184500707200340c030505c401190841d00c1e40c08640180d95a00079211203005000e80c01100000021907410400401820754611030713040b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 972415908 1250 972414658 972414673
    0x2a0801050c2107020120040501020712020102120307031b0c022e051806040305010b1009060f1d04090302010c11030c0303040b0903040f0e01060329060c03040801050a0e 74
    0x561110340d1141854104502c20151600200000000d20565018010b4000001e181c0c1800780b5041c022030720000720480e40309000038188810350341449144000c158150550301c480005600103915184140302180c4001000710001307240c14400e030021050641e05c400751401c51503150300001c101440a0009070b008500710040e80c03120030300d0840900b81c086044045000f0344002c0e118121102c6c0d2000e203054061104000385212584c1c2c1d1103006200844c03040000007094100e4a003800308100c0700f10144414400c0b200400c01c03100b5000685000c00c0d50080c900007100d07071615808856085103245000350041e240540100400d80c0543c0030142d01245910b03651070003056040c481c0d40d40d100b4103030701180e036402c1400828001410b410155800030510b0040e2801d00b6103803889103490024a60044207072603404c01c01000503503094807806403001c5800d0f01502030841241c1502500c4802c03618820f00524001a040303042040a0068502a1407144001e0040d41401d0b0180f40240602c111968014003031144c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 972417158 1250 972415908 972415921
    0x1e0f071a090a0204020a030609021315020318041107151d011e0b010c050f0d0815030a030806060f0d020c0c0a050a0e060619081503060603192a080105 66
    0x80c1407281407100c00901001d1aa030b800d210203900407801c10f00034076403140704c00728204d0541c0c00908a0311140d4030f071113030819140808007440c2e88103410458095400030407441400310450284403c241c3c100b0340d000b29044200ca01d002c141c0e8402c8800252034141035603614080018aa0051038102c200300300071114081402010a00701c030600c1070090204109407c40d01d02e150400e0704080025001410000c4060b001034440609103c4503000e030b004070f50041d6580004040e00040c28541041500c149140c2c04e00300b41010039602c04200c240074090102c4900015210342d0340608450404518000c1940c82d1140c0e9000d4101030741181c2c80f003030114000d4140304081400d11030b0308242220700c0108041495840c140d048003140c000a03112a400010800c5001c0d43c0002c9441c542442ca00141e56208440c9041c0110546202e6051001c41c460340102c400d0107419035000408010207011810a8a40e84096242041001c0c10420b0010a04002c02c00c3c01911b8408500070401120301d5040284616070320030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 972418408 1250 972417158 972417203
    0x303090308010f0b0a120e12040e01060c0f08090f03070f140909070e040804030534050a15170c0901080903030606040311060c0a1401060b03041203021e0f07 69
    0x600601360503030424452000340c24411414241c20006c8040001031514118a07035a0809107007402d000d5110200003400c01c46042035520450041c030f0740d490a42c41100c0306695440c40d9110310603000e01042d1001ca0319140b550390b4040d00314901f44004088171003541e03440c0325004203803090344070308100f031000204404110f040540c2150b00c59640d04c7c0150120a082c000c1d0b615000344003610a88009100f40f00202c00620100b146c60761000c440a104800101599121311260713554034840134505003070403000c221035116040c6002c140d4240d009c4542e003028009000301d450100403080484000c903040f003402480c0500c0d000a007040c2100b079844402d5035440860150b96803200390784070f940000c001c01c410030218404a80c58410503d0080c5882c4c0f40c101440700d614908036006a0a031a41e0140ca55071040b42902441074070010300d0807040141c103503d42500e4a0840784003128460003419000540340840301c403c041e0001d400f1014211013915031614240003c29900040b008a5004030786000440420310003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 972419658 1250 972418408 972418439
    0x605030a020d0f030c32030a0215150a090614060c070b160b0f241c020303130e100e01030b270a0542090c0409030309030801 55
    0x600002401901d960720543c1034030b10a142607041068040840e400a00c190b80201d40343c40b40c0c2050141990202841c05140d0020081d0007a4581d00422100d1040d54000c01d00e010f908a001d030f000102591002101c0c00441a801003903644000d009402103a00c0340b00d584800300b5201d00307a903083c022881070024461544102d0803504210340c0301000800c84600c2d410000c051102c5074030f00c2002c2c40c107000e42c0c0b4203030040b10039208250800203600411495111101a981400c800340c2e10f075003041d150540c00700d900398407007041c80c1e1103040b000c0e52503206644080084a044281000100b0a210350b45ea203801d8001205855120702c4810b02c500020b40d507e600700b5114140c0360400054035483e02e40010b007080954043c00030008030701c010007500200c154103104040a00740202c02400c0d1240f19820010000d1203001c0300b281c901d8200450070340c8146000c60000c46658a8444292030300c0d1551800c0e50700d89261105039513030150410290008051b410b0f000058080c1c03080c0c9444a143c0d032103919100d0300781d20 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 972420908 1250 972419658 972419663
    0x40909150e100c0302070b130302210f03041e0506040b0609060603060609031501172107120302120a09060c0306080c06070c080706090e072a1a0f0702010605030a 71
    0x1003140202e20021540154040215400d00500e051907e56800f101c03100111041401c182140380c8500625405110080800700791159071491007411103080c1c08140a402283e81c201d00b8088001030420146010300b130858036804130941c065072110301e04590b035003034103c3e0f044880c00406004603c550900380c000c0380c02102c00030021410b42d80c82c10140212500000200c940c103103d11500c60f1801d1200e80c141c503029002c40c036120070700e0000f0300711420300d004683d101602900068210a81500c640c02c410354000c20f41c04804810b9030071446508034064014000e0725145401d0070801d00c5001d02541d81b00c4110302e40b0410040c041d1104010042d81203a949102d00750041d01b0202074080180f51403c0104034851042c154140141c0e200c100329450480c054000d0000308010507002c0c004060a0701c0c1e91940012a4548004100c400541001084540d0900e0030005240100c490080040e0040c180308980c1450003a0641440d042906080114040d0394440142d40b13041c00c00b0481d41000319621480a4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 972422158 1250 972420908 972420913
    0x1b0c19030c030b062d0301150f1a04150518010f090608060319080c1905030a030c03390e010503010e04061d2109030a06110906040909150e 61
    0x40c5107898103c0c150f54020855603100d9264490b01130b03100c60404803a0b190040d0aa280c2040030f800005140c2181c0c42040429101e0320081d8040281d46e8020302c00c0e40a60b41486154012200328000000c0c690040e034102040b401c45030003a5001c00c540c01009440e030017624040c50103c06940e030005441c0c4050703040c0f108002805010080c1315031400b60440726040000030701140d010a9101e40400b61000384500215102e600006009001c1581004000c11a060f94400082c03201115607a4030ba59200700901c200c00e042d142d000c0c47d001540a5405820130740201c0311380284941144031040581c20002401e10403240714066500203041c42416210040a410385403140303140d007049119068802d006200300c03071060300c803007112041905002c98030170301d400c100b0000d00c40641a1543c6001c140c10890348603828050511454501c4d0780d00240c0c120000c2e800c080c00195100c00700011000910034102e40c0d50708180700140c002410940c6603c0017841500500807283d03903000e00860901a194103045600082e13 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 972423408 1250 972422158 972422183
    0x5090d06090b012c07181d060f01020307140715120c0f050706020d020408030412060506091e041a0705130f0f030803070c02150d050708071e051b0c1903 67
    0xb51306907221a04042c20f402c0071030003209003100d0344a00d4201c1e80c0007040d514501110a624501040080c0c940008007183d44001d00210000000d59074024030b0b90150250300c0380e0b898030341c0d05101400000003805400d0214103c0e882101c101420703021120314080c0340107182c008854030030391013110007020b0324000d544da080c13925030b850f00e80034047c1d000a4110405a03908001c001842281040280010903001c4682d20307480140b800c0c51822134000601c0300340240d0040e41040412011500940700895007007060200d1603c40d0300b00200c80e4070400b01000700002c210003c4c07046464011015203420681c48074442c4040351a262000c541405a00c03800205440006050001509010213154040c000f0f2510742104030041d00050454000819900044500005c0342c2528030008d0040c581e0181d2903082c6480141040e8100504954400c40e07180810703a481803001c20340520032021035801c004882c4698141d50340c20b20587d43c0310360351744c0382c040e1213071016071400090340e8042414007049031303007003011503405 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 972424658 1250 972423408 972423479
    0x6031a0a0506010e06130906080105180706050417010f093e0d0312060b04170105040b0414010902060c0d081f03060f020c10090201200307020f0105090d06090b01 71
    0x45400c050006c01302d080303ca800215540b4204e100b00741c004c24200340040b030313a41091428084040861714010813030360010b0030b040c0541a000700441c0c0840e03402007040d000b0070306100311440c01030514210311860a0304003c4030205010f20150040c420410320710f502c00301c0248040ca0314807100c0741c26603203001d07043c0140c0000440d03242101c0c4080011740a802c002103446001c48004007212655000040d001c50003260601103800544200d844131040f07400204000c0c101512482181d0f8030080c00241017820001060b80d010340203400000038641e001e001c4603110315040400c0c0742c880c2940642c00e000181d6030400909000d218a844209840090103155640c2c1d0560702c5070b1000e81420700341c610b4030395000c10290070181010081d030f100c2000781c4a40050300500b9840010300b00041907044a0188c0c40c1001942d0144a004c005c490300c041e0704451000c032843e410001a185406007900ca50340c89001ca84c14030040c40b4142c0c0001d100d03030744281d011075030700c1e03803a81d81e0304215906641039001d90a1448105000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 972425908 1250 972424658 972424669
    0xc100207021801181407080a0b031207060902090606190e150301060f0e04050714090d0b01032108040309030f05070302030615030f012d06080106031a0a0506010e 71
    0xa1060002e400e0b010740003031001069203151070a90150100e0790b010780715001604100c0c4a40c6103074000d900141c207510f041400004208440182503c4181903850400c440305503010401e002c9080b840100064440500c3e080410080907210b001380c1c05100d5641c005000c514215085690614403418201c10000c20318104036480002d22030342e940c01c21082c01c00d094095241d64040c44c000c0610f603443c1d0f641c0b0114018020100040c00880380c0c0207904003c2031111041d0400e910005540ba44078000e070f11000101c1c0041c40511813130001900b43e05c3c440c000030080c01401ca80c1c0c0e074603844400500c0c0308084080c40c821140c0b6541140c0140c0024810342c0f043c4000340709990f16465681c010001c40302c01644a8000a040c0138050307030480410403010251141a04043c0450340e80c0c82002402084001000301c0e0345040a03041400001d40a000b114240040c4802c035800000030700450780c02040390503246d2a240c101c42c0d0a1441c103140c440d14043c005503001c083c0f4028240710f004107079a044c82c0b0740d20301003d210 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 972427158 1250 972425908 972425917
    0x1b210c010f0501120303200a0c050309060c0d0815090103020f01020f01050a020d1103090d050a0207120614010e090a120210090b0106231801031803030b0111030c1002 73
    0x509035501d501003a030400708503002d024080c00c0001d4002d0161115441d001c1d0440c2c10001c0001085000042034041654485040d1120010b050911403114401858560705600c15403880d154048070100b0714265894001600414040d8a62100720440d2a00c440c281201d14001c0700381e50780070f4945001400141440d2100c0040090180103c40d07664540004890030350703074201c03001030b100361b80456441e0308181c0074016011400c9804403481d185080030b919260310b0741e419400d040d0501800161030300c03065100b005110000c00700307200001c1c002c000614181c03015100740304040746000420380020801303180e02e201c03140c0141d488600170030000314907590f805042d820324007000303003036000c0c440c079400003030f55640500000c061180160b2080d0b981001c0000d06500540d180f103482c2d4803071804010308040d100e0001c840142d280c03401c12125805400740103d0242035a0601800d0030340d07000034402c08154150f040030401c0030090700c491400d43c907100c00095032406021303801c4d407d0780c0c480d40305400c03a482c4550051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 972428408 1250 972427158 972427177
    0x80c03062a0d06090504031215080c040506010c05070b04180608190302190b010f0e0c03040618150f1a130b0406030b090604031403040320071503021b21 67
    0x2040340c0d0b130388150010485d4401c40d0142c010607403403901e21140042e14071454174505050345511417103604000c0080d40d100d1342044a54099a600e83c0400d403d80e01400c1020710030f5030720108a07092183c44034160081d83e0002d01c5200558451945c2c0c01e0498001c034000c84094868503001004d2501114203030446031900600242c096008906942c10006104480190035900800c510040355151001c03000c8602400d602c0000008098414002c1c11071056045981164200102040940d042d465413800107564a5004000c0b41800b0a2084c0743c2c281a00420038452542508000c00003000e1120405c041809080c182c1c0b11550446403c146a010b80c003940e00e404014100040e0161250345000703801800792952422503002030100010158009070041810900d00e4906d0b003141090303030b006805900203500300e0700d0700ea00961101d074040c1d0080011500501811240d460010542d1602400030360040c40c1000108031980c40d1000a004001070110015090100080c0c0d600c20300341171403000c2c1e040900e00303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 972429658 1250 972428408 972428411
    0xb130801110a03021b0d030606110304030c03020d050f0a060b03010525031505060d0b031b0d1707300201090507090903050c100203190b130218030106080c03062a0d 72
    0x60b0745c054a0f04102e500c00008642d18001f4045040003000b525401c05141202ca641d0300400040c00001e403032087c160201c90303043d543c840d206e182c5482e240e402c021091a00311080c0c821a440941031140f80c0c1c00038103500304c0c2074002f004181c40e0114001e074072a07201c2207990881a00381f00000d0f00b03248a903002440d00c0314240030b0401c0c1c05845500080c3d01d64001c0c01401034140d1034115941c280d2030309020000722103d24108441d0f800c000725000c11300c00340050dd006491a0107064600c140107407204110341a0a5108041c26040407030410444d000034420390b5420f20040d1129144426a1700500c100b03440150004002c01459161a1510024001041d4114100807051010400340b004c01c0144c61822a0801009a02c0b40713084403c8200041c00f101c541c1040c1c41c2021304041c15a201d0700f003001c0b040c14410f940503039074001046200a45142e40780d010341e010b61815000103004400805ca202c0001c204400350b903501d03150346201c14920001c42c2103060201e01c01c40e40d0052404440c2c0c2c01040905100e400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 972430908 1250 972429658 972429697
    0x10c020c12070b1b0c0d050a02130605041b090506120406150305031219020a05090906040213030c18020306011d150a02012429070c0b130801110a0302 66
    0x580041c0e40c0108101c04c1941c40a1508248050828012a07804603003d69402c0c50a03442070f1104d5985104034900640280c101c0e50010102444c1c17a00040d010744806001401104c140c502215000c078550003c02001800c184004251482c0000440d48908a1030500001680359611218000c080740c1011900040803103000100040c828009401c0c0b018290890740344c5882c200c0d11440400203801ea04810803032040059040040d00001610307041e01081e51061003540d00d01b000301d8004d1140c040e560f1051400c01e40700001300805112040103480e924100c0039042c860805140c0300b40d00007512140d0101c0c6617030201c0005546081d2004144440c0188580c01e8940e80d010a144258070100c8000c1c0143d4407294a003200090300400f40d2034201151074000d4a142c9041d884d90403056919200d03580810303083c0f1003c4045114401075858454100a01c2c0801035a0b642c2000d0f8113601c0511076060141a00710005440c81040c4900e0920048401c4411300d0004034440172402540303c8480080380415550 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 972432158 1250 972430908 972430919
    0x140d0203120318060112120e130c0210061a1818060f01231e040b1c0207050d0e01050c06010f0906092c0f0316060c02010c020c1207 58
    0x700c40e4580401441145540381001c68803000c3c2e40c14a000002c20342c0d4004401000030308401c070740403011203030040262132002c1691201160040901c44185a0148800300504d06a608940c00160003200640849030840165440002616402d02c994404041c1c1a02c0010800750740340001d10a070020b210304050180c0594000806628811181100317400161080105a05118041c100d5650003420b00303000260b4641008140900c4503250b020500c940031a001c0c016007881001900220194202144c80310b8a0b800320314280d81013900c092030f40100341c10b80c0940c54055417003280e5071940c000014207825519484252440a82c4c1e002d00c5041001c208648000c2c0a81440610b01810f01c40c03544002017840d00405c1d4007540d6103900032419042c588030410801e00301c1090713540c2c05164240310203c0c4026001108038142440003aa0090300d00001a80080c840018503e50850502c03588041100030041c00c0c0c101c1c00c1360840b58042000d03a0054558031401c1c07615090744403491120b08201e864568866 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 972433408 1250 972432158 972432163
    0x60f12010e0402120c0f01140d0f2a05030601050f1c09030201050604020a080105131b020f10060303050a030e030f040e06100c0b01030803040519080c150c04140d0203 73
    0xd80c03106070810007070030900c011480d21418071110503040c440244060385404002419030b40a0310030003410f00c5003200360780b80c0ca0795401d029104885050340040000c0c101c0482610054642d864403e00803240070003c6100300c1d17061401c0c4080300e02040ea10341e03055688100065506074404180c20580390b009026104281d43c4200f00103149100485000c03401c0b55091502a0940c1c4001c0e1940344114014842051469031013040641103483c125503000c400303c42603e9000092040c1c21512030005c038411221915660000b40c1c140c404144403084840005001d0103c3e0704640700350100030009001004106120b51007500300508074408207042d1703481e00c008812070211507031003544144100c001d98402c2105520307004d200018100058200805031501301d41e03c0c91804941408024000c04000c400300c3c09029042001c041c030380301400001000c0d510a420320255541111011615034424940b190070b58001c0304c0c80080c054051016041c0c10325003800c030484854101c85e013041d81c0024a502c09003001d40d808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 972434658 1250 972433408 972433411
    0x70606060507050705041b08190c0f090b040e0105010302030406060f060c020a09060812030a02071a090d0f020606130b03252103050c15190e07030c0302060f12 70
    0x1619029038650b064501607091803100c1c2d000a03c56483d000030011000c8940e0310100d4460000d10b84492541c0c0c0321090f0564400801c842d19104d6444c0c80305060740c04d41c005a001b1107084c072540315076840c03580d10018005540715600520425000c0c010040005501a4000d550050301c5001c0c0400c400313491b50200340e0b03001d8040d40200d0026a420650000b542454041c0002906404809004860030402c0e005d07601e00d408400c41520100c000002003410f0a5070381030355116503203c880700705a800403600d010301d0800d09903600445400303844210000a8060311a42d00c90344116005441071380c7d103590412480c00d01c100da1025903a0f0301c959100005170f50901c800c800c0755021204a5100d0765144c414449446034580008203201c8801003075000c0300d0301e14640340c10b900e80e2601c4c02d25a03600c1e091801d031742411020961903484402a030b040c0700a00300d20391803c0d02c0b8504142c404000c81c03555506c0c1c05a03102c07030600c00a070800445c001d050000d41040402428030700c1c072100c0b80da440c1150b800200e012000c0c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 972435908 1250 972434658 972434669
    0x51b0c0316050415031e0206190504060305070201050603122b02030a0c02030307020303150409080a030b19061e0201020f03070e040506100e0d02010905040228210f02070606 76
    0x4180e0030502140c5040d04c90001000d03194001384000c07904540e90421388204035060800600501d075510802c540e2180c04864568041011450540d84421409086500180519000300382405c0002e002030744140b18951013100000e0080040015001e10600c256010280f0710b1180c0b070103451000012401858050545440803600503960b20301605084100c64000072007100b15001081440301d03890740041070f01c0d082044080c204400c402041c001400174a00b40500410241d00458026240790305580f013a1b030a00820b5030f000410308900c10301c41d503200b403240c0610004034480c003080780090078080707440c02c41d80408ee0000500d000035a661001d869042164a900080c203240246c24180c1030038010b1365000306094a02c46180c041d04100038000b404214401c500450090740800d0039684261010030052102034001c540e03c811500d440050740c2c00000301c1148a034025107225096912841c0e5440c11000c821501400304107034070701190301a08151203070407100c80d000d22000000c180107100f01c0c002400b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 972437158 1250 972435908 972435943
    0x3090303020d1d0d050c1f021e07031404060906110c28090501061d03070504050106030212100602120d0b091e070207050a052403280b01051b0c03 64
    0x42c0141194039041030001c1d44d0003044800d2144486030040012100b001101e45900c490400100b402044000d000350481d00710032507800c5003403021808108004004480c002d5854001603468a001e0302413510031846a440010800541004514402c40248080b4100081503d2400c1d10410010300212410320b00c241840462a2902e075410076130200c1100105400901840250700d03120f0080c10b101040b078100440f0380c6943c0c052640c680d5060000b1405010010810455035864003c0100250081d42d60131900c1000312002c1800402040b4160040b0ba4059000305050287d1440e4040300d13420802c64191025260f00000c0309a564071031400d48580c005502500800501005102d48060090500c0d8155001000140034940f5005181c0c030130784906079004900824076014611203052500b00c80e06e0b840384048248480d0b903419442c60354243c0703600010350040002c00c5040c02e04030307400e110505000c03541c00c20010901402401c64003030907051950a4400340c040160102c1d0900948402029845 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 972438408 1250 972437158 972437201
    0x8010e030406080a0501120f060e010501060503071b0818030a1403030601030501170601030308150d060c08091f15030206030a0506030f0309130b030313060c0203070603180303090303020d 82
    0x40358081c00342d84d44203a00d50801e1050707500d0030300091201901d400e0040c11101c0d120040000703000d16a00322312980701c6180002c00107981d54040041c196001a1098000509a44400e404450b50880000c0c411070300410700901d003100d008a044041c12034002001d802d40503855150740031600c440c030550400521213000e569685400d07070004003207800581020441081801003103015840020350705064940c1821301e9074503926100c00c1c0d80030003e07044500660180e1400380c803204029140e00714100c00c86460711141d40725100c10041c1d58690420b100701d0420342e8040c981d00c1e80c00007101c2d00180101300d07242c6005008a0740740c1d0085461503000301c60500e01d80381ca510601c174150504002c0c80c8045c0c1e0329003020754240500321001440e40c0806e000c124001c103440f2218038501380d500748102c0300020b00e800d42c00c2c459a0341e9404061b00041450070180e101e40514074000511a00a000384c04401c280501c41278042c08060b40c0075001403100c2c160503001c05601b8032281c402c080c2240318a40c0d01032032150030b45211 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 972439658 1250 972438408 972438419
    0x6030a0813050a0512030a0c1b0305070515040b070f0c030204020a0512010e010815060316030f150b0607020d0309030206040f170c0a12050a06050f01140f011b0c08010e0304 76
    0x1048041d904c800d0064038281e2117918042d801105840704404549401840c9407680d040205940050b500080c116425405000042140004800040b210b00f610180007030062174040f070340e09003d00d00c1026882c020420800c0c00090303c45d03205440c0c0e28410b030910305c070702c2c0c0d01c0750045002c0742c10020182c00030070340c0020b02c2d00e180d030f0b4207030000c50041010201440c619818500e030180c58221300d01c5038440c11214000400e465036801d0006007407410341000031704202030366400c2c1604d40043c009030540740f485140082c4054000580100070280c02c000c3c00441c03400c1340d42c0d0309020049203400b400b03408000d00034801000583e11100100010504503094011450070a150101199101000f880e000d50100b02107404644802001c41d040703901001401c0000c450300c0c01c001d400c05000d0a00105071904e0202001300362000700500034181c17082c0c40c42e038203643c003400c0d0140440e04d032040d0010b90114090281c000f030300c400d1071041442c3c2548644101da100946d1401107500303486a81c103a400007074001207020f211 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 972440908 1250 972439658 972439669
    0xb1305070803030c0a110f0d030b04140a0902090f3303060a020901090f0e011202060403140a031403130b07051308030405090c07122a060b01020706140d0506030a081305 74
    0xa9030b6a0395400b4010110001c5c7c040d0b40d03109451015041490b4480001c2c07505da65969102c810244042c0c0111540e616042c0d50142c000c16142030100c3c89450801c0101da01d86400c45540d6200780b14090908043c030165030f010f0140c00031890101d10840303400c1c0c0c98003401d6460074400d0314000c02c4203100268540c522200050a40d02c1307650049a441c0005c0036080150045162040b03044074040e164540c0c1c4459030b800411054851074102400b0004c0074001c0b4041c15100150907021540240d0b98244e10004000503495036200642c1d421200340d240d01b49940c04140c441082036008862410514075285001420301c102040301e03400f081603600081030401c03050500e40c003403550055201092902e001c04076607400b00072600d04500324040180701c0c1e02d030102c1500090801c20b2030004003c8500d06000c2075161a002510f80e04c04d1060040c042c2210010340e19015000c040d00d240e407266501400d001c0450000300042a00800941c1d05208410b200780100e108900100070251036400e0380e001c07031403c7c00107110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 972442158 1250 972440908 972440927
    0x519031211060a0c0e101b1a0c0c1f0626010501120213090f080c010518010b030a0219050a0305030c010b01021501090203100305240a05040b1305070803030c0a 70
    0x500d0f03542049032841c00581c1c07240d41d101c40560100c070940c8a180c6c0209080b00e507092440c0a901007421a07103010002c1c4443c0004998003041424107204039a038031440010354500a200b8200d40507849000e0b45900303a84048482060f070b00840c20001103942c2d4078808190340840c0710b070a0701e402d80c0b1001c220b4006e8034400c0c080e007070141c00c4005502d0018803056000c264000e0243c0e00b03244200c0e0b5194100300030046212021a20706400090300303515460030f01d10240c002c00042d65100801030000c0e5104503000740600504004110041c090595440240c00b070148540001c010448811a01c007000f00f01640c40b050f2000c09507000d800150f855800c00004e0f1400c5407124944103055600c0b60f440c640c02d040c0c143d0321150555145840258880e21130070b201d001d1520340398200078541d0142e0140c6240b0f06403503c00d941d03900d00c1c03601d41c45800c54850928007001c139101910041e00740031841c000903480621400000e0100783c410000c0703554080d6a0180d03141583c2050341c60b0301c1d000c200081c180810961103980030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 972443408 1250 972442158 972442171
    0x90901140a020a1211091302270f0d030e060901140c0601150e031e0a05011e230402010f140301060c020a08061e1801090f1a070207051903121106 64
    0x80242c1c80c5e002e080740c08a40209040940f29281c0c02c0030301c01c20041942c05642603a07442d80480e600c2c004440101031101508400c1d540c3c065000d041166001d0f00d049003110005a0301a1502c0c0480d000380070500540b5481840807505005000381503c80c1681c2e07a070b0082409c02e016034040c0002e941481008000300124455180400c8562a10783d00c040c1e07008544d590807100031903c0303c070480440c55030444c10680740c943c01a0295181c4100c0c000040d450140e810f103140001c5500304203103034600840c1800d900314a01139000841c01000080e006501428000c103498040b0f0500703464007003402d14548200e80c826084030002680070002c02c021801c080c4400c0010340807801c060729840c90103c0d40c1307295241052846441d840282c101003140d1300b4a20000c620740c1a00203000b1b11a10f0440c5c1040316121244140072100c5e0544442c0701900c1d0041011a00e029100541c05010a0ba15140c1003004d504e0988240c104094181c00e0300200150f12840d851b8900b103100d86408800c00300c1d40300300e00e0501000034200c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 972444658 1250 972443408 972443411
    0x9050603010b010c08160303090506040b10050105040803090904170f0702090c0c0c2101060303020705280e0a1b02010902090708090a0335010918030e090901140a020a12 74
    0x850002044031007911741514129540111b902150b05044003e0706020602800310f004103c02d0005100130b45030458840e81d600103162141c03503955401150230344654030811a02d6082840344100724075044106640140c010325210700884100b0b40c242410ba40040c114200c1054002582070441c240340d14815400034074030b0314080c00c1240d100d00994880c030081c0c00d0903105004118002c1c80c0c42c02c00b00411069440880c1c002c000064491401954030741e068020300e4410000d0b2051010020306a4035911804d1070f204104014040c03901c505000c8100c005480a4011916892860822034440301600c99448481d030002ca011380c000d0050000d031160251014080120380410000780b10340000c0ca10128603410715041d03404104445075184507000140d54014085c0c00c80066a011940000308541038a80c800c9040015000044800d024146140c6004001c16164145111545045000721360711034420000031555a0116242d080841c0003220350242d0783e42d0118a50307805e564400010940003104450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 972445908 1250 972444658 972444677
    0x1b07150e06030a090b1807080703030507080a05090411030f0a050610050a0e0405100806010e0f01091a030f031309140a0207051018171c0b031609050603010b01 70
    0x1022800d011500a000c0c14000000c0b03529007465601c6910002c3d080302025000e810042d0200a03a002c0800704805640315819000c9080200400d02d40c0841e03500d6101c19203080c0784c6a980000c2904802950740501005010602040d11280100072001412071440b0341c0d6850800c00e03000e864400a031160b01c0280c900002c00890381c0b140d890b450f401030f0140c2401c6898110244080341e0301484a80d115401030708180600040c010000c80b8241036030801e070180d40d2142c2c2c0f43c007003246005104030349803100e284020004208001540c0e2040020100030708483c4214559040464600091002112110b9000052901e4034008442c903080c0600302403502407001004090021144d00000b8001d913600c1a40094104100042040038822005ca540001c3c80100c8200c0c5400d4141c10895006440c0b40e030094540c0c450a8410f102100c01041c0c4005c6644010050000c05500401e1410030482d018070a2050040c0d000350341e011000014007441c0c6010034180707001d500781401d4612805c0d00360b0600c9503604 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 972447158 1250 972445908 972445949
    0x10e0c0c0c0906150408060a1d06010920130611070b0304060f0b030a0b0105130204060f0e1311030603072411010f02180f010e03100504080c031b07 65
    0x1400c4800600115200403590702c03078000051004c1c1d007884112100283c0010000b03404000030401620459140008202070125a440c52000032280d142040d1280c01c500018464004154802e610380c001d071550480240390032000450030344c4e2181c902c1181e0805002000c00c50f59074803c0d12040000614000340c00d00a00c0c10b0780f00c6055000140c030040540f0740354442958414059401002000300040c110750f400c2c0b80609184103c82c81c2805000d010f0107541d041c07010328400500881c0c0880760103070358401c5111b28504003100d025102030400c580c4001d0103e10094a488030f800303280049501801070a60f203091010406260103642c0d4000805401c1d0400741c03241000005071803442940543c1450700c001d000c04228540104070302c2c0709204040384041048251220341c15180300c0314100030740f0805107140f201c070019250040c180c01c425034075601c00424004114402e4008540061161150904010101c001f46045410000350319640408007011401c0f405820803c10004100c1d071407501c3c04408288 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 972448408 1250 972447158 972447163
    0xa15050102070b1b010207080703090602121201180915060501110a1a040305040e011206140405060711160e1906120828030b030f03210403200303010e0c0c 68
    0x4c040d920000c072003450001040d0070a40440d140958400b03011b07665500c907498040c0901110f800ba5400501c102044180342046000803210b500f600a4100c00c00c036841d0000c440c0244c6201c2500c4405103848072529000100c450b03e1107454002a030301d0124001d070914000519000e1940a02600fa900c84da14040110f40105160740329110190b801ca0041d55803410165130078412540000c1e00d1408100001411202c1400d4991300a48a0b00c01402130030301110190f00d24a606403006081d60b00490080b0304202e005031440a50003c2d0803042d50742c81c8691010341e0001c242940d122909144e541000c00030021401011030304254600d800c100025400d00440d03000003003000324024140000000d507031804d286511100144c200c01140096004001440024043c158268a284c0a40300381da094003414017000c4181d440c0402d050040341ca030341200e8140c0a07003103400544103406100842e10915200008100141c410901e110b000b1962545071035100340700c502006101d080b003224240700040c42100302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 972449658 1250 972448408 972448417
    0xb030c042901090f09020a031a0f190f0f090e0d020d0c060e0318010f050a050d090c05062b0e0619020405040c0e03010e0307080d090c030b0a15050102070b 68
    0x31241c4118241e20000e0058401d401650008801d15105020000c1c00142e15002400c0500141d9401e120340c1c0b0896441d0403414080907030455000d84071207504080d50410044c40f800107042500c0d460070301a6160000e18000b4010340180581c01d520309014094001c079030041038000d208bd00c0050401074a542c4009481e40c46100035901044240c079401c1041c4102078100704002c40800060381d0f034446100703004004551790810454045800e00f1611541203005c3c038243c1d1403011032901e86914100c0040400c0c03009041c2079000b16000c07010098046601d0310355402519003902c4080201111421101c0d017503001120558110300218108606607105e02c4001c0707005604403041590040d01c0051103e01a0701030300031500800d400031325061b841415a58014040e80c0c0615041e0020050b2500c011001c5450348a061b4000c0c2403041c0400001101c002a45d100c0080d83d4044d0450003181a10780d0340b10341c0d0030789080c0c030600301c59034940b0314220002d00d41031034100051809000400d00c03d4588100300019015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 972450908 1250 972449658 972449711
    0x611070f0f0302030d051806062d03011104060801090608011a092a0423031f11040e0103120e010806040c0311040905010e0901090512091804060b030c04 67
    0x4404a03241e08050081044d1176091203219000c0c4103d26040c9841c21914407074400140b4148940004605603080013801044041d80b0324202c0010140c20102c2080b41d101081801505990707140d10710700c05181d810020300094600c90f034880c1c4055241c0964602034030b50580008134583d14003001a040410300041642a0381c0b000d94010340c1c0381d40e80412980b04a180320041040e070812912030313268017150040082080e0f403003001c01442009411200c0c081e10704030718000c00303405600c1030440c0c1d80140f04d0108911b4602510800c003160800d016038040500780c005034045011040004014010030030a0a040c1c1c0348103034145051250308c0c1010000920714100a00300c5401940c0e942003007564988680c103e042ca03505103000130b40d9656951300400005203000d06c9200c00590034040420348485040c010907420940040c010140340811140061003a8000310071164000100c1705804000898070b4809841749001e542c00186459051080c1809c1400a40b007651080d45081c0c0d40741807501001074442002c42 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 972452158 1250 972450908 972450923
    0x12150d030f1e02030415030e070618030c0807031104020309060105010e0607081207020606010206010b0d0c05041206090b06010513030807051207060203460b1c0611070f 74
    0x265000c01540c2c4400340c0224071100e400c6107000007195a40000080007100c0348070602c030700b0903d81c030740c0220202c68140000310380c41d8110540400c049482000500f0303c80504d14090005a030707032a5604005541c4a600c074010540104804009008101100ca140c10405031415880c41c905103006544654050040d01d05000c0c0c551040807064643c101510783d10340e40900250780d90b016450b420001c5020855500006114020014000d03501c0070680d94100c411101c002ca0510b250f00981202030100361860303908003c018800080c0015101c0803140000340151000a082030503810480c8039541e0050400d410700800f0042c3d448264038a600c0b90040700c1c0c10014454540d070462609505005c40850703191001d07803001c1800414400650300070f5018425225a0741740d4102010450201194502404d20b43d0b170b1410402c403e042c0c040e1807808620704030344110001e00c903c2640001031411000c0740c1d1401c03c81c4800f20346c4104000c1d480c03141400300304004038a981001c1c000e40e108000040725580040c202d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 972453408 1250 972452158 972452177
    0x61305190302100c0309111009150507230f0c0604060c08090301090c090615050f0a021608010f0b09060f150d18030e10020303072a03020312150d03 65
    0x1d8400e1001e011049030f00b50081c030a03190300e900020060501c0e000185c50700c030b440142403502443e120300c0940c80107010f52141d9001d2460b002050603c0040d85a44209010080214000013207218681900090014050701c1801c1c00c070104442c9010b8540805001c40c1c0e000d004803d2450f5140e9054408640403442c0000c0c805c00710b0b01c2d2099040c0124024503404d176080184034000c005901c91b1039420b4a4080008100407035694a2031888641101e8407031000ca482040702081c0804280f0080c081c0c00b50900440300b181c1d40842d40c415a0084c0d0303034425195a5541c0c00149901a054061202d61181c1124007092500b4043c0003c1c2c034008510191070302c9414540480c410f544640001d44070001084001003141d588504170314200c0c2c2411040031000504d950003015064909040c140441684035030040d4215076039120180c0d40b00101d095146541e0015445542c03220041200c00380680f03104c0d902941c0c50300f003280b07180c9040480c050040f1107a02c442441310320701c58403102d0300e201e081d81c1c061802030442d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 972454658 1250 972453408 972453413
    0x28090615051f022107050f010c0503040b04050c0d030806190b04090203191e050c070c09050702030d0213060905010c050a0602030a02070501090b01080706050403020d0b060111030304060b010206130519 88
    0x4015880c1da4541c0d0010380803071a46402072066025040080c010f0080d035500071f007070b100e41c2801c880a80e507003600414000d0020801060410484a80c01441141110810301503070000030302c0d410110004a00240d601802c01445082003100f4208000c1607c4d01da07443c1904101c0540c41c58010b600a0003180c641c00700c00a00415900704040120141c260340030000c844807622280c3c06c01c60300d400c0610300e250800700410441501c14080740d80d01500594288095810088440058480500410b0841c4020301c5010030200003440204080a00c0720310f6100f109181c2400606800c801e9805681803100f010001400310718085849038030b00342d000780010707a00da032140341c3e00000340101d044c0508a503191600c69820005080c200ca8140c82401e02112211595074200300e545215070f0100940024074070100d131000882c1d07410129000710050500c800200680026240b039500119806c1e80c2c0c0a85586082d0250758060110030380080c0503190b4981c0700704064035800e56485646015400c5101103260075400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 972455908 1250 972454658 972454663
    0x2071e0609020d2603090619110a0c020a06030b010c06021e040303030509061f120501060b28030c0c030f0e0604080f0c180105060328090615051f02 65
    0x2907055008000c0324000031641006110050105280b010481070011424429090b81c030a903881688404002c000c2991079500d450b40f014214032004c00010b40720071120201018100141c40d5504244c2e40700c0c2d00405441c0100002100350b0f0780300c2c0051500d00404604181d80c00007401a1440d00440c01581c2d80f070140a400c20741d5801d100303070408103010201d404000c1550607041140a00c401e003044440544900c03044204600940440d80310340e2002c0403042000c1d0b0b1180b48064180c44c0508000620039a40d240c1c4821103a0080350b0818035900701050700081100d202c0710080e024000780c9400c0002c03010285001c2d00e184800722001d0300b408203208241640511582c00600310440162060340c0704ca9544c940284d41d85115484000c09020391403400140c1d06020b11030340c6c0e010740844184812a4680381c180030555202034401c00f500808103800065a8142901508140c00407000004028800f402c02c1c004640029070711100c0c00c40e08000800695951150451030303942c014560100241101c41d0507031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 972457158 1250 972455908 972455921
    0x80601080c12070302190306050303030106180f261203060427030f02070621110408010c091505072402120a150e0108030315180910060902071e06 64
    0x50b040080320042040b031941c0b44c1c0141880d600090911a0410320000b4160180e0349540151501540103200420515101c0d2007510540e5114400681e01213031245182c0e02c000c072480d005840143c5010004000100225190f0814074503a0005003134281f002280c1c04206200c098902e5110303a840e0416480e000d00750402c103d0010306400a01c1040c03902c80d14002e05100c1034a0034160150141c0600000c030113006a2203a1007452001c44600500401c100719600241100c0d11070100b5000180404260280c0074429617110000c1c030b490b52008a460034001882c401107022078031040207018041200050403a0703801c03404080d00e9003100300e06006003500c510000d008221b04080c41009080500405800ea68000d0206850a000181c8111f4440d040d144079508207103e81040d40e0b0007080001c40c50741d0031106030081150000e000042c090b0444040516202e4255070340c035840d4019000906c022150342c82218014008040d003903042011580b5100307008501c0c3c0312841c54a1300003403480c1d41080015807004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 972458408 1250 972457158 972457177
    0x14011a032217070606050a120209063f010c03180b0910060f15020312010e0c07020d0303050907060908070b0f0d02040b070308060d021f09090612170a080601080c 71
    0x103a03e0308031500b004000f600e807034892180200c2e1421808240c90361810201c8005940203003c180c1191280c0c0c2c107004801000341d15074161490104a007024201b03040d8400c060020303240d10300c540e1080320b0082190848160020480c285494041244810710900e084064400e03000300c0c0d2400707546d4402084c0340c00d21111000310040d42e40b0b45040800e0303003034140c11030b841500d90343c4540207000140b15000366601d10a5020b41c0301d0004c030100c010080c0c00e8030240c02039845901c204003141440d5103a03002c144284800c08044001c283c4030000c100c0450410011ba2000b020745140c40e14038240303000b50340360b01c5450501500a803030a002420100c1d060301c0c801210010405440301315503440e5500300900c001c1d08402401c5001903104000b00f030640c50b001c80302c1111039400500180b00f0180560740c0c4c0b03000004c412503a906106d5420b0001401042d548902001007a164555035040810b42c03500f00d00480304040203004000c020b214441d0755903071141c0c00a5001900307082014041c1c0b80d07400b5100c100d025500d1403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 972459658 1250 972458408 972458453
    0x12030e0f06160e0a0b0316170a05063c0102030f0a05090a14060a0f020a0c082d030901050f120a020d060e04051c0e0414011a0322 57
    0x50045505a684180c11020071583e20f80c98020820b03000c1100b1252984540e81040c03805102017505841c0300d1030001e00006403414007001941c400d07000c0c8034540700c080700c141e10b4455850040000e00c1c14041e5441c00c01404140c407011f180407081440203840d02074285148a80071804001c24110b9000304221004401505402a03c0e070241080040896104101c0d5034000c4005110008102c0c00e8100410306458000700081c2c04c18442c03100456210f075104007403c04622030b480540e00802e042611301c00140c9160005007000440300024002600039000b255030451450090300c100010340401680d801100900e032499840ca02820b8001e03c901032079010000b0402d54600340503400a8070ba0003040c884003100b00c113000e80e5583c0c2d00d00d044801e43c2107401800c10b03000b2440e0a05849089281c400790070032941000c44c2c529180c1d00c0801c007182d18114030820703680003240041c040d5154121a103201c143c4001c416915502c1d1204040c4106c44404440840c2c5038441c0a45e442002070303000c00c00301d80204100b003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 972460908 1250 972459658 972459661
    0x1090506030a0203040c0f03031e050702040923390315100b161b08120702041505010f080903120705030601090503010b180a060f0e040308010501090312030e0f06 71
    0x4840b0025401a90110343c0d4540e1a88000703100c2c80040c40000440b81c060b201c00220044050142d5800a1114035050400004210340d00069842d44607040641d0b002e071402030100039a01205042c850403c040e143e00c2c50303000c140380000541403002c0303c0e981c1e0900c3c66420801d100e20100700c0b10700c02402541e0103038540500c20b601a082c0c280702100303500c03e03400e50180c080490b03542c11100e085449002031940809090480e071030b01003120280740d07210b0780508840d0300403400e035148007460078000d01040340055458001000000d42c5894044c3c00c503a146100f12034683c00707243c54006445400c510100e60140850000054100d040520030b0394110034003561030140b5031401c1000100160700031949907021542072000800c0c6801c052082902584010b0050400e13001281c075101656500204007116040e00d50790049801c281c07100d001801081703012404681400d0a01e40070f801381b40d0503002320341000888442000402c100e0b08009420054078100002cad40d48003e100b00d403c013a42c1c4200700c24903101d00380 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 972462158 1250 972460908 972460921
    0x30c0a03020d09050604181d030d0c1403101502010b0d03080708090604080d021c0f02040302011e2312040c2309010b0a0909050a0621050a110109050603 67
    0xe0542900409035440d0000c080d262003c020182c02607010701d40c103c1034405110076002ca91f0341c0c0102443e4081212500c0099a04224a46075134031070340703140070169169214000d91540180700031044c02c045544541c1545840d502c0400d03840b0709881100a5a80b981c4060b41e0701a00030361001e01c84142c00b4200c09844a41420040c0ca4120240c1d82c000011300250000340b5000d40100c0c1c11405143c0c0000210f2078010400280e1029411400c2854584c80350500126210221880f4001c0055371940c1d01585603455400003402d0624000403941c00040c030075000032250b0340d016071810746025010800354820415800444900e00482c644003250001c03440a100c00c0c80464041101250000c9034030070b10056080c1081d5032580401442c041d00519048018002d41c952080505110b501e83e1410700c07003182e0f945112006490040d5032000c030040d80c2d01410300c03680e01c0c8258640d03200c002c07120868401070361139650790350741e06003120b000345c0325440900500c49542e100c1e1004070010300300107003030326203d08054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 972463408 1250 972462158 972462163
    0x201140403201c112101050f010f0602030c10150819110402130509060411040611010b01090b03270307150f05091515060a03090201030b09010b07060b03030c0a0302 72
    0x12031005206884122450f014411200760140001398416200a403859030142401101512600c400d000c2607482105010f44003001d1142c80d2181d448031104a1507545007496103003c081154000304c0c2150010071103030000310710008007440c40304460b03840055210fa03070012038000c410b00c0c0e420001050081c400d07002c01009024001c504c94902881c3c10a43c1144001c0401c02248186002d610781034500342c0b0200034600d40300c0c00c81da5208001400100321502038480341e507001d40c400d42010003c500c0f07101c40310003180800d104d281c00800f028203000c220141010f80c0c51070340e80001070040104e2030034602a0b540d110301c0c581805100d00c0b003890407291600a240707410514a10840100004586450390b104580c8120f80100c500906030307100070304034007246c651801521090007802004520000c8071795070405d0319110010180030413a6a800180413406100040581d011424010311a0301110014442e00717026800702c41e03402d507001900181800b207010100741940684044c0e1039003400743c007055000b4103030003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 972464658 1250 972463408 972463463
    0x1020303010b1318050910180305030405011b021c05040e010b0304050f10060504180218130b010e06010f03110f071e0602210c0306011b02090c0c07050a0b070201140403 74
    0x8010031b0f1f03130904090612000c04c40303568090030100302c42281a45004640100000c503001800b8400101d000444269041d4901c900d641c03050300103a10000d0030502040482c205d070744030100545405803034076241604101000c03e040c09000106000003001c2010000d0030050098409900420384104807511144540140401e1042034080c40c241030b0032152044542c444d16440541c008d00600580b030fa40d50030b64007200e000900801c221200109090041015400d42c43d0091803502b07900190b0746402c5000400083d068a1241d06150805d0311b0813080c00384010540d80030b4208481ca1325150542e07414480504440d803c29840e5000c0380b044800c080c002141c000f49009100d00d280110401d0a10b0003003040305200b12248440d20800f030010a04035881400b1070301c401c42c1080180d81400d50240c00207031020070192407808048d80c0004d409140c6000c10302050b0700030181100e4892000c0d180141c00c918601ca0040002d0402c019946c1014400341d000c0b0a40d00071b0b5420000f5001040d150a140c90f443e44035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 972465908 1250 972464658 972464671
    0xc051f051e090409081c09020d030e0a091b030b0d0f030809030706020c03300a0911040f0c02300f1902030403020102120304030c0b0a1805010603110f01020303010b131805 75
    0x1100406d60340c034203440c0920000d035940508601c401002c41e07203084607940904801158029544140058005620b000724040f1145d0010040050440004041d00f00d4860103c414050300421165802140344040300800c1a50035041c650301c80c0e69510342141c19071241c828000c050a1001c5804c8054031400809006004a680503c00c0f0016201112812411110b00c1e40701068210741d0000b480c4c0822500000c0242e440380302e8514100189000003401d5440031000030007000d0f5210340110010354100400343d81501001003404c1800401141851511810b5031074070418500010010110611181220321141449160041006203400000c3d101d5105100c1030b40148103600801d8807075000081102e021b19415104c084000d862507070b0f000e041d42c00c0241a503820a58454241409842c015482030074188079200004180f03080d8502154011510386400d1f0089041c2014442180d80000890341501c0102c94165201e840071411802440729907006121052440c403103062218089400940c02440b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 972467158 1250 972465908 972465937
    0x3207050108010305031e0706020d1a0a080307080f0d14010602011a0a0303031d0111070224030439062304090e15040c051f051e09040908 60
    0x6555200440d5481c0082c08003034143d400400440c1d503104000c400035500424480743c05810068691200412030700601d00c030708042170b11841140040700c04855100c13640e40c001c0b00c5420440e420106441d035240512600204a11800a88410700115507803c1d20895070722008103000040250894140100007031040310007641c2480360200c001e9030b20040182d517a0b070002d40f400c414603155882c1140902480510204032010f4035140c0d1301060028019034005e0001500420350b82c21140c81800800324100e48a0110011a07500034258001243c040300c1d00142c000f0030704240e4942128941101032050140a040c99031064049582005900c032110100d8000f52035810003200352840007807041a500b0203c0c0c0c0302c00c800300018000d0440580c0480402681c4408a401400c1222550035004906840944480c540b08108002a203000d04480011003100300c0042c043c502d000758040c0c424058082c80b400900c4810482924485501043e2182118010801d001030481c5061070f10396544080c02005161 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 972468408 1250 972467158 972467173
    0x9030210020a0b0f0a02120a02190206040f032001022107110706030c020f06100515070c050f0117130302071403120a0309080f030106030b012a32 64
    0x503400481c442d407080b5040b1106400540d603000500064260003400032020380d42c00d121040030076000c50035103403140c00c01d90801030791a0000001c2c03512a01c041c94008003154007600400c800256514000100343e5030606003800403000140c1141e4210f144241100c900e58408034180b20b070480c040710804110080b1151004882d12001022100d5071089014041c43c1ea001400c2080a54440c1e40b01d56004441403040c2c8400c0401d60920341e04003c01503a00b01642c4241c80c200b07001078039002c15604d941d82c815012942c035200b07582d5100440764850b0b1007054816003540541700e074283d008103c13054175410068600040e070f1500d07442620403852118001e8006115040000c20800815104800303814001401000200d400155181ca42d510410082c01003680310410b15000441c505c010340603110041050036102e40c100840201240c0011403a0790402011000da0700c40c6440448400100001008200100194a0404c254a000c00281f1046002421a25091903004140d28404484180d40548903003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 972469658 1250 972468408 972468439
    0x72013090515060105040503120306041515120f0603061d0c030c06160b040305030712060302060706090201022109040b030d020606010f0909060608070f021614150a090302 75
    0x440300c540d1002801944000d4504603032a011180d0580d000d141490641c0c9080d4440300801d0034041e049d0300300c1403103010102c2808028901405580312500882905614052602250103124805034903240144000d60102c0e10059225030089544000d00e0b08060204d030f5034914120004103040c5040101c109050072540301390304000b05640124002c010001c7c003140038160100407490380104256103d100a00c103017400000c61040c80188618001d8440b05d4481c5000310024007a04044051800d00d01d10703202044c0016914282030310050394004d175000401c900981300507894144054051000c403640540b01c040d00034150001014900d80c241e5041c0894846d0500381540d901400c0001030141e00b10f480021400d5228421842080b082403070700d03142003950f48150703004039a060742080b0700052000042100c029003003018081562900d100601001301445182c5c107280000e40294242c0810007480c55103207070b0b00c1c039042d2040c101d0015a01545c0b8078100078050314002e20761101324040c20214041106 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 972470908 1250 972469658 972469661
    0x100816050130020d06120807030801170d120212090c1003140a020a12020f13170a150603081206090c1314150c011a03010e071a072013 59
    0xb4205991003510401c15034199845019401c41c0103800038072980c450700020791001d15001c5c2104540158401580c0c1e1005007002007c0042c160041c000081d006074180710075400002da00440e22006103014038030356000c0002d00010384600500396914003111420b001d28403c0200b181e0408603002c44600914008005081d015180d484030b081c0c42041c4800005030208119030010242000c2c245483c0c072f5a14022454502281c0100340346011050003ca6245640c00c294440320b005030265188103c200d40603c0325480d61812403400050000301180034800d20000d1581000000e9a0b00010840d1034a52070790425180341021900e15200e4500000444d6040350110200c550516400010420041c10451584c0842410740203064004150449101c510a241409005610003150011590081c1410b0010b070744100442018030907454030070703144042c803400a4900201e610540c4406041c3c3e41d401ca10308054058604e018008040d503c22810507803010111a10254000702d4a4589624520b001d800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 972472158 1250 972470908 972470957
    0xe09100e0d120b03010b060d0906050601090b19091a03150a0b070803040206071703100e070219020a030b0108030c0111120402012d031a120c06031008160501 69
    0x401007030b00582c1040b82c450040d0400c100c00e41004d40041850865000800c1c51940407400e444c00b10340c0d50b00307104810806140200342d001b200900e0401030705c60800708851035501c50010182211000c03042e882480398011800c80c8000c0c5003400000701e40b0314020841c1d004a90003140c414011280318101c07000b40d031810103c102c0a603a002000503091591540d1034060310342c0701401c143d82c080401c0c044500041d13912101041a51410685d0580300e007800e1101c04128601a0061408054103600b000f00c0b569002039444800000c1d5002c48141b680580049440c051298201a0062120342d00109158a00000030b200388050343d030007002060840c00030261103000e44559410b00717510350000318000d0362180c064030a611480c812441c0380401d0040520039440450150b131004652900041c2c411045c41ca060074568000644a504581140c0d0103082e840300c00c01d00195201d00300100105007411508490040a400c40e0f40450300175080c42ca50340040300207140702d003070b0028454034080340403050303415081e2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 972473408 1250 972472158 972472183
    0x1060b0a031512080a1713140a17160206070303091202061b0307120608070503191a041b0603140610080601050c1f0b09090706020601090203100e09100e 67
    0x1660f00c074140d0300c941040e44503810300710402c404030703804018001e1503032400c0d401104110407011003d80b0368a4441413580c00c1d2680c004142d04981e0907003003c140802240c1c5003190383d80c95143c1c2e803800410030b88880c05801d40c2020750040400b00f2201b04041e0960b00c0180e10301c1c002c1d1030058100e440c03014200c0e5262803c40d0841c1889012301c0103000340d414024082c4d9040380040c2803505a60080d00c03d03400840c1c03440c0e4030082240c2e001d174408200c08d00b000c0c081085900c021111503d09400c05885034410b5484815000740714061042c001002c0c4002d03905e4903c03038100c0444641d401c0640e103441c010b01070800e811104440801f4500840c0e4180303016081b24040c0d82098807103500d01c0e500c47e4015140c07504100c41724085130003607441107095196200300d8801e5400090303000156840c000c105000780f0078001010345445600148050240d0703900014030034111707060040c2c0507a40b40d6410810408503401584140d158403000c0e42032001d240c0002c10403042c0d01c40b40903802c1000c0f18800360000e91b04c00e0507000304c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 972474658 1250 972473408 972473429
    0x240b09090312100b0c07180605060f031017060105090106030c2021040e060102030403031e050904020d1d011a0d140d050c0706080415020c070801060b0a0315 69
    0x2503606019142c1000350f0b110449510318412141e480c0300c8041c150744098030088040e00145014846451040c01400c50202c4d5504104001400d242c0413138107620480e01c0e8100d09a9011000030181c102191019010b041c02c611001c1a4400034040d99940d040203000e080d20910700d4030004100540700b441100200303e0250f5072240a00384003d46a4080c20341c481c04041d190003403020100c0131003100031b45072541101c801500c5543d86e20300004100003001c041d06040c1190030070001000807030340c003d000c0990341c800360380710001c2d4243c1141c068407184070b00e00c40150801e00100340c4120740412640010108180000144a0060065110350803140452030f6131502070841e40030742c161420404a030751040361060007440050a004408949050b182c1400c800004200298680380000c090150600805a908004549080c00d0361a9562403201d02841002076130301250007004681c0400a00d00100340c02c5008006007501c03018100c03000d80c0a0348031140404c1c20041c060015001e400350b594100e940d48041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 972475908 1250 972474658 972474667
    0x106021b0d032a02040e07080d05030c0702040c03050f1320040f02040e040c060c05030405010e130501030c09060f0f1a07050d020607140a02070303110a240b090903 72
    0x700844040c1951098040198140c002404407212040051400b1855000308200e42041c0c8104070540e0540400d20009820116082084170000070f41002d8170700c4142081c2c1e4407a99491046011401170100195000c0c0c2040c1c000b4013021f070150720030f40c005d44a85000520030781d507002c170400e05640c072800d000b0100034201c141ca401e03e100e0440c401e840c82c0f4000f040442c80a120504541c2030f44c03c5034101901c8100000140010406209640d00003001542080c44000314182c44164680c040c0707100705030501010100c84c420713a558441c00300d1090f451020003000ba80d6124241003145010900404030b449161410209907826050205c000f03c0b206900302c0d0582c2400c100903800e1101c6041c003000d03ea101e0500a16000a2080c45049190300c881d0740104598a00480c00600c90825100b500241400402040c0225a070203c0c0b084152501420102c51004100100c00d03d840b02e01d030f4000d4540c40241101c54408a1811080007070714a034030780107122030148181009102c450075200031142c0c5c2e10402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 972477158 1250 972475908 972475963
    0x50f060d0215040302091f0608100909020d1506060207090e030316090510050c0c1c11060c010f05010815070801060309021c1208010f060f080a0b0a0f0e010602 70
    0x1c103510a0b410300c98002403c0c41e03600e90102d8000d41d4142c44c02c042c070b400164100100d8840c90003030b020042c03005142c1400542000180490301400394010b10140c2610799180300195111a016900e05581c0305401303110a401842c414402052540107410050086510020354418180030303500c480940303a005907140da1070300c25071540e600c0701458140e828052203c80014142d501d41c0022000c5001548480790b44240680315581071200303040145206400004104008226100b413201143d544031041360030041d5558000f03501d901a40d907042c200c4d50300b015022003110030280c00c1913041b030b0700e105d04035440021701881c1c2d4030740414201c8840001803204d10042240074401c0e041f84480c540050401d900944180c8002210100a64070a40c0e8080a0101215009500c4001140103040361601c010f040f07401c041004080e8550f003540c0c9820000840085001b8070250b61001c0d00d0305000070400c40307013103644546400b40059a0702c54951051254400050064004031322902c47c1031070302c400900c6109508 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 972478408 1250 972477158 972477169
    0x903072702070f030e090c1204020d080a0c030e030f1f0605060a1d0a05131112040b181924050a20070f350409050f060d02 54
    0x282111204a40100d022440c0e0304688002d01c2c0c0140180401e5100d08554140981014120b44029008605070005c010f075204000082d920140110040c056003a125400013034606662445c02901c840000106034039469008500f003e500c504c84c0d150850314100b008101900c400c95082c5041d00d9820034540f9404c14001002a0550418601000243c56031108003040c12a04006a21004958800c80f0710203010038480b00c12040c00d200319039044006042c6400304183c1400e90308080c02132612907200f141c606100c0001d40b0701c0d8140040c400700c00c501d040d080040341840e00740d82d001010000603901c0300751550046208190108040d907200b107003030328a9a6121100030894240500c43d100c0310210103145449000f840c1c06201c0e6018041000980f031250400742e42482c400344481200104408000101500d10317841000c0d40201c400508101c0c4500001d044c0e458184003000c070143c9011001c1e204c13807607030700141083d40c0500e02c0410069460003446010b100e410703101140c0c030481121902c070041c03821 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 972479658 1250 972478408 972478439
    0x71119060b01091d10090e0c060906040e0f041a010e011a040b0d0b0a080307022b0c0602010e0d0c0f120e0409031d0a030f08070c05091515090307 64
    0x10300d04050f07501d0350ba412280340d50b40300c0c03402c600d580e004100c240100390b002180c410f00035008204003044010b04440e4400c1c0d80d4443c05292038010310012079040015034801003560300a00a9030291072061414501840030f04404075800c54041c00d102c0c40da82d8580b020040708a05803059080b900005074280902c0d2003aa61030400b5407000c1c140c1c00c00c40819405c0c900346c060500140c400c800403c61080010402c541c0b050390790045112035005000100c00350765000e0f00b400d070f0810000b0a4000c1c1c035410b000c9041d00405200c102500c14036410b040024440c0d81580040d412800d903c00b643d00f04400907030115191040000042c110070180e40200000c40d9140701d410120190740c0c108030204458440c00324056500c03103001600031542d20014501c00080c03058002c10040c10031a5404140d40c00d42e42c03901003210320183c3c054040c04001c80c0d500f04000e0300418004c0a00030040410030113250121000107c0302d00c800b00603000c1c0c10503411384031200310300340c0035201c013048000c0140016a0502c4040d14541e02c130f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 972480908 1250 972479658 972479681
    0x2111041703130614040e0a0b0d061409010213060e040603050703150b0f1e01020106050307080c090c0901021f0e0105190b09220303110409090c0602030702010e04020c03120a0507111906 81
    0x281da83c40381800c0d07a0b620184150252240d44041030bc2900c2e181d000c00b80754402070051031140d00402280c0044000001500300350342060400348000080e9002240007014550001000c81c807800ca004801d1000c601410110365038081014060360f00b54005111803818010342040d081000d0b480c0b85e0010441106810310002010300c000a881c03552040024134006295015100980000f485c0c1000c9040c5892030592045152490502d8000101c0000359078801c2e03e006210712840b01c0c07200040c41f8440d50002102d203040d9600a1200d82002a100600c0040d59007404082914007c280340750fa0400c92602c0c5e104031000c925002072500d4000184a0500f0f01c2c032022010160340703007802054410440060000360034603076000280d1515034a4008001c140c076030040401d642c0140500390050b07a2110401740520b80995006d600c0e4820b00c16214070354002d10744610100c002c01c4041050300c840550006214400c10f641c0d413140d10a880c6d900d161140401240d10054030f0091000e41e011804a80241700e4846 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 972482014 1106 972480908 972480911
    0x3050f04020907020f01020f0d0b030c090c031003061409010e120d021309090f030201050c041809080c0a060515012111041703130614040e0a 62
    0x420060000348075500410005a00b540300b40009684403090b0030096442c4d0075940884400c0341c00048030720400518128070607201d4600000e8907856184041c00030092a1164440c2e9441039000928000134000d102d800080042c03428483c84045031226030b2414441e00304406400c0c29100e0803400b400d85c680c80010120741d91040303102203410754000000010307564903a8100c444152031061388040202445d00040b4410300180d540156141c610a40c02040180e6500c4007200150065015004406196503141d1202c84d40903400304d14900c0c050b803401410074456a0b400ca10f8100e80d45412100e46480304140002c10f240600c079002041710900700903001a8503e005008000d2074405100451600c0b429003031074642c2c0840071280a07200444170111a400b5004095980e130f48030681e100c16a0404010000d500c0e8403482da00003400d0302c603a00351840c0503d031014500c1e02402c0079110380e6581c2e = true := by decide +kernel

theorem cover : BRFrame.Cov 972302158 972482014 := by
  have h0 := BRFrame.cov_init 972302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 972302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 972302158 ≤ n) (h2 : n < 972482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
