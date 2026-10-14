-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:29:51.489631+00:00
-- url     : https://prove2.me/submissions/b2b0e6cf-c7f4-4955-b2dd-80a6d5eb6722

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 547122302 ≤ n < 547302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 547123552 1250 547122302 547122311
    0x1060c0311150609100302090115030212010b040f0b07020f210a0305191d0103020a02030c071202010e031b10090302090a0504050c0d020a03060b030304051f12141503010f 75
    0x5240000d01104143c074800d2190944802160781808108040022290b0140c0141c00c00e80c0f8010011083e1300c450030307030581450340130040250000c0600c41c844d40a0201d0700c402585035414148a4001200c5640018203a81410800c401c0941d441c070100c0e0b4151601125005415080c0103084ca00782144060017840703602c10b23000b0000c10141c0050151102c00a908007400200446140c1115401003602d030f5841c1c014204107090b61154841c1e001020300926900440340740040f0f04102070301d000415030183d09203e00315180441150381c00241140403100881c0104168031040c6001c0302005107105400e41b00324240345d4402005402540c1c10320003550024403400032454040343c0040581400c0301c084500303002e0ba00303424074146002000c00c1c1500ba006000841c50a00b0b66075800001c0c0350748000300341d1510092100064680c1c03094012400d0070b020315892910800b0f03d0700701070510b40c106244c80c40140d04021800c3e0794085c0c0802944c0c1e000c4e1246103d880c04510354008a40186400f110f04680107052 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 547124802 1250 547123552 547123573
    0x908070309091401030f141e0718050c04090f060b28051c1508030c0307030906020105040332180a05090402090414030d2309010b010801060c0311 64
    0x1458000c200c840b890000c0c00080c14407110b03540d41c50424040200f20301e00c085095008510301000d01c2000d038282004075006d904500c025040130f4400042e43e20565800b1000a0118104241400d802d1400008040c80313a1b0801d0300b4103d8481c011409a003104a50303d0f2080c02500d0701700e41142e4010400301d0203080d41c0b000c0c070a8004001da484015410300c00e01014901250491144003102c03024482500b126011040344003100c0040c140000d020301446a15003170100360401c0610007010800c01c806c000750354498043c60082e015980035842a402c1d6403501c1c0810010940040e030030316000c00410b0380d035510314031440b00048914180f480016100307940415841c111130607221204039103500880d2803094482d078600c10890120000c44000750448212404100003d00501990280c0052a401c2e60f0800e000b02c2d0b00b000441d8180285020280003200c10a110f80c40c920310f519410408007802444828ec0440c0041c0c2003e00600c1031b42c04000196002406152042c02c2141503150200150381e50200f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 547126052 1250 547124802 547124807
    0x806010c060906140412080903090d0609021e0909060f011214060a0c030f0b13050601050d050a060f050d0c1a0904020412050114100e0a1805011a22020a0309080703 72
    0x800700c600303d0724900c610000041b8203000d81c600300d02c1900194015450540440140006000854030484140c1d480e00c1d44500140d86809199003403e14540c4641c800e60426003c10022101c06091140c840d0080c0c03003401004500c540c2c440d410740700104c6485002407038500d02140c11070344142c1606a1030240c9801e22059044541000402d0080b5135414031048245101000481d034501d200180d10080304181e0418180c0c4135005140d01c0f8005040a03824032018075854015202c040b10100c80c02e80e903d00091246000070a180c2002e8070007568044c404000070b41d604122900c1d280600201d810140c50740e4040480042c048441134a0042c1003503498503605c002c0c1d03000c0e5020121040b1140d500303041d820700302d00400c8031030715114039102e10507550818a007100c1d010804002606110700036480344503c1c0c0b2020020030b090f4035820711600001540c0c903041052002035002d1405814464030050b2407509500902c400a500d044071500b0005a4503030801c50241e0090440c0759008100d0000031a01f4400d054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 547127302 1250 547126052 547126091
    0xf010e190f0801021213060b0306040f1505071209172b09051207050304050d050c0102010501210b090c0d0c170a020108150a0b0316030b0409030806010c060906 70
    0x80e1150315850701c41d5110642203080c3d000c0d006080407084010400038100f003441580407040c1c14000c41000444c46c8010002ca0305090003103d0a44008610034929010009801190710040c1a905020021400c10038002840000d1002d40c1c08009a160304510007440070140e080c48070740b80c3d4146a540d84080d4055898012180b0488020245102c0700c034101c660000c5014402171180e026014012000d0080961646c0390458001980c140c03000340004903050325000341d802d00d040d000e00000c05c0b00754003c000090039544160400881402e0203514101000d82803480c00007820742c060001089a61101c078401e260565050050350310140f4014a041405040684507082d0303000c00241c00b001d692007d035410360320070440b400240088c00400014050400031412040721071170003001e1555050b41e40101140c66003090354032007040b80070740000d214010381500c9004959201a00c0c18881400a40c0703020740030603c001c1045042c0718000110000304079042d448601042e600c102c0c01c1112003041a00f0b885c028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 547128552 1250 547127302 547127309
    0x8040f030518042408010c0c0b070915090302100c0b0a0207030210111908011805060409060f0501050102010b0d1101031e0606080103020a4b090203100b0403110f010e19 74
    0x2031380c41c50021404400600a1050500041e203851030090129510b05d2a109002440c410802030280b401050240d150582d038070b07450503150349080180307095004000d2641c4035224180c06003c00e040c0c443c400180803202d49644401080801603c580042c1001d80c142440301e00004456131030140038044000980020304110500c3d2003040044000c0340c10281d4280000b8043c2100340140d40040800a450039008241e201d0000fa00129100c0031980e544400c1c0c0e40d0140098041c00c0e1180010300c01960709108070861038208495111104072030381c980c03d000740b0500461504040d00d03443c034111040010070301c0720f80d00100000c00b04101a40c3c1c007402007100303100380001c911130032080c0b40020b460b500210340d00c4180000b000254a040710154511601101038840c0b1941c6030a603100004032980c06881000c0061944990150b5649064282c05203054500d400c1140300c09024842880843c01141104010540554020700500031440042e01d18001c10556144d214031140f062048811184e09803d049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 547129802 1250 547128552 547128611
    0x1c1104030c0f03060c021b090a111b0c0a030818010302040f03060e010c0503090d0e150c0105060301050a020f0712030f180203011506021f0608011103090d08040f03051804 75
    0x14116103c408903110f04100c0034108400311f00607100c03030316460b24581141d04007031070001c0068501d611494900070341c1c21802c400482241000d03022460b00c0414020040d031054111001c568803400e42e502e031744180c010300000081c0044800d02004541e40a41d0484001c0c02d41c081140c0f408507502d00e00003000e0000103c401482e5400d20038902a91400344058034004c21400001d000e207500000c0080b1050398190050a0b0720605469000c0d6070b008900b80200441c0c2c1d0003000101d100c3c41c01e4028142540d1015044d00d0001344100103e10b58607080c81c064802c0184e00622001c9070246d1040308401500442520f0040c05152001c9010050310300081100503a20a0b00280101c91441c2400c0100c801584120310140e00070341903030001440c07543d800884000c4840000181c080d11210502d00f102c0c000c4509170007900c8000140180c0c201e040181604841541c80e0032480f500d0142c0d10b2440c3e10300d01c280024207116000c140ca14030264102550141060013500c204039404004248610203906020186c21 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 547131052 1250 547129802 547129811
    0x10030c1202034c0b0706021305040e01020405011b0206040b0d150909050d1d0402161e0221070b0d0b040e0304231806030a050f060f0a021c1104030c0f0306 68
    0x9448540760b2401c04940074148132909000710368070b07000040d41c054060704461412070100481c0303c1d82c581c03140303014413440c2c4000140c465060400141c0205c030050511140310109051060050703480000325001e5803040001c40b600c81002c00f141d034010780400012006010120b01c004035021040d640f11800441c0181300700c4890386440344041d24030b016110a44180740b10308041c40005420190010040a0015268125500711b541c1b18002c0d0300b002145151a210b20621030b19081d0f280c442d50019004029000c9200e070f103100a910281d48200602c00c0401100c4040751002e100140c80c1c0c41400900009081440600c5551b6219030b1243d1141c0a21245c244002c000c02680401c00d0301c00c2c0c802400007601d06203007440d104410407a075020007040315505d8811001810005001481a0f20955071448003d00031400d00b51240c00c0c1c58200100b0011130f40e40b06014032000012551084040084403000001d52002000d112403480d00c9107800192002110020000703041e0241880d05040300d000d1340c000c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 547132302 1250 547131052 547131181
    0x8210f070e010e0321130b0703090b030c0d0914030a02010606031121060a0f090c0f032c10180c090e07090b0316030308040210030c120203 61
    0x100c0c92920000f00903056407100c80b02c000b0026038622080840c030082102d10781840a071803075034201140240c03c41c1c0e60306000401d030001010380200c1c190b0302401000b8110340c1140341c469050f1420707005141030814480d0329400e8000900c40f10f071480c0240c0850440580f03540c0c03099510003074040c0c6640e1051800203454201c200303c61110030402e13688000004100c0c01c400c4220700440c0103180704081e003002c2d4040201440043c2000344888031700c0c01000000e02c04904140f484c42c001c0c0c44604480145820300d428501080545c001d00d01050504441d441c007a60081010307485050320b0b000755000c082c07000070b20b02401881c240340c25894507003081e403050010100c49a120311a040c02e441440c03c12030a140c2c4000c00501c0444500d40152000020240403514000d0356401c0c200c200d118540d1055000c40c2c1c041083c001542004a0522082240350400307105c0488041d6008207100d00d0350503100680b80d40070000c944161800300078403403d2a01e02254442d110840d21010048411300c41d10010400c40072401c1c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 547133552 1250 547132302 547132307
    0xa06020715111606020d080a02030f0103120c140c0f0307030c0515070c030c0e0901150b07020301060807030c061106090c0103020906070f14010606030b0d08210f070e01 74
    0x1810341d401030040034442000a181680c86030b07010080d29009020341240c60040390940c0411000821041c0e00601c0030f559540c1028240380005442d50f030059004004200d400814081540d044aa2104888140a6251400315000c0e02040da00400c640c00d0a00080f02408001a20f428101c0048401c03a943c21a0281015503540c2d2078032000b032040034512800c0000345040400316645000c107241051608605503038021607040c00ba00100c95415080c50240f040d45481000a40c1c0051201c00801c0754006081f0003a04042d064821411000000102c100c210b444c04e400c58001070116900b102c03070b02c50710391500c442c01070a6800303214001026038108481d2514006105805000c1102c0504507484503c40118082d5002035015034006004010000009428001040f0500d010b812042814045c0031141800d42c1d07001c0c0d0149003018140207030b000c060340d140e140007044a540a00c255980c1c0d0032000c0b421952034244260046c0c0080d0703200400400c1a0071304041c1d44286074590f80c1101e004d03a8480113 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 547134802 1250 547133552 547133563
    0xc0e0f041401030b013605040212010e03120c1c050a0209032d070303140702210c0a0b040e06040f090b07080601030b011403160e120c09010602030f0d0c09090212060a0602 75
    0xc94a0b440403088006c2d41e41045030f0000c5e07013144c005024180d1192145500e0303070070f50700e480341e002a06902c0040d1000014160803090354103c071030000304900d05031803074004225408007014210309a0369900042140403a403681140c05915004d0256031254807070020126103030b101422041540645800c962030070050206811040c0c0e540b50310341c4c0f0008400c00070f0040c42c85d040028220780010401c04a6140ea84601408040d1400c2d04002051a075010f0803e00511a010758801d03200c58100340030078407024008284945d072020060f80c00007034030080540700130050480740c0c2004d800f0088280a1201c0e0f1031340556180c8c81000f080e2001e00c98880e04100448140340135030304003604480c06101048409000013410b2030b540740346241948098441d50700041d10a405244e5100340741d440801e480e261400c2040c5e0150040c09113002640c1400001050010b440c072607050402d03582603940f2805c100d101c2c01510000d028140d042400c546030038241202ca036150200b590a40e110340704501002510500c0045c0b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 547136052 1250 547134802 547134869
    0x30506010b0c0703080a02010f0f0e120406020c0103241e0f030b07050711031c110601060c170d050c0414041a1c08070308070801090c0e0f041401030b01 67
    0x8222031032540e1a403421720303000204000c0071552034403004241c4d11101d00800c031899059800015a504022a24501d807440c0710207107511940c024041000b440350041005480b415007820302103284c140c4503031448100c642e00300d1044542020300c0320102d03070000314689050041d9800c0d5607103035600c0e8483d64290608034040c40018039047c814070010b8109449107001d08030582c8607240a4003034030380c2c0c0400203007411050064800494901102007120951202c8108087c00407040030300303c02d50410b030004021003d092000341c080209045005041d44940081300c04a4640170f10400060900140f0004140c0c040d01ca2802c2804200300100014509881100d040d48400b400e50000e070ba1000c000d0040c40c1303050880800c00400644003442c003113001c0000a260a5210b90385880c09460590000341962078117030090700d94286440014045a604a84271100354081184c1c1801000916800100500720308002c0c005480d060200001c100030b90782d01c0060590700070707101d0368282400c464903950141d0050345 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 547137302 1250 547136052 547136077
    0x1e050a12061a210c0d0f02190e031e01061815061803051207050d020f06071409030a060f06080309010801140301060b120411090f07270f030506010b 65
    0x900c8021480c28400003003400d800b01a050b0400d01c0a41c0e0460034010030f0803152554069000280140c1d885541c5c492003104100044003141407a940b1715600031501034025091040c00705030502c84510781c2d07041181321043c0442d0040101c000801c894142e010f03001a02c00d04400b0403034402210240c454138007894440d8000c81482501d001d01d0000c080b40c00840e08060b140e06401941400700101c4d0b0103000c40700d038440072411070a6580d1200e11701146031440080b050011500540d1211503c040042240d42e0441060325181c2040c86502c00d02d114a44100300461794507102d000c92540802100740c0015441e0035aa40c81007003101d56401c90710743c4a11507540ea070341c0064006d40052081c818080c60903590342c1c802400004c5e03190345490b55000b080e03100c0b550341c000307400706101000304200301e41007903100601091381ca110050078582e01e64090090082c0109040c04030341c10202491001602038100c2d030790b041e050200c00b8242d45075180350380b402440c0400d0b101030081c0c0d400410700e40740000c1158000030000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 547138552 1250 547137302 547137329
    0xe0a090b151c1119032103020c030a080f090f03040303111e0f060c032a0f03041505100501051204030201151203030b04020f0f070c0b0f0a120902010206161e050a1206 73
    0x6c0d46070506040682c101d9005140d4240800840c801d81007015061048071925901600d0824070a44110550005c0c106034840d400380c80d07141d2030108084252000c0b664141881040000074201090800c14400e0109002503200703203560161a500040c800101e492650989105460306d01002c48584022641d0200703c25241c98608064510300703d000000e0b91480032143e0800b8004884600160b00680d025501c100a5501000c1440710034414903400818041d02d03038980794030f0200064003134011420710029152502000400341743c000e4222a8028454442c92098252030318049448a1010841940028a010350046280c2450300c21038031584801c079026070030058000352990340c941c0306003411502c1010790300300042c45508600113440400000342110340c0307a40009a000f08080f44042050785418109503101015036000300e001a0044e4403d0001034081c00f0f1450190303404200c60507604604000c08046240d01584103001d0046082140c3d01c5200082d5846001000d682c05400b445002c0c0020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 547139802 1250 547138552 547138583
    0xe07030e060c0f120106051902030301120311100c0f09120f081b06040602121302011d04061701090204052503022a070e0a090b151c111903 61
    0xa64010b06107010140703c1052508001c2044502c61403001c0e401100411000314000407916001c90201c0a0160303544025410f5602d052000c95400302ea8280207420f000c1c03005108002007100740a0f088401032a4035081c802c01442c02130081440c0c01c0c84480c140010a0f4550114003080e0a481a400080e00325800c030010182d00e44402c6501c0e0701c1030a0051142076041d000c40080d813001c0c468148254040e0000603120300d12050303190003140d00248828401ca4111030080010303a049441c40001c0c2c2c0c3d00440340040402620702180c024412a08003d6061403000b00c011050350054010b104207500c00d840500150303c07070303107883d41c588100420480002c4220170a18526607209030301601c42140442c00e0a0030f103140d082050010740140c02c1e40c582458010240901c820305004d01032603040030a04808010540c00758550007502403024181c0b03d9010b0354a50b9008860741d40030900590b4000135070400d848500342d454510240000312130f016000b400b03a50305043c1400e070349002d244206c0743c2045658011198 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 547141052 1250 547139802 547139821
    0xc09132d06060207051e0901140312040e070c0c090204030f1202060c0304060903140417010b03030a050a0e0a05120a03020d030b0609040c09090507090503012412080f070c0e07030e06 80
    0x1030ba2008080c040611424809103035100075401d80200309c1e41c9191351240e4402030a150a2100040b85890040b104002c100f11707248040051031b5001c5401c0c6482c40d10800305182c040e400c0201607020a052070300220f408000d100d280006106060301c580c0c401ca081e107031200d00903a155034040b030301004448801d100003404a5190b03000419181e2180c9040701c10643d03c1038000c86503800c00d030032524003408000d2111054500034070a00d04140d0080340118203190540728010502d1080c43c15290803c250b00e8076020b40e607141c4107404c2000d80001070060003031120740f00c1c034199641c018003415001807080031913110801c0e0280c41613000c256805028285003c00c2807003480040e0000c400300c0303010003001d0080001c0701c64403481034501036501c960b913030b44145213410209403d41c0c0c40405444904011000c594000610a2407000c044401c0d00000d880b82da4031a0401b50010b00604420580e82c2c000051315000300701245c544001a03c050003080e00c01c60315464030480c101d40c01c840b009000d5078410320103d1403151 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 547142302 1250 547141052 547141069
    0x20d0c060204050402030106030b0f031b042d0903170f0a0203070507021207080c06040f171f0f2307121d060612030309060c09132d0606020705 63
    0x5000328405480d0980c1c40300803034200e910076400800041c1e5075800e046554a406c3c612050b1402c003c0b0010f000340d0000410191030740242a024910070342d6200d001c07003141c034152f0052420307000d280300d82a10124a000004d070301a1208000c1280010a80301c0c0c0740c070301200f060241502656074401000b40c6659086d000600035403010709040c05208084c0191401030303503074446800d5103100e01400703481c185151850b40e901e40103005010a1041c00d09107c244003101111000d07404480c081000101d02e845400c09407410403000903101003c44030840c40c488508842d41c0c2201a80d00e00301c03030080041030100c000b001c400b80c1004000340721003810540402c2d00d081c8181008413018003c0000060382584160207444c1c4510380b1500f6143c1500324004004d517918100300000724020101020754a54031b4a403410b16104c1d00c2c0203220008aa90210b04050903072550611700000d1902d0100400100e0f1001c075052907042c02038003215540c0125006c0c0d80c1c0c191200d6000c1c440032070744107400034078503103042100300032a21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 547143552 1250 547142302 547142327
    0x406020a0507020306040c050a141c021909020a0e060901050909060418060504051507021507020c090420030106050f04020d0b15190207060905060721020c0f030d020d 73
    0x101c10300680d03015075000e002041c0590322410302940c1343c610741024064950001c0d4084842c001c0c404041c000303603454a04c515002294112503424500000d0710015511a01014000200d1140b01d9008144031009900a00c080b658503201c1c5841d148851080010a2040d90342171400124244040009420070701841604014002c10200b40d041214a803d505203410800640c0c030766841d10240410302000744000d082e21800c1340b011003170038034082030065a6078041114140c4040003800000301204d00c28000081c04180c0184070311458107141c280026410342d01d036040445108a016178206618051203101e04036480130340303469824650f0404002c0250022407080c0175403601c5601a00d007503a0b8640d0140c05e000c0700405920b88403416849240301c014030400c500003d40d80101d0007400126040290302007203c4085074401c5c2e40c0c0f5090f280002c158034a50310550100340e81141c04002c0b99801085202c00300301b040d140c90000340c00041c1010382d19400c00b00800007580000052444840c4904102c4625 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 547144802 1250 547143552 547143557
    0xa09020a1e08010f020417070501090512192009240f1c030f05040b0706020705010e2d1b04151502150105060c0c011107030b0408070b011505030406020a 67
    0x690781d40d01c01d6404e440b240300702c0c3d10003107500003428400d02401c2100d2150300c5500d04020301a0781e0803c400030304000d400d4081c40384610a81010104260010416814030107840b80000320b1b9180319207040d181ea01e0000843c90b8000142c07040d154201d00f800548a4841c0805a548001604412081c01c0c2e920400c054026006a82c116402a0782d442da100d40c030049218002c04104249514200140b01c0111140e4800c03c11004210400c0340c0440c540030340b46055008000166100341c90b107815070041c0020380182d51a07000b0300078151441380002a00240c1d00c45240100000d484a103030740d0b1500c0d0b20781900c55201c4542040b8070f07007910307003407036484201280300200514000c240c4031880414419008144000160701034031380c400d00d4100205403d80100801e6030940d04192042c15881d84641507480900c1c108039030800410641c0c1c2007040040019a00300c1c4010300a42058101403805901801007584c00c080c1c0a80006070180500c0d121500e1346100c0e9480d13a00b1031300c8070b0317403001c000e5807141407070307208 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 547146052 1250 547144802 547144859
    0x714030a0e090717190c050a05040317120a05100602010207020303030115050f040b09100c030e0d08041214010c0801060f080403170a050603010e1204180e0a031101050a09020a 77
    0x301951101342460140310400702040308201228142015540c150425008000042c05a01c8407607801c1429142525800000380720140b50061115015004426080c0e02d600b0103070b000e1000c445155400715004441c030440b0306071500e8032148103909034860700d0300c0203401d0382c000c0004000c610b07a8600c1d000d5800903d494014909241c605884581c2d401c241c120215070710001411025514000341c0344003001c45141030008a484145e2000b50503166441c0701c240c002c0c05908081c20400c00d000048a001d803030034403a02d200440e030504200e004180c1a0411008a41c40c14144181c0c480c01800014100c07281c6664070015800c0072081200c5c000c201030400c40901440c0706203020240107808500340b1445580703400144500e4210100750950740032800c0d00c90942c01c203003442c0ba19200c520301220b0640f4440300482070000c0c02d219100c0014500250300e5203250042481680030540c0c0501c02004203040403000f0f000365124100c0c50b404540c8041da000b9404800c40d00e0400c0200d102e44074000c03501030036443c16003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 547147302 1250 547146052 547146077
    0xc03040e042001020606011d040615020f0709110405130902090f061f050a0e2706120601150804051903050901090e0609040f02030f03040b0714030a0e0907 68
    0x1460344005480490780c020a10b001100920440040040400c80900c028880c2c0d0810300c0028000d0583d80728180c200e103c1c910040030103601c840e005840140f0f42d404008100741c00b9014029110240c140302c01110b40184040002e41e801c25001c1c4030a610503807101c581c5082d14086c01c00810641010018400c070342c9421583c1c02582c1e0f500140d40c85a4543c0303107401e40038075080d410031047d6a450140d0a042441d20300030307464003036408400d03508403e50909140c6c842c1900400059202c0944200d011003814450074040141204258801e004860644012914030561100c890701d40b4424000d1181d80e078a0611a600c03024401c040e10340d0040d0080d82030320014902909654002003449206801040d00021030381e116580c008648001420070f50b010513400d04140000030035003003000d040a0403d07d00d1003103200944d601440050074020b03041003225a0342d41e490729060141d41040c1da003035031244a0002c041000703a40c048125400420b01e59940140241040200140d05030094041c8007088032210541 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 547148552 1250 547147302 547147319
    0x30304050c270c07140105071d0a030501020c03091c0803070f0c05160608090a02010c0209040303020408030c0c040b0103020c0604020d050705060d15060f050301150219060b0a0801050c0f0c0304 85
    0x1240289100240b42c0d541d03214034101120460f6174820040c5050f03240038200034503164072031003000705c0c0244d0400c061001085000098841c0c2d03400d80015105501c001203000b0728031000402498211403d840e40642044800c2504a0b1038040a80190440f50104000b4541620034540071217801c0c014100400300311140d0b01d0310341c03800551084510702200d000c6414450940c00800030f0f54400e82c0e020083c040404c15a0009011510400000b03020ba10814042030070035000f601520081d240e00401c485c0c480581800c590342e10000c403074015000d2442c0520804155101c1d000716075462150100420300c40d207584d802e2048048100200713403114029400d02081c40c0e038903200244224a0700f03500c081a920151691600d4104650b80540c09201501e9000d00b8070913040000e50341117442c421304446000341081c50507400c1259140901349011501c14000b0108050340e0f004140303480017075448240e4952185011800c882c402d407174414004078140b1040d500d00c60000e004000058220f416a800c255640048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 547149802 1250 547148552 547148629
    0x10120314030a020f120405071a07020f060c010510031401060e0c0903120301180b1f05030703230103050f0609120d0e010906060e0f040f081812031b030304050c 70
    0x60900c05d0b042182844180201001142e001e41280080c4081000501c011700c03941d4441e0001c000e0040c146001070b00c0303496031820280c3d040d0b80b1440000b031109181045070360030307419158001110410003420040b401000144518429103135020b540d10003e8689a0303580e070440c3c1081684541c0351046145d0002c0b07a15144015500a001864040302401c1080904c0d8054a446c0803029000c2c175580d080c0b0720038002c0f0310840942c0c0300d10607007042c513500c0e01c440300210b0241441c640101d85845219940700b00790007081e00024100c0707007d541640c124550b07043c5c0180d141c080c180e0340c03142183e115510188101c2014401002c500c1640440090303a4800c1498140c00c1d10062041654000e55400b01000307900d9940400950010401030702d00283c3c40c0c2a59403401d00095042e02400c54040403d003601240581d060000c202000145245180c1da20406d8450b034035404400300311a8440e602140c00703010715002095a0103244d101016111201d904c0302130200510109218205103105841e0120207103440551 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 547151052 1250 547149802 547149817
    0x61b0705010f0213060c0c060c020a03210f0e01020d27090c141306050304060204050d1101020f070b09090c04050603040507060207060504030312050a021b01020310120314030a020f 79
    0x981c03500e44c0340302d81c519918640e52042c0140044403004900141c06c01c1b56050070b94105041002200d8498000308681140f0ba400c020080c02d02400b0300c0e0902c049108094801460b81d646d00020061100d10480c0d1018604400c5409a440b11406001715401441c0425101020b900900309200e8003461006a4031010340c40f50403840ea488040100041d4040c1d44c240640864010f01c6103400490001d00e80c00040a2043c03a007002004808103003000900d4040324010940206081c41c0004a41040c80254180c60140c0d03015204190f80406109004282001181d005109503801c040500c1c050001080000303024040e181c408000101d003941e50200503600880c000d10040480608080020b4500324a5400441c1030000900040000950081c01c000071703a05100f1011070b4945032000d9100290240003901c01e660b015228044c0d090050541c05584286020000901103586e90500300c44101c113056000350019403404002e0a02003081c200031900300d044000c0041c034158a11141f550160803411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 547152302 1250 547151052 547151081
    0xf03211b14190c051f0815030a0b01081506090c040308030a06080d0801090c0e0a060c03020111181903050307081602130204060833040f020d022505061b070501 70
    0x807402e0281c1d04144200d1105c90262031103d4014a11080c070107000f4180041140f150201c440180a5a684080c04481c60a82d80303c007052140d56114212a9250740b1150040c6154a248000060052400300b660a02a06844004601d000e00715111303070300035500040c00d080149854800015002f00104000140d030a4a56103000e055414840358005440313105101d03104001116001e0a069501c0701c00e200201c850078204030f101c1881624003a409841505190f011155010801da100c0c40b81064890240c0354007251030b4503170040401c200300d40c0a403983c040075055510a04c4403200042080e0018010030f034490007202130060280d4006585901c2030441c19004070b030082000c02c002600011450b4200030007408143c0b09244034102d85441d041c42500c010386103187d205c1da070f80d825103e65001c40c0b1005242e00082d565180e1420a8070040d6000c42006640c444032424081184a000005000e80030340c00801b5282e6501c2e6080a00c844003803035281605400400c10231000005c000744213076000d201040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 547153552 1250 547152302 547152323
    0x708030406081509061309150b01091a0702090405150106020a02090f041101180f3b0402060912030c2505010206040b100f03211b1419 59
    0x41c10040091402400d14045040814903100c1607564618446511002c2900c030211055401c543c0000904480400a0310941c060400f1519a0030301d9040071085280c203896104481e66a82d4600d100c100108480c0450240240a581c1c01454003040d05600240100115004401c103c074452034069000c0c1d02c04009039000019041c11400c0c81c031b00c5d4552141b80b03c812007205203055186d0340c280105038481c1604204003521070b0a0055002c0c4aa14040c02803040d8142425841d01c880440c0748510080781070811104081104202c01081000d040181024207503d1454950303074240b288ac2e8024007e5168080b180842008180f0000c101910101003140c0041c40021041a00c0701545010346081c0a20312886200500050b6000144290486d602000e41807550380d0764010841350441b150805050b203d031040000050142043c806100c3c1003100414050080030010180c5607041c86000318841c1e0f094400f80500440d850340a110b204244100c240d40b558020a10503400d2020032110440704103298 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 547154802 1250 547153552 547153559
    0xa090b010b040b090d081b03030f0a1506050c0705090c070c05010f0c030c0f0203070602070906150e0409030e2d192d03061415090a020901030e07080304 67
    0x25400640c01840c0080e0164075180c14446100703418850601600d01030081e461540d0100101c0000702d60b45a602c86040714107040c20100b4036600c99000365240d00001500002068416000e403049044013282d0503000081c40e07290110a40c1e1581082c04050b8450041c44ac00180c145c9400c02e0482c820390784510071940d200d0440c90b03c1c81c0d001400343c0100e41000582d0051030f0354580c10030345401030640c140c1846040ca51051910680d04004a031009425025420000501c50740020b9500283d60031054244040c075101c9a80703103113a181c7c91064000080b0b0394010488541440d42c0030028582c068a0142c4801182c070000c03a84010103c40342c000c0047d500445440129049182c00c41000002c9403122150342d9086480700a2000500951801c4c83c1450a2803040300203585000b40f0640c092030034540c85c0c5981c0d06280000b00b04000b0400030a6480c0780008110300d441002c10b031002c1d0801015001d003610f03260820002904010817540c14160b40c2d01d01d41803002c004001c2c820080100030002c50381c4030704 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 547156052 1250 547154802 547154813
    0x5240412051c12020f04050607030305090708010b0d0201110c1e0103140f0a05070c1401060303030b060307080106050a030b0414070f050c030a0e040b0402030a060f1703030c0903030c03030a09 84
    0xc141510742d40140e00801481c2c240ca0b800002190040c4505a0150310384000440d810001e00c61a400180e001000040b22010150541c018511400710502511f0701603a4850790142030750081c0a401b688104140a8080190301850603501034525900803600344244040205900c00b0b0000070aa0001001a504070910f681c94090440300b90510003500c4030340d05001c0c00b08080d00c2d90140101c5041510384000a104a200c1c4194a22a5410944172a08039881d160424000c0c511070005400007410401d0350345450600da0200d0340a00d80795036034600168070b0400212074070340142c1c101d03204058460108a0f05075440d070041107007040300d80c45141c11030b084c0303142c0c041d00744203c00d410803051220510021044510200a0b550005110704040d020403101c41c00003001404442c8265078401e2010043c406000c1003a4002c90954200310200090036480d401507a41b01d070503c503540c00d0300c6da10800c0010707110000d82000d803046580160480e410900b07001115400d6400c00c5174140300040d900d505200a202 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 547157302 1250 547156052 547156063
    0x90504030c14030a0903080a030902030307141203280b0d03110f120f0711090406050a0e1902270106110d0302120a021c050a02180a08070524041205 65
    0x41c0b080008500e400001040a040f048603484040e201c2e120104d405070715140603070000c44d40300303070b000b026a0ba541b1000c0c13421103610002c20413905020300c208000c80b0401034400c0101c9000e03851000401c8854010b007403150403903801607900ca80e600f5885000c00c0105d916100050075849103c1c1d00e461811300c580852442c03500e480c0104500c1540d002c0c800034600c4c01030600c2207400685040c1d0509644107920b05200c2c000c40c40702c8038000d4101d06920108818000b0542c00a4000c80d44c401e42030019007410980d00d0781d11100c034407005001c0c0c005d0b915400c005103003000c42000c110303209258400c21a1100251441220000da108502140281c80031403485681405420149031031810210705001c82c40030340300c19050005000743e02003a800540001008004580d0f0310301210a04006d11240c81c05100160183d00302400c2c0c01c9002c0b507030300c0805282d807500c0c5c162030040d235800307400901c40039140608202154681d5070003e42400c520700803003021014a00003e0010b09080a038400e00d095051800070b01e00f1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 547158552 1250 547157302 547157333
    0x906051c0f0609230103020a1503060b1b2103060d020d021009050909030f0a0f0c02040c030605040f0605180705120a06030c0e04200103060518040b160e041104090504030c 75
    0x2410b1303210061005039642c40c415002d0320459410341012040c4004190300601e05030304000088000401c0510246100c0c0d11465003804c0001c050360842d9002408054501c00e1121f280a81c3c1c031414400581c0c01e051685022041600041042c900340040d83c02080704141ca07260003c0029844580501182c1008102d107608031f000480198035060348120742031180d0013400c50350390800142c0e01c003c01d9100d02c00c1d0b2070b170070986800400802c5284610003020b0003c24507441514001c600300a442d62036601030307100f95001c031500076249403c00c008155000581c40e00003010301d010f1003820b00944075595503e4401611407041800001003650a41c101000050382ca94072042c03038401c2c801d0401001a241410f0782d5940e0b024002242d03002e00b60007005078003604088c0c000c56005428809045042d071010741c0058012405010451050b85489441207040201c0b406a040070800c4801e4405540c1020b0f070103030800030924181541020b860b0303080401910402d0303070203900088940421401b40100c3d0701308442076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 547159802 1250 547158552 547158611
    0x80d0608160e040b150306070c060615050708090316031101032007020d050c2d15160807060906090203010f0b0102120304051509060106030c0906051c0f0609 69
    0x2051400b902ca02c04070744020030040a40c84030f400400c1c0001540b0b04414180e400003420fa8100f854a40300082001c1d4640000703a803c141010380000c1d03008510342400100c80710b1035840c5898003d160b181d2010700c0e8803010a05400d80300d40d074001c0c14250012814040914406c060130390a010480c4001400e44110408a5000031a0100070409031a40d103802c0750200340d811303141000074018505109081603a0186101d030002c03268520404031003050829610b00140d003010700345101044405100c668542511804c1c070710031082105900c1d00f80c160b9114150540700e1800340c1e03c1d2210969648090752070091f4103c440d5621005000c085150038041e164032000c0504041010f4142c02000039590f0500200304502c120000011800380f010a004143c07540508222a031214203140109950712202403060000184ca441d0441240034482d040000460710710342d5400341001043c0c410620890f407180c00540100da3b442140260401c240d0180f200282083c030400551402c41c5100a0300700100c03000d04406 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 547161052 1250 547159802 547159843
    0x501050a180b010e030610031b050102120d0f090b0702240a020d0e030c060615030f0711100c03061a0306030706080618040b0421080a1107080d0608 65
    0x22a15500741030030940004840070036a642c0441c016510400c015101c181c043c016001000310408042180404072445980b40391aa06402021140d07694920f003d41d5006810048500004a1002019000a164900000a80507801c5240b10111081c42c201124581c98032410403054640600c4800400c401e58000c41505040b101071048500200038074020300300e540480e544d40e00010650011100e00b90741d0b0201d9640340b6004580503950300041364250301c903501040d03080401d46420000c3da80a41120031b44004140c071210b00542c1e54000f40d031089134403403003141c4000003c1710a41c001c0703005140e22610000750385030810204140c000c043e0744280c03001003001c0040c0072083c0c50014120044901e1841d0581d095119400000e003005035107000b071944c0c030b039080302031105006011101314062031040c610f603100c4540310703444015410302041a00012035200b40004211440c2d41e04261095580b031090f640c42d1111aa45e0302c14550460b592020000d82e543c403047c091030f0410824009101c04031302c1b0846 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 547162302 1250 547161052 547161059
    0x4120804021003180204022818050103090206190915020102090d0209040f0506040b0609100815040303020c070603152103030e030417060402010305060415121a10090501050a 76
    0x311a082080e040030300f0160342e00030080b2001001400f1400c500d50080080d980c0d0100d45404d140500702c4154000c000144c0070b42107030460b030300603201c18008031600d0040c64408c80c9000300560060907284003e07a0000801c01c500307426041241450040b00301c0d41c1e01d4208000c1d0400480da04c0e94270343c250300241036a10420604001d030341c1d0078249010450341103c8024250380c4601c0c20240344a10048014101d1140109210401c00342c0c0c48843c1c407885042e60002c106680322901c44c24009002c3c4241c0000381c01c58554083e4103056030080a80c428001d05015180c003402d03110a0746040c00c2a0301c030000090781e41800303030300407404610b1500042181d0003008940d0400c1042d420140c0121802c007c040c15a06c01c03140407c0d240500a890050092100040c0c1d840c45460029447d00012103080703000916002c00070704649014403441019001c0c403949540c100d42030030415408240c1c080002e483e0302040040c41d032070408040b0b800c18482c4120307581004000d46041ca04500750ac50603048180714552a49003403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 547163552 1250 547162302 547162309
    0x30309050d0207230d06060806013020030304080c1302030f060d0c050312040612061521330501080c0d14040303020319090b060420030403080412080402 67
    0x3440d0356894035030b00207869134015001602090b4034a0009049506003507000407203480c00b080301c3c0c0c121485d8492503041c46080142c1e030103076040300c050000410358150a140012441a102c25400e1070843c0c80c6c82048102c900000a182d0b07000365000900c198801d4104001a040000040038040c03040d02042d411824032401e61400e041c8001c2c032103030103a0803800351401408452607e074001094003406a0320380034030420184203141d015000349004501c3c0c81e010340038440c40c20301c600001c64100d64507090013081e400c882250400490703c00110210102c04003508001402e100301c1c448030f2140609000e0351540140c101c0340394050714032050200240441c00b0041c90b60046540d6070300102241103030780c1c0c03140c200f00100003c1800d01c0b01c2528100c1840d041208060305640110302454040b034600411500d40984941910004000200f40c040d0340c42c0456054103250700300c2c145074a60b0f8040c02030003861203400000540c000311400e03000107400340103000900c1000002607004606914144c040c5103042d8021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 547164802 1250 547163552 547163579
    0x30408030601080907090609020d0513030c030e180a0e010e0f0604080318030a0e031903120f110a0203030f0a0504030c02090702330606070f0b130609030309050d0207 73
    0x895043c003a1a00018013090014020b55000e00308040c0100f01c000e48a8080070005c0d0014900141d8180c98040810320f50488946100b80d100d0307160780d400c1790310410780d81c0442c0c4606480c440f10341c0206402c0400110b083c0c4200d1003600c65801c1030710014070032007200f15035401d40e60200407142d50707600000c68140c10300801142165200f508410295640d440f42d00d600a020201d071666985180000301d4103461099011080c1102c03141c08130120741492005000300441304216400003004650010b0b01018406c50030f8211103003451900500042c458042616440580e0210607030340b0041e0000010803072803104400350960400032045080141e45040e5501a207035803111500a4407502d03080c00080c100a00c00c200310318100e6030790303413020045c6003541031002c1c07002d480d441640010114040025000d42040015078000d280c000c4500a00000c403501c0c7c0c01d040a0001e803102c01d064084200d14070100740140070385050580309607000921a120f600b410f5061466000d6100215000304408105924072100e4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 547166052 1250 547164802 547164811
    0x1b040e0601091109060a0f0f050a020d12150b044103160b0705071a0703120902060703080609060102011a010f2f1c020a03030f0b1e031203040803 64
    0x10002044680066415541c0c0201380b20030740e10460004a03c5030396a40b00111b400c1034255919038404c05040c20310151030351b01903403282c200141d01c0140c0000e10311748184816120140c2039000042e103000c180c001e1400b4258240c00c134000d0b03044002003c01c03846400307001c1c41c0c400c082992980707100c6803204503101c4910103401c98903886404c680030020810381e4050051101000040c4828030006594416610980d0484202952140200600000c20004012013075448840c26203d20703242201580d000d652404410038032103000c0d59520b040300700686400340101801802512601c0e5036140410800141310780090500e411641815119013841400080000b80300c402420002625242000101d88814030036540e68403960001c0301c0c600c44010480480030116003441c0987e41d40c580304017004c3c00442c039101100b00040e0302030f1300898042407007035201c1c440485800d0320114100d000080020303050000c8144080e1000e8403090322451515040180c1128000000345942c1146029210180729000042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 547167302 1250 547166052 547166069
    0x201020c0d0221011a01031b050f1e0318010905060615070606030b040c0f0303050d0c031b0e0907020a0803010311010c1403031e1311040e010e1b040e0601 68
    0xc01c100300b1561503028440d401c54464102480b9485059810740c041d040c400903100311280360b00c8001030f95500c01d024003a505103600754803c40048008008441562041c0700424201c0030a00a0460480c03908d052403000c005403c5240391641003000550500090501c40d070701d8149e03d0004050002a0040741c4964060300c1140c56038080349000000b032185215044000344a1498050003200b0801844000c6024500619455102a0325410b540030003110a00010300881c41c01d200482c0d01d60340b241c10040c0410741030f19010800310b0f200c00e02c10b801c00c40040540d001203110044c00c419541032850030740d58000032a100410016031103884406407444103000144c0031085d40600040103034054201c1c501012b5004484602150410780481d0701ca07001a108410700000115450341e080d40a29003090044102e040383e021080510f5407090324a03225810020340040d00c0d09540d03904140d0038070980b100810341c0c0014203814589024041001e075034880c40c4620079031800d007514000440000310641501c10b0348 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 547168552 1250 547167302 547167319
    0xe010519030f0e1005040c05030c0915030c1c050d0e0a06030b0303190504030b010506280c0203161a18092e0501030b090c0a0c0309050d03030506011b0201020c 70
    0x310642c81c0030306400c8090300ba041c03041c0720300310a004035240d002920550140c05542e40c030710f4650b0308050300c0350340350300340c4c2540024054041504508042640b040c050f00080c1140c582070f1920012688440e02ca0106d001455640300859050040600081d00020940d282c2001c00450560001d0341c06c0460380a01000c060351352107242d03d20749080088070781c0e600105200c4401003120000041181d41700b400120380020358400001014200041541d8a00c0400d4032a4101c515424603401c07540850380d0709102c200610440c640c005a18207010f07062041500810f4404c0d9141081c25044d0940c080014000d800c03002000f400100d540c514a40c0c0030140b504803081c0304280c1740e000b10240c0002d07506800c0311000031012102c40f411032801c00c1c048203d420a0f00c00b030001c03d4000c02005480c110488007001c44030000c0280d0180c061248012207500c91080c1000c1ca41152601c021600d4402e81e102c0c21004a682c0703406100007503070803003000c110405460251059650b00743e40000d46601030900c20746c0c0034008a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 547169802 1250 547168552 547168571
    0x1271214070b03010f0e10060804061401060815030708100c36060302070b010b0903010f0203090703051c050a080a1b030603060b0109051507030e0603070c030e01051903 74
    0x540c0304030364540040100315800e41c0d807a401440314541c820720602d40c00c9848101c1c0010441d403100d902d680704100b00c0c00c50103059407070990300390303400b540080c81128003558031009041720741c0e10b0b0103801d4080c00d29a60307803c0b95407a2920481c1201c21072009801d2080c3d20070b00c02088800f200268030030039100408400714507480f6219055448000f003540742c10380c8a1000e124802c80c0e401c501d03d540307131400c144500443c1140d0365802c2174003203100b0741c4405402030740315400610042c22481f00500d14044060000100c06074042140d0b410be810541304198103401c0316404200340002000000f42d24941ca03a001c1c024601d95910140151240c40008028003a0190000d504d0031b000f6400b01100d228040e0013200b5000d00558000c3c0140b0180c0003c4915525142c0b24840315449151150159513000d00680c851a411192140240e081031604600308120091102c48545400000d14010745058444034080701085c90041d1a21074155601810000c00388542c04110f500100240c142c401ca9040c0011003115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 547171052 1250 547169802 547169813
    0x151806090201051b0a060507030506031e1609090b01090e061603061203050a0f020c1e040f0204030515010e040b04031d060408030405011b020105190c050d030b012712 73
    0x42c45003601c50315038014002c014644d0b0046020420148140002c00c0035030f681032000d90440c1c000b510044e805130701c2100081c841c902406c600008080c039050840c1c040a840d0041c404203000103070483c100351030326074000c02e0400c42904440d0f400b600e02c019081c000d002140c0c42c8c20b644c4040c010042d80150140e100582070700d42c000e5210360083d1642561f25071840310103080c05401a840314001e00005402900540d6020b0b101050501d010b1800901100001d4214003901c69019071010a031035100da510a40107a250304a840240002e52051b00500080308140365840f2003808141d0200c14a142d00313008003c0080c60701c048150b409581400c000c0c03002c0e132591301c0488218921540054116200060200d00b8aa0010181080380c00076640d00680800880407800801d01c0c4c80b000070f01185040c0401c548a145000c12611014858500f85007034090984950b49014a803401010110b6614140f414055030701100550300d03508080009420681c10002d01061811a0302c0758040e0301c41a41d840504000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 547172302 1250 547171052 547171057
    0x32d012117190e0a080d0c080c06070f0212070305040e070c0f0b090c01211d07090906050105060c06010e190218091b1602040b040e0a15180609020105 66
    0x10240181d84400c640104030140c0c40005812001040380110703d42400d2420803050300946a0490140c607041c02543d070107031156400220300715031660050180340c4401d03008016403032144142d91340e200d0910340c030000003034140341c07c00c3c0e00c640c4001b02c104900310200313400c00100c5007107031114030f0350f8141755880f17070000c82b108004603030000c2000c40902009000d0100320107502d4060781d040825104051482001900d150030a031403e840981302c078020b8914600310540c80b02c400018941f58a1001110303000003241003510360f400042006560742448410f0080e54440c0c40d02500b01544d285241840e80040a595440c0500c110810300640b07600088801100a1b8201c0a00d00702600540d107403410729101c00c004418507003c041c00f4030300040c001484001c5031500444030240859250340f0f48030710071101390f0f034a800108080c1c3e005511000c1c01d24140d2130344d00c07525400f407000e100980742500701303454044450315649107002d9483c1c2c10310b810704103480c9070403503c0f40d1003070b0b030110000560300031601c01a00c190 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 547173552 1250 547172302 547172333
    0x141006210224030a052203170604060b0c030310090507170405240a050906070c110303040302091e15060f1309050c04150810051c08032d0121 62
    0x1850103c180103040c6440d40119025a003e00e2407041c00046070b602d0603005010803500503002403a040c8005201c0001a24599040f000260000c550700703490b103030008482c1c0d0217001103e20036400041040b4000303107c03511000180103051000e000b2800e0400006040c0030a54802c40030580c1014040f800300141004000c4e0f4000c1498071480b0b5458440c06803903425081199540542d609007000690542004940e1728408c540c070361502d00600d8519220710354a10b9035224000e4051204000101c00342e92074405241c410141509041040f4651459900860790060310f0740d407980111f200002c486a607020143e03400310b24601e215a884200c10024405000303241c1d4014080d1602d0a0140710340c81c90a01c00410540e4142c0c82e4074020f90b2030b603074021a51003604a0b03070000d449168483c01d000610f40314400c208142c0800803000521001e035103540c0310326401510098104103903904c00070107441c2441d051250841c3c6408030a51203614008402426100b2902211030340c8200710503034000c000703100d507003020032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 547174802 1250 547173552 547173619
    0xb041209091d060903040e010b0f0c010f0b040e06010e0703021c0603030309120504030c030b061f0e0a0e010b0a110f01022b0c0c060e0a1410062102 65
    0x100d90050020100d10101064400b20300d000c1c0200252840a00200701c030101d83c1c00700311b100016840c01c40c00100c0d0f500801000400c2e11010010705070051024019000180300f54003000a0030380480b0108412215003004031501da4120600401190001c1840c0329400486400d0141c0d9074019074200c20028039018001042d40341c54001d002c002c1c107078140c0c09680c0f4184540420381460320765220a41c0d0b91b02651000401b05c141440d001d00012780110009504454090104e22410488a9101e203014940814960004542101210080c944805200001d02968041071b9041d4182500101a8407800710890144220810785d0209290100405841070701001c0086441c2d00e1060080c03404040e10f5008100044001100c2c0c0115440c0c0d4072030314500b0a0580c0360f81860201036500d080c098a0701c0301c1c03940c059009800a410100d085401c01c0c4807610f8020015002c50b440a00120342240c0094200749a0f414850407a008080e00710181c000c402c540468007100d6690402004500c1000c030030140501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 547176052 1250 547174802 547174811
    0x109050a050f01060b070c14010302042d0b0a0210090c120c0806010b190309030504090c0305090f190314190e03010608240604020c0601080a1406040b04120909 70
    0x784403000c980d00d0350440784180284040c540c1e9036a0301c50a800380c00c0014000c20032070070f07042061030340c55100708041c0701043c1005410f00f43d030360745040d408400071410302403406407030780008120000466902c005400b0000500381003840521000b03541c1c01001c221205241d5031a42c910060007c115070242c0100801c0c104808407210b9882c01d00a844e503175110384c006520504001040040244c000c0e1141001d60035000100c1d20780001084010300401a415000e110f010080031070281d586004004100200b500d0214190038280301f02441c1c0101c8041c007240711b80106c4544d00900441611068060350141b9103904400c0c01c0440b40d13072140c4501001c5038900c07511915a60b0000b504450010b05143c0b088008100040c5d42d02080c1340c50f00043d849401043c00031181400d8403183d80c0c91199008007020b0401801c0982642d0395500e02071003a01706905503401a01d807e004c0010100702003060720118005460b0f42e00b40340d640c1c000381d80e40c0584000c2c850f031002585402420301c9500d1071001042c42303070000e10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 547177302 1250 547176052 547176073
    0x40e01020f070c1a040617060a081b090c041212031512050d1103030604090c091122080309040504050316080306130e070302042d0f140402030c0405060102010905 71
    0x8000609032013241d942165203a070103c00503407101c0c250b408440f410b84516120000b00d00900e200107500810f0940e12815008021460355002c10108802e04038450034040140b10084c02c0085010300181491144081003205100c11403601300240402984152000030072a003090f0190003a22041448411460b0102400105024400e2f0280b0700207005009071340e0461070b4801c0886040306442e0f007075241d0350701c01c20200c0e0700383c105940405002e03801074103015062a164603030355040d241c0b43d089001d01104040380c131041c02003056003400c00c440781c010780204007140f404907603944a006400241c0c1c8501c0e610f0000030b003800000c0c0101c0307041031105901c0c00d00a51441c40c04480913041520744500407840c21218240300000c0c2e1240c4c10f20103030b58030000c2001c14034581c2044050004590100c10b052243d92030702181800c0040b4482031484018800314400c040256413104440080c030041c0c80c00c0c1400814080503071000304044524000541d00850035540300c3d030050340900078610313000b40588903090511 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 547178552 1250 547177302 547177313
    0xb061c020a030e011407140408070320190506131e0905090304050a03021c0c08030405010e100c0201180f0b071109060303190210060611070e01060e040e01020f07 71
    0xc200300c01d00e948080190b002c092541d14202c0396041c00002e20034090350085005140107031400d18080300704100851803c0e0b107403d45141011500d52044a0303043c2d005141c120f8100d001c2c25060031071502911407014510000140c030f031008442c0d06c600790241400017142d08200001900c240c010b0447d2981d40048070081e4211441105094071481302441e19100200b494031030003108982c101c2d4001171007103962a0a50f001c010b040302054034588070400b4612048800101c946580a00400544000e540c80310b1412001411250903d41c406100b100181000b0b54500e40055a0b0b1042c15020310707060842500c2c40c3d1800360314003040d800c40303143e981443c0e400060850300075005091151103881101c000364604400e001d0004410b4a9007541034106100f00f20616446a050504201251046581e0201c2001c0b0070421982c06400c04400600a030401104002c41000104010140d800019602c0c0d850110018441d40c4494030861159817207000da124661006d405482c0c0500200403025502c00c511700d0074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 547179802 1250 547178552 547178557
    0x190203070c06050c0c01110a02040f0b0910060206060108012301110f0304060e0f03030f070501061508071112031314010c17010b0c030a05090315090102180f0307090b061c02 76
    0x101111071217249004049548203044840e58012030a00501c00e0700c0107a800c01c005040c0303050301c0d00700307079560341e04040c150303035584403445005030501c00c07000e2401410301c0802030030702c13100502060500c15084010890104280d6850f2441c0248a41154902e418503004031160f078800b5074000d015203c0c1201c00b0700d10749000300050003140c00c21b44170100482c0c00703d000d00c0404182d10748035542c19002442500826286540100f40303052060000141d020f0b222900640380d40084c1d00d009000418500401c0301310340d0402010303000d0307241c108010100780c0c443c0030011183d8807004000f0341c07200001c241c0c2070003004003500c0c80c0b110780e0884000902c052082c91000800000705003100c50100d290303040c00000c058044804480c2d05a1001c00510710f05852a0000c0d5607603070101010b07982610454210403500d60981c003115005800e020005a40d40800c58003a118240070f0030503061141c4908c4100c0a40d95800281d088102c4c2c2c100c41000c503d8180e440c002030401d029150034103a9100c0a580c08040300030b0075900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 547181052 1250 547179802 547179817
    0xc01060602061504060518070c140601050103050702160b0a09030503030f070f08040305031b070602071506050109050f120c10020f120301050f09042a0f0509040206190203070c0605 79
    0xc10420f4040e07200400040e50300358412503400c0300007455000310081081c00303c581d114409040104902e00706a4810400e451700c81c0b0705044581003407005000b07940c0e02d402a507401100920081850001da820503d01480b040d00c2148640000003810ba0422401a15100000c64011007030380c2d141d03c3d046005508103102110303104005480d8803c0708042c41e02900e007590003250075a0303d0300d04543d1a54106900f1414180303036055840000e02000000500354001414107a1041d03d019030707a405a459514107443c030036086641401450f100600c0350f0340b5a078000300305000b0211000ca45107040503020074180690154078540005401000091080c2c00207803004d05408400101c8428004007010305039a0300080c010294880c52944d410080d5203040e1a4846c1c015000d00d06418240790b8140220b020250f803817000c250880e210103020080b690b10f40d0701441c010201515515441c0c60107a00145182c40b03189076006a0101c03c0d0400c2c41160301c00c00c19203000030f80c07000c01a0312858903410701420300d4003c0d41 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 547182302 1250 547181052 547181071
    0x30709060f060c0b0c0d0b060403030203070b010f1d040609021c030f03020310050103091a070e0301181212060e0705040905250509010201021606020702030f06130f080c0106060206 79
    0x740000342d51845400c004003000d40003020f80c29142c4909013841010750014030001421501c40b4540c07061a80c48800800045119800842d03407030317019140450701444140d100b91801d9006d000304202c4500c8000d09000b026a01429145041d0340b20f00c2d12100404641e0b0020f5003041c01c2c40d0001240c01072070f0802d420002d000740c99402d80ca401e00882207090f444211400c8049424001c03042000d54040c0c0c00c48184c00b0301c00d482e01740703c05010401000040c1d40450f00b000006030301c0c481025607400e003846003600442e1040c5140c2503800c840d0710b80e065100080d042417420403001d40d400498464190380448064100301c00346200a0610140007040e50b00103014880c941d0345018041442c0d140f1554851007203113200c9500707880080c04410150703525042070381c203641595003c10105034180048941181c0b480d00c520401600c4032041d005043ca0049100c1d4510004c0c2d00c10f200344109040c0851030040e4180d4440c0c102010490702e40f0301003916009480300b04149600f06100825650740106074140b00b1301c00b82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 547183552 1250 547182302 547182329
    0x80714090c0306010c030509122e18110310021611181b0c070308040e0f0c0706020a0e03030c0a0203010c14030c03070507050d180902042301030b03070906 68
    0x803070540d030152000741d81103400702e9802e0584000190056014000715030000305040c00d01a9000e801600707103500f44000140503211589040c008100c4003a44600415000000700005c05562076100f550f4440d81e00d01420314414041c41032a15641000429110185000107546078000c20311001c20320840118102c0b801352054080c83c0b01420912888420a1850f950030b00caa074076903505d5020000413030782d00b2813a03400042000d400c012100300a00001184070702d5149540e02c1c6011107400e0840350162100ba0208107160510010882903070a44503015004100145d82e408034031020340d40081d59030310781901404045000194880b0102e9a070a880303000750000d000c1c07074141d4582203c1d00ca1200383c00000d40c1030140003103415600004055903100360070381007041c90005540c448614140c0100b008100040341d86034a12540516101400d00600b840c440642c10a420b088003420400071011854404440306240b1580c541c0c03094000a9441e10054280da9896445800c00710190106015070728070904130 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 547184802 1250 547183552 547183561
    0x7030f0303050103150504030f0c060e0f0a0c0605161b05090c03060310060605070b060d140d0306150e0402090d0b011401201e0a021503010504050a14150a08071409 72
    0x86004047c40b5581c0344d80d40070042c1c84503400a441c038138109201561503650714038042c0f509000801c01c40c415030103520001c00e0700c0e0555280107194906a40c2003c410003800344019960a068008800601d40d0700c031404a0007201101030120684080b54419944901040244225441c0d0000154080c10b0258152460030b04108030703541c05e40e8468400c40000480c2082401c0206889000082c2c00ca6001400c07058030100c0780e00c6a40350750360201005800da8100b20103144026816107d00d60051544800801c0c0c01c4d8100344002d0164107c0d0084a401281c0005050503e5035440503d4190701c1d07440402841d565031945e4804490810401a00b030200d1110341060160025400a0000c7c0580d6a0010300150407903018072868002e10101445943c400c0b40040401039942d0388603000801a00c500c1a46c80e0340c5841c081001b5100045c124244c030600d024421128400300210050b8808000c4140160301c11410000c1200c2d040c040c0d10215140c01100008900f807a01400c09401c503c1007244c01301165101d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 547186052 1250 547184802 547184843
    0x36010c030b01020c0f12030304120906170406020a020114010b0c0f01060b04170307150207061b02060f07020a02130b090601090b0702240a090e070507051b0307030f0303050103 77
    0x80341c66006000d6442240c04145900c1d0403007286034020409422260803041480d00c042c61600281d0f0100c0d0740140034408480c40650006c03d00008103500d1610354a0300d44100400c0c3c0d2030f000040c20103800d2907000219142024001d400005600388903454071b030700b20340e0348a010290356040700c2c070400e0240c000c0a940c040a038105005040c01d41d0b0010211b680760516110391100c0e180c1c40c00710101800e010500400000c0341101020545a02d41140051380d00c0200d49400012515442207054404224034403007407240e6400240d1507408a03440404c0200c6817181082a45001c29180b8000d50054031403094410142d41a0441450154151450300c07680e2100801580d80c02c106002e2842c3d0790400307001ca44d015240001130014540031050f402c0760070420314515021b869100f09401c6000c40d540c48010000b860401e65042e03030200e490700d841400c06083da60b9140d22030202e5250601050f65400c0250402c0d40d05100c0013005540c0035000b800c10f4516460080d02618091000350307841400c061081c2c01c00107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 547187302 1250 547186052 547186061
    0x20604060f060b0f0711060d0501050f0d081602041b0201020d0f1812090e040f1403190c081204120e03120f03070903140a150b030c0936010c03 63
    0x10000c0d5280f82c100440303081d04a106070050103080d14143c00c00759425025865a00041000c10118a004241ca604050074440c60301c800c801d96134020082c02c24a0000f062241c3c064948035482103106030250060f600005020b0607684000b4451118420540459203805500074000408070103010f000c0c159642d0f0001c012200004901c840c00602400550002a03480d01001081d180b90b041c0f4050460b241d014518030200d04680441e820007a4550080601102040445a030100715000354508603414410310b0740181c40030f8200c000d0040c1f21702d010f4108008042076500f00a94521020700b10301e050b09150318801c40201111300804c1700c1c1c4070054003c2c20701003140340c1a200440c40f160702d8400c22202c40b003a203501c0240b9200400019030000f20010380034002c01d0140c482e1103002803461003d6070070f0001101d1111002d416100b46000101300d40c58601288850043c041254201a10364504a403001010046c003404035954203075010b50f42400e41191509514101903a0007000341b141003450a90886 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 547188552 1250 547187302 547187309
    0x5160303020303061003020c010c0c050c04150506090f0301180b0c0a05040303050c191101030f051e0601110321090a0b1611061512150708070504050907020604060f06 73
    0x5030003c00001d0418142485481607038861860014a4002280c20385805c4602c509035400001e05240e40c8030003170100410034040c14074000c607400c01c562404401800c11603034440c0704641c05250701180e01541960340305d02a40005002800a01250548000c03005003a550302c00100c0d03080c243c1e000070802035031184d000e80303080e003a46807182403034103055860688840d0441c92000e5403511500d4900d02152140c0d58000c0e08540c40b84889a01541010300051305444400f40c0b5505103600e0241003148012081091403000c3d03500b80e00014440d161000100c4c1c00500e0003c3c1030145201c002150765026030040b01c41d4031800301d4040a46c034161134003104540ca0728040d0801800124032079000c1100f80021545990f900d0846040c07000c90f006260b03420b0f50801c9002c5440807409032045103080c041d401c150580032102080c44010307198120000810703000820020f00080304104c16800080d198501880840e07024080080180c2d50301d1500000007540c403041140e044880c18100070404020080c18003601b03064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 547189802 1250 547188552 547188557
    0x1407110c330a0525080a0309110105090a030f1703010b1201060e03060f190603080903060108070f030b04030903020a08030306040f060f030212160e1b0703080604090614010b0705160303 81
    0x600410b600544100780107144d0004034220416009000128000001c2c1241d014070f44001c41c20201b681810b400d61070002122070f0500c981000305601e69542d4840b10025a42c0c002c02c07851031302d0700c0c40c14605100e41d043c4140169142c000800440c0610300117010705080c40040003e11841e83e21114100c03540003d0481194240d400130000c6041074a985d202c00f40d101803c7c00140682c0041011480181d40c2e4640c4203854501000505012508081c4000e50261401000422425280143c8408540300502c0050400490080454200340c89400040000e640041414201c1d0380c80710421501c0380d000f540e4280c4228941414107504210700d0140310704483c0001180c01c070181c0b843e024004039030101c06e00c0d00d10300d00801400c010036070321283d07940019000d40c0040314074610b4034880c066403009200c2154a5400414000703400025481250158880d50646000c140e03c841c40c5000c801500703000800c0e1a601181c4000800c00003512405840e10b40d0248003203680304825540e50164000c00360201500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 547191052 1250 547189802 547189807
    0x10b0f04020703030905010213050a0b030f2205010204140108151e060d0e0a0302060a051612020909090303100e06060304021507050703080904050a1407110c330a05 72
    0x2414582075000d00061402810f010a19291a9540324226803040d00d010a20b001003802c14072103800c0c100c400c2d00190040040061450500e4011406420030040c40d000c000b00c4d030b0842000817010320b420003c52160b4030000954885840da08480780b5a05000c0a19000418010015100030f0030610085003032a805070402c1004081181d0410b5176591a4840e81d81100b010051112451200e10402082e0303d40d10000c3d0404a850345002820f01401601c010503042c102800e01418a8000d00254007010407410015606042c030b59209000e030107040d00c0e90745d11140c0034003000a40350000c030046100e510844210940c40ba11042c030103c1c2a0801d0300c003280c04c01000e100040050400d0b41c25460301a40c0c580f030715407e00403580e84091034140c1980041b680920f000c03e42180c2401c00d40102504180e208406101d11548040c0c102880000142031004009980721424034611043c000a0708074240548460000c1260451490307c1102d01c1c19045e044855200003a0200d204c59826540500340c40c1d40d41c00d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 547192302 1250 547191052 547191079
    0xf0506010e01030506180c0301091b022e1b080a3821010c110c090c0d06171506100e0a0f15030b0a0b0708220308070c0503010b 56
    0x10001d00380106040c2d04503c051519070b2880c07082c40d1006110364410343c0c0c05a80c2798104210320090740c0020103145000d01000b0300241245401185126a8440d482c2125000050b40c02c018001c400b00100400307034a91818001c0c00c408104d00005d408543c40a8849089a41700d442290301180c0c1d2000e988410380320b55039495107450700110a803180d02445010000000301d40000011414030311310221402d0f9109680c004180c03445c3c00c1c041c00f040c0b1645410a4002000c0100324180c0307840d4041c4080f44120340140000708109403460595404c0007400302e0802016440785141080d00200a0048401e03202d070145004501540c1c195551040c81e02414602e81198180781c280c0c1c0ac007106240d441c4e4007108014010a0460300003001c40003c0201c1c48070101d240c40c0468014044580c0c4a51145c042c03602c680e010310165240d4011601003940c0309510a03a01e11a540c64148682c40c0d0015142a070b14544400000b4030207000043c0203000d005d0348004440c04e0b540d404150898540c010010740007900c1c2e0b905503 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 547193552 1250 547192302 547192307
    0x230105250806040b1c052b03050912031f0801050705040b030403051c0204210c06050a020c1804140106120f1514090c0105072109080a0c06030f0506010e01 68
    0xc2c0c002102030800f04c0c04082840004008220044c1c10f2114000d00c10540d105200f1304118100d2203001c0401202800802c80b07003903908a4195424070802d150f100d00112302c08040802452030f444080c0c0401e16200e00b030014051450685140d589032000740c00d60b07800b2800c000d040c42070320b01032003481e2107452905181608007141a04010000d0701400800d0101d13000411100821425001005100603034481c24106a440f043d00303804601c260040000c01940c0c00107100d0900c0c10156a00c604113540c4038009060b007245002c80400c0c91603045154070b02208002501c008141c0d010358450f00800c0d01e17012200030482e0803128180700f04001940b0302e01c1c01c98046035000e5030008001c0c1c025001c0d4100000c0f604481c2046d654507500075990fa441c8042003051504081c03100320384205003481d141c1d240a2072030700d40030348081c0141565141103289030122490036002e14040c5000b0880001034401803442410b00c810460064401d20300800d0030000a180b240f0000d10850b4170882058480800f07039000351004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 547194802 1250 547193552 547193567
    0x617060f100801090b0610020307030e0103050a0f140a0e0303070e011b05011a0a0506040612020f0405090118060e040203060403030c0e0415030c0e0c0f03040f23010525 74
    0x24000400c00714001060020007070007103001603030150300c4441d094240401406186c03d0540c2c10503013103400c03c0c040200000c0e440614445070060901c0c2c0480d1503294a403810740180503d613010000c0034500481144103100400805100b844501c508016465000c00e000d41c5a00c01251400300064031101c10381010740c021030440801e10312029007409010800d81c0c44d1821100610100c4045111080c14001103143c00d2034288043c1805442250616140101c081c104405060809080f80d4002c540b15010513028400e80d0000c2c4402003805405581d07500480420440e0700b03003131450890500401044a000c01075200f03000c0c6501400030030150381d503038800b00c000f040310a6847c000c200e03180034170780002d98441c018400114030600003804103518502e04403031032003900c2d40000da0444844013007101140440b4180e0341ea491404103015902da80c1c4d0320f001d5000c1100312400034514012020301000400391502e20a1070798800c0e100070401078481404118402e2000400c0e038581280341c002e0301303070503602c200075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 547196052 1250 547194802 547194811
    0x504060507030537090b0f0703150e0a09061b080114011409040608390a0312020709020409090b060a030b0a02070203010b06040303111015150c0c0b0d0617060f 70
    0x1c44120340c044035103c0405481140170700355035240f0703094148007081d8414516580c00c01d6150034200711a1040310a4840c3c105910301c100e40500b0300703420010741002c22640100031500c0e4095410410f0744144008a8881001c90100400103155100081540003c0d20078141ca4058161104024800d0300940c080f00c42e4030020015820a0311210000365001d0b0400c10f00d0074070510717149412008080d864548440500341546a80e00100d101c0445c0260384690036540705498000e1036003c4010302c144000c0e403a00003e0b60281c05520302c0081c1c0003440031540d41c849001148250161106604c4070340800068401502001c0e01280b0040302241c151a40b41c1e0080c00034910160010864a0070807000620940091703000f500450f40b0000a805224014042009481c40f03101003003005000d030403003070b40c0c40300050b000f5180742240a591a10015000380000c511081d800101018626110034200032203800c40390714400240d0238084041040e00452803034640c140c40c9400100015607400c040b1440071174004c1c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 547197302 1250 547196052 547196131
    0x90b1308071b0501030f0615050318030a031a37090501030f050d0216090c0e060a0f09050105040e0a0b010c02030607031a180f09010b030307050105040605070305 71
    0x11a100000303080e0306080d8244560b02288849180c50f140003d41610a0300c2d09003038005140500030300512900311000040c03041c0924000382c0760340e0742e19940c100381040c448850540c0d10000c10480c01540d41504800508001000c69241021059003808600d40c0c50030155030a68840440d1001c00b054601c00c0040401d2080550012950340c64010318201c0d2001e81007960590741c0d4600784003d22070308211041d0b407000e4900c001e19107a995020401a000c03058011040420344440c031004040784201e911403030015006152541d6201545c4020300b014190038142404120720f008002040e41c0210140c40071180c624805808a64a134400c01c5d0050a05111041c148050b14940f140540c9040100b030f8440d010f240c80025010300b02800076030400c8001908548079184d02902906512142c0c4582c6400001d402c01031741040c0c0b25583d0300c81c05422400c0f401600b40c071002c9040800d00c0310540019006a0113104108603e840311326003201a80c408a0b0000125807041300d54a203c1680f40400c49903031942c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 547198552 1250 547197302 547197307
    0xf08180106050406030605100e0f011401051905220f050d050a05030a202a01030e030c2a0a0b0a0201021201090212070c020a050d030509060c030a080a090b1308 70
    0x5000203004c81300c042d002992959520b10410901782041107440010348004000c01140345084000807240c82c07070501511074100030801d4280216400380082c0c410007a4900e170a544d061507071a500602d40d4104d000c40000c1c0c9030b91001e2656869004000a0065514400c84207030102e0405003484000a5408000c4030284a40380c80700c0040b070300900241c102c41001d07a986241404130700190100e003859000c00400350b50031100c40700444a003140d4040b20b4025400511081c154541d4005900820514420f400140000a00541c50303050106485610b59400c8000c0d1030006070011088002050944200c0d400c00d54205082c042c8004160180044402c00c3c4009458141040403080d00d41c0400e82c084010550085446542200f0b080c030040d52100d61454584501201900040c8504102d07100f030302d004510586040c0c0030301d4482c41c00c55164000c0501015a1030643e05070140e601c0e4000720300040042c04640104020281c10b01030752440d150003c4440605840b12040145140b0026100b1039125208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 547199802 1250 547198552 547198559
    0x3010e090c0a0e150d120503181504020103090213050a0c11060405100504051c0221090a171e0c090f0f0403050d09020d0c0306050c0c030418020f07050105060109060f08180106 77
    0x2e1b401d410310042c1c0e640b16202d040070b490101c101c84101001c404950400f0003005082100010fa05a01c00d0702484c0c040b48454680c00803d643c00c030030903100e1101c0c80c240410071502200540121054500e50740e12084181c124081468440c401510000c005400034618030356440c5083d04160740080c000d070b05071408004050098801c2608080c0c05101581100f40600c40128403170007404412443d80608928000300c03200051421801070095902010024003440c0300d00404000c14846c81a410042115541144808568404c200a00c0030300c5004182c00041c1d1050041c0c05150003851200801225902e840d502660160000a904103402d640d50020001507925281030801903402520b0300e210490450a1110a4030001458030f04c0c694020000080a40000411503044078403030320307280c40d00303131010280b2002130301c14210340c0c2c0000c0c3c202080c40018482c3c1035004500035002600d481406555405050781c42801407035140300450324a000052905058008101d48903440c0c00000900300d88 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 547201052 1250 547199802 547199813
    0xe060f0d050601030203010c080c0d0c050c01061d1b030403030c2129030a030509030a06060f090c0224150423061801031509050303010e090c0a0e150d 66
    0x3004001920280c0c0a0380040055040a10400b00200100d1034400c0403803601c4a03203204941324403420800150b944448100a02d1301c9181a16600c0140703400034090b140c0d07180a8074000f207800320f03500ca8918000303030301040079034407403854100e020003c141c62241542e0b00d81c5c41c1540100030a242110070301c280f1500e8083d07038030442c2c000341c61824529200054110300355008130014464415a038840000708030081240b42c0d41c0060042c5507280d00d480c01c50340d03410501c800700e410b19248503130081029003003140200d0362000c100820800d030368441404112070040745404a0b0f65800c5010a000209840310406c0000004200200e5000c42c20f00c200d40c810940d00400308003200c000b0b07080c200030141c410410406030350985200720380100c1e048a011002c403001807541c4043c0c92041c40020300c5c0a40086200c2031a6070907030481c010140e0808192074a030760392511001a490421641c0141031301920890503694a0582e0000040e2404403244000329030740c0d03a190104415440c14407a074450840906440000d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 547202302 1250 547201052 547201069
    0x90c04050f071e270506030406230103021804081603090618260f03040e0a0c0305040b1603020d0f1b0206010e130f080d0518070605040e060f 62
    0x49a0206030700307003450941d10003001d0548090311000d800082d01900d40d81594018440324081e04051549000440441a044000c840036071250b90032850100c1000240072941d800200d80c050030701000c4040d002c1030b01203845c0f10602401700950100d0300e41c19031622040c185003d035900c144981051403500c180c100b16507040b0815035404400103404180140b0105501140d4038502f4030383c080c0400c405600300b50300b20140001c040760100d4041d180501d0001c00c20000c1143d02c00a0403000d0503a40d0305c545031500302500311021030f182c501150420030008807a51191140c50301c9a60414011100b50300e5191070b110f4100041d00b030b004101902400040001d5250344a4105030741202400010150700680ca103401850024002c40c06641103180104400300318a10300b80ea1204e845880d50f000d98400f031a081d5040c1d03540e0708000d45030074004500d22007076160030f6009600511308001d000399490f0142d00700079943c5c1103900440000401c01d0008000e2980c9548455410140013020404107000d06004680f440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 547203552 1250 547202302 547202311
    0x90f1a210a0b0301140a1a130609050c0a021b01021e03040e0c09030307030e061201080d08090106080703060b040207080708032409160306030501110c01060b0403030c0209090c0405 79
    0x391114800d018008a0710311507002d07109400d400034401c0c148a0b29141e0755611004169280d00c0f81c42d0b81d501407403041c2000903d00c10401c02048144020b4420a101c4003c1c09140100a01ca601cac10307000c00c10200300c40040d105680034950003450580c2d403004003e40022034000710345065100300b122004407100329004014003d0716810007140c0b20361401d90010210740700608006680081040ba19506413000300444c1d0482e5014140048c94410794004911180b0889022400c400d51032130010601080110b05513842103040d654441445d2100700c2c00908075000c0384241c2d821035202c0d80e010800111a50001056250000d000509111458881d0041a440b4002c100d51403c00081041038440119600d840f00040f90000a0211b91055021603441040a440300e052440c1c8450040c00c590300c41d0b0000e00113154030000a004070402460180c400707130449803040c8025400c00b41e011a41c1c1c2c070180141c2d0300b00d03030705030781c41c40074000c004c2e000d00c900c000d00a8201e007014003446100c2c42142d184c0d405154040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 547204802 1250 547203552 547203607
    0xb13112103041706160806100903050d0c03030b030f06150102120703090609060801081b030118060608100e15040201050c010524030118060c03020405030f07060807090f1a 75
    0x502400c800c2240c10310364000d1804940d405240500103607540e0098030301343c0c400000d648e80c034a00080303460250b0f0004a0b41c4c0c001003162055074612403880c0e62042c2600c085600c00e480601010303c5000400d6100c0742444032101103540080001001100d01105020007440b041c010740f17480b11804041d400032540542002d0b0081000c5100800c01583d2102640f00281003520308407815505000071184c607032055400f407002155009a48031055a029404102e0341008039503507070f901110500e0f1043c007030041c0b48180d04ea41d01920a400e8060360840c040d80301e100c071424000d000089091060810803540c060010781c1085410b022120035102c0c03d10a5a005490703200b00802032944200520303603a0302889042c180a40d04140f2030303e12402172100400f040030342c000400306141c90040400c600038040c59002d541e00d48502c0d41003158800f00441c0d40000d880303945d650b000c01c1d9526940151120421485280d411b601140d0b01004030018200700103426a00108401d031a2107075020683d28403c82030a0030300c82 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 547206052 1250 547204802 547204829
    0x1b190305060a02071a0c070b041e05010507080a09080702190b0703121a2409100804020f010c02150a0302040e0f070f140702090a0f05010e040b1311210304 68
    0x34445c0c1034084441840a00200188528140d58070012a0050b007100400c0008170401240401c1400c20940781e1030455440e030a202c209042c05c0c070398013900e02a18030802190f0714002003614400e40f070041c0c400c0c441c1c1110713449192017669405d10100d40506d80d424000d20307402c0c0002203004150b4400600059009980d5020824010042a000c6810044551960444110b140c0420340c4901086401c040b00c035140c80400b40c01c24141c60b80b00c5206002010340d104c190085c20400481c2c0064105000328003d03180c00e10207540100040d11440076006003c5d5002007108419510403058500512800116180242c101680c4501d0482105d60680d81c0c090520307e860b040040040d880400c0c242e50812503e032800300046011030b4860548256a4041c0c020451100000e80194603500f040e4020706003160100101d682d0380408081c123180598044941c160760202003942a01c20400050b1015081510890701c01400d2040050403248026011032180c0b0055100c0d51044041c4050401002c012201c500d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 547207302 1250 547206052 547206067
    0xc0d08070306080607080a0e0c04180b060612010b1c060e011e2607030203071419060801050d02030c09070e0307061d04020f040305010624021b190305060a02 69
    0x1000e07035078180c00c01003d550201080040d65035101d1403858000000c140f001030b41280e41502036080c07000500c081500301c1d041103003a800c400c9007001011605030045480e4040c40e15007004000d154851500340f0340c05003d6450040c00204038510042401c080083c0d10b60700500050700c0708170151642c41e80041078100011004120031485903c4024004a401243c400d10900b44000124060300300019460350484040802015103420413400000d590010b040300c0219503a4001c444001450701c0300540160705001c11003a03498000350074001079605540b19005941e003000300744003180c0c0d84e50030280d81c10f101c0c0701e070302d002240c5500e544070780aa00140ea83d050041800801e25260034910307030102c8100020389d8240361b0003400380b409640384120219009a41c510781c00c503a26009002c0d6400244c1a5460038800261600f03101001075143c0c40c0016641600d20f00340b100070390b280d881080c8c840400b03070150030103101da902e03258540030782091826131b20306011a220f84805242820803500d05d0700d140c4c1d0010b4981d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 547208552 1250 547207302 547207307
    0x3190b0a1103070f030e03091305100b040b0a030527010506040b0105091806031c0f0e01031e4113051203100e0403050901090603050606070b0402060c0d0807 69
    0x44008945091860b8514205194001c00c00008018040d080640d501110155072030103004680b4415801800c10f80804026009000180300a0b500d49402044019000a402b90304100380e0b1308131811440064104142240260301400d001482c4942110050741104c1070011000e1041d82d20302000000021a480c24030705100443c0e2442280f00d0500038140800d4907155240050309254529001250185840c2d10300440d2400b9407403845281402600d08240141c0c95120b00d42030781400441ea00e0210074984000150304036114005001e482e43c856401d8810413032101d8110121300202d51f10000e021111000a1000f01d800c0020014526080814000304440c40305520b0ad410003042a040200c00c141981c580b41c3c0c5d401c102c80d4403100080088009045c03541118504001443d1030382917858079141a01d40140a580580041400b1452800e00400d80324428410f461088201074403c07490b048481e01c50b2440306030018022603000104105100180100b03001c01c002c00b2601e038546203554141580c1c003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 547209802 1250 547208552 547208561
    0x801091509021e03010305280b2a0315130c020c1003090606060807020609011122030203030a1107080a0515180a150f05040503071103190b0a 62
    0x15046041859800c1a04a950011400c44500000050382c0c0c03038612218400450b80d403a41064025000300002042c040d01040c09944943c02a122030300d806910310351040002c183d00c0c8003400c140240c40000d101015036080455001e47c4030075607070040d280c051032114075940c411140d86980480d240800042c500300490041521001c0300c60a110351900c03003400940e641c142600705441004c00c0181c0c05c440c640607901426003590420030a000094607640050a11002501c100c4014460740000506074031041c420f1140246442852500c0c0400c0e1000c105800404040310508510010704e0000041e45c0800c018a50403625407141101c0b01c104c00c1406090044170350292450342c00c180203040020720086456020004d040228540540f5096951400c005078200180428030a415500051181151340f690074854559001c4c006201d000803c00260344044d140107060b40e200344040e1002851802003000200c07c0a003c440340000e13500c2c1c8041000c1086801910002103000901283c034505006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 547211052 1250 547209802 547209809
    0x809010c140105151e0f090c0c0307030507021507030207031203020f040801050105040b03070b0a050715090308040c0824041e08071502090d02040e2a040b01090503031803010216080a0801 82
    0x31750740c40d00314240045400150000141c501c40e40d0442d0000303111454140603142e01d2640b200446e40c803484c8a1401810951080506920448038003508160313400301d000c101d4041c540d05901400341580345548810402005103016000e040e002c0c0000390032080703102c01410007000070900208055142405110480b4060300d0045d00036089202c0610017410002d00b210741103241450710546c1d851880c2055200d9481320620410441e00742107040050603408048540201e0060704240180d07030351081d00c80d6079072040062321112108130710141c035507881d1204030095006000d04040305d0403202c020321031820000d03c0c0c00c0494540b98041145000e11515500d440440f40303064000714508a507220029548001d0048000d226946503c500c48401c0070034803004003841007203c00384a00032106002400282415183d5502891906141c2e032120340c42840c4050484134040e01845c98031a01003001c944004d5124905605590204100c0c3c0c000408020219942401100b519464a0220000800e0101c0690 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 547212302 1250 547211052 547211089
    0x919050f0a0614090a24090906060c08090604030506070f020d020d051828170102030f070c0f0813030b1803160c03020904050a02120a0809010c14010515 67
    0xc5041c0051600b051820891110045043c2c1c3c4500d40140000e10258240d04503803400680803481040c48141d80090080b4410240c071201011525484000100c400c00e1007000001031700c4070f9041b004149481c000703104c2d40d54064003c902d800d03100c1e11841d10b421015150300002032291120003031580d40c10300082000404901c0034250050400800411a00412a58422101089981c034003990386401c401d03070201102200b02d02c0084414a61481c1051043c499040c1010310040c008408440600c200d0748074000e4154480803a8882103021540c4100b10380d0f00320341103890000c000c004508004044c1038454410920030b000c060861801c4241c840e0050020b1400403041c01d48200c440d5804030075581c080000000001e010f0701c5504242105940c3c0da4000b075040301e01501071105001021805825860090310703154005c2d558100750396928445400301808400c0180481c141640c8120154240580900038006160b558503d4103401c40e00305841e000041c0c90f10f445500c51030306112050061801d50712 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 547213552 1250 547212302 547212319
    0x706020d0203120c09041b02060711060c0a0503041a01080109020a061106010509090705120102040504060609140f0a05041b020f07050d15020708070503071a0115080c0919050f 77
    0x10000b407046100544074544004d00401c2c03c3c00d00c0d407141c1d406021001504c50b52400140348044002e5290603003074944800080d200851005815000100b59010301010b040e05c03883c043c0400c10455058001801c1101c00e440011505854015204501030280200c040005880c04081c13040200d1f59000d07070f00c40310601a480d40e4400307840070041195411110142c504ac1020396601c04030b04e0030a0455080103521100500d000c80c40307024158080c01c25907505403400c11003903482d5082500d8031005803140d1080c01131005071208060130294542011120050030002c1d40c5512400000c3c103403103a07603081c0c10050a00c14101c0d41c2069040012154640094016241990a040208800c0c402100c0080c00c0b00c000d01a000c0c1031030810f54110790f425600090416190440d41c0742c01a2640e101c0c3c501919072032640980c007210403590400842c102ca03802e000114940e0b224505c1540d80c0e02c0000c04d10030480340c007401201c059450300001a088440c0f10608482040e0504080104800311403851a0061804 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 547214802 1250 547213552 547213567
    0x240a0c02060f0408040f0308030109150b1b010605040903030e070b030105100804170a050705060f161b2901080339100b0907020c0604090911120706020d0203 69
    0x10401c0ca40040030320700510015a10760030500550720441d40b19214050124000005115aa401550684240b008280040c075045032002c6540f0040c0d00803200d03074000400c1150030100030b04840700003c00e119400800d040eaa108001001c07109118826404a03407103d510100d10a4284824000342a1b40d104660071941003202107440548030f01e034058140320010300031906101aa40c1c10b00b4607040f0920103d0340d986140c050041a6800404088455200d1003011884000001c1c580d28820b00e81b01c00d815010400281e02100d031180001c0c035041100070200040b41c040303000215200c640c2e044400340f00540415407201c2103a4503005901801f403a0b08184440c1000104171000b18840d03011903aa0002e0010100c0013910101001c0d40001920b845000c2525000581c103400602041d0382c1110941c2056480d6003040e40c40708241041c0e15484a000c03c802e22011040d80d025090040c042c0816400315080580868040b600020320074503170381c3c0400c000308802e43c4d0421080510541e144061400c0c41c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 547216052 1250 547214802 547214807
    0x7050109180e12191e0c0507030807110108070c0206030a02070305090a0306020414060301030b040f0203030408150a0516091a070813030203010b12031603031803030e0d03023108240a0c 81
    0x75400c5c1803400c004201c903440040c450304009a20186420422a5172360704402d140c0003800c50200a00d65010400210000c1c039414010310032100803d4000c2c00300c510b19599009104002e41c0071b80030031401c1c0309090002d4100c4c0c0d100e80030900042c5100310001a915401c001c40c074480c4080f80d00c05148541130410050001910b0400c2c86900554481258010b0030440e100103415406250041102c0384544076620a03c081c500003050302507001150204030a131140e543d00300b02540350303007994070219a6041d0208650114888210700103424810382504100c10f0b0b40d98000c45034803102500141461403002401546001c3c42007000394402203c45c21025003600c0d019544034000e041c5500c010402c000c1c03440d81814020340040c6141281d9210f0301e5000002803401600030051502901000c2c031a40c150340104500a100f2a00c159952a888251030100211560356100342d0390f9580801e41ca10410008005008201001f8404a80c585a1401c11550002c40729100801082011441d0070240c2c0030346002e8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 547217302 1250 547216052 547216097
    0x6121a0c04031a040b150f0409052401090c050c1b1203040b031906031208060307030602070f060507030c0e0f0d050a0b010e0903070b0c1b0304060c050f07050109180e1219 75
    0x9064401045100050a110b8240a414180010042410300c1012f04e030080c0c9140c0036044c0c0301c04600c1000070b0b299135070702281e00b40205c00b50348039164410780703040c1c0034240700000081030190014108049002c107102018219003166201e20f01856003c000d01ca010180405030413031200011804011030361550301c0c0c0300488901e81b2800000d02c2444804100c0030b80302071219401958004000790b6485680d440c0007203940d0030000c41550040c0c07034400403e5aa520034000c00340c1c18286951100c03806807400d010400e124107a8181d0a0f444a40d14100c1000100705100c0780d00554050001c10b030156141107044444014000d040f07110b2a04200009030018100b10012030300300000c01c982c1910b581080c80954941011030001000314400441c2c0000c40035440340c188450548188203075501c020840a0031a41c942c2c080c050396002c640805010300c90303103d10001d0000800381c880c0012814003001c03110f0f113050807958075046083c2400000c007400e10300840c004d108040d4400c0d2070000c110300183c0c40d1034039490 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 547218552 1250 547217302 547217329
    0x80a110a150b130b2d2d010c031413090903090e0f010605070602030613090c0501090605030103050604030c240c0e03031306120209030f010f06121a0c04031a040b15 72
    0x4a00b00c1513001608480b412110903658009000004950385c071100200801348201c800a040e103038125000d20705940300350b120180c40c0f89c0c1525904580c440710141000b2036001110309094140c1c0d06080050130403070714055104c0c05400780e20360304209401c100300305840c580300070025400000540010841d03c0d40c400110b400e65a042040103850391640000503401c807680d68002c0340c10504229100d010700c1081048101102d0003602c50800c80e9682e1078050350301c0c6c00309100140c601e41260001401103401012003d6801d846100214000c1c241c0312045007100c1e14400c9400c42d41c036a112403001940d5000b007066043e2140440082d070400c50340542c100102c45450280404201d50003503038a1799105a6010b584041000030241d030500026100040e0080c15102400202503092010010b0241c0e5031004100a40d9008051642c1018106410300309c0d404018004e29030b0040100030010108030420b2112014041c1007840c480349040c00e05022240038405890240c06400001c00d0b01e546e07035505568440e84 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 547219802 1250 547218552 547218589
    0x30a0e0604033c0207060f020a11040e070506070b010302031005040203060a1a040e012405030d030c20010e01110c3a0f020f010504080a110a150b130b 66
    0x41a800428000450074080d041410202c0141d0f5410007554000c161070090700c500f43d940480409606404994400340703040050030b199098040c560302c41c1000c0d000611059150002c803040d00d41d0303c001040a0340d120050a441c800080c0c40180118581484043c00c5414400c006112078181500001d80b941c0d0007800642d0519596140c0e40800e1044101d04481c07500004c000f04904520034034803e0190210b140c03069444d003c1800350410314054031105800b81c402c0940103000038600b203071040d0018441e41000c48140281d01110b100780880100c0346803000c9640000114200d104103102c0e07803d580c0036036540c0302c59410038400001903a500260441c0490680c00701401c8100043c42a441621541c01c001442e0405040482d01c07c03507086914076507410034990271a00344001e1850303100d0880d801030760018081ca0701000108400341c4a040b511407000020401d48040c01d0031b80d5103204900c0b007020100204240c03500003010040c5092000315416001d0f010060152494290000d481c1c801c50580440d030303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 547221052 1250 547219802 547219847
    0x30215010b03041a090a12052104050a0305031b070c030b100b09060a1107060305042102210c0f06062403130c0305010507050405091f03030e01020f01060b030a0e060403 74
    0x415408209854619406c0b03040710101f403c18440041450307200e10120046044800003100342103401e1080940b25a8011014041c800d4159400700c82640c03000e070100341003412214258116030814001070121901c98111409240d1541c540714a090900502d032086000b0075100412120301007000702c075070b0030104a48035a41c450f5036a00550310321a0780720400d08035120f80700b00030800a800d6130000d4043d5024107005110111107528140c540c0445201c03580058200c4034017182201340c40d00c52034002c0c0000042e12410642c05403803140c50050782a04050003070f07200c102440f105040c111144003404000c0140d201a01301c0149031101d9a06c4003034107800c88101e81c044000c0600800000e4031016590110090025040015000345142c00c14040c0a02c00c1c40e0f04004140454100460507104102001006605504c5c5440907650781c00e0714541d09040d0b002d03065104484ac04c0c28860140901a045074550b01d034180385042e90111240d000035940d0540c86801403202080d04083d50000e80c1750280003411 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 547222302 1250 547221052 547221061
    0x1e0309010f0e01060501270e04020a030b1609080a030503040b0a0e07030803150402160b04051c020f01150e0a02070807060203010806090c041803050705010612030215010b03041a 78
    0x90040c6441d80600e14900d20348408072101003019009102150401d98425104a54603003440c11130a01100740c80083c0d619130f290030013200c446000c0c410f5009000030503044400360b803521080301406007100c080300c0032000015250701c1c0b641c10180702f80103005130743e0040001190341d40e0003824a1002800c05441d801846002400d0700c1c42079000510150b6061094030b4075680e50707107041c00860b0810358802084100e001a502440c0c181807095070f0000400340150f210300d4100303440311089040f0203803040e5018020002d0080c0302582290071803415040329801003d00b0418404e0441c03c40d120450030a41c1125024420880800441000d9420030708101c00113a07561750901e802403c600c95a0801404a80040000181c0940105425110300907000a9500c070040c130a04110855404511140701c00760b58803000c10221303202e04040c20180b0700c2100006121611460f80507101150354104800591000b6550030400d00d07500802c50050440021144c19401c1503501d0510107401c118800e06150900070015 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 547223552 1250 547222302 547222321
    0x60f1b030a0b060403030f020c09220f080406020706120606050415020f0712021e03061f08070305031b06091902030a06050c18010203090310090201020708061e0a021e03 74
    0x2c9001c0080200420f5031143d40e031401806c9581c4940740c600150080b500b800c1c601c2c0c10111185445102020440c01404410300071a00d2002c001c0c076030603500d1055640785d01002600450040002c3c104503002003040c01d203001c100400c5048000ca60361241030802c41c0412480c2c1d0810113440c16210310004074495196260000c82c50204821003d44481c0700700e0b200020342d0300031440304a541c2e60007036684010307aa40c440c6030706003404101060b0350b8059009400080c460107a0108100581c00c0b45004802200c1e56810400d01d820840d8100f92259040000e10305003813904810309040c454a5500500194646540d401c2c0c1c4030b180c0e90340c60f01e03202000c0181e184115030342486040d0040d60701200c104090308042d1540ca400741c1109004021000c400c801e44201580004291101d1000003801404410000c003007000207040c0100d03040741075108400020440c400144040391240a0500b00444280d80480d2000b5590002900b1034000c2841002150301c810081a00c28021945400b41c10340e407501e94600c40d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 547224802 1250 547223552 547223561
    0x13092004030c1505120403270305060f0717060f040f020307030b010207080102040b030a021308030703170a0b01050306011110110711041104120204060314010e060f1b030a 75
    0x180000440001004001c12615648000a99080d16040003142c056010306403004d12500d1560307404480c8180c0050002482030603c150070300380301c0301c0d021703d14210006208040d101503041210700307401041c10451001c03903481d03043d58410950310b403240001500f4032281c00303001006401c4600070751221000218548807070300090044040c103041103540f440d14240060051100358095030060242c00000942c0c0030781402503e064481c0401101d1840d16a43c00600095001030840311140f50602d90000d49043c0910140110764042d031180d20410283c600200a04c0e04000d02020142d03280103900140c03a41c0c00802d995000c00282858a0b0703004d45e00c4441440d10390784041645102e41003042070a0781ca40200050700545200350b515200340d8240d4010001543c80d10700700c00349040c5003840308200d0f1903070032140308070598000390000555903100e883c0e60512074000d00345042907070744410341c15100303650800410340e114015480e821094284144501500a0340f21542101a40041b01180080d07865030300 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 547226052 1250 547224802 547224851
    0xb0a02030c10112d07060b01121a12010b0d0309090506030111040e04050a12110609030c0a030f0e0604060923010e0d05070e130b0708041e03120e1b04021309 69
    0x2485626170f1010310701036004c0c0254216590000b645000a400282e10a0003414440d00c01d0b141d48002c06500c00341440503880440403100c04079900c0340c00e48401034441c00742078000741c3d001e40d0f54201c0c0f030303800c10852006607071011b1301850182c0e140c6584c440d8001200c2c1d0030341c2c045e41c00351101104c060b200c9040140c54401103007806000c40241214001c0c0c1c46800500c10b1240840b03000555240d50703a08101c0c507440380108a001a101d403c00c0d022503002900c955081c020050740c0703080800c00242c1e400046242070308150400004101c20b1102448401155240c2075403075072203610301140d89100840000c05006c05190a02d000d81c0d000d0391004200041400b0f088013070300c510340415844e441c08200c91603014500080960348a804040410240d6104050b0030788540d030090007442c8003d1200040c0e44a111040741c0a400304a031501581d0b10046280c020300228014200051030060300c01c02c08a102c512a0100e994810391040000d44140303050900c445044074120313100015098441101041c1c5071001c0c00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 547227302 1250 547226052 547226137
    0x6040902070305211f140f01020709060e060f04021c050a0b120d03060f08151503010203090d02010501060c0b0c070203030903100c080c0f03041b0b0a02030c1011 71
    0x30600034244d54040350320b034070070041c02c80d000da600d40726112000101443c5000b986500400c290340f242c214140380b04240d12082040c0304403462580c3d990001c038110340c4290000300c445540e96050112034034041d04202e090304011202186003071448000c00102c4c80d20090002001519000001c1030304069500500440401611404403030000510280e15025000c2e5070101191400c04040740c40c9181d4643d2200703075140c3e030b0020800b4807040d48031a0000d1100400d0090b0451211003100d81646003030002d1406a0f10b25001403032030088140020342980d1050300668104080000d00c0c01c0840c14181006030400c1350302452503501d41c0c017400464210b108031005580c1501c5007030211840401a64050305a9030026a9814040e44841c40d200b5003502c91083c1e01444080705101090100d0a0440b032485031030340c00300e0b082c039400c3c1e51031815000710b0f000005030802507000480c56985156080c403c131500c14000032000c200d10340040046003403500034650462080d441c005044a001006103404e41c141d0321618 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 547228552 1250 547227302 547227337
    0x110c10030e0d02070911030106140309160305060702120c1e0a05330106140309070e07091e03051e121315020109021e06090603070810120206040902070305 68
    0x900003c3d5490841e0301c241080a03103031070102c0c0c0d0380079502c0080d01e05840341c0780d03102220591424046a006e0304041e05031503142c0a001204081a404414034400940c0b0030ba02400300313880c040c0000780c00d20040e407003603038111041040200c000040105440808204c1481c1803805414120000752420700300c940001c100c1c1c45072064142c450540c41240c4d00c00710a0303201704010645104410880541400e1250001007408891407015000131100650360054401044500301a542e0302c62400211341a58098040743d0901018400c2408003041e4203d044800404822500d240d65600c90381d44800154000345000320a0384128103000c24014881410aa00e0055807a4a070001c4480e000003030502c64110241032a0000c140514010301980c10002d8006146c50000c811600d0f1140307c130f02ca60440c0a80c0b101c070810980885070340e2900030b54000c0d8416510240c1c103180008440641100c180c10144032954070100080c016560b0304100d07800d0755101c20f000342e15414186000e94a60050214408410008 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 547229802 1250 547228552 547228573
    0x1003020d0f051012050c1c02130e0c04051005040203101503060f06020c0d12021207120e030f120a05070f1a0601030204031502030726070f110c10030e 66
    0x50b04900d0240d0700c00100301400c1aa60898420f04420807100288107402c41c190124240c5030014103403c0000c00c100140550712250390014400143c0d042072600d80640c0d07600b4100030711000300411020440240e03810031550510700c4184488040a214107031146800100080c500f184682500e401403407000f0041c54051610700000d0050035160003851a8a80e60882c00101103100281000b40780c00058515049004951070745d020b01c0e510907603814207601c110741c1e003003110b0303040d0300001c014950007095050800952100000c107440101c8030070781d12030760121303805100004d00410450350350718955001568608090700203441a0003a244083e02c40b91500030a40d0510142100500c62544a01d070b40030703480d607100401901240600c1c0000b6042c0803501924010780074550703005581201460030084116504188c9400d130700b206050b80d03a038118603e0001d01400b01e401010001400d0000c0c1008610b80b04610742c00740e501c00032210041d11605410b052030075814083d5100e50411412441a01c60035600c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 547231052 1250 547229802 547229831
    0x90c040305060c090603070e3601060309030206190603290604110f0d060906380307181a0c24040818031b010314040309051003020d 58
    0x1251106850501070071001400d0041d030b9404580b004000140541c0c115103842508480320f505406186811108448034542c2420310030207074a0034181c01909182c5024200d004500c100300040e40200285420100445c1c00241c01040a992043c40e0444440700250180c843c60f01034042030380080c003000000356030301c00801403546c1c3d0b514034244404640c4640f901e5100c00d000c1150244109524840e4003403041803000d0041100130007024040ca5000b08815488015040490702158018031b8070780b040108500720300344400004400c0780c0c1c0741030701c942c40c0482c88107003120b551000400000c104007074200348092254404a03c000a0004c0002c410164807100c074800305280e01055515040e413082604482000c05400030032480320902501114064450f40e4585881e9041003c10141c0c0d901c02881c0007003580c608101010380d01da10f1001170301c50144010005070484400360b0458800300d40784002c01011030b8210b4402c3d421940700f0b8039450a45000010214000d02030072140d00c0c440c605010700e0902142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 547232302 1250 547231052 547231057
    0x1e040609050d0206070818010e030f070213050402090a02030601120c18050904080409020a021f1a19031e0b16110f0709020f0409020d1d0d050403020f060405090c 71
    0x61040701191400300d000d2400382c2c0d44903c11958a40000c9000000440400480703803000304108800f0004a000c0c401c454280781140c00080c2c0c0350201010100d010419072420220042100d282c0030301c1008542880d401003803002c2002025694442e0b000001318149034851840d4000c0c072003038070030308001a429240c0008c0c000b20501229103032448001101050b1850140d800c1405944e000049a1400e031030403030322030040c0d04004040001d60181c00c0480000340c4c01011b15101d4054622800140c0e040101d0324a4148510404d00034028417545411400c0c0780340800009054039000420300d84083da0090000398441d500742d90040008850b8810b01030074500300ca042c0000907000f5140d040b10000e1903d0707826a14143d46401819581c0f02140400c50107801e41c0c01081d01c51482041a0711b4591034a182200f41c0e400b12040b1002d955592200303080c00000940e00039011062080680000c09100304010224010350001a01c2107110102051250f602e61040314014503000d49100450f1608010316400da4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 547233552 1250 547232302 547232321
    0x30e0d0609020f040e030d0b0301060312030c09090e0a020d050c0628050c0304030f0309120317061f0315080a0506150f0108131403040902070302011103130b1e0406 72
    0x3a030322000c041c820713450b00f0301450300340324080c0000f03608122610b41d0070b4002d0458203d00329010b56882c0404000701c0c16512440d00340c45004d0301c0202c0d00381040b000050030010b1a900908c0440e1902d070340e07200c503000080303282c0b0941c40c0c04940803400443e4070300307040342401e500c0d80c00340c0c1d0301c003c3c000340c81d040070620366660442d90340c0040407004003910080c0003942e880c8181c1a08036540d4004110600001d440455000c0101d03010307181c000042030710b695428000e80c0c1020001c0e400b241d0404c0440342211290781c195070340403c1c15101c600c0c0000b41030007a00c24088a040c0c0c06024146c0b5a0600224901d204006130014a4071500302c546681c400d041071030301d40c0c5065901c40c099464407154042036042c400c0b061a0f05182c180d54590031944ca4400e2805584c80621044810f0040703503920107444142080075001030301d510240181d50b07840d40d00d00a070071030348401d00c1001040e1042c01000702e145140366150040c82c0d00071030754400c0b6607a90700d800b00480c4070000200c11100152000e220a11071940c2c440c9810 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 547234802 1250 547233552 547233559
    0x50a09021c0201090302090a060b0d0f0506010e012c0307060e010210060f0312030b0907020f0d0908070509040218040303020a030b0415171603080d050c0f16030e0d060902 75
    0x140e03042038034441d2019800d10190202e10042c2007000103040c500b000302e40c010031034880001c0c1d203070b20f506984049a00a01d42508510b86542121100c4a45441a40c1c0c002d0000d0900d80342d07001e035490000c5c3c200c800f031140c04081c0d00c259558010480c400b03d42c0d0f076094001c0003419070b0344440e02d51801900d85038266603540d006104142440c00050007612a0406aa0041209038065451640d4009481d84c1d800541020181c6415400140303481d00422540102042e030040c149045131040c3d1745281940c515103100410540c080200003465000c2560400c0c0d400c152915101c40d555400803071420003455020390050ba1105007041305142d0305502900d03052078980d500340030503c58402000f05480c83d4a011420f9809082405c1000b00140060301c02c4600c1d10209540055200500c40207000c40300d43d00598000d10002042c0408101510440d80d100c0c48040b0380758100714021140d00002c1c005e01e00d0300c0030b142c000c141403042414003814000c1e0031150700402d4411600d2003894060080c0900c00310480c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 547236052 1250 547234802 547234819
    0x20111130306060f03173609360a021009050109142d0a0e011a030f070528050d0e0309010e1318030f09120b04081309050a0902 56
    0x108141190503240451b604440850340c441c58005806489a00c000c0549002d1031101d031441c0707016440100c2003803442000000d01c0710760000d1700e0140240c401c0001c000c40440040500306203007040040407460000302e003240c0c0401c02d40102e401c4003454000444c001035840f41094598040081d48020f592007a0741007070f03817100303946ca40da001d84075420410b4500b07007507103d50b00324110307010120404410001c1e400c20b040c0300340030112460080b4440d81c405400104001041c00c005008519800b00c401d8038070003400381550b1851134655043d00850324081e02c044100f02c00010050401c080b15035035640104040c036040d0314130407001200030700f40354440740c1140d0fa11801e0003000510308601200780c410240040c0c6400c10084c1c0400304001104a0019803017003c1d6036a0261083c0312006021140103a0b032007621180d1070319802030ec01800c8404594802044000c910b6942000607001040d15030308560b2140c0010f45035000800f80c8100c0250715009a440c030f41c0b5100401c0381c4465250000c840c00b80c0213803034a64 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 547237302 1250 547236052 547236059
    0x6040b0705070b12100812030708060d140304030b0105060f0319020d02030106030e0606030a121103040e040501050105090f16030906240618080601060e03070e01060306150f020a06020a02011113030606 88
    0x5860787c039148130b00e41c2205400d00000e5860750060440c580d02c01801000c9004540782030f6101800c0d00c049040c1e0501c141c0c00800c0034410050441400d60240c0001c031129401d00c2601c1d002500544001810229a0081d20601456420450b0190394142031a180c040d0345030345c5c548000138004d21303d90345904454400c51011401034200030810702001e80c0c1100740a400034840c410140e415900c4014bc11b00c891200304000945e2090915030240038a21130000456103515020400840c0c4e44003410040d030060000c400c1c4901410060010b41100da01401e001c1a00d55080c01d24900078949404280d8a20740c040345401c01102c00047d0800580e02591078556000f4007141d40860805e20034010582c0070740c0040018005203004244205c0d00000090450f41c5c4103854010501c0c41d49001c0e8000c00109840300f005000c643e08a00c142028000546000e180215146900a40d1b444c40b40c2d201a02c603503070005102c89018400c0d00200400010741000e03039601c07040f03540070303e00d126014881651414680f52010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 547238552 1250 547237302 547237319
    0x30c0219031b0b07030f1413090209031c0503010603050402040e10051f120807050f030c0106090c110d0c151e06060c05030403082206180506040506040b0705070b1210 73
    0x9458043c2c00d030b1b0b05c03414000c9160600303440440716112504419401484500804602c102100c1d01a1280050250b20380c1b2040c0c0c2410f00c0c1c80d43c1e8000039030000c10b03410150303000c956018003524111207140c0f5021800d9103035800402c0041200444000883c080c0412483c451003054120302d001d6444850400340a0542041700080701d41c0c54050803410340d90310540c200100300782070701900580f4019801e80e42c07070442c580d42051030741c0d0184c0700001450351110001c100c10002031144200301e40040c03c11610410013908026100c0300300205680502542040c80710900400c071009411503191a9002c21010800c0ca50740300c150381c0c0d4540c04d50a01414040b0100e0024400e08100c048141c0c400e00550805081d42d86076130140d04441c80100c07091960700e40c0940c2c1025828041c3d00100282d84070b100c0302c0c0902000c00b66850300d8030b402040c020388080008001d651a1034007140d00316a515000b0903211459850510305103001540440c13580e503404544848044501030030940038622420201c1c0070283d940804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 547239802 1250 547238552 547238557
    0x50102061b0403140d09051909021c2903012d0b031603021903020a0608090307020d0f030201050a1104091a0a060302190807020307020108060d0b0a020d0c030513030c0219031b0b 78
    0x2901c290242c00c00013041001c907150040e000c40d01c41844101d205080000c400bc0485504090b0780b1071011712074680340c401d21100e070062101218240c0007801003000540c40400d100c54644201c49062010150580704007080f907001103e4244000c3c00d90710080542c280e1016004ce01c2d0100b68816266008200c0d01c1011a004040446e5806806003080ca454030300143c440e604020412006030008200703420050380d420201c200254841d1f540d004065142382402800c540c0004d0404541914208440c0c0d00b9005400c10b0300c01b11003004d4004500000c868103120b0303042c03044000c6075801000005010074200d40540160070030020294440c000300c20034080403104101c0588030344c0c4c00358004000301005548552822640701d50040c116580344401381d511071003007449c212801c100c803c1d80864904214056030040309448041850b090000c0e04080848007402105040000c3c00d004030501f8030360464461080500110103041c240c88116540ca0400100d0303c00300074000c20601441305c00201350010003409 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 547241052 1250 547239802 547239829
    0xc090e0c01110c060a05070605070c11010507051506030a0c08060703140c161103030c0d030c0216090905010612060e01061a030a0b0a12050109021009050102061b0403140d0905 77
    0x404044090b8000d21510758171404150040040401c20200800c1590080c0c5020341c0d0b090780c0d800c818941904007038403d15a5066200d0401500300700280103d100040d10450301011715407050b485131030380741c0001e2030448600d0004141150061001655290108070240300f698141c4040c0400c2040840086c24030b0320413030b1651250314040c0440a400308040b0380410b42d032486032042c03028400c00000068507580100300441c41c030340c0c84820561406940b40c003a46c02e4054960004002c0d1852003141c05000003424040c1020042d0703180a08000e00409400400c01041c1b11000c0341c00e8009541030000184c104007101074907560800b40001034450051004081c4601a01c80c1c03282151a840d54500182c840001440c0e8007003a90f100101d120000414484001ca104100002c3c0003c010310520817040315201e0040184907190b03004008598020516540c444a0b41e01c450009604000c142881c5004d030340c10140402500c3e000d007004407480001c0b14803100005071903804590360f8400c10081c50052540303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 547242302 1250 547241052 547241087
    0xd02070605030112060902060708280c0602090d0606080a0b011d22020a0b0717030606070b09011b050307120506060a050a091a091c03081308070c090e0c01 68
    0x100402c040c450340d50242001500ca40000b044501e40ca8000030030076081030303c02b50b840031400168040720300030544030b81c401c001e40d03158503614000341c90303c002c5d10200032000090102900017803110100e6556011000e289076202008022a54603802c4481c1d545100700800c40380403800c02d002140c401100c450300c0d130107031100c05000d018542c0e5a407440f888603c60790310b880d100030040d000034a005a0343da01203035029248540040340c40f00000c2c03d21030441007004849030320070a010018400240c075a001140c458a41000300700b81d0a4036468810380c010000006210104800303401aa501139502000950092010f43c0d0360305500345000c00e40c602103481c26110181d00c46000c00c20604140c3c052405840801c0c1d4508088074142c0c0d80701c2021140400c44c0c3c0303540d801c0e600002169a400d04e8800d50b5007124861141400114181c295405042c0106c00344c050762428121144910800c212201140e0246601c0401c2c41120795a4ec107400010303000c44004070815000724803c1074a654459080f0000003807141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 547243552 1250 547242302 547242307
    0x221d0c0c1216050d030e010605061c0506030f010c050d0b040b0d150e070f0302090108190b06040f0c0207090e0a02010c1101230304020109271a0315090d02070605 71
    0x41d0400591114081c41c1800d0b10903012400410418424905421a50f84011aa580c107582d00d590859140d9002580301e803034203001c0070400711061241ea0f10220561000000e5079211900060303d4555441c15045841d0f08000d00055001e82c032001074640074812030410310071081e02c54100020360360780a584903000004800300d14042104040304245404081e0000640a0214481c560802000360001c3c040709802d0101041142805c0e80300364010700000e4003a000510411703200c0401c030327408583c018164100d0540401c0903681c0b541d0128101040c00c8008000c000c0e40ca044c0652240c11038850258082d01d808112a1141c80200710450702c81d505030748058810300c05545440e11004c01c2c510b0716040060341c3c07155009a600b101c196540300c1d203894000c10b459240a100051001c000d6400031451200168500070008a05100b8240200c0512101060707007100a0308803981ca10034213011503814811b6410003000710000c04a81400340d42481c0030303034003440342299060b0b0fa1250b0350300c141c41c00500c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 547244802 1250 547243552 547243573
    0x40e0309091f0e160e03061f051c0b090303011401050304050c060f22150518061605010501050d020a050114190801051c050c0402221d0c0c 61
    0x20154680d44025009036141d503426203905060041590303034103c05810300c581001c1c810b10198201d07880c0e000e00c2e03140ca000b403040d0195902081d143c1102130401d0744945800c070b81c54503c5507802d44202d4042c0402418401c03010410005450301100c10400548000c100c040200f0080c00b004000c070703410307a041c0f00c0310100c0b40703441040112240d5000410542d01e502030b81104101c26614080240f03100c04400030000d444141c0340e494144070308400305001e04a070403103207010090407880c407120108034000c07800d1480c3c6940310445d1144900c009640c030351f9030003000000c081031001031110301084101c0c0100002c0129a072a1b00a10090060200004c2d40c840d403041c10401456110ba0031211003000644009801c0201480950b00b814400c0640c42010400d6403005100c5801d00c68020212004446e004c0b59941c000d540707402d601c41140c248458003a40c1c001a1820614070301807483d010343c04407a104102280e030303500001d50003440c5580900c60380401403000310303907442c0088003941d100c0840800505400042c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 547246052 1250 547244802 547244809
    0x21091b0609040501140310090209010614192a02090423100c0e01170705030c07050f0c0f12100504020d0f0b07120e06012309071805040e0309 62
    0x991158103a000c0030070894404151600c3c0a503030700800907102c051040916010806007004042400c6202c810b14000380c0e00096035940110a044500f1400c00300f0101c124684c40c400385100e990808034003100c80400d90140a41c0c0204103e036001c013045c43e5032200c8401c0c44c0c00d80302c016001c40c0010703511164031404123020074004154103850300300b41c031500d642e00c0c1d0058221038205101a10450034280d0380d05a56201c0d1031300144030400c184400d2819020b403546411300b1f03201045010340280304200005c80010a44441041103e6001d0382040403140350100100d0380079662807070001c40d1401444100c85c070f034910341805401c4844bc440400083d000d2054141d107108000c20004105a1307115191041c02c0700031031034005017111902d00a01883da09494804005810b6550800064100c14581350703442c0c002045c045816410f541c4132000001c0d0801451501ca00300c0301405000961100000c2c0034000c01e07030f8100003c0540c45075030f0364485200303980d60810001160500382e004509604100101c2c0c540c1d1030f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 547247302 1250 547246052 547246093
    0x121c030f141602150a2405011b11030a060509121c090303110403080a03110c03070f0203070801050c04150203041404020d150b180a1505030711030f2109 67
    0x40940304958070b011180f4940d04e010301c000d030789040b08540d580c40480702c49a0400c01d24100c40c011010610f81c41450040000c000c018500f820152841400300f40302e080182103651060754100003403c6800020031401c000004045c1900c0c80c40302486105c41c40b114140c2c03c0d90544da0340c80d80d84624800000304415090000e0300e1202411020035136985d00252102c2d80c65000740c03000d507003e4030300103444419000024046800c044031a0220110900c112100440008100d4079195070002801c5038141c200e102007442d03c10980c220045a509020400c000a0368080c0944216040414802012445100301303030303200d12a5004603034070130851600500ca14182600280b00e0600c90050009411080f407041c00301c8480150011002c60300001642508900c1d0560f00d5415104120781c002813451408040f0750485202d2500d217002d01c46c010000500701400744802d200c0801e03000054030303951740c030207034140b1030541c45410082140105145c80e00e0f52404a2403010744140c1e1040002c1c03103450b031804c02000000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 547248552 1250 547247302 547247341
    0x5030715110a120f030b0a0303201b0402070606080a050d0f18230d0b0106031a060a0c1a040506160c240e15100509040b04030c02121c030f14 62
    0x1500d40383c1c014880c7d00d58031000d10085009954609406011001c000c18103d1503d044090b154090108501d511404e2400d2006100086a006a6900c40c619200000c0d0a040d409440d281c041d408001e024080c0c0800c04504200e515903901030b071492680c1c81078546220440321980d071085210420701c80c1a00929060301080c0040065051210141c8000744420100d20022519082c2c2c0380010064907825001d04c0d44894400000286007100c0403010400c180100721035a0f0802402c41d001d45d05021100b86049512a034030007484500d8507044c1801c2e0303612941a600401c1072101014400140c512440340c1102c280da000d094010b400c1600900c6103400503849040b2101d050ba180300d10038107184200800d0b0502094000748011524180d515490303424201d070f002e03a0045941404100026060061940d8855414205155404824000310302c1c02a0350507206800c0f40f094202c001c4000c0040202c0a6407503c090b0350130703c04415120000025221020318207200d08281c00c0c007081007101c207114200c008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 547249802 1250 547248552 547248557
    0x50d0506120d090e090304141504120b1e0f060f0a17070905060301060810020a051201030302011407034113060f0218040209040605030715110a120f 65
    0x50020094181806148402d010a00d41c030400c020820a90585640c0900c1e410003a509051504901107030324110246824815040340e015103024810358810344000d04007006002201408038600103810031400c2c3e45034a080d2800703010b045096180200039501c01d4451050004083c1c80d21000c0c030600c1c6440c901810780c415406200418009100200040c554140400908440e4274204035842226409008503020764103000080c0141c9000081c1d00c10312200540005940d8601081304035058001d028511489000c070000010034903074150088860001d80900d1401b0580703075110154201c0e540c00b00800400c02001005041e0190170085805452199046a010480040c560321540781c00c2100d0000320010101049000d0143c9880307030030b4424490090031031800340048100d6a40c000700a000c24801da0300080c411009490f5070308110000c080c0502200e180a40390305000302c030b040c07003180c0e00d0000940740c0861154011000800282494002200060010f01d49004841110110725840c09 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 547251052 1250 547249802 547249819
    0x170313180b060c070302090f06102d030e012307110312041b120308060f03011808090411070804050d03110a0305040303080702031c020c0a050109060b090c0307050d0506 74
    0x1030644407140100306580000c03004d04411802c610411244c000b000d070901c55443c00d400c08000c1070b611403402d0b0240031a2070741400e01682d140a888880e58003044500c00d4000010b61034000c030615015003001d049900030324001e20500c070100d0400c1c1224400102c6254212021101065106002d0841841006a8881640d16100d440c1d0964403100178141c40490b210040d4074049080c0c4403da00010016048134201c020b121065510000c00320f610140c600c0e48110b000d584880415502503110a96094600045410211140c10011f40c0c540100c3e01a0b40038a0034803c40c0c40016502004441e4000d81c0604407500305800c110a12010f02040c860480034041a0124038403981c10070407810040501c2a80c0302da542c0d50071403a004029807c040c2c141030940d4410f0000c80b0004090031610000c15a41070b00058039a50b41c42079451404140c103170050040d528015400e0240010380c0c00c0402e00d40d406544060068854a100302d1451100320348800008000303101220003446503400040d0416001010f000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 547252302 1250 547251052 547251071
    0x2a2a0d0b1e1006090602060907050118090915110403080f0d02130803190e0f191703031b070b180c090c130504050c0403030c15020307050417031318 65
    0x490504054504402c10100840d0411019922602010240502e84050b20f01818462040b0b13075270700158052181030110a0a16207419442035a00c1001081c00c41428801d01c0e80e942844e40da82d050900110314032500701b200d10f07021540d08400b03c1d02101d51000505150a1002603041207d800642d1071414841e02003104140700082c5202c1c400150000030055a981d025510800103078800d01e030750603001d1241048544170203640c0c94180943c94041a41c4a08440d40010340b076103c405415001a000c20b0140303010041504c4000020310b100d100115000c0000c1c00e801c10b81d003111380c00344c00d0b00280560110000100754000000e640c040e80d880076801c031160440040000341040f00125211a0f40800100f07151401c026820082801007600b44c0e010003040c105000381e0141d0340300714000a024410803511410801810542c020070655000341c00310b449051500005050364010b11035107000c900549040f841c01000401100e02c0203180030041d649031490802c1e403138200d01c0f9002c07200e000c40796190242d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 547253552 1250 547252302 547252351
    0x1c020c121b01150e0c07151b1106040b06060708040306060308070318080309120a171209030a021b0409060606032316052a2a0d0b 57
    0x142280480007000e40d00d10900d0050160860318194425401030000d00000c02041c81c0d00c3c40341c0c9401850415000307070784038181c5c01c0c2960040c50b442d80010005103000c404030a1114010301c90034481c0d91942c0c4940048825602e001d0b5550b005881c0607080031200d001251162034550020070a140c4118a410f0a1590742d441e40011142c540d40203541080c2c0000c0c1000c105540b00f00703480b203080d4038401002d2a07141400c44180c1d482c0180f048603070007803544a0040044c810304012040c91950301c900d072520b1109121b100c01e1001d402508a4007000c920b00d0011644051000c070030b032500b4026607801012140c8a0144141100d10b0034542c41e500a40d8402d000d03c041116801194003421035130b1008640c0200071503010441041c0b11a244c060441494144510f0840e0028030300a1103842e841c180392140b8600740c840d201d501e80d50009010301d00d400c0044125401000c0307844041180303800302001c400300f961403043e5440c030104529182d011201c81d119000003440740300e85c0c0390003801102580f02e40d01d82c01c0d00318 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 547254802 1250 547253552 547253557
    0x150409151104090513030819090501052a0414010f0309060f0b0a060509010903080c03090d0308070f0c1e080405100c020a0501020a0f060903021f02030f0108031c020c12 74
    0x5141e076281c00054107215940040c011190016981c488400d4040001e0724000c3c1019005000c0341800c0201c102c80404034000c1e034101ea22241c1d0060000c1043c0d0410255418514600103a03001c141c0458510104011a1304406c0d20f0489000c40020b1900001c400c004444000d80450140181681d48200070041741491003001d0b6049000c1078000780310711540c1b0402c465080160701032810400c04004001a50340d114400404907135009025681ba0300c43c0c1030b045402e5006a5014682241841004a081c5544611118001c0202d070700e80c070a80c18001e8104850f044158100640000503c14442039540c0080515240050080e82c0041c2041d80f2480044c00c0d0b402c1c549800800240c1c82280300d42545418a88000184800d0000344040019903603450509562440c01402013640c42004030207041c003d0022040034002228101205240e0300054002500295140242e40c0c0d04080003127200c18000044824503842a002c0784e030360594030500800032f9030003c001d03005103010300c5050390301c0304245001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 547256052 1250 547254802 547254821
    0x3070b0429040c0e07021b03010e0d0203040608090a020f0f0111010c020c09010e2509030c06050d0e01060806130f080705031b010504030509040b03010b13050709080615040915 77
    0x84854507802c090a2018940f16650000e0450942c96018080c4541c0c001038100100c0700c001d8808003205108400003401890396400820560203110609659103602000400c1070b01c01c20b480c0d11015443d02024242e65000058000b500110a070f103c0008074900344c00b80c400c0600d414904542064641d0b2600c3d408c0d54407280030a009030384006296203144c07500500b183c0c054001d80100200d14604841e06070002e01c42403400e2603016450306c0b5285903151003076104001440d0400c48021007250f844000500a501c40003840420f1450000841c58032501030150a08640c44027005001c1034031249109982500c0e110801c456201c82402c03a98006029400500111405540a19140e0310081458a0703c0101c0107100f80569142c002080002034110303050715007000d41601c00080e004040d030701090041ca00c071a2481e6001028000c5030030032300081d801c441d1050307509940380030000343c1c1c91030a079503109030a9422862505110442601b2420103900182c0300b18060420341a0315188038a200007101d80400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 547257302 1250 547256052 547256123
    0x7140d0509030309040b061c0c022a01230a0801031e0f170c010e0102030402030613080409150e10031106120c0d020405060309010603060516080a05100b12060a05010e0303070b04 78
    0xd015628140d0103200c2180001c0000603400c40d600e250010bc014111000c0c1040d505001e0b100c2641040d03654241070f80007281050030748081c8d03a01c101850261080900b4807044843c21544108000900c40f002207400f110766000c80c0140005100c0c0c1c1d1071070001596840d000184072024405420a09024094038005541280005070707a420580181420004005d245590003a260108a40003c41400444046802e400c1c8006540000c0403402c8101c014a60311942c218007001050000d041c02850b09403049038401c4c0e01d03400840e00c819060145a0180710138428003035801030002040d00054030014444c40a04800040c0f41584400020b0750300d0300142d81c0d00d0b006030764600092041042c83c3c810590051070300f010043c01c042c10044000c1455030000c0c1208401e0ba1a4000b04031011030741d004060203820301c1a030a5459003848003265100c1c0d1002c444c1c8a1041403459000551540203100d41600c00f040a40034614001c10f940f03a468070341d9006401240c01c85901c0c0c80c0080d01d0340e091086880326a9490 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 547258552 1250 547257302 547257311
    0xb0d0b01091a010206070c03030204031a0a0f1a010e0607060908030118060308090409061401150e04020c190318030c140118090e1207140d0509030309040b061c 70
    0x1403036000b02c03800d5800700e00d041d101d080a1030240baa00051401d5024010b803500300940c0c0c80310b1030210064001d0742d100514007448900c908420380c0603600d01521502c02da1004101100f00e0594190645080c0364500c080003488140c024202c1d40721b1100c4a084440c05400755181076040da544a045030030059040c0c46042c004001440038140100300a140649003117011f0016604540b0707003080600c04c0205103840b4a90780c242c01001c10049810540010307415020140c02c41da5074100150300035101e03104410010f910495001514a041c1c030035244004410b000804031005001c0c42440050740d40d240650034040a080107043c50042e940e1903001842c80b440ba01c455561405920300103001402050070b06018403140c000301481030080300343c022034000c504041180007100d41010705088100c0b00c0e074409031400050760418002c0020940030005200422035421610102c82224203005203820142c1c0f50f00708100d242d81c0751603d50070407004004000d1110f03192604810021a42104076209002c406494 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 547259802 1250 547258552 547258559
    0xe0615040b161202060606090603090a0203071806050a031a04080409020403060209010306060c02010c0b1b030a02090111031201090f060b070302060a060b090a0e07110601031437060b0d0b01 83
    0x3c151050100c0b490360000300124100300000500314040c82c40c2d090b004007004000103040040030050250825000390a90300d4407a140d01030542d640d042011070000c414100040041c043c100090008222600240c003642240c00328107800d0325840010b4000e4500a13014400424401600d200400c020b5103e400010790b245010030002d01500d40300c2c0e10001c240024902d0a0700135076000240704500c150f111031988419515651420940480c09008803c2c1a80c080104010101d081c0d0081208140907202d980402401c0090a540ca00c14541d0300140228804010800d00d00c080d04000300a10031500c0100d039003034485003603101e650031207182540142c1c00513003032100148040c031500d0f0150201c8d1082e80d00e02030060340800c210110078415000803100107030008907014481e03030500b04075004841c20781c4e010b56501d00784840040e821110703108040c01411000c40c41a0801c86a000c28910001e20b4000c41d05242c0a07650181c1c001504103865141c4c9a854204255440c4101031800c18880c60a40b80c07154107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 547261052 1250 547259802 547259813
    0xe0c0d05070504080c0d06060f0b0909010e04031d0103140a2a090e042d030f1823030610061202040b0f031302061b06100e0615040b16 59
    0x40506008207118042009003d5030b00d005c13a0007400144252404400b02c103480c5441401810540c0c003d4401981000000c150042c1c0030004080c2248201c6502c002640c0380d60030f1040040c010785000700401c80c210408540c0e10404492034040e01414140003821100000078103440ca002101c1c24441c00303513039850703080740071031480303140041031485c00c1e10382960800c10b03200540030301d10500070f580071411248000350410a10320b0b05840407500c1c000350308082d404c000d0003050010800500450104010f10310000300144030b403100c21a01c410403684194091710742162542400412044076101080c1c030030b4240c03034948080010318007038108210f41801051609000a024004114080e94040e004000c20400025608250340503104800d9030710703640f9255403c0f07040c00800602c100942180c40030540d100c00a44092040460140700030030303070344143e40388480c80040346054040c04040302c1450300441d1540c104031003143c0d00321202d812414a4944c58a0500282c0d41040310b40c0c02090300c1303400d00d1904100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 547262302 1250 547261052 547261061
    0x706180e1503060a05070f140f04120201080114010e043315020a02062a0f030d060b07050706110102070203030d09020f01141206150a09090b03190602070c0e0c0d 71
    0x131502030208150305081500600c04031b06192880c04001003080039000c0141c15908603a10b8880000320b0716582c5665800c0b00c41c2c1c404841c50186d010503651030002418a05484a0302b0340740300142d445005d400ca071481004005c2426407961a0094100240c8a220307007025040070a414a400ca010030070b07549403091242c07409001030b040704115000303d40703424016152001910100d02001c0704420524904402e51200c90008900607d06c8d40700e2074450001652001c401811003010b03081c401c0c850789485084000c01c1d84561038004040d5401410b003004858820fa0040005146180000d40741440c00d03000603145800c001242c0ca2203603901c407005811840e2120b2694000403080c00d00514080030202101d1090165550001e285221640041e54958455640e43c15800c400019961100c0c03217554001d01400b814003502880746d1900114014500d40098800880a000c0b421100301701c9007503540c074020b904404003c0707070b2440c190305021410707034804011a4410405160016160103c0d03148100c00e89 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 547263552 1250 547262302 547262311
    0x1f020d1401052706060306012102071505010b121506130f050409051b0303040504020705011d010b0a03030c020d1e120504060903080a09030b150a0b0405030706180e150306 75
    0x20700282e014061400b9520384030f603010708200c401e06d460b03075502c01c010b0320900c0071510741d5640c03440000c0405070700015560161850707601403003111340b00300030390792121088481c08e004e00690901c05102440c0c04034810ba511540c019065980d41070085144004100141c02007034620031030404001d000d0201a61b2400c03140002e240c102d400307200c1d54419840310741c1c07602500150740705030700001c0d11036405c00e840030821103000f0400984110740d10786032070800d540200b88524409694040500c00c555580c0f07814018208400c01c01020034229600d10f550035514699111402c0b40c104142030030460208240c0c424050303012009001c00c0450318445d241071311451079040e10340018000c0078001808296845007500090329070102c0815565920717103d040d600f942d1107a0004000303010b28410800e007082903042c10071b03003840e05445219003c1d8403007450b2007850146016064045d44034003007c003d604d1144100100c80d03103a0300c000b001502d4641c014a03601074411111a42c070700c3d40000226119060411005620 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 547264802 1250 547263552 547263589
    0xe090105071e0c08030411040b0f0109350d092403020306040f0606020c01020f0601150320070b041a07080402060a0203040915050102011d1f020d140105 67
    0x2850700e940082c08000710800d070444010311207404004414025440c000c0000d820000d00350722031130503261114500d0285c080303090140381803c003201e00900302103008281040d0141c5456114604101e031000061002c42c0140b02011203c22001000c00a0800c4900c0b03090001005410306110804000d81342003556886000c0040f11014a000420107104440505075001e2030050307034a80302c1d0760008014000400b10610407910740070300054480d400083c010007a24007a000d5441c0e105800c0c1642c0d40380c040900c62a2090301540d6a41d2a80c2807003588800380e02d5040c40c19580c821141d00d4030b11a100d4012142c02c44000780d000e0140001d021001c0603c03d0451280c401180c036504e005d010041030014090002801400701203000c003200b90090094901030807030000c00b000a0000d07240c1c41c44e09070000d0300ca01030241d4a480d10040b440300d00a400d006403000b03c1401800c05200c0c115000d000b82e41940d18400e02181e0030300c40d00200b200540101e5552806455400701107506143c104103200800c092020b02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 547266052 1250 547264802 547264811
    0xc0604030c06141b15060105070b16260f0c040305031909170304141903030c020a0b0f030907050109051e030307060c02031c11030c03100f0801060e0901 67
    0x920703072203900301c150744151030024440c102d0288181c8113801010303140e10081c0800340200042d08000281042d88041896a2484d6074403240010360303461203003134005054000000001001c4001400c814290b90000d46171001001c642d69039101c020705648142d141c4c00e95004010b100701d0707240d03a2140c940c0092005a20301d1070980745640d40d540e68403604010729158804008090800d070b01801500f0024400043c8030050841d164a50640b603921a0051041070100c0c04440b40703590900e0840042880d20207414a50301605517201910411600309041341e00125130440800d0003200741000e041903031509000b80f03440b81801d00650307040295680000d070410048002c1004907940301f0030442040e548482030b003150101c0c42800301742076104480000d029581020141111258004020440e041e1000040c545a007002d00d80003098a00307800c10100d0242051012030701307000980c030056812200c0216160082d079078a01e06c0341c003540b040f0f030b215001a955842080040c0d1500050181c3d101200c04001c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 547267302 1250 547266052 547266059
    0x1103061602061b0d0e1f06050301110909010302150d020d0903021e0304060507060902040e03030613020408060609180f0607030c02030f181c15060b03150603060406030b0c030403020c0604 82
    0x3d540d009245400d400240c40c1d44a80852030014010340c1030101c40c2101c941605c3c5440044000030744060310605009620b820340c80b0104003511001d960084d00000c0442e06946d1070741c0c0030000142e10b40c1400100d04c0c081003190001c1c510302da100404001c62800004180c004079401c010741400d80c8542c800810254140f29000c0c0303000040111420707103120741005621100281014001050401030082d0014035110880d945543c00002551041d002107078460b0341c9820b40c0c60b4000c264001c500c5403004d9517104501040c56403a01c540d030a54018100b04d1554000a14064010301d410242d01012527503401080902071150b81c14050300040002c1800118500a8100c045405904c24840c040403500e010071071050640da10100060310000f03403030b28031603140450390803d01c05410400c9070721300c50b0a1404a000907003a105005580c405c2c01140c0405440071702150510015501c010200c0750701c03aa0f01d0002000046444060600590140c1d120700d480307240a03e400392030850700500c0709126103014003041 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 547268552 1250 547267302 547267351
    0xc030d2f090d2003100e060903070308010306051b19031d1c031d160f0509040212031308061509040c0b131503020c0d031a0607110306160206 62
    0x1000c0307155020090a034922400d050054410f0016030304164140100b10104101d62065004090711500c0c10007030300e1998603846076003903481c8505000107012448000041003c01d0240d0700440e44040d010040140d900c50709582c1140c140c0c0701e4540d4205140c010503181f56080e605201740301301100000d50038000141010a05030351040d0301088070848000b05814201441c0c07180e0801071820f00c03203075403861664444410141c1c50300d01100b1843c50749001500c0002c2d504222141050448001800b80c054031b446a8003806000b5404c6002116030740300c01c1007455440741021001300014041503001d0a52401c2c43c0405490b0500540d82642c464a0144140004548854060405c5036161115555030704030f035001210060b4501d40c40710030200d0030110310f13200b204c1d01500200b4926070501d041d1440b400d18180240c1c1101c03406c110003804601e4030440c005d810b0800500404609001d161100301205008000a04c0d05c00c0403254201014010418489040e4040200307540090303901c000800d40c2244c40c440c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 547269802 1250 547268552 547268569
    0x309070302040b12070f060f0503070f0815030607021b030a12050a0903061a040c030507020c010c0c2c0106140702100e150c07060912020103020c030d2f09 68
    0x19210302e5445003d041181d848100c40d404212005080e20440d40e95040705402c5410310f40f091201103051221081055440741e0122031007020175448841c01d012002e4001c5440e000014840f0850b000d49141c6100c03180c0e41004417920030003c036402040c84144256070010305454410135140203078400d52014000400075011060701d0503140ca000c13920b0b40880e18007110150155400500b805162481ca42807480d40000b4070101c9a9054505002d400c14002c01202150812980e410068001d800e9803c1c0310362148141c500c00a004200a4007816101c08401440c8a4010284111000d02c10061000841400c03c25401001c150030112a502081c9504411512840ca40280310b03440082c18004030303d0040c04134804030500030340300140c0c54110000c418070030f03441140e03810b480e0311448100003500c078801c662850030b0f5813105100e151106034950064010f034201300c014403814007080c041c50098620310b10520410b42401040c243d90f010302481d11148141d40c60340f100700d2550302000000d46031f4662000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 547271052 1250 547269802 547269809
    0x5040e0a060b0112050c04030b060102030703020c0f0d061b031b0906140f07060b01090909031b0602040509130c0b25060f0903050c0613020a170c04060b0a0e06030907 73
    0x450b00310000c500488000030340f62066442c80d89007609010341000d031500a081543e22031000020039444000040e642ca0050400003001680043c0d040141800c0403100c4004092001e0804440701046903207240079642d110308090346100d80c16440030481d0743d050003400f0301c1000c500881e106240d8a032400a0480040340103460034026040407102c0e05003071500882da035480086480f07540341c0c00035140500192500318100d50005451481c081803403500d9201e10000c40d9859200d00034451401c0f640c041c80c1c1c4c44c800c0b00980f601c540c00e01000a140e03e500f40410310901401a00d028003242600d0284110502074021811109052006614a020556010140380c1400060600410300c0d840c2c03100292454615030130f01241804613030010950490040c204903114641074400c1a03449103049040c411101c500694071a00510080041c0e00c1c2e4440c0ca140c0d0513070940150390414090501007000e44109a100c55514940050000c0c880b990100b2008071b4008110341652640c00c100b4441c558901e020702 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 547272302 1250 547271052 547271063
    0x405190203101b200a062a0c050601090b01050306010309020312040b0702040509010b0f060703090506070b01080115060210021c060e01060207080610091d0a0506010f05040e0a 77
    0x11500540d6802c100c1c41034981000c82091201c4941e404030422110a400a0540803602018501e801a2850107101450255140042003120800d4a03030401030690011050200d43e00c6202c40c0980c031300000080c6800081540382d0400700c4085151651a00505a000e40b030840d140c004400b0a5a9010301103a800141c2440c001c12019030314000281011034071400d84014403000200041c0107003208014009030380c02154108090b07074034000781d20f0980c0c154030303100ca41c01010710b80d8409540c03901c074001d44a11070107483e040c000d180e2901c0201e40c907580550710686800501500400414009010f400e0288440c0b0068015551034044040e542e03602c81c2920b94401e603004120504919804c00c841c081c0c4040c1e801051003500d40d644100c10600f030742801803c0042c02801c2c00130400d1040001c401d40181e855161604240d807506102d02c00070040c2c84020f2600c40064007080011010812184c120b0034000e401802e41545132083c007068036440c90740036501407400c02c0900040e494010850112607908003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 547273552 1250 547272302 547272343
    0x31c1b110904050114090c150403020307031b0305060703020318210f0f07080a0e03061b03070e0607060f05181b0102031b0d03140103080702040902031009030201140c030405 76
    0x1e140007409000394040380410401c505c403c102000301d00143e40f001d04034041d03580b00d014444c0c85000900700d01c00d40c00080d4055010340d00c1000016071040e00d19400a40030f81b0b031542400e482c0e984c2d41d801c0003002d80d20040000d8010060220843c00022102c3c1c0ca1060f800042c15441e040c414980c4030f0114028031880f03001e4000c28107089012420701110090025900b1003a9140c200303190860554001d0309208000030700d0081c81200034100080c055008850102c0d401944003000170788042103074402032860342004006c2e941c4001940700e082c082c2c20742500c90640401e0700002d054601c021108000c15001a604480030f84102584000c103d0304406c40da1010294071070082e4800607861449841c100340301d44402a046841c2d040c4001c1941600100a5502800070143c0840e607800c00324801c0c080a040104202705000051901344c0c010b00802e031025060710309031144070000500b203544030181a40941d4442c00a500c5140014050582c49400b94190310b06500b00703500c0d21607840c407c10381201d1001844 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 547274802 1250 547273552 547273561
    0x60246020a08010e0a06050106080c0d0e03090d0f0b06100e01032c0d0e010c02060901230c030405010801120b041403040503060a0b100306060806010f050702031c1b1109 74
    0x180704100020784110002400704241c0c0550f00c9603180d0207480c1c140c410714980000440d58501c180b5420340240b000f49080ca04024020a041c0e009090040154549100c204524551915482c6880e41014002c820520130402c5504141401d16801000540724019004d030345146940c005031084605103081c6000901100707076074201302e91601803180441031100c80014a16400d803002506030f915400e41da07220802d802045005640840c07041c00d0003940f0203810b200c0c0b45000c1d48542d41814541d0300c0304840046550b44d140342d0203482ea2002c0c01030641c83e08002010b00095801a1200e4010301010303500c0048517403a500d40107044100544020010080c550117011524000c10035038024007002000e0b0307503860900c1082100280a6441e07081e0060865a102e242c4d6640603103e11011104141c8034140691380d810700445096042c8019001031040c140000809600c040011288003081031000c00d50140c2070f800084c1150015001110261080102c020000b5403440148101315909a54080ca0340d140c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 547276052 1250 547274802 547274809
    0x12030b03190f06020d15140907050f0d0606120c050906031f080f150105010509031506010311070602070b0c042912040c03020a0f061d0114030106024602 67
    0x48100c2d000c0d101d00d002266082a101ea82c0e8059040c845c8096910301200799294942003030303241400c11031640000c041000600d074900800041c014444205201c500d02030704c0d00f000f0702c110740c0390350805000624460301000d400704440c4900d021505e0b480c2001030600e82c80c140010158440240b120728040100031500400440740079000000d4000881615000021101e1642e80d40400d8036031a90180c03001000018254082c004407000340b100a0040c101103900c02426030304401c00545032604050b034035a01205400d000501928045100e01e0000d030343c441060508106442d40540010700c6d126041108001d020340508000e070109030643c002d00e12801d1b04e1211004640070b50044c0d41c00d0b031352008081204201381d520020090340c0c8204d448000e03250b120840301c0055159402040003244140300c90040004001550038400c4405150465014040031021080c0780c00c01e07071001003d07a01c402000544540e100d00b141c1540b421350305a142a4002c4003000c0b505452580d5143c812888041c588181950bd = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 547277302 1250 547276052 547276073
    0x9060b0f1b0601090f0507110307030f140c03031b0f1207200105040c0e10050415120506070e0f1c020406052d030f0606061b12040312030b0319 63
    0x541041a02c0b125a5102400e070050004025141485460035001589040c0180408103400382071070021410507119030350940b241ca40340c1c61540140b00d205250b0138a0551780900604403601c800010310384900b828039540c07000c00e60a6005001c04c00050203451800841e400c00d03540304140d22001c10710356032038403103094940d0b8548040d4040220410203010399060170540117980118412000c2561030359a524412a134100103036410038014a40c44020803840c82c0035000a00c9031002401c0b1121100c0d603c0d055410980300d401c1c3c007110560807002c2005a80e9400506141c07200c0000e80348100c40f030000310300040880302102003e121100060401c1000d544950f8000005000040c0c000483c0d00c0c410021401d0741030991918026201c48a10144894200071a650080901caa0001c0c0241e4039064100b0102c0c6c0c01400239041240c40704c0441501c030080c1002820000b0102044e5a0740e07560450a03d02501e4040c5411481450704080061802c1e45000510803041c0d481d0340f111070142c0f00d80c0d2515041c3c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 547278552 1250 547277302 547277347
    0x9020c030c1b0d0b04081c060303020c1905101e0f02070806011805090f01060905090d0905130e150703140702030a080106080603120414190605040b032d010f09060b0f 73
    0x13441304050307c44c02150301d40c40a815680a9000c50340317208120f508000c40c0c8010507400358104c2c00c0050701001b69040500c51080394494034180781e030303000e003002440002001c50115490000b48564001001c1540c05104403405440078070080c010359230415103040d0500d8401c0b81c1d403a240682d5080080c6100d80c5c1400b84102108008009010655858140c4405000700b592080040d000e034540045010703001d14054000c0300c00c0900500c00f1800254041002000c803060030480318081d034120310110201c00040944a00d0a540340000c4c6a8030740400759000302402001c403c00d640c420401ca040c415000109981102c0031440d20106d80c1e681c54000c242894500340000f4008100840c01042c109c86040070041c1c04042510861078000c100e14045032441c1603441a800410b00c100802d00c2000b001600655120900003a0401e403a00c0078180c40510384100340380c100303995050340014001d01c0c0318220424010800190309105003428915101e11a10484041e20070305030b40000d01d1a0516110300300312003038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 547279802 1250 547278552 547278577
    0x1050a020307290f0406050709140f01020111070606060e09040218100801060f08010e03130b03041e0302010f110903070b0c07080106150f031b030b0a09020c030c1b0d0b0408 76
    0x2c42c21315459900d852081a90222400d0b4101800034110328030815007101103e031080d801800b40340d0400c041c40800f42c00042c0d45411952140a250590300782000203141c804d10030240002c803146010001050b40d03084100c110311944141062002503075074102d84811285030100e11644c00d84481050440d50304681e44400380319424004000f4101e040342c60000100c65941c2c009100090250412544920070103d4a0b608003148140a000c0a100f40e0082e65105114900031420000807003c441004844190110f005070344617032160824a81d01e01039a900308058003c032a081c4100fa500003512148940164181200702240445140d00200001f8000b0011000200402a218000c4000320100c2c469140e012811005200d030b4054030901c14244010305000316281c803000c81d10002c80c040c1a00080f01c5510444030071000ca1000035a1000300703078580d48400115940d410101c22107080041081c003590b80f41084001c1440c50341c550286c0e4094080d4003458107481a52107290607205405400d020040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 547281052 1250 547279802 547279883
    0x1b0703061d070f06170a060504090803011805010302100f030b06030702150c03070203032205010e011505061207030203040f0516032d06020a0905060706090b0601050a020307 76
    0x94049a020703118900124400c2c0d80c031003903c48200140b0b801071441410000781d02110700f4420b4103a007600351034000418010219040395074000090035640051000e9604010000041100348900f85d41e55220081202060100d07602d1a0001078003060032914420600404080403000244280d0040709641002050f076512401d08503c0203540c0c40300000700300746072009900480c00018a134002e0340c0c800c0700703e58000c0d0b2a5681e05541c0d6910009400140a82c2c00410300b00100052404e0080d47c00c801d4601000244161403124000303101e52055125a0003540c0c200320706550f9816800d012603108105090159882d20317039103000f5201f074003510750181c150b004008908181e49000d05020089038043c060004003a0030701c6003510021003018201c04069034141c014540042c146801501c5400610f085c08581e041c0d5502c041403040d40518801c03980c0036540d4418008000508003081c0e080142842c015042c038851900c085d542c0d200f80030001c1e001e0f25003400300b000c844038610841c01040155803407400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 547282302 1250 547281052 547281071
    0x5040c1d0a121b06080f0402040b131a010909090209060409140a0305071a0108150603030d0f021908010302010f051312080a03050a0b0f090a060801050c041e0b1b070306 74
    0xb9000e8003511507900c10020f61890000b2468440c0304054080d912050440c0a05c7c1c5480d420407001340410700400da00500d01c0d070080030442600b403080070703100501030500d9115060203200040c9140e4030394210f18082403605810300096154030082c40c2c0c0c000d0041d100042c03585000d08040308001c0702c5441210991140b005408100f6030b000025200c658481d0401c824018140008001e00101c2401114510703031100501c04038541c990050720b0340100c1d0140c1607a103064100b94180094903645103450003040d0300060000d9590f4441c0500c060000c180f403900414950650780003c01c0f07040a90400d0b000c204021409076012804a40040b00038880445407181403107042c07403c4081a0044180c0b0380c00b103407501e00041d400a44500480c1202e800080010302e4020581040185140c009406c100324196100c2c00441c01e01402d10076180175804d074041c20b50722945001c4849680d072145504440e0540484407080168142ca4400c1c0c811001c168000506111a02c03415246030441d16803024100e10304011044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 547283552 1250 547282302 547282313
    0x1140f1b0a15060b070b190e011803080a0510060c08040b21060d050c060f0d05070905030d17070c060905102019030504170418050105040c1d0a12 64
    0x1440d1404080401c0c003403590390382101a00da010b101d001600d9512074000182c00c0c0031301c4071104846110310f16400100c80602318461030031102006050039002c101d400c00c2005268001340596404400d0340b800b44030503c0e0404205000702c403a88900300c14419503000c00c60421003800203860103802001c41260705e074514604040c2d0303980791612155026501580100d1041c0c00c00030702d20b203140c0342c000000740300c07007000c00052090b41d0380700c03440d00903104009020050f0550380a011703ca0041409903980320006060004241c2020a45028502030105200b6050388248580940c0756000b03415080090a00e15142001001340c01e1082008005000e415019261040154040000500a40714801c0001c2c4100b0110310341d403080610404084025501640381940b00703800c05540903114410003030f0450300c1052402c0564000e500f02808940c0c03d8100d20784414400c1c0300703250045c1800c0380d081c418100c40c4480504040c0d42c4013283c03c00c20032030384994001a2034904600f001842d14614004544a450405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 547284802 1250 547283552 547283573
    0x108091e03091e0307050906120102030a051b0403030e09040f1a010816050a18090b0901020702031b0d0f03140d020717071707030306170a060b01140f1b0a 68
    0xa46210f00740640503240750f1140050300c90300c0280060000c140460800c0100005118002c1400b80d00144121186001e82000c0c00a14000e247c001000b00d0142040e203451070310309042085600070002c0902c0b040010a17400760908407462401c0d07070070356003d807500d003001c0d41c1d84000d40ca40500240c00d046110900c070102110827034106d848001c05d507012848681b6540c209180c07035100307c03640302c981240c052080704001d45044034030024040d00000c1200150303650042c0f410742101d1040c0240d502180d0f501c15824180034510307020100181480010b02d1a800180343da05001d07201500b10210a40d0082c00c06000b160545284a0302d100a261564a104216006540403e00444c6e0020180c14404080340c650001d46d4070150780035078800010782c0c81810600b001d410145064003019215071000401c030003020300080e4484a0b8402505414120341041c0d02a0b450520310581081108a00300203500301c0c04c010380b424052a0603001d65503c1d40c110750bc02405450610b0314415004110310102008461501c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 547286052 1250 547284802 547284817
    0xa091104061e061404050f03070915031a0402100305040320100e06070503061306050a0905060f031b041503170a1209030203071106160803060a080a0f020108091e03 72
    0x30702d155450315081d00b00c414469404020304c9a81042c4001e019920b0111400804d4036000760489200503a208544025140d540300034988140c0c41100c00d000340428050014503a0030302c82c00080b250f007460340c00704e010350050030301c520100740d035400105003014440c6440520b40a40903007044181100705800315101e00300524108402d528066825000741400721369207100c0d10f1280ca0710b034210b940b00300c180f2801000d820403044c001592500f011860781c1d0b5100641c000307000c0e0308030005075502c0c013182031201100d001c4004511a600c04c401365000341c06c075401c5002141d1801d440106210010100658003500c95410082003214901c6541c0c80a0107100d01405040010f5902c60030710600e80b0a60408803001820064016003040003041c011548039445a200902c3c06000c40c3d04c1c0030910a4440d400500b03504c001c885141d000014410240b030140760382c6001d084030300c018150995640c0e0f105116080b140b20000c3c18032000030b00040141400780f142002010b2540e000218524805400a071203a11464 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 547287302 1250 547286052 547286099
    0x110316020604050d0804020102070801050108070f120b010320120109050601060f020c010305040311060403020708070602010b0d060b01050f0f0c061b0d05220308040b01120206030a09110406 83
    0x154284a68800121070340199040405030008048a41d8100c1d11024003e1090341580304000001032407080900c11503009055000181402d071781003601e851040e107040d903c0005000031a0040b01c5c080b03540c06a940381100d500011031809400141807060307101200540c000e03800b0902481d1000302481c10340007000304c10300ca41f00380c400580c0c07503100c25902807840141e2030307006034071005081c1c140e940282e001b103420074040d04201d100003045220040c580242104c081300160010001080302c042d041082c00d01134003150000344101c10880011a400c8030000b203001e015207480d0810f6114590007081120748a180b16440a55102c060103100c403026400000c2d429010320406c0002407102c1c00702801001044a4041881e140c9055081518090f00c03024020140390581c8451280c06242c40c200c2003503a282c460740764842985400c0c2018441080b05038002c0c49940c00c09038041c1d0060f41c0710383c03c41368070a04440c00001d0003005410024032100100c400542c10030720b090301c00b04074103010304e5442064001c1c07c1e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 547288552 1250 547287302 547287331
    0x20c210d031a06070507052107091e0504080a110f0a03030b040906090308012310030506040e03031602150108150405160e1611370b012309070c03121103 67
    0x8403007107004900e0102345251380e4001302c0c030910078200300d50403c01514015244502c1d143c80030325500d10840d88155007c41d1a120006440301c001a0401c08031900441340070040d207541e0180c542031940318101c4000003010141c0d0355100541c0c980e80ca5100700031185c1c200c0c6d000c1110f048a8a4050701903403003805002160201d018004602010031840e0b17440e0070030b015000c81c06c260711100090b4081e04c00600140d60080d1503c2082c0001c1c002080a1803040c500d440400d400c60002c0740000c0d0500d040024404015180800103100d150000518a150000010303550f25255584c0d00b030a03421321500c102d6060000d99000000140042c0029606005070a07174803004986100b201d50995074010160a01d618541007024400d0740e607441609201202c0600054244c00c045080459205101711060129115118000140310070300980213146080c08040c60503001c0000c002c40020303040c21000b42180d040110300a420420507104481e02c20403000c00c48810300508009104c15900e6800c101d40320200305664 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 547289802 1250 547288552 547288579
    0x11042c0115091d06150411120f19110403121106100608010501170105060a120e10050610050d1824050a060311101806020c210d031a0607050705 63
    0x21440c1c500543d010403841d00c050b0105414803001c7c0121004503c80004140200082030202c1400326110b40481c52600e2182d18040f69001203030510080e00742280740c0b4141030850042740c0d91040303c007600d0700948419001d01c0c1c240411200a50402c11103580c600445080c014040102c1e8542c0b425595241c0350a40160f07200ea004580744411301d40001c50903400d0b03100402050030404028100b120039403a0a9200354000e03da48016548200d191048551120142c5c026000032807181035004007040729994061119104014224061503a0200400ba036401d0205103e000007104400141e0344841040b0002c2c0d140c91300006c200c21a02c1040031094244000941200340e2880703100d041c1c0c1d6000400e1071541e000001446081512206140140058140d0b0b034680b55840c00d0203400205504ea00a01c11a00050240201180f008110295025081945800c0030b64041256440c2000d14600042c82ca112084004602402108400c1d04a980001d1620911101140c440c0556209644c0040103080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 547291052 1250 547289802 547289861
    0x30106020709110a0f09050402070b010f05040e060403050a030902090915182109090c0301150c020a06110705150a03050c0f090121050a0911042c011509 67
    0x100005103c6101000708440c284690085540104000c0e59103003600200d0348440201e000c0382e004101c00c7d101c00d40800010401000c101e10b2040207014150350601038454017125146c3c0e00ca10140009040c4100841c0d03066040d842035003c00fa07507075001001c10300e007805e01360360254580c040030b070040e143d2203032607030020303c0085a03a85226141b0560100401c141c1c2020702c8022028401982d0407020400304004160250382c41c0500640201f41409280d552945400d034800c8078043d818040f0b00c10300c1854040f001c013503a1804c0300441150507130f0900c002c0352039181d1012810501c15402580c2d0102001c0598030028079010013038080780520362410402500c50840904090140c0e4a807070014007070030008130350207502c6a40c410000080c100d19034007901010092550540c3d00c100c1d201080240d42c0d40103c014040805078540c6c4481d000d82c0c0400c00300505194102840540045001d12280c481c1e4007078040810941c4401141c030082c1ca020603d141c0c40f4814031000e0f01611908600c4140c114125102d00003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 547292302 1250 547291052 547291061
    0x180c0206010308041a04050a0b040f0609060509040f0e011d0d0905060315030a050d0c1e0b150d0c08010b030708073002060706050a0509010603020303120624030106020709 75
    0x3d0304000040d0406241c00841500001111030f0025441814000050344d40c496402e90005401210390b265122407c1043e401c02c0b100d07030f5500110811168000400005070880c04403001030500781d402051508541013100098940384648454540c42d002445070011000c070524906050b190064032000d24408004807007100290044650018003000485d1100c608000001d08030754016068400c41001a150343e420104002c81c20008104404044420064581c04150510441d1110740040c0407041d100c40c04890002851a00c00d4100c1d000f220b109562010801000140d0201c100c0204648455038035010b494040314050103442500c101041100c004905070068480030142c1070101c2c0803001035500c02424444402504583d103100400241c0c1314203004012883c024400420369060a030742c0c0788100e4030014250120f81e45411001d20050f9404411580e424114402181c16900d0b41c0e800201003001135140f020031203000c015560452240c580103181200c40c0c82e026900d12030303941d40c0070100b17a5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 547293552 1250 547292302 547292309
    0x909030a05030c130f120b01090504050a060506010e1c0203060601020616030b010e0d143f090405012c06150c120d090524010302210106180c020601 65
    0xe10900008051200321000b03050000d450000c1140819500c401c0c03140014000c0d00038451114982c01e1000c141f1201d03450441c0104103145007002140b43c940c5500740c035001903140041465032100049100c1d80e20401d0003d02c01d15004110801049030741000807100c000e1034104900a0180c0c50010b2140c0d800428070364403030100715040512500908004900601c400403106060041d045404183c07520b41001595103d88510240580c1300003010701030f40b41c01165216a40c4944000080044035000039280b100c0e43c2040d000d06101d109000c1e0030f070002c540a03e03c04a500a45400c00000d40310b60700030b2800c80d60484840c030400c0c0146100440a451400443d42d150b08103501505114900040d0801012460300d54020780e201a11045851800d662220403040b1400c0e44032a0784006009051100484100e50743c000c079141d81010940400d0b0094052002a204040565080c002080303007080c519000380700302c0300802c10307192184441b116141c4044c2000d200c1d146002284140e040c00005e02c0ba059 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 547294802 1250 547293552 547293557
    0xa030b0d08120c12070807020f1c050f040506070f0209011703190201020d2a030516051303080309061902120a05131b06021203010f0303030f09080304110909030a 71
    0x800b9010000c48200c8400070340309006040f41000000100c14032440841d020352801e81d00d128080c00c01c030304000d180c00d0f041d548017805500880d8403292049a080304620702d40c0401c2c10456100c000c25481076100d400b96074091a0806000100d103000c0080d00724014180901c00c80c2c070003e40e643ca881126400c0002d46800d20141c0d03104011042c000400d102c00da040c20f000510000d032a24404081030010345150381e0400c6115450003801227042e194401030404114080d01d010081850300c0031500300d00503a00c2410b00c092010004041f0171031694003024402454100d2002c3c3e507030341046d60b8002d030358400450b03080e2985181003503480c0c0201c8040c02107407801c1131828840342d9240c031031114900c000d104c0940790350302500d06084084000740349805100c4d055000e015544001500d40700b170103818003040c0c070b250344020345041005024502a4003008816a40c25160015810340c012490200038503089801800504000c0b04220800004c070b040f1025026090320703065160f40b5045011542e9004040301c0501 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 547296052 1250 547294802 547294807
    0x120b030c0d0605042f0618040e0705150906040e091204140102120a020c1513090e0c03010b010f052b0b03010f02030c0a08060604030206210907060e01120e10020a030b0d08 75
    0x101d51401801410880c44054108030018501f4000607088810450741ca448503000340130f08204501d0104841c0c00b01002d4074002515101c602400640d040c890740c001d480c5207030100c0c00880c1d4248001c00000d000c003405044201d07604e07074480c8070f58408038120800312401407041e0044001200d02d40000e98040c9241a0000e100144840341004841c0034040703101602e5900520040c446800705034103640041103070600c00200540840c0307805041480a1560380d0084e81080020b00041e40e00204000022100749001c584407005045100426a10141c4422001f001e1103584140a103041d8042d0045042c110300070018400c200200509a00040f01e01100401091000a2a50340150075240c2d001c80001c01d124505926680000c507203411a03410b69090842203000e0301c00140041c48402e4006480500030100d051801d0030003050301111045190421402c688043e80d036402982000c0c044940402c262070680954811410080d00040040400681400b2000001e81020402e040246400c05007092 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 547297302 1250 547296052 547296143
    0x150109270b090109150213050a050619210b01110a03050405010c05010603150b150c0a0311010b0d0b2403060438010314030307120b030c0d060504 64
    0x140742000301074407034654035001d003800040c42c0c1081d59002012885001602c41242d0388400c00d81e0003280d0402401078005031000e02050b5a42c07020750f442c0400d00302d18001607a819050032118000d050304036005846662203144070301440e42e0841c11290000782d8400c08907078a114810703503460412101c0a008190104024421948510541007a02d4000d10001c00c4003682e907510380381c0380e18040804961595030760303818010614150b42c3c49c411010f10101c00a0401c210449010340340c0b81c1803400141070141000b02d240c0c4406080d0800d0003c1c0500400b080c9416550742841c100040003110100c8441c40b000f1000c521000d9050914011200003a00900e030560b201d1f6102d89042a80704210b8110705028101c01000301c40e81203401c3c19a004000c1c03400100d501d1850103083c0d02900c0e05052600d0f81040c810008e2099000712145410f081c1c021002c64655907400c0403e09100c200c400c0d150708500d18540200038461140c00080c0118410000340444507110001d420144554410458200140c0039111 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 547298552 1250 547297302 547297313
    0x50f040209070f090f1e170601090c110d030905010f0606140f0f190e060a0c0b060f030102070503071e050706030c02031201060201090c080705010e0904060b0315010927 74
    0x526800300d500348034a0080c0c9443d0380340c4144440303038450380c0c2c03251040c08005a941b0550300103200071302c0d2161908004400c64000c560311504140101804181e640c0030080ea950722a000b00c1d800e0140703a50640340400348514009014060280b402d4400e0341c201103400150852611070641107441d15a54485200004404c0c01455804468840c455490501542070301003910300080036507411010680003443c0a83c040603090300880501144120428005440604e0b003020003a0603850380060038102d00d549120000700201419000c15406600c00b00e42c1c0c1041210000042040c203000c0c0ca10000c003107000c4049400e11701000c010082440e048002c0810401c0d00030341100000e07040704d0056904110300c10401d14490749090780008e0042c0c0d11011424140046441d4410150000c80c018101031346c24940080c1c4591030600705980644005030015041c03080661211200400003016289030180511038840341c0b0b0004e02030004558502007412410301c00d0343d4a040581515441890140105502e52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 547299802 1250 547298552 547298567
    0x203040330050c070c0f080601050d1a070207080706230a0207050d060227010f090506031f0306020d0203010816080a020d020301140703020315011115060123030109050f04020907 78
    0x706003c0d480140045000555420707080c4c0c002d0441240700c6201c40346000c011500c1d014041e44250301a004a5489501007840100132902600c440c2c4405030054850b650201c0c641601c542c0b029289006960004c111964011400800c00d240899629244005c061342042c2c60301c11101c00707202580c4918400c000e203040041e41c0b061f1690080000505140180b00d414480720140c0e41d170309910850b003409002096800200001800072540341924452f0709050226032544009002c4207060100d41c208405c070306090b40e0292014590088081d92190f90501020001c0d420a0056a40301c4c0210020780214004003400c440450302d80c50700600c1504134680a003c90340302007070b209903015500c070300001684445800c0c6d4540901081d03500140c2e6481c28401000f16000d440403051f040094425020030500b030000760301104c05075411605441a201c3d10010394050f40700c00c021b03541649200030a00c500d080811302440c100d54095506215aa0703500241d51501c89003210300039405003074800400c40c0700b44640344 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 547301052 1250 547299802 547299811
    0x9080a0605061f02010b10051227070f0906170d08100e090c01030b122104151e0507020d06050a2003090c010e03060703020c0c13020304033005 63
    0x30f1145039004480c94000400f44168410250f912401c0d52016030902d01e54803100c10700903240540c10042e0b00901031504600180540d02c3c210010008883c1e024010805c81004420150441d80956500c1f0110103a07140944030391301c0e009141060004001180c05502c00d003400036140904214450514241c3d0889406094012041100d170000724540142b168843e0281d815400103140c2515079500040a0340c45071200a4040d1280802c2158074100000b9503800e200b40701500b10078010144020004136001d82d5002d8004c00300d00340001040981c1106004c0220701a0711307001c4005082c5004240c50a01c1894002504001c43c902080d0115485a20240c0c22042407180440e03216400000f1405004104840600c21140001481083c4034200900d0122140a081c03481c000c940403800652141c80050003807080c19000a5180c1e1103044c00e00542c4070140b801408104c401e0401d030741c0c80d0001d40080b20110080741e2042c0100c0744c102e081c401d80c07440c0c00c560200d40340c41101119480701c0c00b4160290 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 547302158 1106 547301052 547301059
    0x60e0a080d0f05032a0307021204050906220f060f080c06190c0f0812060102011a0103110405090901050f0c09100e130606020303090d09080a060506 65
    0x250080c0d400005410941e07125a64012040001d40c0740001c40c603460030300764174020003030320812010318054a403d50848041c00c24440303d49946110394002c0d00ea124807824002042480e154159a80010b0320703511402e404c4201460714001e90341c0006580320b419482e01c006020340200c20440200505901008000b9060f042010882600c01c0f4441080841d50080c84411070700e01845d1608051a070100030340e0030b000ea060500d02d001c1c0c3c00c045500400320750308801050340c07584140144c00d48400055600103400c0075440040d030080540071602d8102c04814070002440d540d542e034405100e450454001700340d501d4110061003020780010083d10444c1024000254507031643e00c0c0e0390111001ca824840245003001300002c002808146071407806508100000c26020f138048003450048015404548019203202c50580e004445400780f49030b82d1b03100d0b20009004c202180c0000d5000200078 = true := by decide +kernel

theorem cover : BRFrame.Cov 547122302 547302158 := by
  have h0 := BRFrame.cov_init 547122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 547122302 ≤ n) (h2 : n < 547302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
