-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1862
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:56:31.923844+00:00
-- url     : https://prove2.me/submissions/1c5e3b13-c4a7-440b-9c0e-8fd7e2c3c8e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 334712230 ≤ n < 334892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 334713480 1250 334712230 334712237
    0x10050312160210051b010e100c0c0237080c0612010b03060409080f070201180815100806040302030a0909050705040b070309170325110607080d020d050708090a03 71
    0x48140c0c0070004005a075443c1003090103410040c2043c403854100b42c80c0c1102c00588000f040151003090450302d81400394404001c0d682c608041c0004055100000e00001a01202c140740700d0b08000b2010340c1d400c0700040900d080340321029210090b011400000d08111075074102990140302040c01441a00e10414590f0203901101c0c00040c03040d14250409103402c400060700002d00c101d0780c1c1d510030754a42c0c4803820105070180e0100d1090111b41c0c1c805081c07071282d480f8014000701c540c607018044d41e841c100f00314400d1041030b520f4001240c0013085010701e070040101400700c400320304140c14065100c0e403007010b0b501c000070489407010845c69002d0240f140100340540e02c05140510b4440c3c00c0c000e641000b14100d08000301d0510004040041c901d444041d004480003440c2d580701048000c1600c418104c070711381c01c81074841000d04082000c40c806028552016030312655550f05614000784180303c0c85188103082440400c04020f80007683e0310051043d0920f0300c07440120349400140a541c2c588070310004000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 334714730 1250 334713480 334713517
    0x130e06090603060f0c1207090e091c0e030309130b01120209010504030b0c0c16051008130311030705010609060311011d01030b0f15120f0405070312050702040510050312 74
    0x20030b03204034203180c0d1020175131740054100114079000707050801c805d130343e00800150070110901c81031050034202ca40050080c0c000b4134070303070340c128050000c058008900403090000e0a84035031020b890038022a8600c8500801c08000c0b0b008002e00e80300200401c40d5483d000500115405040002510885020030f0703050715040c1c200313891a5110031461800410201c0042000d22014034803c00030008024103040c2440c00c0d40c803903410700c414003003031142c6080441c04001c242014009800020480c6506481d018503150212800c049003152951040c000020304640c40c00e0070020b101d01f299400501501c0c840c51149c600418032600441380c2070b21000c980e406e100e054a003003036007660080c3d008503004c41c030103800d01c00e803c0304041c00112428541054444c4e407140000b00150020448001340d41d01c441c031203080360b2035410280c50307841d81c900040c00000e200726510f042c20700400380644140c400e020f50050051215140039600062400390501c5598043e11072224a103100d0701038401615403000307a4003000100d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 334715980 1250 334714730 334714741
    0x61002030d0203040807060f05060108090d20120c0127031718030c0a020406060906091203090902040312020601080d05120c07021c0c050a030206030a0e010b06130e0609060306 77
    0x30761004e007044991000400c444800901070f070050042602000030002014900b110001d000d405d00101030172542d8000a40d140d150741d03004010850032224050a04011480c221065490310f80b00c080b0812140c2d5001c2502c102c01c0c40e0540002413000308140e0455480320b40d48924907031042109a005001c40d04ca0b445100f849146510b4040d4002d5050591400b81300300d502c2d055007150705c80005243c140e009020100c00750b043c58060200142143e160070f0f01d031107181040090101111b409019280c140038103203801454829800f800c090042140110354441da40d04c0d01500135a080400100540540f80c000100d006020403808071240b15500c2d400e147c0303484030014800310b0400821810008800780102c50250f00e175146105448144624026040f46150400030b500a2159100c14803e660b074110510042e201c49040c2c030341107000c0660200c0e629804001171405041004495900300501040a02e48000c0d420001e20488800340c058540686420003400031650003117030710035055400203001c102d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 334717230 1250 334715980 334716007
    0x3090b0913020409020d060803070b010e1f14030f120306100207090c0c02090a020a0c060b03011b080a1109060421080c011a0f010f030c05040306140f06100203 70
    0x49569030050039211241c21901e1040201c0c0c115400454a096010501c040c0c8400c0521520000d0b0100e10019030078914265078801002d4814060301c0c0107000614046562900c4404443c1d600000b228041484140c40e5a840c50810313104500e81d40c800d02c00d40e0140030709000041001c0c132010b002e0001107072542c6e03034290511201e488035940310003c52080e00300000c1d4021681c070542e10b40007650b640c0c01800050078010080c040ba0041c0c29001d178544100242c4050941011045101c07584c041c2010a04084410000740100170304210340024210810300500c10700d0344003203054800e402c1c110b0208130031306d135101c0e095602d0702404101c40d422043c04c0200f8403c0018200707000400a4007023512001c4004560307150314041c0c02c1541441a07582d11255521481e92944400b404113000070784040d00c110300014002000070f042c480031142890b0b03842160b031455510560031240a181c01600a0001c1c900090102c04981c6040310380c1d281c0d8441d0b143c08241d1a1400304c400c101c0100143e4001c40c206a4143c0560 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 334718480 1250 334717230 334717237
    0x120b1f060f0507080409051608130308040c0510030c0f1d09100f0801022805070b0c0f0c07030618080703050a0c0f080c060a0b0d03030e030c030c061b0703090b 70
    0x701c0a02009200d0400014681c80041010b005191400314040c20304030b010185900050141d001408140020000348002801141c03040d15010702d0540c40c1c54a86051803891112960055500039a091908202003a0140c000d90303c0d4220903603649802c0115041d0484205482c451500b01024000c0e82000b0709251a41041c0d8100d80110820030384950340344800701c040c1e07110f40d100b00840c0e5004142c502c0300300d0a044442081403400c06007584030f4409140c5c020943d100b114001421700007020041402104000c05076603107941c10a500b40d646028041d030043e41c520481c88105c40480c20121000100e040d8520281e40840e13110100a0816840e1356050300d46800001c1040d041020660b8248041421440074604c2140a54040740c2e03036030003000a0b00e050120080c009400c1c2810640300031015140d1988905900d6014500000c1480e20207680d5420b61194003100200c42c8008150980b5820020404a0092a66000320841900d0700f520708002c90113800c0d0b0107000300f40700391070400c0b09000c0304008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 334719730 1250 334718480 334718507
    0x12030203071407052110092603060105040506070c030605070302130f081c020f031204120311040b090f04050906090d0c080301050108070203091503060a1205030a14070c120b1f06 78
    0x590f00b46c0c8804544040840d4401401545c02c41840700c041030140704224070162100690080061440c0381007400030304544107a104540c010440000c601013401251240c4601460380141d04ac4003d0a0580e001030280d04881c098640c1c414400b0000185610090210400c035041c0f04046c01040406c1c0d0280b50741c0301045004c000135802102c0301030400c560140001c01100142c0c0c05501c500b402e19042c921800036001b40c3d42d81c1032601e0100d0105000c501c04094404503680321049035a81d0042030040b50116860003146500f242c2000c0070300180f0840818858440d1a07031a040342c441d1034403100c0845400102000141004408200510803541301d44d08150784141c00740102c07031401403d0404aa1810300c0c3d0144800040310201c1030007540e10702801e2420080c0181c01c01121210641d844650300c034442d01100009010003106070400440f002d8058441c05500042c0e80020326549606042d08104180011101030321040c3c0081c0c6000d02c800031948445106032000400300e8281013042c0c1d0180c144412 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 334720980 1250 334719730 334719733
    0x30203100519020412120215010e0a0e101a100504120c032a080d082205070303020c030c1c0b04051f1508010905100510120302030714070521 62
    0x1c102580050700081009140c0440c0c0c500307120729541005030030900511b50010841d0000c600c002c040307480e25184541519501988902c141d100e14031000e0080c034440510751181c1c041c03040081c3c0d130300a040d030001d600441032003411545501d0450030040386840d8084d014010510610040c4464580c844520400034410a100f5200984944800d00300380403002303c04454282813803a00300c00c2c1000341e24400c02003a00e200103045203010210040c100b010010503487e400e000203040c0b003444c008040d944005050704407040c0c80210303460742002912184260302c414042d200d040705010550030810b446005213101e1070b041500304096a980c02e09000d401030030036a441e1040074003008544056024141b4241403420002401c00030540c03520140400c141d2011b002d41c0d24203103c90010910210700303455040308210002886550301ca504100d00c41d100d8004e024200c0303507a81030790105034000001f840c02034003e032025618854030500e4075686010390b01131036030032030f40c081c551182110714560f021032503505000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 334722230 1250 334720980 334721011
    0x90507090c0519261312020708190203070f0611011b0c0f170d0606090503011116030c05100f050a0b060d020d020f160210020606010e0609041b030c03060608010302031005 75
    0x1401304c001004161004e2403004a031121031010080c2d031180041c0c2c03052160002e042441e19102c546a00c1d4402d60740c02001044039040b2030741c11940e0038003540c000340103a506a41400c5880303510007050114140812a20341d80780c060755225500d460140c0c034146244a13901e100081d0825582e6400000e242c1004588084040e64004802e04915020f4440803404480000322a86489401011030345a580039501903454008c502c560036242208564032000940d18050014000b0b250403100611691405030007401804106e0540310750756004a4064410744d2024080383d02e8518048044481c080910b0703034031140401c01c4000c100c3c16a0040c192669a41d0001810084c3c0da540074001130340000301480e4203504c03420f01001180790a1041520800552000303100c145003540004c0c10080b0071544641c031400d000301d1400c0d195074464200e202c0302850261009991179400c040900505106070100340404d0814101241982c8107012140c120f0790000c00502c800d00030200304000500e005042c1125504104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 334723480 1250 334722230 334722287
    0x50702030f011419020c0a29060f060318030c010515010f1707020307021e090c0313031b12020d080a140609060612010609050a0b0901020d03051504090507090c0519 72
    0x5020172541680a000c0190030360003802340380d002c0900390119040004840c1c1c000c0c881e054440e00c07004044500260b4500c0c0d500e494610f410f80e800c1800c00b00701003003803000181d4800000019040540030f680302d64600100c0084003c0196607134508a045080052a0656280218045192600d410203440e0055902d403410540208a00c03031080e012a811341515048003040d2824171030300560740903d004582030300310300b400b211950fa4a00060700241c204000700f13208180540300c50401c81f4802da801440001070400c4514040d4495122002a601040080001800030092801450107010781c00640c508541e640d0002c03c40c2502e800303001c641e0400340a11a900c40302c0710300401c0501070030b115145c480ba21441c01e0304204120000d600300c04031346d80080c420040181d0f00003c20000707807485410045400c0d51a101d0404100b6140c01034107500608104181d420f20a021400405544811a05001e40c4907d41400d0b9031a00c102d000c03e01e19010307072407010421517220764484580000318400007110503011 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 334724730 1250 334723480 334723483
    0x4060c140a03090507061407030c08040902161202030a020c15070501091505090109020a0306091401020406050703180806040b0403090801060e07030b0f0a06050c010b040606050702030f011419020c 86
    0x1d8194001195480da40b010601c0420000702c0000c1490b49000f00f90101000c040c001107014a58009060001c1d51814000b041500801c0d140901040703101103403520810849981100e5400500390b46006201c40180b12040c4084100d03196214207400030011a007212090040c1c00440c4160201c00b0501406081d00090081c000c11408038050080d8621010b1207800c100c1c1100c4025004011980c900245a00141c84811011046a030005400102a40642001e02807104013881011507035200140c00304039607420901030000103001e50b482da00401070312526003450b0b0886020b45140c0768011400a00094004003100340d120b8403c2c9800180c690344d40c1049c0c2e0a445068020300c40e40048001001841d03a0300d489542419001103614008517011035000c608101300b41d0060104204c400100c681190009410103800c14002610400c50540da036003008150341c0208001b2442402003a0104807590014003d41c06914070080040300d40b5100e0000d183d004845d2041c2071458503400b40441e8425400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 334725980 1250 334724730 334724737
    0x4030327110d0614070207060207120f080a180e011a0f1801020f06100311090411010e031e06010e0c040b09061c05040c0801050c040b031305070806040c0521030304060c14 75
    0x16140c0040c8105418020041d060081c5908000302f86a01d43d20380101186900700300301c41d501c0d005059a03a441415500445050500901400401c40e00780c80000300e000c000d840c0c00b4102e5694070360041014400c64920100c92044107103600d0f40c03940a03c4100820f403001542e02107054414012211003d906001050602c00119a04160010441020014011401c0303901c07040700b0f005c540a01031440d10b0303502d5201d1147d00031b400c2810060041480c0c2000d480070080e85a62201e024211900a1688a1559a00d1500340038a4480c0c4403130001082d0203031f01190566041c2c40c5174059440c00d02d2008424440c181c2c100c8041d00069403108801c1d6210b01c5914030502e80107a0056014a42617400e01500030300396030020707192066412007000f0400a101c80c110030749070001c1c40717100138070216030a604082d80380042d540c000600307502400c020310003082020500d002c11610280d540080d540f000e0015441d120000c041148002c1d0001c000080001e4416880088512220300f89688401c00010054036a0b80 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 334727230 1250 334725980 334725991
    0x2060c010b0a0f030201020d0e03100b03100f02030610020a030c030503060a0e070509030c09090d0507080f1c0c0201020a0e09190e0a0204050916050d0c0e04030327110d0614 76
    0x18800c803c00c0c003c0d96818440c0c90116852414495400c0d615000440e50b80d000e1029080c000c00d0b80c4070090700b865035050181c440c035141c801c481400720f079460101b014020750040e1003291040e00e40b4440840154004544030840c19010346070b00b4081303a01910140d47d664001024654040e0189001080c100003c00358a4007585e01d5035200e5480300c5503802454909403060b4000781c440c644401c10400000800030f04500f107215075207000f079200e0b201894603641078000c1401d03e0781008008590401400402c1c0c07058550035207907134414040142c00c25403e070f0803803081d0311410700094003654030410b00d030808c03400c1c0d00c1d0411049101c00841140d4072451004480c42c40c2c9a852658025110b0b01d010740c13809003d081e0308883c40300080e00c0c5800010b10082c41c49a100d10500c1d0154103411205c0d42030280906031a80280315069204180b442e0a1a00070010300407164141031204801b10b000000c07141802008644681c403010240070000000100f08101c0d206090031142c0355180c0849481d802c4c1c01c00380e51030151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 334728480 1250 334727230 334727249
    0x80727030b0106031a030c040c0c020414160309031b02011b0822080a1112060c120903030f0403030209030c04150312020f0a2d0b19060302060702060c010b0a 69
    0x42d41051002401d94600804c18411040e2014224070181c0d804110b01d00500380450f4002100241d09800342d90f140e800b407102a40c090320701240d00648244403000b0700d2003803500326010500c1070041c00050703044451114024001034a80750800c12122221170943c0c940c0342c01414511519600c64404184418000c181118408808141aa080c0c1100c51500034803640d5448000c240030305002d10389545103403150019201c1c10381400c0e014226224015a50080c080fa942540e080745001d54411501d540205508100842c004d00000c498071408001d0b6801222060028840c030345440e24201c000c5c2d00501c0742294140a0002004190390302c600ca05400d07140f9022841040340e1442c1003107400304c13040105610541d08184c0f0403030a4603c1c046031a0b41065030250b40c42030015040503c00c2c40c0890b01ea200c44c0980402e1500b140c05204c105498288200d0740c000c41484206547c083c50402d030f469921009402003028000c2c03100620708507019013a501d46103800083d030500b010340001c15551055000c1042d2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 334729730 1250 334728480 334728503
    0xd020a030f03030c031506080c0a09030503030708040210050405010f08100807090501090b040606080106110304090203070503091c020703020d080c1207030201060806010e0c030603070314030c061608072703 90
    0x3c10781c042c015501c038200203203110742c1b80c00c0c581603024040c0b220061041c3e10a5200068061705103004000e6900a950010700701c94a900c3d00e500f02034081c402c2550280d00c2400001011a50f880c0704100b114280d0788103950b1602240381a240c15941c0c0b00340076000400140e000000070404e24801c1040c0c0e00100750404011809500d0b0040020840c2e441d101d41d81d010310b00b004028803007190045040c5045615510b80210070b000070a4285003103018540001489030300000c00e00015541c0900a14082c015060940303201c00843c42d800001c0c44c000e600304a0150300a100200094500203040c0d444c95030003100850b180243c101c00c91030501c601c6000d203101a03440800e00805042e8248070f558094150312004042d2941000381c05145200b004100fa10040c40c000005110b070b0b1010301030180216880300442c1c102e4215213445644035003284401c0c3d8018840d02000400420000c0d8100c0c0d04691240c4802169845009040fa040400c62102c181c0264485014441c100314044505000754040d01d0308a41 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 334730980 1250 334729730 334729751
    0x405070c1e150504170705030706020403080913090507050103020f041a0a091a03060f19030c1a0301140904030c050a0503030109050901051b0306030a02041d15070e0d020a030f0303 79
    0x1200c9411030940d82c0d10302010880041c10607100300d0f48014608104985500303152a0051562103000001041240080340c008100001103010b444021003c42d0001c043c02904c0c4202000c4814219000c2d11a0b80643c01c10041940254020050041010304841ca000c0d01c0701c01e42014030914280c40100c0000014140c240e883c0e111805070050101c902d0404090308500a0001f1540805440c0078421f203031200540e200c0e40d86003030003101201b0507008181d140541e24106000b40a041d8401c0d58642240041c2042c8103250000440f816070711101401c4420030748031400c0c04a01c4000810450a019000c1142404100308111400307031284074900079a074035810502103205032000a018514140e0505007803144600340c103400000216070040c8500d84030f0742c0c1d039000a8500311802c000650894a000ca1004034480e40040c1201d036441310b2401c0f598001c0609991500d4a402103d120b0009400b1041c5544e107460300003500706005000078082c0800035140d4859840d0409012400c40c04281d84000c0c20b0f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 334732230 1250 334730980 334730993
    0xd060302042a050a020604150618050402040b0402070503070b04020a0e0c09180403020a02220c02010b100f080115031407020a0b01140105070b06031608070e010909110405070c1e 78
    0xc030402c002e803034480c0c101408134401946d540341c0604020454032000e008054600e81980c08070004120600e01c02040540319000a00200800c0d10b00380e0040d0306100824500e0700342802251002903000e0019450403c0940f00d100c3c261902a208030f030702052040740064019010000f10340191015680183e07911841010002980e0080c17400541d00701c440360800010076004100c0381c02603501035485c810030002d400128140c00d040d440a1001d228503044d40122180c3c1d05510560800b0025208a03420711000c44080c0d510030701013800c4a0000d00c04034018080c2e000c200f01c0595500c843c6d42404a040700f103aa12808000000326003410040e4400b90311801404526200e0500414004c00b0303060034001071400003000c0b803060031406040c101c80d034004100940c50800000c1298180b01c0c1c90180d045407260100c546481542c0711f05140002500c0000c16122202d02c15003201c20b030301400e071403100c0d0044d00c24003000d400014031090501111032900004912802030b0103038040400b0002007003a64852400d103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 334733480 1250 334732230 334732301
    0x30a0605030a030c021e03011802032103010510020a020913061d0309011d0306040b0103140106271e1e0504110f0616110108011d0a020d06030204 64
    0xa220780d02001c001c030b0102c3d411044001c8296010340340c10080b0194048400c1c0309101c414121905986021011504403407403003000550540b003181510728604000342d214500d440c26001d8012400750800c010801031421300320042072400240140c0744510303c260002503210004a49664090645104500801904e441942c214107210000740c090780300b000002c5a981c1c099040380505010301c41c8a4001484c1060007001203014004007111198501803a203090714840a2004440c045081c512844941806001e01816501c2d22458019a8010703415102524240c07038030599442c0c0c1e51420307540e10910703500350b1050584040000204a01e14811410644030301890907400c0d240d4038010a100000b4000c412000e081070b8101c0c1c07141c07205807015000902070300c501d000030105000b00441c0c05040246c44190340300e4201098980841c540c2c3d0f07500710180c0e212407408680d8035100c0390b50001080300d441540030340511070310b40500085042d103940c041400c664101c041d402c00b80100000302c070701c0401c030307043c80 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 334734730 1250 334733480 334733489
    0x609050f060711060903070314010207060c1b03080a11030a060e060f010507081b10050916031a0c0c03040b070c050a03020d030c24050609070216060e030c090c030a06 73
    0x30140342898070b031100f4010744003140e1500d200f150b002488558690b42009a0400307160484448400310038012003850003540b141c80100d41050824201c1c4e141c85002d001c031080c8288440d00030411803030300741c1d404903490702c2c00811002505994040d0348622039500301c085e51242c0200400002d505050000400c0d80b004014420b61003010100900102d81c0d03031090503115000d5000c1c02d015200c40c8900d075002c03505107031070404001034801d03ca0b07590111500360704000d0107a9041e4096807031514021303022001910705030002805009201c4544400c500c22089104c1e4449400c10b0564248000e03001454115806640f084003030400200341a4148000d1120b003c0c000d2108031117020500d450355000c54a040031880c0b000d814401c50201110a11a9043c0c50405859101d039540707490421546507200181802c2e24818040d416220029200303e000044411100f901410318890380341c40d28008483c00440310030416014084c036640441c198070341c59400d6000b1803107900c0700d03070b2207107824107640c011640294803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 334735980 1250 334734730 334734739
    0x507020a0f1103120c070311060c0d12230c0904060f0603060f090207030f05180d060f0507030b0f0f030c0603180d020a021c0602090d11030f01150608090708070609050f 74
    0x5c1c5a0100c100007170014112076010310800c04441c80f80000400d5809410006140c078003d80c034095a03c10303803180d0140000700a0100070466000780c085410000c0248100d02551180708802007000f0100c004041c1000320002040400c80c661103405220f17101c517145e84500b02281c0c4603030b003d00c95240c850701080050418280f08605046460700c000b80010611507001052040028040e044590070414a040301c03d001307841a11050302510b44a402000b105807001c09151404011802e640e10038014602c0100d40181075802d00080f44040100290440500300c0e03041c40b0b08001415152204005103229503292034141400e0704200c41e050b410441c003800d90200319001002c00d04010ba882903040034a44613450740590080d5042e1410070000d10407111442d174401d10355065003003000b1208401e00c008034020703410b881480b9056094182694400350590550704003101003030080501c06c0e14420350000c0500c0460b4103180d5105456400c1c030b0311b1504103d0001e62a10418041424095518980c4e01c80640d0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 334737230 1250 334735980 334735987
    0x1506040f0e0f250522241d0114010912050a02040c0f0504062a12020111090d06050601050f070b011508090c0d0201120e1e0f060103060507020a0f110312 67
    0x2079070a4070300442400f1349886064285101000c46402100702220803035a07100800840d040c000c1810180035054200c041c041030403942c007140c1e40e080e24692010303003080303165080c9580c0d00301000510302c551043c070901d040000084000801d040500d42c8895554001c90207806407211500501080c6c840c4807100b00c0c144200b03e0310b0700911551140442d0201d48161900381b0342c80042d810316007a50146964100c2e090040b0010ba41c0a00910000c1029440d502e50020400b05408140450103401180c1141d40d00130038101403000072500d160051580b04905250480c5840028155014140c003c83c109030341c0392a881d0010300000f90601c07400c482d00541d50510782c84030300d01b801009980d1b400b039003242800746100010040031079000d80b040c42691401c1d0f81d010b11100135545022666000c896511071001e4400b003031180c0401d00040388950030001d021000c3d003da0b81c00c5455160107003101030810021441024902404141391001441700b40d84954200c82008400b801050300e03001600b03030003546074801003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 334738480 1250 334737230 334737283
    0x120612080304030804031803120809072d17060702060f220203100606020c011d090412120515010e011119030504030503031815091506040f0e0f 63
    0x91041d01d501a61610b0146030f195114901103d02400390f0007a15811551488080100008207040061020041d9100700c0296605c1610581d20040d40c4280306840315062604208140081c1c0110100c81c00008800d00140c0c0d541810460222100403190f190b0b003008051095040d814002140c00c0b90f04000040654107041c0c0c500807a2111414001d0315913074802e20640215101071100740c65060508a04011f00c1d60f03540800f940300d03080c140840740002c015100700040028044006025450007074000c420340d5407565a922003c2020032180302c00d01c2814607044c5201d039900d0184034401c111482e032034084030204c41c001401c07000500e08003905000b4800f030070011f641d80010304500009000702d0b0605100016040aa80c2440380750400b42c01d50100004100c102c40b1050400c0354482c0c0c178070b411a00003a150400c1c0d2800e190007503032030603020f0300000c2d80030603045070f00c0d0081904083d005200080c00e03406695402c2c05c40c0c403180b060000540201c00d81c00f650407020310002c502600780100031a50350790380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 334739730 1250 334738480 334738493
    0x11401080a0c1202130e070f0501080f07050306120106090605041a030d03020a030b03100603051e0601050402090a090c0305040b06030a080f031005211605010e0d02040b03030703120612 81
    0x6000c0c49032480a0703400c450f0199500d101740c041740014818402c00480184103d49030302c43c5054080c040322000664000141d6501c9081040e00c2040f8130440c0141e03607181c1401c1103c050b4405045103034013112441c03003041d01c02428403800c0014080c0c4400003c043d0b2425003480b042d1440c0180c190f8802d502d50f842108240c80124100491001e01c1c58011381e91800d008040c0d00524072600034541620030041081c5440b00154040829a0301490442c0c0612441c06200e004a081c180c00d22481c64021000401680c1003e40180c0f043c814010418400c0c03e4070f8500550032a00c00c201400e00107a00d900511051009842c041500464190040d107003e00090300ca00c2aa840b640450500000300000020f84100c000c001240282200174a0386281030500c6000480ac1e84040800c00807501880000406080444c0c103203404903501030311411402c1141d0340403c40142d4142c0300c20703600191038040450060342d081c8000c0c40030501c0b81d10303000314104038101c05a0480e51142c004081d4982e4082d00302c1d011409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 334740980 1250 334739730 334739753
    0x2102c070f0609031e0201020115030c0f0b0309070e070c020d050105100f05010e0f131409010b0301050103021c0c0f08030a17010302010221120103080a0e0f0907030207081b011401080a 81
    0x17444c0d1013060303000f425440101d0040100301030885d45455020008400c001958692904403800f01c07028644158072001002a188404d4800c0712070359000c10780800a50480f05100b41e4444000e090807001ca51258010604e10f5981d6101160709035901c0b403c2040d44280c420713560015050000e07101c070400e410000040c00712007107076a480b0b00c43c0383c40f8490303031000e030b90b40000b0203411131403480b8240300d03084000b0080f41e50100156551505542011088100350030144907280c102d0f5001806d03121f42444d4550690300a03000301e00c00360b419139225403003c0b83d68030400ea0b4420043c40d0360001542d0780d50802034000c15400060300c1108003e001c0c00c0040000d81e07030024140111462040d04007402101103043d4042900c00e401c50600007030b207110000801d005074170014101c4100140c980b201042c400104100c01007034203c20003603000381880d0118001074440d601805400b80b044000300e1521943c0a01030b600c17800601c0001c0242d80d10307810804000100313a81c0d014010541703a40144003484244c0d4400303c0360074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 334742230 1250 334740980 334741013
    0x6140108070b1e0d0605032a04023006010e0306150609011b061d0a0b041506230a0609080705190e0a05090d0c0302102c070f060903 58
    0x180c2c08941a602d40803010031a03c1c4000c42c44083d1607031103944513425400340c240752140d684a40520f8204807100c120f50010002140340350744900d018a014a001c20009401021440c0c11020880c0c5041d030844950a17403168030400c240200400d180342c1140014142840c0b0004680603030412014040d6240500a031541d050380704540b01611030103113000480740d04200041e00340d0008000301508040c01003d901c0050710a0550f803940c5110391310440111740d0b90401700300003042a60340c0c0000602061045503440916030b2680c40205280c0d236195603544000307070b2140b0702e0201003225025000452400c10403141c01400303a0f080171040c0310b01d031920741d60711151640314860152084804040380850050021400703064503180c0c040c0715040407507454000300403c413000034003803180c0c40766408943d010b044903503101641a8010000c54103201c42541c080c000001e0840c44000410361005c0014107140b04882e0398a07499401082280d191500e240d2401d80d06900940a0110443e003e201180305504500e2680 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 334743480 1250 334742230 334742249
    0x2030403121403160201051503030901030c11100b0f01020c030628180309140a030f020609030609150f041a09070902040603060501020f0102160b041e0c030614010807 73
    0x38441c40c0c00035a954881c0b4a00002c2e0300e18000704201342444044a001c903090b40507402003009a0310000311111441210319010341c1036009200c3c8003e1076100b40c000d00b0751120341e0f103401012143c0442520b40b8052401d1101e90465032282000002c03400c0c001540300991000340b009241803402000030039210100505100351400200d44401d420070100c0400042038100079200f000401c0c12403401031050300c1c2c920801c600240c10100c1c0090041c0049005030869040101500321041c074558501e100c0c07203c80c96049800071800e0111100f29030302485414414040b0710045c040340a94143e54410008001302031480c0c414000c000d200c08281042401c500307040a456114610342c481c10b0504d0318114803503000344600f500016010a1003680340d00000c0071280c0c00e80843e00012005003104d4280c0c002d500050b4000700d00130703100c513010403c8955183e41190082070304420301c4900800a03180c00c9820725081c1c074540019241003040080707621404956018103025250103504220100784c680c1402c0c40b900500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 334744730 1250 334743480 334743503
    0x4030203101b1209020613150305071b02120d020c011b030203031302040b031f0e0303090a0f0201050409050f060f01030e060a05181e16080a0f08040504020310050406120302030403 79
    0x1c2001d50380701c00190745c0c0003001c4075260096040c0080030420f90b40100780652601c40548021a406406800c0c022005920303040e03041d4500c10780300940d4a81c009000c0c1c0c4e00c0b403c0c1d81c04101031804140304890480c1600d074041c1c11140a8000050561289041c95044180301c1c110b84401280e408410f50b80c0140380e8841110855109000083c05000700c011519410700503004a410344c940010502111502c00308001d00001c844072080b603480e03010884450b030311074011b4a495800941c0d440c0100041030310505042d420542c41d203000d5011250202d5000f80f03a090054180207845c5401070718103c070300c282440c0030b200340050380882c4c2c0c1c1c0b10280a8005078441d51a01d01061000c20b03180c5284004a40f9507084900c0c6085507075203017506062260046220340110b211030000e0b00c6030620700c8800d03102020002e104a01e420340d18202140b499503000e8650a07014000869160341c1c50000310b000c0c0c450303006040f201a050004000454229501c8503c80c00b0b0100031a50000e500801901c0c201d07a040b610303110b203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 334745980 1250 334744730 334744757
    0xa080708030a0b04020d0c020f0706021e030f03130302010b061801120b040905011a040c020703030809070f080d0f050a12020903010207020409030206150604060c141002040b04030203101b 82
    0x60300f070903807103140c3c031500205030110150803d51111541d007020ba42142c00b81e03691403480f00d07100c0300340340581e00050700700c2c0104518403022016480f84038036101080f03c1c5050340c56841a0a6a00306413040d206099140c02e41d1020f056090003034200b414001c6980034907017141008800e4201981500079414000e49100c1c044200460b075100f1008a0800380c000d01caa0661032034003038004c20304ca050507400c4120f036a9040300715013000d10a4288088803138004000072421f41e2415181420b00414181840c07241400100e5200035915429000300500070041c0034144821001038003440d40e42d420300082000510900683c01d07440003041c1e103130b100d0700c150069864804401080c0680300d000c501030b40183c01c00c02020101030340080e4162040f007a9440c0c040b40d071240e9400b00a16407095208000c001a4541151404a4141801182681c01f01000c0f103100c3d00345482003200366081681b06503803040d070202c0c0070020741c03c05211a1071403001d800c0301008100440381d01c603242150140051410016040c1800e070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 334747230 1250 334745980 334746001
    0x10e091b120a14070303080c12240a0e04031205161202040515031806010506120612062502032503020a080c060106121404020111070e010e06030706020a08070803 71
    0x1401d900f1078609400d0705641d00c0380d43e0b035803801e40c0700c2100040d100d800000e44040b0040140c030a15003440640e21030a40f00d60710325000d13501c00c511000e0003000c08a13072a00d00c5980c55400e02ca0041c0f0740d510340094903103090304018100da5403040e0076401141c02c04042029032488500800761200d401c3c02e0460502099509040c000d005641143c1e4000901c43d6031216030110100c0a140715400100c94603040d504100e40c00b40e16a6030030720034540c02503810b01144488860401e40a680000080c060940100200c1902c9251100035648400d0985003001e84111505000040604c1c40d9254001103140101b060f038074103403088580d1100040d03101c0100321b8408040c420b01c15184010340000c859500c60020301c1481c0d440e0b40c0300707110700000709002c420600d14424590259054805400301c040f9415515900155840c01075222501090301500802007118111446400e002c2d003545150b011451428901349803034020940c00c414199803120a0510000368400b00312244664011407664032526904000e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 334748480 1250 334747230 334747243
    0x70506040813170f0705030706020303040209040f051506030d031e050702010b0a0303051207030b06120421020102210c0315040b0a060f02010f0e10110706060e010e091b12 75
    0x610640380f2030b501d819040c000000c0d415068002200c240e07804079030fa443c201a40c81ca80c41c41100c015820500000340540b8191038021b07400f50003840b001d40c10341603135600e01d0308020044101010038071804c014403c40781020060001c0c4244d031405e080100329980c0e800c0c05481d10040c080900e0194072407000644591007904010400c000c060f01c0c56590f02d481f4503000d4a40d8000c014501c9031440c00c00001031f0b00600c43e00424000703a4020b0b01c460304e0a0380000b0302c241002001042550149007801e485500e64031110704040928400358001611000c074031038203900032007003000022074000c02c070818840369a80c03030070440c0d401013007036542445812262000305024005480780b48c0d60201104c40c001401a0704045180c85030340c21540200b02d00d50282c0303031007011a201e12501e030308203900020f59030040080680c0071801c4101506245401c01090303950728001c1da00590400b8030301c940c0c03180040101c0004452141c0c0c01290400c050304010300d550800e8951640291903080c407856030040340d4101040d0a1044 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 334749730 1250 334748480 334748489
    0x1d0c12150103140d08070905060d0b100306031b081509010e07062d0e0d06060f092a0203160201050d0f020423030a020f130f0b0103050a02070506040813 67
    0x440456680da800d2100c1500c1c1c540c05444444d0041070740401483d441800d005114172400c0d2103031541d003030414050010304d4008041c0395101c1035036103040d05100c1e40ca0554150a9404c00e41d408601d103801e602d1300d03100880142d03150500c10b810a60b028813007840c000c60171410b02c510480e80603105580d001741c02405043d4460300c3c81c13003500480c40e01056903907008506408801d007918440d080307100341881c0e0300c5641ca145200400041c0b8003595410380c52501ca42e60048550003840041b42d09510341c41e0303054020400b60b10080e0100e0761410030700c0600103015141004d52000030b061031464804440041e460f48511250385000140304180401107a0080040e54040541c915041122022403121800254000e008035070071a210300107801d90190404150030188200034020b02100101c80d803e2023500c0c442c00700c00550102c5000040100403106d0f116414020350700c04004206204260005022500050002c4010341d00400c09036001c00c2c4c0004040f900264401c00c95a5203003040b0206c90160304043d0030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 334750980 1250 334749730 334749763
    0x21201170304091109120c0f1002030f0408030703080f13021c1b0602010b0a0513050a020f0703091a0309030a0c110d0c0513050108100506010905120607031d0c12 71
    0x115070f001310300a0141035004002ea82495030000d514031416a03500a444400c0ea100040160746082c2e410282a6201403680500440c3c0c148245a942950b060b0010341000406910105a92050583c07080c180b80c1c101d2215100c429103820218030f074a4056500d1000070380a41d1441d0215102000012010154181c11004000580a0010b2000703040c00c407522415006608003501c03001c15107008484d29048440c001c02c1c02040e41350164070701020f0700004080002450b824041d0318003821084c00203202580c1b107079a0f0920803a052024064511074a500c00c03031000c2c0b40500800205100000403108400e00794200300c04117105d40c2c941750048030b0403000b00503000898000c5120801251001d000b054950840f8840328180c1700d00d4031407040300c5092103201c2c00c645c84494652601225540403540014041c540810255100c0001c1110340e5000180807907d68008000c000299a151180f0010950780f03441c07460310722082c0360509070b0725000000c0540c407811142c0480c1705186420044083c00804100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 334752230 1250 334750980 334750991
    0x140d12080906010b0a0c020909120714100b100305091002040b070b0c030c0a1107081c031a010f050913060303021c020a2004090c0f05100302120117030409 68
    0x450042505034141c5880d00148510800440c0500502d010348021640f16600d00800000e03075000c01012190143c2140340d01c1c003602c2d10314110891450020b00880b8051300001c40651071840b2070500d08100c0e00c00b02d411117850020303548800d64509003600c00701d03829840c0106082e140e0350a900d05107240c0450542c1018400030700011540c5072640500032040c05084103100d240e40345e00b0780e076240e03110407610000700c0c3d00100301c201e02d00e5004605600342044200125a121511002000d14040100c0d1420b50101e008200654038694107015440500810500902c0c51990003000a86148001354103001072040c040350f0040191600050242d150340b080741c0c10320207150b13281806521840e00d14142c3da0b5a48601c400364022600000340021038583c070042c803820b005600c8800c901104400a80954815181e40f0454007041c501c500c2c0a000c4c040c511003002004d49001e04100c049501c2400c28030905006100925035404849400c0381100d01c00c0246218031843e440c0e100341584100d400c030700310b01450705 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 334753480 1250 334752230 334752263
    0x708061b16031206080a15021c05070e040b01020309030703080a1112030103110604031a04080c0105070201150519180b030d03020403020f04050f04030e011e0e090f0601020304140d 79
    0xb11407180203c4145041040b0381e22000342e44d88484083c01d001c0d10b207185e520529003819800358010407a241e01c070160044160305181c0c41100390703401640c441c00040c90b070756200d00c8540340500c2004580354090005516107020b000200c0c0d2644024030010301301001c04107200025600034001c40014138819003d40740d2140800344000c2098100780419102a040d003010000281130441c21a401c0d650031100250500c4070740c4c02150868035000300211441e000a00c407043c010082402440c0c090b100d2900003080c401e040c0940103880c0d9950703602c807e104112100d44240000c0da1202d80d8016903003851402040d1000100081010344030818034aa050f200302400b200c0078503803660203001580c2c422541e1031910b00000c8100003c3d520180c4e00303001401d072040040b800290282d030084001160605100500320f030102c0010385034106020740f20021442c0c28601190916102d01803683c803c50180b2f54a80071b0400c000000d599005a01911112400d07010445086648402c8c2494089034400c80d8400f0040740c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 334754730 1250 334753480 334753487
    0x60c0e0a0308071703010515030a110412030e1c0b06120604080406031a01210b090901020a080f01031a130b0703021b0705131104050a06051306020708061b1603 70
    0x2411051342c10007004c01c024035107800480308403412158000c180c4610007401024402c2d90b94805051411255992000c9031600c4100c0700103400180f8007444901d20740240c600700504041c9800e40c40d140f06011a0f918070300c04002c601040c01f40607401a0345050950741da000814610701304d80c0314180705440756600700810003d07c0030040040d2021a41c040c8062034650700700c800c00754018086980411501d03202201080d01383d01d1840415520740c540443c03400c0c100d101040d11f0300800c0d00d107080c041c4d4000842505680d004145650080f0400d5001c0c009580f45459494424811040c3e0b2420484403901089501e03816480d00001d1079004846a2428100042c02400070f500c034448040049002090a041081020440d030040f00c0002d00440c10344100700c0c012000034080034810072001c090038031020900e500c40e440381e4800340401e03071500342d40c0f4160340e01320742c1c20360322994071130702c11075003c840d091000320300110313425800c911156200e00e08452030728000c4139580a00f03445d0000001c0d1b41d0000d5414140d2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 334755980 1250 334754730 334754737
    0x3010f0b030d09030c03140c0a031b0f141512070801170f0d0810080709060302150403080a05070c08240a0228030e0601030f0507060302090904060c0e0a0308 69
    0x304404641001c2c2601000341d50146141c800601102640c100406c046140018800d00b4141c1040694801440800c00038200c24202c0c0c0098a10480c22002d9481030440d060500028001c44030008941501c0c02c04107184c0c207a0420802c9001704200003c041c4030720801030550708598049103104038a840c00240041100320309101d40000d09802a040703d240c1d2a000c5100d070030b1415003e01a0401d0019400c06480342600030b0146c40c07101c030890000250341c20040c4032507070140084010103e0340c2469401049090064000680c440c403000b04410000200c0043c1150034402142c1080c0d0b49480260600b22000d400300d134003000701c0d80510416903064401401513151100824149240c2c50b4589540101c01c901403420100c81048182d1a03280029202c43d88482c2c407541355107000720700d550305100300c00d05111003070b40100c40c030a82c04d40d403150800409200000181c1003a203000c6003049501c2c00010302c1050003910150805546d07028103518103202c0e40400c0b0860740003600d9080581c1e941d20302910300c0c4c0d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 334757230 1250 334755980 334756001
    0xa020301050a0e060f0405070807230f090a0c1701030f12020f0705010804140d050315010f08012106021908060906060f0a0318080405030d0305040312150503010f 71
    0x5181c07400144074a0311511801c41202e011074001c120965805a041c10340680c050003d98a910600720b0010300f560081045c94058000d001d40745540f80e2500e0094401040315294040c840d910500a00301c3e81d44401600070f9001c11101d00102e0220303800b8178203503041d00c0b0846c00c0221800c40310f0004014850305014001c0b050b0311428010000704000107007281c8802c81401ca0407095081803108001035031048450745e4025004400a40f080000c0c00301091401c070004001d0320200c1c0c03000c030400142d2160044a03904046080c2002d02d0803041c100001045038405000d10281000c0f003094a80f028050070301d008692540c0030008540d6110309194554610202000000c00181524001440ca0500d6444903025031307400f822803400c200405101c203030150030000c1d00b001015541c2d9035454420580102c0086014000d544a95a40b41403009040c10940d0b10320024052506002c203110000b688080e88041c2c401c0084000070720300d5503840780f41d003000c0d182d41d10840e495030030001605202c5001c4c0c1e000d0706003070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 334758480 1250 334757230 334757233
    0x5180d080a020d080c0d1e06141002030301060806040e0a0b0c04050a081515190b0403060501091407030b0607080f030a0b100f0c1406040302070e0903040f09020c01020702120a0203 79
    0x146a201011104c204046818481280003804032010910071600421810510b051100c02c81c8080c0d04159400c8034166401104440181c04e2080c6803030501c90000035070b06540380f018524641c145400030b8003032900a03120314012541e0300d000c483c0d2400c2c2488089401680042c00380c040b170403c1100101c15030018099180700c0c7c0c1040000103520600019581040e107075070b003103820042d910107078a07050300420500d4454029600d103078140ba8450080700f0b954054504200311948450440c00c0c0718080722016008078503003910300b40e003400b4010005e5040591100b000d2401107040309503180440e1541c069000002c00300752000c04c492900c0c0408601441c81414000c40c10403000a8480408c0503a000070118180480e400349040514640300d0071044c00c030b841c050414600c1d02d850040441346884000c5505400680007128140803507141c1591071034000d18014000c42c10b082c1443c007060f50302d000600c106a1440d50001e4001d4610800f034040c5d56507035400500f0015000d0040c0c0c1d0050b1a6900302c1c0c0201d00c00d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 334759730 1250 334758480 334758493
    0x130f0501050406080a1713080f01020304050d030207020d020d0c150305060418020a090509031b0a03020c1e0402130f1211060f040302060901030608031b07080c03060705180d080a02 79
    0x2500310000744101855000100d8089400d0140d00d170f403102c6c0d40402c0104c591f40001100101e48130f82d080041000c06020003000590f00e11740b50030518145441080400109030040014001503a030303168501c01c0254044401010307074111441c1c4810154442c0d40800b49821081144020081e01507100720311814080d034042c004403100401740051500c05410095102040140500810329260312884d4003209580c2102d280850183d0402c0c1d01c510000120358050b4005101442019818069982441002c0d03a00300541c01209005009466621000600a0380c0c0426900000000c06e0f0011005000c080d00500365141c45856a101002c0208025030740041c2e5450000c4039400c06078220303044598409803d50401d41141c0c00c22981e5409001c50904168840d403001c00c403010180000d104000d2403c84484044100e0200c05040409681c0401020303000000380b8441c684010510340c0c2e000c9001c1c50074030303541d2024407480d8455030490050903400c00c0c0d10700d80030800c004d802d00007009801010b80031180c9 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 334760980 1250 334759730 334759739
    0x409021002010c0810150c0305070803010f06270b2107081e090c0f0d06060e01080118020d02040e190b151207060e0105120c070c0b0a0f0c02130f0501050406 69
    0x11765207140314041c041180710400891041c480d5105081c0b41d442450400d00d01000e584520006070001c0c1c0080340051030700c00c07042100c1c41c2c008000052100070b461002103d40100d40e480e5220507218807a0190001001680d0100c140300140304104250882c06602280d040002004081180480d8500100710704229a6446861030800b054401da5030100100103140070f41051088100d00c403150190809064003c01c0300150850294202a1400000070007141d07240c101142c0c2913510709034100d6402a801419600507031035000b98456215010340703010403004100e03400ea51500302c044034210740c3d200200340c41c2002c00c003103814014040c1c0000000c100f001050b02040100005601d131406445030300c43d2004200391030041029a07215803050402d42c0c1819400c00302d500148004585403c034a110014400c0104104000502e0161107031540c840e0400701e00d0607000e480001105c40103428030000516206c115a21000600041000c0740c00610006030790b8559040900004e00030782c2d105504100300401d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 334762230 1250 334760980 334761001
    0x1140a0e0307050604030c0f0503030a0504331a060d0902040f0605010203090111011d0c1206041a13080c0c0406081c0e0d02120a051603200409021002010c08 69
    0x3004650850003500045c0c442c3d58040e11001c01c089811211030100301184804900c05101461042d10a4071000c1190720302480c2c4040b0703140c0e101000d17600c0e01005440003035051250b00413400d0072036811302000940240e581103820322a071816010036885180092500d181c130300690881034034a442a80c06009601541000303070265241f90080c640107030b2041c80750646a43c4980003a089180c24400001842c00114286500385030500d84001d0490384803c41c0e81401e800c00c81040e8100082c4900907040509140d5185c000308208040c003104650041d80100c1c079200c41c8125075180c8aa0b00440c043c3d6035010340707080f060b1139070010582c0074070403850207000043c1220046001c0c0b01d038440810544031860a1000262855010130a1040d08904001540c40068403809004604010804001c1207950114a041c070300e00380815502e08030070345408404000007114101002d500d42c210342072401000a003540850000d06101030069031002400f61000b180f55010f50010982030125a50b24603d80c0d151003004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 334763480 1250 334762230 334762237
    0x28030b09031207030b13150302030f07060509100504050415030615150c0f0b010305280807081606090c0f060e0f0411041a27091501030e01140a0e03 65
    0x8400b058044000a210511a03030020342428030061202c8010000340540c8012a81c1c2a401030b8612082c0740d90030b109604d000c100000c06044100c00411345941030150040180c002c0403807580c0254011101045820700032801e0301c0161501030402c0000014110380070349000000e00c800c0d00e140e441e109000c424011980c1018054551802c0c89a44103146003008981c0703600030300c0c01602d58110340e29103c80001e008050386802917000f9801040300c091450501000d5004421040324070803910700443d00001ca42200382c17508243c200188603243c40e402c05c0050b0506c80b00480c0205880e1130300522100304241806520140c40c1c40700100e8000c0741c1c40e01010364122480c80e602e550710104600d00125146040d0f0402e80300741d0410403107682815500d841e0216480700c60303050006482c00104003007201d03103004541c0e0035400b4550000150801c03414000716944500140107441c0d001085408400340d640a5001480744070400002001811079035803070113500040a580060004e030404455003140003000040c1c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 334764730 1250 334763480 334763497
    0x60e0609030606240c0307060b09101802040902070c1e0b03010b07060204053604020108041502040803070f061835040602010b0f060c0c0f28030b0903 66
    0xc11050f2100410020f5003182d4000202c4404140030180b00d1250043c005400d9050904000f1515440e040c80c050b4155546810410b01400b0050208180d60b40104100c008450b0382c100c10070b686e24460340d000300192085402c8504c8450000801c1c200f04101c08503900e084030500d1010b001800401c074008000e1406501c1000e15410040c401070000c0ca100c0c1d030003416000c1c4030f0803005180c250fa40c0301066038a06c5c0010886504000200c0740200ba1501d40c070315809202085c108001a4905503002a051100180000d044000954000900940c6990468010b04420000c0300e440700c846240ca078505d25120f1404442081c1048001d00c8840a64890756425540c403501340b0444400c5c1c03941d2003040d18550656400382d07010b8086821700c480d030348e00010005000c2d5503001250962201c001c0c4503003507040da511580103400420480c0b0900b8008140450f01c503004844c1a80360005800001c4c1d5a09014501c800708c540c11900000000f0a2184000c003c40e403040a41304416910340910b1901c0380070b01d04c00d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 334765980 1250 334764730 334764733
    0x8150a051b0c0c03010c050d0c03061d060109030221071203020c1e0405040c090c0237060c020c01080a1e0f3e0313021002150a06060e060903 62
    0x10165000e585a8015000801c00d0342e04880c1c40640c2180004e0a49200603010401704000190120600403140542d0420701e502d82414003069140841070b401c490420200c015080f140c002c0480e54503881031098600640d0000c0030007000281241d1398540c0d0082c1c82c8812490391181400c000b82e80000544d00495444c1c041c0c0207410010309260520102d500c0910525a40c0400f03118030032450794540c810f16018501500903442c001d810700d141310f0121210b81d481201550b100210400389034040c181c01c80101540820628020303007040301c3e03074041d5401e60040203204c2801c007588e40e4030069001071808010300e03099a411b5a1512105860400c4813800c0a1458850801208501d01c640a94000c481582c0002c030340081d5510035112081d2a01f030b40000f000d81e821034121052101c42e05550302c031074401c4490402080c95401c080e00e41008000c2c189030024015805400e41c01c62490003480042c030b0312086050180c820b45008507544e8000d288502584000c103002842101c80e03800d00c8816110820310140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 334767230 1250 334765980 334766011
    0x1d010c0c021309080c0a1211011e02132403060509040309090203071101090309030b0601110303010e04050102070803090a020907033e0a02030301140f090f04050a0c08150a05 76
    0x220314409088610700c190384d030b42d0040180020441c01002200000b501032411f0310100c0e41400c0b002001c030340c806001800960305004a40d40f4000743c0800c0e0881f803a41c2c0400040c2d44003154903a410b11402c40f540441f4403682c0442e04054440b0b00291600c0e640015070307a007000003c0e26081001340107001902c000e400100c070303088184558801030740210b40217140d0b42041941a900c990740c05080d2800480d00b240014a108001c20400002440b41e0b0303040780c0c003420031810011040302c00594a000512400e441c1c10900400f15092060a604559425030003051165880c54841c014540d41c02c88420128068042080040c04051081c8209201c410030307a01424155454a41d510100d080030409610200f4a01070742c4501504e000301c0180311030744407900a5a201e62505011030007040f0340304038081c02031013604151045070341c1742039800764072940003070702a1070301e46a0b41040d40c0340015690b401003001185050100b00d40c80e000412070329210590741080c41c250f568024a0041d19015a0449804000700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 334768480 1250 334767230 334767259
    0x103050604030c0f080a1101050c04080309090a091a1008060609070c1103063303030403120e060a11010b0409020f1003290307080a050c0904080d1d010c0c02 69
    0x80a5083c1e5050182d41000400c100313a0700e070816103174454113841021420003c0190b14107030003801056884620031101500785031030045101d450b4450659117a10602040000070400140c5a200300101c44e00410041ca941300714000708040c485d02910a203111142c2501e0000d016040011114805c22000d010b0100381c1c1c6800400b03494841400204492810b0000b4503448181c400f001040d1148d5600e26410110744100c403d122074180020340115015548040700f8005d5480001c121000c03039501c6a5014106055100d0840d50003020401440c2e02c004009041a4020740c03025a07210a4003110008110501401c0b04100485009000003500800400c0d1a071655142681960900810300e003008a01100c1895140408148801c83c1e5000442c102c1d0300c0780d059040801195004d80030180c01024400704680320283e032021040201d51007402ca500010b020080400e05556640d06030b2001800400074800c00390303003545000903a48426628144412107040d118101c071092554024000340e080c000038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 334769730 1250 334768480 334768487
    0x250f0905060d08031e07021606080408070308190c17180d0e030c030601091d0a110405060105073c080f0a02010912050a0306090c12091e0c0509010905010305060403 72
    0x4020405e2a0420f140f80712602e0f201c1540c9a202e2081a0f001c1c05510b2030041ca4021109800c0d0171003801c004c003082c00c00c00007800c42000c8407141030301810500c1132a80e0f40c20041c1c01d4100d0400307442c0c3c08141015001c0d07000c0794000c003481c21009600d1030144250399480d560048460030906403080d1a510620140d04200e0080446030100d0102a00360342e0b00050a002003817820b07100f0382c005100c066613207400c80070030802802c0c01c80c00501d48030082d100a0704241c4801c01c080d039074180c05501c1070303035201c0100f000c0d03a0080307044451055200c4001c000c09101102c600300e0440c007101907002003c00d080c02c04408000740c1041c40c5540c2e5408400c581c02e141c1302001008442d04018241c034103566a601840c800308441804003100341890b0341d10b80d1b990b00111600202076036902d9000020342c5007441c0700070341d180c3c1c2c01071040d1501007041c40e0009200e101500302800c003454032040312040303c00105409418060401d4204003652415903221807540d0382c80d06801c003114024800544660013a00c04100080c0c030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 334770980 1250 334769730 334769737
    0x10f0e1002030d090b06040e03120a110915180f0607030e04060f17101512150510031a0705070201180b2b0e030307050a02250f0905060d08 61
    0x101c0c0704490a041034029003100725042224150b50820700c0d8002c218141c41d29028801c13100c800e61026500708040c80203882403980c0060703c9100c800d903c1e411441a1a00c4c0c99047d034002c3c02e001003004d08002101070998290754044502007030f201c040d01c5005407441c2003258400782002400f4103a1460220140c504590000c190403100b40d210b51030300c0001585221a0003440098440210a43c1c00300002d6517806240c5010740400c000103d0602001e542c2c400100c080c558111021218200020103041c94842c44d004241403450080d0391900081c002c010480035860710540c2d10a40b050000200408076040c4080707811107010001a07401c00c400700040d481400b44402541001944001040e2203152910701c03504245010220745a400c0c00140c00692444100e107080300c08010100018140e150941ea100d220090000b41800400103401642905c00c0041030004c03801885020340c9a04080d020940805491241040c02c000c14000070401d03902c3c921581d4000c10000741428a00302459941215540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 334772230 1250 334770980 334771009
    0x30d0b0105070f0c05210a06020d020c0709060812040b031308070b04030e0901140d02010f0917070807080610090b18040f0c14090414010605150c010506010f0e 70
    0x100c20312404000910180010b51054071400d11000b04e507081905018440c0549124140f100c0c01664003848030b1107021907a005100d800c50b4015903100805041d0802030f00c0b5100c00c17081300344201900010304104981c090001d8400780003e07184e4011541c8004136443c0158020b290340303000c00f0804520341c01c44041b00c204a00340318002503824030036651107800b40550b04441c1500810722200f40105a440e040d2000341c00b400310a42014910002c0c1380200d0030f210740300e2400070705100070019a000280d006e0b202203001490000c0b6121300d24507600b1031071034403981d8521443d40d20703200b2a00046500c480101c1d102c1c0c441c010b112020900c0728074101104024041202c040c54000000e50420616138103620899881503005034000540500300e80b61007680c0803000c3e4000c0a08203e44030003080503560307110f801078002e45c0003080021461406540300f4010201d0340e104551010501c0041d16486800501812462104000800960781c0d4030005460f41000796a030b407800107003030301c5036840b803480d02040104d0b011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 334773480 1250 334772230 334772237
    0x501050f13200a080307080309060105120c010806220912050a0807050306060f12070f0906020712060e0607081603050f040f03090b030a061802090a0e090f1902090f010503030d0b01 79
    0x144c0c1e40d095080d0035980040c8040e00c510034000200001d13060200007041c018402541c03451403040c0b0103c00203440c0d55811000d1410401e403440811541d5943e4004602e11041d0b580c7d0403000040b80d6200c26005040d1030383c3c1180c1007101900b60310744030b60169040d030b059a0742946900403c1d99032840201d9155000600241d40110705202108078140c04c9406041200c2180b0a012002d050402010b401681440741c1c4100f080b070b40c0d140034441280c1c045903007001c89a4400301c0b076118035240c0ca0008060104081d042c64940305101c00c0041d0b065000b0000c0b806140c04078000f195910000380c08400303407282250300a1016440b04080b400040300580845030b05402803505210761604da140b280719560050f0750084240e610f40009002e00e1644810502d032000c0d00b03913021440d00e41c81c007006c140c00078101d20618902910000c005014414140a0341d07190840c005c090b00c50040008610b424254a1048140c3c06440c2020016062600c1590b103030303068800040040d030600c40d00b510650040c294020009041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 334774730 1250 334773480 334773499
    0xb06160303022a160807062a06020a14070b060d0203010207140c130b1003180c030f121704022709010c032009011404030209040501050f1320 62
    0x2661200f0101d40301d0700107425034003508500c841e003120b2a01d480344a4507804c09922034010002e01c50000b4050007150880c0c1070209040f80307a14001d03115111f5a80d04104a402c188203104104200c5a008100703040043d200e002c520061618061441e0041c000020440300c02ca03004030f0700d9454441d9031115030b580700800143c60b119580d41c9201c100c81c081c1402c49e1031a48a541c007000306241940d500b940b003940d214070400c8011350340c400040068060840c0001416600c4562401c0f48103981a0150103d8000c110b0324495592442d0103198580409015a06040d21100c028035080c401d488010008030801a80075090700c42da02000782101a101303281000002c0000c090f800110102c0c00d1070710956640f000000c080740380d44000303000d841c091540c0c0020b08840140f07a5000d1298001500e00914080c6040000e0b034115280034240c42c416034001030741c41840c0b00304000070040150000351240c044112249100c0e21201d510140707024403010020021a83c0b0300680d1520506185180b140c2000244078008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 334775980 1250 334774730 334774747
    0xd0309080403061509050702010207031718070e011d060d061a0301060e10060305130f15050c070c06030b1507020315160906021f0b0406150309020102100b0616030302 73
    0x49030a540c03511542d0003040c0c142000851750b980329440c0c3c4800341e0700081d40392003000d9400070703d00071081030b00204c20840c0802141d600325042c40384807142011a022107038540e07214403660306d91401c01d205440c00001c00e0b54000901e1115140998000e080140074000200005e0340c407103018105000501141041d051200c074400e41e42402561700030715130b80700700e2092410010400304001050340c1101092604107401c1c44034507004010148000c5401501c1000f0080480c41d00304450240045c000c10a18200b8040c01a403080c2c2e00000c140b950b10a83d0725124603503607130409400340c4101c1c0700d04e2940a9203410109054425041c02021481c0c80102901c42c040c0341002c0812001c0000e0300da1610b405040140001c01d90341055030340707000c0c1a90340000c0404075602d05040c103e421484e82e80500303550310381d540c001a42e200e64200e01c0c09030030010400071440c00c200034001c0040c082004d09034018031a5a01c0d4042d20b10040c429000c81c0040130b032850786071110514075000c211178003601c100e0405908002009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 334777230 1250 334775980 334775993
    0x203060f040213140a0501080117070f0b04060810180b06090406030609020a0b25050c0d05030a0906090b090913140a06050a05090a0b0601050417060a0c02030c0d0309080403 76
    0xc061503c0c1c8005100c0141011503644046203a44909805100e00d60010301040e07030089007040c1142c05c0d01031a00c0d440b6100e1040241000b1455110b03904c4904128070101e4844048801340046d165659500d202954a0111582040c86030381708081c0030307440d42e64500c542d80745181c204402041d0068483d501c1c01100d8801301c4c003200d8035944181c41303465440e45107104600e00410b282e00144441100d090a0265100003d000f1700e0202c82458949080041c0380c1040080901c460408201d00904260001da41424410307140c1e8007034030811000440f14600450418080c4c260402070310136902641d82031959540901c040000040e011100f031210144002d00012003000e042a5501d040c003000e802d8001306868030000707454001d0f008001c0e407410300c0100b061049000401c205d010360095400e9406803150001a903c40c4a650080100710351291480054503900240543c0030701e01c001010000c512120703504030703201e0081420701c0981d83c002c80c08550710300c2c1c445d4101c61460b60003400c4607460300d07940740d6401c1c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 334778480 1250 334777230 334777237
    0x1502032e030510090309080609030a03091103030a03050601200307020409060605150711060403110f010e03030f040e01051f050f160303091109011a220314160609090203060f0402 78
    0x207540d0f05444503030f400c0405500c01080700090103490014221030400340b00ba55102c3c02031010242c00c065442c1070142c20300c140b142110141400240c00e4a6440e5500d40c3c00a001d086c0461f0010302040300c1040111075080c901699030700d1a120000650b080c4040c980c200b101800c0c0000080e03c04945611010405603030300018080e1202d803001005c4d60702c0400e40360081c1a007400c0e0f403119120720740502c420008a0000d0800003e0036404440c030f04446054034006958100d1380004c000d81521010400040d920038010080054a6100410403074507a41d410800c00d20003841a840d003d00680c0c00c40300d110240c0240c01900050740d40101c05810070b404c0040d100184d4006482c02d8000a49400d00300c000e0204000343c60303004600a560f40141036041041c10401d50f240318203003414989000424040c0540041022258010180300607800103540e820010321084e0360003000501070040600d8005911440d100c21400c03242181c540072912443d0421200c02900004e220715084818018450416641d92004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 334779730 1250 334778480 334778503
    0xd06020f09040e0303180106060806240a0e090a0c0203091905091006030c23160605130b01080a020901051005070b04080316031509150b0f071502032e0305 68
    0x21500c910741490501a1001c0102c1b82d800d2907450b186d0103000407548810810b030701a00680744410395200407940050340c40c0c0034911500b9140d1b00420301e50302c0150302c20b1080c117082c42e0496200d1056120644000102c4a52541d14000f46c1e00801030003046040091440711400c510031040380300207554070040750315010221003034025580021028050980c00d4030401e03040c4503142c03412190035402c40f00e40a0022a241310703c00300b8880701040168202c00c1400c024400e03a6403000040c03040c0e040c41042c80c68401003141007116034800140011510503070000d442c40016070020302d004580c0e403904091100d00810151140c2c10000c00b04102004100030303001c62401580700e9810f80b903492802103004e4005142c100120310805080583c03030030b02c403040c01c881d030000e6072120040020040e15950040099070440d81c001c4401c0e01d000700d41000c03180c0664014020340c0d40500c086140021a0a400000b24841194071010807100034246003e03404006810b03084040340c8626148055440c2d84842c3d01d0140344869 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 334780980 1250 334779730 334779733
    0x1080c12040f06143103080c2205040b060a09030b10080114071b03080a02250c0807090501211103030c011e0204030b070e010e0907080a11090d06020f09040e 69
    0x40c015040c800600300c240180c40308171030600070083d159818003040c2440038081e04101424011810601c0303a84215021014038140d41240307042403540c1a0f05005440c0b14140c071803890300c45400024240340c42103402503000c559524030030724210350b550403400300040c00c2c0c0446000c8556010507251000d124a072240f15a035500580e1a20784400b005002020904c0c0c0017882c8104004000d00094000d402d032500f000c02c030315002d600c9200d600c6481d0050141c4030041090402401c50710024081442a41d000f5600400b069a02040d01d540d08041039400a204450b602c04551100840301003a8003100280f040c45109203016090048e000a45560007e864032710b440c0c0d42d20b01030140362520641c800c504042e801503055003400c1c5180c4031001207880c02030030107085c031207069003c44050307100300b598020441c40204064550b0404007402403020310f080b40c444020324a8031012900c89456007003502c46003040101000d01120b140e6450b82e0107508540820001c8280c10702441e9803c3d0703130b5030080082c000e0b0f02c0310 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 334782230 1250 334780980 334781021
    0x1a040f0c0603020a0c03050c01090c030c1a090f22021c0e0c0609010815040c090e07110c0607210509031501030c0308090102031c0b010e01080c12040f06 67
    0x10880503488980d40018245031040124009840e0442d040c640c80580505040b901c40d10f1580416024001c1160f00420003501c11001008003c8030301880380980f90340402c0e84142c80892030401c86940f10b482d48880d845002900903014624003d5401c051040303030416014600a10040008160b0b08420310b05140c0c0035100c0085466071220744503a14140705900010081e0071502c401140180c86204005810031400800080d403d41c0f0004500c0400000500100f014402c0c110b4024008041ca0046200311003003040800d1040b0b10135070300039480c0203860000d40b910a101c4020400345901c8030008481401b040154609240020024400200741031303110195030380505403c160419140f050010000d078000001840856200b203102403d980d40954010303641c040800060345180070b41042c040010011203c103450180141e000815038403020788942031041c42071170055642902c12210504005030a0290400d03030040d60742c95a0700b1501919280003e1200d5440f40420b9070700c40c60f48040d030210001d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 334783480 1250 334782230 334782233
    0x30210110708031e030c090f010c05062a03070f1112040b0904110f09060d090501091109010b04140409031106010608010f09020f03060d020301270c0602070b0409091a040f 75
    0x280d1540c141131a25100245140b624100f260181d00902c58030902030744001c051301321780f64010f6a202d8030340b80e0030004030754240c0b91111080050030240e984039141d440520f40000d51506910094900540040d112012a2800800704950a200c3c03500050032610882032002e42404043c00100302410070b03a4045c9640d8492078050100f682c1c0841d0030344e0003002e4101701903200b45410380c00b0740b142d81004880d21641c2d4440da140070b00152201a1000e0069403900547c0d204001a2104005c80340d0400c0e03550311056070340d0b01c1d100740690185100305140400903100191043c60242d01c000c0d000c1d44a400e10b10603da201410756031416600f60000c20100d00202c0060085001c01040800140b212510540c54040165190340d03030303804040d01440c0a07042118181e000c540e030a401046209400c0c1048019403545800004e82c0d075400802c0580e11005401c8001c52002d00c007150660a4400034148546400e2034004e0313003402007203503081c20359400800183c00360540b070411081c5030245001e0502030ba2a41000d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 334784730 1250 334783480 334783507
    0x70807050c060a02030f03040f0b0a050405100510050409051c0207091503080427022704150608100806010f180e19020a0806070201050717010f03021011070803 70
    0x10320310200e1240c02c092160070300080e4000211103508407a400000e4481e00c0707502d492407118019040081001d072843c0c0c20131035100e8140d0310183c0b2640c05001150045044c40381a8811900d007072700c5074900040010810300030f6060035005440b0862103031049980d41a4210224284850307004120001a009000f08100b44d60050003100c0c5401c0c4e6071145408440e2030b5980720001c0d4892132040110361200c074105181c103d152001504185901488103540e00e11410000c2030300802151400031a90003060580c0380d003414540305410282e81d075901110503050070b2070784c15101c07e140140811001c51207140c0c042201d04060051600a00644108102150800940c160310907042c0a80040a5140c0034071085000c0002401803155843e043c1484010030050020900303101d01504241503038031440c01400340690313055114a200c0d51996540d10f80e1600303102503103071045c0d03420303c201c54241d0045403040c80540f90910719102c001c1e00c241044071a082d0001c030040c0c200020f5070300c41845074001017000040ca501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 334785980 1250 334784730 334784743
    0x507090602060108060a050a020d0e0c0102070f0e0c0306031c03090b0c18010e0607051b0f0d08041e0801150501020d02030913091412071a0c0706050a1107080705 71
    0x240340c0050105903062080740351342d070003004081d80c0b040c6d034883c808120f61207d1035048400c50f64240100b445a0422441c2d030a95400d100480c40c0d006228403500010201810380000c015120042120700b02501e90b000c11060581015001c1581400380044030070043c913900001c4100c0c01020303240810b5000300713802c00707040c2c5040044c50313011440b80030072280084144200075080c0d40442403c00405006486000c0703880c030f00038241d0040261048400700e04034290303000f4170301414003011079600701d0301398110b81804000c0f812440000c12a12090005101e25001c405003003c00190384038075882d00c27541d20903e4509440000300c031451102002038042c4400d580c180401c04690706140011490000f81c01e02140c1d081d0380ba480f404030300c0380c2d8840c9000200411030750303940c442010320011524070038104070082d0840d038071005040781c8184020300705212101d1050802485045040080c0b818405c01d80c40344806400c00901d9491881c0e5034549448a80e407415001e000c199000341c03c2d207620781600e86059841c02d05c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 334787230 1250 334785980 334785989
    0x4170d0606120515090405101109090714120408160b150303041508040501021201060203030114150a050d0f1a0a050904020a052110091a01050625080d050709 69
    0x5083c4000c020031a4460210b003542d450044d948018140d0325418010b08040780c10002d41e480d03c0c02c1c001141c01c140072800c054150210115991318443c2c440d00421745405045441c80c00801c0030501c4480c5040903c1c0b40260380c80780c080e1000624204000c241c0041103204c50741d00f00e03102c0360080e0901a41840706400b0240100066008500d040d003407994450598018074018030130080e1344000502007001c01c0d0107444004516681c0c4a9540d41c4454020303440350003d0280382d86200715030007200003a14046d03a0756031414240020003840e00b60403940c100e6441c0d020000e918211501d406c0404c1c22007140c0d101c1c020202d100d805120041d5030030300d030401a0110346984014401c004003014007000d60740b66010b2100b11441210b41c0c100c081c52858001104900300756100d210b074054405401c101a5150b0814024a403041c0c3c00006006620720309441d03004000c0c0242d03034115030107201100e08121b040b07a401c01c03a08003848240740c00f000030799128001c90b400166000f4040392076905200344d19400400000c09003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 334788480 1250 334787230 334787267
    0x90608221a1b03010b0c190b04120503070e0906010509030a030f030f05150d0c0f060c060c02031603140403050105180705120a0201050d110d090b0c0903030706020304170d0606 77
    0x60b02030520300803502040c01280d032004d40010b0303d40c80382c55042000951044c7c4899202e410101c03c0d0500040a21048400703440412040c168502d90310b00c900102da1181c5040e85619160094620510001c11401080d403810f02408102c2108640c1c0c0401100d1314243c0b00340c0d05d2100442c80c1000c021700380c0300f41e83e0003886094141014801000c1400c2c0c0090000e440a03184500d000d0b0741d03801d00942449440d4042c0301a1141564003207034840e446141844c02d940a13100500241c00348040c1241d4a1190682600c00c070014550340c400001d10416803101850342100310385040607180e490782800c6078401d480064041c034003440e0561000c00144a4803005200c101c2d245c541460b111307214207440e07800c1480000d04202e4005103509a0003815440208503943c0071780d0300c5072141017104400d4002d00b003d102c29941e44040400140d082c07240380d230444001e500e000c0c01860031700c0029a80d0b40003a4001400494100507000502c0300c41d000d03503101034000c01d001584082141803404002610601a01c078080040e27 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 334789730 1250 334788480 334788511
    0x911040b0d0f0b041a09040201030207080705060a0b060c060f0402040f0c0302040315020901050f0d090803090606030c040507051209030405060307050409050105010903020f1e04020c0d140a090608221a 88
    0x300c0151116408503540f0030354403501247d903584012402841911002007103500f01044001c00e02c00c0000d2801d10407074001c1020041c46c1203480030003185016429130507055601200003d00d1100340342140d07a80251000d8000315460320799405000a641140c0164800260301040402c00e00c200c0c0c0340d03046860100c000c001c51404d280f05c80028524440d0910000a69100160b040003010450b03000100071500011115242c0c10310984080c2c4402094072514807a2040b10440b40c0149001d120303490041100e42c41e44c074505606401602c0207907a00804184290105100000d0b540d16100c0c0250720071740003036440f29500c90401109600300e0f5010b810081c1040b04580c000e0006803544070440b07045403003c0340c0098241c0c43c00490038100000030380c0c090fa08240080b0303181910803000035071038500401743c0e1181000d403c81c00d810002e84d402115100030010300a101c00300700c05030050f8542074200c40f8155145a03c1d0b00281d001c120001342c500303011110885100e0003c00044108051550007000c00005c4008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 334790980 1250 334789730 334789751
    0x50d0f061802032a1c0b190f0506010e120106080a030f020708070f05060706150902130e04110120060c0304060605010e150a020114130303050702060405070911040b0d0f0b04 76
    0x2c41d140c11044d824001d0075070610740800300960b0001e85d0300c284c0e806608400f407407501054441e41c92000c00c0112480f03d080c140c40c540609242c6c0146031045074183d450298444004c001c1203e100008112a4419540e410303000c0362a19050044051036402500d80b07006174500b400000f032034819141d1002034903822034076050005500c1c01c1c00396000c66000721980d40e240c40440c14502c005044010704d80785050042e0000090300070060b0041c10195000d00e00c1a841c19603524103030b40c005581210001c0c4540d0051416001640c062184030400d0f501c1013002c851404a0458120314085060300c0d5450601004070402007042003601030103001e40000e1070070001c0c00c903440300814021132042055140343d840200f400c0704840d03c03d61000141d40c664001e85003050a00c6042c03458603076040306094001a0400c80051015030001421354000ca43c44001000b01c0c0c0e142c903000b1002041308002a040299040000082020a41c4007504131180b800300f000600e10500c0440d03030105e070780700c000da1402541044141403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 334792230 1250 334790980 334791043
    0xe0f070c0b0c0a03020d0f150503071802070c031e05070510021011090307090e163b180f19060203060d050304060504031515050d0f06180203 62
    0x142c0040075000d03030589480c007203039080d40640aa21125140301d480c00d46002c2d2882c02d281c009085844038415010307505600c41080c0351710360360b0310302400d1105d1790850700d0b40300040415402040c445024104140700b0340d490750368038440146501c00d100c0c4a8400000d4040611505000f99030080404403a03101c0552041032001e5111140d41c0107400b030340303581c030f00f80b90302d4403645082114039851000301610506170f140c00303441e0010030511520080500c21401e44010f1903d0302d0041e2801d40d10a0002c11000c1c002c0f90f030710b03003d101c00b030303a00e076904858406222500074a580c0c515260190328100301210240c04c80c0030032540740c4651a20641c1896001c070750100c4145121508040c1c070a9000003015a82e980d818020415240002c0001049444000b40004005500c0000b50054078800e03840d030304009945180c00f030140d07004020003111070700035000b0400043c942002c00300840752040d40007810203080c40d1034200445052003d01600740485100c103500710300d0306025441e80c000f0400030b12481c0c651603003a0380 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 334793480 1250 334792230 334792253
    0xa030b03210702030114070203041706072a050a0b010305150114040f06050a030303091b060f0507030c0b040b0603010f050c03041202070e04033c080601050c0303010e0f070c 76
    0x4901d0360700c00030301c001c2952000e40052114414503610f40c00740b0300304040000e42d20b6002c0e00ca8920041418540b079209803101181c014040c003441d0341c40340c40c3d412184002c9202d0101c0d1b4840080f1006054440c10f00082081c4842c0071500e01412580010f9851800c00c00d052541c2081c0d001d95080d003140041c01071740a00c000803940c82e2816100014042c007100c00940062502e50449684a240c08500108240d416000300145074070500800072103440c280c01202401c0c0d200e02545001c904009114180c0300d02c184080c0c51154002d1500c495402d2594507124600c11060b5029281c01e40c68008100f402d08007400740c80d081d01ca80c884204042d01d411132040c0458000070300300800306100350b4500441c0d14420000030b0301038203030750281c0006820320340343c040e10106055004180a5030034542d400050001d0001c200f241d94640f03d4250013440c123003542111505030081c4028107001d81803000c0c0c0c1300d41d40d00300082c0d80a44004103849015041c585c900c4205128010401c0e0104055401c00304005062072041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 334794730 1250 334793480 334793533
    0x6070804080c0102130e040519050a060f181112030a1e20010b04230a1d030d0204030c050603060303190c0b070c0209010509221106030c0a030b03 64
    0x140c07199402182240684105098049503c102005c0440c000321010b41e454040e900c6042255001c090010358032404105110000e0312680041c000c1d1710119a003504100c0300d040307400100084505030703c4604141c0d24850348080d82c00c1121009902011308042a200c80c1c26900180110704050700c012000342580c0c2d20f541e90510510a0b01400368105006c3c07110380440c0b01401da403d102601008103198024624000c206102e1f43c00d05428031020320107003a00240c420440300142d00c9a645240c01800070b40b010403d1542c03000e045071810441010244040c100f007402102c40942d440340f4500b442c051003010b5400043c841e500410034081c2075130b00001101c2841140c000e1020958400d10301c10764030b0101c0b400010717081c4036070b0100b000805580080080c00c9148201d40725207003a40c0300c01c244251340c4421108589203190440065441e0184900e052511078420360545036a01d9a03000800e215410568444c98640008141c88104039014041c203088060298014200a80c0454102000004803642e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 334795980 1250 334794730 334794743
    0x9031002130b0f030411010c020d1e1b030309150e0d1e080424050405040b0607050703050d120e060a1e0e1c0215150a03060c020309100206070804 64
    0x59090a1007008020341c8000c1c07940d004810345031001c001e05044280e0040700c04641181c010400d520196000340600c01c101600a8800ba010700c0d1a42e0320607121028413158400c0b0080031805000000b500c1080440800c5610341d80d410f0894a545030150090f0000c1d00700450040c031022030b031071100b03a1015402071074843c1141c2c0c2d2201c1404600703003103c20708091300c04e6004002c8400e07841014003030300c40000c004903800801c04003450000c00303065900c424003036500f040015000b08810801c074607194002c5094200002c2c40e42e031604019654440ca01a150390084681d5000329810a15164200c4034003000400b12400901c1242c24844100d6100c00700241800c0100303955880b41300c0300390f030b0440c43c0d46145403100c282000005603410752035950b4060000c2542c3c080c0041030a19014620124100300148183e610000300c0c1e46411502021600030743c0009a040000d4400002c003040d0070740140c400d00f150f01d8010b169520301110500811180302006442590310120500444c0d5600c00403143d4015049034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 334797230 1250 334795980 334795987
    0xa0b0721050603100c090b070f02010f17010b0c070b03090105070f02030703020a2013090507090608030405060d09150b010905150307270f09050105032107080403060617010e0309031002 81
    0xc101b5142c0d600e06402020016002091003002c1200c480010724042d8002d1721b50030816216248112410703000e40d084a401d05102e040100000200c0708054100e034a10b10050b2040395448464640f0590021105204c881e03440e041440b441c1a00042ca481c1c8050061028504e45001a207000c2d5854410b2840142041c0c0001d4030202805100130000c0210400200300d028135000034015100500b004040542d498083c4860000d0141d84c188900c408417a2080095824140790070204800c41d0450303002009016151000c040c0040c4c10010032400914522000013201c0017a0340004103880c1d440c0e00304900031409601504411001142500d038844418686025241110701d6004566801d01180c0880d00602510120740c1c0e101032034078142501c12145007000a03a036181c003017695540d0700d0105000c000b5030843e00c91501200840003401540d00400c01315160503921394521088901991108075621528203a2000c415428000c0911102c0c82c10f0085041c03680042c0040d4a4800800c502c0035041d6001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 334798480 1250 334797230 334797251
    0xd0b180316110d08270306011d040213090506151509100207080609010c020f1501050607060608030301140f12120901120507020102040602070b030103050606060c0a0b072105060310 79
    0x8000096000c2d48401882c0d242e0041400010750342500c01101c4c03100549507542d0007503a040c00200d0314101c6403145180810304040c40090312713805002600690700000c8107035800d80d42e481c0500038484071504c520010000c40ca00640102d1029080c84084c5110b107410141c030121001c1542c0684a0400084601c0c510340b508402d0b00b40c1c5407034426031080c03038a4080c5a00b0000b41e02d1066010100c144c01c01e8080d43e09070380c02590016120210b408400159010700001407040e0b04080000d060680e200e07210001d1800e44684d4801c0c46c0d1b030000d0f07000905107c1006010030603400e0103900c2180e00d12003502c6900c10154007100542c0c490117208408610b02d070b0b011815003003030784c822910002e07034081c0c1c03417401c000038101441c000b030107580107010360b0002d4400d0f02000250f00030910112070490f41c104000e8a6162284001c000c1103900801d10401345200b542c205a001c28007114145004804d581c1321540b91401190000c0c0703811202816010700c4902d800d0801141c1c1d200461040707007074201c0c8040010039001d0f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 334799730 1250 334798480 334798489
    0x10152607021005070f020708030c032a30030f0610030b190f0e040c090c050c1b09100803040e0402060c0d080f0a0506010f0c110d0b18031611 62
    0x4548042c940c1814201407121407074008806001e140190790980d10203a17140c1d05425a64482d5120003401640f0411040350016540003031042c1480786e02081c50807415001d10303141d00d424540540a8290307544c29520f045004500602c0d0800154000c00050543c0343c03030481c2c2c504d88032009000d1401a891002c0014070300d44258458441c003100180450800c44805107400d80f00da100c2d0080c44203640c036103000400c2406c004140340344980d61040f032030405a42410317080c5020302400ca001200b800001d0001c05002d00341404040700c0c003c0303e104d0031802c10741280d0070410780314006084070100583c291418007501502104071340036220210f502e00703841d823501e201050351849a00c001340542c0c000c0c4102c02044c0f59010b02294003500c03c011030220546c841c1901c1d241141e900751503943c04201c050704030b0502e1030b00980714070f8803083c01801c69010a003400008a40c00c81500e4004031154407200041001404800e1500081c000205001350306020291444d04c0f40c1c075078600c4d400380080b001d02c400c0c00050360b80c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 334800980 1250 334799730 334799743
    0x60f03090c0504060b07050f0a080711011803080307030c0504060203090d0c05030111030a0506040c080115020a1403071502091c0f060f0c0e0117010b070302030903061015260702 78
    0x40c00fa20400400b40c0e030742d0a03000941c024020489150003821440c4007007000004041c140f541d00003c07414504065503483e030b40d2401080f4640303418000441080c1d4134805280080e40021801800116601c1c504004018101c401c90403074101400400e01040c492281e0000c00d45021a000355000c102d01005030800440c0c0b500d2582c0032aa041d8207041d020401c411048020f140036401418040c010b076158402000141c50341c0b50030070000110480e0040000c4400000c1110040c1c445005072402104a500c1f030061505d001844900203030f00005940301001507050352160f00d1401c10508500b81808040042c0320a03400400c41140b14510000f1041032200094444040781d03030004003003000c070b2508a030040250162800d224080f41d015031007008594082c0b070000715002401d4071b000380a42c1c02c01c658110070340c01c0480d041d81181320511554240c1d850030002c50b401030794030b61400380d02d0614015001c101d4240310a0368404000144d108210f00e10f0b10402144c000c10b0310264000456500d8000c00ca14050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 334802230 1250 334800980 334800989
    0x80c0a1b02040911100e130f02160506060102070f080705090712020a020c0406090902030c010819140a06060f0801031211010218040506040b0609040b01090305030a032301060f03090c 80
    0x51410070944100b0603c0490b5800020050300c00442117110309209880d00e0b1880080c29400000d030600009440c62654400342e100c254101005050014994542ea80d070004c2d588220f52980c000c0302441019a010030692004145404200c0100ba080044041c3c4500091040340c0c021050100404e07803107805415030364100040f10304215110403188400a503186c035000415801149004000309008001d17005d40c08a0703c0c2c0285c000c0140c82040c03401140c80040003080140d00c0c806240c5031400c0c0c3c1040f40140d514010341c1e8181c04501e41003101a036421156140d104005015039260440001e0750049148e5044940010141250004e210003d0303604d040804c1c1c00218951000a4403642c042a10044504400d000e403001c200d0713913480c2e00920085418410352507074001d00501113480d0078a01500aa1898401803410403d1186d590703413184e103107411025070f1001084e10381c9448078000342d817100b460034161041280321800b540740010142c1004000c1c0f10f00390405496a94030300902c0b804121800081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 334803480 1250 334802230 334802239
    0x40b061b190c18020a02061906080118170306010c0f02040f051303020c01052b151215090b0106050705010e030c01021c0911090907090f06031101080c0a1b02 69
    0x307007a0303072034074075141032841c010410700503000c104041103048144203684007101c140e001410306845840c41061b03078441d1404680d44c015110f400116401c0428015400c14840072180140068010301c0c0c5000038807950010003881480901c00c2010f80ea07880030519061a4104400400340e40e0580003103400340c1800140300b60840d041500340214040c004c0c0700511024060ba00781d90714822000c00440e400d1040d1100800440362140420901070100e1400c0842d103449140001015a85010801c42040e8640d11482c0d00c80d1401807079000b03102118501c151010701500b4204004076450f40c03801000e00040c00717010b04014001c269030040000c00d42c40b00d8140d074051001c5070307200c0b400c184045001c0d602c02e4500c02e440309100a610381391440345000c0ea1544903800031003662a048041c06020000b20700520a1a2911803540000f90fa1a000e205e04000d80354a2039010a040b400c50600d104d442e510030704103d0401803074004000a540d81001920080070041c43c000400814121449140302031400010750712 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 334804730 1250 334803480 334803523
    0xe0603040f111e130608060f060a090203131202030d0e0c0a171908041a190f1707020111030a05040302012a030b1c150b040b061b 57
    0x203008003424010340082c880d2509280c4460010280f01c101c08921816908980c400300503460186040c11241d8000802c0b01400107100d0340d20141c442c43c1c03180c16260100740c00c003590280120b5081080140c000ba1244246c00c0d803450a001e00302c46160300c45c1c101c01801c004030a600e5081d09a01c00d004a07401856400c90502074072040c042150b031a106402c181c2c91080e080e184002995850400041009642c001d026280040e002d255031030303000c20b0030f8500b00e92008003000003003403009850690030380e40c0c03181280f84d98861018500c80001c08020784400820f00034111102c900d0f03568040090201e4004010015500e611103141c1a4003400f801c01c0c401007441c03408001c00c00300244651295105034040d500902000c010302e00310080f103170020000080c449040250000030203009800100a2031000740c81d03030a401c00990300e00c148100400c0004c440b540388148110500102c2c43c000d0050640c0201e43c2044179049950018003035201d800c028031b98400721120459425034051001a0100d400700503030040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 334805980 1250 334804730 334804733
    0x30c050a0b0901180f0b100e07020604030e0d080714010f0204140a090e0d0807051312020a09290f061b1203010f0e09070b04080d020601050d051203070e060304 70
    0x20009411105003040c3c0d0f18050043c466442d1021200f8aa40c0c0c006a0980c1e10000c9a1580d900004008242d007820103030240002035400c0c449141c251007045e49902070111401e0600e402072410781000740080c41340044204c1c180229891348105c07801258822010101740a000805d0307809010a11607007503038107201140c005280603080702440e200e164216141c1e130710951200301d000c00700c0315591041a061f900c003800d400100ca00507120103800c60031f2030030202d040c607400f004ca41400151030380008200140d0003000310300314144100c1800140c50240401e00212003066000301408080164000b441c8429600c007802546400080d10184400a0002540c400703400c9040c03a07164801e18000c1d0b40e2845018a6016200c0410303056034183d070400c48100200500c0d010710441d00c039802415a00702401080c000045600c0c00d000104020400c075030180c0403c500f207481c081e0821005910650003048122001d000154000c80c030400c6460480104a440c0d0701d0307200b8103e90b0011140403171600820700105100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 334807230 1250 334805980 334805993
    0x7110a080f130b03070e040f0c0c140304050306100302130b0112090606032909071824030b0727050909160f090501050303071a18100522080a0309030c050a 68
    0x11b500d0a400d031001d0010800c4500000101d81720001041c0c00a071034580e450002800c0c049180c115000c00344100c5c0d04081d1204000384c1058001d5521403001440e4440c108210b04225180018084820008100343c090b00c0001078407400d2204200c1c0c1c20a5a6003145a0801c80a0361110000d15000400c00d4465441c4517505440325003c3c00311164000b20240015001c0e4030002031001c20303248030100c0444010f1000c00301308054030200201d003010050b6503050b12040f05407055060011405142c070b0042a08045601900154841003805611012407903c8030195401d404040b0440b0416148000b0940c0c8800100d41842c0f031560050400800380000065080c8a514500096500c0403408200d1640e0341d2080580e04c0c4241ca80092030140d800c8001080081e89044090f1300840402c4004185030a403029107041440c200d042881c01907a40303051210314030f02c0c0380141101c401040710648580015440b0b4208a0140710300c01420540c0301c003103100030144180360862400350300c1400ca81c5180460314004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 334808480 1250 334807230 334807247
    0x210109062f0a02030906030a020c030a0e010f11030f0c030f0a0e0301050c031e0601090506070c090c090302130209030c13050f1f05041a10020607110a080f130b0307 72
    0x4a5003045000111100341c0081401c03524074000a80007181303030804c4101402402c0d04014804400c440d420700c10354503403480a00003422447c16680d10100100846c90024002036400d000441c200084140e0340e42014400000b107402480ca610300c42c580362881c01003114030718402d645428031070b000c1c045480e0800940141045200e54811002030103d9500c070903548440b4001180c0f2500601c40481c900049445500000da41061040c900015950303140c00201c0c0b0141c0c0640b0086070b170b005a541e4208902042441110303075103c080d103064000346203141c00240c42c004600301c3c204809540085c281005940030040200c1c4010054250b54100e42c00c42e414000801301141c0c0a1081100c141c0003c00740503c07500020300360b800707112580c155a401d06051200401640030303a440c3e403000381e0801c03850513070b105c00b00103c0c0494560b00412407442e0450004140013524008801c0e01d50200c0e51890010342d0a5090380c8100720440c521a4480b02002208113810095034890056140b0000174000402d0713105064 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 334809730 1250 334808480 334808531
    0xc081e03010e0a05071d010207030b01180b06070b4014210a02010612050a1505100608070c0f03020102192a0822170c21010906 56
    0xd58900350f070b411000d0400c1c4c45007114401d0000701c02d00507120844280b6141014411410320442c2c2d2100d44980e510700c404942a0440c0385800313000300910700d0050aa000d00b00008030700ba1901806c0ca409035490560b58503010f047c91441d10152000700c240200c0c0c412020b83d0981d04921800280c05900c4511001c0a114050a40300450001c40c0301440d148001007900c408955800700c0c02240c24030030500b12050304190a06021952101c41c005031071401d0b100c241c4006401032000d023003080d4080c42e100011001080c841c845c0d19040100300300100380d06200c0d00040354042d04012140c0d60303a00000710740340f441070840100640c900c5803c0c58181641540504964160300100c4146040404400e4610303c1d03100c1300d042101031500702d500d1072440e00744502d106150b1107601c03e20b0400500742e507100700129112082d10048030141ea01003100200040c0c4000c00d008241d1301a0001c0160203020031030008480d101d400e480f00546010890301d410941c0190903098100300308200d100b9216180c00b801082e003028 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 334810980 1250 334809730 334809749
    0xc0706050f0a2901120209031b180708040b040609120207030506060d020a1e260601090612030f0e130510050a150311120c1b070b040302010c081e0301 66
    0x2010740c2d0710a03202c602e0040c3c0540140040340700807000f004592035480300081c4d8100c19001d0000354629103040005403903e100310601c00d414804401c00b03000c104100094585400c5c202c2400b440451908550b000e0b400a81001100e001c5540e60300b0310031b01820002800034210310f482050721452940c04141d41c0184c0b4071550560311a40c80c3c3d80d04101007194034040195010008000402070640d070032035801081603035981c0317a003800c5684000c0e2031002d40b07001c0c10588044a4040d44012801000e211140c09400610010090541014181808803182500040c240290300000400890003802c0803010944002d22085c040690b21040e031024180640746046075444c0414089400e00d020a18001522000001040900c404c00400c0300030303004481e030040ea040c40402105001000900401e4800c50050f94419540d1907180c1c260401c05080c82007203e01900801c000340701c01000442141c044a40900e0a1015690b440c00c11079850310940040d005111049601455000325201c0614100e440b17100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 334812230 1250 334810980 334810991
    0x403050c010507050408030f031b1c0b010504060c08131a04060306090908030714070203070f0501110a0201080606071406162007030201050a1707021e0f03030a050c0706050f0a 77
    0x309440600580c00346c001e058009101c012910003c8401543d800401500c00b1580168030003039424580d80100d01c01450b00b082604001d03c9081e5034000d004a9070428070304140f84c035140040050550800e45801040c01703030300203180c0002442420040002d060414400300c980c0c1041884601c496000b4810540404d06212000038400c8281c407501c130060f90008005842d641d510f41040307951140c21000118007001c10701c142400760700c007001080d018005400c0031740d21150a000001d044040700034002e10440e0303c004144401031764050305075600008103440c035580703840da2403401c0306190f80308008258242c841c5008001e50340092058482c174800350394544611160341c90344441401000403601e200c656010b80410001075200740c00400c070a00c03482c03070710b0f820200d11405006d5040f05e041c2c400c030005034460106180756094900100440440c000000c00340e8030305000f4200e0312400b0080c80c045005580c0e0300010f144440c558120f0310f9042d400303501044245440304812592000a81d080340c0f90502d0803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 334813480 1250 334812230 334812241
    0x10b03010e070e0402060a11191a1303030b060403050a060603110d0812062214130b0109051e0702030310050a080c12072615010b04060c0c0e0403050c0105 68
    0x100d1070b10706550b056210344440f5922a000e01c06540d115030342c00402c101e801305080d11985414042503840d0315840620800a603194203005088a11011009900114034001d10400c840c900000e100125410b050110b4031081a80c00552280110307400a40b13a4000c031801401040107950110341034034810410541c040355a1000e1003080d105000c80145500d1040110032940c02d66a00640d0380704034014802c3c007500100500340d40500e61400090142a5141d81c886c19441c850100751a60060781c00300c44800c00c0c40d8a4944000b1204188100210f00d580c903404249a024142c2508805404984a900301400d200400964a500895070b2028a80044001003207602c1c100315204d08031030001c070040c224074006908000e0034225400844c0b44034400e4840000c0c40e030301030660f4400c050207505d203100c3c03000740030740c4078207003001c851303000200c4078003040801808070101c800183c4058030f00c3d038540b020508850780fa082d00300010a8000082c0d9171035010410040651010080100c0010b000c020702264894 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 334814730 1250 334813480 334813483
    0x201020301030f0b100b0f0a020f0105090312040c030203071d0601210b0103090b130b0618010317040b040b0702012007060302070507050a080105180f0a030f0201021308010b03010e 79
    0x2c1c08000e00c080c00108410004c01e01050303646400201d21003810380e0310342c5d50b414213215917407024580c105810f40114a10300d03001c1d018084a07a017402428000e121601d040981c542d00c03442042c4880160325000c5002c00c09220440314180040c51b406000ca6605a407a00c4d844070003000001e00640524000d0300001300f0075440b0315001004280d45144c601d0b5401c1e404030b0f004024011a03002c07117041564a00041e804502440c100794058840201138800c00c101c1403d042071b400300700403c4070b400383c040760400c1080c03410013448450440b83c1000440007a15194070b172001552003650320001e2010408180401c0c0b000704400201010341c400d88940349800141e40008000260009a0002c0741d04220f908002d020b00a070010810144150103490304592100c00080c000851b9411161060b0b5694040041704040180001010b295140040104040c408030752540c501d260340f001010030440e00c60011005000b501590b80c1c900b060a4030f0030803d515210950300900c1e50200e00b81c425828000c40d5584c5d03000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 334815980 1250 334814730 334814737
    0x30302030609160915020c030a0303020c0d17010b0304150606081509040c181e050a0b0312190908010903021516021e240613110d0902271006020102 65
    0x41e440303545080d45030110b14241110140405c1007075001e10001448281d800f4081030392143d200b44c40041c1ca034003000c10414507049404040304140703e44400e103201500207440640c0c0c1158401000c1503a40d98462510f00494074007100004040b40c1041c0000c100a5001529a44103a070350310300d80d42c070250742c26007000000d0005860140001040c83c0040c48820222485016480f00d80c11012403d4151031824420000000c44600616503541c030902801c03a038140107072076001504400400040110b0041d074503c138401d840c445020000340000c048003150041e00f4410007030031088000c000302069401d010352502c40140b41300380c2e026880800180d850700101c2c48410403a1040d0300800b4002c20041c1d10340c1001450135681642d034410000c1c800d05400f028504002203149001e000303c11810b0030f0051141d10102e00340b1012056041403072800340340741f0090564004a2407503501280c0008a1f0011a20f828610b081010410400715030b4940d413610064101c41c0619000c44500e00031701d0b500c074002c03030803800b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 334817230 1250 334815980 334816021
    0xf040203060c071208061c0311060c0a081303030603080703050309010b0604080c301b040b15071505180c120303010b13080109110907080403080112140307030302030609 74
    0x3082c4124a1318410a0031075800391001d400d14100c81c59292080098640001d001c400288402131001c481c04414004d05410047d003200c52818940720803c0504500320041020501d540380d000c10788241031007600103800450700000d480b0360314042c9040080c00313580201c2c0d406140358203080c114075440c1002e44c103c0f412141d00c00050011188823108100308507000541104030304000b000081e0b0182d80c141001d106c85040c0078024040f90000c0d81030349500302031200202d84501e02c1c0815655107034450800e03a04040b43e4200845544421505c2e00d60748080c000c01c80b81d60014600710030031103c9112504181056894807007141c4080400c00104510607401c80d0f11040d0540050004105241d103000181c040a4103a201c80308903c0d0302d5100c03070746c210340103148251400c8810941030051401c11700841c0d0307040202c2d072030040041e140980b00a0048941841802e401e018280ca8400c14016843d92200301c40c03916105030f84c0d0711022420000c0c0603403c00e40b4040c1c070841d02240460741000c1000501410f00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 334818480 1250 334817230 334817243
    0x203060606160204060801150f031203050403200318090c0406080c1e0415022a030a0b13110d03020a0201030b040b1c05060c040b0405060a0e090f040203060c07 70
    0xc0d51550280040740d004540500b03010035119650b000140d03914001c84001e051001c000013180344c1d001d068001c00200a60114503464108103040c0b001c1565000320f1313100c8180c18103010030242c13258501142c04008462461200030502010040d118101000030100b6070080310118815944041c200024a401600d0801c05043c041104010ba140100e02c80b6034030601080c0c040b030a204c001204804410200c034401000250005420700050760380134403000803d000d03440108000384060301c1c00308503400d20340d5610041e01d045001100b400d6a0422102c03055603032125400c000e03401d0001280c0030020744039604981144d103000040702141400e28035152040d400d5801451074042c26001900104480301083e60000d41b50060100c180d2541d44d0410000259010544a0001c442c2021414444040c000801001c010030040114001000640d0f050f00e804070354040da01d40c0d000d801522007061918541d03400c01080c00070007484408446245100724000d9060340c4541c1e491010180c541e1240d504001c1a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 334819730 1250 334818480 334818493
    0xe180d0f09030605130203030a080604110a0c14010f0609020c0d053c0a05070311070f0315140115030c05120a0e0f121803030301151101060909060504120c0203 70
    0x840c44580241d500180c100700c8017040034440781c021904503840300c01d940010500304000e21440d802c2c80c2c421011002c810042c0c19040110b072a10082082241a8014040c00c201c1d01d8070107220b841c01c0d03000341c00360301d4031032400c109003665001d008020350400d0f00740c07410300d0003027104441c40a03010780f0440d06d0494140c958005084074102c0c01c00e00c0f007410705c460108e500c40c4855118440d481c21000810380c40c421a00c0c5e03070b41c5400703251078024206a110100c4210b960800b02e009c006202c00340440e0030503640e00c9100c1251140d9500f0b145801440000d1503020412a44030002411010b00e8810003d20400382c0e400740a0080e440b6400d985504c20f10b41c3c2000450b03a0000040e2203c5220b40c0005443e48100043c0c0b01c2c1042d0380c880e42450403440c4020144d002800040782c1d0003901d582c0000703403511841036014608540c5880c040c00142000342c1c282c0800d00c21210141e000807902035210201034260190100110f02090034100c0090008403001c032001d02a100441b60b0041c0140d0700b000e0000d5004000f040c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 334820980 1250 334819730 334819733
    0x13030905060c010e0303131e0b070e030f010516090e0606040909030c060c0509030d0c05030901030207020118150e0102010e07180605040204140306012102040b0105040e180d0f0903 79
    0xc15601180007031010f5582d448130301440c0d810500085008850245407a45c044100e801c0400c408550720804e0322036044001101d800042c03101d21050fa2100d03c0e41040e06601c0b0711640400e007031810313071541e0f940b40394070380300070051480c003440075801c0e515007260f1320003581c15180c000011a1403016906141d028a060004202409254114444880c42841e000400d14400c0c0c0e68001a200103540d68004514041042d40d024207041145a52003c400e1502444400c0c03141c98040d160720030003d0080c1016000241003003964041c0b5402890401c1c40c203982c1c1000c0b6515402441c807250122036080000b00d41c0c02e0390790320319031050081020b140031400203010024641600146c1352090460b0302d0018545802001901e552544058001007001d44038116031454240c0405003000016048805501034020800300507000b171b0307000ec01c09550b040d1000190b002441005880c240a1688490603407106107080040c1d42120b41d00c0100e100190394101c2c0c0030040410b1041e50a983c2e841c05c43e90004269460410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 334822230 1250 334820980 334820989
    0x5150403050d021602120316140f03030106080f010f0e1303140a180e0f040b13060c020a0501050f010605070b0a020f0406260c07080306120303010906050913030905 72
    0x6800500c00e08080d45030900b0344046105a812016260000000003668101075081c0780215940004401016525260121401d4007d0f0806484058042c510100305103003004000c101c00d00002c1c0d22141200d0300c035a500c01e002000c91004461080c81c0030300c00b4000281d2407401170031020640b5102c222102042c2c0d60390303071140201451710605a0410594040400c1d00c0c04100e0002e00420042d40da501c44440e0740b04580e80b003070000c03d42c0050070310701d56503082000b5a002c401365550010784c0190381c000703592103400400d08004440030028151a2400001003441500000c1590030a4800e20003030082d51781c4c064001c6e001c00801d00c074410120f03070200a03820026441c801f416522080513480103041c56040054400113800540002020072010050f09800c00c0c2c25000710805100c07002e42ea007149140044448407a4007503440010030040000c000310744503640d06942e980e1001d00c401e003241d46035a504d00a42c0090a20352165034010600308002c01c1094003409a19002950140c554542c2d1510303140c00d21 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 334823480 1250 334822230 334822273
    0x3020402280905280303050715050c0408060a0506010509040902151209071502120306040902090411040609051015050d020406050306130e07091a0301020c07030302060f0405 76
    0x104505007264000c03200d50326070685880c121600964a0144650502060246840c14034038501d84041c5021583c18809100c120701206903541460655102c6880c0c1c03420100c2c118042e81103011146c100800c2041405038600a0310480700030004542440d01c490030350314100c0740140d03541d074009002040184014201900240c06441c0701804014410b54401c2010610340c0100000710145100780091081412041215034041c100803401055200e46d034400c065a00c6e41e001400c00300301c16001c000035002d95600d0703003c0c0450580113400114a880c051402035110046000100d10991034148042900c214600c141c0d80700d102c40f24070a94285052501007194540222003040c1000000c2004100765540c0d0700190000340002d0315682d40724200b0380100415120710030558800903141112000600340000361940848003060030024200d1500180200301d40301d501446074156000241440c0311010018082c012030380030b6400c1e90015280c00c00c43c0e401130034090b900a0b0482d4403d6903d0041d2070008503c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 334824730 1250 334823480 334823497
    0x3051b0d09141809030904060306090606050a0b070f1103060406060303090f06082a0a020f1c120b01020304080d050c0d0503090604141006060309050c0307060921020a23150403020402 80
    0x316030070591000c0000c0c062340c0d601d03081210142d4840802c0001c0054602071040038010454a0a8416007030003d80f01e00c0340510b28015140a41c2c81380a4014001800034900100300081d0036154a890f040c14040c000d4030b0241f1080700010000c2d000000e5001840c02a6802d80300c01c1c0e900c2684c02d03245c01e180c450034020010815441d03145818203144550003184000c0c061625290041c1a1617046e18903e1410845080c03841401500301c00c5428400c60380c0800d54035241e61082d507000038040c40200040707103540102d403c1001c9500c5103054000040c0d80040140140c0041e020484803d041c2c0504101c503036001c10b6604650992081c00841c0004a045201c9031040381a00c0c1242c05007019120340e201928203644c8120007281c1c0c1c03032120390280300040c040604000d50a4009022251401e80014817045280c811030654000c04050f00a5141600c10b4047d020f07600203115001031600d441c0b0760700905200d01e80c039071411074003031000e00240e003001c0301200c500805041120f0305192a5800380400703035012814 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 334825980 1250 334824730 334824733
    0x20319030b0604061d0603100e1003020612090c06032701090503070201050f07020a12030e03120412020d050a030203030907120804030201080a0b0406031101030e031207050703051b0d09141809 84
    0xe440c905e41d11210040e506c90140c08442d101403a240400709100c005002c1c1c003006d10341c000c0e40342c01d001613140c000c21036210215a4190900759540c02020a04100c0502050b607409000042400306840b0070540400d8540c91514002e40c1c41207103030004034202c429414008100d50800d0042d00090760180c809030846041600c845498000309500280040c0c60315006004000300455600090613404661180c00320405d07402406036550754909480d0130f00841c4101315030104646440002c540300c1c190141801c0f03500070f0855644031000d190280d00c2c0c1e003044411001c00d200b074000000303800d040c2d2280c08241680000c252880c09045030011600008000d0502d4a21522090711031503545072845a00000c43c059036002003450ba6000005099580f080f803c44c0c0c00b58418083e43c0401d42120300d04e2500701d5068200305a40310360510703094446006a030780c4100f40c2503610000c100b0310300c5e000c501308102644940c0d505206548a049a40242810390746003500400c00c043c0c04103000d11843c2d0140d800040c0b890 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 334827230 1250 334825980 334826027
    0x30803040c0b030a0603120c0c05040203060105160c0510170c1303050a110f0f0a0509070c0f0b01080d1106150f030a050102090f030106180f0b10020319030b060406 72
    0x48940005510135281502e0079981d42204106000309200401c4220503e49403400b091805600c034802c00002d07030b0150030f10403076000000c02d041b030b0300810840381d840f0140c4410162101c007034107062081c00c000b0b1080b18020640380b8034031000350744100b02200c01e1294101010b00d8544a46a529409400070128010481503900c0c0110200e40308100300340200d032090110300c020403509030600c0102d098503c550390050151000d001020354607199400700381c0d81c003903400300352598403880100c0708800800c1c0054605404c0581c203500f80282e207180b86041e0f50501d0116002001041c070202c8041c3c05250f0400703029007142c0b0228400941020b0080310f4200018180203400050a0001e0304021101004458684d80040c2c818000d045c00485060341c100d04030002c004c1070340f503d961400d82c9280903900701d1145560b407000240100d0b180d4400c0342d0040c8040c0c51060410741c8840048c0d501d5008010388007039000907000088095119001e9210654400ba00c5241002d240450035100c02041c620001074070182c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 334828480 1250 334827230 334827239
    0x906140405061005090601050d0203040204090f1401050718050d031107090204080c060a021519060e0108060f1b0a0c050114011a12130212010c0203030a0c18030803040c 74
    0x8a001406a4021400341c485030421402512400c1119031160740503091200c100300c0540e801509a070702030f0594107000361b903950303072440003400030030035844000d10008040780c00034144441c1c0c03084102100d444000801264a032042c0566249800d01e5171004200030107101400316041028501c44224403905014071a201102c00c050305010603a0000e070b204560200d0100003000c402c2040725032098041d10541e1610b2a5008000c0d203801c104680340020f01c072541c0105440c00c00003180b140031000f5000e03003005040d40b1040c803012284028480c0a1041c45090081441c0d100c400e68082e00408007189003001c044400200d14803603400125225080c00805000c1e00c0110b1030038066400e204803004c480020541c1015440c007036071151036070984c851034014810340b90304034400c5136016040505035401408a1440380b001413000c01081008a21a5090580d400d11141c2c0000255000e5640f040081c844c0d40c203095400c440040d455541a140a02584410800b14016000031074116004408200049445 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 334829730 1250 334828480 334828511
    0x30d0306050a03061a030f010e1516031116050604020a05180423010608010501150504032004060302100903060b0f010909180b1603110c0d0f030b0a0b07050d02010209130906 76
    0x1d280d80c1f225103944030482c004110b501030001540300c0500c82c410844a007024010602c441040358000e20034559038198a841c0080b5000580310748940207412008000482d18100c4e071124006c0e0b85c101d0040a804901064a02d800d0082e83e40c20340c500100001c1d1555152500380501c445101818444000303000810340e455420300450014000035800820194504801002c03103600384050001003200500c41440001d01160040c0502800d000d00306850409031000038008025690000b50b000c1880c01401300e0321034000f40100c0842c7d00030702003005100101e4080c00801020221040d002981017041030125003116440034101c60750610f000d410420150341d8810310f64600b0b60b4929105940455411f2082e40d150042614607244a1411402e0400d0484010383e50303a004417900b81440b0110f5184482940301758001d40711290000c281c2e1211640c3e50b80003030480d910450080d00c0c24060a01c02c04d20450050084442d01c54000e0f0900c1ca40204403d4114020000b035902181c2254859902400f01e001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 334830980 1250 334829730 334829743
    0x12050d0609020c0606030f072312061008030f1c09060204031406090d0e090a0e07060509150c07051c02091e0709080705010f140403060b030d0306050a03061a03 70
    0x4039850050ba542c4403d18580d10308240104420f00c40d5000146294018801084200417100104058441070006c0f076050101c04c1c80c103c0c00181c2001b106490075900b1040080c40d40e006144481e6012030454a07501400c0d1644030303d95802104107030400400a22641c250142e11f805002e01000148002c616580e46d010b0341c0c001d41c0107440d0801900080b501e04181030051a40005c2c52000900c3c0340700005002410101e1b101e45654030a501c0c540029403030350042c0e0480f0030808411000d95102c0d6459400242c0103802c2440c2d110b02803640345901044003a0660211910340f80381c4002008503510704010090750307155500360300d909925500e0050740141c4034118600d014a00d11288500c8501001c5800740034076a00510201c200009a03404102c401c070041402e5094880a03e80a5024200c0c1c480990380c8a00c0744211490030030000030700200f40007091744450411b0300c0480a903001c1c2501020214141da07294051141c2c0400c00c2030003000064240d1707015098201079203840880c0025000c0c0020700300704 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 334832230 1250 334830980 334830989
    0x170c0d060306060f030c061704170903070f15021b0f030a05061006030e0309010f032309030901020715020705040c12020a081801020a1209020d0c03050a0c060c0f12050d06 75
    0x2c2d40104103004002c1d503014210050b210914241c071710f11174142c8c01c4141c2503501800c098101004450b204c9540604501110b845d0400030b41100c20807907480c1e0f18400f5400c61449020700f04000c0d0a6441c100d2440810000c0308900e840314150820600e00c3c0400c400d0000030700009134184540c1b044500018800e1040d00e2080001c012002c2c4400c0c64010f0140a40302c11040c0441140c00030802201c00d6030b08416840c48071039142c6000103021050f105000b8050b0b41c0303030582c07100300d0300711004001c1110700000041c01c1d414802e0b0b099a056560303a081890136040d03505003d8000da0000e000c180581d05090380031001c9101e8504e81003908086c42c0c1819012030f480009400c0020700c40008001c80c81600022403201c55210b41c000310701e455a0702d90b0007014094403c0403413007540e4685c40d80c4401d41d0344604081c0c01035500301301000540d80c2c1e03074078005035141c90300178044811008802000078070354012589046000e40003010f500c42d110b05555090100f0240003c0d02c8103000c01400701c000145114481c180180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 334833480 1250 334832230 334832249
    0xf270303070206060d0515040804120c0518040203071a04211406010803070303050a060812030a051003020108010b0705012c0f010b0f131e09060c170c0d06030606 71
    0x2030500540003030514a009101314040c5818036800800503500003a18028850035094074401d40c0c4a07031a00b1001071040741c0c4109401141280c06005000c1d010303080d1011590116a034080c85035110b410f28100030b500704d4029506810012040011703d1050148442d84455594690324064660000b500440c071400e4051742040829000c1808109000d4041410791880d80000c040d95807405407101c1e668403920714010b04250b12a008145003907440c0c1c07c00409815040242c4e842c41000c004200120f03001250201641d070708001c040340c0100c010002d00400d59806a45d4800c2c0e82c0c3c00c0980a00c419030006404a50031b66840040c0005040d4a609050203d90002e2221502c3c01e605010107142c001d1150b18183c650745404d032503a060703540d000c19500c100201981d01f00c481d070708c00720304000c02803008103a91000d92071188240340420005502103040c0500c1200100f107100c6204c40f0859524001171810750325101c1c2c003000325a40e44c0004018119a5402d2100481c9903912503403030b01c05a5070355912036500c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 334834730 1250 334833480 334833487
    0x9040c0c120201050c0a0311040806070305040b0c07030203070807050a060e030d0608070b090f1507060b09010608040203061f05060d0f050c0f0415030f021309061d0f2703 75
    0x40180c1540e200c40070690340e00c000e03c600d0030440b000c030300a40305d140c005005065644010400d42c104110039a0005c21000d400c4e10100d00e00b448019025010882c2e003202c1005a0380000b40b2070f14006025101c2464043c0d00650a026040d40c83c80300c02d9100c500180c50511518034500f002407054050100404005005551220f19050300700c0709a4080c2e8001002c15040300200b4055907001c64140d40c901b5070100d0702a1240c480d8800803544101c1400c407074200c1201d00040b1501400060781181201c0342e030070b40f40322040381e985801c200d4845500b82c500951582043c0045810740d1100b80241c240280141d01540071107540c0c0c00001c000ea0305c40722007146180e4955040da0304104039441055070045840c2d280070726003020501c0e2240580320b50300800075001d0f0810702582c0650311a501503031149903004c808564401c0301903250421802d003446103210321820300c040810740050b48026141130643e1300c94141942d89483c9012000391200038107030101d0b8140072240f01803072851041c00019607204034024564 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 334835980 1250 334834730 334834733
    0x3060503010f090b22150c020c060903031602061c0b0321030106050f04121109090c0a03020609040b030a0f061803080403050307032d050a060509010b0f09040c0c 71
    0xd482c40080c032030252516100590021508200600d40e10018000e0380241c101880030743c420311020710810242900d028408200a902c0c41c0b68810b425840b03403a02194510503c0c6820860703644074041103140c040d0020311040701c0034140c4541e0142c0d07052005103031a040861036265030400340039084403200c1103512560958a24142404516102c810501d147c61220700c8000b000000c1c1c0c84180718290400c240003e400703040c01000d1040d180031340850305000103400e0203070508010b03007404201c07040d101d00c0e090f00100380d28540000d001a001c48000c0d0a042c070003450b5408000c50b541045856070782090311800d90201c0c40c2d0782440798620940c819000a009000d0070308181048544a94005140c01c044540d0140407a400c01c400700c2d8065410310385603940b03581c2e4079000c8002d0090f014040315480d0014801643c82c45100315800e50304515208100041d598006505065400502c1001c0e0000d007003d0040c4290312508000f0300c0051b91101c3e08078605480e41c1e01107004c44100d103c80000080c1660314000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 334837230 1250 334835980 334835983
    0x615030c090a15020a0b150d140607020c030c060f0403021503101a09101704080c0f120a030b031905010204090b010503040507150c05030c1c02030c060a05220303060503 74
    0x80180c200f000c4041502d400d0280040c0d990182d1880142650700c05a0000c0d001c00b00c202d0072551000c8000e450200c140c591460954014140f88400e405140030700710004900c00d00c0020800c01da020010010031300c50b1b2500003480080c4c0c1c005060389903100c00030480800541c40c4d200705281c064111034061907403840c0000300a210311640d070b04203004814101c0f2000c00021501030554003840c8040300c180200803030390002a14580052508014051803110803c42071044040c00382c890b24242006680d880d9117054115521403100c09502c0550311020701100b02c0e0b44e4482d0f4440318915501608480c9880000724078030081040440c01150315a400040c180b201c800140207103a411042030030001d05504050f03444a8549400b40607440341000d40001c003110540c40b8071102000907800c04107903030390740b000440c5a58030f42090031841e2190078208489200071510020031214901e109901509054a0f289001c1000c0c0801500540c501c408e8040407a17404101105054443d510a840c0010001c0c540424075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 334838480 1250 334837230 334837249
    0x3071a011e0f140a080d1701050a06021c0e120109031d010509040f02041a0304170408060f060105040918050c09060607030c02060f07030c1104090305040e0615030c09 73
    0x202800524410451484500280c0b82612900180d6000c4a1600030204509104580c06a49188550402c0310192508841500440e03511555866600c0c3c0e26003013404034050031031180b900181d000a080d920018000000b02c002c48480349051003c202001e40002c1e031240b010326100c0c51070b9642c1c0004004054100c10107103100c42070100990310200d120b0340081c2860140e500080e0045807079880c2220703181800c2e4125030180007091100718620041134004800e44e041200d0464080390400c80500c800c03510401034404680301480101419515802c00380485c08015110b1410700c00c06100120759841140076004d000710510a601d006d0700b019040c031900d0418060b0505000321180c00c20b2000f42c0e1525011200d0664240c2801410241c40344007080f254402e03c0b00441e9403136008100b0b0410160f100446030f802e980100800c001c0c0c0e070340250810088800c4d181d00203020400420040040c440c44404007036020704000e000303508180c2480d42401469004903295040c0c51070000d444030b03580ca00801d01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 334839730 1250 334838480 334838519
    0x1e0a05161503050705190c0501050c0702040e030304020d021212030414060a0c020d1416050106060801170c01081e0103080a030c03020913020f0c0109060c0314060a0b0c03071a01 78
    0xe00c00f40c1420800500503100b4410350719094030103441c840581500516000d10410703407050007000580b800a6080b10150080ca0080348140c1c2800c080e82c421070000401d80717000d04c1e001010301e00d1661540e42040741d92682e803c1841030501400740d4401994a100010b14400d5014200480c1c080c2201030f4020306101d00200106801c9261a1181c01c0c1030b90f0008003801035a4850610390391702030f6400c8010b503d6000e807480d002c848452810840c820401c047d0001d10031070301e0030348895683c0c1c4d8031100100c103800300c0070043c1e56155012600c15445580b14042e803a4010000b4040b003c0300c408000c0713940700c84d40c909030000c1c2c400000000f00082b03840d17072505c2103103104001494218280b441c3c5000082c00100d6050340326072640d401045030950030000008941c03050078054020460350f03070ba51400d5805403400070440c6012030b00d0116000302c420050707849036201c1c100061090280600301000c00b4241d400520030030702709100030700440000504240002d0342071007030f54058903060b6151080f42580c0360840501d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 334840980 1250 334839730 334839737
    0x12050a02131a060a02010209060c030d2f030a0b040c020c031c0c08130506070302010c0315080d030c1202041e09090305030a0207050c150d0f0c021e0a051615 69
    0x800c40910b90899003042560300488030303160f4079040c50904a0183c041c1e200c4540d800000000c50480b400d00c000002e0840d00c010403c14044004a10707140c00407502d101e02200a030f0025901044152042c0500440d8418620f400004424600070042000c4484801448001d42d1081d03044000601d0100002a500310b41ca80c0801c0038a0f100000051030a90522001010b10710080764030805040c90105500103441c000e00f0454407a042d6003402400781005283c9400441c0c03400c8031214140f0b03242c09200090310782840c000d00310041d03e0740d421002007100134400070422440044998141b0380c03500040009001c1000d14002e41c01004140400d070b80210750182d81310710701c0c281131440040d422005483c0e002846200041c0c490b4060305081d03081c00c52411a195103e8001c0c00e07003c83d0808100003810805010781d50400c5441191000340701150041465074016a0028100300342045e01c41c044085662010790030782d2001c400d141c0d40c162400008244546502d003000b1030611080d041c00603005040f401600c1e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 334842230 1250 334840980 334840991
    0x3120a0302090915012a02060c03040603060504020304081c1e09030e060309060402010c030e090a0c11121c060b0a030605091014090606190503061815010e0a12050a0213 74
    0x70000f074403140320190f0051b00e014035001041c0030706420040706030284d5000b81490755540400000746499500c64020000400d20f0f040b000300d050304051003640c4c0315903071001c000d5103801c0344040c20b040d034481602d0601e1500364032210301d05000c5051460900110003008030215500d0900d140103050300101105450244800340304006400c6070000c0c07000d82003502828940302c01242c81c10102c64500b01e04150640081d0300c0801e02c60300c0e0080b036014042c011940e81d1a800d81740001e01d0f8850f141c070309460b141c0c0b90004080c492848181d0a00d041d81d5048840b10100140f941c1d91034400d24419000016804046551104200514140030364000d030b2101110104c0445181402c007600620001d95003c1402040300302c00050380386c2c841204030740b80c107a0010605103103001c1c074820041c01130313000312041802800c548862485584003404424000d44600d042240201200030044445803000701803658004c400b00000155410342041e0ba02d401030081d00078100c1d0141500500040082c4d0101929100d0f183c01d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 334843480 1250 334842230 334842271
    0x708030a0905040b0f0f0102071a070c0b030405071521020301030507120b010b071416051201060f090e0106050d030309020a050f010c060509160b030103121103071103120a03020909 79
    0x1409181422900306ca120940d0002c00b40102d00e412030301d8009000407000d24800d042d40904010240800c50700c514007013140c468903102034404074041980e000300a540301c140140b000c0340b00d0a1458401c1011803a14030120b001a42c40d00d03c840109101c1d01007102d5000005000307100c410701961020300b03c4418240016001e41e81d07220707180c0ca0144558001441c1c0803991101300b220f50300c100e201c580540380481e1100005068240881c0310b0b50712407148100340c0980d40c080d04202c1070003a84100c030002200107191a03c2c1052010140101040d08862550b17110004510380d81d0f40905448980c0c000d40e40001e101030580b0600143e00700a402c5a40f003104a448a03905aa038001c402a08aa9200c42c0105e9151100c038650f82c505041c2214031401c00204400c00f1602022100146040300d006a00000c0020b5142409440340b005170085064203401c100101c50108007001050158154040c0407640341140080e002c15041d08804880340c0001c1c0c00290341a03161800b0b485032904012640700e42040100c50 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 334844730 1250 334843480 334843489
    0x9091f03140f0d0903030c0515010b090a14011205060a0b030f0907092a110105010b0715050f01031e23011a13091401021801020d0e0306071d030708030a0905040b 71
    0x30717032000404200c8200e24840400c001032201c4400b49960345c4500506c3d50b100d039645c249580003501558001e44188070000f074442076540303c00e42d0491041c2c40d105520581c0300c10410107040028800758000b0a40500003412007541e900a600c11541e941c02002141001e288040c103105850b48000025130a00c1455541180c02c45d5a81c9500e603000c0c401d40e40c0c0d1031104c43e0152162140004183d1542d441e04000003100c074050001080902d2007541004220703014a6060803c8580c04e60341d0041480f949401840040e04d00d18a0101c0c90070020484070b0401595620640c440701c505140701200c4900500d101d9010200f4000d0b10110050385111000100e01d51000c07448000321103400350340083c0c540e8085000c0c0030100340c3d500f0780c0b109194000d650700d075160110109802c0c90511481e0042c4100364402211078810b61040301a060000c01410740768030341d010119141000140324803641c0408810403d500d42d0104400c0006080c06d030051516801030f43c0001e841880c03a9403106000f98242403003034169598 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 334845980 1250 334844730 334844747
    0x9010b03040213050a0e07060305100f0f090203070c0605240409170a05040504020c01050f010e010602070b030c0412050616030b0d0204150f0e06100507050309091f03140f0d 76
    0x200c3c0d0004142d42c030008080d000d496002d4402d401800350307000c0482c001e03525811813881740382c010201c0710f212603070743da4001200401d501c151010703454030500c02d000c9a14250000e64000300d0a141c244290322080c1c07589011030783c090303031040c0185804904858054001400300d000c82881241c04004100701c1d9100e000b440c40b04104800c00025000a850031000e010b135054030b01401d03024000f15104c64503000302d00c2c0200400e0391881005100400002181000313652181e0590f200707940586806442c00400001503000038081403d905c0007400081f1b140204a104010068019070040800b42081a4821150ba840c00f00c40c104240c100312150300d00307441701d5090284c080d905640c0001e6407005402190551640c54011040514549400050b800310449085004044c2124001d10291028005550520410310028440d40040c02408510303d001140554013440002d03201d50703010b03146100700580f200300c0d0b0401c17644504142c0085242880810101c9061480c080040078804a60000a04070380c0f03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 334847230 1250 334845980 334846009
    0x703030f0c15110d06080c0910081c090306020c101d0c4605010207030209060909010e030c0d121814010b0d030f030f090305160f02130b09010b030402 66
    0x1616401c00c04583c107a2070301260010080c03890100191502e500301d0548840c008000700f842003100b803001c16105e9a0080707804007200c41000040403072400d0454110200d141c1c0d81044010b10000401c000702040c4607000821140c003840d40500340b2400300162034812201c10002c126842040119040700c0c1000010314000002e4040b100140801030b001d01c0030254a20600c0003800c1000900790308404150300c842800b41c0e600611490038801d6480c0c2004990754181880082c0d0b04c03901d40004a181411b005891907001400d048c0042040103e4401041c6540c0c408055441c041d8844521080e801e980130310004104021b5107418041c5800c000e01700300c042d82c880c410282904030340b4501c001c0e20480950042000680c090455064503009007000341c151313841000078101103410001c1d4640680070714850315171410381c5612030b10308000e11800b480440d400102c0f011030720171410200c500d015039111413112140315000036000c510801d00c001401042c44042c0d01070030100d5030a00500c001039031228084111075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 334848480 1250 334847230 334847273
    0x6130e06070509030a0503160b0a0504050d0e031507120f050c0403020603060a0312090e010e091b130612111002060a05040201200d1826120c0703030f0c 67
    0x1d02e83c101c000390070840c0380d40004160b44400130f0301401c01b80e000100e0411841c02040412019a00d41c41d00300d0907200308a40092460b0003040c440c03000c2c00c0c0030780380d0741e0712f07401e4003600b241c0c4440c060100380000c240c0145d55290201c0c603500b4500704004818040c2402803044007005020b9420550780c0d62039903000305d000003482141c0c00710004040b0388032191848002d580140004810300c1c00d116000d0141605030040b680526410030000c9160145140024050b541c0f800041c10140403400d00d440114100c0c840b02075000d20400c3c00200020024010300740a00001d00c00c280906580d450301c051030141c020540741c02044400c07420242d0540120b2039660005940300b02041d00e64a5200403250403807844a02c0b601100554401c0c4800c01e03000441541000282d01c17094241d19034240d601c00425040d103d160030042d0004206150b48601090500065902c0b00860303400107062520266641c1000c201801039502c4948100241a0300008807000c01d4a2401d109820006075150031207510401d91510581 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 334849730 1250 334848480 334848487
    0xf09310803040302012f030426030a06081605010c03081009020408070801060f08070b09040f0e010b091528080a050f060606040b070602070f12050a02120301052209170306130e060705 80
    0x790270040d098200f1030701002c0b41c215502d250022f90440240528000c1041e144140c107100403030b40c42e50319220415a041615800100c20207580c04032642e100061482520710300e00f0800140259407400500003038a10480545403840c108a401d50031a000c55110130064190f840d8100140440410082c082c1c81408010303aa58400400214009e131010002910300246001020404a64194880004203200f16500e01035520b41085840c155040410101c0e404085280c09103070002051107015034180030389495a2401c1c1c1d950b0b03080390902034142e0302601c1542003440103500061083c44820343c0400e0484a050805050500701141e9000d0103a004014640c00600e400520102d54112081ca03540000102c1031044420304c000c0c110f8010b08004d0f030240c4218584010b00711400e03016241038810140008030410303103000940105c4942d039265055a1030f0f0f200c2e00740001c901090200141c5000300078041c0c4c0e03a810080709014624440c8144040003d1412554111004001c06c08940018040c5801c545 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 334850980 1250 334849730 334849763
    0x150c080705031e0f0403030b030f030307050d0612260a08180312010b0c0d081e040c0b0d020a170415050615030103050109020f09310803040302012f0304 67
    0x310f4544030f100f9803810340480c404110031000c2c400074141c4510300c2684c0601c45401040181591107800844a0301140c00500020352401d10400c003420f0818049180030a02c02d540390b0030b00c1141501d411050b84c50441901d07a400000f2090b842410120251a10044c40e112007100f00900070103019000d502e0f002003401001c3c525031001c00c00d81e0f640301c541142c100c44650355034011420075440429400282d000e886040b424103070144140a02c03c0700481052003280d52480d40d01d000c3c502000300b00311605600c1c003801050b01c0003858068920824030003001a501d02180034050004c46c010742e01b155200d9145400c0100150092039a0b107402e03006514041500c1c0c4512000502030403c0c00010442100040000010300005411a04a250007542c0080102140000f440310221b400c81d030000c544020003102d40982182c8140103500300041042c41e0343d240c000c5582d02c12040c1e000342c400343c0040c2e458450217490b0040341c86980e03065843d01042485000c0300007901d8112808010806880103840ca01d00c0360 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 334852230 1250 334850980 334851001
    0x4030804150c090503010c03090201210612080c0601091a1504090207060204140f0a03120203040909031214072118050d03050601030908070f1a13150c08070503 70
    0x440201d1a628240040107031400001e000c4229449954440d60a0056156042d4082e11504604d80c0c0c06a588104820030400c0c4c0c11400c501382c0e400b6650086e03469500050100403500c501501364401c0304030907564000071484c2490100107800501c1140e203800340c1e0380300c0030902000c030104840083d182c580d0200b410464050240c0034541c8181241800010320000f00007159008106540c480307200101e80f11446000d00030041e0103401c0e900d40009003281300384003003032011140180701d500c175104991400c0e490300080801d070740c9010003c601080c082110401c215049024035041d004240250151603d0401d100034244044070b407078080c00300b02e10040710078049403d8014a440d11141c42c40f00b100c2181e24502640c1e1010030541f03100c00245844040380156101e8050102d400c2d070403403105410305490340c641c035002c07900040048400c05e07111000e1154201d1704c1c041da244510404081c19800621604021140a48000155820502e060101c0a203140c0100d001da0304003800d0325005450b030303031070b00350300f6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 334853480 1250 334852230 334852253
    0x62101090210020c120d1b08190e0f010e010509100e0d05150702071d09030706060824040803010303110307140d0f050c0a08090117040c0509070804050604030804 71
    0x280d0041e00340b030502c50a06030001030556180b0020b4841e2019411203030740c41511240d503040c4002c00910034a01188098500c001004c01c4103006481306840c05c2c0301c5504c00b502c01c8a40d052010040346102183c070440b468201c1648040c2402070130b040b000303116200c000800d18400c010360107100d10204054400d180388122222242d0403405024014525a40c1c140dc9a990000491490b845200d03500014156413022402078200c4945070b000e401c1d0078422118549810030000c1028056200c144070040216045008110061407108090b04089403a00e080f126640c00d86001488168098401c0c4400903141c8021281145d0b01803900b0541c8540c0791840600358824050090810483e02860080c2c1d041c000c42c189406c800c00307031901e201001c0c440606645174010210001907503080314034484046803514000f440344a00514052501f400400303085141c0305c4054805850310b8a000380140010304103850081e030004c1e070034107040015140ca503941558410b03005100404218021001c50104218515003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 334854730 1250 334853480 334853483
    0xe0102100f0b0a0e040c081b090c0c03031003050f0d0c0b040204021e0405040605011407060c0315080304091a060a032c24090d030b0303040306020a210506210109 71
    0x54120703d6552004c8550302d54058805988071520088001110500080c50351601105800090f21070368100c1c04010b10350350002c00011200b90100440c0441001c144025446419030700201c2e03a2190842c24020b18109070b4811004007a400041d0f05007903590450001190f40d40e00400100040d43e65101003006400b0300a032800403c0120a1711240c0d585001010740207076841647c041220a54900044846001c0e0400f9a640d103a010040d1401140d038a030041030340343c42c0900380410f03405844683d581d41c40d0365a034041100394201103001d21403a4058081d190010755080c0d0310403101c0311358070009001b52090303104d40014107503174416099008a100d803540c4404044035075085051812072a5107a1074160400081c4803a0124400d0342c81400c0d451039103d0b004484140c0109461912494150b004203120021103078107110900000000400c0c81c002494408110fa41e016880103003100251090605680e60304421410401044291b440300c2c2070701d15490841e0001c1180d00c18100c03034440c1c01003240400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 334855980 1250 334854730 334854739
    0x7020a0503011d0f07050d0f051c2102072114031617190902030f010c0201021306030c0203071104020c01060303021e030403021503040201020708070909060c0e0102100f0b 75
    0xf10b5a84800b054400e04400301403003e13240300b18054080e00340c0302d52036401380d00c0e40036001c40011b4011648101480461030310500480388029000d081101c0803051990742d540000d4000400c04101100e040d241002c0034002180650800546a4400c0d90000c0b1101242503035880c9403a08100c628070801380c41110140d440c103065500d0510480d91074900b07660100e145d002c5108420040c890700840c5030124400c003481c1d49a06400e103a4034820740c01401c6c0b080001d0b0390500c50b0800380e00c2d0712242032098106041c01600010b03690760303001b01c800740c80c0d0032070380d2007c02894a012141d4000720340100c102c9184a43c0648030784107038846080010001d004d1456022010341c0782c01c201000f0140c000844401c1d40341f01c400c00726000d00364034036820342d45e00c6507000003904058500c8480ca01c4007918009150843d1050050b50000340c3c8500090745000f074540e00030103005885000403814011a441040100c8400d890403c90301d628440c0042d5454040d5080d0b10661542c1f07d4084217024201d91014400e0302c401030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 334857230 1250 334855980 334855991
    0xb03011a0f0a120605030303060a0b160515060301050f04080715091e051902130203041e050604021836030a020105011a090108220c0b0310060305090a0807020a050301 73
    0x14008283c008a00c07000da0b8003510b44030002c00c0c0d6140c0081030320301c074140081411507968100041c1c00700d00c6e005445003018024110854800068003427004480c1e00000c40203900c52454800101400c0d140040c01c6004000c440d5024800403502d810202c544445d00603204500e02c8000110b0480280610040a082d81480340654052907841d40e250320f55190081c022180e2080101e401088030550761480294007900d040003621902549801a5611a000340003407800a4039401d40c28944407086001120325401c00b1040108520703141ca98074030034002248028603c1d10300804020170301582d2001e03200c0805600d514101600800c4070010920540e0a1b00307681d200c1c5494400a80030301030038001c4070400381080a075014203d990200b074400d107140595941c04952590f20aa5515681c2e490201400c04000c0707200101180745e440041d801458070100940d501d1074100c0078440404016040b440c1010f0400c0c09000035810001186002c0a81140061303558840c030344000b62152031070f9403148ae019403c05 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 334858480 1250 334857230 334857247
    0x8130f0e0712050c04141503041506270518010615030605060a170403051e0702011106010f1707090507050c07060906020607111e010b01030c08010b03011a0f 69
    0x19501402500705032102441049940009002d6031412500c0b1480020180800c010420682148002c030f5071003d0700740c00e511060125407031030315803044400b0303101e000e0ba584c41c01e04000514802e180c0100060301c48210242526195140310844c8441d01d005d0705520b80021a61156100d6030103061420940c008000701903490788a80743c0d0f00c003184c80340c001003803a000e0b001885051040440e898042543d40d100010202d014032000c1c074030f6010740150304221040c050300c150950320350028031008000c0c41e0099119117070342c800101079504008407640143c001000420012084071800415554010148a0408000020300c0d00c2c0907031660001007154240818040b00607003100081016982590507541815110201034807d03408503c101401a8420000074060501c110b0303080c03a00102c0c2405131001c56040c03149248200018a0450403141d64032201008a980c142c41400e100d03019909181c8a00d40c903149541c1442d000520610859202d121203080303008142d03004440340e205c540ea58482c0ca440e40b4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 334859730 1250 334858480 334858499
    0x7030b19060e0631120602250b010504020c01020f12010501020606061e0d090f05010b0109090905061609050a030506090607111903090504060b030a0510050d08130f 72
    0x300e00c0340c0d10104102411150050400008031041424905145500e04200c1020085201d00301c100001c041d0400c0e144c04102504003800c0c0709900381c0644800341e21049000c4601705601036107003003000a00c006282c0703a8002101c0c8548681120300403a00140c0350080c1c20401c40c01792007078000880640f03800188414a0340c200f1019a416198284d003290081e568007024030006100c1c001680081c0021450601484202c040082c025013a11a1010034078808594550030030340b03407903a02211140d45942406001c0d59008195100905c00502d0070301c9551101c0e10390300d84076140a40f60400100988684154150245443d03e000b410040c00051005650303040041d120281682c0109441c02074501003040d41d44507000032902c40e140d0344090720051140000045903154088402c605001c0308050001e026912446110028a4448050745d524a40303241d91004865001f40b18a035140700c0701509008981303440d690401c4050b889a240c540da2280580049490320070740e400312002c00641407000c68500e03038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 334860980 1250 334859730 334859779
    0x120e061b090904060908040302040905030c0606061c0f0608062404050610080a0f050a0e100501080c0105031806010308090103180b0a2004060302090a080a03080109020307030b 77
    0x20198010000c192600d0305030811403088820701944841c1e00c1002c540455031680c0020795191103202103500d0540d132903000ca0250b42e21820107503207981010807840d02000c0284a601d40c0440304450342e070320300704015403401c610401c1040c81c50056503603002400b444094a610500c090f103015402c4803050301c5c5c8540360040d501da030440d201000420351b550030f13072050800d4007030580030712801441d424100030351400c02c84800384000c00f240026504c03245010300c070f001d091140a005085c8202c000c200780032002340340362034003401404802c2807614080c01084002070101c2d0503101c00b1001d190a90f5a5201c40104080100300135045801600510000008100d83d0f0300c024122090280c80c1401103940c0f51004003a070346030051b009085007104074009400060964060354002c401c1b0b042800b5a180c0045901c011a00517401040c0070035400100f5006030326040a41c540280103045c01408480381d680e8004120840610071211000c5c3c011001c107a0b00c038025041007102c01d10142c41d1448410f00c601e2031046141 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 334862230 1250 334860980 334860991
    0x411090a06030204051819091b06212406050304031d0a060f020a05060108030703020f070b0702010c060204091a090a110708090f10020a05010f0b0d03030c120e06 71
    0x40c0c054000200c8601a0083d541103681c014500c900d520013519404100302c0004003081c07542110312150700040e220324031940000a002e801028802c040e541e51703043d65801b49800800900c51803075901c10204015640200d42c0d4800450046042c10303111741001191081714010b007941174410400451403030f60210207184654007940c3d40d41d2003007201030300d03000072100d6100c0c00f1600001c074624144050f60040140050480c1c0c03610480d074414025841eaa800c10f642071300140207503000000d001c402d040e810442103886082b860050f2003501e151003040310f880d1240ca5002414080c080000340f0a0203543d6054800030800000144202d100c00540c4d05224054401810f20075074120002c26400c50061066101a90281d42c045142141640b2100896000001b0b000c3d480003180000c180310707407100101e031010070005400800503003d043c0741050940c4c50181d000c480042c07800d0100005030399100c44004101d074244c240090451010395007100c00520a10f0250511070600f07511071041003000a540703100d132 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 334863480 1250 334862230 334862239
    0x70b030a050a0605060a031a0a0b1e280507060507020d020f0d0e0d0c0b070b04060e0c0901090c03061502030702030613030c02060d0b03010c03020403050d080402061b0a02041109 78
    0x2d60340d1180c2d1000703c80c1d0030f00940d83c115a0500c540e0a030a40254040540111041c1c28144c1201030f08000900e031319025003101d2280354011443c2000031440140c650b0769401c0894229050603010010071440b0421850f081d6415031034a040714100c180224102c80080740c100d042032010f45411000a942c400400c04220014842e011103100e6130040070945003051942503690450049840d0304201b001007403100f003580c080780301b60340001d0f14040171002419032070310414100305d081c68141441c1c0b00b1200c5100c10165140c003c0f8280091903551003c0300ca0540348030050008044c070742144218008c04440e040019015000000c01c66102d40000180011900c00c904550f0240e482500b03429580035031001c01400b00d040e11440d10014034214001e8914100e4044000034039000d800000703802d4620ba0500b101c042a0300042c18018801c040c460f00307030400300d5402c040585052650100c1e46520800c4200201100c00c41d0500103c00b0341448604a1749400030301c240f09002011400062a43c071482105100c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 334864730 1250 334863480 334863491
    0x30e1005070e0d08031306020409020a0e0a080712060e0c2e0905061602060705240105120604110d05031201060e0904050d0c020109120b161b06110705070b030a 70
    0x1031400d007110061030f03640003400a085485400b00c019401100c1107040703d07500e80900c804200543d140c8083c0200b0a400d50350f80300320302c803494240445d1380c2054001c9a0304d80c11100050001109210b40c41005982c407076000942a10a9001d2900f0460a4169240c1c80085d504d43c1c0341c8204071701994044800c074034140300d41441d880c0343c5042c0c49405440c841c15030071803014420f0003045410350384011003d41c0081c116a14005950b600d0f2070030107900f622040300c0a41e0b402c0010521503d50340055014150588100041c41443c91010356103800040005044072581d00030180162100e20301d80070100d501c00100e0f40c423401c100312001810b150074082c82c400160b019941c1c0f8401e281510090340200c0c2c014010f4502c2c204541801c6070f184000510030703814088080b90001e254201e5a410f550800c2c003c8130051498280803061000b02d1304000c5103d000c20600d041510050114811a806500e600103c005101090740590307010a00543d10090300302c0c060f0560000303500b203266000b18403481ca8080100107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 334865980 1250 334864730 334864757
    0x150f090302101802010207260f060703060608010806040209091e0102030a0c0206040b132f01020705010216050d060b0909070e01050105161e06020c070302040b040b090601050a030e100507 82
    0x3d0005444401900680c00003808000c420403881c01039141560718140b22108108000c40750385440040303042d424842e4090010008441d9240c402c40016204c5450203c109514112155079905006800644500121404114542c0c01040301030f03065403030451001c400c3c100580c1680d000b5081202e0005202d42490419000b25101040700b03403099500c40541c4000c1c0d2030307800e4514440301d0320300c500b20703050f0500c004c1240e000061071a0ba6041031001c03402c146190728080000a0034034400b40c0c0681d041d5400740c070300c0e2004101c8201e400b1007031350b0341a03549629035541402c01c03e000d0017420080e29000b00204080c001074110200d4050241c0f0f5200c440703244d1699840c00110f46034400d501501c04001141d11621001803215030444001898425210034001f605407200b44c201ea1141c00c956905031702510f000c1085003042d021b00d4080c4082100c04001e2003c420000c81c4955800a20080c104100001c084039038500035400240c000320b000040380c40d50801c90603038600410781a1209004214024407049 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 334867230 1250 334865980 334866011
    0xd05010503150f04031803080d1407050a0c0807020402040b19050a0503061e0306090d0f05040302130b0d08070609021c03021506060c0109051b01020d020307150f09030210 75
    0x201c804140ca0b0b5a521035501e0301045151010060070880c10425503856a250000c9030f60b6400340035600900c0b003075030b0350700c4101c200c40101d0b11920314060744c0012280401030000d030460141e441c886601e060400c03e007690f43c40e144200c0c0c4104038000350302510228020070012100e00140c507000c1e803038005448d107070390401000b550b641c081c050700ca10018200300002260790a0a01c1420401000003040c0d001003c50400000d05041c801c8030021025400402d0100d2045d03404101090070401605180b032030a0700703580201d201c0300c0c039401401c07034180e0b01c44003041195115640c2c582c00d100e4101c00b40648a00440c0352010262000700416481054000807000699144040070140f5a91680080043c0306100e41402ca452a00501d469401070091100c110010360a0060207501841200034151420010020b00714860b801000c1a0466124503a4201c0064002040310301041d0801c1200702d400d1240c86461000c1c000d0305810301071850130b0500400415400080300180200107240030301030f1014091064 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 334868480 1250 334867230 334867243
    0xb01050301081b0a1701090302060a09050c0d03170c09010f0305010e1305030c240702060f01061b150f0501061103040603020306121603050709020f0913200d05010503 73
    0xb82d180d049030841c83d200f4491049488000e042c00b4254500495850300d5412031841840d04a01499440d031680d042019810700400380c2c41050f500d4100105c810580340c0b95a518170301003203103014004036445402414080d070036148101040c080c0ba5102c1303192580d804a81500310498003408100c01c211081c986070b00901445040e5031141c400818140d441d580003240d5401031003402c0e90035000811000c1001c4d402400010b5030351103010300520209122200144a041300105030408542042050081c14452650351070704545040c41e04a201c3c00e2580303e40c400c020050007008141c100d08a001c03035a01c1e00c07950040008440c81c44800c001581c0d0380c84041d03c0014241030071041940041005200c2c00e17010b94041d5402000160504041b40c0c00f40001524203400310321080400c1181c0c04081013004003c000d41c0c400341403000c105504112201102e8105d40c00758000052003800003000c11818803a40358020401161080072140d098002e181e05c0c0c000f1544400511409142000004545810700140d40b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 334869730 1250 334868480 334868489
    0xf02070e01050d030c060603020a120218070f0809012408060901111b07170307020907050a1d011115010503010c02010603020f01050f0705120d0c080f04030e0a0e190b01050301 77
    0x1044a00483d0390110f0b4031030300307403101112801d58401022001d81c5607540c2d203001900700840903e102f0312042c0108120098500c0e400504c0d1031450007040720140d88400740c6800081c4e5810944c60a440700503496015010074100c0c20603002c0e10408204280c039001c9010812103d1303c6003034428035150541001d00383d514803058240c0001082040c03c8040207010b450860300c400d942c0076142d5054607110b000e00740d0002d141e200700043c0c2c4081880b07019407424118198005420f814140e02d084c80082d00503048954400e610030303c9100c0003050f96007a0340034000390008a0b0401098400f207105c4021004580b10080c01000e0096107010140300380302d401441071070143c2e038000f000014215200740c011201c80d44886941c1d8000d09090100800040081060610098408503003d444860000303400c400c41c1c000c0c03000041003201e10001d102003029a2030940790480e03014503092590035044008160382c880c140c0d10000500340d9a1041104041110101002500030002e081c17040c5000e21004544901080c000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 334870980 1250 334869730 334869739
    0x715050c0910080702150c0d091506080a0b0a020703050702030a060f050c070807080309030f0409060302030c01090b072a170d090b030a090f020909010212060a0b0715090f030f02070e0105 82
    0x162210024846c01d2495409000ea0071050300e090540f180d03100c1514540c0754211481e580c84142c0b030200e103003140074400103071035070384d00500f07402826440d100102e807005010b0010065000885d41e0034140301e40e0407121b116401600f20341c50300c81d144c0381000003855a0350030907040300d29080c00714000c5142503085545560300011464103200c0704c0d848100d00b50340f01a22004441c401000030315246050310b8080c000414410714002407903031a50050500301f81c0c1041420341000072510f0140050012034040d0380b1b00036004850000a002e00d00c0c42d2400300e140a808400e65400c500760300088611318141306502e0302460000340c400c3c0c808001c4090300d00001034001c2d0b1038014800d02c0018100401540701c051018040c10030b41a000000d9004100c3c2d09070306503042e80c0c40d6500082da0702030002d40310b0600c54100c0416905514a9480e140d640d80c05030040c0d0500420049a0309041c104681030b0381c1040c0c0100350420601e0b01c8529052502030300d107441e140b4007040540103003100029564000030351141210070180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 334872230 1250 334870980 334870993
    0x290609070c0803130c150305060402040303050409020c0c0a090606032702011407021f030c170721020406020a05150601020d050901052109010e0a020a03080715050c0910080702 77
    0xb42c40051580004210f1056526000c0041e40030603600c1c0c041c2801801d0840a1100c001c0c680d83c4028182d03000240f9107801f440c0100010000654071070115011100005001600d030841900c840c0d0a01a904a003503034001d54100000c101403126074800c40441d0030545080215100700e00d6003102da00024005050780d204007590300300265020b006207900300701606006070303c1c03d0555400900758a800c0f4002a0131400754140f03c42f140394051040110422450401c07112480440c040303a001b0840c0249060100300034500c2800b586040444909407540b0181010364442c0d8407000c00940d180c400328010346440c8501e00380040020080c060b054060f00041c1d02400020741c4808080c0c0d0f4542c060010141002401c015100d02c428a00c82500841d825141c2010804d00304140030600351100c410300c41c42e0304d03000b001038070005030ba0753b01c8640e00301c076400400c1a4a0f800e041c00c0542085136400706a00740c05043c44100805e02020700020030b080c0384200c0e40c8120022100360116044c038401c90f16080981e003c0c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 334873480 1250 334872230 334872233
    0x81b04060b09040b010c0f050303072a081303050f0a0b010f080309100c02060d140703020406090e04060e030c0610120809040b040b041a03010f02031b0a0c290609070c 73
    0x113801510b90014181465100391a85554500f0804614042614140c00200138000096032200c03600c49502c980000990f02950a5800c112100003800c0c8010841c00c40041c040815038112200d00f4002c50b0402c05449040d0300d482d01058480c020340404581da000c160001103001a2114480410b0300c5014004500b05003411082c4000000b013040ca803800e0220b980d02920060f9118001007051140880e800b141405032805455a0901e0250904007418010701060060070b0f8800340003400c460110001119646460801d0b20040c4900340c21600c082c0000110580340300c0300000d841c1d0240101142500070240d03a40103015038642c1455006110782403c00150406180681001100c94401080000e0076038100001600325003400101c20b0003c1f8803201d0540e001c0c0340a120781405161490760039891860039410f00c600c0000f80c1e94003c0030340c3c200403074801420b074800e0741d00c80e43d04d40d031010072030174a062012a4040365016181c01401c1e500d00890010301e05090032280c10b80540015250300913110140e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 334874730 1250 334873480 334873489
    0x60c0c051f021c020703020706030506310203010617150f060706140a060806090c0a050d0501020c030f091c08250c030803070206090105010312120f06081b04060b09 72
    0x4811003884a4080c80940c02e1142e56021003030388101e03d0400169542c54610380a070034480141d002c007052510380b804102090b01c440c22a103410030002e004240c2e410050590310140030b00700030b55280803a44044008114030744c0003010944002c00300e19004540d030782d0780000030001c2c11f007004699410110000404909042600c00340c0300007403044201107003210071440c03401115a82100c20b8402e50761103402c20480396800744503560704524040041c1402d09074400114440b88518810140181d54110705c0381c041c0402941038440494814080e00e948585244044095400401c196031040003480c0d8604145200340c040003041981c428101d604108085a41c194482660704010101c5c0c42c0d107034903800c0042e40c03000000b03010750f104500780c50312420f200000a00d0303c00010000c0d4042e078580300041c0046610032840d034000134281e142081e000a1032040300405407000039131b40030f900b6082000c040b500c3c3c1000b05c0d11141e51850b64241d45100e401e41c104101c1a66203a00c2038540c8001c040101e907490b41003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 334875980 1250 334874730 334874773
    0x70b120a02070204090b150d0b041e08030f180319200709020d050c1c0b01031d0c09330f03030a09030b0115020d03201204060c0c05 58
    0x204aa001418492141c000c54290760b120b13501226038444603010020010b001d00320801b400c00d015507231801748502036a00c402e00040081e0018006442006543d1054030884043d5403d030f0368001c01054aa08008003000c040341c2c0240c0700e20040032041d04500182280000546115080e0281c5c4180c58411000059520702d08080417040d0440c2c1214003004c5c0c2c000c0c100b100900900728194016580c054400008040711070103001c0c2c40002904000c4c1c110320014054000d2914084014005001034054005a0050098030600456200c0602e004103040501003400d003580c05083d00c0c400c40550301c0200642080d01e010301c01c0d91007042825001941005807040d502c1380c10401070b114000401082d030010740346402120314180024410380d814000c0040c00b50003540141141c0c08106904560120003a40341e5180c00307075000815030307070b4001c0351240c034030102e11440344010390105031383d0754a00e28414480c2c1c410100d40c1a140213040005000e002441445042c00194008003c0d1120b814850704e42c43d541072 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 334877230 1250 334875980 334875991
    0x108061804140709020a020c04050705040f0306051017010902030f010b0102070b0d060e09030d060e0103110108060a2607080601141338100e040b06040e100611070b12 73
    0x1040680100300c1904d14401072031411071507002030980c41800400c000654600400000403c8020702c01040750501c00c8001c0300560368000c6022076075030381e1442214a82c5005070f0042da66014000e210391110b0740306522001c40d0500950070b031001145040030325400e0700d9a030220140181d11056040184170703907890103451a01c40801c00850240d5031410555800075003030b20303410710340d400c001400b5008261500c29000113020118042d5059803654a07074803d0b0804945000e41480510720010300c5c6540c070580003030081e000003410280c802110b00300c0d00c05002621101c0c9515845202c8000c40d0101000134000d0407608059400342900c4540340c01c2c01011035000e48107214442c0c66513072142c40e0300700c0c4038070426181e82c409102140c8540c810100100e00c100f00344d62540030700061102d03044880d50000406420001c15180452117024140101c3d407184199448041030507010410303c1204a00451007100b12419507580762600c54184400c162030f0010b40c80742148090342040b80c0c4015001d04041c80b503215 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 334878480 1250 334877230 334877233
    0x70203010e0601030b090706020609070b03040237050d0f1415090c09010e07200a02030604150e1b0d11030d0c0303050924060f12060105010806180414 66
    0x90107040c0256191450a81040300c069003040104807418000300b104000800d064070090240e400c08620041d2525a14080d98200311800000281951580c3c00355450f14035041c41d075000c0b0b000c0c0d1805428100118540b03980481c1c42c0a14000400385814003070801c0307032900701e521024285504d039501c0070f40765215a8410340a0140c4061429a0303036807890418400d100d468043c0250b082940100328040905822091080003200e043c40282c90340040007501d8050110040480c0581c20301c0f549151820484c4003d5151181400700400c1154481c5102c01904115109106200c040401c00340ca507200c0c44026080c200840e1082c0b4031510301180080e146500a860080c00103d882c00801d08045131410450049640c0d120000c08056241c8038070b5034401402006031800c01e820001c140e0078191b080800c0e0200d113480b0343c00b04500d50b0342e540d000e9282c50001001503003c054030084517a00d0300400d110f4140071640e20000110b25050031020304400b58088018441b1540d61540c40398131402444040c400c4a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 334879730 1250 334878480 334878491
    0x80604020a0912030509011403091c05040b0f0403020a0503010501080a030507060b0423090c1c060e0f0a05010c0314040f03030b0415051e1807050c0a08070515010506030c07020301 79
    0x1d41c11981c030f46524007400b03555000c0ea14012003001504c424015407103c055a81d00f0001c01c00c603218045144000000c00040380032501c1ca008030300722224052500840c100100003c0e17645000d40c82040240202c0c1e100360b801510743c503078820805088450074480c4c00803d4101c80620030000380f10720010036405214403000107601c0e01c1400072904588085180c1000003550850070086100c08514450b032003c8408014000a180d1201284040400001c0b0400315190b14820404101c0580c0029407807504400c122201c062688400d103540c0c00d642a0191840d5207801880d0041911034061804504c0202c0203200303940d21350750745501c2810044d9009400f003542d644e0907992190b6480c01340d0200c200c00d00100d0550f890604c820009110110004811015460301000c0282c1d101c691101e01504125118403850b0b0740c410b14151058441c13690f503030085014000000d0204101003020f40201805442100c05030800070311912076001c0b080c090241d102c0024400a011036100c00010944144050b001045 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 334880980 1250 334879730 334879739
    0x90c1504030506040c0542070b04080307091e03080a05070b0403030e070608010510030c0915021501050409030e040f1d06180d1d0f18060102011b080604020a09 70
    0x1041c0d0280c400f2074002d005e4040420040c41e03c0c2010020404070030340c5908031280f070044064019400d000d412100c8064101e41c0301d4940440500ba5110103400c449103581320f02d814904080158011100f41d07001c03410b840004140000780342e00c00c01c81c2d8164414182016821900c900e81c09802c5110b2440422004200c07460002e1664140f240c000c0c1d02c69100030650b805880f9240b414044250040d00c00c02c85800010045541d0f501505c8400907128100040c103000c00b03440c100c90009443c4c11420000d0012240484201e50020f0140b0b0140540c1140042d1a600c980400003542c401920141c0054034a5a9407440c0b440c25501003440c03040740013070000b5140f00d40e10303540e444585086003d400680060342009100300c400401e1005062140c80582002998008040d004620020f50382d0314805540d481d05580d902d034007224100c090001807990b50407925540f02c810100b00e0843e0614010350030104150b0030090000e15903181c03005162600f170a80e07580c03001888000c1d0401c840000810090440014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 334882230 1250 334880980 334880983
    0x80406020d0c03090201020d0e01020a0605090c100c0b0601110309120102041208070b01091509020904060512030307030b120d03051f031a0129090d0503161a090c15040305 75
    0x4444a034644002c202c4135424000a0700380f01140c01041e052100c00f0035007038020b03a40418221550740c0c0c010000207058031424103a5103003644080116801c00d40342c0c250b0800c40f0760842c41150034203220718825000d5580d010011611a52850600f00c42680240a00f024901d0202005a00c106125000504059039084540c1320300110309004e650302c000009425003070007020301159016207103041c001d2041d88a1144041c2a000c86440384024803540032582d00c40c242e40c1e0f5000000241401800801d00210440641751242c0c01a918070020a1406c40300031400c0c10000d102c00030740d841c5a40540000d00b00c0210035400b51100070b002640b5080000c00072840421900b40c03200141d400b41d001195641500c00307000f502c3c0c0d00180c02207080d40f203001c06100c20820081045404000010726807545070700c0c0305808100000d07011400140203000100310380034270841d01c0c0c1070380c1c010341d024540382c6540c0c20000150101c18501900c0700d50b86504003421425150800c251781d89018110b0000480c0340940d40c2d203905 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 334883480 1250 334882230 334882241
    0x7050a060507050c06010b0c120f0f030103030302041d0c0307050a0e0d03020a0c0f080c060901020a1502130b07231c03020a080604150504110c0118030810080601030201080406020d 79
    0x1000714201050185100341c042051502402c007d8600a290107010351449688128856001060301400100d40c00c994074030805640d5824038031a80349449507100e10780540650003600507000c00e00034a920401140fa600340d51580034a00c25484107143da150481c3c121991380c095050750301442074003100925161600c0c3d5440a0703082c065409001d44520528141020b1002030340007400a45804030b040c8030417480401c92045540c021101d9035070b48e801400040c6e00340503031010080e25480d00c40080c10804c600c0c40d002002c0416601509800c02d6880351900c54180c010340341d0290110b80000945503a1b01c0132100d4204c00b585d500c000715194100141c0000100c0042000600000381d00451480b0646070130450030381c1c000508440170f001d03c14449440760605204c911446100f240c0340c041e1100492040b10440d81c00d51040002485040481c10300241070b54a098400c0b400502060006421201005040d5007915403150142240342d02c1c68004540090b005401503903565405c2013517480148a91048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 334884730 1250 334883480 334883491
    0x1021602041d1e0f1209010507031b120e030321041110020a0605130b1512013206030a0605040501020d0c02061006030c1b060608150a060b070b070507050a0605 70
    0xb039510410b4441c0d0800d04040002150000d40d1740309002514200340782e00c0586140400a00c0d000f0344804182c00c0444040e03131012034040c4510640c01d648001d001948041c084550042d07120315080d4000c180c24150799105d51002108044a42c2d11800140503d00d8a51303a00203006031201c00d0300302d00c80f4000071401103810140c1cac070250748610a184c0c00c0142600031039500c00380c10034016110707581c1da86070300c0030804000f8106040e80d62003880c0c8a210350784000281d58450310f039800800c0440015038449516042000410381d01d41040f900010a40070304c078400e01d20400c40074018002d1800c2d25a41d0030060314000c3c1086845540912500a80d15030034440c4003441c030380c594000c001c1420042d100d40040e8690740c22141c1014200070035040141d811886c40740d59020203034040401c4001c03a04005009105039000300c0d00a0003141900c0c08a044045400350007600300388010003001d42e85014541d000d1042c10002841a0701d41d00005580078001d001601c1102d000f8019a491f01400d40c0c0c0e0f503000c03210100c65 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 334885980 1250 334884730 334884763
    0x51e28060201050c0306040c021c030618060503192405010e090a0b060d03020c10030b0109060927020c1002190203071a06120f010f0e01021602041d 65
    0x424410625014000001402980000c008a09190240a01911004005c42c1c021a02c0784400210300307200b00800183c1e582c1e400952104c082080d200200944428803510002c42d0b401c910083d0f090300c852180c0411104020014001089400414aa9107114182c2503c1c40c2e00e426000c0a503420610181210100c19254005150f6043c5201d804411030042c20f0000d9582c0708540140c0052039100c01c054229404513005188080f01d468103e00d0010901c90141e000414100000c60300ca425410a507881503091700c582030010307164101200c0d415894804c42e098428903603032010b54880d4070f11032050f020704240c1c00580381139540d44107585400309408020a6180d800039200482125003500c1d84207211032071014510740310454075840c001014404003603d0407083c0c0004200382da070f26408a104500441d000342c0e0301111120740c19030700070b144010211103240e0a082134440c1d4100103208403007035008407151247d82018550203010042200d007291000c003846500111201030310130411511602803020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 334887230 1250 334885980 334886029
    0x3080901080903030601170615122d0c0306010c020301020c0604050c04090b06040e0c0901032604032402090604030f0c0e0c030103150204050a081c0206060109051e 72
    0x40010700d05038000b8a00400703900280180f21340c680e806407125000d08032005006056460f01000100d0581500490f503000013000101080107000d01c4e000240301303110083c440d44000182e00520b28111118442c402d0b040b60300300700086c4014100e0800786420040626001040781130aa001c02d007240d000d01882c044542c0003004100c1088010000328044620a82d000c1c00703801c01c030303a442689500025100911558540d0510506c1000070440c8403184e100003000328695507902d041418000e42d0050b070b803040f406a421107240d1a203a108003102d048a62180c02c41d0000c00c0072000c4103503404120301000442503020002c2e403d20b80d03200d6019201035801091031041282031441d001c50a00b800783c1c00300802c1047d403810030181c04919415a81141d4200d001c207810380d02d131002820000c1c480c0c2d03001190710424556010407410000100f6400136200e84400541c00c00e5021802e9954070343c2202c42e24001484014244040d08103c40d85a81c0c2c80142e1005800261006000a411074107504d8088074014101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 334888480 1250 334887230 334887247
    0xe0918011509051821072604030b060103020a0903060e1e030a02010b03160e0c04050607030f08100302031f021e030712140c030402030f0106140a050f1c05030f040308 73
    0x10381e904d500651420000340254032043c0c04280840b409402d071100c0741d49002c103142092220349800002c807241c440f81c0002000324945a80e05054100e401f066929142c4034001842d50b501920844800c03540c1030b1030b040180351459503040064040c001003a071003401041c10700c03c0360b40c400070303101200800c456006e144c48865101d0003e086500c0e00c03808610a5010507202e003a0003d01042c4030059828000d02544165946110710800f481907600c410b0f0004000202c990916901140d00844049540c3e40c00c0120f440345030013149507130054007019525411071188102c001300001406403100e40c0440c2d002d8113180300e80001c1d4148110140c00c017030704c03040c0000030054582d520018960402081e001d0400c14003558071015600c051004224280f012400000b080a668042080340882644607000703201040e03c2d025039540a6600041090103401010008119458440a010310409000d0102c1071034035000e1540404040c6654002d4425000400080e03098240c0c050052020b140100c000945c1c5142071b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 334889730 1250 334888480 334888501
    0x7140f010c0903020907081b0a050403020f091510020109020409140d0203031b0f0f160209010503030901050f09010513060e030622020118051c0b070e091801150905 72
    0x1000704500801c00c1403141400180d442c004210741020007450300f1a566a180000b041a004072039588010915001c10a000d0113680000100b080c0c0c0d2003aa10802101d00e4641440000c0200343d800b5091141001d100d20b0301418000490400c100c0c5501c00410248440d401240c115108894140c2d11000c1241c5486000b0a08022820950036188015851032600ca8520203036075242c000c0c003440c00c00c6d00040481034202c25600ba1142010038030400750380c40b08000c22541c220b40b5054022402000c0c404000542c81c50044140c501003601a100d11745000c900c0710b984090703684200d0701a4103001c000e001e81a00f02c0b950a0903000038104036140c220002e0b110307004151034280003c20200f204001241440308200c8031a2000112980c2801c001020728a5071029100244c0182c020541100b02c05085141d912010303140394800a000399001080c071303100ea4004a0f0002c20103140e0729008203d6a0104002102040021800b108030f28000542c407428150403000e5100107510003102540c0319003d12000e11754 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 334890980 1250 334889730 334889741
    0x1716051509190f09060f170d080c0913020a08071404060507020a0312050307030509071a03060a170c1305100e0903040e01061707020c010e1509042d0507050d090807140f01 75
    0x106511903844202d1f0041d03082d0355172100c00105000b000080004101c0f03201240d82038441c8800c00811041d51601c1241c03514000750003500d0500c00081286005c02c1050b030003014200001050341075460310702420401c041c0c0b100e030303c00302080341c100c0780000f00080030540e10584540b0701ca000d940c42c40d58a040404008090b180058030251041e00b01070020404000c0031104400345910841c1515200d50341d6a0000d586080340c1c3c2d002c2002519401200c0c50428008141c2c0f031529481101c20344043d4083ca02404202c3e44111481c040520042c802440380011a2000680c041c1c0001c4c1202d14181d150100e0040e806020ba01180c00b00c1c072104c00103e100786034024020790180041c402040c0746802080020b1801c81701000442c054200e000044004603a0f40d421600240c00107801405200c4406440d04441003502c1840360346002d2094010b9102101401014025085540c0741401c00801c4108070f00107246803641118000e100f0000700c00000c0d4100d1585030100e10074400341c0400d660040300d66003503a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 334892086 1106 334890980 334890989
    0x60b0d050a121101020403080d02070507080102040f0f0e04030e040e031608090301050c0c0a1b120b060405010f030506041203061716051509190f09060f 67
    0xb100390a1204040c0c150b0f0703914901d40c0921070b00e40b4200c3c095400003c1400c1020401c580001d50150050140107001c0c00036104081e540b0051a800c99000d640400c403480403a800030031800c0700000208005109002d800c054500e81a80c0c001d12100c0340f81c04040c4210b0b500d410540781008200300380c80042c00700d180440e12003503e07410042c20070340026450030302c1307503007044001070300f03004800140c83d1031489040051008a40ca5603075203002d4100740c85240c096008a80c400904094222400c010b014083c449144841c20060280310a941050f04171000b00c4e00016402c000042e00050354a42c866000314602d550310340c05d03c03000c03409071650f13900200e05101000042500c000c008103000c010403005010b4401016910028007004612150404181d0b0905104003035060400320001c15800003240c400c26090707900d03100c01e5060840d01c0d80007101c1e1140d449409000882c0c5c0c4401000280 = true := by decide +kernel

theorem cover : BRFrame.Cov 334712230 334892086 := by
  have h0 := BRFrame.cov_init 334712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 334712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 334712230 ≤ n) (h2 : n < 334892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
