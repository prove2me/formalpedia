-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0381
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:31:07.223494+00:00
-- url     : https://prove2.me/submissions/d1ca832e-ef2c-414d-ae08-6028f6d05c64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 68345326 ≤ n < 68525182 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 68346576 1250 68345326 68345357
    0x30a031503020108011203020f060a020406110604020121020706150504051e070f03150605040501080109140703020a020c0306101418060118030605010b090925180f03080703 76
    0x58030944406070028070840d004204110300c1c2103030009414080d10583c0e40c0d04098590791441d10100740c030200c415a40c000790400c1013941c00000080f018040302d01810075410f080e0002404265956401c01106404840840d02c0200039411107280c2540f0010511511f4a208003000b82210b01e80301e800d008a040a00088010400080c20110307000c2c0501884030a0b12034030f400323780c40242100c0100615039580b40c01c0003554828501e120003003c0300da070b07065072b55410800014241d0700706a00039000c850034080203020315507801800545c4941d5501d00141c03100e000c50012482c00c081011150341601944d014003824840426901c010b651030000351007140780319501800500c05400c00c00038146048007000c521558401e0084e02114060194050b000507100e480c6c01044032820ba006a10f850750018000b445402e1007a282a8848040c0c501c04824901c81c8112070a51100035031400104004c4610003491000414103030000380030002c05803042380e17171246810910b6900001d415004100c07011181c0400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 68347826 1250 68346576 68346611
    0x90803061e090a270c0305120c1207240e060108030a0207031b050603070305090d03020901020c040902060408010606050702040f0522030903140c01030c02010b0627030f030a03 77
    0x200c50000e44880b810741d8492105034024201c3c0c041a101c01a00f0f2800d9420440c5103c0c00c21802500941a01401500c0c1d440c2041c94640082038026801c0c00510540260500100c2c016900303c400d121020303510842403a2400b10100c901c00e400411004521321070449500b103900c02409010300760111146070340c0b15045155640602c0703e8107001a4404a03082c400a0507001070046000e11001d0310b00001034444000429941080b540d500000c2d50381c070200501400c04104c50302c40c2c00001e040440c500200400000d450300c54554038103008989908003a41191a02e60480300102010390080014a03122840102a40c0c40b007070040c3d110340c2c1030151100c0c216480784200750040d511540d61405200c2400e81c0d0f6880c00861003000d805100c05a075001000c2101542a54800320081014000c1004000c2c0054100c4103d14a4142103a141c000d09601603124142244e50b1640480300002c9040c4000441c9203200c16550701043c0c050186406100c10b1007400006891132480d180c400784280d00c0d004003070742d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 68349076 1250 68347826 68347879
    0x60601021906020d060b0a1d01080402010f0e130204080d0206061f0804050a060204150f0305090309120c18040b0a0b0f090a090605070806040c03060b0711010504080109080306 77
    0x441c8040741e0340301400520158010300305401c6074140031603410750702c06104440d0340200b08850007007080c2c3c0000410311a1842400000d1500900742003219007010b4000a000044002440d0700340030207800000520b80c0c44c806204080550f0000c00d540d1350fa181d0190350b41b2415515000405403054002251061038044c00760700d008164405e411900e8880000e00311640c4c1005441919540201c118000100318640014800307000301c00b07940e42d070030200d03004014681510881d540741058505403c2c840c08620100891780910000c880301c004800510019a0500c600e200c0b4090f8440f603081081003108202c0c1c0ba805220318059407082035203649540381e10b41550440b0420325884101c0c030f840c1c00c1b228500030306140d0f040f03080b00c3c000040c3e034440d640d100b0040307034800d81d58100400c07200c408000c03091510f070060002804003840d003400b056180085064a5000710700f40100102c1e08640300d040283d00c91401c3e9001000340c14001d100300d071031034140071045510a540450142c51350800018030180791111150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 68350326 1250 68349076 68349103
    0x80f030c0307030c02130204030807020909011503031409040f0c0801050a0f030605071403040606180605090610111603030e04050108030a0c230f06180703031101060b0a03020c06060102 81
    0x51900140360b0301141d00203041031080342e201b081100190b803021550320180c00a54070440045940707410a004011407100d001b8804401c42c0c0c1000b03600031403031801c8441d4a080382c1e49418090b415184502490649001d00501d040c0c019140060b0b130b49905000b50060500d07943c041e1584a46039899030140075102585029030200300b49810410000240c0940c0416030110007460000300038401a22301031070541c4250350641d001915001c0038030001035000d298154200e0300c01c2c8208841e61a00000c00c2c0750fa00010035941c0300d00c021101c0e41c200c85005540c1c0b0b00942d40302c042902c646140c0084001441507060000741c002550800c003900503402c09100d00b50580e58000f008500300501088111160b58015004441150b8010014040d154442034504518a00d06000d081080e060030300052500304010401d90301c100c0a04081566072001003000c0080e2034051521441d04994040500e000d44860361150b003141d00001140d006803541540904441505a81501c640d40c890100480e42d5080300101311 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 68351576 1250 68350326 68350333
    0xf0b07020f03030c1312050a020a091505011d090708040c09020304030905060901030e0303090309090a02030721060e01120204150e150a08010f1b03060b0a08090c030d09080f030c 78
    0x283d13032040c40c0c1000d05020740300300c201a42c1598a54500c020911000402120241d006ca08140114545400e52101500d1102c40070460f29004403400070f40038405204160500c0480700078480c1c3c1d082d2050025880c0a006040b99546081030440209040400c503001d0750076041d0410301051080b8107008480c002c2da09540d60558041c280741c200200c03030b03000c004001d05142d59020b0002c80d406090018500c1b420030100034646a001020030301c48c113070314024252100136104004010840741c018002c01c03201c80c2042c03040020b024640000c0e00040c02c15030444900c100b1610000102c00ea60291210443c610a44081c009950b9054009900c940b06014244000540000103640c050346007805a440c00380c000e14011541d5600c0c503025085403001c3c0150b0003410b48640d407003111840079148000d0705200c03528013000207529003084882d030340c02551340380000c00c40040041030140c08204000d0290301d42c000c094601c00040c090000d801c0100c913125100e058010301200c0304e481b44010064840704030070007018 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 68352826 1250 68351576 68351581
    0xd110303060303040608150904060e070501021f0b0109080601030804061e082206020c0304060315030b0402060714010c0806040b0a03050309100513080d18050d0b0a180f0b07020f0303 80
    0x5591b031100041c400720285003c01a0845265a02900e06000d0380c0980d41c001070340300000602e00c1c280001c90700454150b41c8003c90102e0911961072070100141502040040d520751203600403168907801e03500180d0103116140000c8107200c2520020411140303242c0750500c0d03988142c13810500098003102c41c0400704241e00000b030040c200c04402c0030340c2e01d420540c00201340c8901e44e803010200d8201c16800c6105600205051100300c2e0144030f004001030a00f204248650314650315101014002407000707009034000f11340c0c1810400c940d4180208100104020b101e6800350b904001e0018004603500c1d84502c0c1003180020750313802c2900d5001c0550350031a019501d00300c100018040c2021088004104016040262103c01c146419291016041d1a80a410001c0c40c0e1240104000c8002c1030b10410092406800c0106640d01c0c0d03800a142e40d48022002440c3d503070600c07500000c1c21201080c40d004051306103a482007110703041004004030b10415041c0c0c3e0702c0c2c07600e90b4226500c4440c14501e03110b940c000c002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 68354076 1250 68352826 68352839
    0x504062105010b04180209010603021207050c07030c180609020301050a030807020d0506010605130f06081303030605040203130213061d04110607080d0b10050a030b0102070b0301080d11030306030304 87
    0x698081503070060700085026042c110201e0211051200b0b07514902a04142607400c500c1c10000403030040207549010b50034080041440c40090101030700343e40511000007400c02c6020000c2c052030380215003004e0b070507003020740c0e079140b51320141c141001d041003191400d01c010400e580c4500c20759041e00d60280101140a08554032a022a0f01030792045e42d00c251407041d240000740080000501070f05140c1d80e005d48811481c40040803031152038001000b40c1001d100f040c0695a400381086a00880d403884019100c482c50401b41c0003800d09800c56a00180000f08100317904460342c0710803080071b00c2500c41002ca01d2842240700c0458801b406040c07480348401d5980852150020711582e0050301552003804180c034000009111540810002c8402c0300005c00c42c010040355500c20340c8001d01c41070341c07802340311400d40718006e01c07900c030b88aa1101410707521242a00c4c0e42e482042020054258441110b80d00d513150254240e68404030604100050100182c10302d404001000766070280c8000380080d81041d05128 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 68355326 1250 68354076 68354129
    0x4050615030718090207080a1407050c0f041b020106051216030b09070b16060c1716030612050c1c0825050d0f0206130f061d1c020106050406 62
    0x21049000000fa400700d152260b500c000c10a59202d200803030740c0c480980c0006001d2440d40b030010341e030411080c4101401305201044141c210b000854030b40c152034489000203402440c2d00841454500041101e00d0201501580240c2c19500115010340c01c00d600c400c13003d645d521000c500a99481e00240301040080e0502a95640060440701507039112a29010702c418160840780f980300000c103000c00c004091011620072000401d80a1400c030840c5619200e801d00104409045000400300000c000c03025240300758440c070098100350310342100700040d07800c1c1565038074414541a0f200d11f400411080310400b0503008044000d074403208050070105c41d101620b070201c9220724000682d8030110000000200700b40090080800f06440b200b840f07102c0740308001d2134808002c0c006107201c002c0300448404102d070203a0107003500d544180d0110b86940c0116503459406140c1c9240f41c11403180014440f41401141006200008540c1c000c00450307642c0c10400c015900c8038411450700390754040404c5c03140c0000c42c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 68356576 1250 68355326 68355347
    0x20703021504060903090e060d12090515040e0a02030702100905160e180304061b050109050a0c17030301062c130c08013f0501050103030e040506150307 67
    0x900660307200201c03158544400380d9007214112002655500c060703080540045041d00903001c07010141040e45030210106142101d004c00191652400d84409107880748180e00e084050305001d018108a00f843d00490a07039900680540c0c581d14140800040c0050858400e99205a02550003030038000030110340361004003e001026140c40c010310807200d40040003595500014000c4055503192443c1c0244c0300090700200846408241e0410881046100d5004000500e03401aa4580001e4070a84c0e00c0e01c07a0040020f894010501d0083c19540010b02c02c0c100020401c481602d8260790600000841c1940c0301d106c00d000b0900440c0d00c907414400c40c405444580c0015a140e00d1792483c15082210015440c10016240d2050385074581c40010021548045d5450040911603841098600e440da20010040d07005102f00c1c0646044281580b0402c050710b034001046500080200702b0f5503103c3c1401495000d01d401c080b0302403424000481c2c0c00d81010300704480c3d901105800182035417a0702d44106c400400c3c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 68357826 1250 68356576 68356583
    0x409020a1a040b0307080402010e010e060f0f13060c0203060109090201050703030509150406021801020313050d030903060f02030a050708060a0306050702011e0501032d060203040816030c0b090d120207 88
    0x41c080030440404000046000c1c008031b0f00c41005900d40362000601c0600d4000303505041010000310302c0c0e07086d202c0000703940f035400f0400401925402460060080c50089000c8a280b0012a500024605401c06980705c4034500907025a00141e0322001003000390f5908240090000e0401c00145020070300c26880076400c03079040000d41d03111480c0360036804d42c5000199001c1d1070441d40002c07104480b58a031032410982103400c3c0040c60812240103407840a0000d9489214060b032112100c0c001003601c00d501d05001b8551101080004155040b4090000e4108403000b440d440d00d0a800300c0c4450340148d1445115200090003101100e0640d03a80402502c4060582800c1d036403565030080b161061344a0182c4800c4c4a400002070646c51030030201c0100d02d561003071109408010100448000c2c0341f4081104164000304090796a48461401800e60700c2900c0f643c14400150104020800da480b003803402d100fa00501c076003801512160f81d4075803115003000106e0041014440c12042c58000c507009001078a00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 68359076 1250 68357826 68357879
    0x30d0801030201180509040b0f0a06181a0d0c050301051003021f021903080906151507030909050103080c0705120a0f020d06020f04150e0d0201200d021005060409020a 73
    0x1030703640114510000a840448d04031078020104165850031038420b5a1040a49c170b01803101a141c0781041c442c12070079801d00324209445d05401001b0070804034114911502c050144001c030101d41c10000001c84a60044911075401c0402043d4921500340000003035903001841e2080000342c0882d0030056240308000e41c000d6000e02000314200094050401000714000e40302c3c4d20b62803070003c00c81814090700a101d4450b02240341c41300421501e4006100c10b40c00414090540d503a5420b060665001c0c1460740f02d200c20300e007003030004410440100e01400000054008460046881d80200609161403000c00d0010740d001c0402c1c9400b0803001c1228150403400030f4408126284642c031800240e030700c05202c0e40210035001604102103400e100100c1d170340410300c0c03400c46030140100001581c40003000380c028cc100800745e009012070351012000d4020025140044955480074801c000e920f490072803540180d054070302030018000e41003038003454403125401003202c50043d0800210685100402140c90050003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 68360326 1250 68359076 68359079
    0x140105040509010902030303090f07150503011e15090302040b0d080906070c03081902070b070201090b0d0e070e01050312160b0712050106030515040c0e060c0f011a0906030d080103020118 82
    0x89090004501505027080a031039842000c405152030409180e00c030b4141d0f00040e0300c40902c003e034010700f0350781500d0811000c0c41c880c0d4214003285155602e682c0004044104681c03012418582140160084a201303403001e21100080204020f44402c41640c0074140e05010400040189415070081c101c0d244100d4400514907240e882c0e480c043e4000e0078103a840c8010161004070380640402401005044078803444d45803d2250b030008040d00024450410446070205d0b200c000140c3d00c3c0c004d82107160400040700c10041d900c0e100c4820009080c403605029000740341d1100c103c191103104840c800402c01000c40021200780d0707580300380242c0043c00e24003009007580c101c2d0800e012a0050318020205540d020a4070304047c460030b1000900303101c000c1d00c56494104c050f0903054001008952107038040741c5591302c62000304020b505100c0340f44007070090355107424490314004151802250101c0021b44080c40d40e80d880c401416030b00c2d4000140794003c20075100040005610071440c003032005a118020070318a5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 68361576 1250 68360326 68360329
    0xf04060306021c0605121009030306052d0a0305120309010212090304030203010b060306010c02101107030b150303090d20060301080307050d091d04140d0f020c04140105040509010902 80
    0x280c00c8594034910451070140e8000d80c500450007100094502141d601900c00b1b1450302d03503552443c80d03000560702030340c5820034041818080c0d4010001004040d0443c201c108418042142c810103482520340b0300a513031101075156040482c6404150b07988000240303204000001e035400582c0000f442d0850542d000c20242e4025100030541e035025000743c000941c0c0362800c52042500303440c0c100c0102d9014040c24010001641c1e0b021180c202c40750f4040c2e40001c2c43c00b8071810b085030320300b5014800c000988120740c800010400c90b4199240305000c00c050200104074004100740d160711440c500b050344611640d4203640800c15035162490241c00e40c40d2185400c0c004000801c110350000d80c4003505a03000400c065051042c00e100c3c0d03510041040c50207080080c180702c40e101c1298545444004108603882c0020704004514011840b45445c4034202d0740640307581e4500070720b40141084034600601410140324181d0420f4042c00d9100c0d103514414074000d81c02c10003403000078400100380141940d03d4440c540050b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 68362826 1250 68361576 68361581
    0xf0d090b130f0305070314010c0806041509110a110303060a032d061a0a030b01060e041409070302010f1106071b0c09150e010b0403020603090a170306010809030c0c0f04060306 77
    0x55100388084c18443d0314504281d0603105001407900810b2341410550081035072b000f4001c0d503000d20100c0c0c001844040c104030b03484846030031390080d1515518050110446000d09405410385082582d0703100581d11030460425100e010035600766802c84030b04001840058600114016402a4044c2201c2e513902c4050f600707562035404403401e842590303484442d1810b2942e003986118902c0400e43e003024059103161303181c01c00854144601010849140c84603a10755580350050b903d0b07112640035150681c149070714650389424040c80120b000c40d5000d442540500d0203199036084000081000e410565a0401d040d210582211904003241c0640d502c03c00c00a0f04c00070034900a000d07031020028010701d81c5040b68000381400d401c00302840130040e004001050041c4100d8003500d030305454054480c5c03901e8240e14906841a40c0090201041e81c540311a07049101024500c68042603a801c00e080d01c54510b100d0300c078899120241000e03040755020305180e0034000d031514684c40025200003015a501c0d00c1d00002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 68364076 1250 68362826 68362829
    0x20315070801090b011803080f0f0403060209030606010f1209030e09150907032f0408070303050a0e040207030e010e0112020d0203010302040c021609050604140901020901020f0d090b130f 82
    0x310314207900601c060689846600011002800c1480b0541e4441000440d101151f100040c84190000740020b5403030021402e844e0000c10b2111029241c0741c4901e0040c0107034011141142c000c2c4501000100f042d03108071054004081d0310307152100114900003c803409000d003480c013a814400d48040030951600c0d2041610b1003030590064500c03150003800f082040760f04014000c0c1082501b820034915604840030160f544942d2505041d502103070083c0c61818240c0610b503c1a116802075000020a040c0c100e0020b102c201ca0607030341d02d072100000c00300b048200d000c0e040e170243c002820390000700969401a2030400d82030701c3c14100303440d005080d000b014050768090b030031002c00d82c0d4000c0010421030806014184c1d032282240050160a0821222000c000915100c0c1c40e10064640c030114000f6219903200c0d0460002c0360300145614540302240d207011713520050101d401841021042d101c0c1e0000460720300e4800e20180c0c0d4884269140c0711200c0103d401200e20f024180c1403c000c00100058031059990 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 68365326 1250 68364076 68364091
    0x70213050a060602120a12061d0a0b0103050c04090b0f30030705190804080d0c1406070f0f0215040c0f060f0903030c060f0c120f0b0f010309020315 65
    0xc0ca80c500303041d0300d0040e6000d6600943c02d550200c245090002c603401c064031401e01a52030001881000303e0a441c02034a00ca80c000c1d0107047c4d44c070001124095a0507522442020020401d00c81d0b4013415004608541040b180d840103244184001c0c40904115003042e9100a00105134a0240405c00001060750184054480f030714500d120065442c42c207104882e81d1b8046541000d50b08041440d200c03580c0b1030594006015400e05403141e070104003c01d0000b920054a01901222510f1400d5a4080d14645e0346050551790001da42c18104401c5800141891090704543e9071022400010f9030240c403605042800d03101580546101c42d107101d0311841226211303a00941e282000d0a01c1c0100c50f18648600b500728604212401c00790f0200940c000c2c00300c0c07040725414039080000f60301a041c2040100703945c5000300340b2141821903401100750b012145014131a02d400c0b08002c1040c80b80c465204640c1103280017900660b20b40341c00d40c0958040e80c41413204034009003d842c00c0d00c0d002100c0414040b41242d03280c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 68366576 1250 68365326 68365331
    0x40e010507030e0316020d050304080f06060a0803160303020f0403050109061a06040e010e130b0a0f1d070915030b09030c07140d020d030509130209040b010305010302010c0602030c070213 82
    0x200d41c0d81c507000b80801ca42402c0e024502e41034111080c90242011040c02900426410380d02c1d10401000300100e4000f04101002d40780c2c9040d202014680320340e4140c40c60392041c0d803559800300751100e011003258401130720701504080e11912a64103070041d401c0401c0180104209100000100308280107a901e918800c00300014007450310222180c02141400107035005001c240814811644a024001c0c1540c19a01403070302c01d0342e1000560700d0943e00c100c40040041c00d480b01484980e50305500b141c0703464860b050041c000f40d00150492680c0414618095032150f11911081114011580c04494001c4524444080b40d503101e1302c904034152810b0319240c03160ba1001400d2540a1818001708004d00002e19022004000141c0090284030b0349004c01b0344200c144403144010140684100c0c0c2d551280030300700403940a40002030000a402c00040c0902903420700c090b03008958840d105141c141ca5058442c6e4040041944892000f90001020345505000400407280941c3d10f0403e5503401c02850301c0013 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 68367826 1250 68366576 68366581
    0x304090e07090f0603021c063b060c040b090d06050c040603060b030112120e09071110050c2d04030f020319021005090f090f010807060e220b040e0105 66
    0xc4034203c0305000c003034000c3c5a190a2003800117960341952112214603a00c504a40820141000700c0188840021240c6040c1c000c1240300c0b1527014180401210303030411203055806590101400d0b00c0c0d0100300c840b410350f1401008140308510254025080c6c150f0041d1100c8130008550b40e07031404564068400c01c8200c0b2003c00d04004555141c042c1c0c40150403145030b030714119450100125485c240384400144508060840c4c801d02c00e110b010015400980103040420758201000c020f00f0008406609202d80c2c0510b03011442c0c92407190081c60b0048140000543c58000d5130215500598003450080b84049140c6e21070351034105440000e0809907015000c01e407464031540c4105031078628800c203c14248204a038030000982c2d2a00341c440c4c1c0b020140e04085580740d10710000a40f01c28480b5400640c09510070060040811040380140d0580b0201000c44d94100e0700e548040c2c0f040341d6005091b580c0001c1d5012450007100007940c401a207143c56060124600c2003d400240c1648d0440e4105800d81e99900304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 68369076 1250 68367826 68367839
    0x601030302010e06011202010c080901122a030603050a080901262d01140607020a0305010e01060501080c191119032303040206030c070512040e16120e0304090e07 71
    0x3c80d80144481b50019802d5510380e130010741110204070015207540e4010030f007003169900031070440a00195000c810800e0462209418980d00103c9140c2807185550310714101c05140248102c90035241c0140040200b21103030b54515039035074401ea1807141041021241082e80c4a4000d107072003c40c11404084050274600004001c045804174417030041d580d0646081d18030002103020005065425036800b100c10702c0c2c9101e01152181c85800c5009400c83d0412000000344070040d80b1500b840c8039a10000d200d1540d84000440d4134080c25501c040c80031600300020150f5202e140403849061031141081e01001da54000c01c1818151441a46540d0020030000c4034201940035103070711103450f10351550655403426910308070114000108000e02644000001ca4603210740ca0040e42c4c29a42c0c05021141e4011900404018a40107440780100b0503081d80d001c0f0b59042507044503005274400d41c3d40e5801d0303107161a10a00024040810401c01180000c00c0007203103240c618029040ce808400c8000c1081615044 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 68370326 1250 68369076 68369083
    0x5130611060705070308060108180a050109060b030610060f0c020d050a030306090203010b160804030b011211060906030a051308031807051005091003150923040c260601030302010e 79
    0x280b40c0350802c03400b00240c40c0000e8125100540196080c40c2003042d5680c2c15040480b04040340584035000d12448003040300708078054109000c81807180c00c05101c6078001d141410390f10032040e90722400c1c0c41d40c1d0307142c144101031058050041e03644891034002044d880d03a8001c551084000c560a5425401600852040c9a050b0142c58001c000503607085195614011144140303009200f050340109112090001c02d0003502c506490146030000c0f12050556524081c2842c25a41e0784022030b201900060441035500d081c0b01a100ca4002c0034041e40d1840da40c0300317045401408010402c1803500307079030103070a40465400000346206a14950409040c03e507000141494043c0070b500c01403003003220808000700703240d001c42139a00c20401500e502c0c071500d2003a1026009402840c601d10300d000c5420710001134074009034000a80030000c040c0403030314501c04404130550800c0d040314098900035908004200004420080c01d041d40f148556130344140c41682d00c0e071402c062013030b402034005030344402c4510000030060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 68371576 1250 68370326 68370331
    0xf040f2c040201090b07020109030606060906020709090804181803080601090509090304050904140f0c090c130e3301030507020a030f050a030f0f093f0513061106 71
    0xc15001400386031950008000b650580220b02c1480d070041000b40440e40500b1020029603403040c02440600d840e03450090044016210b0040148229140098801e0051045d0207075136800c045e2980c038060600703100d0310f8400b201d0b204e5a00c44075561000c141c0803032604051020228440c1d40d030fa40850410304001402c545064101c0340c8500010b409000441000004540c1111002d9910b23031040d90b034506100704100c4a1100000c000e00501c100c40c00c2c90303240801c0d0b801030880c3c1250900c050703889180e01d0b04a103010f000c90380e09070604a1281403240c1d40354001865480903800340d1071801e940c0022414100410b4074001400304580e00038040c126507801d03010701588105144024040595903882c0201a00b180c150b1010501000040c2c4c200a1172003900030003044203101d0004e00502d1004864035004090305581524011900c04250001800800540c440038090017504883e8001d1485820740301c00010021500b03005040199000c0c22191915440041081d51a020081d000c0001c0050610381c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 68372826 1250 68371576 68371649
    0xf06160c030b10080a0f050a0f0803010305060c030c0a031509020403030e120c03150405070302090c070302010f05130b1e0c1b011e0507020709060b0c160501080c0f040f 74
    0x2403071400c3c800040700181e1940210f400044081c800e54050414600300240700130054106400c501c0041c05000cac2c8003000f10304a91082e002c40d403040e515903132166224001038845121180c4108101103504d031294020452204002c14070110480e901d6113154200c0e801355208030003080819070080c0d410310b040c001400b0b5559042e405007a6816240e1300194841000000f03460200c911540401d05204040006070051a80500100003600300300c0c070040555000701604800541c00c00007103001c100d00e1405030500500d050480e07003800f084103661315080c48000034000c0099140305004030ba00e000c002c003d614090b0b4940c0a0b03440d95045117246013a0b00030642803115074680c2c100070b192090141031450704100740b400e0b0003000490351509a8128246200f0b83d002e100a103040520200c0c0c02484070005204504407041140d075075407111010901280410710501e0702060b100000100e01d8244e01d8000d040b60082c2d9090b0034034050700c82d21180c12840c3c0070b81142c20365407031000300d88003001040004007180d200e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 68374076 1250 68372826 68372851
    0x2280513020702010c030804140a1109060f03060112031707090503070f03150b03010209030f0304050f01020a080d0b0105070f030806011202030f0117011503050c0a0501050c03090f06160c030b 84
    0x2c454002070172072180c5c0c400007010000d410000409001c0d00300812140c4900e020181c801c071400a00b00705048015032407805125100301030118a5618000c01c49845004001c0c010b005140c1c607007100c0707030042e5040c080140d0912100b03c02c8604507051441c02144500455100d0301c01c05800d000a0500e04180d6400c24078030394410303140c1800802c0400a2480b141d40d40d8045c0403602040441c0421701901503103d141e60584264900c0c0801c0f400d000c00035100780c0300b007030740c48200844081004a80c2c8800251020f0401501041103449841641c0c00c54401140181000d07460b01c102940c580c001c901c1c90080a500046c2e0a005011345076900001042c2241c080c0300e425811810400c00c00103d40b841841000003032560007900320b0190b0829000009190b05040b0401c03d200c0da40e003807440c0c55103e4801403071312500010001050b07541c0584180c8000010f0b044c011401c01165a0a04c0300c040c0511800e41c1d40058140306810322150820b00040e0568403a50741c02c0e6019245180c00740980402a014109890 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 68375326 1250 68374076 68374087
    0xc1205040c081524010e0915040c020a0b1311100206010e01170d08060102100e0303010f0501020a1208100f030302101116031412091c05030601090509040228051302 72
    0x3c110740d45605401113030412200d089200c0001038508507002e036071032500031650404000e060704d00f40c03d900d00181c00a80d0305001041403050100d840c0c5141500c000c103880301202c0400c1ca1f60900a449002480c4602807003015101180001502120b00d1800c90006a006070014081c001c05140c8550041c00103e4602d00400d140d10711060b142d00701e012101003003207441c00c0083d00c140c0c42042108007210510f007003048010003048019403681d10034040d005000071014800034144d4400100c080c2d040360000c442000c0000c3c84102192100d80141907100007030110300000c568111540f50400081d407098000704825000c540c0c2141c156000c0b0601200b40f6030041c014090640580308010b030426505142401e05c074040c0d10f4401045000d40440900711070010410040d06100000e0243c02c05e0341c05071510802c2c0d0310944421034141c80115010380c002020050200b0550904285440e04207200415901c0d031942c3d14406a410311000c0001c051506580040420203420b088032910207000c9044010342c07a10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 68376576 1250 68375326 68375341
    0x5071d180a020901050910090c0c03020c09060f09100e07030614010908030d0b0607080c0706090f05030a0f03020c100305070e030102030103051b13060b03061c02130c1205040c0815 79
    0x144414415070340100d080c6c3e400581085000705020000d010350b40d40802124400380801003e5254100048025208900705400d2034501074205510607070300180b100c05152200002c1c401321110203026000e14000420010407030341510b4540601c04c1d9030643d40000c031103241100c7d01070709514402e1480e0501100c404c05100d03603480402140c84184d002e08011a1003011040410a5449800409000c076032021500241c0200085440c40807640c1aa803407882c0240c0358650088040c51900c601c1c1e074954003c0000800140901d081101114040c2c0159030900c4130980100f0500b09165140100081d40c0c1e0b000c00a110303800121020b8017050580085040d58159036480b50340d000d0902410540c607580311101d01503a6035602c1c50f00ba42c1d40c0813000c1400200d0b0f844450941540064541d548100514244011007e030609500700303c86400a18220b01500481907200090610748051030400034040800c6e001814140142405184190003a03800d132480d0400c140e041c2640850701b500000d40c143c040c00141c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 68377826 1250 68376576 68376589
    0xb0405060f0108130203060c0c0c03031810120f0501060207140904021203070807030305070e0d0803040b1008010c050309010f09051507120e1c14041205071d180a02 72
    0x41d00000e00f4000c109403582907601142e9039141c40300a505110315003c100218409802800b043d9103100111410351400b842055124007500d00c0d040384015803191100090b00e0282e01c0d4440d40d154030700380300c903401c3c601d0900c02e0b00380ca400d000540050303516400104a011750406c00400100500d185800d811040c01c0006942a00b01610191052103a2590350000110a0003210103144d0b2140401c1d50352640d5140140203440101c813a1800309040360710781081810241d500c0050070303600c000440e14540d00d42d5240e0102c002d0240c00400014842440880c07254003d10507000313175160546071103480c4c0c5403804405080d00c1842410340c10a50510020b8000205d0014261104e00395182c001a159955149c0449404140c0700056126505242052070b10480100d00d800c1d07446e03d0350300041c40420354403000b9074000c00c0e001c52039403846030b00700810031452561807803013003003107128100b0796500c41e85e9940c121850010204126011000708024407101a500b0417408007240e6200b13014040180d003d0b0001041e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 68379076 1250 68377826 68377849
    0xe0301111c020d020319050f01030f030f0201110c0703230304060516020324060a030309090b030109020d050105060a120b0105220903090611010605060d0e150703050a0b040506 77
    0x240c1c00d00750000031429003090b016500c51045440d0215200e14105491a4254007126400c142c1189040007044040e4405c801441c162030700301407a000c00c503820340d404070b40340460120303840115580d40465804680926009010740005800209596030070f60400088103a024080e80e2251144002c00341c01786180030040d141180d05a040c030740c0e1038410541c001c99803943c122174001d505004c0c0c8152030100d01700501440050516104990b403465030307024107000c40d604c682d020250120f60b0031442000042d01c107812001a074207014001141d0807080d5404107042040d5802d049502d03944850403c841d43c00c04a41d180010214a0780b43c50300c07206281ca035094001418051240100d0b00c0340841b250004a1010340030450900e40b070208032071900c50170700800310324503401007a00098070403100a182c0c1105009490940d00003c0c105440d2545c4010600c000b02000c1800080328000c0400c072600140408103076034070a0303000d03840c082402c1c980100c0348400c480203101c5041c81245040c00f4443c054842ca8040325 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 68380326 1250 68379076 68379097
    0xf03020f030a0b090a1106070c0509060d05011415030a03080c03060a031202010f051005150304051c0918020f0a0e1507060b030708010c051905040b0703020d0e030111 73
    0x19040d1219000c00c0c20445540c2025205505440602542c1800000e10404140c00b82d00140d1032440392504100c0d4503c1141c1014221030b009043c180182e01d0800f03529a04060000c20000c0400c2e1581e030340909445203e01c040c451032120707004108500e1160885403144c2001100030b44034681d0142d402400481d4081c0420541490200002e10161a042c2ca034a02a6130428524213680241c00c10090180c8600103100300c0d078508242c049140111210280c01c05e031100145051343d000c3d4481c030850517940004009890301d110700d24040301e400385409a07481c0705005c5035407240c0c0c001e0305200441003c840d14103004110799204212140c4950013a80c01c1ea44801c0541c80e000c01500880d00028824030440c03212440900000a1008100301030717640820154202603090ba5181562801d165003214003c04144020603c104041d815000180700c40710450000c07130810608003621003007001d903a60081d131000c4000d60b201e04009104683c005806044188049000f80010030100c0b0714450580228514078 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 68381576 1250 68380326 68380339
    0xc0e010b040317071e1208060d0305030c0909100303090602030f1207090803160c0510020a021309060903090504050f070906030c0302040306020f03011e0e060603070e100906020f070f0302 82
    0x10201d49200504440c50b0035001714102802c400403c4200319148140581121030403003030b83c9500c20f49070040001502c2072074014004800390b00315482c10b45456000074070054001408006580c0d0300c2d600c038891701340034030800d81d08814910704500c0c014040c102960401e00a40d0b105100070017941611b00121025100c01c01c801250a460f090b000b955604020b801c081c8180c0008109112204001c0c0070499065000740400404141e5402c05c0c0980394692449400040c0c00005030780c00503080480c11441401c6081c1d000180c004055201c200480d036007480100c00040c5908010006031030301d8014141c0024801e40c030b00c845403c0035070010f003085216100d401c4c18541c03100e82410031a8040d0f0706440055411400039507a50080240c8a101d40d030090003060b444030703120b81015002c03500c20b0007134030142c61004510030f0309034440b83d00700311071a0002000003003042035111080055480380c10031392a00c0441178403002203290921001a08060075030720400c2840d4000b103800c1100c0704070f40e8841011680c050707981 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 68382826 1250 68381576 68381603
    0xb060306040c0c0b190c030e060604110c011404020f040506010f140d060b070c060801030308041104090819020601050d030e1002030903060c04030c06050708190e1306030c0e010b0403 80
    0x103560052070b602c000384c0781a803401d04015182c0240760050080562620003041060918078058085541148529100c0c1e40405c0c0080c0480c109544640000784102c804a42051801038200b800e50b0001030418940c962030742c0034003085050403180c114001100b202c00380903929103000001c19103031030100000304000d0040307060701c0260004030407141d010003000028032802e525049040300d80c1e40b1864003255100007079800001c4040c03141806034140d030303415900c1403801d032155100d00c2c500c8905100115071166079000e81a00044400008200c2c02d17441c01d10b0ac408a10395400702030304200701680308a018521071110500025404606072601520071618050b13500b4004030100e1035405142805501031003a4001e1051107440341016004880c0308600c1d5043c41500d0f40c4003144d96004203440105208003d12030100300c0e001c0045040c0741101c003440d0240e0348840600014552042f00b2020003095955100c1c248103206000e000d03440540b00101060000394980f0f0b9007410740703104610000e8021050a0031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 68384076 1250 68382826 68382851
    0xc0f081b01050d0903170702031e0c0c0a090b041a10080907031a010f0906050d03030c020f1f1503020108060d05070803040609090c020d050f0a030b0409050105060a08010b06030604 79
    0x703070f4141d11030711801080100010310b00a01807824400345542200c0219002802c11440041200c869120ba07100c0c142408043e814120403d4018116030100c501171001e03840241d44074460064020504100040f40d000e14010074442120516481c2d1010702c5a81d0040700d4a0340c0701c0d00f1200d960348142e407410500550391084135508014241d00010280b0704500554a261f074200801c0b241a20308030780481549a40d0340040c98221400c2d44101c41d0052171501c85140424040c0c0d020844a40d2240181c0d49070808220a80342411400305801101900c40581c4500080c40d502c20206111240021a8411819600042c107620340040c02540f050120f60317620801c00c5024003c80006100940449459944810020344080c03c035001da4078100b03140002c0d040c403140c800140c0d881c2c011502d450b0103180c940064101180740c1c0c0000e01f10000d01d912400c3d241c420340c1b1180b068021141c062800054181400c00030001c1c0340c0c0b042d500c035540c180e0408040300101e40d1103004803604207030200d034000f070700628281 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 68385326 1250 68384076 68384087
    0x80901050a1809060501080901020c0a03050304051e06090106060c0f02060c070e010e06091f0b0309030c03041d010b0406080c0304031704050d112b0c0f030c0c0f081b01 74
    0xe078242c1e40003850040000b0045401e4103c40c0079100e0076214078010365900d0014034201c0c003a10100300b0b070b079501080e1031502090091000b1904a400303641070310004441a51201149540c8052420440d44a18204119050280f03d4280a0500c518120045080c10380b5482901e9501c0301020740b0550000480640c0d105080144000500c21200c00c3c08503903071f4405900c90b006030112a40750051350600f0002e031b03200012062240d0481c004d42c02200080742130868850554100030b154031140d2204220f66030030310004001800041800e054400c035480e0140d20302c80000201070b4004070004a00f0301081c00503640007203459a004500c146c50320b4580d80c42e402e0407150183c0300c082120304030080400303010600901003060704000c01d041d161074511b4040c0d2409503941c3c034400111402e401400c50354000310000070a649141600107481c0c00f60450031141c46242740740042d40402c40200303010303055900070030142007000e44c000c140034460803510038907210b03260b40c8810101300100c10740c0b40035440a45035613000b103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 68386576 1250 68385326 68385347
    0x102010e0d020a0201120b060706053105070f0806180304051e1516020d1103061e06030601030f060903020726010b04110415120f0b0f03010603080901050a 68
    0x1044070749450316400082c1d2036281c040c0e02640000c50101102008400c1c3d0b0143c1007400201929551611255803280c0c0014071000e40701c80168a000745404200700b00f00e0101500c1c601c842580c2d0241e4407160b01d416480c2c01255840b0701c0300c1c5612480100807810010540d030398404543c03c80c04400d1480c42ea20b9600314031951f0029680188000d140320246c8600c10000400100c0540d80189078105031901c0380704600a244540d901000310100c00001800d1246000d812503200e850309002030180c51700000e042c0311048580070500000500c005020304c00c2c00b400b40381c00560030b4000d000c8550454444c0221015816409081542c4850030b40f000c041c42000548000c2901741404c01c40c0c1920840b5403102c001c03d40f1000030030796007480e900088a02d424490100d000c0403401c2200c0c070300b91a0220040740645030055040502504010012a8020368000c0300040484283c001801c14001070800115556000c3c0b05402a85004c0c0140001207200088071003205007403d1217500d0b00c0c410401220b164011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 68387826 1250 68386576 68386601
    0x8010512030c031818040b07051803060414100504080409051e01030302010c020106090b091605190228051b0a031406040501140c0301030b130501230a0e0c0609010201 73
    0x19119003910f1002c9104e02c0c2c1803421030350b030f24824400c0708141c000f410080e980506086030f041c011594581c040d20040c8028032408a062100d0444000020f08004086600b65014013100079104074201d8180000703520300725030113010000c0303082c10344885d80b02c2d0023140205c482d40b0b41e5510204a0030039000808581884031030709220850340e120314000740680302c8110380780055800d060010903405500c0c0280300c074210000c0c001010a0341c0d03a9000650152012003408184881003202c0c2108030000c0d41400c82c418070315002440ca600d24420441c11303044210b2040240c031035a1880d920f00180000ca2a0b000c00360340e440c1880072284141c00040c03003541e5140c0c0028105841111080030009000c150988564041e1008120706041140b03041a018411541c510002104100510014491405058100440302c0c3d0758002c0e40311590b262400c45600004040c4814058040302000707001e00c0d00044c2d0f000d100e900701402043e1006540030307a80d10708176441c2481446c0100f90341c291640300b540302c200c80112 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 68389076 1250 68387826 68387833
    0x10c060504031101050a0209130c051215030d08070c15060f060c05070b0306010228171306020309030a03030b031c05040602061e04020918060115080f0708010512030c 73
    0x20180350180103020f5049118440307500701000501e01201d40c1c820ba030341d4100082c1c100c01100004001c800d004004840303000082c480240590240c20100c0d00c1054440c001f100c1c20704d481050340b002014a050f402002a0f000c03c4008000c1007042503221041d0509140d03c0702c800d0b2019a10880c5040103040c868000310b00149021000144480d444450740060740e0049040d103801c140c407088500480c0c8402c4800a0143e8006132913840601089036409500d0b2951540c0040003502d16a81c1c4031040242c107400400c3c20030081074401a411030300f000d010042401d40011b518000d40c11011980301c00e07620401800385541e035840002c17076031414001d080c0c0405a05556038400042100090100d400c03d0007402c0c01480703000c00140c40d0040c2c00854001140c0042030b204000e684550070040000001080d922050303200c00d5500301c90355420080c0364080c045510b035400d080c00510310001d200d000002c0c01c07452942c103004240f02d103032030f040f4018905682e8107071010303040346d0880000c580c5103104e600090f0a5610 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 68390326 1250 68389076 68389081
    0x3020109060818030d0c0801120201020c09100b1611010201050f2206050f071107051503071b03020304090b01090308030a09020607080c010510050904030806011101090602160b010b040609050f010c0605 88
    0x103540c0c01408503c0c0303180c480201f140d0301c9441c5882c0382045004005c1c05a03020010103d698540034a00c190710503010490703006010b0b120039100b410358000c3e040903401c2c04041210002042403140380d0039100d120a100030002c618180040000801c0080c001c04e610b00b094a03110f1000c070302020910b08060b50012814810340c04c107020000c2d41503500311030700b800040c1c000006051259022030000d0031100010554500d003660b501080703030a81e101400d80005c0c0941040c42d000c2446410303801001140c040c5d0055600c5a141c68512750548031014600c41c100201d821040c00000d150070260380e000078810344001000c3c003083c40411400c2c8504140645006d20200d0211003030001500a144100303584414070050665403c00d0166561040d2802800704011400040095102c1d1b0a10610001d0303c0b0004112400785450700c50491703001840741026806c0005111090002c0c0503021401016000c900510741450300400500e0300ca00340c018240f00b2407018030440e074181c2c85204e10004260b0018070070402030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 68391576 1250 68390326 68390347
    0x140f070503031f050a0e0703320703050c0708181c050a030e01030218011d1002030c070b0708070602090103060905010b030906150102070608040204020408061f0905010302010906081803 81
    0x10f030321803018881c0d8000200c4003080d14141030f40118122039180c4994202c03911000700035030180c8030960f680070161004001102c0c82844508000e0b03050940003090202c2414060001000d9510090401c41c3d1040100300c041d00050ba0401150f540e025500869034804500400181d4070031202c485014069031500d24031001d01c071000c242803c01502c2601c071580700d00e01d9080103600340e001e00c211285030444110714030b40240d4090340d1000180140d03400d04218000f850350024034580e03021054203006a00200300403034030403410841c2c10007034991441107905041c02540c03540c140e80308078080100840c0d000b08a1a0b196402030300300c000074044d0b001c402c3c0090343e140c00c000e004c103030412615080d043c491400450721554054441400c0290186d0107410700d5402c10714140c0710307040d000d00304a812503400c11000842007800d1080340c0c0a10809a514804c03125540129890341013903801508a191501c001000103070381020003c42291020b0901c07518651700d80405c64804525800d005203d80070004160026 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 68392826 1250 68391576 68391601
    0x6021e011103100e0703050709030b06010e1005040603060806010803030403050a05070606060e010e090907092a08011a120a0f150e010504110301120807050709060305070510020d140f07050303 84
    0x25644440400d044c50780c0d0b01c00b0100c0998505a079403101054420600303001040c25071000581c440c0b010b060100c090f02004010880a000707055402c4000742000c01d040c015a64117004007001071030901300514240d41001021a100c1c84050310080500000080003c41c16003e00183e032178898100004002c42aa640005400d20b010309144c00d0008d0002003002060b0703d401c10105014a00b05030041072014100780c00c08000744502c00014140f0350708008144261a03030352a600018003071a0340d0702101c65140030070181030800c03400341c00c8441c00010720407180d41000700c24032254000f2800c880441d525444040510084c004c01c0003540c0d2541c4040008281c04c2340d03030341440d4102c0340242d904100303030260504040003501085c021480003a04000c400e001050420004d8200640a00c080e2011295139070034040c2280c940394400c88045c0c108403400c0000e0303d40ba101c0d00914001d50300140400000b03180005000303a0609200e140d900c1c1020a8110100541c68150303101540c3c8003084036900d050034030300707440e5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 68394076 1250 68392826 68392829
    0x8060d05070909110d0c06080603030f030a02280c030f090b0c060f01080106050303030109020d02210915041109070201061a03040c05040219110114040b0a0506030706021e01110310 79
    0x3c1084c0c81c01c05050b5a41010105160b649070884445203020f420a4011100010090300c802e606110038001ea8858070324000045018030740c103190059135814903440d030f0030304490f80080c6505400c502106104106c0d800c5800003400b140d0515000c44860354007641030740c11680940040c0b004603000300c0c0082e40941c4c001020b0b1300a401e071150004003aa6078031002c40c2a04c2c46401150340580061004110000700c94000e062120070080c0003606007080308460350042c408411280d04c0180ca081c06102070f9100030f208561042030a090400351a1400340c40b074460524010000501982e507650005030003c0c401c2d0700034000b4028140c052440ca8040c03000090f4075403c2981c044c3c1d00c41241c0310000480703161601c00c5401c1c0003962000011521300710704050b2042501c1d8044003e82c0e540341e074400d260340a4440c5c8502e201d0740c07069054030301a05002c40d04030200c50740100254001d9221003030501586400151050a20411101d044516490f030402280940105041c003c0340300c40102c00e000244100a80c03400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 68395326 1250 68394076 68394083
    0x16140705030303162003071b1208040303120b100c020310200c070f0b070b06040e0c0d05010902040e030a1202041212050c0d050301080d030603080a08060d05070909 72
    0x508440d11a0209901c1e48000e8031aa141040c1d0300d0340030003a05000c2c010209503001c801c1008040400300c000c82a0440d0b0150700304617000094141045070400d20b48494101030b208521002c845640f00da83c1e0601c081c4145c0c04081c0c14040780e42440c0e02d44d4400c0d90800701000780d000d000303c4080440e500d030180c000060f01004a201e170141d09000c1c04202c003240301c1d404485001090000c440d0b01c1440d03251541d41d121880d403440c90b0082c0030303001c504402d2031481d0310f00400b0b44825130303a910007160504132513405000d02079511860400001c2c0c0c1c84080b000030400c80c411411604804110710324a00a0b00405800034002d4000d420700036644c2507800c0110203042140d4081d2a40c8460100c04039000c0200e21890143d1460b079801c3c1c0080c1c40c00700f0455605050180e0007414007030b02c0e008440950390b00c1e01361319442e20400514008018881000c00b4000841c11002030306003880421704596403040c1c070b03000f06081d000420801c04005143c60782e07001d80c88229181c016040c2c40000e07841d00c48900c054a80003405a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 68396576 1250 68395326 68395333
    0x150507030c050903190302030403050d1206060e0a1e17030304020103050708090d08060103020d0e0705010e010f050f0f040b0c0c03070611150406020f040902070c080105070c06050c1614 81
    0x30040c20b0003481100c00c1800c3c02006032241002240d0050b50805d10403e054003113100900001c80020340420106404a0305a00ca00454101c4003800c48191002508100204401e11707610102030341342c1d2000107058402806c10b044100c0204402502040c0042e401241050b10041c84224441c01c00310055010320b000781d03010300a50307030b80304401d82f0b10a0042d610060107601c41c0d1f141448040c42005010b4120b00d05147c0546406803080314034050b51000800038185402c5948104502e6800c240075000800080c00c01180e41010105c001c2c0047c090306480c0760ac40040098100c90419103002128003402c9200101074480384d1018203550b41c4d81a9400550203440b4585020811034021a9040c4220326484024a50401000401d001c6080040d00460701c4039024040e1a82845c07006c0e02030009060400001611036219081101c003d001d0760b408034095926000501102c1c80c2e0000c100d43d046904068003040c2903d604043c3c0b460b030701c40c0c14103a2100500443d1060300f0041000c0101041d400e280046 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 68397826 1250 68396576 68396591
    0x13060509091308030a0e010b090403181a090103050402030c030d09170c10050706060906060f021e0304051909060e010503010c02060601020309190302030601080604030f0207140103021615050703 85
    0x2d098051400032019150b000c0620000c2d90808903500312144c43d0031020008503940e04650b020801014040e5000c0380841c000d00f00400c08035400e0005000105074103440b2010300ca8130142001d80901c038104841d81010f40b50b00000f01551000c20201c00d211030040c0c2121051064500c0040c02807841d13006154208100c850705178200c140006000c0c52441c0700900f01d02c071303482900f80150b6443e4003030781044030450b0f11802c001441241512900c0001c1a41d900c501d0404120707038400a0034096000c01e0300f540324a0102c01c0707610b059800000e44056460079100c0c41c00780000003d04003900c04259016920742420000b01040713140c1c124003140e04841c02580244148003069200381d03110350080307898038011b034002d204c1610076103000030010703000200390031070020040d84a402081c03c122090300040b8859008100740810158001c1c00f180445005102901c41c041c1400040342442144018040c105078000c102401901080c040600f0820b1784450740c00b50960580701e420000d00401c0710500046440c2c10f10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 68399076 1250 68397826 68397841
    0x40f06020307020a09020304020111010606030605180108060408091513060e0409020f040b040e071e060206010303050307050310080604120f03060509010b1e0304030507020a051f11031306050909 85
    0xda0300b0156000344541d20351801c0c50942c84c003d400080080e4101b08140d00f00019080c0c0a1142c8001f4100760303076010401e20300341401d01680004668051254000200c0100103d18012030203c0d00240d02501450751800304100041d80380700c03e014000701d000d40029007420401c112815083c221500b98407101c010305c00b00010082154183e03103002e5000b01000341003803018030300b0f5400b1150881005000146690603142024900700d0181c10402100080c40c90702c1c2c10181106105c1e000801c4944010406036040da80e005040f030001501600a00101002140c01200343c24660740140170804115566450541040d614680c0d01e10b8045000c10034036030300520030501c039000e080c05482c0301811000944e481c00c450143d080c0d1240d4843d410030641001840d18a40c544401140198025a80c203626a4030b03600402500312078503440540b0941d1011004000511010a8170030742d0800b0382000804052110b0b032080c19803041e041c0d1203a042c401d02e0400705185400401400d0514001c3c7c8241038503656404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 68400326 1250 68399076 68399083
    0x80d021c0206060405181b0f100507030c020105070b090d1218020d0804030503120f010b04050d060b180703020d0e010203010602150709050d06060501121413030e0303040902040f0602 80
    0x884100040c2c0140000405604140c0c120a40011020340740302d03400880b4035001c90a158030164171007000c510306410301c0010b00c0d11600030350950b48200c2d1202011140c407400600241b0620000a05010b0003c00c81d1003568022000d80d10780c2500501e0750001454000301d0192503442581842020910045840c00055401d128a0307070101010710840006041c10340030084141c660711030448050004020100004800780058170201e808064102014100718070032500c80601604065417410341480f00708074980c0d03a560060002a004030f0009082e030200d40100b201c40c540d00c40034802001189003440841c030351550050124900800f41040043d90b000741710b070300741e100c2031140c80d00507440b90248a1112000c5842240c0002ca603090000505540320086540101c100c1000c1d5091a600d000070061540c000341118003c031201d4004100145070799090f41c402031005043e1020025031100b041040602800c221011004000d08a80d262640c2e02c0240000c0d61080c000c40c0c401070304a110016000c1d0001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 68401576 1250 68400326 68400373
    0x40f02060a0314130c0b0c031902010203070f080601080c2503120b04110922151802070c03080913020c0d0f0c0812071202070c080717060115030b0604080d02 69
    0x120407103141858603d20310b80310340084100105500040009c0c40d140031003250030b08103895a0350005600c0b40381440c00a41542080202c000501c010700c07081249982c1d12401c1d0703e45c0903d10400c25520f4550714180600503100016400320341d020007441c04028541c20441001d00700d02ca00c81e00b07120b448400b2003480241e82e0301c4c0c50401e644603001d121000040c81c0100e0301e90303403018250751444080c3c00c14444950940d910b5481140306082c80d00803d001d80b04502c0259410b00220340ea080d8600403c998807140380c0d880b2484040d126002c0881c40410075038494266420340b4280350401d540321103c04200c0c0d500e0301000003c5a012900c01045104258050010586415045144141030200c40c10211b05140c8000300004100052010160003c0303405202401e000c500541111100c903044c681c4040c940a01034001c40d690103144284860150400240e040c19101d850f200e402941c0c1090000341c02802000042a80c061004207012170403943c002070101c0e40703c0c030b00c0c1e0840308600c4001c04c0314002c021b090f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 68402826 1250 68401576 68401583
    0x1a040609170703081b0705061302040501150e010c0507050a03030e0a05030601030209040b060102190803070e09010f120f020a0b0a020105061504090b031f0209011206060f08040f02060a031413 84
    0x5601c000f07a0005c14643e00719882d0070180000e1440d0117215907502d03091402c00c850030990601900c00440542c207061003401d0250080d6010010015410000075242031481681d544c104040d40100d402040028407186005200183c0003801c45500c91801400000d4010007031805213540c0e6100140c1e500e40080c0280c100d07034004d0510002904d5540350078408070300c0184001c0c1588201c15000c3c40c420100d41c42d0b0662a4001c00f0b00c0c075182d0600581c0200121040b512607441060a81c00610004c142049000100d401c0b080c144103401c1d9040c54100c070708100d5400080e6000428080000c0d43e048064010803030004a54001c11560342c0390380400000501e154a07103082c04070107010600644021350701250f19004003c3c11240201c1900500c407800b400300c95404100b0f103402144079495035806c60710090500d6003009003800407508203040113100c0c0034103d6101003000540c0380800e06200d14050b0100000b9005403556903102c000b0003010340507052441a110010034003d000444452840d0886131841c6d60 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 68404076 1250 68402826 68402837
    0x209040f0219180f060f0f030501030203061603181101170f1302010507020907030e1b03060f131203090c140f060a02010e010609060501020c0114030703091a040609170703 75
    0xb0802203d00d41c075980741e416030070f01e40d030840850f240c49014940402030038242d42d22002002e03031402c01400605914980000d15082c07500510050f500030407119848084031054400010030035004a0181980200b11000100b4041d0400180003c0000030703541440280c8a80055520030380c3c004018a00881d074100c0828a102c01050b400c55024040e0150503005161a90500310340c1c0e000250381490035030f003110100340d8030800030039010024800012011001c4488540028086000c0303600c4400041c52840860640700004c0c440d13808400c4d16031507072074006d9103040100b050020701070005c2404000644002101889c0001c2801c0020103010042c00c0c00307480c90002007401c20038020b40340c000d24602d0b0155501d503504440552800d00c81e000040040910110b042c80c81d260002e81050544242281000b4883c15011400040c01c0b080b00e4200c000e48c9030000315490309003090b01c00851610020407403080200140028000396800c511152802901c52054006624080b852640710b490401070204c0ca = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 68405326 1250 68404076 68404117
    0xd14060108062401030218100c02030d02070303050f03090f060108030310050405040f0b070e060d061d040b0f0c0f0309100c050901020c060310120b150103020901090b0901140d0209040f02 82
    0x14406c0e000360690b01c0d41d285105a07105403240c001003e0300da00e1081e10000071a603207900c1d02986004c00800c1d03008010341c009040d0302810b540740180144201c044001e00c1c0032001002c0f41e00e007102000460001d402c0c8000b61030140d611520016125031054407215418a84224040382c0c925003845658011036108403485080d942542e07402540540040c180c0e0144000c6055420613520f40742c0003458240155440050400d0801c952502c2c0d0b4000c1c00384854034007024104000c0003604030a41c098001c00b4052280c4030301d9469120306031a910505c006031000a0000c42800507142d00024205005080300c3c105202c80440c0700002c40c1d1700d00a03641054016031210180794103d003060401582c0142d04460408038903038407900d40c1204809107180881c0c070700403900708020700006c0c811016092510309103405d616205d582c2e23000800a160f01c1c011100d100758001f841c8185a8090080105060039803901180c40302c1b1501e00800003034220b151581d0180d030411401241c0049144202d80524503036209511842 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 68406576 1250 68405326 68405329
    0xc05030a050a0b09090d2a140a02100306060807080412030f0209040e03120106080f010302040f091a1905010b030a09080f120703060b03040b070302090d140601080624 73
    0x4100181950b001d030340e03580c2c00b040400d0300e40075680e521480204005240d02520090002c22500c80b9500a040a00d80b1521080c404804291141911900300309000c0c107500806408604000341806c00035031040d840011544100e4258000ba0300b25199900c1c3c00146995103001a640100300b1503005008401646c031030072030076000c3d9110104810100000604020350040410115103019065015542c008103012205a42400341240904000e251101040c2000e07a02c40d121a5410301000b44035503150244500e202c0b9696101007902d542000e40c01c411202204034812074910140c900c5200d419004955064140300350003000e040300c0800016070304d96600e00011400a1191a500300c2c0c0d91306003001210302803818000030349030400c801c2404003880c1c1031068026003111a291b20500024100303204100100c2e40078003046a0011280c100075a40d03401040008000c540c0078034004101c48201445203021600c0000c0c0b150580e2185400c0f1001500c07820800c2d0701c80303030610800310940d000c0401005c005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 68407826 1250 68406576 68406581
    0x615090a11040801020316020a032a0614010302040f090201081303050f040305011e09050316030315080a0510020c1f140c0c0106140307060c0203030403050712060606030c05030a 78
    0x418480320001d1042508210703000154856405480181e40100a101a44400d04080007440368203000911030594035650240482d04414402c9010300000e411841d0315030102d00e008a1115800201000038549044456045581c00e00080e4041d43c5004030004031851070380b04103140340c1d0301615106032a665040b445c03208408101811802c101d01440303411680a45c0101800185225800201e440c075840701044480f14052041039030351074184251940421004401c83e024040072905807424001c6605090300a408903e014440e5140c2c1b40704c0029220401180100e200c511036000d4ad04134480b6110090f00b64000c0d5800c1240b1504222052a4845e03a080400c1440c0f40b0130384c0380400e1942c0b00080041000308103d480d401408400281d0007807003002881000c01602c03074401c507800380c610218003190b50356401c0d0040700180809003403d04159a800c2094070001d6900c0401c0715006629003405221003c540300044400d282840c1d00820034030b00038002c030010010300390f50790360840e550f01c03140c00003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 68409076 1250 68407826 68407831
    0x6090506090607140322060f0302030a0902060a120b0612010524031e1303090504020c1c03151401080c070218090f0d0e030a02010c141b12061509 64
    0x30b0005007040b042000a02009000740360340701d0180036640f1440140580100e2903122400c0d400c0000291806000c101e420511805800d4142c0c9001a142e0340c0b440000d0005088002c0065032080e00030a000c07010541c04075039071200322140407052000342c0c11081030040c140600d80160000d004040014005420042c10f0b20024070000010078882e05c900c0c0e040b803c41c40e401038403251709a076900008298031305440c022844d000701c07410805410a0b5030580300100700501a0155510568002404040c154030801881e030a1010080350700c0501121440050001c03d0040d07820301581131301042c00154a001180030031012041030312101e21540d40c1e01000520303507109401c12607000d4010b6031000980301416880c03034030401d0030a00a00000309001500d503d88081d42c0c0804003000300320342d05c2e205c281d10003040748001ca503420708080381002003a1030090800108400900303160b2140344151604d9408282654400c04001e403042c1c8540b04405000300c0d02c5400444100204114900c5c4001140c01d000c504c1c41ea = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 68410326 1250 68409076 68409079
    0x1104020a05042301110312010323070906050108070507030503040204050703090503030f0a0e0f0a0212120c0606010e01050412030c060b060f0c16030209040303050403050f0403061509060609050609 86
    0xb45041e0315441c405034100d2182c40410140c01c0c2e50180d8145950708600c0401e140c0106000540c01c090300b42810902c812814040203044a1500d45810b114400c182038050003030154009030342c2029100c0410703000604551150fa03000408110100314480c0c02441280e01d0180c1540c2c82074615504d80e02800013500010704050101a50707404100040390313090002c2c40c05951002504e01301411b1012003035040da980200a0041c5800c040f5180c42e4036000010031714681a416142003614a1461004605004008010054410b0005600740c3c220001090051140350241c81700046001e558004540c2030142d8012814403c20340c41402002c41d001340190041941320f5900421074100c84c10114030355802c4642c0301e20301c4807808240d040d404442840503a01b01540c3d07044440f400c42c5107400044400101a2008e003d0581d1134000c1014540b11380f04941c001c90905007800d03030300d41d5030b440c20300b00602201543c0c2940814010340415002d1042c0606000c9800c50350f90550494106802c10200e5401001e145 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 68411576 1250 68410326 68410337
    0x70f0b0907050d03030b01030b0a0f030b18010212011a0304080406050706060b040605040504050105090708061302070506100504051e0105040b0402070510060f0f0302010f030903020a170a02010f0501031104020a 92
    0x60a607100403c0d103211a02c2a42c0218180c810b42d00050240c0309405480d512804d4110410b1003044111100041125004107402d210b0b903d0320051144004641e4240f1500c550000074583d040c401c101071000e0486061003544180d1104040c2d140e24180415100108000802c000c100081480740c4c000d09140c41c0916030020300c4a03543c056040c0c1560199000d000491004202000703240703024410940100000c2d14139070f400f80350101e03000b407140300b005101504c50001d07103801c404a11001c0d4183d03605203602c0780848225041845194000308898880c0341c0c802c0b424040051440912100c410203443c0036081224a16400d0104200c06040d8034400036404c16824404440415010030688010b0001018006481800e2190003444082c0c00d0700f09201195032004d003040183d034401c5911400e5401c51038005410701c86898100e040281c800c0c4050b201c0d198280c0002c2d0586031000080c8070201054000b007198098442e4080c00b507400c244406010201c05403000c080e28205074005010441091421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 68412826 1250 68411576 68411579
    0x9020a36060306080c010518100519020106090b1c030e0d080f07210806040b120604061a0103150e07110303090a02090c03040b130204060801020a030e060705070f0b0907 74
    0x310480031149901c01c030002074641600b000461004c0c05074000c074107020f29126281c40d4070210280e2411810070350a600501400300040d204a1044003920000720316074046100b003140d2100c0090280c901c03801640041460006032241c02c0c60080003030700c20140000c840303000b00b000c0c54a003940c080c081d030444660850050300c410380c0081c00050060402e085034800795920b503030150404035440c8014809070007010203803e0059010941003004540e0020040328007060b20002e500218494201c0040740c0380c884c0c4113600501c4100960b58200c0300f8603004140c146070752481d03050700440039200c0c1c0c80c0c8050440452200203100015241000c19803042080c2001d9008051174440280f071039000310f0341070f2410340180c42100c1c1145841c10340c0a030049002051181182045d1f00c0f00d424100e0b01030f01c0515404a131417214000c545403504108000d02c3c03040c0013192100c01080001d0060200140c01240c0c0e80a88800a03ea5500804c281d034141a0000c00e28010b8080595800e035580354054111515072091020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68414076 1250 68412826 68412917
    0x1020904020a0201060f0603090b0114060f03010306090b0a06051012021303030f02010501081b010507020f04050705070b091c27120b072a020f06040806010e0109020a 73
    0x1414404615030000881c145811030f20321b003481c019000402018201410240440c008402031303415100001c03600c4403078900803400102d080c458000d54003840f10f404030000081c44501e41c01004d44500501062489603038074600728080314000d0144682c801c0821892403143c5108801d0298211541500140392038819030883e2440c0030349a01c11800034813080041d040e5680e084c00744500528441004042c8040758006031a000c0030302021060412070041101e40a5541f05400083d01c048090030820050402c21002405a0300000060301e01d8480038011503100d080c0000d83e008122090942c0e544407004c801011504204018446401d940030b1b4505000801280c1d142a401070501c02401e000c0c0042034a0100d681941c001c21701401e03c44007030044075880c0003c0402c0ca1184c00404200001c040c402c0c40003c20a4078501101c07500184049804141914001609410380701428800c0405aa035020341d90240c0c404c0d818107400281280d1009109440c13400500244640002000d5915400541 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 68415326 1250 68414076 68414081
    0x12020c010203061201021608070203150c09031207050712080d0606020a1a06100503100e0112050c0607110d0303090b04050606040510060818010b03030d0207050d030501031a0901020904 81
    0x6055801036503001051045901e05000d204282e40c400d00300030350511001d8001c0300204031006034040c2c0080c0700040e483e0215a801c1c0f002c2c1e40b0f461b00110f00c04ac104d04103074400b0340340ca800888a0b81e0007845000d550605202c0707004141c41070964400010045c071814010768054030325402c0303002c980c204400e0011090400150190501415007a40100081119410991101a5400420728802c1c4103071050141c540c076046800071183c0041d0400c290780351604209100c003024194482d00e11503003514000300315903a003820103811082c0601c0440d129150010100070070342c0728400c0010702c0d4007414414141a070500b034075080c000300c4c02410002000c40094880c0710101c41d0444040340c9603008181000700c1c51400c0c1c0306141e08108040e8200c103d81e42042c0e0042c1500741c0180190350001780040f80c02880708025004004402d802500707403a11800828804c801075080194200c400f4000c40030002c0202d031003481018126030300055510551014a04a0380b0843c0028103c44001d5408011000d160385490 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 68416576 1250 68415326 68415337
    0x702030a0b0403080f0103030f0c02210a02030f011103011e0315020309100501051c291005010507030c110a09290d0209010509090c040f0b040b0d02031c1202 69
    0xc100e0300e079091a007481c00800c406802400890078403100e07801800401c0d807008054040c6607483c10200c00050580c000124840900081c001901904002050703c641d80031642c002c4152081c1c00304c0e045011601c0401d420b80318580044940380c8414401013001c40100c0c12294a407200010600c03c0360390712525a40c01450b0030110043d6200e40000903c0044a42045030410141c0481c00400c02075040c2400640780300803420014045558111b40401440b64000c2052070707140e003240412a071100c1a49081c204803804952099480391002400a225401441128102545030fa41c1c010580110381e107510105101c0740d16180c114104050120301000c1d0f512891014001c440c2045a200300c228040700c41c2001025161070040401110450058603a0160300d8159401251b801691340c3c0c0340203181d840d0540e00038005901c20301340031800c1d001c1ea40f594440c4004070030551f001d0282c0b0796184140405000a0200250141d10420141d07850b8064000c0100b880c002c0c52030015100c01e03105c0000e2040c0e0700320 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 68417826 1250 68416576 68416583
    0x2061911030c18100203090d08160302010903110f0a080318060c04090e2406011403040309030210050c0d08100801020d06080c0108010b040501080705120a0b0312040e0604090302030702030a 83
    0x1003807800004400f0f210014104201d41c9041d1400c0b41c0000203403203000f000d0281d4020400300e01090100000036051380c10642c40c403040c01d032800c855414024041d00c2040403c0d00800d24840000b0650800402c8903618840220700600c0700e000f16681d03c0f011503000500450340d0902d83c6a50040100c404c0c03080601429010144603165801d240580341290381803149501c03994020004100b1440d510025000120525404c0c0312880e641c640c0182c0d00e18400b21140600d01304008100003c0640169000050307074004d8503560410240f205081e583c40c4502c0700c154032035502103407013412100e11880440354030801301400d2062990342e410003a400c0ea0401c0c0e0360490240d884407030600c8885d40800c83d2411124003403910b2021035150100c180501d108038003845040202d4100081c071400e006904440c04541584c4420b4aa450104c5608005000300031925219015403101d00041c01980820340e416100003101c407c03034a46840c001c110041c140400d080701540401d20051000d66014049110300c2da00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 68419076 1250 68417826 68417851
    0x1103010504030221090a050609011103120a0c0314042310020d0b010201060b0d090804050d0b07030605030105070504050913060c05220303050904091103030c03120c09010206191103 79
    0x101c15164004c1e10b944500c40d00c0358410502280000b940c850050008860742a280380d9130f01c1100300012102203880e1490b04503903100001e1910050f44130403d640c0c1c8a01c4803a001004411714000045007500c42c1810032a07450400e07000810089034109100e110b00111401d0081c108803c400b0055041441c0045407008080d070102e5507040010b414091200101002d2000300101802d0102d5000c16000c0c4440011405a0710070480040001d4001201e010b00001890200d10b070620b45084400002d046481c000000e04181001549040c14040e1134007608650310380a0170716091400b400a414001050407482e48000c2400d840451414030038444422030940e20243d980d06502d8a10380f000c031504403c100381030075031300c0300b000401c4d4080107031043c1d05011200800d40c410141840e28090032004010755060200050003954044004002d01c1d90701a65514030031070380c0d03550f0b016965078044c501086025030044000596402e00c10000302c07121031905800020040c413000400300c21608120b40500c01d01e079 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 68420326 1250 68419076 68419093
    0xf12100f020c010b03070f03080304061103040f05010b0405070503011203053127020f0c0d120c11210d02030709171f0c1b050106050a0503060103050a0f11030105040302 74
    0x4004c0c050480540e40580040000c41c2c40d20381c654041c6001840f000e82282004401700d400c20034a500400d1003642c8100c109900c80c141820015401003081c80d04681c250702c0d1461070603540c207260003498401c000030303207650f4103507880c2c03051041003203000c24012010054100700c0310324503294608040f200d200814041111602420001e00c211a007a0740000c00e078a1000c0c0208071011b5004810401c038a0700300c00340940c5030b02078841c08002c40e0146600c2e42603035005200fa8104501da101041c0441c20318201418000204881c20944803d1000394034001c50341c000521928641c2c2104101081e5196500c019174034003101030700580300302d0300217171402c038002501448104510710003424660907108240c800340c01b80b64201c4000e60100d80d81124000001360300c031401c10707035110300645240c407145021034851554020b8038a0314034000c00050050501c84c4c4840ea00214903402c000400c04d040e41d90150040c1840c0d015901d41151340d0b403209008907915003011184088540b028018580528403031b07001000d404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 68421576 1250 68420326 68420347
    0x150b0a0306021812030316031e0e16060c0609020d0b0406090521030610050d020c0309030607030b100530040501050906130807020402040b030f090d0504050f12100f02 73
    0x10f28640140c400c442600003a0319514011044982180b030f4040003154068410708254041d081d4182d00b840d82d10103c22015100030f42c550401d00c4080a00c10650f0503403c90100048001901c0d402100d00081200080c0000540140c0c4024050b40c0010230801a80c21680d42d5400800400c403421500b250b1114009000c00c881008046100c0100d400d0750083c040f501034002103d4000204540d100b102000880316825002c2d00407601e9030603003a5425541d9000385c00000791381c0c2d481201418002c0c40390b0000983c00601c84d21071100d01282c0100308110303200c4142d004542c2600600c1c4105070040c100340c003508000d403101584010b1603141a0541c900780c9880c1c14204d08460300140009183e4018108020072058407020614100c3c1e0f003c468252240481e0002c1002030085030040140210004203224252448110ba6841f4140300800ca51300c3c80e000a204481b280120300c14a0741010100141e20342e946003e041c00c50401141c9400c440b10781d000659850161142c0c06100c542c00380c0d00050a4800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 68422826 1250 68421576 68421607
    0xe0d110f01050c090415031b030506011403060f0a0605030703030806010206250c0f02060301060e0a062604080c060703200301081011070501050906190e0604150b0a030602 75
    0x1030800c0c0200301516040b95400194815011000e106542d10340f20045800901942d810155030428001e000c6440507284403140c080440c08252114841d440000401c0800403d91511481e4081c010b4031594940e8000305440600141452044549489000c103140e1000c010790350045000b41d8800c46203040c0f003000a410b01c80041c021021205200c000d065162880714030201c0200b240e49010900c002483c1024500c581d0f5440d0006d510120001c00014607070740c482c81f12031012104a520300411691800c003a21b0010103503500080d507221262016540030140c40d00542d0180c090f2182516040b001484607042c40002c0b1001c0001c41e0386d8011604000310503111000c1c8900018009038695410004600d681c1c03d114906469603a84840c82075012410041c10754000c603900034024003490911141c8a0748403802110154050b640c00c4595121030f240601a60604601d400c01600075602c0d82e40740c0e018074410b40d100f201c0c10b168980b5940000394484800000c01980a01c40068840c580841c50442 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 68424076 1250 68422826 68422843
    0xd15060305041112011401081e160504050402010c1a010f05030a0c050904021207030c0806070801121218061101110307020d0c0204060f0603020706061502030f0d0e0d11 74
    0x41501e403100300000107020310b40010700350004071000404031010b00952030242201410400c45c090708040000f40d94803001031316014103601008603c108442d800c0a1a0341c4041132410240d00411041c400c1002d82480e0748120380060040c54043c68124040d210301a010134480105d4000700d40090040042d0074400ba60b079005040120040c051803074582e190b03007480241030300603148500d160902060440d550801024540350305002510901c07561b80c10f1110100e100e901c5030010700e0143c1000180c846102d0401c80d8140c540c603041c08107800606444c3e01904402480030b000c1405103021000c5c0c4440d4540c1c000c9401001290f9500c1c1141480c82004c40c00d490035031446444400e010303c203102d60180c0104520020318038500d089115940d8500004000c2e0440d0350100e003902c110007002058041d0305400038500c09000c0c01007030100c0740d50b910021510b0b012020301c110050f01705002c00380035428582c00501565080040c08202c00440a2469040440b6442c0010120318121125180c0325818400000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 68425326 1250 68424076 68424089
    0xa020a020319050901300b040b040e060a0507140f0a02100510080c03030c1f0b040f050a0509060c030601050706150b0c07140d14032205120303060d02040b01020a05030d15 75
    0x24a46d0401440c0b02404c40005d070f400681546400c41e030702c0c40d034031141d12a00081d00000d00074441d00941d50006611200280c408035100307410040001c0506019030140d0303038100756526081e4036000710b8211034245904041c00480842c00354880c10002d480890007601e0040d0400030030415140e00d0070004a01d00300107100d0040c001e403c10702140c2590500841c64035014180c0204022400700301c24000c800403e5080c2043d50b2180c6001080c9080728411340c00b080c81029807007810011601e4242c4469910002203030031601c0010304000041865201c0d1002e0140c02d031040001003028482040100d40445158001250030440800c2e203000d1200301300702d1540149010278905841440100200b040b045035038001420075289241c4054105a0802c1141d1a484664079082c080071103808011014400520405100d41c900c201195100d4902204483c06590010010140c0751056800c0c000a80a0702010714103500030040c10304003141090000f0501c0282c4003800044402c0e0a100800c00300007144c1201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 68426576 1250 68425326 68425367
    0x1a0a060e03070e13050a0501140702011802060a03090501020409091a01080a080313050303090c0109081203010e150907020309011707020c1302090a0f030203010b01080402090a020a020319050901 85
    0x15a03107480c08903001064804520040c919035940c940340e8183c5400e6284010050f10440e0b40c000c0c01e120301980400350950010f4014071300c07503d40c56001c13401d032403840c40361000d99400d05001c1c2c2c2c01440c0017001015208502e05010403002503e48031103007260050f500c102001070304c0e625080d00700703c481da1803500e40480341c00d65203003154106a8403075a07404608400a0440d000040803030001c0c104060790700b040381d900100b100d03034034a8140d00712511440a0301c00031b800310740503072404240c0d00340200b115440140c4101c80c05c0e082d40e10f4034000c00c90301c40c40a41810380e1500003511020050303c40c48900f40c130400c0b2680003140c0e80e0101300c000400c1d4400714014490b450841100348a409079012030709c1a2504021680e40d1203290070aa2184020700ca40801070340e001d44031a0000806096440040c0b0440380220003c000c0328407044015201604101d800070351265604e00064140c207150342c06464101520310407682410506004425100a848040d82c0800c2000c1070b05611036a100a00040100e08410385 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 68427826 1250 68426576 68426597
    0xc0f050108040c1503090609030e0901080102031504110903010c0824010f0e1f020c0a09140c0705010204120f02030c01030c050a0e0d0c0b0c150606040302060313061a0a06 75
    0x92244250590003a80100c4c0015404e6405852081d0800d5980c150044d0040040c00001e01c0d0240400101c600c1090180c1c01c003400000c0c44c181c0603c282d078801d1324140c22141d2040030100c200001031002d48110500140b061114480c1505c092007481403100310b68a4984003803c06100e5107106441c207514010389050342600c00401d9076403145100d4001c446604184000480d1680000c100880710303905002c4a512144035495100d5000840240300103040c0c4501e0f0140b602c130320b100b0f0180c500c42c8001f02102a01c4002041c80f0440c1d807001080550b00410005081680742c00199000701ca4415007a140a148080504107620b01408420461902400c08000728143e003203014000d405038012490510017400c101c0481038a40780006400036130b100300035100c3c054548042403d03641042c030b0340210901c81c120031000b1440540c3c0324035004100c028491424545180d00700a0582d000500c00b044000446494100096107401000d07c408000b40c000c02c03903120700d00284001c81a0592080d000c12000404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 68429076 1250 68427826 68427833
    0x108030405120304080706050714010908041706130803060d140601090f1802012003030f07030e0604080d05040602040801020a02010c03111606050a061701020a1d091602190c0f05010804 81
    0x2643d60443c3c180d2304201e500d40d40350f8145000c001400409401d12542042049030800802c0302c001c01c203646001d1403920000d15601e00280d6200c00c11914503810f49102c0d8400c0003c1018a4041c41c1e00460080828005004c21382d11028240105044c49085920040051011607800d00070700c60801401c0d50f041040880e03181004903002c045910103410303c800d802d0032410700e9400d64102c0e000403010f030003101d95904200c165100890f10403680380700082c1c0f401e03c0746444800c0c041121030042d0b421031882414407804580480c000e090140c001c90702151b0070000052442420b0025006400694000040329151610090140c40400c0040c4c1a051404c001400fa90700942c50100040c1d904540c0001d01681e84088190007400d503900032509080383c0303400e05c83c0307401030540040014203016610b42503d840c210f4a003e41d2443c6078031007144d0041c003410010b88586c5c010380320f40003800300a1044443d01c410382e10031031100b0181403009403441b00d070000044c03041c001035080c04030040900b81f81082d85443c00342c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 68430326 1250 68429076 68429083
    0x3080a1a01030e010209120303040b0a0605010801090b130c0f080106020606131d120717120a02030403020a0b0106020d14030c0403020d050703060204142706040b010c0b010803040512030408 83
    0x1461103042c1036a4101815000c0c0d003d41c1a039a2149000d4103203010441240c01d455581d0300122805c49400700a4070010703d26450ba402860101c5a044e11a00b02e6a403c00e80200041c003441c01c20705410080b41d80c0d91614001395030088407108281d980701c0c02040c00041200a1111b18140c02890541d40110144601600c4002114400c802d010f200010100a6004582050004180c84040f144540d41011b440d503038000c0028040c2d50701c1040c0c280d101401340c201903129070082c110b008481d5504480024040c881c00d800842c1e10a02c28410380d142c4990301e607a000c48004084e0819001640030984408446c4d8115003100c807a00c260f20000347c01d61400751041e02c010b12032400001e0141152450300030420604101180281d984400155151a12100880f403000e0006001904c642d0780d6038100c049082034140b11341d40d5008217150014032596507205000140040388000745c1003040c0084002e0115442130750103800ba0a20390055a07a5038030706410400551803040c002407503500704000070400e050002 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 68431576 1250 68430326 68430371
    0x250e01110609120702041e05011805070c030804260307120e030405060a0203130602030d140402010e040c0c17030a060f0b030f060103020405190812042123010903080a 73
    0x2081151303a01c03591440450042c054416880e10f2602c44c00e907000c005000c0f150090740c1620840f1183e540c410091013404800e5036010b44003e404500c0350b010407800700b48201c1503964014091056040d030030041c1c0e50b0f21050189840080504100c6c08024020400d034032880e8254807401d0800d06101c901510428152240701e680304080c410700c0c000802851032402842950148404404007810413682d4260107922603020340c020340d030f1841c80c1000f0307038040441d6038041c580129010780d980381c860700f490703802e200050003810190403d04c10b04018240001e40c898001c02018144c1881280c0c4a00b07002c07401600340c0b2120b40112080011800c0c080c0125904201500d0f4440000c0c0c000c601ca58892000580003480b07160840e58004c0c82c5030348446c1505040100e01d5040311012012140d000d4020141510035011310b0040d8103a40d0007828503070008059031600042e48501404071030b000c04900d04040554030301914066925651104403c02c1855000b298007584100302d9541407140c1100c0c0e130360152004441 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 68432826 1250 68431576 68431603
    0x120b0d030504050423151302030708060d140304170d02030f0a0315030206040e0403090603150302010c170310031104050402010c020121020c03042912250e01110609 72
    0x591122650416072805620b00d007172090a82c00780f003402d2a11007102e1201a07070321414090582d400320403d20400c24805c99110380440c0c0c0e61400a43c07500342c00c02c03a1203440030b003042d1003e49043c019540c04c00401e10082000f06444d180b03859034240c904001d5802d041000d4106015500103000c0900000c014030200c8105c1c0b00c980c5030008082d809036054600900705a0000381d00014003140100e0304114901900740158040c3c0c80e807190351a910301d0104c3c15106281c1c1c00c04081c0c46107060400065004800c44582c0302c2c4284031100f421001000c1e9040740f6007040f1140d070b004296041003002808a2101e510301ca20742e042d10103014a18154001808070005803a0090400001d03c08103005031440440108448540352020765803101d190360610b90702e4100c4d00485142e45681104c842a50210003150406450300090312801e003182c8100c4d60300700700d900422041800c010007501c202d00c9003111704000381a01c43c0c0d4950a610801d0100010007040740002129030a034030100130b0110352180050401801c128 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 68434076 1250 68432826 68432831
    0x1106010b0f13080118050c030f3304050d0807093b150307060e0d03110a060f020d06170c15070b01030501061502120f090a030210120b0d0305040504 65
    0x1c1e0b007900000320405941c40402d0551a01e604910307501a520141c40c0303098012001c5416203907181d006c241c1c54140c4244002500d078401c001a64480ca0800c044407508103448129190060612a82d8003070400200e8084070303250031120382c0402c2c0507004a48141c004880b460442c03c484e041260058051160f00a00035099a002441401d074040109200c402c109040d998a9194100100070301900d01c045c561251081c0a105004942d440c820301c802564118020017000014000391001e840c030a04200c0610307441e0054250010100d4100e00030340d00708901d0000c0059460b030008148101700c80c2c003900800782d03c54011031099810300000800078062041110407514214051044046030302c0380200c001c101c40c800034000401e0260660000e8210b690300e1807041d40c00c080d00c0380200e0702d8030448007500301d5821303090040404041c400006810005000342460511503240c4c4c0000d100f0415411600001540d180e440c0c0040d0140c0b03008003c6045029515651818070301d40e00a070840c041c0780600740c0110b5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 68435326 1250 68434076 68434087
    0x2120301061b02060d15150c060903031506090f050103020306030a03030c03060504090804090c0807020316031206030b061e0a060c0204021608180d0308010308091201020c0a02011106010b0f 83
    0x4000c08616102c1960040025a660300708003031960261025851001c50850b4000300000d007088900c1030210000145d070760b42c4200308081c1e61101d00a2040b080240c0406560307140c10f40a00c0764a0b081280a05419115440c820b482d080c410700c0500b9131900100d04050061080c410161400a907804c40c0755814100032034030a0111104400528a99002c00c5c1e200e03040482610074003807070b14020f005807606040140072400d0320841c1650854415219100181d004000345411104c0d041081c0b050681310785040012200601c080c0800e0f03074620b4000340c85140c0e00780140041494032003091076184040c14400d03a001b88400b030001703907019040d10900c801c0c0303c101c4038420f0441d0345650480e112100300e5208294000352904060640f5048190b01c041d400300000c981d07a1003407074000d04113100250b15580d65604c036821550f42e140180c002000203500041607040c2010b68030b0003070000c0d0414150340301c02003019070010700005101e1881c109100a0b03940240005210805038501200c54905000b142d841d03468 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 68436576 1250 68435326 68435357
    0xf090d0f0905211212060f060f07140303040803061e01020304090e01290a0f080d0f050c0f06060120030904090c030c15080105030c030a15021e030603010c0212030106 73
    0x10f00c0c40340c800150740965040003080481c030b0405031803c0c0080300420405640c504c803d0002c0d41900c924519400803003400079000001ca80d00c014004a07124041c80407520181859031032031904151411520400e0100411480e070802c0082d40e102046940d0382c2800801040c0c00103522032142d40034003000035884041d01c480d20304094020444c0001c103d1040c0411314180740400415036980111140300e41154200042c034210307400c1d030113801d85103031001400790840b2641d4141c43c080b200303440e1601407200038000350801c00810300c040f0368450141d002414403860054001401165529002910150300007600d619501f000400d41d40d044809031000a1a100c0c6401d080043e0102581300404803034083c60003042c81c0624100400d9510116220003595980310000c00d6103500e403540751903401d507000c0f030076500c041050002c441c95151081f41d00145011862110400b07100d10380e10a45d04c18140000a00581d0b003030034450302c14007401c80d202428083c03410030480245448184100010890441c04a1812 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 68437826 1250 68436576 68436619
    0x100806030c0303040b0322151a0904060f0b010302121b07080f0c06010f0503061504060b07030804150504051506011404060c0606060306050102030d0e0a020402030f090d0f0905 77
    0x1541002403c80b0303121540d90b0600c80480e80101d507101c41820701c511044454000e112880d04c00a0b9000404200c1100001c143d540100802078080c00d0f50300e001c005000d850384500c5021401180202404540d241020320500e0039a0385865003581050700c1080f40d890b02e84c502c2210143c010b060003200302c000030001b54150380203004440020707180310800500101542d21079001015901c04481c00d440c41c03a030380d6000c2010411894822160150040d200088210bc400e0511001c05c40e002000011403940714480410641c001e603c0460200351414240418070a4841c2c0c404800300071032605000a291507920107407903500e40541410b25004113000300d5142e0380143d0b0080c040c2140d411500b9199903441c10000e1001c81d50f03540c1070720803500d01140490210311900a4405451042e0000e5103454080c0c012400140020f8040c25114021170002c030005903528001103000f0310612000550b41c1c02d0950441c0c1c107188200d16114203011040c1400d8075401d42080280c0102c3c1e808407156841e1115079408c0018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 68439076 1250 68437826 68437843
    0x13020d020f03030f030f0702030f0711130c02070302010201051b0f03130f0c0302130c09140604080601150801080a0c05040207050c09010e07090b04050d02061e04180509060610080603 80
    0xb4980000700e82c0240381060340000e0b51240c2c6081c0c040d00c106484840e016a00d0b4400c86120098061040203208049034424004110b4000b010740803244808482100104032030300001c01c0401600706030010402d66a090081c241c1086400d03804428200100600386901d10134410550107007200800003a0002d01c100c004158106d41204100ca940700e120320700030341a104940012886002100c6146011429070302c40d4104980c04c0da00c0301080d4500b0218800c100c0070b41c60000701da005034104400304458105121a46c020034580c0b181103459561103101902101c1c05030071800140e4010704040012075980da0340c0340125401a980103a8540c00c9081c000e061040e514501500103040d4800027850405101e001c0340310b603540e40e441042c241c5d00c601800c1180e100b2481903d46c002050900100545030001c0104110001d4445841c0d58098048005e202038015038040c15600e400c3c007080920500d514002c4c0d41d445034007c0c018107074619207103002500002e00341c0120760800500b02c0021ba550b4404120580303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 68440326 1250 68439076 68439079
    0x605120d0c03170a060f081b0118050d0b070201060b0a020309151603020705030c0406050901051003020417030903121603080405210712020a0807080c100e1506030613020d020f 77
    0x200f403480d105161001400051180c40749a0760b181400081e6218041074889001010b41c2414001041d0b0300c3c0115040e403650b8001500e100b440c01c078001080d55410014140d494490218020b041c509000d000c0d0845080f5449150090f00c10001c06d20b4480e0702008036500c94108841d2080350003400712207450103005401010303404402c41d5200e1014550001200300803651b00300c08440c911a0054180025145144240c0780c20414440c0140854a0032280b48410700d0f00c90b141c01030603ea80d611565250030342a40c4090303020b810014089500c0c0c02d05000e11494404208003183c5001910720b1f41000108009402408004842002c00c080140038400d038081c0140808491003400c00203442c2034000d600442e422184401100d6141d0800c038008144040c00c59001260716092000c151a10003046d07200103144420b0340070340d601c06c003401501885150380d40740010b4000e018200703d410b000e03c281c5201a141d5403003070388031504205414002e0110084800d906803490035a04083e440442c07480c64100e024503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 68441576 1250 68440326 68440367
    0x302130603020c011514090606090613080607080c2b050702030a1b0804030803250801030219081213030803010e19090818030c130509010605120d0c03 66
    0xd16181d264028088480000c0003c010121003051141c94544551046003490044880e281149280c007030344480d0300001c098003040c5090413000000e68103502500d802c0554106030001400108800c02c0502e900030224102802c950614800310261070080f1009946681c20042c01d1505650140c9200c40d003681d40048240590b05080c84040e40703039007080c01a903000030b2281450380d611803040406018010380041074185400e003103458001c0580c2c00101000c43e40e460000d01c501c80c00c2c0340035043d601c0c500c110b85e540c0e240710b504520401c0246c0d91404000c1e43e0b00350000c0400d2188410104400f154005e050005c1030341c5084280b0f00d40040101c42d80060001400400002030420f400c4010078440c3c84403604a00d82501d0003002d0a08560b104000502103078003d1245c0407a02000da01088200f0000030700f21083d2103140400941502d80f040c3d0b01040341070b120000d001d40d980c000d000d1000500400c40d01011081c006a88070b50703032404405607140c10003550358404000d15020300c2c2d0302c441c100c0111165 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 68442826 1250 68441576 68441579
    0x140706030501090c05070803010519080f0102030105011101091101051c110703020106080d050a05030a0e1b010807030905060c070c0f030c140901050d06050402120307060501140f0102060c0a030213 86
    0x5030082009101d1003071601e0034410142c200c1c40c03044003105d400704d5008a55a04590801041c051124802040540040098600480d00420170006154010800703000980e0300d6040900040050040080300642c1d43c0c10114000c0001d000300a814881c07030380030700e0002c1e202d0303511001d10101440c441012515113850302e03400560b034501a400074407645000c0d800030f00003507544071152542e403070001d1310100c00600144568607165108400075074100320b81003800b00e81aa041c2c290b1794148204ca0640b6106a0710700f20f007000e529600580850b502540500b810010a8000e441c0c054803000000c003a9210500c0001d01030080181c03844d44000601400502c008599440b85845008402c0718020004c43d410300c042d5001d903e140400d1a6810f0b01c1c0081c004180c00442542c41d5000b42101402c00c0740c0c80844000c40001500040000c0c220300c0d03004201c08551549010000d41d44840340c00c5416010324001c1800c020540d03000140c01f038016100c400143d642c1c81c2d030354504030024010728440c1021000c100e40c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 68444076 1250 68442826 68442839
    0x10e040b04020a020f0d080f0a0f060b04080d030e01180f23060901050a0501060e0418080a0e0a0b040e070c0f0203060115020c2e020709090b01030c0e06030a020d1407 73
    0xd007900740d01049030407541c01c2605444281ea08001c11241c0c130462164290000e903008465070008ac41403483c0c00c0022415545884665400b500190400085a4401c0b82c60144032545800388000b4180200c0c002c1240740c0000c06880d0100c01c0300d2a0180610400b4650402000762140a0003112181d01c2083c4d49016462002d00da124141030350204810340c2004007181954440303106581c101e44058491126016081003480041c0615a0503080c1d00c0c603641d90010007141708000203102d80b030310b40c0c2d5403000c10350a210200058a00140c216840d9900d062000b4085c640e445e41e5112381000e01130428121510f941c2c0b6180c03120105c2d009000b50075000700700000541c0207966121651000d50784d001d40d008000002c007404021501501030650303608a03032424541034011101034410140d0b9501c10307101800c2d11540c04800f60740c0a002e0480300801030400400c00d200c2c0507207003d00600006980107456080110020380d440381551406442443d26030610030820880c3c8100500039141c900030b0b5005142e50f0392 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 68445326 1250 68444076 68444083
    0x30d0e12031306110601050f100203121005030f010203040c03170706090b040b0a1e051009180204050c0a0905041e05090703031b02060304080322080306130608030702010e040b04020a02 81
    0x89030a004c100007102d0700c40004004a2141d06a90000e00000b08600305482003111210300104444198041008800110080280311604c65001490010045450401030616015242100d03400c180d1042c4180000100180c0042c4201e03900900c801e06980805510300d00684110300300205054501010308040110b07515440e4441c81c01005491a075988682da0403007551034680d40702c010010000300c1805d03441c0d01684190340110f08105c0d03d800e80358440711044211100e10704604002521a00e2141c1117103800d001c2e4660100d8990369060401e4040036000d00700340c0d034600505100b1512007070001c00701c010f9101ca15070900900c00040c0464181030b00310584480c03150105030009034412150300040401184200321155024004620350713581c5071989000c0c2c0d0006080d01c60660740d000c514601c00c403240d10000c41d90500400c034543d23590514000300824070f10034000c0100c4d0941042000c011101010041c0d43c0e6007038080c02d00d02060f003500800500182200351140d42c2c4288081100f0746200d6000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 68446576 1250 68445326 68445329
    0x4060617061906081f0f0c12060b091c0809040906140603030309120d110a0f030501080106150f0c0c080a060e12091005120708160c02030d0e120313 65
    0xe03180c4410b07007801c0007040d0568400e030250760015440342c1800a110050300844860100d9100300020350000301e15040001e407404210090b0005606d0110024000003d101da1401000c520259900d410b4114002c00c4c40a284031031042c03201080c0900761410720130109e007240c5010b0402081042084800d00d030000061003001c006086038410b040004d001c2c5d040000850340103e0008008040da0109803501c92003d030f2101800024058841084400700d9080c40d000e456060070f03949406039052034a803030007011100140d00c80f039690381c180001040404004100900c1c042d9492801a0480b080c40000360742d02703800c00b44010403031046c4100000c0c00280110f2403006240c800d40c418040705101c08081c940d50880a640741c0d800354820010703075030b0078944525194004e51160804c541040c060b4099404005011110400803800010410401160400090502040c54284640050000c1c0c020035521440120030384c0c00d006141c9031082c0b1503903c48003002207240c118002c890355108000108615000345 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 68447826 1250 68446576 68446591
    0x916060906020d111b0303040503030c0c1f090312182402120f1b0f0d030b100210150909080a030b22020714030a0206011802040614030406061706 64
    0x22031012140451007400300d13135515036111004041d05070081002c80c44a100c114080c552600c01004005043e4405101810040003010040e159a4441d4001d0004440e1038414100c090400c07a2001c80c02d0344d8000c90418103580d040244803c10a80309041552640d4618407450710700004e480c00080c09850428080c4120542c0d2408403950000d490010b17a40c1d418801100624864107000f850740c0080c00c82e01074200305070501c0d620307080301c0c8600c2406413302c0340502c0900b07650b400082031103c5c41601030103107440d40385080d900d0820081c01488001e481d10712a810007043c081d220700d01d030141c07243c003c400b03040030f002810760402c41105a441c04040d10341c040200100401c0c2090444030b0311f49440341020b20042034030910b8000604150180e24003d6114000450b015507004030140d058850410182c607246c00540c00901e180e50404c030860080c0d8140c4448100d0030380c010030042c048107a2104d543d4400b07040180d4040c0e103c4d1124a0000058001c0b904040c42079203000b0355050061200003a160b002e1040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 68449076 1250 68447826 68447833
    0x90f04050d2a0204140c09150307020c010806030c1003050415060302010f0302030405010609020708030a06081911120d080106030e0c0d030c0c17100f060e0708091606090602 76
    0xc051000b518100040c40318a0001128440d11905030362102e29110ba849200074000a104501101031382c26440c81640c5840403468040b407004500c2c06c000000c0c1d2040050014481d08528060400030341e1003461080705410400d0007030118445840402480b82000c00051801c00b900d915030b00000c000342000c84068400f003110400e404018001e900c41d160036aa0103031360b4400c2000c104101540a0350001d001240d1030342d641e800014140181c2d10261008a12403000d140c3d070380c14051b401509845964000c0b8030300707070400040c2140c003500d80e003a003900c0b00b80e110003600e400340805270000303103d00300644030100b990080084c01003141e5031200d00715040e03c003551410802c00544000b0b40f039481000c0215941c0051424080713001180c02010541102846008180c0c200c94542a0151114840c940d034080154488003240c81d0104150003903501050654204100c41440c04550043d8444007400440a21294030041450311034248222250704910504180780d8650700c6a0040428545104143c018007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 68450326 1250 68449076 68449093
    0x19091e06050a0501060f110c0306150f01090e011404090206030c040e010803070206030106032a020c0a0608040209130f0b010f031101031b110304030209010e0a0e0607050a0e0f090f0405 81
    0x91148138103840042e5140708003c5005101a5030700b013a405502400781c460200d4004182e13404010f5103108401c04852202481e0313250782407140420040c1c2c1c2e00ca05112079207909001d4a94104c203107a0444140d407101c07411600c0d10034007044c0202010900a90002c50010401892421031402402101c203030f0100406030340c2e61501880d8582c020b4010080d0b01920402c01040081c0c403e8005029089407541403064031414041d008203013400703110700c201c05030300085250402441c1c0101104000c00050500540c1441c0c90750019116040080c051623485640c007245d00c1c00d100301e01400229240d0306c022803240300d58454684a10081c02c03840b080b41c9441c5c10024048003135100780518001104410310121689550010655085a443c03400581a100c00d210010159032562007040c024400a03c1000340c07402d10702e1511084c1ea00500c0407030702d642c1c094014070003282d0384141124070009031854400b5242280c0000600400d04001846521641c08000c0c00394180c0070001981c000d504c00e1088802c0031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 68451576 1250 68450326 68450341
    0x613091407020a0302060403030b0103060b031006020601060212040e091204120215090607020f060d090b0f0c2b0b061206130c09030b0a0204030501050108061008010b0919091e0605 79
    0x4210f02800200140c0001001c00c0009000b0740184071460014100480c032240c48101071181500119002c0d070350300950240c20444103030140443c0d0f0141c141c601c050444401c0d007100c00d2604d40302e03a118040c441482d220005a0344042880503940f5240d800f4011a55150341c0c9000300000a062081a4414011040c83c07030a50620301007110750035800502154202041502008038404810442070780000c010050480030050500c0785074130703151050b0400702260401084515a000004001000c452400c020030750325903015240d08050300c0001400c0c60341c10182142e060b0050202c00015036080700010410080450405424a12600c42074903902481e0401e0700010041c0c030120f400c1e003000310382803420030b0002c2140300101c5035002589041c054038040d0380342c3e44e180c04c48409034004c01091f0031400c1840060000e40b05c00740024141000240580302c2203500003044d03640060400007010800116801008506070490165290805400c0c4820401541c0c0e034200700c2c0c6480307000c644143c03070440080c411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 68452826 1250 68451576 68451583
    0xa0c0c0801090312020903010b030d031406090c040312020705030d0c290106032406020a0515010e01050904020d02100e011803050721050a05070e0f190209061309140702 74
    0x201d905552406101138000440310025404050034513010b540340c45588445803410002800000c1180c0d400088601010224a09468001d0500c5109000710300c01e02c40542d0440e402e681c1900c0d0001d900d20311544103042c0907441d0074120303401283c060082140c00f415080c1c0002d00906404d004070466441880401044468003180d800380300c161002c0240144003143c800d038400d00c03082a0506501e03600031314419904420000300c0d4480350043e880750a4400800400380311504050703ea2b6000b841c201d5060842c50010f01c001401039502039416500054103544e40e00c0114000700d03401500b503a190540511005040c3c1840400c1c2070b0104803e01c101d80381d040040c06032002125000740142c51800d0801c1a0720000828081201020000d1952200003050007400b1072001076220b030004140c82031800100c0d01035003500415203c0001680ca0810901144129070700d031800348440e0006980b10800d200084060041441220780c218901e0408200d0040d558014107001d8101c045510319545c5014040f0b94 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 68454076 1250 68452826 68452841
    0x60d14070f1e0b03090a0b0405030702030715020c010c0f06020705010b040e030c030d020703030e060703020304150603020f090603120c01060f0504050108030d11070f05030703030b011b08070602040b0a0c0c0801 92
    0x2031000b000d01040002c0a03d06001c1c1da00310b0900760a8030084541a120344112074801c3d0b80039a0150000100d400c114581041450020407800174651081074a40c90701940395082003460303505001b440f031030180030407450a07845203065900880443d182c20b005d060650007400202c035010b005529203401165502000029981c3d11200c80c00103500d02201110358002a400c000d80450515480d84409d0320592800e00220f807003106c09541c01038680c81c150510440d140d90104211541e81d241c400d080c4056124444500b8941000b81c8182c012500ca40700420314117555940d260085c03001c082104410381c02d06400140495241d000d243d25440c0c0c5407410801207903020312411415601c00c02c400f136a07080b102d800c01c404545041009a0401c1440d4031542c1600010f0b0108a80d2504002409010542c0511070381c0d502c200b003842c01041680c507014802d00c155403d110301804802001c030364402001050f40445005d03041034020075480b101c200c0c1c409491020002d60465406640c1100418140414030a068 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 68455326 1250 68454076 68454119
    0x903031a0901050a03060b06091203070303061202150a12020a170f0709061d060a0509090a090804060e120f030306010908030a02060c0d14010605030a0f02030f06040203060d14070f 79
    0xf07603005d14613a1464001d00045422a401070710038040c0508503644c1e24841100341c00600003550b0740b0002494010200c8920780c1000603e04c1c0c0401c0c4101c09620303648090710031000c41c1d6605599550340034a05644142d0803074003d10b912742c00000c00c060381984c0b12400d817001d00742c418154401521a03150041841400f00c40010001e000ca087c1085050b104000f01003100250700c200450714207a8901150459111f800b011010030000188950942030800800344d1113000194100b1440595135030b6000b851041c6d116070360400600c242240420360318541e581200041003421240f07030307405140c021500e0350000c0341c1541c04251040d40001d580800401258280c640e20740c054031403a0790f4410030180c0c0c1e8000e4080c03101440d070f0740c2c0c01e4619440e9804c4050ba01810740e03074503a43d44901c3c04074000c1c000d8405000c03600000d94014000c1c03241142064007219088081150096101e035101008100d02c5141d011016043c0100298808020311000c01c50005071403000e48030100c00360b20b0740031044000b09840581d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 68456576 1250 68455326 68455339
    0x70213060503010c032a1b0309060e030c030601030201030b040608060112170c0c012105070909060605070f060b060c0303010308090117010e06040c0e03070612050708010f1203020703060903031a090105 88
    0x4407078150140c046d030f062044803401c142101c01c681d0040348a04c0441440120045460002c05218003030300b00c0858040c00b5002c034001c0c00c2801c5e222020944480c01880b002307040c1600c99107105a295520341021005c1c1180c01c2c1240c0d03066940301e100d41d580480162041d60081c0071441c0600d800c0d10324004a40200b45990001c140c0078490000448030ba4103140d4800480032900088101d00c20490702a950081c000303955000101810484040120741c020782c000c0050000030080500018420300044003a1758122500142e0040d0b564041040b0b88600070303a10303081d40030000c000b0041000e22400307003042c000281d031409071025600011581c401300a000d44000c1c02a0000001e45500e041c2c0c01c4215500b025183c150344c41c40c3c00c0e20109240c0f41460f044100402d0804880c0300040e002d52081580c001024070385610654034040d407a4082e240b841c0200a14003032102c020206050003000444c0c01154071080170010a611030070003d006040c0000308003d01c070100c00c1e00822900d07050f64024141d40c0f0082c480b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 68457826 1250 68456576 68456621
    0x20f0720090103200a09090c080115060c0c0807030c0e010506040e0a05040201090305120409050a050c03040f08070803070512070201141305010b061201031205030108030405010f020102070213060503010c03 90
    0x148145101008448403011074000105491354031440e441c40014903c1603c00b1581e041d01c1d10780f43d03401d0b00040c0c101905980c50044400d9000b0690114681200c81d1030400603c01d81907418000a11034142e00050f0030f900c100075000007000180d2509501302e5140400d203140590f02d82d020020a403040b0311074143d003410300070301046942e0300780e40c00346411501c14100104016900c3d83e032542072100c0c0c24651480b0100c0414100083c0c01e05000b455405405808108600d2030642440364060102520140200c1000f945050400003c4c008440d200e90304400e00035103034030f80664010681d03449003c204009502f49808200e01d24014043e02d64001e038901680d03c210798a20600104210781d0a100b03440c10340d2100340140031621074000410a1a00707000001d00340d5815400d1042400b6500041c5070b0400004100400c2142c0010003540c0940c0c1091a155907600c0a01100f24068024070b040a0340c0203241845c580c00004040d4004011110b0a0b8000c1c440280080d80607400ca0f80e07800124080168803c12 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 68459076 1250 68457826 68457833
    0xa08010504240f081209090f060d0b0901051603150303030513060509031b0706080105090711060a090203060c040605090d0317040b101212180801020f0720090103 71
    0x30600600a402803800a06801e24803401d58594581c09890103083c0444207006422060042a49a00b000c20510740b5100c0c0303140104408840041800158042c01c40208005507a03c001740540e250308100140403504150b0911802800d094501c15010f145a086051205002e0f00916102100c6441220040c4d45981c4056000c0e003001043d40d586c400000661000241c024450140101c1d1004010f545515040c0c481144c214a9096411602d0307001c90005c00c10268003840d11815141c00b0303126155a5103074440c00340e8040307545409030f0105015110070442503000b1680304001c880e008408403501c41d07c1c1d07a80141180d1040d801040d000640070031400503c1d0404085040d010751007490500c0c404401d41062854503141a18200da41d4031804042c0610404483d4070780c00680f0041c04a202d0b030707005a40d91500a0001070075050300740044030100d9200b092080c11284000e03c00b01c0c000795500e8408420b40c0c152030744108400c8502c16013113440700107509826804280d0800010f8800301c820303401c40c1c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 68460326 1250 68459076 68459081
    0x2060f0420130204080109110303030606030106050702010912050c01020127020d1a01030c09060803040612151a0d1a0102070315110414090a0902060a0e06070203070f0501140a08010504 81
    0x201c58035000702120015030402d81e2144014001060307140c0000070000824508081c411070340038540c0744aa0701c18004e204990340c5a10072a81120103e041c007658414491005a0380c400300d075480040070b554042081400e0120105244503204003d034000c11941400303801080744000f01909000c02c8840d120750010050030000c55150f84a030013000c1c44022a41d03c280c00c83c0465509130011100c1c4036101070100260505400f07458007030007009000e542814205000184034442202981b01116121200420a5a11200ba41c8081c3c1801036000740000916540790106600401c3c3c040c4200349000b030b0040b00d110003201a00e210303c0d016400f500300d481c915180d1003c401c40342041039a00300da440d9080b4100502c02001400100301014096482150050402001500c0140380b280c80c5400d0845840040c2e881408498500a140c21b0109900d07a9100c040781440c018400020b4052003611070125a4a26a20700502240ca00343c2e10450407a01c0400140d03070501440c4680d2000c0f81030640148403e18103034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 68461576 1250 68460326 68460383
    0xf07120501030c0b160c24020102040509060609060d0f05060f04050615031f060c0c06050a0804020907020c0301050f10080313090c27031b030b0a0e031b0105010602060f04 75
    0x80c0b201401d1901c203891b45062090141e20800305070794103600000440c06014080d8803d0701581c0002c504042c50038000c40c4401c00c00030300e55440780c4070000e64a1101d80c4c8040548210380803a1030304104880c805000d10303004040a42e8958416a03c012025131240341c1030041902c111b41c09080031410340d09054030704c802a0400b03042050690010300da0100d00746061034000b0010103484e074448800c0d61841c02c100107840b0864102d01c040000c200b0000c9440c54010302d5684c0c10a41c1501e00c5085031f40c407500102e04015882c40340aa155080c01c06003c0440c4111040034000d0207805c00c4120040e9445d8017807540c903c5101084040742d03600d00000c2044140301d0b80300c0b002d0385009042070107441c51041161b13011070302d412614030006441c1120905c1031007141c0700400508071340181603180160440d100d050a038540144a802410341351038096400350000e00070342e8030401c04205202e40d000007510b110b501806003406000c0040c81f4080014041a0182041e50700481d00110a2900804100071194654042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 68462826 1250 68461576 68461597
    0x50d02070f0f080406030609050106020606212b0c120302090301180303020a0e06040b09060903010204030b01030c0303020c03010c0e0409021908010b15040303080105090714030f07120501030c0b 85
    0xc807044404038404030a0203503800d10410490740d40301c1c20424050129000f5801501400e440c040c01841200c0c4c0000d441d40e0044002c640b5051007202e003031110301c80c9441e01040100540601c5030007000700420034100520740a483d540081527501200300031140071300c2e142c00c0904015a840c1c0c1c1104480e00950080c00306002c042d002140740d2002d0200181240380400040300003030790014070382c1c5105510011007100410b0842d1040c0c0b81503d4142c2c0511580200740d1032512445d000141c10885640941c100c60042d9440350b03440401d580d59040440c9064400d10081d0094007070613a080b11f29140612610540c482e03036846421081e41003005010042c200b01e07070200e80140e240c00300000660749003040c90300104103400010440c11264000d21012080c1082e80200d1000180b006000081d0461000380c199039042d070790b41450f56614441207540c0c00d4640390040030410300106000c600030110744001e02c900c0107520f6a01d10540c0a11024040b14000d03c0081d01069016209001e01c5040800502c007203001c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 68464076 1250 68462826 68462843
    0xa02091003020d030e090a06030804060f051308030909070e090103140118120207050612010614041802040e010e060d0803091515030c0303040602190204020c16030b0c0703050d0207 79
    0x84075800f0500780721580b80150702107030b0803ca441d149460180551030784600e528400740802440c558501c0c0f2309020328065002402103079103040800078070440c1074400030200d030754017020844e542c0d80180341c50390701544d15107000e52040c00004004901481c4000c07003c0001910602c1107a20b075450343c041480010391009555522019170081040901010340c030100d000e40c041c102e40040c4080081d25003031059100720300a042c1440350311512885c2c41e007003504490003401c04002510f46541000b206108540064401d01c0c10003804000d500300660140099908138101504180d8980c0c030481c10005044850b150300c801d40c03140080c0010350030806503800001500460704852040300b288003560004468045106044450f2040c1520b41044040c095000907000b8502e0701d8241040207494070042e41a20300c0d4129580001e5085450300c1e0304450034a02404141d03204200641e0f405241035005100035100c0c1c0d248000460080c090100c00c5800f02c0798162a4145049a0031085401039003042400707642800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 68465326 1250 68464076 68464079
    0x50301051e06042d0e0105150906090703060f030b04061401081902040605060403062a02030d0e1903110c01030209031f150f0306050f04020a0311150406050706060503030c0a020910 79
    0x14201d91004c4802915820041602103400c8070700390858500408000410b0160b401d00e56050700c0700060f480e00401c2c01d80700050300c2c0d6a209015405040154000c0300381c90a661030000900c4405070010b0700444c0301b644140400400c4000c1d280c0c0840080c09804140d40041006444d0883c911416402c1c962000e0004600e480c0c2c0d90000413441e400550003038030000c0d01c030101020180d8104485561100c601118400302260f040c00082d6240942154520601c0d903404807100c181e94200f000c1c1c20070819850070350500012616009080c440948034240b690300c00c0b00d0890714158040d0003540c88100c0064014500c400c0d000041000841c0481c2e40c062005503503010903410048800091030240480c41c17602e6a03002e02d140340c08000c60703000404041c000060714040c0b00060752030242c9081140c3d040768001c60b5803450400000c4918400c1c0e010b80080c0c41e000140012210b42010240100c2805218100034599807842499128031460341580d81e03079040395510800500c0c00d102002e4200310751041f4450481d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 68466576 1250 68465326 68465381
    0x80610090207150e0a020a05060a0509060d061503090203010e060f270a060e0d0507020604060c020f10021608010608060105090c07060203090307020913020102070509090109020a0f050301051e0604 86
    0x1034401c91004d00003074100f05118015030900c0c8a16034010300058030860301c0c212030404010300600401d11031a00c42c1c240001c04408142c0107400000183c200394082000c0b011000e0406001003110020890083d400d00000000041b004a10300d8071540d4908040c0400307551303e4440c4c920f100d440000744134640403486100e4840b03142c10407100c4d0189210301000100c50840c0b20250f460103c03021401002c00004010050046e110070702902c0840b0010b0501c001e900a0620000e406140c00d05081500103048002d602c036110f90015208005104504c003904030751741c69140c9182138035141e0141209550010340100540e040c08020f45601120304400c00741008c0071940c81a040e64026614601991306c00b00e2003000b5840c19482c0d054008801e40600c0c1c40c001c03000d0b030011b13484507107601c00c95128259100024001030829080345200507801031083c45070341d07201d8012200803c200c2c02454040d48c80d0800140c0540c40300c07203150410035403091b4420565a600c0e01040090a60b4280e4005442000903d0801740c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 68467826 1250 68466576 68466581
    0xa0e07080c16050312040302060619140f040e060106030b0409020f090601020c0307170c060408100506010509031915090c03151b050a11010507050702010518060c0607030608061009020715 82
    0x38030345d5246071130218101405d00130b140c85409084a480383e50102c44620b10800300030f040d081100c00350070440c61140310400c00500c4000700e02485540090405940300b209800100341760307060f144961000c10840000c5014041129440c441c000e40081008121140b245000d40585601150504c1101e100b000810042428541d29a1142c481da002c4105401051501403001c2c0700007480940c1c90504191a09150550311921511001c003c156104007148003079114108983c0315180140854401003103d01c2d02007070f030120f140d0040d140ca203640c0b0000141d20007107001740808260007a0001c50194196100d42074540316109003200c60307039500c90f0107901c0b2901075005401411800d0302c0e1151900301d10f8074050a002c482100300d2855903d0702e02081501904075003940e2840780c080c603209880d1000c0541e0707145944082800e0903800b202c04a8410f14007840007c405125142c0c0756024060b481c1d69041140e520030f0705a488640201d0942c009221040491340a015858040c84640c61507400f07a02030f5108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 68469076 1250 68467826 68467837
    0x20d0c050712050f0a111023131a090f07090516020601060203180a0504020706090c0b040b0a03050403020309090c0a030606080615090d05060c04050a0e07080c160503 73
    0x1040380481d501d002d0001c000d0490341d281e210360a180e0703d400034000f203030b00e09031007801400001d00600004181003d0410005a0384000d400304040210800c407800102003083d10215209241144100084403680b000719401c0e80310f41d0060742d0710059401d4000300c240e100d9004024000a101701d10724901045801c00900f4000c114500d0006998280701c85006012664800c1d00e20655104100400805a0001c11551110f8034460b0058a505042d8000740c50307402c6a601050384640041035600a00105500030107880344603c07c070304401540c519807811140500e101d4000d40d000c0901564441034000e801c0746e940640700c2d1054915010440c000035183d1042607414051982c00031417030184064040c401d48000c3c20050925031014602000025664007807408804c5140d0b101140c3c0000380d4840105400c021513003c01a50000d181c2030880c0550340d080b0348a21480340141c6180091592100408640110300c5961991280e90390100c4032642076000f800000303c01540712448a0210340140003815 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 68470326 1250 68469076 68469101
    0x41509060f0b0f090610020c03060f0105010206090a030504030605190912030f022706071202010f0b040b0f0405040c050a03061d010b0310050a020f0c0f0601060e0112050406020d 78
    0x180700d0032207941d0701045440000149001e000f40f00c4030300d1a2541c4603c1c10b29808070086030103030f04000718a0b204904082c049808540c1612600c0c040c49815a000580e040c180c0302c00380d00320fa2a5603190081640d50b003000003000f1303002c91810001807010942130b41095a101ca01e10681d0040150750303400744070842ea2503d6054400315550240100c0b1030340e160091000043c1c20120550501c00c0d1140340da900e01071f01c03896604050710850707031480c075586642c0150358140760048080da152450300380001c3c8c0030b44540d201d5401240c1c034211402030a883c140c0b0644001001c054400c0c0f84501d03858081c0070003000d0191040d564921510400503080e80c418080c1400383d071080802142042940f2034400c0c0340c2c484800c0f00c001a03410966109150f88000548114101da841c402241d10344a01d0b0301c0d82c0c001d00c111880c4003081c0000240c41986450000340608034990f1400031100d150707a1b40e0b04102c0d01a40c00c1c0f80864005000441181c04440341500055007040c040c40d80103180c200c032415000110f44400340c1d80c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 68471576 1250 68470326 68470331
    0x60e06250309170d060603060f090f0b090f011a040605040608040f080c030405011101200a030605090403050a11060603100c030209030a0f020a120201050d0e0f0601030c080c042304150906 82
    0x1181c40f016903000c5c40000f00103500b01031240c203082c680d549005656034003824104c1d5646a0712441042c2140c1c001080400c8082d003130b507000303040c81c15418042c03510034042c41989a42c030582e01d6130203030803500845d001c403681d40d92410308003814840c1c1100c075850b01800c161030a038510440800800d0000c801040000d1040d0000c42c1c0e42c510b010000351260641140c088400c2e4542a840e50100614004020081e440140c1c800d54400258500f5001802c0b02d40185800c80002000c000c20540c0050040940130169101c0300d0412104100040e43c90008071407043c0c01d9040101c442104025a030082014140c0600b005404d00c200900030034641102c90f1002c0e12000ba084241d10305504002d22400701a1400d41d0001104541c243c0010f0070600ca4515030211496481e0301c0cc03581c0d810b080c00f10300d07054000344c003e403030055a4030f0404d00300d0340e90240282c0c102030160034180c80b0b40389082d120700950000b9039581101c00b22440305002005000060040d1a45484901c015506510714400c4004c41d61080000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 68472826 1250 68471576 68471587
    0x10203090d09080a061d03070b15040e1509032107030c080f04020d0c03080304030e0a060e09130c080a03090306060501210e030c010c0804060e0625030917 68
    0x1514075100c401c0c190380040c08000402400040d1021408081c90f6421500c0481d28000f6001b46000ca512942c054080c14080450042c003000b01d0304031018000d546002040078042c0c20242040120794441c25040c10b039a0050b45401480b95140c0c80e1240c0c4107168005072400c160741041e41c1d6104080340c4031902d0f12040b00314204051550144290001120203203030002283c9040850001e0f00c0c4c41c082d001a2203034490b18130305403c201c0b030001d125003c2e5907c09030407170312403e1520703014040c00d500c81c080501c22805020045407040c03080900f051505001005403c0c03030748a421241d400b00141d42c0d01902c11a46140c0045402c81c0200104400e581c8250345101c50a861070400000b120301c4c0f50005410046034010549088101980318500c0d02e010000004203003040b40301803881c42c82070b03101e400391035400c0c00245c10f60f098000d10498803d5009a01c00c2c451012010640c5484540c00c8840c0d5000b0642c0003d1b811094640c0c403504044282039044c0002c041400b52508a904d80d581c0e0800845c00c0400a007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 68474076 1250 68472826 68472841
    0x1080706030c020d03050606160f02043c0b030f0d11010203010b03040330021201050603010e04140f06190e06060303090d0606030b0c070b0106020a0c0311011709010203 74
    0x8800905103840d041007286102c0078000c3d1925a03041c9184201500c840100d41036641e454100d0b003030141c45040e170b030f40c110040b403500131080702140d80c1c1031b8800c900c2c11072a0603a00310702150941d006941d000030f07544814590419425501c007107003222050942e540c06802c81a071020001c0c40c8020190400400a454191a00400b00017400b92003890907401400100040c02070320050325041039040c20403044415044c00960038018611180f4446a03d0784803400081121136801842c000f20321080c05011a038030ba00038403045100c2072155280301181d480c00980483c0031101c003a002008030800b43c41d1035102d005407480c600b180544010000701c210108595100c400362049030520591403018280e81d140600002e80c49000b50441180902d540c2507041c402c1002030b0380002c010310345c031207154081c5040c5114005855044040b00301c1700001784000100d41c3e9400002d214000690055201c0540c2d82103907650001130407490100360500040f04440209038001c40c3d00d41d40f03c0d2070b5007400140c40e440c0002 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 68475326 1250 68474076 68474083
    0x213020a0c0b01120210020712030c1a0f0106030b030303190e1002040b03071707120c030b060d14010602060c03150d061e050105010e06030109020919030308060907031b0c020103021309050108 84
    0x1046d0206543c82400d0400c2100b0540d0440031242da01810130b4810603004c1e041940012010052428103510740200b0000038030b88002109069410aa4007000f204a86000341544c0348000c0e0b890b6110044000c0d080207146429030011900d11547c1e40a64000c01c00d14558002a41c0168000410303e810220800c1900c65111000900e0303c048640c4035401f60808101c06410842e031852041903854031030341241e0149000b03410103100c41002030300e50703540d540300300032400001c041404001c200b040001d000020b03554400122580907030200040c40f4a140c680c00325030480000300c070300c2164001c4010445c1c42c2c00710340c09100e0701d00000d1039039942540001e0690300b110104c62050b00451305001d8107068a071500c2e280c0e10290bd041da400c0c420012f035149030b10000100320000801a500c12a1091100030003003540c4441514017440c0283c4a0a455444900c0e0585c213035100c8004222044883c840100d001511568003111241d0042c18014078000200f5100d0035600902e8000600f01600e90300100710380201007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 68476576 1250 68475326 68475349
    0x301060e0a050121020d030f02011503080c07060206010b0409150506030403080a0606050c0a0602071e05030c19030c03231803120c0303012d06110d03090213020a0c0b011202 76
    0x22030b035080300419282e00180070040700c01800b60402c2042c4448e00304e070354000d60000000740501c1c1c54654030310b50389141640c8540d000d003050303401501510400052060001400c20706a5000140d80b6041900303101c0810000c21119070031240081101d000010603031201d00041d0b000d1130003590341c81d001d460494408401d50f500f65010004010081040d0f044450002c5520800a54444009079440f2641d007031240c4040d104940e11206240c0300032494003002070010040c01001102c6056400044c1440f0f001d912007010004040d0201360880200c4000134403480c00284e001d44110344101000031010900c0034150408180440c4d0520703080020200b0b854104078260000888509203481d1030380c3d1025541d141e000610442c5141610390181030200007802685032608a01c02706045079440c1c0d1840020801e0002038802c0d141c0c0d0080d400043d40c03051107805107401e21034001d05801a04100d01104000031350100c02003408201080f00190001860468154003c081c00290141107000350300400045070400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 68477826 1250 68476576 68476619
    0x306080c09060609040e01020f0a0302071202070501050d0f0216030203041716030f020607060c0903020405090607080411061c05011427131b03050d0203130e060301060e0a0501 77
    0x107030800c80c190340d0b4841103401d154003e90340402e8659561440f60f000e0b000305140d0100040c030100d50795984640c180d02810f9228042e00041c0c002000b2240182d0315041c4a000d0940000c800308544000071500d6080407841c0b000104c0010b2501c9501000305e80c448880b1032007140103810004040088800c480c0c081d400030340c800000b40c911481c1c140c800c12008901440028031418103020590150340d5050305565005030040300501098002d040010142c40040c00124480c5182802051082c0800030f1114400e40c602d48420b03100e0340707a0b5200ca80104114942e02a84000e040003201020303001d0040e0140c540e510740001040035410720106828000c84480d140b03003e00e9800d84080f511000001000c6207504280008081c10b0303c1d0010b051080d441280c0f0098848030503190045a0200701240c500112401982541c09210385000200d80328031489a04031202103000205015400c4040c2105820031002000040c0310b9503070310a140e5286000306c0310340d804240d6620041003150514880040044907 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 68479076 1250 68477826 68477839
    0x70302150f030112030306260706050c06070305150d06090b01080a0804090207050a0614040b010b091305090a0506090609010506010504030f03030c0c060203010b090312040609030b040c150306080c 86
    0x60781825980103000500c180d00705000c8580381c007418103000c0d070311580140200c0e02c0035008000141b00140c64042c2c1003180503e441c410544002a980d20400075640b40900031800307841c203525038000440c042c0038060700822000340b41d607441040ca50b07239020400100030701c6181c010a40d0074030790822a8050340e05901141c1c031a04038007100780000b8480f0b0100c0d01590000380c80140c0310303089410702924006135410000c001c03a151990142423055038107081c5200382d00c41c0365850700980e01c0f002191142c1c082d00301e40c1500405182d203100c0d2220b4503034104944c000c2c071010894200d0744007074496a25020381624803130081d420002c1800409e0f002809207a92000782800c02c0d528280c83c3d5038503801c884913162400303820180d4a00100900c0c910680c1c89062080d0441d5040d916561503050005a540c40300100c1c40c4607115508800d90106a68015642216196200d80400c28a075031107940701140c8c01003045554a0500d140411000c00d2200b20610550995034001070090506140034900300c207881800f44101c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 68480326 1250 68479076 68479087
    0x106120308060f0a0b070809060a120b041406060c0a06051005010f0f080106030209010c060905030c01060f03020607021c0f1101110105092e021c0b120a0f02060405100207030215 78
    0x8490000740c40171507040d042c41079610710541c285a0418000d1080043d40054002450346401c0d071700c058494441070290f0b108002600c80d00f0304210880304d6138506100d10114000c00519246404405004201074071010744901c91110b95410040710400c40740106200308001c014800b03560b21000c0e40198612500740b284a0403c4200050080c0c041441214101900003941d012136911900e088031005500510500c07451500380703481600c0750040307804540c081d843e04000107a500c8440300340404880d005880113140440130b03000e0011214607940844070348000241400c1c0050032041e2407000c21400340d0101c0740d40c000c48000050400c4102c410040d860ba051500303001400501040d4030345540c484924652011a01e228070b68800880c441c41a2a120710106d0800c0780400103034022201c3d904404020005088640104241003800c048410791580c4000703800e80005c0c0e040305040d1172a6000500702c60519580c0c50024010641e070040d03420041e00210410811401c08020540c04480780d021510300b0003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 68481576 1250 68480326 68480329
    0x12020304120605180609060a0b010e0f04090602040e10030b0601140a0f230903060105012307021807030209040e19021309080a0903050c03030f091207080106120308060f 74
    0x803a00750001800403540d034004180c2040940c450001844180c02c142c56461500c8043e45403141411105025601d0a280003101251b11483c25a001c41c6801000d40010006d0902400018040064219030040d4200404100c001e10340141910954940188174100d07030440c9041c05407410050207490600180700c11002503614094180c903445070052900c0c28071040310a104441445060103c01c40c440906881c80c0041c01628000b419081c4d0244c0031105142d0303a230300044695010b42500d0503d00d0246105c601c0342e0240030341c020010340740028175044400681c201d841160070805d0320000e001c25070000e000341c02ea0500c0d005503a1640c911030060310b0300044040d40e1a0508250480c024400c0c0c902c4110035110030f0003035100c510000d42125055450351000d01016000d81403e000583c0e485c031500303211280d01c1c03400000712aa00c0500060300e5040c26589814010058400844464140240100481d038800c00340f02e9803004100e00c15000302100781604014190306d0000e800503004032141421444107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 68482826 1250 68481576 68481599
    0xe031b0d0309020a03060c0c12090501020f07060f1107050a0b0307020606010905100c051929070e0f010c0203010509011e0b030a02011407050105071709030c34030c0312020304 77
    0x1140d0300150b001c1f4081c50100390440b80300751126001080e4520a640c000105940011981d0940e00280c003100e14465102c2420380da612003500c41c505c00940da0703500508190f0f1151180c001d83c41404000c65240f2600c541c00500704107a95002140c08110201c108090103a0420105801c810300303081003a011410070303012440409444038600d0038441e01c502e1401c20042d08100381c3d0101d140c941c1c0101c440c0041840e2030244c101c4c050200980c08455001e8100b002c0302c203d2506806a00c40b911030a0407600310360188074100815000d0641808041e49181025031020300510b40f1419a80d0000104034104e140000c2049a240901030026458480064926240000d02c00500340d02420585410603e460300000c084c422440001c0c01542081d052041c0e46420881c2444074100901000c075095a80020b05556401049802d040c1c0364404440001c1a0801c50100c0d07072003410144000c6001e11840c0074001d03c0203400d90041b128100168410001d0014009020782c00c1521840598942460140c1c0380b8034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 68484076 1250 68482826 68482829
    0x206160810030605090a170703031410032402280306030b010b0d0204031a0609060108062809020a0c02040f02040608010605030603030d0603050606010305090706090303050705010e031b0d0309020a 86
    0x1c3c2036484022910b42c41d401c2040002c01c40d40041e10314126403c203e482c0a050308211000c80c003103814220005405581c81c21854454505441c201155511310380328840e01c0010111702d0314007190615501200406a40000c1c408a5913403402d207804929103c500d181c088a0788541c810406290000920024481003403c9044482c1b6000c0941c4403045508004001c0c03089500081083d020303041e6040b1000f290080d194483c407021140d001507135941c100150340a1500f1502585c1c0131540003c5181c1000d00100440340c58000d0310080140503071240c080c28201d03402843d00d070010030314408800045140602039003a00c0406034000758106450070501410012041c010b407010721101100013401500c0410580340035041c50314041c00f40c42d640381046a01c64038160303640b41c0040d013040300081000c0c200192507400c4840d20741d01c02440074079649080fa80d40e040f02038212425500d504228141510801c060140c540000000034107400074440e56920f4040c41244540502d82840741070400750355000c45000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 68485326 1250 68484076 68484083
    0xc01050c15060301020408160807090b090406180221070909050c06030703110307120e060105130b0103060f0f0608070f020d11010e01050718050a0b0904091b0303020616081003 77
    0x50036500c030b02c40020301900864002c19894494110f000d5036042602180c1c000301c402d0742080e5000140c50b0408070041d00c0c400710b0f4080c1c111503600046030014601d58081030001c1d41070b0b020340c2e40c80031039903000030101101c9100141c69505003400201e010b5900b44100c1c401040785a07010861801d81c5c0d524561241c43c1013001c24801c4c000030002402c0ea43c0646c005658200c0820004c81d502d1034080c0d005015030307140c013070243c0c4410301d80303802d21100f50000600503058400040250b81d181d0382041500010f0014a041c00e8101900c40e0030016110022184400203018058624510a41030030402044014001c2881c010000082c140011756500810151a401700500d03000c0003904030034100d64003400408000400301d42c80c120410107080c1d800815202c10600030360130542034955400030043c0e82d03101c6000e1700d40100b60800081b08039240603482040454803034003150784031740284200c100c26809030354000d8015800900400c0003415284586200b84402c03802d02c840c0d6414102e01141030002c5131701009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 68486576 1250 68485326 68485363
    0x60117070306050406050f0612120a0c06060305011a0303030403090515040b0307020f10060515030603010608030d1b0c03080402040e120a02010204030c120308130602041701020702030c01050c 84
    0x1152204424840c0c03602a6030001001d0095041c603142403c000c0208680360f034a006200d82c0172544616112024000120b00b510081024908150a41070700741e002100c1c11040c00f01800c040c00c001103090003000001e500071400000c40a1076128402d0303076071122b6003070144030344c00403c10080000e0b0058891030941d40c003980c00c804441d007038040d02c12840c421500101c29402001c000c01001030703170001b80d0038800320b840030594520300c2100e0341c868241c80303150180d264409102c440041500100c0320146030f00880c028004903030540e0702c500340d13400e590110303040254694030340c203461004100c02244034440d10460300d020030001442e900c0040a003803001d00002c0c81143c9a219101c0304807030800082c2801c114414850740d403200e034804080d000390303c988811070302c02c3c20281c00020040456000140296015110b074000c664074468030200c1c007400c90300c049580b180d090101048515000a0645120707150304001aa900c2443c01014544201060620b0400c541040703420303800d21001ca0031031100560b05024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 68487826 1250 68486576 68486609
    0x506060f070206071e05070b0f0f03060a03060603030207090e07050906010503100e0c0d0509010606230f0301030b01030203100621030905030f1f02090102030412110a0b0903011107050601 82
    0x180080c42400c1d8007a250000c00c0440341081100020070300e803003e01c80d40485011f296100e030344400c00d000d186554002d03100c040c00503404581c4004000c0d58001c0c00281034039041504e90f6105001c4600b070340c01c00c2d00140c1c0101c03824400341d20f191003081071f44841c03a8020800c0ba49420006150300b500145031604205022003c500d00f80d526003030080151000312045020740c503003140c20003640e0300312a503140e01c0340b8280f1020900448043c40b0f03e806540c0d46680750b901040e480c000a012941c0c41200036003101104100115500103404051406036102d128048005e5240d801018942800000c400340c4c0185408820800e4000d4900c0598900100d081c801d02c61211074181594140307002c3d0b02c01034050290b8080030800a8000c52848801312028520720b070300191a602c0c040480c0078440034540581d01c1000180803014181061944c4207105681580010a04d4004920515610b6108180c1408081003c240c507160a005482d076003070302004c3c10f0b41002c0413130b00e0709655524180300b0360701c003544503518 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 68489076 1250 68487826 68487829
    0x23010c020d020904060b03010b0105040e0403050703050c03030a060f05010201020307090e09010204030209090a03032703080414100f05090a0218180f0606040c0f172d1005040506060f0702 82
    0x40d034a075540d4000307003007901515107418408058103a82d00c0700b61180d460144951074540c081d400b540c080e0b94a20001207030a540e00d03a4190350030351180e0016000c0c4501413003041403202e1f04200552086c500030300045055840c01c984521481c5161700a2030659005000b0080140c2c1c0c80000c04040742d1910300003000940340d07446454024401c42c0c0000e9000302541d020091245d000051040b000341c800da400f00211a4002994480d03c54001d107503000c02d460b00315445001c00e1040110640050142d20044d01c40c4008510661900104200e00003441e500d0b14401c00085141d485140c0c1e0049010016000b44d08840d030004548615080089490410b144042507028120300b0760b8018004126040300c09201d4131f10b581541d01d090465084c1e101c0c608042c1c0100c01144074503400e89560b0300340d450360044903901001c0d0100c450f20042c1a003007117807500b804000800340e034524521664455180a4000c0d81050794031420540341d181c020714006c2e400d000902000343c030344404980c8224080c05a9a84480d520320 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 68490326 1250 68489076 68489089
    0x602030d15090606051308120403030c1b081c1107050607060209100c15020a12050a0b10051804020301050132030109020301061b0804150c051c020723010c02 69
    0x104540b40b2030f89829030100d0055086001408043c2d103c3c0e019142441c0c0d0ba04200e60303110a05e10140142c52018041040002c4c080c01488140522481d41c40320240f04001401010340040c2e80200c1d02640245840c132424030140e401100c8000462030110100b000e05c1c1026a0382c2c05440c480c50b03020340d42c00108542801050303419034490f00c07401066014042e0340481e00038060b540d8050705503260342036042e4520020100b0b00c01c81b02c4580e07031502d481056000002c018401080300611035220701d0b8944480c1c16059980084028410407a03403a810b80341c0f0300080001d4400c601d844c51481c02284100018082613070001100c5132030b0720f01d0b462109015040c0180b0700340c81c00300710444031403803003001720021030006440d4004d14145c500d075582c4d03000c04803140c500008184003000c801400c640000c100905c80501c2c405000e4402101e1424140145212076464a14103c41d1000000c12451140f00c805015941400b0408c000e20040c07a01180c6084c00c024a03511110b00110b8a03418030a40741c1011085440e8807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 68491576 1250 68490326 68490329
    0xf15060714070b1b15010905060d050a060213080a08221a0d050a02030402010c15020f13050907050c100507140a08070206100803030c0c0a0507091b090602030d15 71
    0x32420b81d25003503a10f00311403c0300c1e0800f401c42d800000740c010668100c1200010031901c108014a001d20242c0d190509002c020710015000541090a49129901250f0200080301c10580301d041e0060341c8021103c402c5580d200c031030b00003240540040c1d0403071005c214242c003a12555081807281c04d0600401c00c2c0c405c166603105a020303800f5085c0ca17015003030841e0024000350805c210340c603005120a9442c0d8000500700d1000306c82c003c0c01300301c5a44040300841c404030982042c10608480042c58103411441c101c0071600040200c070614504031006000604025072059040f44940c00c3c203e0412284d1301055442d0805510701075045d568400000e55051b10034044440c03c2c01a540c2010307079502e1407203802000d01d00c00312425405486400d01041c0c0f407044e50030143c001c8800c0c01e0040c50654840007040580c41d40090b101d00107505c84c83c0034040204106204a4000380200c20000812950301c24408040d42c4107850340c00b06200d81c83d10704114a070b802204903446002c2d030350300008070720644540401d040c580c076 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 68492826 1250 68491576 68491613
    0x414030106050312070c0603060501021e01020c150108011103090d05130f030318060503090d030506030109080408100606050306010807081008030a0504060311090a180f020a170f150607 81
    0x40344d02c4050000014401070152034003a044803164152100b1060b008c0d00c40912416005a0014a0310802c2c485842e001c3c010f882d003204009032804a5070001d05140001c00d24400c800740c8003040041019020074402c10081d0f0300c00092440c1076150500d02c05480703044116420301481301c0000c0308550b8084211420000e485613503ca56125516801c009001c01143c0e1040c01060b41513403c085400c0b8000c900b80c0748074441407402801c0c4442c2c800b030220040d0030060081c9400d0764a1300000310008031018003420241c401000103041028040e21014140c5100e0b500c0030050107000c100340003413641c0c0b1241140e4480d005040100301c0d600c805140b0481c4203101c0d400756445001c0804d1405480d684640280200c2d5040d6605110583d40000303c4003e5100b0754a400f0740c80154403504102d0300446056a25120218100008a07003100107100c1d4145c3e48514940e000261100c04000c3d00b0807606503c558001c1010101e0001a140100e0304074801444010134910441011450b00200101c0c0042c40240020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 68494076 1250 68492826 68492833
    0x6040303051b060f061305060906041109090406020901080109091e050a050a050c1206012d080f0a02012c01051621020c09040302060708070302040b130302091003030504140301060503 80
    0x421071302501d102030301900c015118014030124500307504080c0c01458002c8000034a00380a81d15038ad01000010100071a07100f0340b240d070620009000d5510003c0280c0704d18010035015a0312160f98000408088058011400441c40c20210501180205c2d0030a0898a0b006024882820b000e040c601c0c9446605e4100600c0ba00c00d04151504111004c00c0e080c40c00c55042d00c0986001a0307465485840305000d01410b080c0441c0080c900b452400744240e029001c0007041590b1240c2510340c030046042505500032280346520141a1608550788080030f000580c008801d80c0b40040502c41d03c0b0000701346000c4000381040000b1480a0380070700038103500780d03103140d1012020340c4488205500303c0119110704903140160162064541c10f42c1094440030f03104d2075155000e40503542c1c40380400e80c0c1d4083c000d000e02d4101a0300340130104207072241c10010400b0150212203102124a035104001a40c071b00204409028000c00e001000000d40207010395050b590000c20082142240c035001c40d00425035603000550510 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 68495326 1250 68494076 68494081
    0x4120305070611180306010602030a0219020d020d0302061509010b09010c030504050618040e0f07060c08040e070e040e0111040308030a0207020a03140105060103020a081617090c010e030106030206040303051b06 92
    0x2540340f0040130380c1c0074080c0d05a611503a0b0750303041681c50b070085054400c0503800c444600304841288500a52400c2c0c4010062407404106401180081e0750324007048000d80e1000c820b002032542c01d200c00340d0241a00300c480140700d60500c03c140e0090301459455605008040001c1d00415000e00240e078090280a400c890715051309004c44030728040c1441029004600d0f060503010b40000c00f2070b0492401108100034000c2d1450404100c031000d040b010160b074420420310020990682c030a103818003801c1190b032240c490003500d108010813100700906009aa0780f4ac102e25025410109040c0c4007200d03045424683c80341e60b424800c078003a02c5541002540030754540e134088200725030311050850f1500701d1030003009160f40b8007006404030702c105601007010580b20300004000f01c0c84044074440740c004038900030607000d01c05180c81c040c00909590100c05508034400031021540d104511200700c4404400911511303195070041551031081e4080901000320020ba8105403402c0c80c0c42b0f1901c802c103c4e0003140c07074a2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 68496576 1250 68495326 68495347
    0x250509120f190b06030307020604170a051207060e1f0e0a06021207180b0405040203070c020d0606050f041401090b0105070506090604020406080d020c09070e04060b1e04120305070611 80
    0x1440c542c80454200e0450310204030b05080000075100c0c41c42e40501482d01d028104503100c05140801d582c82d00007440350442c4540094000c1c0310318140b07143c006407042e858501130321b803100c01c0e070f90304072100801e59024a092000300301c2ca001c0f4407802540c81c100c00241c4040310b00c001134100210008090700090001480089410070280f01611962065507200c101d0107008031590003801040c882c00003004018003041c41300e4a0b26030300075600500c6504144031950302650114164030300514096400641c0c27a40104900e0400314842405820101c50821040391140c40001070404180121074010740e0300d0500c5c40c02a4003d0045548840e00b0204940c510b2604811041d51b503081220124007460a0840020b641040003801601c41c0c80c0d01d03005001180034030720a014485078010f002204014581048200c0d0741c40724466040a8149104a155142c48030b0b1140c0403104403050400d01107410801c0100180e4580302c5100ea950399040c030740240e80310b0150402030083e02e20034880850b1058005000c0303910 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 68497826 1250 68496576 68496613
    0xa08040e0f040f020405060103230406060b0c0601030b0709180b0a211101030f140a0c0207030201080f0a021207050703030c030507020c12100e06250509120f 69
    0x49039140c0c6000042030340c484a4401403810103a80040801540c404030300d0043c41d007604420740c4800c061400140100288012905002c02c2d250003102481c1020b00f48414045507004140141880c480760700d10300420201c7e016a00d610510000d08a0141580816200307440303004510024103992081b492450840d09210006203080043c2038440e0b0410301d40022080c140105c45007a043d17190869020400c42c41d29060000c084000409042541d2442c0c1074424100038810409500b10001c030200e00d03450604585001c55401011850942d40160005c0005030780c0030f0070075503101030007450041b1a5180c042500010740200660000e0310419401040744060f80a406001c00700c2c0665024810b400e4801e0041e0101c90081d90904010b0b0886816006030b420240400d5038040f00801c101d590001c10300034038804075035080003800c00c1504600140075011b11555400e2401c01d03d95610320200c501e200c0c002070311510030f1760295400b42080081d10444140144140c04032805401d095910307144910001402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 68499076 1250 68497826 68497829
    0xb0f07030b090103020a0311030c03030406050903070b072f0301050a050f0f04110118090207050c28060c11040905030901121406040e100204090504110d0b04020f030a050a0804 77
    0x81c50701912850524111006904980d009841c41000b079085895080404a041c14240d40503c5811015103254501308010002810103584880e04c5600c02001c050a11000340c0c0442240c5100384030314400700e140841d455480a08a807040000041801c1da205600c00d98001c03180d41c594606020800824031035042281700700741003d0b000d00c0030344d1600001c0700018400e48001c0d0511110358582e148550250b119400c04040004103801c407241c0d01e4202009a030304c202021a19038000c0d0f19009550300b00401c840c065101c21083d03040110307180842c45d10702c4032a01c0c410002007100340c0c0759130410300c841e07580c00d045040406482484283c1c12800c04070303503d50002c404207001441c0c104402040c0c0d120380c81041d240005090902600303486000030030024044011101e02d036405030114040362411140700500c028981c495011681d890181490203c0c04a403138885400340b41c00000403030004000e036125035030042e030440c1c0505107200c0100119150841e010030003070052098064180520840f03001800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 68500326 1250 68499076 68499091
    0x70207030606032001111b0d0c030602090f01090608060120030307030516030b030a0b06060c03130602010b0a0b0d11040b1809150a0e04060b100e01110c06070615030b0f 74
    0x104c003241c0a9004490800134103402c03180b903403c1803c0c04021107132203002090280c900100a002c03041c0003074a940c14003090651048490f20383c005507404d040d040c50100c681c100502400c2030010385250000103000076100520003030400c00388240781900715000000c040e40300d10288040f280c603031034a0a000760081209075009200d0b03c0c08402032400140c401d0203048484000600900b46948583d41c3e00703400c0c0f00300901a00c2c1c1c4040203010f4041011000c1014103550b04400074088507030351a1401c080e084032400081e01e8000d007400002804440ba04000300c074074180d0309141c00105103a0241003032801d40220340140f81c07085400201c3c05640b078a100c01c01c3e20b1050013140d50031a1600c0e02c0d88d94064005090a5942d0080018003040040c07030052812207600a01a0b100801c115a40e5800103502d00340d004008408103000603100426540d02070100511140118000c7c044800c4a00000b8207a0084e084001c11664484000c7e603450310951a041008642c403891b060f416042002840b41c400e0811901074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 68501576 1250 68500326 68500373
    0xf1104091a060f04090e011b090f050a0b04050d0515070e1804050a020d0303060509010303080708100f120510060b030919170a031b030e0c0405040c0b0307020703060603 74
    0x81907900d0104100c42080000801d40c80ca400d00d003940c070101a008a1030f0790710655583d0070000800d00551070050008040d169100e14840d803c005030030841c1ca480c0d800403402041d40003018010f400d0700008440541380100c0310280e402e0403910340240b4145d007680c7c0642402825032f080c886601d4008a0101140744119504010000b580071200c826000440d4044e110313500c06c0340f41d1005414081303052101c0a000b45004613415480e032000c9103c802080e44100e00169002d000c10803a140e0019106400c64800005980098504041300303414610300c0c05542d9901d0000c182d030720104101006034a200c00c0b2542000c1c010607542c0c1420640c03d8004807042100350007400c480e1180030040c0105d0440c1d0b00d9101400c00c80d0102e81c083e0140140c2c20581e600c070189507880d441401680c0300b1104c2c030391040d0360aa0700070409244481107242000c0c0540e4000340034900301800e10001402204c00442956404d000b4140c0306c0c0d580d008120714120155201501c060f1500c4400710910035400f410448442e4207002c0d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 68502826 1250 68501576 68501621
    0x3020d020f0a050303040209060a0e04080901080c21190e030403020f010c0b0c091206090c01020705030106050913230106080c100509040908040515040e0609010e07030f110409 77
    0x800d0b854210350903009200c0d410401c0090014a080c40c0d903a074000380003400026070941c50305c20406103003500b51400d40322080701003403681c0c4660303010380c4148d40107a031072010074100320009024400a224610000d03c2040c0d4500010b00c00e6940c0261140d50300b02c4420003440302c6911803112603142d6003e408183e00400711021450019400346144103102544174103103107510350700c8200700c42054001800b4140d101c50466900c10f004101003250b10b02400300417004e400c40d007000f800064640304195102d207010385d0424a01304507030f996008255600200d006040c100c2c01d545480c1100140b01c0301110703031750301122012064456560544c42a02034814076400c0301c41240c1d080b01041ba0400280300b154001940030010bc1c64103040c160840c0100600c11000c140c2819110400240c1da541c000d1168400090049070421252031036010154000c0c400380d031205501d50401074000d0990000401c14028036465000c03010b140300142d4040c65184044001c103540f42c07600d8444680190881c20104c0c4a05e4611882 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 68504076 1250 68502826 68502853
    0x2805010908030a08100e0405060f0114130b04020c060103050a030306080c060405242b0212040209040314030406090312060b0a030b0102120711090a0209030615030c0d03020d02 77
    0x3550415a00314030000c41c100303801018110ba80010080030040880c01000e0001a5064070107030040c002d5101d50040c051504d025041e1000044059000c5030002101e000000310300d4a8088c7c0750000c030190304e04c01041400c0300d440810041d20811241105c58405d03171000006012022800c051402d219a4003445195642c00c001d82e40c42000440700d0f980040c041004022528102c01d030000c59041e00f505105464001c098074054a4000902d81a1001c0d540b62001c41280344d40c80d445d2000030300b111821414450001c4440260390300007000207000e401440041002d060203843c15013280410001403a58030710b810318043c4003034201c615045000c90072000740744000941a00030f00d0280e43c0700802c128245503003400110007030030008407464154000e01002201040040c801090242e002e10b058154840310503050040803a0f004100b60503203441840000e8165802051039078103e0000048401d0315072595002904000e200515207502c40b20031040c0720201500401c007a03034501020307000c0d1030320307480e2411 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 68505326 1250 68504076 68504087
    0xe0f10030c1202030114090102220305060c0c1005010303020d080108150f071205010b090306010b03041110050405090f160905010212030714070b2a0706050a0209280501 74
    0x402851680c0e920390501c150002403042c2490280010000300d15078044e6081c8006401c820b030360303200a176500040c0e00c051300c034441c00000107a0702c06068400d07252895920323416214031002d013103054041e8001070b03921030420003004800c10b41603000c00104000c2d6505c3c40c000c0c0d07440c140402c004010502034000041c0500e4003082806004106402540f400c0d900d2000883c8000f00060501051010011082c0c542014520a03640a0004e000c82d8556502c600400c140c0743c141c05a20440c0043c4040040000145044202d0220791500340c0744284c0565075110156524000d40d00243e4115441d0307000c10111406070f406c0c1c0c074045c4040d524072501065121100b00c03540036541c0959800340c3c0c01040c580420158420003168444624680482d204000358001909540144415078022446030180141c8070380b900d00c421401c14078120615240007020810b40c080340a8000e0140c9a15aa10009104041c03280c040341c10600c0c00400101c00000049440c40d07500c80e0117090244d003802c0c2120040380710350181c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 68506576 1250 68505326 68505329
    0x40609140907111608060901050c1c020702030a020405070806040b09011a090f0d080403030806030a2003120d020a030e01020f07020d03020f011109190f0501030c1106010e0f10 77
    0x50541c030320700d035a9440265140c607100d400d0f980003480383c0c080543c1000080410f42d400b5100340b030f000d4003035424030360145829114080c002c8502544100020304101901800829600c0e503440701c0581c079444140006424007103050000f035002410312040011160b845004144181c00845003000803002c00e40c01d03c0341441c0300b4003c18503140c000003020014002510064001c403c402000006601d01810203e181c4042c00c01040b160b44002007414010190840c42040c3d0026003a00200700000550701e03102d49800c991510105851180f592003451514280900a81280c0c0030100c9691800c0c2c0400c41c01c000d6002d166020002031901904c0d81000006000321034400100342151405c1c40103c0e000c01c101e101c0c0a000407002e6100b00c1c881194202e00038050004900c0314020095203400a40d0f05000380110f18068444a48003003a0041c44401000c2c250041035803028640020117003071007641a0b48854101d041a2a2440398400003d003040d0f18540481c0301d1101e2028604094448c000c00420002e2507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 68507826 1250 68506576 68506579
    0x2b08010812070206070611071509080d02030a0b030109120f0c020d06021c050a0504120807020a06020a1107090c02190b010302010e011707020a0b2404020304110909010204060914 78
    0x10608081001000806010180c0c0010015071034017005503a05d204039040c00209030b1081034040307010b80904c100034040c203100c5c00c0c683c001031050480070340d6420424800c0480096000b5404404121a0a00e41c2d00c030380d00c1120040c0003003011030890305090304054144941500007030054070100710b900b44201484440c2c0c907405440d5241e500441c4d500c0001940212100000081d0b5880c03d50741400e0107401443d0245c4100100011681454200107c0d03410307202e08150244910755088c818031030703400207e0021058100c3c00040e10b030701301000110742c0080442c890589602c1000e80106001e52a50f21444080c2001d800701c03000d0002c1400740d50700c0580100004ac103005101070041000d5402025070003046541403421711142141002c1c02004880300b603600d080103a00c0b0440001c01c00c40b440141c2c40c0c215050040c0c55204600d842e01920b080b040c001d031028055500072000c2410020105001440040020103010003468080c0800b8002d4129105003000200000c60019215081d10000071240c1c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 68509076 1250 68507826 68507833
    0x50a090c02060c160f1a0f040305030403180b0406020f010b0307050d03030209030106031a0f180309010e150c0f070f0510031d0105010603060617010e0609040f052b080108 75
    0xe6440c0e510101d600815180300419007008813620010f140031410301241d0303200c0c82c030600c0c00321070142e0700740d0b000c3d500105401101591042404042500a0b00b0b4a602c5507051600c0a42e0b14000d51140c0b0b942043c039803003d5a8250080b070081035030307500410a101059800d000030401900748000305a41c4d4610782c4111504a03100e0700b141e0011a1080e0005c02488501600202d0f9099403552060340c00d1000c0512902895190814403400f074940c0c2031240d42103c0619407040d0580d61442c090381c1c40b4850540b40c50b05104442c86010035585440503070f240000a00c0050390f450700304240c1441d403918038000d0220f1040c01039070070204803c146180540f041e01c1c005001102400840e8409030010080c07a01c0169800513819844400c0000074080c89020703241503074010609034034120000c0c0284c140c07500ca04103482c044000510000001d000016405401110703a001e444d1654140f80030441e8045c40f000d0414020540d29810758090103074106031240511078507404040c1004421100030b04203024450543c1c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 68510326 1250 68509076 68509081
    0x504051302010e0f15030c19030c030c020c01080a0f060305030a03050402030d0203030c030c0d0b0409120e0d0816031101020c0105041202030a0801060302030c0903030c0a02040e0a08040b28020601050a090c0206 92
    0x1715400d01540d880140c4040c09881e01c041c403002182e900302d20403c020300190319070b5007105046074140222564010a4001840c0000401c8000f90213200c00800c1514211303034590242c051103035250810802181c1000c141e0b40c0e00e40002800034041c00c4100c4059000b8401c1081913481603100204480c0300b4a008020242541c5032120300007425131109038070071012905c401c00203503a071741d42e17200320380130b09100d0903900c19041403042010300760607288914107200c0c1c01c82c081c0030400b00d00c41074111404041c9082440c7c00702c210328a400e440307542e140c4505c640303150310104a03801c00345c2c3c055101d54095801007100300340500d0214012a500d2150210100004003014010404680203401858100f6001c80940341007840c0240402e1540d080b004214070503a104050700307019400c1520500c000e041023817001d04007080c0551102000380c4030703601c44d40310b0380817000030b0400c0303001180109208029803107001c0b01c0c20f80185040003540ca400a000340ca100d04030701f441c001008071051013100f00781c1c28550041e00442d0f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 68511576 1250 68510326 68510359
    0x806180327030d030c0315050315060105070b100501140306210f0d0206010509100501081504060e01030503030402041b0c0f08040801050f070f031a09040c0504051302010e0f 76
    0x5814001c0419405890441001d01560301800310841103c0a41d400240c0b82c80c240350020259209210b001c4084241070b0001e11003503d001c6007500c6860924209400c1c0d640b41eaa00484540c4030301c1c0d1001e01120090001c1c000e006140c0d03400d0504448003640e80c6481200c0700703c5c035805a03100544079594001d2914008111480194102841d202020800d44414201880c00c0754104000c5120340001604554010704c414079084601540110094002c00d0401d800c1c03c00181103e04041e00c42002201616032030001c40d5a503801090140050710640d400c156501d10303005030b8030303042074030128803681c1812501460006540e100300d5020b0440d80e03504269005613180c000507041858425100c10004000c0810707031034024001e290007500144020002c1d450f061800030202d802c00e01020003054204901000c209a41c0d5405003007a1608807065032460b1110302c2d000702060403540c09603400c5414501040001103070240e001038558003e0325040210007051040055250f4401880360f401070150080300100c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 68512826 1250 68511576 68511607
    0xa050f0f09010e0d020106080f032a070504140f0703110a0e150304030807021e1c02030c0a23011e2304050304050a1d01050112020d1508061803 63
    0x754080000103031140c80e00d900504001c604c400c0100075070b465010402c1240360030869440083c0c4020065030801515808103001d070b4030714440c01c1c0e44006d02101d80c194031102c24400d1070000d2100030401c01861003190880310180b2400c80c2d116001c04032901c00110103034040d00a450315a0090641d081c41e001c6600c800784c603400c48100302281c00c1000c101e05515104c0e8040001c1d03004038000e465044880c980303694001d00d007005144801d28160074410a2800e661800103004440c904010017100204d1132010040f4a54021895519190b0ac1420821002d02060346a0392140207462a4000140900901c100d800d03518072441d098616031820804899040c640c0d484011440a840041003441fa500081e070204501c05407000c3e04d082d000003404015501d04900c049004000d1440907001c14031502d4916880d49805200b014107001301c045404a59100702e034102c2e07410768030201c000c000c40d140041c020440310255010701500d910540001c219007403c0050145c616103842c000842c0b808202d0382c0003205 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 68514076 1250 68512826 68512831
    0x31a010804020d170405120c09060607050a11060702040c11010f020f0403060b06090a080606010305160e010c05210318120f1809010e1f05010e01110c0d08040e0a050f0f 74
    0x491380040c040800d0300c0d500c140d03030848003030603180052100306100d8040041b600000b40140c0c0c407a10302045900c0025001203900c868140c0c00001040d4000b0384c3c10081000707440f9010000b035101e881c00c40c04038481c3e40c020b40d003803800c1010b600007004118900e000f400100d108140c00c248500b00d041c002000020b105030044048a4005020301e41071082d0f45010070310f145030640010700540c00603800c02130f0550707040c402e4a5100340d604008401e8290004800b0b00b02d4000034141d103040218062000381404401c02c5100c8103048001e03c4040130198802c260a030540090f2140a184c0c409a800450715120006181e031718810000d014134980500204143c0a540c464441101101400d01c0b03c00303000d59851001500808031090000341074a480780b20032605090404041281c110741c1c42091050766031004480d440c1d1364080c2480c44030004c280740701d039150112819015a002002c407a88c001009101006041115242070714002e2a40f9004034150a440c8122400c810b002c1040001500c0c0030608170400f41c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 68515326 1250 68514076 68514113
    0x1005090304080706050406022812021204080a0308090109050303191104060804060b1207060f030f09030c0c0603110a0f11070b04140303040312030b1f031a010804020d 73
    0x1c1c41d05964031400c5042203c5a400300011410204040210580500c000c8981300d00007810328122070a400307008821030900c0100a044145981034a148050081040e1012004400306007600c503039079640070603501d80c6044022000070745040302080e020801401100c11040e8440051801c51b80d074141388251800c400030b51445d0b410f49940c10741074044010740041015101540c0d60403405e00d040e04140003541d0402c4542406000c2400f015600e01801054203001d0341d0061031701d88a40b003000501200030341100964108001d183c8080841007507088540000102d108141c030010301961004182c0444001180040b00481d040010040ca01d2180c0d029000d0503078a03091860159044403140e501e0b2211940100b108180c0008080c80786580080d03002040c101c0c2200118034240c211354400701000040d1001030185070325403905096a55803c0c00390a8215582c07603414109170300140004014000d52044036140300b0403010701035010351007042494440c41d000b80c180c2d456100b150350f80d41d41d01d4090304803a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 68516576 1250 68515326 68515333
    0x41a06010c080301030b0105011409010804080f040305030c03030a0b0612060f062107230f09030c060703020114070318030f090803131d01050a21060221100602100509 73
    0x410000b0308010266000c0e40c001c2d6003101056040c42d00140c422240d600c0444409038040c4103500c0140c0c0c1c440c402039405544000c82c56142c02e5a0f0750180720074065504014070a00010408d00d040d1803000018602c902280c1e0000d0182c125082c050000a03c00c03004080c4150361b06100145450818882c401d1201002800c05490b00d042844082901c0d980301542520201030841031010f40c9030310841242e0880d48540000007602d45942600d2001d01c00c1d04106440c0780c80110f0090303566075080c4108003000c00041c2c58a0769a00d5585802030003881c140d1030240e140741c0c8000100740e1113840391180f00c0c6c44180c1c03208800a010b1968400340d60007008007204d04100541501d001c00c008000f032001d01010300d02d415800010504001240050313684618088031500541d0004200d146c0c3c030b0f113508000712085000101520580680f00100010100001820441c000103244c1401840101c0c20917035024801d19518403030300c40b89074020031008c0300d21883d00180e1061046010f0510242e120540014640e4101d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 68517826 1250 68516576 68516597
    0x40506030604030e18012414040608060d050a05060415090c0314011d030403060f0e06011a04050303041d07030b01050d0e01180308090f0a030f1214040b0105030c010503041a0601 78
    0xb1748500304090300140c0111104001c07400c51902c010f2020003e4690074145004100c00da207104410328001c5205010030804540041000c6844000c040c54445401c01c090b60551030340ba003040c543c0c0390016a0111200011014001c030912001e01c07030700f108642e01010300b010311407441d207480a086a02840350704180d503032899180301085007034a0030340c44406a0070203946c40310301e50b007051012600119881d01540b0304107040e404209402080190540344a400c0170818010032643d911400c0c000c541045415100c00100414003a091071880d50900034810000c0e90903603034201d003c9081c0c802410929021503818810b4420208250300110107101d051400012441000101da6003040c6617110164040b520102c00e201c02040140a01c90881c071900c8001c0207843e006950040c0344034981140c1d801000307469801d00034804103d4101440302941c203401420307241400d08080d14801420b2164074420322460342c1c4000035500a00691f44a035410900c0d582200c40c089030108030b407800c0101014100400c2e0200f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 68519076 1250 68517826 68517859
    0x1809050d0503040317010303270302030a1b0906060504180213060e13020711090106020d05030406020f2b06050a1404090f0f030f02070b07020d1103010e030d05040b06040506030604030e 81
    0xc1c18001e41c003a94651203064009504031414a00d500145031945030782741030078400360b10005501c856590340b08030700300c50080402c0001d0003400c1c0704d074000d240e2560030b09000195856009024100752441c2d1072110020110f101d0f006d0040b44100d2854000304040400c04001c202d00070004042c00c864040c09201090300080d02c0c4004030780c4a990119020080001280403e08141021a014100900081112651011000d032242c0401480100134a0700000c8207080c1420000640341317000001c80718150190500d5000002c1a0122a104070306a03140400009a07480c1504050301248c1802d07040c48586012201400041c0000f808241c030581c2c2ca1000490014406080366001a07000f42d03a214003031707540d4003c02030402940358090002880c0a00c01500035030b0b40c1960030b1b8051680300340d1980300d0742580c501190141119040071100c1f4000450700140380c0c69150030141c415031080e881c8100d2542c1d10b80800c402c5550544515030560300c04400140041d0190f14803420450000f004440703c01c0f00080c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 68520326 1250 68519076 68519117
    0x90406090906050c07030210020d0213080607140f0a0507292505160516060f1209050a0807080d021306020f0d020d0e0d0501050a061809050d05030403 66
    0x2032010402696a007803400a0040030700c906600640340c48400d42c03401141da10003d41c5d504417640b0251549600180c540d80407080c0e42d0450b084e080d2420740c0756048950b6441c9540d00d4000454001001c26906041054840d103070030700312901c1c000340c6580c141c24958600c40c00ca83c01e030401355044074060004140a5120001161041c4a00d000542e0a60071450282c284006c1508014480382111850030500d5003056001029200c1c03181c200820b10007003070700c1410041d25180107650500c1490103800b4010a03150750043c035038200e00100d5190360215a500541aa04440b0480400b4246401043c0201c00046401c4003c081550107000e802c2d08044034002090101d92103400811343c50810301030304101070754040c883c4885004126000e000c101106001c0a9281d40d0300095001c01c02c43c102c50181029034644551685403a0000005c0005180070303070121004186074010011800c0b09040070000070086030040d05c08843c0d100024088122586000382d5003030304050021814804165002c021107413030003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 68521576 1250 68520326 68520329
    0x6030209130204020d060b0304020a06030204060507020111031b030d0b01140406030903051e040306050105030c13020d18060b0909060705040b0d020903150105040f020c120a05070c1203021005010311090402010203090406 96
    0x1d1501c140c2d0390424ac0304102921100d540141c09050050100300000f540010540340602d03020309001889040c0786102030b00394072504007503800031040c03005a02c01078140000a0f02c018800d045040090040c10401134441d0346c62022100307038190081009210f42c2c0c1c441c1c0c04c40c5c00024400e0806509000c00411328942040c00c0241c107070f6005501240c01c00c1030049900405004000c25800790080d1900340010035404400b100140d0070b5942c000814082070b040c507038005010255903828241c0035480d40d28012000e031440c00021845002c0d80320100364103c0e000b05d03415020f0410b0b42c54481c80d00b07150035040c0c0500d80100c0800c8044941c240320040d00f5803000c0c803c0701640700e800c5443e401c82d581800b04210840d03011f6100c86100a10612400586900000c1c80c0c440801108807201d0300c0f81c0f85100100c0b038500c100000101000b00b58900000c5941d580401e60300d4142c0f2036000c0e28041154640c2040450f4001d2102030a05001c2030041e05041c2030404c07085412030300601c146c80c504408080810260340c00e5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 68522826 1250 68521576 68521589
    0xa060e030c0f03210f0601140d1e140106020a0b2d090609030901021510050406030813050f011205190615020c030a020102030a1d0904030e1306030209130204020d06 72
    0x200e288400e0400000141042c1d6460703411602800c20b245c10001a9038014030b90b13070501c419268400d6141d48143c09a485a80c0f02c000140b0241c2d06040d1000380c200c3c1c2c40c400401245041544100b400d03d1500c90440c142e43e1240d00a03c80c4080030b8445060724080641686084c1045c48004440c4041c04148104950588045049142400d03091103191800050401505810600c880145c03681e01150107150b420b0b021480d250b080c1c8a010281210f46075580c84164818034107200001005102406065260602802d282c6402da885082c0024502510100d500183d901060000c031ba1100707510407078001c24402403140a0350f0403d1083e604403441e80d04800030041c00c00e0104600b80764100428801c4c82d106801400c0038543d1940080c0d40e0f40a024500c20500c00380c00012000c07116407070486821510001c0004266051504000d044a00c0203c03e250103001c4100c0a00507010890207a0001c903030b17014040c1d44603070b600c100ea041c01f508411101280c0c420f40070404080790742d5a43c00b030440038041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 68524076 1250 68522826 68522833
    0x40801020703031a0301050910020714010203040507080615010903020402280801080106050a05060301290711010e040905070b030618010f050f010206040b07050f0708070302070f170a060e030c0f 85
    0x182d44a442d40481384034411030784030f1380c1007000300014a00e000c52800300090383c1040142e2641c18034600070610501d50500503503103620110420060240c0001c002045a200406803411900c42018804081407003240e0f41e400301d040c40c3c5007000181069070013003528204505050301d03070043c50402d10303d010b1280780e034000010306980c0050000480c02e1141c5d00007002c003180d5440c0034601c0d14002c60440c1c0014829007600b800c4d44000010340c1124003182d440455071044406913552101e01c0d1070707102c0201103154540018071030840c0301e40c02c0c1080e1080301a1305400c07070014050945800e001241540c0001d200039044111407100020b844001441d82e800b0340080801003010300d08000910048804140c0c0300e82c1190b0041c0c080c400450b964104a030340125983c502203555a5211024100e14401c05000078442c0c0e20000c0c5c0070303041c11750219042d01500c24a4200105043e990709040814010048100b0740c0ca03004962204001381031030b80718040503015001501d060502a540e00e40c14546484030440136600f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 68525182 1106 68524076 68524091
    0x201020424090e0a06060306090621030e04020d1e020a1704110904050c1005040518060a0e16080903040609030b04020a030b01060f0212070503030f040804080102070303 74
    0x408250f81c0010705001c502500104503501c1007100091510f4030114802c0080d00808084074504042440045440740c0041c6a800d4001e170200e05006404d2840003441d1114000740800e15810040060826a00103038040b144201d0044001d5440c4100072500c00640c00144260303034142ca9511050b4141e685140040e01421140d5040303074054a41c0c8100030411034005070400b03903440700780e03120020340544081c1941e0754010b502942d41e1007035003402c0515968821007a040d0340480c1c0181010a00c5540d840980c3e85903506803154031035440c0c201e440130b6500f40c1081d84250400b008900a614191828400401090242c0002810440942c02080a55546c070740310f00c0195400c008071002c9540c2d20305020303084100c10840500980103000207030284180210035a088950000045c5296030364008500c1c03904840140200e448041c14040459480400d00c01b40a206109403000104003 = true := by decide +kernel

theorem cover : BRFrame.Cov 68345326 68525182 := by
  have h0 := BRFrame.cov_init 68345326
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68345326 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 68345326 ≤ n) (h2 : n < 68525182) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
