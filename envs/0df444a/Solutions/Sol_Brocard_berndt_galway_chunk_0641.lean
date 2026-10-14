-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0641
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:53:36.767186+00:00
-- url     : https://prove2.me/submissions/d25c48e4-ccd3-44d4-8f9f-de61e15a2cdc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 115107913 ≤ n < 115287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 115109163 1250 115107913 115107953
    0xf081b03062e0803160210050c0309040f0b031009030e0d03090504050a0213170114011202090c0405030d03050114030a05031902160303080901050c0408030909040809040e0a 76
    0x14501c1e000c1d02e0b80c494192000c10100150700801d80e080548102034100030064004102920b0f0b456901e100b52070a90b00c00c11200303074855480300e6040709065014400b100c030351190f50b1000c0e44c18103c00701d0400c0300a02003080b0f90003101d900c0705034410039a5000c4c0540c4441c1100301c03000050b003a1040c10000d040e00251441c07280201c03101842000425042076100013103c0080307402160a58400e41140d000e400b070201c510840a180c2034012604150682c0c2c1104c1030010b601c000c01c1020805100c0c1001003100384500b0141e0445481203c0c09810034900007940000c18010080c502503607900440e1a01615254000001c1e40da0b80050140415001c1401c08500c030490040a180d04203807242a101d21900010000c94000f084040c3c1090f80280285800650045800354a4a40c1c9040c040c2400900301c401200c613510301030014864844050a40703041c0c0f03481c0c00c021424080700303800380510800040c0007940c02500c01d2000902554541c0925001d0a0040e030144c4841c001614011580301c1c00c000ba2100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 115110413 1250 115109163 115109173
    0x15080a1103011d040503070515040314090904122a141b0d060b0303030a0e06071110090302072c2d1305010c02031b030f04030602090a0f081b03 63
    0x3449101c0c0c030010020f40020b00f08049854a141140c5035215001c0001d140b80278480744d865001d6894040310313100d94040e40b188214083c00f00d07801411845400d100075803120700c0c40041408070342c990070105201c80090504000c0301441080180c10385d0541400a45004804c40c059401c000501c42444840f0445800400c8150080c181e030040741c482c40d4000d940104910003402c020320a8a4008816542e000b40a485d544e0400c1441c179005803c2611400c0b80340e10904c0046200340740700c0e40e02c075080300360b04a024000481070208200090040707500250218440c60310041000c49412042c602d00281d06c0300d1808095042d42c800a2100c4402081c0c408003002400480d4443e4540c0d90b001201c1e040b0b214550550395452120a84100307207a404040c0084d072800d41624081d41e000002054050701a948007c0c0030321106200e156284517404080b81c6015040c4000c000041103034000e00354000d401841c404566460381500407070344045a05c480340c194081882c00491012403d854081242c0c05d4024207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 115111663 1250 115110413 115110419
    0xf1a0c010e0d11030702030d0c02031f0507030b03160302100201060b0f09120d09050d03090306020a08041124030703110a08070f030e0a121110230f13020a15080a110301 74
    0x61303180d080048d000014070003031000c032004550f41071040c40d00001c020040c0302654407600c903816006001c100c4500000c03d142c6420b003403a03840c00151410105030000c0204075554195428400180c0552400700255900c440c40480e42042c1e800181c04451022102d0302c0e2110a441c0811950406c1e186070f42c1030f1500301c05801074406501100341c00c01da420a0b40d2080401c035081c5000ca07409000c6a0005d000d003803002c84e0001c96568000710941c0a540101d0303299000020140070007103865074449211036844c100601d2441c0d4a12010061a80900907040001e58000792001c80741c803035440070480700c0000f245071003000840d503008001c20011300b10910b0704018a802e0200001c1d82d9801001c6c0280084c0e9103903a20141c040d126484020000c0c038288243d90000340c3c1c1401d0400a0404826210301128102c41c00420140c0c20890240c8101030320100c40002d41c840151491508520f500142d0b0403985001d0046641c5030344820b0810420032540e2450058a000007404040700d001c0005500d14102c200010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 115112913 1250 115111663 115111669
    0x61b0d1805061e0a0b0607020a060e0a060302031905040501060f0303080907060e060901050c01110c07091404051509120a09170a120e01050702030d03240f1a0c010e0d11030702 77
    0x31503071190040c4c0001901c000c1c0c140020f541e0f4050540004e41c4201c6a402c042074103540041c0100f0441c0341524003038030050722001c05605a00088803143d0401c003901507018800d9049030070050b001401400001081c03a120040e0f1001e0350101c1d001034001c125100b051000c0e89508000b05c60080020703240030b007003003038100740091424456801030604021012a071500a40380030346c446030400c814000c001d80c0d41c007983d1280d55116271461040d40e25142c502041110081c882d200da82e07108030782c4207010f80b00411255450b100c0050000c0c020082c0ca2003000a505041c400000c028503441306640c8503007401510f0606400d44a0701c00c024490040d07080312441c14000f030a400503c054100d55401d0900035413800d035004032421b008040b0082c0d803610031481c803039201c1c54050b1f2100c10102d055003140070b1200288841e8450415003031240d550b1690782e0101c1008085c00c4062058041c07030030180710078a0081c0c1520740d1425074948039862085030304091104c41900c2c0d0869144129007407058040c6003450025000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 115114163 1250 115112913 115112971
    0x6060109080a02220e0105090d020f0105100905041e050c100e0928060b04090b120705060a05071a070801050d03091a0f030403080714040305061b0d180506 68
    0x4c0b48205500b400c4e054260641c1390804101c003d1140002c02c0580780c80c1c4030309070b591600592001d003d03001d194482c0824003c18001c403032041248c064018112880d044440c03004090007481694840011700c1581c005001400006a900780540000c01e0945031140421a58040381c2c0c1406040c425848401c10043c1c45091207903500503034004005054101c24200101e00900048408298510b0584082255200d5001500c1a10303032000c8100100c0c0d11000a015802c0e50a44c1c20350302592125804209502c0d080e80140203804003460301a0070300403180c0d00e40ca043c1c1d60000c4511990b004550410200f00c1c0c0c001850380c01014104c0e44044c12003681c1d1006442011140140c00420540c00341510169401c00e00b15020b200080307000e172759203251500340100b0b4080c0c02d4407181c000450100001c92a0304805056809494001c4040c04040e112031000d01d40d171300d0085004103583c02051050211102440c4a402c0e0041c04000081049181c1490001c0c103001c4014402110f0f504070b0040040340e1500441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 115115413 1250 115114163 115114189
    0x70e090a0b040318090f0b03012018040f090203010c032906070c0605040608090a0309050d020406050a060207140603010e040201080406020408030409020a020f0705031b0a030f0506060109080a02 85
    0x1000702403039181da080844a480c4040b0400414000c4d03400c00280340b0745954009a00b014490804020705c209102c1014241c0380c88448080f0083e03000c1e02c409240c0c403503050050071042940900c10a00505001c0490141c40034503004074100d40d07603032003840700b5400c080c050038034800d1151400700303c0d4051a03080801d41c0301700c5c2d1007101414904164401440e407105412140c015812440c021851569003000401d01d038024040d190003e0091000b04a41c1c400c0001c00919041c1c4c1a1602243c25051600b80711503405282020b0f40c1c000e840d9140060541c80e040d400e0f40242c1102d9000c5e1026504200c000c0c02040034984000d40611420001000059140000320341c1141d8246018070480c0c80c0c03800c10801a00641e00312a00741c5c08005030000d07031054a50300804014005400b940c0c43c41410103550340c0c43c0c90191013550342603004900c1003111403032040c1000c014004000d0441e40260307180d4440b090b04040841e01140c480d402003080c00345941c1c02002d214006c0030380d203000f0440312aaa074041100c0d005546 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 115116663 1250 115115413 115115423
    0x3030605090f0f1605070203190302070b090904200a140a050d081b10020409090b0a0504052104090515090105101706060714060a0f0606091e0302060708030108070e090a 74
    0x20045071310345110394216044150010126441c204160304605c85a41030030400b00c02510503101c00060f121584410b070740d90001e0027803502c80c0a68564480c050143d050040c500558841c1c1012800070796500304416010344005c4070f41504e82c594400510500c180e440e000f403403042100640c00400070f44c0b80300844a0680c02c288041c00e403036589408642c6481c059011002c0d056002007004a1082121b07441845007a0140d400511140c4504007440111001a1005803158004954141d0000720141003101280417241b00d5515103551021000c00b2034005684600e0380400d44945008175141c04034040b805000219400f030386400079044040e00b074003403400e400829403010500103100f5035142400e4400b90340c0c1000750107100302c07000801a80c69001c2103d0300303880d01d8a0078420744240002480307101d0680c0c80075201c0100c0f41e0704050035401000c407028448009180304000200058580c2c40c050107810f0b21a030724040c1c82e0750401c03c105061003480e802440307200008100304040074400083e03001d00c80d9000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 115117913 1250 115116663 115116691
    0x80a0906062c071119060b06070f030909140a0b010509040e010e0706050c060118060504050411040c0203031303050904060305030f1c090209070509040605040501080321132d03030605090f0f 83
    0x2600d0144081d1840a903403d502040c0409d00600b4841054004400c40e8820f955281d072032a11480c0d004122520014061020f40000700000c80c0c00c8642ea011280000c014100716042c02007000004056442288021207035075150b81040002040c200814400f4000c1414621b0030305d80d80110040e40d030401480742600d00c0751070321015070254040e9072041c400303040090401d0010346091308060303002c141800d0700c550203980740c245881c4c030440c400300507a80100c14405808500b54041c1c3c03403c94040e0050300e5920352150341c504000000030010070003071030b600100303590701c030703140d00703c2004501502003180caa01c9032050502c164140140d0360a16001d40c483d00e503051813901c50354040041001804035421181e04107140100101e405c802c004081c211101c178021684c41d60a140049600b01a03809940080307202c41856030303902c0041c0c1883c15038000b07a240d010301c4510348007588034046040c2104003000d4010079501d0100f40440c0c180a462141c2c441a072034030740c6102c1d080c40c0102441041c00103284588031100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 115119163 1250 115117913 115117963
    0x2030c2b081008010f0e0606120709091406010608041401090b0c22060201150503070f0302010e0d1a01030b070816050f071a01091b080a0906062c0711 66
    0x2c0c0108010181c81144000c2004895400b13405000700300c0c4680300308140c1700302c00c0018104d1500300304042c00c400020010308242458075110402074410b803141280d80d003045128000c40700b0700c03c0007000e008081d00d40c1c40c8060390405051a0210315114083e02a02e030341440891404a00c48a0380c01d6000502c0d415066600d401603812140702411050300303442840c230300e8040098600c0c0d05400c0324600c504030700d120841e15584d41c000c0699030340e1607208081400114010800266000d504048182c28001c0c001082a511a5540c0788440400c00c03508201184c01c100103100344546007410301d0740191107003458055414500404110b08200200c94000c200b000207103850f54849004c2035070300761a031001d400102a171583d0341d851441e10090041c0e40c2c1a515142c601140d012000c90340344d00d41a1300da00c61015944809012401601c0c504000343c6a8580707500000410705124810040740c0e01d014410400c043c01d1a40c4454462140a410501084108601d2110320400031132000904407040705220001c3c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 115120413 1250 115119163 115119181
    0xe06040b0f13050607020705090601020721080f0f04030318060c110604080f0705040b01050702180901090803040b0403110705060405060c01060f03080d060803030f01030602090112050702030c2b08 86
    0x40c1004282c4e000d0780c0140008140c001030300c40c09581003180c0b400031980c1d0f202c004a07500d99041c0314a0444d080d1130703103901488448450070400428010801c2d6032418000c1c01d40402160311203045034042000014081050603801081030910310034803088542c40f14a04800208080326081021303202c80442d0021505641c3d41e0700444c0c00502c00001a0340c0c80002d502181a111a25440f07818041ca080c401035810541c8034004950030340364010508140e2920203910407404046c0101100b40b907641e50074150011034000400303903110794407418801c9920b19040c90300038201600003401e02881c0d80030350000e100540d11001034400752507080e03ca031500d0308203260b0124050310040c0d00920500004034008414020b24030020043d0f01c45580d01800015074440550342d070b174401100c0060080c48140c00610000320b10790014042c11105142c00f2584840403503041e402c07140c054400401591001850000d00b43c0240204e0380340ea5a020034166400c2d54180c080c44114082c20a00402c014a00e4001b5440382c2c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 115121663 1250 115120413 115120441
    0x90b06030106120e0115081c05040e090a0b2d0f15010314070c02030d05030105010806120309040c050d0b0a03110d02031908031e0403141806030c0d0e06040b0f 70
    0x4084000911409580160b06c51070742500f03020792030042c040d02e404c50140440303164601d20306480a0f0348035840e207483e0400440e0b00d00b0000d00b14203518001c00781c00b0f074042560045003038040c0409107645c4000c0e8810b41d0000c3c0d41c000c40700201511590380c03003040089818450803607681c046582107855107440d9201004034024010084a4081c0440724014080015406420240f07000e01c25005c42c2d0a201454005403034500092003664000b43e8900001341203402e106c1e00701049c1d0310308982124100107402c000a41a111a520704800203003000c24580c001845502402c85942000c3d10450802821500e4480d484d41c0031070030003030040c5c0c481542e01c0308545041000030080c1d1139082110341034501a1a00300c5075540140c440811080c10916071303540c40c0051600c054012070f45522122012080340c4010b24403138201e03000300540d403030300141075200d50386030000223500c00da0b40240b955680d19400c0c0c807100c0840d50102c80b002c400740e110030100000941076070245900280c0d011400c3d1190303915900940c40318 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 115122913 1250 115121663 115121681
    0x10501050d0212010807030218130221150a0c030c0206011a04080d03050618010b03040f0c2304063606210308090c01020703030e120102040305060f01090b0603010612 73
    0x43c0e2803000040c1c00714081400b20a49108403141c0d040340c4440190100088815285a40840041c01c01100180351000c1440d0003840c40c080c642004d4072040c0150f50a14019840b11011401c140e003c0000c801c00a12504d01c1100d840d040800c02d14004c404000d55541d014007d80410081014008900c0402081030740d00a00042086038100c0b103100d07c0080c050442543c20350f00035a145c09107820035645a5802506031040c0e16146030640d600d6468180c02804007950980300400d5120001c18540b0100c0b8400c40c516440025501c010348070281807000f01c40040e03101080710341c0e840c0714949905c0d151040303810714140d52041340220043c05075020030040c840303030703001c184074042c44040ca1000c00000000034080074001c0d00d44446966036101001c1d05c4003c0c800e2600c0c0103070850201440004e004600f5410b55140c040c1020035581d40700d4158500f2680250002d98103503010400700000c421039520f8071809002c0a5a0500c03492101c030010070302c10f00044c0501d0042c03010116400080170303143e51100b040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 115124163 1250 115122913 115122937
    0x2030a080f12010515032404050702150c0f09190801020d1b140f180d0308040507080a050a030c060f1d01060b030903041403150403030609050717010501050d02 70
    0xa01c450003480d40c440c50340031201c0c01c1041421640000b80902e032070f00c0800340c1000c641074614599542e036109902d181b120b10341034082600f0b0346503030541d454035180300702c9106080f19001080010174801e0a42c01c001002422180c7c121410000c07031001540301e0054440389072054030501d1a4010003200d03400780c40055004186036603c0845c3d501178882841d04424034454042c014814500340b9000100d48407001d428003407104800801403e10038502c00d0b0024009d004840c0c110400121024001554034000c0010940000711103005000034441c081c0511001881120000c0040e016195282c139110030701810088c003481080c004090510a080c0c101084000704180100544081040704042c0c101d610318001009610300b4101241c601020011680140006002541418030300035900b41d10307003505031080703401d8002c000d4801543c121060724a4041c0f4883e0b06c01091450030300381000c00700c41004003548100700c00c50b405040d00100d941010f5040d2103007841c2c10355482514424001c041e00c101d50a43c18 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 115125413 1250 115124163 115124167
    0x111e0a15051b0604020a0506120705030c0c0627060f04032604030309050d0309080409180f0c061409090f10050307080303040204050606030919030c0602120f280902030a08 75
    0x26040d6000c43c45030b03c280c0c42207031071411090b212000c1c403829000e041b828000a404034404202d00b140100301031948180040001c0d0302d448545201c1908229050780c0d15107245160703813114001c209400c0810f1040c3d040000003440c0c1803604444200700d0700c40c050406410710442c9021135240900c0e5a450600540420b43c0c4407540d400c2a24000f401004160b80981c3c00e4000e5420340081e10b4800d005003d13046410912990925040443c400000c144070750210310510f01000018002a0351900d6003e000c50055610041d540d01e07104000d030404101562040141070200a210340070741c0d80404c0f0301e80040c0780c2627800150340ea030300c2c040503d8802c1e2a01b00d03035454480c1c040c0000d403804000004601c00c9100362003d21068880c0da0500410740000d80e42c4185580059251203141c60300f6809040125010f46081c620014403170f1217400c201d92050f00142c043c0d01d40d540c20084807030316440a55811a00f100c0020403240320408085010481c54004212520b84501c50076055503000c11010201d039070400346a80e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 115126663 1250 115125413 115125457
    0x90903020309010311041206020c0109171b0309060d0e0703020319060605240a18030b010302120d09061b1502030108060106020109020306071202070f111e0a1505 71
    0x1035a2500142d5000f400a03007044105c070b607220a86002d440c21906004c2002102c200d0664524010790005101509250b680d50b0034480441c07140340d1355060803200c01807059a44c1100d1800c40180c107040303e1001c0400d90041205100231703200c035401c41d4159500c0400010329128940d076614100a410b82c400380d40b6116018540603980c5161110440a0b8895203040084982e0780c4213000c1a80116000003c109040c030f00d4844000300c10000900600403986440301d0710964100300707080d44160582007640c198000400510171414507a100c0900c40384003400410090110b148020014a01801050104444090082494030416070342404840d07201c52903600380034600b00404001c3d0001d114001c00c80c4107035000040d449006100c4c1c00002a000b0f40646425a82c5501c1034a803a0612804240081e40c200511400329035085100c0505c1446002d10139085942c5a081002c03100c002250f0f14200c51402c100005070790344901500703040b164599400d8128109403e410381d054083c0c40b120444000d0303042026 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 115127913 1250 115126663 115126667
    0x60e0f030f0111030a06090506030c01051c050106090608070c0f1e06020c060a11040b030a02030601120e010c0906090815041e050f0d0305040803071404080a0f0218040f0813090903 79
    0x41c0d44a2070050300c00704841580c7d80929400c1d02e02c25a11282c05410903904900694810401460964024038085002c00d101781a60002c84100364058000511141401e0044541c00640103801140350315204000c0402030301c5007030005454800080c001d8070140d81031620f01e02007000c11203260390059021900c50384890001e035242e001c110344c0422201c5c41c1083c3c0444420443c81903400751202e944d0f215085035105002d82d0000c0d4000380030541449112100d010408241d8010344412480450011540b00d6407000090401001a007004d000c0c86100001841540d0000800c400f00303604070071200d400d50719242070601c00d01b00d015010340009044c0b01068070600c040054401075032001182100e60b054407400c0118100c6606803401441e00208001060040d40b040c01000306106c01c141000d0721702039a804105240801000c0100c130a1b112a015a005514006c40480240800700480404501c0d240d590307083c1081780420300405014000c101d944400110b2840700b4003801c00746104000e205004c0c180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 115129163 1250 115127913 115127917
    0x6130615110c03070806190908070f1101030506060a080a1d0d0f080f0621030409140105040213050d060f0f0209031b090c0c24090d0801060e0f030f0111 67
    0x405440c0315121003203106040019451080740c40c02e00146c8000c0c0c48143d0403484c10340c0078007101c45145031544428404112044010a019840f80703d062162040318640a00c070b0784502183c00f0305040c58041007005d281c5900c2c0c01c90314040c03400d14040ca0a81c1d01c01c0089401400185000720b401a19544400c9415400103940e03468041140c0f10204903d04000007203031a6002142c0003026210f20380b011900c0f80c109407040091001c00d149560b910025580700c824a160010390104800c2604c0d0322655011200ca0b8a0306805808180c5041d45450350810340381c80104641d100e164020340c031122060b0148001623004003500c03d403500050050950040c00b5034040d410040142d48640034030300c1038110031004441e0610000c080908001802c0d520750036086800d40111208c031646024038100c1c000d440a0740003410b800c015090190850342c1c1400c0060514003a40c4c2400078084c0705c003000c01071024580110b00e800701500d0495001420280d0030020074101040d03051642d09a60a18040010040360040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 115130413 1250 115129163 115129187
    0x120609090c080106050a0b072316050607050601032a030303050402040b1e061602030a050609071208090d1113140c0403020a050603040606051c0b01091406130615 71
    0x541d0508191591441800c0b5085407040c039900400e030300004c001168034400580540c41c0078a0230042110300da607108104110130340d13600314000e801c18940300680c100b0401510340030700f1042e07aa050130400c0c01d965140d600c0f0740c10300002d80304000440e071040b02d00c20075031400803240b45402d0074500050707a60710b0301402408050740c04a10840c20000b5070803541c201103000c6c002e0300f81c410001028080010050140a80c84081c0a500d005002a510700150702c04000111806100314000c0c55249041c24000d030034640282c20898080d400c8101d08004103d6403015100400d80c2110442d030342c400c81f80340964401140703502e5141c1100d60300412020440740d950002080d201240c4892540ba40e0342200010b0b140300e07901000794000c0042c03400f070005e42032500203154040c2c81400c00082403500c80c00042c030300054201c10340180c0c60101d02103204000462020174010100f0140a0012000594250a009a001309400d024880d0300510410a01031500080d00808180c42d040704e085007401001072181103001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 115131663 1250 115130413 115130423
    0x30c06010929010e1306030b040b090c090106030b210105150102010b0105070b060a030819030b0f09040f0303090b0108070303090b13030b09070b041401020606030604030905010302070312060909 85
    0x40c140c1c0707411992440009042c09003504010402d41d40b610700568800181040e400d81244001c50f00090900b003501c9090090b600a90042485103400d00e008510860001e02c2021036402451072108075855400e05141510070500700400c411b1150750100d81c07241c1c08131580e0394200750490420652001c1c19400207020700701c0020b6001c404862240160300740c0c1c4241640500260040022002140711015980c0d08101c00a004200243d52519005c2c0d0f5a08810004d600c3c4000c90340f075038801507403d4441c1010700c500c01d56122003e003a203e400102c8281c0b000708060542044900d0341410148650301018000b644003014051b9561905192542c410715400101c0c041500801c01040c81c40c58402500d42d4542900301000002c0e095a58000301443c0280003030015210310803010501c5038905020300b004e030101d440c56680b403c0d11840024a0300e0000380c6500c0c0250031074030600000c60350000044003500c1e030078200585c2c2c0d04520316013100e84001c14890810300300c2c600039021520700000c4c4c20045d40b9a000d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 115132913 1250 115131663 115131671
    0x110403050606030d020601061b0c0303210902030a030c05010e0a0309050a050105070c05010c0201170c0d1404030e09060f180601080106082202180711010606141b070503030c060109 79
    0x414144c1e100080b18a05000d640008010085548908100c00b0381c0f20f4a0010806102120340e00e00309045c05a810403030100b0694810080c13905440780c4e80a82c080301e0310b4002c1c4074160190300441d495070281080501000011a0200305004007500130260301d03c40c03a8112042c800181c10010300100e03040c02640d1285134a020300140030341c07281040e90383c02600040c01100b202d25241c010b498003004000124144018003918036444112581d00c0b80c4070f50002c5c40ca082d590210381d01ca9404881c81120110720580c20300007808080307036000d50341c00c44130701c01a100f180c21030302d40100040410181079501644100b480f00071aa012840c0c003040c901442007130700c40a00741e0740c0342c0386d040e81c240d20202e81a41e19580c540e200e5280002d02200e032802254005013411042c140c500b660070f40030180440b0b04074081000d0030066249050309104603002008145880c09903401208201c81032403043e041d040c43c1d40d14002071020309201c2c06200c0038000300001822246d44121602d5407903203811007441400310403454 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 115134163 1250 115132913 115132921
    0x30b060303131e08070e0105040b0d05150402011e02150c0703081308070b010905060307090615050c16080d020114010f03030305070e030712050f0a03080414010f1104030506 76
    0x50b036200c6111240051045800c2c030071a06203008000e01c82206028010100242d40d00c014405c00c4046c0401e00140f02c03035981043c0034042500c04882c441401850f102c01c610b0040f030300110740e0400c50a080034120310651039600049034008012030031030500101c0ea43e84841850f0300003455003800d144124000031a03075102c592000c02c9015802c80640861090700c0001c0c488c00222136410002d80c4100f48450502e84561150a0441001d030011010282d46800384007007072408102180c020034801c4018000d070f80c00c019012000b14070412194060103030106041d100c0c40c40502070040f00320025012500000e44e22200281d4540000000a016500e012a0708018200109419050381c08600864076158a5a9012002024000c02d0701080003810210002c5a0390140f05480003001d40c0d420f8005c007032400e424485c1c00d2a143c104c0c0c045541d800760030300c000081c1d003214030b09034080d42080d005107901004042c00360140c800601218012490454500321a18052002c1c0054901134000c482040d61 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 115135413 1250 115134163 115134169
    0xc030803060406080133030503090d060e030a091d01060509190b07050106030b0c040506070f020103020c010c080702100509100e1207081c29030a0203060a090311120a0518130501030b06 81
    0xa1b4901014003580c04c10002031141d400d104d600680c4252107000000303050140d14403082e045800860304140042c04400040040507109104092048000c21104d00d095250030b0002d401031141107102030150380302c0901801c074030700a568644010540030440d44e43d105010302d4998020501400200d40104d440700100d2100d5601206a400303540016009615000c11500c88942844408004a0405800300450030008078280210328400c102e40e110701c4900d0a003035201034241260011800707c51403500c401c1000e00fa02c001000001c00c0340306000068042c41d440034180c1030110700400342c1715004000608204001808008003d40d05a0403050050720711a000520107036481e45a1900541c14115814240c0c1d84141c00305428460004045981d031854580c086414000c08642c00143d45a4a18007001416000175080085d10175800c05801d810b000c0d4042030f109402024940010000c0115048801040c1c1c01400f03074101c20020068050f542c68060b950f4007070b06003404110355a5005c840401c0c3c3d241 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 115136663 1250 115135413 115135511
    0x60f1003030903020904080412060903030b010201180212032511100806010e0f10020a021014030112060b04020309010b03010c0f05091c0609210207030c0308030604060801 75
    0x1a9240e40c980780e0b00352458003040305210001d030095441c1e0804110000c0c15820f010701e0504154030481c40400c1403085400c02800300c0c0d00005005040d0f904020040c416110480c240d19002c50341292000c440b50711081c1210b10b98000d6050540030f06490425030105281030500e00c0b110315120309444c2c501101e0314824801040c000d402c46101044044010680540c0501000700a17580d0241c04880301200c658000303244d142144a2020150300401d1101c0d0640c206548188100020340c28203c410b039500c800c480ca441c0c80144900840e44d48188420010031599411000070801c00070400d6480e420b180480c0e6000344212290b151080d0300e00200b40302c07610b000320301050954205031521820b008005040c807240001031501c128a80c41c141d00c400c0005001c5200301c04056000791781e0f1b5159414a9284405030400c1120200e0555000b40070410018192000610660794450341c526220749070040401c001e411150000050340d428010034280c0001021100f44e80701054051404900414a014036042 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 115137913 1250 115136663 115136669
    0xf0c0301110f03070c0506070309020103060b0a050906030405010f0504110907030b0a1205070504050a050907120b0606070318060f0905060301030804030b0405070308190806030d080601141b060f10 86
    0x40c4070300380411058007940e000510360100c00c5080ca0340c0580d160307a0f01d00b4103044c011203030003001c04d540305144415564948562006041c2d0302c08041d1501418640191887c080c40094a1280b1300000002d401c000e000c5d04000441005140203002c07504152614211601490300c0b51805515008002900c162007801a8060004007411861215040c400c6d41d00d411452407005a41c01c0c0b00d08100020346484522407a4816804520005a40c1c10302d20841c508006203030303015035904100040302d940403070707440170740d264000c0d00480c0c0e00c0d9a640d10900e001e40d5040c01018a40301c030b001941000242c4103400a8401c402400e06a441c4440380f9101e01c10000940003c3c0405032043d80c05100c18070000d082d41c0031458005000300b0031604659605e96403140950301a80340c4140d4818041048000c154102210940105c0c040703000e020209411f007801486010300a01c41410044e03508980000c0d4080101202c40c403801019802156440c00140195502c000b0754556061040410000b9001c048044000080d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 115139163 1250 115137913 115137941
    0x4031511090a140d0b0a05010602010b01110607050d09050a030c020f10050f030403021912080a0c080a09140d0305040507050118060e0102120a020c03070e01050d17090405090f0c0301 80
    0x8182c3c180b44107242aa000c600383c15400c8403d452840000c110500d607140d03c0742e51b041c04081215818548000d0a50320072211050522000020440764000c020a00c030340e00108514205448003001801140600f500d0840a0464010300c0c03041c1050560003008400780a00079907a90140310b224405008088441d888003070000307a8148240444c40a41000464005010b84100e404225100600c140e0b5140c900008548880c2070703d107900c102941007843d0ba0307884100b00500b0400703405400c4000c1c0400380c00401c2e14140f40c1d074500c010001c01c00c0c80c0b030f0142e00c6009030104590b075002d102e150240c020312080e10140c034288150100056290b21a41c3d8240502d0950351a4030881032030070308151030b100c0300e80800c94190300440c0302201c4104210f0014180001c00f076401070065003036100c01d242c00c14503241c004c03001a0100318014411078884185e0401c07440d41c01172220590310109840070b8030300d00a280c201c5030300c04e0070704090007001500002c0d1351070311401c208240c0b11581d40c940304040c200c680007580714003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 115140413 1250 115139163 115139179
    0x10f03020904140d0504090c020d120e160b040f05061614150a021801020a031d030106051905090711060402090601020312010e0106020120030105060702150403151109 73
    0x401401d251036110340091007000c42d010000900c0d01c205042500d2482200e001410100d02041071007041d0049081c43c0c034940c0050495203098007402050120102010110380b41c85000d501101441044240300d4404d51a2000f0500d54681d1041e04040d4054840c02c240d40160300000b044c2441c0c500112510380c1e61407054106100d5542d51180000384d1501819225401900702c040e01a480c40f196140c0300c0c5102e500e0060b61a40d001a950001d100300c3c15403c0d046501c040b80b0840081d421200b00d00241c892042420480220100024090145504542c0d08000c0a0b010031071910440545041582c1040300c018240341d80342d40089500d4010321070200345540c40040404c0150030081006a089a41171054a15016000c0c3c40804603074000c0e0301000100403100300410080fa428420296958002c2603140105008150404090700042c0036652098100180c4002150754080486032100600b01030780e41c5460340d80c14414110500241000d0503141003813201403e200160045801a01004044c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 115141663 1250 115140413 115140419
    0x2010e070e060d08030c07020109090e100e030c0f0f060106021203010302040c05040803030f0702071712030a150602160f030210031d0106090b0f030601030b07080a0207080c0321010f 80
    0x2580341c03100649440e40100340c2550010206084000551140d0a40080140d484803107200041c41041207a114944092900c0c603a80d00d00398011403840601c0c40b09090200350302d2a00d401300c904500c0b9400303001080e4402c1905400300050702050700b1070115181400c2e2070303090381d94610a90300c1c1d44041c60300c0e0030048001c000510061825034403016100b0700c5450302e030341401c2d1600196461503000b9030714001d41c000c0f80070403c42c1d1071303074100290005040c1c402c090340d00442c0418100740d41c0e1140d030b810750b04005a0220024071f5211f050b600800e404c0b9203c04629403569a03641010b516080200049280c500b440796012480480050440080760b41c050300340e0f030007541051811401020044c100180c41c2042d03040c440944102401070b8000f8041c5101c0010b050312180007040400d0300041c1110340079170000001080440c066038500b80d440407503410208080e0361124011310080c4900340006116080c00704400081c910000050041c0300e0320300d0b0310300c040d12591000b00302c5012000d20a100c400d5006000c14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 115142913 1250 115141663 115141679
    0x15190c080414010f020412170a1b1b0e0a1401050f04150e1f05030d08040b04080d1b0806030a080307050d1d03071a0402031b06120c0408010c02010e07 66
    0x2401d0300a09800002840d0299003410020390f805544911f004c203c3c03e0f0101018490561104400a0290003040f450002030b1400070308000b20308021002000003034407500b0b042c07001c6240422001a03e90b00c1103132120f911405880c02d0845c1c2a039000007803510f8041200c030041c00c21a103445c16503400802d0106901407080c20803000d80721500050248010740354000558503d004c0c0700500a41c00700f40c6090402d2400300988000604a50109100794801501d000c10150010030940e08250040c5143d07070503a5550401c00500d00c50043c040c01e160740790070034480c0940b04c507425802001c0041c0d40d40700c00b16180e403410103641d0b800700d02c000f40c00b40c4020800b02d68100d02810041c15011000e0b83d0104180078214008144400b044100030132582000405000304030040350f030400c030a04c007102c008105040030707008290307200703c40c40720303105500805420034215546907010340d0407454141040410701c0c5419520030030690444d03c41d45c82e4543c04c10784001946070042c01075a900d80e022800605c3c0c12880c080e40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 115144163 1250 115142913 115142933
    0x5010b07020d06020d0603030509030f12070f0c08060403030506040509030901090b0904090f11090601140304081e03130b0115120c140a0309020a0506030105010c110102070815190c0804 81
    0x3c5510315420041e9030502040d9006e0007005501035211030752140e0888090500b000300480200e501a04404a0403101b08044003c0c2c0301a20b400c180c201092040a03e0300c40b211003c0da400001642c030450040000705585138002602c54081074406020700c0c1c5441d41c00c0c560300c3c001c0c070104501043c004202030000f1301c3e860003c0d004c03159004101007801d44403512011b5017104915400d60f80e130040f51001c1e800b5800d02d04465a04514286020304d00e07600c0440e40e02c2401e01000c1c00c010b090503000200600e40c400f103411488401d0b0f444001c2c10340e490600f20007035015141d10b1101120340c00d494100014112a08400c05010348410b074444c00f10442c0100305100c010801148030380c003401040c0016405030030703580f40030707108104403520f000909042c580108070540e60654130052080a0820040c08640d07480900344165aa200500000c0d9a414500503070070580d06400141c9288200703031240000c1140311035014000c2c003500e40c407003607182001840c0c801525072154040300416602404540002c1c00500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 115145413 1250 115144163 115144189
    0xf0617091f0f0e03040b07080a091a0c0d02031603081305031b0c0f0109090b130510051305160809120d020c25060518040c08041505010b0702 62
    0x209651030049101d1000300315031a9008241d0440b07988041d00c1180b40214400c044500b9503d07001581000c0c5042440015442460340c000c060321004600758007002c0c012545640a010080030718440140c01f03031907074510ba400444c10320703401e4480d200103210304900100840305a603c40d02031001c008241e40e00c094071440d501805898a80c010603002f007012078001c0c400740203105041e40c2000c4113051000c131841d05d0b15890011b00c610410003d5508521a82c00c14440d00c11240c10300000f103115170100c80000e061400440d0ba0600c0c05017028204080c43c03000d00c001c007065403003c03180c822049440c17101c400100d0b0800c40d0355004105046c1c440f05400d038000c455141c1d010310744408961803060401d08594542e044074800f400d82c140c0125654403110002c2c041d010350200c00003100c8041000256882000100c98030541091100000783d85031030b14510b61030100c03801030280040c84100c4003004001d0101ca421103065451810380c60766040d103c2d035035004250488541c600c0c82c0341001c903150204900c00440c0341c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 115146663 1250 115145413 115145431
    0x60e130504021c0f02041103010e07050406021e0c0a0312090902070b01030605060d0609030c110d0507060f02010608061e01050d0b0604051e0405071502010608030f07060603080f040f0f0617 83
    0xc04d030016a04e500520710480c284210994030b030752412517501c0400300d01600b81d200b8040305100900c0380340d13170000e034842d0110031401743d900340400700f00300ca10b0030480c1013030b01c540d0000c1c00407002005020a8100e1691054503a6a0780c00805035281d960304101c8c065448000d00d07041c80d0070010400b007201904803940242d8010402044400240e4400c0304032200520708402003010501000140101d40c021008500c10560b40c074403108a003640c640d6100c0c101401898180444000d5034a14a0702c02d620810240c02c01c0f0b0f08032909810560342c800c0340c00b90402c08140102c25254000b103110b05001ca000c07901d0b03a0348007440008070307210001004094180144180c05e00192043d05c04031152601518900880c050005002c0c007605004503100395015417100e003c107581c104001008543c1000045890151103460015183c010310b10740a030107000d0f941d0014011000c0480c000350500e00c9030004000301c98001034004611950f4640c41e4042da40503115190202e03c44410b100500c0d5108003506a02642751 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 115147913 1250 115146663 115146683
    0x20c06090f09090f060105060a120c0e04090b010e18060c030402010e04090303020717090d1e0b010611010b01030c080601051303080a030209130608070501111204060e130504021c 78
    0x807000c5044000103d0300b0074060b6100b10944041d291003402a18050007065440500d071844420f8090509200d11294803152940c5900d042c0003180715445d0350010341c0006005004c0d5165a0a080903902006c0c01303403d059210003400310b00c039000340c4c0e41c107940d0310007000019100d41c7e03451613085107090700010010381c10304c920803c1282c081d540b1440380c111341a220361001600c407101410a0501070f40d1082d08078002c0d41d41003051000568030100d004818650081c14005600b0340314020f0307441080a041c0c0200781500010020035116080201c158581c00200020019120700343d00440c19550000c28403004100b070840450070651007540103180441030342c58180030b802e959541d10581640711112000001b6804240005145000c010754504403142000520005003046c41c2d00c2c4e2501c40d1031141c42d051014014003020001c000340400012900090080c0392510f07600d402c007170702c2c04014601480c40b41d4042104504906024410503004a030090302c40320075100c0314000c40e941e81000104c1038a0071600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 115149163 1250 115147913 115147939
    0x603060a03170705150405160b0313050a0b040302070303020609010207110405060409020a14011205060604060513082e020c0c040b040207060203011706010f06020d0e18040303051510020c0609 84
    0x4000c407200510200680d000c681ca040e01f4014104103107202e651100300c0e401c0c00c007000819104001d4130341021041c152076244400d1803038178900d0442500d100411042d000000c100c14141c002c6501c4c41124040d809485d520307075074007400c00c8c01c0340b00709030b401401c2005500441c0100e0500794400780d405034028000142d00c0140750009404074a182d8801d5158840d000d60910b40b1f540c9c4908401c442c070300049000e02c55414581d0000d0303001d00941c05000f04000d00894612141400841d142004100c00404e43d1082c0f0040b0500007190117496011480c8034240d41051800710070940300b124070501300380015100101d078001c1000301506c5484605544240c00703006000225070140300a500800d100d25205e02c8400c91442d00609103a0140d0007404052402c45c0108036070794010401c0800410700e841d00305c001c00580d00006070203854480c0b5203600341800c5030070001019010b030f0005015841c60304c1950716107032500080014000e10744848400503081813007024010304200c0040c150b0120000d10390208240c3c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 115150413 1250 115149163 115149173
    0xf08090706140906030a0608100b010207030b100b0703020303071403040b0403231b0f030708030a11070602071b08010b060a05030405010f1104060905040204061403040f060f090b060603060a031707 86
    0x10a60300f40c80717047c1d61040c0400000d80d003000700680b100c0c88200107002c583e844000207901c3d1401440081c002003002c0c0c0000301070884540b02d02c00544440c0703150310b481e0016030400079030701d81046940a000c01c00040d002d101d41401d50b401d036842194070183d03101e01c540e643e036821583e04956031340200e540664219060f40080c0c1c802c01503c90000350390a11815060400c00f66407408145000403542d5400400500c804283c1110880e82d010b030340d90001144056207160a01103030701c1241c2015002038400720b6080308100e007200844c03030325400303c3c076032010100c7e180c500c0d0034220741e21400c1c403e90082e010442d21350481c0c019000343d03500500607000010102c020003072034800c0d5400d60581c4400e03850000b8051000ca85c010b2503c5000d042c054808504080c1006ca0241500c4140c4001a01071400400014100040f500001d00c66aa00201c1404a1800100410b0180240600454207142c8440c0040e005040c54000d480c81034900501c502c1e1a90701c0e5413200b05420b00c0360707008074100b45010031480d00810307 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 115151663 1250 115150413 115150417
    0x4080702010518120f0c1f0f1101020a090e0603070f090b030a060603050a0c060207151d220b04090f06020309240709090c0210050601030920010f08090706140906 71
    0x1500e184c060a6540b01071501c880c2025005100309119a82c1800044404507060202000c58080c2d420321114014a180045d90f240b44016010001980002840c1d000389900c82c0d0b13410222100c045454845460350020161140340341c0c0511000190100340030080c0d420180c000314a5250f02401382c4100d140c5a44980003a591243c00075a801d90082960304c0030400e4150002008258a2014010b080d00700600345480841c04440c0c07604001100044c0030807806241ca0140032035100130032060314004040558a803680b07080b04184501c61034021219201d09090003950b4089920000083c40c660003a91480000c7d04094505c02c1c0340d1003070300a6220423038502c649040c0c0d441c16104c0d403a11607103440c01001740f1032040c603001680310500300590008816000110308010103401c0001158607903c40d00100c004091405018140d06503000c0c80c4203000550180210821030207130707501b14414109903019130b51440195503800103940241400c102d12403258110100a114007044245003555800028a143e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 115152913 1250 115151663 115151689
    0xc110f0409020901090b0f011b032f0109060e03090307051905030d050d0b0a080c040504030216090204030506010e13080c0a020d0308060103050708091b0f041e0b04020304080702010518 81
    0x440e500d12400d00b1300e141c051f413a200075000900e4141c06541c0300254141d5801112500102070005000000028128188072000941f00c100c003aa100d00f6041c1e500c00340600f0440c44251001d0703140804c00e0204105c04001c03145041c001800510900703180a05000200030a40d14200140c03482c040301040b80d603002c2c040601249019525241c549500c90140421104071348046803150488450170840f42a000c2402d034401d280c00ca60000d6241e0726420140c3c10030740500c2a504c1114446c100205109002d036018106a9000b0001c54400e41c0c0c8403e00d21b00c0d0403200b82e07200c02c3d1414a000400b00015014030080c100d80065005540e042a01540450203040c1c1d0300008401140790001001041c0d6070521a15038020b015140c894500d00b08001d01584420000700c000c0640061040b5031840307910790201c90601e406010b041080f03034081300603080a240c80d00c110242d0020703062880c80c0002d45894025640603030f4100e60324600d0041c2a5005503000e03846039805410380180d50703004a40b10b83e617011701c85520b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 115154163 1250 115152913 115152929
    0x621020a0503010e0a1406060705010b030106081005010e0f040f060603050a0b0906070c02210c03120a0807020a02061206041508060907091b08100b1314010c110f0409020901 76
    0x2ea5051960560f805034004010385c0d00c4c84e00d80481035011030000040c0c03542040080c0c900c945e46204a041c1940505490512550190700306035000650074030019400481120001c02080742d030341c032100d02413012a025101d0384590705034200443c0c00f20b103411080e4080310f80b050f400004e0403980e070303520141810300c00c400030307200b01100100300007200a0601c21581d2164507071a0101d09141250b000800000000046a0300b119145101070200c280030031209030050030040440e80c1003480300281c0c5940364450382603c000200701101240ca4035000145a8444a40c01001e40d4202600c0c015500403e603801401203510079280d045160740440e281140001030250100604058a058804075152500e241d00c0440c18600d07201503801d540720541041d00c241d05a0303142103100d948441c0020303c10700403240c000b445590341c00210890f4554400000d00c04035420300c1c011080400e2580010348035880d1422026203405c6640d1141c204034903003a880300c400c1580c0100009403102c01a00030904600cec090f00a851 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 115155413 1250 115154163 115154167
    0x20a050601060302130b090d0b060a0806010801090c081605010c031202030907140d170f0c030a020a0303061208120601050c0f070e060d1a041a0426130621020a05 71
    0x1c002005d200d4500600340c4c0c0410145084400c1c1c02281d40d900740400e0180c031102075180450541d503541312a900081200700120380ca1540c650000500070f0100d440220b400241038000083d4090b000300760030b12101d01c1c1000021000385400015160380d1000030f0100c08000f10b0101c001c44850b01480079502601c1c010000f45002030800f0041c1d03d042001840b0541715400070b6061200195070328020141907510164003c0d00c1d40d4140d91f0101e10341c0948640c840e40c5000200e200d0017483d07800034400084500940d8240460b6542d2074102c00104042c0300040c00307000e0100081c00c014440841c4040e0000c0042c5081458140c0020708075050034980030940328560420002003244400d40c14109410040c21902c181420003517a880301000001c214146902c0d8010170009028408000c503107241891200000c80c0315442d01f0301c0c01010f140c4140300e51b4103524021064840b206034000342a03456400003c44080741d1603040c04002c0d184c06840c403107000981e0906d1600d103800e00305180007030f050258580d140c0079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 115156663 1250 115155413 115155427
    0xf09060b0a0c08071e120207050f04090f0506042103050f070c0201090312030905010605030705061b100f0504051e1b03031608090901060e0a030308070e090103050601170307021f020a050601060302 86
    0x1400c060030345010b03d030841d03000320b000340b149075115070354ac4032181011603000680ca081480c240000c815142805800c078004c1c3c4080001b070004030719100130800500c6e154051000f10201f400d9040383e01c01d03205000900403d00010710101e008200b40c1039100c1c014109480260b54071394030781c000c1501a40703280c00002d40b02c0c0508003c10109002c2e11000e080114050500176090034041200c40c01040c503100ca600665404445000d0400e114503007000b50401c2c1d041c0000c2405001d40400341c02d003560100c405100b007000955444c18410842c60f8102d0384180501f03408a01110313455900e924a002d000c1d810702003040b01c0a0425001d601c01610350740726640b038580310a007543c00c2040700081644540144044850012907035966020054207480d41030410b02540c2d00e410200300c943e10745404445400c00240c00c0040300b40400004c12074100c03000d42c2d100d0050003020342d04068a038050418000d4100f840012207108418106240b19400790031841100c0c40800251240d500d042002e900444c04254002101 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 115157913 1250 115156663 115156673
    0x40c05090a0602010915050c040b1908010806040b0109050c0c1f06061e081305011a030706030204050d120c0503180f0406061b0c0b0409060f09060b0a0c08071e 70
    0x144001c200b180000c1106a2568884008100c0440941c000c0140e813080054032212160043d2009400302c45503481d00c074000c01803d030703004d660381100700400300f10300000025429400184152181d640110790b1005a40380c9001c11028003400791111325403400034030840005980c1080481c0481200b1032180b2214000a490f207422200c9070b030011020000a5100e07452401540840701340c84050501c0d0a452594a074020f4500456402030001c2c45542840509050b542c0c50b110905040c1000b242924202503603a0804e41c100e00c20b038842c680d0050b00b80450340001c108609014010303042d40381899141458a55151800c6a11400081aa070400d030070700f01003a42000c860301310b42030320b05803800c001e81c504204010f8026105d8280910b00075105007a01c8042100300410040200b54103030708a138440b40c8031041d81014100034040c20701e02045042001604601a0154500b1a11070950007850822100c1045480c4800e00505072000300c030800041c40050610104600341410300040801c00219500d01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 115159163 1250 115157913 115157929
    0x60b0f01030c020a0b0403030b06120f01090c090504150b0304080a0809031602370819020d08070303060503070b0d0c030c020615130c02010903180b03150609040c0509 73
    0x50a040600d0b14050b20103080c0c0000d04002469040326203e1159500e901d0b086000d040012038460304000c0110b02c0d1f000c2c0481071803505010b013140385a181003507038880c81400c040f01c480305518030000e0340c038220800c582e04046e4000a15034543c1c08441d0001925035480391007950099138100e0f044200000c0b118041a8081100e580040c00c5c400034510706410440150310902c80c10304040e1141e28603000114884031003040320403043c000200010a080240303041c01203526030500c501d0040d030044420028041c25942180000359034010141d004200080d00d4402d401c0d0024030044003410750311507002c6211394080055200601c000b0a11555a6034100c0d010b0080e01c1d040602c0501b814203040030003200326000315031550700c0b40f0404130b80b2802c0b240d21400109a6403190010280140c5408180035081f41e0641210031014060b481d4100701c2c20310604240001c864501c1030044d420810300c00300d201c103c411048000100001002c950600c0300e00d10000b001c580802000e800072690003d0404001d00384038031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 115160413 1250 115159163 115159189
    0x90606210c0608010b0405041a18060102210307141b030403120305040f140a0b180c01050a020d3906150b03040204020a0c120203071703060d030e0f0d060b 68
    0x15100f981c6514180700e060550107103000e0103225549404222010980f0300007511400000205000200300015107140f001d9031069032144e006004214802c41d44035410302403818240d00151350f1500e19903d81c2400c544048803c8100c4140700800c018802c00540c040d42824050131100000d50f54441c514a4a140c9045401d07201070141420170082201180301c0060358002903030089030f011a4004604038107410702c444444000c0c420f8800744248042141104201e82d00e034650441180c030400034110040d5004c1c00b41d140c2440050b071000b80b07007540c080d00c035042c15201141e8002140d00d00302640321207281d107600741c0ca480480c80b6110204803000d0110600035400030590f0000e8240825090200f800c0707007440003c001a001c1d035000141c0c1800300e4030900c2c0305a00305402168241840303503424402500c960000d4000d41c4d400041c14103402c2d00c8903c0c0b030212030190710001c0c60310114400954042d9913007191181d05075488034016200f40d00980302c1c10304040e01548070b940b000480221020800c003000134410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 115161663 1250 115160413 115160417
    0x50409050a0c020316240e0105060102032d0409050103030503060109050a0b0a030908041d150603071b0512030c0912060106020c011d03070e1602010507080a090606210c06 75
    0x2040c82c1003054000c01124044c00881100344c055464509040020205540f15032030f16032440c203082c00c00788800d603110010800440000784101c1e00c401004a94030f0190b504070308507410300a100c01800c4080c41c2102444220b42d010b460341025612288a8206d4800743c2c0150b001c264000b04000300c641c0d0050740e04000d000116444c56016080035118181ca0180c201070170b0906030354100200c240b041d104282d90081002c2c41083c01ca038a2403115500c028802950503518244900241030000c0c9481c41c2624491012a610007441158543d041c500c107560541040e1101d026210116a4840c00300340118444c40865400c561f03100c070150706000502c0342c01d61070f03d42036410440c0107000e031030760200b002e0b040d5039003d00e800728010f101590304440400c07800501d035906100301c1400240d8000c0514080f48564000d00c1c1c0510204001201a0700740d800032038100c1d0000e40340e100010642c910030342c4480100b42c002d500015100e903c0d001240301d20003022088950007000303001d00104116044100d840905858 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 115162913 1250 115161663 115161671
    0x80a060c021e03041502011b0c050709140a020307050c01060f080c0603010f0506090312180a0509060306010303050a050904140108070b12041101050d0c11070b0f0d0b0d050d050409050a 81
    0x2c0c40426140e024500403241d00c0d941e89084406010f00c00d402004000c400e4904003540007210751800740803220441c100721070b81e001d49800017459260622600701e04804058041440c4d03590304800b503001b580001c0c10941403000c28405c401400030248141c001070901c45d005508110305010a4514100441b000241304602c100b00510545100d2100b00088850641e20350351a0000400001e040410304d85001241c0b10300401e0324144d0300c038101d0400d44246025502800c2c0e0341d0303e41e424019040c508440c25a01648a50010000070b8400d1004111050092600c5410b0086400018040d10a1344403014031103108000103100402c0c00340072032002080d168009900d400215550268007010007000a0105518502250401d9000e00108c52034031140500c02c00c100084c10601420b032848044521425101c0c001001c030741032509070300304c418814a504186091030b40c1039001d00c000c0d1000c2034403590002c2e00c204010001610070459540001c3d00c5446441d1610b082001c2d4104807240200142007040c20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 115164163 1250 115162913 115162963
    0x5030a02011e0c021206010f121e060f060b040302040c020d2109060f1b020303010b040b0702040b03060112030305090a0b0604051515040602150c040b03070207080a060c02 75
    0x40000c0c004600c00340394101d002c1d015080001e4907038052800700a900030307010020242c030000011640740c0c16503a921003e2600719440700024503091400680050034420309148604030308000238040c03003203140709103070224a18a41520a0040d02d200740d200e1f092005002c1020700451400d4000c004070304c000351004194042543c10b008180c42c0200e04070412181c00c81c01c1c01003404009420100500b90003a005001c1e900c000c55140c0300078802c108138082e039100e5030868126554400300440e8100c0d0b1250700b005081c1828004851107980c014402240c3c071580c2ca4607840c408d034505020841c001d000300c5000c1850441e1b1410040c042d03620003015400c141c2c00c42c0984100050942e182d0580028080d02c0014a43d540e1600e4040c5a891b4403070900d42c0481c000500304090307556880100255041c2e582030f18504060011109060b101c1920000e044c01e01c2408140034000e090005180d01102510484902d543d481100070301340b24640c0400c0d580a0b4841c0701c4c030881030341c041205040c00e1070118448404116 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 115165413 1250 115164163 115164167
    0x914060619050c0c0a031a06041118030705040504030e0a24080621030c0d0206010e15011211030a050612060403030213030c080d17090703111809010b0a05030a0201 72
    0x301c210740190500c4004a000c0080040410402c0040e60010b803c8040141d00d070309003400644004e000c0e455121300d001d40041c4660401c0e001c2e00c00104080c3c48040d0800d00b0360700400d03c021031302216083e0940b2641d00300140740d0307442d405036030f00460084c0c69039403910a00d031090040d18010707038214202120360071001c410104401040310100c02e95924020001e80c40340b02c000794400e146480703030700d10180c802c1481c0581e03003201200422902c00c1a104980c030f281d591010990b2226400d02c98103090007000c0d400144095149114814085d030149000490301803d044010b003120018442c034542c0e0328001c8108003c5103207500c20180c00500072284256071101c0b140c840e541d03680009000800f0590040f07140d0708000408186600030350703440416403406546508829903114142c0c141b00d00000d800b56140c09035140340c240f101e4004d484030340117800319509640300c107900a034001e98020b0b0021480c0c4076010740344250014083c0a245420700100b15034424108221407007407950440361003600203100380310040c3e0f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 115166663 1250 115165413 115165447
    0x80703050c090a06080a1101110706170a06080607090501030b040506030a140316060b040f38090112020108010e060f22020a020304080111070c03140c030709140606 72
    0x1046640360b5150340c6183c1480f014005552191829104420040040201e10a018850b0040030707070380c285a554090354210b5640419228080c041100781c844903800818201070154400c05200d0042800b941d50020302e840d05100301c03110b400103884070300305015542c0c0c1400340c2c003000001150280300904143c0c0020781c8982518500503e2440d104815613a85201441a26010240207a103c14411001e0920001404024800520840c0b030302c01c00d4048442c0e10b1252000030200600582c102c5060069031000c150210070b40449020400700300e0301c400f0b0380e6642c0e0842c06412880d83e0301c2c1500c0d850740700240150310103801c9088549401c1082007240d8980d000c1803041c560f03007150004c4104c1c03001d038000c1c80011100d02d51000c10302d00000706c81c1a06900080140221007040000300205090302c650200140940b1600802c41e0381450030801c081813a48000d803110f00e0510090343d004098a03000a49030039100d60240c0c0010303844404945039184445040380d03100398150340c120b2410400c142143c0c810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 115167913 1250 115166663 115166683
    0x33020708090108130804260102070807170904060611010f0507050d1e0204030c0e18060402040203060117101508010819030c060e0105010e0105013e0318090108070305 73
    0x1c80350354001a40e0031004c01441c20030ba074102040c81d6071140c0f00c01c05aa000254403102c403a504040101c0315509440503c215851181c12011031401d0040940d1000504044600101c15802d000c2c00b51140581c1c80d449010b00038890303921264103035213000903941c2c2034403160041d0015140c0b4190800841540000450b002e48804020019401e000700c5078600260800c260b660081c2440402d02004000c90360300e0107425a02c4251074000c1656a02a8842d00b0700319480c41c1f4032035074000b90b020900500341074028580000050516503403018049001d1102c414007160b40c0d00b20182e0380c00301046850b100044840210303130380e440c0c01c440c03541c1414042681c074201501c40c00c9002144010183c10f140c426086002a140c0c020418442e0560440352280640302c02e000b5080d400080f41c00000e125801842d42211b203084441240303a01451a426102040d00080c0c01d10042d07032064035419644003414401050560398650038520303442440014081c0b40001600310540b0f6600140c010700109100040110768 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 115169163 1250 115167913 115167917
    0x13020304030807110f070e100803030702150402120a050c130b0108013f200918120708130611060406020a030615030209040c03050112020418330207080901 68
    0xc03016a513514a0840c40e40d5020001340101500490a5441c80503c280140f5002c5080c14440381c0b10140c1c0c0b605c03444180c62940150344031f024134202d100c00407180f20380e00500090021045264085610f030404000207000c5410b60416003404400345480d50b00d0301884111034034100f15003000d03000060151201070080145c4501001c1018542d1400580d40340d0341d0180d4691919500007415036020000c194000301220540c406026038a20703c0c024075000b0200c01c170002c1c43e00b500380c2c071110021503244109401a03035150041074600b070300504919001741a61813103280003660b40c0401d04007440149440b9082142009060b2080c91061000001c0309604250804030061307072490048000d0303000306504da000006030441442d40e00000b5805034041d215200d010b540c1880b00240c90a0210101c0341d007400740d002c2c00c5c00e0110303451025003496401a1a804054920302000d0301c05601c85000c60340400e160070a1814a40c0d034502c0603815040010207261801c804103504040c26595500340c0d0780506da10140c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 115170413 1250 115169163 115169177
    0x90e0a020f12011803031a10050c070902040b0903070e011518051306060219020319080d050103120f0c030215150901080c030d0918090218070e13020304030807 70
    0x180707a03a900301c02900c104000c680200075481800707850411000340050306402280c9412803064801c80060011780701303640020001d140100b1201d105031099001b20600c901148100c01c00410044050310003000640742c042c1900c0c0d110481c05c4101460507841d070300580c64240031a801088942c85084000d841c01100b801e00c52506d03910000c48801c0340301c0c16032020340d1002500c60141e0400006070b200c6000e80d0074a9098030403003001410402801064200000d426a000000341000520710169103940b01c0d01c54800c0034038042d0200401800d07900203800c00e44082d0701d5102e004804540041b02440400644c0c01d0608100d1555180651a01ca03190752105c03001015000041e001a24101081002c0b08024103c11107541c40c0d46600b0f55850501c0c1186001f03218055441c200c2d07501410482085604805010b8000c003441701c0c0c1b44000d040e142e0750480e040b1000c0c1d0b100030804070501c2c86240c0b0858043d510700c00c111a1401c1000310b000008640718141da8810030502c00030a1b440780c402d5034068011309080c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 115171663 1250 115170413 115170439
    0x1080d03150509061203030f0a18031e03060801060305010c0306050a030309030b0a020c0a030201051f0e0115032717030402100309021201062309010f1a0d020c0313090e0a02 76
    0x117140e0704810300604480d00001080050f40803040983c1c40c02181103810030490b014240105400c000034405000d004a00030403a409006490000352000081d61454080f40075992443c2090a4030455001211540d45810b0442049a810710890006180488558018a01c4c5440241a40340316000141059a1200002d1003102c551740444991001d40001c40e40c0d44266824024020316090340c00303032003580c41e41c540780010100e020505000c2e20b10341d508581107a440e060074680003001c0f0b0f040e000706240e10348505480008041100c4980c2c103819145035128020b040c94884080c40c82651005513442061090001503190714801000e00896801c1c0003910610500000745103c904080c3c01d0b859608004020511240403000e9240c99000388001c900340b06085c9040081480090051780b00d030b4100c1c0c0d40c04001001c00088100d02c4115040000340c51324030100130711010b981c0f068090100300e81c4001580d000140e10013854800904035210104a02c01c80d00880540b07034040f424010344203981301c032900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 115172913 1250 115171663 115171669
    0x20903010209060a0e04050901060612091b0b071202011a1002151014030f0604031b061b080601090e060105211501200c060a020109060f020301080d0315050906 70
    0x10b40e00321038010b00031902c40d21013180041426681c010820b00550070080451009641401190180c9080d07448041d108030510504000400c5a6607080c0c0d6802d101d4001980000201d103403000c040d0500d806000e0756038099041c58403405044042540c110781c0b40805070303000380d00c560160301040241220380f807082ca106408105c1c90591604401012071101c01c0c14000070840030707841201100c004200c804c50300c3c46000205925182501142e01c403079080080007a000900c0341a0403c040d10304401c00a96044031500c038102100d88008047e1001e544500c80c0c41d640f00d4200c1c2c2c0f1564460802d280400c00182402148581d002000c5c046606010010545402d41051b1100742c42c40c02d2004060404035146c96281e42e4010b003401d40006010402a007521b010b20011610703000700000e00c0b800180540564403047c0b0050ba405182404115561100c039007001031858018801c04502020000d6200d50400c4c1c001030038140185a2401814038103210b00e0303525403182c00c118048840845466080b0341da0030f004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 115174163 1250 115172913 115172917
    0xb07140309040c020d020c040216110102030c010e06040611070f1112010207060209010f080f0c090d050f061006050a12050601020a0519031e12050c0d09140d080601120209030102 78
    0x441c2d119007849025420144c0c0061000c104200540c200e91461080360140012442039104c0f2038901d851290304800410b01400c18220041c406104584c5062a0303d036100b4211a8000301e0703101700c1c2c0c10420a1000380301050203040d26141000c80c409180c0f10041d5603846121082d41c40041180820749800c044c16680c00c50b0300e04e0b000c00e05000a65842d4401e15104000303500c61410300c3d010401140d1000c03ca41e109000f4544030f521091001c1a09442d5140f240595400066003568031107080c248250008205001501240300d580009082d0b0b4201400340750340e8050344bc0c1000d0100501488640c0d002544444c01100c03100c0e4000c80040d03140c4407000100e003040c3c00d00b40060801d1007003500c8901c0901600c02d4044205020341c6c0c401e41111051308800340800700e8441031000081e201e4080b80406c49190380910b400c03440c603941151500c115128860252103001e00242c40c40c10005503c6e600e415818422140c500b0218600b0645074034011001030907000024840c100780c0c0d54089411052606d00b581 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 115175413 1250 115174163 115174177
    0x3050402041506090e1302061209010603020619030f1a1903020405090d02010f0b010e040510080d0f030f0209090c030703060306060e01050f09190908040308040b09190b071403 77
    0x14903510019110715001d0000b1303441d8428071450071420000984c0d842039480240780e1181e4000d1415103050640111501642c101a00380328181d56112030003c01030341d810004056400c5420b1803500344418005003e01206d114100e02d0710702505094090800d081e10030881d04001d0b0046400105c3c10b507040d90b0b12090707101c994000940052602c020700051345000165420035200b16402403015113600c2c105501907656440181e0302185040030401258501078002c25400079064101c0b02409035600c060518104108080c400894032503440b000f041035241c019020700d0801b840e429032504100402103616071000500c0c161000310040b012960451003504000021908100103005083d103520040d402c0d45e40a1080f030340720b402c3c2d00041c1c00340c5044c444901c0b841201072069030100a01c400b104e840103050100011201c18600b088003100150490000d803002c0c0407109401511020f0803020300205044042c0c020103100341817041000800c14010458661755403000030700203035941200001d807031402010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 115176663 1250 115175413 115175441
    0xe1e100203130b04050904080307110a111903080301120813080105010e0603011a010302030702240402040b120c0d0f24050a02090102030702040c0513030303090b16050a0305040204 79
    0x4210246240d00001409951146120b8603030001c1e900c211a100a1045110f0190000480000030740421581c1010307660255288c00c1c0040d8408120016508240c0f500500303c07416903110f146080030f8289480307070900c80e003803205c10021903908503140d56401d40414810f50480c420448503500811a1004c10740c0d407442007654002c0140c0f1b4803188118083c010034010800700805280020f074642c601401b95040302030920360884084034842004501a500003018031040d441581c082c1140810308802030070107800d0a4a15a0450030544104010b9a032038611484c2700d4101c030300d84003000035404915a40291800c844a03200c1d0203145c0b50003450051100400f802c000e420340313a032171341c40304100c114600051208201080a42c1c1ca440101049000f668006170041e401884500b0050a10780e019140c42015828200d0400100040c0e1a071004401e420480000e17495980c01420015004030054000e140804404104080c4141c01081402011040c42c1019203560100c0c081d5240e80d0f001903250140301d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 115177913 1250 115176663 115176679
    0x816020117040629061e2b150305060a1505060f0a02060c13060c060204030c080d090608070c030318021c02010909090203070b0f0d0c11010b010903030e1e 68
    0x2034103000008101c2c0011300403864800380c40c42e0603492003031444110000c0c4001c081d2810a40d0742070030303560701c20300c500f0403200c240c9010803140307030418442064071585800031340450000742c031040d540d10250f641010003040700c00300c660300078000a200451a1684803505c020001100e58120a43c50107506540d40b019400c480001144041c2c0c43d40b540040041104075001c440158a030400b40044500c9a190081e4401e02000014048a4401e00a0844041c043c075009420141c40e915280d4405450741d003c0f4100380c1c468114124610b030401c000310010111802c0c007541341d10304400040d281e21880100202015520000f22188031a5500d8040b042d0b900908030200504415003012828640c070801680820000400054041c000380603100140d54041c3c041c000391441d0024840c25904031040864a10f2070900040064540701d2042502d0b0a041c3e50795060300001c1d201d041403c40e20302505441c100843d896050010a8008004500d0341c9000d0340c4118140c16810f00c2003618007090550140d02c1590 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 115179163 1250 115177913 115177921
    0x110307050a24090c0303020c0109050604170c100206011a0403051f09120e0411090303180a17100c0206100b0a050403150504060b0303120c1806160b130816020117 71
    0x5400144c3c0180d0b84240c007105d010700040c1005440500b8907105070350b03004c41c00b00f07c144000b602900e484046101803004986844102070006100300c442c0d4088035006a0003800100301c1c01c1911001c011000c0450018a03180c40d0450300d50b9070300e034241900350034214446814901590500707640150f1049800c00b0f40b06141e941d0306c032001000c00c1481d03400c0034840e5052134a01d92040400c90201d0b0303440030700107000310702c0c112060540f0701c11094048905c0380d00c071240002c0003d0704900003c2c80030b0180c150202a000c0c48600d01103000441d00510384a00071035100404102c900b00c1c104c1c0207241514250020705440314034086040b90241310303d820046c05a008a105841841c2850700306900841c0b003001c042c055044948107042d40ca001362190904581c001c01e003c01d022081c902c000f00580c540c80d200155103541030801061142d48030024a19400000b02c5042e4180100c60000303030782102c1d044500a1242d66140c940940ca40680d40600000c0d0300e9a4001300b08684c011650519460148001c007136440c54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 115180413 1250 115179163 115179173
    0x50c060f0702010b03010e030d050604020909070e0913050a0b040516080304050a0504020f04060c0c030f0308060a0e010602030f030c1b07080d03060605030a2019110307050a2409 78
    0x3000e4a501c00550b0804000130b4062406001d0140118a03c2e4021414030842001c0c5602511002c1e084075005603081010749071540320b102c031440c03040701c80b5200d65203850281d500340064168010421072001e5500d54842c8006440803515000b480c0d00304400030070310388407410054107045002c110500b0f00c4c0071000f000034110300040f000d40122134046907a001d801d035841050109a20502400c061040320401050001e50701511000702002e0194003d066400d4036595070f6041c4803c0010300781d0100342a0070420100b40350000e4808050301401501503c40d515045000e541c4c2c0c000c030345c500d04000d103001c4005256012002c040d110b4441c0a0792890003590a03020445840701481c0c0507032016405100888402c25000780038110444006a5809255a4079045c0720030041054441100c000444074800065290350f00c80600700d405920499244200440a0007601c1c030420700042090a03001803101e400030034000b00302c00d8801741c2c10082c00d079840c0203068061400740c0c00c18103140c0070951512202c201804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 115181663 1250 115180413 115180441
    0xf05132c01170f030301060f050f04030506040c242c1005030f0903030c040303030b0d05010f1b0815061b0712060e03091f0203090d05060a05010501141603050c06 71
    0x2811000341c40710200421007084d101d05c4240074100208905600b81c07009036120300020a041c0c5607900059003096165039440e0304007607003518143c602d11020300d4140102c1c0a03100c050404c04080f00105e414903099150060044d0b0403200300300440000e11084c24020022020003944017181c01000c40c00c0d9075400080281c4550000d58410300d84045200000340b03403650010032240034800444100b8140781c50750340c0c02c4003c0c5c103080398400e40111b000c2100e180015400d00521042c070110707190200d145441c46602401c440b80002c510f00030030400f034090007170410440002c050a500203480e1130b5581d6050502c085504003804202981c46d1090500001e11543d010b40078000040c890001032014008500886690f405080ea10b02d90108021552016a815850098080c0601401034905180d10b03080043c4851400f050140c846401920821405103501e10843c0e003d03003803d080a004605040394460031368010110300310250a00c0a1780f042c1414000e0f000d03a20f44d144d9006c1100c142c0e1a0a600c101090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 115182913 1250 115181663 115181699
    0x6240304031407030e0f01050409140402010210060e010308031003020d0312060501090602060a1e090804080f06010609030807020112020307021b0307181109030f0307030f05132c01 79
    0x3031a01e040640e01281078811110f5841e0550b40d003a055551000c100400c100000d40594140403040000141924441c0128034119603203090f0449a4034050001904100303000d0780210505280150030300c062091040440e0640350414592a03d03a614013004000c04207041d000658410b00014a07a001c1690000c0c3c910009003e81e1800d11a00b07039103c2c01951140240d02560001d60845000a441030080b5440300d46d1a0b40b800c54101000c0c03e5002950b011143d4070502524640c20002e000c2c07050076001c10040c11480f0514004000c950314207200101842564040180500800107001041d0382c801e0300705d00350942da030f554215035034202102e01030340e2965041d01e20b204825203c0700d42c24040c40c0c08541481100c0300401030030900741d5003420030002413001102402146000b4003505d501c40d10100b015011030340c8000000c42c1c2d65207071070a0103492207021004e000c0800c0010001040c094041c48813003011105010b900300b48007604195101d44a2844c0e1388040c007880c042000000381d02c1030040c480004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 115184163 1250 115182913 115182917
    0x110c060a140f0402010c0507030b010f090608032802010b0301110304020f030a150e0a05060106030e19030507060506010c0f0602030106090602030f0306010804020d06051005040e010b0901030b0624030403 89
    0x103250740521068084080448420151525003000107015500480110362080d11400c1518401078595940806072a02030308604400040c01d4414405412103200346c0b0060300d00840158205200840000210780083c0e070b0117181c003254460b01d08001c0d4001d40103943d480c0700c01070091040300c00d5900c0707910742e6400495051340f003000a03071900441401e022410700c11140d0405d0701d02a1204080703503208064050b131104200b8038031611400d203011070700912455001c1c040036500070a502104041c2185000c035101280740024010f050390782e0000382c10000315018030381d110101060303030b0fa0303411b0041c1c4441030008c1028042e002e00139803500420086d54025816141c440c0c13280000151a03400c22a941c0c000c094045810030030810110b032103980641e00503580184000e001101d44000355482d041691400e4410b110740200283c0c1c140500e29103405640d02041c1920020000d0041442c0010003088041c0700181c02229000007051003034450f50442e000062400e545030904600303800311007240d5482141c050380 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 115185413 1250 115184163 115184171
    0xf030f15010309052a03010e06040b07021203040303050a020c0a0c030b0903040b090f06040510020a03031103060907030f110a05042907080a03021903090302121912110c060a 76
    0x300a601900c0340c900d102d900b000c02020170501c03020101d025141108000030007005403007500c114a070303000d004000301151114090002420f00745403000c0781c040c000e0700e047d040d50841380e01c611141609001356544a41c1620700484c81e521032010303890092080c071080c41001d0050082600520051440a104891141040890750344d80c1e0280140c40c0c0c051800340ca8590541007005100e00d02d04050807040c2a04014101850256118005117910210110803005a081100c28005054241c0300b188010410414014690304d42000002d200c24401840c80d4240b66482112a030102100e43c4035080320701c640c0e4251a0b66505034200940250054442d012166688011000e091613541c000c52001d0035018a6031400c0c40842c1e0f980904540040c3c004030708250b8280a011a10700c6403051501010070b45880006d4002900c0c14001c0c180590114145580d070340810070419240030f01c20595000c81c40c645404011161800c2404010303040c07488001410010100c0c03100c2203884040380c014010485000204 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 115186663 1250 115185413 115185451
    0x40906030803060306071107050d060b06070309140f010f032a0c150b0d0807050307170c010f0c05030610050903070306060f120203030415030f0609051906080a02150f030f 75
    0x4c5010a022020340460f8000940400050501c10010f0a9203403007a0000b140e41b620324008650f03ba00500300c01c1c2c0c001001c0e02e00c100300482c0c0070610b07000305007001d68944078280407420001e00807160f143c0d9500200756481520306100419000c05411860781d5183c020900c1300801c030000d200840005083e550740c50f01d82d4400c240340d401441072181400000d4200c0e10f8408041e00c440300e17140c101d8003050340c850000300a6040054810343c4120b082112101d001a06d44140c0d084260031030b00340183d01e01380c00340f03040180260503030801d0940754804401c07030300e850108441010440b581c0c0520002d0680610074844080300b084459007040c0141d954500c4010480c580d0740603200000034825a02070340603001044240209051a100150a044641004a00519003803003440803140140d01c1100360035520810700103020707a140d13900318042011640c240052401c00507001e4880e000170784000c2c801c00d070b40248200304000f02000c2d151444400c410040e181d19060300a4602c50700116000031521060740c00d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 115187913 1250 115186663 115186667
    0x1020d06170708060f01030b07050c0d090e0901051e0a0e01020d2a0f0305060105090607051605010c150c0201140f010501092420010e0109110d03080c090604090603080306030607 78
    0x345c452600950a410541d2854a501000c00703c00f90500082100800c12104d01d880200840c4d01d24684954416240901c1c1021294000300c02030540c414590610040c014980d40c80480660f2010f03040b42080c0c00c64455060390300080c0a9900700c3c0115500101d070154605070746034415806420602c0c04c00e114090300380c03400918014100046004038402c0b400d0010520311039404140d0001060509503e800b0030f42000800036041420704403180d03484179488038680f50140b8402401401c00382440e006140c101e5540d080503501c0ba0060025181d41c0365032090100e4400d4206041c48404040850101e04107680300c84401c81b024080c1c90301040c0c0c001d40001c1c0d0324031201045c14100c040481c0311901c050400030120b404007484a0f50010f034010000080140071800e100303480101080170000580201e25243c05410114040b103807030702c100b904090010200341c00880c050b5002a00204082d43c9014240000c0c185001d29082031452618001000c002c00c0302103001075005140c203e08aa485070790356a81 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 115189163 1250 115187913 115187923
    0x180f02120c0d06020a1b05030a110111090d081b10110702010c0308041a0907050909070303020c150f030705251e0203031b06040c0e040b130501020d06170708 69
    0x8020380201d01d556009001c180f0707a90190954581d5840c0c000c0301e254900c3c1c0322014904c0b981c842590302c0d4000048100d0040c0e040b02510304940c0301f0400911544144124800d1140140340c080b6005d12294502d8008001d83c0008581d080c05008440d00101000f900026540365144241c802c481e03440e000303084c0c0ca81c580c92400e40702c0640c2d05958014048106030b50846140c1c1c0044c0017221032400020b4a03501c20402c0e000f000b482034810000805840c0e2134103040011140c03028001c020b0f55085101c05102195001c01c9840519070241c2c1d100e1215030b0300c030380801300e90b00c100280d2080e068000f0041c0000c81d40e00c036008201c0d8082403840000304032200b80010603a840a450014100503c07000d161544807080004096083c1c0005c0550381000c4903d100d085a04c048c901000031243c06c08820041005001d01b0390710080c0c441340d55141d085181c280d80c1e440801401407c80c0090381c1d0031009850804c082501200d06803103064001f844050341e10704406210000c426034440c414011110b0101e101100002c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 115190413 1250 115189163 115189183
    0x803040807291c05040b06101b0602090d06020c0601091d0c01030c0215040501063213060302130506041b0504030b040305070506010b0a0207090209061c180f0212 71
    0xb140c45010041080c001c000c03544140e162081030183e4016502100390284a410720581c0681414042d0345401c404001c4603940d5050740c2c4040c05007014000e1500084d0341e20340d244a6910840040c0d0b102c101a0004041240300d040042805000103492040240c000c0741d40360403a5190302081c0a0103000d40408100e01c103091a07076480b42d40c000c96013030078190b100c5d4002c0c2d0740d0034001d80199951003120390b5510729a1a422181651070741c0d165007042001044d2005191a4000c044008041c80d103514211521622909100c044c855000c408808030300039640c3d4444401182c0c02080f00566100160b0100003030041262014400c030b01d814898000f440f8107490075400c00d4466600c4138039003411036840e042c001001034810307000c200c024054100064810030046020f05014881d2030340303e250181000b454203420380c00c50044240184902a11500c494055a920010a001d503095400c014a4160018424450f0300e03890340211151540600501c5484010154000e03900c1120014140411035a6255203c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 115191663 1250 115190413 115190459
    0x706030218010f120603060902090703020306060a0305090c090109050a0c0e0609010302030a0e06070507110109061704051f0207060b18010501080c0f0403031205060f01090b1b070803040807 83
    0x14495400c642c418618070590058600304030401300c480031200300807141250011942c4d20740d101102d80c00c0d4900800740940c003014614081d441c51034000f020820f140550030f07031201419210004140c00c00c0052080300c1d1000070103003407490650303540d40703088010303040640e82d030318180d441c04200c0c0b0182c52056800402c01600980110303e86550140110000d500092080d81942d81d56403c0d00c002810078000036000e4003880e07803020303140e002c6400d10300c20b0040400000340c18040c400400704a4940c00660420008883c0c4681b1111692039040507805c044c2c0d11100c40a0003a020141501c000a0340d07030103061000c0c01036504000c42c2d44ca403003c0c0013100786466040106803400d01c004010940c41580d0307090b400580085481c0c28540741b500b0001301c0340c01c0350b00200d022034006200c41d0080c030380368418282e0094040f5000501340d4601e80018141c0b00844c00780801084000a01146560000200f0381032010704108035100a66244942030311394020340242541030103960030020741d07c0d4124024403d824050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 115192913 1250 115191663 115191697
    0xc11120301060e030109080c01090c0e040f150b0a0608070f050301030507090e070f0602060612011a15130b040603140106020606010c020f09070c05060702030a0815040e0303090a0507060302 83
    0x2a8058809510440d0040c4d411341d02c9440361000921300b1405400501740b01000807451036018503020700240c00540241030704d000c0300710070040400c0080c100700d8011500007040c5000031440c1c2c090f880242210a0200c0c0c0c0213040100c000400726400220140300ba0126070300c0440c0b10ba07102e08122964403083c4005041544210014440c010480d4081140c80002004407501103a59100c841480c404591220026170404400c210382030403c1039500c1e44040c2188020002d50441026080d104201080894007491b0010040002c1100d000300316800700a8070011140034030754a51003094181c0c042d004610000b4240318101c01c07000345c0c0d8038425061b910740b50040c00d101d03a500d500444540d04004000d0382d11000344016180309450b61f16280c0e019803440d6075110a8001142040d0b0300c1c1c90405092502150320402082c00300384e0780504000d03000030304210301e41000d0b000704001502034812211807038040d000006c10b02c000000c0014507000898030402c00d40310215a100420b4007240903400c032031107202081e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 115194163 1250 115192913 115192919
    0x402070213050c070f0c0509132a090905071401050c0703031b1e1b08030a050913240f03020603062106070e0301152601110d0c11120301 60
    0x2050704010340c4860100c090701d05244042d20f40702550708018005aa50210b014028407460500e940403a502c04820050309086550b1684c0cada04107051103500703e81138079045c823201c200015039008400c00200b0241c0800e0040141e1400c240e6219442c81c8a181e46124940c482d00f20b05500402c00e0f141c1c2103103403001038800c05142d44c5040c0d404c0d4003ca41c0d001c01032140c01c91104001030341d01d824a41038510907424000542d0007890000f015041d442840324440d154403c0c2000300b0440041240c1c8417141e1031030031684030045030001c59610309042092440c0f690404d4504c0f040ca0350b5000d070001c5843c0140c015140650383d10003800c3d60101d05404082c1d0441e00420000f920f078103104400c01c034502203d4405230045203a001c1180c1c2441019102400001d900880d0300200b0329007409030703101d18054101208680c41c03429268040700a164811300d00e148820461024000c40e0039403000c0d240302c0b81c807190b1554524170306182c0e20080480142160102d83d5000c440c1c42c20f01c00c0064500080e2901001d02072540e42 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 115195413 1250 115194163 115194199
    0x6060915010c030c06090f03080915010b0c0111070302160e01060203040314190c08010c05091c02010c051506040606050a0c080d06082401060f090311040207081803010b04020702 78
    0x142d90303201074060010414100703002507010310a2100040c003030700141a0505081ca001403400d0009811425554800c2107a5105074095400250444a60856182d50b031491104168054941d007061010b2162003c81c0c0301040c1900400d000c0e02d400f03030303144a101056440d9104034244c1d0000b8060040145d005000038000100402c07200960300c14000d04950f8517405d180102803288a5800c412506c0384c500308401c100700030090150307030105d08203424101d0824403601c0218541d0508800c255021941c8003a4000135a400707080c102180315000b0050b11403848a541502e20002c40650320320b4050f40c0350000000b242d51140c4183c41202015544481c1900c20030380f11001c203504118242c0d00341c541d843d000020340318400c002a170041e464084119601501c10a40030000510591042040c400b640c6128030303034a0b611141c188140c07948507085241050205020030000d0240c0700c0000c0c2504000500e942d10410003c6940100b101c046000b0710850004030244810390041c940d000350012290060258801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 115196663 1250 115195413 115195427
    0x905061f0c030c0204020d0b10020a0b060603040f0503040b0702010207050406031a0c040503030a08101508070302030a15060507050c03010225020301140c03010e010b03040f060c0201060b040f080606091501 90
    0x1c0d0107890140240641a00018203d07440184c41480550341e0351207a48990610341d06881030f41d910b600150964405640300c240c1c0101004240318071518002000034204800390300325000494129040b203403600c0d1901e0949030954040582640540300d400b80018040ca0a40681401c2d02c0d440b50713040d04582d5400d51304103400440540040350703040041c000030509490410140110f107030305035500106402c20b2201c4440b00e5600d80c0000c8801c03210f83c3c80860a647d0071096294010020340ba00581d6680e03504000801082c0781c2a45142c5001c40c072100007603040c0d0040181022070b005805a680707110003d41054200d12418100019010b0541c40340e071003d030b48180c603130314401c0d00180000c02e80d00341c44032130300e000704c0821a4481004040031006004800b002d42610740980101c10045103141442d403507006160403105002800651586e01074150b9034800c0d00828001c201401c1000d440d00d0320f8103244c00451206010b006c086204a0700002c082d07160203032901c1d004201c450105004071440000445040d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 115197913 1250 115196663 115196687
    0x3140d0e0d02040f0f0c080903120c0d0b150702011e0e010e0613170f01060315020d0b0d030807030f1107020108061809030a08061206151909060905061f 67
    0x411360700ea140f415148428041d01d5a0a60f2242000414149209010307000c010003802d100b01b00d500511100b008290719000300c64009104000c00c5403101d0b900c01d00704015000c807031200c5400c21a5110700c03090308002c84020346040c0f8402d03200c40b003030303542000c07400000c55506100030030004182048500c81c0c0c4d4003c03111082c400300054160f61905056a450700c400d1000b540c006101d0b4100402c16480004041c001c840c0c2c04241c3c0c27002403040c5840c50301e40140707400103009140d00d282d41c000b521990090582e07018601e841c2001d003070f4241c088681d00300500031020440e1540003090902d00e10001c16001d034820080d00305541c0c0f5000341000d40a80044801c145c2c002d101720342105560601d60381c10000c815950340f003528182e000b940d860940c0c00c002454000058001402407000b4000d905001d1000f165a6078011104000203a000b10084001440781c2d44c9010307c2e00356030220074030210f100c003041c1e0412400d40b05107241c14081c039110318061004201c5000082005074010107440380c40ca9118070315940302 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 115199163 1250 115197913 115197919
    0x509030a110a03060e06070f09060207030213090609140618060103060c1b0f030f030c12090201020102040513201201060e010507060216021014040b031801060f03140d0e0d02 76
    0x11203480b56079580845c0c1c2810444680d55000504001005074011451401b007000c03854040300c420b14000c8060340e0781c841e9000080c030030301c0d144200d180603080c90b62007000c140340c0141040c0130444440c2000800d141030b800740e92440740038100001e641c0c1102c0c414030400044800c001007000380e10355110b580c010141c0b50045010040c8100c440755180320f49511040c5c020780180e0030080304820030315000c1c05494100d1f038044181030400b0001180c1035049183d40074078010100c00030030300400d83d200407030080c440d40d00450760010b0940b20007103203001c0750b500030b1800c0c54210740c00740040741032215040340c44e001e104400d041024070b4000520403a03200c0c41c0103022000d8181401401c2c003905070758400c103a8000d5811401200803030f803031132829890190aa0300711480a404c00d005449a042e000d0745540c40340c0d010300401c240c40040400c031075403261102c1400d500068002008916118440104e11042e50f00c41030b29002ca1001850201080204011018500c140c03503002405c02600300b0312403203003034268007664 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 115200413 1250 115199163 115199179
    0x1a070215091008090106060e0906040c1101020409020c060a0e0d0c031e030203070f14090609010903020d08091807021c110625020f03120415090501050a0c0509030a11 73
    0x40700d9250403601e044042060744400e034039460700488035821940d490380100100b081c200d40f40d0080740c44050186d900100b040c0d901003901e0300e0511090790888090840204950701c0000c00044c014850b034054000050b901007901c4003a11010300300d0094070a84d00314000c039500892900903090340110143c4407004e202e418400c901902c800d824034620102010b054000c26000000c109519603c494000c1c90901030781017070401002d00401c08005400b585100324040c1c0d00001c0c3c1c07a1500e0b0b0181c61024011680203012000e44081071400c4440c50b08407d42c03543c09100c00d09154405840072a01191103005158002c0100c514100000300c0415800d80700385040c488010409030910000303201d0a882204510700310f040e800101c40b504440d05803049601c90071508954800140034a0100480e0340484e26a59005416101c6007030029803541201070054100b850010000b04004064108030303c10b10002c00300f0010b501b44500c00340c900d8451f000d03180e545a000034005c00700240905001d900c10700d0001e0031241d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 115201663 1250 115200413 115200427
    0x90c010e12010504030201050f0f1e0a0f090c030b1b0306060304020a09090501050601090501170c0f1303140d0e060703081b0a09030b090d0207140d08040308070b011a070215 76
    0x1900f1903e0503603081c1d00503515030041101c4498070b642540e800045d82c4850204524104a4a1203161024540282407c0440c000b044c418081ca8000003c201d000039801c200c0b5000924002108035400c0c80100c402c800c44a0002e100001c211540c0c04241c4004244a49150344110401c103140e4001882280d1040c14400c001c00d08600601c07604035014441c400000b10385c00d026001410541a95120b24100702c030740164920a614241d0309030760401450120140c0b0388042c1d080b40700c0302d801006160100c0c9840d00400205001008010360000341030041503603000d00b4023150894440e58884040354208408015900019100340d00082c1c1c410304601c1d18800d1050340502c10205940541d2505002840910091003071144400f01c0a800c910280700520349148021000b83d21b618480c820213120343c0241d8540c3d041d903160341c01d404c00303000d038020801d61b551500c0c3d03e080300194008407421ba402100d28400480c10000e011071483c0c0c40c150b509003450500c8116401c025480224070448180041c06100803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 115202913 1250 115201663 115201699
    0x10612090f0803040b1b0306010210091403030c04030b06030c0d020d0201021e0c010905060702030a031107090203070f1d010207210b01090507110c010804030e01050c120a020c010206090c010e 84
    0x7a40c00b45104005d942250b0800b0015259a0b60418841c450030724003c1040c020b41c4d0303800190324032840200031404106943c0a08000071081840c0345040b48902000007000b04101256004000740c1c4d00c50001c83c07840d5207404091540d05c0814111240e00510b00001c018090f2034500c001e01070642c41441216250b802101c0d03606590f0354000d04907000d80d8171242c118005980c1100004020304010fa48007402c180443d00000d540359240c5401506101c45810003019443c5e0900c40f0001424a0394015075036418085070041541c8030f61040e00b4005141c030100c04101030402d409480300c85005a00070b00d180ca0408203074106504000e24030111582d080c0c40140009545241a1802072807000b40c00902882c001c5000740c54014005142c000c0b541051940604aa0f0032405040d04150545003290041c560134005864501c140d450140f5148108040e4500a0321203030010580300c1044c2d400e80e500100b2110040e130b075900d0700381d80000c40354000a08000c41f42d4818000005c4140e40200071854403d001082 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 115204163 1250 115202913 115202917
    0x80a0b0703020c030c07141e0609100c1410050c12040813030204090510110f040e06010e0301140613091505040201030603020901030803100e01030b061e0307062006010612090f08 78
    0xe40300714114007d0f08510300d0214410201c0007a2030142c03c41c500204030001e4174138030942081e41e200b04100203a10b00e00344d220300200d4a140307134081c01c0159000182e000142d0744841500c20a140d59044c9800103440902c44030a884400c07450500000c460384490741c8004403600045d11580c8407200720400000960307150b010b4091620300a00c050960880c03081e503030100707581860170b00442071103003046440401726844040390110784c451601600c10f038840340d0049680044040005515608104280140344000c8040500444040307a0346035104c3d8106100d04141d4038002002380803440d00030344110401643d9005940d1040c4145400945d240c1c40c1d034001942041e003a04191183d8401000300040d8048502241d4060b01c16001c0d042290341c13440d610b01c1c111140c024206030103004400e605140c900f4500c0085010343d4002030994900a13210740b4001e0100d5181421383d094503010100080d80b0310b101254440c10380e03c940e81c0d441c2c040009514900090000c480f4121030304050349a00a000c0340e80200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 115205413 1250 115204163 115204169
    0x3180f03261602070503030d020304030215150102010608161202181e100e01031506030606060309022106070f05070c0905040213060b03130c050d0f0c080a0b0703020c030c07 76
    0xd003080507818500c2c42a5216218a04680e05660040c0c800384016070b40041504c11400d40708001503901c3d42c3c0c0f490102d04040d4010680042594246c080c003469200400250910030300a80c000c00056a40c1c41c0a80e9480591069041014a80c040c0a004c0810b8154154041d0760000e4401a0751041404101080800c2110340c1c203902d060303460341d005030b4102c6031007000d40050f0048500b51065085c0305450303040c008103100040c0052003450340818924030a801010013140c01100402141d69281c0000c0c015046c00c0f03a04a10072441c0c2c4107140c00103541d13040100d10f26854100102503580d13035030070196441d008420118052140901506000440c00d001d00805000300d6180454241003510521452a420280c081005401d04005010788801e04090760341c0302908808040f05144c43c0c0c10007242c004003980059412540703180b601010f010a21800590036449000c00071400365680c000305488400400009052403c40b00c0400c2c0c1d203030300c0b90300501024101d5006407850544d03664046407410b1060382c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 115206663 1250 115205413 115205477
    0xa080307080603060f0403021f0b0a0801020405011b050c120a050d0f09080d02151302090a060509060a030c050103150819060e010b011b060603021e1003180f03 70
    0x2004014081c20f00388403442e04051a0704030300741141403568000e901c41c81c1c02140c0f010103a200504070b032000a4550800b0304841c0000e441c0041c429120f11540c0e000c0c0d48540900c1d40400e40c4440d131604043c1144501d400c00641150150821a0401e0300708120751500e1103c0b0061441214404000f10304c0c213011059428074552182d1410090028028212403c140d11400b000d400882c00341c11415004942041072400e501030440300366540440707860a031014107002035048185030040150a145070f0b40076406880c01243c0c0b48500345d41d0310b410000001424000200440c000e0307030082004d94001d40044940e00d10b240c00c4441c1c1c1540340d0308060314202c3d45800454420110104400600003948103423152180c0750b10090040d602e20b4400a84404d26142140a9944400114405004040d44448040c5a004141d06810111250381138010162072080e28803800d4418044a2080d00a2260441e00c02c2d44080f4a030708444240c5907040701d0f00c03003078a00f0340c14003400500c8400c0c81101e0011042c1e8202283c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 115207913 1250 115206663 115206677
    0x40b0c03030907090207081b070f08030408071e03060c05070609052a01020d12020c01020c060a1a10180312030e010f0b09010b0d0b030a11030d0806010806120a080307 73
    0x141c0001c03032030010311340c0c40340c0c3d4090b04c10003000c0b000c10300440481303403c3c0042501e40500d582c0d4200c009454507500768400c07000d4441c082c80202e81040040700603c110340c07410007110305142c0c0392154001c030100c00d18661109100960010400038441c0e81025080d80e12030b04103641450b00303036221178007035510518040320542c104111506005100001442c000b0001d000715100c010342090010f5030315001020994144140316009000e0f50480d80c040301d1542e80604025034032181d940010301d03030b28441603608404c05410b058840304040300d1620080c854017030082508000d592125000d80d41402503080040300307240b00b04408000700701c49039001c3c804880e050383c00052812001c01c42e6821941c2c41e140c84842ca40c1400700d442915078401082c107055030070039403032199200e00604442c401002c24141c066018002c0d20301001c14809520b40303802c010b920503404d48001c0a18820b048036a00021110503000c220441d010402904020707401d084400425002c40e0f00404590300c6000c40c681080381c1d4280010f01c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 115209163 1250 115207913 115207921
    0x8100f060f03051509010603020c010b0406090608060a150506070203030d090302030a170105030601031e0b0c0909160f03020c0102071a0108120408060a3902010e0a03020c090c040b0c0303 82
    0x2042c40742d207a001002868402521300c0c0380d000600d400a041c450241015008248007500d8082036029140c80c40f0300800400c5026607450280780a803419100e81e03a0117020f0326000540021240c0545c0070501301080c400c000160401c42004065040441c05903050f10042c801030504001a00c0390184050090700259154952403400500c800058102031281107035050040143d0f840c0055043d0649502486d0191120300b00300003462030b068148800b0300004c1c022400d0000391302134040101100e10083e00c444015580740c1d803000001310403041440e0006441c400400081a109501400c1008400e030005860200c058450782070200080f584c0105014000d4010010403d080040e180d918280e41da0507810945410030741038480307000404c1ca4400a86070382511007480c035440c0e040801c015070701650f9090b07079048100380e0b82c00190b5401e02c2c1001d5840e0402d1003407134810004084000d143c2c1680105407585260081c0a0340d144042c2941c091881d007404042036011030342c4040d0260444020045480c1e20f0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 115210413 1250 115209163 115209167
    0xb04080c010c080619080c0603041b03030c02100801081507050408010e010203100e07050304060b03010b10051207020615010c0816080d15030b010b070c08060c07031805030d08100f060f 81
    0x61040b45e507220390711601c0d0381042080408100801070140440d41645c607566541031040d100300340170341a0400004804008810075400030700b04055580261003401010071130540640f0802c0d02030042912031342c40030b408142e120b81d070401341c3c40c0d000c8801d140090505035035240450079581800320101c000e035004403c000e901140d45840c80c00600c4490341e481454241200054014400640050030f407503100c00c50846951025000032040c40d43c050003510560b024988010071a410010401c50030341100030200f42e03401d00c0015024050038807490040c4003150088010b48109410500c102c420620502c000c81d00c5031990b21012a281c0d005241c150350740c0d500c03110404e044403072103014100b100010000a01c00f1802d880c0300300341500c0114844c99650f4000e8180100300404a131710032007a520a00040001c020341d9040900205840798450301d000081c448110b01d40c6200324044c854043d0b0040840c944001d105098513508080700c1403199a1103600c078003118000300100d0300b1400c00304101c44881e06002d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 115211663 1250 115210413 115210429
    0x31e060501081f0912110304050910060e0d0507140409050609070e2406090301020d05040c050a090b06030601030203070c0503030901020a0914030705060a170103140d0203160b04080c010c0806 84
    0x2c10050401100d455135070b17822484100c80382c4d1710041040e140e00003075080b80204202c0f001b40c0030003460f100d00341ca06091000010b00440c081d010000c1c845c6a403122a80c10400c02e016070043e402001340c0074882c100200244100000170380c0c5035106465901500c0414014040b00b40113600c000c010707003041814000020f84c3e03400c002d40700740703984140d140030740c0088036440c04000c2c40c211003141e0701e6a82d40d00302030000c0d02900607088404603692408080c04108a400c840400c00c03944e00366a41003223980e558076002c007103030400202c2580290f800c00000d101980b080d801158011380d9403d1684000b41207480d0a132550308211131441e01a0340c0080c8281401d030b007000200d001050049404400c5912a801080d210019480b4040c043c400c041042e40c4c0c400d01840060040042d941103004880d80d42c0d0800da55180389809000c140c1d03014003095911804e20101c100c0c0d01d240e2512891020740b00b9a03a8540740c0e41c000c010030664070400284808082c4023801e000e5180440c0389507849400c54100310041043c11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 115212913 1250 115211663 115211713
    0x5010f05010f0215010b16120c1e0b0f1b0412030806040c0e0915030a061505010203030112240e0604030e0f0d031b02040e0303010603060906030804031e06050108 71
    0x142d0f101c3c130301890524011454050554510903091511920925406c81c1e076000403140091100d0701444005029070340c00002005154041c900e4803c1e801400f0391100e010710072400028007103090034000202c2c1d5000850385150404000441a030040407041070103a01904207410000c0381d01c80743c000c208140f6520038646900703c0411034040101200424014099580c0c00b07080c9405016032000285000d000030f01d0140c070301c16010f03040c5d0b060000e0781d10f062801032401e082100300c01000c90340c0100d025403000041e40c0c1130381c08000008625541d16100c9209121102c840b40b404460f904440c8012521503014841454a025006003080e0510389405040e030611922086d001d203600f40c9843c0b41c1070355070703d00840102d6098140710341c900ca82c0d8900301280818031200070390003e0a0215840d045030300000103504840065804000e074507180e0481c14280da01e50311015001d01410300050000c80c114a60000c04014100c122102c2058cd50b910340703082e203038264086651a00306030701c00c48844510314540c0c0d5103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 115214163 1250 115212913 115212917
    0x100507030e04060b03130213060602030d11030c04050d080d0603210c0809100c1415070201020c070306020d02090a0b03070912050601060f02190602090a080c1003050a0b0405010f05010f 81
    0x843c140a04c400c07007030100500a0011044114070001992911b0401d0031289420307100030b10005841d50030207036503503200400390b0005600e03100480c0710801d114400e0f00c2c0201c025040040c41d00f0b1422081000d00d92281700241d504200c10403469042c1501c5120b0320004610402240d01c652085610388001c2401960800d41403003c10098840010750384001c42d034074580f084070560b07460100c00004071075800c1d44000c014035010502d90485000300001030400d0003508400b010314036654804104900f44d000d0840246000d6002c2c6c0c0707040c40000d00640240c1601c510308031006080c010001c0015542d0001c1e03620215000f00c1c00814006201ea0140c0510082d1000154042100029a54550303982c00144541d8081103a20607980312500d1003408980b222800355050091045c08a041000003503001d11540c6d4440c01ca480c0d40055003102c0070030200d08007100203108010000c9400400e901030b01c0e00400c2c0d0280d540e5961840d02ea560f459115240c080c0170445c0e40c54403403074142800074010101f10300c18182 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 115215413 1250 115214163 115214171
    0x102030c0d0905121504080c03040306051e070c030206190b1e040b03010b1f020a080f04050906010806090f10150203030a14010308180d02040207060e1203072c100507030e04 76
    0x805d441e1520700980c0c2141d0b2249440f86c0e998040d0301c40a00710300441c0c000800e2141400140030680010001185e034404014103500c0703075511004000e40f1050f151920040c0075800c0f4100191303640d10203142d4480300380041c02000c40c080070100c00180400020b00c1864501002c00304000306641490700c41c3c100b5000e01600200131782c86a000000303031104040742104040d0740383c01ca0100380d040d03c20300c21000d0044d03200c4140c1c1d0712854801560005c580082c01150300032000c8200160301076100e078000d2401100e024150000f030340c8543c000c0b110070f0b00b8004c042ca0040c1c010381000250304e401000e807190740e00665074041e580b05c3c01c0c4507001d1000d4540701d00d224191001124010b00214106174102d81544004200300c0c5d4070000c00c2c0c80400c05c5403241c03890103580144041020b00500900e5003142c03400a80c41c3d03081e102500c08003249850940015210750002503803215200351f00300d000c0101c80d45080103100d490726942e042100000d4586118040701c00002d480418114105508603080403081d40003110288 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 115216663 1250 115215413 115215433
    0x507090b030307020d02030a02030102130911030610031a0910030b0109090206090d0f06050a050402040c020d020c0f01170907060f09081b0402190801080f0601140f0102030c0d090512 80
    0x80ea0b03d0107103000c003a10515800072a00110b60b0700f04600c00e0b8641e400341c000d54903584013205e003a0a807000f44c443c2c52055401e010440e8000c0d1000c2c070132a80314035030081c0f0f03140c504801070404070010500c240c442c3c1c60300340d1784840400741c03566003103aa10f20403820080f841d441e0760f00354070f4005d0a03400180c2c04800560301309100000169144019614034100c1500c4984040d543d5007450070f032400303402c50094030182c0340c8000c0c0201b13190f294105520550080c0d8040c4110601c0000482c0d542c4090b44443d4010781140c40901d10600d44848100c0030360805140108150942c1000c500c0c0da80c0303095404411540c404a410810140c11495002c811001401e000d10003602e00324002e9203d0269105610001082281226442e540c03541038454a2034030b400031052a080c00100502000006c0c00f44034014031486000d0420360500003465130580b481d0880781e5072000029418007240103110103040c2d041d40014409604204400c1150b41e40b2b801103551000c59152500c4240244204d486020310043d4120040c80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 115217913 1250 115216663 115216669
    0x15050901170715020309010801080a0308011401050c010f050702010c050f0406081008160e06060702031e0c091e0c04150f0201020c0111040e01090204081005100e070c0507090b 77
    0x2040c1121400701468a50080070002030341401860707080078031025080e140c085580d5900202130301c4100c83c01e80740c0d1a03060342c8480079290780d01d04000000380005c04040040c88130308100c442031041110f041c10840d003803030741c211010750a40c0c40007180310382034a607a9010015110f40c2401001606100c40c18041e1a081030200340003191300c0741340220420710810314003207400210004080c0c0f00500242066070011070003884454427114981c4122a4890310f00c001084461a140d4212040e981c0c0c020300a1040c1c0e000304160100c0790480d0b158a04c0a030180340d454484980711200c038980300721191988041e01c61060140009a2100902110201c0703005000500107020aa0b02c40c80741079983d802c00e007014105511003240a03201c3d44800c131115508013103031000400d010703901401c180d420040300f40881c1d0b81c03107003030710001c030b0189100d031202a612003560b03400102c500b0740c800ca4002e105500011805900e903803400d40c400c4810b5400100180384c2115440502400b40104005842c08000900c408803d107800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 115219163 1250 115217913 115217929
    0x30d08040614190b0102120406180510090303111e07030618080301061b12020c03011b050403240c0e2701061b05101b08060310021602030715031505 65
    0x124100c15602d00703402c084e0380c0c001c02072100c4070101d80c60410f82e41e5448031001840000c0c1c00440b503648041a120105d903d180c040c42c0903a42801e1036507401852859030310b007110030403400c41148489011b2402c106609003001c507031103144200342100401d41c4626601d040400c4071610040d810704140303182c4105c03000448400031a81192403501d0b0080d01404000030485c490382950000400e0080c1304400d0707034074580d000b242c100c620440c1123000304103000d40d6840c50000c4061061520000403400c02050001401c40503501d8609c10030a05031203028541246583c04582c00c2c2c03062000801c4c0790566034912840c1980c0111030090001218040f4008400340c0e0421100e41801440305010440520300c03014170206040d0900d09801400310740c0d03020010781000c03000b04021f041030a07040e13600c0d1181d00c4c00c82c1e006944060045001800808180400d40380500007500098000b078498442150303081c01603901080f150340500034020300c04911090710300c400340407250b005a080c00c01c485042030811950f980c40f40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 115220413 1250 115219163 115219201
    0x307090302091e0f10120203060c0309030c010606021501060e0904030311090904140705060f18010309020904060506091b040509072007050102160e0a0b030c030d08040614 75
    0xda4010340781c0b51039203210f0724034098880e45000e4102240400120491295405000716010b0402d0903425888000c645c2030101c0701c40001c2d405620200c003003580204030300011503005500c17a0699003007004041d509402d6a0340c541c4100016400b80312060b00c8a00c1000d6594010040d0781444070324208640080741d1444001080541855600c0d200344140052580440e40c01d039400815042e82403402d8900245882034034000080d0070311400c0e2011555003084412151070250201e009801c0160145241e404503e200d070140d41010744903841c61005803100b80c50140560f100d8400480d280c0341c80e00a01803130f0b140c0105185481104280c45038101380185048400365803040c4c0752840b560f038681d00291030062030016055042c5084240715136000708045912000e4030000d0342a00c1d49012200000071404030f160241d84041408080442d101d000103602003400313030f14040e040d15440140c000000341000c1072a294100813650101c00c000401506100e40440380620325800c0c0002c1c20a5444003440c400220 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 115221663 1250 115220413 115220419
    0x31a040e0a0f020415031b060512041407030f0b06030607020c1309060219050316030c09050d06060806010807030213050103050607200304030f021e1c0602120109020715020307090302 80
    0x42c1542951610381000315085200601c1100a40e901d24014000c1c035051101c1c8010410520700200b0002c0c032030070031030340c61b14100c8600c00c81a480e00e4699000c280c1881c41034001074418040004001054120300001482c09050a260580b0b0640706040c01e0800c018010700441d00051001000c558a04451114200c40d14030002406010f80c50454004d00c24210098a10310b10140d40c40d043c2c90340040290b101d01c0c0c42c40c511141c80c244800c82502501c10803401000850540c500c24050b505000c0b040400c014007800300840c5c40c0d40d030f81c440c26052920030707040a070840c0c00038907080c07065003005d54908400c402c3d0308004002035132544d1505500c50030090040c4041158402012003040c80c00b950840200090005681d5a9582c81ca44405800d50160089000b038040070205d44950802c401414890980917080030382c40c400b507150039071001c0c014080031141160b0900c41c40940e40c0d131000380350380a49824480141d640300582030003080e010041d94200c1c030250040080002c2c8036441384042088030703819 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 115222913 1250 115221663 115221683
    0x3020f07050901170a02030a141204030206030402010f0c1202070807080a080409020a1101060b04051201021204080309010212040804030b090f030a03110409050708010e06030109051c0915031a040e0a 87
    0x465142414020748170310181d41031113584076103010300441d9103105003064200c2084540583c0900c1c02d00071240140d1001039440082480003c006d540112008103244030913190036159017505694007040c074101c02e41410700603070020009200042007046803102070550f5900410002005544007803c1d40709601940d0089900403460026980c0505c51654032109240000d20149032610b8008a4503040b920416101c0e40c0000d602c01890031042c403c07280b0010a049000205030b8850b12110b400758006040010999420404011040c58003110140114402c8003401d41d5603295042c4654580c0300582004919044041000f484281c0003003100d8507035115003804684014001d0040d60035000745d81c008040182024200214264400340b40750503261440c0080d20315403500800d1600321905510028840e50000d400340d484c009403034404000100c010b02d0b011071000c1d00c4101548130f06100d903050101080e207800c0ca1007241418056100100402a601000070404419020b55034504003003018045280d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 115224163 1250 115222913 115222949
    0x90303040312050912030307020c040b0102191e030801080105092803050f0313060606020d0207060305180a050a061a0108071206050a060512090318130b040f0903020f07050901 77
    0x16000380c031501381e0010103040304190f00c0e444441c2c070703a4400c49101d0014000c02c2e8200c00a481c25104e030314074600041e0b004041080b0594001e4224000028080c0d80d41d80c43c6200c5605022100d000b00c045180c0b103036039410480d5151030740190030345001400c404855000190b03010b40d00030102000709071150312100c3d0b0f0b10300e4401c2030034140c420b03100b400500c885002c000810080a01d2525038040c002c0c0c3d2040c8420814a5030311042240c84074a1110f0380f0005030040c0e54100412840f84d0442a005801d004011901100360031a6524084a114003200c481d000145103100380012445031021290075414035a248504420000303100950040000040c049040503903002e421840e4090030107000089c025008260302c40300b01030500d800100003840459170910008040f6440132040d41e01941c022030b59031526032408001c0105003c5040408140955030f030203811015034580c0544180024010800502c1881d5030500a0a00e004c0041c48203807540500c1d020805501e441c07078142d04550f183d200224205503 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 115225413 1250 115224163 115224167
    0xf01030803240613080616020705220f23040206030103030507060b0a030803100f0803030112080f040b1306020105070e0108090c09010b0a090509070c03052a0c0f0105090303040312 79
    0x702c00000940c20207404500c5041c048928403c100070f0356038050440e116036850031070040680c0d01c405490001a00424002c1002d0304181051900349038603040503200b400030020001c0c0403103218a9517442c515441e102c9842c02d07101c140e142082c00d8500040344a02c0d07442d29401040340d40c0300600c00241040700000d01c030401e220340d5a004441c4d03104000c0000c0d03100780d640d003460b110716081070318101c074800c0c6032403000208d400031070790003030100ca02c0c8401460039a8a001710141c2c0c00302e10002c0075504000e04100d03011248107810024009809101100d684414841d818200d504403030b50401820b5a1504084c004030641011900340d1548091a1190040d91010201d6080401c24514140c2211404d03001185000c071203009004580203558484140c16910300410088600541d00c1c0004290151000c80110740b14a0040050410f03071380d000c03018440c103d00d202500d10442003503d17805800407102d07940036150010365a5240002440c4c054181514000001d4803840389120042980f8414440461494 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 115226663 1250 115225413 115225471
    0x1c0b0402120105040f050c1009030b1f0e09011802090402040b03010605060d2406090e27010915020405130e0c0d15050106180323010e07030b0f01030803 67
    0x710500240b20030b09107450000c00508a1040c215920300807941ea0201900f40602c50002a9440741e0790152103514546500c0038402020300b100801140d403c502d2482594420900401888000c0300300ba050315102480302c0c219191445c2c0100d0418869030601c1c0541c4da0341103a1a0002d8040301d0000306081c4850010340140026440190014030200d01c441c81865190b01a251840009035146e003595130000801c901c6022078090203002c40d403074407014803100b240000c2c0564030100d0300c008081b0a0000781c4a030951488004030034200380e03440313060020811860344610781078694244415810a404c1c0000240b042d258000700d00c0c0c04d565605400440b86204001a08103054040c08046c82e00702175044ca54031581000100c1d00103142081c00014030280b00e48045010101908150500e5130304650b900341c842564007148210b50244050031190100c0b0a1051185d5410b0b800c0013401c100c8d1640c80e200c403420b0001001807403503503415001040480c803950201c3e540311410804200030b000e1942c6040243d030f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 115227913 1250 115226663 115226689
    0xc0204051501090e0906010308180a0b1b0616300522020315090a02030601060306080c01020319031503080d060501031a130e0a0501291c0b0402 63
    0x9400c01051040181c84800100c4034034000781d80c0e550803a5110302c00e0b42400d150543e02218240d109800400100e103520000d0001005100c445091241e00c00d000500c00b210039401c0002043d10021362030000d48600c588680c202c40c5403001400b02d500d001500704100080c645407400c103026820302070090410a003410500d50708006414030315248001c244140051204688000c040110b4092880c102018074011210481c1c1c000c2c0105030f05801c40d88241070070b50000d000032a051080415403001aa02444141d010b00b1032581c000441d54940944a86480814210603055400402030101c803880001c0c1855540341c0309007030204484171140c010b41c80bc1032131603202800c00200400d00b0303140100f0540003001102c800b40c4e828400e5040f107200e1009441d0b2a0452150310904c51010380b41500403d401c01c0002c0710000041d01d034441d040c4d4440c0c9081d500c1000d0b04440c501500315000b4070440c44014114490103050f00d810b07848208107650620300400ca44000740840038503c002908540d580e0484c8082 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 115229163 1250 115227913 115227919
    0x2090606030c041805042609010507060902040c0201150906210c0803030103030302040e0106140702091909060902041103010506120a090f1b090e0c0103022110031203060312050a0c02 80
    0x41000030355134100100425542150809980c0041340303107031071156001c140d210b42040d04481c03070807c140c0019141984514012640e5030f48030b14000003d0303600c5103d4203d0115043e0004a181d6191403405258040380e9006040014030303000040c05441c86100c07215a1001c2000b00c03020300c0001a04040b01703002c4003a48030b02014400000080101359042c1c000d04203d505041c0c1d50f00d816600d0301070a9810450b007044110b4104030a11420300581f80103a0070f240c00c00c080e10880440d44000d4001d003019511042002c2d50381035182c44030303837046050501c82d0507070000031800382500319410440020300510801c11814103a20101e00485c0c120403241c0c0c030007400b042d8002c0f20307900c02c48214541620f50000c11004214440141840001c0c035030964010401c4181c440b0000d02072840c0800c0c0150020340100b941c01281440300c130b0b8280c1c440c41c1c1c0218a14020540c0310840442c462441c0340c40703002429072103d02420141010070400000341203010b61817101c502800d026440310000780045840040c079101c0654 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 115230413 1250 115229163 115229189
    0x703020409030917011b0e130f020c07080f0d0f020c09010608070e030106030206090613092a020313090c0e030d0320040e0f04080d090b01060f0c02090606030c04 71
    0x10815800a01c80c500310f4103245500c624604100140c107081b42e56038100c04800d00954024011031520034a0182c0d40c41a004046028010004600c641103550304481c400f0201d50008100d0740091080060740001d0228000400800900040141d1222050700c00388003030250000010108900911100700c50040141070404190b0b92850300428140c010f880007000314000c008140c0d12802d06001e00001e90b90042c100c10700e000b2150080c04110b901c1b100c0899465880400082500f2219004204500110a000c140812a005204019082c10385a02e00c2035600c208040305450740c40840301800c0b144643c80c00111180350800c03c0c1c540c44c80003e40320798540140101c00c6805034041c6c2c07008a025860041710403d0507072004a012840c070031070180c072001000160010f043d59011482c0e0950107449042074030f081c0303a00c01a805054407001081214911071400060284640c0544075854504840c43c010b2294112070b0081190342d90b000e81218080c130800400a003010340c13000c080310010900040401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 115231663 1250 115230413 115230431
    0x19051b030715050f130210030f0207051c021603060906060b0c01050a110702031e07030233120612340b04060807030b04141306050105040c0905060c07030204 69
    0x864081e5060303401200781d40740401190303002400341c204078403500f140004141800d03503580030485200200c200c1032040548409c4460101552400507010192181d00244050342414a5000c1c941009081c07041c1198400c100c20002400041085022250080c1001641c0401410030a01420403a080038448105c00501264081070540c06948241440b0504011004214060307000c103100b00c184c0a541640140351600e2800b00300d40300259900b410400311a01540d0707070f81c0070501040004130a0490540c00c500c0c2c0d0b0b200c809007000f4050300e500c5100311403481d00481101d00b01c50108050700c1030b4015008510790800c188010411500507a10350100010401101a00190089a0031456249010310321000054604098041d2070540c1c03c141c075003030075680ea0307000d04800070b02449000540c000e4580380304200440300318000a000b00c510400603515000181000801c3e02c1c03040e40524021860020031401455000081d0341c10744008a81c82540c6140f044c1c80280b0704000d9810181d84245441c41807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 115232913 1250 115231663 115231673
    0xb0406030b1503060105010504080a020f0d1e11010e0a0608060d06020301091a09090312070903020604152304140103060e07020604020913031403040303020d050a0606020f010219051b0307 82
    0x2c042810045046640f80d0b0b80310801190180500d104002c0c442d0b1113565000014a0702403800e105284028203108506151030700c4800511010165000801d10a51242e005000308030011145030502030074a4580072108001041e401c02da2481042e04010b20b81c0003080803a9545000403554503004001552607503114451440100008050810b2300d60211408900f5810035450320380c8600000d1001c0d60901c52030800041b141c90f4001d2100d01000a00800400140e031443c003e0304c00344c4811904c000c3c111001420280c040460030702050560095075803a4002100c16204460990f00e110b0101065850f2200050b0b0162185412403800d01000d10b00b00f01718564002101c0b07100700e008540ba50b450381c89800c3c3c22010389209000246c001510400341340d9403184c12000558009100340fa0040c94446920710403000c413581518542e0174030380c0300c50382000129410000c0c40c9900c401e4100031032070604441d0480d80282c0e0041c480c04140b08000c2981002c0b188060501c844625410b420381c0e03940c1d0001e10307103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 115234163 1250 115232913 115232941
    0x30a1506030f0c03090f080306060706090b061c0203120a050c0a0b0a050609040b0606071103010903020a0302101104050f0103150803091c05060a0902130c050903010e031204060b0406030b 82
    0x3024000c41c0f4003a000c0b00414424022511001c0c3c024203110340010b51a21403040310360008007000e8100204012038800030300f003886004103203030041a2181e085c0c10144100040e45100c83c40c3d100e0b0002c8060900e101594002c078104600880c54902c1658031081c614060350140203030300190300580108141c0b4400d01054441051240d8601c0d0000c00150307903000100300706d01c08291809020751208900180042c10110002c101050090174980301103203451000a003500e24204040b00182c101c100b05004064041080c1c000344203205c0e4040c006422811240700c418062442014030842c0c210407240e2903039000341e0100341d01001c010070000b26181c07504105640c0c2c0c0c3c0704c40c0c0000d005242061003001c002c4680000f0340342e500da000002c1c0190307440c2c460600010780002c0c282039902102c1040c0e4081054800c0c41010f82d08200c0d40c40d82a10350802008040c2101c190b00c0090605409c06c21510b044035540e4421194056440040050341c1c1d4140310108009100d141c2004100024400034400480301d1140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 115235413 1250 115234163 115234181
    0x903050c01020105010312050c0a0606081605030c06090d1e120908030a050715060e0702011406060711220c08060f040608060109090f12050c0d0801050312030a150603 73
    0x200e61500308103a00490803103070244400360102d25a40c0341c07904100d104a00422a0b00111802c4a44858198a039030341142d00301d03846408154000c0d104d031458a41c81280781801000b040707001d011140d405c2c40100e2480d02c15000e10341d20981404960004001425000c04a01d065400812620080519080c1040450010320b40b02041a031940014960000000c4555002d07203660707070b24240303501c40d45c40040e403041c40b5000d20585625442d01017014440c03022246d21989482c3d0001c104480038090381aa0001d01504544c00b8042c06c00c040070128030141d80e0a40c0381c41c0240e640aa511003562042060808a129003144807810540c84c100016800684140180011600f1001818494040004580145c420a403664101e01c0042248002d660321400095000d56503011013100d1680e03a9050710002c03c2076410120b030012a0444d2002c2003000304040710723180f90500021079410030000a64070003070302ca0314611882c4000b00044001c1c001d03802c82d20546001031606089140c075400007402400c000d40c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 115236663 1250 115235413 115235423
    0xd0609080a110304030f060f021b010507030c05040503030f0a14030405160503300403020a0b030a06120302061302040b0907120e12030103080a020c06030109090b06010801030218100b0a0903 83
    0x10082d1520000801110101c80d48003c41072004150741c2d585c803000c0d081a00810484c0c1b982440a881600c108070300d089440701081c0300000d843c2c90410809422074400317011807810044140f0041c413858500204a48948030400501d54990078900d00450749040300c0c3c0144500300768044180302c1000f0380000c015403000e00003408960002d03160400d05903200024480c9200c4c658040b1602d4650303c100ca01e150072800c0d5071190f0301c0d2405445c0e40210707a010480e40d1104805820000c1008405980d84c4610405406840d00300008191035490007582e0f82005000c1048a103a521010310440d607031503012042507800600003004918140b0800b816040300e1b025800034031400c1442c0210765460100309190314101035131406045074210784441259402000c0041d0651041490512030341c0d90741d4001c0e5008044110000c2503101c1c040c90034a5080d0030140c80740c1e050009500045c40140d035541a6034503421206035804040e50b1703821403100031f42d10382c503407001444490002d0f00050055000030350105582c022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 115237913 1250 115236663 115236677
    0x80c01060b032e0807081605010c05031207050712030506090a020c150405011d1e031305011d120a0209010509040803130507090606030c23180d0609080a 67
    0x81c10142019102c1215200441e0009803482065110380c4428a10044042030916810035116035002d890310314150004e40c540e900480320005400002c2840c007001e040d0a20f4084000d034921b0b65481e503280101d06082c1c0e1200c4a54000071f48451066055900c810b410a8813554040d000710b001600034135007900d405004e1441c410006051801d03500844e96600340c81c41c02060884282c0b03801d421240e001810440e4a07542340c803214003000b8002d5001c860841100c80241c81198803081544002c4c04075103040c041e01c0e41003489405894810051100c04071103080c2000b000b550782100d21090915400c260260340300c005a404210805400650444441d20a442d048096601e61003080780c148800c840040c84d01c40e0820020b03800050095103019070034454400c4411039612000d81c1d1080d10b101ea040032000030f98170369420800c0c03503100d2401040d202c004403518030140399488100c035062180c4207110148411a102d860000c2e140c90f0100050a60041c0381004820960319051402c0c0d8400300c0d00100082d24 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 115239163 1250 115237913 115237919
    0x9020c010b0f1c0201030b0303031f060906140c0a120206010f0b0306090a0e030d180b010e090c191e091506080703090f0203100c0f0302070804030615050607080c0106 73
    0x410b0710682100c0360000c1c1031110034810000c50262080305000b04034101612a4605040e541303007000a9401444000c0000070342d9440c0041c50420320000351320000030030403042c0003040350540280061240c503032042c514541c1e031414040740603d0501d001400400f000d0f08101e80c02980c60b800700760b050607214a6070800d01039943e100c058251900065890f81d500c1102c090114080e04095030105200108a80a0300e0a10404031130b50402c0f83c080b0001c1101c1e6a042601d80410404610201350150409094994850415082c076641e52410016117a0040144641100f811181081c40b90010070308030300300c00c810450100442c7c0c1228407608c11408254140b400000007c985404035030103452803540d40d03403241e40e02c076135084010b0105828103507001c050310034519002d61402d009299100886650101d10f008640e5030080c080c84203003e9240c00c052040c851034001440d4001107078100c0b80c00c4013020400c1d203d280c14200040c9895401680d0202c00000d903030f009c014442c2d01404002000302c008020fa695 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 115240413 1250 115239163 115239169
    0x14060f06040c0e1e0a0303020601030302060606180d06060f0b04090609090203120325030203060910060c030c1502071b060903111309051e0f0a050a2a09020c010b 71
    0x442055440d020070030207220f036451410a1001120303030612000b907520340b2101020220b15020040d400a90040e0010401802499010448650803080c182d0355a13103440c1d0008035070740105400c0c91502d8400e9091a180c4814402c56070000e0020b031190482101c5030303070ba0ba0071100e00268050b114000030b550420200003404001441400b0040303030080e02400c0d0270041000134460f16440100750700000d83c8a09003230301c4400800419108110750341c3e180103a403414090208807a0000c01008095607038801c140c01c4c4840c13540b2050503402c0300c0e450705200c001561945030001d40035000d40e5841900920101d1a03d007030042d0b0440700407030707c56404d10003944191030b004122882d5206002c0a45100144140c0c4000d505110f041e0813a1741c010500300240395645562403505107100200b2000c4032510140e50421019400d1004052240c001300080601e90b03a560f54140c2c82e0500344201620340c920b8410540040c2c503900724403110f0806803480808220f625503035002d000390003000e0b9550041d8600002407115007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 115241663 1250 115240413 115240421
    0x605030c03060f1f0e0709060809070f06030c090302180609091506010c02011110020c0106050105090f0105091507080301030c120512090f04020304080403330504080714060f0604 78
    0x1040d000804662541d540311040a4942040500381300c0e40300141c000241c104c11051900d0140107a90345003101186403040052441074060301c2020541c110070010400080c150001c2c004031520380c2808100c07035010044c140c6944c1320f260710103500a085220026440340103603001511801c0c0407030b10b00ca4991155110103079609103141a40d208070b1b40d100b0110710f545d0700404226010f548145001c129078281c400350a41010510f01c0254240d5401154078078010344c081c0503c81c040c0c4002e2a18904148003080040d140c0c010003100541840400251024541c496a01a0b600003072010802c1d65508400e1030200324a0703000b440b0548942580c9400455510701d03040e82902844d4100005140001c40110402560707881602015484030714541d0500254950740040c6120314000d084903030300c41f8031f142002c001448111400c0716005000c01c020a20205040412200039105241b001901e5a141c0c81d041e4018881c0c1030303000d0480c0581c100b400300481000140144a01601980004140c0303c0c3c200b880162 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 115242913 1250 115241663 115241671
    0x10e0f0d0206091915020a0e1c03050f03061801060203030403030b04060b0d110405120f060604020a120b010507021f0e0f0a23060a0809011107020f0409060b030607030605030c0306 79
    0x81e0b000400013071100440c000c4240d2115018a02d00c200c80b446800c4041c0803a070040488034081024158100400c1c500464442156008c0050703101c14900c29581c0145107119504025000e80804000329400d070315030600c41c013816800c030648040395507101d02010307640341c02c00c80c0c04400090402086014905260241c0412103010078003480c244000c403141100035003002c40000c00341c29014000050180d41c0c08210000850501024005882070200198102007009140500035130040010b064450b5101c609041d0118002200250f01c42282004803490f200e5020065401405000e0585001c20503c61103180e00500362190500c0104002c20721002e480300c640c0300c6a020300d4552040285400e001000400d01075400400c0909012000005031a5003264580c0c00000700b5000030004164400d10400e5000c240301c68409080c60b405074000b034980803a180006003e25164002e8608128035504400140200207060300c0c49858200c00060081220b441207038881e200e80c4481d842c7c00e04000c0303246402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 115244163 1250 115242913 115242931
    0xa151e050d021f02160f0303091d28090804080607110309060c0109080708071b0b0a030b0409141b1503010501080c0d0203042018040215070203010e0f0d0206 69
    0x10348032a8644580d2820300ca07000f42d029405268202e0184040c0034000502601c25000032414031400c605004105247d16002110b0b00310b40c14110007070210200c0503542c1d11002440c4104a814600f540c0c820351518052982a605820300e0045c00421580502400039100040111840341d82e451b40210341d00c1030070000c04940c2c2c1e082003140030040d0a20000400c60301841400100b841038032551046104e80c0942c1c3c046c1c1e20030202140742b030108a60100703030200d040c601e00c900902413424054510941d2060000c02c005041e6510100c070041d4079103401c12805142c00111000c521041d0205180c0c880d4011003815007903c40c06041110549040e00b025080043c21100da6402c5070b00300f100554030500d025090034807231481400900c54442186c0000d51060b4407890100100e4a0b81084004030503251000e1240f045c10410b2147c1c0d04981804000c50348540c04a030000c1d012803495501242c0381c440c4001c0a5015406c052031062010070001e41000c080c880c0318100d035040c2400316022030300e840702950b140c07131 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 115245413 1250 115244163 115244179
    0x303170f071202070b04080d0507020a050c04020a0e27010504060e1501050f030717010e040305221e03050d031b030504020301020912061608090709050a151e050d02 72
    0x207201d07100b4008124448501c2000600d4820340307807640c160b10b80d01124100c0310043c00241140f094000c41c05880d4121400380000c0070f1014603560781548590b030300c4034801e028030340c041004030a00d4413078036020000b0007018200c03102442810100303607518213100001070611065607000042e5401c0038840d00040300e20a01d0023401944442601c0940c1c058054100c5040042c14482d1200416035140214081d50b140e85410030321145030f15a41016201c16846604070729480b07c10440400d80000c01c0391512211802c00b204c81002088202d242c01c80f440c0c021550005401180d2000c140084035880240c1e4000c00c111400852420011000e4441d000302503040d100c403180040c803000b40260025504148020000342c28041680c1c0411550100039050000c2c5074089000d000b26a01a4501150488218130b41207459240040c0d44070b5640c0e102e40704004510395200000382d80c040e510341c8820720102c540b5040070300c1581d440d02c0c401c0c00b9151603241800c000c01603040c00a240d25100a03d0440c0d203034041c2000c1c13 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 115246663 1250 115245413 115245421
    0x10f061202090402040f0f090e0c0f060a02010618021809010f0b070f200f040903081b040e0f010f0b040302100e040e0604150b01022107030c05060c040303170f 70
    0x140c080d4100c042c00c9904207030244404aa02c00c03811001c038015240c01c0c1508000545001034a8080e1003c43e1121109500801088907251301c80d509100b0402100340e60407507454260890480c0100001d0384203030503c109010004000181c65001080c030b2401d41082070104909250030843c0d007040071300c2010140c03100301500700000c051100c042d21415000b401110f041e5030083e140c1c0d60707a03107007911070507517610043c2c050480d028a0010b1410300b985038103413000c00032005d4940c4d0182ca081d0000d806220400d00310003680700414401c00446001c0c0002ca5440c05603820004045203d8032000e000d040b1218019070404640040c214094030101c0740c00401d0540c00403140607003070f2481c4011450003174100744c07a220010024002005210700640c0306503040070210010590001c12140024581c40c119006603508851405221861002401490702465501e4000d841c0a81d105c1a07600401400d90280b50100800181c0e240040d0048070301039240c56003161500780e1004c0c3e02c400300300d036501050000d0708049 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 115247913 1250 115246663 115246697
    0x30f0c03060711120d0b1f0801050603060d02040207050109051e070303051305030a0c080c0f090a020d14090a051905030d0f020d0e01050103150b01020706080915071106010f06 77
    0x2040c42c0c0310100701581c4014480180388101d80d0300c0710f011200d40640706c8400790501d00341603440c451181c9011010004013010b2060042c002d460620645101e52808000300320306503030781c4a440d00d010f58020421075480e519032030180e0107031000e078000390307058021400180003c1c44c1040000c4040400340340071b02241c6085940580c1c1641114581000c210301d1680c0c08a0030745c504000449c007042c054100381d0b14051914024601d072811654046000e21a008400009519056051070304850281c03c00b680700e84144092100908105c49000008890401031124031800070548015050242d07055510070071450301c41c0411030110140040140e8802c00c0341c8414003850354864000c180d070446016242404280209041e42c1c3c404030f150f03189075581d400410030090244444201c0c500d404909004120300040041c1d2241090320801d4284031881c2c000844224091106144a250300600300c40303581401c240091a00d214050711f00c03e0703841402e00103d500d4914442000c1106e000365507400042c1d81d0b003400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 115249163 1250 115247913 115247927
    0xf110a0c050a0b010603050901050109020426010207020d20090609010303080603072c0105040e07120303020c0316060e012f070c06030c020d03020f0901080402030c150306030f0c030607 81
    0x56800380140e14000c800981940f410710300070165644c0105080c10090780343c608483d01a4003a6006510411003003100e01d0002c1d400b010b1003465441041400400341c50307001d02910540c07100030741c0700809410040400c0300c640c1c0840c003a282e27400515026110322100703000f8140029a400c550010502d401040020300c0b40da00981c2c00352000c0d007907038906503031512404141c15a406d1200c080500004401460100c95040c15004107011501446030110007101161110800d02402c0c04c482d0301140b821003454000c0e0100c894412802c012242c3c0e81c000c0c01e000120900715020215a410304044543c00b07020014040d44036414040f070a4400441e04054803442c0d50049101c04450556041c0050742c085610144d10700d00408290b10302260b403d0303000310000d0511218120700c0090600c18010307010b5032012282a110003400a003840c0ca025100c500009140c010040310b03695002e01220180394000f20304102541c002c81c42541200d072000025104103850f1031000c42e840d50194040c1001a503030b05e1049807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 115250413 1250 115249163 115249187
    0x601020309030f030414060702280810140a05060a060f111c0e0607050714130c0f03110703020309040903090512240105030c0d0201091d0402040f110a 66
    0x1100e1070030480340301180c103006000c0700c64502c540010404000e40f48400003040c0300703003008486091034180c290380090014440303070b07603000c98040405410500301c080c0540d08902a00c0303108121401c1d2421050a00c010700703c0410344e90310307e11500c404100c41c1c014a008107409488003c0201e0022410020708440c6070300140c06000402a000200b000d01030b400f071002001c101c061840b014040c03c540350b8040d01114201907201e005500030002d0030003064010901d00e09076122081c402d10020b140600240441c1c00480d0405089890000c070381c4444c80d08141d0300713000d40100f0b440510881c481d015203d4200d0089020180160300f0070001d60f2150314207984170f800400e2203410283c1c0d82c0742d00d40f000315841407803101c1c1c0d0380c22503444a07a5607080d100342c640000c608485100c50310300031036040101107600c5160714031050f80a04010304400c81168000d03007500340075046044108007840c49e15070b450111281e00351400c1c3e00030b61829544094450860142d0500c0040e031030420f030b10344240301c0d1080700d003140d40e05 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 115251663 1250 115250413 115250417
    0x50909040201140c03030402040e0d0c03031e02030703050703050a0b0d021903080a020601090b06031005010f09090507020102041409070e12010906050406020901030506040b01020d111501030f1505060112050601 92
    0x103c64001840d410301c0030340710f8441c40100854803441c191040c44100d0780030144400407035004a045001503070f4045910801c440d49480c0104110390029002000d410102201c43d012500100401c45407a515505c16032040c82d040e07905100343c0d1103d44082084401364025550045842c0489030098180700900c0115107490030741802d1200e541e51110703203c6401c640000700040e00000010010f0300000e006101d13a40c0d078212100ba2840c1450740503040c6003800380c450340c0d05201703400140805407401840008000d0030044014459858100320080c000d500902a00304403506a40201100d401c007002070034400c4c00540c83c0d0402c003403c040200401a84d00a891011964a0350302003c0090164011207000710711560001d40c03035203120f4001509a801c0104a00e00841c03a0500c020070b6a0390000e100d0300d00c07446a05003030300038800840070705d410301c00c560a03a0550150b00340000001c0000c8003c1c00c00300a4024002112405400c620030b900740c400545219000441402440505c40c2c050b1f0f02040e0400414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 115252913 1250 115251663 115251677
    0x1080705090a081006030b010902250f050106170f1501050d150c0914040203130210020102090a0b0a0f020f0304090f1e06090506040b181308030406020a0f0906050909040201 76
    0xa16029450000031130041c059180c1c03a40d2080040001500c10b6501600c2480001d6051000c041d51954501c0742c45034061041818048a807000d1040340244246202c1d000380c024018a500c4e0f00941c0b000310540c1e02c1c0340005204da007080e840525004640041d00714904408804a64600002c101405412560503a600d5050046002c000b11b810b00c1062440c0400d038603005a550300c3c00751054210021b400c644e0b03008900400400411410b24080d848007aa07044800c08102004024102d00a00801030b0301b0750001c0410784d000c50034420000c040d100181203a41c50001000544d00c00f2601c3d41ca0340c140c1c1e40510390040c40144003500d642d410400c0d81050341390b0000b400c600c0f03030792000091f01808a12141025035446050044803083e000f025400301c01540e040c021070701c4c50800b085030154ad9000072031908020034003107180000310705500088250080ba185441e0b05107420010000c0d4403085211020075900c09207a2669030050190314116a000d8407401d08182c62001071129846004108904104907 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 115254163 1250 115252913 115252919
    0xe060a150810050709060c0305030412050c01021c15050108010308070303110f1c020c0a0b15030d02030a022401030b190e010e0c2e0201060312260601080705090a 71
    0x20420440d448809911000700700d41c00d140c1006010503070540c06c60810844800070010219800c1000c9079001075124800c0341c8201d400180c12a0319008044040499500009500c1600340d0300d501c40200610208104020207040081c200035035407118421540410035400041002c25480400340c0380103406800c011450704c001400101850740310701c0c104034402d4404100c642c401c404480c41340c2d000304040e840452602c0030841d501c17a035030010454004d0108400d20001511309000280c02da0340a1f0015046600041c0c0405020b51240c00000811005201c0c591300302012030000201d0100d44412050810116400e60300d40c22900318000b00180c6803c8001d001180d07010143d031080050b00249000006255061101440d0400e040419030764070a004006807203050840c3c0d2a010403401c03070080514901c181d960b50003a8050f240b02c0c1e10240a041e11620a155020b42010300180c0c50104141c1c121070000100010620407001510000d00164040c0b0001314120b0041c0c00500c00ea1000901c06021295 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 115255413 1250 115254163 115254179
    0x705031204150606120e03040e010e180a11040f2a090e010b0d020702032404020a06050307081501090806040f05010b0307061407020f120f070602010e060a15 69
    0x442500d4040d03420124034200300c18080103449840140950320b2050001c585042d40052801a002a00b2503295540b0b20381046001e40c20011200107003105419130340d071903035034084071710a50f00b046420260480100d0004900d0310004281002c1d644da1013407942d07520300c04000c1400010b255280c803003c0129030b01c0741031708018407220500d89222041034500511440031408018907440701d540c05050502116030050000155260640e0340000d5480001030315091343e40000303494400400d00440c0500031000e08480c0448500d48030920444c000c2c0e41c651b081c00e546480803201c510045039580d00042448010802d183c40e28102c6014011052506032805034680249505105094500311060403080c0326040811400703028221403010300302c1c00350007024034015002c1c0101c5e0080c03098040711680000d10f1801c56540c1741c11003e010304042c01840c5018401c1000503640c1d10040b9030b6803a01c1c4070701d060004083c2c6c414001d0281c60300100c8064034043d114032910384082d00001441c03441b0f500c855040842c20307076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 115256663 1250 115255413 115255417
    0x5030a0b071b020d1110391e29041416090906061202030304061809110a030e12090613030609030c030905060a05030c0309120d06030204110306030a120302070503 71
    0xfa0150302110b1841d07145101b04421a8260703041c0906104800707600200f410b000e884403810007580c102ca2841000007d11a0031000600144002e2403c0e01809185c00f03850014500c3d003403501d101e81c03407140c40200c51603104582c100e105182e01c20100c2d114400280000c0355110503000028080c01207030040c0c080051080e6510981e07400c1b40740000d94031108502440400d0180320010f1540e0f501504010010b900070940740c1c405d074011390040c400b5101c0c00c46600410300c0560001052208010040403100302c0c854840742d400b8038459000a400d0140350446d6800115841801c0c400d40c04d01c0d180780c918403800b0710005070801404810780700310742c01001001ca507490041c41c4100b407003691070a0b046442c901d009400081c0a0b00000c1c000c0d50103000f4038040c5a00700d03049a81100484803d1612956414280d074130f0100005c1d08540c20881c04908043c507407440c0c0d0400001e4034070843e0b05012080380e4560b085c40501080b80c3d000d0380f6500c03142450303000c16400f450948502c1c0851502614208a94880301d02c0c503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 115257913 1250 115256663 115256689
    0x40c02010903090f0b0a050c03041d1602010b240405062212020108190b0d0c0801110c0c0d05072106060b090f190305100b01020705030a0b071b02 64
    0x540d4440c1c204000b0181c0c440240b4016100301141c192400341800083c41040c09030001040500c0310005000103074800401c203a400410000300c9540721100c5201060307010160698410640c0d014109000308440d0040c0220b421421014000e4050101104503038041c281010800c00c1010908000104950700d500000b0005100e02e03024844640c50580780340d4004040d00d0344402c0304000f604400c6001030f0b9000050540005402c0342501800e10035400030b50040c08080d100720f80c00514001d41c0010001044404000c4a8054000700498004c106901a407071107407000003200d5410004590865151442050402c14050b00482d1940c0780c0701c020f10382078075600f55800140048a00d0b25202008002d02030748001d440d0302440d140c14401d01c800030440325003030559a18810041c1844c5044205c285504280065810004568646607450120030040030483c0101d801400703502d0010401e828005035800d062544014041c4483c0e8a09400301c400351303040ca842c2411214011000c81c05603654080700691 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 115259163 1250 115257913 115257917
    0x3120318061f080f07092a0c0302010f0b0a090c170c0d11090d0b06031c05090909030a0914010c02100201020c010c081b030405240f07030204180902030c040c 69
    0x454003a444030400e4000030b550001c8072640c883c541c4840103c9000c40e007003084402c04c000100d05011011011b0310301008241c0b42c044100c040c3c449018501e60720103100c2c2e80c0d560180e0000c100c600ba0b002c44803019540d40122603904051170200030040c1c200c140c0d01054070092a0301e0001070904045008403402a000c0e143e000f4401c0c1c01069801880c002d41c032501c4001144000d02d00d140c07401c00d1011403201e4581c44800340807409032100180e0381da00c040c07240490000360b040099000800c0140050165013001210074002d80300c1000050b22007100004407401d103410b5032260002d0919203c1041d510038001d582050400400910b00f0740180c542e2101d0020425103070700090b0311242e600d40618219a29030300c03880700f001034010500091107501c4010144100310104415566034035810110301e0f02048812803da505002507101200900422086010780101500042c160715800422803e0340250301850000000442620090070b185900c581038131031014040e1400d00358804001011601ea031150400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 115260413 1250 115259163 115259191
    0x3010905060a0e0105270c191a03010b12040f050303011d0f01051c0204060e0a05041202060408090d0f050a03030204080d181401090905190c030b0312031806 69
    0xc01d00c1c02c1d40190140054084002c20840c0f4140d40d801404e03000850124401141200780003102c2d140600218403054400303010320b0b10803411507400d1f01504c0660701ca220340031009400a5603164008804503030480e10f810001509141c4400c01c81d100c8604041c0c0100ca2401c240000d41000a0061015600a2040000345c660207200100e4108042000401c500f03081240c550040c07103140d55a48464101c2c0209d521518003031079551020400a191070741000c40298034210070440f1240c40c3c4e400c001d10440c480e18046d29a6001c0f800c3c02da80d540c4040e600107107000d40600c1003e101382003014050803094001c01601540e01032a4071200c3c01c20040080603000280c0004041c800b1100c1000102007010461800c41804503005042e10801d0203075000f440000b5811038410440e6078418403000c405041410020002810024040c5824651104580e2582800c0000300706032517019210703011040d98003030064001c1d000d09030004c0100342d00003002004d2218041c6001c07141501c0c200300d420700c52460000920 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 115261663 1250 115260413 115260421
    0x809190909050c01030c0e010909020d27060606140d020d0908130608070e03031e190203090312040302090402010c020301180b0603120708040b0702040b04020d0f0608121c0b0301090506 81
    0x101950307000d07005502400800d020610090764489d0400d402ca03108000d0040e1180345000880000d04101482842c0010040301040380f00a581044c000c04503104003c1041244d070350b420251858606069440050b8005002d020315050480c4c00415804c0c1c00d80c04006071510166894800c640c116210a09040101c0882070001c180c11500080d0001681e00f003003c111490440020b81d81c2c81203040340060b07190340007051075a4204040035142e0f041d00710039040380f102c94803070780080d038a4000480d4248a403013103401c040c40d60341c003420442d030035070350090300440c1c903aa21074006541081007403104913015075a885021206d4010180341e00030300c9120f181005490305060b0205403909681004811481c841040510002040d49040b201290840c802d250703100c00c4103000007070003010f013500090f401c00d0002542c241c7d100c41c60340c40740c240203114200800c001c2d078468220790707500c00c1503079142803207000b0400071481c0171240205054181d0020901c04621000c01c000460709585d2407400485059101c4804c0c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 115262913 1250 115261663 115261667
    0x90105041503021308071a0d09051504030e0108040f030f0c0b010b04081b0f121006090c0206070c0210140f12060117040b0114060c1c030e03070809190909050c01 71
    0x10b04d000b0030513200108003150400061084421a202c030051048400080b08038078024583c1140801c560020b0541d400c0070842481c1c2d818880044404800040d0000300b4a0160340c02544007a0003560000d6440490340d08039642a01c811800f50400340c24800c0410040b40080c5822001d00e001c1c0c2240d800260b200e03440c00c06160325051101c44000d1121b0f0040c01c5410a0361140c018298250200b01c8140d0400c2e900b0101c001c2c100341c45450b181c00864109140030900ca403154101c88600e500303a5080311072a90f01c0030411904081c034090000e6104460501d41c0345414480d444c1030602c0425021468030f09803000c030114507140d00a44564601001c0e00080186641c0c0100f920741c4907660744081c54a00e46043e6890030440c100500410392420940d004103034a94541d94180c0d1010700c0020200c44208141c0a000103e4042e5000841c0020f0300703003d0204240c803c088181c0e0400d41e4054001810110f200080060101c01d4038006040c4542e5583c0c0040c2d011700c01d0061910302c0d80200301400c4024882c2c800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 115264163 1250 115262913 115262947
    0x50d0507050c100302190302160219030b09010c0f11150903091815090906042d051c090807090b030109020901060801060e0a1d07050c011103010e100803030c09010504150302 76
    0x2c801030600c1030200109c644542c481401c0c1c17440c5c6c12110a16241c015143d00d407280c80303942d00080d042000002c1003003615a015407000401000589801c0319281c04810200d50f0035122401581d0960840595440c11043c4c40414941103000682520704246084010681013032416200f41c424000c3d080a02a205044010800e55800b05032017a49040c0342c114030003940c41101900050032600320203044170b85584006203404000c2850012003000c90a80c0c14950394031049580c0c9288440403881c92020180d02603205501203c0300304001d485040e00d485520341c004c21258000355015521030000c2001a52613100c007a0180c0082e03240d0403025418504000d151041c40302805010310030401f000c4c4842811101e90110b2109001d02d50f41003590380300b070100c0700307070243d061242c00719801d01e4040804d6080e660080c1d41660450440400c07180d4800d82c40c2850360600784240c030002c2c0c00802c08190340a600d03000411100d001814190b01d4540d551010104420103000c00701c00180e0b01089410b1441d0404075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 115265413 1250 115264163 115264207
    0x12111606050a0c090311061209060f09010b010e0103050606070b0f0f1501050301030803070908121b01140112060e060106091d06030d030e010b0a03030e0a060c050d0507050c100302 79
    0x12040000541d0060050442a4240000741803c101a903d0038003503a100f034100c40c0008c00050402c0d5150070303c40d04650750b55400b6600824510700315000500b18000c14811044180c1f0169290070703d071008140154000c0030007402c425004442040480086481010190700406100d0641d16070380c41c000d6044a0003507000351480000c0c0c422a03c08483c0b0baa405070550741929000784030960389480700b100c161034134105035101051502801403005c0e984491440649070780d5403441006e200716000c11014038201d0b4511907004060712a190010f0101d14640e12521014921030306000802c0c07184880d00b0b5103003003401d92007031000032000c00091002040305d0981c00355034104045220900d003000b0300006d88030403c0061130000c0540d2800c40b25401102500040c3d05604003070310011516840f03003002001007500b9502240030f040355100014000740302d442c0360404c864101018055403d24010112604d5102d04402e8901e0710415010904942d50403003411062151518010303030300c16500103114000310101d9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 115266663 1250 115265413 115265431
    0x10f0e040b0406052a040920030408070201140d0b10020a030e0405090a080316080f0405030a0c031e09050102010617060a09050111030c0702040b0d020609011211160605 74
    0x2028000000da1080e900c541203036000d070f400f00711a650b0600082400542c01203604507010700c1c11240111001c440001c005958468074207020080c06240b61825615544d080349258010800000380468252006003036082d1051600d032542100111150202d5045884042006603550183c2d12161030800c41501a5404030b0000d44500c0005481c09890040300060b01c41c01a80c55100144c01d503034052250340d05540d07100c0042e9440e801c01300506c0032034203008041040400c0c80c81d008500104426496030307100e036600c01d0065142c801030180072248a01292000c4090002103c110545480c9440108058001a66500708070a11b00745c002400d40301a58480d060007005620442080c20b004135030107034016440f49002c00c4440c540d26020380101000e070242001403802005005000c200c40700200800303802290240280d003961002c01078000300d910b9009601c81e20030410300b02e1079400344c4810390314191a02d0000424449e80030010090354010040d4100000100d1049410082c85204140d0010180 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 115267913 1250 115266663 115266689
    0x30d03110304020d0201020c040606031d2a011205040510110a14130b030f04030e030118140c06040810140601080705070c080d030219021501090c0908030f03010f 71
    0x4030012214038440540081d0065114460035400d6900801035180300c41c00192042100e41d03940c5c84018018030a81910440720707a078050208071045400190045004503812264400350150078581081d045004030b803030305011461010244c08640f500c42c96100c0c0e0f0151000e8a00e1142c006445c0e0f00721a0000c0300384a06083c2800003042440e8820000301c0003041104800e982c0e82e1800380b1580c51490503070701040702403900208100b41e0760383e0043d9071402140700340c58840b1050b000000f05401d0710507040e40d0f01d203154a9648440042004400041410305443c000c0e00e070814004000304801e54440c1e0090a4264081611540c0700e002d1441105803c581d4564030140074244900000c003940d5014100303004205020544106200301d84001c4401443c0142c2110032800207104050042d40004030720a1080814440703080d42c29002084006040e1440c0c0103200307039a07080802e210000c0c4075140070f02c07040007180f102c0825251803c00080c1086625070f61980c2d243c1d032429010b80c1014801e07400135039000c190307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 115269163 1250 115267913 115267931
    0x30714040e041e0804090e010b10030c080a06030b16050d0603081b0606090403111005090d0f0e0d14010906020d020405120a080d09141009050606010e0a0905060303090a090506030d03 80
    0x1880017500d0a6428030503020800c9044940309502404101480c203078041c075441d858102a81d0540c0c008401b40304151110100fa58a0403a84405c6800610000d441e0a620304001011750900c150302d60b05550316801e040d814548001044811103026400840321803030000384081420541c3c03c40318410b4004c1000500680c50128045007036890003a00c000d040c00764014000e10084030500049204901e0300004000c0f628160403490b81c0e4000560401d80481c03510607071104c880344100000000c040700603142c541c6040c081d03a02c03021708a200c0c80c500c0019542c1c60040c50000344140c002003c0c40c221203000940c40d81d040c941000849203504000b020036620240c03d00001070300010550341c0d402418140044d5a80c0141014018500803202c022901d0046035440008003001764005601c080c050070032104c0c0350740c07141c00658908090300010380e4007440114081002c000590001c942c010000f80c01d490914842101003804420305801200015403a90100f00b49400c08200c14140710300c881c5001e00501c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 115270413 1250 115269163 115269173
    0x1120309030b0c0702030307060609110c0a03080612030409060801060605030907060c05031902011e0e070909050106080604140c01050a0905330a0917070b030714040e041e 75
    0x640e440001e000d915103000080c0100c0121058400301a00078040d20780d10b1059150140c001c00850142039200f91400341203420742c803901025034000c0740d0b1001c01420784494a480966030b020004244981c0302c410300841042981c0180060801810694808600c050030301030702d54290780d1142c0055040280c10702c10001c4451002405504031151410303c0600e90380c407800c001d401c40c4108410103409048042d10303241070660562090300f000b000d51100c0e2820251303841500301603c070040c1403c1501c4d400010b040c040c02e000b0340c2c03100508034403800000811591355000d09080803011607050701d00a119000c03580703040c0010302408100c500d00740781032882c201113000c02500d400014052140a4a40b000040b85d511668040c11801520b00302c0d1007402440a50004094a501070b9051400252a60780001507500150340c4000743c04421001801c00141854800c07007061304014084c000700001941c04500d00d000200040c005410b8000c803c84e1301d0310301414060384802844040b14507007403d045c90480030138 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 115271663 1250 115270413 115270427
    0x209061e010f1103030403080a050907030302030a0f09030b0103031e020d0203030c090f031015060203030903031f0308070f12051801030b0409061803030506010c080702010c020d080a080f011203 85
    0x1400c00d0900041c00d01010104498040322501245014400001444245608100c1c1e6a11900c00d0369130a011684d82c1a844507100d442d588002001b5902c1448283d0a160180e110550050f41c1c624000003202d580340c948180b0658203a00580101302c4800b08803200e18644001026480114002841030301d0b00d1300c9000b9580e110040000c60b200401240c0c5400d580e48500d0303484401540241221010012001d046000f08084404a84c00c0b4034121000104180040180e902c0342000c94042e50075540d881200691402002c0c02114500b854601d0100004401c0f00c06440414080c0f803102e410280c891528040500d040380003e400d000040c0610015600b00701303c207008606081c41c000c12008042e030301040241442d040d0040180c4e083c90184070310f001280552502c210b0007a901803056480301b40055031460b003c5400904021801c1003514050b50051400481091001c0c05101d5941001d03111525981c00841120000076550010b000c010303407000c0d98450142c102075000c20110355140d0383c0a0000c1c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 115272913 1250 115271663 115271719
    0xc010516080f0d021803190f0605090a150e060601140a0c05030d0c051815041e03140c03010c0e030304030308060d1a04030906080c0a1d040612020906 66
    0x30040c0015035240c0e409955060f24520b028102c0113646664a40440d004640c0504100e14000d21900514003240c0c2a80c0c0c2c648a18103030480145500c215140d1540009414010040703031070b03841b80b0080e40000070400d00444c21812100c400008244407440e1749141040c2028103800d04018110312210b56403a10303001200d07007514490402c10f02da21010728040b815070140003000c4c18041d00e40f039045d003007150b0045e00801c11901522001049403202c44104600304100c940131802c030035414401808407803400107c41300c0710500702c1c198680e4169203564894080d0340b464000301c6a6001603100210906090103401c0182486045c1a8000c0c1d80c10004283e59000c0c603c0040d08118680340490446d0701d41e10028800141c0248070700c00c0b110384142480400710f0081e10120000351100a0010b203880c4144040350145207035000c0240740009a2004461091152040350440a45200b038130aa5a0305e500c58038004041c0034109400d465900d004000c08044c2c0140303402d02030076204803505011428500703c0c4940c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 115274163 1250 115272913 115272923
    0x3050615040b0a0501050c1c050403030210020310121104050a06140d0503270901060201060f06051303030e010e120c0a06080603070302040504080d05010b0d0b030318040f0b0405040b0601020c010516 87
    0x445441080251522320400140002c40a61204100b20640e00c88000e1003500d000340c08444d10010350340307000e00c200d120071101c0c001c40440310364040c40300700301c3c010610b4805401103021400c1d00042c900041e0464406860952450b50b44840400c044840e81c80c2c1e60443c0c0e0f404807013102081d401521955282c0c0b10b4500f5004010a69404200b01c0c0c001001581f041d48102810694840d0384503800a402081c403402102c0511125040020f1054450000c035825000c4580c0305440b01890350b0344c01c1d101c1020f03001e0554103020804601000c00e4480c61341030401e8040d08401864608060828810000760b603422020401200c8010003e1503140000d10710304480d030542d40001c1544d02c80c00c4c04082c9018903078900a04604100001603101c00c00005001d05480300c200811042c505081010341d680b01d50103036075603100c03032019102846280541c068400c480c020000030480070403080010b42180d404540855601590406102c010359040025551444081c20124a014581d41c114216410113a9000788 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 115275413 1250 115274163 115274167
    0x903060e0a42090c0e0a14010b09041505060a021006062307020a030b07030b10050307120b011b0501061404050c0301090e0114250504210c0f03050615040b0a050105 72
    0x50b0440c9a10800320190440300b2100031a469900c020503400056400007880e6003403000000c0e0525052404030704a40034482c4441c90031b02d1a405100291410819070300c44441c08090020b0252901c03001031086080c55030107040c01411446032801218269000002040410124450070b002d4106109841d00809130703106895190510000340401d24940004100600c03481c1444040c0f038040d00104180d000c220703048460310520b244100d43d603010880780200000c2c040305248207034031641d80c0804180b150601d8141460415481413540b207001c035a0b8100c83c0d5030341d01e80c020005a05541904103510304110ba042c002c0f0304100346d2414042c0818010b541030b040d039888031100001403d40c80306850031246408004d01e4034000c402d02c4d4140040e010604110070300f807081d421856100720308503416521500140c1c66000c20420035003588100d10002220701003111100415000741c2c00d403481005610a40c01042c2e64602401034101c0820800c51103030255080c0700403070800b035841030380180a0344d8080c60319903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 115276663 1250 115275413 115275533
    0x90a0204020f0c0a140c1f030c0c020901080307170a0c021c1a010e0a11041401050702031606021b03030a03110702040501090f1116120903060e0a 64
    0xc030a40725000803190742c0e104c0d100c504400c018901e22100036003804d0505030342000c1e18842c24081d6600305107050104100110000c415413500a81c05902000d41034070300344146049641c081850343d0020382002c0b00960001c41c2071010002d818000c400c0400d900d0b980c80741000001d10f001340450003000390080c410865a841d0f007031084000032104d40981d401c61064500d580c1030581d2484030080c20300544e54041c00700e8001a03400070460203400c6001281c5400c061802e03192401601d400c005502c1c08038108a8200f102c03201590f81008040c0354a09030600c0742032200d2071708402034507010300b685140b0321100c00d80d40c0210303180d074010094440e150b0640c200071500e60351a6542c030025101d00078000354042c0c0f4080020803c4010741c0c1c408a4140094101005540d007030a4103581c043c0650310308c001054030b1200d45100012981d11401c1721190050810b41080d50f03c0760380711303002c1e0f07120b0407043c9071141d00c8542400d09000c104060036040a854ae03403010001c0da00e412001d400328000300c1840c05150f140911342d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 115277913 1250 115276663 115276687
    0xc020a0b04032006100e010806040c140114030901021b0a030c030e01030605060a03060e070302160204180f0f1104140f0702030412030e0f0f09041209050405010e190203090a020402 79
    0x2c80f085001410f988003842c003540441c84d0801c4038000c4071a1074120200101f91101d0000f1201c0c011500681d0031000d0610700b44400128001c128010360401a0071942a0020803a0f8405580124203110000d81c030b425140c44520600305181840c1d0070644e020381b01c8034012a40000034008079030b41500e0b10010403061640160080c04480d8090307078004030001440b1071021740c5030b4066006d40321707101c601382d540da00c070400c0c01c45c10f030b0068400d100349000300c401103440140f42c241e01106000c40403800c00080c00030380352202c06a110070604183c89040107080000200660b5042c060f4200104030740c1000b01545162600020b20700c010210b11001d008003000c159084e0003001900c001307009000104100b890b80d450010201a940c8501d20300800c20f114401e46070b403500c0d91a030501088040c0c0118a182d580e511148030140e1920703420400d006e0744150100e150703240c502545012f040300101d203000a003070600d900c07148d8403104440441c88500c148103001005101040306031805404840150b1110003a80708 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 115279163 1250 115277913 115277957
    0x30c060b0319030201022701050f031f0305060406140c030708190e0106091104080c0105160501020703050c0c0d050c1302040b0a20010c0906050c0c220c020a0b0403 72
    0x142c40361a02d4484003080070964150028180c01090303e54503882c40002040c1e91b80707000342c0f00049a01241090201d2082c0c981c0030005140e00000300009510f00111808a41042c401c0c60f800070b07212508000704010901035240103500794002107400c0540149001c401904041c0405000302041199000100705421080c03071981502a030000c07800c01c2030f0724a018540c0d0017001c440c0301c3d103506035090004800484a080040e1421661484081c002455a00004494641c0102c546046590701c00c04940c01107402440640321103880303515040d96456411000c1403400000030b103100d10030816003d0080000e4008200e44040c000192185082c114640d000400030340115000052900c001045801906500c05220881b102140c1a131811050180c1445403c1e60b0151047c031001c00c8281c5010420203104500400d40512440709480c0c6d01d20000001a03016454546445132074a184017001c1c020170038a102d40410303c102d034002008414002d0f912200c0c0704000920240500c20b0030513128140d5940c40d04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 115280413 1250 115279163 115279183
    0x103020d14011502030702030307062c01050717040f122001050402010e1e0f040609020a0306030605090d091e08060705070b070543230109030c060b03 66
    0xc0184884510403079000103000c001d10641c850400d9004030300010300d00110440c0c0340242c0203405140742101c1030315810050004140d0403a21801c1018824603c2c500541210141040d1240042081e06285000030f1602c00040d16003403030001c00d002804002000f410031445d420f5800340100c00c9104c00010f0654500b401d064100e110000c04e082c00c096000c40650200d44034a07c00d0325003081859801040c4050410b500904007085003105004c4043c1d4581807119500540c001003010401c81d40b161141d00c16a00050703006000300e0703102c04045c002c110b801d0149591000030480117080c00110741310700034510a0305d480f0b41c400100c1d40da44041d91a41540d14071102a041c100100c3d90181040c0c0b00c010701e80e41c4490f60035a01d080e83e1b90007141900e480780003100d05c04003652070f404444001c900642450310309840002150a4801c0003803409140030340c1c055230b42050040f180101035100607103031b00340c110205d40786119142c4d1514400c1c00010350080c6416048642080c0000f138286c00f1200481d181500c646 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 115281663 1250 115280413 115280437
    0xd0303020d1103040c120305070b15130203070801080c010518150301081509010b0117060a1502030c0c0402210408040306022b0506090109020c030909040609020315071d010302 77
    0x28050001100c8010b005602852103190700d640aa961202d228100c858161802000594200800008100b002c1035030354000b12214007001000182c8400a40c1480b600c5110751065078012040200194001803141e0041600c14007600f031551701100000d200303209440c0d81d1624440c4000705d54015071221555a400034141800e900e650356128002070350345280075a0040040480000012200c3c081809060400c12040c0c5403448403281e007003050418140020a41c90300409106000034030340302006a420040c1c45c00790040c40c5d46002c405c48203410301c0c0f00703400510301075401000a036030a800446004408044000c00007030f000d40741e9107084e07111440382d5070016052900101d0848081140c035611038107030090105401d01d1000841c1e00c00b0b41910740441f02c9607402004980100310300b94081d00200788500450341624a4140b803440019868601070728199030aa41d903030417a6007141003c0200d40c1e4030b5010f414540700186803180b0300600381c40c02d440362104980c20160807071085034004e40542d14650414 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 115282913 1250 115281663 115281671
    0x190906020406020c19050a0306020c0a0605041101021e070608070507050304080303011412070302090a02070c0b040503070803040f0b071e0f0507120209130f0b09030307030b0603090c0d0303020d 85
    0xb41000030b541e048a04550f41c401e0040440781d0001c607000c5855002190070144c5900801451611050000d41007062101c42c00d0040350300850010301e171403203101d03c654840e480c1a00d00220b840e000a203410001c0e0604098040440c0c0100d0340b060340041d0b007004850051415001e0350340c44c2c1030f0403a050700421000400e82e20001c2008100540e01102840c1650080b407010b1140d1801c403000c200002490304000c1c00350382c019030818405410041c22280d80a00d00d1400035140c514559160011010954000d01c01c6040c041014011441c083c00000c0003000c28030019401c06040c0880ca4550350001e100e240340601c40000e54004015090310903c0140d007415040c805825a02d08104880c01c101c298101c5aa0154000105185403c0c0c00c0c0c0e100d00c41d401a12200d5180d80d4050000c102202c006000ea410403072621502c000260340d000d0362403107804031501542d240c1c2814040542a1000031064511071242403040011040c80020600804201119074071460001420b00307400038030854080450090030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 115284163 1250 115282913 115282919
    0xe0405030f0301080d140f1903020c030d0f050f04211211181c0b0c0d021b0106050a12020402130503031602010809030301031e03020708060a14090c03061909060204 72
    0x1c43e200100151701c1d2940c101003403000388160403d1107419556035035840c00703100c03424100c00400401e070780321126030034014a01a2a07000c1c1901c2e6801036000c0c61145030712803080b044658614040c55411411303980c900c2c101030a2640c1e600c200c0b40700d01070000020803120480c03051500e101f480d442c000301103030340c2d0304000f020981c1c03200d10190f52049141900d80c164070322100741d1030704004400039511080c041c81d9a41034000c3d6a03640d030402d0406030052802a03010310540f04481014801006c0001120313442a010140c0c407042c840c20b4403003d038040ca1041c8004642000b28141402180843c260b048030016600c100301280030000f0032041d00030315050720000c42c0402d00f11803001c08031841c1d1400bd890700000340c0d03a200c0c4c45581c0c0c2c0c403003404003c1440c4071441c4840d001810150340050840d20038015140400e448008040c54003a0031a0481c1915171550f5101e001c500d24204810780143e00c5002404080c42d0700e002103540d0304000340104110310745008c0c036989a0360745540407050b2954401002e40d46d0342e603 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 115285413 1250 115284163 115284179
    0xa03060603121d040e15090c0a09020a0807050702060c0703050d0306090501050a03030309050a08030705120f060d021e060c01021305010903240b060304061d0312010e0405030f0301 79
    0x40140002ca46401814410350030890080e05030103107440c9192054010404010144400390400310fa00030308078456000480079111052080a20680010000f03040c030501110800c0384a80f015808030160034410003030005010703401003040e076001c1c80c141052565841c1d18400305e403c5120300b1241c079a40e8000d6440c0881003141c00f00d07002a41f12410381d02131060319200c1d14a401150000e05c107859110900301002c100080c06600a0700286004c2d4040ea513440032584c4500c00340c0c3c0c0c4211030305000908001140541290f4580400e60422141c0458100500e8420702142415041d1400a48a880c0412080482c06211041344504034009131005842c3c1c640544a24047c0d001110b0b0400c0d04204240049001d51084022500305d13900800284c58041071070606031180089103440c010150f847d844418507540360b207401980180e101c2d0b50300082c220400c204800350324200c0095818660400c1100101081d03038107a0440c19255101c4420519440c1c525003545548640549402940e20100001500c44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 115286663 1250 115285413 115285421
    0x50d11010807030606080411030304170a1502040302010c0b090f010207060203090606011b06050a060f030807050607090b180604050306040302070801060e0f0c0a020106080304150219020a230a0306 86
    0x52007a21824000c0e00c0d04407055065414034000c0e40c001400c14000203002c02c02085040724001c00c040e0a5a24003030b1a030200c4a0445213000d480d8805034402c1d121702080006000030246c609154140440c00c10303085600081c42c2d04c00701d0390080d0004000c00046140e00c101400031101c1d070401c4600840da910041e181640103900304542c81c42241c00340300005141940138030b510403000014808241d401c40040d954900c010705015046180d2243d035800d011501215068070103003e180106442600e9442a00d0601d1078440b00400140c01c00c10b0388070040111117624415180942840b9108042115031240424000d0140e036005a6040c803400d0f06001c1450340228500091392000c800902c40c00307444000204886100381c40711003d0038080b40010b04c071032390000c000d40880080b80c070010440c075649020322840c0d80c00c150000088118a941120074407501001320544e6810340034807500603410b0507000a0f400c48054440c1c68582c0c6a4180030514400703509035041703854a4010420802184c49007420f200034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 115287769 1106 115286663 115286693
    0x503090715080402031c020c01050a050c030706021c0b060f091c061d06160f0c08070b0a1109090a0b0307090f02030907060f08070315050d 61
    0x300c6118001c01d0118035540e200d4220382018010035081c4030290300c01c03203041032100380203030222138010488440303400090803d56224448010b003504e02c2c0c0700b0503190041500001880b101040385943c081c00c030002c44003a00c5551005607403440c01c01c589800300300301d41c0070505100502e190070742600208140c44000e03003d412a40203044006010007000c0380c044440359252028444518103030f000000552150070018146401d240c200002d114181c080101e040041e6000f07074240d003038002c090503440241c0c41500039944840604120744116403da80c00d2407441d082001c00c60381c1400640544850700401820403002c1d0b01d8005c0b09400500c02201110381500035281c0000c0c854446104000c81d0a040c00005680c6c3c0c500210102e0030078180750031050911000060114031194048007860740445103040014940c7d6240d510f0b0369681c140ca521503a8408500484901040004da54809076 = true := by decide +kernel

theorem cover : BRFrame.Cov 115107913 115287769 := by
  have h0 := BRFrame.cov_init 115107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 115107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 115107913 ≤ n) (h2 : n < 115287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
