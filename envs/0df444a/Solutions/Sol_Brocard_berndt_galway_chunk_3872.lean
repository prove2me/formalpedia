-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3872
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:55:52.117078+00:00
-- url     : https://prove2.me/submissions/fa0e8f94-b0d8-472a-86b2-3d36cf3b73fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 696223021 ≤ n < 696402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 696224271 1250 696223021 696223037
    0xc05120106180b04140a330323071107030506240a090606030f0204060815040e1b040608010203010b1c1103040f02090906010812030402040603140715050a 68
    0x18004a03268000401d90320501821524009207000c0a50001e000408030005c113150040d0158042002c0500301c4c0e402000040404a04103580155582d0f04042103004000130400500f01281c04400030642251411240c500d400103a040e915079054896104580c0d03999284c40d8400c05954440c1c45081c02d10001b005035210700c01103011400d0b00c0100d290843d51043c101c0f03900c184144c000500880c00360340204001075640c4014884154517025101001201003c1980f074140740c40c074001c0c800600142180a8840440b071101650f65a0707030031511404204500301e46c101130a2400c0d8400144042e01528816841d14200040d08401070090301c0c100c8907040a154207050b500510a8140d200311751843c001c06a442000041d01c24520014601450060101c48030800c014414000040f00140c42c020659200c0e2004100703001e0005061001010010320090b226204c074404507002d07056581000b854098801080c804803400080c031001140c4020b0100b83d18030301c84800030b4a0611545000c000041d45203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 696225521 1250 696224271 696224279
    0x301020c0d0819020310062d200102040b0901120608060705030a020c0601271b0302090301060b0f0310140109032306090c040b041a041d1606030c051201 67
    0x70402950f00030724100100f1800740d0307030341c01c2d9604907070045541c03242d028181403041c0b19181d8840448140134844010300c5240032495040303183e42e05800c0d50390a0070084003010740d09610718a0084000380d018040020354890b034842c4540032903500210840f500050706140104510100360040204440b040da018003040d4440c140102d8241e440101440c040729000c2040712803c1d00d0801c041402007041c00002d103040542c81d030360b40b81041c400e00d0507042c0f240c2c2484c001143c03a081c00910000c04400a09006030394000d40c0c00401d0150005501040303a2400c0450441d821411640c02148200195190b000300603449001c003d0482d070b40f03100140c0c0000c400c80c10910028121074a44400c105c0c0e01001ea4403d4040050b4403482c1a070122000c54541d00300140600d2242400e026041080303004403801d015040021241c004060f00360f400c0e8500c102e8803803110224035180008044001d903006020303039440100ca009200c1c2207040e90b1003010700091074025680d1a03240b14005813009640d5045140009910f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 696226771 1250 696225521 696225527
    0x18050d080306011707030606091e0902090a0801140703060b040f140f0d0c0503061501020c060a03090b0a02031e130f021c050a0c050a060906210501090203150301020c0d 74
    0x40100254180502010b41c513102450040d82d0900c00e503400e40d80440c0c2c2d9410302000911003c00c5078010b906c0640c0208601134108030041c014000e5131441c400058807007454100107500826035a101d05659403030141c44a240b44040c0e6000d600c581c4554400748245030303450402e040d00e80b107603100c9d00000c2c07450541c0038407050035070300384c4042090b100408281e03d903083d020001c0c001010700c2d0002c840300704140b50104040d080034001076500c00c020400c401c5800000d100013070f444690000405106071400500d00140a0195011401450700b1908544061610902d440006d60055506c07003003e0b40040c000500d02103a007104a8441c09601e41c00220140c46a6503004415800c181c0c102e900004030600c580c06041c0300d160180086004000a1807000214284032030541c0094001600401e40d41006000c0a90060003440032902c0340c0c5000079480329400702c1188600100401c08081341e0070300000140d081c1090300614001d903481442804003180c0d900c00c15080f8881c515001c00180c1011501c0500140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 696228021 1250 696226771 696226777
    0x501140d0f020f09070309050c010206090d11120c160b041d0402240d0e0601081f0b060d1a0118090c02031905070308070e030303040b06010309060c02010c18050d08 72
    0x407000d000d4103c2000038100003000048111340600001340d60380034a00601c6001c11007128885800c3c0050121414141d0015464640490000c0140429072102c4886040d0030046481e6032140c0d031820356200d0304100c8a003520380128990101c501440c440000c100030141001b15001c4507124082004502c07110320b040703003000100400980e80442501e11a1b60b905000c52118650100045085070386c5103400c440e00f50848404003502001940800010701c444900002c1d181420b940302d4003400c1ca030700312981918018114410219403c00004a24404082100d400c40408010680345a0f01011015801102c0b61045882030b80c14244000c181040041c0140d0f00625102034544107032842d141a0b1445480034100d9001102c0004000080180a255000b880550030400600e440070b031104031440000e5032400b01403c01780c20001c102c004544031768080d901c00e490103a0b1010781440000032822002e4028001c00c40c11707002243c4040e40c002034807051811500140e5100a10105100b16961a82d0b41c003a0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 696229271 1250 696228021 696228023
    0x1201060e100b0901030c050c0601030804090f15060c0c1715070302120c21042010020a020f0a0305060703140c0903030412020409020a0b0406030f0203093a03020306040501140d0f 78
    0x103070070023000540c403000b4000d1078080d50269071100d60311031802c1c114104a13000802c0302038803680b41204241c1c80209110000003141e5091400302062401e50815810b08650f0340d221040c2001c42c9200d90034140c0c800720380f6001d0b241c801008480c10b641c500c1d105030241e02c55020300071540042100041c1c0c4407400c2d0005000102039003070301061402c5455400c4020300d24203403010303038801c15240082040100c0d1600035003940300099540c0d0f500740d182c3e00e03006035403000f081800034802c0b10035072101e00f0030391941301140c0025500b0208440300c80c10f160341e020b4001c3c40c03110805100b180c1e940000821802e50a001c440440402074000d40c41c00b8035210040000c01039410f01241d202d91030f0120003015070b0303508c5002c03800342007001c199a5613540380c440090f00b11213800704848125401401004186c100c00700c0c91b202103e0705001441c1307000f40c0210740900b001a0740e8844001c4107400e045400e041c075078103a010314464102651708210030b90b290000020314100d00003282d50f100c0c0290300300341c0c00a6117459100d1135503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 696230521 1250 696229271 696229277
    0x801050c07050c0d06021e0d0606090e2a0d0e0f1f02070c0f03150f0b010c080901140d060603060509060a15021f0e0c15040605090d021201060e100b0901030c 69
    0x80d5400104803014559007030324903861f10701050b903007207403500c600c904401048a81080e4000d24948940007900d032000424500c2050000204503c070a511805020700140d20301c58140e40da070080b40b05100080541e41642c1343c26105500705004001130002c0c0b00f12903c52145c0d0701e60090480d800d8140044d5002620880b02800d50550014220000441e40d0016611520384500c0519900c0d071903008a49100c4038100c0c400b402c000c50011580d0b003009070b081c101508104030315501c09101005075510741e5030b8207801c0b0480500040006044aa81e40580191a000c2d0740600440b40d48008010030110240c5a003540070700d44c004100b0002c00304505c0038020b902140156001c42e5520410f0008019810032000300c4c0c10f80310b0500c2084500184400200c3c0c1c0d40c212002540345288503c046030300c0c065400f511061103c00240803401340d44004100c604103900410521b1240320398080f140c045e00c00c62003144650422036022034200991000c801f001c3c1c40d5541c0303509040062440c0114050f00340042d0140038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 696231771 1250 696230521 696230527
    0x501050f060705190f0215040f0b07021807030605120a051c09030503070507140405071706011710030c06080f040201030c0903060e0d0f0302040b030a0c0917070801050c07050c0d0602 80
    0x80d22540f000c03400400d45c001d49482d5452400360043c004410000707400300c0340403102044103024158018040405440b42201c1003502e0f00740c144046000f41d0814101c0e0b00181541c24200502c4a5140d0001c0040d1982600c09103089050b080010399a868400b60040c580d030054060100c440311700100702c0078811524603081c0d0750380742c0d00c1d159103085a00c1040152540e400581007403103000005100103a03d80020381e0100900e00e01010010035002e14003504052406040c030124405a06c1541002c0703000d40c9180304000386c1e091508440c8038580b410310080780ea003010170b400019503d000d12038881c800c1c481d9542d0020982d9481d40114001e11017089000240000070b08084042803481c0304040b8440342110081528201ca203502030406481d480304001050b004020a000c0b191030304040e039400940a80b40030031401441e4905941107074031504010440b03000c40207842c0041c200000d00e2411281030800030002c80d03e480c0c040c005c0c0e500c5080406000b90b030064101c034041c3e0525420b000051801b8840040c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 696233021 1250 696231771 696231793
    0x80c18060a1205010209040b0d080712050405102c0a21060504060207050106170d110a080705070e0a090809060c0c10090819050c06070c030512030106120501050f060705 74
    0x10012825100f601c0e16940480c010083d805e044c071410269080480b00164000720340d03910340d8070a104010000b441c0106000780130400d81e00900603580904401040c00d41038141c8514010203440c1410014520281d58901c0d0000b600d60180b40700c1400c0b0320150011410500b40402c8101c1c5003d000d40089005040b5181d00700413600622138940510b21030b510142ea291518103025003916003a4014104841000c0f0003035182d1580000d100813880c0d0a81000e10007850846245400c0c02c41c12880a4411100052600304006c004946030741950711500a440b2142c40e240390740760895030052001030a0950800c03100403280f40c610090120b0101c20811030300c034003522101040d1207840f55100d40c004a00810720a1045101c148206600c81501210700d07086484282c40b070a5841240d200e89902030700d00090300009008a0300e8040c00959000070484103001a40391000d08598400d105010005450010054a04401d40922412200e0041085c40340d031040408005d0541d000c0c44003211039108400b00c1017 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 696234271 1250 696233021 696233039
    0xf0f0807030e04050a0b130b0d05030d061a211f09060f0902030c0304260a0503010f05030a050d180504110306120f0d050a03110c010b0a080c18060a 65
    0x4040c040c429614078404600407000e000640d03001400e07a08119082c010045995150043d001c440284000030108000c0d03440d1001c540741041408000d4000d00000401c101440925080341c0112105600d5441815000700300d07500050255a207581d40c42030000110040b0300140d420441d4101c080d401c0c184008490b00e500a00c001002075001c400c905403540c5003085000368410b01741c00100184403095240d803520b44214511444010801008541c0390062026507004035940c0c0258030030740c0c20030543d80d6550400c014145410912455a55500c02d06001c0303002d0401085a001140d4840020482d80e940c0c4142036039148608201000d24080403040081c140d51203020b8091081101c0c02001d54a00b0040c0c140550101c284a1200541d8000c881030b201400000682010654140c90183c4c0c6941c500362040f0044c00050048101c121070115540912600c198440c24034101c0c02c503004540590b8811406845140489056500c0000300540b4200c00340c0395644c295002400500782c5046c50b4460400c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 696235521 1250 696234271 696234277
    0x10f050d140609010608120703090510020106050913020405060a0e04060507050915130e0108030f0a122c120d0f06050d080a080c030613230117011d0a0f0f08 69
    0x10007543c0c0d1140c00400c05a0401c0c4003940c401c00d10003c20522300f26036520081d102c80d5147c0309103402405141a6103201c94402c1d40704102401d00108134130882e0401c3c600c44002a8210701c030981c4200d282201064482c40e220346104112405180c400f40c41d40d407a510b401004000041503001402000c222000d120390760001d41c603055040032203255071609800c1c860b442d84c1c1481604a1100c107481c800051095080000c01c1d90780410034075509980c0d4910001c0c2c00c4400c0d100c5c0c0400500d50b542800b400d90420050300b21079041031080003e40710961802d540c80640e44e404000c480341d00802c02003040c054480d034640c0101c1d00225100c0d901088441d500d00c0403400c15032201d0700c2501c040001290380d0282d82c2c0d001c21810703003120b8015950350031401d164000a801c180c00051810001d41c3c2c940781d10f000005002c00d04c2105a42518a003501503940d50300d6072405582404c0802d50551070800006031000c0e44848040c2044c0020004051000107035440401583c4a82000da403c02c0910f180d100000e2116001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 696236771 1250 696235521 696235531
    0xd020f031e01020408100204060507141f0204060f0810090902030a12020d0f2a0f0215030601260c0901090f080c0a050108070e060f130e040203070e010f050d1406 71
    0x50b504d52074200018213007960a40c02c44501801000104181944a002c1e1218990843d5812a074908101942494502c21150245035a03000a281c8601b4014a6001d0b01c02c0b201c0303545403400d180c0c0489a00700c50403001211a0707040d550543c80709200c07200155201c421403520140848407003a100e5215080605c99400c00600103a00c170400c04661f40d51b1002980504143c2c0d820310301000c4002c0c0002d00103d04035080410b903481c410b0b4241d181805003150101c0303000c0f81c02620000d20521006003200c102c1e80300300c40e0b0300d011070303440040344c403882c200048200c074182e25010003000c041e2030f2491218001d030320041a1504008900340c0200c1e410250014850040c1a0680201011082d05042c40704001d403983c4500c1c180714410013007000040d0001010081c00408841d559521132090004081d68000c86c0036010303006202220100c1c00603101601d060245000320708942d84240d64111546080400340030700c0491090f001410403003800d03d80d075441e104074484c0000724402c01c0a01045464054103c2c0e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 696238021 1250 696236771 696236773
    0x1709030f030d0606170415051b0d0b01031a0618040e0706030605100f0f03110c0706090302040509010903020d0c02030307061b0315061b06200310050607020d020f031e 73
    0x140130000b1580011000c030882d89640840c01291a0a49a4811140b144014410a030b603c480000c1c402107011925000303000c41c1000c4880d01c0e442c1e40054000180107041045010a140c1f0b0340801550030542d20080507004001c20492908506814601c400a529800aa0000d89585840600e080140319000107400f039650700007522071402040106404e1104582c406002d001d80b9100d04503907100e81000c0c4907007407905010840180c640e030b80a8152180c045030310321310302819401041c91903001505c402241c0c0221401c0c01a0785502c0d101c00c0c01c9404211000f800f6030711620007590f0303040c095801c02e0a0680010252810038405440b0719060b5101060b20282c0e0741c47c01d100180b00f40d90140700305110a440d140c0102141401d01030090000348200882409826081c4584010400150400e140c589000c182d841402005004540d000703400070740d900e801905ca18940440e0a0410f041030700c60303c075001802c48510300800e40070301800d04c0008410350740500070011840c9a40c1c80112082400b414880 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 696239271 1250 696238021 696238031
    0x603020f040f0e0f06013603050708030d05221b030206030705030601030c090807050f040f0f060503100c0207090207050a0f03050307030b09042a080703050304090e01091709030f030d 80
    0xd00301c1341c140d00001304001d0500211400700e0603440320103841c03c0200034440780542444031031034100400070b044030f41c8014041e20074120081019100400585080c4d0300c014030600640d118400000500e24140290001c800101fa1142003c07501195101001e001030400300406039440342c010a065600884148020a40020038420366582c10311400001c03510a18200083d40e0810900d00d454003078a106280c0b00e9510801000d00a6030313203500c1700a078114a80ea0401501818000b207101800152240500c0781c02444808a00a01c1c41d004600040610798003030640c003414501011300030f41041a00b59a03611820032281c0c000380c45c2001c00300301a400b03901c0c0e894580c9854040207041e140e064100d00e0049003d02c0034040050000030003441c00c03982c0c06441e0030310202020740c200030900081d4030100d0a031084060000600c4400f00003001541c543305000d100420b0902929801d1750701490004020095803940b20029100c0300f809800d200c00024140c9201c540d80000080c5180c102ca503001e000300707a9807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 696240521 1250 696239271 696239281
    0xc0313050108130b0f0601140304050d0810030305040605180618120a05070e0c07051527030313020a050a030c0503010507090e073002070b0612070603020f040f0e 71
    0x2c10b84480d4802d403442c0600704044103568030350314034000107801c05803d9242d0b0008a46160700907209403a241b0782002030651070385054205140c0d5028440d60130408507a17103c002c02c0110081c00c01d0801503030f415454040ca414540318084609c0c1e801101c24850b0920000d2035100c441e500d5400502c1c44900c140060340089060008100c8600303160180340505a002001040024074042441c90888000d011511419070302c01c030300707525140b1400d0300041c518001d00a1410700b220840712068042e84a070b10400b640081d01d49011100304c104078100c2d645507841840001e600c406070309108003d440c4050956582c9590f5240458000c41c016001211050240201406541000d1045542c49116460030003445883e101d22000d4044010f40b071541002142d0f42404240c0c000117a942c000c8a1205a4040c01e00c4890281d80000b5084054225813290001c0080340ca54541003403e1020710030103d0290205901c1c2a40a80080d8880c000d4031846600c10f00000521440001c50340340101100d1410340c5140c548 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 696241771 1250 696240521 696240527
    0x41506090b1f0e0d020a150206010e13020919110a050c0f0102070b04030c05031201090902041d03030c18100e2b060b0102100c0f021e0d05030c0c03130501 68
    0xc905408101d1441540202c403540315103411900c1c1c0090710b10b240580b44500204134151001d41003025024455468008943d5000994a0482d031a0101012903900c0390002240d1810041034083e60040d0b071140071070308218829801c40180c882010b800640c9005014072090746070003145031440892004642c981e00001c0902001e415140c1043c000c41ca040840d95030002c405c00d014202400308045c50021108102c01002264820f098141d604502d42d81c2d641110005040c40700b50407030160f0704040702078001d0403541040f140358010120196003169240fa2203070f00b668001c040300c81e03148104503040100d6511000c1c0c1604140c1c3d0300c1d03070310050031a035030714103210b40114102c0f00035250307001c1d40d0541310302c0c40540300d8042d4045a00607030201e814010900102d190604804510fa0194940300710a000a50050340e07401d03100000e50261220101c010303864981c6958000c02c4072546400000c0d140c0f1030302d0711620003560f0158492900904201c1840045451500040134100601040720024041b80d070b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 696243021 1250 696241771 696241789
    0x21e0d0e030619021309021305040b0603090a020405072c042003011509031211120f0304080327060106031a030c090c040519031401090302060708041506090b 69
    0x15055005009034246081c0c8560143c600503008003409501280240ba60180508a0401440242410364507003262817070100201c55503100da24403c5160a25a0189003000c106803440784105401405400040703070240400b80c60028050300411044000441003810790030580d40c1060b400e4040c40e04401e880c1c1c0c1c2404200c9890309480b8110b03a1294242c4800d06000c0c104a9054801c20a503000c034104c01c0300c0c0c0c241da080301345401c0104001c0307580b40d400c20711640c040901e00350315000c0811a21b4032604e4011406081c442c0440120920f0410400140803c0b051001190484c24085c1d000d0f941d0160400350503c1c410544221141540011004014050b414095103900040c00c010107142c0c0700c00c0c500000c1d41e816074030034601d003e01000302c0004c0d805115a01543d006020182040500c41140d0000508208450000305c45003960716080b56002e0405101c3c20240c0340d496002841180c43cac1980540301d03401c00a008135102c00c1c0350568504006558042e1100030310800c0070201d01c500140003084a886 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 696244271 1250 696243021 696243047
    0x706090b151f02120c03031005010e0315060d05120705151501030f06051201021b030a051b19030306031a060307090e01150608011a0c1c021e0d 63
    0x103105040c0d01400342e501c03800c0058440c07002c00307400000c2000d110760070790420701018000c440d01d0001003001214404084010761040c2140c4000e105010346541c01501ea603441590711540580c460710310100548404a201c5400c80303401482c2480d280310319550b41340b608101c16002c11031001c0c00300c7d480080020070000e0f0340d110303950400c40c1c003210316004c5c0520320200f28100f4071904068030f4800b040c28407006980308501414000e070030341400744401e0403d1360107503125544906081e00d400c1c080c03010458002c0259000054181c2d2070516090705144400b40040b580d403000005402004001240c225224440152551007600c000c01c409245007800e20079828252000071404403210101710907a0340104d904020b80b803c0440002d5480003c08080c3c0c01000500802c4141001d4031102250a0713070080c4405040f5041003ca1049503610048031a0850286d0900c200c5683e00c03850602c5552860241c40145007040c501c1180c00d0110040301001d00d4002c0180d4041480d0442e01445880b2984400d04000031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 696245521 1250 696244271 696244291
    0x20a120201080c1b2b020c0603040201051b0105010f090605030d08221e1119050928090c060513030605130503070309080c1519050f0706090b 62
    0x215005800181000000401c8000301e03180020740c201000810004a1120180b413404490301c3d00500003214407610a0b5030744407003520010002c06803103503200003111224480082c00050441d2156801902c1c035030001518a412201c9940303c002c08003509110781d030300802040e501640620f150001000445840c1c2d00160b00079004840c500c03003000d4005901c3c0703030001c0e03d0f03103a2952034406d910840d965421100310020300391115146c901c924013005d000703002c003501d005005014a000300a03042092139200b4211107142c070812000c04010703501d881d89030a40e10222604e26241d407881692904010842580300c2c40059a548110240c01d0104203809440a001e280c1426843c16000e001001c0440b40140f100500c40c0792036a001490010384140c126060507888030460342c0324074003813601070401c41084c00784d00345a20919400b20741c1454404203c4611070540508180740c00c40b1440301e0721000c11800042d07c01e0202c1082310f0710b10800034000500c40c50303005800005030307500d55191400c2110401b0740700480c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 696246771 1250 696245521 696245549
    0x20a030b15030f1012050f060f010302010804031211071514010b0d050a0603020d0b16020d17070306050a120308060f0306131b0306050601120614040905120313020a 72
    0x200514034400c030b070380007100760032115a1555102e48402c10902c990300300e00c4228010098100820000248421480702e84800f0340704e03155545068046540300034400a03000440141c0480d0100b801f0b80c4407038032040c1c002240413078140640484119194044031044506070395040440036100400d205400400c00911954010381d407500d500301c1003502400400010301ea40c2c600c04100001c038654040f100440d4081c04040b91124141030480b10340d40c040391203c6213101d01e1105495100c0c40401c403491140c1e02a15032564240884030f81600100c030080c4414107051b40d68001086680c0d502da9004018400c8800c0f12180303c0440c9001403513200d000d40700c0d40c0504400c9107015050356011801d00e50010744159480040304490178082160200c03803070702074003000840001005010180d00814441c0e071080e25200c040d5015091180d080780c0070781c42031881907850308500140c503207007a402100d0740c140100211002c800001d502d410a990050380c44501c400c000b04226000c609003851144028400300300c0c0484 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 696248021 1250 696246771 696246799
    0x15170f09030301050f030f100203010f14130903020114010e010801060506031b0a020a0606030506060909030a0c02040c05040b12150d030903112b0302060603070f0e040222020a030b 79
    0x141d40c2c04103010b01032080d100f4561181151318200080340390082c0e00c8040368001d25680d02803500940c028014810904031903000890840030080c0d442e40004006407a2100c41c1400305c01d00720080840c0c440841c115501c8000000306059840c400078080e195540c601e06181d45004075050031640507600a83c007a510034410001d0184280c04650715402c098651030b03030740380d440400482c240610400000c0400d86400e00c08824040001410341c810802038a9a00b04c40e16a1440590389010b0144001b00280000050a005042c26003220799451085d050141c109500c804070f1615680141e6007811880c0340341c00812404a40f02510000050300c02c3d54415028421503d00402c00ea00d1408060704440e4040811382064403101e211040c4440714402c48013603004a81c61840f00c8403000390701540103208100204203a0300d0041080802c0311214840440601d203000b4102c0d1030380310010000c1c1c0e84032030070800a941c400c0030501120a90075580200507950084a8030107022544003811f054015800425028 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 696249271 1250 696248021 696248023
    0x306060314060d03090b1605010b0409240209030a050610060f050a050a0504030212060708060111100506040b190e01060206150405180f0309120d090b030c0415170f09 73
    0x58008905858070303500c4021a09041d10f41c5c40580d4890305507540000f441e4030040903907200701d4510070f105000034040008684100004d6591007200030f400e5190511481c0c80704101c0340071400740340740110405800d10010000090502c014900d003a0750300e400101c01c01480b0f250005085003d0b040a04000c0c1d02d800c42ca4034010554000c094506040c8240050030034807003030268059800455004240108000d031000002d9141c0d4400d03220341c4040764000340460765660146840076010b001c00002481c0c0c1810061f0a04090940a0300d0346410503501d00f60840552580d8482191070305090b0045205c0d28505041c9a0500d60141c2c411411034108105014400000c68510724131007108403804182510340c0000e031440c0740d009840c486124400d80351405074009000c0003910480c54219001e0100b207508000031a114014007020342c00007000341d00c00340b150303d4035a030180d500400d030444824142622000c80d2404a440100082c01181940f41e1141c4200007001e02d856005071800c4912042d420140003071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 696250521 1250 696249271 696249311
    0x2040b0d05030f210c040311040903120f112a1c0c050c09070810050a182406020705040f020a0914013b0910030b0604060b030f0703060603 61
    0x103044403c00080380c00b02d41c10060b5540c0c440e046103d200c04460f0911a03542c0d5807960091200b221281c200c0b04003100301345402c3c45001d07400c0e5050388400d038090180380300e002d000b07255074542c8a0030f1542d120900c2ea003c044a2024092020f203880c04007000d075079070303c02c030344c4003080781701c280030b032180d00035100b150041d0120301402c20521341505219260380c510340390003420400080d60b45500401000c0c10099425489403419016081c031005804080781c64000f480b998191a0050050788044000d00403a64034075903005440544c060022040148461103802c0041241c43e40004010307405400140490710b4684280703020322202400c110316140b011030015008011910802c500d00e06040541e94071640640358420304580c007040b66901100c0c0155120041a2400a445251a440803020a810b0030a156528042d64918000020852555582c0358821000800d21500a40c0710340340060142d035036502a43c010700d520a540959840e144000078100c502580c0f20104050078403002c40100500b044503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 696251771 1250 696250521 696250537
    0x1002011113051212070602030408220302090606070302030715062727020108070210090c1e1a070f06110a030b060a09090f0219080108010c050a0807050901020a15060302040b0d0503 79
    0x80581c60b0754442c14502e81c4e0780510300bc58407852940c49505001135861a00c9903013528402c4440f00015214642840400c0c01950401000741c1c0c400c01c1110003080030000e02c00030007007014501103005601c2c0c3c02c10001c1e5461001c01c2c1a01280381e0140d00c441c14005004100802d04880d190f01c8201040c40160849258031602c0030b4103010101c8086041f240c42401400798103007101c00c041c003080000d850840f031840d100d8406c0300317401028950020240031600030554121003403100c1c0040c1c0d0052152800a4503071040b40700300e9440d4a00080c400009519000d031141104042298075102c05c4022406402d582154000c54480c8004106a40301180c00022a0098858440c0b00081e02c50140388018000e01c98050010361580310800800341f584d07031000c5400d040e551842c5c000c0c40f00c0c00d400b0703905540034080c4c801f09402150011002500b00c510a8000e004e0b5004144100c0e00440d402d6169109615807006041c2e41d07140c0c0b0b0ba44180150f0034140a0008a080150f928680040c041d4850585138026494 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 696253021 1250 696251771 696251783
    0x70b070b01081b040b0d0209090d020f0a11012006011419061b0602070503040305010c110109030c0f0204140a061505070c330e0f0d11100201111305121207 68
    0xc0a041e61500b2031006c0345e03141c1c0540140201e0420700b80b062303030b100190061349006102e8801140402500882e9505101d40d1001e10784004500c1c0400554030807403990016100c210368801c10040503501006164001c02c1d45540529114100714180541c4d5840321107885900c0c2c0750700404208003640481c0120070310740000a01c843c4d14171035141120107449a18000f418078480400c0200510406604c4010b0362880398a41c50980d0040d154101d003079070a05980a008074400d007172848081600d0342e401c0144607100900000782002034400d40038480700281c2d4a4030100b95a0003013408031200b201038019400e016414040d01f001940d60f547c4540980d58090320455801c1c100c1c40303158122051a60103c01800e0306450018511004001403140c41400689071040d60010030000c01c0d4246000d80162180d04203100d04454000354043c041035182c0d5044050841d907032482082000c40500000c1d0228823841012884030314030700010032800d007001503001c50054000f64400c180c070350120401c50f03400681c841 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 696254271 1250 696253021 696253031
    0x40312170a110d3201080604020d0609200a06030228020703050a03050325022a100c1203270206040315050a0509011a060318070b070b01081b04 63
    0x211030882c140103144180c94a2404c0500c1030b222880f400d509401091042c42000018140300658200280028442c0d00410f0b0000000704015080c221a1480001d0081e0400701e081b100d10760f10b000901c1c054050328007200e00e0300000300d50945031440c00c0e000100790519056042c210420000c180310801c100c1740100c80c1511000551300301d070003801114001d40d00300b005c2d42d100c0c11450070b000d081c1e540201e40100c01c451060034407104002c1c8040c071400d445201d96000300041c0400301104964400c03c0c1c0c40120118080c2e0503410001e541b002e4510070749502c16a1849150540303482e00c0e00d542030b03900d00400203040c2017020086104003101d0400c031108042c1500203403200da0714000f19032035104682019010500c241c02032913042640380c104900510500313108028641c1d40307285103400c0b2102c0005405250300c007008034034480d1174148017864000e00030380088018660456070241c07618034182e0052000c081c002ca5081c046c0b2411100081c01402000090420b01c00b13180c6030101e44428440e0040e109035594 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 696255521 1250 696254271 696254291
    0x120c01110a0f0813050105040f06080a1409010f0e0a03020d051605030415110a02010f0e03100216030f02190b0a0b030f030405032401140102030d0908040312170a 71
    0x1c0215100041d000740a02c05a403081d824a000c40d5403082d00843c0f0f980409200c005a554454400c840c2100c0d41d140e010040d42d030506004840140002d0039000f00d07103407980303000e101c00070310541d81754002d6604a000142132042c0880040988401000400f0f007500000802000701e500440c00700310252440c038029903252070164103030f483d210300701c031000e0306c54480410081a0100c0720780203103424182d00d455140d030090b403689021f0740e60148030310024001145001c51198150084a201c0e04090004041e941c1440541d00c410080360055510200c0d41a00c2d4641e11003416041200070003002494405056040030402c01419200440d100c005c0c400340e03202d0300003960420a64080310040400400356114042c4040e2070075903d8006011700b0b8464040da40d020384e0404c3c1d400c0000d070480466102c10840070f070318141000140e48840c2c42e10b02c0c1940410489600c010340b20b8803408610030300c2810b2580d102c81c00d50900c00d2460b40e8103402d81091266295031054414041005954800c0310503101140610039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 696256771 1250 696255521 696255523
    0x114070906180522050103030c1104020720180901020403061407020c0907030b10020d030c02030a0206060d050a080708030f0a050c0d0902121009050613030f0c020319060506030c120c0111 82
    0x101c1c4200b1092417a0500200402d40d01c004092041800383c50342d030341c400c049030040000300d00c20810010407603490308046901314200c582071000305401c014a09076086040f2080c218400d0000c9600a201c1c0e54000b9003031040040b42d1040c85040c03400c4000802007481c040030080e40d1070100c20000740c4204d4058000400d10303072080d040100d1a61001d408460b034808458000780d03450104900d400046130a052040c07491510001c20f8a5202e809940140b405889080c2405450116041305036240d00600035034601098100d80206200362040ba211540d80c903040702441d091200c050b00071200281411f041c414010b9040040d100010a5014001a6162184001560207134107400d1055940111820240c5028091344200400f500900c00e0703805c0d503510001c0c00c204d02e401541e002008241c4000c11452254071402c08050360910280490303211a0240c04c2c0d0499050582000302d94050322071081041c1d07410280b00c0e5040716001515540f4041c1604030440c0d0f224400c80c0941410020601d0000201c000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 696258021 1250 696256771 696256819
    0x1e0c0706060506040303051c200f13080703110402090a0306020c01060e070c0c050f030715110102070804180605150702220603020316030b0c0901050c01140709061805 73
    0x1004002c10b0b56a950386c07a000d4190b0300211501031540b03c8030701c81404d803c4442d000d0901808512070344402c040c554001c9030405a00961000064014140049101c040d8111681c0000c1c0101d08003d00c90075186143c082d00c514140880940500d005009a54590326411015805e4a500100160b2684007007401d0314010726240d449101c4811820040c44103440e04a15581c1c41076025030f082c485000e40305e1060060f908600034082d9019400b122040040d1600ba404021102901e458944800c0c8030320741380746003aa003040f20140c0d40f4103070005d010043c0c183c48108d40142141c0c2030b5003c1c0302d524940400100e01e1002c01c00910f242c040c0c0011058110340c0c0e122038825903041003401b840010481c0c1045540107080a000480c01380c4103080e14039480c0310010f102c60084030b86c0580074052a50721064140d034250407210000341800f000b40a02c1d400f0250a004405581d40c54150706100b0345040003000307009201c268012418403c1d42040705000da0483c2e507904003521020f45511a1500061004100f810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 696259271 1250 696258021 696258029
    0x904020c1e012d0b1e010e180402010f021e030d050f060a0920070f050f030f1c0b030607111002090d0210090e0c04030221060a05070e180109051e0c070606 68
    0x100342d80070305c0100b1420311801d0800c444820ba031400c0003500504240072000490010f040341284c13000002400541c461040481e40f600244140e07601c80755144041050007540000e40d640780c0c3c00c0401c0c50400c0d0300036480361690000c1410120041401c000c400302e88086401c0c0035011001d40c88440c038802c0400b90501c0300200040440c0e11607507818082c00c1226191205000c11651806403416660415000200740c5031400f101803029841d281d081000010845041102c400c1c10f103855140c4d60103c3c0c0d40500c04684a2525a21443c3d411700b9001443e42c1041150f101c24140ca61040c410b040860b10740d41c110513511941650895001d44482c601580e201c10a60300401f0506403210400c41480c180402402c212842546e0140780b08100c0184103414038011070314003800380d02200004681402c00d40085400680d41c0c100086801175000c0410f01002e40c0441a4020842c0301004016980e1288100780d4003000b40c80707500040390b90f40d000d01c0d00310f58005050025201d20216000c010300c10b803075000790020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 696260521 1250 696259271 696259279
    0x9040804170304050307061806080402040b060409090b0108010501060509150921010b180a051801021809010807030201082e140f0a15140904020c1e012d0b 68
    0x1d9601c000c425a01d500074040e05019000c6d005002844902400315182e1142c1d142c0c1c1d0102c006802d00f1412035840d840144140d03031094903031012501a4807a04000c0000d0308100a02003099040c40c00d01c502581d0301a442011261325001c0100607080e441400d4488003c0110780b00c0c0b144c00c1942e10030340d089000c1c040c0e4007070340500e1200c4042d4117442d450401007201282e0360001d000c0c10003260b003003110a0010903006901100c1c60000200004150390041341d20000c1151220064071520f03031850308a030887e10442c80300030b10703002006240f4504030f1007060044c000c01006010070381c00c560008243c0700001d4881001c00c407076400d200d1b0408034003031030408008100502c21002642e80702500040c5141c0281c00d180900ca41050300c00c0c031810080c1e4001c0030b94030500818090341d4403810080700c1482910200e40c1c40c2c0300c010721600440360b569000800100c8d03040c6005000320000c06d2a4200804000300f400030460707240013141156044a05039980e1003200c42c0300c0c04002941c00d51602d00140007004912584 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 696261771 1250 696260521 696260549
    0xa0c060e0601051e01080a09051c0801050f1e0906011106070201050403030e0d0903080309010612060506040e030c10110712030c09140d110105090d0f050606180609040804 75
    0x10280000c1c454125071045440701d40c024500d25a980e8144011303006580011301c0c440016140b00d402c1d803c8110514800e604542c1c100c0c0025495019542011001f20001512440100528a0800480382c0d0381300301107030340800d040130f03503441d100f0086501403819000e03d07001f80010b622680a154a50301020341001070f03a0b00c41c036040e00000e00a240490702200030a240019000500600181512418a80f0303100c03c00321604640b0380f10a681c000400002c010364a4210100380406480c0110851034801c0e900801c07281000c50411040e42d41c0c1164403203940d401404040101107001420100141185400090f0465007400810a0307220790380001c2c0170060074201000e5a1589603125190700c4200e070303a4543c00b40d5180c8002c460034840c00f55119900990008032031012070a036940b0301c145180b05041a5181c000b4a0340880c2946e4036500c0c050303c0142c1d24011a0090240520403140e024008880111268240744c030300d421900800340c6520b005044001c00242040351100c2110b002d40f1581c0c2aa401c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 696263021 1250 696261771 696261791
    0x10e030408010507090e060102030d0e190f051b0d0f02130903020a1109010503070b0c160f1404020906160f0c0f050f06031005011101020d060e15030c01080c0a0c06 72
    0x1c040c000c180e49010009645c0d03007001030092500120140030741c505078095840c4c5065002c100b00508190182c250290045546103002c1c00314031003858641c24410301245032002881d040c403c0c100191208002c04007014a800103810f03940748007001c155103074080c4248032450071034008600029100405110203070303d4a040b070010b1580014145c540144285003001203100300d4402d010b1a21400e119a507019404043d0030b021081c0c03150003074448113180070204e481a41e8054424040800554401e0070b05c0b82080a082c0a10b203980241c80d00304190665096207880f0440001c104c01e803091f02c000c0da16002c0810022801c11019102103c1a282c0190a4041c0161600d0090041c0b503403a104680c8982900040b03100541403c0c0182d07841580c041030101c060602e01001912407091740a40702c1c14556007000500c15032400f41c1704010190101202100325032900718010f140d09105056103610a600211540610782c0e400011f86511581c00007000b6141e181c0040103848103113058400800e0b442c02c1140c100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 696264271 1250 696263021 696263023
    0x4022103070605040210030c0f1d0a0f0f1202060a051614010b0109170a020922080d061e05010518030303010308190c030e1c0b0f19111b010e030408 65
    0x64004d5000b20f815003044007034184c09404442070107042c2d0700411650b04207144414020f40e90600d0a070b001c80801c40a00e1081c07000103c070420543c00001400036010300500168495001d480c014240e00c03000d00d840341016800068681c001c0890032002c01200013034170702080507043d2010116641c450307880f141500715242002d003e0460204204d0018400201c00181c8001001c84960340b00c47c0c02c0c01612650055400f48a81860010180010bc94075114a00891480141070131f60440c055180c0e0358441500001440a5689075031103050b040d4807500e8668000f007031901c01002140d0003424a01c2c0da40301c803000e00f80b410840300141c1503410b01000c0000800d022440c0000c10702c4034410704a2040c220030450703090750550300711070001d0b0000340c1048802c01581002150000e902c1d810f002c0c815900c0f50710b82c0d1802000e80d003c56100041e140c0e41814060145050044c2040d06508143c05002d43c2c0400c0410042d103000b505011000c030980c15132240070040c401c0d0320070201360303020710203a030b940380d86130544a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 696265521 1250 696264271 696264281
    0x1612080f12090d0318260909090c03060c0406050307031d010e030408070906030c0b0a050702040e0a05120f122703040e0c040e040206090a0e07181d040221030706 71
    0x20008030342840685e071101e965a040080700b0079440741d09640b00b090010114901c110000810040c542c0041062040030381d54000c5c080d115014410003015030807000814141802c130b01505105910034280814060a50880c00b80d80d44041b0501e40090448a05c1c04010080003400c410302c00103510300341c51100c00040100c014801d482194007100c6410386e44465600803507056210242000c69080303c20301800070064000c00358000d183c40d110b4100806900081d0442740e60b203000f071080398008085032040000078480e1b00c0860005030001410540e2010785440584586a0300c1d0240210401c0040c0d60040e0010040002075007044001c0880258104410360302d0307000340100190000c04030b00103040305600c40d0071541940c59402d035440071038640f9802c0c00166003100240c1076010f00304503404a22524082080c6109401076641c11004019650000e0700f0344c5503640004111050050881408041c042d800680041c1e050341c6024003000684a940c24900e403031011800ba500001075410244210342d040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 696266771 1250 696265521 696265543
    0x120c020a0c1e150c02010c05070b12160c150903021011120109180b070e0d05010615080108070b130e0a050a14040201140f070507030f051612080f1209 66
    0x101e1002c1a2074100440000b001e00014000045080001e140154890200744e5556031142c0100c1d843d281c0c8654030a20160040f0b00200c3c1c440000800f04074006040d8003115810420700e041c991042d00064075102c070310045001407015035070340750840081010720822240030400c0008804002c50406048481010b034807106e4620703014000c01c80042400400b600c68401040400c036846007171416a5078424400c5040100300c0d006004402040e07524540741d200c02803000e43d100d0303000024582c0c00c0c1103158500d22003038484202003180450040c05944030018418040e80c00b04071130581c5400c0c21000741400c0c40b034039420041078048900c0610001c4111034000b1401500a5581480b00601444403000c0c401c20854011b40061803092011040400d00401010040c0100078128503043c0d154803036074074180035548100e5244441101e003000340300c800e01561002e02040443e0840c082d25085480c1a40c0301c25840240800d0030005514071038004500444004000e0400c0b245900d02d0210308083c3c9440d0003203c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 696268021 1250 696266771 696266819
    0x44d1201053304030203010c020109020405010609030512090d0804080c09070305091b010306050307260309060d0507051315021554010e0303010501120c020a0c 70
    0x10070700c1e103010b001e645146002d00c1500e40078505040b180e245185000030091018010401000c005070700d0a020340c00d56014103070000314000c100340c41480110b4905920007410010031403030a100260000c00d4400200140e1885561030f02d0352400043c1201c85041c100421103c0700180001d03c0c0c0e4008110701e8502c400880f50390045541e1004190b0a0700e40c110b6004c5070681090b00f04070342c0c0080c01c1042443e204018500049c3d00c6031070b03001080c40c0034007035040310005690f2115448501510b508644021100c180301950401f105500070800e240035007110340b00b9190302c81d000a091584100281d03402820f080c005082d0b055a204c0744a0544154282c0302c00040c0280200c44102d003649400d10750142040303a0b030001c142841810b900d195450b485608030744002c07031001090120510015080c8100c010b070802a500e10404225460864a4075190000150003e00c01000260303000540300b1400789001e100880c804c1c400440480c1019441d2030020322011800001141c0c05a6040908100c0142a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 696269271 1250 696268021 696268057
    0x1c230106140712021204080106090605060406020c0603041b1d090c10110703120201061d04031d0d0f08091305090a0f05121602040b044d 60
    0x20100315040e44000d648442401002c21441002840032111503001000c10720660f1110400040800200e9100e40d0294886030b448000c140f0103106c1903c00c1c100104012200d82d03181c24901003010b515903101d03800d850311404010001500f0701c48441c20700c1b1421507402e00c0c0144003540720041c0d144440f030a580d40d60240005640001c0b07080100180c1d2001c41d000080802d03070f18203a941d004440300c90800c0c2038201140038210b00000002c4024020320107070192600003240103410031a0302c80c05a07110b0351691903812380000c18840802d4000c100b0b082c1860207038070852552189240860014504a14024418084410488140903860010340b103103071401c860300713403d040651040c1815901c0c00e0301c5000300c80c1c118002c901c00042c0c010040701c0c4814800c0303044d590039040c43c0c0e820103c150466008204001c1081c9080c00c01c40c90984a85501032400b113808200c11003185000f500480600c03000007500280991f00e10300b02c00001810341740404608801940310141404009225420003031044100e10050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 696270521 1250 696269271 696269279
    0xf03070e10090e0a1e0f080904021204050705090903030f061005040b0c012c07120c031a0f0c0301080a0320010c0e0f031c1d06040608040b0f100603021c2301 69
    0x841040c0c04494110392031b04480310340b945130300750107510402034a40d0096007080001480f40382d12304694031840c080e6014041441c540710520410040081084180740c00400c00c10039050345580240c0d8000c10151560901d501d0030400541f20f600c600d03080b0300801c1d900899043c210003015080000e014241c000d442d0840d00d03510f0701d0010702145102d0380001c0c5400c808404c2c04406504c007804100c042c080c40b42c03601c0c041e640780c50700b84e240504800d0700440782036920308011005c0041091550000740e51000a8915031624445540310446114014200700b252080f040c001600710002e541c6440c4003000820011141c0e0b0005003030481c031769691a004800c207008400c410300c3d02188176603040780c2ca656007446620302894110b851400c107042152a00c1c0151100c8140e6840c1c0e0000b80c00548120b440740502d038102428070203440c0800810030200641040b0420400740e10514401080b150542800358917904d100400a94280041c41410180e92603c4a02c032030321740a1490400c2c3c10503c9412241e500c0e40c032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 696271771 1250 696270521 696270563
    0x8010b030d110c01270602070311030714120a05030c01154401051806240118091154030109050106140f03070e10090e0a 53
    0x80366825050350f004040c3c07800321035001d00a40e102d44644042c180d254110035114060f00024141c002e03d0043c1d20005091041050907411000c0843c81140180010b40c604409800d0107520380340281e004000b41c11100344013190030080040c2d030980c4034041d00e840300001009503000709180004041000844500040c0881e40c1002c080031040506c03000c8130300c19040300f0700311030a440300c0c02905505064003c5000050503080c41901c0c011560743c3d43c2c1c1d030b0119022942151608501502e0200c00e80c4400510323682c80c4110400c0301001c49800e08100c80d00d4001c8001c8805c0803a05030340812201c0341091107200a85103110001c02000e600b001c2200d510105800004070400801c02c41000902d00b050840200a60103030101e16204020041444604400c900481d0035109811012221a1f46909040c012003540200304441e10304107890424544900b480001e036942824410300000d41c00f04400b0422880023084090040c02d9100e8040c4004244102c0301c990305c03d1004000e5581e161844200600d80c92 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 696273021 1250 696271771 696271787
    0xe0f06060f01050f04170708010912170618090c1206060102070e07090902340212010b1e0d020d0506070f0801080307060510120602030a1a2110050108010b030d 70
    0x45413004183c20181408000c81903450303011450300440c410f24400003644c0c0024022100c52034801c29003104524032400c4054260340054032040c0087c1800c400308000c2d40c885142014041d1250b455003a00c1d40c9039601d00c241801c80c00c0802c07540242e10308600039455000050f00d140226000e07400c80b0b0304240c2d5900d003409030721000d503103460001b80268000c00186072a90040c02c44989041100804c0b545c2c0d43d2080303000d50008440d00d9122240d80c1c00c4001c1580360038180c042a0900c040e000340001d05041c40005c5042080c08a20b24601c81400803800142e110420b06290140e07000d84440d0040c11207050203131351200105c80c898001004920b0901000d4400c40a5034102d5241000442c02c000e065a038034005031400502c0100d0025888400182036042280b008085038050301c0d00580d02c0c20300005403c2900d4540d110341c104406440ea100703003280c480aa0034140207041c24202c616015504c010395007080908101e62035910304001c0042155101948002d000d46002c0b0121401000d000070b090707032040307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 696274271 1250 696273021 696273037
    0x1c0c1a0702010212030c04090c0216080303090d0311040924050109030209270102031003031b020d17090301050c040e070c080301150302070f0f0308010906050916030e0f06060f0105 79
    0x84c101801c90624018003030701840c4c01c0401c1c060111b00b000e40702d080c0d00040340c20080b03002c0016800182c01081c1004200d0305407000d800790f200610f24600d004106187e0300d0b100c14117501c040542d100d256081000c0041300362405041400420b2021051203d182c4019020301a5a03043d020580d280018466002d0080c200c01c517540945841d549503100d0080e010302281200e03080e40001040c2449004206003032006520440c03405440218182c21400d00910000c171240140c240d94260641290140c0c0d510250b0403840c681c010060558034141ea1220380d4180102c1000a816608180600c208084000b002c0d0090700c030a404c00038541ea4400c0030881c0d18219916028000403410070050060b00b50041810381450154100545000304698405400c1522400292500400d00c00080e0415900186c1580140b182d48810300000f0705200010300d100101902c545185980c1c8400d8645650090304000c60b400c06032800d8611039042c140480741c4400044840307070321a000700807035090607601070740c00d031042c1c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 696275521 1250 696274271 696274273
    0x1e02040f03030503040503090405070908070b040b0403060c1202040e04020f0418060e0f070b030109050c070c120303060504020c01051008010e061317070614010f060206151c0c1a07020102 82
    0xd185551025101540003600c140c400303000400c5100003a890324003904d4000d200b1a95942050342c0f80500650404d5299080b01030200b608120400c840d00000060301c050b260082c1000a220701104030980d000498201084806400410002403a0756400c0380184242e0080c1e4441248441d100100022200c0b400c981003aa03401d0741070755002050382c42d4030018541200314121240030100f801010320b054515800401a6132001005009a0b002e50003496001040c2d00c4443d400d2803400d6a540e28103003024019010400c4e00c13100041d0130700d03102e1341050b00204005001156950038225200340a80021900c050803a000c84c88000b90a820520400315000410b0024084035200d42d038502a00158a80302a14000000141482581491801000168851b8800090000c0c3e100500c4141c41d00c16845403620f2440841c00f0000740ea004100103a00c400c0d5242d118105000c4030001800350000600030701407003c0c0c0606a0020000508081015035040d2004210220f40300051000c003440740003402801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 696276771 1250 696275521 696275549
    0x30203010e1302041d0109120c020102030403150f0c0c12180e09012004140d0c060f0c050d090305010b2403071110050f39070b0103061e0204 62
    0x2c040d9004111844440c8010401300306003203910000c80e00b0300c901c1c0b085102541d546400c80400c015500801d041d17444402e051042540c9140e800103501c1c2d019510016000201c501c80641006585500400103020044810004030034040c1c40204904440041100c0481a115001e08800e00403d0000780c40c803101034041042c642010a90009000050141c9a00d59240c0140001f0f4102022204240111610500d910b41e4609a94045401c9031010380c58041c0c14403002c42c801056072060044183d135840d0138989110304500d80100c8038800700c10000360035400741c088000c139159840b100802c1180e01401c003d00603d10140100614450a1203120300c0d00c01440840e924854100005154044400c0c01c2c40001802002c04036814071070600404012141d40d48100b00e00994400c050542000c0c00800d9a00110800030900360010101549428540030030b00c1c000101b6084101211126948603900c18801c2d6580d00d4040b01801c449441e21408001c041c00440702c0742c03214030a40d000c075030040c10180e03c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 696278021 1250 696276771 696276781
    0x240509061018060801020a0503040213140a0930110304231306030f0218070923040e030a02120c0c010c080d0207151a0915010c0c060f0f030203010e 65
    0x10311021040c01102c0303955100e490000d103118080c0701030516400180c43d917540e1303031806204008540d44480741120340d0354030300100c80000201c51419540c2c40000d4900019001005003000c00d80c000e00001c49482048003080c4000001094a0303110800705015150741c1485901d14030207a03104c8c001c50203030004110f40181c82c4079410009000c22110000d0140c400284419100c00707000594510790002c4c1d91035451289413a04500304081010703d181c400b10718684a40c100804001c1114059100c0d4403480d081c0782c00c1e0200d44600e5400803c010b01001442040401c0404a019440b07800001303485016004501c1c01e0419107071020100d40e8100c4035400502160040d0b4401921880194002038030300700c20600901140449500c0248019401b40c0004d201000302043c0002c03d8a42c46603245903428000f1060003100d48601c4025904010442c8080c104244180d004850350202030401400f44000790400054640c0c1001d1030140c02034130307560742900c1400c03c80340035800e910080c411a01c51004e1344000a03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 696279271 1250 696278021 696278039
    0x909030c1b05030613020f0108072c130e0d02030f07120309081209070609080d0305060301141807050607030e010c15020a020c0a0e04020d0f0309032405090610 70
    0x14420900181d01d044031a881e840840e00c0c1200403500b40c08000241c04044080d8644071921300f400900900c2c1030201e92034030f0000203040d040800d281d605484482010803403000c0310030504c0ca06642d806442e1041c145e81d0150220003603c6060181c0348030b8012a2001542c1c90320100c2200c5102034441286498003046594420100c404c040b0068201569800d0401c0010a0f10006001d42120b40408202508141c804641851142d51190060140c0a401045140030110300c04d0040c0c022070a000646603200c10100b4090244285a00c0000143c0b20402401e1000340e01103000d4842c04c141145c05441e160b0701404000c0c40382010160100700e0400108440358401d044d0750011301e114403045800043c41c2d4004005903081038200b0030158000c2e41e4145124207007114614001d1913070702c080b500541003c6c2c0228205429210026206d60301c103c201c0d20074940038000700002982e10402003038003609010421003c59805500c039601660805010405200001604501031a546483d0102ea1890140e1031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 696280521 1250 696279271 696279293
    0x207020919090b0103080705061005031009030201270c1403100e030723010c020313050409140f0303060103050f06011409031203010e0406150605030f060406081b04060909030c 77
    0x60614a5100c2e41a400000c184440c1c05000358032400a05e0b4503940503140c09418468024051051101c4094040085076030009101d82038480e1103400050315209400c2c100d01414081071401d101110406689121001c2101c0d41c540d00c500031036580c032000d13880e82204882c04001040043d4941e02c00303903207000042c0d415840701080030b40381011649024100da840d400c2420390071070080700d5110b64a0254000220070b01031410f81012504c091460700c440d8170004c02c44070f18140240303030260344d4400c0070b482000a03514807543c0c85c4603c6411259142c02c10b41c0c0081c0e482d0300403100f2358006410000880c0240c10307008520703401848161241034404000c120503c03483d810034505958940301d004918035028003140700850107484140041e6515182c1403d001c0190395403103203a0f4803c0149400104030031a84041684e80006940c05190f206072500c2001030094811a00035464502030701e000910071083d504040001410180c4040c083d00740da4200f0802200e24405028003c520b2640c07518000500400076 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 696281771 1250 696280521 696280561
    0x40b0307111504050c030c03070b1308030708030702070614030f07031d150702120a0e0a0509010e040303050c0414040905070e09030304141c0309030207030203060717010902070209 79
    0x18000e000c5000e01d040d8078107a651046040c11403569014003003440401c2c0420494101300340c1c010300a00303c0810109550708074500c142c441a800c040785c090038a44824a054004048280807a5143c3c80c282c14014030651098590782c0c00340c4218000054032600540e80c124200c4107149400e81182d0741c1c010f4030004494020004000c250380d0300d8113899081c541c101228600035108005114280407105005c19202000c0e18610a6601551150f1480c64501046808007085498211100740c03540000c40c030401540d410190b070050481c0008240c00d10ac0c3d1500d81d21880c003940e0301340401c1d107451044020600c661300502c1e8400d40710212400040c18243c204000c1203118408549005079101c541403850181651840e165400010501062088074020403041e141080c0192110912030030351150201c01c800b000c0380515480340429814035000b80030120055401a0035100280350080300180580d41c8200e00c00b0300b415950f400828010414030903603491980c060440255515421020351113804040c0c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 696283021 1250 696281771 696281777
    0x8071203060515040801060e0903090111101407120b03101a060a030902010f0f02070302100201020d0e07051e0d0b090a12210915020a022d120f040b0307 67
    0x440002d580d11024000035401c1008081141c0756810300250300d003540c0455121041d601100c03018021040d00c08000c442c130000090038000311aa18000c0d449040644020710303000042e10b000b19806002c3d1045000c07038490b5640f561080800c06529015004540744160b4143d01944120500d803130300c00c10b950011035034100750b1006d40410300c2d000c400074100307a12031102c0c500025121031040c811960014081d0032410000c2c00c0031112090140d000958901140c8000b078441c5500300180c5034518001e41c11100e8000e20303401c0601c0605130f0400c0d00365942010b0300c25035000300b68080030001c0840020190200d10070307006044220525480d15510400100078001c05d00c2d901071900e00c0310004420350391043c0340800c40d4507205a219030010800d812141c40b403107541c01240c185411000000c0403c02000c080364040c41300181ca0300e4200310200d107072141e07010f250b1141910405004c40e001c0c0801c21041c03240401107080b54207005031281c40441074001d808004034207080900c0140555134081028540c881800d203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 696284271 1250 696283021 696283031
    0x80d081501200307020103150305060c030a09020303030702070f09112215020a110f060304030309060b0a0f0801060614180613060e0a050108010510052101180b0301050408071203 78
    0x29458411004160b4082041039200060310303411035030540100c4404001b5203110662031031440c0c070749a0311404020100e5044000c000006141240306921025215070040c040707030b40728a0405070182d61000c450003070114120020703400041e18906401586540c00e43d200f03110382411990b407100d08911a550030302910b107151014000c180d0b000d652040c005c100001d94000c0044901d18145000c02e5141041d42c0360140340c101c2c034840c10f03075210a400c40b6082581460300040b040340c1824810010048412000e0b80014002000501101102403441c01d403070681c0000c00c00c00e41d48070815100c001ca06203103541000d02c14070941903502c02a0b00402045817000c2c0c01c141c58444010b54825480c0c0c0d0340c4c1c2140d408a648a040041c0758180400410041c2400b030038812030f154100f03400254034034941841441003101c000340c0201000c102c002442d40d48443e452001846503110401000e0900c11035803180b24582c600f00c403401d1103160500841e0f01031a04201c00074074041c055250003410804144103c1c00f0f0603122 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 696285521 1250 696284271 696284297
    0xc11030a23011a131a031606120c050a050d0b030d12150f03151116140705010e04020705010b04060b0702130513030c050c09041101090b070803061908010c0201020d0501080d081501 79
    0x203000303001f01d008405921601403800c0c0380e00a0444c0c101e250004a140f40380c54040b210598020048a4450710f941c01c1850b258400020140043c2c004803e0403501809250702501304160000101d90a045584d50b0501030745140d8002040b030380f0781621500c01c080c80c14003010004200e95641d5409815030829020440b030100308043e405039800b1041075510b03180c1c02c030350301c070b00f8007070400d5002c0400180e00015058180ca0000024040792122030014401e560000b9650200042584212000350004d4010f204155030b4040c1c486160300160026030080310b40132420140d43d03125114440c4039000820b504210988181c40803101d003450302408a50750710807951101d00d10b555028045200e248940c105034584603064000402041c034590005030251024480b0a00249140d01030725030010054400e9680030034190344c104034002460340a408154030740304010141350b03030640080c1410303030940106101e00d0f43d0342c4044079034681d010340003280002c400e80040f441c81124045a910b2140052502217556420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 696286771 1250 696285521 696285523
    0x30c0c030c03020a0b030f06041503152703050f070f062a051c020d06050a090222060210240608090c040504030c11030a23011a131a03 59
    0x11580003074a5001650741c080007145048440724010b02003800f999411400e0104003e80e0500014105c80d114035115540728007034040750500c1200030740d04800c3c03200124525071100001020441d844510524214240c118095030101000c99143c1d0f255588a10309103607058201d045401c400012a171042d074a5a803680820960b02400a451041464009080c85100c02005d808110001c60000380807007842084028000358600c00c1000c01c4130314002d691801d040560100401d52904a20792124010002203582c880f41c2c1c0c0549810010f207140a1162129850300c0c20401c0c3e0644030f00c1005a01140084c4041d4110350081d400303608843c144105045070040e400d840855087c0c00c050300003501070003003000c1c0b22000c01c8601031010060303d04008030309003610010401065910007910004041c0024145509c081080620568201c001000c0121181c412040c0c901e81040b40c1803501d41c2480546034862820414541c81c50000900340c80340742c00010400c0001d01442d65020003603108080c8881d0072914 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 696288021 1250 696286771 696286793
    0x120605060309150a0b030a02090406020d050f100f14040e160605070c0509070c14070f0306060305010b1518010302040e0406050402100807090605091309080310120507030f030c 77
    0x307540000c0c050a02889143e100703000d00040c00d183c012404d0204038a2a9140810101e401a8041d1004034803507581e0b08152019104100100e041d003403610341003180500c40e800d2500e0290401d0b9000c070304819078918207580b81d40d10703078020074070b041c0383c1c0900300c0d11145450f60103002c40c01c0b11001500d41e0300c44402d14104242419a100c3c80101c0e40004c5d0150070040d9001c1040040e0408880d000032034240720320001c00e40a44014010082108040812507201082010a004000c0b60a49403500d984910341400a0505d61008960540c02c007102c600c3e191814003103d00c0e1400e1b004840a0030400a1500001001444061141816400c00c00403902a20b400da030f4a100b1070044c20045168201841400050046c1a580104104c0340d10148885070343e00508500440d946441e00c10349032413800000644030017003500403e20443c5441010009c003c41e0201440c85440f81684400e15590365042049841901c400001d00b5a00100d400703200081e240d14000524034008c2c900019801500c0c0c1d107001a140e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 696289271 1250 696288021 696288031
    0xd170415051f0b071208040206160507150201020930060a020304050d020312060607031403041b08010c090b030a02040b130312030207020609150d060b0301090c0306030c061206050603 80
    0x1062142540002c501ca5454a80080601604080c540801901c3e40c070160b1038121160b0003000120004202555982015501ca81c03148488440c035072940c0340740203a980c07801d510580506006804046500070300620075281e070508003802e8021240a01da4611045080000003c5154041c041c0f03c200c00c80c40802185208140c00a80181d0b05c0c00d2500b002440c145c07000c0c480b40210f41c0100030800d511007000f0940c90704000241d4415465081c245401e84001010440307550b1011008000c100501c0b121001249545500601c203280c0f082c2c607030400a00341c0f001c84c800d2070040380300d42e6401c02214101e0780086600225081c001414507440c0c614052039640300505038440300d21802024003c0c003580d50300340940140c850804600e04005540490098041c40901c030b881049204c40c40c405503c040b2088410f00404000208080303615900d0300401034000303001d80b00030301e8984444004070a000740700c2d400079a904440c0e0300b0381c00c9240083c00c407403659412108070b041e50344540300080c840e16410050b500031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 696290521 1250 696289271 696289291
    0x40501061a07020f2409130504050a060b1903021909020a050d0c050307080112021f09031a040b040b090307060c090806060d0c2c01060c020a080d17041505 68
    0x3550180104040200600d00c041d00c68117007242d00d40310610b06200003c00d0354603025138180d00c92240354005070801c903c900c442c0801504000c104000c1000200740341480c1072140d0f0040040c0e04421050082d000006000313140304500700356041c405464507105000c140101a00c0e0801d005441d62200340a9810540380350010a901180445009420340074482100c3c02a03d01345085243c030280043c02d0074010700c034000032519102540e00541d1214610011446880045030f107440c1f83d9024014201003c510095555104c40002012100c1c448000300703000d6500400c2640d00d0742c80d5a15500ca07245000742100c0000d2004104101c00a921401080240b8072280c841c031518518140b606420480c0041c0014441c0c50381410880000303d40181d62401d0340d941440a000d060102c0068041140c114a80340e800d43c20750f02d00020f10590302c441c4900f4618400e4a84031041c1e5941d0460b541e0b22550366030351001042503c00280300d014800e0112503482801416680300c0c0300d0b031091f050002c40d5010340d452190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 696291771 1250 696290521 696290527
    0x30b1b0915030412080708061c02151b0a080304031b14010510080a050d120902040f0b010e06030709060f0903021201051b21060a260c010f17040501061a 67
    0x20b200d2034124400b070f041305504003400c040c9808a0010a902c00080240c2e2250032a10a4044203c2c2c9440851403080c0e400742048004042214032030185400600902e01201c400003400b450406020a400d2441980030301c08a0442d00c8e0fa0b5400d03a2685840c1890094525804030300c00041151001c1342410300002000000c0c0d103042c40e42d1f41c6124100241c116100c2a0301810700c0100040000a0307211160b051071504004c116018003903500903040c00c000c06503115040120290a01a10303501206c000d003000d880c0d090360101c22900b441840e010490b1820046a040c402c100b25113030240404411020381840e02c14070381d80d16540040c0c0541c03404405800c540e90b403001002500c0b031405c2401b5a0301d00e00000c0306800c041c44d900309108a44804a014400ba110302d2000c289280c442a104901808004014048205600900c60b03900c01d00922508154490611440465406142e84048282981e075500891204200b1030710501e21010f00304459940d40c0305070002e01d9000382120b40c2c442845480303241c0d507 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 696293021 1250 696291771 696291773
    0x140f070507120c060f08061e0a06022505130203040203011e0c200d0e150403050f0d1b120c0605100518071e03020705062e030b1b09150304 61
    0x3d103841441e000b4a0030300100113421490141c0109400350300c000c0844003619441c4010344051041030310400c4a54103d2030b11100410000d4010aa030884110031030b0b0248010508007000b080e80300d28611800781c005003c555164180c10306a00110340c054000350010031a0090038400702101c2d01610b41c01d50095035540a00c8084d160b00c180044802c4018044d4123200804002201c1c0c0c82d00c1c3c640c10b44001b88030441001a40d00d86440c0c07101c4d141c440703200c4a040c1e140c655a040658a0780600030702c8a42c1c0307000e40c04110021a00400c61881c2c0040b2000b844c000303018480c0d480008120720b050f000402c1c000d181c042080043c1c4103000d2513124050010201461615000074841600c00401c89550b04204c84010080d442d54007100f8864840082c4200c2010700d08890001da009105240014000e4011766040000132518001815500d00c0442500c0711105465030075002102101d0000074800e07100304000c0b070b0850410745012036421a65440b21803501612200240c0c0000c0d240e40400d00071100802000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 696294271 1250 696293021 696293033
    0x50a0b0a0c0201052412030a11160f0302040203040312110a02190b0f0606041a0a11151b04080f0f060c030f040206070f06140412050703140f07050712 66
    0x81d80c440e040e0300092185003402203652030b0311210700b03010070302024404251074000d03903900c10395a202d2030040047c1d07a660b41c071700300f0000c0022906041d4035000c0d00c1000f84000b00304448250840495140c00d106003d0309046d03a0804c0701a51003d442607040241200c1e40740b0080409204035480500300f05000c80c1e8544a070b0002074105040c15892005008014556001140f21b90960f02d07445a0685200748460b036654001801c1d60245400c040c001064116041000d0b8508500400e015402c54541c1c03804100c9180f55581e640c0640d42d2100100c0c1c1c0741c04046074611200b100c05080382e2610804203410241c40e10f80b035516106034800d2001c0c01e5407143d003a01500321f02c1840107903049401000300e0b038510300c1d00f0703c2400c4000201910007401a900014002c05001104040c4d1064aa10060501011030451740801051038207640a40b003519200441d140054000c800f2584800e9040d181d1440001e40c0490408040c0c00c9031805403000302c02040060000760f814410003018140c171440600c0171440c1c9007044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 696295521 1250 696294271 696294281
    0x15260907080601090204121203061a0324031e01020c101a090606161703071112031b03040c05030f100b0f0114090f091602010f02090d0201051303050a0b0a 68
    0x240040c02d10400003801f18070f01d901e514444a50304081d1440344d9644024046005040c143d000c031400a800b034041000010040340194021841c6420204030000c0300505030001c00d244c86003031031341940f1103180451510214005070381c804d60b0300e070f000504001010000710309181419690268040c3d88180e035952112012002d50f003203500903140034200c0e01c1e010b03000c508188036000b4032130b4001c0b080c41c40150400c4503428104000c140013061540c7c40b404c0840340070b0708450030300c0401d080c4c50003091209142500c07000c0c242d034450340a88802c04007800c035001c40c020142e40042c1095580070b000350008141501d0800c500a980301c21103000344078540030340c1c0e107a4081350400d0109030f12940859100c001c4583e40200720b00968244a8203080d5600f030041c001400b6000243e40d000d0304a01503004100c409054502d250140415540080c4401e8580c0300144c1c1c01c82c0310728241e2680c409480702149025512840180c02e40c1080040d40194035612500c840349409611034046440007440b2041088003c054019 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 696296771 1250 696295521 696295529
    0x6241b030403110625080a08070305040308060f0a15050909130b0f180f01021c0501030b070c172209090b0a0f0f02040902190915260907080601 63
    0xd9801e01c0d0440d81d407560400b1400c10902d1103040e02081740b00e59240b000d44400034480040c40900c010340201e140045403034021414003400710303140d14000303507845000340240b42c0b140c0d42c5980c4005066540c1800c1011400c1c1e0f481b074258120b451100046a1220010008030068040341c8031a601d4403000c50400c181100c00130001c042e46440c4540c144001103415010a4001100388a1075100c0c4e41e51040309007141c0e0f520b011010b614411044111030008040d401020400c1c0780d0b0500e03000c0e40000340b5a0030140d840030b00c0002c0070799400b540014105413058003400f0009201790300d040e180081d0107005045c0c42e041a0480b501e03088492210034284a0409501ea0040c54200e100348000c058a860315411070348010000c51449172141c1078070b140d81d0119800502c020740d480070119240ca413640b031303800020f411024441c2002412044110303c940c2c007500404003111000006001200f440181c1241c0072100c03810505990380c0d9280b21f45802040081f03040b445020301e030700205851490311140e94507000f03041e48 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 696298021 1250 696296771 696296773
    0x603021e1c0506010b1e21070c0818120a0c08060f0106020d1d04090b01030b010803090904030e010302090d0f120801060905152203050120030f06241b 66
    0x1c40c10005030021965604455a48080b00d45a00000c3c502030b19510900c0404802d891001401d154450f41e1000e020001003445c15100d45d142c0d803890800ea5641105034405090000180803030a0911061601a800c1050160a2401c03601c000f801079494030300610300031034004588110a0040d12400c008850340650342600c0462a03500d0100701a460f000700c01e60313134401c200e01c3e12001c40700c07072010501c4507200280c090000c04c10f0032454104401400b10030b0004903245954038000140012002098802414005040301116100c1e40d030700340c3d55007011030081da060540070301c1481d001d5981c0c8903500206a000f0a03004070803038518030b040d00800110007070b42c1051140d024018040e030b039031298000081c0d6405840f841400000f46008410900900003030058601c80c0c100d000c100e031903000c0113120849119800078000540034241007004031a500308000d0a030345003840001c94084070280c1c1260444400f50031f8440e060900b07008001c100309140101e141100c1f00054000f954000312039420b5602034620 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 696299271 1250 696298021 696298069
    0x50402030c0315040504350316020c030f1203070c1502030f061f05071b0915080114060d061d01020903100e030a1413080a03030507030b0a03080a030603021e 69
    0x1548000c107c48101e0b280c0107002c0d4104184031260440e1401c11480540b17007002540e1280ba00440018000511860490050007134800d400c80c1c9040001c4c0b0030070100e458401400360a240c49442d11410f40009101004108592030b40501244029054210706410150b025a40e483d05008809001c0700c0940001e00462620b0004215660b00218000c6081c0903854000c0d512070b217a0400e420003580c141c0e4600d01c2404078010000d84981142e01c60800302a002e102d0081039503030741000300c1c200c5e800d0940305021321549100040312485d00410f4009094850760000413002010b02c00d00b01c00302e1030390b00100680d0f03600094428080c641044080780340745c10b8506c00d00c01582c2c40a0704681301d002e1001001c040c04082c800408038221128142c840960040c91000d0b17a03295200300e00d6558041c06031055000c02d00d04804500f01d2446400b404c142002c002d401180300910315500c7c0442c1c0d600c940d454804160b920760b80840140d2356a651410360a90360550301011410500400200c04002400104140c1241b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 696300521 1250 696299271 696299273
    0x601060807050c0703060f090204022a0a03050a080a1107050a11040606050d0f182103060e041205041a090a060206071d2205040c0602071409060a050402030c0315040504 74
    0x1440313800350f9500c4040400c45000021070080546500c4038001d52060004c1511000e00c1d80300307011425030f0203034904c40301584070340c4070411a11620800c402030002030040003c2c00c6035a0103070048641000f0400d41c0041c00d10340c4800050400d0304101400c0310190010b003d01c1c82030142d801a20010680215001c102040c9801c0002d44244501d20001860359112200f0100c000025072202c5885444400760506d441c50502c2c003030856982400007240800c8041903004070f050721a01c076090a80c2c036005410040d6454503217a00e003165030b8244100303040000401001c00e00014441020f40c1c91030b540300e1155140c1c101c10080003803043c1d168000354219404481000b85550b80840400b0034002041c1d42c03504a030f0010b40104030444c040c4104c01c0ba80c140030251200800081d0761011b0b102d640212160243e0a44483c0101d0f2135106920407a140078a1660032030009207040342c604c940001d8010600e480ca15580d1000c2030903600215065205410007108000c4481d50510081012280c201e408120500d09 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 696301771 1250 696300521 696300523
    0x11070203062d0a020d0615230c07030f1a0f0712062102031b0307030305070606080706112b201605190e1b16060b01020c09010e181c020601060807050c 66
    0x11645070145603a1462310320b440c502000001c4407180e116800583e0f03202520303421b045455076040c10080360100d0800e881c000b10b59880c5402c20380611007040c03825040b510303044412030f544143e03450050032091b550b8000140c541c101d2050303440b0720754082c0815641d884031030042509059161015084150451303014070a2642c010400c90292541810100c2d00c034010360900d88010a441d0f008a4614801c105012541d5900442091040181c00003190414202149044d080c59410f00c28601c00048404802c5902400b98500e0b5500121001c813008201201c42206071030040140032080a0113030810043c40941442c54400151401e9140c84025a034581800029441401041c0040c8101d4041082824074a03100032074550241c030b01a0550b2101c072a08200000340410b080f5207016100e03040c60041207081034448641241c4d403c0d801503180f07641d051000307a95002c0c03901ca40d0080e070040e00180030042e4004002e40643c1805640200599810007801070070300007000d04880c0a12a0500c41c40c550040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 696303021 1250 696301771 696301787
    0xb150c060a0c11060a0207170705071a21010911040602060a020a03180b0a05061225031e110a0b1603021e01050a11070203062d0a020d0615 61
    0x80c007a00c0c0002c181d10004401c40d400d01e8042001119400b4103c144140300125401805075503014070706030a9030000d100c1803202a842850001090fa030080300301000044010a00003c120300d1086410349000c1f280c0454000c02d120242c4011101c007207040040c0415400d80c410540d50002c1810481d02c0c3c81d04061020350390742c0c0c008001e40c0956070002500000c40e40310360414221581306403100b9000c19942e1425202c5a60216802e0b401c2925101c0001c3c400d15140c4071030000d0818072009420b5082c003030403400c01c02c0c0b6034406c020040746080d2500000020703403601c9020300d41680b8140c860b40044980ca05070040310240348040d481044040801e00c02c4030450411030b5408016980350104043c054a8140d0408994900316041c0d02c600c610900141201904070390320130100b4140030000699817000b501c0c000e0040325406500340d03001d14001090050b40321040d20b60301d40003007a08402c401e01e07000744043c00740084070001540ba40200d03a503403a40c805401964041c14001140b954051035213030300240402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 696304271 1250 696303021 696303031
    0xa030603050f030c06041101021006060509040b010f05091512070206070305070c350a02030a1713020d0501060b030c0d0b0a150e06040504091b0e01030f0b180a060b150c06 75
    0x980810002c7c0c2643c0c0200030641144428071000e11201d41d655401070a130350441d0300300d64015420030104940c250722669190500303807010740fa10342c100001c0c081400846611090030664440003080b10503444039800b08210b1068100707600800d2680707807240e0000d0a44002400000030f0029411140000554828030443c1c101141d50055200d04550321031080e10520f82603440350449000100b40c2d8513540e0200041c8003188aa490b00c511080c110607600a90480444189601c1d00c42c00e4590740c0140341100420f440349001d500003280c82900d805110403103500940f203400a0070000251109840c0707050040541c030210840e01c00c44018070303003404401200d03480c039826010420304800ca07000036900c00c0c0c180c070050f0a0181042000103080c0c900f40c0485800300d00d1a050303140d003407040003a0a400c04900c1d18181c940c015204490491255214502041302034208083c1802c18003040303040120400c03280078564050040881e50404560912122038071809806c82040c504002d095450038001884503042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 696305521 1250 696304271 696304283
    0x30f04022b06022505030429160309030c09050a05160e040b01090e04150e07181a040f0524010801121703040501061a120403030b150a030603050f030c0604 68
    0xb861002d01004902c0b840844e002014448083c40d0402d11038000b018005540030031210a0403a0714010102c1e0380211040c070300304880e40080003c00840d494039845c0c4402e0714401e0904001c01a00c03550341c6025046940c1141001c20795410402100b650031303006880d044000b40020545989401100500c1c544109201300d0040b910707114900d129900c141c0480000b01904054135042e4105071a05003035600750b44450004280c2040404031801c40c020803020111030940445400c12984100507002030000000034244504841400480640342e074000d0440c0c4205a2600150910382208207003a20b071a0080610001101400d0743d0842e03903084500366040d01c1da0030a00146440c014a0031081e18a003140355046c480d200841404100601500310000783c0d142760b207001c601210842c00450903401030400000d04410303158040703030100b8069407080f9020303c4041c180309100c610840d03171114a075102030039103000244c0d607440400a104042c0322a000401b148006036151010704070b4040e0382d400000d003005e005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 696306771 1250 696305521 696305527
    0x7031b0905060714071205010510060e1305040c0b030a020a0f030626010e15090d140d0506040b120c04061e032009240102010504050316031103030f04022b0602 70
    0x2c404104035140091906006c1c01220b11403a203486e41c00f9140a8a0328101130300c40e90030101d0380501503000c200709540050140241c00350140d10640141c6400342c8295184a1020303408100c1132103103401988964080c0310007580d10035100100404100310381207005c080610b449001d001c0110510502c00b503590500010007146a00034112600405050720303c510b5901c40c40700611840d000b41c1c80d1491244014100703484021501c500103542612807541c000c0390b4804200054040024540d000d00d0b04820041d000184280e441404550004503103d440500c80e1f01c840011034030f51078207000301c2e4050082000081c0200012406a403005021400010000981e80503107000000c6004454103e450000f00a503072282071444001001c08106154030320010000d080c2c130300d019401409050f01460380000110b150407041d50800741030884060040301084146040d080381d4041c2000613500600b0200a06203860400d071042001302001d48103482c0a23040c02141002541e210160300c0906581c02c40000b690b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 696308021 1250 696306771 696306803
    0x30a02072d020315041a090c030f031c110928030809040b0d0515101703090a08120a03020a0521040203100902150912030307031b09050607 61
    0x960007001407080d2011800e68600081c0500c0c03a44889035845000390203584508000103a12107001c0011180545000f0040b035400c0c0c1d1680004400030f40c42030500050740e4401200382d00103420500355001921043d800411014081018045c041500c1c3c402c0b418100003082c1401b00024860045000c0c02d031192094006042c000612840078030600380261038245081d0b61240b42a4030a5080003104138050307454548030f220141414260084880e42000003046c1014040802c4210403c000b00000c039442041c1c0c10008500001064a481c6031580d00040c54135900240180020088030f90305c070454580c04010000700d0f4810361400c0f114180e24914015a1724402c0d681c05403040d103e9a004201d55404585d1214400d6074002003031402103100710280e51144481c41c447c84140c0703000800186d8066094003c40c0e03c00c04181008015640015209204142500c0c02c1caa007542c00840304800881d40300c0d003c4030030491813011080c43c0c1919500740001098242808282507000d004002420003400d4190a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 696309271 1250 696308021 696308033
    0xf0405040c120501020c060f0c0316120e0309041b053f0411150a1b0f03090e0108070f050405100509010902040e01080607020604150b040c080f0a050606030a0207 71
    0xa000b0b010402c0e01040580350324a0720718002d5100803611501c50141d0b801042d2100d800542150041080610a509549071138102c80102021074034400184440350070031256000940c09048118541360000c2c60b21443d51006000a40710700c841c043c40c6000309003007580c200c0ca0b082003ea0b80d0724442e080090b204009080d0030041e185005401011282c0010008054040c21401c0700a110303a200302e0340340c19003000710000c0c0b12150031103a1906075110001d014048696100798000381d0900c20081c503c032100c40311907c031100195a041c00a5002800c520010320082481c003807043e005100b61710051448038035220b0140800381e507900825214584500100f00c500e06c03481a0345014003001082d214465944088150007913110780301e58010b0b280407a00000c1c0551020034440c3c41740f501d035000303084255501d0342c0e0f8444142d8812600144156102c0340340c80d06480341d100d101c900c0407150700d0361005070611410f5400451001051004490b0601080000503255a001d990b08540301290241c0ca03039489241030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 696310521 1250 696309271 696309293
    0x1051f0b0306060a200a080d1a010905010f02100e030a0219050709090807060e01020a0909140f0c0d02040311011706030a1b0e0903042903010302010e0a0509090a051b0f040504 77
    0x411a00d11500b070041741489180b10003801c41c4c0588100270040e0701e10140c509500410740a0200340803480044d0100055401807038840310400c814410f0316100204a40d1410848400e007404081982c80130500096140e010040b100c4d030321760610501d41c201200359603202d076141486c1c0120f44549403074000c1c5038100320b0b54200365240b11340d00c00c0040c010b0f1107a40e04018000c0d00031280160001d59400b40c00a00c0200700d1241035207122410700c1e800c2895540c0ca418004922015001006146c4d080050b052042114400341c005103101e15505028194500001460728041100114500840b8018401c0315a000141c10003400d6111600c0b4142c401515a605000c41c8168031142e0100b00f030b44100004d2a101000401c26200c01c00d220032070780580b480e03520815004004118110702000c100501c00b560240d0084280c2002c02001380422548640114a40010584110b641c1d0b50007600c0807420007409210300003810444040b00300c4440740c80f40024081408101d80300c1c2c000c694400100e82400200b00c0d40c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 696311771 1250 696310521 696310577
    0xa021f0b121501210b0f0a1a0607120903080708041805130f151515140406030b15070303090b09030c031b0703060c02072d0506090f0301051f0b0306060a 67
    0x108017640c903046075203402503d81141e41090b40da181c8a1510454185584840840c03c0c000c1c0c102410300910756141758220300641e188005004541c5000000681c0103070040040d0303032041201c82d4031076180106800c03208000f00c40c0004060700303100801c8581b1303400701074100e525608203800c541d2004c51400c0c511420390034003440703018040c2401110043c00320b000d420181210321320703200031941040d051800c54841c02e042c1c542c6003104804010800059100381c00010f88840c000300b801c1180f000d0300d082c0494580c0408000c1300820340b0740980400b4084600480d42d4041e68a101561410300446c01c0c054070303841261003111080d00804902d804d490b00c2004014040e40d800b45081103c3c4070301a402a5440d81c60f0321400c840380044850380008101c108034108811031034144413103400c80c1801c003004555004400c000707402211403030100601d960240141d5000e00200c400d1058041c10003451486100d506402001c88100b0400902ca4203071100c00440742d0740c5c101d034a007041030610b00000c212403084000c29 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 696313021 1250 696311771 696311783
    0x2011b0c020f0a120b0c0903030441100c080a030f0e2b030c0f0c0614150a051206060f030f1507030507030c140a021f0b12150121 57
    0x80440c400b8540c0d182541a40d002d0b42c00b40001c1d688407591240c1c18800c0c4d1f001140c06402c18001000039500a6501c0c00c00c4108140310402c64002e581101c00100311402400c20380984215110b924034100401200240b128918151452100c41d0301c81420350701c0b6a1103c0c004050355404020303220003240c0c0c41140b0444c00e60040d0f85a100300b901c030000907446da0416020f400c5515500c60b80415000f4487c0400d4684291074040d0700c40207070101039a0880440b2000d0b03521945074401084a00303503850489110707810400c100441c00c41c1e0042406a0400903400c40713030080c866104000c042c801c000813030f2a4410412a101901c0b14488000319040084810805e00a40701e42d05616480d01610300320380d07104120076a0208015a0303120b4080702074644440b03000001c01c610b8000070080d004100c0041c400c002d094012114005a0486200c001402d000e50705850b89135504910b40c00381c90408002040030551500500b10a00c884810601109062207044000b9a001d0841950016502031000407660448 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 696314271 1250 696313021 696313039
    0x1b0801020c030309150108060609041113060f0b25030e031209090f010e040b100f060c05070806010608011806091e050702012009040905030c1c02011b0c020f 69
    0xc1c0d001c1e07540c0e40081c1d60440e2a4010f0204c040300c00f010b000e04040c101c500100041804d602c1d100c05201c94040d02500a1302c040d414044243c0700354075080c80020691a0f04100007885070b1410071205c62240311500510b40c0310504020381d01018904296020030300d0703000f49003502444441d103029a01034003040701300c84c0c06000303078144504032041c41005092581010381d407442e400c4d80c41c5814007008040900986580d20308100c040b40c0450205d1448030f030720541025401c1c4e009626448000280d25040c0d220300001885204158104071003071003c1401400418000c10080d41000700107003003074030b0500502d0800600d010400031002116000780d401000844403c003e0074084458403940345281c80032604d903003410300e00407c603a10310510441c00140f00c80c0981e14070b42e01a410343e544540c1d00c01c00b03109a000d92909000c40201e142400149102041800103100740c0b0200c01c40e024074642d412441c0c2c0e0540e490300c0784003d8103851125510080d40a1841e1a0301d9080340e0f4800146280c0d04480e00c00e41000c448 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 696315521 1250 696314271 696314287
    0x5061801151b0c03031d12031c0b0d08030c0d020a0804030e0306041709060903010c020102030f1003110409061514011103091e0d0605040b0609071b1b080102 69
    0x10180a4044181903900c410322071246072040b1031000342003400101034100c402410004644528550b0440020304a0f405481c001032400240c4200303a40c003407100d49078000042c5541c440c01800462411a000d89100b800009a03800008001460f0b01d80c01900c555400000520000084400c441001548050454944c0d1049000410a00342110114003160000f01a0082c034074000540c0e610031548019034002241c4103c10040780c0d41c120a94144d0045000c0c4001c10559500f80501d4103000450b03800141c50b0304c0d001002d1001a04c024001000d003040981d01480880c1000c1039540e02c0c603030103a0b00454000060300e0f140b0001c0a4503850401e0100710808082a103c99103140100e4a50090340d45d688901c501588035034407485800070050b0700c56048003000709407841c600450031045c00c004040109400d903984410341540e03001c850444000c4201020085a481c1001c0300c0d030342104841c0380000d081100ca10302c11569401c1000c014100045216544545005259494000c0c000380b40c000d41d190300d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 696316771 1250 696315521 696315539
    0x40203190f0b0c12010b0f1201080604030801050d030c020f0a05040903020c0a0b12041103010209032b170406050a0612061b020c100318230d0e01050d05061801 70
    0x1401a080700c0d44082c80d00032a00f0101c03510182c400b114480c8084100b90b074a402131485c850752204503200408074080c04442c0a400e040003829000780403920180c085860649401011900d05030841c510920b0200e4400c00402c3d800980071100e142c2c141d441021540540300040d00700e5000e40e01c15a070180c00c1681b003804041c1e010075041500341707054603a80e80c030588a8030401200e000f005c55114605007040e0005011a031516811070901d031002d400113207044d8000c00428103002400100c050392040c1c40024046080c0301c01c1d100c082150081c42c001c5240c01408c3c650300c83d1418050409020309403140d01062008040f80c0c4454001c064119603840001082c0c42c066002e0f0002c555445040000d443c0a40c111300d0021410182c40316000300b440041280900d800d500408a024403004070611510720000050b1641c0012034120001c5000011107800c0300010318508420321404100f0401c040e03030200c007180d0f0014103880840842000c042215610f0b0800301d840c030003440314900c504002d65000000e40c501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 696318021 1250 696316771 696316793
    0x4030b06012d0f0206220804080303010b13060f0f03090c261b0f0607150606030e0c010215062b030503072003031803070f0503190c02030d0804020319 66
    0x2e03080d00c41c0c001c10a00c030300040e030b12901c08558006030f405258154018503140ca0307000380b10b007a21034104507041c20340350016545503400036009800e42d004006030400e0032421a0000c140200080e103000801e407800f414006048540d21500b01050548540c510f02c200b0081d01e17501700249c06810050440310860a92090500401402c003c0c0a801a000d440440340c1c45d80c040410360303100180c2801d02803101042441100e0707208800640b404600200c00400309100c4d03000d004000d00d427176540032a003442140d02c41402c0801000707003181903500c40090040d43c6001c0700001680035008450321f44003200c110120450480d13001c0580c044103514903200c40308041e0000003460040c80155100d043e0076504003002c0016810010031010194014000540d00480300315080c0d44949100007500d00f4100359940b12000315909040441d8184c0010511a5069a119220744090020703490020041c4030300d9000303c1c3c1c5403071402040c10104880e0100140564908002c090060a0105003444803c91a802d0164040c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 696319271 1250 696318021 696318107
    0x403030609060b04050f06090a080d0905010809032a1006090e011116081818091c09090c02071701050601081501270b0f031005010201060b04030b0601 66
    0x15203007001c040f840c101d0080035a4107070380e40074000044d840311100070088240c000b02d00b1903500118403080451101001d200060000c040d54507680d101034102000074150180003000d1024a0b40f090069a4480290b045040f83c05e8080204031129085c0b070240725801d2202203c00c1c09000c80c181200014820b030554440c1140144400081142d600e42d000030001718801d1150381069154220600d01c045040300c402041c100d002d20307401c04125032801c4045040020504840003081480904008600205103d15254280003180303415a6010149014082c00b200e03000701c1100e2603031400d030b00140900030040200640420100c0c8024a8a00040e80c1d0290404844890024800c071004c10021500000b07500406a0141c54100b003809200411525482c0b01c010820014644440f0004100e500c0100034408400182051aa2b034074040c1600c00c180b80c21603002504585c500300f403c0244808500588090300c4e40030003004441d40700e82c40100d80403880c03190000b00500030055520360031404010384603520 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 696320521 1250 696319271 696319289
    0x608030423060304050a08030c071e060507020c0604290c10060b130306050a0b130c020c0d0506070f030e01021303021816030b06130611072405070f0b04030306 70
    0x1e1440315040c00b40500050703e00403c158000644000041c102c03c014640c050101840d10703041c40f8168441135103800042000c0c04240c00f09503405400d2001c2c038003410b07500101310b00007480810402c9011800340d114074410400b4024083d008001e0001001e10488841c641410100707403203010342c0083e562616940609400c4242c40d043c000a003210f1300c0c0050340c81321180401d56070045880c42d03ca8602800c0010290741c0a1541d0310603c0503956584d01e406c18072411102c0d0009a032109401001c1d16009468064500c24038520440000044000076500d17809500b030714203c441181c4181081e400b030210080d0000482d4000b080b401c074020811b202da1000c072030088640c01c04040b1940f0196942d0b040544030a502c07003600600010f1460b000750000c0030514400340003140b0340340b40000360861502040e0440c00c001183c1740c80075540301c0420032585001d440c0c060000080f81a01304e6250765103c8038140d03a1801c0c0040440c0400901c0300c0000f070003540d42d400564a04003482c003450024001e00e007502901c004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 696321771 1250 696320521 696320579
    0x204140702060a0b0604260706050c0c0f060906130803210106030e15060f0a0306021323010c030c1401050a0e010606021522030809010c050702010e10020106080304 72
    0x501c0f41c80b4000c120960801820309860141031a20511541140074004580c9003866000b800d03c51508000850040586544036500d0381c0c4841000d070b06004503a000305106054001c0700301301d20341d5404210f0b2a103840c00c0740d80c00d0b566060804d0274060002660301c4480e1501011071b00107001e882000c481c0049002c102c140c0b4600d80c1e250b8505070304549000844855543c41546040205e40c94844929041074004084501701400040082d0f9007030402e03002141c0392500491a078075005140c82d810301c06424000c4d1402c104000c000955030480e040819920b0410155006200c145030250041c081b08640044400c04012189001c40c1d000c0c10050b60003040b800e150140d10fa8038058103115400650710300d540070305003203c41c8000948038014007600c2d5002285a0306c11116102045100658440d071180e1070712807440c6003107070199007102c001000030000e22800302b100d4030060380d11881c2d8209404013207070000001d04028804034010015604100041d20002401240c1c400c080780620032003000300018045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 696323021 1250 696321771 696321781
    0x30506040b09040b19020409090f060c08040f11060f0a1d1903030509030f03070507030c090204030221010f020c1501090c02070b0a0507020a0311010305090d0f030f09020414070206 79
    0x2d400d4408603005488408220045030b0210030504402945041c200c0000d42455140e4039010304071082c8410445801e809a0b0116080080078001c80b00170382101d003440c01403840d260b190302c100c2c1d81c1e842e4002003d0b5000540131083c035907076040c252152001c5041c1c1d1180c1f94115440041d040c17407031410662650442804c000c21031f40c54038001b00d114500b80d203043c8a14080c40d541c0d0565503a0403201c0a240e041c041d55609549111080010b485014020b0004001c3d40380b45003061120302d413694000c0c0703070070a00401c0248050380790503144241040f502c6c04003441c120240072186005000910110101c01d0000400c00e686540c006041a6107100c2018805200d1341c1e51010102141e4103011584091b81124a0130041500050041c009003001414054501105030340064880030807a04101c401407805480e61841d940d0500c2001c5c0d00c4000c581c0203080400520074050040c5039007a12101c100740c1c8941a940c05840e0580115490304e5025000f40005041c0060001168508548500c0180b0505000039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 696324271 1250 696323021 696323029
    0xa2307061a040b150a0c0f080a20010b0303070f081c1506030b0f0f010216090c03051303120f0b04020c3315040e030d0f0c02030a050d022107030506040b 67
    0x38035480404d0a1805541e042d090351441000351060394203c05013010344000c0750104000340050b0140796101030b100c0c91181840ca51030000303941e030030640d43e2604a0320300080e14000212502c0b030f40c000f00307070140c1181c0360b1520a11030701c2070310401c45a51031203440310312004c2c43d103400422030203045207002000b05031220022011100011a0316a00c0030780c40f046550a4144a0a0903100020610641c0c80d40540c541850390f00d40080e80c401d00056949514041009a062183c580c00c1030244d00344248448460f20000d003e20f10064490507203aa50b00d400040d0f5002e2a80004449038001e08103548035010300014580b00c06d0400c018250a48058541c142078035581800e0041800d40701c1e40c000903544034103003000c0341d400e03a02d414141c01c60b81da0285004880800c102030030020416940c00b01d8400d48108101d020303602d01140050940d8401d01003940c0040d00507041e00c29090340350a0041c1c540311010801d118000e003900f511404840c48100f032040301541900054400c0109540c00d0060903000001c0c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 696325521 1250 696324271 696324289
    0x50901090c0504201602010306060c0302030703030b04061e0e0f040b0708090a020406080c10140d020c03090d03020d03240b031801061214030a2307061a040b 69
    0x400008452006100c185803550040f4950102244c011501416100d20542e20b036000c04210394014050407002d104640e030501404001c1e01080c544054488801c0d0703006540d9004401008046c503444400303d48042d21103900140017030808104800c001c2810b0340300261540300c0c03401081d500c010301c4800580c85010303d0103428026a8404116030303042d5207481003103d0902d0082d1141800e0302920b1008005656603000d807401070a0b002029000144171301042024000e0b0199401003130000b441c2d1211203050040b8180d40400344044805640c80c10890403250443c880c04101641c031141008a0100b403550000d0301601601e0103490421001da0306901100c202d844004444954007030f02e0500707014868103140a50307004440e0480355101d0351105d00c200c03402c2d544140c1041d0001c84601e00c0403001c1c841042d85c60103034844280302841c644800140b00600740310020100900050607040d01c08001c89803203085584540c0c00200c1040501d038110320558004051800141c451401e00c0a4400d4902d400703951 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 696326771 1250 696325521 696325523
    0xc030e06030a020d20040303050c0a0206040f05040e06070905010e03071e06081003050703030f0528020c060309150601110f0d031406220e121b07030b071409040f0c0305090109 77
    0x110324141455640c00721b44540c403121001025002f080200700068039190050700103403192094008000e82400144411204003028038221a8850818050181c0c1c00c100c0e0308042e40d20a02e403401080c602c45000c40d00e400415400384c96062003039842550103001e140c0710202078a04990781c840c10790301c84142202c0c0c00323a07040c0009030194004032010000a80140c180340481181801c050781005500303c81034914220008004910b1016100100c80f4907034188a940e8903050116070503800c5041400c1d42c1c680d20108004a031000c2d000c100081440e82e80212000411250301b0300440f00514001c1c1c60564440320028032031070101c0c0c20044900400607041e001644500000780009800311606200600d40c80c010f0306034054000e1365068401078128052016402c600e81c0108559540c0728515441c5811618025441500760043c850600c0001d0000350095044030342882c205440100d0810910242d00c0b4400c0349542c8585044894040c280d03150b000302c9805440c5403801c112a42d40d19040328207842541c20 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 696328021 1250 696326771 696326831
    0x2010e06120a05070905030d0210060b121b1306020a030806010801033507050114090307050304060c061506020f060702010b0604030318091415150306010c030e06030a020d 75
    0x30310b60386019404141d02c034410340b0b071038402c031a520000700303081000001c64140140c00424200d04000300030301454005000c26103080b8a8140c001010148500000d81700d48584100c5410790a00c1c02c8129003a5a80e100300c01d04141d12083d503440300a980c562200404402240c10a00000c88949c01400740f03d0403203402004a00002421540d0040082100a60302034000c10088418401c0440d000c054902a403044000081040e03404a201054120007001d2424580c01041194000f407004021744040310b0b014100070222419a00d41031024042d0030060311542460010001041c981c002072402c50280030b00260344050315031070f81c105d0a07912600507030382d00110100400c00000c0e103e5500c1c08080f04502d84148800750300c49000c402622240d0b540e100440f12100d0500c100403118100254100f8411039a40d064500454540c220701e000051441e0705003c10640c0200c2450302558030518005401806140d80307103803241c3c0202c020340003200641d030110324000624003906103030000d170713039034200303408 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 696329271 1250 696328021 696328057
    0x3250504060804020a1502032503171b03100e090d080c09061306030209031b0a09050a0b0a30150519050103060204150e180702010b090c0702010e06 65
    0x4415526000b024000300c0e000440701074001000b00701e503100c0d100001740d203601440d0340c1e44020740e030713211501d5003a4861074010290703110840029400a0080e020101051581802696280b1080c2d0342c100081d020381001b090000204a400e4840300303850f00540e44026403304150311592075081c0c3e50b80d04a805a80842c0244010070454440b66010f4141210014604c0f0b241c1080e003100003007181c003e42d00c0080480c5c0c010070303408150b18042c090b45c0b2900c0040b0345050525514000013847e480c220f0300c00c0c922003542d60b0780400c1300e40e620307074005103100390018103c2c180c0c1907560f0349100560315248440c00e41c00c803007011410f040013420001c84a404c540140000318103c03018961039005003400340c50f08010082008405010440074003840e8000c0d402040016142ca00e000001118124058411010018190307640c0c4041d64501018600b4040d0760804005103969441050740101403100d60154405042800c0121643c54031000b070aa0030300c01c3c4d85030881c03a006181486080c0c041e02c0b0303070800440011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 696330521 1250 696329271 696329279
    0xe160b0903060103021c0213090b06091b03040201141801080112080403080c190b060910061e090f090207060c0507030c033c0201050114010509010e0402041a03250504 73
    0x70006803016086506c020841200035800102a14010782202ca6000e4403901c40c2c5d018402d9030351b4180e601401c20398040140340740510031401541d103014052104914040301003001d5910602421500e03809a141180d903401c6c0300c16011400c0744600104600189480c0b0010403208000c20742c1a000310790103000c82d402c10341103540b010310503000408000151301c034524003d10328040c0100c01909880c051340040d80b060070043c00340300c1c1043d0024061103d0700c010a40800031660b001b012048904c0c02e03042c0d91a130b40480c201041f1203e0f007147d40410b00544d460301001c610798015500412195208a404010400c4078240a803128000d0603000342c0416000020719010a0041e20b0f0903001d40d44064030300f0100c22006034a031095209000c4007010b4088001e40c84003d85409125883c00340c03100302114005c444030301000034020300c80c20341c03660704110610300300b001c0580f2241c0503180900082d0590100c1520807940114017a0000c4442e2890825882880181d000030f0070b080c1c58090800d42d82d940e01e02828 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 696331771 1250 696330521 696330529
    0x4061d0f0a080d0f1e0e070e1f0b03091b030105041a040507030503031305010b0409170a0905131b03140c07111201020a0306060806031c02030d0e160b090306010302 72
    0x7211644100da152660111001c8951900c100585c080c400b600480c101c15250126004540403400b01e9001d5501c401c00604c2000a102c1f10103600c076651403151070103400c40304001d903400c4005501085101501005001100c2004125011448500c00c2c00f011207503840c10815098031001c1d0750103452607603c03140a080070703c0c11852603a40940200210384c0300030359a41d11103145034001c889200004050f09400c0707080220130702844d500703a4002c41d024084a01c103a25903019140c411001c4002c032080020303542e01c859000300c8602c8010078008203450130a0464448170005810781424a9507000c007840103802a85009100f20400c116024043e284283e50b04241607c841d4014031044da41101c45040c070901595800046104d113008640000d030303c802503100c0140503110b098100205014a031001c0050686000990000d49021009843c0994841440582c154401c80803214150350030b0806503450036000083c084580752a40003850407040e6a0180c08445000e1088901e43c5504000b00400140c90 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 696333021 1250 696331771 696331777
    0x26060105031803040308031015120e0703020405040b040b0c030c0f0904111315090522090807080705061015080403030216060f05060d0b1b04050904061d0f0a08 70
    0x3010b2001c401d0031145030001503d035411980c0b044031481d80000420002c0c0d0700320000c1c84004c0c9544210480b1760550000064692102c19a00d5180d80da034a401c01e003545081000315000545d0081d10412090406041800844004a80544007225550081103640d035010044a118140b10200242130034940003007007010f507111950303581c6d005489990410703409400c44005d1202c00d05800850b004103180004156084690880e414140103400e4010020b940390b40384414010f81c1e0042c0400c030000b03040c50b010002071032440c1c40500360316404500001049117100042c441c89020f1005c0b110180c1d100c000d102103120060240010000340c00c4800c0c020a4013403010319030014441e080150a158443c1111600c4070340d642d0b800d83e8040c9d00c403103002c1402841442220741051043c0c0c0c01c44d20566507a19400071944001e01010410080c450141281c120b0f0381c41a54041d000c01803140304581041d041c02c0001c3c10a120380d20a001c0043c10440d0003100d0f000550502c9825864054084442c0585454102d50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 696334271 1250 696333021 696333031
    0x140906190f0e0c120106080a0605060a0b04081f0b0a12050715350c030907090f0204090e060103051e100e030408061f230307152606010503 61
    0x3611144070440e124014001c8501c03002c1c0318802440144500002c00c43c00003000501d624031070b4984401480000701c00700b202d142c11030f04031401040070f4490101080803480c440d0f00590510401040c08a00e100c0041403045440943c03508028a200105103d0b80440d2019440d140c1d200b0030843d000c00040c03030a14a14800540600155040c0a030f9840b51b203c61a03911141d00c00002d00c410a5118105c0780e1440c150440d000c40940d0000d4800481c80c3d0000608006080703929480000700000701e40300c0781040600d001d4051440140704850304007850078042c0d0001d0042c0c0c3d09141c108500c0c403c101f03200041c03260489030807800611499001c401e030035a94480000080300b80e40200940a224484240201d800128140c0011070381d41d850310000d6410a0005011880d00d80d0f03041414038544c42031240f4810a0b201300030700c200c0c200b008442c5004001c1d1406807105826001d0b04da000200305102503041c102c0e41c80c40743c803010481444045e4000c06811005100c56410001c40f02040003940703d400a55401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 696335521 1250 696334271 696334321
    0x400b0d0209040302190507061103030906040f14010f020d0b030109030e06030a0e0a050f0c06070c060f03020d090b090d26060d0b0114040c0509220f140109140906 71
    0x204070180c86040d40440c00040650703046c1e02c000c0c1f04002c110341c401140490038070054003450950804c100c0d0562a00b2010344050f02d82c00b480d00d203100600008044142d41d03030440344020403d11556050302c002039000440c5440c0124540300b0305042504042c0121020507034155140401d03108607a0410443c1c2d000604149031aa58400301d4a807180f0301040146441800360001b011985148040d0a143c10040030505000359010700c860030000304000020720945505080c040c200c0ca100e203508400900404800500c85030400c40039005001f80440d90034014013407103099944003c040c4c0030a55490a0902205400001c0031031720460800030070440b690445801002074603142150745624640034001e0300711103440240e9090400d56481c003803049540d00d220500301a828403c5070f10000c0c18000000740c200e0000c4604c0707103a05141c03030003690024a050030000810442c80800c10f40307041001100740110054035103010b0381032400f4000d15450700d00c03c034082d20041c84550344000c0e105482e060010701c50411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 696336771 1250 696335521 696335533
    0xa27230a380411120c040b0d020619021c1d04021611030f060412080609010e010e1f060c020405060f030705010f031104030b041e05100902400b0d0209040302 69
    0x115501c5401940c4001d4042004103809402c0744100801c1f070b442a800288900703d070b80e001c50016141c2805455810200505080c2000401c40b816818002e03c55203007050a1402509000010b401c408044811140c03805074001c1407465001340002c80c821541c107650b60504484d445030004018050b001080c9001030155014054205962803030410159811298216260b08840342c2ca58410f0002d644450b048410380c0195140c860302c410010018000e5101484104c0005400b900200740c4041001c540c450a608145a4415004041180e4400101c3c8200d0420004c98418980700300b0941c00020024040c094042c508001507402403212960801456141c2c00104895000314000e40000c0d4001c40494060740b4052800600360700c610340f001e4845502d00c0300c0c4a404580009000041110b0b6104000b42802c4039000007050400405950b41404140c200e41103481d05283c0c1080041a04042055030740c15082d900311802c2e1040300d048550811030100790b2101500c2c007110071a030098040e0040c0c3e40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 696338021 1250 696336771 696336803
    0xf12020a030b181906030201200c03060a0c030e06060303181305100302130513060b030f070906080c0105120402010e0a120c0302090a27230a3804 64
    0x2c002c1c0501000a034040c48207408000c10100080d0459003410b50004d42040498215070020701015407000303c007050b103d6402625a0400410402d0a10012005040780c10a250061005014001c202c00c0400001e0800e016083d80b1040021414040c90005000c0c6041c44a903a110585aa5102c0788103513116180310003151903069903102d014090f0121a0b03246074224154018080d4884000307180c0620030780381070304000e05500c5d181c261000c1582e00c0700001c04d010010f007001030300d002d4521130300c15401d0003109400103044000d941310300100c03600c41c0107540c3c10402c0e200040d5094000d082c243c3d1124201e10000070010343c41140c14404141009000c586226203940010644072284c00c03088580500c11401842075103404c80c541a4800901902403060103d0300b0300c0c114040001104000405494030a01c600b04030807503805031502ca004502070004a035110054580c0c92514480c1651a03c4d448120141e400d40400c5410307002c000280c0c0f6280007041d40901c0c840c103981c1d0080c400d8030184c41c8524104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 696339271 1250 696338021 696338029
    0x111602030f01061d0421030207110d0809190816090e060609010e101203080a05220807060f0e070f0501080c04051e22050f06100c030c0618120f12020a030b 68
    0x6c05e0115055500603100c04041c0340000c0c030b02072007c080c3c0380303e402c0100419002507a45400c45d40c0c5140140c0340c180340310801021458626420760445035890042080b0341c441d11002c24040c204464104006020104110312442e444902c1910303469000309280d0b00520004a0070344c012034224103054240f0700019900c000b0078009604025040b0001441d81c010300c03180400a000d400e0304013a940c021405442c040701c0290140c4480300301c004002410100d51403050080d0f65000040c40c86001005004042403210307119152035041c01441d071203400c00800414194440c0d6046445544806600c80c609800e1504011070414111075060a841d0701d1401442d00340c036403540d0380c54102c140f080c0e2206c6100a086a00e02601c200904010201c1115402c01070f450755910080c0e81008030781d041c140901c00940c102181c040350580c01c00341105040604648648150414034402e00d07004080100d4005454481120856164210700c40040c1043c0080040701009a0040c18a50903034180054150b0100000c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 696340521 1250 696339271 696339323
    0x30303010905011509081e280203060a0b180c07060e010f0e12040603110c0f0a140a1a0a02040e190c170403080a111602030f01061d04 59
    0x2003099031204010441c1d138610384c0700903000320243c3c104203210504007210507590700080b0720008018401d510b28112050402d1202c00303440c1c544030302c44d2102003014140c400170384680787c0405c0b4002d1091400040040e0510712406800040c0103003103000e5103651180c18800c060014180083c50340041041500007440340c071846400c40010f80000c03881804040170401140c0c1e40400a940b941c0201503c015071440c1a02200d003600c03d241000600e550b0501d0b10ba040c0c40c003030581d07651000d11510000341013504000131184046446004046c005070380b0b5042068075007103003107801841040131903104040d04110144c0b4651000e0100801428160341d000c0c03464180106540c05034a08a441e5120300c080f0625010710214030300356043c0703d000802007000d08804404002c1000d020041801d010070803001494208600500b555202e042d10f80018040c0c0240b100c4007590f00f21310a1080050300d01c5440b5060280030100e801c0f00c148010f19489814003c1c5c0142c034000c004484048204103111003810100c010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 696341771 1250 696340521 696340529
    0x2090601030e03030a05010f0614041a070219030b150303030402011d0d0c05090105010503101505090904060b1807120f0605220507170105040b49020105070f050c03030301 75
    0x46001c0d45003205d4001d140361280c11890030042400e046100004c1c90ac42202c1c1129020021606840301c003409004890050f90f400a502c0044407d03400d45406646249005407030003000e940307005890303002d00800d00c086038460300341d010340007400081c0246d80a075844400d07441e803480910310303c14107000c001487c0403c4104101c0c3c552107041418010b50401c248000d01410080c02c2c500e1450500e03c8464002c46082c1c0b04a00c0000d920080404949208030b007a14844c03640a0008191404c203072500c03030080c180304200b00e80511002e02d155201a004030304e01902840998582e00724140303000e01140050000388411036000c0d916502c0024180c0c4a143d0b42e0302044481010f064108a00b80c0e02c01820768038003901a00400003c6651010300d040310a20708c0d4111141120001403486500c400301d039410307511000c1842001c0d07a900300c015140b10602d8a200000c81ca0b0040030b02d064442c0d001802c42c1500303810020340090381c184a000001451052082c840f5800b4608132a0341c2001c00000138990350090300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 696343021 1250 696341771 696341791
    0x1112010f0e0a050f0a02010206160909021c05070c03090605090402040e0103030f0f0306051e030a050114072a02040b060d020738240d111005031302090601030e0303 72
    0xb001820721009000b01e000305140d04000e0f2606814a4000039624603014000c1090390301ca4110544a060141102600400104c44c040d034840a0420152480403406241c050546044c100018440c52082070f1078080d07079615842d9442c5c0c490800c00216400c0d0031042e0480e40060b0b0070400410400c400200043c000c52007581c60030030340b60071114000c0c43e01c1c40e0030390210149414a1402e104654403110605202c40001440b141d03585001c000007440c0c041c0f005009420b030351900400010104022a0130b500c03038000b6444100700c20b500c6821141d8918030004d000d10400d0b02d03140300240140b800c2d03040f0307160644009100c90f081603030b00c00601049a0111408030364440c0b11514886404030384420000640580005a038010279801c0d14404440200506001d010301c01c1541c500c15400141c4466018124090818004041545802c176034414181c6051442000180791449849104604992103400c0c2100640b00c080c102c0d900f44129094080e048030f050640f11500c00601c03140070001f46100e164400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 696344271 1250 696343021 696343033
    0xd06030609060c081e071709070302151e030403140d02041409010b0913020d1401050a1502100c0e100c0b2d04060605150c060a06031112010f0e 63
    0xc03038034100b2150030f11550f03000d01003c441041402d010100b182405245081e0784110395903141c22003100d0380102400d51200c00c6803200180805134500095004c04c0d01d1090301da100404c201c820102e1230a01400031032503142c46030042d840703001d2201d50b030186030014824145001078680b401c005907a960403d2940030302c3c00360b0204003040407000d11030b00d000e9031810a50b44a805541000c7d40c80030070f03205540d00c40e4010300900b800000043c3c49a412140550341c040d0080204031500c030032261007058203110b07c1b4400c403030f00040420680c10118851555404075001840c6201345840301c1d80140503800020380610001d01502001519465000c40041030203a0b203000343d045480c034182d0307840c0c5c0d80907147c8e05050101d6014036007801507951a40f000d089214550b01480e03511031403c48040c100d01c0e0002908070f040c091400c0942c0c0c040002501a00c003004c0142d441a60b2500b10303900480c0c10703520024040c1070807a80c00080c0c4d0300340b01d10915186162440080790b43c143c0442030300180d0340304156034101d0341c3c808 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 696345521 1250 696344271 696344273
    0x110d080307030501050d02062704060f1a13060f0c06050a091a06012007051503090f120a050307030f050108100c02011811030a120315060509010f03020f0d06030609 72
    0x58803c041c0580310131910455801c01ca42c010070810f00807062030313103003600c54000741100a010250341a1660754008009110082c0c0751a04807160b030415100c3c4c00c83c00c280395580f00c0c05e4014400d05031060300800f1000d6203011850040212200210341d030700c40701400750b94020500821464001c4500c2081d0040011440c4030007807405261b10855074040c074148008240a00c261030703a00c40c902c0040384203500090000d1450000450b4140344031035002c55446841c0035030040002e0217490241d446805a0340a44000a40c03481c000fa48403501d03100711401b8070b02c007044607000340340c0100d019503000910361034001403a68003e04440c2c100c60007a00002e00d203601142c001e003000c480c54001d0042e07140407807000744114441c2c2e038511444605071700303002441500851f520580070f85042000f100483d40080c1070444210406c2e81c06002803004c4911000c0440c880d64020840791f024a00300d5a884406070340b0342e40100401c081c1100250803012009000403001c200c1c12140210900800c1c020314001e40000031003000d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 696346771 1250 696345521 696345527
    0x1407140111070e060102030408030408070611060c04090f090605042a050d060c020109050703030e090f010501020c0f15040b1207090617040213050a020c0d0822110d080307 75
    0x8118242410040c0c01000088901000701c0c00d00d0032500780407000c0c1c1e850303150440140e080d0f01903134120941d00d10000c03800284680300011a00125442500e82c2c014800100c6040d680b1408100c82d24001840d0810080090045a51000c045600348001c0098040c0d0780d80e40740004e43e00107560a482c1340294410a1700b250001c0c0540000822040100c1c803401481c1c00d000c80c4e07001440c45800380c4040d0f0b0340d859203100c00b4000e4001420080c1d0010540322110340702d16001d0040000040214001e14206000031a005040e180f5107059400503002440f50f501c0c603000300300b41200030081b07803038104145035400b8605404036005000680285d02c1209d03100c9d0650b400002281600401144c10080d00b5042000303a980c00441544c919500d43c10001d15a85c3d9600220758044020313014454824580020040e030515a075000c3c1040901c5030065030307078000d00c0b02007c0380c3c48a010b440c9104030750a44400c0464800305940c4540c80726108480200c90a540c00d40081d1a00c410039809444404002041080742c0c1c1c1c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 696348021 1250 696346771 696346799
    0x603040f030315061d01030c0c39031b03080403151d011a03061b03090313120317151306090e0c090f13060b1c030e15041d0408071407 59
    0x71080c1f800704a02d0b180d803030004055080648019280340b074080c8400320401c1381c0d841c0d09442c2d00b00180083e008001d4100d4030100c42e01d080d01c0152804132102c442c0d40148206100e110044035000304500742800e00f15120341080032401d184180c000c540d01c415107500aa8508084100c6500e41c50000035000e899a000da600503c130b84c41090310030f811800070040c071092180d03034a0043c0d030300c18009031340c4030794400740b107945580700340101010860866000010342402411200c2804ea10a0703643d10f007010107801d440c4100c4c20302500d0843d0400016028240c0d54202201d151042c140070410200b00b050342c4101c0c49089401c50318000c01c0e15045246690003e0801c503000e90b402880201c5c0c41c03680340c81c11013100508064a000c00801c001d80707030484210680d031307034444400c9000b81d0b19004065081040c90042e1104c903511000d14043d0f4002c42c5030700c1c054031840c03040e14219500111020000280c52510444c0c82000a1085507410300610414000ca4003000702c8440c151440340c001c0c02280d041111410f0f66103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 696349271 1250 696348021 696348077
    0x1031e0b0120190c0e0f07030609020a200c0a09090b0105030f03090415030b07020a0b06030a02063a06080613021e0a08030705070515090603040f03031506 68
    0x240800022880100e0300090075500e00301e2400030428a40500d15144c000c480041d03000c80c030228040000d1107000a54200103502541c00380d01c041108640d103402000c16030007001300d0307035001c2040b0424060610003441585901c1c00180c200361f03007468003001d0000e079070380c3c5039500b0158886545d20240b07020407000326006400350004500070b20f5004900e81c4510303078170f21800c561a4001c5446443d07260300f0740d0304040f078030029507800f20303002c1380501d01900c0c02940c80a00364400d5031030000c0c22000c07407030a06002c20504100794000d4040c5107030106480b484903000351390100c265404d101a00724045146e20b6010110302c500c0603000c0204803036103070020072441d01c40050800c10702140f041500703e006079940c22102060b04010310244d00c000c050600003850458007640410702d0f034040011904100b0201244800c10394100300c50702c0d200c90319002d80d05c0da054014620059000002000404d002ca08046029545a0300c04e24020400b00c03003e00940d001d00046900000200d400c101007048030204603a140c504503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 696350521 1250 696349271 696349307
    0x3021003021e0c0a0f030215011505040515040807081605030c090103060b040b040e1510060207180605060d0209040f0905070b091206091509030304170901031e0b01 72
    0x10070030340c1c031100c520903041c1d0880c05584000043c02094014060011100451700710280c00560301003801c000c1c3d2907419003203400c0303e512103000c00800c1c0c401245840740084aa2a82d405040c5401c000502181043c106444c6491130014000007415040401105001d05810713030141028000c41d03d044002012940c011034440d4120031301030031301038650b82c240c141141c3c1c1000c004203600b900b45000c034005144407441c1c0343d04181010f42d0710500800016a203035104d400203044412503603407100c10300d188800a018690040e040324000304200c400c0004508903080c8003040c0010b400380c0c1d03003000038072070350041e43c04000c840d4020808444501c0c052203205203c00e881c80003800507040da03507030f03440d00c4d91043e006803202940b01049c41095a11461360300014880d800040f039038181016203005594650b841d2098018166030f0b0001448620044166401683c0c0f11710561601c091001c40e03007070030760003071410030741019a00c0c454550484000c01e0902c0111244400010b80210010001083e000c4210300220b40b07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 696351771 1250 696350521 696350527
    0x6032e0b0a0f0f060e100309060221160c0f02060c280b09010504050d120609051e090f1b0111030a081b04120807030509150301080c1002060601080601051903060302100302 75
    0x60b03a01c9207803141c0468086c525001450403100d03e4200000d001d503c40c0062944d40918002c2d800c40c9a00032254041c07508081000c010048546040340c02c81c564075030080c6180c04c44403a000040c1846d202a00210b414102903800d250740c00c503208000d020100e19131301510b03030192003c281444942c06031181c015440d20024012858181c0b600d81da512103440703c3c2804c20091141c0c90701c0a041c294410b078064010003005201504059681c4810001c3e0b204008192010527000718090050000c5c03030600c1e0400d80c034041d00d9a0181c3c4184a05840050700b20641400218410320f4903d11090000b021030140588949645003000d1403284074044a40e184040b440c50104401e1106c07a51540c140c1f00155881958a83c0d00c01403458221094060901201e400131076021503900d640081d14003840c1650041700455419201c0c250400121614245484001d0380090010440c1d9501c0f808850358001c8044c140380f85440701e4405003507004520300840e080001d0307407003c0c18001c601e800548004040c4041c541981 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 696353021 1250 696351771 696351797
    0x2030a170405150403180f0f121703070905090405030a020106151202090a051206071409130b18100821030112031403071706032e0b0a0f0f06 62
    0x40c0c0c8110180d1880302d075003d4400024101407190110826200340303109640d007a075545502d18101100d0b03d001340e07071640a1085010a2252011440b089420341144100256442e11090f5081650018cc000c4081080f81400406e058490410650107a48034100650b03075a0745070302c4003c1c21146283c00026105104034019040280d0001002e940c24000c000c0060b6590592000144060044c2e0311064008903020b069100c04800420750620406458507450000380001021b0f20240c4900a82c0030740c0042e840441c2c40c00540300741d0241c00e110308043c0030404814441242041d1580080b142e00c110b001c04d0030800d00555100f4414003104c00f001901410000014014010643c00705004144042c0c44c43c039503500074103100d1040c4100411440c00a141d59040c000402030042a0801038004203a1442e00842e0007400c0004224aa070300456101421038420b00c000c0c001803060072500d2819990321160300412a41d030f00c0029400402d5400c1410a0551422982d0700005034541d224205100c80726800f10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 696354271 1250 696353021 696353023
    0xc08010302130501151b050f0d0f08010501120209041509020405040c0c05150c070c0605090a1409010605031b04090501030501110307090501050a032a031107030c0f06140702030a170405 81
    0x6400e007802c0c00c04107401c1280c040442d0345d9120031b070406071003446003c1d10340c48800310101e409841410503907141c0444003e502030030b0758000c4007071141e0ad00052602030346400c19041035019004500f40202702003a010340340701c000032481803a07130800848182c1c00074081141e850184200070039840f41c2d00b080341030f05000391142910748881d0031070288000c95030400142aa0300400c200c03543c1c2c0d41d21a87c0143c0f50303500e5000c014965000005100d0040d00000c00c0170845104190001124000040640c0801c2e8248041220300b40c00c003420720300c0b0361803109054400b03181038640a8000307040032034030000d01580f4505185081d00c0072450a19032a0000b082400390940c1e00285440a6070300a0901d269140c80441044005000c1c5442d5410110050241d0b050340c4008004200800441a9401c0c0f140400442c03200380345102c1c016005000c900d05030344480c0003400d000c0030340301c403c0d014002c0080ca690940b07581031032a440856440006070000540b103651182c102c4a0b01009038807a040d088594a4a91380c0d036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 696355521 1250 696354271 696354299
    0x5060a03081206010519020102182e200114010501030b0a090506010c0b0114033c07150210060b0301030308040308040f050d050a090e0c0313050109060c08010302130501 74
    0x900b40e03802c0788900161007030b40614100c03056410f41108640b8840c038a000001e000303422242c1c0305480100c400340085628603003401d02040c4047d0302403150700d028104500c51042582c1851284040c000c1c505088100305440440f00c2480c42c0224001081c25100101c0d102044e01d0142c1000b8141481c09034205165100e2591050543d1800e80002035192110302c0142c6060000c030100402e440d100034004220907060f18041102014203501300c1c0d8110752407034190211b0035014842c00700c41c0007241700510184524603200c00440c00300d18003a90151501c0c1d1801c8c0e64003258020005000d07a214054060800425204140046c0044001c65040d54110b41d030003456420302130800b40811840801040c240040b0360010f03101341d0f50220071552245a111400350298100030484804107100550000f00c1d0702c06c004070544190324130044185541d9401130702c8584480c101c1400c1e10190340e03500035040019400c0c40b5240c3c0c0000d00e512220030940c518410060b105d610120101c5840d4107003c0100008201c191038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 696356771 1250 696355521 696355537
    0x90706030510300c03060f050609250c0f0c180b030d0c1103070303020c0103110909041e051203010f080f070b18061204120908030403020420180405060a0308 69
    0xc40d110b10804204507420800d0054010b003034081c4d00b45000040041d941c2c0705088030f5070030a8050225540d00c004101424030201c64181100700e0040302c0f0442c0d000c040c454483d404401c1c0c10000010941d64a421021a005000448810944400a20075404a10701051349205001010b201680014010a444000f0780c00f600013030080041405007040180e9503600e0030746401500f00e5070082d540317060081d40c80b07442d16100e41c0031a107400f040c0c1c6854010302085030041030010b44080d0182c0c4171a03490000001001141240030082c1c2d00000c00010420b00031a9145031180da46544c4950401c1184078440c2030300d0780b001c02d41c0d5110310707520080c1c41c00124112040342e444004107500d402248204030827501c1d00021040e07000f40b0000384a188801c0d0101c01501940c044c0602d80464403101d0420344000d6010b005240c92030344184001c01c010f203816002620b01c94110241c0112001010201a03016000481129103910f01d007501c605440c01d1a12440f90f000200303c5030194180d01e1510707003419600c51090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 696358021 1250 696356771 696356819
    0x30103030504090b121506100306083406080103021302030f0f100f0e0a060803131e1a0c0f0d0c0204090807020907050d0f020a0f05090a030b090706030510 68
    0xa2104c00503905c071414901c06410550a071100c1c412080d20b80d28107090b0454169200d21040d440782e14440b4400c0c030909040c2c1d10b88030300503c20500c0f84100a440c1c1c580c0310048180608020509030120111480448020106a03e50b0b0a103541940304201485174070380e4891910364410720801032999400007015800081200c550407264403648581442411039030400603c0c030414120001c0c031014502e001d40e1080d18084010801141c031440c60545074407a2652040350101d00010070f01218840f82d142c080020610907400f602290740300400d00409000f4003240d0032102000c1140750903100144a4042e07540102005000d650480c03580c06041604026006401950791302c054004000d2260203c4280d20340045c800f0310303517141c0301c50010030b2648000402e420703050500301130054524280c002d80f4800281600c0b082420613910100725070b141c00209160742d11200801e1300001080d84541841d00561151010b0142c403070511002500740c03100a450400101036004003085a1884030790f0742c0041e220341c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 696359271 1250 696358021 696358031
    0x1e04020f030723030705030c1f0c0605100302010f09240203070c080a0c0e1501030b040b1012060e090c0d03020f030f07210c0b0c071707020306060603010303050409 72
    0x840824680b40140d00094503904000001c00c98100c022800e200001e40700301c08680c0e101340c54105040c0c9541d21a0052034100112820070440100d10520360000075060340b800419480a81d04c6040c107640d003d8440010041e042402801075507072141d030002e4242042c0c280360404070710307100b5506666081c080509144111030715030304020900c28001c4400c0340d07030000002c01344039440d00c4409458000f413503411224000b110800054807507101c00414800d42c0d0080901861441c0c080056003c2c00c8604880395000d940d07196a070751540e0300d11012801c00f15880c1d0391007003030107821086442102e1340350301304250410700b0038200004a040080c4141c01108151415010b140852038141d00d40301d50000151080d0001140385840c228640700980740043c041e0041c0441314490f5884407401c1e10882004c04000b82904850750045506c5205054000f804800003070f2601003d600c80000e05000d990ba88450901c000840c030043d490100110750f0000c50071144c0705c0c42d55146a034080d015120720f21510340072a48031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 696360521 1250 696359271 696359299
    0x51c02030d113417130305071e060509090a0e010c030b01030509191e0b01080a0c060306140111030c03120402041a0904030305090c0a08030a0801170c060f22030303051e0402 76
    0x45400e860703500d9503000031800d40e56124907040f500c40f08c1902440c1e80481102c14940d0302010701e140717100200c0c0c1e5039403200c174030f0400c2d42000e00543e440000c01410486840344500700854100740f00340e110503129030364005001c400740c0d0001000d50b80040c10f900ca0760f0380074501800a080402f00c00504565100340a50040098484911800006101d024050142d017400009544078049000700304284101401c062040d2210010390031120940642c106003200810380c003406502580d000007e0a2201e03048a0030036048001e01445d5034003990390b42140f10b07000030038401182810701a00a190503001c5100c02c0091507000418880e0000a00c090200342d1104082008808244540d086440d0041c04801c1d0300760715244502c0e541e41c0034041303140020b9058400041e5010450680c1010011100c01801800b000300c02081074982044249268261042202911180200081c8a0413005035a084240035195050150484000405000960301502d940c0c4201440601c4060b41c4a94121003601e810246 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 696361771 1250 696360521 696360563
    0x60503060f10111c0f05090307170106030212120f0f0c1009020f12070513060e090a030f090f18020c150105030f0a051c02030d1134 58
    0x1898559504803184036880b180040c0d0100c22841256200801c640054404103011002405801d1408001903844c0c070743c98400e02d02c100300030400468002c040300c80c8140c542980401600c41b0702c000e0500ca80d514501002142800c01407402c0b41c0714540064401e000240c403000003144903584c8140200c000c00030b19001c00c2001b0005a81d0824900002c807510704260100080c018482400140d1040964820460080c900382c004c10302802c02100140800f1468a824041044095442002d0b5070381c0360342c030214001d0034184070340384a607003a5401072060070385c00d0401800640c0000b11802c1084040002446a01450000e0070111014100310842c0710344a609850024000c044100840f805070b040c039180c5004000009605844044098581e203020007507049a40b010107560007840f942140e440c100000c0e09048003099070401d2401500d10f0110541805401c580200700102c01c103a8020988031507601038943c000b10303104250f0800c030003440120980505070918010000b4884c405065a042507a09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 696363021 1250 696361771 696361789
    0x2301110a0c0f03150e0d0f020f06090304030c0f0b09010509040605031009060b0a060c1203060e0a1a0d1a040602130b0309191e080412030f030b030d0906050306 70
    0x740110006040359280e108007800c040b0070b44000d42d2000e41d81007030121083d5480c0700366807003280000018100429000010f45440007031314203820a6005a0b0191510005d040c80700c039205075420707000f441e655400d52130045c200302025007121700c4441000d0010300c0300c10407500803104401e4007403c000d901c0d40c2810000402501c01600b010350580641c80c0790f164a1078661b00250241441580d00b4445e0409903002c0c440750300e81a1086034001034403040e520000c10706100007000000c141340382c042001a140c520b401c0c88003c040d50050301442c1d9036a00c0c4d49582200750071003003e030041102d8803d8108500e03141d500c443d540402c070b00415203402030082000c1081e550704880310045c104460158107641d030345400061360411207042c0414024000c03030102108400b2445120140d000c0265003002600008030251003c486034110b0b903142080101080d00660030456817000d5210750381c1c4410340c00862000405440c0d1031049030307001ea880480118030150308254080180c2e140d9260242c0c981da1034100052400e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 696364271 1250 696363021 696363023
    0xf04050a0c080c1807120f0b03010908030a050703060608010608101505090a09051e0a0f0f0626120a031506080601090b0c03032d0906010f2301110a 65
    0x3000752078001901800114911000314800c440c403034090304400000310307000e04040310000002608485c0c0c4000c500e10320313400740140d8060944006020091400401c0c03c6914250050340c6140c0003000304540d01100c2e000344d942c0b10f019442d0a001280c0b40100240c88408180548804d101101000030446c0403d520624000c05502d0b11982110340005006403150b444540e90902803400d582000c03d180701240103107801081c0b00c07140384444051098080b5a401c00c00b03842d41039006d031500400030b41d606c1e4034052441d96407041e003400907041c1c6c50701c1590b07160440340785c030a0b101c1001700d20700c01340062101003081c0d40850f49540d1417641d28891480100c0050804001c02c3c201c506000b080418410ba00c000c007648038950a8071800c28894940024031b0f0180201c4040145503401000025416840c0d8615144d0403c01c410038408001d406c010f01883e403030401c60301801180d00800040103003a0701e60303031004010300500e0000c9001900520501152100030900c2905121001c82003d14a00041000d14541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 696365521 1250 696364271 696364283
    0x90809030109140111180d0510020a03020d060e040b0c09210a060c050408030d0b0d02130504120507020f0f061204080d0c0504051e04020c07091415090f04050a 70
    0x80381091a020441d0301c2844810f500302c0d86083d80d000c802001142c00c5481c41105480f0081c0f0382071085040081d07014004008031082d000f4640000900354280c005020541030940f07015895841c041040002c0703070700310b60050769440c1c0503805200c00309a050380015000480204140d130782c0d040c0e806c042162aa45d010409090500294284000d03d81c0400d00000d032510810b0280400724800710115000c1c0514050b84000390030400501c8215103d07a402100d58540181c0034540c08610354000030684551b10321354804803620f50040008000403203081900f584170a041082c1049400c0d004104c40b01c80d80302e0a18000d68408035107821954070401030b07444040c60661100781c50f00e05458603240075080030f01c4203584242045217032141c1e10300a6007034805681c0003400e0350301c884040d050060f0000315951141608a07500308082c01c0c01c19000e00005026181e14800800c580c0e640c54444420800018080210049028250b5410755504645540c10044803070b0086151b031100e04060b410720701568002825 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 696366771 1250 696365521 696365531
    0x60304171606020d0e07030209191e09060b0324062e020c01080610030c1107080309010216121401151d061002070b131203030527100908090301 63
    0x80002d26001030544114070341e014841c000c118483ca03660390340075005c02940803540c100052201c08038a0324003161102c0c40503020800c002e0511240a003451440340103059903481c0c980c09024001c0c60f00820300800c0040e0b0041180d070101200c0e000e00d50910003805c038680b400d45030120700180d5440240b1118902c002c035000440b118207041d00700070030b180c03070421001500903000c4c50740302503000f2018180b05140140543c4d5040b440034104400420840315401c0c180140b2600200d4461420030152014004000c02103a4030012384001a1820b1074100c18020400c2d0801e82c1403003203290b080c00c07001845900240c0c500210700c20540c8240034140c40700c00b80190794030441000070000100d000c04040c0070403d001e6003d164686005100a03411200103c001582c00402c0410001c42000700a0600500c60380c2c0440602d51940c42803201110b07140002c1d40041e40340c10030700c044501c80c400c558400f5218181c10f80b280916000c41140c131200d81c10440c7d50581c0d41c1c2c40e0f003102401011003ca94005c603000b002000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 696368021 1250 696366771 696366773
    0x11b050a120e030f091c030e06030901090f0b0a061202030d0e1512010608070e28050409061a010c030c11060c010504030c120c0302120d090b010e01051804020603041716 74
    0x82c444e0845c103c4a4400d5140005665119049040208030300d5003555a4801003100c4509000303075a44003811840656580d00d0710071002c14450b04070654002e10503400442035041000102c0d050f02c03210b400c022400112403011100503640051200b02000301c9040031316501d82040e0004c4c065112210940503059000545400e04407100b1050034142ca200703846200490702c1c0d1007012101040c003000301c10303088101202510100710340031440040a0388d640600d041c883e0f444601180c02e13a4148031040b100e00d80c544004441d0300180404028580f01c0a1030301d07501c01d0b501c03614014860a901d0b00040c000040240065a6580f65501150f14885001c0000c1c8224102858001d00301640c00105032010076103500400303c154411120644002e41550051034016101e01825040360f100d0201e08031007070790322824280003a0302c03038101c4c2c0d00900c0452517246c5550300d04414441c1c00c0000c1000307000400051b00410005035902c00030390781c2041e0040c92000c5c520342d00205420711032240c4000318086010300d01d0140 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 696369271 1250 696368021 696368047
    0x2116110a030c030c06030908090d140f0a12050a1e0e0a0b0901020606060f0417030712020f07050d080412150f06061701120b040602040521011b050a120e03 68
    0x82c003102e110314040c04050340d5548084046400903400180030701410040c80c081450300c40302c81c0540c5402141001070300a0302c40d070101e10700112104110031540040c0b021009210180544803910f503a40d0400c40d2130038180c81e400805010382c40300160301c0b01d404008001c500c0c0e0720540c0403424605002d42000001c680780c800e50b84103908002d800600501c980e41c0094502e080000a0381d450307228038103580f8101030411410602c0700b00c003038000704010300c014007406000c40d02d500100d051101041d0007034a00500c2145005041c014160001402100960080c0001135001c1c81124101d034141d031200701c080519843d1164580c42c102d01c115134140c0c00c101c51143e110040d03900400032907143d5181d12001c40900f603091903401000744900d80180e001542c500c00410f00d42e035000c9500610441300185869100d070005200c0116501c9140740c40d40c038401c14055030403800d03c01d904200c000074116116000380c0400041443c814541c4540c2005821480080700d00041c0c2c000b4a40c1041ca007050f20b8680110002076 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 696370521 1250 696369271 696369293
    0x1818010e060127110d0b0f041406010801092a1817011d0a1209091401090c02030c0607110304081002070221060c0313232116110a03 58
    0x1c4440d00303000b0080100110360f5104401d800003072001d100341401c0d100300c0c0110085c00286c600c01d400c80c04001c0b01c200c80703039560b2182e400b644039403412545807410400001402c50342c0c1600102c0c0c0741388c58081d8400c00112081d100d021000e00e0411401f6605440c900c0444006052041d45100600300307030804240a01900c50040303018044500030402c03000b1140705d50241e102410705104090b0000500500407561030825640c01100c139062019105540300101c1084035580110f200407200031800511030f00d0094060041083c800b44011418101c03440c0c0c1c81c0d0b89030180074000105201481d100101100303001c0c8180d500030304c100004e41e070b800d8500513031503000ba41c00722800320f114030701301030200841403043c1074003005541e460030092800f41c2d81c26103101500d40c40609401c0c1d03800152030500c0c00040303801584840034064846c091100030309085d42c262406200c42c4501124a01c03658403415514042410b5900601c03242d0001602c000309400d10809032114a1401a003004002d40c000c000c3c858070b2000e0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 696371771 1250 696370521 696370559
    0x30b0a06050103051b0409020901050c070e011409190e1218090f0f011401020309120c04051503030a120905010e0f0f01020405060d0b01030b03011503050c1818010e0601 74
    0x600c20380e83c039100e4044011045c10b62024802005100510505500740d002d00416501170410f0745c83c1c207100000316403030040b0541c410446142d00d0401806094820100791840107030595142c1020300700341c0300c00c192521000480800882d44c070726607601d5854080107042703448501071002c2a5101c1c031f00960031a8410690301400e01840440d408540c4850303031019503130b00c40ca42101c4901000c1e401c0642542600c1003030034550f81144010b000105007990380404101c20904a00f004004161f82300c010320094400060003030314482d000c09615401510080210750302030455240444161100d9050480149a520b201038100c0d841c00c0702c001a081000036a47e0842100308040710302c0c2460030310000d401d0748550700a5580201061120840e92070207a0054480c41c2414180070071002c041c0000b0030b0840d080801052428070340e40b032082081c40018400c80080709401d070340b00012022414102007000d00090441c2440c0e001a640c11141e4420a501180d00f100b50f0070203803801569920f40480c0742d0345800c18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 696373021 1250 696371771 696371777
    0xf08070614070201020a0f081e0a11011512020402040e040303021222020108071101050a051506030c09061b07270e0601050114091201020a030c02070303050919030b0a060501 76
    0x30071595408690040d20016a0705038010040044155a042181e80f042981224116000d00142400380216461004418881502c00b43c50701c084140040181c0c584102c1107440364980003140184011101078003041d103100d0241460802010300c00300b0020f1144d030740310401142001d0705200406074990000d0030301e00989032214082c2c2e10f80241139011900b80c1615004075564070701050300154001c40c4000e5011619050050f00078111080702402c0d01c2c01118030307008141d900e10821540c0b41561100501c0702e401500c43c2070561070b0140305a01c0c148a92101c1611420b00032600e07440c1d090001400000302d041d91401d07a00749076555400305481c4510340160304030180c5820303025841072006210740c0c003100b010f100041101781d03c5e200054401000c490b041344004c0e003003082910800d0701c5500c445040040140c0005a9907130715000000c0440b5140d002020454000000c01c03c0480c0e44841070760f0041000310b42410401c0e140702c800d0140140c0c0c0d588024442c003110030820101d601103500c1074088070001c0c3c0f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 696374271 1250 696373021 696373037
    0x90b0d1a010503011404050c12070e010f110613020f06180f040c0f0c03021018050106092a0507061103100f12060b04110c0d1101110f030601090f080706 67
    0x303006481500003401089a150580c44401c0800c0c0340c2504120f408c00c40c4074080c140b0703118100c4115041d00f03c0455620b40403911a4540d0455540c0c0304500c0640c4100b40c0c54030440000941c540b094a524001c0c024a8403000c201d2039990641da80c1d0309000c080304a00429680da100700000002c02d80c50040c4030102d20035000880f0105e03850a1602030781c20301e0318203580c1300c0c4c6426440200c1910b40f0707900c25a0a80862140358210400d1403018440c0e40c102036200703800203540740c60710b10348182501d440d500011000c03810080c11150044410310355000d41307900364007402c034000b000c224211420b015a00c0050701e85410082d04095024064000358014541807450246d60ba803a6200c100840c20140b01d40d0040000c119030010118100f603000c1e200000c8014404111520700107103840c610380014120740100d0300413540014071150405800e4a8000085000b0b2003402024480b4880500581000307215502c000000104280e2080c042e0001900c8980849070415480300102e9584100c03900417403020800c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 696375521 1250 696374271 696374321
    0x121c0e0a0e27070506070f060609061206050a06030b06090901021e0403150b2b0b181b06030402060a030b090703060911030f01380a032415090b0d 64
    0x11078a88142c54005d030940f072030300c90389699503003803201411400c1d07500a55800000c01c402d0b44034050040149000c40300036407481124108035084900103007114030b034145040f20800025003040162503201008850540095039940384440c0644038070100000601c03a48002002406040700c058000d0b01d008007808110650541904401c4640c0e4103402ca0b480b80c19400f0108040d031805000420300c3c1e03540310b10344604100f2a66810852002a0f600019544022003911100c0f08200f10007080c006e803000b43c1007200070141c80481d075036201c0604064000c2c900028a803000a000b5046460024405411070f600e5150100c0010000c10450054041107410000301348080d114202c00c0d00d00480800390301c1005a441e004448244c9803011345440b000020350b1040b9000320014040001a9a2280410f1662802a07200c01000c4880f101c3c140400c81e054001507844007103060140d4010340c0c072042a0300d40e0000c103c08003a18a07a07000d920010401c400080c889603103401075009007450360303503243e1424410450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 696376771 1250 696375521 696375523
    0xa17010f1410121d07080607110a08071721040c091e0b0f06040902070204140412230c1b030d050a18170c121c0e0a0e27 53
    0x10460000c0010380c42007002496800a0ba00c0080c4c628492140c45a100c11400149400c29543d030340a41d86035041b5008100e051a0043c040307000000c1c2090142050001960b0360007558080d4520160a032100b44001b02c078844020800c4624582c40810002403440084465040c62a01120221380c2c0341346906000800301118098044031816188102d03144180454a6034020240885070300c0e030001105480e400d072912500003e00c040d140b801c0000d0307070350616070041c801034a0070142c00c1030f0800211020800030511112900c44010101c0c500181420441d15032014841203049031106e4017500013828028041000078504008007440c881209110900c20805d6200c0d005403880101103101000394440e418820451200e11011000b42114180e840ea040b001d001d00d4948241c080c00d5001510030b0300d051801003503800340c90102c08010400d2408044400c4090b16684000c5001d0014100c0c0883c41569103d000c200900781002410705140b40c420f0391000540c86100020f65100c4c450f65202d410050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 696378021 1250 696376771 696376789
    0x320060301051e0411040b0a020c2b1a0c0901080a0504050d0c03090807151205010f15090512030406090b07080a0f050702040e1c08040c0306020a17010f14 68
    0x4000c0c2080c0c4000070107088181e2015030b000f0001d03403044c2d4840740084459880000707030010b445119170207900c40d41e0301c480191401c0c00401d8001e00c10401c031095080c1c1e800c603100030442122080341c206c0707521180500e4684042e101070150703421102c488004203c41f0282e118007801c0036a400760380761060741d02e440d481041200c505440140194001c2c00c95003030b160f40605140050310b80300345806c20050756148012420140e1582007521102c846186ca0091103a1050f9006680b00b844007040081d5450000f0071141000103200715400000780c054800d140d507000d450b44500404000d05150001c00b0703c002e0fa00d0f200d41c06801100049101d551000c12074900e0703107040d0b5284507440b0303611780c0c074000ca401b005a07001805001a00b04001c81002240b0058071240600c2003020150002030108c2c8601d081e40d0655071003181c201008000e400c804000100d581907070458101ca801080c010707924a01558103d4080179003590b0001000c06039000050030318a1805d5140c01c440120240e4601600900d0800c10780d14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 696379271 1250 696378021 696378029
    0x70f38010506032203120e0309030d210204031103010e120d02090a03080c010c09061d120c0a08060108011a0d03030c021f060e01120302070b03041b0320060301 70
    0x15800100500040c1403140045030400320980586800c42483c070011800b050070440201c0020321802c02c106c102508071300802c00038844c10300166082405140100361384c1c06c0359103450740c02c1083e01005240c07099400d441c0d4500d58200034100355030342da8403030038080701c0ca0000041d030a002c0d40c40d1020300c8182e03d80c085800c42044001c000028075140070190000b010350400c0c02d4140d40030030704182c00000941300d0002880e078120001c00115107241c40311030180c65002a0391100c018841001c848a4044010711410840350008075680010754840c100e20070f1038021034900c1c02c3d4214019241c00314400704006a4036049031089802445100201d20100480c8514200450f4000c540051300c8000240207800c410549900e51044030000e103101d091500d10b0500060301e9010042c1c1e02c020600003002c0302113429015190040300e0a2910700e42da60002e56031a00c901c28001c1010012000ca420001086500d00b00011003c41d2406140d48a0400e1150b0607400b11002d0000d0254412440301800c011044e02d04132 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 696380521 1250 696379271 696379373
    0x41109060a120501140103030f02070503010b060406050705010b090403090f1406041503090602031617040201050f1315080121111c1b08060901140703020a020102070f 73
    0x503a14042e000070990100d9041122a9502c5410842d110701258511600a602030740c1d601c204121041e90203401c0540680081d4080c0e4102982c0080b10307115003013154115240b41c038010741c0c0d8400600f040d030b005204c2c1a104640c40b100e40700a0106040e48102c0356401c0d075403180c00b111036903039441d183c0c48048501508855004502807004000f4500c1961101140b01224207001c91040000c1d07544004a81c81141c006004e0050301c0d441e81030260f030003040c1aa44040900c020f0f4060700b041d400181c00d601071501100b4461030005640341030903800c0041d140050540a040840b055031b005400340201c2c1007402a03401c3c040142d1110745a540c5500408a841c0d504010002402c804010621140344180f9001c6000c02d400c40ba15080000e040c424055041034881c00c001220314204062035043c07640103402203407035a041c500780c00341c100112200385400c41014280180c1d544a10002680640a4204060301190f0480030340c106202c180d030244150101c10005000381c150755110030b6076065101c08102c03821 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 696381771 1250 696380521 696380539
    0xa0e091207061404060e0c0109030203030f07170a020318040c12020d0b12070302030106150f0804020f03060a0b011103070312090201210e010b040c2102041d04110906 73
    0x40c800c154401001c0e01d50144001164440500c0c40c9008214070580d412141c15030758200c900c21046061013849020142440d007880c04503d1500060b07541c0c0a07445078203880e441d00003800410050081080040440000329007502c030309400801a46030b41018410200080352180703d0070152800d0300c62640070300e5040d2a46c0c030b880070442050301c000390070018190031016603c0207003c2d060b60b601c0c4842814107540000406820341144189800c1d0b41555003c6060781c80020a20840304d034005c0000301000c0703480d2034048410f40d12400060074259003160f219405024550500048034619040100030000c01e80343c90811290742c050a60f683c0c86040c074003400040f881071802300241c90580000da036590052400c0c107842c607480d05801c00c640721a4680755804a039078031091080d06100380039031001390008640422284a19210140041d0201d121803000c0317107000d079520021880c080e07042d60050001d4859558154840a901c40b04035002a202681e1000e8410700230103061908144080c4a4003000c2c191382c034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 696383021 1250 696381771 696381793
    0x50a060c0b070509040608010f0f060b120c0915120f060a030308090307080a0c171204230105161701031106070503041d0a05180606120102040f140a0e09 67
    0x2501010b401403040180c00c02070000d0075920350044074003030610040001400e1981208400450f003052000541503820400c00300312242c4840b05803818002e01c0f40380000c01d9941c400e03141c1154130400c0c0c9016403164982c5003080d180d01100001d045c40b500c0b503600051490f1100b6040043d42c8804460403940024100c0061000034030a460045d000301b901401c0302d09184880d60394003480c2d000300070304200003590074490304c0c248101c44030b0b500900da000340d054501d0f00c500340c40d10001d528002030000e0900c1000307045800e9400160342081c0400401c00008018034201070580c610040d450210407070014400790f120440d4600141001e60499a1140000351a4040d80d8103122058102c0030040d5190300013400001045554298114072404030007c070040e051402005002c11035001904402c0088000c1c0c144183e1904d001480c980c0112088075020b58480c09610305502a00c03031351f000031b00c43c14031794000042d00b007002c130744030642400e800c030340c4c143c82c07181c9070540305807448003c403071104155104244c0c1c04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 696384271 1250 696383021 696383033
    0x180f07020c031e070302030a0f1703090706080c1201090b010e030312010608040f080307020c100302090d1e0204060902192a0c15090302040c1803081b1e0106050a060c 73
    0x110842d04004190f075441985c0b42c0000c3d04203c0c0e10041655041080b450150411604800a8610a1003403d5843c1141000260f295a94029029240a01807480049245e01600801313442215454048125a035a12a031919001d4900c4401b15804035080c0340c0064018580802034401020148907000a01d84c070f00141191540070107801500c0300d1841450400101d102807005503c500040d400030141d043c564020711000c403005d0f40c99542014410b019000c0741da074482a140d1000c94012050617885061208483d04800d800c100c0254030a2805100040303104268000d450102c006803140c0d2004103402101740c403440000c1854001500030075050074240b049100820302c10034018072651503200c0e100c4040005039a42a1503000214400c43d03420000c46c60203016080d620030301403624242c101440b41103182c950456000c01888400080790a03000400426601c01d644c03801501114005c0c000c0241d11848100040c100841c2c55007030060101c2c450502001d50011a1896a1004101d04060301da803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 696385521 1250 696384271 696384313
    0x2102090a18081206030715021c0905060406030b130510090c140a110717030405060705150c070b0606120601030209010210111b12070206070809180f07020c03 69
    0x4403660101450004010030440c80150940381c01c0695060f6540c280a0300f018644102c0d60b100c61a10f10290358000709840c2c0c00319001414002030031203006900741e450f800707030349226080d00103642009010034001076183e0f154009402d50601a580001004034247c0745000f914070440c0c0229071002c41e100c5c100070a1940e540300c14041da5070740c13500c0800310501504040c80c82e4070240700a000581e0510f00d40502c0202400404014520316803044074007414002100c1d00c038000c62040034495100031407410103128042c481400e01c0e059400f580f005a02e00102c0041042e001107900351846070b030308030008a45041c0b0754122640c1040d45a0440c1c03507642d5250044010758806480765045001e1102a10802881401074007035020203c2600c0c0c4e00c500c90300c50790a280410358a40d06219501c0000429014050102100c10f92134044e6642a038400590402a11714842c42500f180c01c2007596114400b18241c5020050180a0ed142c071441c46850385001240d94081001106074150885039035150f88844110384 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 696386771 1250 696385521 696385541
    0xc0315010f050f070602030708150109150207080d0503160306080613020f042a03050105210a0c0e0402040605040902011d040f061511150601051b0607092102090a 71
    0x10207854043d4031511509503402006044840702d03000b0050004040d04603030003651040002c10349198015502c0002014030aa601c107030748401c1400c0487e8003031315109000c0c400180840404462200c8080b54004005a100310b030444c5e90000e851102a0100b4840c0c02880100c400c1c041c01010035840d07000d800391040c56454401c81e440491642059803a403554040c421f028444490080b4202002c20032491021156800800405292200601c4250f444c50381c9200b8881810015001c4d403c9400c82c000c1c601217416101528000440000040c83e00380c51100754400ca00c2a07a0600810380e44409000c103552941c031000340031070394040d0403640c070910761418a41c0c01d100040000c918848043c954008480c015041205840001c0382241d9400390403c04185170345203040000c0800225009440c94003410252402e41004000510b904400c0d42c0861820750900402c0b0a1b1001403c00220240c0010700500c00d6580c0c82d40d208017101940155100c00c240301c1c640290540a203a520050f0700f40003440c1041c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 696388021 1250 696386771 696386777
    0x4060e060c0d0305010608070905090112030309050609010902031203041a09010b1002030706060f080d0309061409100c02030a0207050f040239010207020d060e070e1009050c0315010f 80
    0x11080e81140c00400440412102d030340c80c002019418184003c182040041a8030288034100000304a2611403207441c40c1100c2d00d44250300b5a40c48180382c02c0b0302400131800080c0442c4200e00038450190340652002c80d0030f0340f00320112016051604160382c1c09020071103002d01103241481e240c0f55103442050b03140d0703408807001c800052800c40c018001002e0794007060303030303a00164000f05010f0100841c600c1510058040c10b07120364400740c5058211595442c0c0e40040c10100b544449c8800104040c94018880960b0383c44904045858254845c5986900026903041d4290814190f40500c6d4004011108501703485da02801c41c44e420f050601c0300140e40c015240b900180e0801000080a03d041c880c0c560341d884106104000141080301c60381c0411101204491f00d03403041125030011781d02e0b0301c0d6080303c513071b4054000b04646041e00081c0c0d041c0360081d40240c000a90302e108114400014025178000d48210000c100184d455108641c4030b03074002100c416204d40c030b12003600505903005881001e2028941d01d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 696389271 1250 696388021 696388027
    0x306010e031f020c010515030a080d060f1d13031b26190302130504110702030d050306100201090b0604021308190201080702030a0c080d0e06240a0b04060e06 69
    0x70b6003068142c255010581120b607800701d240e051821080c02116042500c40070100f400c01c085034000ba07200d12000100820318900000c1c040ca440c0c0158000c0303401031000402c210b11b0640e807030305100d95060741ca6000101c82580c28002401031081009184140c13901a80c40381c01c0000441100031241c0d251003403d490b0506003032400d000005481400d40d8a200c1921500c54031803100b0002d80c10000c44955068050500500c0380340d030300540c0a0450022a081290f000c10340c3c0c041c4d040e00381c6091059580194142c010500c0c11980680c000008500a6400707580580318204901340480c02c07910042d400078204404000840e50510380343d000f078a10f0710320076a1400b110aa1f1419039070f14101d817810b80e810b454a5003540346820740d031b00404941e0380190940059403809002ca02c0003040d098140c94002c00011021608070640101030388041c80c00500041151010300341608096017148804402d000304000c0c20741c48111038208100e00d0b404481ca85103032641424140b08050b9020080d04200c140c00c08418 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 696390521 1250 696389271 696389293
    0x30c0813080c1204170c0315070e0d0209130c050f01210e07060e04061d0a0c02031e0d0513030f110a02060703110c0102010209030d0302030615210105150306010e03 72
    0x38402000203245c0d08a0350000d801340c03403aa1a0a0010340b0b903146200340c0140c1148200444000713602940a83c0529040710b0000314100010720030b140304c0360041d4108680d0400c0040151b40c00303070b1a244075801550000e504507543c804214004c1c60b1404030500084907a150200f03401d88091120000600c0487c2c0482d212a804000c40e2a07c01c5d036901c40d0002074160b13581103500d402c062240354007500d5007030b58002448070441809529a040600003507800d40e50b41c20030580480c8207000381c40d00140580d40c22764070032400c5542330f680c90b0000300f15181d030030b4034200100d54a4440c000040908540c1038030360210041c0d88001c150b0301241c502d01002100d0241c104914010382d1110010481c19100e0f0721114900e03014042e085140c01c1040300c0041c10b41e0b204000c5200c02e5a800a080a001040d5241c056601e036a2200400c0e070030040c0c1183e0303070f00c42c44020421284294a0880b8403082000c0742d00034200c6a80d9507402c01c05032084e60320405034146810004502c43d940300340d010700001c0c0c2c4e014044031107080003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 696391771 1250 696390521 696390553
    0x12230d0f090b09060708150a060c15020a020307150905060708040804050402190f080405070b0703210905151308030a020c0a2102030f040b09030a06150303030c0813080c 74
    0x440700c0f0501500420104004541c0140101c2e0700980c60107500070252a00102240300701060703016200c207003c0da038080801003200310a8009074003c85040155207030600b0050217503a0b600b2041e011106c41d400d01f850101c01840510504003503e070854005d26803600c03403540130742e031411000d0003e8440700c404004c042440d480d103000810003080c0b10820147e1100c01004000c1000513101400d500f00051041440041a4001160000e03101c0d0944141e603a03106514050700c954100e451241e4800c00030f640385900c1c01c645036004c1b440e13140c00345054a403400c802e04040220344038212004500b040f03042e01c80c94003150150010b982c0c402c441c404c0040c504000c400b8403070311744a40700d80103c8480c1300348483e00c08900d5000b00c296003100c0c2d00d40015414569400070070b822038000c60040080181021590a00b5a0350802c0f00c82e4945800000c100510000c0318090112640b941c04240c01090070710105044042c0320702d0f0520700c00c245c88405139a00e00419641c020040e40322a0813000d2510a2540400320408 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 696393021 1250 696391771 696391793
    0x9150e10170303040b0f040c030b1f0b041a040f060f0c050109060b0312071e030318080a200c0409060209120f010c0302090105160302030d02040312230d0f09 69
    0x1110800641d204d113030520703003104841c42c0101801ea007203181c90180400103c21300c4482c4180ca501c5020014107079114507c144004507204c2a4031260090407c0005451086000510a03201d043c10782450455074020012228860b62040c180d51424441c410000307207105501c3d020980d00c8a141120007541151201800c0d1240d07084250f07851642c070411140390703180405c808031a018050304424200407040c0c0310217a0551282050913111641002154100b610179400f032003245070149203030fa07030701c0c44141420a025000311401601244170204101c3c407540710f041800641d5124840104040888a4140000b820040d41d044031169001e0045507141e80c1c400d2012250140c402000b400e00d41c4440c1c107400c0c2940c40b02d4042c40189841080320300607a9a102e4201c3e03034602802d032000f20080289142c220701d54420660380340d100d68408103001c070070045065054031281200d50360790480c0e5105560f6940030b80f4081845010300c1c200400c008100000650061400981d10100c0007540304465114020121 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 696394271 1250 696393021 696393059
    0x6011e120507121b020a0b09120412110102060f1303030e01060b091807170411030a1110210b030f0d020109021315050d02190311030709150e10 63
    0x150810820140c034000f00e1150001400c0c92500401004507598400b0f51107070076061001d410f10074140002204c0f1001009801c0e42240003070354050359540e03914000400d011741460100e41151069800c01119071000070b0890054506841801f403e85958070040e0745000400c000714180b43c2c9940d40c6a0840b4000c0c030403c001000c580124550703c007005402c2181240070081c20b410500408424029655441401071200354401040d00c8855103c40c1401070501c00b440130308561501c84c808040b41004039540e03445408074003d5810221100c101901600c40464a800a58072544200c04a0f00d2984c11034020f4810442c02034259407006008002c906c0c03d00c00c096040c0302c090713034560400c0c1045003000c6594043c4011002c408000280001070781104107005441894800d1384035090041c1035680d151140100c1390b40d28007001442994030701d08101103031072181446119020325040014050110701410002000c03540c40d003041d00d0700380720b803604000001a1140414a1441c41d0100388003e94441801040c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 696395521 1250 696394271 696394277
    0x10509120c163b060105070c09020409060e0708070807182c010b0c100506061c05010503060c07050606040908070c030606081b01050a0e060903070f1d06011e120507 72
    0x680a01d03140c500c8481d80c0484560350b01c58140d000074002c6041603c9a030004001d1810503958603613814050f492041c0342d0400c0000f240b00080015484499902c8041218114412001156100b035025510098101c0d003600101d0560030010394510301ca00c0310386220441800c000031481e81c41d11079080d00d0710307051a1006814035540748030382c1c43c103e1a10403441c01080303682000c80c40c0004000b40b2503100d07910a04000e801a440f0004114165141c0081c3c42d94058186100c22240d00d01c02035060190001b0b2103924080d0213490042508400008201d0b902c413a0490000d1001d0344034802444001c000030001a00e41e5803062112000007810030104a00850140038003141007820a43c4040c2000040e10000103d00440300140b4802d91b044000e856081a00d8142004450049001700703a00d845044c0c19554540210400400c2c056045600041aa4088646585803004940b0b0342c194103142a1445800f18004000b14010f09845c400003180c00e01d045c2c601f010103000324408a90a849050f10f108001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 696396771 1250 696395521 696395549
    0xf1b0c0c040f0c0210020f0418090b16090509090c090403080f22030e0f12010213090501030812040f020d03080403110607211b020601030311010509120c16 68
    0x481c1c50140140d8007403124241e410044403200d5180655640034000c0d0a0a0007600401d51240707000d49602507030001c01c01110700c0c1c0e9050008011074001024404021100714075480003042e82d880c0551000ca00c06011078a07016510742c10801007001242004140341200c0c4602030001d40583c81e400d6806010302d21903160300a0701c1c103041241d2891450001c120503500c01081041e0304164128a070081e0b006500341c107246100c4604c500115041500c101e843c107170041580103001c0c0900c0c0055009101c0c172188e1850b41d61015413900480f41c1911402e1001030f021a80900c900c080940840380e866401502c90b858420381d020940d8046564071000a40550202c3c8035002004149500800310b20403000c4154041c1c0302504c0d00d00c4000d01815981500000007148104104801e40366650042d9500070b503848060300340fa040c9a500035540c540c04d0208500241c8800000303045003070140141802400c034580600303c0280d41c1000c0203403070b030072032180704d46240f00b00001c81640703840b68509500604960100258 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 696398021 1250 696396771 696396793
    0x2f070f1d01090207020f06030a090c0f06030b040902030709050619090911010203130905060609030304090b1207140f06090d030801140607050a020f0109081e0d050f030f1b0c 76
    0x142804140c1c009071042c1c0c0100202c07401683d96014110100c1400c6581c192a0b40761910710100419803001c006010410304140820110085500302088601a503130a001a240d41c40512043c1c03003c1c0c8200175019840890180300c3c144040d0040d036408007018054007041e00040d094042ca0440c2ea9001010050340d62942c18240320846c058510138802c00e000651800d90301d94441c042c00f84c5c00e48507a80f2180d950b00f000c1040c582e142001c03500d402c03100804582e00e850322900d10b0310052a990100c44c4c4549640c190400480c000460504204c80b200300d6484c403019403003028810455a04000c695000c282002071500596960342100f003950300907502e1070307034070340c180075403400315880c0300300501c1c030586080c0300150008100141140f400d943c1510103080002281c13005a40181c00c40d04900720b00d006805010500348000800c8807020240c4100715044000c41c0030055846208600401d16a64000c00028500041080c8644d4001400810251803030003407003080341d06034000340401310050f080202410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 696399271 1250 696398021 696398069
    0x40f021e0a120204140d06020d240807050114030a0207060e0c0f040203010f1415220b040b04052709010c030b120a02010810120309060f2f070f 63
    0x88060a03003428110301e410305021400700000c200702c401782d1007034802d085590300304407054041d2110034541e00c50a0045594442844440c40954201d2508001402400081c24680000c80808586040c3c455080c1c4510501c4188540e81c40140901c43c2c10ba02000f408002907200c0c80382c655401c086001502d0281e09140820607455164030f81d41d48218010b10041c4881d00000400204692062850a00350780347d01011034030020b5010300200c45d0000101d02c1105104c0140c4040d5400c0c4004060040b469454400041c02801940a4050724040c140803d21190910000b50750521102c001d0000842182d800011850902120001e40c203944a911445540d5014081c51091349404c541e415111a404241c103503940400a0f0042c2c10011144042a07441a150001c2005406011503d4050341640e0034058410b403650700c41c080008a040d40d80c203100c0741c4206001401192207083c00c885090460900021040350000000e039a405080340004030f890142c040c05000301643d403c0703c42e0b1180702c50011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 696400521 1250 696399271 696399287
    0x3090607020604110409020a0b0f12070f0834090f050a030f060b0d0c0b091804170d1118031e0705130b03100506090a0902030a02040f021e0a 62
    0x1150955020009000004d02c806804450440080e0380005000100703000256425540d58040d8800d034500040c810303030703e00c001c00040c80303600842074040415072a0150308a900b1040c010980303000500c200f0200c1d01041c0c40700c140010300c9510248000d080f91072501c040309204588075078070700402d0b4000010460000344103441c0c0c00402d0100d074401c00302c51844d21440034101c841c1c0e500034501d03980d071403400c207556a82c1440000c4d102d400c51055002c0c140c40d2a503c510710b51190908903c58050b40711100307404881c08000310311550f030050310751a43c0703c003480004107650084504085900d80f00e8100d0341a90792681c024080405a0f003900c20505e1201c103046c0350900880c40080c17107215030396041006107941c00007800c104540e816a94541260b01d10340c0c02400a1420300c604a81c1030150382940760a0649582140d400f4000403035054500d81c461030f2204c130803980c0c00080290503030461110203000d8a4240d11128401601d180090315080c200f038011142806068079124042c0808242c8d0301282d80c3c0311001c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 696401771 1250 696400521 696400531
    0x30c030c0e01020601170f031801030f09020303071103030936010305030f210108030d0629071b06090603140c1b0a06060f030209090d0509060c0f060a02030906 70
    0x8401c4194203403000035201c2105001d4400300e610405a2802e440c281000f000207803c00301029a070300c80c4c0c00036102c24411240700655034002410200e080400482d580b2441c008613600030011485d2a08940e90780780503030465070420354503000500110b80d040d244c014440b1050101c52103884003c444200d002d0181c0d0366510b006440401c0d1110051000803000021112214440f41409403113100e40c041c1f11000808407070403280c0b17108000c1c000068055000025207800c5052074000e000321350303c0b407442504000074841001c1e0100140301c00c61511002d00001055840d0041603900184142c8607a401c10040e640e5108000003180d10600700001c59040c4101400c00040c03180320421818606500441800754600c1040c08840900c40785c0c165002c01c100410b101540144103102c02540d13507520b05c1c0d50074040d21003640206981d100003684c400000c5884078841d5003e032155421304014005116460300305060003000c520460340440e1981904102403403142c2c48410f000b42c2d43c0e20381042803605001c000b0341 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 696402877 1106 696401771 696401777
    0x6141203160b19060e07030b01020a050c0d031718150115080601020a0b0a050601110610120203070b0c0d091512151a180303070b0109150312030c030c 66
    0x194170784540c03c01d4508004030210100107907149d55a14400800c1c0f9000503514032007514141031107100c05070007454201c49102204403681a140d20540c2d802004840701c203a450150746007000b190714014070585409015503d0100000e8521304916400b1081c003501800007800d07a4400c0041e43c4115400c03a0450401c0d09011100000900040e514180003904202d000e6840d003100142c5603001380192901900d105141070361404030300000c2c00c0b08036418080c80703c0018541e0b0348203000c4c127103071050200035003000304000303002038040201e030b502c04034040007419401202d603030300503001c162026031704400450200300d4104901503240780354100504600500f400034000381c1c45203015004101408004800d0031000008042d0b4a0003030800041000e01040018400b001c86904800d40c061a0030032050480c644a59489402d00c401401d041c00087d5125100100c0300d515004003160406582 = true := by decide +kernel

theorem cover : BRFrame.Cov 696223021 696402877 := by
  have h0 := BRFrame.cov_init 696223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 696223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 696223021 ≤ n) (h2 : n < 696402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
