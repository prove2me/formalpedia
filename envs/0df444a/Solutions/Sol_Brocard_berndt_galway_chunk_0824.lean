-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0824
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:00:00.159989+00:00
-- url     : https://prove2.me/submissions/4b7c6d6b-4efe-42bc-aa24-db101ed5629a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 148021582 ≤ n < 148201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 148022832 1250 148021582 148021613
    0xc0213110906030a060f06030e190201050f0c070b0d02070212010903021504110310061a070203150c041e0e0c07050606060903070b04090b011e14090d02060d050f0a09 73
    0x10318002010074502c1c2060780c045c00c010038040b001140580d480300700050280c808864072510501c2440b40c100320380c00d85106851030807941616014600000301c941078000340c01c114503542c50360040410020f4080301a83c001e000006210b6001a0303140407502c10402c80d140c100054080c00c0c1e02d0f20788000006a0001502285841754448107001e03a1f5031464880608000d49600540501030f04a01d182090f02c039030098800c1e180744405600b902034001040305114011040e019500d5417100b03444482d00041d000044d604400020b120b64030300b90701c07070000c4198130600070002004050340d8481040040340d800744241d0003100c2070038030f21714004907602c8555440343c016002c944212400150030345544d504008040007400003000c5140c9860f680e460801c014640f02160794045240407200c400f00010042c0c03840c50300c402c5a02c1d100300c1c11111501400d696085801300b03c0d0030251061000000d41d690601400408001d460089064907090144501744e4002a004c00704190401c040600021502c0f200401e00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 148024082 1250 148022832 148022839
    0x3050c03010e061309060c030504050c0d021f050702030703030503041506030f200307080f0c0102030703120203041e05010209211005060604091d07080d090b09030703120c02131109 79
    0x40c0103002c1d10700c02c000c103117061005054518202501c0050303501600550f10440c06401504d100216a20511070000309a80000794458030b00070f84000c04c00c01006810848501c94504141403440d5580424600300d5203402c02d5010800200800c0304000c135160061040d1001c5500038004689590b036a0200c50140c1c41d4000e200302025045103590280680082040d0b01005040799401e9a540361080c2c1c64960390301000c1d005000b40e42c0c1500300303540004111034840d83d0581e10b480512850107221402504040c000325107504090500001284a6070030f00c00c076090141d0001a600c6241e00200321400044803c0003070410703210b00300070501500225150880c40d2105c6004a0a90340d10720004180d8882c0d80c00c5000218a080400185000b11481404c0d0f007200800407508105d80700d2022585d61440c1c1e8003800001a8403410a0010501503806040300c1d113009001c03141c11588907580c40340c80c017040030303040c80000340d59010410a6152452400416020841c0101b0033880d03120780e400e07603521601004501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 148025332 1250 148024082 148024099
    0xa050706020a02010b090a0603050f0a02030d0f0509030105190b1807140c06010803070317060904030507050a0b15030d03020c07050111031e070c0e060d12030204090905010c03050c03010e06 83
    0x2000c60017034010017640040100f080b2001d10740781c000780e402010540820780f0a841140301c807007008280000e07802003050300240181f5200c0e100480445008040340c840104001080c403803c421a00d090080d18024940801d898901c0d942001a0004580526180c244245060380120402110a90055400890b41d2030401c41c0310000e1844461140b160f81e410031801d105241c000201c1440100161114501c00da0380c03494510303100d240e81d440c040801c1e141941c1c011401004240040d004034020114540300c1c3c81903460420703007030f00c80d4502203200303c80c00c1701c1101c1019400c21031850f080c000001040f00b01d080840c20514101140b42d641d0385103000f80303410700800c1c281200e8002c070100107a078500716800c0010b40b446100b8104402c01500300c2442110200b00c26503012800950311030720580308040140032481000700645403141580000d004c072009140d401c00012800e143c0c079010701036450340900c0c000f241c4907401e018024115000240600443d07001800180000c400010748240c10541c1168800c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 148026582 1250 148025332 148025347
    0x120c0308161710030c030f02030d08010b04090b130f05010f17060c030405010e070605090901050414062115010518060105030a0c020c0d0f0c050603150d050705030f0a060c050a05070602 81
    0x1c41d103030440e800262840303421704000000c02c0721207203245840510030380588610701e4038040b00780c1c2d183d84207000e0460302520510045c00300c84541e80c00f48840020007070034918110b07148100402142d2a00303140c40407182d12a801445003030250030000004040883c031000e2000284050503071220b6000d01804c00008001002c50f060100940005076411200070640d140d4999032240502160b1000c01881e019041003000000c03585814030428407032141030351100401d5500d2a04000070307000181c0c5010030120b450000b40350744801c2040128a85010300030a009a5410303e4100400c03020140c2c00481c00c412a44100502d69900c81e003a02d0b0801101e00b80401c010b41500e90a9050034003201003aa0000d8486924009000c04400c5101c03105024620b8140045d881d8800d000c03040c8021108000c0202104075400d10509081403aa1300080c000d0003a6400d050b03c60f03000908007800202c0c00032465206601a00a0045920070745410b0151070401d10700d02203c0700c1d0007610700e02810001800e956070104011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 148027832 1250 148026582 148026601
    0x309060601112109030102042306070c0b1c020a0507021e0a0e040303242d0b09030a020a03050a02130606020607031e0e0d030b010207180e0307120c03081617 69
    0x440b044d00c1c0083c001d54a40e601e0701c1a490b2400c2c0da40003c0303842e042212007100010f06180d000c9400c1c0f150880c604039036150070500d10b20903581c401d030414032800e244400444909010303440a01400282552856a0f0754568010810088968100030f0141c4144142024155035041403c00031696440202440d0f03540f01d04041e0001d0400c90701c412001000c01205521000742295100c040e41d03512a041000c0b000c502020030380e101b101040c950140e0020b003c00b40300c1070380799201070000280000d00b169100130595003c1409484550701c2264240c0c81400707a030046280c0030307110b01081881c1c8038040003403d103003010095035071070090404006d06580710b4090314004460650b0214030049042d00744410a0032248441c0d031410540180400a8540700c000c007850b6102003007200443c1c80c060101041080c00d0320307025004102e450100011844100805d40c001480100e501c0c10742d50103611180c0040010b0309020301b5000c802450510440c0c42003440418454001c400454942c1c608900324541d40c0e10724201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 148029082 1250 148027832 148027837
    0x140903030904090203160e011a0a08070302090406180c032405010305180105090a02101803060b0102070807030c05040b01050c0a0605100f080f010b010309030f080403090b0f03090606011121 83
    0x1c0c40600000c0020108401c00190f4201c1c3c100da41981190a4502004c00707270200078003403510303180c00003103001010810952180d006400e01400040c400242590350340c581c601841400d9400744200e644612201081710f406129040b140c5010307082580c240200c0e81030101c000030041c09500d051540d55000f050b613118001c22460b180868040c02003240c2d0070000005031382c4100344c04040b441a9400701410310501c0c40780e941485581503100340080c0c52402c594800002c1d0440b1055a030461151040000f45501c0c1003040f0401140140c21500449050000b804151200e03c19440c0c18001c04200072400c03103400055031802c003600b001c0c00103015250243e0080d5061140e52048503d05030184010400c10004102d502241030303084000c0100c1307a94400154281c4065940103404244003058040110740500e040d554021721910340320348a01d031540355000c1d007a04015034142c6c84400200821196440811403c1c0d003241d0242006902040314000341c981c2d4120f50307582c0030101c0d5050000100c100240109 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 148030332 1250 148029082 148029103
    0x70f05070c030b15041a0d1b060504031a01030c0501030504060e101508010501050108040206030a1404031e020114150d0b07080628060f0203070c15140903030904090203 74
    0x11a00d10580e40d040c00444200f040e5040c80300300a004400200301d10b030074441c002e00c0c0d1801207002c0802001a10070070038000164203054a4143c0d4403c2c001207540e4044a0020140c252a29150780361400c1d4200204050403100b022690303892010010b00c00710b050341c0b140c03408640003480c000c0741c0c5598515040000d40490003404840384102c0300608030a803401e403c100d0300c050038006105c44090ba280c04480c00d0301c0d1b0a1207402c0c0032510400209000d800c1100095610030840c100105104036150560950014226000d83c0056400040400b0031080055a1100c07012148024046c50f2019a0084203080024040191301400b01d9800002500c031165454200e40d0011064200f5107030040010344a00f1003110340b03174400c101c103208440f80302a241c0b00100e461129104549940350906c0e005503034208003074807100c00b5880107118210000b000c40d002000549406000240b860110000140800c8144940c03219018010300c402141034400205a680ea50011280460203000c2c41c00801d040c54580e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 148031582 1250 148030332 148030343
    0xf070303020c01110a11190201050702061b03070204060e060306181f050108010506100e010804020a031515080a08121e040b0105101704030e061611030f030a08070f0507 74
    0x180f045201c15081000380105c80110348500e581821118081078884890388184036150f04945881030265100b031001d01482803010f00040d10300081c4520b404d00301311407443c150fa12a44000f65050850a060291400402c0e159100054a0070708400203503c80d0001031085600c01c8000442048400003002100c011038401c806a03c0c008070303c1da00c1c2d940502400d0050381e49540c2040d02055903420402c06d80c04902c0e24943e11034140100074401122030002c09041668010180140480070501c4400300f505e41d41013010001488010080813445401c0765a803101c280d42d00503541c01c00205406008440d1301000205a01901c0c0e5240070144c0080c2084041c4511a0700341e400410080000d00d80001e0b040e550112104038855200e04030031100c41c2c00040300d00e415426414080340c0041d00407907003141d0312840106070f24204081044501021481208103aa010301d402c0c400c43d0f80d5040a004024000c8000e0018511304020309101400d00710019001904002560301c1e100c51031403159058a2000c2e5000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 148032832 1250 148031582 148031591
    0x1e0607080a020f0c03040305210a0302031314010c080f130201051b0106080a0605220b062215080a1a0a06080d03020903010507170106030b030a14070f08030703050f070303020c01 78
    0x134a1820b950b50041d02003141c580c401c02c10030307040d030107080340390300031401c454000c140e2030070290000440c041d410180c0f5a000d500300c1025182d001a542c6041c00d001b59929a000050300c05a42c00000c010140241c421030f10f8500140034800c600641c01400403440e50203007070143e60703454200f4075550407035107040104210f0b501c0c00002241014000c111066428000c060911650300c900301807130510440c80740141044c1965009101c002102024803a510800040410807648030a01e1440c404004091000c00519035a014408400c1303c5550341002801c4c64800a10f12400d4a5583c2030640c061000800502202c0f07030000744064549800c240c0c050150401541d00d2180400c20250103034010012140c469400d0034001100184109121080f54003030181c000481d03407034200240c006290000c149074150042d90040408100304400245041c0c0441006010035441c10303101c0c404170101c03500401c0039901304115100100b540300b0141c54424032200e607a5030356103a162509600034400c8214540155090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 148034082 1250 148032832 148032847
    0x7080909070f091d01150210060906051002060f0c03040507030f150b0d030f0f0306090e030c0f060c070b1503060405010f1817030606040b04030c06021e0607080a020f 73
    0x34100b41025242c0c8500c41120344507501014060440d40440c90212444001004074001ca0071020f0854511401510180144101900107031800780c0c00079400c06071078080070401400d01e00d00d61300390411540f0150459080601c1c101d91404009410540043d00c00700104007400301c2030240800031035000c222041740002600c0d004030091208880741101d81c1c6441d007801054142504a007010551682c0c85070751a00f054a001c0c1d46a4003e495038004055442c800030031030003031601c1b40c500302c1e0080c07400443d100c55aa0030031310f180440c1076400c0c4506030040000c1c00811440c007002c0d01d2100d035115001d02c1c41e030354a80c1000000301e0780820741c02c1d07418400d07181400240901984440044035807280c0910175200381c51000300003c00c95200c02082d4890074210381c103414103500b000e10382004000341980d19080e6200b14905460304a9003040c0d410040010041200513010070505160411080b11000308800880005da2120f20060084c814414440c00188010440e94112106001928406a102c904 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 148035332 1250 148034082 148034087
    0x8031012030f0906030e0309130609060902040e01140604090c051204120e0307180e010b0612090c1c06051503190b0f090705150702040c0507061805070b0708090907 72
    0x300707182c100892940a00030910a12070f0040c0d100920280000711f140403008002c0c040c0100039403810804c256500e10001c50364240a0007071000411403050b0241c2c90340d040101500c031b10700c01a401a0307039008841803040c9041d1190b0046d90300300c0f08000d900140c03007182c182d801d88191103000c0d4100c0810840d2810401084000030035035440c8249a541c5e008421905001e250b9504a14012000c81b55245140602012440e0308100c541210044c00810105124404a1010780041c40030404800051003000f01003541000314000c07144003101c05040e20300b601403000d40d070588050005480380b503c038000544868020301560102e41405011070f0070001317030075541d013000c000c02410448214101030082303507042038440300550040b01c1c2600604203083c50101008020b1859040c0540c0582c01440490050707030b1a0b11484c41110200d40355255940d007146800b000b103655500b05102d044030241d00700320215a0014520341515448007800e41d0318030850800810034007400549a601c0640e0078100180c141c3e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 148036582 1250 148035332 148035347
    0x1031e0204050a05150409050c06071e0f0b161d010203091801151107051c080307120506010302070f030e0105070503180f030a0f02060702060c100c0e1008040803101203 74
    0x84c85103010108190311031040000340c8907041170151035a0b1002e552840c1c0ad1400c2d40080c5985441902084102455414554018808940280c88401c442c0d1030348024020540182c913070003032849044207520328011001902109421440001c0d400c02d40328034031202e034000c00441d100706000400d00d5001850020121420075800d01070720b120b408400305544042c6016542c1101c00880d518041c1207524205801c0c0200c000c9a07065007440b044403c10500003007181c600c000d500940c05c0e65118840c80d108070300004203540d400340200d810103104020748000300e5518542e4285184c0d1500d4102d500e4141c00c070048680b806441c83c094114040024040c04240c0710709092604e0310400c0d980f000036200e0100400d502d45004090140c81711141c0300c449001468004000c04001d480145101e083c0038040301c9941c94400c983d012100d1090382c3e0460b8001030b44c1c11001c100c600c204225003510712501c82c840e00030100d89010308020104040413002c106400c9420407203402402e07a08a0021480c0d40c6402c0051444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 148037832 1250 148036582 148036591
    0x3100603120314060d060204030b090307050115080d080a0e0d030212011e06110312040506041703010602032a03030f100b03010e04030e01030b300106050901031e0204050a05 76
    0x540900d00801d03040c0e0290107400c2000b46500d8641010b43d4880b42404040c8804140440f8400d074200f00120014240e948001d0040c20301c00700441e20b03400a0b181107402c56183c03800f14100f0b91078026080044007030000c0e22014203242460710080586940131400080c0c10141407050300d0340240b210b403070080c540c154050921003401c600390a445980c0c4605010725814031000500b5204420b04040c4943c0d806141035401d0716941c403003101d14241c042d0300c12141c100425581100c0310380085042c0000d01c1480c01c40c04101840c5084298655458040040c0d81c078822010f06561420300001000b03112200e0880168013079000006a0b43e817403808079130030f0b41341000c21501c5c42000f8011041c042044412076060724180c40901500c0e0450340c030340762026100043d18100590405032555041901e41d245e00d20451201440c480a10842440760a6840345034250803d5010031a850480c04002039611402200d045030740080d08440c00c450003504040140c0d44a0380c010307402c94104010322002180310351000e0301c00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 148039082 1250 148037832 148037843
    0x30302070318090f2016030216030b0609060306071215030803040b190b01020304050904110307060f0201140907031e0501020a090512190605090106080a061a010804080d0207080903100603 82
    0x745814a415450b440c50b1060000e9491801403206060381b60024000401441c001d00403255201e444240c080d20603c00c507002261010201014010f0341d0604480840d0041001c40240001e442d041900805040d583d5400c90f03100c40e2a00701c0341d80c4582e10341c07214002940d0000d5416944c1d2a007410101141e032001d8650003a1184100c0b807061071310301d00c0d10440045420580c003451805243c101080400c2c00081c0c010f60b2034000701501504c0c641d500300700da10000d001c0c40e00d40e8031440c20b103074001070b08580d5034070140c1002e0700035001008440b400100e42982a01e82c055802d000f50341118001d10022151000700404541c030010b40f0f81b081d20742000e141d00803100200c403180d0454400119494640750204060301d0301c0c2c1c030010407100024001c2d07080326078410005400080c02560f1005041d15001c10604140c604541c1d07501c1e41620704a54a51002107200c023030034a5012400c107542d6011641c800c1c9885100d2003580030501008001e044012a101184000c044451250322009044001d05051108486 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 148040332 1250 148039082 148039091
    0xa0b0601050406080f0c0d0e060a29130b061308120a08160216030804050906040203010b180a09060b0a020d0e0f010e0f0913050708010b0904030302070318090f 70
    0x1840d0712410486065800968442c83d55403030f41a0180d00e1a5000341c42d41003944014050400000860320076402c812400307100034010b41c1002400c4008482c0c158440c90200401041519101886003090000290b03064826100880d1203c00c84401482c8c88c1104941c00b81d80021300b0152516101a4801690130300c5007964940c00031110304095078802e40c1210380c00704504e41c0000c3c5607082040c020940301d600030f00680e540c121103081025440c074002e070011242c14001041c03c4c025420103101c41ca500c000c0540d0111728650400303182c94501e0003003125030080f40b503640060351b0303030b503112402c21b58001c001262041c41303515240d0b81200c60541041000200501c01c9506030081240300d802148840900541000c1c00080900b00450341c040f0314290590f00031402c00042c04d03890b1a04142c0612601118071007803a01c0169251003410003240303901c8100141e05207201300d1850b65640150b10340260b41801e0069550000c1e180c140c4010107500d070101141c10300b036000004d010b2865000580c00c1c800c588070030003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 148041582 1250 148040332 148040341
    0x30405060105030307120c0c05100306140402040303020a08030a020d0c090315060e0c0901030e0708012301060203090906130f15050a150333062c19170a0b 68
    0x1580ca008059025014680b09150306d1202030051103442100d0f405029481c1d9119101d82c0810008500185010002030f904ca8042000b460b20091740e1170184c4c409c0b58190320305032031030720f00a59410f40f051010f04510000000305030741090960445e480d84850400034400d1b00c400c4580a03100d500e90744030590306200c4c51024005c80718502e110344000e84200b84100301d5280c4500401c21203c0d001030107500e060541e074895000c51aa0100110320007800b03008004541240721008102520100e01c0046001c10400c41c010f010700c1c8d40101c00d0ba044202c09030b4260800b40d44100008040c650714040301e808a43c600850141d802d07121390018883e0980c61040301580940e80d0040c40401c1c000351040051610b049404107a101d4481d0300080c0e158180b454400ae4500d4a01084000031481002210407807500050108005c503080031900e00c3d4420841c983d0004400d10303440450000d1840750520380325400c541034608205584a08420140c100815450b4012242c55152030352048103941c1a03600446040005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 148042832 1250 148041582 148041589
    0x5190c0305220c0306020d02070506130c0b040609090207060603020d05070504050606070201021504111008010608010902030c09010c03020f0a0f020f060403051005070e061207031505010c020607060603060e03030405060105 97
    0x380c0558440e90f100007841c95500d4410080d040b2042d9075500e184c0800102010440c100605800b60744602c0c81010301303c00d42e00e04204410401c2e4800400e81ca41808108800303901300c00b441301241c6102e08050b0303032180c1c00d04e0a0b40081c03109800095102038411540313810301c040000c1820075198156010041500c407402005200c0c01594030090040c0e0010454442000d9005061a04079205e03005e1030306074110701d50020b080d4a00e5a1610000220340400402c0ac4c035a1120f05d079801000c0e201c4085296040810201e501c51240d035943d90f05100226024008140c0f0030003400e00407489642c10390b04030540c0f5150000c088030311024140e2185030f0000150b02549000b02c200c3e01100d5004004104802d07000c0706090142c00000d1040042c815606408016038850800410f60440000d4800c078051429600240481303c041902c5800d41d4500300c410f10550342c0124000c070410350115403290301c968691411002610a07900010b01c0c00707040418000582c41c0000245009521810588450b681c9a0051 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 148044082 1250 148042832 148042891
    0x9100903030b0a0602031827041406070315120c030b070f09080c01020601120519030c05011409060601030213090e030403140d0504120311010e0601090b15040905190c0305 75
    0x2d031482c00085c10850102d4038180c41d180780004c014240c5058032451031040306900074411103094846018420381030ad0924001e00666034041c241e070908202e8200031a0410350654004d006c0d40904101c003421142c00d20801d800b20034001c42d4070a00c0002540380548000b03001441c05120b00000ca01d4800c004551180e0200d608410404180d0003800141c0c0381c20580300480440704810f64182c00703803c00014a503000001c111401a020f902d42c803005501500d400b038212000042101d0858070b20106200c06208049040c0ea0850024603000d40c43d19480300348014100c1c810350010310500d260051403410141c02101410490b40030740544501d101d003030450036494001c109003010006408000c00c0c045640042841403042d4068903003140d001452060751130840b241515222203583c08000100142170840c000d80b20a90415208205000107030303d41c02c00c0704e0150340125102540c03550005811134050394100ca82c40c0204220900071201c16100c0500100400d403000d100902c4642482c14442505c01d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 148045332 1250 148044082 148044097
    0x10603110906060f0403050105010501120c02100b0a080616080702030f030103020d0c030b13020307090b0603040204020334090f08100b03010f150513090302060f09100903030b0a060203 81
    0x284841450008400c101d00007400800d0035034030000900080150308100e202800140d4419000040c0d00e5050000143c0004221880c00b4000c6040101103c0392030350118481280702104440441c80c41d43d83c13070000d05a0781440e0043c003818842c40e0100315403140101140c06128855448848441e200e101040342c5a01c5105a81005032008100400060400700324802403076004030f21201c9000c2d142d944400c80090241c9441c3d100c60099003604040d1f140c1071003800000c2081003405c101010081000c41c219003c0100064400c55020000170b4054a84000080c1c0380381500d402d61800041d81c40a1075030640c607210040000481c440070119024612443da070f4261f0b0a603000800c1c00100c00840381028240d429100d84d015500c4242c03044030f5021901801102080412580001601b440c060103201042415a80c90003410143c01c0d0780401c0c3c0124035144c010000141034202d90b501e01100364503010f80000161030f8586041d40450500d94182d001c0c15030342c201150301504441d40c80004990f03a000e100c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 148046582 1250 148045332 148045343
    0x70201090c1712030702030c1506030d0305040609020a06050d1a01050d021e0a020f06090a0b04021207150507060b12030f1c0603050106031703011d0601051303140f010603 75
    0x1040c442041226800010b000c4108201e03000b2121005840c84250015a02071025a0010840070b500078820300c00401c0d0701d540303103d83c00101c0ca002c0d0002591000405880703001e05a0780d1021a041c401c03603400003107403550050000c2e02c015503504c0c40101039501072800c0d0303001c280c41d000810b2804d191308058143c4c1002e05948880c140071000e4810300003544568082140c42044020300e8500c618004090040e1020300c1e0040c0c40400d110a4645003003060040c018482038001c14a01000a46504a01500079030103440c031000c026000d06071a4903100d03054000d405290480f100d1911451340c094014886a445000c082c008201e664007406210903940072105010740003840620640300e043c5019000308020484000049503500380c2200450303d1641080d02c0b01d945801007402070000d40460800c900c0c988602c1680303150701d0000e11403490100140d6008101c000300012a026038412401c2d06c0b038800b00200860f80356603503850034051a008600401c001400f84100c48094124184100b50407660400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 148047832 1250 148046582 148046603
    0xb01030b341b02090c0a031d06070c03090803220e07120c0c0b0903030a0c02060c0a21050f010303030b272802031f0b09040b060405060a05030f07020109 67
    0x101c0207031510751100020011402592141c030740540c0d105032281d401150b0303410300c082c2d03241000013004003030311204500d419140c0c002d10750b40500700f000010300660000c0903180001241066107401c075186846030340000301da4030010030000d000c0c0390001c00e0005013030716000d04407660580da0482da54405100b15881c80200d04c940303440a1141589800980c3c2d81e0190b8a0a003005440940d551180030206130303505c41c143e600110422040600c2440f6925a085160004003410300d4a003d00b0811032050307150f1182000582c2a0a80c1c501c079502940e0504070088040900c82c03441c1610a44284800900c801c2d00080e01f03190000189080007024000100c520a00f200f0b2400b0700356200800f5008090710346072035806403000c03041d006040860104000290824090f0b580e042803800c80001c44884100c06100f41d01281c01000140d5002c0200c5d4070660082d81c001c82c040d21544c00059007801607a2140d41c01040000e840240f90394810700840c815070b08410710640f1500d621030102d00700c5041c000f006020700b03a072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 148049082 1250 148047832 148047931
    0x2060105011b02010c0b060301020c0f240c0403080f04050d0609050706030203070e0603090c031c0e0f06180a0b04080313090b0a0b0309100f05070e10200a0b01030b 72
    0x3c40e1b018030350155001e00054a040c41c3c400c82d0501d130401c1d01c003848115800102481d8011141c40011101d20700b801e100c0b5200c54141036400d04680c4c1700380c0c400144041d0300040d00d01811082441075400801c402001840044c1c1142000d001070306461404541900402c0004242540607100744d90044103140d8801440100030818481c8a903c00380084009100b4681c640e582035404101c1d1010424800d04e104803142d19070381d4080c00c4810000c0752240314500a07584000d9079280c210070f071107070b481034800042810b00300c010218145440c26004a40080300014000c03560060000050015000303c46100c4015940d512141d001c072030700b1480e0346a00000200b41040000018006990000b440c00d06440010010801d00b20071240032015500e41552600204002c403070b00010740420300503081e07030300c500c43c00c1c141c9000401004c05410400100121740100c050102010170107500c4191340002048801c0d42c4a09025200740d00c229144401e0b104089400400044100d11101281d080603a07081f07020f244 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 148050332 1250 148049082 148049093
    0x130e06070c05011103071e0207030201020d0305182508030301030f020105031b041e0501020105090d0f020a0209100504050601020f0a081804090c03060509010603030c08130803030702060105011b02010c 88
    0x2801c42a1025921018000075080d00240103502902d410307101e481640c80740f0502d03000721026100102d0190742100c6d008201603600411001003058441c40c00003410395440d107240280d4070b6403840c918038a1084100b0301602c00141a081000c0c0c0200004564441c0ea90f410201c0e920f00c401d000080c0710132564030241c401540540f000d19003150a0030302c1400038407001d82d98002e094002c0c4e8001c480381040c520001900c103025003500800303403000384020b021520b0120000382d0358911a00b44042000032504441c04c3c00e51003808440800381c0c0c0281403409500f03003806401188040c0c0d0080c1442189810041aa03540c000518000f20003402c0010f01540b0545450b0341015420a49003280360b0090140300645c50741d1a03100d0101035501c02e01c9920001410344c00c120080340c0008083e00e00740d17850043c1c28008030741c100c2d650300d24045d40f2a034442e0f911000e0300412020070480d42d1101c0f45901c00030061180558020400d2816601c003a80d81001211250310b804455a00c1108081d01080001081e6404100e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 148051582 1250 148050332 148050347
    0xb01050403060c02150408070204061401050702190506131502060402100e19120b010603021c02030c090301181203020322050c19050a0515091909060b09130e0607 71
    0x11101c1c0162203807215503182c00c031305c0c2c090111000c80716040c0003e000b900310701d030a205110242111000006c170002d00200060891302c541c49010784541b044130403070461600c814089402402c0d002c1d03d903a441703241d041d114071501d0a86010320764a10085032200c05860748006081c0388038130780040100c03031400c00d202d00030b4030800300b95003407947c00c02541c000c040c0c084000e4011813001000302e44910b50441c0401e0030300150b80681030b08100c0c02c06004002c105148041c04102403030909448000583c3c0743c8034003a00310014810301103950b406500700344505080d8010260201c403030502607000001054080781c012006ca110445403052084100d419200416620b1070010000500c640c04440300c1c2450040083e10340202c80032510561174244000380101d00340789111100909007038071340d05038000000507842024040c2200c1240a08001e0580c102850315820000e80240550703d270030060315454901b00145a40490490707400342c03440c03048848120364940b11b881490f2140001402d1552101c440858866 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 148052832 1250 148051582 148051601
    0x51603030e06040308070e0108060a1710090606050307150906030b2707020717030304020402070807060f0c0e010f0c02060309032101080c06040609031b0b0309060405060603010b0105040306 83
    0x25030768442040c000c400c00c1081c2e50007140039841d12102842c20060040c801c004004d101e904104a00061050548460003150241c500c6040c240d05401c0c40c4903a218035103030b01d2000e00409503080c001a00f09111850340642d0549000b9003c3d1550183c9404400303403e00d900d000b0100005507811401c00016100c1d030300500700000b008103039001c4680700e040750011444c4584102c1c06124084000d102210b41c040141c8002040e9034443c01c50791100708202680c49000082c40a4041c0c1e40010354401044003650440381129070040080210070150039010380108082500c4401240e160201076000b503024138078180f10b030034195450205107011607090052756080944844010720080c4104180010000b1207041c19400100007111550714000d4001d10b0028551460b80c010801040180080ba9100c1c051800742e0350000301c203284000306d80b400500d013080c003940513801003e0048240b084403a800305030b1501480c0074508a0380541c035920700b050300302c0c2c14145949011030700804c003c2000403215000765812 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 148054082 1250 148052832 148052837
    0x3b070302040305062e030c0b0a0203071704030308060d020306161202070f0210080f0f040305070b0c070204060906080304060315030203060708090f010b0105040902070c0513020c06060907051603 85
    0x1025540d0743d910b440c003641500c4a00702190700300501c40d030510f246006400000f00c00b5030800c01d05031540c0ca070800c2c480c404d1702030b05001501c001200c04941e402042200d03103941d44a01c4031400506544074103c0321b90458002200080e00c07100114046180610802100640040140c1141e490300d001041e03088104041c4041031080d003440e0722415801e039101a1140314001c0c1c680383c2e10380d445841000000908001c0350f4090258250600101034601e912080d403140c1c01c1d03020454a40c42d5410242c03603074080d55100a2146040404005e0400c2150b0003821009109503800d021031034503503503917200742c90040c00740300215402072000b013050b0340c03083c6c01400c100120f40528042a584a030042814124112082c0f07001c1000c09040c480440004c0200c1c00030110041d00070400c0070394241c0000d002d80301d03500c1008074054011480c20103000d40300308484c00500c002809645010341648129000c0c4d0403600503210035020349000650241007040c105031080007507640360b80c9400040703119a05070350840d0505404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 148055332 1250 148054082 148054087
    0x2091810030c090b01110d1e0e06040906081e100b04062616060c030c0317150109080109050a08030c1e09040b011e0f020f010203103b070302 62
    0x851540d00402c005000c8100c00030840008110000d48400403a41400100b41d00010590000750741c040e040200c0e05c035a001c0c41444040c0d401d1401c0b600841d5800315254810030004c0c0014402103141d01c2441164220400d60340c0500c0c000d0a6076240418900c0720352016040840d00b030990b004580d0200c040c5040003800082c1075521500703401b0348100d0b914000c400c02d0260b070304d15229101d401c1164146e03064141300407101190600c08000c1c41044052402024002c505200008250082070186503003107e4a02e2010749240480000504545607021a800710783c112a002c00c20210600560a01c103420000410b10b480d001d0342d03200c80c01e90004141001d640024001c00c408240000c6455040ca90254400cad6140c0031050708020403a29001001c40c103003e1005401c485002c0c2850f85a0f000c40e000d07007006010803400c10f5050341058214035003207020354800020001c0c5410402c02403015500c0506005400c2c07843c240c1e405070450000c10f40540e54090f04840e00b01c4c00310001e1391540d800242854090b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 148056582 1250 148055332 148055339
    0x21309090c0801060b0309030708070212030a020d080711071a07050706080105040b040203040f020d0312060e0f0c040f17030d1a180106120b0414040b07030605030102091810 76
    0x112003803124115000e49600a0801200d90700b4028107000d4221044120300d036040c40c001c516541d10807c100201699070102c1c00b50103540d55115851143d034409015a40d848021590080d106d540c1401c0304008502440007145826224800e0890344281000052080f03901782a401d0b640e100341c154030a00340e00720802010000030014007100d401021140c5031000c1c5541400208400c0d03d4250341290b0103584103004100220303241c4403100c1c0e03400382c05a44642d4542c0042c20110ba541c0c6a03100309003045402d01d040003a41c2c1d0044c0d444240b0410810b40c0d50704558a44000c0042c05105074810300d81c80801c0000140104403445468005201415088030710740340014622f4015201c15100c0c6240b805070700d40d405100c07030070580c40d814018964010380445960501002526049450004103d03c558901c0b0304045912207900800d50300031041d20f0070074a89014544000312050407a401000242407440014440c101402699035078080209590070110b501000a40c040f0001440804001d00e69003002 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 148057832 1250 148056582 148056599
    0x1507080a020d030b150306060a27030605060301020301120813030507090f140106091a04050d05010b01120504080403060207060f05161d1503040206190201060501031406030703060213 80
    0x103002950154020348041285000081d0445904074a4503000b008404440800b01e0f8910084a40c001c408440503034940f02108000c42e11090075805448040c00036503100300120100c0503580007142e00c51320b01409565585010325090340004e10420910303980340302110000401441c042d0003181c00d0101c021807065501d0b1152403600c2c2542c1d104407441603454014014202c00740c007480041251150928556503d020300c018000742c014072543d03075100707110021403c0c8000660100c0d1b0090400400d2210001e5490a240d0700804100100b07502240c04a61202e0700d02c600ea0041501c110740000b0a2410189503403610342c040c1d80001801c07107400b695a810741610b1141032180724013540e1001c3d0900020041d00c0f01c05040e044002c00c00d03164007040700290004a0b500c0500744003221a00d6811262651078a20200f5102c1c05070783c501030516003483c07091131034181d415032040048950990301440318060856500014a40c2a00c0894164200100c10f1012580d503400030f0a00c0d208105044490b10781e0b41414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 148059082 1250 148057832 148057837
    0x9010f09080703112401180c020c0609120f0105150d120302030406180302060906010f0b030112020f03100b09010b1206010e030c0a060201050f06010509030709150b0705030c0d031a150708 82
    0x1105030042c00d0005004903078280d444969a010107d0b400c002d40b848000c0081e5413401c0c5090014460100050801e0054844010461088550001312002100c0003000503000c8e10084841c40030002080c2d4681d10945086180d14800380e070080d01c20110038140301d0048000c0e60006200352002d907201d19a106900c160b60602039007507070113079018000909101550a0402806a0002c08519100310041c8100242c0004070303030455005034000c00c1d0209503480420950400d4051483d410b00580c3d5240103808810b8001060701c07581121590700c581c0e200c0046890f0741c007401c0c440f102d0302c03000100004e60a50040b292000940c0c00113003210000280a00050b1740701e10681c01c49030060b5103800500849200101c10b00d50003240c2401c02e5810706220002090b40d502d42e81c07140c40301803a10b56017581e501007003029100002d40100c01c0c0269480c0d0301824429941e620445030b4080a00c00c6020664070203120b07209100040c2c51907081540c803c040ca60030004514405000742028420130402100040c4a0100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 148060332 1250 148059082 148059133
    0x8030405100c0e0f12210a030c0c0c17010e1902011e08040f03140d0b01020c0405040b0612120d060305060705191d0d05010509010f0908070311 63
    0x30310000314480303540425079500c901208244844140d501d030850383e90740a4200c5511003919141e59003442001c48034546004071803900c0e0740070541340c00c1500f07191454000704061f000c26203050200c40d03100340d800c4409800d08000500b030541088001e1011440401c080721010034518004070382c4800d00c85219003803450240070165008594000f100440d40c00c032a080129041080c400c1a807210407100140115100400081c142248412007008143c051455920f030100210a84c81d2107c800c0180c0200800300b85160501510079034610715450320b03090094600c9030340d0100d403081c07080e1a450280002c2503083c07040001c85016400b00e950860b5200700c00f03455103200e01171001c20740c1d82c59401c01d80d05040000d81000e0400204012802000110360707440352429146280103003000124400185444003810b104981c03060720384280310144801500043d0040c0d103880c0c001c100c5204001d07000c904454103030704010b1a200341070000c070000c070f80100321f50703104d140308401074441000500d451404c402c1d04010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 148061582 1250 148060332 148060343
    0x606071502030a0e060c0a0c1b0b030109060801050714130816140102032502010c0b13050705010207030c09050402030a150504050c04110306090709180f0c0e0a060c060603080304 78
    0x1c20000002e4403070207003044481591020308030346d05001480e10124460110500b0500c1070200d8010108818070030202c402d644011401030100341c44140340620b5500a100f0907020a0030701201107040b010600c2164000c02083c0ca81220880f1492005040398100144440350300810307103000507100d201800019101000c01c0c8504501900f40b621400200421944030790455205012981124580d503007104040303000c042c42040c030b03000c0901c0101c40404549000074120444d00052040c22600584c02c09442072241081e82c1d1001d44540c0122303038130001440090807400342002c040107039004503030080b90041c2c006000e41e01c4000070354542210205549405800362503441e8200310900c8070a00c13880c1090700084405203e40003c11942c03543d01d000c09050b451141d5404000302c0c1c0c43d20300a2806400a09854a5500d28405c900410703600401b8400002c00e082410700000e014072911417070120300a10700c002c14681720541082001c03116114030206c1100e5140e039809021001c2421b0201030745c03140380b054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 148062832 1250 148061582 148061587
    0x51518300606100306050901090504051006030305070b01060f050403032003030711060601170f0a0b040507090f0e07051c0e1209040f09050d0e0d0605090f0f0607020c06030606071502 80
    0x50101058003c44007104040c94001c05001654407550340d141107603205540402c450300e441c1001801c00c02000c00110842d0315040c000020075420034050403065016646081480e030345ca690a13124010080000e60006070204021307c0007a01500d4403000a01c003441c8440d1000c03584072040340ca10741c019501400452103203004010306143c100122a88043c003843c114956882600742030400001c003034076901c8007514241c0024880c1e0401e0344a900601d0340100148520306000502400d0307400135003da4680b40940450104100c80e02c001c48601442c15503480d0391400050010000c899100c104121240366110110320026400401141041c0e078880c48142d5611200e82d41004100d843d0a10780002160516003500003080700400e83c41c80819550404000c0c0301e4032200012204600042d0080890b03162a060007141000060b8604103403445038112030400c160100c400340c3d00c2e4000c5603c0750045c0e00082e58201542000030107540c00c020064001401c001c040d0391505256200381c0c040c402820b602 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 148064082 1250 148062832 148062841
    0x11070303020f07061110020f07021008090c04020c0a140a15050f0129090301020f0c010e06010b250f080a030e071409040b04030c0f05070515183006 65
    0x520030080200a030341170030110200307901e0a41c0d0712680384540f0b400c0400d9000c50035040f80c2803030f01c00b103825455009025080441800354045c245045c20348c0e0800841c42018414081d80c1003520031228040000d0700148900c034070315940e840007402c000c11400ca5500881c00300100042c0301c02c0704c98100b01c01e44140400c0714608910a80d800c0041640119100c10a0814230b04c2015064090503201840105c00b1581e100d508102090280c03050000700314001c0c0c40000e07040c0380c411043d4021840c000d01101661103e90781c6010306503040c050b16081200303511942100c1001ca030301218010844611801c40030b5401081a212403400c2c0d00301d803078004007080c0c4a0001c0768810009000c000d0240683c10400c0544081c8440814044000144020124a0888003081c1814010401c5540003a03001e0701201201a292400380e466800700c0c4074203405402c80780c5040e40d038110028281e0b880694040c0d180000700860004000c41c816102d601043c10310300c100310710440d440d02e10940a040b0102400281882d050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 148065332 1250 148064082 148064113
    0x15020903161202042a09090e01140f072a0b0108071206020309030d02221a0a030f0b041d0c04020309060610030225060f0e070504020a1107030302 64
    0x411040e10140704000d00003409040807200046440c540c05840c0003480c00d0100034007070308002c2c80c1d40e01113064510704c00e030290a1552040100c070544800810034404071041100305402d03181140103140c0c2d1641050005174003040726601c0640d0100c02031a004407101c0440b40e4501d010764a143d0070120030701a80110301d00388803006c41a00c1c01412007c0041081d0341c50101c1f2221050340c2400014421900000440c501d132004005a40c0f02d1040c946045584c0c0701c1c492002d0798040c601641102c2e09204c41d1500043e040340010f240e1005032314158003075140507440d403400c0300107000c001e00c0802245e5903241502490b441d10300c00c482620340d214903503103040c0c0402140940b0f040c801a600074070031030041041110003040442d42540028090f1014110008160b40580190140104ca6a22615110b59442030008065140144503018a40410540034012140000d450000a00039102d070300c1440200101d04003a8014004007a0710b1800803466001074042c14244041c503030040d40140c0c00b01e40d04507500403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 148066582 1250 148065332 148065343
    0x120c040609091b0b0306040e0a1401020a02060703020301030807150f1109010e120c040c0917070608010602210a050f030f0a0b0108041a0709090c02104515020903 71
    0x40a00c1088540e0f00d14188030b1800d90711005105034061500d485940c101240c1c05c02020b24926400350201c070315081d2603501c581c000d4001c10344030b10042c800c1c0401300e030440307001e8800c5a06903500425002c1c5404141c1c1c03100c0c4c0b00300b0f6090407a10b04040d0f0f00c080805c42c0701c10903c02e0911071000d0b00c840c15912010b00b40018142080c4641c058811910004103d001304270000c0c81d03280e411021b65021845507070080080e5a444c10b0382d48035141c42001d9015002030400c0106080007030391119210b403d0643d880d500200e940d180b0310f10840c40983c20340d401103880b0640c0e40c400340049810320714140d468102c4d80b481500f10358205541d1407004c1141001484052007482c00340c0c5101a0081c68408500d00d4030361107046035511031b500700510090040010403002e601c2200150003a01242c00248040300d26080025131f1180fa9041c500500c40c500100140207070741c10485007420030010f0b40b01407116070041c00c0240682d0f40d214540d011702d00080e640780000850000d000c0d0700c03c080402c1c005071a601408207142c20007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 148067832 1250 148066582 148066613
    0x40c050d1e11090d230f01020405010221071704050303040305010b031902030d27170708010e330c041e051c0501271401060b030105120c04060909 64
    0x9510a2010020300d4413091070702c0142c940c00c0300c0f000c5120b4441001c0c0c522480c540040d0b440c0c2d2802002c60480030010150010000c41700c00ba0300b290b0000c1c921190503404212000441c1c002c10078200880404a090080710b680042102460320b4505655a000a45198026841221980d440b82c0c810f020b2860140580025203031100007902924405d540040d85441034801c0c5003041c49401d003000440409100220f2043d21601c241d2071103450788502914515a05e070340000540352182c80c0c40810074400c10b008289007035481300d004080c94022b0400500148040302c814861000c4240c40103451a080560120300070200c895049503900d0a100c4010070b00089145034003240441e0f500100940d80710800360101150584080c55164640391420314050407801143d00c0d507588000c10050f010095110200c600507102c0e82c0d20b80b0300901032030851801d84155204a003012501400104094203081d14402c8002500e01c00f52000c41200800041c2101c0d05500b140003084d0340e907540c0f074007084616036013400007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 148069082 1250 148067832 148067861
    0x8060903070302031605120304140606011106010504180f06150b12190b030d02030406030b0123031003080c0604060f09050a0809040f06080f0114010f05040c050d1e 72
    0x90900c50b0301c0182d580c2c8180100408074001c40400b000034040240714054041000f40005a6203040600b003400002d000e09521561354010720f40030500c55801200d07889407030200d440c0508180d80c61f00c01007000a102040a500c0c490843c003401c2400101018101d210262159500080c0101101c505d5005040f0640010310301013420055240c200c00e21501c4c1c180d100b61b0700240007030303444080b01d40d02c006043c1091025400d807140c07070b00304208541c0100107441583d0980c0c0c0c0c10001c40c103002c0300440300003c0e1004030030784000002c1012000454058000c541c4491001128040d603683c0f0365034030165510040c8201c2c0c26821041c14401004002c0c0251040c9019801e000d10135540c250b11515120340c80300c9030041480c0c40c005010301154603160865030307050f00484001c01440d903891300115103c0700003800d82500d6528041c6801aa815000c0300e00781030f17501000d04125458101020b100040440301c506200f0310070b00340075a0000840070700403443c3c03c440c01c0081a40c44205901107078242d030030f1092141007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 148070332 1250 148069082 148069087
    0x20f0d020c030a090b04060c11040e01020705280804030605180717060a0203151201110c03030a0e19030509010c0c032306090c01120b0406030305030f0105010903120809070b1308060903 81
    0x6171a413080c01d90203015089148270315460940d20005d0003d0480c810900490750020840b54280623000c9034040a014445441c59480351600e140305410302d13041c2c0c0008260503001d1209201294565009907403009075044a01804104e04003440d01d02100c0e580314003012101d03c002640030380c2d4240b06554000c003d001007903046050904102c403241550580031070042d8003038100100405002d401005500800380b882d1562040044201a1603074070480d120100c04c0c0c18441207601001c8002548824003d04241c01034034051103a074200e4107548a40070040c10401c3c0610040e000c11803481c0c400d40151700c11150b50f1072000d0003c0c003000c0e4030031103c9010b460b250009020000c0d03022001c52814151513091070138080481041d4444030042601d0002680c000e0b180c04000300425411400960003182510f14414141e07aa0304011950201d043c00b000348a030000b5030b030600038a4000d40074960032401c01c0d405c1c1d40c0050342700c541da0040380e0400300f03601c196051554010401c0c520244801c54200044002451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 148071582 1250 148070332 148070339
    0x60e0306062107090507050a0318020f1309020a090603030816020d120608030d0915090203030a050705010b0310021809041a04080408030c01020909160c0204020f0d020c030a090b04 79
    0x101d8006458021002c803030805402c0004824080c041c0801400b0100b4040115040940b0000c1480d0440d40409020a00c0d040b11021081c0141c0750300361134198014014078807030703041c8014445603485024105412948500c4c0c4180160746008200014100c00780000492618500b00107100c2c00c8007814400c80700b0041d15016995981c003003003c4504180ba402c0000c0003d02403540d0000600559002c545d40780404103140300c08a0f904d41000d080e240c09420900300000da078640f41345c02c5841c0da88000307515500402c644c0340824000c0e800383c80c0300c50060300002440707403007800860305090340e000c3c01e07800081e400641040803407800c1090801e001019904840d1038940f0341e0780c407903401d803074020001d4079050144009000c11a2420441d4040c1980030281c82d00c3da0044844217020307411410405200e0340600000444c404109031400c0c20003007850341e80045041464007400004c1d4403100910040c10410480d0286200c001d00003080780c0d01d0034400031350f0707101d16581e4010a0b4015030b8000b1230b4852010030081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 148072832 1250 148071582 148071589
    0x603060f060c030909040516060503010b0324041b031104030201020a0f080c07080d021c1209050705060a080604060f06020d271e080105071d2107060e030606 69
    0x642429030203440c81940c0b105032080301c51031406002105540044008204020084d020800c0000407440c050b034040c502d9260139068403540400d0141a444400600014440006010110010050001d41001034131b0303e080100f0260b0320010415001c040781958a040a150715200d811440040d00320000e00307107829a80003d480c0e800c1820003a0082040700c1a00c0c050003003a100301c03014609098100c45070296204441a06e60b4501e0400e4070242c09460800380c55013550300b0342c4010f9441e180d0350b10540d0300c01d86107901c40100312015080e102d902c40c0078000304007a12008003c0c0450640b0340c4440c2c80c03d280640c104400d81c0d8040d0041402519011000c200c256000288c010049a1600b441c1c1542c0c00c8003038401500e00ea41c00541102a0140907000698070b443c04100c03080c0c04075110003040420740301c0403403a00b070382c90549003e40041d51407000f8070340300740b1010014000c1c040020050340c400d4043e0001540319040060101c0c1d03664201a104008158000c040021022400d4000c1c0c0601c0c034059001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 148074082 1250 148072832 148072849
    0x70504060f03050411033304020d02090a0905070b0711030d02030702060f12070c0303150807121e03021e190b090102190306080c010207030b01090c0207030501140f06060306 76
    0xa40091540303980c04135080240110480702c6084014088030202c8200341c5a110340444240040044c0e24180c0080c040c4075050814403600c100d4014000c1190800580c2c00d0044541000b070855041c140c1d5041c1400020f2000d000203801040000e415986541050504080f086d5910070307114400d601604410403400d0300441a0703115103030106c50b01c039250901d83d019014980b0800688114111003281000340190300418881e01d858040e03034040041d541030300701064081e103003800b4240d500e900c111020420306c60f8003c10240c4091142407680b0b486451a00c5400b20a42162011005a0020045000c880000308114070814490400902c03c00c1614201c9400c3c46a990314003500b600c00c04000250440001d4044a1402810340d01040140c0c141802c001e00a10690244c0d9055000305800e4032140c1d80700003034003800d5075001048200303280d00c0c0c1041040103000380010034096015400000020610a10800035219000b104545107031030101103a028620001340128810a000d006002894844208 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 148075332 1250 148074082 148074107
    0x60103020a05070c09060306050a0e06040b0603010b030a080a080c0f0316031b0c0b0108070b030a020304170a0201141308070f060204050402041e06030c020a030f20011407050406 78
    0x80041e5220303004602110b0038450840301801100b8000c4002800c3c110b2680150212409800100000d494a160b81c805a0b165000b201c00650720280c08076000c00c489501e416080000140000b481ca00c804002c20f0030600c000c40c0039542410042444d0030f05a4021642c40c0d07100301c1030f4881c1480e05900712858140c84c00054020344548860b511003102c0e0902a50058210124103800c035030401101d590010f00c2e40b64036100480c0c50220329000020741c4034000900400307607402c4031100e81c00c40e51801c628400075000104252100d8620f90b44040400d50741d00010140140d56078008200702203001d142c1c4c0a001005010100484007055104000c00c0104082d100041d520016201e844c40f03850410101a001b00e400003940320344002000030345810b076404458000d1003ca40d68441d5203595600a4017150074103031001001d41c0080400c040080e2080c1041445c0038540d0401960340d00201c0b0045925410318403050110381c0d500e1001203854040310200381d6003c0b01c907140040ca828207240e00100314803903d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 148076582 1250 148075332 148075337
    0x3a020109023d12020309010905153702030108030a090e070816020f01020c01020c0f0106032103140c0405011b2f04090b0402090c09060901120213140a0603090b0601 72
    0x10700680e0b051003500303081801d0048500030f40d1a0b04004003142d00030891147d0460302c40c820b420455080d070300c0019a0701c0c03180e09407203540000c8824403111707075250100c84030b64079031800e809040320303250855148040d41c041e0100a004541f1005801c00241ca100e00c01d0300a40d060100707079001c0041207540100010b900182c50003064804200001d01a440d009040f0310341c031019400460341280084055020b481c44020800480f038100001d540590300701d4003035010107040110340070707a401c0413107007040b0800080c1351051500250000400d891010034507070681e09002103071000201009a03603071210f9071a1130307000040309480300803520b0b07641e400300c194103000f19a04089045e10b00d200780a200359040c036a9000302404c00e000b08400c44c5000783e030342c0078110703412481815541c01103440f040c141e106582007610082c000d1031800b100e100040da9449026202040c0882d004c1056010318022001d0707020040c28070700c0c0c4a07403110b54203000700681070585402002c1054034006038840071800618409400480a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 148077832 1250 148076582 148076689
    0x150504090614010b0c2406010e1c03051b0118140f0a06060f0e070504062f010b010807140d050903040509010b040906173a02010902 58
    0x34541040a411001100b000b4032001800008011403400e00600d481c400c200c1c1a94002c0720b5030a10407010701c000000903003210f80000c0000300c07a94012025260f10150040200216070f9501084048162000000700c0c002440413807054101600700c1c10014a60301282d009002c09140c0c7c000c00480234804c0d04000c3d1000f41c2c9100300001c0d80702c0038486101051021002e0305c80396082d0b42800c01c085d20043c425040c1c040c6406400203084010a104036026052656a441c41c0074078000c001c8800080c0d2011047c11328040404c10010034040c500e200b80310481c841c1c0049040c034800b4001401c0e6000051190050002c008060302d07070701684070308541d084451014006401e441c1c0c89016461400b030342c2c02464200070314100110b000141e2802800484142907002c3c00070b10745410144094410012041c85681c0c8560203000d000f02d014001100000743c845d8201d4000d803003c20400b0038144000701c02c0d2001d40d641d027011109504101c8900701c41070700039040c2181d086014202d213401e43c01c0d03c3c0000c05041e0707080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 148079082 1250 148077832 148077851
    0x501030f03031109060408061503010e030f07080d06080d08060303090a1e08060f01080c221e0204060f0909060e071d03030a09050f0312030105010309030507020604060503061201150504 81
    0x3c081d81c0783c0c81c8018040b9070712640c851036032554a00050b06d03000c2d9010042c11001c0340034075050184a0304c25510401075401c110390700204803203a4000c1501100d2081051248003801821440359100904010000380490091008040d21035000030706024081c3d08108904905a11440403da080b1290550034070446602c0c0032601002c00c800390000b038007138000c0000340944d00c075405074028140c450000c160380b00d148842c010442d030020300521144440e03170329010014048500d81e000740da002c004091501d1740b03a040503100408903400307500100c0c0443d11402500c07405a500c04882c001800003041d08005072820324100321801c41d030003041c07181000b0116044084103c1d04c224850785441c0301130200c07600c5031015003000c1c1c41002240101c038090020300803000494500000d21000d00001c6c41c1840d0b1640e402c0038011000b07007081c2d0006030244901040024010f031a18401000104034681d1a00c0c0c880c10302d0410410540140404800142c6c10000054200c4100c0b44603c030403240115800204a140c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 148080332 1250 148079082 148079111
    0x1061107080102030106050301051c0302060a0905011805030c0c01051c2d2003060a1509030507030b0901060f1a0a0306050306040606091d070e04080403050d0c060f0501030f0303 78
    0xc981e0801070305940044000651a0f42182c0030318143d86040b00c81105409004603050090360b81c0a00c050010703032003034000c100000042c2e480032110900400002c28180c140043d2140404503c11f011282540001a0200803030b1052104050308142440c12601e0054100d00401c142803c003031614091a607501000c1002860740c02018810622280e41507030030b00380001088000b421000c400c1d0094550800e40c1140101010003128441d050041c180545a42404281000b02050303401c503d051111424001c00850000c1100000039803145514092a00d00a44210701303445d0154440101c503e8964800d002c0400300030003000b80d030010383c22029140c400d4602c0c200c01a000540c403140d090f0189400b400f0034420715410207404e8600c00c40050100141c890030080e0040c808000a50050b0400c24041c40b001c14075512854105005000d0302e414503850761201c1d400c04480ca07900a0108010610070300802030f490164004440800d6010812136245848009400c0e2101c21f0090405554050204a640 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 148081582 1250 148080332 148080343
    0xc030303040b070512100608060105042102040209060c0705180613050903090a060c0b060906060703030b061902070e010e100504151806060311031302060c010615080609070314010611 80
    0x801281d0034040b406c00e81e40b401400b103142e001311400035141c100010003d5018108030b5040365a0380011021014070013021088580c001c0a080340e02640800c200c2250f9507a6802074040368103440302500840d891b00b800c01a802000e1061070406174005010000c066035207509124000110010202e040c0ea24038103a0360a602c594046154410602c010118500b0360200c040b2566038407030340e0b0001d092345070441000307c008011100198050010002c0c800002d05ca900b2501d40d204025058504060200c50340c1d002403219040c1f040c006920001042006141880310705005080c1d09856401500b03104070300442101c601d004080c000da841d8901e00030030024009001c07008041c070307025071a00000a484484080c0450340701c3e800c0040e00f0480d640c0340f07006440701183e018100e10440500301c0c000380d82c01d103d01c1cad400012a03109039540c2e916000030000808113014000030070954600c803039482d210b010015422409082c91042502c3c04150030312410b0205e01d42c5042d078149082c00d87c691220b03040c1040c82c25 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 148082832 1250 148081582 148081597
    0x203060114042a3e06060906100e01020102040f03050102070b0718050d0f0b07111e03030103230a120f02030c0d11011d01020702010207052436120c030303040b0705 72
    0x182c0d040f040c01340c1e01003003132540075000740d60026551951a02020085000e1042c0c80040c1c1c8043c140707000c44280c0b406039450081125041c0005801e080c1c3d5000070400c24142a0702c02e0310340e41d400080e038404001c014400705600906a050038142c0034558006d60703102c0303c15400740f0303070203a103140240780103203d0000340d0b080742d4903031081191520340b515107801005104000419106441086600d823401c0c405002000940c01c000b40045007560310b1503c0e000c0350b4000d44503852154181c0c014004503c05002d2100d45209801001d424125925601004000303201c002401811500240447c8400741e00208000010568514010300441c0301c01c00c43e18010201002c0b400b041c3c503400c20110301d0b03012040d0042c24885000741c0079141665a1201070009000685003802c5000350258600c83d0b00e03070a554090400b40600500903a2140441c00850340d0441a446140ca202404a110010f25150502c0d4a54211920a001c2c10040718040040b942da800042c0004009281e00070001b0345c1c245c46501990f40c003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 148084082 1250 148082832 148082897
    0x50103080a0216031505060a1e1406090102100c0c1502040302180606121801020720040207081c0209040e03030f2406030a140705030708070503070801050415030203060114042a 77
    0x8200101020700042408ad2003480010b09649000c0a01442c00c401038400540701030700685502007600e41444010940c0d00e40c1070052004c0081c00001051002000036207000c009040166a6400c6004100c5e000c000805803480c1e000b00c3c00200821525230f0340561748000c40d4945c0a020a40300c040701002e40400040081c491584003042c0d00d01031003e0030419001058000c0d04411500c0450380922040e0302c81c1d0100030380308a10410007000701325694242000c640c401080010304080c105000242a07841c03c0c694109039034008000d1003440d0034219072040d040150203c4d200c2c0d0103050311410f01039401c40300103110310928000c400203070072001039000200e28500f0380100182034600080003a2064200792004c50020381481c00181102d405401200e01821b56a100c2c2d99180c0c5c45c1404110140c0380c0182c01c401c2c190414040040107803030400809004e05940c15111542208903000e22046458002512850880c0c030810b9489007103c030f070b5001d0321001d00ca1524178159002a41282d10201a21644840713 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 148085332 1250 148084082 148084109
    0x801060509010b0a2316020f0405040c030b070203040905010312120b010906120209040612140a0f080a02030d110306030f061009020c0a0f06090213090b0a1e050103080a0216031505060a 81
    0x4405100030103801510840708c0c100c0c0e01b00c1040030700c0201e80080768001c0c17407081c0b804d138240702164000ca007c075407052052048920346504d4400c1d940640d030b0280d00445101a42c0e03515040b5a58100e6890255410b03c03910421001c1e040c3e9000078400c0e500c0b4480d09091101540848064a0b0140c04940014401030810701c10b42c0c0d42d502001e130946105110031fa0b0200c00440f5099070141e00410301c2c0c00004c0e041452070341c0d82c00c09901e800001d98004000034095200400c18441e090b5218007407e13880525108045403603190000c140b5003014070540805207035400003020451565a24140141a00e040b51001601c0383d0714040b07003d1800c0c400040250a80c0400b900000030424280c0102910502c280d400e081d821440d50044016181408001040f5241361400121407070f019a0019403600900841130012428034007128040358420f800959a030f680000e59010b80315010800d0284402741c440c0d62070345191442d22000c480000b41441a20810307103600218180f60385201d5a00043c0265140104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 148086582 1250 148085332 148085347
    0xb0a0e0612150603101a19020a03020d0212030a050606220f0f030201360608010306050108030c0a03140409050a0b0a05040605030a03050d0908130801060509010b0a23 73
    0x8903074030701150845580c61041c20702200d10f0410f282600d0103841040c030407000540c10030800d0715420300300c4520122619400d00c445555548124110b42c480e50031600946084401418000d0514a014420400307650003035900e0f4240400e03080842e1303401607285000298ad80c0720080090410711540c1c1c0c3c4000c80c5502c003410030680e0000c400452040f200c91014000c0e8030f95032403144200001c054840070780410780c5603000900c6d4469840b00403110002040451107030480b212004040340b10b0903003001001411b01d60052003046803a00c61a070242601000850400610312407644d9112a000c03801010841c6558200b40c2d018034041c1681e0251401803401e0042c1d01c0c3c44000c1c0801032445803c075a2140b40600c2c2c0c005081d0070039202e100141c640140c00b81078555201e49054400c1c0c1c0c0544007080d5065611015000425100005020f07202d4003562526140b914003841242960480c3d0440e0384903000a100400c0b159031407408950b1900600c0c104010401201441c034a0082c400002c1c8021619001420705c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 148087832 1250 148086582 148086607
    0xf1809010e16030b2511060c04260f060109051e040c0605180901030501090c090b0d060509030c0a050c01020706050711060304240504110607020a0b0a0e06 68
    0x1610a0408000800c44818030716100c5540b141c25500990915481c0401407020990018002c2d0707204400380c44148460300c55807454080c40000c451030400041c4c050303180c500306082c14845150130407602045035042034200440004050f603080700c0681040000c0c410706403101014008441607054490540b52550707501c884a1000c0c0c181114600346540030315042d00c41001c14406031500480d00020b03c02c0245040c41d006442a52102000854030085c152400000340e440710f0005020314420000450701c200e591801607000525504484c9a041c01c0465600490b02d40c601840718543e0044804110354642101190031441100b09800450190300148414480000b40302c40c1c1f43c64080e82100d041d59a1264112014015040018203921210700040c00b50b260071000b41d0313041406a20380b50b40d144c062101e0b444010840140311461240c482f01040203100d404d034400145104143ca42ca86844a240d001030303001442801a610803aa012404104440c400d0706000d000c000301510095940b80601c148 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 148089082 1250 148087832 148087879
    0x60e0d06090f0b090d0801060509210d08060907020a0201120b03011b020f010204081b0301180b010302040606080f040b070212070510060b04030807080319020d0203070801050402030915060f 83
    0x241d0381843c3c0d0f50045008494000358542c5c2d48509940c4000e010703400c1c000c040302c440d4408201141c0c02400052280d01551103003e030b0814404412008003140c0c0301c01000540705080c010003281c824990301080000458010134241d10955092038030007048200c005004005081005100c0d416600e4030140341c08841c0e5160f422424410184c0032690849220b15280d0b00383d20590060244642191416144440d100240d900c1d2aa40090000c11668004c690708843c810500500381d44080d00700e03004005605003803181102401061030b00815034034160721055030a60001c0e000030491122800041d402608c20701908280e00740da821225900c4449040c901e558160a0350f0f400c4801d46424000202d03075886608031001c481e402a0107608103840751311001d13800d40004000d0402141c6898029400c0b4000e48001e064400400e14010786904250034000d081802c140c0105015034410030074011120000507500e03030300341500240ba0300701d175441c50049450318200206887c2c002d61207400041001007480300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 148090332 1250 148089082 148089113
    0x110a02010e011103070c0f1514160f081f0b0c0a02040f0608060402060309030c03031608070305010302060f070c030b100e070c030c032d05090a0e090304060e0d0609 72
    0x3d001c0e40d030400303003035400302d200030b494000105a1800e8000c00150b1380ca001d454945008414155001c04808546415a8401002c0c0034451050300104107551010b55504000307a0854501080203201610010306515806810200c0d81300250f0411003074043c9604c401009400b560342081e440d9402401402c1ea074940c44a0200d12540c2804042000c1d08a02c1c801c08085035000c400a2008e611644c082c0200c65002030985a5203010800202060940410045000d550501508403076107480c520000c0184102801c4030042500f01001000581e0f21001903d0072170004d6000142c0c0c480692804a400309080e510081c00050108100046a018000254104c50354074064541c82d550300714003110002d140401c01004035000048070004280700b001604000c40242070391150807501c2d8020705040441c0d07540030b00001070002a290a960900d0140340000f4213010324101c0443c02d014940303544900450158a04011079699501c0d501d543e01d0984c091003603004441004107815906214410001102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 148091582 1250 148090332 148090361
    0x81605030c0f160503011802060a09120507033311221a0a0c030e2206080708071d070e0901080102030618060d060504110402220605040e040f0204110a0201 68
    0xc3c001200e05041c0202207a0322040340c020181700c2c90039400c10610b500b01822800c1040100c01c800700c1e08070302074000c003046140114000d02c011455403420b850407401c1c1140c5000300d0810511510380e03040c0c0c80c000700c406642c4035a9000c5a01165880c800700c142c0510101c0d8002c5020b6481407128101443c4090f0058400c090320203140d4050b245045141881642751100000b140062100d0110b4400c1d40c04058004005140b00c420b1340c080c51944e00c046c1c0c500309450001650f6548204003801040110b0070050000c40702607e6410f24040b0101042c0c100480444518560b00c00042c00309803092044980c4e00c07000800600455849000e40741c000d4000700c896a005100103403a056009000c0b091080c45100300510304510b1040c0c07940c03000c000d007801410450300101c000048500031341e03a80c0040c140d4a003003894590311001c03d050103045048000d0b444a03060250810007030012010032040540d2141c0c01009540707610516102180003400034048903041d20a01087c86c410196045d00441d0381c580642 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 148092832 1250 148091582 148091623
    0x804050c030f150405030405040c0e03010b03120d0f0b030607090305010b0402030408040302061b030f0a0e06041a0309030c0d0909050601110d0f11010f06080609030304081605030c0f 80
    0x503400c1c10354410190250041079402100003546411040565036801407041c0c00341c3e410255100c021400752207088440e00080303404001d6020b1030b420244610050761000702c00070a110364500041020a02c1801442c0c20780c03984410204c0b4084400d608980c1d6203c038007604481080c9044913006100e41441d0004550325401c008040d01c051405000b524084d81e048203071140703018619420002290322404080035205030000440c075800005001400166031260403140d83c0f1080c402008044500320300100c0d20844042c001030000f030400c2100c00c00100307504c92060765070792200900d00341355000e41012182e06e40f0618451400440d40300c8207400c00c0700d42c603c0081c002034a9600054644242c007411404d92a405150120040d0f03214600502d00030089040007158524060b03411030958203c4215030744103d1300c03102c003000f40c484200241540140d80002440c00d6060aa403118160310503071841903207208a540b03e6405210302401205e200c1d8107484210b40343c0200c50442292551120341c1e508040c100013 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 148094082 1250 148092832 148092853
    0x1b09061101060b090d030309050723030a0503070b180601080d090501031a0415030804030503070b0f070e0d020105040b07110a0b04030c090c03020c0312150a0e15011e080405 76
    0x50007124142ca1003c40202e0404803e00306025510f50b80c008141e003096180c40a04000c160280020b00141c1400301c883c031120f4415071280c0c0d1500e0001801240a9404406c00304040745001c026900480d6000c404c240701ea458a6400400d0007914040e03c207540c0c01440d000080301c1c0c0c0e000880e14090105611582d251a90713900041d4115108089800c0d16402600310240e002c1c40c00382d100e400f4194802c110308110546a468041b00c64100750011074007503000040803800e210624180380e038070401c510014405441c08600040503501d8a076a030701d00503030081002c441160b0013101524003624404060684441c4d050920ba80c4130050400018001d080c032002c00301c0c80f0800a004c5a0035a50441d514800d00c510305041540103020500311201010b50a00100710b094205000610150344000c0000d04c29003407289152a10500c3c46074400d02c105008541040104952440745900001c44103c81140d2080d100050780d540300c2d003418501c001c0e090038402c4025036401c80b0695004a01410468100029 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 148095332 1250 148094082 148094117
    0x12022d180c070201031e0f0e15011d06030c120102030601080705091e030705100507170403020a03121101050108070e0f0702030f0d09020303030709180908031503011b0906 75
    0x54039540c81e0a041040550059400b0741c002200c240802d41d07640f9000003d0420315822070b00010010004140c0b02c46010002c02e03c10403211a501c2c0d901c844188265141c40e10007880042100c0d03003c6081d0070740d000002c415907001c2c0820214603502420300c001034035040701c07118007d50080b10014041030006021802c0389104030250707140e050f40038200c0b02c090b60015081c00b004c00510b00c01544d0501c501d0318003041c0c5894003400d1f43c01403540e03500d8560301d98446180801c0c0c0c0c6080c032000c44144180911040016a0300c000d44142100d4006821503400340001500300d603030860920111580e50b0800c400040e42c40c0c80002d130718049a0202845040c0c5442d50035490455207020b6510400580c018003001004a03104001030070481c0d00000001920891a804a41076401c100d03030b80804202400030410200c92841010342c8801e20400e0b0070440340703203155200e0802d030002a0420039a80b0344c0e11200d043d603840952003c403207400519440d00d01e00024100040c000e8103a405200001080110586507925 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 148096582 1250 148095332 148095379
    0x12020408122d0a030e0c0d030306080709110a1b060501150e06090607060b030304120c050f03030a0c0308060a030507120204140106140702010504091e0b03150112022d 73
    0x5000c03110785450106803c000700d010b004c081003c445180183c140542450350340c120b032140c040b0300c00c0d100440c000d0b150640041c00c01c01e003548981181410503031803d2004400030102c0307007140d041e404c10650340310a080940c40744004003072004040300e242c1400820445d40c0b540700928032280750381e200304002d0030400c00d001a5000d0802001e41002c03091161600040468102040c650000780460741816614002042c4510081c04140d5060206010601c040e0030608a0a1070300340c000d400961400440042c0100804180d082c0607007045a0307103010480c40e80d60b0300200d00045401404072410541c90302034020034101c007480100d214070302e030580e0b02000c8060341031014100c2d0980c0d2030b6071340c1c203515145510119902000c0c01f2810070908102c04a1a0f014038806d148070703c095108039007400010101210112006035020a00c00d91104402d1071200302d00250460660b58204082800d000e001c0c408914182030030b03640039046140c0c0300c06500c0c0c440c00e131100301c00704404106c0d241060740c513450700080d0040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 148097832 1250 148096582 148096657
    0xa0b0403020913020105120c0310061b0b070e04020c0309030106090509030304081c2405010203030c04050613050d03020a0b061507030c030e0418200d02011202040812 73
    0x442c1000200b01c80f0450701c0304040d903030040c10b00301d14048084140101e08581103070311000e001408800e00a4409001401c0b802901107410710140c0c1000501812301e1030640e48100510381401c07900042c492a218604c6011060400f5000f503443d140b0307180015481c1c0d0440c1c150903000350318165002403443c94502866000d820720a01075481c40c1c4030764079840340d15402034201c03228100c6070814003c0e6100ca1445802c1c28954a880300e016480c00e01159482220100d078080360440d030090060050344042003044504407034044070101d07607d40301c108460100c3c03003150f80510303405811001e04c00249a000f14840c00d10a1040707041700fa85a8407081000b40d00d54085821026440c4103202c004000f81c024051414054001d050251100f012a40018103840c408501c80030f00703e10300e0f00d018007085102e003400d4071100140b03031092002e155840003185081c0c4854502904001c03a811031075558103240d60441c1d01404050007600c0b0801d090b40c07456112f55100491061101982c9210310034000318800c0200d0300b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 148099082 1250 148097832 148097839
    0x3030318030c020105220b07050105060f0922020a172406040c050c120415090302090c07080f0a020706090501030207020f01081806090610060c080409020d060e04030207050a0b040302 80
    0x42e81d50011603950b00582c00c10b0003001e2600085c001d2081c1010020750081005641141d41c50340b440c40c001d0f00f03581f80905801d0046200c2041e503101e958070141003e81c03081610402c002000d00300c480d449010308a15101035001810b51b403011412404103159200400e804008030f40050003540410255030400c0c01c0c20303120105181000c2450381c5003d8005002d880c0c40c503d040d80c2040307800242c1d07505082041c00e0942092a00080c1041015000c40340b205203a18a800c0102000b40396801042c060031000b4030740814075600280c0340003003100c0e41090341c00014140719100c0d20b50050101c041d5450405016440108041110004040d80f2a00890301c0d80756019080c41c601070030740401590070300e5014204605100c028010f981c03400f8030800c6610311440d444030007400c1c54104400040c0400050340c0100081202038100c000104284004990071607003007a000580d00c000143c41c0300002c0c050b41d04903080b43c13000390f400e02061540c0011001c0984030108e030704803a01c40c0c1e11801c15602d40320f10f1000035003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 148100332 1250 148099082 148099097
    0x10906020607051b03120108010f0e0a02040f0e0307030f021504051b03010b04020f1308070e150613030f02030106090203061309020402120c07050106080307081c0e03130303031803 79
    0x42c00348100080c14080030507000d20400c543c02c1d2030a02c2c4c00e41c0c000d20f80c0c209040c580c840041000c0c40090123204108400b480d03003080000c08074013407903885650301c240190089440380a02850050a948100d0140c10803200b03403500d4103420f1030000c2030007000601c407800510948041c60304060003049a140120746c8a401440441e58001900d50170510001c030b22035065590306c0c00140d0544540c0010080b00e030302403071220755810411001110300c9000d034201c102d00d030380710540c10310480c59480075840c0c0214001c0300d801c049094103000130b0924412001c0142d030a2080c010000f082080c914421050700384200c0003440001d49401d2580203e01007100c949600100d5507031243c1300b41040341e100300d03040c46c00600050b00d450480100741c500024140d40c45450704800140380020f001080c4148000303800940051450004643c0b100e000e00c0c0a2010000c04115805600b6282081079070b000584809055090320b444001c000b26010640401e48001d802003803c042c80305a45089050110381c807194140c07194903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 148101582 1250 148100332 148100341
    0x13170606030c010c26040602030919060f12181a0718050f0103093008040503071707050601031203150e010b071e05030403150c120509010b060f0a0305060109060206 72
    0x50307041e902e6000c0c030309080c0d8420705c100b1900b541402400603120307907001143c0c2c4004002c140710150765103050302080d5407010541408566404021500501d1041c9030858030b103580009220300a0894203031075101d4810041080c030420400f41613101401d1118184e0038074582d5042c0781950030031018550300301c0e143c030140070500040c40d050445a82038241854006014641c59940902615140c204035030510030500e071450b04040070464448850b0f52514103010141890b680d26a41c0f03026140b03005024811200c1041d4001c1100c1c3c06450902d40c011040300c050756500d080c850380c0030aa40b4001c0e00001c0c00e007079200e0130303410b1441c40c5030007141c01100024a25a2820415000942001d0401c0781c1e407212441511510022103564044440c1c0a10003640e038840c074510b00a505a00b40c101c5c03040d034641c2002c405040c81500401e00030030a540c602d10108884c4c9d40c01d00d000d8014110005110350204011035401d251701148405080724042d551010041510380a006580c0c0d980a0321411005034000c2d400903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 148102832 1250 148101582 148101593
    0x40606031b0809010212090a020901060f08070c0206090d1101120902090105040e1617100c0c060b01020f070b09040c020105010810022101030b091011120c13170606030c010c 76
    0x11076100009800050601b811000d80d151a45010f03681c00c5500d500290710541589086031840780104010f0600300340076800207a018103811002040c10302071184042c2c41350155240c0008540102350300400321036501c442071500c2040d245103d6011360008a2240140000b10464800c1c500d40301d400500c1c03918160b04e08010400038103054460a100d40c040c042d40a801d038806108140007403c0c0c1a11850b5010480c40001881e2440c0402440c80242c20702c6964140c0341d4000500340c00440d000350000c18156070500040c0d2614100c0000001c00c0d118507080003c000c4940409030a003032008a505104102c400f10040303090700c90a0003004c041d03070001c103221080842683c1c02070144010604540300c0003640c10000c0990034030240c0c02529216001c07002c1140c2c0c407070705024054809207643e000700084054580915564000d024100b410794813600080742d0404c81070410b6031442c0509056038508140c640885001c040241800c004070341c0724442c00b042d51442c0220345948610340c1a55002c2c0d0084694451 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 148104082 1250 148102832 148102847
    0xe03120a02040305011401091b1b0f0804060f021005041a330f040603050309190801050a150602010507140f1204060501080708151f080109060605040606031b 69
    0x891a510380c0c02c000000010f00207015210300f05a00c1d029681441d03140050300004e8680320f0f030a190910440301182c0180d207400103c0d000d0701c42540c800862a6240070300d400c40d034551803428080c0580d100820b00045c1140e210021031122100755003070b10309500c510340c2d2810558000703079401004001410b80d480380b01590050600c0d440040205501002d07009165034010300703080d01003821030300340390105805100d09090001c0d844000302a18108101d82c9075445041c0c50740501c0511900c682d40610314100341d214402c4468000c0e00c0100020019800c4c4070b03900100038002c400801054600424000030301c0d078018824203104907200d850382e0415041f0012264420760145055412410061040000b14006e407008148134610859000840b035042c500c0c00d0740b800e00c2c1503200280a502410502c1c2000b11000b80039031300b00c0840700c100c180f050440408182c0050590300582d160358070f407078914014464103030884404c64900351408c01046403903a808500b40c2d003612011080c4242d510841042c0c9901c42d818 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 148105332 1250 148104082 148104091
    0x6020109110907050714060f01140a050103050907051915140403030309060603051e21090603040c05120307110406050102150403030f020c0109020a1d0a090c03060c08090d02010e0312 80
    0x74074500d040d00940d40c003081c00c085036221000a034000c7c0b04020040303201c041c2407030140c20300c1000040124400b00004214813828000c05040588400c085000e21004004007030142500605000c5140010005c0b04070201035881601e00b00c480d5501502c1c4058060404001e504074a952103074901400e684040c0c0c085d00c150941194090b9a41d413001010030700c10700a0b4080641812080c103115800b40e900186021001500c030f8260400003502440c440482d0001c031000440260780f0301c1c0e1603503101e04080c80c03803590561051790044201110061422004001071030b0142c41442c100d0982c4043c1790900040300d0160041601691001c0707030603100b59500d10005e030b0b0301501c24940890003184150010050b43c101c0c810701c040c96916540d0580c1103240024803500985110361180080c003080c0000c0350218031b00500f1002080d541c071a40d03002031104200d2144091500040c050262000c90f640007070000008440b0354046000381c940381072007240b041c0901031014040b03000a5040003000c007200c2e13518101c05070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 148106582 1250 148105332 148105337
    0xc0a0804080f131203020c01030e0703020103050907050901080a061505010e010804050f0102041202040e03250503090607080307020609160b0a050702031501051c170c100e0d0906020109110907 84
    0x40b441c8000300f60ba4000702c014092a400c110b800350030514001c4c1c44d1400c100e110034185400c1c141861100200004c0c04000ca80c3c09203000304054940844042c2040c0c400c3d00515003041110700007081805001a001c03074a144102c004000180c084400ea070b0f200d000724001c8a0024407200f8003031000f5032142141030740150054042e91150b152014015007207a01c04c2d07000c100c550701e55034105010f501c0c02e44101c841c1c80e03c00070041c51500b070b040c050010f141c01c4411410001015210300d01c2c03007840010020f4918484020304404ea5407031143c10000c103990011034110f0010303c03e03100080c90546001c1103100003440340c0c000030400740e8100341d005a40ea8000c00000f004204c03051100c800035035020420070201510601c01e4034100c1d41450103000c1124400201d2141d000e90004511300010380303510f01c2c25841d000304043e4540380d000709200182081007608008440606251140b911220081380031503440b0240c1c1c90310f0203116603644003a400d81c0d84140001d442101501007000603420440c104961003440c91 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 148107832 1250 148106582 148106587
    0x504050901181104060f1a070804030512030103150216060b030f031b0607020f0304060305040215071202010509010902031c020a05030301140f0406051f05090a030b040b0c0a0804080f 80
    0xb00102008400d0b0b60742c2070350000108006103603a41400e01c6102c000c1c0086500f203002e40f034180241c0c1075a2a0904171088480e10000421200340100c100a40b406554028180c5100120a0380600c1c80381e0000c2c041600c2d064035070022000250264401ca441a8160442800600b40261641801425222001d5030940941da0000354809818001000c81d46c12641c5030180002d50302380d80604d00310000305a00c09540c80700c81c00303101c1001c0010643c1e0441f03002e8500030600d41d4440c8042200c0c1e840c00f00c25904403e80c040745220401019104102d04140c0700d0b4000c002640c0e4034a0b905003030320140c42c1c01030341580040c09a10409400f10703071361203141c01c2c0c14011200010410781d14140f0310383c0241e00006c183c03000c01a1030380035490444030051076080100c4d8140290350501c40041c1041c0c61601e884845100d0747c0103200701d036900440a54000c100003d02c4804403541d03d00f05401000c0044408031500d2501c01c0010303180c824083c054034040c0300c0960310784240c0d07902d42d81d4110659003c89a81c0b005014103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 148109082 1250 148107832 148107851
    0x1b03140409021c050703110d0507021204060309120e0a0306050a060803070f11010503010b040603021b0123010902031e180d0e120d140702010c050a08091206100504050901 75
    0x1180018806010104802a1020b0000d81440300702c0c1d8002d80b03485c1c20182010b00101d509080300c429a421440d25450015407610313601000c2e4a001d5081e42c03c800701b03c8001c03d0000d24660107502410409009245c4ad0905a040041c2112600302800710b103584110510003e00103e15648d200343d910403048840016440e4070760000c4c0b40b03580c1122400b100d4900318074413894104402e062040603039500a0034510b0465040001841d0140280c1c0a090200740e8046510075682e1582d42d44100b545003424000c005100c3d4240b0488288601600b01d046003041e00c00c0000350803c91131080364800d041885000850a0408010540c04100580342c00501c7c00c1e50300303010100391814040001c20f07100c4d5454642e200e5446500307000728070950030a030002540044594807441070b001810412200c003a04000da41d5103d40b4401130300c030510701b818054000c1c401c079400d01040021803001011400c004880b003013030a1150a403000e80d1138000b25412104240500030400041c20315401407904441c0600c00440c060030f8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 148110332 1250 148109082 148109099
    0x3010b070c031520030c0a030f0b0907080a0b03070b19230301050108090316060b1201050a06061b0f111f0309060b1801030831151b031404 61
    0x10f414401c40c45140d888040280070260410800030701c0c10300c92400341c10b41c030f8003581c80e50150003958184070925403500c40c120b444034000c0e80010280d0000402901843c20b00780001080508121000007502c2c6c50710040310118580000d07503008a8a00344801d0780381c91080d004070207903081c2044025080c4030b030b040c005940500080354200a000c4041c1c8269880b03600d403900050480c04003030f112041c0754008028000005114100140d4413640000001c644540e0700004900c00480440401c0c449510b003105106140100e40c000600b00d0b140c1c3d65540c429085c1380001c801a43c1030021004103640d1802000400241840d4202c2c00c01030130050101c1440c03403030140c9003185903051030040b900207030391152008100a09482881d0016000791006440c1110841c0741c034507000010700014096040104070000302d48028440d2020115504e00e080b4601088045080300725101801890440192100d040128902c0303000154044e0301111003010145050f03403019a4040d40ca424a000e40c810104408500303580e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 148111582 1250 148110332 148110353
    0x30807030908030d020903010609021c0c020709090302100e030a05031609050604080d1713060e030d020c1e0111030a0506030a02090c180a0b0f0a120c0512180303010b070c03 76
    0x1307400348000d69a2500710301018211149a082800800d105000c40100c1031809600029440002c402c0040c0540c110401a490041070790b001d00b810a0508000408050f03020502103041a40e0a1061008140c40000c0e40e07100d01424500b440081c1040c00055048a07500020120b0781881c4d0410410301d44d00c601c0465083da03c40e410a0119500100800103800d921113941412080007000c03290942c20309854840c02c181118902400250b19150a1000040140111011450002c0e0b00315990440400c2e43e6813140c0d45043c01c80c40c02c46680c400700c41c0a180c1801000800c0d64001d00540c03031981c03100081001810050a0f00c0c0d00351242030324000040e16030071003403030140c0f80030030910b502c03807807410014162010400480c90040070300c840c0c200f000d142c0c14005c2e100034a2a0312100c544035600100200d500040070314030303860322074141414a2030a5401c030000f020030b41c0b18100c201c1b00b181e48003d001071503940d062100c80c01c41d80c001c0004015105000000e8041c0c83d110380d640901e01a601d032070303154840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 148112832 1250 148111582 148111597
    0x305060c0c1c02101a0603040606080f150105010f48050c040902060d060e04060b10080f070903051002030105101b020d1103060a090c0602070b030103080703090803 72
    0x5450000301c00110080c2003100600b00c00b02001810b1211100b048000c1d29004036400c2c20320200d03111a4104006500e905200b0440000984800c2e201e14040c01d1003006843c4502c200c1016004446d085503100728040758801d0307038041040040c04542d2805004540719611641d43d84200008400441d00309515a02c521019901e004807449048c400000d075521640c00344450918a80a226194000207001240505007031030b0441d400124800ba0f0300104030603120328105c840f2100e01e0b00030701184240c1519130041c001c50082c1c00800c1940c12200c14040da55110020f0000410020310006070700c031101200d4540d01c00c44034900405603642e2956004d2a0624034004000003e40101c0144500c2c24003820b0040a80d0540c58013031040681020342444800307890402038010310500401109000000300b01e00031001020741266050710b00100da103001080044012240700c5043c85001404a10008120b0165000100146d24607441c5a840d8045075210318422020710507410340000c0d0b015420300140800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 148114082 1250 148112832 148112851
    0x105220203070c020907050c1e010b03031207080609060319061b0c11031c1409060a030c08010f1a1809010f08010501080115030201050a0201060b04090f0e0703111009030506 76
    0x3d44920400101c040e000741080d08000b000e03c10404000d00028a4175003c1220030003469030384650301c503400d0240861005150705440b00049096105060300031181c81615140e49485141e180c03d020451a2102035802950550101c084002c414a5030f802c500d20603841003500050390f58620f0180c01804222510300004a26400c40751410301003100c01100341c4800413002703011141082040d1450a135038080c1d51038200300c03900b140c1e00c4201c1d00030800c17207182090052010345c690031003440090140c421500e0540008880750000500344a4121840b01950b04030781c3c88240481d181c91540385a90000c2d5061001d6400c450003071a0582c55101c503050203054049009003601d42800129800d4880680c06100c04e07a140c5140e0700c1d00c52095190b07600c1540d0342441d0407a5900c1911000b00d002d010640c0000090040004001542507225400741d1b8001c45182c00c244061010031007110740b10761113480003520803407280c1203d02d41c1e03150104081c10004501e0074140d106a8403074450500e060000c4505441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 148115332 1250 148114082 148114097
    0xf32030703110102070206041a07050307060506030d03060501020d030c0903020909060f070903120806011205010b13061803020d05120a051c090c0905090f010207050c090915010522020307 82
    0x525500908a82e4031201910081d8602005980401c445215600c1512101c0e01c40d200320760006900304c1c045600040d0030200f100d80350246400c1600017801e0540302e00d4070921440c01e00d031040c0b80c0203018200441d08160050103a40800c10016009814044000410861450300100043c6d9038101c51a0090440500030070003440c0103941541c5031007000d03084071b05128400c0e00c00c000141000442c0b16074045e503803030000c2c801e80300d000042e1051035030f2040441e85181040d00108030362400001500d442902401144400303503549001351490f030381b11020410070304511003007880942800383c0e60074029445401120340c103016031081000d440c0c116005d11800280005090200030720415185150721024003010086010660340390071800706035200744c09205031280c00007828120240b088a194622681c000d541c2c03040c01c1c4c03078002d13100d0b581c6507002842603803800d002c44e1491500141507007440b501421603e0b116401d02d400c100000131170900042d03a10070300401c90700343e48100340051402160b00c4e454611 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 148116582 1250 148115332 148115347
    0x306120307110301150b0a0c0f0b0a05150105070b010e0402210a06050c040b07060506120706050301050a211401060302060a1d04050903070803060d080304051011070f3203 75
    0x14251242c2c40301503502c8801c008406d000702080c90f0205c480320038042c02c1c03501080c691494800d503e0380540e50090054041c54040100f144041d4120602c00c00154001d0f448144080006440f20f00814201505900c0c2113401840885070009030b0030f8216000030b00e41d50580d9072801081c00300041180c010b0b501a0041d501031000c02050340030749500710640302c0c400c49c1001e0809a0510082c060100003030065521030703020804c2034490307000c0404441001c81c103a0b4034040d1200d0015026600c00e22031a4000c01a50100091440c801500070b003203201c0c1450039074800089611200c0400120f07280e1100071355a544400030051351440010b104a0b2001d4807101541d2205028240700c0001940b442c0b0b004508141c1084000c42d1b0110480d509554469070301a00d1751070312004a5a02c1c60024001000440001b060009003c400602500302a0120700f05001c41681c8564a10703443c0210303240203180c550820b50b01400105000406903c40b9204810402420280d0016402034000141c4110341e9400005140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 148117832 1250 148116582 148116589
    0x510061d1f0305010b1602061c1517010605180403020321180604050c0d05121b061515030a0f1508011404170702150307050a090e060a060302030612030711 68
    0x95005004030301c80c00c5c0c1094036440907881b408075110741c02880740d10001100852034801c0810000c04a62070003040000198820445031520358a001c0c100d03500307200440d00003910350140501002e0b15000751041068003a043c10149580c0e07006407088066000a215041e551903050703030b000f207a44003e0000660316043c0f140c0760031130641541c503070780185800100402000c0340d40011000b04065099032005945c10340f504125090580c0c20340c0e08002090b0019403244000b0b003042c50000592000420340e4040d07203030000d202000800b9402c11580001c1003119400c42484068091984030036007500201d81c0b401243d07a00011510086c120220207422040c00740b001c0c8009124200032412000038514a40c20541c0b90aa03541072010140100b20740005040710440d00d500d22101541002642070a8883c10841ea000e006504034407580380000391051800101c28144642e01405411301a0500494504000c4210041d500043c415500080880b1503c91040401c1004140460061604d81c10011003034041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 148119082 1250 148117832 148117841
    0x4110d091a0406050f25050a020c030106030b070306170601050906010e090f0a0c09050108061c0c030309030b1605030406050a0b030f15010602030301030201020706031e020d02070b09010510061d1f03 87
    0x390a0005e0005240c0e200d52a000481c1300000d071b00320b041c01501c640e80c46c0030880c508002d81d03142507059400c1807800000c200403082881d026069548050018548410000d40408000070003280c4980c0300f40e00420030343c2040501c0e184c101c80c061605074122404d00e40407502c002c0050342d403a12106108003c025403001144a402d212148901d00303001040d14000000b081c000010380010b218065160b160301083c500a0106a80294009514801c042e07507030030b018141801d03522090391426141800a80360340c0d49440741444502031074480303500795241d90325408010900285141001070b61984c1c1c4c1c2d9a2958200320140001d580100103080d88541d1906034807007000184e0041055500c117000500050ba00810746400f82c544904d80000e4242c088902030070382221045400051074800520000400131a80007000c1160203003500e00c0c1071341c0300d114005080301c1003100d04110300c0070300050600080b03214072404440b42c00c0300d00e40c00c030003122250001000c00c00a2a820820160b0b4020060945601b5005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 148120332 1250 148119082 148119091
    0xb0411010212031017010f32010303051605070315020903100501080a140304050613060e0a0e150a1706091b010f03020d1d0c04060504110d091a0406050f 67
    0x1022401c6040010103505121500e00585c2e100c4604045444000403003580b0000003d0000c2c442031203c2100300d4580c140d401c403402a000006ca062289101480b105008502c0c122985a84d5040c130304030a0351200700610240241c1201d4034010550b00102040ca580791046840d030445200680d118841020185801404c031140e19040341448010003882c80c0205150070b440380c1207000d0000046080c0425821481642c020540c807070008540140c0c00200c0e0075a503015213282d900d40c140002030410810054440c07034415100e1041c3c0010000350b03100942030940031814006086003644d25110040c5540300780c2c50f0500c07074070365a0081c010000d9aa1013040030b02c00341c801108807141c1c00e01d40580002d00b0141c040314210145034000806541d200c10550040104404507014010460061443d464541c51603c3c607052190b030910a000c40d043c2391178403031b1004909101500c5071912000007081d07009040c00140984800c3e80c0c41c00b00c0d42c1c0700122a441e06104a108400009040c6003000003544c1403c00030b003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 148121582 1250 148120332 148120363
    0x60e0a0e071409040f1a01050901060302030f07110705041107020301060611030a0e1c050d11030a02030403021005041d01030605130807020f12011505040605060a0801030f02010c0b04110102 83
    0x2041000342e6003500d05458400039003903402100669907801c040441e041c5151006042c0d00d840014001c0c03403c0e804450724161038045840c0d03134850740c2c0c07001c0480903800280c94109102010b800450344050240302048240f069040903250025079a0000800300c4030b41c107003412540a00040d23081d0840c5000e00c15034001e0400c506160046401007052642e41e4000d0065000c280104607103218640c0d0740d010140b20001c0440e440e8a035440207d032800700d03100c2c4102c030300050100720380c05001e03203c4501c040151200c52256500a41c101803031a0200505850441c3c04a81400810080403856060f6948400d40d00b101d8010311666035455032600c1d2045450040580d982c1e03288801c1000005a1144116120710360100d84890001c1500710004040101080c3c0c415215841c1189040c00450143d059000f161411103003004443c2d50b54092103518031548a4500c00614040c0c010300024a2003991361000b1030062510445c60010395407402c9510070243d406075002c4a40f040c40101c690781c10080c0c0c0320b02090b1300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 148122832 1250 148121582 148121593
    0x509070902040e070809011b11010c03061d15030a0516060804081204020f0301020c2803050a080a0207020402040b1224040f1e09021c050705040f0f060e0a0e 69
    0x303074103940c3d65403000d0410020080e1407030200790f1104094012000000568012003620405040050a103d00400c207101807035007422626010280248a02e501710395000c91681c445c8030b000303c5031903404030008040c00c4a440814500d52110b8500f0020280220310a0b4010319070701515214025001105038031027000c100c1d40d0b60402c00002c1440054940424110f0035051098030f42d480010b5881160160040c1c15600c041243c5403044d10024194815401520300c0002d2091110340c60700401a4000c4041c6c0400c4080150a419030f105440c032a900100c2140700500300003883c2c0c00a81a030303101d82d1119801d410301086551310308090b03c4c001a004541003401495940700243c00829559440e564180b00382d5481c034a40b100030f04d194103e036220642c01da43c110f00f0b802c8558164801001d1059081c0c8c042c6020f0079542d009045140d80ba106001c1d0040000c01781c0c40d10f48420017014000c01001c4062140e1286442c03806400f03d809400c0107016894002c030280d01c0c0c0003000030221107120441d4a1140e002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 148124082 1250 148122832 148122839
    0x1905070303110d0c08070807150203100b03010302090f220b010311060c15070504030f0b0703141009150909030306060e011403010302100c08040303020304081516120f0f050907090204 80
    0x2c0b03080390560990000c4907903298515400c0441f010f0160102c05064520710080340c40020040790700862081e0700031a4540301c1c050701c0e50201d1159010900009403c1100c5001154514072504032055015040e24030036000e600320b0341e09807120f1045806085400c00c48050050041001d12511110296419075020341055016080700d543c48201618112102d07038100c012401262244d802c860103503422640b00800b00ca064a02812070480440d0503900203440c1c030154402401201c0c0e8164000e00c002401c0c0c004150515020703800516803100d20814441904000040d080f115004d1001c12074026140003a580c1d180c650080c04120580500302c0c1040400f2542c2400e090760602501e064076010364441000010841082d1440c4000341300203407680c0300104002042540c000006c001340c1c0c00c03d0058880c441d48103c6110b00c010340c01c0d0707a00301c0c841c4400100d840b41140b20300c03580101c018160202007040f54004240004890711200a403c040f600c03a001c2000c803ca007000201c1c001d20340098118a01440c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 148125332 1250 148124082 148124087
    0x50a0b090408031b1e0408010509030901211407020a0b06091003080309010b040603141501050a03030815060a0216290c0c03031305090f0106120e1905070303110d 71
    0x100400e8801c1104c020f080c0e91200c2d40141060b41c40303080c0c5561a91a1556409070219590340040c4100455503080070001001d1070340200c10b03200901d4041c0c5400d002d002428052590701100d5104c12a0260740e501030080d42c0000c415003079405000310740c0107801e0f4031303209080198213580020a09802884004144042050303074482d2002180d4200c00b1282c2c07291030340c00006003d008107000c40c55002e41400808410b000b03c02c0e0140e0704003801201141e140c0e6040d6808404520000d205017640501508020000b007401844519400304c8080101c840c00c58081c000180303103802c042e14a0005910007454600c0c00b5030320300104d1002e0400c9000c20400c642c600c5a0840c0c0169000c3c902200040c1e0200c3e184000d08400c01c01c0800701800203056944582d000200b00303103410030500c111441020010042540301311820001416640540c0c1e85150390b880308070150000d814481c010022030f10444e07117601f54007a0b0601345800c440c2d2203000504171407440c5080050000c2003c1c191301c8640c0c0c00c134407004015180c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 148126582 1250 148125332 148125337
    0x12020c01080a0216050a080316081302090a02090409050f190c060e1f030213060c03020604061d060a0b040b0105040f060c08070614090106091e02030a1806050a0b090408 74
    0x140303064025a45084110f030021541c414804014200c6c401c100c40481004a4000a0361040d400e0010001031a503400c80104c641c00015a42c2004020050610401504086050b42e5011035440009444c1c400501e010a0458502d040e0540c3e00750020742040c061500b0501c04440307030810f20141180307100506d407698001d84100b0302c01c5009002c40840030380840d441e01e0390b02c2c0c402d803510003119001c034289051018019510030601c4665600c6011004180d4900807002d0040031a010b60044c01150f41d10740d0342e1030060043c4442c0754002c0e003c0032074030307166007404200003481000d01c8132011440b44858818401a03810502005050180610091010782d850b420142d00715038840ca0f000c2803140050400080c10321409002400c0710f0700b020a210032114144150358003440503000200036081c1e07500b0102c02110b209604802c070a90107102001d603400040d0700a1a00002c80f24030025010385525460354595020704000c0701c0d59a1203804000301c2a00a20520405610560300c1c8661460301d96902e2080d403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 148127832 1250 148126582 148126591
    0xf03020723010605060d06051903120e15040602010f050604020708030c0a0e040c03050615030c0f030613060e250e0910091e0608031206061b10020712020c0108 70
    0x8141c40011261101c09411401c01442c02400581c1d480d2501c0201801900150058900503045e01c0349034071241a06441403000c80e03070401b895217a0019480c0c42141c0c02c080c060300156101c0303003404014461039019070060008000310f4000103007951006141005461000f0441c5224500c1841400701107030980c1c0869038046c1050f62841e944d66800704003911141503a0820300e0300b09291910701030300960140c1c411130140c1c03011a201200c1131019189010903100071206086502c0080c0005840641001d0255802200083c000d0480d0f010141c50001101c46640c0300c491008980002d01007510f040c521200c40c10202030b001041e845007a8100034004404004640d40a0603000300060314000c2d5824200c406442d5007041804224607004000e21004588050040403d181060000da04200081154058007003c0c00004482d964130081010a030010640c0c1417500c10014040320005c3c40c10f110308241c002e9103600058503040c0c142081243c4070240803058040d9440070300215603d03a0468107441d8070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 148129082 1250 148127832 148127873
    0x8030d0b042309010204091b03050f061f02030c010203100f080304080604030804060b1201020409110313030503130b070914040b01080a020d020408060f090c010c0b0a021e190f030207 80
    0x503440f031010450080c4680d40c0900f224614100e03c1240d400303a130134050020030109641c28450b64582070200814a0030960310f5503072018030f01c03525910001c160326824017008100e0042c0c90410810340c4880d805c0ea4021900c0b0200d0307c02c4940288800d613020011a400381150034000e50800e800c18040c181c0e035080c0908042c0520803d00d0010b010010140c100f81e11050002d070200d81c0712949007100d18003075041406084030301810310284843c02031280040e280324202c1d09140945c02d01072a101980c0c2684041e1000e686e0141805c0b8050101c1c001d0001140950000c0c1d44c0c078801d685ca1f00b40039920080003c0b400c01e100c1e6040580a0410381c3e400020741e500440948001650ba0100c0ea41c1e400003889140c0c0f06481901603070003045a212454961148103014410684000c0411800112545060110003d01b80300c06440442ea400c0300a0b4094159040c0c031410610060740c1c410341c2c40c80540c100f20f40307486460faa40200d0078030503a0f002540817642492400c041d070500c115a6a00d488d9040e00d217070340c02c92 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 148130332 1250 148129082 148129151
    0x7260403080a0615090312140301030b04020103020c0a11090a0207030509040f063516060c11120a0203010c0801050d0818060f1b03041401050705150108030d0b04 71
    0x100d10714aa0702401c01851900b105610b01382407820044c202460798401610001428140d16040034055128920b000d40c010400c0d514503802d6603a200e6203807902504c2a0b0400d6420b21426074488070070044483c03024054a20070903403500c40c000300b0582d510b004bc11b1050183c014410708000a420006540300f41e00c0480700825030f03a084800c850001e000903409100d041081103000e1003064203010146001441042010417000c0380220000d40e107510714210b064520081c0181000b42c2e078405c0030450707256440741c041054841a803400003282114039811f603015a4201c200803104528003481940541040f5090403640c642c54800050924140c07443c01070a1694002443c4406140d00e000105006500070503e689541800007425250b81181e400340314581c2c90984420b0300d1500000954086131000c0901400100314040110b41d26085001c00711014801c94485070048009420814082e210400082da04d8080d00303064041916040c1800c42d0040380340140804420100c071011005100c0d403081e4031013 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 148131582 1250 148130332 148130341
    0xf0e0108061b0d051302040f060509090a11060a0302090406060503090f0f0c06161205090a0905010b18040b22150e070f09231008071205101802030726040308 69
    0xa800d48580070000d601c645041008c01c01609070383e0215040c0d0348261001d1202d5641c2481465442e400760390702034200f50150001000130300c0c001c4014000019545009824212140701286c00e403000f94002c6004288007008104501c0c4003084210203141c80035009010501e0b48940040d20380c0c038000500c500880300065094080e4900c460004c2041d54000146902031030035903c000c001d0380180c0b1005214114080000441800e140900d46c10303180424002460103d5180c814030500c0f6600803070075005501d5040c0c004003075654900c0e549280686c04c030501e46142c00c110480c412035244668102400c1003004051207003990504009510483c00c0c100300c60300342e4206070207542190781b42e88203081e111006440070103640c070040ca107402c004205440c0140151130100044c1e0f0b0b0035108481c500001008048200d91a4860703400c900e030001800e041150060380c41d85a07200301c2d4856481400c01598000082c032454990107808149007400c0503500440740c987c00c4080d410030040190002c0c08103d45070010a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 148132832 1250 148131582 148131601
    0x50a0b01032c0a05070f030b010510020319111504030e0a0e010902090109081905060711030702010e120102070b04021002060402090c03040303060b040801150605091302070501060f0e0108061b0d05 86
    0x183e0560380003402c50782066520031005141190324041110064801000002d141c203006c0820b102d0004113401135800c20b40c5410178245442d80b01d080e2030040092208540c0d103400c41c00d025882c2d40e001c1c0289502154941420003030000c0b2030801c0c440d8054602c3c90000c100e0386039100b0f9583d054807070b00e41016070b0b174000d1200103d58503022a04003074650b00035000c8803050560404480c100b080d10440a5507403a0351607500a035600694481743c8505c0b900100110001980708000325070380880d0040090b4030409500c41d00030708a8120842c2210b901c081203042c8801c1d1f18004c92110700881e26440200724030324090303001c1180308a0207800c40850580100c08101050301941100d4050711170342c04040d444a9581c000e540c040c0c5408081e691925a00007004249244500300716850a00c02034620801c070403018441000a5018a0040e81c50303568607400071403083d111040110080030750035103225617035050920300c07418040013425030741c02036400202c00b60001c0c40303040a654180c42400400501c940c0c48000760b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 148134082 1250 148132832 148132843
    0x30406030506151204120903030801051201150801090c080f03120c07020405070e130b06031914070f110601060c110d060e010539091203070501050a0b01032c 69
    0x3034040f42d000400e160710f804e1540311806104030b000c0c50503a49540c28440e002d4500c1d05242c0009000594500d0050200741012240c01d40650031a000024a600d40c485509031007090381e80214600340d444180c0103081c00f0310710394100c3c05000002c01401c451448500328980c4c91003512a1a000e101544c000030b01404021402d83da02c8540280c801d204601d05031800500c690500010144145c80000800b0107603c03141c4908a401e10001d0012451034903415103031300c11001d8500013003103001e48411030025001c0a82002030b0040c6070f0b41e00c41e8450350140d03200103050344008072681c210b16848140100302c4141e00c1031004104907003182091800504e080e01003000070f02914805881c4e641032481e282a400700551003980714110305014643c420032502d0303021507a201c000b400b15000700e2142c0c50405d084c01813000103011544c0700030324000d00240c28041345811900002c00540e01079650343c2c100025520140102c3c41e0603502440c04201a00c1c03066510800001049a0340c40c010f0b1202c1024013000f5420071030b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 148135332 1250 148134082 148134109
    0x31302060c0304030c03021302030708060910030516031218091a041a030f030406020c040f140103030201020319020306060a0305190e0f07050303030405060a0b06090d030f02011508030406030506 85
    0x5403a0b4444e12410f041c0d90b019050310040303004160110803440c0702e841c03600c20f60b030103101c0e680d84084135500e0b902c0c00c200d4003441c0170b020b80c1d020102070140000050002c0240c0300300110001c074405103040c50341c01c000742c40e510b60701140b009021b12000c21106c102c2d507031072001082c4c40c02ca10303000402041007032400d40e044000500c1203401c0fa14000200380c80c0a828281c0b8581410101c04460b40404030381d10340c40d00c90046100b42c0026900c1002a000c140c035158001c1d01c05440c84040000c0c1303800792010344221803242a130003034000d0307540042440a00e0141100d102a045d181c201e080d841c604000011407141d03c41c82007003008242da5400804ca04090641402c244010103050a1000c082c1c4440322989510003040208010f214110300042c0c40d050200a5038410358000000e08500d40e00d580130400a406185031031640450104050b01041d9102e000ca51001e60017a61210582810404d020f400c40f0142038040c415014019000c200c400300c008104c40541301d0b14600440c80d40c80d8103000c6111007a0412 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 148136582 1250 148135332 148135357
    0x120512090109051006180915050c0c060f01031203020706060b19030f090c05130209060d06170a150c0504091802030d05120a021b0a120212040b03130206 67
    0x209004180d40150005581a0b0040381a00c0c041d0480581e040e04882c424880e05442c4400e141001040c01040e9003c0710400e401070110030819a9052421421104c0490b4809032909000c07800b0313440e08008020084d48540888044800355066840c0c01c5505420722081d04105500024100d08002c1181c01c8030001b098a4880d5070f4850340c1c0400913001080428480302c00003460080954205e41447c0102c000c86600504103400c41c83c00c0c0024000c4880c5148a820f441075001c002840303454171020014400503412100006482c0d0a00107454040d01d18900f1006007079108040302d401040c0600d040a9407070048020004400c84440340079a03141c05a070b0301090b00d003032404910716a505030011000c080c2e10b01c214199020400440360949040c010310350342544c0c061401000810640c440c0d4020002c000200902d248001080c09401c2d04d000328000301190544c00341c401c1e01c03c480d901001100c14180064107000d0a06003091090081400010049407100500211800c195103503a0200c4001c42a1403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 148137832 1250 148136582 148136617
    0x70e090a0c06050d0f021c090203120d0501140d0533010b040e01050a1203050708090603041a0a0b030a02090601050c0d081b04060c020f0103060b120412090e041205 72
    0x40300301500c1a0000b450710642e00b810140175105494041c401c80705103c2c2ca5100408900f00e400c42040c0c02003c1004d0300302e801d0701c60b8960850781102800c0141c0361200c185200803030b066040c007481c103140c000ea560046020b80e11844403940000c03800b00c2c1c4a44031075100c58101c2c0080c800400e03000207d03041340401c160000400720000c00c032190120020420b403607110251403110f0b43d842e0103003d1403501c584601204112441c031108000303440342d4000d00c40c3d0740c01100a00e08003054540003c125600517201182d80d1030054810f8500100303584c100303e40c031003c0d1040401c2441c0e0300c03100ac00d44901da80a4000c0c842d50003200002c13803580c007400c251801140342404442c0b400b422a0005003043d641561070141501840765030010b203500760b00441c0c0684e401655898031120300f40d800d200b44070781a420550b06040c0c58900c0403840d501403e000d0300c8c03071001c5d43e0544545420f041c01c01000b60381116058800f0005422800d00c40c58201c01286d603001a8400c0041c0341040b000a02190039014190424450f40070340c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 148139082 1250 148137832 148137839
    0xf030f0501050f07090603050718140307062307020402041d04031e0f08100b0a0309031407022b020409060903021524030f0d0918060602070e090a0c 65
    0x4464105a9203489000200819100c1d1851040d50301812120480050400c4a05110b80c91181d04140d41220050030140c4000701e400d102d00c10042c540da013165400d80500310140314145070421004c0c00419450a00c03164541d10102521600400300018000000000400703000319140c03503045800905101908a81443d041640400c004000f0b80c4d06800044040b002d0b0304026901c0351715a0b0958003180c41c0e40c401840407040607100898001c0c02c50020401c000c8002400380d04d05802048000c800740c0e40014030070303a40d1601500c03030030301d800d880d07517100c2c40a021000050700e80c0221041e0b01800820309144030340040c0010240400400c000941090900c07101404010440d0070804c4103600c65000d41308044010486201c0107070084481180b160050305100d50b1610307030541e070248842c0300902a1140b208921640074039080c01920a00001501d21100b04129082114000c2130442412000d0266a1808c40000d540d0314260050345c4680035403102243d61300d00c00704044d2003201d82c001c2d40340c0700d0b042c0d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 148140332 1250 148139082 148139093
    0xa0803031e01091406131d1c0302030408120907030807050c130207030e1009030c0b03060909070b07030315031202060f090a031b03020718020a020106120206090d0206040f03 76
    0x1864212800c241d510000421100b2942c051801d902c1007030004803480341d0703c0100b00020304901c5a0103200f5640d58544411009001c040300c010f034860500c2c002c10050070700080c40d011503011900760100309031041c82440b000502100840d49141d400b401c401d18940c640301c403001d04149050340000c11151001641008014012440e050303885030481b8100110b1103929480810380c1315050005000a90b0000915107a00d0280c01004141ba800c0c0340c041d044d503850390b031407615440c542d4000c03482c03040010040002e2403070002c1c0483c0e40598001c020b024030b289842003d0f2914010208003c040c10385403000c4204000814030700f100190b802c001610071180e9031781c4000c4d40b650f00039145100511650400a0070a01e8001170340100d40743d040d0f45484100300d0380035025410306401501101140a02c940008051034500d940c103c08040720703400142d03640005400a42150303501d610a48150101c62400c42c096600d920039190b010b0410b4802200c40026440014030074448c0340c000d0038040e514407802009210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 148141582 1250 148140332 148140361
    0x40203070e0a120c05012a05100903090302040b0303120705030c0d020d02030f060418030327240522030c05011e24030f030302070b07080a0f05060a140a080303 70
    0x14044d20241c0300039034030791004642d0209098014150101013907103c502c0341c1c49400d24401d10724000c0f0141d031102c90b64200d4410a49200c1d241c00c0d400100715075014030030b624091289080c480011401035181c0180342c00180000500207022074203105012000a0b000c00096040300c1c158038506000310350b40c5142842c607e0081d042030341c681c0085402c15000410509180c4079500500700c241c7d80400455800395800c07800303001d502c860b01811207034000050902c0c0120f41e020414040c82034542c12225188912090418244a458440b901b0b003840141301400703428000000f00700809080c0341445898034241076804400e0840024555880e00d240c4024001514800c0b0b045601c65000601045032140e58408100f9081461001c54034a0700ba0200001104e480320582868481d04015050480c41d0319000d1010304125410800308250404021010055102e03981c000441c4840421140c2003da0100d20001c032140540702d03828000c0e2250f404107558101c0084000c018400840f41d0b08d18240203241c0b40c40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 148142832 1250 148141582 148141619
    0x28051c03121a040b040902040501091b02010c0801060c0201051209010b010909090209070305040c080303190c0c0309030b0a020f0d23010608071b050f010c110c0906040203070e0a 78
    0x380001100d210440c41034001c1c42450700420081e08040d0b0004410440203044c640e090707170f074013580c0e650300900161558060203000f041b403518001a9240180548901951140e042e0b0046900d4500c1400040d0781004999040d1106803404004078503803880103171038a00c682c200352041c0100d800100b0020030415081145010002c0e41d480e010541d54100300e00680f0700b4014001d6204080c100003400b1a4400da20003640640140d03000481c090740e8200c0d01d829540240c4400d00c014864120700c100020443c003a00b401e9039003601c3d001c03190040d0707070f10001c000d01840c3c000104003214500101d80d1004194051f1500b0000700d002c00d40d5900020f24841004051192400400e0b0a8000500c41300070103a11144e0304035002500d87d481c07a591154070444d050000c620a00328014903030590300c0c000c100200321000c580751b03101d03000045600d581400985404003818000c481644002c001d03600b544c4903203059640240c0e040e100580c40351103400b01500c490740714010554001005140c00174440c9003802c18207095 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 148144082 1250 148142832 148142837
    0xf130501030c050c03041e1205030a0f0512060904020609060a090f0911030a0e070b031519080c040b03031b070303080a050f04110a081002040812040528051c03 70
    0x4010b0451015540f44c0107640b14011260010320040081d03e8560841d203150110411105101c1c84d1208200307150aa07180341c050b52150700110f068440c49401240c610864400f5080141c101242d8410301c12480d24000c00d018000d64103640460115144d101c1554810440100304c6616403460f4200100081c4141c8902282c0300e03032032940021010710364460401d4880541c1d00d43d51641c1c1d40d400e00900a007003090400b100500c2280800108a0103010140d801020300c2d1036000a2901076004026090440c0d01c807403517040030701e6401040100000030f1120f000348070680d400314110302c03202c000905500a0003004144807458511404034201e01080d0307881500e10a484d00c0b0000e0307c2e00140c0100320b41c000c44404040d504003002080c041445110781c0c0070340e28030042003100d00f203460329030050a003541d805e00000c040707402007401e01c814131052202003042e140c1d000781c0381e040a1074100021042e1443d82c000740c040500c041c18108074150702c5d0300200702a10f0054103c400042480c25044490350449405500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 148145332 1250 148144082 148144091
    0xa090209151204120c0507090608100614041e0f0504030f0309020d0b0c07150e0717120f1905090f09190c0e0405090a06060f030b0c0a050f13050103 65
    0x10320401ca6060b150341c15020414010955925640c1511070aa41c00c0d84405000050366000d00080781000100302070401d144001c55442e02e00000360303150284d118043c503803050900b4000d0011000c4441c10b021031050031600032401c03581890540d0804001444111407a5003000da00c00710f014446d40045014911990702d80b10a48040f180440031111107035802903011000c81d60700303008a20483c0c000394001100d086030510f8000380e55035542c840e134a14414106002c5c1c43c0d80d091040004288008802001c000e0f9031710304048000c0313524589944800a10741048800802e00140302c0e0711201c1a50411180369680404120300002d02420580208845601c01c40c403c1006080740e04208034150b008200c1c801c01c02413041c50750300c4144041c2100050340002c04c6400000f0302d20341d03612805154043c813a0503002d003001140300c2c10300b40c0980d25160811407181c1c2c0e00301ea0800000c1c0d6501d40403030740b005486a52580b54424560210740d11311070b1082903c2c00002c0407403000e018002448440c4110b4100b62000c20 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 148146582 1250 148145332 148145359
    0x111070b0c130608150d030201050f090a0b060415080a080d0b060408150405010b03070f0f0603020309031b01020418020306040f0b0d0602070c0e162a0201050c0c0a090209 75
    0x7119403046400954000d128010204040c1d40154030658000700344c400f200d1030070b036420740109440010080064006039161018007200b1569001c42d103400034448405007a240c00031392940704d10030350040e100754066030791055400c800300c0c2002800070140c481c000030380320040f015043c0340d04150041124128800d207001030389903003890400212400c4460303680250100e4591a855101103d1004005541c19500c800b402062a503003802540b01420070ba0300e540629904010401941c201d950b08040141841041448030011000054800802401c801c90309400e264003030b10781c00382c0610303800000c40d103028590f0120071040e503402a40c4100000d5a04021941d0f04442105c00c0d50101e103a91034000c000240c10f04003140c103940041c180f80b405454081202540c07220080010f147c225001070010244101500d0500c3d0b204035022445a908860b413520485401c0c44151141c41010000381400b000064002110b81c0c107101e0869140ba00a2004029507520f0004401a510040349039101e0404014983d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 148147832 1250 148146582 148146601
    0xa0e0712150e060912041802070201030f020a09231f09030605070507110a1404090623070f020607020c0603041e030509100819020a120f0b011103090108160504080111070b 75
    0xc6c3d08941116070080c800c031201403280c5000354400c0d076050741050b4545084105855141c001003110742465a50310007003500e003010140e03030908480c10788034032680911208a915944d04414241100c46044521007005440c41e042c7c1d10141c01e58030081030305007040104a1100d07040400f80120398003030b070f40010003180303001e0800030807007881d00030f850308141c01e50301c4c4201c075007429800361950501c1040c000558444e00c44074103903030000b4880300f00154042d003170400c50703030710ba02102d0b0260110803400181440e04011101a403107060301e1517443d028000100008042c00841162290342c02c0d100226052a00c40780e0a000704541e0050f03801ca40078500e010300e2800e5042c8901e961a00c500b80c0104031440d002000d02c280800703940b000301954100600300540002040551280f8401100d0074240000c0c02c610707041c00540140301d007912074817080e003042c8400d0300e090f604014444e510844804100794800c4480341c0c152000e0203560840390344e80d03203807040c031190b0b05850f00001c3c91894010f0700040d040c1d0362060402d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 148149082 1250 148147832 148147837
    0x130905010617060712020f0c01020d0c2c040c030f0e06011a0f0714071d15010503060d02010c06062705010f05060a08060a09051e0a0e0712150e060912 66
    0x848001402c03508054170f1283c1650140440d41c0509903603600d007000440250782660081682c407415660b17a5100200d0b059042030b503241c0006281141c40002c5140485004410341ca4448564046d903250702d0700600441c86a480000612000081000811203808500381d446c4403d01400070009009211459808003800a41d407404200080c028a0318a56580311084001110740c0c408a5108009000c5583d8401c081c415000e00c1d207a030001806c5103400e10003a800e422030f00c50441e0501c10300300180711640d00c0742c0a0a00407640c0a003011380001d01a850190700606499100400b006481404005180d1400d1001485440920740a0100b41d8881c2c01481c3c0d4968203206603544071400300310010b49240110146c41e48075200070300501000d6900c0c41410142c0e2012107001e201300d01600216101e01022810540c1c204982120403c207040c01313140c0150b80c0703580c680502081d180707000e0799103c2000f001552824030013003984c40c01d00c5149072010b006952840705171105000e42c014407080707002c035100d44408d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 148150332 1250 148149082 148149091
    0x90204050f0612071208070c08070b0d0b09010b0324040f090201092309040503040503070f0305060703110d0905030403050d0804031e080a0203090c0d030f020d050301120b0613090501061706 83
    0x18041d401d02c11598480110b64840c020452324660340c520001403504042c40020001d20503507283e03e0740d4104d039600c1d2000300c41e100c20580c1d2080301e4003001030107100032038001c3c1c9500c0000b008514510440c4040092040c0e2840b08007c2e074458201030090001c06410b400007030075140300f0380302e401515884690511010204a0004107002d01d480022241860450407103a002801081a00c2c6010b440d01c01090a00c1d44581000c15410482c08040003048010080c5560240d601c0c5000c020030941c1c5010015035129540b07410350000c0d10703800da00040c000c041c41120001c60388001200d42d101016240500014411503041d404180b120b0609110310060041c1c0c0241501035650780d41c615a501145140250006404036034144541d1551002d20303200e00c0d0080040764002d49900650074001440285440c0344210490108102800100b000c0030741008144131445c0d2041c0002281c0d42d13800c010032001c04481c82e01c0c00041e03061855110900c0300640c0100c0c29980043c090341e107a0322610034200e607294810354 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 148151582 1250 148150332 148150349
    0x11808030d02070c0f060503100918031d09041401112104031b03121503030e04050c130b03040302210a0c03050c010606081501020c1e04090204050f061207 68
    0xa041d01810241e004080b07051280600011441d00e484040840468540002d008600d000090100c034042010b00700c8010006440144140000304d408610b803098083c4004007071141480000340420b407808a201c0709400d0240100d030a518082c100100071a90780071800055502c0c041c0c140814192010465441500300d0080300c0d0920030022040c5001340d0001e00c10f03800c0200350040200f02140401160300520b00aa60b00034249280c159258112001c590481c25201005201000080d8100c040800882003c03100040c40fa07640629843e80c0783302d981e51001e110f503811840840d8880c0408041c40c002c80c002c0e4211683e6941c422189041c0d900d00281c1281e100c074017881000e807842d00c0b4034200c00e9124402d140460070304400340c40707031401d441c5280c01800c0032039500c6040041c08800300348200480c260901c006d01e00881d03400041812141191007160781d88211000100060721150400d00340d0301c0d4058010001c3d80750040118040100544045124100c1c950314100340c0c041c0096014151030741d81c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 148152832 1250 148151582 148151587
    0x5040b0a050a06080a0209040204090e0c12070303110c0a06020706030e060105090a09030207090e0a0201021207080703050c07030516031b26100207030e030609011401090c030f090c0501180803 84
    0x9401e44d4003140080c580340340203408011940e4652500d001420091007185030108a40d909214014140707149203501034041d44022001d006403010008586045a030141410000303841d0702040a070030011a0200c10f0f40001c0c500c800000c1041c1c0c009440700440714565001c01140d440d0101403a128032080c800d141c0e005030010003003000c00b11643e1010750820b1003401195496a511811b0b403003581e4140603034040c03a40100842c3c405558041c00640c820000c505445441d0014640c1c500c1000c0c050000301600700038002c50310b11030741c413000c1110350301564100b800c84200103152103442000f410341d0300084030301954140502046000da210321009440414007600700c10103640d003200260700030700c2e90300503c103105074202007411075411b20040034250301179980c031220340300042c0a141c80c000d00035048200c1c9178901b91680c02c000c041308101505650558801107042c8489100807006000b000d0b050310300340b40c902985d10782000002c09030302c002c64200f078942441000e10b10030360300d061554620a4008a4104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 148154082 1250 148152832 148152839
    0x90102090906041a03120415030209091303020f120307030614031b0103020904180c170312100e090d02010501080d021207020d150911100c020907020f010f0605040b0a050a 75
    0x6030f000b2185502c4d0013085800465490800a1b18140c41c50710000400c0d400000d050014100c0030b15891004281420113615240ca188040b42e00640c009182030080e0350344410b04001c141c070902c100c50751000781c4411524104007210031a1920350003078440e40080391400f4130014400742c11244410329203000a018001c5444c001d0b42c41c2000301000301f1424100f545c03c00540e00d0070755845c81381607210481e0654001d0705c42c07000d1800720b99140c0340c0c1c1c00000402000c002d04c10300000000040300d000101c03003400000c00e511410f6030070325401d10641191290800c8013041000c504000150001e01c0041c5a000b403003240d907075554280d114120154002e005030005120240341480e1030004180d098030160140612521540b03c1640c02c03504034a000840c6502c80034000709128940f031805000e801b00312405a0b4400403070b4800ba0460003821002805590b800002501d00c500910801c0c043e005610000d0060708003201080700202581d01401e803086280ca0540e5445061501d80d10003502c4000d4550b00c502400c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 148155332 1250 148154082 148154089
    0x10c0201031e24050414150f0d030320040803121003060e030a020106140a05010f020c280801151206060b04030602041d0603030a1202041e0e090102090906 68
    0x4560704510842d41d2402c010000310950f0711410495024040c20070340308a20710f001c0003c0d040c0d419071025100301e08200101070300000040c0b083d1380186004000304450030791341001c50074448a941c0710542c0406040050028142c15070412a04501c035104c030006515580c07100080c01e405240288116a03105000c6403402c2000500359541046800352084551607031703540c9940a445150300d01c944260404104480e980d502402408050301d81240490500c03400074010450b030100500c9064100400007a00f0311501c0e0003400030000404003e49000b40303000c000c00c0c2071072807008806035400b40b206018400041110061040c82450490780132010041442e24484c0105003200c1340041c0c80300c541e59200010711490301c10040c03004520401d400350304c0700d2406405151846201c00314502c002ca01c48100000350307034048200d40a094440c2410020715980780d1302c4900074080d5400049150724a2007518411403620910003080300d15010580c100ca585051240d0300b40e0041c0e007440c1c0c1d04140800c02003291482c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 148156582 1250 148155332 148155341
    0x10b12031b07030807080406170106050f0a200105061518010804150204080d09140f06130308070c05090903070b0705090112050a051902040305060408161406060a090b010c020103 78
    0x4168821609043d869480c2c11a142d802040c0844420f07134001810082d0a4000c030b22074071034912400700e05100d90f01d022006405407240100d40c0400000020303100c2c5485006401005e9481a8400c080242003034030b01c03d090082900750b40f035078800d101880da00040d0325045d408403400c140d00c4a0300601c1192400d40151038042010340101d4003a03152801c2100c8400240c40900001c00645000b0110001001005002400d580e000003082000d90f001d0b2210359110141400c54a55040c0c940660b02d94462a4141c00e5452581008204800004080c800e02858400040654104548a030301d2900c50803000c40d580d00ca20303600200000b0031640012009809000941000001070401e6448100320482c81000c80704122204444a80d40c1e4003407208581411030b6840314600c00c0f810440c941030a58031095130b6900d008100910b404000159090000790303024241080e240e04c03000340890010059425515104200c40e1b440c003038000614009500b6815001d0340c01da041061310745441c0d2002c41e800450242 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 148157832 1250 148156582 148156627
    0x1106030a02070807080d0c0804050a1416090506100c0f03030e0a02040203090f070501081515040305011104090b040504150b01021e10050907052b05061305010b1203 72
    0xe5824024400402c00b080c0050642911540ea401e40e90740e154034030101116030446024040003640d80821001030301c00640d2105503034000c10034646050101400d0b501e0104040f4492380c0304066142e00240b0541560007e60044404a031011140d030710301c4004a5181c0303040c00700581f50401140544011134000e5015204650444064030141c1c2c0160300440c0c05e07a40300ba034a50100382c2c8404406c40742d00d0400d10514010f40402d01c1d00803c0d030308003910010407084124070351034441e409185808001d85000030803503000350360080003800040700b0041c40301c080d0342061141c250010300b4035001c1061031a0901c141482603a00c41014188000007841c2c410051444555260551151000c541c4000c0655800c2e210303802128001050800d48108d280301c296507015081c00c5080e80840400d1200d036660310015294030b4190440324040b03041700504006144c1c1c0c400d601404500640e0244007260348220303500c6500340c0c000c10007800320350742c07060502c00001030160034001d0035007080c07004900c402e00c844401d4089 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 148159082 1250 148157832 148157851
    0x804030209100e160206090d0f0f090f03050f0609010b01090b090103090506010e090d050316050703020703060203070f0f0e010e01050c0a020406150206010f030302030405090c16150f09110603 84
    0x10648a0045007940319064911141300304100f08402e9a160341004803980c04014903015102c0020360705005000410600310f00b4050003151502e4174501440b40780990002c01302002408201640c909205890350b211000c0302145018400c00503403000c2c0d0501540e512568103a40c3c03803820707900d0300016401d41c0d01714000007410562206401d230b01003002040094080c280b4243e81150b90b0400c514564980300188120b101444801d0003000404c29881d84084400c084034203045903281d5107032501b04d040c0550764100030580362010040c851044d602c01d4117840c24980940700d20074505042b440a40c3c0001180010500241d403205141805512030005010045c40d0f903002c40d001010303d0b50014003640e103550403906d1417104200740c0d00030280c1d0402a05005000c2c400c4816242c900310f0718001c0d16031140d8010b55018091701e4020405006130a070482c1c00c05020700c40e501c8050802c070302d40906903a00380d8400c2030034141400f0440349600d8080c0315803400c290b4008010100b803e13000c2e00b84106a04003d006011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 148160332 1250 148159082 148159111
    0x61403040605071b03030606121a04021b03070b0603070b040b1c0f0f0212160206040f030509270108060106051b070305070e0a0509010c120b2107080f0a0804030209 72
    0x14070304e0345800021009200380c0700880ca442c00c12078001c1201c1c030100d420803a0386090001610136004c15469101c0e0100c0c068502503655003c9020722125404d0004101d8400c3c4400542d100c2841000185980680030031420785040341e560302c03c2d084c4240182d0040744c00e07440040100c12000c2c0c100e0030007a80c2c42c61841c17902055039220004031400300c2d40d042d98004121900010303140c02d9525012080c95209a05408150f604015040001e5036520014801006c3c4c4030206810403d140c01081034448000005120701d24449a403000700c2203240c500c81c420301150110000218685801085040c140c40581d83c40070f041c00700600c0c11030440f0680312408406801024800b101040051040d01c0103007454003c0d03882c0c61b040c15007001e411940c00908042c8030b0703450700d900300754841d9116490f0000342002680218440c011b6038000707480580d8000092403090107a8003c408140c0c008260380c821a0392700b8090b5400d00584016454a514840030000c1c035104040005000518221042a822143c081c40c00034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 148161582 1250 148160332 148160357
    0x9010506061c150e1503010b04060303020c090a09020d0c0e06010903110609010309060501080307020a0b0a02030d02210f1801050f01030b0403050f0a0203190512010308091203070c0302010906140304060507 90
    0x1071030304e102070b180340207604d4078582200d41c0c50a0900072401100010386007001107a01c2c503207000b07494450140d21a4032034208070000c40d00145894101c2054280c0090010004111342e2070003420101440c420900b00300300700000a90598010482d03902201d801075100f0f8569080102009410b41c000e250b41414943d030f4503500401302d2802e10405018004010095545d401d282c010415444401d038440c43c10320340d041050a0381141e004c015180e111865600260700c51002c0005201001e03180321a40080c40701352804c105a422a0f21760b124040c1040c0d0b10007810046028071024203940c0c084520a810f4a0700c2401000010481035509500501034601182820565443c600055010b5840c6400690001c103e100c10300c034100003584808117503402d205d4503041c440203e000811304141b0020f42200f0307001c254642c050b100d030b420f0b00d9030035858201501d5843c0007904d0b140074802011b010a034002840d40002044641c014210940303d9100c40d080300303080d0f5803242c1d02d00d03018250081c090b50400c1500308600 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 148162832 1250 148161582 148161599
    0x41101021504060507020c1e041a040513061503021e010201021201030b0105100e0f040e0f010603060e0c09090316050a080c1f05070e0d11090103050609010506061c15 73
    0xd40680c0c40b070000031844d401c005034004d10303110740109443d1080c07107500c0401401b0120f151206941b0041a14042041d42c8020b034050fa25824402c8046d41290a01d4204011007401440ca01c1615100722410486030401c000441039552481c00001c0d00310a10f03011200c0c000c0c01e005a40b6034100b80c141b00162600040308060012401c0a038030071114810700310018041458540c10a03901c1992519024111751000000154003043c4400003602881c0c1c0c91008000a580922194003441900e00c024800503a480c03810000130300719109128100d024810840c805403505800540c080da203010025410700790040ea03071400c214419101103d50f44034600c4414006441d20000e0aa034191810207801c0c01d4a2020b0f180d903100f20041d820030090b40c90642086040c81e0405c2048102c083d00340c034552400007551400385030002c1400c01055214a41d40f00000410900240e12440341c8450320090003142c0310700701400110b00500d00d00c0308040312241007502c0f0302c5c0c1703559101e0599882000d0b0045825039440411 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 148164082 1250 148162832 148162873
    0x30a0803040f0c12050105060414040b0901060f1503060b0c06040b0a27060c1e051c06080102210103020109030f08090d060f1a060f0901140c0a03091d04110102 70
    0xc1c400c84d45030414a001403207420b06c102540044180d8042c004528103074504540f6101c000c0000704114002001f007044c01d90250311100150040d07101c940c43c0c41d610742140d01c0c1641509040200000e041c080301090741004032081c0c0b00038058400c010807007601e6965400c0f08800d070003012403aa55684001040031306800310394940c40002e140b8186c0301c2440d22414040701b662039140040c014414202d02c8000b0b2070201007080100002c1d1854080d480350209644001d85c01103c40c0e148804605003080030a0700407040d4002c0c41d60002c03407410140ca04c5606088489001e10901c00a400300f45a032a003000800c1d24440351603080d43c8559a000e103088a514005070862820440c10380e0392581c0c403890f4250541d002e118400180641c44540311481841d4800a0014806d11190150041c00800d00350000d9000e410098601d000c0550101d0325a880c0100d00c0c3d940700c00b9804c0c154002905200e00003030041c0c40318440401e003c4005581c1c006581e036038842e080c802d12041030301c5d41103204444861030940c90041b030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 148165332 1250 148164082 148164089
    0x92909061608030c090a0918021003020702090f0105040e1606050a050403021c02130b0306130203150901021206060a051624020304060c031104030f02010207330e030a0803040f0c 78
    0x2131080d200c0320300b10180309120308150812040c46141000750403a001c031014038005a650b0403a13100c3c8a90466020440190040010094110002c2000d002e640000c0100090590b00140c03020000c00c8050742d61207070382d52100e020140c1c108040c00401e1014510a200904182c40542496858030307599034081541c1d00440140440307214800305088007185021000d900e21380c1301c0d0b0401800300000c14800030752121380c00b4040f00102004098000115101444404c0f140f00e03803d8040000c41c075290361158080d41c003501010304d4101039400050721901c1c040040e5481001f04c0e40e6100d0030f00c20100a440041c60030124280c0310071700d492903c0c2003103841140c40086403000945000d80c483c00c0c20300d440c605403108000d44800b81803c0c400b00c03800d07141e003001c29601141d8001c3d4034182c10502e44d000503420301210360001203000286980240c1500ca440c43d00f0241c807400c640708640741940c101d00807154092814142503042d085060244007050910000d140c000c2d00410809081c1007072030747d4040c2400020360 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 148166582 1250 148165332 148165351
    0x80102130803190305060315040f030f0f140c0705060a02010f0509031206130e01091208060f21030c030c07031a0108060406051306060609290906160803 67
    0x500800080094000c400080c009a802541400044211052800d021240100826507036000064a5603800c2050510703a816180c0c0f602407505160802c1030510107850410b030089200c143c90311032214418140000c0b0a01c40da40c8110300200501034180d8070f42d018031801500f606c21700101048555822006048c2503c240d0000140404409648001c1c0e41c0020402d02868205104048254082074980d55202108075613904d42d0960b040c0501000f407070400307403010242d843d150011003084072914100c01a1540e544400b03102d0380e260400c02024584400c1070f5500a425003940d51f050000c1d00401e41480c0d144403050b242461300380c1c012949540c014040d4043c86038495082013003440702c40c09824182c045c8a0300ca11043c1d60410703503941c3d0740707140251000301441da640c8002940c02c1d5010a000714850760100e024081c040c2d6a802c000e01080300f034042d141048013821000030f06e4a031454010303840102ca075007400d03003040f804008010040c0c100340000a01050302d08500d50000b01601c1c010341c400c0200c503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 148167832 1250 148166582 148166587
    0x100207060f020c0a0603090206070605040c030606240503131401050406060806090c190b070b0a0606320415180605040501021005071809060e060a05010f05030402030115080102 77
    0x503a0040a0a020425038001d64020f0300380504551181d6822005650300ca003004145246648017040c0d0070702c2501009011f0a28180600c007c00606080303407421280100418088141c0b0303429170400c10155440d0001400c0300050b03840319503078051006140c0c00b0312a40c09081e2070b50141d8a44005841d511a4400200e075505c400300000c121242c403450000e403050740020090340c0f40c0004a1503540692482d610b20900707824000c4c01c1b042201e0304543c4088d04101c41d04a84802c0640380258078001c0c140c540360580c0d42030030700202c3c00500c2402cac0d5a030410909010111904c5142110a0781800314071045a040c410400c0040346080806404202d0281680e58048454201310560f03840040c182e0807440130400100800c0046a90004204030350362080c00d400940e03611001c6041c5c40d85107054460001a085902d00025a100c4550080049580500c22404c450b942c0200300039010049001e01404544201e14410080c0d11031400396911600c090b000191b030000024842c2c1c03141c0c001e6486028203a400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 148169082 1250 148167832 148167839
    0x1020306040518120d06092a050f040504020706061d07020c0108010f210215070c0504020930060a050105010f0305040503030c0906040b030112170307050910050702100207 75
    0x744a80d641c00051510f640102c40841088151940ca05107808a1138000201e500c010100e9244d00c0741006040100c000c10800090852000341000440007003090003600005412080c0d01660403903ca0141c0f464560346443c0c100810400290402081920840d40d25034000c6200b41c00d64060761504400100707100403d240c07040d402480c0103400d07454541040248401041f00e0ba1402380c440d130030341d000c448820203592503401d609603051050740c1029600c500b082002000300600e21005100c000d0040e8200c06400c4d803250700b4030040e0b101d0049001d402c21510341503c920344070401203507038a000807980c060b240728221840c25031a080081e00c1011015a03580010084c035a002400203d00c071042c0e080c00d1003945000d450312505c03800014020013000c500041c4142c3d85e90307140c0044134050000c41407880d03140c0d44c64044410603003a08540441e43e000805a01c601e10382800c0068a12034025a528a45440081024460b00f8500340c50442d040c0316050240c000180e8038041401041c607070399401032070034924 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 148170332 1250 148169082 148169089
    0x207120305040c0b0a0507030e030a0210050415030e0a120c06111c0b0904021504030c0306020a110a0503040b090a08030c0c01120c08130201051905040311010503090c09090313060201020306 83
    0x1c03268040d42135254200302c071020040d00241500e0546400d800c00000000d0054046410540e4a90000b0340c0848045064103d20360008080c10584680d6210720108408001095044801d01004640c01e64030040a0b0030011354041d040b036601608a142c40a0314502e140d885105a40c0350070014400700d400400c000c00203a10707030101c565000c01003034401e21281603c04045100c0c1e0f640500040e003e10202c4540c1812a0400300032240216031100d050281e1035540d080400003034000c64030340000102c04800702d60420344005840e59107685c100c00a18a024540f0100035083d038480d05442d83c000801e036070700061010003480580040204003001e881c0e40700c83d440006000c5040c0b419074030300e05803800c00003010080e848001540d03c40018035880400c03600c280010b81d800d009860b4014050014410204407041e0f021000d002224425144900c00010420064880d030004681c5910307250700c442c1d1b190220b468020890ad8000c08000b050324a041ea0001d04140c4c205c4441d0000c20150b90000144002e604 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 148171582 1250 148170332 148170353
    0xb0a020c100c140c0303070f110609030303010b0901090909030507062a0e0d020306130b090102190c02010c08040f1a04060f0503090705030615030d0e1c06020712030504 74
    0x30101c40d000d01c18500554007078034a948050019004210407904000d411104025031000382c00000c0c2100d440e82c1c2c441ca80034404824020084400d08490143c1525508100c0103607407054000034060343c00d580c208420072aa03900600502410403502d24000503404689109501c04d00c0d000c0d54840c0e03540c48080c02c25200381c9825003041c0d4009004112000203d0203922041420f6511504d000900f8001e00b41c0015600d90245101a6143c0200014042c0c403001c02c5040609880c0301c1d03240118a80d0b45c011041b800c0b80030303200c2e17500b000c00d89250918001c0d034404c0c40c07840752031071050400d89003c0b501501c03a0782041e0019080312a040c1c55810060294254804000900d070150081ca83c1c60541041d400900415900f00084180702d00440412000d4805100d00e40c0584805400c80f2064074000704800800385c00707021070034040d020701004603600c2c030300c1205502c0e00140081d01c01d811110000b060200c140c000c600d0251342059080c000e41000034003282c94110000b0b915a00801c450500d030a010701da1a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 148172832 1250 148171582 148171603
    0x1080d0801140402160b0c0307090608160c030224060f0301060b07060b01112e0b030c0603100915090c0801032402070f1505070c03080a09050114010b0a02 68
    0x44a0140100001d941d10101c0c1c22190b001903c1c0507848584031031400394001d0b50704500a248802607002c0110740c641d000055481050180d40701c0310441e540301d501b034400513003d896500303a444480307d40c000c01500480c1701d801a21700c01c0c4100c500ca013021001c494100b440030107411030704000c070100307101951a1920402c140100110000c104551424401d0a4184500b51000348040e4880e1080142a1b0084000c0400d8000440c1620f41149400300706840e03920340d03d0311400314178130400c082980b043c019116101c820b00010307004101c40c400309020045a0b400040c449002008210b201148041c62400307034402d02c845051754401c4a03414180070710700b81d03000c0e07002000030070442c1d000410200701440304130a035500041910100403a2005404400b0340300340a000351008600203007140070003185005000046015017420852074a903007000300c030f00654001e4050b0015640e0404280c0d50740303166000a8245110f20000030712035910403108800d0314000d0f80600000c1c04003154039841260184980e8112 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 148174082 1250 148172832 148172837
    0xf0c090105010e010c140c060c2413140115140306010e04051903050d05092a01020a02120106051009031202123001090207050f010c0f0807090e0403030501080d 70
    0x1c42582c0f80002c0c074014840314054260b4142840d4510051030611010f04078100242045503903003481984140c2e181c514440a4172614524416503110b00b14011009014050010100403884907603101c4110541941003010859541c0d007c920b0050410b8cd0002d40c01803200354083c5c0040b02da5801050b041c50130507403050003048165800c0000103400443c0d0801e040c400b4054980541c2c90354107088800e07001c0c0c450f14400081c680700920400c401c1c0003908a248000030380d506141914036181d010b2022408a00d0f8601683c0702059040c01403500d000400050030b441c40c00000d003d6501d200148000128410210210f41e0390a8144180300c200f6031607401c50140c600041010700300440f4012102e10400c40041046c124180031381d1065200c1e04032248400d604000c1003040b55131a655024000d40c4003a030f046502d485a01e12900c40304a040c040e081d0780b450561103403040601030903070690719500c008010300704112071500f0104904014400d4940214081d9500080e0b030b40c10070840e6854085141d698209 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 148175332 1250 148174082 148174097
    0x4090c080f101203110601060503160f0207060e010e041b0f020613030f020f1c110f031b0a14150f060a0501120e10091106030403050d090804080f0c09010501 69
    0x3100603201201c02102c1c15080a000205004d050444002c82c0010b2603508a00071007000082195010015502440c101d52501c10a05c400755800e640c1c8140f000b0012006d60840602044514014400390400240606201d00f140d01d4401c0090101d0320001000d81036241d001c03209400c0306034001008080f0481b01d000034107050a052405014008260800030100083c0c0401070601502c00e00c00c03500c0900c400707800c40c1d090800c00340c10900c0c040305400e010700005035040d0000038840c5000541d4002c2000d0400035614008540c140d02d03050a200f03496000715440b03500103030400210184410032419a52501401d1905100f20180d0781d4082c01400800c1020b42030014400c1c60399952a06d5000c0301c0302401c2800d680d05e03e03441ca501c0a410990080d03400350180381262071414001d82c0101403100e1240a05120070880b610800019000560f000b0300029414400070a0082c03003a0b000660440c06580280c0c105a03031501000e1901c201d0000c1c0703910f140c110480c208424103100c008107015001c242010308 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 148176582 1250 148175332 148175341
    0x3070b0c06042a030809130207060e120a09141c030504091d0c09100807080c03100c0507110a030f110406050604050312070c080312041104090f0305090f040204090c080f 74
    0x3c041062a02010b070a004c0002032000181d91002004130803628042d20540d183c0c42c6600380100140002c40400016005e0510801607101e140403c0360700740c01158881c01001c60424202c4a0194195681240c1000d0030080030f988952008031030a0038a4400c1e560643d40e41d0410003400280c8601c20010000f02810191400c0001400308580c00c61000507140e09e003650780c40f510100c1c2800d07c1540040c000d0301401701d01051001c03000c50921584002034045400071410042003000310781c0c86030807110001d00248524000640301418115552034000c003159805034490703c4020349541030860854203080b0011442969041901808000b0841222860300f42441d00000c0707030303c5000c400120250b16400240030010082021a00005881c0340011030f0348404048160309012070083d10306641d58182840c000703106140c980104504141d100404e0320b1410315959042d0350540001e00038603808029001302c4800e60b141ca201074402042102d0000c00d43c203203450005040103030090420120441e9000410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 148177832 1250 148176582 148176653
    0xc0b0409180f0201081005060406050406080c121317030c0c01150302090601050d0f0603030305040309080d050406050319050a20130b03250e01080718090b03070b0c0604 74
    0xb010324030307020b0030b00d204107035a0380000103498081900100c0e0b10400106005c0303a5540e12070003034420b954407900e407292540c0f02d41001c1a598003400800003c030740c10450000780600020107601109a129002c0d2030300e83c1e440c10a4030250380d0800c0b14502180c01c00130941d0b410f482d04c00d0156100c1c0010a0b41000074840c00c540109030594002400a4180440000c9a100303c640d16070000d462a41d142e039040055589038039006020f404245c1d0700b40c00046020790702240b0514041824158000f041d2102450149000f82c1507800c2c1d00010003d01c402e80d0040403890706440749000b03141c403d04a0082c0043c00c01c956032200c0040100c3c0e8030030000c00030030a000d12040b001000c079064094801c08815941c480e070b10354000d0f02c52078045e618400c0151600194102400fa0880c8054003030b1003003606c1d0702c0d0050343d4806040782c49041402c0c980d1840e0001000c00c000381b05c40ea512003140b41c036014064a2450741c459510903415070100707200040d15804501080140403040c41d508030b8216402ca5400c7c5500c0d2030710f00b40b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 148179082 1250 148177832 148177853
    0x3193b040207110405060a0308030a050402091608160c02031516030c02071a1903020c060105010311070209070e030a0812060102061e06030a0c170106080f0709180c0b040918 76
    0x30754007440c2e417240403403025540d81d84428001c43e80603181560300e03e046c9081101402003510100e004842c1a00414111540f10a52070703c1c0d09400d1340c50351910340e00d004d180c9440781d03180c80c280414404a0b40c030503005620144145082548558007121b4039041202404000d2a0016404410141303085201e58907982e000c01c0398021500d00c030314807005c950980d105d80600340c4034520140d0822691851100505905900901a00a8100300741d030240d031b036078900640030b403028003442e5162603a00300418001840c104a00982148552a140b1704d00d40441020074a440760285007550f01c400301040c2d0000441c103580e1202d901400c00e00c0030702107078141f00305407070706c900d00e2444203624002c80140001da441e1010007004180542141c501c0d120b280d5102488400c0b06500034a05010b035080007000300301c0e280f00054521800755010700404c0c07407074030b0540b56100921400001c041c0d069043c10480012602280c00301018010b52200250380f03910380030148044901000640c00c00d44842c07500c0c0000b0070383c070010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 148180332 1250 148179082 148179113
    0x6030403020c010f02010c30051807090c080402060d0906020a020c040b04090507120302190c0503150403090b07060905011b0906090302010207090513150c021005040503193b040207 79
    0x140403164091b4481c40016202002c108e0000b41c40c64002080029010f255a4000d054644015103012680703031201481501c0f080b0903004c01043e0100041001818400020728119107441800181c0c2e05240c0e0b9503400341da100c100f0200040c1d00085c02c5141520307142c4200b9902c180c04542c2003242200a6580d1034681d1103038860300d68902c04191711807060500034440400c01c20b04032908040d05440c14642010080807600405000344140e800040941501186207805160141c81c1d0b0600c00345004882489948662400c4405a0701c07402200d0004000f40150f0503c3c50f500034070b0180b07071f201c90500100100190342c4a142005011402040035076004182a0203a680507100402c06a650011805003140e211000501d2400200c0020440354000e6020115224403039013994401c10310311341808150385007990058440d0700f08002c0780025483c1000707000160140c43c104142c0c00d980101e80900c1300454880c0204014503560440040e44600008070074002400b240d0841c1004260b03122140d20020400b07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 148181582 1250 148180332 148180367
    0x10506090612101103010e0f090a0210122f0307080f06311503080906090d020d060501050301051602060610020f0d0203180f01050a03180206030403020c010f02010c 72
    0xb0000140104144103504080212803424000007140210040c2c66900912504003d0038a0b440804c400700d00b030460b19400748542d04002c10786000c0340d800708500f4400c1100c0401c28008524a9080c400015000c0c801010101c0d15448185140c210a422410580200c2c458500c41d410404c200056400050990300080c050885c2c03886a80c0c1d040104401c21101c482c1403500d80c420280d002c401c1c0f642240041005412042c0604c0300c08072240000780707550712600004184031428444841a401c240d1b010308600c00d40100700122444d9250040b0f2640309800070181e4059484000512483c102401450707042000307551102d000811004000752204030151401348075200d66200d025510388200074141d00d01101c003007907841c0c2e5402ca60004c1d5980c0d01c4081c61416041030000c401c0440d1504401c0306a1040068544c20714040040b1001c070001c04100300d20800204400030a4805030311000081e40c410307446a002001c01010240001d0b00c0201d01c110300004583c1010703024100140d020341074002565044 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 148182832 1250 148181582 148181599
    0xd03140a05040f02041a010306080c011407050c040e160518060607050106030602031e0c0f0418020403080a050d0b04060b04060e06070602030a1e0204060801060507030201180606060e030105060906 86
    0x1032a050f400c001c0e26500c0a9071150804101c1e180410000b00b41d8600e0381400d0305c04201150f030350134415846104042c942404201040d1805c40303460191070081010b40c3c800c1342565103807102ca40c001070403104e10b0240709489a0221000102164a89c004040502821501c0761013040c0c50100204180100500b40c0c0e025000c089890f1040050075007100015580c404815034a901e440d0000842d182c0c05078920b404411030400100320b824003004100d5116071113030f034825882c117070070110840305103031351109649241a4200000400b088440c0c0103845064070715a17926664414462584081e5480e0f4000144900c1c507003403040154072014800c4400300e400364181402401d003a40000382c0c450054010291440740000300300881c60105d5400b451601034808804041401e000c03044804034051405050046081140144000790080004c1c01c641442440042062948059011030b980049501240c0300b948996040c0030698020368516041181a80200030520702000008c05034100030300441d0080411 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 148184082 1250 148182832 148182841
    0xb100b040501030b040f1122080a12090b040603020a0e031603060c2a06050c0307080a0b0a08011e0608150c0901031103010806071d090f0c0c010e030c0d03140a05 71
    0x3141c122551071071105100b0170100001d4407c1310344a5001140302560815046c0b560601040c03448420020741c0c5400c401801010507075664260b003504c440e141c22003844001003000560350504402400a0aa543e07009030f02e8000105004d0841d1840704c10541c42a00110031240045075150b450708210b98001c80c1c00300d80080344440940d5041e6101ca00c8012140d2020a401406010384100c01c03400c51041c5420041030303442c0c0080c0e800c0e501050b00d1010020321607001044130f000d000c0c0c10060070319500401c070311441035464a0b0242140e0341c004a00002c11003404401000c915288105002845610003402c086c43c0310071125141d10100902c581034007400440c000c100ea1b40b0a40c84071400a01042c12141c1e6542c4a41d920707503440c08121924030001e000034000c0c01034241e1440c901c00c0e0980000e0803101d5162140c40c4c036003e900300020488a90440144242c2807200c100f4085c641c2c0181c0280061580e61840207012030802220391000d0040c5410311910400d45c02c4a503140550007220303c1c00008483c1c44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 148185332 1250 148184082 148184089
    0x50c0a1202090a0305070806070804081605010f09032003030106050d1d01060f1518060c020f030d0306081203040b0c070602070f0b01141f051b060c0301030b100b040501030b 76
    0x41c2c02d0440d42114081c034000c0100100000c202c4151074821013110a2030380d070710300d0840310b040c03080f10010607800d03041c0700811040c411664440c0c1224032840c000f2032412800480e94080f22200d500036000542d0b440c501e00000c3e020308041c03a264240d4540035621319818032202901c41e00c2043d2010403d02d41c0c0b01628420391211200742c2c22101c030700d40020704c005942d401030141e883e0518000c89403075441c45031112807014003c101c14a52841c280ca0484940c61500c04180c0328500c08504c16a0009904078007440103560a0103910b2800c00c290701c00081c100c1c2020082860440d0b91440801161000c1040c00701041d80c0894480e0704c1180c204509580e4105031920001a00440d04002d083ca03110b103918800308503900c0710480c1a0380d2250031240000d01903004100510a21921203031540c07035850040301c52184100010b0000000c3d910071f10890101284100c0c0c0340c00300450b8808017040c4084014810489007000380c68011543d10340c01300e100f5040015158040c0310f68810076042c159560180e44580e00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 148186582 1250 148185332 148185337
    0x605090703111905030a05060412020304050a05040e150408040f08010506130b030a050f030a08060301021c1a060f030429061309080d090c050102030f04180617010b010210050c0a1202 80
    0x4085d06440030b500051410980d81d11094030112000c1108040c9000d6040c80042514111000188104142894401407100a043d0361102e00c0f0a0301815070010048541c9200c550b006502c55400103540e2454801140e801202e20b070442a0640d043c001480459a1a05202480ea2007001c00c0001d10780e4441001a141c078080c110010b00b6070080350500b00d0510808005020450741a86800c2030300d42d5204105800c03485400c0b112004511101d0030741d5841390b10340d40407a1000703200b0071050640d2092000090680c0e0080c180f2409089400410402040510342901300400038030f00c60f0b4940580c00990407600100020030741c0b4000e84900c0038200240e8965081494400d130031a46043d0b9074021480c42d00c015103068407054820340c858200002d01035200000701c0e44800081c40140b8105800c00991501241b90443c60804654403074401203002048807456011003010040001489001076002904000c80b8040c0c8448003440c0030100301d14407a2000c1100e103180700320701d00700030101c164020002c02070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 148187832 1250 148186582 148186589
    0x4060c0e030a03120b0a030f03030522080d06120b0c0c0a0605010806151e040f063809060d1e0501081e06060105040303050d060e04080706050907031119 67
    0x500c52903041e103040c5030300466103004a1070740b000107014052142d0207111006000303210040800c04008c00400201e8030980c0302a40001e1003244c00b0842c80d51800e6819245030407407500303403485100007070000d0002d0307124410100280071041019108900b161102510b15000038410380a44c0000140c0405262042c802084c01c1c0358000c008200300e584031b081c41c070784d0744004948503c40039514101500c49031070a80000ea00c0c69110000d1000e2032000d150a20015245100740424007940f5000f001c20240c5003801006552140c2da60203076000c038401303640426030051450101403100e204112044640d110042107404035040d881b008100981d8400b0040039001d029444124a6882c000000c1500800400d2044070600c1c00e103014600c00c801c901c282c0d5111304007a6802c42c0452410401000024000c00c040e000d268002200000d080da51030300741d140000411a401c5522840001d80d420030800f052059641168440e0300400b86541160b8810042c0b400346645213105226481c900b050f51040c010140018 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 148189082 1250 148187832 148187839
    0x703110304030605010b04180e1e07030b09010b031c0e0603130c06080a1104120308040203031209030304120e03070e190f020702010806090403050403030c0804120302300304060c0e 79
    0x2d17036030340d00d030060300e2600103001d8060f6251600400708950202c0d03001d20040404014003a09a2030301801003da42c03c40521240c0d1f940b030041c500004003007140e0845c91b9202d0400a0008200c0900b4002018106020308560300c43d03803800050103826030382d4001070181e044541a41e1103540c03600c0ea00308800e10309140c00c500800141392450045502030b0300c400340b580070361a010f00501001c1d20f1402c2c602035600890203884081c401e40c1040d5000319200390720325030300980040d0603a4501b203c2405e4030015140c0c1140c074069682e2001080c801007203a4202c000340c85200307610f0640082018800000c0d2100c16a205120101c0c40c140d0100d500c040f14604201060324941c60304120180180120101940198030180d020030b08000c0080d4885c1800303440305124560558800341752604681e0181e4190610355015a54010288402304030701880c05c000140d46c50182c0c0040041d0407800c5260003403698040c2002c000b2110901400b241c0c42100c000b6a0340090744100045621160f0b030004075070140380040c0385a030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 148190332 1250 148189082 148189091
    0x80703060312030e0c01050f030c2b1a04020a0e0d050f1506180702031231060e030405030a030e12060f01180605060702010e011e020f0105010f0b07031103040306 71
    0x2290f415a02c08440751601a050b5450011135a005464502664441c00140c810410010f040d20300f01000410441046540c804143d040e0350380c00b0052011144025140350f079030f52a40d820400540482400d10040440d0b0941c600351031203000030190881a0074040c024200e880c0e10b002040700a120060b0300409540c11a98a4907010200003104401645c5560040d00301021481c0c0002c081c151880c0300700c032583c00031f500d480021110a040890028507030800d04150281e52000245440c9003000218495082805030340c01c542810390403508030200b20308083c2d1040000300040e8801141c505009501814484151488c44000c581d1350950420203007014000c00081041a010358402c0c40c0c10384803214030352501c0c004c0103000707242220340754007800d640302c036050003010010b61041c1a21301c840d00043c0341906186e000c3d466000a60500540c000f03015810030280031101030800d1182c00d00511680b094401c01d549401c900f408507201f00c80c0c2c007070104601b040043c01307003d034100110b40007958010000c02 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 148191582 1250 148190332 148190363
    0x10905060f0a080618070507080903060a0209090f090705010e03070b0c030a0224040809041e0c1107031e081201090b040f140a020d1812140304080304030807030603 72
    0x780142c1c0718807102d0010444900204445003400840e880741c0140e450040301007515558002c7c0c5440d04202e4007203d940328100401803543e1000e00090f4080e1a10400143c0c42e02c11480c1045990100140204804420351040081400001444608a440030b0810100c0101c09001190506030380350040f8151410008144541500000042002151540c2a2034041c41c075621b0b5007030403501c1c05484c030002c000c000c4007207008110410002c044c40d8074003e2000802540221200122980c3c0c0d800c843c00c2d095464482c4900550000c02222468603480040c0c04040c0c10360391390740465180a0100c1e501700c001c500e00801084079440845520590180700c2c000c80d581c0da2002d203400b4101e144991406542860403080300c44690340168a5a104441074600450b0b68840da40402500003541410f1140d03118880f24540620100525140030700034032010250b42e0034041c0c00b5102310785800e0040f8048004204001c04900c05206a0760015894502545580c9418908401a003056040a440c4400c03800310714 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 148192832 1250 148191582 148191607
    0x303070212060f06150a030515130911060a090e0c090901080d0207090e060a09021c08130f060f050c12030f04171309090611040f090e0d1d01090506 65
    0x90b200c1d00d1041143e030a550b03242418891032480002d030303041040340d05006548207107009800ca180c0c40203401c1035011107240402d0028121a42e6081010a05c2e5a100001ca042c0616410000000039054500c64030340030389004000c002c0c0d880c510030300072000d401c1c6011500c2d40081d1000c6600382c43c4002c0c0014040d5860f140b030301d51076824594100c0003500ca445000221409140106c0c140068040050025942c40e150703088060100144200c3c0d025203034104a406074220161b079840c03400d000350112601d0b07640800c402103140e0710135040540110001a010030002c2e500101031a8001346500e17013242c0751a40041d2803441d04052651080c1c0041c1c1c041300f000741c070701c1051404a00c1507002da01c000003800791068007150688520a0000020b0f450900b00b4461482160002c287d1107220302c40010302d81e1040210305981b6007168021482008a4100c20880003001f80181c060107404040174203c20880300102804258040800d01c1443c0315400c501922607006880c00001840081c02d402e0b5101410105c1c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 148194082 1250 148192832 148192843
    0x3040302030a021009120f18060c1104060e0c071106030a0b1008040b0a0c020319050702030d030c05030f04081e04170f0307080913020a0c0c060305061e0303070212 72
    0x602c0041c8511003207000e64012030301440303605035007000d1200d51303a01c040241201d0312090303948010b00340414400100611044651044010300003a0b075424000340881c900b03502e482c09803502062045040c04000c0c054010704080300c64102020b45e02e4617039103400b42c0c40d00c411381d4003072451010341c4030802108006501c11650058800150103e503c20081c0d0100a070035114100309490203001000d4402c00a03421403106d40c00b2520301210350048070305010b441011250080140f4440c18006440492450114101001074200609040c241402441c0c0000070040013404010440c04026443c10003040500548404031100c149100d50303040b21107894010491007a50140c030035400e0301c120f8041080304000000c540c000403840641e014501d0001240c07209815034100007200341d4041f001103640054060548020701d041025521448100b450034100820711884035800703c000c0c50b00b0601080025600d40008841d10300000d240c26607a80c0c403120209145004440d402908071481c4042c407075019000250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 148195332 1250 148194082 148194097
    0x20c060403030b030313030602180d050304050306010e07080402040911040f0e0d020c0d080309070e01030b010f0f03050d12020d090f02090106020c241603080f07090602070504020304080f0304030203 87
    0x40a000340a030100503d50340c1e06c2402d032000a150346280040c00010081c0d00141780611540300d50501101c00540000c43d003480c0400304441560000904214a0801340600c6006100e4000b003d0700628090710040c00b00d90005200030b01c6243c0d039034001010802d07020b05440c0c24110140080021000d5a802c0b03000901149244602500c80c488a038000c0d94400108a0070301d41c00501541040030880c1c0c0c94403d10380014104000704c1c00703100710229152400c60300c0280210b0094421210551400785080004c0d15503800850840074001d10078030108500080a1032140c54501e42481380b098030352020f500900441500e416418186a800824000c00d02d0180d005540225000070059a90b03000603680c030043e001c1410f40020200c0f81048159a040200720f4620350041080e626203044c182c580303010000201d80413804609074000340644082010b40791075100b92581080c062190528001a6442920384510b41c4240d40002c000f60801003007000791401040304400e41038890a0500e4007070340f43d0f0010f0b82d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 148196582 1250 148195332 148195337
    0x30f0509061e0711060a091403070b16060c02070506090904060609050903070606150c0b0903070b0f010e0601211109030307121d1c141015080307050d0e010c06020c060403 75
    0x454807840c3c03404904507050708845031501002c55242c001c0030721232903180d4045e490b894020702400145101d00d0350028441541c01c3c81007840740800c02d10701481154014850001150b2092506000360303185d02044482c0404100c600c50070560f61403500c00042d103516041a8807050620040c00100840000070342049440307841c040c0f0800b601c0e6030041d1100c0d500c850002000401810110f00850b007010041030700001d82c0003d89142c08126181c0480041c0c046d100e000c405c1c040e0000400805217403583c043d0701b1003001d203032407403a510442c7e0240c030400701e0000241c143e4664680d0100d84441c000b5088614101e000b9050b02d49441c02c504009080e62003421000e00841c840061904210b21021002032a92400800048000780f11003000110106152411119440c044998101c444810065105071081010000c281e0402e1500c915180480a600401e4164401d10142c00092001300d089000c071480e42c078000250718104d800407540700c0c2600c2005400d0500c0098003a0401d04c02140030351041d0301a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 148197832 1250 148196582 148196603
    0x30301090c0e06040323070303090906080f0a1103010b12030a030e0a1e02010c0b040c1503022d040506040b040920090f01090503151602030403030f0509061e07 70
    0x1c01501c801c2806142207030b10800800060001401034242c4200e00940300d0440e45140c40001d0007030303107003801c1c81c0c0044e40400d0081004101c04203503400ac6034041e0004a001d004508020034519a8410968400410074107440c07084103050740b82544038040000009103a07580f00d40c0c0e80d0030017949070761003101480c0010342040d04100c034500f0001010342d82c2d16404584800c40e4444240070585241149904034104040c203d952000f00d026407185600a44c0900c94200d0070078134201d9014007085180d0510801d05006008080d00f40500702004ac010518403510100c00c1c10f00e286200070381e8403c0d900501e521400114020500d903071940c0103841520403d00d000c01450b0a038000021034140c0784078401d84000740401050b80799003401403c00280c1241030601c41c41668640000900b004610011951a80070b207504002090003840c02c0044040c0c100d00241d4a003038110380380142403000310f40b90101405000124051241c40d900300326034511310fa0709002640e0411007000c02e4256408980c096a030b22404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 148199082 1250 148197832 148197851
    0x13050306040209011a0f1c06080d120f09050a0b041101020304030803070f2a02010311190c0f12080702101b0e0a0b031f1e0302090408070c0803030109 66
    0x156181c080c1e900200404210381c40d160000c00c0041008179550f07103e1409200f008450922113010f440c1070417840044030905101203480c181180c402da4000419039011034030aa0106420a0030784056544411021900802d6880032070090804a45c1c0141284204100c2c0030078002001e036070038010f40c403035107001c0f07000305482004990ba070207036001c041e102c0c1c4c01c01c1000c0303078403d07016981054a00e080390800d9110702130303012244000f2031180441e80c0c0040d0302e1042e40c3c904541e803610550824183c1a90900c3c141070300c0400340010032480b01140c0d0180000f030f1940800380001003412000300c960003180a185080150401006580107407030b81030141c03084030a80042d20340a40900c02c6a1503400c182010a0a002c0401f03c0e400319003003100c0364000003107030b601041c1c580c0301c44003d40c49a12031940c191303486002c20b0040d440c4900980c0c000380501281d07120b10f0140210304600c0b0411a0380494030800a6100d5082180c0d051244500042600002c1c8a0000e5a918040080c604a44088404022100b0b8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 148200332 1250 148199082 148199089
    0x40326040e061201090510020a091703120c220302040f0b0310050c0c0a060b03160f0306020f0f030708010501020c030d020a0b100f09020d11040602100911060706021305 74
    0x9240540c2280c55110070001c2c60b0340c180203400e540480580d50002c03950411607210f090900340c070503203403800e003980008160303039400d4010792445c009280e42201c40180a0038000d50548074003550240b588101c003c100461041441c040c165003512101544006c0c0c82c01c20a4402c492100f642d00c01240510700700700c20200900214441d00c08100c0f00a005003801003c00e441c40e5005001c020110414101e0034007240940c01010455040b095101d82000112005c000d4101440d100c4445040020004502c40911004103c1c518907400c5179800b240c05612440c2d032515005150094951030f100c03484003c03042100643e440510726040714001c3e000c0e41e0501001c40705050b11103070b8003d8002c0c003684c0101d410000140c5081d0400c1c1e44000034942c0081c6044c0c0350844c002c2c6958803540180d01141d008100f507c1d041ca00d505c01e10754107201607020a89024a003038806504c60b20b078806141080740d91201004144007110062800700c00f00281030742c0e0307a400e080c50014001d40194144001c0006041030104003801c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 148201438 1106 148200332 148200337
    0x130905060d260a1d090c07060b010e0618091f0302010c14010203180708010204230f03100903030b090708220209010605030a0c1d100311040326 63
    0x51102042120781004c4c16003140c420180c034000d00c4a00c202c103400300d41150f40d0000d404200c1100c00710040c1c03503044415007002e401000c00140068041c20040d040c001800d0100e500d00130a8071400c0701451501c5103000d035920400480d00d018000340d0b000c0c0e10035045640c07203090122205c002d030701000f40c20ba03001074500d140d009110511103030441000348945000340600800840c00c00345462100b61b01c10013201c403544000c0c050101e0070106034540c00b070380e410009005402c4031b144902600400006205210b400d400082ca4000c0e15905458103007041800f41506a440040503142c480d203a108100c1c5020080a8612240f441a4016100c1d60407083c0200542d4581c15100d01e0701036048004d851000c031840080100c088a08402142d840101e0550900290b80c07103c10588080025030041c2072201d07051101d15004600081007280082e140610384016a20850000006466500c00790 = true := by decide +kernel

theorem cover : BRFrame.Cov 148021582 148201438 := by
  have h0 := BRFrame.cov_init 148021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 148021582 ≤ n) (h2 : n < 148201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
