-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2661
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:22:11.918046+00:00
-- url     : https://prove2.me/submissions/8abb23df-3a0d-435c-b249-b83496242217

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 478417266 ≤ n < 478597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 478418516 1250 478417266 478417271
    0x1201020702030d12050a090b0708060312071a13050307170f040b0d0b030c0a03140c0603070f030b03071d040f0c0b09030f0f06040308040804030c0f0312030903020c04020d 75
    0x31a5000c2424208070441c10f502058010b0100361000c0114003034140d002070341c1340007005004105d4449112050020f41994140b2105101040d507035201031110901d1000021601c40c3ea0b8240ba03e8050002d94611000c505a004114007046001c040c6598211410742c00400035400d0071a591210000c407052040101100e1404100e0f02c03141c041030307a02a100030010303803415030b0b10781d1010941c00f019070341d007482c4051003500700c0d5202d00c041da038075040b192095070b4010b0f102e08898007107804014940904000f9080c1c5c00340002c03042058050b4030000c009030782042a5028008001d4050070b02d0b90751052802100d8401e507500b00700ca20170b480d108102c180e0080c0201440381a040303450719080802e01c82c94004d004044000a0401e026003420428080d4003140100100011020440c40ea0b0702c84102500050030400c849021802340b0503540c05039005160040c2c1103200113940d41e07045211909803448119080c1d40f21551450102d4024410540340540540290284406220410000703610030783e0501d50065 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 478419766 1250 478418516 478418527
    0x5090f072705070e030f0111040b0a03061d100e0c07030503130f05060115090e0105100c060e01050106090611070605030a1e0506040b0628050d1820090105120102 71
    0x1c16002d0103000303a11944031800c00b82524418107040201e01c0e20546c0450b810a006142404049001c50302198401a28140c0b1000049812000b9020305d81c045400c2d07419001c2c21304207441d5207415060081c4440b00704401e00356551454901d030b8180c1181e112044c002c052142c0b4022a00030401190b10040c0c0d0707070f5104178151080c2d031004404001c001c416203c0e03038881070040c000880c2031060791070604482c0c01c08241151404c1e26020303d01405004072800f42c034048401c4d8501d01e029052403813a2950040c41402801140c03101035000382024841c2c00002034020340d0005005025005c00302c61451320902401800d03086c400c06072001c0d032014165070403056503849210080328801c140c0c079851000c60f22010400f820603204100c00c0d140c551034414032824003040154040039400880784042e03202101e37410142d801401c415a03c600035030201241d41814840396a402c0b007010b048254030540301d08410140b943c5001e80b4180d01c4801c01000503048143e4400601503480c3c00343c80042d00c80224000940b900 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 478421016 1250 478419766 478419839
    0x604060b041d060103051207150207030203071e050d0807050a08070e1201050a06060f09030312090b040302030702280e0c0d02040b04090608010c0c02010e0d050615010305090f07 78
    0x3800701082d00e2401d4110100510401c40e0504c5101807000c0c0d141c0c40f09080c60f009803551102010625a40303c48554001032800416009101b981c040d280c0090034509107445025032213550b400690030450703c60083c0e16030400f540c3d00851445010b40c5103a50f943c0d050078217000065400300c001420180070b110055000101c2030340d451000c40c280c80c41100010901d41801400361f011b0342c5091700138009000c481400400c4c41980240b890080341d415140400e00340c41c0c101c1145009005800c006009038524000700410303d600000100a8a0b02c00e5034814030044a281031410b01c0d524180c1d608a0440504904003d011400c411a0b50048443e5841a01c2c1005404440e030032030b4011ba000d4545084003003010041c0810038450f160040040030000c1c000d041c0044401031100064500003414411101c00040700c54881d81c108050481d80701040311060b042080078050650524990180041d01b010005014600c0206410080c0404003000b07100c001e06060420b54950b4000c501c411002c9501c3d00034035940d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 478422266 1250 478421016 478421051
    0x501061b061d07030317010b0a050307090503150906070924050c030408060610030603170a03020712050d150b030610050d090b06090a02180111010605060414031606020604060b04 78
    0x642c0d00c0b00004094180c554035014260105000440c0e42d5038034000c00401400d6246012580e2082031440c026a0320303954003502380d5a4455507088283c240c81144082400568895003c0e401095068101d80c2c83c0c0c0d6491004885003800c0b801194200910048aa112980b00314892443c2c201942005800c0c41016101c0034a103400ca0340c0510020303032111060000b10f04107035035000c0040e03405150501000d070940d160400c1c820bd468000310200c000c0014000300080c443c0d4152908194440c1000000c81c2c00420014503e400030010030b2001458a04401c0b000c6003003882c8142210703401313400c003030441e500c050030003411241070380843c801d00000300301c0c85820310710611500c0c00c0d00344501c9a017012420140c041c0702486100824481d091803041014000d40035441001c140208002d1820081c4441071191840c050131240e131165411503000702e80403614074504030b02d00002c90400d604940e01121820b810003c070401a11901c409030f046480400d0204442d43c02440c1c0910015002150144a00507484103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 478423516 1250 478422266 478422311
    0x311100906060e07080915130209160906110604020405060a0e0a0204030b100e130507150c050c01170a02090301090c0305010209030609210705120c0a06060602010501061b06 76
    0x1160303a03403001e0500241c41c1003000290071104c1441c0c13058141c40d05c941300da659941c071404070b001200300c1900040e9804508103051111668090411001030506041c0405210380300c103402400b25028400102d901841210419403c40101700106900d8485401340030003498060b0815401c007801c00d001144404101d0451070103559a40f02c0160b071603103075080402031458043c182c4541070496039020400340c00c07400c0300300740c0190f42c600841c0f201c07010b0303132500ca0701c0d084480d4004107070746210510034411990000005900e141c00b840c10785603007128200045030728070110324009000d401c41d03c000c602d0b0b80c070556001d0710400d100a40006010101604c40b80d60610550b8000c0b96141c0d00002c045d0030905081c000030360080d00e05c8008011150105c60410010019129081e58201002c07400c4018041d041190882105a00350216911000d8400b0103485071525403069a03c10705010780051080d105201e0503048400603914120200c81d90b0030155120200f0010984010342c58072040d019540881080c0712 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 478424766 1250 478423516 478423523
    0x903150c071b06030c1403070807020a0510060302010806040c0f0503100902040311120f121305180106091d13140d030b0307050d02091501110a080a090b0a090303111009 74
    0x86110f443c2a5000701034400c0710f0411010419100d1880c58139111460075603070009a103003400c000b42c0d03817007407422442d20f204000302a02901c25600601000d5525034000c03000d403130003030b61216400d64130403080c04240c651031099040080d01d5080704049042c4118003039034200314138204000742c00d0707900ca03800c40c01c1c0e03000303900309640c40c0c02071900000062410100881c0f6501401019020380f07404001020b032501c60b12111049000e0300007034449108000d58034004040e040052007186455142056003042c03500c2400f031540443d1502c08041808110700c01c2003da1960a003080740510343c1c2c2c45640c5061800022022150781d00310066a800215003070001110141c030a607000503e02060000b05850208298019030007050701d00400005a101c020f080c0390300020050000b01481c288100485d90100034800c0758bd0700380248500303882040040001455280b140d43e807090700050700c500d50f000084c03080303c2099001c922844410000240500d40e58807480306508242d0b6094441d03840307042c043d682c44109c05c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 478426016 1250 478424766 478424813
    0xa0815010510300b0f0f100c0516080d08090c010c060914060912040b18210327030d120609021c0f02030402182706040c0b0903150c07 59
    0x2200201c00f68460007080c03040459400204000d0480440c1c0010078800c902802496481406180d45010b250041e456580c0078048407003035180b84502d08502012405035010303600804040c0700c1550b10a20849001e1060240500b000101010054480c0c140000c012268203440f4409800401c0e0345130b8440d8214181840500198a0b11803840c034188000c500b00303103103048820b0005001c0107410742c00baa01c401e490f010805056511003400200c000721861850032210002d56041a1603100200c0078200710341c82000d02c0c40044000d55001c025030901000103507015440749007400030051054102800311800c185e0006002c548546800003683d100d41540034442c40f040c0d84110036951a03106891403c07040d01f05c11406e40c241640018034541d50300c4880c903109082040401e0003e12900c0500903104014107804000b100000c100e25180c9904480030f43d1100400e902c00100c0e10b00c40030445610050043c050704907400c2020400003001c001620f0010b80240504c042c200081c090f18a41070000c50b411200c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 478427266 1250 478426016 478426097
    0x3091502070515090319050c073606030b0a0b210d2703080a02150406062306030601050d090c1205070b07050d0807022104050a0815010510 61
    0x703c2c80b6520081d180011641c8200500d042190808480307500010381490240c0e583e40540111a14200c0c1a400101c01d000160055115882e40061025040c240c40d9203064840030144804108603007882c80041c05041d055000245d0300740e140da002500310302c3c008010700070804032241402c4c5214646401d0403010760104c80501c01d91500304051a04540d1060101c80c80d02150030405212100d051000810919020070658100380c024081405c0070040030401480601d850b0034840060501c900ca04000c4070040038000008042203003070700002d07000241405140d51980001101c0b40d6102d02c540e202515603401d5042e0000361020803001c000d2109003003180f50351419041c41c6040900c20340c8440b01d40e00301080410005072000c500b0b40d403000c1c040d06010950380e5030200160706045030f80c0c1202c43d00040382c030b040ca043c9403085000303001a181e042d184e40940b0b5440f024000d0340c03102144e20b103c100c900360b040108502e181c115445c50b070b240703464603040641c070b0383d49d4400103482c5641b100c2606450804912 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 478428516 1250 478427266 478427293
    0x80405040b0406120f032003070c050906210f1e0705100f080a06080d03090b060d020d06050907151d0a0e0a0c0323010f0b09060a030915020705 63
    0x3a1003035985080b1400c1001610788240c144210b004808014030700348290610b02c0a050017403c0c5c14104115401001da5190040d5a030031361258801c1c041118a0030300c0001c0424039003008102e00d80310b6840640103403010200c009120304c00c00d018102c02c408030b108400d6140c0000d00c0a015041068045601c0103001c0507412000504007031882d0015406110045200c03c20796a0000b0f0410f0354540c0e0b41081c0c0300030344540121101074406500305000e50302c104c010101ca0341da494ce11a010b9940a81001500e50300d03404200f140702d0b207290f00080e500081c16550703500411169132000390804072800072141d4250781c6000b0480c1e512208101d04001c02e001e0191818518101c0f000c4031040b18040711003150340742c2003c00f0312407101409001000002e9694002030b0402e800396020001000100094052761840407a88040c0c468090080354203c0000b404000b44d444405410b82d540c840006001d68100581000228000c041240e0144c0710309100c2c030303408481c0f0704040c801080c03040d0180c0090039100700707400d9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 478429766 1250 478428516 478428521
    0xa0f020c010e1f050615070614130204050702030412020f0a26010c03050403120203070306050307080d031104060c02060c0c040609020a030e0a0c06031802040f0501080f0316290408040504 82
    0x81800a0900781801c01a0325131b26070a1240581442845040d124501c0741030450060054007e1112a03c50380700070f0180d091000410301081500c02ca40c1408243d039140c000302d03168041c80c400c10f9010001424240c00510f0b020304100c09140c0041e043c0580640d607075440303803a071000141c0c480200f922082d2000c3c25550f028041d1010962003414280824246650001c2c020ba401000340241141c2c044042080d00e0f20a40041004060040403a50800c0d12000d040d038640c0c81c0740d0f45000c01310f8030700b40c4c0d62540380c1d000300165000c40f0503a88815803554120707000d0040305c0e88080005c113058011000c20301d055649610900e00a0300b101038006072101c03080c1c0d1002c1c04032204103241c040a640203010ba900022800302412050340c01d6480d01043c80340e40d01d03a03107600701c0a03d2240203500900740203446040707445560200e0304950000049450404010b071481e42c90f8071420034004681c1a1500395800840c03440b1050400092800c0a1610340d008035104a003031580c0c1c1650304569104e030000e8200020f20b45030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 478431016 1250 478429766 478429813
    0xf0204090c11011a010c05010b0a060f09091109060c160b04060813020904080f07020d050a050111190e01110d0c03081f03060c1103030106090302090c030f0a0f020c010e 74
    0x200c004c120804610007140c182480745003105040201d00e94455042000170341084450490141803c1c3e6000e48408018212402c508412000540c020100082003074560091010b88184401c000c1e103001100c40a11606134331a00000f2f201d84030740030030b0400003082540c1200c01440c54403c610b8885080840082c803680d07000d840c4403413111114010a02580d07818001640056001c9100c0750340e4201c90700300700310034061483c01940c4a140c280d03481c8148140481c0840029101d00000c2218040b2440045c80324000c0f160207100e440c0c5c1c0741c0402c4914070b001b85480705041c0390504010025000c0500705a25044006c0a100d00080807580390303c082540121115800140c0f00c0b225440e00f15010030104082e00329803201906039038842c0d000300701d40f078000c60b1240d01c0c480420041e2a035031760b101e44020f024081d081c40102d00607400b410020f0310420f1a10107890207080725828504440d118403545102921b07107040d600c0552503080088040c402d10910a000814011102600c200c1817842441103100604 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 478432266 1250 478431016 478431047
    0x170403050d0c05241501110a0c050f22051509040f0c05010f0f0e06070b040b0708090a020109090e0c040524030c06070b0a0f02072a05010f0c060f0204090c 68
    0x80071342c81c07180c8034103404d4194884601e6122600186a01d40120f0780a0031401c00d503e05801460408014020b02036244d0381550360540d8224501c00c5e0720030a03c4060a48110600a08140003d034005040f0494100c0c581054103980005841d8416000241104030140d404413613050700918050104040301406e10020032090900d168404425480900200b1508240000b0410005061b480302e40d9114162001242c109000840500d0980ba244072043d405582c1540458030100c0094618030b030002c2d5a05071683e0694580c000f0500c0c2c40c1c034000c05004490807a840c64020401c0c0740c00315440398441d82d84101a00301030201203810744075050f0040100180c1d114020741100e0360004542c1c55603400c89031807640c8551040c0943d0345800d144002071038800b04100010b4000101581405500d2408d50701d5003140145007101d0000170300300354114240c103118081c080740360300c481c07000a517004443c604512030244402090800300c24514404a0303005810110a060780c4401b164640c96000d42c41040c0e21a0703 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 478433516 1250 478432266 478432303
    0x3041d0405100c090b0c1908040f0b18090702010b030607081b040b0708030606040f0807090612020f09070c0602030907030c0b04140d02040e0f010506131503170403050d0c05 76
    0x40220009141d01901d0240f074405d031900003162005a4010410b00310f104e20882c0320681c407102d07a80307001c0215074414810303214002d44404010424050400440b03600d807003205004000b200c2c180301400f9114000804041c29956101c040b5109618107019580c424046075513880e48924102445100d414940251040c1440d001e210500007a00d1140c1210f1303034541c115400c0c4d522031340d801b00060304520858114200348041440c002030134040c0010303100160350710144244100381e12105110021180300d00083c1d440a4010179054840c03e224490b80e800c00c4451410001c80c22031600c2e0541641e000762030205855002610070420322440c000c0c200d002d080ca00c2d00c107901d410702e00400c0c0400328030300e82d0a941c85041048850011599242c1c06061040f800c2816038060607404540c1d14000c00045030164040c10044d41c095055020354030440c402e118007800500030032401d41d201c04100d25071074109c03039130704900c04c00001c008071f2420440302c1c4e070341e581d50368802ca1040907503d04281040040b1035803101d19407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 478434766 1250 478433516 478433531
    0x209090a090c061715041d030403050c221113030809090105060a090303030c18061d100c06051509012907022b12021614060703080903041d040510 64
    0x14441320480d030030648545020764203101c990b0000e0010070140c41808480e12043d0790307429103000c01001500441e401030041e1390400303400700117000c0c60031800100d4840100900001d1000c1071450b9004200d071403003121065042000b0782020030465803a03500150b0742c2120102d080401886d0659034240034100c16660b560500200c3c0303002905001c090b01000b000e241c0c035201107142040c07244180b6030940310340744088004169120b1010304050007080841b070b42c0c1022610004243c5c00d110b02032400b280f456940e4a041424561280e50040001600c00c0d0f48800404d40c0300c05080d941c0f05104d0b03010f01004020860a9862082454007400c0f00856420201c4410706c88180560b8801c04007506200140700d014035440c580c03164011440414860041041e03417a04c070250549a400640391002c100c401c90440100d40c6c03211268040150702021240c0d010b142001351a0010344035004140d003081200c012a4206a03d41e0f2400081c00314802c1030102c0c08050380c08120a1040c100242840181b4040c3c0070441c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 478436016 1250 478434766 478434797
    0x1905040b03030412120c05100903020c0901051f0203090d06050f0f0c0414040f0606020c10020609100902011106070e0a0b120406021c090b06030f1f0903030209090a090c06 75
    0x100c440c55009840702c51030030403282c0700c5c60042964040d0b4507803000585040f00801e2030741d600100300c0c0340000d40040c82841800e9025040040d209416104001c000d811101921101d0140107149000c00200718002809454100c0e01d607804d14004841c81018041035614006400b4030350404000d08181e01d80910740d05012126024404035401e40303c1c03040e01c00094801d07010218002e0144640401031440c60b02100081080d4082020701081c08210380740090743c2c54000d41280d075401c00b500c04200a8100b0703106002c44903426400b0380700c818818100b208040c441d9014080c10301702c044038404003003400140c50010614100381400d01070300f000342c0d200e814200b078010461401a0f0040004024a03800580721038030052071461002c01d00c211140501c40c425a038a000151003005592044c001d1055000b16902d06002240300c04a1101320174614041704030400d07481c405888160f8090307003071590821480d00c0c03d071240310110f0720440b840380340030800350490700e00014184465800741d4108401121054003c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 478437266 1250 478436016 478436039
    0x1410050901030c0e060304060b03190b15180c030106090605040e19061203051b0c0d1b0b0d09020109050f0f01080405100c08040308090a0206030f04050c1905040b030304 74
    0x2110081c60005001143d03c1c0064a220414510a0707a10500c040100000c10907144c05c042c042100a40c2a40e400c024011581103200341501d1000b8010b1b04d40c04000f40210790840003e03217100c0750082a00700c006da40162084031f00c0070241e80214800c0d5001005019882d00300c2c0d23002c4003d00d81c9141c0285040d180031a4088040c1000c0c02502505620400c9100c06000c107800c550082c00841144a104404a1030b000d840b980c852504562203a5411031140380c071756408549001d1400300a42100820400c958994143c401c079007468506484200e0008034130003014501800240e1400100000e00d140300d400090030300400c81c2d010030f01c5403200d50301c0b030030b0a034851001740d0059210a0801620585a41c503005007440031441c0c21512607850102c041c1c1021b03900007820b600690181d00c4142c0359843e5000951b0315078800c0300010350010000c00c0400c01070f80a001030700350710a00400035251030300308107000142c6104400d4480da83e04000c40c402807003070780f03800d104441a00004800552403d0320b48002c0302c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 478438516 1250 478437266 478437277
    0x70e010b120901150909060b0901030b06150f0a03060e090d05041a090d0503031902160b06010512092a0d060e0a08040b030f09030703021b0319050106141005 69
    0x111007004102182c42c001d402d420803000e84100719545482c0b15103c83e2010002d2200d058141c40d00e030b042c02c12660b03641c04c12024050503039030000c60b00000ea81d6484140f0800807811001c81a00e402c080140088421207180039122101307566401041003445c100418106200203080750f501034008040c44038109070494100c5040328402c6400c1e220f17078600343d10500e8041c080e00b21400d4200714a042c1520030800040011403140c08140032030480120203041c0101207001c1c60508070012601e00c0c000c4000315044008040c0e01c420305140c40381c0ba10516554404030705005854003441c82d403101003014030780b031402e401904c3c405607808080000112080009508400040b201800c1039a56107000d41c0c05110a00009000715044025650360710b9680803050740315841140c81e01401440840890310881000c404c5403050354065000345000700103503103a12980503c0c4418507a00d481154480b40c0e0990700c00a0034400c03a4052400000c1d05890040240b00300301c000e00920b40f00700028000038607d40d800800307503203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 478439766 1250 478438516 478438537
    0xd15290906100e010c050f28030c110f060d0e06090115050f0105040e0c070203010606050427021303050c0f0102210d060f03051b01020303070909050405010204050918070e010b 77
    0x69200d070050f60310f042c001401034000c1c003e1044000c1f03012000a00c0c013440c030400b04043c1000280d00d541d00900c021a51100400150104103d880071469408158490a038014001100714103c10000740d80d83d401645100c40d800d48800701040180406c1c000c44d03501920400003809140c90307018440714034586078003660384200e41d4050390009030b900c10b5042c0c402405260020310207a092502140c8002c4c2c0000c2d504074407a6003403130750118855210f40140c508907102c00c07031102c0c04010980b40c4203c0c0d9450f00c111741c4984903030901030100100c0b41c500194005500402c0603010000030780c0c0c140246142c00d850740c030f815948803840c1c207076801c51042043e10002942c42c20868031200c5c00540c0030090200e03940201d00402040d0808010b0240100fa02401d42c0241c1c42c01c0700c0c144101e200166200d000c201c2c0d20001040c405c0500700a2860319400461b4000d2041000518040d1120b00003609540242d400701003a500010001074013200410907540900107034030391814151315043c000390380f9110f18259074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 478441016 1250 478439766 478439777
    0x50c0c120d0e0607320301050d0302010f06121704060e060c01090203060408040602010f06060207060509030f0328080112080a030b030a06020a03290d1529090610 71
    0x507036007819540010824502482680e0280c01c01d06002400c0c61040342c22030310404010400010901c3c6001c0e020301c014810309002a00310b82c6402e00b0041c00c0c1d01020001e800395500c82e89140c1802550f48503107400391651070008082440c880c241172240c1032244502518004c0c0070001804200d400c83c000506c407400c01c543d0a941e800d001b0500b540985601d2000035098802c2d881403104200114020b80107548555000700f081600314035111046e075000d03100741c001503000b0351824130070588118020407501c038010b07044941d500038130080149150f0100362041c9403204809501d100e0001100f448103401c84c11407400000755410b150240d03001e1140540c00030000a0005460354a9a0294224100c205c0004081d10100451420108045e60084900c14000380c68400d40e2103407000b104400c40c40f80704110354000201c2080009010381445840c2c0207035060f0155480b55500d070101400b035044508200300b01c103890105044103000040c0c058070109403042131481d00b00020341d103903900888524411440c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 478442266 1250 478441016 478441027
    0xd0b0405010e0c0d0809150d050403030506010e0628090e010906090c09080706030504111c0b091212070e060403030507020405060a0b1801051b061503030301080a060b0f22050c0c12 79
    0x8a1010388100230220044c9824030701084141501a0701240c0b241c203003030301e608240c01c2c042010041c00d88103100c40041007150001444800d02100e030b441407500f07041d80c20b0518a103521484031401c803141c08d070b00030110540c85507400d02600e5928004d2031000d640703500305080d4460400000e140c541c40b1070b00409040564540001c0d0a210b8141080219002c000d004140450b404500b00f000034003913040191544000a408030300030394000141c11405000e018003c90400020151000440801a2907001000015841c1c01a00d999a074010700041d846507c50702e030380d40064410b000a4680040c075452045003010b00070804005003204469603080311040d03001e009001d000040c1c0b0742d40519003010184003654014460480d0740000c0d00da0148400d0341c070745240800e9020802d40d170391000740200c08442d08071030380040000b180c80c4c1020110b0b1030014080c5502c020041c1c00b04001098400c1d00704104442d441c00070f221040c107403141c00d41150103800154a0300011410040d0303512040c800120300507034000350 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 478443516 1250 478442266 478442299
    0x2040f17011413020406080c01120f060f1d010f0e13020109030605100905060a032a0302090403030504030f0804110607060609020708270d110d0b0405010e0c0d0809 72
    0x800c08000a000c040c902c95414901c14802a400300da10049000d0343c58080c0105c0d51000c00100c85010000c169656040305080c0100200903121300c0380520034a40d2a882c0104400380030015060142403114032010a010301d102c0d44003900041030b0302002600000100c240001030140812680c8110380681c1400e06050b00d20040741c05119950001d030400d4501340071700501100c82c00f240d10484400030700c14081d50b200c280410407540e40d2480010800300c0c80c87c005c404404074100c40c015808014800010009a0325004502d18040c12601140002c0e5039a0030001015040500c140e02e960403482c00300300c00e01c0d00c0da46100821220131107003489024042800420404150400c3c005041c00b14410764a070b0340c2c1032406840311b130008181c00c0780e10b24010b00c0d81403401c00b220003182e0000000801c9004444001e4071010b40404090884a030403516403807406002c070b034904181900492060000144040c05140f8103030038180340d00d500304e11402002d081407020440c480701340d40c01d800c0103e5010085001880 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 478444766 1250 478443516 478443521
    0x21206091e0a290c0d110c1509070305010c050a080a3b03040315050105060304030c060207140d0806030f030901210b030a03050306010909020405061e090303070b0105120102040f1701 80
    0x101402c01c0381120704000d00381c803050005d0980c28040e0300080c043d403072016203010018083c0e2102904103610403041e5003e00c0340700001c61904000840141c03550b160712510340c5420340320140c464201151000403400f900651001032a03602c540110380c01c0010582c2e0040800f41440e0314140825460b00c107502c00020302c00c903004075502095500040301d64031070f80ca250940311804d0440041e0340461528000242d40d003042406c90340700300e9040d9a503000e00741c00759507507500035000202c00f0345015924541014412904120700ca8820391140c0b1080000d290680c1003501d02481182d80307a03502d800c02c3c13052104a90700107081581425110460f0307008000d0f004040340c000c0c05008030b003540c18460413008005264006005500407402aa03c1c2d100c80c2381c80d5002402684124410140c0050082283d42464400070300840312040314091003c4c5001c0d41c1c400020720396044000c06a0302492440d0040102c0c2c9081130000019041c20700003541818501419000742c180c1521482c94811600000344080303800c00e6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 478446016 1250 478444766 478444823
    0x30a0303050403051b070f090510150203070b0a0506090702120702010302072a03050601060504150f0e040203090304090501050d0c150c05070e0a15081207020d021206091e0a 76
    0x2800080c01c0c48028408951b51355055210302c1c40a181c1c5c0d800042240c80160003806d201e42d03001401c0035200740c40e0254282c490f4071400000c034110b000901092002540c29400c841c01408281000b081c03a0410f001000b2150002030320140566000380140102a00c0800694078115024200180c5034209800c000090071f070094818007a1820300c0f0107a80c0520800d0104030203807801042180c0080c0e0300c1325020351380382c442c901403c40c243d01c032842c04460b0148a100040841205032a00440325460880440d003a41c006407801840c07600041400d0040d12b00c1446180e005007811030305090611120780b215482d180e0359018005001c005002079440d07582c02001e0300d80d00c5a80c8001184c415507621081da003081c10040d12882a22070806081c0110000c020741c05109580c8a200940741d80805607118044035801700301c1c00c0341c07c13481c00c1080c2170250765070200d845443c041d101d000e07051915011004e507040c0103000710101d14000500c80c0c031002c0d1a0700081d00624183d4072843c000c400d02000b05026a003040c04 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 478447266 1250 478446016 478446037
    0x40302060a0b1c0b1e060a0909061805030406320c190605041a0613150503010e0607080c04030f0201081902070501090302060604291c03020a031409030a030305040305 73
    0x4040d000c1c01041a144c10082c414091060543e5031810402040006810280c0306c4aa0001e4078001c00c0c05121120b074407070612544225000240c020f1101c01152050038000019100354101160400c450b42d0080c40410148080e203c805084095180c0c2c0b000e500260440d0207605c000b804034549080d040100884403550002c14028a0000c0107840c0900c0a000211011125080c4038038517032a40c1d40c8100c0d481805a24010074110b000348503075a240c0001d003c00600200407089000300000c0035102841130041d9905000040d0441c0d1515000190202102070002c40d0044020001080030440b1030a40b50001c990900e0b00180f942c0b00c003072100480305642003c00008602c009a00d200f04101544044445c0d07200e40c0a130380c1d80755242d4040004651220403040c41c00e60603691040b00c0c0d006109500144414020a100ca402c0300204420361103840000e021005a070142d1801018150041d45080100f613550580610702001f030004661140c2040e02c00070223140e15140460100f6000f0416074400501 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 478448516 1250 478447266 478447309
    0x1a030c180310061d0121051213090605031906050c130b1803010c170c0412030801090f0b010f1d03010507020102430303060b03070c060e06040302060a0b 67
    0x1550b0082203148075504854030502d0203000f2181d5444413060481d50303603c2981c10310b0183d0100300c881c43d91812104456600488001280002850000d4010700580700c01700d00c1c1e0300d0b040800410469080790802c82c8643d0151840f0280c41d2401c40d100b00000e9442030700806d003030b11500e07500d144074001c10313480004001d00200003044485901018018051081d4240180c3d07030446401d040c03c907801c0394001d4000400e00032442d0845007020b00d08580100d0b4140010b40f0b459940c007030a110341d1550490850000b43d403500104100251384c002e40c1982040c40300300704070b468800340004c2c00100d01590344070103104030303410544903003c250441e4002e6440d01130000c0c403c91402c2c00009000354400022510034003c0c403500003000300c81d142c64014400c0b2000c402000c011540703c03c5808090980141202050348981020901c0754100020358040c1410fa22001940b50340f526000701603a1101012500d9a4881000c00021960014140c0d40090b00c0c10000540e0710346441c00710300c40500c02c8001050030728 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 478449766 1250 478448516 478448533
    0x1b0409051503061006050d0b0f0d03030605011403160807020316062004080307080c10060e072709020a1205130b010b070c0603020306010c05010e0a0203071a030c1803 73
    0xc90321460818007010803030960300c07507966402600100c40000d0280c80c00241051020f1402826113a01040c4130103070041003080086080f90000f98031880c0c3c100118002921500c0c2000340d035030404120251403140700803003800c500d000750906144d4074a00c10382000700081d00001c200d1040c020b01c11684604480364070341c00c02541c80d0805030041c09542009100403044001942d40700c408030b01c05e4030b0030385442501841c904869502c030b42e0000e0b000b03820303200301c140607991021084030018030805000b00841d0040410710300e805880604030841590361401603410103456100c4102c45420b4090030340320003640040e201c07400c0340e008441c0d4030b001584e00070260b40307880d00f4452030031040d46c90010f00510540020381d042c1e0301d414150b0054000e21400420740c1c3c0580000303124290194000d0742c2d2199061400300b0b8400c6040e00d4943c02c2d40c2c0c00340f008800c21b81200303012a0650030280010000750038034141c61a03150719100e4030041144802401109907040110302168843d20560308100849030060403183c07000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 478451016 1250 478449766 478449781
    0x90312061813030f02030406020705090604060e01141003020a0f0c11060c0c030c060a0c030327060b090603010506100c05030c01050916050102070b0d15051002010207110301060e1b040905 82
    0x891010b0302540403a10303000c0483ea00c24800002c543c01e0300c456a015168441c85d02050140d00a405001264466144e40021902001c5903c1d100e008180000300c0c4000788460005110300300704188410000c050040000040071070b004800070041c542c851803d02e40d0260141000343d00c204040003460340c070071400161026041000616826500270440c19160600081410408140f2808800354040780c005d84209011901aa00028043d881400a810b007407844040c01c0902400c0c8507412a2039a039960849416030500c1c4805d1640b20b80c040e402080a800c003072000030849075807600800b00f0420241c0d1030100b0000e041c81925014a0b40b07074001e0140b418003030a101d071504145e09501281c030a0392400000d0961000038407104503044018402e14001182d0180800b8000c201001c0c1d14403e90040e00155075240c41c50b0b00c1c071403040710342e000586603042480c06a031300d90203204002c0c2c441d0b810400c0600801109030309507500103a40c8004500003100f40440000c0d0760141d5800103881d64a09030410242 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 478452266 1250 478451016 478451041
    0x1120c0903020f030f1c021f0203150a030203100b0613060c140a032f0a050102031f0513020a17010605070b162c130204051203030903120618 62
    0x1034a00c03c889080c402c000305000d140e81d506001c003500e0041e92000114041d1615104c040948203030051041c0c9901100b111003100e1941d00316040032a030380790b000040100c0400f6002e000300c01c1e02011501e181e4440d195400080d0740f0100120419a400c0d0303038800daa035032a6200c0d8215408032240810b000d0545554500180c0009544a030546180070100551000e90001254900440350306071540c000c07081d031044404240315029005220305100300d082c941c13103880b420850b0b003030303030901c24000580e41340780c5400000c0221440120509032440790803410b22080c0c1c1d4800d1144000c0b602c510006859400543c400c44d5000d140d0100c4900b03020360780d400450450392000050010601502402c0500d07210b0b503119600032a209005d1100198005608a894041031a0002c024145028820b03140c20070902c00100a80d94a2040803150341e80046e0070001d5007001d240074855584100055420351601c03c2034152244207014010407036001750f2000501c107596841c441003081071400d4092030309145c8186031020 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 478453516 1250 478452266 478452269
    0x6050d0501020417120a0c0c0b0304052a01090e1b03040302070305060c03090c0f040e010c030203041a070c030c020415080a0203011401050d0206070501200d06120f080901120c09 78
    0x1a00d96090700149132011002803045030072034869007114071b0040140012140440100070854102c41d220b000026407201b210041d40c096402100509000c074072020f2200140c1610404207074000d2840c0c401c007400d41ea00240290202c5001c6503403480181c0c0c3d0741586024580c0b00c022040c0c01540d010051005140e400580e2100356480f903400c48140d500c0d400080d00160004845000247d4807144141c4190709000b0b003d10752092001d0404a01400d03095550b03070070f4803141030404002030b501000300301c2482100a0008104442040c95241031704103503d00a150104422001d42031010b800f00500864440d42d000c800c03071050000d00035644135111500103440d50705924040e842507003040d00c03445000e00300010450480318001c1205410034040d40c2400100e802907042917900d55a1019505403a42284401440c0c0d500304000499880420101c4001165140d800c00da1449418070380260000b501920000b0340603400105094541080a0040b141403801e40507900300c560806802180d0a5046680b110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 478454766 1250 478453516 478453529
    0xe0418051f0b0a06050a0c150e06061504270606030209040b0411091c06090c030b07030b0f130b150904111905130317040e092a0406050d05010204 64
    0x40440042a00c2407041e01c0c250100c03168820f41502041020901a10040180034441e007400d0414104944a80600108442001001c03903150103c1d0204c044050220f07950001d0300704d8040315002000c003204009401540525107000c0d200101110007040c85522088038a8480b0406005044d1200d038010b020790404647c42d8055030500d00e544426260500403c00c0064144055904080404040003988078a12415030301c0400c200b1640008140140101d11985020300d0780644081e00d180b42c54004135000510354020149480e00002c490381e181110440803150496400b60005011406540103004074001503501886040250710701d0b11201002e4201c41a00311010030040c0c0040107036075080c3c465500b0042c40950550aa0a0340d00e0094014200070301c6034000400d44c05841c0e0340c0c0c04100041e2400c1c404058080070404002004442426541c0709000034041d00c040c80003001c2c0e100080c40c071035481110400140074045081e8841e503200c1360040c030307004040e14034002d01820618001e50144c0510b2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 478456016 1250 478454766 478454803
    0xc05100204060e06120a0b0f04020d14060603010807120201050415030b040b060702010219050312071206170a02090714070311060907030b040f060b18060a050109050109060e041805 79
    0x502031460004241c0b05440500300d5001711640d2268204402000c0281d0000d81c0a0b42110340b945864843c0e1014091515a510000440c001c40c80d806010109004150724814202040180079822010620000f143c040600c1c640d41007041c1d01c0103032124041c030b1700304a41400c2c5a480021900f40c4c103412010140030148c030100b000b43c00030001c2c0b21561082c2d01c00a4050b070b20440c11020b17100700707050303d444d1003030f01610075681001403604002c45a0301c41074401d8400150f505a00c40c100c8032179407003158010f00e50401d03e2070399203c03240c00790b98880c07210410192003100e2840004400d6809040c540c04850000840955210305900e40034103110240c5c18010481c0c0310711b02c00030344055000950481525004004c2442ca40eaa035036801e042c80b0f07a20041190b1103511003400c03242c1a00c403000d9079042c1a20954030703015a440c014003400085170301c6e07902c180d040000c0c100f001c200e107903008a20001950910310303021054080c0780011030058007071503c02001e1030415115801c10301002181d401105030024041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 478457266 1250 478456016 478456037
    0x120f01061107210f05100e0303040b0109090302070f06170f0c070f0606080601090f0f05150609121e0d030203042003010f0e0304050103111602100c0510020406 70
    0x49800140d001c0c202500c1d40c0c0001014002c14201a003ca40c007101e942e0721071a40d00c80150707600701d9128403140044440340c5c00340c888a4101071050043c4070003a084400194114a0f184d01c40d5282c408041c424050901d90f942c00610038140b0030b0102e03402410010206038010399480340010b107807142d04000c510028911a0200d07040c0c0008406150140901d0a0428100052078445034044420500c0480d641c035541c1c440007135201d109001480c000c0070042d10000385001c901407010180c441c0caa0f00c4402251a20f4100450040080f0038540d060100341c5519071a0410600468814125003030443c22030f10a0b0903401c000e10410003220503902a08030151162503800388000d800368002914000d0104103d000c80c000201e40d20a8041c100c580d0090002c42d2025143c04140c046074804035489019410000381800556098040c00e15a19540340b030062070a03b000c0c2d0a40441100c1342402072107515a906800c60443c49043c1c0b89400310f80010a0b54200e40da0720380041c1c0254807030300c60b10b008214800350 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 478458516 1250 478457266 478457279
    0x20d0f051c08040506070806060717090111030909040320010f020702100f0c063305100203040e0115050702090906040302060112150509011e0f06170a080702060f120f01 74
    0x980740560352010041425403a40842600d1907e0000c210541080e02882024049070161f00c2003a0101e003411050350707071428071400042200c501e64600143c5940200482091a120954042d500c10381616245529592079000000310340940981e404041d8200700c0c0c4113044c14800c0e401091603920031a030600100b0b200306000d40310001d541084101240701206090003003030b80c941000300e986100c3c8180040401800c031000d00c804101120007900360740301780014049402d003440426880207050004500349450451307232503031040050246800d0b0238a2401d210240030300a405454034903034018070f04144c6280003010940c5d6410f0481c0c003500140715076000005c82800036624440515002a20050243c540140f120090003010304802115941e13403040c052030420b080b9100707880f0b200e44040482c8905000a44009a6046421503881e0400300032502008910010380d000e1603544c451703005502da107890300015035540980020842140000103210801c2e240001e04c1c01d100d007101c003070180c3d80b59807142d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 478459766 1250 478458516 478458527
    0x5060901061209030203120103030806042009040911100c060c030c0e0105160b010b0c011a030304030f080702040501170d02010933060608090d0e0109030f020d0f051c 73
    0x7250001082048000c946140c4042c0c1101d5002400fa004580c07501d8201c2d5440d03100d60354264000d03800911800c0c00d019040c60a8064500d1020b006400046849102829510070744550180d141c804c0e5510303012072040102c20044406003081c0245003003031560200b4005007401c0d80c110070840b070007840c02d1254411a4080d10400e800440981e5542003c03003481d03030040d203055000c0c0246800102c2d04403171034000a41e600500c94060110b061b6882d4450000b400744a00395002030802e0ba00500e203070f8102241588001045d10100c0380c0003603100d460941f07541400240741c41101400794009080000101e010506620000360402d0840704507041c041c818401207080380c00c130304030003400d005541c040003d01c8001030368401c411400344e090400c41e00e000ca030321210481b915903101101140c5070804004051406002c00e0380c4850140c20201c40c0c2403200c40000708405240d000081880201001c038806548420318542001540031865240041c4103050440e0f0b2000c11441d00d5401030700090031402c0721446170 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 478461016 1250 478459766 478459769
    0x5070f030e0a060e010207050d030c110703020306040201031e0e07030213180204020a14030a09020a150801150c0f0c03020306010b090a0308070302010b2e0801080d0f0201020f1c05060901 82
    0x1c0644101c00880e540c84026041c00d01d40b80000b5134082c8a8980415014030050005081c16103002412032070120000d4004084560703041a2a0080a020000b6803004950241e002e642440c000416482000f021aa50f00c01951621411460443d45403091100000e41100f9030380201d075078900c81d00309282c1e2442580d10100520140c5200808008014141900039000841c850b04182083c09803044244015805c12a010111036807682d1002c070a50506000c00000351100b150940b14591080030050285001807003848450002c10001c2c0703040c035200d1103940031802c0d8030103880c0300b2003c800c1c1401990042140400d0340300c1d00440d0000550302404204480c5d2820014060300d84161554503a0251500240000d50642d500c2c1d0b2142d6119135140c680807205025100c40d000c03c0a010700c0c145c80c030485c0c1d444580b0ba090148032401403082034000100c4032070012440c500001e2404400d08101d029010b500180c0c05000c1001c05c4101030041c0980751910000e0480808110325520b100420000501c203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 478462266 1250 478461016 478461041
    0x90501080a02042f040f0509010806070c0f141f0e070e100b0309061e040b041209171e01060308120709030b10090b010201200c0a0602030a05070f03 65
    0x92845001400e00c1d0704084c443d42c0100f011050001c909000700c03040700c070542c0d0300403000c07280010b014410024425894406000180c440c2210381d0704180400d9591500904444240300b20140020200080d4401d0324000a0340840e105100031118461f495030f941c8521022101c94044111061819065101d8030610240d54002040c085180178000620100701921840742d042e14054085a81030045000318011211200140510700c0e0140c00d03c90310044c501c078482c003108c0200c03041c00b000c1510f40b00c074660070980045000d00c4001c522042034411540b658040e11406c00a98440d1207205404110030030400307108142d02c01d10742e014400681c05c95803203000040030382034184280982900340a803841d9100c0401c1c180035074800c0d12901c810322140011110390202e40c580d81e1050042a03194000c101c54800d0a00091007121905411131120404e03084144500140c0866204080c10080104200c40d40d0000c0d801c65583c102142c4034009040201c81c4407001c280681c50007100346100340701e0031002001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 478463516 1250 478462266 478462273
    0x2120f06041b050c01020d0c02150c090108041520040501180e0403030b0307030f05010203040c05061c050c1c0b1005070809011407060e0106050f0d0203070e090102130803040e0109050108 82
    0xb80181c15501ca40150108030481d650034011207999541034803038101b560745a5001014010802e8076154454200100748450940c0240000f0702c0d166005001c840d00540d00042d48a44200052108001410945107043c550f02100da106100c20f441400200705940080e6902c0700b45891894191403210350901c1644858040c0b140000c021034825807181d0810b031801000d80b48626500c1d101d002d6100e20088040d00c1603507000042c0700801c0b0011081c000202029100b00e400d005601200c07041c44100d5201c098003194454000601c000350030406c40c0c000701c001d24000581c1300001e0001000030458070240502a15081c160343c040746009070b01f5034024961000e003080c07410703011000450300b030389a000035821074280a101c10400141140100600440c01c5030001580314176010400071a41d2402417107030300030040348a6210158401103950001d592401c086440542c0391040981d00901c505007484c0b01040d100c0310301040b120300100040c0100c81c1d0404007945140d885582c914100c7c0c10030300c0340c100ba170750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 478464766 1250 478463516 478463561
    0x60506090603060d051207080d0b01030c1d03010f0e010204080d14030711070909050f010609290f1017060108010e01060c03090b13080708010e060103080708090402120f0604 76
    0x2e08107000100c0c4030300c602d0966400301854103417080560803000301100c84032008140e8101492725485a00d0008809180500000305810000340100b465080e00404140c6c0c488400314150701e00750003103020b1000d180c82c1004140c1c3d03040c1d0114002d4009000d00403d50182c2d00544400b82d1240c04107020700600701941c140383d6152500180c0e042c4075281039400329409254000a034044071407040101080c01000586007562050422900b101d0058014075000c0385803103e645107000260461982030161014081e180303400b00c03000504d6414074518465400b450005102321096803286000443d48080f4484100030749a808c019102080c0c2401411040d04408004109580c41855460046406400c0c4149241d413280803d038401d902004e8105140e10005030b04003e03c48040010304004e00c25403008100c41e521044100d0b440d00d80c18400a46480c00c0442e5140c180b012040859050000040c0110366401e00c80c440582070240403240e41c602e286c081c500045282c00c00b409640c5000d86030080c07440184 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 478466016 1250 478464766 478464769
    0x307030f05090d1709070b07030c020315040b071b0c080705090714030c0d0b0a1707170601171203090109060b0904051038040e0f0709020d0207020d03090906050609060306 75
    0x1000d006041405c07070710a11000160804003000100b030a01e0103503681100d44000c0340185031608510b04183c114061100c000c21020030035074a44260080e50602d0701c16013181510000c05000030340024080c2500d0450100013032440c0001a1135400c455081d2541d543c0da98131301e242503915805034401600c0301542000082c1924625a00402c41803c0d4280c00289042042020a1405c00746400034102c0480b00104a41c1200341008228018400d19000c05800110b03104007075120710040c401c1410500c0340040c1c4050b821014003000c450410051280c80e103c1c43d2080000c2e01070b02c803000c0300b40c0b0041e24244080c000c500b040070042d4403c0f50000e00800f606035150040100078101c0040501078003c071074100714602c1c80a03c0e61400e0f04140d0442c22050001440204000c603402c0c030007da14654044030010070721030004140d180032240e401c1001a1180d851714100406440350240c001d5001d0025200c0c01e0400d13420800c20015610300b401c08010164940d01805040c3c4100040903910a90a00004203507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 478467266 1250 478466016 478466057
    0xf090103090f320c010e1e1206060406051f0807030f091406090312040b060310020406050316030e1b03070312020a03030c02070b0901081b0307030f05090d 68
    0x30074420410368540c0c418079140c490201d01600d02000daa140c41c0f8807006034141000291620305a00315000d40048000c0a00203404846e0003080c81d40100c0d05820f808000800e0201c054002c220050112030901c9105003032941c4884044401600c213078649000800c40e410021070101c42d20a0311800c0980f1446d06010a4621100c020152803c040d2143c50f132140e046014020160200c0c4a050000c100d034800768901401c000703000342040b205a2051081c006196450f14200f604160000b00072551070b01d600300400c0c10800e069004c3c26066000160000300c0951100c001c43c454103a24184180b813034690700085080d17400f02c0d00f030094150700403003040801c0600c900000c40752283c01401c0701c81c299036a941750064a80b04d00c9006015030041c241c590706158150207480001241c901c06498100e0500310f415459004500c0158104204000060840c0c00e45100e241880142c103501c50b6240c3c5002304008001d86105502032844a05050110781001d80018040112005e0394442c07003050081000350b1800d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 478468516 1250 478467266 478467281
    0x60203090a0b0c0109170a0905040203090a020105070303020d050f04030e1815030102130b210f0a05090109050105150a09060e0c0c03040f060e1206090a080a090f1502120f090103 78
    0x1590b544e85d29007100020a1101ca900042d41000c80080d101c9250f0a4050804070321507100e24051030041081003546400400c411160681c2400e28a0f11901182000c070001d0081c2c15040d0700c5a40740100388540740c40c070302d21442d1046120790b440031a00e1002e0000d0000c1046c41c1861000b000c0c03120000b1a048108118141c01c02c040e010740018100b28010b501c914168200e5400030030410400501041c01c2c1c01e04d2124055008103a444055481c00e21002511951000a1442c2d035400e50301c0c000320304812000c1d0008080d10f6080300007400700d4201000041c01d00200d00c4120ba1107841094000540c1121501442044038102c070b041030322503964900c521741c595220b80130b002190b01042202003088810500100301901d03290350b640924400d080e09100c16409513440303040305540843c00f08500a0000200d00920a83c4036a00603160b141031710050350300b6521a000060503924000d0b0100300440087c400e480c0d40401542121800c68100315001401e219841405a10007401c000406040d40203812000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 478469766 1250 478468516 478468537
    0xf2a030509030f03180d0c08070206091c030905030c030f060115030e03130f1a070212030903100f0c09030512130905070201090302010608030f090405130813080106060203090a0b 78
    0xd25004540f030f20321a02d41d20843d10510810040c150340c01803c0c904210030700b018801420b05048903441070b00c648809003c0d0b0309009114440001d210411602d0703244032403107100442241c01d41e01101d02c0c603002c3c00003c060700895000f0301c5094504505440c0026001c0320b410321650141050b80d007000c0c0710b540b0a68180040c481895211103003044d10b4a420001424030705619052142070900b8406403121480c0f0561000c119401c00041e11500610004200c40c09194100d038210791103401d081180c0d0031401101c01c0d090b494041ca0001c900600460342001d158000c80321410011045601c505584030111030002404950110400030010b0105400903c079013083c400702252115942c40001058a90403503231980140d46039120031041680902410000e0101400558241040490400c1e2035015510590348680e84410200d440c0049046222050582207807403940c0e10141c80d600e85003196414400c40d00d0541c0b03040c10004200f40701000f901c0a410000b0b10b20801245000300c00c06161300100b4020303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 478471016 1250 478469766 478469773
    0x3030507050f06010f0315020a080f060301061a071e0f14010e060c12090706024b070902090d0f1b03210507110909070e04060f2a030509 60
    0x82d081c5480400206001740300c25411110040e04514103a40680a03009488280c24014080c800070b017600145407541c0050402c12103c00c5a8a4400103400b40c0f04680c0b0501940034406440c43e100000c400c01459014014145080640c2c0c5119815104121816018051000001e802e0001951845c000c0360024880300001c42c200010a4426003820b5068810001d100000205820b03100c44e01052241e001c14844080d1031405e02d49a000f0f9120340454102070522482030780c0010030768008241e80c16101c0e200000c02d42c01c94684045e82c00034480c20101c44070075031080c404002910b45150003190840000948940000c0340c0596400740d010101203811560409034405010015a03621803a000460081c210511403100690004c1ca007100c0c10209141081010803001e004904402c0e0002c40c0a2020780c0d420025640d900101c030709104a40d0400310b0b40d01056000e0005201070364225000009507000d08106180b0400351980851450402c071462444944200b0841d50780640d001c641d01c11894000d6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 478472266 1250 478471016 478471033
    0xf2a0609130c0905010e0d0320010231150228020603040605060f0d0201050f13150507050115182a1d010c0c14010504050d0501020a080f010f0303050705 67
    0x501c42070351014107030a4001504610200680d40c0d010f080b40100a00c03e56901d004043da07504d0007007043c000c0c1070000c44480c5a40c6041c0a021800f54102c5032254103c406229050280310358114901c14800c1e40461301c104011030101c0c1ca2030041c01a089140d4142d002003c644901078030001a4000c407103922900a20404441c40158482c2d2009610940c0324400c005a40e1130705508010070761501c18990303405030596681e4040141d030010111022046e0180f030042d00d4002d44404981c1c0012150054034420b16450203250019400002810559118400034400070307080c0308800036040810700c61004042056012426202c03101d520101c2c0c400c040500040da0740d0207858404440354012070740400000d540d801c00d400d803a0301c4d003140c1c200e0b800e8003440c2c20105200e59446102441001340107402556284500c00355860b8000c0e0201c9008282c01b6003060403000b030f05d08029000b50444030002010a0303100000800704219040e03520705a4100000341034565041d620100d6294201c181c0c11a00c1e44100c098 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 478473516 1250 478472266 478472299
    0xf06280807051209031315111902010503130606030f140c0604150207083a0203271305160f09090c0504090203041b0617040b041e050f2a0609 62
    0x502501400007d9289200110044802082013594070f040320b0b00e58103c410740d020075403aa41c1607142d0b170340c0e024a080d545984500c0000110710200c8540104001d1034210700104000c014100b8040c000d01039900f800100804018450b264094150055440101080140000025100c143c0043c1000b4411100b58175201e03000720b441c11055109000e00c02024030504030401c0391600102c03a441c4406a0010000701071a03201075924081c039007040a1007902240399602d828009110b281c0c106400078070465002c031600215000600d0240c903500c120884442d20b100c080c1d800741c1c00c00c0395421000e41d1223049041c80c010300783c0002c141c814481c07010001d0800c000105c00c2e109002a601072805a0800d21040590b0211038071110101c4d4041810300c5a160078450300e841b1510781580d03100da040010301c5413a80c0da82c03402e000100074490894001a00710018031303080c003000290038060701a00320300b02d580c02015284028842000c00716001d00741e01d0106d81c041e441d07080c901e0141c072201c4000b5050a1000c0078026 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 478474766 1250 478473516 478473547
    0x100213060c0302030d110d060503010209091b1201090527100f0e0601090204050109080610090b0105091017060319080d1b0201020a031104030206090409020f0628080705120903 77
    0x3000d603540080110b8940048030423032090400070031084000314500603010000c2000001c00800c040400808504d03804a2429550700300e0316050303103514542d000c5603110341104004110031f44160340c3d10503c9c42d00f828010100c2c151058001c015101c01031003c1940440320601804c44240040c0c40076441e1900400119000c00055010349514072026807031f941032030001018252594480659035000805018486100e180740300b040c0d0320300366008201004400010707202e9100d403541e01904110301e0725200c401c40c4c0c0d0080101100340c0c81441c4d0341901f500c3d094109551000c600000e090204480c00c0c400c40002c82d41030040070f8203017901c0d80102c0c135540795802e98803868003522a6000982d4000a6808010340e0502c5041c1518a1a42c16a41001c2c02e60b00460410b000b5203140c0f900640e030791404c56003559030b141105049400c004019a13965070249580301c441000d071f25202c0300c20703400d010926013040f4002d29000b8447c1c0002c2c4d65003030800c1048141218008806844070845000c208040e00308c418541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 478476016 1250 478474766 478474781
    0x150c03071d1c11040e0601060915031803080412050405060a03051005030d020607090801110a0e030c130c030e0f06130305070510060806100e150103020d0509060108100213060c0302030d 81
    0x8500c1c0716641c2a000c401c1c40107170f43c806160700904d900180010f20100b034220030b503003042d50600c819205070344408150075070080220104400f11071200c0c01c0607504060340706480c0e80c40340f1301c07070104107642803500d070000d4416000341d0140300c0d403080c818444030001921a07801030754840c08202600f40d00c203a03500e0100741042d00a000640041c4c01007400c00034a660400f10f42d0008144041c000c002c0c42407100280d40140c040c040e070440c200901c8001c00d14203580d0400440388084402050b01d500c0d100108422030052820701c036a040400e0610305007032a60080441c140e01d1001c40314001e04070554805c0c00e880749a8044000072070034004240b01e9400070800c104594040351402480000318903080500f40c500e400740051280701900040001800310302c0056003800e801c5003012550403480802c0c2c07001600680500c141941115203400208070009000094080c125014002602e42d896500d44044003a442030700040382c000c14403c02c0c100291407044510003201c50103441580c0c02c0955120a5000340c1d00b60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 478477266 1250 478476016 478476023
    0xe0421271502011d0a030905060c100c09090f150e0903041d0106110d0f0806031002161101110a080315190e010b07051005040c17150c03071d1c 63
    0x4501081e00c41c0244c003159004032040740c0c4000d290061913542c0003884c8008500030307076004a90118502081910070045400b22600064050190010200e40104015094800e05141a0404407151000da403640309807000f00c007026400303204050818054980d0910040c10220740b500c400c1000007180fa90f11070302003241446118240020f9454000001e061381c03015091411290800e1044a070982c0d080f01e4008074807009030505414a503903070000241010801e42010a0746400000e0708481c5a4440d0300c00d08590b440740304107402d540c00c00801140d4030401c00b0509800c0d680071003031083c08150050043e5512800ca809494200c00100f00805c00003040d2030a5070004026001d000e0000305140c0c044140503214070289282841c132140c88075a51800010a0914120740c0e80700410705101c1030980c60340140114503d401008110031000903034841c0074024480280324041c02141911006004490141140d91385580d41007241d02d80c0700c120604900c1ca11070340442d5a04e140c50310044141c2859800030702 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 478478516 1250 478477266 478477271
    0xd1410060503060601080c090405180a060e0f060108070603090203030f0403150e0613030305100803030c0310090204031a060406270506030606010f0f03020d02040e042127150201 78
    0xa8207040c940782c201c0c080d28036410f000c840d42c01c2118100b803000668220450482e004201c50721100f0880003c40001c0c02c40043c0390040d00c458105002880e001400d0100180c02183c0c0048201c6110540b601d000707008141d8642c000301c60800000c4d00c0f270380191602038001000e4924141c80713100e500207180e001d54803c0b503505501c0c490404c0fa07030080f407247c0d42c0da000d1a9001b8040c03e10344811071503401c00e10010002e00349070380ca5000c98401d407400c4191901401c092002c50707603241015141484150001c0740d420128400800c808a0100b02d42e0082e83c00316540030a03206060780051000701c40c00b00c070041c1165005136441a0014150710030401d0030a4014146842e03601c9152548218030588034010b0205020742c1c0103030148031036664031038110103405403503140113400002000801c801034070845407401402c500125002c503100c881e2009550041e031003004001c4088142940018400d000f03960400040b030031041c0301c07a00703d0190728000146140c4248401e00d40795120319043c1d003d6403580b000000180e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 478479766 1250 478478516 478478519
    0x105101803030e090a1103010b0a021e01021e040302132a090602071208030a0908130608060a090c0e0f030313031b0b04031707020a08012307030c0c020d141006 70
    0x3011400c031354001d044d01105111a01c442c0041d142c00f44011b12034814002030005181c0c103443e200b88110b201c40030641180b407400c5071925055034080c4d0030002180d51a00d104205040e2160440c4003124203ea0740500740902c5211405c4d281c0b001800e0515031301d16864410b01c407580072070341649014060017507103854100301c00707050541c02460007005401803015803400500400201d03c6030008d59034801d8204030046600b20151520b040640140e000721950aa01c85ea408a0340903008200389219940507284103004590b246041c0302a2524602c0190100d10700c0c1034581280c2c1850065441c0c2e42c030010f4100c92500c84031626021380c1081d16070080c0d41c1c0c0b21518034403c0b140e05901c40c42000500c4d03070b40c3c1038604143c25130304c402a1617590000c0000d40140005031329411906c034800f03010018280b0200030032030081c01a82440d200f40044443d001034408410000341c00d180a031040c55245e603081d6039400e0034414141c3c2803000b1180030440603500a20340640500c00c0b0b12007040200d628004024011402c0ca = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 478481016 1250 478479766 478479769
    0x212010c020f0111070609050a0c0807080d050a1d01050c0706030209100e1c0204140a0b041104081f0f0e0304140306060d02131b030213050a030b0105101803030e 71
    0xa40c00c00440d0101c1c0d05100400f4041d0080c4c2083d1000d00b504114009610401450101d19144201c84001c2000021000000709041d0214007441122002410307944020403d01044400380303d9001000041071000d0600320381c24180c140c2e81c801d070003018100503141c1120300000358075000682d8401000280c0014000c503190500b00c0c6c4280c00240641003001c040b4440600041c0c155100030078003400c905c00040b01006558480d00b10482e62545090542c8a6042c030300851006007a2010f5000d00680c10300344a4041e04944600b15400c403480c902c0a8510440c000102124100e80026165440ca40303d02035002150000c0c803441a8081881001315030f5603107402d40301c4078100000d07000e1038801e41041081156540303a003950036030440c0e41150141103030441c0d40140c0380100203014120700340c64007050303d58903142e4056000700703a0094118038103038983e07544100300300c541c59503400010700b0304801e074004001506109055014100241c1400e0303103d04540354888410400a60040c0c00250740c0c0c1c4107031580e5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 478482266 1250 478481016 478481023
    0xa20030a09140309090103030809120d0203010312080f010911090307080a050f0105010e070c060221070e2e091203051207050a090302120118060203061903050a031b0212010c02 77
    0x28104020f541016031104c001030350050305120180501c225400001c0003000144024658100d000c61f50a8891052505010007900b0901003156086014161040a1406080d4041c828448000004056800c0100c5800074111000611005140a2103581c0090303400380403c070013601c100c00082c0003180560401d20b180c0781b0006811505030340b40a0060000101c00d003031044d446001802e00d5031501d03117a440c01e03000a00c84c444188003160340501c11101c3d20040c0356919030003030009540ea407603840341d403104000900002d6021291821942569006101c01c1c0c4200d1302003214680c00e016542a5591140c03080988540c0400c0300042c01c00100350341c4c151110403000345c004103240b40142c00c0207961203010b40306419900001c0d01c1024444101c0c24914404d41018101c0c2081c440284c51200c65840c0500c0030b90001d4400b40d105507600c100c1e0003500024103404000b26a00200201a2074031300d42c6080e01c0513881c014440035030004000042d009a00e418000100401420300009191000200001d04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 478483516 1250 478482266 478482293
    0x80706050f040c120c1d0f01090e07150905060c0f190209060f0a0b04090e1207080a052d03040209063c1203130e0106080a20030a09 58
    0x1001c1150800303000114000300202c0c400ea4044c501e404000c0280341c10503800160503948808003601e103851052400407440548180a060303412540316003a600c0308100d00aa4404c01035102840e8007404080045810b45035028141e0001802e082032107030b481b04082203407940480f14100243e4800c43c4c007560044010003000911a200e1b85010b1440d0120764001040d8500c050b0006202c0c01e42c4041c0414075035540022140100010106035a4445d139521ba030101926080c600d1038102e0141c41d6403d8044400f5400711030410781d1101034146054102d0720240c4a580081044070008c01d01503400044030030f2840c030348800380300303000da00151030303150030700c10800135040050100703001e8403003c2d007294403c0d000010b200510303c1d6038240c5e02c502582e20030750100010021088656115480e5141c08030702ea00040010001d00c0b1404098050246c0c0798a40701351000e500f0f108101c0001c00c00c80001e44175003119803044140e00d01c00900c8240110740c0004003520b0f50020388611041550390b000d80c00401041204650 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 478484766 1250 478483516 478483531
    0x616051501030b01090c12050127110a050319020a1d150d0b060c0a030504171207060b06161110030902030d0503090a05030301030303061508060307140303130308070605 74
    0x49560450f680c084440c081072152050f182d44030348100469501450030f08071030b41d5100c10100019a558140d0480c84840c2c2420800d041c441884101d4141c2c000d4000d002200900c820741e1460306074004011181680014807506002c0c42280b40040c9518803400100840702c45543c805491360700120440e0b681c5e508495503a03100d94114031035070310118404c10603550b5000314035a0008030740080d5404681c107480361104c00c0b2101e000f1542da0404058004010b02305440e031a07072410b40c01010310502c969503220140000c0c0d00059052086500003050340d00b25400000c40a440b6600b84444005000d103030b4038400004584103a601001b0000c2e5003018041581c44040394501808205015004282c49001c0c40c00d1140c100440000000e1b201802040084061544402101c0c0d8940e52810014000c2800d8045c100c48662081100546180b144104074069100180a00801803a08400c181c5055517038422a0301800203100384028906503032080300003140960542c5079101c90f40c1c0b074130000b1290000c0140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 478486016 1250 478484766 478484803
    0x203010f050111120a0e03030d050901051e1f0b0309011a0315040204090c0e04060b030610061704140a050a14010c1d010903061a120616031a061605 65
    0x40f5840100080c00310000701a441c0642e6110b110403000c40e440c40d040d03150280c252100145000103c00298071640c451104c000c000c10072034441074560000c9501025002300e0280c040710108401701c0e8075008001702e100500c40f04100c90303662a0400107103a04200d0343c042d2140d5440e146803a0011079400d03101140f10080b40075002c94080007082c54203849024201900450303950a00804125007055003402400c42102031942074901441c02c00c0c00b408182c903a1074084e00410000c2804070800c03000b50300036581542c84040404454040d07601185c0b000a00a8620b490001100c2869800510000210324014005050070100a0030404042c01c82c0d11400720070b5030f140c100319503807d07680f141e018004000d500490024103258100102e43c1c50980d03400281580303113001c0041d0b4280d00b42a040e600c41907425140f280040c01c5071b10300c0d940c944000320703546a01405040c0355642518400e0740030070600d02c010440c404403581c0100101c0c403260031110120340c801000702460070500001300207200040203410940b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 478487266 1250 478486016 478486037
    0x140f01031104061b08030c031015141606110c2a100c0c140306070e090a0b011808030705070b0903100906180503040f060e0319170d0203010f0501 64
    0x20074051003544256001c02100e0045184102d10091322205001c1d0401180394030b0341010824094264019104182000000000094144101c0c071800243c002944c580940ea00700710000c800d040d601c03c3c0c03128404400c10000400009149103c7c9200c03030701e00b000c0740b20707250300c0a1210b551600c030601c3d01c0221500320300c0c1043d1020080c1481c84640c5004290303103030300f00411a15400d50f00c100e8415002001642e8181000c182890449200d05686600f00c00720b074500d891301d643c141c984c495499034041d0060040f0b000031301a00521b41007003050440605d480c0312103080c283c20150759200f541c0c01201194200090300018440100a2600a0403034000400c5c0341100c1000020394901d4881c0e011320486481d00304060900990364801c400f041142100b085a80c28035180540c1c881e44640100c05180c40005404038a1a100d0400102d19000103070051615086000d8101e000040a80c03003121301c8480c0c1d0070351404010499014081c1d88126850140e229411308241e036002c44080c0d0400c40c1040b086120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 478488516 1250 478487266 478487291
    0x10b0303030115211131090b030f0616230403151d100f090314030903090d1a0f0408220f08030c070506040803071101120501140f0103 59
    0x880e40c8120042d41080b032009042c000b248145038200c0b01e02600228540f00e131100f46448007400510710b030b4031403c84007411504043d008821400000300898121207003001b003800b100b4201d40c4480509140123003210010099100c0003417400000303c8003190015003040016000b20f4010b91401a00c0701111a00030380c0e480d140480f081d25000e50b01c405403494540700c0c1c41619154096202c01302e0780c0c0c445600e20004400e40700d107107503640c1c031481e0100d56101d240c20304040d51071070144122004141d05a4400354201c07403418240100c0e4002030000c58950100304401416030f654083e04840043c07107403840c0240c1c1440390342010800c0034000e003c0c000a0f5140f608100c0041c03588002c40b4111904000f102c2800e0740360702484098031845801400368202c0c001c00216080d04004003900d8003c84000c00c558003a5100d100b4000e40d030066109003800c2c3c1e4001d00180700058194900d065115606242401103c640407026409840080c4d2041101134202c010942990408002070307a8421803e0074140a004035229 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 478489766 1250 478488516 478488539
    0x60414041a18070507380c0d110d24120f020909071703070c210206030a0213090c0305070f0206160512043206130303240503010b03030301 61
    0x1d192960000054001401c00f44c080d605450310365030840195803c40e40e0704040c4000203164076407a0703030840c000500d445584001c0220031030f00c15141c6240e140e0a020014004501500464084100b11b01007440341d000040d00c0c62145036500c2e500c551450b40000110000e10240320030036004201c00c1507440900b040424404031403408191350590b6008850b65450404600384142034100407510848103007200b1001c00e000001e000160700520807a0646170340c864041c0a141c101039650f910711688030f91071740d01618014016550000d4096005490f122001181c01001c0d907903500034801081d80c441883d940554548a144da0002c45814403075003c0c001c0b604040d550f642c00415601c110141414010b51892040069414101e0150140040d5050601d030010b454030349082c119025844900034200004084a440c40802d00440c000d4030003a103c2152031000340f242c40e802a02819112028007503105205540394400707451000100300340d1400d080401d401e40f007600d5049440307a0310510061100c0080c42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 478491016 1250 478489766 478489789
    0x1009080303070e062713090b061002070f09091a100311040b211207120e0f0d031116081f0b0307030b0103030e040501030b180309060414041a 62
    0x2030401140f840d46400010385030707106000e4440c42c81c1c60308603081e8140b107104202081c840c50302141c0d072980f104c0080d10035608550700381402070088030014001c1052801c0401c1c400b9640c128502c1603c0501380c80709440014241d4951003031140a0348c07880760b002400f0841d0b08403280740d0703007160302307004142070a03402c1d803070150102e00001d012034482014080199445a10100300084060300c86804804541c2d1920744c0c40c0307820001d1402d10b004d0003241212225260f001ca4410b1540a00002403241e4580f0040311500d09880e100d0350402c13220003d400c900d546a00320403400e00c0c403070364448850040312070f081820600c0031070300100510042c0341c041c0315002000c100c40700000d8070040380c085600800044000500001c68440f078050044100c040706228003807441034140ca0103070b00c81c01c404129423010b2100b140c1c024030010309100d07004804605404015080b0010b60220710041b6400c000e41500000c68030703803081d44140410000b100f0401090f003814040d840b80700c2e456201d00d68200e000c6801089a04805 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 478492266 1250 478491016 478491031
    0x60c09010804170415080105030c0907050d02030402031204030510150518130206070f03031103040f0311100c090f05040e060c1c11030702011d1f09170403021009080303 74
    0x4001c0304441a81002920300a00b258141761081414500028083c0f440030700070b0034002d005540b40c080c0181055404180a840340e651564506070410800c10000c0d00007030822603040c095034140c81280382e1500040c10146000704041d0009030720540d030000881c2e122401d041240c0f804d8080400c0155114400340e130344034600c0703400008a0703542d111121051030b4035004006d600201c049000b2040c000c4800014000302d109440401155859070001e2485001c2140c000f0300c018514412040028801c10000003400c0141c0300311422203c00600c45c6040d035800c4034110000480c00c071000c0001e100000e010390010b05003640c04000a0704d01481140d19000001c01e01142420300150103829038440c034000031a1402442d50810035250641000c41480d401680c10000540c02c200c03115202c80149200c0800a1400000400318040c4444004080e118806880c142c16980d4179021000f01d200942da03100120000300441d5a60f40c2148100000441c00014200410040c1a030030b1154000c0001281d3b0044030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 478493516 1250 478492266 478492283
    0x90302030c01120f020a020c030d0212030c070204140a24290c19111f032705010501030b1e0601050310080f0a11032d1c02070503060c09010804 63
    0x1192100040502240101406151710000e0001000350340425844800d810450a071001c00d4040381c022a130781d03580302c007030000c1000c010004641d5540c9a40011300c1d9682c4013510101c1c60031050411000806411141d0101441d101c84001d202c9404503015001c45445041e60f000f8094140605c1c10340038040360310300f5000e403065408040c2c0d05886c05804e480c0f0001300ca00441d0800c822000302690710300d10400041700c50141c1c803410801c0900e0503040c01104002440a015000c402e544411009070800408891001c16900d03291512000421b0807000e03610301a10000c222945546000010703000c0040a83c0ca40e1039114090340e034603d60f0f4804c265045502480c0a640300e460f52041c01070180c0c140e80c003261043c0304501c0d00c0f1b0054031b000f15aa45100d070244001c0200081f0402c140761300e0f443e18140c001212070b900500030858944040182c000c841f550000ca0704201007030f10140e402800d51070700d41405640a200300b000103160401c9009d1340550368583e41810103030000c0c0081c00000b00544001c08011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 478494766 1250 478493516 478493537
    0x5030d02030619120c05011d01031e0e0601030c050108060d0f0c0905151306080706080c0906040e0a052a0c1f021c02041202061c0219020d090302030c01 67
    0x25201d0314460b0020300f000a00b405455a035a9a044200080903401c0341e01402c1c1c3d003400505980610f4058120100400b8864409864180118010718002d0417280314004021003050503030170503228003d0740c0100e00c4020b140c40c0d419424019005092070f0f10903410030010004210b142e8454101442c002540480342003100c2030f180c94994000002c80c0c100c00a52450300041010840011002d916540701c107544080142031410441c40079104076015510341d90703002c01010400241705140b640e50043c0d20400007800c1000c0e40d0001090b5030312a50000310b900c0e80f202d0600c41c60601c02c3c0703d080c0d0088900300c850001100308020b41c07042d03060b2808422100362008a8240500e0106001402000305001d007910303496507299113290001c1d042141041d0f0506003141c0d00040c00543c0703208880036076040c181c2c0c00504481550802150394000b103c0061042c25000b16186280c045001600d5000c201621100113a03890100003072600c0305140c04c0d94200040000e0400260318085100078106000303203410703000070 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 478496016 1250 478494766 478494769
    0xb060a091e050303070c060305090606150a0203040306020d0903080703150605092205070e19140303120f01030227010b030703021b030c0715020c1c0501050a05010311010203040305030d020306 84
    0x2001c01d81c2c00b05805010004d041c8080062441441050319030b191030412681d00c0e80c0b01141c2e502c41d000c4555503080302600d00000c1e0905012009000403500c1c600c11645401d07125542e5001b07a130041214464401e8660703022108050300201d070951b00c11041d2908015a0a85104c00441144540300710300a00900041000250b29580042407104226280c028450054002e03040010a82120007a0001700952310000d1035141c29401944541c500881c01d548050a113144e1035002c016103441c050341031000304a40202c1c1c0c00342c4490640300e43d501a43c20b02c4298518014030100140601e1080c4100850036083c0c1c1da80c2c410108010705650210060039200d6842e40c0c0240c0003845240c5607141c1c100c144a881030300355030b8000010030b4086010801c1ea0240b541e54404140003416143d4080050381082000c690f070383c100104403820604081d505c0116000140e210142142c005544002c0c8050312007006106200c5c20b20a1807030084030a01c004c0d4a000d1442d11070340c0d1627000300e070008060b4a0700000803443d113 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 478497266 1250 478496016 478496069
    0x5030c070b160b07051b0f010c0c030921120801090506010306051e011103070c090c090501020604110409120302071a06010e0405060a0302030d08070305010e01120201050d060b18040b060a09 83
    0x40c001a007402d10318050711801b02a6075120090303c411055801c5c0340300084518410800a1071080d4561101c1c610141481004586054107603410060b2400944501000c513027210f07861b046210182c0c4480c0101d5051900510503038400501c20360505007040302c104507544450b180c0c1412040500080d006482d01c101c0120380620743c0c07078000000e41c80302003150418010304900d40012188502030410040031001e00582c0c0303408007485042d015800010004020171981c40740c104480000410010f85a02150790f650105d1030718000348400039a01081c84c00800c0040d203042080020208400703096031a00f071b00003c1400c95840c24150055481c1c40104103603480b41211000070355130003000c0c0c0c1c00d004046035004110300c00448140700040e0405000007440013800e101c2c80e050300d01d680b401e80d45944540d00103481c240d110301d400c4102c180e51100c0005612501d4809011a4035400d5a280d42d010301700c80400c000d58014118240c414402044800c0d40d803908440380340101c030340201041c0025a140103c1108 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 478498516 1250 478497266 478497277
    0x3030f0f134b0e04083709080714030a1509031209030207170a021008060301110301050a170f070b040f080a35040305030c070b160b0705 60
    0x142110707030019400c00e001c056205601c0300c20b084203503488010b1400440080007039400d00701400440d420744052200d82e0b0a1010540c0c06400348110b14544284019600d403083d10f03800c111404009010011a0300120701c8144520045061801420303481c01c02503510744682d018071620000010016012582e920140f04c039203211500301c1c000802041000a01c600688107240c0c08030000b0b10304480303003185a40da80c49410507458040d4003c2c50716504003201590101c1c16212440d146100d20b201000050340c48440c0808000125134a810440c1401024503081d03e00108000d202c080040c80180030588030007000c0021030b1210303089070590342c0c0320360503141c02c0000881d02140349010710796000c00c8001c480760007002241c103841e880d800010f0fa500d9000340c8940441d180103286105c0e0310361015200010103078803100c03803c401c5030b1144020105421004d141c1d000d07030b00480b4141c1002c100004e03403040620520005121391416036240241000064180c85c0034000014070041041303010680081c480c00545a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 478499766 1250 478498516 478498529
    0x160809070302061c0c14220803071104050a0e061f0b1b0d0309020112050a0b0d050c210a030c032c03070504060b1c0b0d150b03030f0f13 60
    0x3603661034140ba00c40c940f40101c80c041c0c144c0783d0030300c0603c55072640308441c0c0001ca44520810542000c880000d2800c0802ca8943e08564541010001140318042480101000d6200c1c00d012040000d4501c107010907150001d250707110242c545042e00b05c50700d401041881d4048031a200050502c00344064091041e0f403580c1101c212140d010031100d400d05544500c0c0e0009400c408215000d54440d000102e0942d4000c09009001840035030001400116030b400460300401d00480128006c403441010464400303580c04182d0381c42d844000c03141c03014109540c646460340d4150b840700c2581002c00c0b800740d656007003071880141004400c80148052510907100c20710076545e4041c1108090008070b041d080d200f0900040300c1d1090054080005071031a01d407150208130342d2400f46050800aa1228002c2c49800c0c4824140d00c661b261394500641e660740105054640d4401c00512443e0101c1104000480e640e107000c1c50b019610401002c000781801c0700a50b010340d03e121300003d5030b07070486520003e01005680c1c07040c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 478501016 1250 478499766 478499779
    0x40314011d06070215040312020304030309050f03071a04050d12020415050714010605091602070b0d02070c12080f07210504060e04091a0603191209050603160809070302 74
    0x1c8810001c0403465500992903682103e40032000102900b8000009540040128a0000f02d01d40c0c0d0381d01035001b03140d00c1402410005052406034495900b08185c81a840c1e0b6140c00003c0c10f402000001f0401000000303c4400c3d042c0946025a1880e03075401d9a100200203210b80c0780c0b0241995007050701240c000c1e02c0315204c003040e1b0003035140e4050480d800a040403901d114450701c0703410034208144150f030700701c0e203000340711413016210021501150b5483c9000c0d0300850040070800300307040d5210002029690207030000181e440c241401c1c148055482c64001501d810201c26204021982c0f400c00d17218110481020207580300040d11308145003041c00c1d2407410003030400d07980841e102500300010704101c03401501c404440c803080c04108000c440051b50000c1801203c0f81c040d50760050308440c01640860050122100750000814550704100248001c0703c9440340980c0075800c031940484114000c140c140c43d4181035044c91010000c10000c0d0142500c10804c0b20b4001a4521004111000040d500075004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 478502266 1250 478501016 478501061
    0x90f0609080c0a151103161125050f090906190207020d0b0601030b0f060f0a031d03070213140a090201051b03130b07080406051810180b0f04031401 65
    0xc1d130b8a10149411050520318082d0030314100114141120310800d4141846104074844032400e907442d031500207001c801c83c46590190408420742e07000124a103014030740030821403803500d0108010002014080c0d40114409814080b81900010749603402000c1c14100c80301d040c4905d05140000e000d07103900a54007010500d110418000f8882665000d239000307030781c180500035580c01400007282d0340d22036a5410001c2000200c95480c1410040c01c2d640c98680f40200342c25022446601d40c44014945100c801c0e000010080704500c2c00403400c20031144043c2090005e070540102070420000010801ca001540310a01181168801c9084071107100d541005454400c1e0500040fa070b41e6040701010010140000c14003250f071440400980d14215489000245002d08020301103030344d81c01054041c4a03491031208000c0381aa01c4440145100c2540c1d5a0100c0168042802c940e20504540c002082403208004100002d00601e0454003a2a0000107000d07001990905180c018004682c101280322842c074130 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 478503516 1250 478502266 478502273
    0x31112060312030406091403090307051302390c0108221b170a080f0a031e1407030c050405060a020304091a032a041a040c030203010f09090f0609080c0a 67
    0x5039546c940900c500e106011400c5030a56524403070010015070590220808208038944403034401e44020b034090b009410101100c4014401c14410018185d0030824540c42151307c0c25840764608030740c15004000c1108041c044006001040701400c8050354041c01002003002e52504046480304680c0300507907000f4550090b140031910b04044c003c404622000c1d1f20860ba2050340080e070380b4070881c2c00520315031070110307541c044500940c44007a04405058589103060402e400ea0505080034560548010130019901900c0d4225408000d06803414107140410545d001540030081d641900c600707482e000c0c0e403407442c1d00b0180e01e5405990301c1500800d040000500840c0c5a26a0351b81854800fa0105c9040c002c00240002009040d02703403010030000c4000d090030151a09401a0b10340b81c2c200f483d01c030445142403011a0540b01c1d4082c2d82408650000b0040101d0707024800784800a100c11102006500410342c0e982c503030206240d40151034182c50302c40300c0c800c2c064004205c038280072038a030855140241c10318 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 478504766 1250 478503516 478503521
    0xd11010315170106141e0d06020315010f0f02060c131205030d0b01050315060f0408060403170105010f02150606090d0c06030b0609091305011b1806031112060312030406 74
    0x703000c2c20440d42003480000c0c8002c0102030346400303a0340c020f000002283c0c03452207002c0101c4200642e0b0340e1001c0b1543e01000881d40034030045000f1480206050b4000d10b1082c009801040e038141010108840c1100c12044240c0c04184140c00000103110140d40e036103001e660f1800e904844c5c11454201070780800401c10044e0000052490460351003082c018a8124001512540011246001c00342640d4002d010945003280041030344005e5102054141503d80c881c0c1c61518008032821004106060744800d102c1442100700e07801007109103000155218104002501d1343e0400952880384a450310110b02e2136640d00050320301400003c1d0813a0a1541d15043c401543d4945100f0400828034000c4022000d040c12411190306000c080c1a51400d0b071102d080d189014440d089055845560764580b1b10861040032800283c0181d090340c0b40c401d5401c5851003d100b41030035a104d103003030502e0510007000301e580f12016500340603000110803c09542c0c601c003280c02c6c0750165030903005003000001044200011607 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 478506016 1250 478504766 478504799
    0x50f01110c030f160f1a0d1b081008030c031b0c090c19090b0901120f05150406090c080106140d090c2405181206040b1e04020d11010315 60
    0xc00113003902507a560f010340344040050040700a120141d680d04264010340000610482d407454074005004c02072081120607101e070f184840070010300d0f603a050041c11b0b50641802c2c0007614104001e1803038003c1c45c40c40705989109160310700c96034903e01d4520541808060291f0804544050003030300c02490440b103089002da0000c101c01220b625001c2d05d00044230320840309030701914128005903190505041c01964602013030415080b00941701d00200d07007082d46d00d0245c907010342407800e030707030003100d440c880422040e503003a40c21007030982e8503024034040c02c1d55105409604640e081c0c202880c04d0a4140c07240c204500c030b030511140f4140d09100c203050810446052100c2203c0f82040c08650003403044008101031051824094005281846407000200790000c00780e00c400801808c001c0411440f2001c47d0030312070b00b25402d641d080321110800c2003421a00007008004040e1501144081c909540003030510076400c0400b030700c0c00c6103862010a50742d021381d005007801c0c914040390002c020382d03410200344a03a189 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 478507266 1250 478506016 478506043
    0x1080303040b0702060402030a2003100b010207060c150507020703050f0a03030c051207110328020705010804170d0f0911130903020c061e0309160b04050f01110c030f 73
    0x200003c490b075102140c0203000e01d41c020040c0a01c042c03c5d8075000300101c0001c0c0c0c03111900d510301d0101030340c03a5810800c000324000c20020200e03191440900190030820903922007414403a4030301c581e10004a200820392020b030b0301d20000043d01e8480318030403803030003185420040c407611603440780751201c4100244140c500f504c130350344c140902d10107400120342e03e000c2d800c22845181071080216410718011000001c003a118401200d0900451402810b00d80d6143d40101d18083d00a06c0400311055050000700003a0070b0a080020303140c00c15543e4a074808440c0b4105044d411800f20f00c070518070070140c1103850841c203e09001c0c41012400e003843d03441c00f1803200901b442544601a01c4480349003074080c605c540741c0c240d00982110a403d0050041590064807030340c480c80380340402d00e02150b0f40400030314040c800901c001c01c0840c084008800d40e843c45078008001d800307002d2204000998a030b40a10055090a180c00301010001012251814580e02907866040c0652034404055000020310461102a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 478508516 1250 478507266 478507283
    0x930072307060f0e01082d0a05160c0311011104030b060405090d020705091b041e080c130f090507060c1b0e0f1008011a0f04050606180609030102030108030304 70
    0x80d034407000e0b1602180301400d80f0116550b900c00780c000d903008500440d070003214030a4880142140804131405081005100240041d62001340b000250300c603c510750340019203042c84112000019000f4201188001008041102000c01c050038400d081d041f0146c0d80d5860240552559240d02d0b0000c030101d011030f0303154041c92610000801c0503800095860441440e034000d0b0503004d0a060520a5403c0c006000040c1e851902c01124410240c000c010002401100750945201d2080304028040c440303a94031801507584000c01e0350701c130356071074281541c07007103041da540040c42c80358424110015200c0054003620a0049400000d08241c02102d0901c98900c9a0b0348130b021052900819100c0f00d0b201c0c001ea00819801d1130004000d00c00680009800201c1540900c04103662004000e094610010501050508012100343c01f03007000340c6c908549010440d024040c514000700824024081c6415644059002c100e03444004c2d155401102c1401d0400b5009643e0f968443c0b00322550795200303503411030742501d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 478509766 1250 478508516 478508519
    0x24031902211b040c0806090c0a0507080c01020304030801080706050a2f100f1b050c0f19110301050417030a02070b0f01060e03030c07030201180e0f07080930072307 72
    0x18845d030301035480b030fa01c003c10040c000d4645130071071001c0360080300c400e4050010030080040404c0d4507001074154000d0440c00560303645882d00d0300405200b41030b8045034165000110510640307400505131010784d01c040c0303083c50030744241410040f05100d002c187e0000440c42e1440486680300041450020001503200600041c50301c44140c42c210381c00e100c2c00311030308010441000e2072103204100418800403108111881c414840c507005040c820756071100780d100944288810300300003070400740780201c1d88100c00030800ca19003a10f41000342c000444451514100002c006450b020380e56050340d0314103800a0100312a854401e05292584901b0b004040c0450801c200d214054640002220240669100074102c07080c9564010f4401400083d4015158000a0004584508010300d818800c08030401c40581c10b00703098034080d042181c0a404071603190800c02916100d140e11514070051044c18209244000c42d6100840711340f0b018120000700440804180d080e8040c0780c0c004801d12600051b800e8030801c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 478511016 1250 478509766 478509791
    0x60507020f0d020409020a0806010f1202030607300b0306060402040b19051207021b01050408070311040204030b010f06021203070c030c050c0924031902211b04 70
    0x602a55800a50145101ca0020041d040ca40c0410075260710161010030424003ea00080486140e5000b2942560108004010840103101030000400803031160700c48010040d0082515054002c01e490b05106844801c0c100d58440c0400099203403984251910f8a40031241e141c3c2d000e03007241c204862007481500003003080c51826208403000c0300c00b04440585803040d02c1000300440258011107606121042c8400d9100d102c88108080c880d10995000d0501e0307030b14042c420184040c881d0510703070400c0b20602040c0202000051101b0590341c114040b0300352100c010000501038031454000418109000000198000501880c5000d5070419020303940714442c502c41e1000f8500080ba0443c0000715401c1d03009001c070307000700c0d8076880c000c1c0507200313960309503001c0004103586441c2501c16401c589440001003040f400203e9865000304000c6000d0a903100c88160240b240c9251480c0283c8241c020301108508a1200c0b844421024089026500c610840c1c4040303100240e45c0c055094000ea0401085040c02d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 478512266 1250 478511016 478511027
    0x1e0a0308150102030703080907090c09080115050f040e011e0e06010b03040302060c03190504030e04060902130902030c0403140a0201031406031c050d0501030f050106050111030a0305061c12030606 86
    0x107071407040e070084d818000302d40c07821180c141014060075400c1c01400004540c07040035010310708441e0b0440d2a9030403031624000c002400c450026101c0c60010400b088244441d9545000e042407016080b1400301c0d042c07000300f09050041c900302c040111642d44d8807951698411051300080601c8d148603080d1111a80c0e607051007100782c44102e8005005030814800034043c1c020300c2000d5500503c1c1c3d458000100d540720074070300044a1040e170b03080d03012540c001f4050740d075803920f4001c42c40500707507040c015810f10070045141c000701e041078010141507980200000305800d000409440003035070840602c0a541d01220315003502c985880070300707034000390804502d02da000c08150305260143c480038005024600b10a82001550a4044124020000200f00181c1c00946c81c0c000c9501850080809202c81522072800c1400c5030441d0380803030306004540e240704660038400310648800c8442e030304011805950726000900f0004850140c6a1683d2109682e00c0602801d1002c880101d10a070b2002c024107612940305842 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 478513516 1250 478512266 478512301
    0x1b030501240815040504140c0303070b01050906060c16083a0302040f080601090b0102011404111c030314100f060c1106070510240302040c021e0a0308 66
    0x10408820007820461500c56000e8507401250164484000d1000100080c15030314181c806554528041c01164800e0074248400260716600320002e5141040380d84d039210b494001482141e2141e000c41c40015078948030041190300d100710107000d0b58610312000d101803408462030b0081180b00d10505085e45114030750300700ca898458074446120a03c001903071203030b0755190254078040b00030113800707000c00601134064008000280c11150040c100c0340d810160300d0422102c030194018110380c14080300c02c041c0488200300c0c41e04140c0212550300b0075070000021a500607860403c01100e024005d103e002816415402185402031075800780303400f038481401100ea1700c4180c0c085e2040f075854041c0f0410849008042d611000343c80f4054007007540008800081143e0031100e8152143e0b000202e0882c455810761003480c100c4034061039200d10400800191f85039584c8507000090181d40d07100d403205002c40c02009406150140e0018100080744040003180c4c84c0d034030000080340410007440100700204215415080c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 478514766 1250 478513516 478513559
    0xb0f0d0b0604210f02041802090a060b040b0d0b0a061d03010b0618030a06090309030215031005041a030d090906050301140c16050303090114010602160302130b041b030501 75
    0xc4079041c3e901040041c0441c905001c541001d105004000142c0f21405400d0101d841c0c11101866207059005002c0700100043c6401c2501d860250140600d0b130f54942a5801d032014441181d8841ea624880440140300307144a10f540003400d03010008482e640059048860249141e00518010800c000c2c1030996210384a0903a1190045c07240302a408004901c204486070002c1c102d4845060540b154412a50000002d0300010354681d014070035421700782a44100d40d5100c20090341345140c400600c1e10307244050b001d800e105640ba000800a0f900c424421900c000100074161100030340c1140018007113242030311030022101c0c102400003550345810701c90074101103143d6446d8280f586e6100080025070744480e426a00c0300494000003c0480d0080000c2c41c401c41001e00001104814030341e1517103040f10164002800c41d407254951103031b00d91005444508603581658a4141c000c80e4191543c003030401440419046450003072140310501410318192082071542d18200050b13601d801d071030380710f1009079074040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 478516016 1250 478514766 478514789
    0x140303210a090f110f370b1204061107080f13030f051f0612022110090b0708060d0f1a040605070f020c03100f02040b0f0d0b0604 57
    0x10038503801008141903000140080000701802a070350340800c5500f2050302030310b04813000c2c040f0001c1d41c03c02107030040036114120b900619200c1d18140507440b045c0290a40a081214020185800130200300c4410142084901c49512169106011100540c00b1a415555241080d4880d84890a0300e000c82d5851074000c00a680b6120549545066981c0200340c1d40b602030000070000804101c404116002c030034401e1015040005072500c940c0e0410560011280c8000d18100041002006907010320319040d40c1520807440055084c45040f280c00380034244946140102c90134456501c505034010741c082445609510010340b91094100c40d81c01046540b5078011454840c1314001c02d49507030101c00c59900c141101c51101085800c21000030b030082e0380440c0c030103455506004407140c214003080005a21403000f400c070300c4180d40009a5078040030650500140c2c1c0e41c403103c000300c00507404540160034030807039060751042803400d40132180c3d0082e041c8426032464040d5800b0a403030700b032041b074048074041200c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 478517266 1250 478516016 478516057
    0x61f0605090a030f08040e090705010f18092f0a02060403270e01092019020c03030a020d1101061406031914091b06030414030d110301140303 62
    0x180c440368051206190300080e20300c800800950800d01c580c4550f441064a90b032560310b0882032054000c0086e01840240d000401c0902082c2da1203104406000c04da454600e4204040d0242c4a50120003130700081040c609002501b070041d0400740185814001c9180c0e00701c452040b00311141a0b90081050750760040c3c0200c004a4082403140030350650a041081200030322450b40312503c0d4031400c640e03011058500e00c1030010401d01019100c2d10381ca180604409285007201741003880600d01c22140c032030024150629100c8103803482001000503120b0054100e80e0b03185000180070f5540d01e11a040800000d1a62510000551060143e0400c071140701d44200c106402d2002000b0954100a00070400049403031800c000b80303002c90061564601e01070800720110b04041c8d85080c20110481981441d020030b420200d03409480301003c0700d501c0342e00907045840175402c4800003800d43c030422400503003060410fa24800d020319030200650403070303006000b04101c8107414030a068403405806040c5502c401038510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 478518516 1250 478517266 478517279
    0x40605090f01050f07110f030c0c0109060503040215030a020409061e0f080a03030f0f0203100911040303080612071802090a05090423011d0c030d0e090a090f080408010b0102061f 78
    0x140b110000301060551f01c102010407011441d41d0032298004840e0b034080c80350301d41c103075821900c40c0000e8002441c20910b9031800703401203100200c0146400d4505400080059035099855054502901c00e480085c01226510b030390110002d400075a0054000c0ba001200240414101100c082200c400c08040c10f41e00c000350f10280c00416007869002180b50315602c0c2d461810769a13200852244882caa40c02e41d0a42c1064101c1702140e01030b80c00d45010b1039040005202198000a44035400030b02205c2d5842803041c03207200c142c00c001d0154010400010031111507010a40076402401101600759110a40301e5694001c2001e021020354001d0444d2314208001d40c48000070340700c000d1800c56100004a80107400c1e011492512156401d250400c0d040490900080d01c0c1c28042842894070702c1c6002d4841081050010302e01d07400140001070560796548603802000748038103141d403a4079080b203105915140d450386554042e05080d400f10340107002d42400111003201c1700b03c0002100c1819900c03012400e04000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 478519766 1250 478518516 478518527
    0x120103030503041a0705030a060f062f03040e041a280b2701290706140c040905090d0207050d02010c020607081201080a031e0c0506040605090f01050f07 67
    0x38000e0707903000c2c012500d108404d000b920b1428003070006580c0f01d41d928075102d203a4504485213900030700c0c1c1c5400055020042c41f44c1c001e00d026800074010020815104104045c0481c55a002c001418507000115002034440c4844800d0382c4114007034603c5201c1c81912100c074290b43c101c1110800b4543c0300ca1900080352200b40a014070014030f48400014264100c08000b07080e100b2540094090300724050b0070701c0940c44400c200380e030040c481e001520003543c5182601050300300300754401c0c40402e400402c0550a010707460300310840c0305841c0d0b0020345050a10071215000f42c0d0040c041d08007450709140114291800006840d03034942000d40c0034120581c105804c101007502400e20680c10413075155036501c056a46c4d0002011818401c189035a0f42c0c0321000c5140c01036407416030101d081c0f500071072400c6000c01c1d0810404c50349404400d4041c01c9041410300c0c243c0d42040380e960050182c0c460442044108500c81d80a01c0c040c001110441c2c1716000004081402d03508201d60140944052401080f03c10703001c0c0703 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 478521016 1250 478519766 478519771
    0x504181107020901090c02010f0b030c010302131505070b0112210908061501030c111f1b0206060a120c05060a0302072001080f04031d0f27060402120103030503 70
    0x508940c0c6001c12580015071600402c0c1c00c800440c0f59150080009a5024402c050902c00000000e01540f8500f0b40000d449282e00790f0711505050300050120080d0390000105d02c05410144a00031a0110841c8024410303080248200e580340c03440303000814544100c0c0038407810942e100884615003444c41242100c0441e0170306000b02403001e11100800c00c00010f000c0f06104000641000504000180004081d511310800540c203024698103840880341c40841d1010324001e52008000112069102ca00020120030040c80306c81c440254200310400d030701040c040c1c01400704884020100d5103070180001c140f0152140144070340540c01080295040800c00f41c036105005040050030510181c4481d5284884419140c01d94039800d0764206840da04480d219030020074802841d8030301d1400e542c0c0649118042603400003a420003d805100c10f5458990f02c488020018001c3c00c0701e01ca155403035410120b404d80030481e05200d0000080d10310b0800380b007507401c4041c440b102c01c0c07d0f40e444d41d102560640c0c0003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 478522266 1250 478521016 478521041
    0x70608060f0f060f1b1e100c0c0b010e070e060406020307022b1a1f091d031b010f0902030a0f15090807051e071a0c060702010b10050418 60
    0x601900c1c045808a002400301031000315068031190340d82d1840c0900b40042c10555801d1100b424500d0082000d0008509460047c075000000d00713914910003d607510107500d41c0013043c06c0c031210004a00c01c0a00002980245131a0701c441580041c07030700402044e80641d001e80801a4000d001080141c074208180c060000302d01d407550385d09803810f201c1250129150082c01d0f504c0d80342c1ea079401c10780207005459442d03000c054000d03132070001c400700c805a904d0f0780d04134881c1c0d00c14140c5444501d20441c051025007490a044002282e50340d080890f85083d004480702c548140d15440c24a1100c0141501e001e100d00c0144c1c002c0c05000d00801e0b80c0e44400c4203030440c41c01920005a9110821885020361142c0c40560740644005d50b01c400f074928007180b0307000800c0d40340540c05c4640d000218a00c140095003106648003150b0244981d04010410150b5001d030180c800d9140c4200424400c07016019072040003400401d032419403019214010a5403184924424031217400071a07070900501556a500000c41c400c030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 478523516 1250 478522266 478522279
    0x3309132105130f05030f060606090d111e01030e0321070525020a091808090105070803041a010609140609010c05011a040e012003060315070c05070608060f0f 69
    0xc0a002d9503946015401411200201d18002d00c61403034200301d001004041e80c0300502c0540341000c0415100d0040c6003006010702c00384440b880c1044407010400c542403d01428095000c9107000000500c0c540c1000c0e114003003468040042c0903e40b000c811518050b0744080100d8810310600350085241100400d000200503007485200508a05004445459812504c6a00c20a24280104080000700307503c030102480c50013100d000c40214103000c07088402e4001088540312658080160348a224004008150380000802c00c0308014207202d41d101014820550b84603942e80350201500c0d222414024482d03848111080c03c449441c00e540182000039062400c072840701100e5981d40e080d54040c011003240c2d80c007900c8420400741020b1241c982a040d00308000d0001c9140011004081c141d0451100251000080000d096840402003504c245986a0303109401d8601100002c1c294540c0e1801140e450142c00310002d48d0318421034415000b000000c01480d60b0b0522201001152505044210340141 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 478524766 1250 478523516 478523527
    0x90e070c150b060723070306020a030501060915030f0204050613031101050f0301170c040903050901180b040306022203080403050c01080f150d060e01020d150f0308033309132105 78
    0x1441b005000314894030005d82c54980c0ca08010b4107503079050b0001c10801c00e00000420010750f00c2502ea04102065003400600c424525440c01d0103486035410a070740241b00011807060724a0165890382c112401400c80b15809500b4400450350b51240c1e101c1150344c1c1c103051005102ca00100c130320310302500400800b01e418031040040031506541c1105c20035004240042240c0140313580000200c60030700e015411809100d410240502e69602650001508055021651408040800b0168040c5542400700c0140307603603881c680107030640d0050001310388601442810b01155401145c03594010030004440302490b5483d81c940e02650a98110b446601c0b04c50782201001081c114400c8030b40c018116400543c0d5051003c0007a01900c101c247e5020141510380000c10240e01c1c0088000d0070703a0b90004010b96a42c42c0d00f0140c1c0b0000f4480b8040342c804044172000c1b4000c0d5040c0c40542110304030281e6035403449949a003846020300c2c40489000e4132408103400c09103c50390180402d00400011400c00a0808 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 478526016 1250 478524766 478524833
    0x9030616050403022209060b19032406030c0f0303090b0f03010501050304050a020a0f360507140408010606090e07020604021c0516030606150e040b01090e070c150b0607 74
    0x507010646c00f550150340d40e01151841303040017290820032510b46000c901d960b40c55030343c0700b01d510010140440c0c03001100c0c2041030f000340c2241d000340d0029508900300007201c0f511030b007002e80f100c1e00910044021a1401d00005094000e070825200341040303402030181541e10740300041d0b80d00e50004104a9450040e0090700005a541c0081302003d0242e20b011486860300b03110795081603070708034000e0740505091180b0252400e244039007085000d1048100c04a0552598a410740c2c41081201118400b40d901080105108034154004801c9905d19942c071010f860755071583d4010841c05541410040c0c111074002809400c010080700109401952801185003443e268581000c15014000084000051040060041c20f00642e005440c0d41005001544007603600500100016507125015680300c07030700c03071845038095900340700100b01c1c1c2c08008041b0b00d81250000d1080000701402c60741c0741c8005001d008408804e00c900750710910042e041038548075803a00c42d541c81d10386400002141ba0300c1c40ca0f105ca40c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 478527266 1250 478526016 478526021
    0x5030a080d0c120f0f050c180f120d02030a0810030f031d0406030602481c081008120a03020d0e0106080604050c0409030e0603090f12090306160504030222 68
    0x6401e0fa00d000611178280e044008242d50f80982400b00302e4038244075400040903401d0903020440b104560706404000110081000000050042c00c0c29020382c00529240c1d6801000401c0c058005549102d038664503a07800080401213400050b01a0980ba031000c80000d000e088000301102c0b40000c4c0c0031101c807043c0009820f9a1994001f00c6003a5000b00704d1074101c0c1090440400c401c11020095402c070f0140030b007080005840030120103004407016035560f60440701441510420b20061700c5112901a2864025010800030303900081b40f500c00c00e400003481c13040031504951018912001500d88407071110100c000e50080c98000c0c82d05641c4d46c0100f02644400d118203002410200050645450681041420500e44100aa002d04c0c249604000080c0d840103550201500444035951a41c40e0a011103181a40c03000da00b010a11076000c00d4408030303443c1c0010704513003441103040300c1050b81d903020301484d43c003201d10444020540a0000b48014039000c0404062a0080089480c11481247c111802d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 478528516 1250 478527266 478527281
    0x903110406081608011401080606221a030c0922060212090610080303070c080a02010f110c0f0f0a0807051501060905120a12030209150409051005030a080d0c12 70
    0x10f400d0050080200080a00039524241004a14000e881d0301d070495181c2c41e100d0041070f0368482c480740340300201303c5061a00c0340168401c030500104240352904030110702c07200e10721000c1c0788a80303c3d1860640301440e020419621810310501d103248600c0100c0c6501d02c0c40649548100c400c1e940a01c2251030041280e0b103143d00c40c0c03200361f000780f0043c00d00c072040b00540d031055008804a60810410030288a41041001c0003155024003859a182a0000228014000218007101903801d10081414010342840503100030f48200043c3c444040207140d980b60f55101441c00b41c4000e410000215000c0b03a80c0e1005003a05134090019030300c012002d08802005000c00b600840041540c07000240711070706050200c4441f8a00b0a4000c007071200045e250b0a980452488050040603000116803500e5101c60038144034019015181c545c4540c0c4440c240c0c0060041111100c1c400c0b40a00c000113000e00d40043d461446507000858030380b62a800c0941c12015216447d400070a10141e0300c00400c080010384123044 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 478529766 1250 478528516 478528543
    0x8070507140303072007030209070c02060d09060b03070e040b0705210103150504030203270307060e09090604151505220e03030105061803070510020d020f0d090311040608 75
    0x169685481a006403056480c03034902110440004540e118105c0001114401c4c3c030707011504030b04d0aa417244030845920980100007500007802060089507038410743c22400c02c99106d03100610518003840203041d40d400c494030800360b96a01e04004140420482044035400c43e4041c80c0851401c2204030b010101d09803020040340d17103002c081c0b00410a0000010b0111806400200e040c0864206910000d54a00803d10030b01900f64101101140d070100c0086400741400700a009e90362003d60320f2a0140c0380d04401c0d0b49507401076251a0008071040004248180b007180e00020a0f01d003110340c0e460000042c9989211740d400b1040c0b101d00070a099076070901c8078020701c0300900101ca851a024110005403602050280040e83c0180014081c075500c10b400c1e83c5140c481f00e0b107080e40e0707548018000f03444e03ca2103034062030308880b52040a4481035400300b9004549000fa03001c07100b08200c1c511840390b580011032072030400a81440010300009103404024182e080d401800462502e854000b600e05102d042400e81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 478531016 1250 478529766 478529773
    0x1501120b0d0507180606050f090a03020415090f020408071a090d11040e010c080703090203010603020604060905120705060f090d0c0816060207080a0f03120204030b0105130c0c030807050714 83
    0x130861081486590198183c0d10074080c000d861070315401405a010f1595560340d0b43c00c0110349203a0944640c8901ca001719002802070201030b084c084008025500e5008120b4554103005081c00c00c2e1440f40200d40032140c0d454000c1280c0c51616050b41440c5041e03004140780200204590400c683e1a008501c2200f40149221406c00c20740100300800c843c45100c0400459050074040c0d900c1e141c0000283d0b1b4001158207012034450310902c002401001250002580060003160100c0c1a545c4100b841d0306071441a10b00079100c00441450b00e54407025407007000d901207400c101d2904c2c01da41480c003411564001a042e01002d080c159503031034410007250021030780c961144050135400c07a210307120800249150b00181c10710a085c0751125403501003060380904000034200c45101050320480124121002994045403126180c0c640b030541e484003031040611895545501003400c0c0e1181c811548014807070340326508115007555040d100040d00404201c00c1c841c05210201c0403949945200b5081030829028 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 478532266 1250 478531016 478531019
    0x20306040b0a2411062d0601020a020f03100213080705180105040f090f050c010905040b031203041a0109090512090904120e040c03050615031b09030712120e0105031501120b0d0507 79
    0x3c6e15456101c0c40f0300d0303610321100310007407001a0741c0118034403132100e4040d9203083c0c410703c1c190301181c40c1480c00d004074038005200042582e43c240c122400c00059502240c160745200d0b030b031102002000198030300b00c80e41e0400600c00400052609030700800b4640c0313601d4004680c001700d0341c4500c50b841100725030903260380e0800e01b813220311507034454083c0c0c010f0401210100424440341011a648503000e2400402c03104002001c10117100f06c124548070403c1c462031245a0750360b10b580c420400303019211b0080b01c080c410f4030306c11907a48030070005884d07444d0b50161110400d641d032a1240d4401c0c0702804c100b04213010310045001e8464075603010b0141580305544000c609410490b0602c8600c03034001c811006249018001e0040c01d01c825118882e0341c042040c010b580316400e9200103410500164800080340c207a07410058100262102049040d81c49512400e00c900402d80c019501440111103111009000f0050401198002d80510040c0105280006182601400801d60034009030000751042d0b03000040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 478533516 1250 478532266 478532311
    0x20903070504060b0702041407021905010f0903180605161112010203011403060a050103030507080a09051008010924051207030f0b0f01080d0210180510020306040b0a241106 76
    0x3450055040321231000096242c0440000d45507628801d541966485030046441401025041085552182c187c100120303910340c40c01511990f0091803042c88428400d01c001351a1f030044003540ca42d090400118000c501450356400f4420b600c101d0007035400030300040c0074440c1d88424405940038145a078102070f40071180f0301c1011b1a008008159004007400c020040c00083d0b400403c0d546065031000400f038a8048060302902d05015a412a6030400310400d4a10501c40d0301c000320a040760351f0340c0420880303403018690009009007504244d810f60075111800304180e08002001d509070640d68416111542e4986d41d47c032a800305108002d85e0100310440c2400100580d40c62540e00504c0304074010b010585070410302a4a91880d17140b050040c9503945a001a01700c45c09800d00d14056020041d50b800f1389a001c0c6031002900203544050180c0d180030050101c5090042c500070031b6401d0300c49080b010031060380d80007070807021072000c0608100d040300302491640000c101544c00b441145554542e07074401d081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 478534766 1250 478533516 478533521
    0x70f02060a020f1b0f0f0f0108180d200105041110031d071e0e060d08090d050a030806010212120a0219050a030c0309080a030f11040f080c0d15020903070504060b070204 74
    0x2181c180c031804001c100396030b003540c44152484070400c0a08046800e540c406c600641e0203400100c14500f0bd00502104426855114030b0340881c11044a6443c441c050b80f01320218220758044400801c445540001d118081c9404039400c000181c41e450042005a0420740c403002200e813048418000d075001c00f80034008c185407281c5422150044285da000340914240080a5220000c0e040c00d000700010b07140c04043c001080208c4281d035002400f5002c40000c5031030081c1da04ca003400c1044d0b0001340c2e10004910158808030300614070718400c00d444c5090074104007910070340f49405019010195401c0000c48a4600303003c500031250754880d2125512409400c1024094809050100c4200740c03030120418001808001552014400c52030001422080e03101320800401c842600b49a80c0b100103d00000c100d80c440e00ca07441511540e90680d09504c0e486402c0c0840751514007801040441c44400d1078190652907070240100c0c907401001c503009079948502240031148103070840030308500002001c80541c140307070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 478536016 1250 478534766 478534789
    0x120a0b0a0e030a0c080f19170901051e06030f0610090501060201050420030c09090106231c0305090604140108091513060608060703051b070f02060a020f1b 68
    0x701075803401000c101c00900c18980d0070300040c0420030202c0d940d46901e0040342500c00c121782c104843d01452040d084060b0405051035907c6100201c120000381410a044c001c0c58043e802c91006115540103803041c3c81000d8800409250b010f2207059041d2800a10400c80a030140c0413184074a60003034204040789068810581100c001e40e0b0410040c031000496a8040030115008150000102040c01c0c0c0060306101500203140c0e4850852003d1014291042d4001e0084071314402e8500504d10594481c41503450b890080180d02c080c2d14038048000440750319603450154400c0c0b5250707140916880008405411940203016407126100d03084074596013118203aa000f40342040188800b05104907403c03050b100017003070752080c200644a903000304100d80e04003a01034184501a215503103803400d00140148402c0f622082901d40c8a04c015038000980e0049560300380c2c00800000f1000c04540a1010390f902c003169501c2144502c0c20810a0002c1c180034010b072403008034520300b950382c0605082040721980d6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 478537266 1250 478536016 478536041
    0x3130203060123121e010618090c03060b1809010f0e0a051e1006080102030901060617041707081603020c0a08150403020a2915030a0f02120a0b0a 64
    0x32000d0285034002030600030700a2201120460038a580e04c0c2c088074200342c0521100308407000c0705625646049410b4106d801910382c100c2c90100ca1484459504056841071003000d0306460b8010020f001150340da030412540f030f0501402e084100845095808801002222090900d941d52125100e160415005083e51024014010220b4820603110a91245d0303614803c2c404851000078a94041d03001480050708451446504020041d515107101e4080e5100303c038060f4195281c503030041441401024140d500c014011240344207642c4994880204640b1003043d1040c07904240000400181c081004200d100030480783c0c4a00d000c0c0516010340b07480001c6484600ca09203410782030040c3c0000084081c83e1160440500d850b07600c03a410140c0c100307818044081c0c10940000c00c0f051510308550422801004002c9501c22940c0c1d510403c4070381400200d690a0745508080c203288007141c80b038403050540c203000605c2a429030b180550040d01e030150511742240c5021142b020800c030782a06220f20041c0040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 478538516 1250 478537266 478537289
    0x3030b130204063207030315060f0212090d020a080c0109090b010e040b0607050102130e10030b010608180d02011a0a1208130b0a03020c100c080624031302030601 71
    0x2001c9000d03000180c038030350302c1d00c0044e90305038801d600301030880c00b0310b5403995039400440d0380c0c03169030034000d020300201c00d80440c05000781c40001031210b00c1604145455100d540c06043c1c0d610a4101d85510b44d404540c469a20102002000000d65200c041e0900103107440c500070314115210300700162044085134425044245418900349031640c10804000d0140000c80d000180c1040140c00a0903038008c0da000540a98800701f040f501e503a84441c01c580c16030700c40101a030195940e40002e201000ca445c0402400076040754010442c29008184150300000700d03503202003100387c032600c0349803402004414001c0144e440385001d0403402c100e01c0e81c40e91070001c10b4030308410440c01c00f8502c40b010703a00440e0090041400007020758004070007499000c00342c011481034a60790595094010007030b42124080e00124010303c1121b65827440c141c03203001c7e0744000a03165480c180d5500401c000c4100c582107018035440c03182079001d400c443e4001c80117501c40e412000080d001c03000c003030040c1451f04005802000048c41c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 478539766 1250 478538516 478538519
    0x605090f0a051e130f060f080706020a06020901050712051804020f09220f05010e0f10060503190207060f0621060f0e06090d0305240d0503070f03030b130204 69
    0x845a941c142d150032000d0300050f864480c10000301e100820480500d84c00d141c50300c14105545a01d9030060801c490b0400c00c0318620139103c011850f12951940301d1040503906c0300e106500020403940190255400505007a410040a42c0380d500344889800d5180001840c001403003c2d1000d02201c0c5010303400d401382d6003141071204603404c6c0c5080b4800c01032400e1050f8030341800c12180c2040c10740443c20410b08070105100e034080d01c00100b000b07040203000320002c034285800091034034a4100720f501d100d000c000e104124400d2038494160b850358400b4150780c004001072204903540001038002041c519110b40c0d0002080c8210035100f07803c90f600f40c2c204501d0803545a401408a050f156506145142c00140000c2e400e601101c030300008004120301c00401707028172001c00150b503001285400030300781c00352004e00855442c5c3c0c60406007070000c1150a201d14100240c40d60380d604000c7c1c00c0007461032042044900d4140c10b901c803100c4103420880202d0010f0303100c1160701400d0901c501d2403540f00031840300541c01d16 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 478541016 1250 478539766 478539769
    0x2d030207180612151d0d0219020102150c090a030302100c05090306070e0a0512010c0f0e031207050a06021204030f051e070c03120c05010b0f181009060605090f0a05 72
    0x10b943d6407800340601da060308815a0842281d0b014801112030710b2180c8100d0795040d11565102d00c001ca40c4140940a1710001000c3d8202e102610314000f1350583c003034070184c010152500034091010342005a02042801940c1a0342c446c818008040c6000e60004c110b046515520007096076807030100403040080510481361f05840c0062007903000040e5042100220002d407000c20f0707034580c040c0d104c2c85d0f006905030003011001c0340c103600403d140509541d1344032041038010429502c00210140c6160540d00581d01642e215600e40c0140513007d1242060307400c528150b0300d0b1340b020380e0042102c2e480a080714406101c205074100b00c14201084180c1003150810340c012098510001c50b0203100405000000f0b00c080400080ca840380c1c000c0e5602a600020503013207090000d10140001c0021100c0c5c0d0318103000c0440c18504400c4550041400030101303803100340300448218407440060310f0740c3e4103060b10110124042000780070b04405451a5074656465414440400c501012141000c600545645005101c503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 478542266 1250 478541016 478541039
    0x31511210c0f121807090906150b090409050c040203160818060105120f070303031e09020609040e03070c081c110a0818040f09061b0c2d0302071806 65
    0x2003800f400c0100d840d0350b10b2030488112051100030701c5205000e01940410424820390112100c1409810200282154800d03000125a10341c0500445140d040c8a0b4040301c1c5001c0e04008103491040081d10b007584051000703e070a03a08290b6420000210b51002460382560210310107600591000c1c07405a170050340e0104d9a11001d040c018a4001c002d040501c200b031043c00c0040078030080019085500f556640d00b0000c6c0249440c3c5010b40ca00251141030580e40c20384c43c015074881c56001842580f52a41d54000c00004280000c000401400305000c48000700348200750041c020150400500704c0e2001e00031076900310000781c0b540c280034000d80500048a000380042e241e1134580d0b010058030354030300410305034510702009840c52030340c0141003c542d0356140419400282d40e50348100c0b01801748802e1544d04890a08038002c003580001c025501010104034005542440030148210f42d41c0c417840080c064a012030005903041d00907a00c040c0080146812001e1040c400c007018a408011140c01e160031901c1c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 478543516 1250 478542266 478542277
    0x1050304080d151715090f030306040906150b25330608031e03010602060406050402060d0207060207051e190602090d050f0d080c04031511210c0f 64
    0x8503a590f0480c25001c2c01e2040d040e00904000741004084a14502185030364141140d1020f01ca909a0004913100c40b400003010b41990b2040d90281d03046541d2141400700401501c02d0940c1d40f1901c0e541c03400c0c840000f07030329080040c0071030700030f44c550700d020740c403d45a00425045003c4500104a00800f40071445681c100701c104c440d10f2242c0c0700401d4141c0368040c1031140307a490300005186403800000c0e4003c400001003042401ca2081d11001341d920a03084660ad010034031614000d6000500020009500d5900c42075215100401c0f0500f800d401c200114100c0c0c006501c00c913100c680c0018010280902003058040d40008100c0250b0203101c0c00c224191a42842541c445080204200702d4081100c82e80550303201000150021060b841e503030a243c0d40e00c0040180c0e110690180030b6000c2109480703040c02c039101c2c2d1386803e8158605407441c1c1d500c1c20020740000c090f038a1655540304803070300401000000c020310b1060800c804600c54503406040000c00001c1c10040014100300109801448040c0a0b141c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 478544766 1250 478543516 478543537
    0xe04030f05040506181f020a0309120302030318030c1203190506030d0f0908060726090d1103070f1b0605180d03090f03030816081302090c040506070804090b0105030408 74
    0x9508401041000400031b0355009482000c0301c030901107d0380000d007002441d000381d880300c803016a074840c82c004150761400060016002000020a951141c00020008460b40d0007201d250a404682103400e15058058a00c01004c0000502c1000d0580c0b6611180205200034200440d083c0710000039070702c80e00251f080c0240b10035221080c4210f4040c2e031000c401000e202058803a10314208100615444000c1e001301a5200549036260820414101d0b992080d070403500200822081400e00b6920000f410004410502c02006440c00244005a10aa5092040c1005003580a901080c116404101d81182c010002c050000542560040d01c503041d031010151085601c1e00c0f43c600f0210744000d020b402444001c84525800400c0652110740d45100d044007141c1c00c0c502075007802d02100c0112003903d14054655558240c68051718041150581000c40700c210035107859035030320220302c19810003a03094546080208007000311204901801ea00c00f507091070650301e0342c6030960351040035005507103101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 478546016 1250 478544766 478544797
    0x1504020303070314190e0108060628050f0309010b010f020a030e090c07081206010306120c05040902031606050703090509060d0b070509130204140301200a0c060212040c0e010b040e0c130e04030f05040506 89
    0x900070034000c1040712001608dc1c1035039175a0b443d20354030060103800c110703424a0004d581440c41030501c52001c03400030b246030790540c0d40c0c860074100c400c02c1140145016101032008c034030800245d00019a90300c02000e1452484442e05064504000007404849150348030302c0c098600c090603500000c002d5a103880c2590301c111000100d8204500120340f03015540e00c08180d07240c1040c4004a0400d0304a006440190300c40d6503500e801e503032602c060202018007658201e400500007403501000030109640c0070307070045552404508041d00c0034002114040c520402240e40307540010148000c3c00b9146040014034016402840303900c080407010904440f0346e840c69800c104c008110b00a8480c81810840a0140c0061040d0340310048546888044041030300c0484c0c81d00c049950001e00052001082412101c290707004a0074249010515040800c0c007d041e00300f40d10082140001941da100500c901403c000d03900e40340140380034603001c0e25804083d1350320001d004080c08100901d903200344c1120f01030900c40700c10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 478547266 1250 478546016 478546087
    0x1b130902070c0506040b041403030a0e011b2a08030405100507030905032a030a030f050a03060e070206040b090303010f1a1b0f1504020303070314190e01080606 70
    0x2c1400c2254035000250702200c0080c00040c56101c54010300141c551600e1401c0034007160310209903a80c8140348905010030351001003101c0b81e601031821603642c4a030031800001e60402556840004400f0350514804000a030256880103180b0394254001a25100000358030705400c00000038000c0100341c03c003504010000a085e001c051007a034503036000340000303030032034400c030b03100d060409122001284000d9408180000c00143ca10740040c0c14850580c16899108254070307111422209036001c10307814414591102c034002018001d44946520542d00355014200c2d905061074480700c0800060000d41041c0d006000501c00012907148030422202c00812450200f00c550042c21014011100c4400c0944075113880000860800704001d914031985001381c640300a010021080550005d940c0a900350b4001c3c001d4800103401000e6055401400540450401001401042d480340d409030300c0030005503290340e090700c095030070066080c3c0088045402904240010b4001c0c8484027040c401d107807005030000752 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 478548516 1250 478547266 478547273
    0x80f0408030907030c060e010e06031009021303151a0a030b0105061b061021030519020f030c07050301050606190f030623181308032205061b13090207 66
    0x30f000c01036500c1031110030b805984400c064109821454600e01064081020545c60301c1c06404581c42078030720b410001d040ba4104104000250080c00350b10400c801c400f0004804190740e0094509034000701d0300e0214030100100c0301001c55018000805010310000c64081c00050b0261018506640b01614620380720408030500b8000c61142e00420940390089105020f44c1940104c0c04000381d4543c682a00c450540090084400145094000d40003070414843c8280c40e0380c41201d6030b082c00b287c0b07104840030305031440d42d0741e030859000036038466069100c1c860070016414280100c03035100c84116a21818074100b40031107180560101c070841c00b003200303140c40550318a000c4d5001801401c00f03030700315400030303100c188030200c4c00155561081d215004481e0a64880080100c40c24031402903c00f081e40d1841107951044001c1d0070103000820032841000e1100703912129060480240382c0104010328171800c1004582c038241c2d20400780d0081140c800c104400d1000d44101c807102c200c0707102c1000180e83d40c52909 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 478549766 1250 478548516 478548523
    0x6030109020c0127020315160c06060518040b06010f0f03051b0406050408100c0f11010b0d0c05100c050c0f01020309120106052805060703050c0f010606030c080f04080309 75
    0x4c51015055100c01c05a4284a08490401d1420707109804884070a41c030f5017000e001d010f60445003085002201042c400780741e841005659617040c4105000b066180d01c03580042d102d0342485485d0b14013451a0740802051040f030344441a040202800e08254031030032414010b0401c000c40451209050300d640104403082e00015004140407070610009803035640700c410090003a032052248036664490031054110381849031060411300e51003629152a0080b0810050322602d403015501c0d40b040d562280341062070744403440c0808074184902c94005880382884200030003c0b00131b041140c10413003200b002c07000065001410410b0844e00311a2001c4d03a4400c100102e10354400d0318904d60f0845202a07005001400540082050b928121100305660b140348101d000180342c90080340070800a07000080255080001c01019698000d00d0002d00d0300200c044414508180030400c44103980d5502800c0280503031602c9600340d1480d503031400e81c505080074000d04100c21006031000d01243c0001011030345101082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 478551016 1250 478549766 478549781
    0x301060c0f050d0201020306180f01030221030301080319050a080604110409090f0201020d050a082a07050703030f030b03070314160602150f070f030c020f0f06010f0801020301030206030109020c01 86
    0x1011903d9020512030000e020350803d449550084500000c1d02c90400030220400344030b1a62210342c3d034400e038659007c001d50f0340d0b502c003101c10005000880744014107400b40019406001c1c0302d401195944119001d0414126400134580c080101c103109900510340c0c801b00e4103820940450b004035280c0700062403d0158402d640c40045110714141e960390800c02c0c20340c000c02109000343c0940d80030901d4480300f17490500c00e007104000051824030006015428040302041c1480b02c5080d10b60100400d41c0318462950302503d81036650780d00000e8204100340e40715800d9187e800d401d18040c04510164800729175a158580002000625110018000503d0030010480444000d04410324910342d1280041d40ba401d04d5801044519040c00000324682c40c0521154004c00842d0f568494003012010101c0080501c010210118002d003628829120420400908201004405002e165240010440784880d9586c410203007640140f00400c0507945107015641103031401e203005030703032481140706131401426030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 478552266 1250 478551016 478551023
    0x10020606150a05030a0c260405060a09050331180c0f0507060e12040e070e03030a0e21070902090a080721080403020907050304020906040e190204060b12061e01050301060c0f 76
    0x188244403680d08214603d00b23008034082d006503121500c3c0c6c8642c001c02c0d244443c0c405082e03648100a03045401085d680f00c400c2d031001000101c460010031021580c400c405030f601c42003405204030014070300c4680d1840f5070407980d99a0f0806801c1c9007220080036010740500380e00640340d917030740344c40d482c030600400e01424502aa038035245950b235a85803000b1110043c000c0e9030b4100025152050304800d820300004603400d92140361030b110311040d003910801504455103a2250f111664040c42603010400130004070020b00350405001d40c403072000c5e03020311002c4030302e541c00342210b54004682040424482101c0b207001801c098003444c0b15103001c1c01d000c0403910496100075003100c00310f4204801d0315130100203140201c4c402c1710302107002d49410b02048140c1e603105080c447d158000585031510103c0040e481d00d6101d01c041d2000c552159a02007043d155040862005c1c41c820ac031104002e0a8a030003501805010b5031107480751441032402000a00d1400140a10000c0c4180e12901000f403001c0c24900403000c40d817 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 478553516 1250 478552266 478552307
    0x9030905060a030617010504150b0d0b0403120c14031b0418060f2304050601020a061d0606010206070e010f0e09130b060307050310050703090210020606150a05030a0c 73
    0x340b00d00040c0104601d101e44a107120b0b500d80c084900080602034039018a8019000303a014041100c4d646d0014510902c000341c0c060310740c03450b640c0087c44030000c0a103d00c0c000c1e00c840070703a404401e45003c1942c8040c0454020041c8400849500031070b0f440941c2d0b000840b1440c00c140d0001034040c004c0c054440c603080042a1481142c440362049070f507400190507240308080a00e075881e511460890b1190a06090b44040d105402c0e251940c0d0805501c000e9110205104070742c907900e0a9215641107030310b40c0c00d00c0c070700300c01510141c08010741003007202c5d0742c1010302071004044516003840c00500d0301440d4000f4a040249000351a081544210212554035000501c03040300ca080020f103070040b6844e1200c040710348120845c001111071802140b03880440f40c001d070141c4544042c15800c100240781c02818a0f00b855603c80c48000941c8a1101201002d083d83c2c0003062a800c01800b0005410551400c0f01c90740c0004201808485500a09036500160714000100311362081ca0002e4072503003c51440a11901c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 478554766 1250 478553516 478553527
    0x604080703021608010618060b1801090f08030c071a03011e0302040203011403070801020a050a03020f0c0706050a020c030102071a1b0d021804090816060219030203041101210903090506 81
    0x21300640c051803c88015a2450b07280407145900041500c8080c0320303545121909214110b0381d03140e901d030f40e40d080110501d03111003c642c450221400d10140740c0c101c0440e0b580b0110381c007a2540b02c02c01216001d4600c80c01c903a100002d481c030380c00000d440140108550394941001c1d20100200d280010009194001d00644d100d6031201c014140080c110b142441c4640314000000038802810b10071144a42c0d640c1d13444602d450003245043c0e020358091041611191030411901044150078001034000d06081c2d60b4060f0345650302c0d1402460000c101a03107038440d07407041082b14005202d00014030f880c2e0149030082d00c40c55540540c0b210740c80d41c40741024481180c0010f0040001119540117029070a01000d400d00151405400d10040740c0e42c000c001040c802c000c010402800364000114081c1d28444d45002d0302e450200a6426405484d104010010070b8011091000308654040c2c0d140d03110b0800e291440c900d0306c40d1421200c01c1c0c495500c4140c20240c2c2d0b06201c0c010725104201c40400341c1001707010165102c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 478556016 1250 478554766 478554779
    0xd020d03050c03190813200609060409050105030607030e0a140f07090b0111070e01091509150f08030a0801031103030d14010e01150203041505040e0a09060c1106040807030216 77
    0x2041383c00400080c3c803240040c030b0401818000e4242c50341c001000600140226aa520144400031400707580310006221454140da91280100017610070a800404d09500d0b0100345858005c1c050000c0081c98280881e125401c400054400240d64000d0030b82903a602212155500348402e11215003541d000b00c90000c24102e030240c0000360010002c5c0c0e02c42045100303041103651100b03c0345c040c3c2d81814403440300410124002d50841103280002c20351b001401991405404110303441088000050050354a082100c4240040341900a080c0c4802841c902840d814006010340d20500008000c5038050b00c0e0421161010000d981e6410403412040010b040802401d2008200922410610800840000c110100f00300358a12040020741c0007542840c0c2040c44510310186100249070810806010000e4035213140113906010b048000c0000908540d6400d1100940d120194490240010b18000140308480001c000d070388550070184250b00c40702185800c82c103020940c800c50102001340c0e0300c040f400b0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 478557266 1250 478556016 478556047
    0x1109010b0910120e152202090c0f030712050c040302030307021908010e0a11010f090b0304030201020f03190c0e2202040f03230d0c0201081e0709030b010e060d020d03050c03 76
    0x19062001d1700d40925035244003040022100c0c100c91441c280220200354001414010455074001200402e90b07800e00301080c5684005420440e01c01c800242c810700720114591161007560b030040c0e540007241d4a0f05055402080d0b40384100315009005000903a20040a0f01c001c1d03000350060140d685c000e00c2516a0302451b243c0c0d5039101c402c01d03107440c580f59040420329030241d440d00d900804107032180028980361481025494000800640c1595004c10401880e210f07010f000b1440380000c0b0f43c02c11540d00380307a907a4800f1240b1180050040c0600104c0e10101d5a4410024004d80200002c081031140304070304018002c0c0c01241d104041d6141b002002004111b0b40c01c40e1240d1081c4032030352042c2d91403021503950355614100e6080901241d00e00a01001651084109940c0841030348401c1c0f5a5a50030071105906510450307940e00007c0c1150400e0041103002c0d60a50300418408940103030318184040015919001e840c0002d20641c40d440c01f540c20940900107a4003510b00160079a0346440c541c09807542c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 478558516 1250 478557266 478557283
    0x1b030708180d0309061a090403050c03090916120e060118060e0108010929040b040f211403010b160f05030f030f0703020c2802060d06031109010b0910120e 68
    0x801ca400c06c0c0c8100620f08030000c0034104082c00500c40000e640301c986081c1c0300ca510107528403416010402080b0b995840b9038440300c6c05040c20604c0c43c0c0030f00c0b40e0060300904100d603220a042000d410445030800019000514606640d9035100b00c42c150482c5094031070040481f0391041d418070300c103000001401e69042d8044d11480f800341e003d9981c009280070440340000e840043c020305400d005400315010031242581d40c1d601c42e200e504803818044403078482d0300201c000c9000c0b04c540001d04044142040d54000111800c0104030400e103819541448071a04e110b004030511b00c1641c050910303d10b02400b0f40d20b10580031301e94000c010340e582c881c1c01d004030703050310744c0700310741c000c0078481d526000c12443c51080c0b003159a000c5c1d5000181401c201c000c4000c1d41c8581c0180200200f01e240941101c01586d141801001c1c0c03074601603000580c0500e0b40c5000c90418a82840640c498405000100a5413040d10100e51070780104031020704c4010b801c810142c3d41da407a421141c00d1681d10345a2045905107000030381d501c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 478559766 1250 478558516 478558523
    0xb1807092417160f0b0318011803021c14070206041d1512030a030e030408010c080402030d03110706021c0903122f031e09060f1b030708180d0309 64
    0x402c0d1016040c0002003c11051043d540700043c101c008000864041c4055a0001501e10907888010f00e5020300c2070a6070f100075041110104c01200460030184c04001c84108a1200e507004401d03645c00000107001c1103030445800c50020f80010b4070300c04564801d400c89020700760a940b4440001d84041400802c00d4045502c200b003030700c00e0b040b4042c4524145148a035801600b800071482c0030704949040b00130300300084030807000780301c28000410150340030f00521503141c1146d920001103240600405151601e01d03915001850318103a08c040313024988200b2121050b40041015035201c2a000d9a8a10a400b425031000118a041c1d14a802c0503400a000500c20380009002e01c40c01d03204011089041c0c280720041a86000414024264607060102545d03100490b072603400d0720241000910703411068111034291064100000b040318411500e01c2240d0840d44d900f0750740b1310000050711100344900c00600b001061144030b400150200c04090b803e03016042020381940e40302d45081401501a010306001203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 478561016 1250 478559766 478559773
    0xa0b010e070c0c0504020c1e01140c040e160c05160905070206060906040b010c020306040305070213020406021b22051014181b070c030b1807092417 65
    0x604490b2094960b80301160700074490b40940391826040000030f40c048440c0640318081e91031349810f40f00c00300d2516030103039040b81c0000c01c83c07000c0300708003550b040c0d40200243d1035210140000c0c804610540840d60740201010700301071408070f03040c000b5038000c14008001802441664a800c4000030041318002c11504118410300c01030300e8610f410390f21900d080700c0840d00008000d00085080c40d094210307846078036040c10325000030001500440d0400200702c0341540483c00c0080c1d50021404d20740c0320098000c040030030031820207003070520081d1103018107100303900158030351412000141c2e6803040034940e00018580a1001c03d4851071001c014010859040150182103840000e51169003046401310501c001c005460740750348181508003a00c4083c1100b00e604900403458803182c44004000c101c010300881480e09402c0c510311308228620030003002210044010300c1c00e4002000d0000304c14054620040d8041000c00c1580303042c141101c1b51025070600d8082c11100002d15066240801a4481c00305003075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 478562266 1250 478561016 478561021
    0xb0703020a020f0f18130c091a09070831030806090a0c0203160318031109060406030f02090a110d1a010e0112020315060708030702010f05090a02010c140a0b010e 71
    0xc1040c46a070848007030380c224015090f040c0d0040707100701d40c1030b500514820311080d004016468883c2c0c880f02030780010f48016916a180c00035070f01032701208000b0480844d6240c02528001c034008001602c0603011540c0d20360030442c4600c200426480d9941c0c0d0300070b11180010400c01e1410018400c000a60b070441c018800036000c2281d400b081c0c0146031401380a40c0003549010000740c241081030100c00d105801300900e028038051a00c0c00014064011030281c1e80154080098070100301d506c1e40c010341524031a1f071074030a0800024810a202084140d01152400c64554482d821200544040c0c0b609030005280040d2403c0b030f943d401d41c0400950406c0b01480044a11410019540140120880f50100b90050b02c040301c1141c40d5001994070410440c002c030380404800300824419041400111030b0306001008220344664244124121081c001030144218106809800d45031180084081c1c10409004603801c2880401c070301021442a0040403540051024240700d100100207010b22001c14094001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 478563516 1250 478562266 478562269
    0x2090c0304110a06020a030810050406080d021b09070309030e0a0605120f06090c030a150323011a06070219030b010302100302091c11041d010f1a01180b0703020a020f 73
    0x3c2c020348246400074090001251001e6920070f00c000c240920240d5081004903040e00c5e1030207060002c0030300350018200c0714005000642001140c1121020b1f203c0d0700c0c1c003032200a5507118850f58102c0036604001a400c855410203e4444c00701c0c50210b60468450440016429480700083c44010346041410405484901e8444041c6005030395066004070701c4000701c0c0b20f600c0e49900031a004980030b0000103004c0c10000e8a1541019568000d8402c484840b050445078400c544640c0ba4a400400c001c1142c850324101c481a101c540c0031b861805420042040011511b5002d801440350004142c0d0b01d1b00d0341e5480c64010000c0c0400d01040b1b0040b0350380d06038003040758002e00903500301070801029030403182641d41b64901202c1d0300007001d648000c005807000200782c45500c1240d0504118a0859081c415903406041c01d5407842d1050104040c0b42c182c0b2400c00c449ea00d6060103035103200b46000440010305818904021129030803150040c0b400151003803c02d60001500301c2c80c00c3c801e5640c0506c03003c083c0b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 478564766 1250 478563516 478563529
    0x11427010e15030f0c040e010305011a10120c051213050d020304180c030b0d0506040b011a03011a071b0f0902120411011b05010e151014060702090c030411 68
    0x206080e01c1038420300c041380320502d4101c01c8580c003642800f034460900d60b03940040c0358155020380c030990703050355503000c20002d1902d220403102c019201501d07000500ba40807500200380c80b0003070700c24030041540d5690410411784544200c920800c44000060308a0400031000142003c0800c4125910320400d20711a43c070780d0000c41503404451810075003000001d4540100400b520204c00000205030b9100300c00b00190f0b50b0400300e0885540164014140d81c40c061500b030104c02d2060b0003c3c5111481c9080002004100c50308590540d0b1004070740c10740070481000d01e0800d9001d0b00400800322810001024400d030004094882250652006241b025545081c3c8500701d00c2446007140080d01c910001601140f613022214510724810324151400d500c0c0ea000c0814003840100c005c964a9454010902c4840f42c1001814205004034540445d41d0405400311400541144151400744a41598407030790f0382d40d120183c80704a600540710f4038403440c00002280c0603610807501164030760310020540b055800d00c0c8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 478566016 1250 478564766 478564789
    0x910170703110414040212011409010602071a1327060b0708160201090b0d1508013c020711011b030504052412011d090c011427010e 58
    0x41240c140743c60300303003d05806508003070203010b03070400d40030003240c890070360301c602524000c102d1414030081c3d05c2650b6080002048043e84080115803158030203110341a003103048002807071080748000c1c6e510081e0708a210703074115896108080f07100744042007401c224601041c00300c40580007041041040c1d03d0b494800490302800c00e01070000398040c41001c450000000c04440801d005061082e5555903034401c541070790780003075800d2035041d41b075201d2078544080e20141c04028142020091048d804550588910650301103c82c291421241c9034040d840c150745044581403142440040d0740c1e40d5541d017046024444040c03402400544400c00c0d2a0051850801a00040364103954840c43c1515010411603c02d02141d450035925503018210305e03005988a0003402c90010300c4502d040198503104082e60920740d02d840a1550720200000c0201c01040441c0c40d141e803a8013420701122000c0c4030813814400717000d000c1580c0000c05000a8800e0420164040e840c00d641d42640e50b80783c051102d206125043c00704 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 478567266 1250 478566016 478566041
    0x4050604030915020c040c171f300213020703050304020925030203061201060306050a0b0604031e03030207050d080f1b0405060702060c07120b0606030105090712020910170703 77
    0x20040d1445103407d4200950300089460100c034259503d580c070360f1201c50107444620703504203004c03d102450900d04d85107100030440b1900ba030310032848443c2e0300100051000350300102d407040c50404000315a80c4842c848160000e2400440d15401640343c054000d0f441031b18141d03c50891200042c000b40802c80203074110740304054618424200602e4140e0203508081c18141d803003962403007601300e24202403180342d0003140903480104860a0a90f1260f04480c1c0852041e40241d10401040c004215600a191000ca021845060b603002060504600030700400390020f100b8054220525956980689410300070051406540c0d095140d60f000703000200001058180200c4051000704220b01e4640080d080c4540064a050b180c0403010500a00b0316030250030203002d011140c6642814441802c210580c040001c0d140e40d03280d5410000082d84c0c0404c000d004500b040300820160401030265019506580000381c848416100c5541c0b000c1c1844d07000c601801c0c8c0180c183d03000282028880e001e00303641d2402 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 478568516 1250 478567266 478567273
    0x1516050a2f130c020705030f030409060b03130809010e27010b13091107050f070e070201020702090f0411060c100b030601050901050d080c06070302090f0306310b0405060403091502 79
    0x5601c024034010b091000c003e00b042d070181c1800081c440d10148511008982001c0103540d4075420410760000301c1e1415081030300d10040c1401000140110216040f09181d00300c3c80c820344919245004858a003240c0c10f00e5900504032a0620765110654210103d040c0c04000d000c021581c0c07100e80060342ea0107104090203149074a00300402083e801a480985000b20401440e032070318580d13888642ca030000e46c00c40d80c001c03580010300402c0b14202c0090160b80000092000b03514084c0242c00094803800c01a02c2c0c1c01c0c00070795210104080002c04840c800740070700040c042d0b0752156400c004c102d8580891030011100241401d080c00103034503003c9501d50590b800204400803a908110030300900030300c40b00003200c00d56001c020b00b4202c1a005c1140610500303540d640969903500e00c405016600351025030440c000c0d0702c43c0c0f003032142d4001751038010040040703048481d603d04070180000d42010b10207200c0203003003031804105001c20303c2800728038070f882070380a41ca81161196483c01568449108250300c2d00041c0c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 478569766 1250 478568516 478568539
    0x1030b150409020d061a070308280209010201021e04060906090e07030216150902100c0b0105091003020d0b061206100e1005100806090a0b1516050a2f 66
    0x203140c3d60140100c112190070009500c4c2d21003c442c1000b01c004494920100e0021540404055001a40c1640302c40355502010701c980f04009012410741010000603135440c0c010503859000d0340300b54140c5560301140c1e0101540070074000d0b0104140d50081c001c0600140481c88003149841c003d40e450300c1142c41a10700000c283c0d458600440083d0024083c0c0c003000e01e1401005c078007180c0400e8000d15490352030f10b00040c0d0b860881c810811343c1452030744e0403424001a229100c003c0b840038030490703045610643d403000b1280d4688007142d03030301c1c01742c0e4000a6000004030003490074040f00c2c0c4849880b500d01940c00341d0b111004400c0c120760710641140d064040f81d01c00c200a0008000d00507000e500581240035903e5002d8a40b800a803104ca030760007007040000c80307001c100500307864010001600258002410001914010301144480d0054050b05200580001d0075501f00545142488521500201a00c0352003c0304d1a00380006050300d00c0141c205c01549a849107070b41c0000c0c802c0e00a8000041c09040070a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 478571016 1250 478569766 478569779
    0x3370c1209050d0c1809020d03080916030c0f0503030405310509010209030610051809030d06060203030907080d0801060806030a0203120a08010905040309120813030606030201030b1504 81
    0x2240403820100030011040310000e903948804010040103441100803000e0541071140c4901c14004070003c1900c0c04d4242444c1c0300168544061100c000c503010300d00703080d00d0740c1c1d40c503200d51030000041104003031460100000003e03c045a4800c60680b250842c903042c05646e5242015582c1c0114000c0a074032900c100740c0f031000355844840100c1a0300c100502285942d04a07160340085070340850301000c030ba940025000d5040c0c40c0510080b503106c2c11400ea944030040c1000086510341002ba081d01c4140e0300c490010440042040064540c40c40b085582030060740c0d00c07040000c0d1213400680703541040c1d110700c00003c40c14a4001c40d1000d4840a5a030700d4120036072034040200e64404001c0d01254150207000040c0000da20144541261b9212040016a4520000f1001415000164844c50f04a031401003480002039100f00c00341d04840c03020103d54544400c506010350a449441e5102c42a0b9400000010400940f80c1058044074001d1320104801c4000505011a601c02c003541003090400400051014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 478572266 1250 478571016 478571033
    0x6080c03130204020a0323011809060f090c030212010204180506061308030310120b01140315070f141c0c050c030f0d1104080c010c031103370c 63
    0x40420816905100007150300800d040340d0041c00000002a211011032520050003012007031051398424040516614150360b0002407201e60001c03c50307050b10303419480180117054001051390305442600300106112490620306900c410f01c0201d008801030107032207699140600c01d44080b00e103568030165100205c40e4640d00182001002180d0001d030501100010313000803040f50b0041c1518200a541d82d04000400c148c0d0300c0340e1036102c00910b280074840a00000c08000d1014115007818445c0c000b00b01d504400a4206942c2c5d0004804c602860070400c1412503006d10080310501554890b00035102248100c0c640d03600c21410b00281e001c80748501c3d903121404a42c8044c1c1e900c91603140c81070030141d95801c1541141c0c49542c0e070140f1030001184082124580c2c0c41011440d07003001d500286811f1400c000540c2307480050300c48505110101c1c060405060090103400500c00030142980c5c5d652208480c3c40b08603503403024408442040031803401080442540307520503a01b940f0340706c1d035104010030780d5000c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 478573516 1250 478572266 478572271
    0x50102060c0313110a0305011d0f0a0206090d06060b07060b010e0a030b151201020a0801170f1513060f0e010c09081002180a08030c06090a0c030b040609050d120605030706080c03 78
    0xb0004e05480b00003007c19020711a000c1c40701a8a481400500c030a0b9201502d0501c6580310004103400134100301c00117a0350780d0221220200151103960f00460b0900784900200302a52241c03010f0440012403404009440d88013101c3d000098070b8014030001d0781410302440f42c00c14040105101500c5003ca8442103d40d480e101440c20000e10105054140440340e82c00e90300400640408260070400600034083e26080306007101c00064000d102000c0ca5071601c981d581d140c941e01e80c01f40e4240c0030225030541e1100f86248400d40d0024000d10205e021321010000800500440201552a1003c2100c40700d200381029021240040c000b010b505607107629100c000e5106688200b410b00e144407554480c3e031180c00301d0300010114100516103628071001d14900305030b0024040d0baa0390300a079001c00000343c00d11108200346c94111030400301640d16071420b00018510100003419030300c28200710903a40c646c0103442c180002d548150500c40e6950740c2c828181c5c4e941d52809194040b50798100094124a1554091075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 478574766 1250 478573516 478573519
    0x807061a03010204080c090109022803090c060e24030604021c0908030f070f140d0b03061503010606020a0b070f140301030b15061914040f0807050102060c031311 71
    0x100c46030000c0c80020700b20b034015417040200d40c101510840c007910701001603a0040c0340860342036141c00c2d03101c0ca051234a100c1045481c6545070003a042070107914402d0780b00724400d43d842900300d9001030b111080500b45401031400c90381310354100700d1074540c2d1074054540f19480701543d170303070841c19078440004201c00ba42013202c01801000c0d110140000c420128050020394500031007003540d581c10441070505401c40001c4c1a002844204260200c200d90b112070922801100c030b40540f501e40020740c43d00fa010b0085c00103030960602c42e0605002d03480a540d0303800c00016400314002c00025a503000103a8580741084009820400360f140040d030824062a40d05008a0441c50b03d030040080c00e440c100210b0f00b007a00150780c000070100401980c1d405062400b21105e40c110788007400d10404038000c280130714042c82d4440402211000e01c03030b0070348030607429900500b1195903026040d640f5030400d150348100724803655006114000c0890b1071004c040088078010403080c04804030b40b0200b52034910341d0512602a05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 478576016 1250 478574766 478574801
    0x160c02100315030f05010b0603010609030f142d0706091e0f030f0308130803070c1112012306011b080906030f0a0c0f020706122a02010501060804080706 67
    0x401c440a038001d8040594868061290301001318104242103e083c129068003400d0b0400c0140310464104000030220f075813001510144140c01d19200401e103c0d00503410038217100c0e140b90070003200c0005445080795068035044080745d0f2808012183d070341040b4401c00001c5100c0e080c0c00c0c04840e03113080c0400c0c1c488141d200710b61101d5599a28011041ca819403040cac1d040b0b00105248070400d0b0740b0182032074200e10700d41a54030101c0c9071510f541c081d33848054490010f1004220300d1000b0400e6100000c0c82500e801000540d81208113400b841c01b801d810329030a100f0b032440c59081c41c40207004078005802150107a5454000b80900e020190300307105090425600c00500f07026605c0c1e15500c000040d4860b107034100640c20a404d14aa0f24800d072541c290884d01800107040640d00c1c426030000c1d291045a41602e0100380c1c00c1c40d160203410090100c60080703c000201035040120404c410000a1189502a4000c10072aa41da140468403490169401080940308208000c0400c2060f0054402c926041020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 478577266 1250 478576016 478576031
    0x140607050d02070f0c0f06031523031507050417010e120c100204030f05240a0f06080709022205180702030d051815090d2307030302040e160c021003 65
    0x703955034181654428140700c80b200d0802e1000b03d0303040c05820b0070b420038010300e409c031a428441020540400f00f00200903030a00000d047d00c80f580c081100080f00101d009000301c813030800640086c5151310502400a2584030072200c4008035105109102e03030301585c070b00a882808840720102016501c1154400e6441c452104402d00052052005100662003110300b6582c250091a01c0c6003400d1200804480d40560906001820700e1407040007940085021070008462000300c045d800140b000790461406442041004696581c0c0307a801031604508062418480300351401003040c0c0c2d0302c010301039507800c01201c04d9440b9241001d40e00c9540c0001c40c0f801540e0601e095450303c070381100c60844081103115200d101001400d00b0038004008512030300110103006240254503107079140e64980340201046100c9107000191020101900100411040c05558807412401c0c010040c1d0401e02420040c5403c074800b0814082c0306403000e494401c2d01d5110031000728a035408002c0400703642100c0109040e140c408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 478578516 1250 478577266 478577273
    0xe04030c1208060109050402090a050919050915060306070207090207060b100201061802160209041403070305090a050906011718070611060f0609010b0c0109021c140607050d02070f 79
    0x8180c1d0100031159030b1912503207409000101030340c00d41d60289000718030402900805440701c4c0062030603103105036036240183d19000d100301e1400e040310160844151a0006114203c4c00210314040620b84d0300c0044079068481c407007090b0311000182d0389100540d00100d030400c20045290050001c15006060004800e030700c1c0004210402c082001250041c0d5454005001400c4c24241a04113416126800c5007030400210650b030b15400c49282c040c0c46601d1510024040100d250301c020031210840064070b403648003626000d0200e030002c8004603c03501780c4007030109031030a1240d9141e12642e0143e407013039000040100364880341d4401070461054258084550318440c582041000d00600290340c8840101c421650404e08000c00940103640030000e980c140480d90f56400c01090554240642c4240c0d26140e04885034010024000002e4014400c0c680b50007501440b02c0410007824020180105080040c99509480707860132100e400210708188511540300610b81d011f48409486000502d54100c0700c1e46 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 478579766 1250 478578516 478578533
    0xf06211b030506160206011a09040603022106010803030c16020f060a200a0507060f180f080d030e030d092906010906020a020102070902160615080d05040f0e04030c 72
    0x401c1910a03038040802d012a0a40b0b806489406000502c0900301c2941481c11210f5035190104128120190208020341c40d42d850350b1100e001154014180300d0078000201091088400d65010103145015120001860280c00b004491282081072440340c94072030150202414a01101c1007681c1100d0000d05a2800380c5450000f05600c42c56600d82400c0301e4040c101b1f4000a2071002020321144d0006848040022400540700c000d4801905080d1a9071003030f220100c980c1c4c004481101c10b0071900210016003549401159008d543c200400c0e41d08420a962041c1c4c2a21100b50099120754030030000c4034405100c0d80c0c460040103105d00c94582420500d40d802802543c003030f516041c100c00001c0180060741d0b8000c0120001041c0e540054107031044542c0020b51641c005122b001000c1d50001201c203803440c481c4002d452050303444202006402d60201245e0b0110300c072401210001d100f2106d103060000c3c0070310292411a40341400c400c198506000e02c0e06a140c00161044007400300b624940c4d0009032401c03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 478581016 1250 478579766 478579769
    0x74d0a060f0509012406111213091b2304080a08030a1d071a090d05060702010c050f0301170123090c0a0e0a0c0203040b0414040f06211b 60
    0x281d401142d1400c000e80c0c40d03402c4407000c0580160755080f03450309480701000c07090240b00311001400c000740c02d890a0455103040c002d00d0740e00c1d600a5600001c5400c2002d00b03d00c00e8400f80c0e503e20b84104003100440300e034100c0401c081c3d45800085048180c07504255401240c945040c40002c2e1400c1c0c2c00e01da510896a8544420410201c9042001108200c00d007040d038458080001b00060300c4556926000162a4440c1d003180a01d080011b0010700c80304500c0440d404968540794054900d40c450310305030800301c1c1c84110944554005500304140c84054034820410786500645001c42c041c075603460720f1101c1200b1070380522060120354136017203006540d40a403411580842180e12141d0b050303113410655103040242106c8a54805c540e41c1506110850b0341c10f1802d82e0101182200180c091428041a8594011a8050780c0d0141c40002e0100707a19503107d02c0e03031500c040c1c1903500b84005a405001541605d940703020b010001000300c0d90143e00444a5198400d845000d030541b803a529031056843d8000b281c0742d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 478582266 1250 478581016 478581041
    0x40c02030d14040515010308070605100e1305060105090115080a0906020c0706030509121204050f07060905090a0e0a030516080a0509100c021c0501020f03074d0a06 72
    0x20800c000502206111103041c84590340080e580941c11a59216401c1c0155074000e841c092f904c800282c80300055208886c040e00401c0ca10001502c0c00e8444c2e40080400386404803000d000d403000004060800c14080c0e410b0342c00700350481800e80c036050b90483c5c14080c010594402c064440c0c48000200d8882c0c0700414440b401c00010700341141c148800501038440103020754a03d82d00400c085a40003142030280d900303510103003542e829961602e0420501d003085490441302c0700d0042c2640000d0040c0c201c0c440c942150f100b078450114680e101080c21040b141714004100054001c242c080002922600042020300d00b90700b080e50341c60a60791546042c1c0d0300b0044121000c924002085031b200e142030f20701c0c1e900d900040d1500c698a60300581c042280070408003601004e401d801d8501d00100f000a406903030f5485c41a40010740c40b807601c450014618550801d0303881100000180e101c1c801300450000750000c014074106249000003030382017001c1e1103100640107040c600417512600700060b11400390f8440e0200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 478583516 1250 478582266 478582301
    0x20721030603021e060301090207050c120105070201140c1b1f0f0501120203070e0c0c0a0506181506010c03030b0436050616020a0506040b0f07091202040c02030d 71
    0x1c2d481402480d80c3d481d0410168400c1d07004e00c01201d030b55850100c9040d01e802146c050b8407089d40e07103445807424130900305003076000ca55880314542000055200d03500c181860341c02070111303030003221514010ba5400d40e46180301d0802007100b00a86003120700121110300204080312800003400070503050b82010307084822512621102001402401400340c5809012009481c03082c04c0020790000380d441002d486a211017045400c0000d00a180c0001511510011a0240c1da0b100c5250315040c0c2d01c0d030401b111000b0405644400f084000500050103207a04810f01c01d40c82a113807a540015111420140c00071020582c640b000c0164540721801501400b19450005030701d1146203000c01080d00030158280280e1200d4010f0200c00b10b000012900e801202072008130800401c1190102d050071404c54010b4960320884003403200300b10000d035055108007901040d0104030344440c0c1c1d089819040d544039000d58011900099400351a083e4001d144c021004c2c0101c1c4e14107406803503e081541e06007908840200c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 478584766 1250 478583516 478583519
    0xf030706061d13020405091e1e190b0613060602010c0e0102011e180b042f010c0305090a0e010b0703090510091701090503040b0901110105040c06030207210306 70
    0x81c0c40d11610403800041052451400ca5040e02d0fa8403001d08000e44a01e884101007400c2d0103040c000704c00308640c0d140c00700100d480300007401569650340ba540c89100c507400103010f01c540000441d0034860b2503640d07400303050411095206d4404610340540850740c0480d111030500b8020789580b18900040c6503540000c61441000d1002400710441c1c00040307410369060003150891904a90710000d070075070301518009070b003010302c0340b10307007005062420700508103d046000d10090000100901c0c5039203020301d00c2c070556900403e25000500c120700301082d0200c2d0548480c0000240641b001d8024000c0113012543c600b59224807141301c540342a4054103d50b000000c40105040d0300000070006440103844020003200b1400c3c0c0282812030700e208040c20806030720500050900203401c1200400e40003000c4030b0b161500c90b00000380503401402d032030b4041a20160001030240c0103000c2d072441113401c841895100c928141e000d0300a50303c034010850728147c600103064142032040d01c90b15000440c0303940014500d0b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 478586016 1250 478584766 478584779
    0x9041506030b0a082d030406080420090109050406090218090f0303010f0b030c1b2a011709030421051212010303120f0203040615060f12020a020f03070606 68
    0x540121400c18020089444103005a0100240501c1c01c502d50b0801c0d0012081c802d0040440700d051712440765410b000000c0c0002c0c00c2e41c0c0c0540c021340124060302c1700700c0c030600544843c0ca0780100c040e1401900b00952400422000450ba40300030b03401b41c0904030119a404641e03000034400e411224110040b00031000078000f001c038080001c600000401c500946c69941010341001c400b65543c8600e003000000040018501c10580c0259000c40840507103504410b0250b000d0161180c400c000c042c0c0f42c020010b1041582c605500035100351440341070311812403002d20f00007000c20904000341940141d2108000c005841c21441344181008800030300c101c0e00701e0b40c50b403501600304030901031118a80c040c02c0c007452103c161040c043d541180c2c0d140c01c104190300395008200f8058881c3c0c0e100002c1d105d03c0881040f00f0b101035600a08070703510a0041841085071912030544441c03110700110350015100240460030240250f00a1500301914011a00c412a0700c804042c6954441c2104650b4591181000c1141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 478587266 1250 478586016 478586021
    0x612050c2208061605041514030405060f0c0f03041b050607080408100203090616020726070b0c0c0603040c090504121d0f01230f040807050d020906060c030904150603 73
    0x42000100d10f00c3c0b44c003024200800c4c6000758016a1540180c20010398081030083c61b4030381012100c04070442d120b02e040d080850702c80d8022a4014402e00f192070002ea0201406001c507040c2c201c280305000d0450f2180e031284c03040c9104400d45110380068104000c5203a654543c00b61840c1d51065088551702c0c1d00340450141840c044403205209a0b00602c1440f84841d030208030305901017810343c0740c6205c2c50b6040002301d1a00d44103030f000c02c055181298094011190010074220075800c54401c444801d40d0318400c140141c85501d901c002c41da00040e6140406140c071300011038101e40103400880070f05498445400485000ba14222010140100003150741504034031111401401d840540345040000c0001c592aa00c5003410b05041007280c9046004220046030325081c25200114030640f02d205a03060716802d03074000d00800700b02c0e10510800007524a000e1038080b06840d4082c0288095841c2c10091109170303001414003007074500080c4925011a111032003509100c000e6444516185841c01202608 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 478588516 1250 478587266 478587271
    0x210c0b0301080c0907140d0603120f20010908030708190b090a020d0e01090309060324030206281e02060609060906030c0904060f05010f0612050c220806 67
    0x10126414001004900340104040014000035100c990701540c8041045410885002840e0008500401d002c0d03400c0380030358814000c2e40d01c50240484180300300c04040c1c9045640300300329000a6403849090100100c603800d03220a00200c2e4001080c1690940d50381c0000d42c01c129020400200c48104018090020103421010350804404c1004001e194070041500210f004022205568000507100720482d2198480ca0440b034218008000440741450010b00b40001445800d000a050030150340c1c000c519110b20603540d588446504da856440c40d0700f40300d0550020090441907440c0040b04280381c801c41400c10581d00050307510070302201036100b00c5a00d01003008801e42d003194041010004140c4800c407005400c0b200856442c22642d50701800a8075010300c0c8010b00f40c104c46240144802c1240e00c1c0c200c80c0c0d00341566141400160f803aa8030112120495106160000303800d00004040007203254031164001c14132014a03440d08034280030241202c59000399040340d102c500141004a0702c0d003442240d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 478589766 1250 478588516 478588529
    0x70b0d060f06050304031404050603090c0f30010908040f080106060f02030702130f022703010905150a020d021c05060301290315040506042001081f210c 67
    0x71030007030401c0790041c494040100300900f409202490360b41c40b0110b10050340d00a110042c030700e41e0b40f8901142e8294841c000001c6490044035140c030942d02c01c0c5010821483e0501c0082050f00034003104042c2207402036030341034024545550b1909600041009200108080c2c0b00310707603403060302a03e4410120708440c00c50703002600300142c0c03040100080c0c3d40482241c8030160101c490f1807407c4c1c010b50038000104500541c0c181c0d0f040c80000c203505c0d28641c410340740c402043d007654501d00a18100041c182a035652410081c601e1304100c2001840c050b41d40022a0048558003005080084000015040b0ba100c24920580d600482501518400860041561010054009004250100700901010943c003285100341e41c103c02c004640c1510f040084501c03840800403e5581e50501c4e08105440b02400e40e000c0da0603805080c4055864883c0200e901400c0e43d0694540c08585c0e10341c61680781e00041150103010040c0c1c86a0000741c0640ea000418130000b01c04100070486a0080c42c080107060100e42c0a030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 478591016 1250 478589766 478589789
    0x615121503211e0807090801060f030209100b070f1118010306051b0f0a0c122007030209070e0103090c06030218030604020a05150706020d090303060b070b0126070b0d06 74
    0x4440b01450090f1044141c0e1150900d91129100d01100791109292604100203075880c0207000074018100304400d4003100e0003500c41d000d0944580070b0b003c03d250349500404080701000c014501c002102d91110700e81072030042c4840819000554001941221850314805c036510741a0014410b000d228441e0320b4006120700301d0288914030030300700c02c14a40101128010080000300e4600d880b1400b498600c00035a03400010920300600341000078040f9000d009040750b0a0301e0055100384401400224107040c0c0390000c1500143e0342c2d030000100c95043c0710b030051074109a01d8200e5038000034190f1401401401160320096103629007034540b0740c8603004004500313100798884000e01c03000d82c641d4014001916415101c074200400040340301849485407100c000d05d100c0c80000c10030178010b6594800c041d0365100766001d2014903561852591305002c0e03860040e0506021000400a480000208070300e84418003004618002000c0c842c2c0e818042281e11400340f1440005041c001516144183c202408030200704 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 478592266 1250 478591016 478591037
    0xc0108060f0102011e020705010c090305030405150f0a0c0506130f02090c0f21010905010501081302040b0d0305070c0b0304080403030302030709030f0f1104061512150321 75
    0x2842000050103150140c200060300200a074400c2d0004015080701a00c004c034180d2082e000700c80294401d0300c055446518000041050703034031a0a000702143c0d0880011814542804100304500b00080c0003500740074001c1010001c0d0941007006040e41c51040c0d00c0b10f021008440c108607050010040030b421450b035600344500001171008105500807030301982d2280c1903607035503007040d0218131620051803020072021504018030400c000d40781620b058802c401306507a036a41c1801c5d0b0180e8074203001d454041008000041e15000b4118001c150140c001000410340400350804200340c1d003003907401500080c2c0002030080c00e01c0404200341c002050106107062843c0340a403110541c03405a40001010540c0001c080350b9442e01c650541d901850f001000203050105607d81041002a843c00803540c1003022442002e0f2843d02d0302c2110304481c04544200542c1f1058102120615403484c0200350b0680d40351700d64803803400060000301c0554451401220401d880c420884100b81c0f4000c601010010794119 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 478593516 1250 478592266 478592269
    0x70f15150f0905041a010e1006020105060906040c0e0915040e1903050c0c09010605120610020706030e011103090606012c011416150e0f060114060f0a0c140c 69
    0xc0c22012603042d2a07000400761101d03d8010000d4080c209400c042c6204a0008150440c0c401e940070301031004030140c021441e55901c070507403d0f80d40c1141e089610010900c00641d1a0400360000885201039280c002a00307980c80740007501018054030340d02d49800c5503c5041d0564149403007401c58000d1094010250440384402640b109030b103049000303080002c0840c030082c04190030030181d41c10340c1c4010800102903850342c00041058206d01c611041c881a1100414814101105102d04000b000d41c06003000c1805c3c01010750260102d4052821503650302c020001908983c00043c1d13004603e048090186410590001012a45c8144410404100700d100c01e6590440b0500a502d802100382011a480e402d49103d00e2124024044a03005c0224031004075001c0000300c2040011a904480d1b0410040914105160761401500c05600c1558002c00060001c0074601911000041c40100050302c0c20f0034503165580b480d000b080000d004a040114a0f01c1000444102000e00c070440c500102003142d0b8800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 478594766 1250 478593516 478593539
    0x50f18011a0d150603120e12070506220321090b09040504030c0b0a200405010801030602160c03110102060a05060d021014040311130606050d05070302070f1515 70
    0x20351849400a01c01042c20440c00b03160901801662681c10021160340e410614a0601c2c1c0b0810500020035a103620013892a00c108004220542d41d0010f18100c2e0401041c4000c69000c0d1032000c060307003008180101c40d903040782c148030065031040380c840c3c07100b442e2900f2040c0c01e100c000b0195414004002401c5c0f1400c455482566041402114042150780f22030609a07040200c04202030f1040f07980e441008600065500851106c0840e10340080c01105044220101401180942f41c0010047c8004201060f1190054031081c1c0c00d450440d4001e00059451000ca154140d0046034000213501e0118184e68042c0b10705c5074801a550000d020354904100003a0f1440700b4008000d1180c03c40e5003500e40c64501c181481c04460325500c615555950300c90810780c0311007900c1200340d803180b5288811041d0862803030103543b08540a6840303250500082c1d0082d040904001402001090f500348102004141c1d8031003003031102809100030340030303a104600e00342080d0740d03c915840f1454000c00208210002040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 478596016 1250 478594766 478594811
    0x210a030c0611091012111803060a020a20010b03031b010b01021f05100b0310030203010b030f0601151407060f290d0318060203030609090d080103110d0501050f1801 72
    0x140342c40414106194501402003801e0410560741d021b000c00d0300a81d014060310203000110044084803000d5a40080000a92044959500010b0041c64104002d00c0345443c083da00e451403240040740390b0410a020034030756002040d4080d0240c100305108a01040d080c4500c2968840078405400d0001140c04500c07112030507114107071185599040001d00101404100300c020b408920405560790a0140005103c1031643c00180c0c032a502c3c0075040d011901d4005110049000303844060506680307855011003c8003e603103100404e102091001000d00c0950800503c10144150310014203d440030781d0780c81c112820f00a50024a10362030f500301c1c088040d920751202286400300c0e805480106149170440740818007120303441301041c408501103819900440694070510082d10700c8280341d40d4030030030700380e0b2118a4040107011816140040c400314900c5c005490300c948014000f6000c0740030302e41d2041e007100c000322a54140c05039420140b0a1001810381c0412289074914024000f50003ca1400049034410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 478597122 1106 478596016 478596049
    0x1060e010201240b0304150509070f05010507170d0905070f210c03030302091807020d020d0c150506240d2702210a030c061109 56
    0x220b44640320f0030f0490610321403c03246042840719503503101800c140c4200c050641d504021100c2e9000d030741d0140c0064002064442c1c905036402c151038a170b80d044203042200401c01d9201007200d01038191840b88082c80525903980180803c80020662203000130064018124001a203654202840007240d03049c1400d00e80341c05994400d514070f645809030040180190b24020b0011074441c0d40500a825005000d01c0e08203100c0c082801c00c03100c81241d0441c016071108910304e841a03818000c03d21030801500b02241c11000b20380c3d9910110506515006a40b644c2d0b400081440c1d0300e1b110040907c10b15440d042d115036400a590441076444196a800801d04041c0c450b1903014060b044050280711006584441200d180c0c2044404019910b4043e0040d010584210215809020701043ca03482030303d4010140460b840c0000c02e903007000045a0070800305021035440e940302d18a40b00d1403c3d11 = true := by decide +kernel

theorem cover : BRFrame.Cov 478417266 478597122 := by
  have h0 := BRFrame.cov_init 478417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 478417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 478417266 ≤ n) (h2 : n < 478597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
