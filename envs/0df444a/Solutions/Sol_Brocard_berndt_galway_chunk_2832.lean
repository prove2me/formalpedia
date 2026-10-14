-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2832
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:29.787978+00:00
-- url     : https://prove2.me/submissions/b0272bf4-b85a-4469-ae52-2d708c702841

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 509172661 ≤ n < 509352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 509173911 1250 509172661 509172683
    0x1b12030506041119030204080715030c080103030e151b1b060301050d1b03020d030c0b0a1112041704031203060801050c1207020a0519050106080a0222110a0e030c0d 72
    0x201d824025404040e004e00201a002e00000030082d40400c0008090198081454020b48191400404580e4500510010860f02c580104042504940103100c482004d40d20394107103e0916081000e00e00c5070340c201103034a111068583d140c3c234034041182c480c55502c1000b10013441c90542c003004103a000038050300394044a12801075002420740b95443e00c030000a15031001c00141eaa8002403490450307078030300303801041d22030105508000604001d5030340301c1c0490744200314031542141c006096014014040980400300c1c00420140121201c1400751003a000660710703550350310b03032400c00b0380150400d03c804040381c28440b011440c2d607818010548a5158209120f05010542c00180b404d0301c40034044006500805140c48086038051049080f80700c4100100802d4910b50716050f821500c9036440460140c000090300380c0103130380305030000c0c03039400b00c0021810080c1d141102c0c00d13005026042214060b501700060303040c1c007590080d806d012945801c800b51798498aa800502404802d9075400038902c251007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 509175161 1250 509173911 509173927
    0x80702150a0f120c02071e1d072606010507020d0203010504080403020306071134090204180603051b1801150e01020307110618130605120a03020712031b120305060411 73
    0xe014416040080076900d00c0060340d517038400245621458180d40c4091238541d00700714013180c11442ca005400010f210030003d041031040c80260001000e820075040100000700d280648d030301c0300d080c0b50900d90001e008101ca0706092411503441e50080c40228000c0c0900b04c0025000380c05502c00711050317400080901a1407503100c0c00d07028000c9404600905c40c0d09040ca032902c103504c0aa451502404000d1001a5290b0910584800c40214004d40c403001d90704140003440016001300c2c907509950505401c03104180c940e0700020343d145080d80342d0940d618041500000c0e20a4104000c162040d03c941c8903500b2400108004988a00c12180e000c1c084200322020b0300281e0410200410501c3d80180104200040c581c1c005280868510b01c100d6201d5102c60341400545000d06118690103014030007000650001d607000f0b5216080c07032145907064401252004145405403a00902000740030540c0d2419940c01d00e0400c0c0304228603650345000a1800f800100103040900c03503080b145003200d54540c00d02c010307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 509176411 1250 509175161 509175179
    0x9060f0601122423310902040b01090509060904051e01150506130b0307090308161b060507110307080f060f060418080702150a0f120c0207 61
    0x80500494100211100a01e0501000d4800c80c019500d0062070a0f18802442050b200d010200d80c000000800c541081c8100003030b0340e0200745422078400d0b610580c038040c0003110ba548903820002ca45c468120703d401030f211040e840c2d922528095108980800c5400710300c01c0111401d0806000705904880e03000c0205140d45007280440342d000b40300d0030886801d00034500c3d100c01e20140050b2154404c0e9121200034510740c502040180c00340030184c5006041804840034804400300a20a0034001c0c0d000001203070341c0510415420015681020039655034185203e90806440b003c07000030341d6154414880740c02c003100000c100e0021110303242d403420f003044015265000103242c1c00840c0381d41482030240004040c981401800081c80d5841e0251002d4030300f04160400f11480282014800d5141810f05c0303101800b490b5002d803035150405100d0351984418170200d9480c1c480344c4180e107100c0c00c010a04001080d44401d40424504142c0c0d50000c0304072000003400d00391260010610056000032106100da088 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 509177661 1250 509176411 509176441
    0x30f12090c0b0c0c122b02031605010f111207032d0e07060302120a0207021309030219050705010f1704020907020304030c08330c0901030204030b01080a0303050f0906 73
    0x403015058455440c5000c000074034400c0101c0303202c80d035608028140e0340e500c0c42c46c201941050b60400040d0a2803118414029141e00c00d0303500040d080c0d03600c800c515040c41025405120383e218000400c01085060340e54803800f40c1c20125840240b1305004000802807071080c011201c3c252060300c401414010342c910111045070305000d154070f0003603441d541c0e14000c3c081001170344002c0c030071605e00507650074a12603600d421903001040056030358010821240103032a2400800c6000041c024001007188807480c0032030030104203c0e52009913010141d0000280080840c41c41d0131134009032a44003081c909400300381e40102c0401180d403224406c070400200507041260100364040650710540c0d02c2d06840b03944412180d40b61380c2191280c1d600203d01041d1002d048040c10703010000081103040070601003401100101002481080444404035406d02207074000e40640303000c4c41c7e101e50310541c80c1da180c904090ba42c3e6518401600000e08080c04103258003280c03813a15006081e050058102650f6004070003020300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 509178911 1250 509177661 509177677
    0x21070b07080910090807120f050a21020307180f0303051e090d0804030b010e13060f020c03040305250e0c0a1704050d0206060301020a170c16030f12090c0b 68
    0x3c050801503290803e0a4402c40f020740380b042092644419090402e14858000c594600050264400c291289207030040182e8003100340e2464040c07031040c01024070454010f901c103000fa2040303001000b44103400740c11420180001c1031543d10300c140c1c19aa000c0d2004070880714403020300030400422145601030f1400150076070340c3d940da02005240c200d0800c0030404501f03600805558590010805100300003900b520a07004084400d507038170090800e111240d1140d00b0345a07005042c6651100301001c00442a01a103424891807815261560707580c0c00c0c201c2e1201c0c1040101000070105049110000141004401c20350312000c05604182e5540010034919610024245c401d001f88095251040f44110b100b20384118420030151116040030100a85085400ba1001384030341d006100000483c1d034004030303515016a000700f544089450f030113690540c61048107001c059140d007510301041071540048022058016076a54040d102d48041080404c4603c02d48009044080d01002045011144400383c1814 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 509180161 1250 509178911 509178913
    0x30c01140c1c021219140402090c07050c0303221a04060c080d051006020f0609280501050f0718030f08070303150602071409100e0415060821070b070809 67
    0x10081540c181035a44401700c0300400c6003031030780d146090b440c403443c020341c0d54208044000071030038146a40004c2c036400008100800141c0041340250911204100c0b841454201801b0790b03550b0040c0c10501600110ba80e00340d140c411043c4003000880040c0341d07001d09000541d54a07810704260511008440301411000b055a903800c0605c00501c50540e81e2003418011a000414402c00c0d030314180c006402d2201401844010760000780030005410340c0800d0131410903034080d404214104403414603401100c044440a0306541c41c2000f0060240a01000c050040949031030303d08480400c040325000c05262800010f1041a241c0e82d240000350442001d804010701c40d00700807a04454560070481c00b10629231143c00144d000e0001080f040d2102c44004c201078100352501a00d40c6003400c04684075248902c80c1020028004c4002420b03c0820102514011807002c0240580c42d511000b141c1e0721034424043c0e0a01d4450340c201c243c00883c00004031100181c1c000b11f17424040d62000801d5440e004020711226003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 509181411 1250 509180161 509180167
    0x20904210906030b010e0f042f070201030b0d03170a06050618130e030304080a0c0203060f041a04050606131805031c02040e010b0304020112050702030c01140c1c02 72
    0x410300440000382280e541d503151045103103400c40c01410381d028a2003250511940c030203040c1103525515844545c403001924007240422070301d031020a503144038500d80b69a0303003001854884000c01c844010300000c1d000b41c3e401d120b884110010006801480000140403078000d2044240d441504018658481010100010310350358450224002c0d0340310f020340007200a215601c00c4500c2c50132080110004e54120f01c1003200c80508021aa56880042c0014013500c1c40131940341e82280c82103843e4941e4903030140544050303041c40000060a200d00742c40c01c81384141840600d4441d03085a40450344600d421a0040c8480e4445a043c0800f20700c483c0303000c0301c05a8490700400d194000c40340c5c4407070070705226400039035407401d040000c0c203000541c84604440d00c500401042210301901a0b40c00d0640d41d0b0300c6405039403074460340700503502d0400041c114101a401d103000c0094a58020026040000c03540000740500f00340600b5800206004980510020000f440408045110a260b54041801c001c41c0149 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 509182661 1250 509181411 509181443
    0x40b06010915080a140105030703030e0303040902120f0606090607060b0112060605040f080a0f231005040b06011e0f200d1112040e190f050709050a12020904 69
    0x20b0002d580c030a1078010841d0042881400c45607842249402155120429015410800020703201c403914840682000001c0042420f103903401c4c0100c40c02051040c20031540c41041058080c42040229560741e0350180b203000165442c10101c0841c1c02c0c2840c02091580b8050065464400074446040341e107042043c4460150582d802902c1000003a124548601d511580740a080c1864203000e9088039183d42c0294860764005143d5540418800d64000c010b00703a010320050202c0381c0c071580080143d0710340c81101c50315682c4410319442940503070700511241103203655400041d206403242911040c80b881205024071a42441104003210711807440ca041c5e2003e800d0103000740c96100720078000d0341b6175400030808401081c0d009140c1e0360000c0345c0c0307002074041083c0d501c100b504180224410028100b800b8070001c1c405505e1242c1d929140ba00c205010010b0440d01d2480700020203084904002007017481102154500c2c00e8a04001215a041200d60020350550300b48541000040c03c00c8886160b0101c0c100303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 509183911 1250 509182661 509182679
    0x90c1209061b0915080c0f0d0b0a09020c0a11030c280f18020a0306080a052109030613080c0d0f03060b03010e0406271a0c0a08040b060109 61
    0x140c0600d0294401103a006031030300c851091000702c142c040003404901101000201a14812007410340c4190800054994560001c1c107001e00c1071a403d0050220000381e85c00030002c1c0780d44035404004050b039502100548900e6034800300d10510b10440b01ca80c3c080300d240350010300e00b12088070001c40c0140549904401950201d0051824404043c00d485440f4090841e605828800b21004101c180380004001c4e241004801e0001c2d001c00c014280d00d070300083c8030b00c9001d009800610040c041001201c00040d090300305952510680d0f0007400300701000c840140002b41d0420152540ea41700200600450f03101d000c40828000d0b40c041c0d080314144014410701203c80418440c049205402c1e0310f90750442144100001d080351104d412030380807004140014000020405002c0380d01030ba001c1000a10245800000e02c0040282c0075101c013040c040803105007c10a48410030840c000c038030b00c11108035032556021154103029601d440c0d000241040c00040203d4400034540b504640103040920b07240d40c4400c001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 509185161 1250 509183911 509183921
    0x20105240d05012d050702030f0d1802060705031308030408030405040513060212180712020d02031002040f0f050307030302250306110c0c1207090e0106091d1204030804090c12 77
    0x54004d50b448241d41c004250600506501a2462000d1031508d050049066042c1c0100c0ea0301c10100b0b55241080300c80e1200d1180e440820036001401c0d151200c0b9a498800d036254403595400e5017101d030441001410310000400d0702c0039645034202550405041000f408014000204410000c0344e0451a900100d85948010108000c8100d000d10582c901000000685c001e4481c0c9501c06601181d01008a14011503605100d41c0d4103c07183c121525540c00082e14042805034040f0305a4400240001c50103120081e4200312602201c02c10340c410b07130308c40406840e00c0c5244005070168000b4904d000200850500c898522085e1003c0c1000040c0c0300c3d2640307412031700507000c180403440000481a6200c801000503514002d0219845c0c1c20050311401e103203071503828901c242d500d4562610755a03284200c00307400080c040c01c4640401c01806009000740126100c0e02c1705400c00e03d000784007041c40000c408900f16002d42e074020b80d51500d01450004894000c28040c035000c1e00304041c880c20504000154015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 509186411 1250 509185161 509185211
    0x102100e06091212060402070f050105101a1312020a030c090203060108010503030c120c030c0109050a020a0812040612090210090302150406081302041404030f020105240d0501 77
    0x6120740e1400c01409440c0805160150003d02424481111068001e20144d540400240c802684132111454030121040841304003c00e55400d00040000301008100c080c011a58080051000c507262403c800f5200d00c00c603190411261950340b41840011041401003000c0b42c409017031405196529240c200000450340c0001402540002c240010381d07900100c25405004124060342c40c003001d000015a564071464200f0000b981e002c11003419821060054a2800d480c2c90020b102c400824a00316485d136503036000032842034004101c04280c00c4030016015020500100c402032a081c01c0040541d032020f104030462007400e464954040068486142c051420740581d00c070f000301903041d44100556200148080d20f2204001d00080000d554030880b80c903080b00707c9500c90081c80c003041c00414054000c10460070074030300000041c4402c25901240c042c0f042d00c81c5500800c003580720039121015400c000100340c1d5640d9600110300e410b515142074400419445140001101c056014600c8071050703c41074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 509187661 1250 509186411 509186413
    0xc090303030c04141215062103040302090c0301080604110a030c06111524062109010e0105100b1b070f0303170f012c0c0408011b14090102100e 63
    0x404104007040310350320b180c00b84021100c100c004000104206e603070f4520f00d20384c0c1c00808004004285162200300240902c88051152050b4000c4900342e925505d500c01c0c131089020f80151000a681e41100b8019203041e070f1038017006800386071501d884000ea0000c221030080e500031405d9600100060130b0f071100e80d0003081d040d29401b0040c281c2045490410280260b2441109640410400c07220400b4802030784502c0d5004c0c100c04000e86100100b0700754042c54040c9403018a140d0040c044200450003c507206200d40b00003400702e6041e251655090301c406480300484080408802e0042e09503000140662000d80320070418511803070680c49142a40c56404080b03003038a1002e090081c160f1040e0004074944c40300e441c240c003904241d008080910014030411a1407402006041e001d041280c410055031804034500d000103041a255040303940d0300c58440c4015643c64076400c01d003c0f440b42503002001c0503460700c86d03030050000300d4030503080c543c802e0200b98114012624108442075040c420060308222100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 509188911 1250 509187661 509187667
    0x603070e032a010513050301360506043008060a080303011401050a110601690329250504050909060405071401050904050c090303030c 59
    0x58141800d264020002101c040900d031030310040340740d4400c04400c4940082c42c0c0700c0c5c1e0310703000b21078003040d404880d40100e50306509110790851910040c10780f030300380c60072091080d0030300312005880c85400c25040f01d00104070340c01c9000018081103400c0d03e0142c04805c1c034029101002e00d01c150304c24817030803c8640240440c0c40401031041c01d0824041c1714002e486104021031841d4104101000e40014407044581000f80000d9040c001d40e20a0074460b079104001800c503150365844804840da848400c80031005180340a940b40c0c2d101d0300c5644c10452001107130310300074517801244580070b2101440302e982c0e880d414a07a6007285a94441c0510410004600030041c4d85040c0803651844000000d5a0920990920340e14041c0302010109480d00740b400b00729035100d4034a0f10500c0805955a01560f40030b0f42d405440c0e00c003040170051010850a11841c400c1050b2000b99840d604c212105641c2264500c0c001141030195007042c0c2096400749800c00900340c0301c18146001c10380000c1c555402280c0f404d226403804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 509190161 1250 509188911 509188937
    0x905060703060603110a091415040801050a0c14030f04081e19090303050a030e010f090602070b101805250c0b010501080c0304060f09170403020a170703030809010b060307 75
    0x40c46003011170301c50900d00a107044658000189031045600500700030541402c1c40c0e0f003942c2d64100c042c40d018008010200d4503144d030f8034a00381c002d050444500b0b0a0a0805902081983c800e07990040444c41c2c5075240c0d42035413182541916041c1e0020021926030070300704203502d0210810900084800c0104131607546e10342420200301c45d22411075000405200062000b0f0000980150686264140c2c92a0001d81200d001458502400e4004086020b142c50300c00e1260a02030aa0003d08002e40545c55440303c3c2d0f00d5108034a03102580a02c50b54060080300c1e1410000c80026820082d0170440000160700e880c0704030320150505520589020003c140022590300030081c0da20b6241d4010542420301080501e011480f1070450b220003400141070700d6503044c5040d003a04181d40800c803503079007000381c810701aa40d407190200c1e1a0310600051b440b984d142c841c00140c0e4540c1c400011222000c00b0080c21649142d076a042c0c60410000c7c001d01d9495495612660003a00c80341c015522030605503039410804d140c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 509191411 1250 509190161 509190167
    0x414030c061318060509130503041a040e070801050303270a0603140a02210403110a120311070f06050618040b0106080a090c360e060105011b030e0409050607030606 72
    0x900340342800c0d951300b01807003003003150b44503035003075601c84403d501041140c1c5962801ca82103225503003084a000c03607540b15a000421a1001500039100f800480081580b601c0d0340c1a5843c000c00d2060541c10307407040158007482c815410942100305042c110b40c1000e50000400901d00003590703002080029550306011096040d01e4140075001041d0040841c5441c00303007841320300b812421100354820406510041010107100c0d42a0b805030458010942d10b0020b110301d410504100c070703d40644002400c04903404c810f04070100032503178980d13409640c01a645189030b94400241c0720041200743d019014000b0141450f214940c0c2c68829441540e03000c0c031a42c10700c14003405649015080c0d55200c0d01c3c1c202c8030000601b0150b8000107981140c01400201041003800c1045018002d001460190302456022074100580e0000e915000b1110192146c980e226030044811441d6202c050001e03040700c403c1400401e001b80300400f011140500003003425080b03034461510b40082510132600003690750400f04a50b0b94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 509192661 1250 509191411 509191439
    0x70902070c05121002070f021f030f18020d1407060203070c0e28020910200a05030a030f060312270b27280e0c0414030c0613 55
    0x1408803000c3c1c003045030549000381c1ea0b40d07135014206421540003035100184000a1002005243c0c0200031088003007100d8400108003032141c09000210382421101e060900281c054400192107013015102c82040c2c54080105030f03501140240c68040c10b0300515a2251800e00c4104094412600103640d10103da03d0701d40c0100030036500a0003d4548203003071010011200070403c40003000c3c1040d582d64032401055410091046503030040d400343d13403160413006043c0c000c0300c81c00a0300103031241c100303d80c11300d055925101c03a00c038400140990020890350701828080c0c2e02075480640c404a00290440c0c0300c0d078440c03507007140b1914498042003041e03050f051082c801c1e02c0c12100000d24007065081140c580420b400e100d0203400b101d03018005541407860802400801415030710b00000b441c108240305141c115515035915004140c0300342e480d001c800318042c1ea006028034000c0a01c0700d42c0500d8545425140e80502c2445078800d50316000b0890351440c6941c2d1007000d4800050400464180b040c90100c014541c070f0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 509193911 1250 509192661 509192669
    0x15060f03050609070e011202041b0c020f0306040b1303091806080f070b0d24090209010f050a08010e06131a240921030c0304030b06030105040c05060d0e070902070c 72
    0x144c0241024005401820a5981190f4191440301842c19080c400500502050059401c0070031700002c0b6a000a644408a180f00da030080d00c02103120240e0717509064503210101c030301620743c0c4141c001152040340700724507a4081034002e180c02100c45445080a41030030100c03510020919403100d8040c8642442030040940e100c030414018145103140551503120790282c40d0745042c04130b544001c1c500c148042580011850310411902003801d42c5c80f0400740e0b0094020040e4030f4005160724020080d1a40034800f1508882d00a0f12600100d81c072b010441c0300d0280009141d00e1f0807051036981d00300c07491058003c4014001c00322495580c104090390904c0307000c030082c1030040400c0001036581c0c03c0c040e42040031160384e80c809940889500c0d4460140c1b00d0240b0010050045510000503559403055020002e84103403482484181e04c00e0f1954000c01d401d84105841c081c100040c00d4200704081d29202004000c07005003c480810000c1450840d1401c1079401d90040000c1a0001806130401105008080c080c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 509195161 1250 509193911 509193913
    0x10e0a020418020310021c020f0d05070831021906030506030a020603010b160206040605041404060b0318010e03070c08060c0a02030a180b0f13080106060c0f15060f03050609 76
    0x102c440d80c0000b581c1e101c5011110050650001d00c801c20051000200551650282030565170740d41400030291050740f004400c8c0348030364036140208181030302c9520842d014040c803813402e28400300700340c00150b1032902d0081c01c010000c610300b10b0341005071244903801e60f00b582903203001c6601920b014400380a8410040c80c481c420380021010400603958001542d0644100c3e015194035856624502409290141c0020790701a4020800082081e84103000b4001c2d80c6082d401c01384040c100c44144010384665010300b40c02401e0500c0028404148021002c00c000e114030004a4440f0002d0303e09425544204400d440c52800c5d8441480403e80801c0300f25002020324404130314010b0380b510300030348901541c0d050100300404828021400049240313110060f01c0816107955403001215601190f41d44a050190782107999074800062422041c070409088034042d80310391302102c00542d0b507a81200000c0a045525500d4082c0b1100c41103590f01c00c55000e00481c907440030380c031401d40c100381f454610300400e18516 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 509196411 1250 509195161 509195201
    0x112060e0411011103180f030601030803011401030b010e09130c090e01050924180d120c021203010b160b0a061d01081c0309051f0609050408070807020a08010e0a0204 73
    0x5100c000001b1030f82013042168200f920300c0690000a40390410f26000c03a41d2600c6202c0c000b006101c0420015412281c039090b070703900f40302c401c3c000543c161a00280c015000c1070301c000d204a420b003000b9007215030200c100c00c60101e108017940e40c2c102a03500946c01c042082581d6100c1c080203603c1c01d2240c1500304d03044100a051002c8800580c542450080042e480745254070307804102c840fa03146c91580d250040d28420745000e103552144c010070050a40003a00c4030b850400303800c2c01003d8004a00a14004041c909180c40d5a0800c0118205035100d0340760442030710452080031740481d078500d8415005007803200f0085591442c0540c00c90401960a10b601c880c02d04020040000080003d8280f0035140030194035401412038040030380040c00120b4014195005072814100403450000318030464129044041000a480c0c00080045680440303004100c1c0208002c4000070580e240003030145907200a040642071a10f0308003980c20350307020343c200c0c42c880e5101080d041e00310b16183c0a041201307004a105000c1d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 509197661 1250 509196411 509196437
    0xc07031b0602072402120c1b091918021207030b0618041203020904020703031b0201060308120c0403051b010e1203070201080c1e07141f02090112060e041101 69
    0x10a6a6402d100c2c92403004c0448600f800545c024044100c41344001c11015880302c07448011551904004031800c050801010301c0383c4114902000c4040c0a00c217004004200c4040512050300240300d24803e1010107907000c080c01c40166268060032210114241c003034005e03c1d06d1840c290041c40e02c0940420312032954a03152442903001440500d1b48950003281c0304615190b0303d4401e500a202d9900e00c0b503002030000415409158042d0001150313581d00b8a51421220306070f860480c221040390000410b580c0b0100480b0b80049510142c15400494403000d140c13906980e035440b10310f0002220340d000c425180852076a051907030081c510703c000f00d009603001e03103120380d070746403001d8032442a6480241440403583c081134460b07503080250b030041c00462070084a800a03408141d401d80e086032030f01311603c2c0080c04014102200110b4866102c0308920401170141c0429580000030390054410705d4108119001841d5081d4240d024a01c000c040c0c0410300c00485c00d0504202c500f0710703211140103041c01aa60a810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 509198911 1250 509197661 509197679
    0x100e010e0d050a050d020706090b01050301020a020307060911100f14120412140a0306050411160b04140111091906051b010204031a07110d080a0905030c07031b060207 73
    0x20980141d41e00e4a9981e4003039042080d42c070350091003010900f080c80480c82c0010088503a100740d0f64603020704c1000c0c090380c1c0d0310402c060907842498514001a00203200b90000601a9081509030742d20032801d0800c15071109000c5042c02020758000c40c00100301600c164130304e42d0450000d04002c0c80c1135505520b04014400c6e28007051304054001401d02d00c003212030a01c0716101e400110079051040c41d9050f65030030001001000b40503103000c0c1c1440f5910745042c0c18040d1882000b22003100d14405a200800c54251b151036584010040054518840f06108051009400c0c40384030500501184a19252225841031200c0d2444409800040c0404000e05214590f00320307040d1a9040b120b484042c00c2e800e401c2c00309601a0089174401043c014120090f2109540b105c0d020511991040d60381da02844125180265200d03040c0900e100890030801c04207422508a400000c45170b0b010303404aa103000750142c105843c0116035842039440c140c0740c0e001841007240743c012b1140104100e10042180e1b5040400c2d030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 509200161 1250 509198911 509198923
    0xc09090a020105040308090418380601031e020c150f0709090506040f0204030501020406180b0421021f0201060f0807090207021203030103151407050306040905010e0f100e010e 77
    0x6d84003005c00305080c04965a2034114600040c00c201c281c500c031206a1801601225a26580d00c0c0c00d5070fa43c50510754810709004940407543c00080d01c0702c6298a4820040d00203040240d030814000c1600000a8462040c500080094140080003440c07811400c5100c000c0c4450003420700e2121100110030700004c5944007152400b554450b8100042da40c40d4440002c0c001c04c1c0e10f800b03030041c250010400100b4803406601401c200ea070240c4864003100007a03054007100700d400d07015000700824240000d00074001c400804582405072014090018586600091184024048280846046070354a81161036080c0641c03c005c14010b1940d140c1b41c0e040c000756544541081c0601c1241c180c3c003181d030310203556428a03120109581c0c0410741b41c0d00e503180d06000038001c440c4806038141500308894400250040840c0ca8031403d100c0d6212410342d210a810800500f04480c820344056481d1615034040300d07414400700c050060f01d540182001c0c00713007214000650b009500d2034285645030180c1003440840c00300309 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 509201411 1250 509200161 509200163
    0x30b0103030207270e031c02310e070302120906060f06030601020c060309120a050a02070506040506181201060b09030f01091106070c0f120209060a0308090d050a0605090c09090a0201050403 83
    0x1020407204280c1403614a10701580c2105242d0100546042041c540302e0341c005c00e988009042d081e27a210107030451401c041118400220150f40903510b0401c8004030900c40d42e0b421410901d0302520f41110314106868205080e03c605030680c002e081400814988012000c03840310050300c902d4150315140340080d4455030403500316402044c00000240d81d07582d0611400582001c1102400d0301c408003c000140142c024030800b1001d0701c1484008101854000291021110b0040c0a2803400c1042c101c8541106090401036800c03010418080e070620b8400e0049030050030034a00440e8a03144090105440e00c820f40d5a550050792410a049000c100f41030940100341101307880da1750b50f52926151080789884a03510541d034266400501117450b256000017804054000c640c030a401ea00c41204120050306070740302c01071180d4000c2111003864208000501609802201541c40300e1500d43c5401048d82d10440f1341c0141908180c00421182c9840441190096400c400074071b060395141c1c0c0080c04d58401c03400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 509202661 1250 509201411 509201489
    0xa0b011e081c020a06050f01171b04091115030601031413030f0c0b0f100603050f010303030c020708030715060f0e0c1602131e1112091204030b0103030207 68
    0xb200c2c9144900810007015101d6014408201c0d43ca00b80c080d492400c03400380070340301d01702d001e007a101a09104005604181401441e45a40014070070f401004000c051300101220081840b003041141503485204003001c4006013072805030f0360304e48000010100c1c0c1b00008892445603c010a200303188009554015019605090080704845400c41c1942c4002c900c1c0c4005080c0481d0004000440720300000560207207403101d07034003c0ca641e00c510741541907034030495250f112001024010004284242c20020a000c8240192040c6503201c00c142c50850344900810b6461610780c0f00344010450651050743d0041954039118050b85003403050f0940c40d610068a081000040422a1002c001003c407203503090030383c0106041e22400b1842c6d405006032074460a0b004e030341060680300a04042c0140200a0742051900c00b032031811004080c2405690406000807419203e0700314007100d114949401040610f0080c0c0340b03407000c0c1d85140780c02407400019070003141d0803083c60a0905441e60b0915982001da2401310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 509203911 1250 509202661 509202703
    0x2030c03220f030309090506060909060108060a170106080f1f020304110402030a050a0c08060604060522180608010207031d03010906020a030c03050c071703070e030a0b011e08 77
    0x1c0e01d1100c0c807080710b410a4800261000000040640050300e0800316036410805104540e20b0200300f01c46409042c4219401122440015241e50722031407681c1c0c0d0140780140210701b01e070345641c51000d00b4021140350310066950341c6000c1c0701d002c00c20070504a010850a00401600544041e000d25125180d9400101160040f000c14104402604001480607000d48115203a1500c09030f020084c100c140e03400103a1600d000101e014151292800c035104001c0507101c14a01032600804581d954490f405c540480c0010000c19225a900d40c0c0d050741c02000c0078400c6160254403d494803045808950040d0483da104020040001c1d41010b0105180d071402031290021400d114007090141408210080a240c40040e14400075074065004444120b00e556040003d50b4480c4034906541c41003610140c4034901015440481d11003004c0290303808039592429a030003049000110b450154680c2c0b0403210501c3e82d800502c40d0041422001001200460056100300e10701118030780c035002e51a110315009948070b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 509205161 1250 509203911 509203957
    0xf0807030209031c080f06011b060b0d0804150203041401030b0102030903070e0901060f0302030a02040513080723160b131a090a0b0703050d0c090302030105090606040b0102030c03 79
    0x2981c1500c0c1c1018002d4141d401444542c64410a0b045411200d20040f41c1c0480110f803640e42142c0e90b60b840b600041c0c50b14207600300e014034086042c10003090215840e640303501c0420195141d0140c51641c0c07034400e01f0003644550800d5852100c4048009400342198010b0004000030450a20107941d144400e081c00244d505c1c0c2c840040341544149500141c141c49046000a8400b1035960514420141e1302e000b08210b80e100c5100c0321004d402c91201a41c580d1200c09407001504d015800150400910386182145029940d6030216035003042e5021307224562401d8810350101a80d031214000802000040e00d108071105502e80182d244900403000850800b0070040443c6044132801809412001d0744d04c0d100301c00c10980b44141e54020220280900000740001400f1004a416101080d50640702c8504000301440204005d250f048001c0042115035603000025880a2250600840b062400707880740340b6240c0144400d550070160501d04552040004401c0c55001006445010b054201001880040c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 509206411 1250 509205161 509205167
    0x160e0d03090e10030201020d0c240204030c1508010e090613080c16030c1202091f1802071115040e0603070b0c0f0c01080f0103031b05060108011e0c0f0807 68
    0x941028a0307520a000602c03c84041500f401c2084910036400c981f20702e2100d00c0201c2c2c0d031130f0741c01100414254103e82a50440052140700302c90301d0141d00c00040c1055501e40703500da1280c8043d805140c5400245848075800c5510420b0b060143c8503040c20314909042403c40d0705d980b0f050003000c40b40700008071001c820801052808680c00c11802204441e441180040c2444881e0a03d21088034402000180040c4101d5080042520355400900062036a078481e904038074152200d1211440c801119140450040200112103071901c4c18420010703192052441c040030f401000d03000491140c440c143c2034610690986040b20240d07401c0c00c46049a5440d41004240382807202d4104034190b14005c9040c003000a000101c00241c40742d20811070b404419904015a0a03180542da40170148007900018800f1901501d2000951046452a00001b11150321085d043c82000e810580080c0d441c0d00e011031140c01c0444002c980f061000d901004400b0404001600300380b100310001080c044807900080c0c00c940 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 509207661 1250 509206411 509206427
    0x70302090d06050106050c1b0f010c0606050d0b010e1e2a0309160905010305071215060e151e0405070909020d02040e070203070b1f030f0602070605160e0d03 69
    0x25020300d0a1180e541c581074098034941162072500707124401c10204441c0c002c009106d148c4080d002510b101c5282508000459221803640c10945445848082c00109910744903d84204580260544909541410f5106120250152000401003106880a080301e0044264540c000401e001ca0740920800300c0711702d13000c4405c01e9030030442d205c00205c00c02011080102d66041950b01c14540c0c82c00f8107841d512000c080311004c0c00007401d59840b040050003990400000b001c034071401100c43c1120f421508000b030b8107803140b42c3c01240602d1101c40c01d0040340920a035540703450340021108580200009a0842c403145074100c030191081c0e45410100700c811b8010b16400000c1d101045040d546d650a9881c0003020390b005104280319044aa0006003080348013006039085940c1c81581c086048d107a0812001c00746484c4000d42a140c168a40004001900c080080c05001d100b008003607115a01c5003031142c21038400a210403980707010f0340f0400f8506503001036151000c0310110b0300c41c1c80466aa080494942c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 509208911 1250 509207661 509207663
    0x7110a0c03080c01060f0803030109020703110d02010b09070314060d080906070602091009060c15020c0f0c030105150a030602031b040e061306060905040506060d0216210503070302090d 81
    0x82004a001c418005888000c06001e0041002480420340c0e81d01e4080200302d4078400c101ca503804c244010302402211b50000c100d9980685480e000c16044070002608080361600140d000d82c0d52040c1600140c02c01d10100c0307600c034003141420000110354240b62940e280b4002c241512400700740d2504010410280c050340d4640102510042d01d40c1c000c6d10b0800000d40c084007509106102c1c6040c85000c00341728038000c1e015941103540b111540c1c10349585e511040802c0042c0c0400c03441c2c00b8080d00044820800c42044400c007400000c2c41a50101d00502d42101c80251034130842d05603407108078005840750990041280c0c1d1001005a503555400c2c14001c03032035410140c6408400000400052210082c00c4090080302e00b2234044402420307441c240c10480741c0c14401c0401090701c08008201500d403551060341e01c000c010f03107550301d07111410a00300c049a02c81c080f0f921180128050804c107202d012011000c19884401c0f415032009000b94025026000007080c41c402c05800282a0400c1d440360b0203041600c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 509210161 1250 509208911 509208923
    0x30c06091f051c020f0f0706090506090706090f0308040b0705070f03110f031f15080f01270302030f090f040507020d1101090b0f060102150f011502060f07110a 70
    0x101c0c014000521070b50040904a2421000142d07524103600380d07200300d408000f64006010b1078000b442d1032206031508010025100a5580c1c10007001094090000720720401c404005002c0c0a81031080182042c0d115400c0001d5403942d102080c80016024811034040d01c2101c114175031100302e50318105141002c0b68006088002e82c0e0100007041190920b20708850400465403039220320758505c18556108547e50030340c5c0201810100e09001ca03030701e640c40080d021714000d4040c08580d484021040c90844213034901c0c51960354624034400001004080da007a5280c040c2d41e2005241e00545000b90359000354610b2625209000a91299980e0354040200407098094807e101d00d05e01007102030b45503694070941c440400c0c0c0c02c1c9040349500406225000c4c0003684090224166101c170104082c4a0100920140c1035104483e4000d800f180c8034403040d44034143c42d0f4541d00266052418034a011a6242071081c195417040f41446507010480d00c04070ba000d1030700d1070f0000001c488a48003c0ca004056040580a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 509211411 1250 509210161 509210209
    0x60c0c081006051329030a0b1003060c0f17131209050306130b1602032214090c16030516030c06140c04031407050406060e03011109030c0609 62
    0x401000ca8000d40210740c8102c40c1d40790180c1391800c0b540261000700f20500301030281d01d006400115031008005032190320203001c4030a46c04003a6140620094161440884041c1484003001004100e0045080c131211a180c95000e80d6001c08ac017914035201c4c040e00207030000b0400006440071204c1c5840110381031f00b0565400c0811400c9002030500301241c007480d402030041100286252a41404011000da8800b00c905960b50700c2c841c4039a042c1d0350900b8210b0440c001008013014002100d000b03260709103070403e060318019152100724090018008031150107058100b003048007203099001950100714050b1011151400b00e031804692510500f4420765500e90440810018036602982014002d44549406c01240082000b00980302e142100c140c0d9100000300000c0c000204043c0b0240e01c0110f0710380c2282c070b106440d40300290545109411003000150000d08108071458240107120034490143c002d94a803400f9800826159040c1450b0603000b08000110107000792a048580601e40210700044a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 509212661 1250 509211411 509211433
    0x30c030a1b120f03054605101503050f0112030c020307080709060b09030c1e040203010e07030f0e0d14040801060605031e0702061302040f06140406080c0604060c0c08 73
    0x100205060111000924101c0014059441c00e5501000e02a00c1c5d001c0315400300741e02603e05041061102d090781034480380e440d910b000211a014080c0688c0c200b11a404c05181404c11540519500c003462004050401e01404020b000e0461001d0543d0801c1c0c256a9408510f81825103144002a100941500c03a001001408030004525001928800101481450f0342c844002000d40654018640d041d00403c001001e1b9203094811003c142003000d400381b0030310b80d4020001d4200e030400d90001005910b40010070161a0b1f01d841281e000903040c3e0800c205003640354035800d9076080000190340034858803a00c2c0e002035143d2202a1001042d590000384011030b294070b0000c0c195041555440c0201b800d10f00c0040c41d41003281d15052241c01c1550090259039500351a807220f00a45107000c0c0c0e0002c0e075405061905402d240128409000201c10b01d41e0b0684d0f00c0c45c00c0c0001c85031140c0c000c01190704040e2109405aa0704403c031400c5400d01d10389000320204a003400b5000e284164040840c511031a40503034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 509213911 1250 509212661 509212667
    0x80f09060c0f0105070f110d080603070f0303020a0b010e130204230a0e190506310c050a050a0302130b0f0904050a030807030b10140f13080c03030c030a1b12 69
    0x1845050580c6d00c0f86601d983e014000e841142d100403c2d860103030000714a941141e4840c9440310360141008045554035950b4610710400b80506400c140c0041e08481c10505c00d00000081c0b10380144600e40c061004c919144180a443d8600480000e100755103c104152090004c990108400caa0103100360070b4034180714802000401c01ca8a0f102580d02881c1440020051490604200305401c800546104da0b02c80c00116034211000411981824107403080a02210b00c8884940c0c940e031040b1009003025041c0030070040e00d90016030005106000c030034030070300040e200c641812840c2000210040350590003040007804c020b40356400290003040700010402404400501a0081406521440c00d144c8071550210142c9024410721074019401c99560000a0b00c1307182100ca00410f160412414030040c10300c039011540c08404189000c00c0881c030180811038007403002d00003003801200254508a015441e240e100d0240c288075406026440c900031001d40d1500c0403054240b94071583c03045030000a84000b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 509215161 1250 509213911 509213921
    0x8060901060806041a0709090204140a0b0c100237030b0402040609030b1e090d1b020f190801050408030711010905060a020a050c030705012304080f09060c0f01 70
    0x490060341c01d050001800390004280320740202e802c00160303e00c1c9064940449200b02c005854a420000c0202e0300045111843c40a800a020424049104403400008120f603800c12500f040070f40c4082040341e5400c0090002d1082c040c9246101c0141c0c803a50028900311414244480c0c20f07001554088189401010082c0c0c50180b80007180c8042200d00441c50602049004a019001c0801d88101c3c0c1840441d211200182d03003c040540340864008491020a9104200f039903002e80c40c2c0c1c05003181002e45500107a42241040c0041070300e80b4083c01a400085000851240050042da10102102c641c018000c00d0280a0441e10f0000c2c0420706161030140842e40c0110380780c0380060001030b008081c41006002c1c0d480702c0d9810000a044a031265030b1170a009500c01540380060040800c641030000c181400038244040c0224000a044e01c1d00e50320803131140d001c4400c00203401c0162400c0200180d443c005a41c3c202d00c2c00e584503030301e84090070702141ca0b603c035080d5a89400d01c0b401c1c010150f110015002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 509216411 1250 509215161 509215171
    0x906210a140f101505010c0203032116020318060c190c030b0903090d080a17040b18030c030a050a0c0510051503120706090203071d0906060a1d0c130806 67
    0x11191242d014080c030b40221901300d030501c08030440c840303420130596204031010700c61355000400752450581508108450f10319002c040582c90040e400400c41c1ca801e8100040c0d40040d01400510f24083d07010014131082400c0c0c0c04111310030712012910020480003040f010070844d03028440049080014281740648841d03078802220403000c0840040c9255102106803048000003404000002e000c2e07589104184d08030b1045d00c01000078581e0b039208012440080e141c000d60207103410310014140a48810904010558003c0311540200605c3d848000c0c000222000d00c1c40340d113009a00c40410f507100300c1d80088810005002d51084100c40c00700d50030140d021034001d1203802c520030940c0300c501081c581c0710f00288031000900b80c03040c49840e000c20340703940210344070510003420385100c5a100c0503d58076940c11010f24a555802850810603400d03420482203400c90022100300151a10303044507446540910646599142d1141000c640d501000c0010b032040b080315000e900c28a1900c4c2c0c0d402c80d6440c3c1049903 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 509217661 1250 509216411 509216413
    0x306020c01180f0b0a0f0903200106060801030b060a030b07030f06060906021005060609042405030105040c060507230c040f0b1c0f200108060906210a140f 68
    0x4035500e0540a05100c0610315611800c8544500751a4590380740da01801800751100351b80302c0754140030f403c0f0306124400c5018405d4940751143d0f10b401c030401403140a0500d81c488268502001806400c0d0800400c41c1120751051a0941035502c203070200b00e1300c2c4c40d907520044c19800c504091013007180e010b4122082c1e41034001d070100009651000116200030042c854400035070820b6403a40360001c1280c020b90b03400100600180e00d040e88041c0410101c0d140300b03030b04107403100000712100b040003082c5601000601c0e00318002d008c40d00741601d030780580ea11a03105140501c10000707292410485014054a6259003601003009502d480340c000b551107040c80780300c81c0e1149180000904030707050144900400e040011700004080321711684803081600f05c4400076649800001d04080005030203104003030b401003d49180c0c2e80150035103030004d0145a40a4030040c8500a9a801c00169840c2c02284032607801c030082d4880a4003084041180c10052942c4024005402c1c0007540030a010f00020ba03840010381c404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 509218911 1250 509217661 509217671
    0x108060609011404020705030c0706180902030c0a0305060d020d03020309240304020d03090f0321050306010806040b18010807030302061f1811070507060e0d32070306020c01 76
    0x38200502400709020301003a0b80485210040507080a901400149124104803450048000201803400665134050340000708103040d42140140101c880d90028000e000081d0f0440c00c0c2101d082c1028042e24550740d0030150740c0d030300040705503580050b0341140680140541041940e141002510fa41c042110640501c0001c180302c0c1d1002896034078003090300352201b00d50b800c6031119800c00501d00b050b10416001c2108099001c180001d103004181c00551066040c02ca0204049202038090703840300c0c03698001d1041c00e0040141590300040490382c03004048400003400220500040e501e400c85030a140341c070003030020001c2241e80707000842e8001d580c003030f40844455079110b00d9050300a20028000c8910b01644101c10409146000c030144550305100c04007181c0e10302d40401504560b0000784060302e480c0e000200c200901ca41202c500c400140702a2900c07a90408181c030380301e400954241025040194503000c10010007031782080c600464820704140c908081d030b0f908002000e034224103074194840d4a42 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 509220161 1250 509218911 509218921
    0x118060f0e0a03140a02121902060c0304030b280506010807030906060b0a0c050106120c09020d02090402030a1a03010605011b02030106081608010506100906120e070b0d050105040506030c06030c0c070608010806 92
    0x8c51a01d02403540c0400c000a408503420f000302c50708075158404480c801440040300003444089041e10800c0070040315210742c0d115060400d0040704c01010003522a00e40b0060049503648580060345c048442e04020032031000a186c510001d15031039006540c040b501156211085920440c04510680500028000d103034071600e10402101030806e0090070f1403441001041101142d8000c2c00455050b503400500344021a030106050343d00403140424102e0361101800280841903ea80e42c107041d00f41c000300103190034140040c204445c60b100e220b18515161000d2800c65809401c01000b800540098500742195569440c1c1c0c5541103000c1d401d003550030040001c0160500c180014500c009507a00e000d5140c0c5400c0d815103140c0700c0c0720340c1203c2d0240c513001652001c610801081c1c000308001c00c80b0350740e1029046002002c41c1c00682160340f055003030a0600c5034550f800240e0000c0e480045640c03d60700d0312a1114104148207950940e65079000700180040e43c160009081e41c101c071074410589003d0703a98 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 509221411 1250 509220161 509220163
    0x70308100501020304051207080d090302090f07020d0e0d02060703050319050f040206030414070608090d0809030708031306110301180e0d110a0204090b060118060f0e0a03140a0212 79
    0x11501601d40140c1c01407000308910318106136111a100791035070a075402d20782c403003500364140543d0382501d10105112103410000c50401c080301c554880ca001920b1b0005051521000b0340b100c044a1501e0200404291422143e40e110041c0492040d401400b8640d6000545005001e54108560058a000c1205502c00c00380409000c1d00d84140008540c076503603940c0319070800085070405082500e5441d01c10000100e945810480000a04505e40b42c14100b880c051000c1868940c01103045000c00c402d00c424402c640c0700010541c1c11443d409140207441c0c2c0c0c0c8111000c42d02164071500542603d050044405070b051040300110306031020300b150790481034401d5a12170203071182d0b144080700c00c0c0c3c4003c0e500303503450f44507020000f1005484815690640f18507000101038410404050300c0200010003031040075070b0081c3c118080000c1955100303040714508500030301001e41201c9841c00f80f040903044c03041c1694410303601c40051a070003421031b070b44468090665550b071031002604a006103000c058100311890 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 509222661 1250 509221411 509221441
    0x3030403020703260705010b03160807030602210a2009010509130f020a0801090c021911032107020301111305270108150c040e010b0c16060302070308 66
    0x50550000c24010380b8640c3d4980d401840e0101944d034400c20314400ca11583c03000c00061415502840010a03042c280e03404060612a0310920226548080d560400001102140746821a6040741c1d005854a413048046048030700e0b8510600341c81000d50040081c8179045038450403d8a120350081e40204d0b40a9403458034038418401c50a0119030706100600240c54804080920f048060074045039013800c005401050b038019464a1000c02c40b074034014000300c10603214405000300244028122403409140e00100b02c0501c42c0080c181c082d048402e10500c1e10204aa440a6240108072080707081c200e00342c41035185c101d40e60803442942045014401c1e880b28005542e10008403c0d80000410329001c01c200ea03031a80d0505840212050294106110a000788028020300041d80a0810044d0203103a104111400424001d4400780500c0140300c1d42c15030401d414103580600c550340f0368a0740d0807040185030003d41c841c204152a50100003281c2c484d4590050008a840798170b40700c100e0788403826082e60f00d170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 509223911 1250 509222661 509222663
    0x17041a0d02041707081218120708012309030a0c02060703020a05070e0901140c19020717010203071403100509040206130f18020408030304081b0a0b0601110604030c08090406080316020111030304 85
    0x347e203860000e042880c1c440052003035282868111201c0c56903070301d003a50940f407942c20324000007514900d010b035401c03184c00c008503031003109100503500e0300ca0070480c0540006211440a0702a9001040040405000301304550100c0d0b0403600701c4102d6560703040b0074107a040045075102815401e001c3c0482071041c1c0000158014001c01c0c5409082607042900f407105c04240703520340c0c41144214580051109140d1303899002c0d02081c0400075960307142140c4081e055800c4050b03d0b40c1000700801c100000c002c4400c400b04180d07903003112010115115030002038128041d90210350440ca8443d0f00029240f0303002e000b002c08980940c04581502c015860340e11049010b90b1143d0041c41d0810400180000c07031030780040400041d00350001c0100c01070700030860300d03107000c6400440e0540004c2040c020701c0e680188000d460701c89180002c05083c50550b074004c4c882070412000424011010a42e04000e555a80200c801341046008494030340410044a10090788a00300a0f80841c0d40381c521100d21a101201b100d11807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 509225161 1250 509223911 509223937
    0x50a030e1c0204051902040801061e0b0909040f05030d06080c0d02090f070323060102060a06050f100e0d0b0609090604081c110f030417041a0d020417070812 69
    0x107011980900003c0d01c8001d14404071100f00c004c605604100d51300c00341003c0c1201c0b40c0001141c40c00e100c0019410901c0048558004002240130483c111b2400200c898090381502d56948039156880c0c842d11000c100320f002815400702044018410545500c610201c9014a003103c030402810000d000b142c400d10342c40a0f4110200c1310010707068034415030440d50007403450f280001d41c00440c40500c2aa9250701942103040d1450103091244942e0304021154002c1c640010421107071740382c0400581100010320303043d801402d5503152000a1400354401142d8a04017420410351540b541c40c18080046040783c030381d441404c43c03502290070407100141440c80f659011041900d070540c8004415400d030346171a41405805c1e103404900c3c80c031300d85030340c05454500348485956850741400d15081d800303200e554610b844240300a001c00c000d1009044ac0e4195045200c1161554460b0080c11040103442681c02c01d600611001d81d00c07010b8800f001500800b2501c0ba80240c1d1221a0a42e4450351144224032181c17a00c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 509226411 1250 509225161 509225209
    0xd0f0b010504050c090f0f03070f06030605090c091e060c0321070206182a0103050604140a0216120f080f150f031c050910030e0703030c050316050a030e 67
    0x1246c10700c40084803040350014560702000c00000000707450101c09400c800c468000d400b01c10881960503014250103020112062643d80c6030074200c80126002e521480b611510400c1389086212070300790800c441003000a8a00c43c8e445c40c1c101440c0750b9903440208030712409040c50400c43c2d04028082e030300c68060041c03036014061540b42c03001110030050703100e00505202d002e40c11078070980010351140b800c20180c545a0f041d042c030102400250484600500c0781e401281070048404c4c0e450a1440c13203980c0515072040040c0c5039410719241c1c40c40101c0d901801460b02d450301103110b07030942c6c001000d2244880b00d40d84403509507075204c912089200d8182c82402c031500d00c40569100720f160042c440c020000c400740840d40c444244201a039800026100e4550102e030000507100701d1410000d80e81203140c1c240e401d0510003580c1c5002100e980e100346100c050f0800140700d040e00d04000c024021910003200c082607103020300313140b402c3c0141c488941000480200c0d1400034450098100420034210740c0c440c2d9600004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 509227661 1250 509226411 509226427
    0x90b07080d0c090b031311010e0d0813181512080904091713030c060306210302071a090f330c0a080706050916061803020d0f0b010504050c 61
    0x1020340880c050382d07024480c0b80c2c0c802084444482d405988220842d8844103610109820501c2d104899440110f04000301e101660541d40c40309220381080135403084955640315540072504c2c01d032800c240c00480a80440854603414500c0c16001807105246502c4000302481e1f65407041c00d213000000100030310000701404422a580303004c0d40a0074603140500305044100c0f03580c194505907548881001c0160f0302100c1d5050050044001d00703c4003524403814200051810050801c1c40c0b0f100c95802500030310b9400c1107080c10148203010300c170700030100499881140d441d0161741c140d0f030343c00c0b580860b40035040403460400946000b00e034010800700120341d20003484090703125205403c5201001d401414104205401d40303000304020040f603c0d401f601640307854041d68035010003a01d80150006610b6402500c0070b4480380104403c00c0c04aa0b00c0341400c65908808005c1d000580e20140d001a500142003910a0140903a100d4803d41c081d1040081d421240e80b201c04000c01c441080d1559540210103010f040703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 509228911 1250 509227661 509227687
    0x120a0b18010b0d0605150904060905060603012309030f030106050c100b10030b0a0e070509030115030b0705070309031a1f0305031c1119080901050606070609080c070f06090b0708 78
    0x244c2c01684c5140358006e00c2c000c103004258a001c05072801c80740c0e41c0c1d0310012482071003000d1000c2504100100c00034070480c96081c1111840f00c140c600340d01003022110011880c038403000c00489041c000300c0e4042940320746e0b44140141c85608001f80400c0c1501a04207412130946140c85600740d02a0020150f0f80032045040c001c4000301450700c40d043d0000f1340300d0f0300451448040100c180c40784085564041c1d580b8113010502d800d5613200c174032052020503900e400b0710010711128072280d8001e040d442d0244e12205541000c65001d0104d50002e0040c1603045210b9003140c104c60307011b6104880000480a18045034107000c40e030f60589100182440d00305001c900e0051081170640c0640b0025031401180b01503620107070070141da000042c991002807000e640b48066070f402c00b07001c035400006517000304000e03e0245d0200e881441001d00043c1402c0c3d8900122081000c4102070703c0c9001c12400c21200d505440341c0701102c3c206e046010310340100703007501c00001d1540781c400122480d0581c0004610b0428200310010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 509230161 1250 509228911 509228921
    0x3070303050a0513030605010801060911030708040f0804030b0601082a0a090e010e101508010905130b0906060306280207050a080d0f060f0806060f120a0b18010b0d06 73
    0x1e0100720013081070440100c0c0e614255405140201000145540b400049070f00b151046da001841d40c80c20701d0130f001750080038042540c1e80300d010340c10088a943e4840c50626074440601000800c040720204000c03050001080b1000c4c031811081e260043c0d2a1500312201010004040020042c2d0b45410304d00741b224000304000e0b0140500301e0400400541d1291030302c902ca24002d070414284c1c01c0c180740c100011074a10042c41c1d070042c5111401c00840003022440101307002c00500a1004540c0c9600c0810021858642c0d82846150001542da50900b000070403140c4a450944007107100340300d984c0119481400a005103101d86603540001c65001a102442c44040d410450341501c407400f0346101c04002c61210b0000f0150742e1001840020780d41110440d50301122802e030000c003054000d403003007070005070000a80e071350700580d00300e80c41106541c000e800107a0480141c200606580a041003c00402c21441c0e002800381c8041c450110041030100245400c0b0758011903000d070b00c580d1840c00c3c54007003801782c0d020b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 509231411 1250 509230161 509230177
    0x906030a1509020f180f01080f0705040b0403030e03060a27050a06140a0c0305060d02010c0f120323070503071107050d1a10180e010e1902120303060307030305 70
    0x540792190355a503807010200c1e088000c020100d0744000801c02d015899019144451150480c0e40303090702812600002c5c441d01c001400301c405540c0304000b050f1464010420b440003044c00c220b03202c0d5140c2d00c07480c0080c41405105c1d1a0f6004e88540c0022807014030b900d0107440c01d03000713400c1c0044540c07140c81c0300000c0d440006110280c6483c002d54491901141c000d00491718501c0990000e050302e13082c410f585000300c4041306400303020185403006212070f030303900c003c8a0b0180e584c09103846410718850303040024201140510003070000d401001082c60b01c5030580c0041845000d8010034100048a10651074140c507002c840c6d14000800410000d0102406008941100c15044048444268903280414455010b0300c9059a030300b00c4541042404ad1401c00146610100540c08141e98520703010b41e001a801800411040f005e40745c4403907a87c043d400754030441419090500703c030180d40d10164000501d83c203282e426402111100580c1042c0c1d280041213034064a000788c0202405455a10100c80c99048050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 509232661 1250 509231411 509231441
    0xb0103060b1603050c151608090d032d0b19030b0103020913050d2d0906050d090602070c031a0912090109030807060c020d0e01020a0b0403020114130204110906030a 72
    0x1179110600710411203d00c0c14401d10200d00c00c02d080500044080045816840f010804405c08200c3c00142c08610000c40c403245007004a110410b1008a92411104003203441d06800c203aa40007002e041103820401e8041c03170581d8841d2403046c42d2489800180c1c041e00002d421803a04a0040005041a1000b541d0019000484444001c0e040c0c0d5080d0514183c1642c800004801d40a40f501004540b0002d01500c00c0d1004028944003101e04041c003d06001d125240502c007000c942104070100e10b0f004170215a6129004540d40c20075803811843d107103a2400103454406060000014a420035195207015250507402455020741195903440740e40e018041d5a410000110000800210b00d40064002c051041380701007019001d080340249002d40140c07000c0300b0003481820b0107601e40d8012a02e001d40760380002c452403482d6039906003a8098003508400d804004a02401c0040c20402d110401a031284200d0b07003800400002242c070030440c080e4180d0203a0080040000c150383c0d8105e54080891407581c82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 509233911 1250 509232661 509232667
    0x20a150c020901030f03020615030d0804030519020f2e050c0d050a1b02070510083c0c070c050f13020307091a0a200109020a0b09040b0103060b160305 66
    0xc1c0c08a04808400c0e801102c0101048164004154040c00350a07404804c002401d0559000400020750b160a128001030520a610f800b05040c0f500c20012204001b400240028076038400c000025501c0d100e003c4042e0366030180070882d83c203600861280402030950554801807100780d01d059240100b0703000d020755483c9401000a030040b81c40c2809407034401d046e2031200003a1a8090300c00d44203200c000420708402c5411081050001d580d41c1c50320503202c0300f8a450140002d60700c0040c1014603160448248400b0005040073318402c00380805a1002104205841e03880b64541190750000d0303009004004000f82003018051142d4200301d605554004801000e1245034401a400b01d002c80e070040d640100054550030f010f22400c0d24829425440e12400d40940745445007855004021a0445000d107401070056000d40031030b40c2c0250840410340350010444442035945041904940e4064505103019078289082805e0541c0a0b10903d0b04540e4140d0040f8502403103c044100e11540000080741800024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 509235161 1250 509233911 509233913
    0x601061b061e0e010603170f0d1109011106070f0c1104290f090a0518120304061407120c02070b1303050705030a030507111c150c0903020a150c 63
    0x141c0501c0c5018070307007034201245802ca41c44110081d105025a1110039a050000c1000002d10803000101c003481e01500c000d032114040401c2000a20070b5000000541d41080b40a941012460340103010860090300e440a05144181826840740400c0b10400081101049031811042c06041e01c410f28520601f00d051003541c0c0c140c0020101c41c0c00d5030203d00082c899000480c26075960160301441000100d43c800b10322114180003889080c1c0041c180000c00341c95501043c503070f06640c1c2c011031002d03171341c1c02c05e650300b0798900c404802654000700c3d020303605141031607101e1724000f00b0901210b01603891596000c08540c030805903480034203184185d6408511844c03000041d0040c1c00005400801a004101e200311440c5040291405c80c10f900494401e801018030040040c3e00f00d01101c59596002d440040a080103400140c0e1207401740407045000f008446100c2c0400100780341c0fa80940cac4000000300001906450101d880314420b000080d042030500300c0c02e001c900703c0504108550a00b51828031072444907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 509236411 1250 509235161 509235173
    0x172406190906030b0402070503090f060c0703030201020903010f0501080a1b0b04030f0b100b12130b070201020c0610060c06180204061806050103021905070212240a09050601061b 78
    0x1040080000110307981001d024560f414001c51a00c04011501581400d000f6100c0035101c0c07240c6000ca03032180f25500d035510441d0b1590f10541d180004180251003d4a50328240a4041e40c0001407452180d4a00614075040d42e0342881414107034ad403000d0040002ca82c6540c0c800d0642c15090f080324640c01d40c41200054080401310007000a1481600c01c0c4001c511240340c407061008000d00351902d13150345000c050040c40d80c8071040d40e5030030400c5458000c89494040c0702d41c0014400039006002a0310000400040315015002003141490b441d08030745960780c54502e07180c4010114000c8030b00040320b46003914046800c07600303d00c1c491140f11403201e00c25074843d8006400c555042d0f200c60000f2090300d2000d002c44203544114002041c080c01d080d031070001c00710341c01201120581115024404007040640640d01c0c5c008030a040a6180e00c03c460403214804091881e4020390000b00e080303810880c001600c8907000d4021515160b500c20010034007a401c020058510300400c08156003c00303281c822900109007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 509237661 1250 509236411 509236447
    0x406150e060d020d170702090f0610140d051003050c091920030103060c0801080303040206090108070e0901030602090a1211150c030403030302041401020a151a0307080706172406 78
    0x1740d01076a041e0341c0c000c144180082844010b00c510f09249240701000070b1902c480b208007120112034905601c85440128200b601c1e400f03400c03011a0b60901d402c0401c500c0c0d0300c007003581d00705030303409801100c907070070300c04010040941c3d8221442c1c81c0741070100b92840d044000036000707200c04814405c00d0491014000000d201030b41c10903401910f2050702c0351404050542c015098074007500c100703c0518590310780740d00403480920603031080307604002100c0300042241d84150b040c136000b000e0040c1801d03400d50f520304101010350003458101d0710503d0512030005103a207106042c62180c9a00c2a1101c01401d505d104124000340003004605201d40200b040e1101100140300400145100e0703107005856608022061001066000342d541c10341d4411885140454005140c1b96407020407240013082e40b42c004840050102c16640b81150944035154020800c040041403810541d103640c0d94040c178900031300517003c11400381076030000c0c5501007489800c0b0004003000070041c480c120140c0f40e1882c2444201022404c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 509238911 1250 509237661 509237693
    0x1f0e07050301470c0f010c0f093f03030b030d09050a0b09060912060103170408101109060a110d0c0b1306020702060c010b090903030c04050607060e01060b030406150e060d020d 77
    0x80d65075407014921f180c02c0300e0546100211840d110486a04001e0103c285100300c440c800e621003248940c0c1030031044901a01004101052078804d46d000d05454064041c0c8075005c4114072038003c4032100c01c54144280352040846000520806c4e20070320f019985c020651245042d01e4001404100e221919214051200d0049e5002001421250725604040300890303e08000300000c02e00810042290110024a0005503002c0c0303a00000c800c1030304407080040f8403d00700003507000900402d940c1215900005a80c00b80c034050800d440d8100c06070389003103402010609004088500d00c00200300020544a01600041d1080d10b0061503c0e0464000801e2030b01304007021801c40e91650441002414190b82079034010b0807550080d4114142840c1c802524092070007168003c0402046260500c9181d8003c590590450002001616101c9103407480c5a8400ca0b4240c81d900c1c20f103500007042c48840b2072241c0403150900d001d440f00707440e840c2c00c0040c000b40454090345e01900f44040030000c180d01840c00d903850 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 509240161 1250 509238911 509238913
    0x71407020303120c180f10080702010e0f010c0e0a120b070c0b0c0705190804091a0d05010507090f08030403061805010f060602100b091f0e07050301470c0f 68
    0x5d550a04038244050200c05805010f40c4150000c20130b0340d200ca0702124600e0319a400e05e103c055a540504900501c0c090003424500d200300074140100d410107510103860b007001982d0b41503200e0200c0c0305200c2c40031007a01c1060384400c0c45190070004a50609029504980c040ca4142d105800390307190a00541e005032688407074a40001644420044108504140c2064543c869942c06486840b0711340071380502c1c420603c00c96180d102c64003040000309040c1c00000c800a0004113001c046080850080008503024408200201d10126665007a9841a000c654400c0c009615150860780d580c0c0c0903040c000f501215a501c0d41c0100d0000907002e00881d106a111800001601c5140441c000e140c81d881e240030045452800300c0341d803039645880d5003151780300da9900481c142c200003090b14203125107402d602910310740e40c0c00d5060200389548103004504036007424080001042210f40b41084014642c2c0c01c3d41403510580040c0c051110761051000700e0140424801800d00e08400e410070b0620000d55200001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 509241411 1250 509240161 509240167
    0x20a140f04210c050f040e010e07030614040b150f030a030e0103060b0c0a12050705030307080105100527040f1406040e0109030516151a040501060206071407020303120c 74
    0x140c8140401e220800110440054001d0842d54071160310f032102d14040c0e1401000d2007011804161515008602c01821001c000c10500e621407442d940c5030303034079800f0440b040780c1407004000c0040d0252100e903008035008032400a041c0c070b0341920b46440031082c40d062604041c4004034041c1c0d907a0180507240c1018000d494502c50503011030300050440340310341c0042d003155109000c080300110000a00320b100c154411840444411042c105903428090444d00609c00d00c00001040714455008580c03d0413a0000d45902514500034171090b20603010b07100210040d40e152203d66200c00307079025440b03900f000c0040c00008a521a84061000355207006000d100a02920000c1c8905410305219a5140c001150000c00c0200d425540040403817182000d1303600d842550401400500103030000031002007074020b01c20030503250300d81c8103403180d458070709500d0b8411481d000001450900124030588102d005550b660802c02e03c2d0440d01e8426046004180d0b010700c03082c00f9400e00148443c01d054052004070030784c030fa1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 509242661 1250 509241411 509241419
    0xf09060714040b0304050304050a080304090e0d0f0c321e06010b03070315060306090c020a03020d050f07050313080f0a05060601030f0e070e100602060c0301030303020a140f04 77
    0x12604101800000c2040300c040c1668a00100e400141c8041c0e0b8440e8078016503030f4503075040842c40c0d0700454001a500c450114070010703408034000002d01c05c944002d4414440e505014a40a40720030500c469000402c1002081c61101e42c4150198015288181548510411034042d42d442c65000c0002c4908a44001410029040f00c1044011000d00c0c000120380400c0e40d1388100603443d0041032003180c0302d204011000c5420a4040d03048820030309011007164a016a4480340100681040e1003224149858040240304885c40441d004485682540041c0740104646000300c500e07600a252501038104248101400a103041c00104100c940c4645040300311401d18600c0c50914940c0000c4484035400300c4505000100007280565202000b4200001c0c055030307404003c0e000d8900c90703403150518000c810020030742c0421400d400d03001c0c2c03208003134011240342c586109030703a034840540e4a841c0d0b8000c14401040040e01c25001002e41e60904e03c0c141c0c401c0da01405031201b064006d102d4001006001040c248 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 509243911 1250 509242661 509242663
    0x2210a030e0f060304020d080a120e1b180411030c030f0607021507021c09050909100b0a0614032226040b093304050f010221030702070b030f09 63
    0xc0b415442150301e81c3c81d6043c1640010410200d040c001020454046100395038540140d0080c8206051008140001c616840c1c1c1552038000001540c0d8140d011054148a24284a0310030700d900b0700c28084c000382c603440300d4403450304140700d80298a9151042c001205116241032000582004c600c00c0100710500f0003401c082c0c10700c9004e00a52904030340c803004012501d5070002c0c544401208802035441c41710034404007101e030201c01e81c000e19000b90182c2c0c10b110000c3e50008001c98010b10070350b002c018081d0705800f0440e5102c8148103190000389446018000010180b0085401c422040c0d11554400301b85000b002c0780e0841d1510a90326002c410118000c10640c1c40d0f80f0455146440c003041389131504028044440d8002d0b0b1094074000c80d190804d1240400503604400c005c13001100f005045000e029074290400c0c3d000c0d015075400390712401520726055000089400311442850030130313903080700e000c03030550110340008203a5421407149280029030000300000840c01b030011002044480e2422a04803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 509245161 1250 509243911 509243929
    0xd0204021303060b040617071203021509060708070302090f040f2d050906040f1119080109140705010f050304052d010b010804170d0b092706060a0302210a030e 70
    0x7442c03807c82c452640c045164000304900d4180c911107600c1a62000d81414120300e001c10010041030b03d01c1500f410300142c0b210015000d449080b1507940c00501e47d46030142101030f0b000b5403e0703941d008081100d0100039460160031129000386c80a03170010b40f03c0c018030070000c80d00c6d03244d03031500308100541c000d544241415801100d5011400b4001800b440c11705680305405004802c1002d01000380c00e40100d0030541e607001c0e844e08508403841e40b418029441d496042e0080007179800440d0342c1e4a030900101c81c6100c02099200484105864429800c81c01c0a4140c546a000070b208403003901507503004400300c0001203130700c001251644110b41d56110703200b40da007800c480f448010039061195000400000030052111041c40740c42c0c05000a843c0c4500b0740c04c1e10040e000074117200c0e82c08080641003004d41844c02d4180c240f40303522036046503d03242046a1040d264139041c0c031019088100c2d54014405401c081046400c1b400e080c0020403289801445018240500d5540c1100064108141c41005141c0f9080c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 509246411 1250 509245161 509245169
    0xa0b151909091a1005060702010216030501060807050405100b03040f0b010602030301180b030601030305180a0e04060c0918021b01091b08030405010e090709080703080403120801140d0204021303060b0406 89
    0x83c40b0300390708245001800caa5180e1084c54452040084d445045910a0000740c080e180b5a1100088494481c541540608158000c070109032044200003c1d107071030a401458000c0c3c0c0c55041c2149894100003401314540c3c0000c0040e209062170424510001c0c281031046c60080585074040c54495041c50b590032a8a482d508400c1c1f0640e0405072180001e036400f0031140e04480e814200203648030108542060352100341d40c18198026414040000c0e00c02d0203104d00c034820740c440c40b03040042c401000700603282c4120600425010110301c0315841c0c45a20168000d14900a07001d0242d8415000200e8860079500044007c40c0c0d01c0f90f005a0710f94400041454203405015428040c5043c07a080600007041c50003041e15503441201c0080101c3c8019000f103000a01900d0280152081141c4900340382c0c0d400d600900c000c032266031100090344d171052b1192402d117060700c0050b8400c2043c40c0040042001e5841040c0040c1d0b401542001207403100b40c580c205450046103c0c0001259500381881000100d6900740c0c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 509247661 1250 509246411 509246453
    0x9070f090204210302100519020a0203090f060301060206070f1218111005070605100911070b01090507140703270e0a14010b0c0a06020304060209030c030a0b15190909 73
    0x71000006030300850b80361b08440422100180580d21810301180d9a10700010180d80d10b403000031482440f41d80400100480071007500d0b24104841d00f8000d03c085c51109226030130058101501040b5558895610f0640030b10a9281c42d80c0c040040b2824139044650b40c0000e25110380c074030040101000340c205c1200d05c5107402103402441122800201a0840c85803d0006006070b0f81e4000280c00c9030041034801c0085d018a5400700f11113422000011516030082000b503501110b4600001180507250190b10700c107040c95030311a5030130040e201c141030bc640c0100c1022001d0240702205840001300a1070980b5002c00d0510402c060640307003110100c0c44000180400d20350500b030400544448141c44044c904450303ca14081c9c0e03039404203039140e5080c0100c005004002900010902003448601d40241000c1c1c5000c800341d0b890120643c0803d5500c035001c4d54000d1503014910005100c56018100307600d00104050704010b500f554444c2041d455281c55000035907915a035074005000e000c1044003004081d20f48034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 509248911 1250 509247661 509247719
    0x10b1c0308130b07051b07080102092e030e030903120301090c02192d030e0a0e0906070807020705150c0609160e07032304290f09070f090204 62
    0x9190030b00781070f034000c0058090080c0040c842400a804502c441009642181626034050311000d020303001c2d6000c030b204030b4400e80c0c0e618190208042c00b48010014261810282517408030800409d40140c88104a0b4081a0105002c280501c2e1018002410b180400400841c1e82c0c0d81803400b40d900300c40c2c2d460000021035006005541c00103d60864801145401101446404003210f450b5040c0c20070080c040e0b961001344544e00d01c100742c1c101c541d640b00d03c44111001c40b0015103c03c128800d11104440d0340c034181e48a240410b429900840c2840c1d0804a0352043d034480a031100b010a603c1d2807032491945900000050060b0028414482c0d5038009103003802411550600c054100b666814038090340c500c6640714000301d408107000342d10050302d40da04607840c8015525415000034071034404490944040c0c0c904a15101d00c815607101d000082c540c0748a2100c015180c9041151a440c4003c105400e18410704401080703500c0d40b030f032140c4000d25211001580e203074102680850602552b485001c8441e000c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 509250161 1250 509248911 509248913
    0xf010b0a051c0c0602011b110c130e01021215040e0709020d140109151406040b03100902070b041406010e0c0d061502030c21030711010b1c030813 64
    0x31a80681100c104581140710419281c140040b0701c0201800100803420030300c0002001307a010740040c02d40829018503071943e480041d000761490355454814000c50b0b080b4883d4024289003441404a03075104c0480002040090b542403d402c992020392003040c5039440ea000c1203158440d09940d202d20040c1614148680c004400401d69a90524090b050f0440e40108000340c6a844551007903010075001182c00c14256510410300004004c400343c5a015090180804212605040030281031001e0261a1925081c9401c800e0685034002601400d05840103040000b580300c00d80c000383c030303031280100c46000540c20285403e504040303501108051035040f0a0040050751121401c1c503501038214001169901031445011004150a0f0410109003440307012040071180c1c000090400203c074001212402e200821800d03c140040d8500060042c10800000305a5032140b050344030084030003000800c000006d24001510804040002c0c103200400c1da44507824145c0c042d45442d0089100e240b000c4106901b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 509251411 1250 509250161 509250169
    0x180e100513090c080d0915230c1b060a052d0301051903051b0420130f03020a0501030c050f040b0d0b01030c020618100f0209090c04060e150d050a050403020f010b 71
    0x490301c2031105080c007c6441c1a076130343c011030642c0e45207100d50119a04007511881e6050f03660308000d000d044244a4120303036001d078001120b101c44510320020465410501d5482c030450340c0d5804030303c500b40c0284400c0140030b904d20f1302804401490307440301c0304544c5940c103020900c00145000d58082c4c009817125001040881c50206402d1406000d00c00d00d01c0b2030300c0560010070040c00309168240d51305141c00030344070200c444201c041c041c01c01650082108281c0daa103040c20b50220036000103548210410820805980a0341c480130f0342a00b079042090519101881c030780c103d0b8000754425000726800040c0300044428600c10070910140909080000c061040002551003400900180701486440801c0342c035100e0400001c1000c2350b0400302841010003580015010350040c20040e40070f090b010001c0746050740d20006840503950540d4920005040d454104160018414800b0000c0f41007000000c00301d188074001e051050040c514041041d0806150091901c1100c540d1030350720b40d160000f000c0c2c050795 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 509252661 1250 509251411 509251427
    0x60819052e05040602070b180d030c1e0314090a020f0105041217040503100603050601080607170c0d42060302030405010212070c1101180e100513090c080d 68
    0x750180307000034180c1c0c2e0b900c2c0010082c400c00d90302078250180c0300c0801108041c0d8000000c400c4400c80b0607210000403144060f42614070030b02400c0d0124491b20803080e600c2d07095841080800d65a4a004106081c01007566090a40140c0b210b19864112003156410f5050086000745002400e00c0c000c2c0c989441c04072081e55114a8500081c810b121441c2030208114501e4151800f410f0018142e0316104030140c590b6000b424140700441d00d40c060b400c0002801007020800d68030618a0f0f449000c42c0c610f0040c440c8401c200001e214925508081c40700e900c40800c0e9100300c4a0310407140c60035a400640350528a16a6504040003c1ca100b03d624405018455008035090455000f4140941c480d03c179440c100b40a8050100f038008101c40150411400716401411a10054050b030008c50051442c000119440e14a19000b40d4071461854001c00c070340210700c02160b600150000b101084143c1f1b800004600ca5103070880c20440070740701e940340342c284103400d049640205030310002003604540014014044032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 509253911 1250 509252661 509252743
    0x7060801050d020a03150e0c03032a0f0a0f030815060405040e03040302130203060913030801140d0204150f08070305060f0712050a0203150402090a05060a0306081905 73
    0x40665200804544510960102550303100c003003113003401e9207030131810000d0070b9805079242d523841003840b404400e0801204851070800c4104e0100302c0140203172802400030039142240102ca21520b100900038071000d20069000717070b1080b084500e00700e0660030020540000503000304081c1182c003d1000d0250366101c1240d0455800b9680407401d84131140a9500714015640040d404c0119800d600c41d0000c09039000307601c0344000f01c440301d050ba215100304404440e180b910040c00f01c0c48040042c070444c0e142d0496a20040c41c000d2124024208960208040d9904154011200f80385e1075014041804104245d0000c0e00c0c0c9039005050701861a01c8086d901c1c6400f40140340e0518101010a4050748141510698803849035014480ca0500a03040c3c402507200712420101c040b1401c00c4182d0a180600803a144c00c10000c14900950307080c40708002c002e600820072182419651070001591810030301501c140f0742a0030800f420354000030b00b0316904080710000f001803c040d1918000d051002d001d030035403021b8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 509255161 1250 509253911 509253919
    0x30b100e030a030f110318010f050a05040909080403150506030106060f170907050a03031706010903050a0b06031609091e0305040b0703030b1201020304060b1507021504030f030206090f0706080105 86
    0x44ca0350710003942c001100030b5050105001c00211250600c01070b4840d1400e042081c2c1e5801c48840c64018111428001d0004890000c5c204010070801c824568201a0419000c2c410051900c0e40d80c1c2d48080714010040d80c0c44140f41d44900400c0b030249400c0c492840100881c7c104240c076180e01c44d00051258078203004015540704031401140101804000c008041c020103403c10840644038200502505803511007241d4080400303000032059442014904200c0b0b501100500c46003816586000700244010311058052251100e40f900508149500b000101550000015031205038284101c03a1200300c0680f44018016103003410009602004527802c6030000c06a41e6268600c501d02100900800800c00f0380c0900001c01c4246000c80c103500540c000d5100300010821b031144c801c14407881010703c0c8034803c00c10b14284403010141c00d100e510504000544064103260940329607032882c00e00c018204c01d60042c1d210104000185204000640012000c034000b08411880d00318024001c1d17905001d2140a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 509256411 1250 509255161 509255177
    0x50604120203060a0b1c06060e010b0301090605010201111c15180e06091e16030c050f0d020906040209040204050603010608010602060c18330c07050126100312030b100e030a03 77
    0x103004523907002d6400b401004400240550751101000c081d41c00c02c1c02000351040c540f0a000819600501c16070500c0108043d0300c0d1704012003100341c242d1007010401510809503e45100b201402d40460605025085120000d0060f20040310040219580da48440d0313500c1c0c2c002014008140e0700043c1242c20030009a240445441d005041e031400d0221110503181090b01d000e0011042141c0ea6140e1400c4e62420b4400b0103204a1030420404000d0b0b4210010b074011441710701003161800d145d0003c090620001d040545420b81c0d4034007080c0340364003da12007000106400010f008260381440f1040d00f218030708410b00d04000301400300c26840c8408444562040c50800700b104021040850403a400503482d40b41809130b1410408012001e0740049040710301400b0369540440c103580100740142d01d90f2101c002c01040028a055204214280a04009180b03c0c450b01c000002615038210a900304c025a80d001c602e142407003050004200d078010000041c03003a01541c07002e15031400100404000e80616120b00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 509257661 1250 509256411 509256413
    0x6050312030a0b011b0303090308090c0a090f021e22080318040906050907080609070b0d05060102010209030a06061e030210031a0a0e10140d08090a050604120203060a0b1c 75
    0x32040364000c40001071100709a481c5c5c0030b140d01588401c0b026406521919180d80c1d805402948030101c0b8041c082d03000012903400e02c08444ad581c844c03888101e01c03480040ca000301d005004c44010420250300440d6120020b42a0030140355481e04103900342110030b4560001d41071803400c541724015008845080704a5900304080390342e45412075082e0a40003c0c04012604202120b561110110300440f01c1c03d1148030003141e0881c0c0009902c2d01214043d606035400c100c000c0100c140500030191159045640070311860240b907800f0700003503901d02d20a034400200245071651152203452300c01c07450740c40c0b913000c0c0b0020809600c5005450404000702c1c9030000d4030040140020707511083c1402d81c6030b040903484001040d442c801d01d60080c02042e00b0aa80d41c0402c0e5541c1d00c04403000c0c500b0302c500b81c101c0c3ca580665400228138001800c6403100c000e104640c01c1da204d20104515400c07a80c13000b1a00caa880c4000c40560a05006503a0004081c11081c040d419080021602d000400c42401c41f8200034110300c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 509258911 1250 509257661 509257667
    0x5040c170c0409140714010c0303090804030b190b01030c0503010b031b0310181a010c08040b03072c0f1512010303020a03021006050f0607050c150a0306050312030a0b01 74
    0xa072a1500400070802d1070081d00700403031a038a10310b4200d4942d208202c4080703803402000160b1059180141e58001c040055590100c000e002003080c01ca07000c00003840b0110002d203138816064403804540ca00c1822090380510000d0640f20b9081c0744a06041c80d00c02c66044180e44002140d040d582c034200001d070740e610b616481031445180c000b8080b0410101000340702103d4682142502200c0c4080b15001001c403105117650304030b5851010024002c0000317108000103500910701210740b94003e80d912814280e03907088100542d442110303164000303202041c1000b488491026001c04811149952344880ea00c4180450840071311082c0041c45030b9425519100b40418120846080c07400d010b04a038610b59407813034044d40d0780040b010100c015000e4036480c0c0c0a058150310a4104990b4000c00c40b100c01c60080341801450381c081e00b002d5440340a44001c0c800d141c0c4071102c1041c844c1580199003540c6401c10b000c000c045802d9908400e1081d08000c452000b156500c00640750031481c9c2000001d0384840003401a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 509260161 1250 509258911 509258923
    0x130e01080d0e120a03021b04060b0403020420030106031d0d322d03090d08070c02040e0c010f030216080d090b0a09060605090903030711072d0905040c17 67
    0x1880f44c8103d07002c1c1c008143d030214010758203d8a501d03404900d241c0346420002640c01c90f00601e640045d0903c0204003503d05900312011030046584420300487c0c0036070031542c0c3c40d4426000603010903110b141c0359680f403610350708c215000c0103020003800041d120360b1001861980e420780c20742d02050b02c6800720b4030101c40150710041d52454440c5065910404800030501215040e20b054055410007030b0511610410f082c1220b2180f50b00c07001801e0503c01200091765200e074050844810071881002d4900140c50b42c0c4145041c5a0700200184030b9160000c000410700c00385400c0e46005c145c014080020308071040750300092107170703403000703100d42c60b1301084625000414010001800c40c01c2210107001e01050340360310004940f4003402c403c2c4030464495041c0410203400b03940c03401d00c0c2e6004000003a440e40c828802c56500c1008103098401096942c00180111941a0b540409020703c11320307045100780d03813604c181006100c045c2e02072145180c2500c0f204284441da10412081404901069030b0a01041c084 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 509261411 1250 509260161 509260189
    0x2d060102032a070b1903050411120f063303150f0a180807020603100e2d0103080403020d0602040504060603091a190b150f130e01080d0e 60
    0x12046000c0412542070880300045405000180190707000464800050003c5659140e0990800d000176040000d00f10010b100050044c0c0d07000803181c211944a42d1040c896904035070100c0001d050136800882058244031000d8420201011440c00c6403c40c085541003101c0c50b880084080000c800074440402d003001202000c0c009900c40002c1000301842e6420303020b5008400d03800082040700001411407104440b80c207000780c04030009000000051902e03030000e5274001d070449a01c030000c5a0b24680303890400070a4900c4d0703034003080611506003668a02780c80010b0721070010780d48011951458840c090b41d48110300010b409440441c0030b034010300030303260106c80040802900801185a460384018005c0c00d03d000120303107040c8600614000b4543e1007240300c0c05560561003065580c0301e00c1c00301d9002801c41b4044503070442c01c0080d20000c1c02000b40b018156060320400003c0d13032400fa0940c0070b4485070132900b01d00c2c91044030400501419200203080d4a4944c02410b1149140d00501b00040b00b00d5400b0070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 509262661 1250 509261411 509261437
    0x40b0f010c05010906050406060e1b1b0f10020a030f1401060e031501030b0115080702061603090803040f020306070504030f0b060a05030a12080114010212090613080c092d06010203 79
    0x280000c00c00c0a81c080004c6a4120b0352b4140c098a48807000150305035604465a0041070600240410103480d5010400e05a0208219001342030728511080c00d1070042010040c3c01607010816142803034060144078407040000e10b003049107510382121100504418000c440401c91100d50b02d081903101000070310401d181c00f203210b1300190b0307503841e00c0c20a200c1c090240d46600519080306c03042c00c4c0c1c000c2e01010b004011a8001d000155101040e04c240003100303000240c01c15403902e42003008154600c00a500035400303030000155070303107107401414648a000381c43c1c0310401004010420201e031a441c4a8648544d004020140c281c944000140603100c00740c20059060040c0c800c0c034030410400301c0d240e425250303a50b01c4a0010380c5e640d00c0f030039a520004c2081240560003016081d42050546002085038230001410746060910f00100100418840e802600c0290f000000c0344801d450480d180da68171400c2d14044180c003c10300e01003103251441e0311007045075100f031420206d40389078000e200380c500e4400e0440b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 509263911 1250 509262661 509262671
    0xa03060510030804350d0c1506240504051c2609040606111009140303100608060a030807110312190315030203030f0a03060b040b0315040b0f010c05010906 68
    0x18500c1c0001041e41701c4540c211100d510040c054840d5440b140440c801d0042001e0081500ea4030b41c155403898440320119a1300014102001000c1554801c10020b0310b0ba004010410100302084200040b0407084540c05205062100b04419900c0369094000203544420250096410f480c203a070b50001440d01800b883c030150340345011a0052440038000203501107400780000d90361344000344c403d00c026038190310168001000d0f040c07074061315401007883c4d14490103410320301185039001035085030000c0d1180d2102075a001410069658070100720b5404c00d00868a808103989541c0d01c0c1e51080c45510b200500c0c1319115900c03008240d4050100c11b100c04820750516070303640304903103001801404059125020030302d0607070800305000c8640030034401e80b0b5024000b58a0f1404031180c01c0116000107011008040e121000070807260443c401400003003441d5100d00381c990a00c072207403c00e21107002c0b5200d03000c1d0b490090b43d8501c84d41c0707522242203000e1080c200050a18210b050241c0900380001002e03204500b01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 509265161 1250 509263911 509263919
    0x190602090607060c03050a060b031b160b010f080102040f05120c030618011a0334090204030303050138040308040f03030206070c03020a17040302030a0506090105150a03060510030804 80
    0x254000e81140c4c49556801c00c15035840305110300886d18140200c50b0200801c0c400124961900c8404585a00507407412500703202c0d280c0748407015450340b02d8080f1810f0b12050010880060f000094401400303140c4000e60525040c11f19468846410b0b102d00c1d4400d0f6a412000707803040b0014000501c140101901ba2040d0786048041104031000c41e400d200c0081d0b2034500d020f04d08002c16006082078900007000b40015a600c064441c40c034201d44102010340001d40d0203102400c003900400007000b818844009a103032403543c1030107022200142e1105400c00b80403403071010440340c981d00c0c01c1d466240820405007103800c200d04c3d074181405542c0004040710400a404186101080322202c1124401c1d421588290340f082c00c2141d001144210003000f680c0408840b0300024a19151904854028100541402e52b250002072401500d480c0664907500501e050041c100310a00900e40d000c1940900d0306070f11200300021910422041c4005401e00303907200b01041c4001a080003440007150082e0610780c5030368035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 509266411 1250 509265161 509265173
    0x18090a0c0807030b011208040509130507090905030a030f0e070b0403020406080d05070f0204021c151403120310031a1501080103080708030402010315090603050705030a05190602090607 81
    0x8918019291041409400115400001191030641e0340c400c4100042d44d203884400000605065812590444203120120303c3d501c50b0b8001d03070322941e141611030511786003030308205040c09840d4005404013418001c0c003a02040e0000f0071070391000350a14000510b0310f01c80005c80e0042c40c0711a4800107a00582e0b01c00a45450030b20060000e890080350304000e100d540b9104941d40c0d41045030118023003036040c400400410b1000b0a120842e0f40003510240c03411542e1542e840340d110002e001d8502c16a92445c1c0c118206c0c001c450010b020384900c0c804142e100303084000203130b6580ca040c07510a05050001001030100008640010b000310f911050b06450402d81880d144a18481101d4901e0386a5510119005561046d19400c1c1282e801001252404190751940401580001c005034181034985104201900d008c2c07101070f0061042c3c4100040060031840c1071b40c2003592540c0280e221360b010b03e140002180c00800c2c0c2d00340005403030070040c001c0030b150b1074601d0180c05078000583c1d02050100d00700003403000e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 509267661 1250 509266411 509266423
    0x80405060a0c02030d18232101090b01090e0c060936070807050a0c06050703090f080913091112100e03040e07020a05100f02040b1c0c0c120507021809 66
    0x85242403006d5032501c01d50f01d01e500380700e0f00c2d50388108404820742c8100d0a200307401801c0c00b00074105500b0f0302079098400c0d40c2036810404080b00c58241c40e800400c00080c0e184240c42900741d81070003800700c1c01000700c00106940500000c0c0c40c0f00380c44601024290ba030645200714401c440301d40398040040000d8507540816841102c204010401000024100d81d02c600d0031140b80c404681c4604002c0000c9480d02d00c01801d0041018041c56138603010a4041003003045e80180d150b104544030742d6250120000d1040c0102014025041d050401030050005400300064484081065440e010f111100c046990300c0c12440c4040c048046140840c00c4c10606004401401960794120b0b06d49941e44039041d0481c1c2c0e65030f460170082e1898000da10b0704210300b007039234001040311003031a8005030400c0c0d282d1343e1000b51584600805001014884540b01c82480745001d22004803030030382080f11025906883c0d0401400203c01410108a170010700b8030110340e0b48110010526443d44c41c81341c813500d040da0180303980745 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 509268911 1250 509267661 509267687
    0xf0c0c020f03210d050907030512031b130f080c090c1305150901020c09192a0206010513020408070623040608090709060614030603070e07020a1b03080405060a0c02030d 74
    0x145c24000040d100200c000b440404a80e88200208002d01d8000384414050b040a0031100208c0b145600074000741941d030001d042802604808440800e01d05081c41d018880a6407240000750030010245000365120807503141c1c03050303206050340d645130b05100c4500c09054080c5c101e40e50003c528020001c0407501c02c0041c01080301c081e0222186070b2020020070400d1181202c004501c0e106246d0126502c5204c0c0d001344582041c904240318024081c40030300f200c0340c8101c10032600140c4c001c00041080d450030003803081c21030203101d80442c03905080c18a140c1c0c0703c241d140101030511a103c070400113401a4801000074a403407a20f6010f45807502d03164000c0580317005480106042c42400720224203403401344240350485005417145419441407070700900080d00014420365060081c0400091220450f040403842401c03643d0140c50fa00c9400d10740070b4880320302072503130400110000c2418800107600c80210380581f84100c2e80c0e140c8460003038408440007030071440025054001d1004000c4103a4004020308000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 509270161 1250 509268911 509268937
    0x130905011e0b121302150f21270c0d080306010206071d0411130b0a081f030b060f0a080714010305100b07020a0e0709030201030f0c0c020f0321 63
    0x1c0d511400600240110220640402d0411021403030310b03040060b9030019588042d00c010b0300340000310141c1b00c054010b04d000300c0a4040c000303000e0809503248225500050918500801c4906000501d0182d03010499010103210b4146140707a103440303601b00011040c0d04070003082c210001d0348515002d101030b041038556502600c0b52102088140c1e0003020010601110281e114551250803c00c100180040c0070f01c2c980e00c0030b030410041c0c0c0e035001e00b0f000c4400507100d615038255403a5081030004040387c0c00103000b081650b81c0a514110042c0c1780900100403a5048491003a01e40c0b20403000803158600c0700c284681c000c48101000079910350200d410703021074a801c84c1201d00040124015800e40d20f0450740c0107400e01c80c1000501055005e6000303840403a0014264540207034440c49400c03c141c9090307950b0400314803001d004004640c4d250203081a00c1224160500802c1c640781c1025210015041c0d00038800c1c582c54031014510b890402012400044640481d0340e95540b12050206076402030b0110700d08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 509271411 1250 509270161 509270219
    0x1e150f12080a141621080a150801090b01140603070504060e0127081002090604030209130206180f0103020a021b010302090607060501140f030706030e0a060504081b190813090501 78
    0x20f02c000e10882811141707040d140d10074240e40307403206c0e41c004000d004501b10304154800d00c0030510240910171940a684210310518465040c2030420340803172200740e9003a12a400070020800420750200070349046a4103400c21032080c100d00c2005a03540046015004218004508941c40c0380c0d448802c0c1c201107070084c00903150794008101d07404040e0310907180002d0304040c08020400042c101910280e40c800c44268404088541c10360000d000f50f070081e41c210710511040030b8804d01030b141013450400c01c80001d0234214603158001c00040d440d800386801d100c0440e84000150111640aa01245e04281000705901d40d10034462034000300600e800e004247d80301d5010305604880f0704020250005403070005008000c81403410004030302070410412208018003600945400042250080d40d0246200d03d0920b80c440d05000f68192003011184004002e81d400748a8914a040f01c2856600c203141c0c0140b20b0564030a850325041d20068040d41c8024500e0b4908000000c210b070840d058103282d1840e0b0801001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 509272661 1250 509271411 509271443
    0x21120f02030903091905040501080604030305090616030b0f04020c010f0609020a0e19031a0402090f160e0d05060108070303140405030d030b041e150f12080a1416 71
    0x204900088941c85680d900c02c200d04940743c9042c0346011106103080c03803100842925a00450709465080e440800c00d170703000310180010503425004103a8040100340082c803491501c0b08143c0440b80d551002401890303074502c141c16039500c46411098028501070815540c504140f28414001c180307142100703103154904180422120241d008941d40d004d510313170b1001098000c140c20492a0401010340900d200404c400000002c0c02d610a01c805a80710301000403840d241034014014801001084904115144403c205071840c0c120b03c5040e40c04001c3c40d021501c2e101c40004242c0b480320750b40010b001c41c810381c000001c0c0b1150016840d801d0324426600c0305006000780e8980b0380b0342d00585c0982a4103400000e5566001440baa011591102000f00049141c01c07000781e407140e25000d44074443c121305456a68121000080010190082c00d040328805000b81c035087c82c41ca00e103102c415008000f8580003801d126958890343d00742d0410151149941d503614820002e803054043d00400407600c41c1c800b041085 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 509273911 1250 509272661 509272691
    0x310080a050319050706091511070b0c09010e030609010c0215010e070e01050712020d1103090616050708060c0c1002030705190513140a0806041208042112 68
    0x119281d40c404011070a080303280c0c961010520000f0400001c2150600c11000800c0c031500030b0341d8829026201405c01c080c90100080c5c00c0e580c00301c07600c1c2000740c010003c940c00100c40c4502c4642c4408030404294964034079a0040307903180401040c1c29414840c66050191901d0198000040c6c2645e80c0c0031201000601c00045403040400d100c1d851403024200000391a50b07006161024042205160061804da240d50740c000c1100c0118070b010005034080140b0690183d0028929495840042c0086007400d551400040c000c0c8510b500303c900803040590b10104005040081c0c1e0041c00041c01a50418039007034a42081b00d400c401b80c0e03429240710b80d0a11030070a80d214402c0380d00400095866602c0c007800b00740070a07000c0305129024820030004001000c0002e82000016015014514a0208400600c3c3c100031040c0555007010782c03250001428800001e03c541c50341140c081003820040865902c0d400c000d418010407000481c502c504078000b1041d5590300120092400f8114a410800207860000300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 509275161 1250 509273911 509273923
    0x70503030a180c0e07020a0804031a100503120915070b090c011d01080702100f0b01020f121b07030816031b030e060706060504020c330a020f07020312031008 69
    0x3034403901c038100c810301654141c1c0c1c45060f44401741d40102c03418000c09a17141840b40d40503a009481a01c1c402070f0341d03010541c0016203e0382002000c03907050907881c284400a500c074000030114014400740000c0d4070485840703120408100035600c00c40c0b1b90303d921450030840300900044401d0340440c000e04011044944c0901c540f40c001c0e01c0203840110715030008030b00549880c01c020301030300194440c01e1030710b4009030300a000706220b007602c8510200e004014000003a25204c4000c1c60034943d50000241204d0200401042d83c400b140880b4911080e81c1000c51418109511130b00013404942e80050b80002c41d9540c0c2c0ba00c04400e9100350b8410001c151035041488801140f03140c0100041c40058500400c2e15098003d031a0080c001d16000480c2e5070340e900040c041781c0c0702c00006c280d01d42014000c030017000c2403885004140c0801c03650f010065680380d2160022408018141c0d042240d000c01c01c04003400d14a800e8858040d40030301101c0c44007401204180d4643c00403941d00c6004151040c2c041f85041c4c001c102 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 509276411 1250 509275161 509275163
    0x7080105010e011a1c020d0603060c020f030705120f0d0507030501031a072c0315060103051e0a15080a0b0a050915040f0f021504092a08150402070503030a18 69
    0x4060170040d00a402d10070104181c0c0074076070416024010441d04003854400d480043d44103840000c0c2d509081400a42010700710503030105260014030005001c00c40200300c800c00b04404100c00750b030760701e0000a0072800d4040c07044220010303071030300c020003040f02d4066104038180c074003a202d0143c0d0004001c070700e0210080200d421324005031800001c02440c000542003040e4286103414582d44440081001c689890031140c01000741461003400d218855805201c0c00d90040c91401c56884281c0d01e207107101d2801200500003810450f82e03440344c0308442e4200300030280581080300a07141100e501f400c20100700c0d00143c0742041c8044c940004502050b00004104d400c00500c1510b00d221903869481e0380c0040307125030360b0558045e20000340c000010303034440011104004250842d01d48072030030403130300c0011501441003030403c0020700c06002614844201007040311a941d45000e100c6541c8405901d5800c03145010751a4001e80045081380401502001542c45a04112010002c056030000b80000300d12003840 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 509277661 1250 509276411 509276459
    0x20a050a080a06050411031509070c030c020307170115080f0a140708030307021606081e19050907171b0904030507020d0f050607021f150807080105010e01 68
    0x403548404030301035241541d114031444000600c441e580c0010a00b41c500f05407041e40050800400c0111141c3c142d01802c040c1c1000362204261464241c40203805c03680c4800000e014040044440c2d0f04542c1d0800207000070706100c050b00d07109602c540c0c3c0440d02a16039502e842020704014000824607071000960b030400b0301c8410008081c88081070b100c00d82003640050100c9040c0c0507421f40460b8003141040198001d0460b54028003200d0307048601e02240d80143d4121408020142c1e00f48460160760081e5000301c04c006a035031070305035164621031103181c0050f656098007441c1800108080301c03001084c0901241d004809440200340c0030070680d511384068010819400c81540c00c0c411060034100c441a40c8180310b41442c52400000303030001a602002000212100707040d600980041040034096150001d203540001c03d001c46101c5003000030040c05050504030f079503403190701c0101d03180c0b0303100743c030f801003999500713943c2d12070b40b10103185000c0c2100340181801d0004040c00060b035000c40301440e44c202450700e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 509278911 1250 509277661 509277667
    0x724020d081b09060a0810091407123b0606100e1c0602040311040504050d260c120705071a04020121271a10030f05011509020a05 57
    0x10041c4565042e004056080300c405208143d00b94691000030714107403085880311740e420b180901e104002080240c00054206052100310950b0140c00401680c005040341800002d54180000c1c40c4c004050b99640b00034410145621079004140485500c5102c114034007105200e03005050b40982e03607038810307500140c2003c902c0c070b0821042d0340b10700c2803414005002444585041c00c41d024090f00b1003e070030400c0da261030340001c040041004c41c0c0d151311302408082d1418003c40c82d15486042d01c070318444036044144080811000400c0d154241003908115640c0a030680c1828821051202a0058010301c00369111b00d101142e1000d000d01c0680300c100342d001803080f5040e2888040d1005807040503104a0503c6a070150b0480c054159403421406410704110014881c0341c2d000e20303c4034900c40441c41c44182c2c0c0401d190000861114440c0380c901c40c004c10311442c1035894440400c5d040d24004d50011303164450091b40752040203419004401b500c034078940014407098449101c402244205485c41c80410300c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 509280161 1250 509278911 509278921
    0x20030111130b0a030608031215010309020117060a080d030504022e0c05150109020d0b0f0a03020f030309090405030307170f0103060b0301110d060306230403200724020d08 75
    0x40b42c0201403d00300c81c40c010a1a80e41c8001d02885c0d6001003980c18881d110030340c200001e030003003961b0114969000b440e0a1000f41002e400183c40c4200d0304160040082d0a0f500290440c5c9420800000030210802140c2c0d40e0410240001c00400b010740d01244a11902110807815000c221102c4a0300307a1301280000b107803980b140c030585c0c410240443c122402d01030030f8001c180380080040c0f80360003450500030259039920102014030032200350703c041501c43d4030001101000c0e0348602f650380013600e0381541d04180b101140360002c2d18600429030301a611000c80001c01c403c0103c0400554000c3c41e00d600c0da03203801c900c0c141200c8094030044904040b40000c8100400126110f504000340310301c000f90000914102d41031081072554420610000541e484000400800090b0310030040d01407070b032a010704990241407202004495010704040c0420500c541424485640071594940311400c46045034107550b40c929800308070b8259501d00d20002800074026580103800404c41c0060070909585010003070303403a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 509281411 1250 509280161 509280179
    0x406060905061809102402060a091a0103080702100512130f15230405030a3c0f0302090a03060e0a02190806060a03050c0105090d2003011113 62
    0x180000c5002c1c2c41d10400d04030340340d01d1300c41d110703800350440241d031001150a042c2880b55a444502d08414007100e141c000000d16580803c1440d04586140000301e02038415080c4132152001d0107051544049581c000007080149103001460b14504c2a1100381d088403682d0300903149801149411108408940b00140400c83c102c503d00d2191803003a07180c0702d03107101f4540701e824205043d007141c0000e01303664440340a00307000c4408010903511031103146035690340303000d94415880e40248080202400022070680e13041c41c0080042c83c10b6441803120344080b00e0001a50324003160b085105900109204407041d4481c0d07440f81c001ca52810340b003e009031b900d0750b145130303035110041a40803100843c6008544000340169281104005144d400c85021600c903401e0103003440c00d000c00a031403c0d219400c44441000020b0700840c411003115070901305140c0354201c120204000110b0140c009002c1c8200f07894906c0f1070813034181d05180400058008200001080e807011225101b2200804681c5a05000400040d65 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 509282661 1250 509281411 509281417
    0x503130602130305010911041a0d0b0411091e0105040603081c180516080d0903080f130b0c060c04080c04050915092506050405100207240e040606090506 67
    0x600c0e12400b00c0c1c8070b0741d945410782154021482114441c400711111441ea1a141c0580a54551440301c820460b8915100040c040c10100d1002801d44086c0d81c002020b002c07407140301c942d00d10009041c1003083c0ca400a4210b10382e03007103060204035900102c000824541131500c81c0c141500c1d4040ba605141580004282850300d00031726944240c02c2d01c13007148181090000d00444a030500c60b20040010f52807540f815040795050b6044411310b41d101a800d101d05c558480320390340071039030441101030307035041e409100c03130914807a810300407801c40303901c0c200000e040c02c2410040003003009140680e0300316160100c200819114078810303510b1a5014840c944142c0c42c0c00d900c0240c125080408403078050a0421000914200450303402241d60085d2943e080d01c14500700480203064201030460100e5420704030050028010740c00780502840d02d520162032500c3c000c200c040041c00d060130b0000312031840340d01c48134902600325500130001000d2000307030010780c10725000c0c940954205480b0b0f92503483c20441406910b0b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 509283911 1250 509282661 509282677
    0x905103b0a1b03150e0a120905100804060e0f0706030f02070b0f06100305090d260907050a0506211e1006080609042301090c0e090d0503130602 63
    0x1c00384018070400101c203400600c0b5000e80c00740412904602c0c41c2002d41e00d0700403d5204004290410034540782c03036030000ca10154038035481a1080d140c07062100b42154009101e800454102019a148510345a00020290302c00c9119240500103c2200440d00382ca4446e15180d60303116a019060502849001e508440580640c07080b00604090076905c1d0803842e58000d89040c084002c000041c0306890a2680d0328013a144030504080c401c500b80b00c9000c070313514100f12140404008810602c045048103223050800413028081c1c00c0c0d0140c0c208100d038203444003514030500c0d10840c1c59120010703181c20b03c0000d80d002d090052210903203c8000c45007240151500034440e4000030349010994969101005080c0e00074008200035900090130010041c18074440584080d00c1910319a0400002484406044200804190f0340d45580007514400324090300100380c000302400780023030010840380341c0c10319403a00c03032092241223a894000c0f01c00281c0b161712083d2a8441007200321920344002c201079030003d209030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 509285161 1250 509283911 509283913
    0xc0901030b09010f1107020a0e072a05030a0806040b0a0803030a020c010b060a020d0206011706071101020c010e15060a0305060c0f09091e10060f0c150905103b 70
    0x688000d110641243c0c51a001c2c4c210001012880c401941008c696010242c840c01e9802030150414a4000d060040410341082e103041a9900c880d440500640117104060b900800700c0303488200c001005000d00710210f890074026072405001040130300d0160281c0c4100e8171414061032441d02c40c219030310042d50064070100115034032018414801e4480e20000c014031049503010b420b484d480c080300242021410781c401d00c1900b060072070100740ca40000c6041e1740c000425080c89c006200c80412810f019008611904140707500c0c02200081013080400c4400d991100320380c004003a0303500d101c10820002c0460001610503400702c800a130302c500000004128003c40504a103003030a10302d4001800c1700c54100c482d4004c80703012608101c0c00c103803103088040d003003941c800072800503504101c0020142d0280b002d8240c1080191803198082c400000d00038645c14808100a014031412410031903903d8190140f1290914640011450031414a2090103014520352400924040d000455558100d240c2a104407403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 509286411 1250 509285161 509285171
    0x3010f0516050702030a1a010801060e01061b032304030b0a0908090114070602030c0901030e07180b1201050f180106211a1f0905010b0304030302130306091a090c0901030b0901 77
    0x45030a400c2e080c4601101c0088640180d030600e541c276401c0d80c2480e40010088506100140003240d00040003038038402d100d68082c00c05c07680c54101200d441e210844d40804168080b071030b4107003400c04400100182c9010f00300c181015100c0c5014030040310300e101405069440d007888400040d40c07103402c11501c903144c000b8100c1d040c580280c5511041f41d000380c41032581c1c003000050640c503550700350042046181210000d401041d161400c1c100814041c081e2a01d051a620a5892aa03644030342c0c1c081c01c184600300c003c0003075140001902c2c105d1300b01030303c0104503800c0741c80035810784840502841c2d054911864251007000b00000f84e80b00c03410a149012110001d03040c25020901c0e80c1100001c0c840c401c0181c562410f45144041440040302e03035000284001c0c10100140324000510b81100c1c0c100c1d906140059581c05810060302c450422600300800c8903050a40000500071403034000c990010f0706500880854980b1240250b844c0960b040803038000141c0c60040000c2141583c6086e4400d80250012607 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 509287661 1250 509286411 509286413
    0x503010e0f07050c010e010207060c0c020a0e0703020c01020c0106030302070512030f180d032a0b0f0903070c030b04030e0904021309030905151209060603190215040b0903010f0516050702030a 84
    0xc25580c035107a07465942c7c1e501103100c10900a890142100d14405800c1a030000070036900421030901140c0604c81d4281c142d040802c0f0040e110758101c0f44400c4a00e07000315240c04904c00183e02030400c0b88420b600601c2001c10225180c94100c4284965500c1d1400030742c076000c880100d0000c1c5421514004070f4108210055070381580701c140d9210103541c0700781c1d11400003100342c40b0301c0000110540244049105030303040410008000c2071105410100c2c030614540e60303070b032214003617861889003000c0200a441c40d41400020031115260f958041c074801c2d120140420f400380d091010312141240c020b0341c0070018403020440c4828950081c1090350003481d140d078a042d01c0d8800724460840c40e10140d1400f0100060600058800e03051051b0400c4800c4041c10450070070f00c0000c0c3d0f64032030b0b4400040c4e0031000759524108550312441c5601074896440e28131a104d0745d6806401d40b094011960650103942800040042000d02c2c1c8103c901c2800340f80d90881c00202e11840488694000020403038061003540940d02c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 509288911 1250 509287661 509287663
    0xf03031107081e0c0307021216030311010b04020f0f13080304141c02031c05040e16020c24070503070f110a0609063c021c0503010e0f07050c 62
    0x4086401402116940c000580f0124040310501c003280300070700402c1c00407114051000c400c6407145501180c03600f0708401c400d0707a03007403d0100b659001310300c0385c00600000082503004610054071180950003000454100801c0c8001d03071280010070110640104807040c00001381c80701070440319502c4030407403881c1600d444111389154420740050b2521000003114243c40c0c9070803c0920307000c019040c40d407210090143d0100fa516018a0a00340d0039a003950084c0500d10302c00c90664008100d00142c030419030800074040071442401403280300c014010b860180b40340341448a85920642c49660340048640d06120003543c0343c4d00100341c106c0f841c0c00100201c50109061541c007820007801422685a0440001c0400480c10382e107500c48130500c2031300003040041030342081d52207260000000340860308006807001000e42008006800004400c08094800325a6000500c1d100444500c40c0d2415100031090313041e25940006d2040307a01c00c0c10795100040a1280c15010385030446001d0030f0a6003000906e044207 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 509290161 1250 509288911 509288917
    0x9040c09080c15070204020702011107120b0901090b07140409060803180d0302152205060901051053150408030609061c0c0305010c0302040501020304030f030311 71
    0x40000c032545410701026400b0701000e69400e5085401524100003e020800360b0b01903040003038410741e40810040c040d64003810300541c0b84001c14003658180e40c2c5480308100300300c1720306005907100c136500000501c940304148142d80e072481e0000166a010313502d8076000c44903803d40c841c1d030782e50f5801c0a100000d14180940a0f03100a0480080550703113500604415403100703000c10b0380d0035200d040b40c0440f00000c42c1d0040b6005005a0840c081003406540d152009200614030a0750350104401d442596000d014012480b14000c00c852402031105440c1c20000d1f980320700082c0240c0e0505502520400b00b0290200611b1040e420041080c800603014055078514240240ca034202602d002d86803e14503d070740c2481004e92800a89400c0c042c14101030326584a5800014010fa005102c17080114610b030b99404d12800e00c0222091080c80c0701c194603d0822030521142c401114150308150f85001c0c006e029000380c1b4251141a40158100307440c6481c1c42c46241001caa0950506a8403280840708130310060003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 509291411 1250 509290161 509290181
    0x21e0111030d061502160312030b0d120e0103020301051005090a1a0a11061306050619140117070e131b210606091202060f1305010206010e090a1202030904 68
    0x10001d5401c0c40c4c004905002020114900219084040f8440394015401e00020036241c0050300214801034400054004200c02581d042d8084070034409541003103154400c0d4201d00c00319998064507844900019002e80c0801e000b005da0040d12300c104190300900c60000341c1000100100341340300321070f910140c400d00350810710ba0344031a1f110005140201c00e50449561000c2d43c0035040101700310301d00910700c4141d00a0041c401402d041d110804111503030348840b0074207902d203031034521501001c0c1c0c0c480b0580701c0059a80110382c08125241c16084200e1445030a040c801c0f2a9600c40032009c0d9595800c000b091403200c05c3c0c1c0303050144e413aa11a002ca410038460510310142d0380d1202d40ea04828200740b100e1081c440080144040e04090052080700c2d0701c15103a00c02c5540705c050080450160b03100040c40380c015000b4441c032240c00815140a005840003803001240d500703800303a44d8181d0b00d030102801c02e0070040300d0602c225840342002c01c0c0055513030080010000d2140c410789007048032020018040c0c4d00b55900c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 509292661 1250 509291411 509291437
    0x3020106030b070c0b010605070f050d0f090e06090c0c07030b0103051e01020307021f0b091003062009060a0e0907020601080c041a0405070e1507031407021e011103 72
    0x100a104011402c2e09090b040801400c1c2054060b03d9551074100c4420140245410040d0121b001e20400c03010856014000e507005096804803011514018150318104440c80c1c00039100c842c000504a0954912600031070010b803640c42956101303d82e810041d8003d4850710071900c102030002000c00c41c00c014040c040c6101c0d80207003460340c1c0d00c1c200314081f9247c1403c0c00c444592040092001d165000205143c980d101c500041e001031509004074402044481c14031500007207408100b01d1089031714501c62007a24450181007001c90240a100000c001c0007181d1a03070260400c211540d600e2400703102070011f8a410340b600400c14000300f000b054180000b07680c60300140e8003020050041c1c00007406030f00c0701004190380420541e86a8400e011000c03d0101c440d48c0a9950341011880140c491083c0101d145000740040b107505281d4581414039174415001500003a12901d40ca079080204142120b0300f40313400030040103100000c07903d00c881e00d4601c100807605003c04c081e100303192044284003425802030000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 509293911 1250 509292661 509292671
    0x23060f0417060105041401060f12020d14010911130b0c0c04060303080f0f0c0d240305030a080c070c052e03090b100803030f0c1312020f04050c030c0a170103030201 72
    0x13020711056030981c4500f055101e03413a100611000c1d501c1850a041b920745440e0920803405031001c000d000744940f02c0b0350038005007010208402c01035241146412540d0100c0308012811100303048080d14080c524104080c0b00b9035540c1000301007400e4001d007500c421801c8c05c0e1210b40c0e414600040032a06568400c401081d0404200066030a2a41c003c0d54416035510b0147c00d986403d02c01c013903141c45203c0c000f041c0b00d039445a4204940545e1040c490103503c090b80c1506003a40c0300d003002c42c5d4940010740d918000580b51000180d40003921700070f491507550700507901c4070518100000c1126481402401c20140aa510081e000d902e0511030848040b400c0c45e1000129074109007081c10003c1c0e8000c083c03a1101d0a41d50003041044400011aa40031311000589072803a20390310081052441030701810f82c1d40d0710142c6000714442d0700300311a0b000494030807550056008040380c14041035590803600941c00c040c3c28000151a60211030003460302000920f40004140030003a1500c0710400c0a800c06c1d00140c0d911 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 509295161 1250 509293911 509293919
    0xd0609031e020c011419051902011512060b030109032304080a12090e0a1a10020703170412050d0e0306091c05040513050702060123060f04170601 64
    0x20500c000400d154281c4205040d088070840079541d02da12a40030340c1040042844265044408016201629907080401000b84c95280000304940c120808050041201294140255005200d507400b10110030b501000c00c5850170005805d04141702506540a586a030180b0026940c2880f8880c0e003a4843d854040149900303101111010303860569011000400300001d200002c000291036520707961101c1900a8100007140480c0c401c5160f500166405070803034180074411020b50003900c10071120b0f4034081508a00700e410400c00300451040070000d44c102c1c05c0c040c0003042c21900c0c8001c41c2d078024030546152507501d0620402040310380314240d88030340145000c4c0100a81c8030b0314034a0490021401420300d402d100c0c11490b00ca1041000d1041444c485401101055008074261802030000a000030341c00d10407070301003802424040714210010f004000001c1003001d494580c1c2c03030820078180070800081c42d00a050000c0b41e405020618014001840009414a40441142c9100d42640c2c0640125454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 509296411 1250 509295161 509295167
    0x4031208041e020303030606160b070c050c0d0b180106080f07090606050702011d01170a05040203010e06010602120d020409020c030406031107020603060d0f0209150f0a0b030f150d060903 82
    0x4840c1ca5241d40b00c201c81d1a0401607a00041540d400407411075038250380e4611100c0c00801108400002010382d1100c10810942e0380c0c1043d900c0c0d0081d40a00c05444040403400104100d66007400d800610703115042c800f02c1e2000c51402840000c110415000044007612a041c446c80c001c840510152554032202c0c06118401d900e0141f400240302c2400c00da81480038990000e80111070504081340c0c039a20707080580e85141c1c800e00070311407d044080070710300d56402d1640180010340400c440036030082d0b003014646c090341400019028102e030519030180c01c03210040000c1200c203501000349100e50075000d010109841109100525501854000541d5640d01c0c160000d4151000030080303d00307070841841500d01680b6a50101d030350200b0220341000d4041d81e2480c0441d4046080305002c0d412902200170000d10b25824511410030038000c54504079210702010070005886a680102c006011082c000b10b02da48008002a80d004150000040c1081080b24082040321685401c10f503101d0ba07c9100c61010b040e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 509297661 1250 509296411 509296433
    0x40e0111090312190c06060e0109020c0f07060e011d1002031e0a0504030b0402040f0f0209030f0a110d02010c05010e0d11031912021c270f170403120804 67
    0x143c00241420250600900012104880d9006018032100007904210243d4801005885c12034441d030081e50315140d0b1080250402040c0382c41e02d1058442d074040c8030900050341402c03070300c860b6955600035065100443d00d01461350203200083d0290a07150b00c580ea80c3c0f5042c0a0f095049500a685507034040110710744804681c0311000f40c42008114041d685948041210243c1e0381001801c2c04035221440418020b0101311094060326242105501e61041103400410005004038100e410000070000400d44420380e4200050800311140094185406c040f00c5045c1c04a0050500100706849503c5850071354105080b80301498018103d4030001e5038004078064076281c81c0800950403d000e900d540382101d150280c1c82800c0c81100340102501844a804449140300d900900b0080000382d01841d201410080485840011400c0458031103001700c07a0441c541c443c1c006040148414603521400c4621078650403040000d0010007010001c60481030702c60b60020300507541d414840c0380c513003880440f4038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 509298911 1250 509297661 509297683
    0x201080f040506160e12160b16170c1c0311030105060a031508030a09030528060c02011b020d0206090d1d1f090f32040e01110903 57
    0x10400018080858000103c00d648803003180095030f01d81c5160001a5040320001c42120b42c001d4150442c40301030040820040c0c04022501043d0f08003580390f49030604540140c2d0519500104041d821002051001000e80080301e003000006242040031010300d13042c050011020f030b140362080e54100719916414801d821080d59020705c514110750401000a07240d120351800c0a0425840d845d004504406c1d00303800000900c40003040303035516019481c020300700306007500c019107460040012282c80403a2416104207151014001c0703410507903059503510018038880a5aa086650f1102c03000090250410b0740007600d0407a03001482c1844080f40c00038a0000d000b8400000d64000b41c22500f01260414004659810f000c0c04800ca940340704070204d022811011409085c080f9032141c80802a42c11124507001d40350f000301101a40c80c1c4581d00c0303899588000394000d0b031440c5080848000208004102440c10034000c02c04155041100c1a8900b543c03081e2120607940d40b00029080520302d010400b60f000c803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 509300161 1250 509298911 509298931
    0x212010807050103200a030e03040f0e01140d0b0a02071e0b15030c0d03050906030103030327020303090904060e0708010c17090a240e16050108040213021303080408030304020108 78
    0xb840c0305d03004c0500d040c0e40c81c114405081011902441d0309001c0e82255050b0f1000d00120707622035607902d804480f685660f100c0c1d0180c00c0c200710004142102d5100494840c030b0f00207400d80d051070b041680c45902480c8010901d43c6030542c00e11410000400040c013440042004001d8601304108504154049500103000348544010309801200036071001304859107210030032100001d4120582c14207682c5407044142e081c1d4403030b030000004000c040c4c041d800411002203545201e4050010601500b03885440610003a605900600a0a8241ca0454407040d801842808080780d80240c24000d40d244c11140d0300101100d075181c142c051074060b44001c464490014491541c48036040a12042d500e0f4012204007600f512a0100340d5140610240307405c00300110540c10070483c0d01001c95030542c80d00c503141c1c140b19131200e1004000401b90b02c10034a0b10b014540080418030410f0302420a94003c0d4424401d00c502150700317200000c0450f95140c054402810050045d40d07991800d40700040400000034005046 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 509301411 1250 509300161 509300171
    0xa110d21020909220609060516080108070e0a0b1c020f0a030b0f0c0f04030b01051c030e0103090302010e03040305060f01050301090b040b040c0e07020307060c02280c090212010807050103 82
    0x8166100c660f0300e40c0095404041010100b141c144200d0403504440b8003612440c2405900f80070400a50f00c034922405ca0740354501585040c0301c00c00c5801c51401e101e0000781e94888a0305000c032000d9a20204d4000e4040e000000e000341440000c10150301c015040d030031003062110401000d50812a00380b11085808856081c203590855503000109903001e0320b052140d5405000144098103030804a40e03041d25070040349506d80d580ca180c0218910403d001d85402035020039a07071140705100070456000d65601d034868800103881c2c9401100240400c041c2582150340380c410020001c001400104003460080c030103031080b481d004811105010b4181c0c07042c0d01aa240c0752100c40401e40c02c05006400a038400744250558403182856058104981c204d421603400c0c0e071052003c0160000010101c140c4280710510210700e0828042c0e80329802042d075001d10980c000e07503031a0600c1a01c1c283c1c645280c450162207142a032219081012a003080e02e41d15030081c0e060006214070340301085000010042441c003409 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 509302661 1250 509301411 509301427
    0x3030907080601080d031107020603130302010c0806100c03141c060b040305060106050d0b090703020301150c41060718050a09020c0a051c0e01020c06040b0a110d2102 73
    0x5564004d1145050415699450800d43d4030f99000842d023601e50020102c503203c0c10421820040b078002000110301541c03a02d10090141e500800b846407041d0001030040c40c0e0010b031440d054a40c110044c10071410003d407050318204104654010b0140f0011b03502209a02034000180001200d60341d801030380d10700009000420020320006011410345078a45002d6840f203843d0319454002d020710f80c0a00d03a0010b00d460403c01c4e0780c1d0b4540c3c0918100c5484c44560b402c44e51500300b00792a90425100c010b0100c49400c0624032295445011000e038004000c00c119a00604880302040d003004440303260b9000e50020400d00408a0f0f0000222139100442c100c0d10304c1b00c0e4a40000910420228801c94461031307000710f031041100b0014032824000f15080f205440d0310b00440c1c5440c564036071b5040e9009006ca5451100c1c10019480064034042c05a40602998a05814107090b00500e4001b4004841004109a4003808a0b1003e100500b100c0380030740c86811082420700f20809161000c203090208040c41444010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 509303911 1250 509302661 509302663
    0x9101704081b030304260f040303030c1b1a130807060e061f06030504020609030a050a021318080702121501180c020303040f060e01092001050a270510020303090708060108 75
    0x43e29140b06c1c0b019070030000c1181030108180c2d010700305003245200c0c1d0100d000018150160400110b1071806e0340d5941159024143c12441d191040c43d01401d0100c0604500c08080f40e1211040d80200c40b01c540243c2c241c0c415620005680d00800c000c9803a25207130348440b003018104015154022000740e9a01407407000c0c00f42e1001216030284604010140c40b04d000c102551600021110424009001c2d101c0b0b0010900b03045c3d5546620701801c038010000700342d4021198425228510040e98580c01d4440010040d8a8925682d000b41006a038803118042d52806580d008000034900004615406040fa40c540503403d1000245c0080d800b469500f000c07410207280f03601000b00e0764007903400060b11144898a051050050005441c5d000c80c03903180003800024004860380155031b180d00f40c0400400600c14200445450040040e00004659210b0405100c0740240404420701046500c01d861010740d11030001c0c50420594180c0400360b0000424840048820b00562000c0c001c2d00c0010041c651501143c5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 509305161 1250 509303911 509303933
    0x2010b030316081c0b0f030c01020304052101060e0403120203010501140d14010b091908060711010b06030703091b06230904090c0e0109090809101704081b030304 71
    0x241d8582440307041c0707002c00c00210a0540381003449250144100c0c00c0819180390041000b00f000074480c100d8400951540d190010341e0311f065540c1079002d1800c09181409100048411400e0440079a05034401c07114004c4c4240f25510080c1189440d444d601d00307190401404034210841c0f081c0815004200600c060390b0040e0f008810440082c8601b039442c0c0c1c04103503071402403c00a411f208407982850000403244050030107408010030848050b20038604650440f802541148035550190b0840b0000440c0c2500609040e0f241c0329804001094846105002038610307403040713034140d004c640d03240e0303510081c440121350000392b4900900c0503841c001c2c1401d1015003420000e07210800f4a03041d1000805150135140140c030700c4a90082c00901c115045172411a4404d0342e02c0c020381c4003543c2c0180c0002440b081500a01c55080d070095800c900d0244803005024481402a0500c0103014403d0621082044a060f10030321403400307480d01544500142864502900c0c040015a100303520600500010039002100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 509306411 1250 509305161 509305177
    0x3080f19080f0c09180406050702070b0301030c0528060c0308160c1502070b0108060a0e03040f090f09051e0d020d0e0904030e0d030203030f06041a0d0c0b0408010e0d02010b0303 78
    0x1525103441c040c100090b07400300502c203030380d1817600060140000c02030940c20443c003e400361b4007078036440c0d5201d007034449090000344000707010128141000c006900f045510204294804003040048400d1403642520101403035001c00c000400c509400e40516034480280703901700d000300039401483c2014150013081e00010440144c03c01b2504603544955945a904032840c1d035600444019007580d460003456250318003120b0101e641d50400004c00f001c80f101104480c16200360300031091300c9c071717092030140070007010300d00d10a0300d13610350761011760000c80c508020b84240c5081e84025140c2200709995910304010b407040d1448155881440c0d88007200781c000394000f42800c0251904c1189550b50704048070489005117610b0381000c1c0e1020050103056020004601c91a4110b10b050720a0300c4400c18081144c8100c1c80d44400b001c2500e0141e4054603103d00320f4a42c09009240c0f090070251038080c0545c2c00d6000e40c0c00400d0030f039528286000500020f1101044101450000304914803045010139101d11400d10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 509307661 1250 509306411 509306431
    0xc0b0420030f0604060c050a020d05070804030c24020102210603240403272918130c05030c1e0f0a020615210703080f19080f 55
    0x180169108440d1900d00c185140c00408a802100e805001940c640c202a02c040d117200c1d0901c0343d08100180120300b241c00001403036008026030000000304680c1600701c0042100c44e04002c1000001007a80c08252002505500b800c10751a006441000000254016114810f590042c4a820303000380305004050b01816141c4145403483d612480001c3c103288400c803010794011044e40e2564180541c14003458810ad1113619810000c101d40600c01484003495140303c0619140e8840a1003030000c150858000814484842c00440c0c41060400302160041080c550101c00400f4106510313190820b4540100c16030001e0820101c052400c0080151000030030310259244001440120054a41d4214502e8048801000d40390b01e440070b0a003181d640110348241c014402c00001c40d85040841c0030b8484841402820024071031005160345007581c3c039141c2412410f010300d641c0040459401c0c00200080c40845403000d0780e4001c140c2c007095081001c046540104890b802c10080c414800da91041e80114043c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 509308911 1250 509307661 509307683
    0x1a011106160c0218130b0901050112060e0a02100e180f0a020a11010204060e090603011803080a06050d0b0405120711010507020402160b0f0a1e0e0c0a23010c0b04 71
    0xc00440c5050031403c54083c85102113600b00841540018005d141c03051203030f218045580c0750b0300303952070a9401c01e00900310700440c81d16071403000178810f0b0f0004400103a0700342900c000004a8000500c20070003a141440402e07891202003507240341004000c0504e0300780000820700c0741004510903400c420020050b180d09640050585a95030058032062140e01c0b121009658654503004002c040781304400f4014000d16102020880602d0306024180c2110000a10901c03280d2480c0c90842d41085e000d0712040c200382da40c08000c142c648506030b02c158000d000c1e500c4e1480c02d0070649845445c190011102c0700890314284038410004030a490040c040307410910380f0a0f200e034401e0001400910503134940c4101c06441c00c0c001c00130040d42d504400d100f054682c400034a16a296034800003030f5400c00d180594034005018000210003a2540041d071b055180c1d200300e40740c4041440204192000f941c002c48a00a440c82e49144040c07540c8501c00c607512001e00c0d02098080b12684c4500130b158002d84010100c074101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 509310161 1250 509308911 509308913
    0x8040f020307080714030118051b04060b0a021c020c060a0f05040b21010609051c05070e090a210507030f0c0c1707090608030403140f011a011106160c 66
    0x801c0840050311032201610082980c0e18800720842e03003000f0011303010b5424035070b1150030100c2c1d030b1013882303811134008001e45003010005410208034241c640c05036074030540c0c8a40100c1c880240401400b81d0070340755001000c03a28039100c910b01d040c3c008500307803030115841554486d1080e103d48055400d0100e03181004944a00a84001d031007a0240d038002a800c01310201c1c00d21601c91110304010040b8150884400c039690b01d0781000c545031031441c0103007508100190174000050001002200c8060f00440c15503407120740b19000c20b26000b60a6692005a902c510408070902c401c0744110100d003d08030390100da6552986c0c0c0050840e02513140081c0038411086521201b00d0b009019001c07880c3e0740302c502c2030300322034487d1f44080c007080c02c2c3c18418105203c0c81c0c10110b210501031103460160b0b41804011402d041c40d42d5a0301403036840d480c0b00407140d405640c4250249903424001c503011a4203910306528807500e224001000c0c510007050243c840e5001da02482030643d4980f04d120000d2205140c072070a50401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 509311411 1250 509310161 509310163
    0x60f0403020d1104110301051906020c1e2e1d28030302030a02010b011d06090109030f08280c061a03030f03010905061906030513060e150a0c08040f0203 67
    0x1004100fa4106040c10100310202c00a500110b040c0c8004031941d032a1144402080440ca138071030b005940150703004400c0560300349042c0b0608c20394151030180601c0e0f180400000702301d440c0007901e45035414406c00350b2040c0e011101b1a903445054483d52402d45c07403c4507408041c02e032902d20303180c010b405031211185d40082c8450442c4c850192043d281c07030b050b003030542e6407400039540d500c0800b00c000107520381003048030558801c50512103241d041c180d0100c41c0c10311003810400c00346d004400303840c140890180008001032042d21483c001c507000d003481988074440140c40e280303603220425070410f941c81444d03203a6070f90641043d040d07000c00d5004a170000303000310b00400251551061041c02645840081600c203440300801c0300035816205040b0080c00f2a403684014031440c1416131450046404038104c0c24040b8510a038410366021800e60030300c44110895032200360448100d0429085141c000b0005c51000c09039203104560065404241000300030701c1104020066200900005c1581d40c4c241c10401c00e5640c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 509312661 1250 509311411 509311433
    0x203070f060f0207080c06090106050d05060402060c030909100302040615050715180f140d0c03050a020c0a03060b040c110a020f03010b0301150312080f06040903020f0609011a060f0403020d 83
    0x343c000c07409a0f81302070a414503586c41f2400c89075100158242840840c041c20112201e0501355404402401c99455581c2002080c0c1c200d03540e21600382c4000e04c0700a251b9600e8001442c090070703540f41040b0466003180188015546140c110035401d041804000c2c621641c400300b01c45030685c10407070380d080240c80283d104001d840180b1440c0c0d9401821455407040c4460122403110071031190304032080c0c4190880d03410f43c031200c0300800c00c000300b41202a00c1022034001c1004100300c41140c4103a5054658547c00240350804941082d030344a5910301140880341094400c001c0d07841c906040641c1703a01c400c01003141ea00e0451010003070003840300307940810803914250090103008c507004000f0b000060b11003984640d809602c0c0310544071220b48540c1ca1030740c0d074050140c00d40504201400300700240e42d04070a0102401c0483c1045007148145218100003403400d001e81402510f040001040c0d4a410023017111046030400b2074148944002c009120582c15840111000c880c0d05941080d2600c86a06046000c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 509313911 1250 509312661 509312663
    0xa03090318140405010801140c03090708060a0f0b0406030213181406041505060108060d0f0204090308010f0f051008131509020414060d02010e031623010203070f060f0207 75
    0x1100e000400c1c2c0c0c0600461001c610b403000d540c20009607a030340c000c250070b917030520220b44002c1e103000b030102e10f1f1424182c0082d030780082c00400300e07540d45a403016250320b00203040380e0b44150203982d5220303584c884201d80204100c60fa01201c05200d81ca09640018000d07801440c3c2c811840c5544128400800307804d41d10710b1382c4168200a00c0d0f000d400c800c0724039548868084408464422402640340c135446100c2c42802d025000603540c3c10029642c0310300b40801204810020b580c040a003000790401691203004407501c076442039491000300c0d403420140e0f00c00400542c015482030340018006005a4403030000c2d1009004142c6000006c0b52a450039212040030240310142500149040d400c40400309500001e414510070395013000b0b6401604051030f1480006d99001c1d5011600c169440099032054204412209009040c2d8015035156810304240f01d03100d60004a4014111000b65280d4507903204030600035000b80003541c07900507907564829048007008002000155168506106601c1a034140e803981 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 509315161 1250 509313911 509313947
    0x80601110111070503040329040b04020607081606050709060c06020a0509030f0105070f08240301020f04030c03050d0302040e010611071205010506090a060b09332107050a030903 78
    0x10f1111401d1651301d035800f030300060314606483d406580d0380480c00440400044111008441c568446558520001c0809041070340c5c492000e0080c2c03408512900000c00178820310b803200d00411041d40c9400419110300a04620030b02c00b450300e081100c540c00c01020045654002401a0303640c182c01b0058400f0301601046503014481e030b00c000b608111056001d503000d0405529046411a41c1c3c007021038803044100c6a103e41108200c2c08140144410f47e003820551760020000740c100500d80714010010303003042e8016103d083c50304004005010003840701c400ea0181525042d40f0b031070b042440380e182005041c030035041004100f070303007031b6080b0101400401c0c0588805184240301a00b50700703003e03004e4142540c0b40d602c0b803408800420314076001c921642040318588114181403445600030030200c3da420602031042050042c0b4400c40403250000801001580442e0040e11401c4003405e07002500039078800c490000c00702c0c0c4148000c1640100c02d0b1041142d95180201e04140c107854203c82000c030101c0d400c902 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 509316411 1250 509315161 509315167
    0xc040e070b1605011b0507020409020f04020d02040911070b04030f02150403110c0103062d0b161a3c0106050301060f0503060618150c010921080601110111 68
    0x40019211640010328001d100074002e98118800300e80e517000c9960383c4c08010480400c82c680050a040e0081c10010b8001821060806030300f80c0420142e85c0b0a80196010590001302407002d503440c1e102e015890351140e2015400c00344180d84541540c500980701038140f080c050301600f0191300c01c008199191494a424032124141440c01030141800d07401800c0f000c1c02900010300055210344a501c3c11a1007114103c14510020a0906000700c0041c1c448211002006000300d0110310040003041c0341803807000180c0001400741800d8034a1039001004a54107034002091104031080000c600c5034280390421000c4500c8001d00711b6000d610707880b4440841181001000150850300305020314103c80786a254001c1013138080204442c5440103e41b01070340480c0034040c114580041410307116040101508491000c4514034191590303401c2403110040e16034507103c80401f00324001c5041c104001091003e0300c1c04003032001c0c0c098003c0c20b0007400b460400001520b005910b00c0309402049541c0300044035540c2d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 509317661 1250 509316411 509316427
    0xb06160528120c0b0c090409020301090515100b0306100c0506040f020306060d0b1f080f070329132112110f03160203041d1603050105030c040e070b 65
    0x2001600e4480155040c02c0940740c0040001c3c0540c02c194011580008641e4056030f89030050741a075000ba80030950003070b5403550303640c00503202441810045402440103269030580704e010700b0060075004000b5803c801c542d080c2007000150140030350343c0200040720b8213108950380345012183c204c05c0001c0609184282b0041c0030030b1112182012042500070b8040c2c1e02d555540700140070f10301e007240d08000c000e05000c900103542c403101c01c01040034401007140b1846210760341d4000c40745041004407034104642c003c00810000c100d07091600d80b1407011000c0c20b84d00c6001904034580300c1c1c460000c114400601c0c04200310740070801d50941210001c3e00140510400307800f41d29004004200c071400d940e1249280c0002440c4802c012416a800b4208000f1024a99603e0964000c60104200c42c101c056200511005ca003031180050001010351502151021901d8101c620b039119842d0000c50100745481c150041c009078030080341d00031248006607004100400018803040c0346c0a071540c4890030740400452548 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 509318911 1250 509317661 509317723
    0x7030311040b09010e2b211124040201050702010905130b03010b0d171303050706030b041d030a03020c0c04020c1f0b0a15121a130b061605 61
    0x100740c5001c5e41c0b50008481a201445003050441d40d1341aa4002d540c05803c90612a45241c1130f485481000c10751201c90384610704082e4045041002d001258800000b000c140d00c00308007401100c990314a41d040c0030740c4c29100c49143e81e48040c0020703040210006120065900a0030f0060040002a01c0315502000c10307281c1d48020003aa52000e4840d508160340e0316007514064050340b155540180c10290f1044004d29010000d501c00070310001c00e03024141000000c82d07818482d500041c002c41d2030100303031358080e24200002c4828080c0f15000241d02e0303a80c4040600700c00020f8a807403e105040040e6502450140c4500c0d00c1c1d01c134454580e1007400000c004c04040030109220b452501d105d0090050454502c400c0003e0b100035000103904007842107001c0001c145008402c15401c0800d080c02070525122500d000c00340e41c2c8000f49106000c030218a40029400c0007d0120194038200000b000a03403005400203c8902c1741d008523405004608140b0010300000380b0003086012a414546c144100049410b5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 509320161 1250 509318911 509318917
    0x80415022701140403050d0e0d0c08070e16090e070203040305010227090c0d0f0608061e090309030604080901050405090a05161b02010c0321051501050702030d0507030311040b 77
    0x9400910900c1d6940c3c0b8849a6000b5641602d9012028041002c0658000c444d802d008012640d80b2070325083c400c0011035148510440648420b0000e0b01807103003005c04400185002518041041c0c01e1107241c040c809900031007840942c0c440c022100402e465000c801c03451030286400107001544001180010204555840c0034484030380070b055020b149000d010418400c6c0700f1600381c1050703001001201103802d4640d000c02280c6001160001c1d0603616070812030300d02082107e51a0720041040200940d16000072005a84003e424008600c0c120514004caa2101c001820080002e40046500e00306a0300440030b850213800040c180417058504007907404058070007030750303003d00040c0c0040c201e8010317510a442c026030300c9501c3d880003400c4030b190b0350044a41202040059003000400365480b200a49600e0315001051010a40421281413042c000301c500c404c845001e6040c0702c1c1c00c0100c44010389001c85c29040c0c000c403030700380140c03103120908007500030349407180504040040008000c41c132a60340300d000d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 509321411 1250 509320161 509320237
    0x901080a0b03241006020109020603190906020301060201090b0f15060d0e0f07300b0402130614090901060302010905062b0f0f050c0301090908120c0702030610050108041502 76
    0x100c02211550381506a0032240c5411b2302a40000042002035001200100c0035918a000041c00141110403500c5001c226002a0800c1c07005075101c0301d40c981441406032005da040b558001041450381050300c0e1300b03880608602a074a010310300104420b4031003400c641c80400c0c508407410946142c168a10401603d5201c0b501800c10144046000c540059290b40ca40046440300307a6001022130301e040c0c45219802c50024800ca03403010310640080003000d0540180d80092050215032100807a000d810000421402030810449a150500800c0541e0b44041c03048100e680c00d0304c2041d591200c000c44a803000c00ea05c904000344580c842c441c20110140760303010101c140900c080401903690a65400803e80ea401e513998000c500003480140084243c540c0300380b014a01c10100d0b58603101d9015442034500d00d0844050100c45804500c1200354203003800101e500c482004901c22465080c50b002922507400900054405114001c001e60300e803400e60f044500d0f00442c40b49402020140d044040b11104500304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 509322661 1250 509321411 509321431
    0x210020a2318061c060f170a05101e060f06090b030609180c0d0803010e01060212161a090f0111090a030602030a140109020d0c050901080a0b0324 64
    0x30306258075001d000a03202076800300a10040110707884002c10600340c20100740c90301505803040882402032181d101d241c000300004c0303c0300184140780a0056840a0f41d984050f83c44d84c121612100c0007800200d0b44c4031100303044c140c000480031a00c0410560350b030b04081d10800030078600000440d43d65048900c101c200ca0b5540c0e0360482d4152503003d0061240000d80b0111382110180b0041100444803504101801c4100021541e4407001240043c003000c14400741600d142c44000014041108904152405003400b8001030502000c444010801849400c0401d150f85014112440810281c82d2011046c2c12080c034140800341443c00a054403444410b240d40313140d6103008500102c0c03050800c159414030f040142014a07152644d00c4000181d4002881008180c0e95224aa208a4108a11507003e0510150700503118240070085404480510801c4400d03c40140300c0501d140c2e902082c001e0f4490400480801d40b040722001007031030550000844002c61f030980c000588000c4805107454400e5488103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 509323911 1250 509322661 509322707
    0x70b03070903021507150b01231c06030210080103020a03030e19060f090602060106120f0204080303250e0f060702040b060309011a18071b212003190210020a 69
    0x240040407200207152890226419402d030034442c02e20000308540220000962629001d000c8502c6c1d18203042955040f03002590b5203e0031300640c1410ed014002d804510b0404905a5066030001070711360a00c1d1200030b0803c8410f4a00041c0e5490f4130000607140034683c0d0000310711a0721200090700d0880703000841d40c0014100d0790000340d030510015103203040381c48036280c10ba442510391205101030400301812490003a02040300103600d07071007040110b02c01d4a00c8102a01400403900c4214441e061380080741c1d0802081032140c1c075556a8841107821010001c4070b5840c1c1d0342b90740c0d20219010380b64581500d40d00030300100c104810480c06402c40c000c0c0404030390119004c034241a00f04403036480401c0c0c1815940010f040014181030082103d10781e80e40803000720303040c1e005044d41c0f12044080d00260942600e0042d09580d4446504080307242c1480907001d108000b50401d854840ba41c81c001c40d0004801100c0380c003100ad442600030300191501005140045d96101458a03015120741002030314803010350610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 509325161 1250 509323911 509323943
    0x1e030103031e0509010513032306010801060602030405010c03020f0114011401090b030a090302122208010e0c09070c170a0809060c0d0b06090d0b0105010e040905070b03070903021507 80
    0x5600d100628080c0780c0c43d203e08180680f001100d940d000f90002040c190100c0c43d000c000b20b108509080980c01060b4003218000e03c100c1d03c4030782485030681c40409075138104003092100c0e5401100351001d840c400e227440c10780da20150804a1500ca6409080482035107804800b003108a004080715050351040020080100e0030200111140305442c42000030000c0b05102103a0803680341d070401c00185000e441250241d80000070041c4855008205004c6080701807084c0b01c202550030b1090760020301000c8001c008403c4118000d6890303401c1004420f00c24010000010b101c00d004004401025401002d602010290410004200d521502c044c402123102035000172004507001032800d01c2050b100c0e031041d04068000e0400005028145903440d8052024040c8085c00d49400300b5410b03426002d015003400e0345d49090001342000000800803400b903402d098484010400c0000d4000448501d0f103e140d640b030fa1b3b02c04045801c030159800c001d500400322112550004d0344040604202401840050048122 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 509326411 1250 509325161 509325197
    0x180a0b150a091e0f060f020c041b030e010e071805060306040c12060f0504050c150301050109030308150307030b090c04020421110a1d0a050c120c1e03010303 69
    0x203400501d00001e2903a1806221641c484468200842010b031406039203e500c0d1400b0030811070303c41d00f11400040884011500700c80d0b04001c801e080500c1620f0421916120800403001030303ea010700202417680f42d461010400d00d00b54410001e16905400b80c0d2805500c500e9030411000070030080025040c10702c0c0c0400d409107404074405d4002d9500040c1034292034038241d07000e001403113494001d44405039524880d035240d410a00405e4801c0f44540090950342e08010202301034a09801c00ca071100c03103000c0c4010321082c1d81168444040c0d0340c0604008a260766190407000c05d14a020360456054010040000308000c09891000e0040d000d02c000d40e440c503c44501400102c3c00f892040c0b02c0002c1c0384880c041e21500c041c00743c140700305001d40384e20f40000c078007440031400d4000c2c207601240500001050450340c0403420002c107504107a41144c140400d003085041503109004982d262102d80b8003c07008030300c203041060225011401c07201d150348400340c0010780c890844d400c24881540803c01c854004103001d11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 509327661 1250 509326411 509326417
    0x40c0f03110307020c15090a0b040312020a0308070318020a030516060513030303020705011d241e090a1205040510030209030619020d1d0f030c0607050306180a0b15 72
    0x3c0f80d0050540710741d41000c00c07100314640302400d040303101c00300720101c2d041d2030300000301014281008030301360b59034a5890301100301901c803040501150080b680c0c0c003002a5200107581c0c1c010405d444c01183c0b01c004000a160b511001c2080258400da084200008002010481c0011080020252500d540d65850f056482d80b14460000d01160f0041e401400001e020383e01601c02c1030f015031b00018003000f50f41010311100c4041500484140d0010b01012100d4000200c000481091600210b115040401c441d808144058000e002c011301c000f0000b0b40c6001042200742a0039030080d00621200c06008030140c400d80c4036005581c0695080182c0a01c440e0280c000c41c0c040000c003078020107160f03840301c21100c102d100326001a0f50240e002c003c400c036074440c18040c05260014004900446c550702003a42ea00d1310346540a4007080f03810070f00068078404004a4059170080850900030354030f0390b50a0000c0d030f9000e6030951141116141c0418442c40001e03d601904608000b500c01e80780540310040f890039140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 509328911 1250 509327661 509327671
    0x5090a022704170d02070302070906050a0302180a0908030a0b09130515090c1e03010617061b0d0207060506010207061404120c030b1e01120f0209070e040c0f031103 72
    0xc1070100204000a02c07000f0312011455103000d0f0f02e0700703000aa6010805070f90240006400680c0000002d00c1309c80760078402c0f80d0060004483c41c04030341c2e15650200d510320300d1444074801d1a07404500060000070040e0042c1403515800382086039240b0700300b241203000f0110200b0700b42c05070424100040c4c0210411107a006080d40020041030032051451006101000c0203240311214081c0c6001c060b126125000e03070282501000070896004150300c0149801c41d60303e68000100d11030328a480d070442000202e10ba640081d4050310348040c130710031340400c4d046c0c61041200d0100b02902c000b55403828071102e50310182c081d03003090f030a0300c065030b590340001c4800385007080851000800c10001080821440a12400007602c40e02c4400f2406649498080f079a030b40803540ca0342000e02018004180080c0301c2d17440c0e4003410310303079500100f12310107901c0309031082003102002405141c01c400480c021500500c80109104c9000b4401c1c030604030700c0b2000500380500c40c594400440d00308804145121500000c2e00e10507 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 509330161 1250 509328911 509328979
    0x80109080c1005240415060309030e090403050901052104240504231501080303010501020610080c06030601180314100504021e06041508181c030b0604080105090a02 72
    0x1042c220404c6001c0e8111580301540e00580d10034006012000e1000c115006290786e4a000511900d24100900105114940c40f84100d01c3c40003040006030300301080c0d44070110203107001ca03218500000103501d031100d0034110485181808003004204240340140c0f5070302020000902d150b4122450120b81900c4066a0082082040401d0580c0407091203c01040545890046444662144400d600041c0342a0040c4015410020042c401c0b960100030250f04810850710095286141011141c1c540840d5081a440f6040000210b001d40c2e101d60850054011200141c9104507620b1400300c030710342d0740e4a0268015006010360182c090b016031203070621440d005402503039415068001d2241c40d5000c0344a6a900000502c0301082031007050700c8110030385805458003280c60404c5208035501c143c5843e1094015070151507152260510395925107484445400d000c60340c0036140f00019014000c642218000798a00001c00c402000001042d82c1c1440c001c0d505110482e900780c001b0390300f0840c0101c0d18003071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 509331411 1250 509330161 509330191
    0x9050a060b010c0b010e0a0b12010605010201150b2205031f050105010e180a02221409010305100c050f0a1d03010b21070e041203060b0903070308090307080109080c1005 74
    0xc186c0001e210380c1c1c4454031100001e2080c00450025001e032400f044500000e0799110000d00c095602407107440035501e04603015880701403506088605501c2035040d890172100308030072049014806266480d019020080558401c3c40118001c100c00c0300c4940011103403e03083c140001415405001d5000348500d0141c1118610b400c03025011081300e00c06072500801d90760030001505050001d14280260090030349044e5495403920010048031381c10041080d01c20225500100001a1700081c06220b01c03180c05000b040200e4040c0054030703140203095500401c50720000d2010074469224669a54801c442e0740b01c1e41c240c0c0340b601c09040c204c401d80300750b064218400700e5440090004030300c8022043d0300e1041c12143d00030740351702d11443e0820041c0c0c0c0480300c0e0400a0b400d500d031942c0500880303001e0824080d07900e01304042c2900003079903105103200c080c10107140000d2100c030303e440601c9508040d10ba16002403154291a00c4c0050242e03020f040210694051030301d0340320700c0c2c1d01c0500940b8041c503104849840 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 509332661 1250 509331411 509331419
    0x60a1d2d0910030803040f0b0408040306140c0412020a0504060609060315030302060c030c190305090606011e1b0813081c05040614070218090f0703080403141009050a060b010c0b01 79
    0xd5680c8060010380340303110340c111f0f554001804000510b00c150b00c00c03188140c0301c0f0314502e8100142c0b221a940008032410707407802c03c03c0c201c619200f80d0702258070b60007001c80181d0075070010980d003013255002160001d04140780031500030b17013000350501200d031103a408000c6a400429802c0306011203000050050700708101050500c40c221000d1900040d62010310b91070101107603216811203141c0c0e080072022070f03180c100b00f00c01c200051204d90350014080c201940f85031130303d0044107110151141ca0b0003c3c07062041c0c2c4103800c00c4036000b200c0091680031901903034031511030520505600191040c6002c80c401d00d20100c80d042e0594400081103240f41e03c8407070600f4102042074400001620480d20b23100018801c130405a030703490b03504142e94003072107143c9402400d14030b010311300b440c0c028040c0c440603612a8904100003040d440031a8212904241100080e1405445150425190a0924407450b007844d4424090110100758610300621903c01080600404001500e0100d0168000f802580c8a100100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 509333911 1250 509332661 509332673
    0x80402041e0e0102030115020c09070810150201200c0d050309010b190302031207030801181404030f030b030c0a0b0a1704110a0617060103090501020c100b04050109020306060a1d2d091003 82
    0xa0b03000000100d1100c2559110b400e00750800e001c0b401c181c0300507912040c50f07169806660142c100050381103483c241c50045c448101541c1c03953da03010258100480080019403498007036000c4400d4150090100701c0006101e0820500d110f0740d808107074480d000710640460600801070446001c1581601d448510b0383c071b01810b604070711820201c100d014176251030f51204480b021100951085110f0744408034402ca407030500404680e1400e4200380607a0000e00240e040e5560040c50908951000481030fa0702c20304050b044901c02c4c944c8021040d00c10b400d80a0004006000000b0805403034203880d202c3c0800d54401c000c9521506d41d14001020f4601314020900070751080e00102c0005e8080d0001620340040710ba40c0910b410700c81c004111466035180c2445140c0c0c50030b030040e00e00420084c00c0c01e505600301840083c0b014441c0b001400d007441104d140d41444046800030b15250064014160070801d000341c4003400204c00000a007101d080300c440c0c80c08045140040d8400d010716001c05810410704d00790b0743c0f41 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 509335161 1250 509333911 509333927
    0x30612030903062212020d020d090f0308030604020f0a050705012405060309071a091c0302150a0e01230708270f0607090303090f06080402041e0e0102030115020c0907 73
    0x80f000301044901e0902049001e03000000c492070546c02014129641c040c002e060603000b0002e5010840201c0080043c80c24040d031080c1a0f03600720020555a44600001030000c0c400d01102010350007020403801407840d040006020058090002848140c1554602404e641c900c880300c0d0141f8820240d00784800d04088000e558032030000801c4030100c0d030325485200c20814100000c81c980b450005842e60310781c106049070412404203400503240070703155560082e4a40f1400845d40c2e00c03003c0610300058994409800c40f5642a040d07100800652201810603c900c414008500c58401c0c46100891001c2d84144126841842940e4510010703003c0c5030140d07075003d0119190301f025403041007010100e00c101031007118040d4040d51a4007600c0b0f071440c58042c0c580d220341c1c0d1024540301404041004016004400c0b968841da049a000803105107500805600030000000382c501c480c0f0b86901302c2d861050540c000c505940650500405a80341000200d07941e4148070718280d0000c85610115485030b0080e130352 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 509336411 1250 509335161 509335201
    0xb040b0f160c061e0b030c010c2021060103110d0b0402010e030a0b19060602030c032506090308040b16020c04020304030c0f080301031e08090d020a0f030803061203090306 75
    0x2c1200304800c40480150742074881d0015213544e60300411000391508000501c0781400070701345050b00030000d480d0f444036816441c48400a42d070302141c54003515910f20454140e42070085d680e8003400103a80b0b10a940e19202408200c0d400201c841c9a0b605030b11b466680400d500b0342c03104000000355600d81c0112880a80340c20200c0d0948914500c1d00005030011034250f21400550710040007942c0a07a4103481902c21a0b4020703401c2d9001040440a200800300854420722044501c1c10711040c0c0c4100c802c05000c0400d134007d016189002e840300e01b0107910001d0280941d00441c050741041d115a2007040c00000c00404000150b886980302440905103034000d16030017030080c00c0c58074252006441d20b4084c04108541200e08410000051003085600c5040d0004110003048401c0607040c580c0d00d003802403258a00043c8180140c4043d0421595140640c0c405403500107951005242d90786023a050350b4105032051341c8a6800c031959010b015a001055840594008000300380a4540c0000e89130b5105c44401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 509337661 1250 509336411 509336423
    0x1009020c1b01091703030402030c011e08091e100e0c010c03032a080f0a090b0406052a04090f0207020a030222110403140601030201090b0a18030b040b0f160c 69
    0x3000032844c0e007050942501d002048003666032460644101414001c0103080076052240f0078411819100c02000d415811039074508010000c0c0c1c451401152501c01c29a0704001004901c08000600502c0821b408881f5426584184078008044078025204c04c11b00c0b68450004c5c42e0f2180e00e0001c6442034003c07240949000c00085410302c03051a40b6040e0340d001209680100300e24205200746c803c00c4508503540052070040c01c100300413840d500d50a0000f130241003c8c048075152404244c0c491206c4040d00c8040402816082c1c01c030b80c8007088094903402601c03a8040c0640381103940f440a04240c0200d03080300b0b0f0f0080094101d0750860b820840c00c418030300030b4400344180903021111403d082d0300c00d6005000301a0350701d5072140d14504d0440d000e41e519010160070758001000400c010f0b6000f180c440c3c15568091007050320303190b00351403c40ea09104050400c514540059002040c4038514002e5401980242040c2c0036a680781441c400b0310b00d00c280c03044104070004071440441a0320070307180d403502184550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 509338911 1250 509337661 509337677
    0x10f081303030216080901090806040308040807020103150602160602061911071b090f0b13180203070b030106020f060c070f03140c01060f06030c050315010e0310051009020c1b01 78
    0x40850b0400d01400c030001c5034845d10004070a1140d6070400c3c0d81c00d001700724031802082d4a28082e03400900050700a0401090700c200441e980086a0180d0084c001e04003c02007104c00351652000000d590721408034414010342100d450100307400e032001c03031910300c580d010038558009072240610100082c020125a582103120a021260004805201745a520103011500560050401d4040b43c110341200b509005600c0c94903030203181035200c080195418185140000070090501011410716100d03442000b91306004000000c9200704584020b18181c400c60390864007051f403200412950f42ca026140c002010806002c807400241c42d4102075250b2034030038031b03100c090101c2d81aa40a2240c122803001e032a603075101c0d40180003a54100c0a040e0062201d4a414402da07803d15001526a1202400c00030007494036115100169000d4203010122580180840e60000a0040541e0051405903201c030b69004502c1e0000400500a0081e580342c9801c060141100252583c0d844903000b1100c025141400000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 509340161 1250 509338911 509338927
    0x90111040f0504142404110c03120f19020a0504090c030b03010c0302181207050607080c0606030309010503010e07120c260c03161e0e0f010f0813030302 67
    0x114015000602801c0501501c041c00d08040005a40f400d5014480101da010f0410031216901000c0084803d030480f900310b078a9040d0710210b0003802401403c1107403001d0008594041d044004020044c0310079914403422140c40d807600e404080c14041e41e05200482e503611449410303214036801403c07104940c4c104185440c0e940c4810700141c426000b040340c0420f6442803000782c141001e029021010303040d480e04628080341c8a0f8400428100c550303505001d10501c119080c007080080101101a10700181880d45414491070301244a07481010303200310078000ca901107002d81c1000070903034449103816182d0703606580c02c0070200540c4401c000c019204201c0c80d280d5151040c80e051084100703c010350f03900e0540e9105405200c203000340c00421040c9514001340c04024544060b02c043d40c0d000001e00120b00700100b00c0101c11268085016114085000d030188010511038110503458031203001540c0c90501c20117040c0040d280500e15640800c0401c0120001841400d20f010080c201144a400c00504241c44 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 509341411 1250 509340161 509340191
    0x71220060c030906151e0f030109081e03090c0402030406090c08100c020f030d0b06070b0f0121020f0103152411070807090c1403091e0a17030901 64
    0x10070780701d0941070070000061004185041c428141d03c1109010f00c0000c1d41da1101c00f003920104c40b090601041900c0e00b914039219031340d4410700c0d50441e07402002442542c2c042e0410886070307488000000d0002ca19820821120b25091089d64481c5240c54040d20215880400b03210196100400c11941103607901c48280019035000707443c0024122900c024050f0400402069045409104240c0250f500c0005002030a0b44000121500b403482084c011443c400002c000c1100307401002c400628940c43c6d0802c0000d40c0c0c80141d00503040300d031040c4280c1482d602c4e001440c1c42c030142c686800307034004400d405565619402034001d840303c000c08140f20040c156483d0a2504e450300300c1d055585040d041202d40c3d0070034961020001000c0f8101c08040c01c5a80c0c90401002d9030b941c2c080c403414180b19124080c031110103000304031084203041c80744151581c1c0e140c499111620340d0009003031000030400e0024543c041300d42c00106240c140d94045048035107d00c4501c24200c0540000f800c2e0301280d900e0742d1000d21000c071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 509342661 1250 509341411 509341423
    0xa0e04020609060f2206031802210a030e03010507050306010519120e01020702040b100c1502130801150b190503130f0f030801080a0b0f090c030609031b0102071220 72
    0x2078100650545035010300f080d5175400140d8050401c050500e40a000c0402ca000e010054070740e41110341458244c14010380d00d80c41140b403051803087d4045d004885046c142c00160040350b0140c01c400810050351448401d81d4280003d5413500e00046051112031b41b5162081c861082503089810007400b400007040d0728005070342082d015034400f079401041c200d0440c2030901404903210411101940d0b4502d01000c02482141500009030036400107c0c074815a09002d64122855071650383c0c20248030a440d240014040c100500003034206030b010741c8000541d038450205032060040030307512181d0004101030341150f180d0000351486540d94030070301c09480020602e10300c40107418815044101004682c0c20080c0c01c07628141d2206025401c02503110b80050084040144e01031700c5038910180985858100e079190035074030003102340c252142405100034000d0020241c9025031105455042d40c4407841c06a9090740181c1c0d07001003400c0c44444081c6000382c01520b00620340c071015105500c2d01d0810100b000c0c9040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 509343911 1250 509342661 509342677
    0x905040204060c140c0117130f0c1404050408040b0c1608060714070309050d0f0614060301230f04022202190507030206010303141215010e0a0e04020609060f 69
    0x1a0551204030070480c1130030016009810b49809410010341d07a41c000f07011041c450105450746840f050015141810902480b015982c100b0851010310baa2460061070381c01c2c0c1030080b1104440300d0440131445241c40d00034644615444100b0606007441e010f005d9900f60000c1c40c081c0030f103010701405114200300c01d44441008040c2c8900401c12420122070242009001540404201c8010400c0b1004a5000303030400b0202c070021b5410a1005110742404c007542d5005c2c0310010724060400e1380c03407070070b5070b200203061405180110004c000f000701c41050507500071600081c4c100911086400168810807110042d540140058203614940010700640340200c07002e02c2c4003010565010460f40e0100004001400101041d41000c0340ba05580340c0f0003955405052000400f0003010140381da4000c202103042c4c980403c10091103000c20b003807410780f00c50307002d03015035003580003c006080440c0c551038100c554408840301903602003182d4031941c0a10080794044107190741c000304200420518400854001c0c02c0d90 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 509345161 1250 509343911 509343917
    0x105040c140d200901110610140d120c14070e01030b0a09050f06040312090206091011070f18050c0301060f03151401032f13150c12050301061d01090504020406 70
    0x131038102c00058450940c01442c54070b1540144108005614025102400c1e208040701c03440704140000d00084100078032180081c03205082240c001e40309034101c40c03510711040c4035951003c001c0781101c01080c0c0c0e85d0461711640c4803110340302004001103056440c0c82d47e044140c040c008a004410f6407200392600e04500e10354030040d4040c07030421042c10b41c0450911202440b07848107001c81c81054001882c2c43c020152120710403c12040030190301401081b11a5002e000501a80c80d80b43ea43c1d20100721f48d80092040c4004584000c00003214451588a014440d040c42d909044c01c42c0d08004044070b600304d803c42a802456560b41300c4554040c08441640e00a001900c03100200700312001c001001c0e00d01b51000a1044139040300c89100488040c0e60f520109444409800e0b20356800049c5003204580b030f036000d00304040240246003161603005058005042c040c0580440103030410f903044480b4071003440707807a00254081c0180203d52407100c203c0080c440c0145000301c6030a4880300050201c0c1c2c8543d2109000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 509346411 1250 509345161 509345167
    0x19031215030309170604030c060506010207030b0c0720030a170c0a060605031c020d0e0112020a020307031106010509010b0901260603120c070b03040c0905010303080f0105040c140d20 80
    0x600c0040090000f044003682005d00000e090030344e4050440601004002c0c0700300d4441d400190264405c0101c00004c507080481007009007014080e140c01540300710010b85104004000c4001d075640702c0390746031800750009401080846400c0d100c200450b5900304443c3c11007041008910358040342000381c0710760240111400940c49144c0070816142c5041c0302e076501405040740e45040c004d07540108881903044071600b4541584882400102c3d0044481072900000d01d20100704050f82590020151940b02c1c030a840d501d0300401090301440ea594403d124480e4000e02002c014030550480d030024248100c81810207014200441544404072010500050064000c0004004c0180340c208800d85201c0a0724054520b490601070210361540602d0144520540c00000402c0400c000f508061000f05103546040005585070300d4018969442941e2508520000000216062900344100710010300750f9111070907100145805815280c0001958000d59599880380200300c1c004000c1003c903080c465070409603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 509347661 1250 509346411 509346419
    0x40b0c0a0b3301021209040216050303070305060a0e06040c2a020a09140c0c070515210c03150111010608070923040f0c0902040b0c06010819031215030309 68
    0x15000903032540c00107900c22510b0841041e90300400d00b030008440d0482c0c810303550100e01001c94040c0c8104020320921981440011052013004006540204500c0e5410f01c680d490745402c00007401741500032410f24140c00c0c0003040b514609a800800c0104042c10804640003140e5003d071504517400b107440c10850155000da4044aca0030400c4500a00f00c0140100710301c10711440e08204d48107009188060300031b80001d0300c28000c030302049404020400200b5001c00c2198026400b401508079680c101582c030395421a500f0060401d00b07040f44581c0b05180344606598880d200d00c0c062441c286101818401c4481021010040a01503280500080d80082071207508d001c109030700300e0341e40c40d0512841c1480e040c02c140000c00c40c0c0e01803d0300b01ea01300c081c3c01c0e00c00c20359080100c6083c240b42d104040d114070010740002e0000d190005000c8000301d07070066540c260390f500c0361b079a02d0349007580b13420303005166004684e40041d004030700d0b030004002d024400041075400c6117881004140503410560108203c400100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 509348911 1250 509347661 509347711
    0xc270e0c0405130506010603020f2d040b180109120303181217061e010f03061d16020604050316050304050a060e0a06090b1204050c090709180b06040b0c0a0b 69
    0x13070040c03142c0d190841c032b0500494175007546c1c0c1c05503160000c3c0c3c01543c0e110281c503030803015085401c18009050041e6455070b41341c64440e059442100d1035400644403040980322503004401e02411a24a0f51142420f041c0f40e41d012001018400781804400810354009408940950000c0380d04000c19103d20ba00b40c028901e43c000a2803000300070612603041d00f286040841284848001b41d54400c0c00c041d9018107284e80c040c2c02401140d00003140d02440800d5110380c0e9280080214015083e032850441c80b40403140703040380c81d0a801c98000d8925402000516500e5011880300c400d0180200b00381c0b81096200c1e0000b8014080b10f903c01e030b0000c0e01e80d0440000328a840c4402500134103150404d821424a4503100711807038003900c28040300748800c0400240038010103121506071400d00904d40f1080345071400003d080403459000305124549110199104201240303d5407070001401040141441c1c87c01da003140d0a0303132140c0f10003100da00608032004001420940a03901584900700d5064a070f201418581c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 509350161 1250 509348911 509348923
    0xe13030903060b0607120f09090b030d0e150c070303080603010903020c1905040906051f03050c01030522050f120f0913090f06020d110a0806101103040308070c270e0c04051305 77
    0xe2209e05d140c48403000c0c00c3c0d40c002034400d1604001c0d040c882030944880c0c0014410041e030030b4042d590742200250810a0b5900400c142040c0c1c0e100e41c403a08500d4544405150817200076250003400741e840340e0031a0083d031030008004103041d01c240349460245901e410115043d90840ca070100c2c0d002da03c40050010301b1a1402c0301008052504400c003e10038559150703150303030341303000d90680b414542d8510208655010fa48010410385052450400301150f96180440d41c81d14000c0b8132130700354040c0001d800761405401046580d0079070702c0359001d4185501c2c00308100b075440b40c42c3d01205006544104003400030b5881803034520510300440300181c9900d0100000015154080503a00801208205012100d500150f07940d40000d001d0b1522020010b002006940b09200d07950b480030944404900001000b19900003045428442e0782408455a82e03840312010451107100c5031105140d0014810080262a40c01b0301c3d003c0f2510002c075200c0c03521038400329040301c50a40700d4404100314a01d030b200500c0810058 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 509351411 1250 509350161 509350169
    0x70501021903050d0609061202031b01170612010c0c0501060e04030f0302031812070c0e0c0306190902070303330b0a02070509100e13030903060b0607120f09 69
    0x24201c42005203034005034004100200a081c007901103032001c54200d0303a0744614042c00746444100110358480265140f4812003841c00c034030900c607685420424402c0c4e111000d90701c0c0810b0715038000b946449400c200060304000c024580000e901448650881424040d400c0d004c90151181e030204c6c1e6140c10000d0946445030801e0340491500d20604c40000d600a140381a150014580140c132500c80e1108106014400000c803d143d10484140c0031114401c5e000800101c0d1041010403a502e80c0c0d40031924080300b04079403000000c542840001d0b2203003044400c4070318001c9810b1191081036112460f410890704101c10903000255681c48843c01056100011111401c0e070344104501080320300da17280e1002d10a0f0140d6506580d012034450111030007044490701600000304904c0680c0f60421a54080c119607200d81009140904007080301c0c11159507102c01003940540c0d80c0c0d81c8003030440d01c3c0d1801801c00b510040b50001c0080141d03202050794904000340580f0320384c0e580d28140407a031100030314450b25500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 509352517 1106 509351411 509351413
    0x40f060311120106081005090c090405090a061b0801080c0904021909290105040e1501090302030f0a0b090c130506031513120806010807030e070b0a03060807050102 72
    0x5c00e88a14291042814250ba5900410095030410b5402c003404040c1081100b01034286070304070700d80c8009040d00300e65054281d41da50000b02c1c0d58501001c02c072025075a20500c6c80a610103c0e042c010a02e1030300921400d8031200028001342c030040d0009124003951400b1214400c00710030751030000e090700c2000304901080c8090002c80781e00080d51680c62107044070030000302d642c0580181c40603503041c08084c182517038981240809001c074a0b000c50381848001100000182d0f001c10801c40c1c5c101250024042d10802441c10382d2501030b018204000c0c5401a0812074000d403140c0a40020013040301d940468607444180100341090304850000c504902e41c102002041c0d11003e1002065078828000c1424040790071204444a06090701d0030380c000790031070340801c2c1418401d42250000f180f0903c1998207003562901c407102c05510039400c074408283c44a0041000c0760091003200c00500c4280 = true := by decide +kernel

theorem cover : BRFrame.Cov 509172661 509352517 := by
  have h0 := BRFrame.cov_init 509172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 509172661 ≤ n) (h2 : n < 509352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
