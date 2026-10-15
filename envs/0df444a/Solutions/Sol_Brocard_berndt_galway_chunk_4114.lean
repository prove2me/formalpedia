-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:30.974012+00:00
-- url     : https://prove2.me/submissions/90d64d96-12ed-433e-b6b7-11a8eb0da40b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 739748201 ≤ n < 739928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 739749451 1250 739748201 739748209
    0x10504080106120312020a08040618021809160f0e04031b1a220f0302071802130b09031c140706050a050f04050604060c0314150a06110c0f 61
    0x503904409400e5103011000141c1c3c10010030942d41c40740c4a9154a00b141c0341d52030b10002240125140b80f408180b000e400100000d0040c0e2040c001c0005441c2c0448a02c09180c01048504401c58654200940c00342d0902c844044104452811222400800603846007000f05000e0703c2c60540c4a0320660038060400304080502444c0401d107800000b04c01c240d207040355810450034485a4841c900c000c01140000b01d018000204a5140080403090b9004051851690b4541d841445281c007a01180100a804900420302401504260040450250b118604c6510203d4000095440f4188459040200e81426107021440320900d081024201000031003455081d50950540681007654140008a600c1000590703444940075050507a8100669665000c1c80640c2040c290341c06441d540c0082d000400051003a00002c403025a5450045000e81aa8112034000c800c02c2e5000a002400c0b000907038114100341c0f5543d0020b080380d2520f040620b00d8096829103801ca01c0040030700400040009090a031030b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 739750701 1250 739749451 739749457
    0x2030a14040e070804030f031107031202040905010e0405120711090a0e030a0906120903020a020d0c030f5a02090403050406020d0e010e01080703090b0c0405041d15060105 75
    0x14122a00b4152411000040140408413412004544080e1403401028800e2282c02c41802c0b0013088203103030509985040c0c0340d13210066400032000d5020400460075484a0082600801801c01c3d60301060402d4606031381070942500341c0280050007800b4000100e09406000754400b801580c8402183c1c036041001c002404080030300c0c000602c00055010b0100354000401011207100742d4802d81d03902c95140b0102c042c0e40c1c200201400607840580c4a4003d490180c01c40c0d05494403400c1400c1e10281d503a6211082160140c5080d528508041c01209002c0100340c20000710645031b510880b03800c0d00402070000c039000000c1d5a010303401c1000280c242c480800140e007400b42500180882020b00d0107144c0146181d019000300383c0107020f094011014180118680c1e101c49205849003a00da4845100440b4155001003074881015200d00c1a140030aa031403032030500448002c64041c0d80c03681002c090009445221440d84404044107840090000d800700b0f01203032054505076035a07026102e66004a903540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 739751951 1250 739750701 739750709
    0x20c0a0203010c2c060d021b01050a02040e0705030f1b0d0e0a03022107031d041505041d0a081602120d080a02030906060409020301110f091309020102030a1404 70
    0x5841d040000e002c15802ca44c1e0001c1c00122a4000e4210741c403000500303800d01c20320700e000b250025800e122222811400c0c0e00a03011030300103903103030807121281d844240342502c0e0103460546032603600203024000c40c1d9000c8a403552080841c03c2c00c1d840e5082040105c1c0d00440700501d2852611240404200c1e0204208203c82c02582ca054060001c80c5141e41e8840d25203e001b607044001d446500900301e501c400f1010b10b402c03448102000c2606110080e00c054844c8560740071a44546200d40a0508141e5a0391045081c0252420014034040303003482c0a11040318a124440704028025050070317009000000b41004e070880c0c2c40b031581a2a05ca4914941c400c0d40503210b00291b00580c0b811f00d103c141140003038000c14103c100c0d5a0301e4090f4031607034500c1d4128441a41e142e002d6802000c0014007504190f0001141148042e000203502d12280075201000e030414149040f2441300010741c0c44251030540d51000505500860803c0f424065a00103035591081c40a8070092007410030250703294007103d4064800030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 739753201 1250 739751951 739751953
    0x303160c0801020f0918130602071b0e07030501080c0d0f080421061103040f02012615010e0301151a0426100b030d0c05120412021203090a0603020c0a0203 68
    0x3d6138550114a8a41c1000d90701500800048a20465114100c00c2e064095140e036610003940b1802ca84070b600c080d5000c0340701030760291003008a03101c003c40348024000040164a074000301c5424400c000605954041c0d101c1c4883d07a0080708200000c0e5641a00b184d201c961100414601c1181c600c0c024125000315845400715003e128030340349800a1603074035085414801e00040104101c08800404d05000594010b0302c010f100d075036800015405018031403c0c03c101c4401d40000d055441690142e0908202c03034450007040020015011075800c072034001c0450100310028449507410301251400540544244440d10020010600c4868803072000c540c0078145803e81c036200a05102e003404280e442050381c11900388100e05a408607030449100f890300c000b038000c001d401c0071443d11004031411130702c4038003d4406004940c0315240c500c060200400040072103240c1d18010100c50700410400032510880180d45d600208161406a078038600c01d48181c410f141801a201c441e074261903490000100002901 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 739754451 1250 739753201 739753207
    0x30f0c061312110a0f0311090705070b16110a0506040605060d082d030405060106080601020115031b0b0f030c0a0c0b04060546090c1e0605090303160c080102 69
    0x103005030210443c1c0820f1098410a03511662400fa05e003103a95a884040e00706008030110f01301c0f0f442c01072240c6411114900e08141050096219031445a4040c1c0d2a00e15024400309480303a40e0360040c60240021003403402514000d640e40e155030751074620041004011a030755400142c007c1da1040500856242c100000a46079140502480d08910031100b02103460803c1c2c942071150060303010103d074400e580c8100079002903440d124040d104040090030035810740d52501c000d8800c0c03c48940c0504020f5004a00c801c8103c0d180e0064810320400b981c01611120b1420800a000030548a044075040512a0105039031980025000c83e42900801c900a054114800510003400319036002203000300200041842c0311103460361402e401991004810301c2e10000603810142c0741740140200041070701f000e030000c0b8103882c2c1c950300c1c54030b420095000b448201690008412100c0702291480c00600544d0070001d15018540c00040d91382d00402004070009608110040b04011100d45414001c5c82c20034020342d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 739755701 1250 739754451 739754453
    0x723030304032613030305040602251a0618040503120103060b0111030a0c0b150d0812060409021513031b0602010b0a0617090a0f0f0203010b030f0c061312 68
    0x44000e140c180032140d400060311040c0c115848031078150340a82d0001600300801c240390340c0d051b405480010310949045a092210001c0d1b841001481030081034002700164900c005890450700d10645600c0c3c1152440b6020100311468a4201c40e01c500210a40c04800d0140d455182c09461485002c00c11140f00c51904000810440b19411400082038240c0341d140c119924107841c25902d01681243d071000485445c0c1040214102c2c00080d03400c802e0081d850114100690041350810080e09811250b46d0000138182014005904e0000e80042c1e0841e814880b2a441d500010040040118050040c2d100040c092204c42645481e400045910080110300f1306544900c122090845121700c40155003081d01f4004a0315200132070005a51aa440c0c50841005040107113540d20750080c401481c900c10b480d0460041806410213400381e03845502000070a580600c141400d55050042040c0264400d020165076844082030070120103406403070f030701e468501100a052040c80141e10090481d20600c0201c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 739756951 1250 739755701 739755707
    0x230c13090c0806030c030a030915050d02040b03100b030c0702040e1e060106091212050f07081306030614010c030e030102041a040801051b0d0b0406091e05070302040506072303030403 80
    0x140c801c060132000d481007401104145902c59810100060025417aa5014006d118110700e58408250040c60502e0405507001081c0c03040340d0254010b20f00340080801000cc000382280640310140c14004015411410803003a119081d00400c00024411610744c4002203544104010644494003080e010242d10b0603403c0905869100c04c1c06000006402242c0200c1c6801d40003036034040780c90380014001d100841c40001110030780c0020b25000c8141804100f2000810074140150030350744c0c3c1c4124500e01c0140b41183c090115a0140d00950070000c094208091076038200702c03c002c070a41c050400c1005c42c2280000203009201c2d9802010500490301c1d5810f0307083e40c940c0041c009803000f8038020815a1610420806c0c2084100b10300c1140c0359040201c80e00c60340041c2c00854a00030054004038082e034403004400c0688102034080c200d401c00d00381005224080c0c5004058010103d410110700d01070a041c0401c4051042d4030014014691030b580c94190440ba40c90007552509100c01500d0302d90038685801 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 739758201 1250 739756951 739756967
    0x20f0d050a0f0f020f0d050405160902180d03020c091801090302070311010314011203140a11010c030c0c1407080d1107060813021e060c0d03230c13090c 67
    0x1000b0061506100402240d054400c40300c2000f14404140d0810f1008020711002d0140100200c802d402800100d6a0348844203880390040e014480d0702580314913100f0302c28600c00340c081e144c0d2440751110030b035288003081c0c000c10312040048043d80c40300f0b11070b40e5500401d0000300a480a4140d158a03092482e401d040e4003140002c156445501e03118a80c513804c2004600740d0746047c074100c2840f0626801000b400c0e42020840b41020301c2800d00100603140e400e011001d079009844001c021a1046046c50f6402c2420b12544100000c141001c000100c2c1000c0002d100300b10800d4000c1c0a80d60700c2240d044040703800c012241c002e00e0080e040344c2c000195408014400080c0301550783c03151140100210f0400c0c01031092620400c0c4100300354042210503004c010b02c1c05000d1018602e00140a0403a451a48556009107144c0145600400056a040700f00604440c48503850000002c1c41c920000002c01d01c461032140c0004020980075140d00c1e9030b0700d0a074844400303a800294800c0c034000c21004219081285 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 739759451 1250 739758201 739758221
    0x60f060f040e010905091e0a0203060a0614090906180109080406030605690a080712032109060b09010806070c0b07021e01090605070207060f03020f0d050a 68
    0x189a080c1c4d82e0b0351950026a6400d4130405419081a082e20300d51b075001e038119980748034090046411101d4940c0100b030400400380c49070440c407034990505200d00c42d41708101c00a014400c0c2d07414000d41c1b80440304d0030344554014107035060980003c64078902b003000940284000030b400c820f042da5220354504000e00241190311807d03010752003070ba039200b5409103030101d0507500c3c060032000000500c09244000085504248101a07a503007151440b1300220908800c0c0f04800d801c4517170300041c043d188420482c1c22403c0c1d41c4506000e034801d0009100b60800003070144081641800c01d00c00c42c15940120034220300c0d00c0241140801c1c0b0302843c503030a00c43c5076007210711b00680c00d8418203220b90f03c650080d40ca4020441d111001324007070840d80f500140600c0c00741644a081e41c419110200f0614020b40041c0f11680d00001c120780d11010501c0501c28103104182d041000d41c0002c096041c03510201a1410714080c03800400d1660110b031540883d4174603030849010151104040002c0c3c034000103020010018460 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 739760701 1250 739759451 739759469
    0x203011503060b0c0a0602090604090207060525091505041d060103060e0103020907081b160605010504060e0109020a02070f080f0d0f32031303181d060f060f04 70
    0x30000520700d0f40782003241c00354010308002d805842e110b51140302c080d5015400541d040041044000b4904001d4400741942900c40d60340070606040101600184030040c10f107030307600305283c000b0541c1c0c15038000c00003401311014103071501080c2140b84c40c00d945502455009034901e40d00f0640858500c0e041d592610310070442620100070f070603100d0b280c01c007907071070709010094100d81e07540c02090070140035450180c0e000c10700c403008155175120481c2c42d11150300040e0341d00f01c0c000366880c561010009107008450141c001601e0030017106181c4040c0e1088440184101c603001a400030304001401d10034000240034210226050b0491030341c070f1200b0303503641d60700303032012281030040040103114180301d4400b22105030810344d02d60540166084080381000110348000e00b200c0c40015840c071400f40400051481461115902e44140d003541c00e02404440d0040540050402140e205001103090600342c01400460761118040c0f40d0346010210742c0d0400d21200c1c032a84141c004c01c510710b02440420003402550001c41d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 739761951 1250 739760701 739760711
    0xe0d020a060f0f0804032a170d0f0507052b110a080a0c0806120312010b0405031b01200f100608010c030204150309020616061d030a08012303010203011503 68
    0x1202c11664500d06440040016040203240b0310015140c000c1000c12498480000e5129a1f26588a280158140200305112040450b440c0c420750346074400d10038041100e00080c171a03403034904d1000301303e40320b4a00100c102c04c0f0f81d1082600180364016480c3d6898598120070020711840c1603600c185500621214400140e02c500060902e840310700078000001d201e521002c0c40b13078442004003c20107808034890074042c84188201c9440947c0381c156a4000c0010303450080e969030401c000d02d400c0401403202207081400d4001c1d040b044e40d03440962281d50f0705840180d601003513108040b55003403080c85404400c1c01c0c4a2414031a0088080342c2c445011603101100802400f685a0720507000c0e40a50310423220307445e0ba048208516903000341c0060aa8070f100400c030358502801200010901c036603400054400740d60b9400c4400e81c12013001c50801d004103c220042d03042c200101001409024140035a41380030302d40b00f1400205e9042d40e40e9050062038020001d41d265a10f03291724141c4541186042c2000a04003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 739763201 1250 739761951 739761977
    0x3060b010c050606090a021210090b01090b1c1407020c0319030210020c010219050403020103290d020f030316060c0503090703031d0a080f12090d02010e0d020a060f 72
    0x10840d80740c16070751140c0038054591301c400422014036002481d4500b503503000c0100d03800341d0302200c55240c4030329244255181c00d0303400d02074204d00f2108a00c1c0050b040c04003105e0180100d009400a070366121102034280785183c0d020110000180c00c3c0c00704c0e4420f40600901c04d00c40a0f94011526880760070342a0100c8940702035540b41d12041000e01171000d070260304030080e2070411401d5034005051840000c40054546441c400c100c041080180d0040c0700011000b2a040c0115139040c0158a10411003181070011040c07654840342501d01e000e0059881100300840c6c560442d22415020303502000c0081c1902c0d201e1b0144001c0d442c2d03a0f00c119104441051070000303599070b0300c1d0050381568000ca030108010510b0909503942504d00c410703441c001c000c1202d1000e001a449a54a01c0060090002480a855000e04802800c1c0c0350400c90350b44003820328400c2c0020702d07294440c001d403003580e82c0d024030300107000c00c026401281c0e20715054940a50007250361440400d8140c0c112801c80c030005155030361490034101c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 739764451 1250 739763201 739763207
    0x70e010311130b0702120a03050703021606080c0a1403150406090204080c2106010b0c0d03110f0702132a02010504020a050d02060d1e0612080909040f0f03080103060b01 74
    0x1944031a249440b0760500240980720002e006824210700c007800c03041000500f840c000d072400e651031004800243c00000c03180c003050b0341070101c3d64914180381c040000b018188040540700e40f0004041d28034200002c540250801e00c030300a250292401000c40d142e83e0700740090003004180803d01c2980c0100c1c1003283c00101103030203101311000c40d440c0202810f0703a5084a020001081111880111085c41d200015003541505000ca0790090141ca004250355810110b80740d41800c81421540050510700319080c0d811a1803d0103c46907408140d00959442c86940b0004021f4034611400454491a10b402402840146103194410060403800c107a411641c1c00022400d070313502294000e4000f900c100c400c100904010101825040c4010580c505140c0d0007c502800c840c03403101590b140b0980001a105180c00038803ca90250413221501c1038507910580322602c5074441c0451880c09002d18a001a09110010280008140d84461103064081d483d06004001200030301040d1142d501c2c21601401c1c943c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 739765701 1250 739764451 739764457
    0x105010f0e0f0a02090307090c0503060a05011815050d090c03140d140702060706021809060d032a0c09140708010302031e120a0815040203240414070e010311 69
    0x800364004040e40d43d00341800c1c0607420040f15107405103e0000003003101000e070b0140880c0c817400340d44d4003501d91a00b4410040c494181d68800340c1404109a460050340d211000d0702d0b070640c0e03c0710480708045050484112014030600045210b55480d05e4869000c009601c83c0100880703008030054240b002040c5400d5480e45c040105290110341840f00c80e07401c58400d100a058409c0c0010041c070f0400c515500c0f100140c0e401000c00403141440f0310b0240d441482c090081d030781c00403010303105a18005100d40e4041c202105a40b6601c82c40011403507203201154030100348810850b0700c42c20072850700f0742d600b05e44006000320607a83c502c1c0c01100b00c005162203110700c0501381207940060040c40d600c0201a000105820080481030079070140501100c4482107030001000144010b41c0d50394281d2a10b900740c410842c0315000c40510440c0100b09000c00203840d001c122100301d07400704001400e25203140010b001840b110005030200d59420003046003140e040340b11450305a0080c1c8090080820041003980148 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 739766951 1250 739765701 739765711
    0xc033903060103030f090513020c06070e060919050a1e0e10120303141003050606040207030c030f020a0c06121a10030c050d050a0c0216080715031506020105010f0e 72
    0x81c0c80480100082807144c0d60b082c1c06241e01c2c0c102075105a4031800400c140815a44002d00300395000103483d03000e4103003000100c0d40030a0301c0c94951031281200c800140700e4851a01c419200b1030740c003405c0d00c50442c046044c031002084000c00e040f80d5542c0d15400d1464000d03287ca5842e44652641500107001d00b09031490030300c62180003c641c2c8c0c01e142050404044640000d2043d41095580c100c5a01010140303182203005000403c418458907286180c00d03071a090700185081d016500500c0540d00003504544c1c8502400c2c1d15007400448100c030000d049243c10000c140c0a003e814003200d00045a5820650720343c81d903d25500c0500a50241040c84e00d9900c600307064880d044161492081941840383d48032400d02c00003031428a28210a200802c41514015600494900e079560400c0c0b94150301000340700780002d600144c58503258500030005498801c4d40c80380c60001040c44555001407482a805141150340d103510780f04400380c480c20300a0003001c007401141d6283c96000c8000c10b40b0721a500200f0711070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739768201 1250 739766951 739766953
    0x250609050405090c0d1104110f030c091c0b0402040e03031311010309060609020a020d1409150d02130503060109020705061302011110150f0b03070c050c033903 70
    0x22031500c8180001400014101c81c8240a1107008a40a80d2a121403450950140d003040c01d510340040c0400c000c581070000c12290140003000540132050221040d294800d01c03000c5845d44030302105010614041110741c00d94050405032210b4020821a2110240600d0081c1c404110304156000801e581c0d201c16600002c41e044c5445410700020200120307450180418035000c10361000d9952480180da040d80c1003503981c103801055412045504001c0030031044103c2c40c2103482440560600071062007540440b50140061002100982c00758404841d10f070f607030604e021940d074031354003401c0350711403150f8002d90348213000d0700700000f03400d00075402a01c0aa82c2c2160142030285c6802c441c41c0304101c3c88074401c074184403c18405200c01e41007407000c07000300c007000c080204032500428150410a041da400c009074403401008203001c00e580c0da80940ba40602c0381d0411500c03c88507420401c6c0740c2204950a40c0e0f2500c102e240001201d8025a080100424085001c075000b9208040c002d0030038810f0001a605 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 739769451 1250 739768201 739768217
    0x1505092e0303120903020f07060206311106090d06020c0d26063c0d030504030f170301081f0603050d1202041e03020117060102120f13082506 62
    0x3d08003042d40a190098468011184481d851614650802080e03602020158100d1800c004445a038400d141d048d84401c62000814040001c05c0803145c20058000940303031700c00703503030382e00704203454607011100529802000040c03031031076902c2d0102c00781d4000310481c80c090180e202c032020340c43c0c024075000d00d2010321100c50720711881e10840d035610100c4004140307991200d1400c1e0b8420092040aa020844030582c01d0701032400c5000440700c03c24110750180141c0541d44407950303500480d60140544055a90100c080306420340c041c2804032101d034a41000c4550508008000038005000041e2070701c5543c001e010110803c0a130310030070400c88040340320140060704140c0e86070302c0b1103108030030240c0c01600700f01f001400e15407211035402d03002c040a810303002c8150023207a0620542d17070000c01c5c004070007121440f080f00d1840c0c1340000070740340d280052841c40000004034949514182200541725882c43d40b0b810404041d0752015034941d100507444000d06141080002684003003035103800c000595699481d034a06c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 739770701 1250 739769451 739769477
    0x4090215090409061b0f0c0b010e090a02100504081506060702040e0a0807060902211002090d08220b130b0307051612030f0b0a05041505092e0303 64
    0x40c05a0140003000ea00c10b5a03440c44100080c0d0512401c080a048510503000414a0032005042d60102a0010040c07040e0b0520030000107124040050540e400000c1000076500e0340750741d07245084c2036044000d41c000c1e14440c0314525070b640000a801112800421105040c4020240d940001002c0c1c4001d90041e200708907600c054100f03900135419590005040700c06001032501c03401019000000101d44903900d40c4490f1003545885c02e56150310710404a00151070310302c102d40c0f655541403001000b1112940100301c50010765510020352a8040d0882c8442e541c80c1380048040112401c4c00c8100701ba403032101200421403010030b00580d0b0780580340201c58007003e42045070070013507600002c0546040250820401c83e0b80404c0c4038160100d0740c03252400078200003124202130103407031600013028003851621074030062560320340b2909c4044400540300024001c5a54121648040b040c0e0015a0003201d08014812180c220880c581001401080e8007040c10103e0012042840814031002d00020b01003d039903030b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 739771951 1250 739770701 739770739
    0x406061209020109120813090c0c1205040906080f06070201200304060b040207030c0311030c0712060f020c160504060b03010501120b10021f18030c05070b0d0207020f040902 76
    0x41c501078014109804907554862414509071a401401c03141040d0124401002010030b01008020701000d805c00d020601001800524841c0f0624002d00b404001072241c0a04500510485000c0e1141800600090b52129080340da45c8401d40104e03c510300c503001c0019602c51040c81100201c0c40d0850800c040308000168040494201034403d5940a41d20051a4265a554030091100f64170030345542000300d45500b005807042c2106034030801940c1003003040c07258444002c10720206031914605020107011184c10042c00812030028180300c0e251000039894404800040ea0b0b00c02d40b000c142c4103858190721402030000342c074002c0c880e01c00034000c244014481d030b41c000c17010700241041c0b922001039110a5640000e04080440c10391b00c0250300080120000764a2441004a4a04034640c05000300707080c6004240c82403a8460003d4100700141d0b110100301301062210400502030380300344640781c1c2c040302c1c6420002d500c0303c0d0080303102d0240448011141d00f001e010364248250001e08402c603004624443d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 739773201 1250 739771951 739771961
    0x6011e05071109010501090b1e0406030f0c0e0306010b0c0c06130503071212030c02031c0b0f030102040e18030408070e01060807030507080a1a090c091005040b0d020d0905060a091104060612 83
    0x400349e011400024041c0a581c9019200501081d6804610b048082c0e07120421510800d0340c0c0700400000c12100003140e00e0004990f03045545200c44503540e0314500851030300f800380f0a40c1e115071142c0002500002c8860103400c54099442c11000d48c0c000c903a4031060341d0302c2030107000001450859002c00c445840c0b8000c0d40400d00062960064a240600c1d016025206c00700e05104041e00d955070f1321155465061082d207003400f00348250000c41c941410510b003442c0040c001070030360f0041c0c04241501e58402406100b550010180c910840d900344e0b03200c90b64054882824000c181c0010400000112007920a000d0940101e41b0b94440c081c013500c1d40780740340300a0446000464403610101200402c5030b100d0005562064030000075441d15840c001c0c0400211144140150b000c00c401480b0501031048010202e0710b00003184880140d5503100b00c800c40002d068050700c0601540203590030800c3e14060354004240542c030444481078410224420042207420394001c41c00020729010b65030272003850b25801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 739774451 1250 739773201 739773217
    0x124061e0c030807050f2205030c01021011070503040909060b010314040209060a0b0d05010f0b090a090f0b04020a05071a0c0d09062d180f0b06011e05071109010501090b 74
    0x80d49042c0c424484100107900181425001e800c0e00e00103401c901f403c40c0f1300b82000c2c0000300e0140c0a0840c0c00e90000b9554898070b01040c21440ea510350b09620422582e040390119030384601540d0b180c5950314501002010710203829542107040540d00d4480c0d6210384600c081c1ca01005014181c0340d203490b001e03c007908400500d0250403d80140c0c0100c1c0c0c594400010703010b2880844000324856061045081240c0500d522090904105002400c0a5941d2000000c21340d400c4101c00034490fa02c0001e02c1c00a805544145900244001060028a9030060084c0102402440c418000c0e1943c04091100c114044503c007001e84000d012040740f0f501d0f1a00f20003074450094002081c0130420314104002c0b0141c2040c55000c4200314a5203400d680301074001c0528108060050904054450b00c0344001d00400c008010031500796140014801da01480200701c1002ca2002184400303069488090043d501255040c0c03200e82041c807840c1c02520700514101c4c16502d069542d400080e01e0811801c240303030001e0f12 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 739775701 1250 739774451 739774457
    0x15030c15020f1e15101802040b180414061c1a0106080f160801060c050109150e0f030f220803030a02030709080a11120124061e0c030807 60
    0x7100091400701000000f6580c4800803201256000d038000c51440d0a07036604502c0c40401d00c1c0402c000c0f003030a03541048411181c0400724424249a12110100240b25607004050f944030080703440c040c481c02003110200c15003010384080141a01580300c00c042080300b00c503010f40c04181e414018500081540340f14004c00d1140340424001650b170b01081c108034009070000c0b000200c101c0308202e000040000e00d540c0000c10030710360085043d0843c400501c510ac0501540d41409442c0407820b003040025440600030a41100051100032041000701002d00303403014910049210b42c2000104000c4044120b400c24280c003600039103090b00d0001d1a0700425122100c42d1620213442e400051080c400340000e42c03045407148c2c001680d07841c1c114009800b07007841d508040040e600540010000501103e0f92910317081c01150303520740e081c8010a43d140174013054641c00c0d9000e518004846419450801d00300300355045a15a17a0aa02c807905041e5003001c00d114801e400100e144500c1e4003c640580d41c442d4201401d49 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 739776951 1250 739775701 739775713
    0x2e05060a120504060b010f08040330051305070503070f12020301150e040b0a1817090301090f1203090b0f060604170a0605070237020a031515030c1502 66
    0x1403510300445100f281c0c01d4031499103580098880d0340e40017070070301c2a030307600d504101040d400c0c80d4400400c144c0b150000c9000d901140f4070f44901031f080a050703500303860ba10300d001801946040051780c00411603209040301d0a06c030781314010030f1a14010500001383d9405081507003440c2d14005065260080309001070f03815544c0da10010107646480b07081f0101403da0090324416071f05052800a80e006401044003203400c1c90f004076480c00c5480704003006085500105801051200050000b80324820624550b03850740c070300382d00d80301040048142643c149000d80d80d520b80c02901040d040d030580304407100c0209081509000035103000803d1031401e40210303010301600e0500c0c0d01d9032190403681c1d0519003100d545910242c0282c1c10000c241c002c1e140c1c055180c0c4040d15080105944281c401601140300030071001c2200280e00700c80380603520403000b00e13030008c0c0711012043d600c0c10704480740d00e900008010400c0c02c041c1490243c0e0074003a00601100c0d030203000102c07142d2501e81c004101c0d008030304520027180290 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 739778201 1250 739776951 739776977
    0x105030a0204050d050604030e0307030206220e10062307030f030b040507030f231611100c0f05190309052b0e01030e071a07080c062e05060a 62
    0x125102c41c0380700d4480c0c5c00901d01414103040113050807600701c0303220b44260f000c11004c0c001038903004141c4400c0c144060251003007001c0880b020858200e0b58014044a1005400300002c1c003503000c400b40111507540e283c0078040078020b60420031804502051490002c0c0030000d08000a202e0b22203104104441e18000410700c8903c000142078075001e83d83d81002a49840041a01c2c003024890090f50400d04198401c07890ba003a484c1c05075180c402001e02030000c610040c03640c10a8081c400948400f401f15098032902244c03904072000800c6a800c03c600040c2032044c810351401e004030220b0746000101005102001c42c41c190443c06040900c40c01c0b2024022001c0c00d007007402810039600c50720412000b4240100d108441c0050011028000c52030406045c08101c008411003c0341175400d4079030680e40445804106500c41d400d0784207c0e01d0081881e4800100004d076202c012500328012801c14a048a903e91024840d04038104109031515001b035a0440400c00c500d000801028624141c1c1400c229061704 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 739779451 1250 739778201 739778209
    0x220b010501111516120e060a0b03010e010608030a0e03060c04050613080a03030e06130b0f1005060a0203040f1a03073509160b040308071509050a0c050901140105030a020405 76
    0xb05482100f180100c030722981903016005414404e00c60720343d00b010071019003881c6e40039640e901d01900700321031907980b075500c400284c03420341240468940b0701000303001c2d040c0ea94078174680d29030100100d00006802c680b0403128614021a038280600c1b411140903003824203250410419070700c2a100a500c4002da1840010f51700e4003888a00c0110340661800210808c41d030038501d0420b1001003520140d10b41566074000040c074070103111500700c107030502010b0103079645601c01c6100312400e0304001d0b823220020a251603586d80c00030007002a03c071356403180d0f0400c0c1d5850040000544e041c1c02042d0002401340300107103603144124071010040c10582611f070340000c03031035404c4540c00d101422b00d5540c210286041200c500c0c01082011039004d81d00b180fa019541c0340c80c2c00303482540191f0200030510000000e03074106010451452009001440c00d0030084610b0514245030b41e03410703002c000c0714081542900003845107025000705040b140b0840d01c02681086000c01103450354401880e408070254248070101d0a070315 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 739780701 1250 739779451 739779493
    0x150519020f04170a02010909110d230c0403060b0d020f060a0e1002010204082a2416020f2b02130c080f0a02130902030402010c050f06220b01050111 65
    0x241c1c402826084ca0301c0c1c0001040c80b1800d400c01805282040081a0300c05000804c4441945040c038001640c19444000c410240d1500100050b140c18158240018031084100a0080340c0c1f00340c5007040050224000e08c90084040708000e580080340c010164911704140006043d40400c502e000b1590743e0081d400a60507510740c210a0006039404a0103120403d0100109032014241000072003418600c031040e00400038810402a01445111031003d01c840c904c00b0201601c0c151001115403100d4804900d0400b032444000240e01c648503441030b92500d420010039441801460305242e03095001c614200a2062030008812038000019149107100e5542522a41e040700089903a54030144c104010111105c1001a200d40e825500c10003800c0160030300e01c4005c0048940550380540c6030b5842d800103807505e015841c1c002d46903009206000030b09a0000c64503910603000d2410018440c3e01880d5102107e0f2680d0600420710301d42240103200b9903000d614070448402d0800115407023600e010b00c0c042d407000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 739781951 1250 739780701 739780739
    0x10b011b110d0b0a0b030714010c0503040909051606030b09041101020c12070306150e0118060b1201210812040807150c090b0c0616020c1c150519020f04 67
    0x5280f609000390300d6030601910482220880080c8440c0341007414015460804601090600040070300d90f00802c181032003500c00800045804028508117410000c1e00d545074203071103440828148a022846600078411000c224074041c0c00b08020381da59a80c1c000055240f0003203075041d84224034840803190b54000300f2401c072103c08e8000d411180d01d90314241c0155a0b450741103250000d084001441100400ca203040d04403840718103144040721080b51807a009002641014410300000036070500d015072040e000d0b80c12500880b1403405000440300b1444e8107045c40200007006000d080040d900f5184240240c190090300030410b143c5000156913039662407841c9070011807a49902c80c2105245103030840440c1000b0b1420055007441c001004001584400004101c110750040b00000440064800c000c10340c8980400b804000c401c0070314540c003e004104002e8100c42710702c9079861b0501403c070107004082c0200d25003017407180c0743c00000e122440a0b4100704043d027803a0005100018000410016082680d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 739783201 1250 739781951 739781963
    0xf020316090f050f01030209040b1b0a020313080102310b031609050301090b0a05090c2701050409030507120c020405010b091c02010e1309080d0c11010b011b110d 71
    0xc42c1c0741d035500419070341c0003421032902e070740320030010000340c0c5450f2007903a4002d034040000c1c803031a51001d14000a4500c1549040c04004001c900002070f143c000004040020400c40d04050840d951080c1900380d02c00c00070f0240400c00340c1c2c005200c45c0144c0c0038503051001e00c0d4404039a86d1503100d4041402503001100d0188003038042c00c44030321055030801042c170040d2070180e00a00429071075440f004020039000d481030948907555000595244c50600090b440c0800003082c20541003400b1030300342d103c81c108540c02e40c0f1003180c0c1400084c0c01c2c41c00740b0aa001d450350548400d403c117803503602d40d9a408070151000d070050011284000f0300580d900e1050501a10005141540703501c400d03004d02c03820b14580e841c4048001f42003500480075030f82004010042000440320120300152403120300016001c5410300038403400c0085071442c40d00440e5040042e003003030160382d5500000c1610b40035a0907030f200300300d42501280107500c441420304086100040301c94012610700118441410200d41140040201503c023 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 739784451 1250 739783201 739783211
    0x10f020703091a0f04030f2406050102010c11060406050606040b040f0e0627090f012f030f220210020c01090f06050909090703050d1101060b03130f02031609 69
    0xf020010095041550080f40225044c1961411481900d00c200e0102800700d4080e0860f01040003003d40035409001004613444208050b440c41c650007509580c094640035500700002940001d1141203000411060300b8010403290f280c6803203180040c40041c0c0324581110f41000041005000000180010011201000281031070542d0810340030802900c5c60f8030440d00544940c4d0041101d4420551881c0f40c104d004110b41c582c880c46034940340d0315640d08442075080286645c20014482e80780071174800ba0042603005001c881441e0720040c4000c80d1000070080b861000b06041502107800c454250300c000100c03c0c0b840d02207800041e0703001c01c0c44007500010f0307104004d603401d1541c1c080c11305001440c1081814035064204400034045000c0d00350014014446000052032407082000584001c5030420181c82030004120310080c90380d070480071804819820007034000307070400d41082200d11440360982540c4585880303580711525162945400e0781d251050881d02d001c3c1c01540903484004040483c00017071 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 739785701 1250 739784451 739784459
    0x601110307150f0b06090f0a18090c090b0a1a040b12150f1e2403151815010c080f0c011503030203040e04150c0309020f0406030c0501050c010f02070309 67
    0x200342e480d003d8601c605141010302c1c80e11151030b0401550200e51044880c803a02004410200d84d61010750f500042c003c80102500c01401c090590001800354040d05c3c210726090388441d6910305503489080c52a4020003010f904020b81030712148403582030820400f120749815030310754014030550441034415080e0a210018010002409104082c2d4104188d8100b0803010348000003070082604440d1041490005960140322075681c1028001a0440c0d808440c01d000c80583c15000d10750021948441181685c03000c00c4400c1c50030b00e510b80201d2141c18030700186a81d0f40d1700d88440c01421103020301e05002035070b0080070008181070040c000703000100324030b651030b505025012825910044900500841c02c100c050000c40c3d8080211004c0e140349080524442d111032406107043d0000040007442146040c403100d11445d0b25800c1023507401e00031218800d0024140081200301e84992000405042c00001d0411055010b200a400d495469000014184244550b5501030340c0c0804401c40c0050b40c2448180 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 739786951 1250 739785701 739785743
    0x5070812030601081312140403051203040506100305030313060b09041b06140301060e0a0914061305060f040b12070e160512060f060408030a17011208030f0601110307 73
    0x15a00c01c1c45e00c00d448032107041d652552981d542c10009501b04008259030f100510010090884004607401411540404940e040205040c2c2058a080f500e60140c24003154983c0590341c415019250804091071950b1030303658050100800c402000c4a40342c1c1c1781e4041e03040301d03502c90988502c51800f41c01c01283c9142c040505151550b4283c0001083c0540300036521159020001528152402410000c45080001c00011803600307143d4090341c0c10a003071400300e10614400c20000c5008043c2078440401042c032044c001010345004032040c4e0f4004225056031000c88c64150080301107024050080d1030155140e500407410202145c001501d0811b85a0034054a83e050900c0041018118602a8104009905c4451001001410591040c07004510f1205680d80b8881103a00a2030180c08690392107103007a401130120120809020b68102a080001600000b00301440802544c040340d0b980c91030f0f81e01440d000230710402800c201d04000b0400b29113201450f00308003c09102d8001c181e2010304007032091700300d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 739788201 1250 739786951 739786967
    0x101d0901060b1303141f0b030d030228030b181806070912061127040203060a0b0f040f03050a110d110d1406010906090608030f0301050d05070812030601 67
    0x1501c2e00b2010001080c0c8038140000210070741303070b10407844070074000051151071905012107103a180340416a0080217500301c49034041d0f00c0c0c90000760f041c1d80f1070b400c800000394103e0050720f00060070281000d200140d00340055503003442d01901d07030400051742003030340340401d020040105000d5980781e13825040c0b00a15036044410f141c070100c000d00030100c038501090010082106445680a0403175042000f1082082c5608102d0501000030303c5207484402c01c1034501e505450107110000681100140c01285060900031280300da08054a075103180c500c1c1c01d95140e0130758000c82e980c10180c1030038040820395071011140c031001580185d00078200c0f07d0b0b56081042804020701c26891040310301c00c03c2400001d441003481d40c3c0100c01200c070041800c84909120713104008220401c1000d000f0306001081c07102a80c0e1000741a501c1c0084100000b41d22200843d94034030035082040c2c002d81d006e100400103442e010a06c030b0034681c4550180da030071541e250015072a083d034140d40060241c101200300240340d43d000d552 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 739789451 1250 739788201 739788209
    0xd06080105010f120b0a0f0212041208010b031f0302030a061515120c0302190f0210061206021c02120f0a09031d010e1c0b06010206100509101d090106 66
    0x60380220f20728203a4080500c00300104020009403401e00000c3c40d01d000d581c80258901c0d11801c2c10344d80c40c92005864002128102c40481c0e500c04000c410040725845015620f05070782c0000f03089407860700d0300000314648114403401041101650030005c80140c4043c400384800b0b51040b840841c46080100d840c14010445400983c50081e2814800308072541c0308154194005280b5030014100078035540c1280640700304c020a94400d00b610345111006540201000b03001c4003564261401c04c038000100000742d440512500748100100c034001c00c08110982d0041080c4901c540d05800d441800030b03501400e90300101c8807100744809401c01c22001c0c401d40c0b448190b01c0504010204000d040f2950302600a0700d03031680040c3c1c2240f556405800690142d460302c00000030082103000c4400301e015140490010415044800c0411080402c00035400090b10f0b80c050307846103100c0000181044103014000e14014910304250403460000030717a100281409500c0d1008c804c00e2082c3d18500413004030300352103043d44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 739790701 1250 739789451 739789469
    0x503130501020f150a0902150a1e030204060e152106100806010c0b06040b060d05181914030412080a02212217060103121e050309120d0608010501 64
    0x101c61310720010350103a66038402107440c03002448010703d00102e84020440c11001c02d082000240f065415a000368010603021901540c1071071400000c6021402d9029621462010807801000d40c038262070448070401130041190b00185c20319040003640c980a51000011809940038601800f1050512094603068924142003000b02c0c1d04103800028400d603415000902500981000304ea101d80c0d40390050348008d2001003e407911000051200c0c1c005000c26a11110516811007180c042c400c004100035595650240303480c2030503074854403022613000040142e8501800100004541180b1640524480c18082c410087c1c984090000107441d01d01e81c2d1144c207001c454210400400c1402000841d401440700040000c00c5603a030010384042c80c226600a07007404110445548030003100000d2050490707008a0901107668440720043c2c3d4003e030048905180921804500103050740a90010341d08140f0b80e40460b02844910300031416140c121042d16003951361070320420006080b0034003030710b405011101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 739791951 1250 739790701 739790713
    0xb180f041b0e0112020301060302090a1e060e131e0f020111010e0601090f0204050a090e240406091a07080115080c04120302122d070b01061b0503130501020f 69
    0x210482c0282ca05204103901c0c0755000000b4021034a0a401c0340c00103541c046d10380d400d42c0c1810719011000c1d011505181c0103900c02c0032180500e58072180110030846604800100040e1145003a82a480e1702440e010340c4c1c1c04410284600452000c801e84110040c05541e03038030f4426100d071000400254540104420756818000f003019550f002142483c115014008001607800442d0b0307898000e4043d03035218903400b24230b55400088070300b082e41015051105000c161072401051400046892a8408000d0300343d503000c1c3c001500181403903001d060032a00038003c2e4644c2c4c08140c1d0170326000202c220b07110b40020b5a01c400410101c040ba54041161070f445050103080e0b40780c100c1d141c0102d40610b1065030360142d1802252400d15000703000512031052510403507507903107a40101d1550012480e4201001040c550010326203428262820341e1007195001041480036407a20900315940302c002c01001100142011190000410070002401e00d01d0741c42c40c1c00c0001500d014000b90401c880c20340170342c445800c03030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 739793201 1250 739791951 739791959
    0x405070e070810150201060306020d02041a0307021b12061302040c0e011209110604030303020a0909052502030405040c181202060328060b1903060510030b180f041b 72
    0x903960f00c0d800d030b071030394604441415943c000890241440e5800689403030b20000301041e00d030350241c0042c0152034029140c41480031800609810300e200480703120005800600d103001520b40d0141a565640000504072003c81140b10740e103904048017900c2648030300781e508220800310f0425001d440d07001802410110510181d00740081d020310481c619607048940c0d9511440f0800c00c8071610303100f00301d0b000703172809485640301d00c0c02070300951151241c0390114410010008450200d40207541c41504c0320440390b000c041d1100c105940740c420310802801503010601c800705290b103961043c0c00000c0b040b55100458613525620359a02500035030070030180310000c500c1490258031850201c82d0045807145021800746210308040380c01d5142010f0914000e402d01c0000101160180080c042c0071402d107105005061380001d040d0700f11a11407091030780003030700b26000c603001354000c1e4089643c02d800035102e054141405280d000096408480d001c0c80c96800c8410300042c846100ca04609021011035249030b03507400c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 739794451 1250 739793201 739793221
    0x222021e0a1704140718050a0203010501050d15181a0603070e1002070305070b0315011805010c0503040f080604030f050c2e09060b030c0409170708040b030405070e0708 74
    0x405501e000000904502240c10044c50350a80c1c0071081c003450540705400d407150058441801e60600d16900390381020081203901c18948200c078100d03001611414503100c46240c1d0600074286d0110903051550800100180d04420782850030000803400314001050214000e01c82c44907002098824017409041c410425615049450501030101c126420248006009401c83c41c02d42250401000790007401c10018281c035466010310302540a0701d03014414014441c0044503164411601490740e0880c08408000701c0d4016a0394041ea58014429203280548446494001640300da100d00d42952041c1d00300000d02d40d000505603000b411618085203032404071000300350b4802d46071020884814125802040c11400030250b90480881e108080c800c0e0f041a0074850f00524490303044502901a410300c080c00d80c03409104410b0080da1006c0394440014000c1e00035081d5811025084600400030440810706040ba4000f070b611a80c411030040c400da60800d1032403144140060542403c2c801c0a0f400c9c003c0d0551 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 739795701 1250 739794451 739794467
    0x306061e031113081c180501121d030406110a240219020709060f2601020f040801050a06060c02090a0e030d02040e0103020316210222021e0a 62
    0x384070700e00401c150804012490741403080c5242091900c1110400207040c1e800403450391420460582140485200b10006485043d0704008821140310102e10034082980255100b071210f03912003400154008008000c1100d140108442217880e900c003050802255900400c840159a004005051614059541c445150981840c45000c0600402e2690340c03501da603606a036898080620540051441654043d440346413034011459000e050000220b085002501208100e500c6c2001c03c0c1d10105c80b401003000c80000c2d103990005955000c000c6114409290380242c40900106c400000c0d9504214a120b0308440c0e4a5000c0d205201510070705d00f000d0703901d85120b1039020b80480d202069100d0f0f440003c070700317600c1a52100c3c0d0800d40b000c600400c400e00c0f80380105040c0c0780300f90225440c00000005030303202c800007131251605010011513551008040300303007018416440500151101194400c20080012a841813503241c65800b2420701058a03402d04410010441c0307000303c1d460300c4c101e40c9008001407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 739796951 1250 739795701 739795757
    0x1b0f0f03030c05010209060319150b070b180307141c09030210031509020d0e030702030c100c02042d06030201050301061445011d0d14030a030606 64
    0xc03100001680500200790101c0b0721400d00101510303235030f280c420529040380e0185194400810715100c59101980441140740c426980002c1c3c0b05401c1c221940e46200d04480001c004d225241d507a40c64040e05114100040c021542c4146070342c40043d12244000c3d403401c02103600c08042c120780d028071190703110382004c030307440940743c0544103048ac4c400c52100c254080d0011030503440301c612615100090041072035014003104080003a06200d0401c1004031a596801100790180d2305804c1070004040914001e01481e00c81074040c1480b5495540e2600000c1c216403480014071000d0b000240424410f521f120135104a40307503510782c100719290840d000205a8001401583d0500a52151030b01f04015080d055072103000c00014913402a00302c11001c61800c0005180d0504e5100025201c101c0003161092100c00042c011703511155490200c0031400c2e02c40d071b40390403a0f0303401149580200c0c3c04103819419205550501343d00960741c48411040050480d1140e5018008001090f2304c2607031114402c2890080c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 739798201 1250 739796951 739796957
    0x3061503050a0212070f020f070e0114010c1506091803080408090406090e07060e1e09060d02030109060c02160e060f0a0e04110a1409041401060f031b0f0f0303 70
    0x1554610b840c26000344507030003481c102c00c2e00c6002000b0880d07030b1005643c1403010841d03081da0b4003480349031051139031031b865402044811202140180050701001c2182000244145048100c0034441d031274032400341002d4415408240e40720f11040c00465218054402000c12106c00b110030146540c400420800010b8401444203034001000c01c0b1325510b40d0071070340241005000c204048030040c4416541c0b03d080344184070101e120358401c011185081e40c0c0291911303040b000c2c1d241c0044450010860000402001c0f60350005100001c030000d80c6003482140c000902c1f65400081c20303c0384120284c60a216100841c0999030000c0381417180c0449510780c2c94100d40c0c1995240c03202c42e440c000250f07018060703070000000c0c48860801c100078450030120464030494259100d0403d5515040c00a50600001008a4026a01c07001080c0001c105420880c04403035000c000080740f9850303020304220301034182d200369210120301801d01c3d5240e401a0140c80284021442d0041c0c1a02d000000d24038041c0500c405018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 739799451 1250 739798201 739798211
    0x606070308191d100b03060705071217010b0d0e030306014416090506162d05010e0c090f0702030403240b040e030306060c070305010203180d03061503 66
    0x61a03010381100e5510026200542450f45602c1501c0303541d00284061525a6030512030700003182d04000c9122800350700b855450520301171240d01d51050300e0303804007054801c005030b0091440c0c40b00380d12030b81a4068200c060507240d4071108060050300ba100d081a000009400400074401d103030380c0080118010300294081207520082074080d401415100d114a0386d1901020860910300d403074100b002d14850704c0080c425032900c0342a880111101000780c02400d400440802c85042485480c8510481c5903125000c040762244c44994501030f1101c600140c07039108004190300404115080c09000100801800201010412000060a04000a8a503900342d01502c2c0214504a20034411180070710b41000d40001c0c0c00e1460301c50382e81011421030603608928a070040c500038a203064010b401844102d0ba00550554850302c00300a001d0744000980352040c03150704000000580d00780055440b40105062202084802041c010300305084055002d041616011050194801342580c241c00381e00c1e18640050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 739800701 1250 739799451 739799491
    0x6050a090e07030f06050108070806010506030a1d0a030809101b1407141507050705120a09080f03030601030b0307030302061f1d041203021329070c030b0606070308 72
    0x400c16140360000f500d145410904c0005004450b00070f64101d0b4020400c484001d40e40348252a21800203000e92540b000041011504000940c0c000100010100700c90428111100c1d06207884d22560300c0d401c8010885800801161110522140306400c2d2182c105004c4c842000030310078407802007240c81200f401450030030640c81002c1c0005450000b64030042548400c01030800041d03865401c5501c3e1103104d80c4500000361810b200d803068540f1603503c10020610444007110100b0503401c80d01e041c60800400781000104008100452501b0402c15406180d980c2410b00006043d5600c0c200c0311402580002010070019500040b0140c4c03024200d40807945241a4a0110a219820f0740c4018403012000c2e04040800c04030300750042c0503610031581c40f02c10000c6600c1c240c0c00e90140a48a42945880307940402c55a4102c410a400035021818400d00c42d103030000421425400c401e5094424004001043c070812000021541d0801c01c200e5215062105c541e800414440c0001c152091442030160000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 739801951 1250 739800701 739800703
    0x105040e090a0803040606031e050307020108070e0a0303120e0d08010b0a0c0209070e09060931050d0f12022719090b0913050a0201050304150606051c06050a090e 71
    0x34810a903c68121a0b80341002c0c18150054441404162030700c0d0080002c20b0036072144823030342070b00451b0321001942c203043d8150019181c8042c0108014148444000ca4080355600c5003044000b1b54401e81350580d00f8040d0750701d000201c681d03072402c40280d0360000096160700e64000121030b04580c08986600e03034440c030400c0212220003071010000d40043c5900b0920450603042441d440c100c5c00243c40e8240ca681d40c010070442d1703500c4155032441d02c040e0003805480780240f05104140440c4e44207084401e4a00999454074586141d280c0a480064442070412621952033070526400503c0002c05508010003410030815201c48450740410381c64030843d03075107040c0c1c0702d0710070040760110400c41650009681e44105005031226041c114842c0c4408030015111220055035004030300d4005005104d00c54050b0b0066466130300c09001940c4c0c0c0b50189a4102c2504034a0259070007400c3c1c95030310b968590b5a800c10311900c001201c001c1a0300705040202c2032204d5110b100159080b2040d51001048000d880341480b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 739803201 1250 739801951 739801963
    0xa02030423040606050403110103051b072307030b010b0705030a0e030f0106080d120603120f0504090c021509012d020702030109200303032e0e0403020721020105040e09 74
    0x59030010b00f015000601560000c2c05841224001d0b00d107819202030f00401141140d00442e0881c0310601c2c0740e001c4003001d00c2280080c111040c484c0c041340541c40b0228858031004144030341101500e60010400b4010450350700c09049c0101020b500c01401d10900f555829243e000301002c90003002501007030341000f950100652001100800002c10110b43c80301040fa44903020302800601080340030168840402080c03103284100d0f9048115420114003280044035101036456080003002028000492210050300c0743c0089100f00c2e400038a500d1080040000e00000c0050004070540d2405010b220001c0c2511019040c10310100c108102c2a80f100003200000c0c0070b000c02c040d41640c40c1a8840080100e030640341c080d200724241021456910b10000c040ea80d20089810008a0184000045170001082d021b0340d01110900034600005031034218032205802c045400f40d00503804a101040091103102203030032003a0051040c92290981d680028205d0f115500c13640e01c10503011b1001070305815003030202e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 739804451 1250 739803201 739803269
    0x9080405060706062c19060b030106020109020102060f061c14010e060a0f1514030102120c030f07081506031005030d020a030207050604031104050402040b030102030c0705120a020304 80
    0x1540303420b100c1c205080184090701880502e10441103c545044200102d0501c0b2050961041c60544e5901c29220300038082a00f5a518a140c8804011847c2d106810166018021560001500c00c074540002468103101030507a81100160070240009030316400072078290f0306507001c041d40c008810b51070b2140d41a1100ca09042241d4130703200711080c40840118504d4007404400f001440044510007240b400c4601d41c104400ba510628442042843c000400e40070405500900050408062101c25101c0903401c9601246034800081006400041240016017040f05450103600516221100400c10351703504541c036126100102c0011611040300300210098680541940e12010f00040007035036881134802c080b000760003240400b25081c140341c0199400c482e0031000c80040d090444003407000505010300705981161705c8140365405900c09000941c050b10600701c6540c2d0781c0502d810a0b03070420700c90a000114540c0204a1049040e6000081c3c605440a11030070004801c500300498800041380d840c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 739805701 1250 739804451 739804459
    0x10f060c02152703151609030501141e0727121a0106020c0a0b09010c1b080705040b0f060c0a1502030a0605010302070515190e03030a0e060c0d09080405 67
    0x190004142c0c00c0941003000c1400c200f0030404001c11010101900c034200219628560a01d0707000040a26510600d855414202e0741403600e840c07501c988074070782540d19010b2161041e040a105001c150101c03070300303c140210400c1103012401c3c00c02c0403005000600c44950946039088064610103d22151405100141704a150400c981d100c245000c840040898804440c002c40b00c000010301140007052251700740600410001d891030400100040c560400809141042400c620071000502c0078002c101d043c08030700c221450041c1c0b038a4040c2c0d20b45a51508042e004a0401d84c0b050080d4407210f031440c1059104603812030710b81c18a213490a00d0288980c4003e4200c80402885180040140c3e00650080302c1808040c01303082e85642c0150700b0303441960002800b5034024104d14242c400a0081503800c03001d12400350044003082c0c501c05084c1ca014000420b6a5003002050201c00010b43c461501680c1c0007401900c0d0502e0301e0b02d1008000c0c041c0718441c005c0191980015010412440c049602400f4018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 739806951 1250 739805701 739805707
    0xb03040606170f071e0305031b07050102010e030306042016110a080606010f02010b0307060207090e2a010903080d1409061b0c330f010f060c0215 64
    0x10030060050041072191020321007181c2440a81000c001c6240c40c0810305480041c00461700c1d020b011041d4451020142100e5102c1c0000880010401e0005106800748041551480100903914500781036455002e14150380c0340541c410413181d404000d681e4000740456000030090540e900040d0702c41210f50105c0d5910200140c4d40360350b004013007070441805000d0340000100882c18002d00401207564082e00c0b0856100000040240d8410754052134003072501e20000c00c802203002c0100e46403510f02d402030030140e0040207080c041111144038000d580c0346043c00901c02c00c0e0303140c18180c8414041909000307202c4002c1c0e20200702a4041c20003540119800081543c2d1009141c403108010013820171420302d50604200410403030500001c0081c003509402c880a01004001c0e5201025a80082010310450040310001070700000c80c0c0f81c4444a81160440788107a50308203900901c01600000c20721120304c510040107004c6e4010500c604401e4901c07074100b000d220121400000d981c10039805c01c2c207103002400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 739808201 1250 739806951 739806953
    0x60d06090503042108040e090c092a0901090512031306080402091302090c0706060b070f1e11060c0309040504060e191e24021905070c030602130b0304 66
    0x801401101c60180c04141081001901940113007090307980a806203006010900c1030b0749138181c007907400040c0b0744200d4015141e41c20203e20359034001c890b4440c5901c2c21070120701500d6101003410720404c40c109042850113840b07600281205056025481c041d004d1034000b424a042e042088a984014204c83c454060355135040090103d030b01114220700072200040440c00d07a41083c0040f0300e0749980100010b060350b40d0880a5016500b0a00061b00c15548480e000640701040e00c000340b0202d4024140e440b80c802403400c0601c0703000b42102d40f40c443c03100138011a20102d0030303d040304008081308a0f20641d803041140362a03440c5001e0407407e0b641c41032401c01444100031095000032140d42c011070980740c411100e80a440140c031100c1102800d03290036100140300080207000444002031081400002d0036038211403501c60102052601007a056002403100180200348a80300c6400030580380251810007191703184030f4a0082848010107003034004c03503004d6075111081030407409407002040da19120310301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 739809451 1250 739808201 739808203
    0x111509031507020a05010515040b09090703060e07030b04050a05070503060c0301090908040b1c0c02010b01120b01050c120702030106050a1d0601050915120a09080415051303050c150a1403060d060905 87
    0x2c090481c9100c0c41c07a2030400c3c902414040bc41a01c1040210050485280303103468034400741101640180f007600800d0302c0800003801080005019a0040c8020f001444191502601c9c14400760840362080e44803c003008510760440044a044d02c00d5140c012030060010325002071030f4000c903004001c0164001ca40d445803458071061645054042c110140500c829014003a400c881e0711488641c0001d4041817442d002c0b115980194207010b9041c5172a62400c0c024600f46804c00342d079011400d0007490006500025450240940030103407004444044000e46045d60f008200c4223b00c0c400d4861101240015129270b02610940706070700000b411036545254003403001d0986078466280c02d08414484004500c900c1031501c15a80c01c90740c0079a0f01c0e4a01810320619607526000b00c42c000040101c20020030002c0c901002552000f107200300001c1c000541c0e020701700b14010f0381580020064040c2808100e104036404844180380c1031600d0f000586c2d0351120008200348181d0000043c0406003441c0024082080c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 739810701 1250 739809451 739809481
    0x5031002030a0e070b1b01090c240f0507023a0501060506030106051b0109120513090615081504090b0a0c03050702030d1e02030f0f1023010309050a111509031507020a050105 76
    0x5440202c4062b403800c0d14290382031b149420700320780001c0045c0300c00c00050034621058202c5484211100340200340020700d114618140c0101c0c60b100c10043c0c0142d9081143c01d0281e00e0103440102d98490842d030401000801c80c0c0180b8212203031205038030340c800b07c00c10f01c294006041c0a411484201400002200c0903220350302000c415050140c1c42000011448050f22500c81a00c50100c0c03459840c2c904950308031415840649094900c8400d0040c0124542d507501c944a02c40d482020031040610b42000170901b100c26502d040c0c0b0506017068100702c045a4040200c0e9040005a030340011003145100d0010b40c0c400c103440301d03c05424400820b00220b00340311103c051044d640c8544800950760780c0d00f035240442d11244114500c10494003040d25002b03405c0340541990b0310061500044106d05511220315213190454103840c449074860340242c2900f88081c4d00c504aa90030002549031910031000b09a0320400b8190203881c10041d03601180c50302c0d1007881030f81c2c095900900244420305000e407000f94404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 739811951 1250 739810701 739810739
    0x6030604020c37081e1902010f0e060709090203190207050c101107061b120f090f2304090c0608010e180c010c03030605031002030a0e070b1b01090c 65
    0x8842c403200f074500410000c0350400d02940c8800758506003001442900b0032048501840c640d46042484082c100068200403c0c2c0480506d80c000b2501c20041121842100c031078240180c5650420002c0101c0c0720741104108040340d001880c01643c0c1e03541c03a15000c41c0030001100f80c1d4811070000a0f20f405005002848130b20031072003101c000e4409500d1f00f905940c8015404101e040c1c1d500441403c0041d94020345d4100346055440c01300c42e004000c0f03a80d882e521a0000c086aa0102d407400c01c042c1402170307020607890003a00400b0040c041c00c50030900e01d051340c00680f850b410010751760101c417100192901d4100e0400c40794030645880080351543c001a0401c5d40900403180600e01480000f100c804062004e504991150805080c0d6103000500444440c100000c0070307003c1c151901000101f81d2000c100d064000500c00d000144c680c01e1054a000546804d4003c81c1059404108240700440003401150340415600100c1240c1089000e001e60140c500d4000c050b02440c14201e00040100e44589400210 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 739813201 1250 739811951 739812013
    0x11103190e0f0607020d06050603120d020a0206010e0603370c140429030a0c060306080f030c07061d100806040c0f0f0c03050c0d051b120906030604020c 67
    0x3681c2e0074000d2014902a292010f0f41c400311a046403030208403954003041c2c200d170b0003800703440088401086140c1607a00c12011104070583c00141500030303030b80c14003800707016200b410040012801c1120019590703001160170610942d004000031403017184d01400da00258410b9030003680441600d0b041c0a80c8400341e070f00c11030b4640e15410364282590300d00341c8903100b68501000a05942105c03820090310210401c1165540c162080001100c080f130b00c94440340d4024803260b60003040311410300c2000780c1024a03010642c007550f0300500c4070643d80e10340800c100068404601c1c090141403c01c00c1d1b0f0b22940c44600c0c9040c0d0b0840080505411841e5028090510a91003944c0c144400b402001c0121102c0090b012984005070456200c841c2d81e0384542c415100050007840c1030307400c200e21502281e003404003070240c4402141d070024605401214103410b90b9605901c0c02c014003045890906602d14510590800510070350000000031040c4e501c6234103980c40f4034101400c0f14840030182c4185103001c402d0004042e10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 739814451 1250 739813201 739813219
    0x220501080f010b18040e060405061501090b0d020a2714011e050307030e060124020d0206190906020d05040309140a050d050703021002030418020a020c011103190e 71
    0x30600d142c0c1280d40c3d04122500e000d0300c41d4000306140c0e10718820503a01644030703c009102136508004c1c290245000b0005012541007001d2106c020308501c40c906814014084002c04c1034201705c04c00d84078030007000c0c04090384c4d031814040100d46508041c50701031120880001014581d000101080d425a100c10400d0a209103002005540c1c0140007811050310030000e400d8030680e03e1040d805981c00401d030b400c01180c2c4010300c41600d400c120b0243c00c41074009100c56450440780d0003050104d1381c1d00c1060f0010b440100c080300310081d01c8420051003c802d2282040c000081440c069015056441c0c201001319140c40c004001d000280c10300782c038194001688884007050f131101400d206043e00314010038006600b480c00050049116890f1003e6500e40100007001004d6107034000e01036005101680034540d52400c00c8002643c1d03502103040c03080c507a0b2060060850300344c5c00080c0c030884034209080210034400c0c0000264030314842c0c1011172002401f00c0c24540751060f040034526408410407219000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 739815701 1250 739814451 739814461
    0x180308030709050a03020609040b0102011104030809100f1205060d0c26010204080703170904060807060f0203070210120e0d0e0a05041505011b05061302040507140904020f22050108 79
    0x2804c0001d90001130352200b000c10010072103140542c0480c45610040c000810031100c80a29401c3e650456070054030400300009102c0c5140c50003100c0251949183d04060a04006a200080601071101c01203081d40d40d035000811810386c0c490003100340c02c039032004950301050744403d83e0480801420020000108020703072500c101e04010300940b0305444084004100091850b100d6491b9080701d80802c1e036007107508102101140d00c81c4d01030500030f0800c4c103004200c0780e468000c00408520320143c002085410a01034100140d0310700e03807114009400c5180010b404180c5030840d00040c05941070301c0d0810310400384400720740b9810070942c680c030b15421541c01014954440c1800185c520100d070100040c040790b40107020540c010841c80001c81c00a150102c0507130603036600d40303180c080705858040601c8000030041003140340502600ba8807048601d00944000740000845515014400c40b076440b40350040340e850810040031098450300322100d24040b00c00c2030450181081140a4000d5900107584000003403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 739816951 1250 739815701 739815709
    0x5031e0118120e0d05010903030912170c0a0509040c020c030f12032d07021b0d030801051e0901030b01050111060907060e150711120c1804020118030803070905 70
    0x7419003141c0c4054031185900c030100c46010301010f2042e4001c15080318500450024400c04c10514030989000504c000a070070009041c80c2c840a41c441048030080364108201d80170021150403551107503800e521075280303070700030f80301401501c2403d50024070780100904a20f0340011044c60401003a0243d40c05010f5014810742c8658194011403080c00040021031450802009a081c10801c101c0d000307040190408030843e81c4a20940b00d650060340401e1091b4140d400c0710030210300b25041141d185a1902c26031382d0241151205114a5100c1d02103100d4010002021700c903e50440e04e001011100c0340d6850b407074a4503050100380a00303400504240300744103201c2e42c006045409460301200070244940f03040300858020100004054014650182c541502d0b40450061300103607118035130440c84c0c041d508040c8515804e4028449406034003515055405442d41001650684030b10448039565941e82d00069031011003030005507103c0d0348002800002d0080d03002c00756024070b84590b034980304517544c0e800b00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 739818201 1250 739816951 739816991
    0x12070306050105190e1506040f150306122414090c062b1104090b0f01050f0405060d09050312040501050609010e06010c2d0213020f0304020d0c05031e01 67
    0x111000c048244018001707001034000d0207a000d03104001124850418902143e0f503904940c1c070002010360307629010300ca280d1a15009900e11161480c082191a2034500c04602c0c5841050b4040d000000100050300001d0101210300b410643c0c500c014480c0083d0f196000c450b40d081240c4e5842240600c40400b81030f0720f000c01c1214203201c0441c0d000080b06170fa41c3c503000c0c1c0420020034625080d41c2d44000aa19180504001e40000c107588035000580700306000c18401c18030b148a248a0402208001e05429101c0c8a001d48060301c3c000c1e2031554640c60b456207860010b005170f0501401500c03000c900200700c4950705282d988103d114000900c415221442480300c4c0c2c59080c003030200c1c8170509000003925548a040300c23070034080c0941410408519050124030901920003080a40c03034500013501d0b0305506000352440d038061a040c2c021031400704007002120990102030402441001c07100e5030300081c00303114604107000d446d009081d152412081c0c0da0701e80c682506104220215403e004100d40010b03501d01ca4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 739819451 1250 739818201 739818229
    0xc050a03020918011b0f1101092102030f040e011706010f03120203070b100924031b0b0a12050115020a060b0103141017070312120204030212070306050105 68
    0x101c41030741d01c80800110f4100d242208081d501d41d42c421030b818a04240d08600d00120f40c00340c5501e041ca0b0611329006103152200302d80e20320540e045c2841783c1c00241841c640c490050090480010b104e60881c0401c0341103105e49401134003610000704011030300d2411000301d0b034102d601e518003912150300988503458075040244100440e503c0301ca0070400101e00f410f61000140b0080c5d10550740380010b00d994000c0704410030750340c03000b0415101c001440080c8d4a80301d40c821a0451382280003140001514006410080e4000100321481c3c1480b0040c4180da84100315000c0d00d013900c111501c0b80c14140005000900c02080200100c4c10800001522490565400c010b0440c0350b010344100241070325800090a03c1c10303400b504055031091a284801710006d985401100501204407070b0350300d0715203e08c08480d01035107810b609400101003040041c4042d0290b01000780a820050034580c8003c82940c020f0084d41d201a412240404454481c402e003c2030803c180c0c1d01c01e200c10001a600c1e0300900180383c2e08020 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 739820701 1250 739819451 739819459
    0x1d0d0c1e0303090b090f040f1d03040e041b0b030a0203070e0f09280230060105070b070201060b0301090c02011125150c052d0703050a0e060a0c0c050a0302 68
    0x41d0501c0765262035801410017841c0038045140310305034600403404407020401d10003202c903075450003190304005249140080340c010100450a02d424502102000c000c05800248110b180c03514510105103240c50358002050740750f0610ba203038500000070b40c000c0c1d8011200c0d0070004810040e2401d03940b811030014450100040c03c41d04842c0d0710204001c101d4440b0316061a50003942c0003444114682c180000d01c62841c0c0701446003503143d05000000550000c20840c0e501140d084001c11010740d1388201580c000c0c84c0c000c101801c2039200d07444142d0040040380c02440c55124000008680f0300e10b141c00a040c034030217550003000701400c0d2105e03030102d502502c01ea030034000503044494045504944a00315a04d4002c0152a510103c03402d500c008032004c98240d8404a40c001c1208505505112280301300100c2012010300f2540d8611000400e034410030800505000f0085040399110384500500e29840b08090b181e0340c3c4c0e54038241c1c0050304005100200712540c0d8500b030700c01300b610306020320620220f9a0280c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 739821951 1250 739820701 739820717
    0x4180b010e0912040b2a160b0301030206070210030905060103080c0d110c010507110904060b03070603050c0306091e010e180a0206090d08070f0c14030309010c02011d0d0c1e0303 78
    0x600400c5044c1d00040030101c05a03601b000d05031005540c4100c01129455042c001c00c030704a0f51140c0c880c0355007003951001c58282d40c14001003000d615081300702c5680c1581281c406c1a50031441030306a00508034108017500611520b0008402c2001a01c01040051001c3e401c548a0159120044aa0700d04e03403481030b0b540e40c0048101c0c05003540582c0160206074401c680d280b1040050f500425a004030442d81500e42c83e441d2548030f0003508090052901901007840c3c00d1007145003640e4140c071144005000b6a0081e00d00e0f030000b9801d07968140c1d0102024507290692903a659484141900003182903440c103e00205c80e03034003540d91800c0003420104440c0d0180c516800e005a07041001040600102c09956140007006060700180806080c8a1040d06c100851000d046c2451035000700a00c001d5895406640200700c05a8581c0e0481c80d110002a42407034036040c0c0021a02c15580c050503401501c0f0f4002c4280c2ea504408c12000d407600005407030711400c00212b001c054481c404020005d9100c0503010032102 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 739823201 1250 739821951 739821959
    0x70c06050a1b11031c1506050403050c0913020603090a05010506041a19050a080102070506130b0a0507021903020705030d080705030708060d02181009021306050904180b010e091204 79
    0x62440381c2d5014920f50152801d15031401c491401524070b03413030681d140590350f403514603103000038003030f0000505150310300301d42014115031b11599600c0f10200c0407407013007441c01d00040354a0850401d080b802036005e03024980f2170614a04c900d50700d90416008070342039402c0200043e00d6050620903034050083c0c2400c2c86251500b84424440d145204000f8880c550501410200b4035454181c5203400401c404030005035a40990708015041940281a008030a0184501d45010445050701d207034014456038000122070301d454200764038102d4050454141c050108024000781600466000b0840b5810390503601c001c2900123045541c0340b4102d640350701140061010800c014411034210741e00a401a140c11220201070f00000c03e96204010010500d0440c0c004100400b0403918441d0001c0c60241d8096041c03150303210381d50107980c001e800b685041040104000001d503499420008125001c48032003407440041d410322408030b030000d0060146250311a404550f1a000001c1c07401d805000c6d40032010304142c14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 739824451 1250 739823201 739823207
    0x60819050601050d0e071a0409060602120304081308070618080705010503040f0f0f0c1707140103090201090e01080d090e1303111609050106020d36030605070c06050a1b 74
    0x15800c40106910a0140201c0c00081c1c0c0c2c011f0103180040c02c04070b03648030752410100c0e07010f440554120100310341195401078030341c1d0341d84815a0342007580701c01c10548a003a000808014114240d100f40e08501c1011400284140c125440b41401c107240f00111704995114008a5134030b100500c603040c0059810800100402c00e0074844851a52043d044605414000c3c0c4542c10708a40c00711003519074a100031002c00068807003940003918844000c001d404018580300d5400328a40703000c917009040c503440e040d101045a10400d00c02e00a030180d0680e1400a50f118026507a9403a00401c010340420100100400e495030454980c0c1d100c2d6100c0200301900f16009d550481c3e9110002c819000c0701c1c8280700340e4101c000e01c151a040054480c04500141962410900a241800c290301800a000202d0190341c0f0f01107007800d141a04501104201002002d14103021351218065400034020614050505c40d030142d00003c1c0b141480d004180c00c0c05a0344071070004008030303070351455511201d80480340c00b1540140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 739825701 1250 739824451 739824461
    0x207050904080f040f091a100c14010b0301090f0209100f030204021c0207050d080c040303021c022e06060908101e1404020a060915080c0f04060819050601050d 70
    0x6800c004142090341d07800751750462013031315001030719813a1f120000b480220440c040240200d540441e02030f6000000ea1601801d0019802805043c00e503240e42c0220700350301c0075000000080c402400030411800c460400104035490800c0891081d503400000c2051216294070683c15140ea503540f000c102c501c0c6500b000001e50180c60341a17200d0b4403000e0300c2500c950051011b0030101d4054009490510549040200a070500a00000f01010248024404070b5400030b081e54038442c1904810b403940d0032100f8142d141c40310000c111300200380b1010201c407003800d8101022049110f615014400c0320348409050703d000c907240c011420180e01c5040c1e29510f00003160482036a030101070214824040240c0c0d1094192201c4250300900c0020000074031046042c030f031500d0070040040d86070603c1d1b118241050003450a120301c030640700700441d002c04101d0700782404040715109862001421f550380c1c0c4d40c000140070500b0885015105080140c40380c4414445c81c0500c600c0b0381d605a4030546480220315075040181 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 739826951 1250 739825701 739825717
    0x30d020c041b14132c0c18010804061508070608010f120b06040908041409060306070c030807110114150307030c2c01060804120302121321120c020705090408 69
    0x290500000c0d05c40a003a20500e1910998126201603c0c24400c807140b500d8005411444a18000c10620043c00e8840b00304100c1c0a0302443c0c4070741d00352205e041c05405404609581c0810321706221000811580001300e01040310030944440340c5903a0303640d21a035101000362084804982c0e03184a413030f001030203140a2503440540140001003512003038440348001e03001a0041c0034141c04a000c40030f101c2c600b2003560750b400403046004003020301d070080c4002c205288a034001014003062030007140d01503000710501003000311140000c2046140102586d0030b541c00645104040104c880e1040140741030104040c0d080d039410a030742c030107010b1030054052030b00300c5800039000602000480c0c80010451500e0748034000e00340360380c607a1000e0525050108180b0343c82d20041c010f061040044600c0511455075403640142c040d45011402110360415440340c107403007425410381d2002460700481c0305410003204001c1d00e81d803030410860340b580c2e00d0090340e86404e24084c969001102c3c40010f80012569001444d880c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 739828201 1250 739826951 739826977
    0x10f0302120702030405030f070b070618060207150b1816020c0406080d03110412020f0105070602160b0901060f050603040804030210030605010305100b1c0209030d020c041b14 77
    0x80c12850204030782000c242e0700840182c1001a04028a26080022a080880d5600076000d914a0542007001a1044001c01000b580e100c040d40548883c29040043d000ca800280c1990344036114948100074070100303075a4004161500d540b12844c0d0405440c1c8002070132844007800c50580712a0081c0f6074003100400381e6070440c0b00b0740303503004160f8560b406050b004201e100018000d010800b003019055412401c942403103e6001c0c001046944800540708840540564541c0e45d6104e130000101c403580301e1504054030306400023580912800180703201c04200c038026043d41c40e40f601d44c928454240c444601c00c0304c0c0c5604070842e00384082e03d00a401140c00510804100f80341582e42c0c1e01051010039a00c1e000c03400310360343d0720040090756090f001c0c980c0e00c04050b52440200c0c0b030421a800007503000d464031000d4000b607000005081c140d180da040381c0032000002c040740d220600340350000756039030740004500c5d00031800c07c400c000041e1214402c200c0da46600b516074800a0394010250490364200700309801030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 739829451 1250 739828201 739828207
    0xc030c0e040b030c120f060601050f040e060109120b07080f060109091119090806070e091603060503010f0204211a10031a06030c0a06120f0b03010212060109081b010f0302 75
    0x131950f1045000072100c0c070450090980101c02d014120300b400340041c9a1414007604001036200351850408036000d4030720a03215034025403200c1c03004840b42d09494002034064400d003400c2d0824407025500c541d104178001d90390340c145544d902c80100540542600d01e640800c84402e0140300382000e45e042401c54043d0020340c035060a0411640d036041c001d6030745001000c40d58409051150304024414180d00844d02e007008024266000042419084c0040642c2012075a000c40410f08510070303040319000f807500800070300044035004a02802940701e4840d08101c9100c4c2d910b050604102c003207200f814244c00aa114010840790b08440d0410700005090303c000040600c00400051801e1014601c860b1402030100707624600358041c140f4244811800311b06c545034103a020002e00758080c0e80d041c0300300000c0c4800b07d609120140365038090080b6000b166032650000c28000c030548484800b4070701c501e00036a0f4100c0d465a6800d202600d0301c42c2c4110702003101790541056541c9500070b00080c85041d0b190310300185 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 739830701 1250 739829451 739829473
    0xe1623040221010302030d0806030d2703030e0f090405070e220308010f0b0711010e15070506061804030801060c080d09050a0501051806240901030c0503010c030c0e040b03 75
    0x12800768a6009580b6420a000041c4194103007001a55410403150030001c0c1c09080c03090000f42d0b68015691f0040810503146034983c0041c0c030103140c041600c40085210442c6641340d24001d0405100c1180c028018ac506480400e5103103071a802243c006c90308400601141400c006c00380f0140100105601c0c600003802000000041d4500501aa018000d03600e40200e03504001c41c10742c0c044d18603803049154203000e001a0f0301040e1540c503260b0a88009007850a4400081c1020035840b20300000402501040803600d6012f1150116001e03202c1d100454044441c441000c01580007403600391005000600014014401c06008031055803110340a803121501303048e89000f4281c16150354510459068011100520401c03509000704c4d038018040204405442695659065403000000d0041041184c5081d400385001701c21107003545249800303440e10b030003507840f030401c1d121528451003072900a42c40e00481105243c4a0303c02c3c8450450240d0701c0d10000c078840b81c1000b02404440103110f505020f5055426 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 739831951 1250 739830701 739830727
    0x18061b12100f03082508090d1104090b160201020708120402010c0c23040c0f210513120503010303080402091905130c080a050c06031b040303030e16230402 68
    0x240042d4800d185007a030b14550f094280142010300303001d21550320041051540046c103100c00740c42c076601e0151030100386010181050100c2c03001026289400c40c1c6405501d00600c5012080e1340d03c102c0f0f200b01e400d0032829003804120b00701e20600750302500c0c101d41840010305400d01c4091880c3c01900525200e00c5508080e110300131150955400a52003150054181c0c14900c3c07001d0400303040c1c0c44102e07800c0201503170400000e0917107164000004200408221b120002c0c4500030000070714200d81070b03070400c29854159141c1c0050340100d901a50740c401038044150405120f8011a4140d0307506555481c01d6865a80c00d00c104c05030090320440300e41440241c0500c107045184900c1d4825580ba03c400a4002d0b070a080c104441c55084e042080640c02c012a0b840c0410070000e60002d4681060f1a840c1c0d495940e4444010401d030264054000b040002400005045d0706411107403a40d450b940a5644c060f130200c2d40275000040c14410700c00080360f0074902c18842d0300f0b80d400044600d01c001e0170141c0744c14002c0c5829 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 739833201 1250 739831951 739831979
    0x708010e0c0d0617010c030b0a05060904150e06011b150f1806020306131b080601051204050309090f06011409060405030a14120c0312060f0918061b1210 67
    0x144131040800100c0080c40303090041440c100c40701d003020845c0000c0c2c2808602280024042d4034003d030703000034000041ea19903a1051090301108041084c8081d00c1e0841080d0004090356044e0000b0902e209506a840d908081c0a500940c0100306248480f080c4a083c00039025600d08607410340d9460600541d00e4050f00064403441d8419880142c0c0e900c2d0200400c054140700c800a200d48503d0405840951000c0307081c030750304000460419031600d03602d54004030b13031074804e14080403c1d030f6440e5001d00081001c00805400311071400c40d80e103205036440482d00c80c0802c1e02118401d00155070810700300540e011210060010401c0608220301d01a04c42001c03078501032020104480e800c000324440e100e80c0006000f0110001000300134103161140c0301c940c460307980c065000040b545003040c40101d1203a682e0000c1466400320041c08000c094074100b41e40310032200e01c0c0c0098031624024840090a00c0540c21076030b464400210103040d04100003144180a4040e0040c600d004510950001040d512080048 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 739834451 1250 739833201 739833209
    0x402060706231b04290703030b03060c03040f0b0912131509030c03030315150807110705030d11030f040305031b0607050d09020a090f0c0e090708010e0c0d06 69
    0x60340011040c03071580c82024040140240440c40d07a0600011040e01c61401322400c6510303402020280d000c00200103803600c484d1014600400e04001170500402d50150044c5070914411816a0520750f03900700c40550505c000c0710f00401d15601881168001068000a0341c1c00400300c600300c1d05039070140a00d402e455803001c005d003440104800030411124080c903455007482d142e24a86421030625554500c0d04240d15804000c007850b888071598500b11321a8081e110007810f001c4000059242c1000300a45101001c0c2d41e9200040c801c400c400025440004000046038005401003030b0b15805420101c0703003d2842c85600010340010483d502211250a0240c409903000390301460b518010440350487d1046c503a030810301590404801c0182668012003990f445061031540454084010310001d03034038140e10b8004120a41c6040d02d8040300300030590149140341480c2d04c0d00b5507032105840800c01d60000460303078180040c03181401404861103052149410030b1402c044503050003521400300e0159050303600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 739835701 1250 739834451 739834481
    0x703110f0c0a020424050436020a031101120c09182c101a01030e01021303150b04050c0702040c170f0a0513020a050423090c0a2c0402060706 62
    0x2c0454224103190305d803140100400c590412a00341c0d0844c0d03551240c00e0828a41840018690381301b2a103000050761034500c240d00502e2380954603280d10708041c4a0f4043c140f1940000d070711003112594004584038080031400c050319024403442c6040e00c000211900c40440301080d0f03448103044c0c84072400c58500e4001c0301e440740121003240c003000105c15241c00b1512003d4a02e49042642440c040b00b099010511520710038a0702045101002e4400c03406845070b55402d075060940854004240a090304031a0291001075005000000c03014003040181e40341920000346046007001810300620741540712111064141c00d02c89003040204488600030302d070807100301c3d80300c6c600c00003000001e803001e201e4190300c82c1d42c100720144070034480e4000c80c1c01ca948500499005960701d0081640341a440d440114a040322011000110310b0802403140e181c107a0b44014501602880b500404c200070780400d9004520900c41c1b9030517a8030000d4501c0d01400e00003503c00ea030001c008001480106100d40981d00406842d50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 739836951 1250 739835701 739835741
    0x703020f0d051b040f0302011b121e030207080d0207050c0a0306020901021606081f0b0a05041712030a020d0612061b09061715030a15050703110f0c0a0204 68
    0x4007034495854000110f20ba48800400013070080420100c4442c1c20b980d02817034281c60b4044900b42103009060400d00103841d140c440a0340301c0c40c00382d00c11210f400b000c4114403140a8001d540b0400c1e803d80c080c201e00146540c809000b45c900c1502c00381e0142c2040b034007410454004551000100303095038129003040c3e030b1079500090000f9507541c0400c1500340071314640b5a503003405490014004e00b2004042d010003e01c100c0440c5400f8041a400c2101c0064104d040d01607a4580c444000904203510501c51000c0440560450a2407001c3c0460307400c4400c007422545078515034900300d003000294840d40944241550f18100484c60000c0900341c040b2540c440c800001c1c10000122044c10012a404c5284042251280040c81000d6000b142291040c1d8800580c00302c1c0e8076802041142d051001c088182c0500c1100d660609020094400b00d01c0030302c07010b204101607122620200e003a01c500422110900c1001c01529815454281c010b2402e0003080055841c5070110707500140c00d450080c0081d01c100d034040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 739838201 1250 739836951 739836961
    0x709021c05010e060a150207050a0807030201121413030507050312180a03120e0f03030a0504030909110403080a0e0405090f0d1b02042f031b12010e0703020f0d05 71
    0x9842210b024002400c0114070515005001a410011600540f400200d0304540c2c00c11690082007500c010b003200800d2025010340721070307296a071003207503200070703030001e002d0380c00e01c51400e44140f140301a24500540130003150740d19050300416038492a01d044041010030000c0e00e0100764244080c001518500b0082c00c5c183c10909600e80c20410560b011086503003001c1090b000113a0046500a1091105040483e0700348040c030b82d040c00d000304035402c106240000410000e02210943c003491040307101e52901c0c00303001e4030383c1d00403403c46141c4130245481540402c02400842d0000b0003500032071005140074001c0704103000120701924016240d1004070341c05260038454114052000704483ca042d4039001003200c1e60342c907e2242101080f54064040c3d652840740360148a201400c289490009540c240480e000c50603401015510442d114031184029560411201e2500c100302d030b044442c181040307000369090aa400c0031444000c0e00e9001407687c01c00002520094800180844210390700000441d8502 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 739839451 1250 739838201 739838257
    0x120c0806090c2707110f0106080109031b03020705090406020d09241a060d090503120f1e04060b061c0501090513120507020310140412030c170603070902 67
    0x109810081074031082c0364000e00039043c1500041d92068062810100448900503000c3c1490001804024254203145000c240b18030150401b6400c0381c881e6032201c480c0210003403000c08000110000800507002513030f08110b02e1a00f9404903030002d01850005203480c0540304002d04517056100708031412034040503203003a540c5031364002c240c00060000c1c00f8080b01d02c130b0401c800700f072861103004244140c1d00401c041407110007643c4200003060b44401200c0c0e44241d4444840c0038904121041e50790400c407040014120b0000a49000c0c2c503441051000070282c071a035039528080c1107201181504044140200507800d0710341d240d818a69a0010000a0300e54101525a020740b180107000440c6485c410720098001002a1080800003001e8588252156054400139013010060b40101c16140d0410b03d90040d0041c1c00a20140224030070b1181c10208103808000350159843c02d40c490022442e00305191808010780300c80d1960105d0010159030405440d44200001c81c3c00c0360084028840d8859900ca82d0061 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 739840701 1250 739839451 739839469
    0x30c0210230a051003080f09030a1a0a0204030f0809030c0a122105160f020a030b010608070c031d0d0602030a020406092310030b0301050406020d0b01031401120c0806090c 75
    0xb194000348400c1c600303440c020f61920f0303080c44014103000300050740304481701082c0152045280003c0507941c0c078001500b01070140b41c40e5040e404170102e204401003810090103200700d8084943c4604040c0c1040d009807074a0346c45412801017140c16010b00c0d50707100d0035640c40030007040c040c0a00c0d242e05100c0e54014208060300e8000c070013040c500750800c20300c941041034208007035440e04c407003c42c0ca00d80c00c1c0c82e00b490201749442011200942210303030800040100014481c070036060341c6143ea80e0100315541c80d642111120304980000e0b02003016a80c1c55119190306205802c02c441010703020003c051590b54410382247e00880300e5940c113a50100e8240211603200000300d00500b008040c841c60300000701e80000d5072041c170400f40307840303103500e0360843d20814002d402491220710300400800c5946464201600650320036a29160458509080c0e08255030280c45070340d000d41000a544085a030800d0f408800d6030f03043c002c1c2034070603260000c07001401ca2420030041d4801c04281c00135151083c164000d01074800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 739841951 1250 739840701 739840711
    0x10c020114090604170c0d0f030e03090a03020f28030204110f0307080a090219060206010b070506011a0f180306070903081602010e0a06091e03030807030c021023 71
    0x1c24404184440d4020001c2d00b5500701ea04203d4008048220340d00002e5540b1035050101c5483c0103002010010a40215071001c60344946d1b00c0a0000301c5001ca10b440c0c0b40c1c1b0a00000c0c44c4d10507207800c4107201506114003040d6003410060400c1c01c055104076142030520740ca000346030601007040c00e02841103007003c0c003a801c2d106498108442c2082150841c0c2c1d841804010701c0102000005000100244601e41100901c5500a820b4004c80c100da80c03401070600c2c0c114003410b40076128600000544090240895180d5074011002d440d0751307400d1200301c0507001009000350304014024460000a00c4491000f0805181c0305031041c64102d5003041414103181c802855101030082c10441040456441011545100c9012844220983c0b05200580c0d01c442103859540e004286407101044e200d40290100003680c4045c0d4034501006158150554040e0306030000a0004840302d002ca954240203402880400c1c00790300694007106840740c1c2040841d941c2c071070440e201140c510010b1442c40302c1c450300c0c2c54000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 739843201 1250 739841951 739841981
    0x70c0e0408030a09031709060a0509070b0a050d14181504080d05071404060207090b030f190c0b0f0306040b09040b0c07022b0213020301050a0501120f0c02010c0201 72
    0x10314107610369038040d02000b0500e03800f90740c44028600c01c05202d10544100800601441442420407480c45591072000b141e0600340b0503d030202044014200186000483c1c07500c00074030340b400303854000072122600460820707000903840d0b1a4281d148828142ca00e4030846403080c1080080d1610041d05143c40000003111101e420800d050101041a102c02c90758aa85494800701d5140c407159012200c004101b80b155515940210300441c94070740c0414854101c1d44100002c0c440003640c1010940c50f540b000800f03040650050303400080b0481c03800d40301c0040c14000c2c41500d0409a450341b07034080e0f50740301500c4182c0c0703000c0000130420f00345031500c5501c1b0285000c1c0c529004a250a54071941c81503805000c030706251101048003011541c031041c082c402c02d5900e503c600c402c91005100001100050902244145442a81c40d8001d88107442a02d040341e9004103410f49840ca40401581e0610120412403110b03a120222007212040b503004030702c030080c5036a0002500418829000382101e40c9000c042d103c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 739844451 1250 739843201 739843229
    0x102150103030c08070519050c0102070b090612062103030106200a0228030b0114060c120d0f0c021501090c0507110a080a03050a17130611130b070c 65
    0xc03d030300c204001c50950707122240c00d039100302604003580360000040b0301502e10541070314540304120020540440c1c01100ba02260788480e180c0314007507510b0040c420041d82044082c00000110703806000c2c101d41100e409800c1c0800381c154908610304490a49501c030080ea0b00c0000100001640f26111000f01c00e507a090b0200ca20400e403942e1603c60101d02006441180c104043c2e5500c1c0d484c001000880240c000c010204040d503030700c0c184800c50824402ca4040381800d541c0542c09040c400101c50300713000340b40050030b841c43d10780048202c5a0040e2401040f4165610f0125070f18040a02c660308a0540d503070003d01c900000e0205220809405030412410342e402c110f500d6000a401a01f51402107034010442100d50007002c000c100a500c080d802901d080c400c405460742899000001450a064a507450202c4041c849500c11809041618030080301d0315003404000200d43c55900c00d40c0c411007001d901c5450700e001801e02c0b0420301c02c00c2e00400c5952030002107800400101d40310354002003004184101c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 739845701 1250 739844451 739844453
    0x1006020a02100306090f0f0c0206220f140102120c0f0403020405130f080a08070203040e010e040204090c1401020709050402030604080f120f1905010302151e0a05090102150103 77
    0x1464005541000b8080c14440070300500c2c040c02a00650050084440c04011016201c04810007910154100007856031610880b0710840e07102041451098034141d02c1c44800900b0030003000c0003483e0361241540c10209051684001501189644402410b43c900140e00c030508030030005403a074005020301014110810400c1140c2d1001c5060328105d0b03804560004003961094001508640c01207801080343e0001285941003081c9035015010b4182a582e5184155980700070903170b501d05c90b50103504600864072004102c040da03080300315a4845d101030004111107a15070344083c50142140c0198400c1000070301180b100d944e0400400700100650141801141003580200703450b036401600c00f802c007d00c0064038a03000800c80d81251244100045030900c9850f200a40880c101c2c0203654281001a1441c04881010b0280c014107042c0c2c1d40041500341711024000481c40e0961102130319800310710703140d0504070400800340d0140100709051b803140d42e40c84414000080c10003016182451418500c540184 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 739846951 1250 739845701 739845703
    0x6110d020618010608070e040b1b030103020405150a080606100c1e170406021509060403080115110106080307050d020d0212132601050c04030203060610090e01080312100602 76
    0x80e0708440000c0e0341c000e007804506502c074090001d075044130b00701d0300c100000040d080700340c00c240c10b208901488888000d40c46030142001002804049190070404c00e01c01480989000d51243d60014607624204100a00710004509003540030b0b808401c2a030004004c011ba03505240d541e09050300001d241000d000d074400c4d1b80358909030b41c180303811070020703004119000e040120480801040c44180c907a1941c907942d803450002d64484813281403103400005080814a04c0c000001d95500844d81511910516820b01c011117409800c0040c00408000701d06009161401d020312508010f0104600a950b54068504015150004540d181d01c210350000b14105c400e142d0202d6480b403580e058202c41c42c0d0b3780403001e40d2048500e00c0d50b004074104801d81c2c5800c40c00c404101e008009401c27560402400303103a8812030704140b90301a511010790540c2103440064014032300310030002080f40340340c200410328030b440d0854659414800d822800e02a4400103229110020781039031558070010101c03085450500b420350003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 739848201 1250 739846951 739846963
    0xc0201021005060a080709200c06070c03120213080124060c05011b050c01061e05060c0a0b04050a1a07090501051c0c0f111b090711031306110d02 64
    0x40e01d142d035500814690383c0d07081016001404030760200c0f801517407501401001444c001c0f03000e100b0114200c0d4104000001d00e4140c1d280d625090340a45510b0f65440c074144ca4484070508118104040008040003c4940d4400303040301c01c280300440201c803420310700c0e8a030071214107501c06d8025000c0026030b0703005149500310141c29030704e0514016003101071768505980036015451004000c2086105510b0300c05034010098482c05403840001d10030550b450780c56214290003542042500c4040340800d01440c00c2007402400c212a0180072280143e20030344a68036a1003090f07404642c03941150142ca010f0200d0020b403c190f0804070003081096040030785020b090f01c4a2482410305110010490072440460054413007810b201d52001400886611040240100f0300600c4040100d0400320341a0000c2400145e40380c040b20708000300c02e032200d000b030741001192000103088038200302c400e04000007000c10510280400c8840b1391113030b02e880e50900c1c0c006094810950021351099200d011103e100c26400910 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 739849451 1250 739848201 739848223
    0x3041d06060322021f170408091014030705131a040e15040c020d020d090f030201111216060f0c0f0509011404181407020c01211d07060c020102 63
    0x503d03a440d101e803018404540c0c00000b07020798800002c06152002c00ba401061942e9500969640540507030391700c6c513200b1010010740b0040c1001506022140701401d05180420180741c190800142d50010440280350f664021a41940060404240704034030710001c0c8900b4018140e40f13134211b00c1015041e00102c032103005071301c075000a4002c2140803e80c1c0781d1080e0490860381002503c280429810418041c1d0303907050810103035005100399007402c0d002510490500301a07401150702c03810164a13640044418043c103210313001e110b003e4404c1e01c2e0308044005004140303c0d001e82c2031005001000b81070110459008800034000303a81062681d85a103640004820340030003950918940b25008540101c800b00b240c0030896901581c001008200d002010007241081e803244a03060042d02f0710003000b8028020300740c1d50440507a0185803016250341c040c000c000c8040c0300751a54441c40c8401a80d62001340c0e2000c0c0c80e2600c100c0c1c10100400703000803060101e14007604c100c1c140703a94a07000c03641c0000c1d902e04440344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 739850701 1250 739849451 739849471
    0x605041208030c0418060501020c010912022e0c0c0608070e1504090608010209030f07050a0e0910020301030f1103071d06060904020f0a020d09050a06050310050a0803041d060603 78
    0x140f40202070400350b4002e014901581d0b03800c60030040208008000034000d490240c8100340307003c040340d80f058107951f0a403451001d45003080c81d0240d09014400140e09010a01d201e6a00300c841942c20012203224154559599000c540d8801402c01540e03541c80c1d60000e00410841c1410804881d8028900c0851b001d0300b0307200040361f041c1c1c100b01e01d100d030301554000015950a10000144030030054010f030542140480650b41028044402c8a50382c481512030340350420340c079600c20401c25451070459035104c417244060f00d500f004204841c1041768004d030400c640346541c2072036100c00c0c0601e580c81d100030b400098006100032424403d90703da8074080c04a05a214280038000181c0c103403100c40075600040c43c05002551910b0f09240c02404036042082ca00005100300c03030000214602c1001100115080908120005410648102d405510040c0a10000c010b0340d0b00001c0d8503218005000c006040c0f0078003644c0c56500f44405244011180031b00503180945400c01c2c01020b80c1c2d0300e07088030303049141c402c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 739851951 1250 739850701 739850707
    0x1d070e030c0604091a030a17070809040c08040506311109010308041a040303050a0c11030d052104330e010902040e0303090601090e0a0c03060b09010605041208 70
    0x800003850300148029540d00003030007003400200d040c0190030854114001c82c10449080b0307071200a055907a2030985c0060702041d010210000002d0f20345001345006070182c10b41e0b1b403500380c810000c18140c405103450380380050242001c00050190038814150040c0141d100e04903062040141060040e0221011140c1941000b81240800c00c000c003200d864a1005056072007550783d0b03800c0549080d0014419085554503c00c58001442581401c80782640e41c15229a41443c034003400031105401d00c1d010490b500c4511265200c11582c1c02c01c07092900d00744950b20399a440c03000812072081d114408d00241201605101880000380050803c0c0d41a030805101084592140c0d070b011415030082c5e4000030b00030501c0c0c2203001204400640007007400310b00a0340c003440864000c031f160b203907070344012540c110854008800500c0b003020180c02c082d01184c51002150b05400064840c844d452005d940120741c0c0982c0e850b00e02c211030401c0d403403480c01014141002410b00340b5118500e1040560134070020a100000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 739853201 1250 739851951 739851977
    0x7051f1a12030d1103040302010b030a0b04230109061a0f0f060c0c150c12040321051c0e161511010f0207030203120a0b030d030f0b060a08010f1d07 65
    0x1001521401261a0f02c1400f1036200131007008195842584c040e401942050b501180b40d080c00200454099840600b102d01a61251075900c0347c007450f0714040340c0102091690303075080c8000b40110300e1210b0050000145862010003900b040c0c90f11000114002da025030501d00c0c05d566002e9641448a5003546c5465031400c814443c203080100ca02d446580c0602d2103c220344807056008050884a802d410464000501c038100c400a43d01035071100801c42c24030b086200f54483c01408104003c807c080c240701e41000d5104201c81040350111076010840c1b5070b5041c5201003103100b04079407002c0d8009940040a22410000141d08500811742d44405000a45a0303010301d10000f540710310200c811402c005c43d214119885d00a44036400130100c2c12442d0200c2010642032412032103600b07101d64004009050304125035000354003403c000c600020015648407080c44080d11140000d024402540c0e88001e207642c1040341c48441141d56400078003800c001424a50340c0c49101440301070708000e541c1031151001d004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 739854451 1250 739853201 739853203
    0xa05100305040f0f05030c0706030204151803080f18102a020d0f110118050f03070b04082404050a0b150a0305030a0905031b09070c050307051f1a12 65
    0x4140350044c110300450340000103100020002e000e1070045501690221945d1381d00c110160700641c054010040ca0880303055402a0241d005200355150b51000d4516150b6240c59940c810341080071180c0c045800081e14000305103903a540365420442c101c030070480304008002c0042400c120f2288540c80e081020808942e4030815070a0f00d88525401030030034003002c1c0c040c07800584583c40648110b546150700d501c403c81540c0114481014515005032201085141004021011640c1c800c0d198142c010100081a0518080c0003080500a000c009186401c0700c004440d845418455140d4403084c950428000041c0011841d8803016030815505601e9840c0c0603001b03600c804481881c00d0303100d26640c0000003004804405040f820050740c0b3341420300f81c3c0d00c0f4241522881250500728000c1c0c000303030984039945041c0c1340700e903000261860020b8164185944291a540c07001c4000e98440d801012447c20200f03200b46501c140380501d002c2071000d054051034040c1040d804e8245c81e4440c8402d401c1280721040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 739855701 1250 739854451 739854473
    0x160501090e0a15150e01080a1803140c0709020a2304030b04061e0c080709050108010312030b03160306050c091003050403140406030515030f03030f0c0418020d0b0a0510030504 77
    0x4811081c00316800d003480d101804089100300191b01040c2c21000017100f00c6054410001c4540545040d1aa411119507084803e9403590007084174801b81400903210030300041114074064800410b005944544020300503000030303550309020b144a000140e203d040d00c5000010380d01141e074441d010020b2500c0e00d00d4001e01412030003d5418220201c5500e48140d01d0141d0420b6029076210388071400a1f0700c41510031500d04895004031303400300702282c00410010f0212800c7c1c0006200526000560408000000f030030300c12101400c0c4a401112242841408140d100e83c80d041490b03017101c503280c41401c40128a00e003e29070b8020f8180360303940c40000e05050090000070703509a0307004403ea5a598403044058014641034039203601030804200030090070705001820854665034070f0b0066045941e048124041000002c1061003601d40604c00020b0025020b4014842040b144602589500f540c120400445264044c640e01c600001c0000301700d42e0320b41d00e0710500c04240c1c2d450b01140e2940d035801c0c00f401d448 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 739856951 1250 739855701 739855709
    0x80d02041a09460506070308040302010b030616030b13020c071403030a020a170d0507030c122a0e0310020301080d020a051b01110609160501090e0a15 66
    0x1181c0007100032000700c6840144060302c411107100744400707510000070304001c82180308018154900d410048000f0000030303103964104a40d000704003201d504c6602044003504046030440210320601c00707110030550203016150a074081607004160520300f10581c905810705481d405000e05d0381e10710b55450f854403000c020a002091340350065507141e0000c408182e031011984260410f40c150b45e0207030702c0545404000ca40b8400059401420010425111071600c12990040ca41d0034401c200a10703014042da070f001d501c0c480e0700c041c0ca001940c280300d20300280c01e030b0001c000c1c41c25420385840320141e07143c080e406254620301071490501c100e4126120064460381002423181e80e16200b040d00400011600390001e50680d40038500f612804900c0303c1003a6522414a900109550460f0800b1254485e500c40c6060140405140c008220180c0c00103150408e030040e2000260b641004416000c200e112001d00c40c0140400c2c80e0551101e880e06084031380030000038001450454440f001c2d0304041c1e00860012000d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 739858201 1250 739856951 739856969
    0x10f1116171906051e2505160303050a090c080102072a0902031b0310050f010504060503012303060712050f0c071b090627050601050403080d0204 64
    0x39188014648010281510820110034102510288401008a03221500700c80e007031815a1596465650800545401061141120100300304030340c1d1000e008403c580284400c0500c00e4001c002c581c41c1003048109110b580b1b0520004001d413100c0c0d80c40020660400340e815150000c1c881d29504da07600054411185c0241c0891007013500890707280c0c030650041c460284203220207105a000fa12a9040103071464030748001512a00b03008115214071a002180e0160100c51858090007460000c107025800c15182283e801c0b1604006201c2402d1610105032b59510908100f410300c0d00d000c40c0200144030501402c4560a032b88802e00c0c8480804070306042110b280202550701501d89000010030ba07207842d05282e41800e0a220114100c810780218050141e030b042c030030503480c02d4129101c206002c00116007030030007106000c4000911464600c285000b40c041c800f03804404000b00c0414541480c8800c000440c080e162000388401d980c0c02c40129030450754003812440c0c441d0444e003001c030024001c5601c400c0f10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 739859451 1250 739858201 739858213
    0x71704060b03011508070f0e07020d050706020403020d0f030f050903030d09050c0d030503151f030213050901090f0e1605130219080103140105010303050a030e0111040603050906091b010f11 83
    0x5081c42c0814000c0647c2c45901015608035074802c0903007901e04042d40d521000d6000140c05107a000c0c4980020701e525401554003520381035403a804a01c1c0389404503c01d6441d954900103040030550320a99000d2018100e02c2d01a0401c10a0400a03071644a8032045e084c031960b40e4a000e04c108a814442e2015240340100143c0340c0c203100d0b0030003070701e03660003144e0360041c2c17240c0c2c451101c95901e032003800c241c10b00e41c140000c0384c4824030901064000354401507445c22480c404120014a60f45c42030b1200303000e001c8100012600000103100342080e01c10174417001d40d040c2c100b034090800743c0d0400306908044034130403030754141500d04080340030000740324071019807041c81200628100d6454000606504891040001c4200140c040003c1c0d800c03074200f0f001c02800030340e00b00b2000c5141403003a00012410301a4500006000380800d50075a481d50040d400400071035103400802c8128001404076036071003602c140c06400000e240001204101c0d850a801d14103000024401c070580c1d5204600114252020400f1509 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 739860701 1250 739859451 739859459
    0x190e2a19090b0310030b13051b01030b06030606030604021b01050f180d0e130b0a0806041403030403020601060332040506010b0903031606021603080f071704060b030115 74
    0xd40200152119011909071000010454004401c072407181c003640000341200c5003155586200000d01402c98660032044034513041c0070510600907003000c01c9170074201c10400080000094107850050a4441c03281c07000344208151515440c048a500c08800c03100140ea486072038442e0800f861a50966240c81d40c40d21041110f0401e0030005c07980129011490443ca101004e01215610408100c00c50005549100040150f040c42203000d42200d8003e0700110310003217020045508504180d00c4941280c0c4400300b840188117220890540c0035144401030341c50f602c1c3c2901d010f552000c041c403e250416a440025020740b81c05d09040c2030135010040c040000c403000e0100740c03c00b008400d030390035203041c0603400c0001a4a90080111880791901070082c500306444c0c2c00c4c1c80149441c03590801d84900d5000c002e050888800034001f801d84511903114800c090525594003943c02d20300401c1c0c44280705917403114800c00f000c1609141d6019900c108041040d459074070210b3301504071985400f00880708180049 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 739861951 1250 739860701 739860727
    0x4030c030f17070503070f140f03180102070614030c0d020301090b011409030a080310031b080705040b010e060d090602030702030903010b0a030c03231605190e2a 71
    0x500c1d0066410016086420402150383c0c801d40f4001070203944200100f8001400c0c0c0d07502801c01600600548280d5200b495806082442c00d001e040100d41001031808503500c9084020340c1c40ca00c003840108910b40c1000744c0a000140f1500d0031103401c09000c40003900c0580500c0c1200d80c2c0d2181e0000943d10b0303595038120b0001404410b45560701050308000c0020a028040b02600d803941c40003801880c1100d0962142039543c0e00290070200c400c070801202101150100040c040030b5070100e111400c1603442c0140240c00c105082d0010f81c851030500355190b8a50384c1c07018049140120480c1d40c5036881c3c0c048040a0000c0059510080900340044204110700b40c001c005407200c47d1050713000340030f0b21005c0d41c1042400c088a010003419984081410b00106804030401d12551000402c00701550000d103a505180c000c0c1103025098030340150750244840c1c202540564003184800005444090600400c040c080000406040d018403005d903045105115441c3e05183c0001c0a522a0f03940f101560100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 739863201 1250 739861951 739861973
    0x3020a0305060414010611030d020a02160b0c071a120a0b0f030a02090c0c0f061302012a02120316060203010f05010c0506070f1e08010305010b031207150204030c03 72
    0x150011a2501c000203901e42024024005035400b01c4d200401076a00340395060f1603054440314a80c50700d1200303004001c40070300280300a01125190350003c2c400c4d03041002d03410010f81d000b5081244200401d2000702d80d10080000c8200c1964061034007154400c0103440004514007603080340d0a04041c005048c0710017401180e000da0848601030362800c22408500d0140341ea10024040c00941004401d8001801d03c034405003c0e14030200b0341d6040c0c41003c90001d122500d006004c0e10010911030000324110119030f08600c2044110244100c00303038100110040c14810307042151000b074041d0110f0244018400c0080c01100c1865132000101c06000515082c2840203400900890811b60284d040c081403c1d1300400c0d40b04086503120b00248040d56405c041154011400c040b14414010060701c414428540a449a45165255529940740e9031450500c242501c141524045c02504100340171080010410300f25007144e6000f1aa107080b852031030040800030701c2580d101800b0721310040e13404410480b0300344003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 739864451 1250 739863201 739863217
    0x15060f21071401080103080a03060b18100807081303050c100902030d0315210c14030606100e09090f0601180b0307060c020f0f03121b0f0a0b0a0605030a030302 70
    0x1107034122034541d24a4041603105140d0300b4041030703c800040001865286c010180c000b018076010480c00d50b00c0b4404030f099080500c0c04400f042c40d1405220304d50810886501864a55280c81c111605140350701500300b000161107c2003c50186055905040c0904201c8103200405021101c00b010b0249442e001000c6611040b4842e000b464640d0801764880c0c060081c054081d0f4100d0200c2e1440d000d00096800f00502c1410741c110000c0c45250045100745030302c2070050018039170800d20080888101402d001c80105814800c107030020300c2c1c404090703006605540c1510240c0d402c14681d150514034929101640c00d020109200b001c00120308001d00d24a0203814900003001803015000c003000300b43c4c030342d010b81c0145400204200d06e054054501104100b031030000280c00303001040207800209003465802c1c0440c1c102140c0004081c4101100000201c0c0c1500010000e041a1061b44501d5070700d46c40e80300d10282c41e118a140100d070041006d41e00c10f100800e0000c0803181d0100e1980f402034040d41180c18 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 739865701 1250 739864451 739864453
    0xd0f02100e03240105090c0306010f02120406050301050f040e0d1121040e0a06051e0d0c031b0503010b090a05060a1e060f02010b0d3c050d0f0215060f21 67
    0x6500d00b880706c40d00d405142c1002c9407504507550344004440384040d0a0703004085125419006881e4a00c40c802080681020381d81c03a641e80d170500050000f16640080d0b0300740070710b140205540a0342c0011840c0584031801d80b404042003010f0101d074601d8041d1410034008400300003131401e82c8080c00c40000740101c2d07101250f441100d0b59004800c00440c0c0181c413a0580100c24108024025070940c1c090050944004120b400078054039140d180100d001c942084030b0b000c0c03882c40c0002d02c00722066035840040004a0003401b988400c2c0d0042241540003800b130052943d142c9003c40c031240d44004040c0080c1c4010302e260b522403080f0403d440860945031099001044030b8070002c0c51010b1040c041c49012400180c40780c00103a03090796401c080d0b10340788000c100380c4440030100084140402a08540729445501014078010101c1c1041418415400300d958244030342079a443d505150081801302a02071600403500c2c040c0d403110f020803035808061200582c0150220384026481e40d03800404d003a4556114 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 739866951 1250 739865701 739865773
    0x30f1103131e03050a020913080307030501032d0f08092206051002060f072708010612030c110105040504020f070605060a120809030f03041d060d0f02100e03 69
    0xd207451203590342d203001c0036103e074102810210150070814412070308004503402003070381244981c03103407000d5130400e40d20303107001a803907000410511032401140311075401d45040b1400c2514a200ca940c14407041200c0080a14000c502d02e4400e012000003a64480300002d011403403240c0c981807680700d090644010402c0503900c1c040c0c0c0403505042030101c031901101d03140c000f411982c07038405040b031610a0062140c4200541c1261000c026224035003050b003102c007040446030000342080300325401e54400e41c006440c1c4140c0448500040b0ba80201d84100c519008444481e90200d070000494041c801c58000503005400001c81d42030303c0c0c28107401002118000d86040202d52200c00403c4450183c0d48203802d94696108000300100b19600001d1425003401400c4a8108141c039540900b1a081640580c1e401e10664840880c100c00c0c54482c91750000381140d011016284070b030f50310302c40d0b01c520b210041d0207131817403f100044081c0612000600704c440241298582c40030036100d2034a14411988041c2001504 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 739868201 1250 739866951 739866989
    0x304091b0903020103090f120f080c1810020a0b04110f010309081801211d010228030f32060603040f050a0f060b10110a030f110313 58
    0x80d0351114544803256225071980307145800443c083e1000d0401562901c030165944000522510000b401014441c0c0b10601c00913500302c0080d1040c00014848203144004228a212003d00d07010b50709400300c0e0440d00d14003203d00314903080b0301e400c0003188010901306000c0d042c801840b5095085490680301180c15001d0050024011420381d0440080141400c109103c05002a1350b03000c00f00c042c010041c50080c01100d140141c1c4001100240072194602c2c3c0c1e5140e107804001e00c4801e48450780c0e5240d100075031514141100110a01411072610100c03001d402100070226442074008407401e803810b41090110b00c0300c81e1241a601c1d05c919a80c4090594001c5100101500c041041446003c000b0040c07802c6617110f403070307213034054044007411940c070300801301c40368001089011000101e9024010000e01801c00b80709001030800017801e03142c01c0c082c500c0c00040d032201002a400d005140e0602c0c200c0c01e1000303040030542d07003007621a400040c42c4c080882c644c0c2c030700400e0580701ca01f102c4044455680007060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 739869451 1250 739868201 739868231
    0x418021305120d0503190504080304020a05150406030207230d0f0201091106070203030702100f030b060922061206090b1308040e0c0f0309150f09030a27030302030409 73
    0x1940c2040740072074103c000000070550143c0051a40a1240d42c6980810328441019808540341254204c0d4044e001106110560405000000242c1001d541c1c0b42c1481b509001080b600340114441c0b0000c054000404e9401c104d602c01c951000c40c81c2d440b2a410554000c1c00c2c2c0e06460380c090b0007162001418030910810036520500078014075541103074105600c200041e0610100758000702060360584010080100181c81e01c18a0418480e2550303503420710703807216410040170340c1e1342107620510032401800f02a00316514001141200240508140d0311000c0e07246554000d020702c2d51011101c0e580c0300b0b0b244010b0000e99002041d4284c0709a40212840c0e4480400d20103c940203400600120420321060003020160400103400001c01c0185034101003d10a4890803507000703c2d24061142c02030304000122040310a602c2d0b40004260088a01901c0e080c004030341d490055000e28400c22005240900f04098460019034110110034100742e03e503034580c28040d644e03a0040c8280c00d10281b03400701c1c000520344 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 739870701 1250 739869451 739869469
    0x19050703021603110a05120d05060108010506180411160302010e06010b0a0810050904060b041d03182701051f08071436091b0f0418021305 61
    0x4200e0389860502ca4442d00c0031101c121a40a40d14814860000803c0106000700244103540303a03480542a92480c04001c4603080e900060003140c180040c02c00144501c5e5101c000380c031103401d010180b044184040340d001501a0400410080c0010f000007103582c00c12040700744030300f401342c02038000b07000c04140801941c0c0d40e00c009200301602c07040b05100c5035242c50300c2100055080b08200108400142e19000025055401a035040718042d035215009815824140038000501206507900450010050003082e02c038414180c4540c24400703007030211080c0d6551003001840900607482041080302e0003034604c0c0c0c41901e00780211403040b640e41d580c0e0448001c1c81c00c0041c20300781c084d680300290350302da602040d00c2c5000c02003078110100000344215008000c61501c401860800801d060b0b0802c0c801c0d41c00a2107815148003000c0c05101200c081041c1d00c500b0141400038402c1001700c003940c07541440008889405140c001400c0c0b9044504109400b40b0345070040d1400800c1145c0c005600e998810400803808 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 739871951 1250 739870701 739870717
    0xc07120c0308032a0403060c030207030e0f030a200117011a0319020c01050f100b042c0106090302030d1e080702011508150130050309091905070302 65
    0x503091620520018079100007564000c0181c0c58100e136000f1041c0c218801544107050600c86084002c03c04200380842401110001c0455050440c41c10320b1a450003011807a48000032802540309400000481c2c03010000d09072140e400c03007500301044620b03c043cbc81c0d561007030420044c001103501c002d2503101030341009414101c59000c80c03060000104401896581c0c6c20080c4210141c604107030b02c1801380344c44ca0000b00b85012201d0000240c038034111078081d000c45c901510b086c42554074190207100043c8203100712019a0700e540b0030034102407400340d41900c9500e10b903200300c40c001d210395000068031134210ba6080d040d24401c40c19500440300c131001c2162004a48902c5444070a401d000900c005402400f0b09074100201d48004510301900050410b14916030741e110429580c0000080042446a09011800740504c2075030001100c150f98840200120942041304120054030b40440410a04000b01e50101c540a08403001c1b902d040200080b412201e041584030703203420000001c200038400d1085860003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 739873201 1250 739871951 739871963
    0x306090a0e1f1103040b0a06081908030a0207140601060e03150105010804110402180f060c210405030715110109030219150f020306010f020f0a1719050c0712 69
    0x3002c8810b2030a2020090051000c6a9035500c2c800c10200005500045109500a8130441e14604082c00c407402258020360108419402c4400400b08402103840e5007284182c21040b01038031f03a294100c20900034418920001c000c00e400702480151040b020400074101c9003d0f465012600c0911800e1649482c00d01111a40e2400c1e0140103010a42c012010590018000d606050028003031001040490b8031401082c00c0f651887c03c06080079103000071000c0c0c0300d2001a16108d00b80711035040c0ca2076541c2c51142450050f07040f01c1c10350014400303040c01500c004001c001c044501250b640c24540c40c907000c3c0c18013060300040146540c0192154140100900305038146c1c000c1035421010f11f11034041411583c4110b81c40f00b520185450420740340c1c02004028501e00d440140c0d00e003480c00c0013402c07088403604000d042d908a41261441c8407808174483c5a565004409150140d004201c007480d248036460b1824240c0200c0b600200f2801d61000c007801e6415250400c0320650b540f10030240c0e0544c41c04110052007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 739874451 1250 739873201 739873213
    0x109210b09031b070f051914031c0804060c031803030c0e030a140f0616140706150e060609030703080c0f06010602060403120c1e0e060706020306090a0e 67
    0x91540303000a640701403200281c03801c210309030700c0c0000552a20140d000c41c66111540c24007041c1d40d1043e880004100072601d08a41118980f10013494008500c44c0d1200c1c5c14811035a0a0a40c0f014403901d801110025080c00401c03840040c06015030304e00741c2e010746040e0720b082511b0302c1c0280244240c2c600021070b94031462000c185960220003034400d00c9000c0b400c0240f5292166100e8804010075500a44111404981d2074072040c2407610f0502c00702039007039040d40f11809000034011555010701083c90240b500202100d0b921105003c03038814a00c0c01012640f0b86040a0b00c540c01a40305201585ea80c02c0c42d001242e1a00020001c190160030b0780c45505401c24038bc10400108032500a15665101600303603044001071103401400c100c426485400980c00940401042503030000d20340d802485000d80801440805100040600304940c00b80d4100092100e40a40d03901d0280401c0c1604c2c0728020031181c0d4524081c41c007000a0340050300c01501074480b000c0400e40c0d13007680380101d81d601c0012a0003054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 739875701 1250 739874451 739874453
    0x10c03120b130608030903060915070e01090b0c0c0a050f0102031819081c020102040608010512121c23060d080c06010905090d020a020603060111120a0c02010921 71
    0x401001c070303120055440800d060b00340700d030074110740908801450b4901c0034580b02c81800060500b4218002c02503401c54010b030030410044c041d10450207400541900d80507a80d2003030040145c3e950541034120300b0503000d012918000d007180000d820004a04d05452034400c042d940c509202e418807500c10f256015030000c0c41080082c248a0f40c0c014114140140182d0542d5070304450500d0f072240b1034100c1041d0750454440c01c41c0d0b00c3c1e480043e280300007050340b00840c0f900c0d18204004000020601500d031140c10703a809c00c01c5260030308000d0760100d42600401d09590f080c2d03149402039090b4000e5134501080c0e040060740e0701012110072400c00b101d903003910726a0103951410200582900e4050301198026030902c60101002001c0203250301920052000141c0d5041025000385881c09081200d81103600c0200c1d0b00300161500b0040d80e4211a080c2400031490b602d243c0001d04200d800558601d0364030740403c601124540c04119800710300c0c003c1e21510702682d00e07840160316100c07248180c0185503813440341e408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 739876951 1250 739875701 739875737
    0x2030f0d022a070f030c06082d0105012006010b1b01020c010f0b03030931091b0e0c04050f0f04052e0501020a08030a09020a0807060e010c03 62
    0x490202800304006182510740d61608484075401d001c0440b00744040c0c555019900d000308182c030054918501c4c0003044a24640d40d000202e00d040c040c410400a200340450808583c81d00800b80c40315051845d203041454008800b031120609100c0c890005035403000420100c4c0301e96403a00300416601000e46581e84c02e000c84540c030341d030002ca00c000d0511400c0c0c08240d0140313028400b4080344204200049441e080a4180c94184e86446203030b03134420f801c00c1100d40055a150000104054181d003c1640403110704800900841c0b00140120145400c0c0240b08081240d00b03100c02e41000481100e901e00fa0352564024022400b00f00c40803042070004000a2045140003245c0700455080105800743d44140c0d1404142a282c05890554280845185c510202c95501540a074800c0341059042d403e00c0c58800000c2d92610209809041c010700040032400406054100c030b80d00c070b900a002621360315035035000207544c2e151511401d40000e40552030105a5032103180003668168042d660710f481c501d1002c03014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 739878201 1250 739876951 739876957
    0x90308060d050703140c0306100501171b0d0906050c0c1e030d0f0f0e030903030901030e070302100f090f0b2205040e0c0f060915030408041d04120e0102030f 69
    0x6036643d206404000001030b60660380e408251303580502510099500e0811b1502e40000a040c0300070321109440203100d140d034842c485c02d0b420b901a00c04104152115915032025420450320780e5460500003c41d4409840c03a90044048240301d0f0008010903600c922000c034685c040c424000b04503402c03650f41e10034582092009544a0801c14080e1303443c248038455000221600051801c04407034031181c030900310700103522600d8003041d074a0b80514030b01070707030796001903164410680054180342e0784d8010f002c81041c003008040c01840c3c2c0a03160740102000c0e150301824001c145007402c80040e54514000c60000c031040305841c111020f10f01030b2402c000c1c400001c0c143c501c0c4d001c460b030703e08a203040100040503500d81c00f500e007410304231401034500c9a480380203011013030403054203139405034000f0460ba903110307141c03910518400b10003643d01645a40781c600d40140e10f48100c0d444694a5070300149940300564046a038280101d00c02c021040400c1710488068a0725641d0705120b0340960800e00c4511940da880c0001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 739879451 1250 739878201 739878203
    0x4020f0304300309020108090f0c01030e0106090908091f1d180c0426070303050c120706020d062301120b120a030e091b0702040207080c100609090308060d 68
    0x5100c080e0848512140c03481260b0309210000603448901341c0082d540c00c840c0940e0001d40601c0540410380c115862255118820081c0c9410181c1e92840d6544044d002c0d44900090480c0303c10034840f21426050071841608525a418410320500d00c903159456100d200039850141c0b1a101e1519441040c0d2095084c0810b100346150803104203039280d030300c0d108022806845054159000c684031410540f10004c802008503076140d20381c1c06a07203000854040043c41d2421a540351070a40d42c0e032150b869180703080c06c01001d071100d804040403030030070704020154001c1c00242810030340811102c0d541300147c3d00381c602100d10505400c00c01a605a840d0b5104e0290600c500c1d40d4848081020032058010400448407070403104c0d0aa003140c00c03107030101940007100203038602c1c04884085032401c100414500740c1c040c00317001c6034903204006005011501c1c0c640548603040c1c1c11251903078503004e0940d800380d10703206002c0703c3c9a8489d00e082004241d224651161640303954041c2e6460005131307141c0040c0402c45020001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 739880701 1250 739879451 739879493
    0x80d080f060105041e0e0603190f0f0b100305010f0b060706090203030f07050604050c0d1208070311070302010f050a020a140906220e1003200a0f06020c090604020f0304 74
    0x4007144007082001d142c5d4064251507200c141040c90584090a1944080c2c02c0c3c601c00d0b0441c044090490f8483d2058412181d0407501402840c1902c0c47c1c550141050504028140c0501904000b4000388280b0340000302c0303008000901002040519200c200c61100c080c05c0c0c1d00c040240301410100b03009500c404411351026085924100d12401c24041d6034108072230444181d0700100400c020003000344200c040d48581942c1c0001c64a9a50b56482000c64842c0d046400308a442d0f00002c0c1c2051003a007010201e41c20200071079075110080e0030000d02921080550110050600000c250010319a04c00c988000c2d04030f90f11400c075560703442528010350f4001c0000c158840018405550341c1041c8440210441440c0c0b102d203407a0b10f2030000660f480050043c00f49504116256041004c904500000d9248041c0307003181c18098880c00000a020020940280e5034006a0403008210b031500007074401c0c004842141c1c40d20701c0381c2d80e8404004c00d038400e040c2c10701a5100d047c000308000403001c5000401d0505642 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 739881951 1250 739880701 739880707
    0x1203011a210a0603060e0c0102120703020c09010b07050d17060105090406050a0f1d0c0316020f0f0102041406091003330306060806150f0d0818010306080d080f060105 73
    0xc105264494050318000b00c0c00d69940c00c02c10820071140b04031205140040081e01002c440c03080080d494183caa00104420b200004100c002c25100344414041150010201040307543c49030100035854002c3c040c2125248960115075180900070003240c0316591915074090380a03a034075801154160081c0c0c220b41d8000d03441c0c4101103500e5a0b03500140c00a0700344009440c5810340b40060841c607401000d007440750414045400d00050b80200e60844e58812a1080c00700ca144021180880c980812408a015035006d00010480c002c10103400500488894030305240d410603038041089001d01c0784c0980103601008101d80d1030000d60003a000485220401641da41c0540c0d0004c0340365000d54010001e9007810500c40c2010f00400c02203120710800703002e0002c0281060b16098030078100c007102841c17040e80b080381c04500c0b0034071550340d00404036612a40442c1050b110601c40d14000c10f421084407042e40443e040c0b40001c50441000a2481807182055840c0729194441400c0d802680380e0213000141080410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 739883201 1250 739881951 739881997
    0x14120403050f04081b0117070e0d170c0c1002070b090910080d030903080a140a09020a0504020f09030114040201080c0a020c06040311102c040e0613051203011a 70
    0x81c070070202c10040f0725805c3e02062120f400010a174210515251200b8030f0681c0500c8040e0f540b0440d2288180400e5801070102c0400d41009032072200b1050304032400e64000507980203404004212400410f800f07a481d91140c81c050792080c0d80b1451280070310034a00100b80503411242c6000d04560350006000050030034456225540f00341031441195044020030b4a80c2d84000800d544505081d5015442000070400e8800240210402a60181003c0b26213502d0303200c86e0045d541c490180380004d000080046507030b542404804055034000d030110a1280d4646031100d01240340002d2032a2065505a45440c0c4a031384005000040c3e4020304510b104503c0b41c0321118229854000050001e036008041c402c4400700d405041001c580740c8a1040c20400128019000a41681c1070100e08690b40b035080c80410000440041030080158000d13040141c420a01482076105403980c3c604c40c09070241d01542d05015080c0481c880610082c070609030030703030f06240810380380c0c203441c1d00500215101244d1010400900d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 739884451 1250 739883201 739883203
    0xc11040c05070506010e0f07180e130501051e0c030a150b0301080d02420a020c0601350a050d03020a12060e0a051f0806040314120403050f0408 63
    0x30100c019408200002039120502030100512401400314058200880c5062542c103442548060203034801e000b0b242031420080110448034402500113a0340e03941051a003203d120300005100c1209407900d5280002180380790008600d000705044820300140c1c40d0b074840300d030070201e154401498128600c1d40d600c0400c1d508100c00b403c00380100140650342c0d8595042c40880d50030030a62121a10640d4480030b040000018800b080800700b111015500b45d0211010f0160148401104880d41854140400700410802e00303a015080421540c801c840a9a0f00e41c0c5036600582c40d000482d0a000a0301d03c5445840040e40780d400c0c031038035210410740780e503c040765940300d240440038240035010940100c0c544020960042424040340c128200a2104c1440d0613a480d8203554064002030501d61103100050b00101c1171441c00300080799504510b008a80d907190031503190349064508600081c084804907421100043c181c800741d0302080700307400c01a1141d44c0c082e40c580d4403212010890034018000000c25104c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 739885701 1250 739884451 739884461
    0x30127060b07031e02120d02091906030c050a050f2a07032d060e0f0a0507060e0604080c0409060b04061e0f06080a150e0a090c0b0306030d0c1104 64
    0x1a0300c4181c5900d0398541e140c058104510310003041e00d41595910100786090340040c0307500301c1780803c0400b80d50301c5404400000203031007080051500140d08405210311050881102012901260f80410088040d200304941c1032041c06540c01c001072003400340c81c1c1d13000c0300440140300c504d800201e101d442c0f4514107130803031661048502d02c80c2250020007041083c480080c200c2d040d01c150104d5014528ac1c096410001490100701c4090702941d9541020302e00e111017000105030604408003110b07603411603071801681e500380030b0150034002105080400103e00b0300c2000d54042d0f4000e0340c09065064241c0c0c0502c80140303031030502640c5054440d030340d541a0380c58910486000d00300c84191901045542c0b03192490648940c1e200c08081d03280c150007045016404074031550031070030344600852070350241501c00142c01e0254000d0303084000d4106c14884205070a600c4020344900c030705100e00c03042c0da481802500901003246c0e006e4150b003203040020081880b40700342d126503c0c4201410414542264081002c0710 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 739886951 1250 739885701 739885709
    0x60c04090f0b1e0f15070f0c0f030f03020c0904120c1716200f150d0212270705061b0601060c1e050c27101802030103020603012706 58
    0x181102d1038046400c012140f1181004e0588540203104907500310350b28603100d9107a01402a00b5002c50300c10810102126560081c1b500a01d000e0502d610307410002468200382000310003500c03d03624522110304040441c18466038200d40c90030009483c010301902c0351a20038600316614036907040710342c05400042014040e1005a405801851009864005c0d1019030703180143c0030103d0594004102c4c3c0c0d03110b55130402640e10a5680a0502c00340c139900d41e100f07001d802c40d211890390000c40e11400c841e180c1501e040c41040b00c900c44901040249491840e0000d441507042c1564001520900c1542441002000d10941405c020820550f164030820b05168003038110200080d10f10342410140883c0100c1500312288056160f2000c2107241d4030b041d0740320580c40483e40600c0003100d101c14049214005404540200840310555103000820441d10411601803096002c1c00840c40c02150131072442038a041e41d0340076012516503403d1080505041141115120680204c520b415a03914800d0107410300030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 739888201 1250 739886951 739886989
    0x1021b0309030c04050f04020d2d03080c0316050906070c0315050612030301050d06090b0a09140d050d0209030f0313140d030c0201032703020c030708060c04090f0b 72
    0x54408074109410311054520b5184200d007040b05203d584001c0340d0089400c00e50403078038015071820501e411040701402c8040d00c81c094400d840e540c42e4502c6290b06001c10b0030302c00e6640d4042603888092609042c08260380784220380c1d80c3e07051440301180c010001080e200c000241858100196035541003400550354100321003184507003100d403610008500803550490000c444603009002103042190b41c034001480b886100b0041040800240322140c0c0c00307006115003041c4100c485e03150508800b80542507070b00c0d04541300f507450106180c0d4040b0200c0e00e24901210365851a18005080d402480079400518032194140030340203014a04800401c010040e0003960504451282d20b88a401d103005000041943d014540041c115400240d0154810aa40381c0c2405d0000d205c0160003011150705007034a01020300e152940755024140364000030b0b10801074804408407001140c4401da5a611580c1c15903170b13412601b40034801803003082415040758501000e40308000030004d0760200061500e0700e00b1a080c42d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 739889451 1250 739888201 739888207
    0x3031e0e0d08070f0f12110705070603020a092c0f0912040f090c0e0402040605090f03030403020f10020a0501050c04050f010c03080a0b0a0801051e09070311010309030201021b03 78
    0x2900c028400d018450381d0380e0814020300d00d49858082d200190300110b007000c00140d030800d2603101c2d00400c043c1410445494007042030300e484034194140b60740925425100c2e8410804001841480390080703c0140c80030360344111140b4034208600041b2400100c5e110041101c9000c3c86c020302811120091144240c000c10071302d00c0c00c1c20341440d4109080c40c1550786010204000034071002001d07410a508680c0f010500081c08042440308441e440107000071140e004d80001000038006a00002600e40c1503021541a500c43c0da0880c2056a05d20440c80000c0d0400021001c090140c074007030f807411042c1206030040e180100003560741c0c94216441100c411440b0500403c0520140c00c203a0410765450700c003800c110800c1d00140d14090458000207004c85003040d2030b0003040111f43c450310010340c000c1c076031000240160f08010784001c070b111400074034000840d40200300055110b1800206401100e400030161054000800011006000801000d03015076400f00004404c02c48a0351a60700d80c45840000703591 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 739890701 1250 739889451 739889471
    0x60e030a0503010e09031222020a080f070e011206050705070b0106170f100b1c0e0a060509070b1c061d04140d120209030c06030f090d14120403031e 65
    0x40c10002030b10103003a55009100c80404803034401e4049412231458450000c2c03c4000c4001030200b815070440082d00010140400500080000303091701c51515440190b8002d15121030200f91500402d10555115a288100c800003041140d80280e400101130b1504501e882400c0e1510039a0840a0b8000e100090507481c50401032510307202c06c183c201420f204030342c0050a0005807106400d50703030f00804120b010000707083e180800c00102c0341c160720545a001070000151134941d880e01d4601d105404c2c0c0d00380e410400015a5200045204000d54500c1c540081c140201c9024012440b141e04c0749200489035242000b08012103980303070403240b035020891008810f142501d0301e45103008080c0310300d4046900035018004000e421042c022481d202c0481b0050300ca8041d440046c1c502800044c0c202d811a0f0004140442d0886142c0368512844581088504009543d0b4007152540d403002441e5003401400d122110340c0030410b909064005009141c0441c60500c0c1c01c00c0381c49010741c00c00101500d2039440034201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 739891951 1250 739890701 739890719
    0xf02061c1a0f040509030d0e070f06020102041a18130b011107120308041a07200a03080703090c050907032403051e0f070b0d05060a030c0b07060e030a050301 69
    0x55521400440106840c0c003106020800070b8041907001ca1256454800003030780340100700207440350850f0b0307030205003c00b1461001c0a9110074a50091070502e603c1c0785004540766005000312011191407800603c500c0390710000b0b200b803c1d04820324000d4503644600c0c5020040c3c1d141c817880d108040c56641d002070003400e1000054990240d0701d504810036001074008100d0282101580507a683e01400c1c80007044e6a1441c1520114003051035000315550030100381702110340e100ca4180e007080c07050020818010588031685a03a00481d5800400044058000504840c880e8201c1c900351407141090301d040540351310004102d004119045000030343d6032901e02c00c952900b03074000c29905c021303180e25101070f07070030754941a0f01d0340c0d10507035002c0d9034464484054a91500402248a03280205c109444210381c0f59403140d0b0850340034010344100c0310f00301400f040c420701c6c0000d550070860750700080c0c50111610f00a80d40480740c20000c416210303503a0f03901490310150400c0c001460101c1702641c804da0fa9604101045c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 739893201 1250 739891951 739891961
    0x9010e1005010918020604050d05010212090c1c0507231203090a0b04081002071a0f100608070f14070b040b1803040b0307030b040b060c0a032003090402070f02061c 72
    0x10100b5204c0c0800900581c8031902120f050369003d8510010b0000ca03402c090740a40b04e81400c200000c0001c0c010001c8421004c10443c000600c1120b440c105056118910558805400e0307005d825604180360410950160020340c005c0160031810000640e101305001802a8900b5203004030103400c000f40b5100c151521401000103031200d00080f6007414180100541e482c2840c003101c03c60607a0010385042845844c46c0f0306284d00e00200f00c0c000a51801403c1c0b802541c00554066800d03607011480400d0180c001e02d6020722170001940c4039942c2c00c0e505181103d030301001c00c501d4015901c003045250003240c0d800220500c12402030407040309600f441d070351584c00c0c11542400151180c0007440144008050301044903084170445c0b80c00b298840c0079000040003040c5986040d54001c40001e4006410400400e00c0f030800340c0030352034040d5503000d900061900c410103c1d01800441c0c00810840160345090b50144c03803418050001c030356101e00c2550106405a1042541050713110224058407904a964052 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 739894451 1250 739893201 739893221
    0x1f030b0306130f0b0a02071202030a1803260c03040902071106030c040905090712030f03140610080a0f05040c080705030c011403250905010215090303070809010e10050109 75
    0xc030030380c03002c031a2107a0a20182c0604002e100c1854880855442841c0342c0540f004690442064000c0b1184080302039507a5104120440c0030942c07104901d030610400b0009030040301c0d0408100c040e210303040a001c2c01814110150085c0800d02071004050088041014101401d00c070240107035a4012401c00d02d003590018819244224810010401c0c00962101620212024440b01254030b40b900c00246043c07540c04d402540306115403079104020b041c1c1c010705c00013103101343d51401c1052241e201080c504501c0c0448800d40c01039280502c14070a0703441800c0d2194892030200c4c0000780075644011903003d50764140c41c00c0d10100007068061000c52070620134600289400c03402000c5e13440c0d0903800030740407c500c0c126001c5c0c1d480b4044000b84840700310300c050ba56040380710350b4403a03c580c6480d000038100300c0560158900510401c0f02c0310414544144900340580010001981156190101102d604030014140d10580d52140034141d06404100700c10400c94500c66004241036050500c040100c540490b1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 739895701 1250 739894451 739894471
    0x80a11030d02030412080d050a02030414012f04090e030c0706090e04060b040e070f0807090506031c0c14100e01050403090501050d11030a05010602010e0318010e1f030b0306 76
    0x9248107103a400208a900f207981c00d010200940d6200d042c1300005008208014210604090412103255041d500035445144150b1403000c8141c2070707041241c00c035000d148903d841084540c4850f0002d2503006907031035000540001161030b1644800700401130b569000e0031001207910129290307660031018030101c005442d03176152611a49140200005516402400280c860ba40e1034201e456951030319004041c1c0412481d00b140c42c090b5850302098401d41c0c445c498044140aa50381c0401e0942d164040c860281e0b0b0001c005094a030850003000c0002c154210b08a0305101d03426016000185442e012114901d0000e0090812250110042c07000d5a100250891681e45000100300000c0d401840a10039110301f0f05c0d169803200110ba90b040700400c020210801942030200402082c210148c1041c1d06032041680203100b4400c0d00b50507a43e482c01a400041900c9825040c00d584c2c951090070103950403000207205030510700003076200c8a07524006601400000380c03a030300d00d10b00d1400c0420601c1c1d004424031f5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 739896951 1250 739895701 739895713
    0x80a0c080c0324071101020a0e04061d0103150912120f0902030d0c0507080109110f040203010e040609030e10020f07050906012c03010c05030a111c09050f0601080a1103 74
    0xf0f45140035481200061890701001200480c203142e103e0385040c0c00b2079201c00004c55480c48061030280400c064811702ca403140381890300200b5014107102407442e144c0c000000c080000e9085540341c0119a000e41c4590350070594814121012442c045003020200c0a60b44828240c08608a08203090f2001071042c64071032400e000100c001600e0010300f024074080c01c2c2c60102c40140c200e240c0603061000c0c0d5030106038550b09180c880000c0c01041c0710b0701c1445681c115942d090100d5140144000c2e40001d00c40c10b0041c1040f040050040b5101380c009840300c41c840c0c0b6004814640300400a242d0700c074640020380040c0e212820603558000200f0040e00a0041101c8003070799407528000080c5404480c080d0fa2100810410704d40d81603145062418000b42d500070000d0002e2500d001c0f0040054100f02d0b450a040c07420184219944040034007100c100fa4150f2080070170304282040d602000d070107840d100302c400d48a20212000c111030113102c020f000c1d000c420040c00100c00c01c2d0802c001c2082030303550083e110760041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 739898201 1250 739896951 739896973
    0x312031113030b040201090f0b0405090f06030705210601180e011406100e0303040902071a0106301e0e0c030606090402031903030c030501150206060118080a0c080c03 73
    0x880701950460f607110315414640e41e211300c012595004a540840552042c0d05004110b0384240700140c019034800761011034043d5210087c08607200000d5a0307160700341d013101100340620305001d050810b020009a040c21405e81011010600e841800d9000b00000300d01502c140c0b00c0c0f848503001740d83d10400802c009200d410000040c101042a0140140b842010000b00c2d04114500a01c1c0864007000001e00ba6070722a6659802c000103548104421035100709480704410104241000080c1a0b07041651240742d41d0485082c3d400c1442c090302c1c0d68402410585103502c1d910405030180e4980c0d000040f01010020424051940580d0035200c0055001d402960241949880000310550b101600f2103249070982c50354004030b0704205052443c090039504404002040c542c06412480c130505440c1e41c00c0282d40c0c0c0e100700030803540714031503490390041e0040c0340441c41d40c0d0300c54001241c00b82085070040144554a42440d840c200006000320f880c415184002c01a0800030f00102098840c1540504030103041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 739899451 1250 739898201 739898227
    0x9060302030415051302031002090a0f0e041b05030d090303090b09090f06040908191b0b04140f101e020408191a01060e0a0603110a0c11040603120311 66
    0x400f02e50014510703640c01c005204003803401104860142c000d000c0e125041c40d140c000c40040e520482c03659003e444a150001142d0b0079110040040340e80c8044003c50343d84590303851000a0601380101c808100041d400400d1030358041c0618105060140c039402450780c907502e4040e01007c1c065001002087c010b115a19140d120100e5983c5e0002c0c5519110100b641d8150000c0c004205c00c402c0608421004103854044803400d4001d407503181d02c25110854034403941e23201c6a41c03210056100501d4092044049000520001c1c00b603d07800c0060425900101600381d941407600d00c07e0500d407040c494403284a2442c011200e446100301040486040d0314090401a104e41d42d07102001000c1c8600c0c0c80305044600388400d0080418407403c07842c11480c2c640d40d40b400020003184145465901c207414040000411034002d104440120364402c2403a4148103441c0c2050ba92200643d005444210282011500c03541d110b11030040031714411000b130205007400481c01012600f51141c2e14019420800151803076400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 739900701 1250 739899451 739899473
    0x6010b03060a03024f0f0e0316140109150504020a0816030b06090103110d080f03180f0a020306061009080d0f110d02060a0b0f04050412030e031e160c080c01090603020304 75
    0x82c2c0e05001007000b44003680b01b00c3c010300d18140c22007050301011940b02c0075520008a0040210700403034444500c01c44c0c00104a080321001c0368000c2c08420000c54990b0956450307000f07268401d00040460203507030b540b141c0e641e051001c04400402c00300c0781d00b2014401c0000042803d03070401c1040e10443c241c0d42c115658801044136201d034061180c8446061030303080010303003811550fa044480c17000a469040c40c40c1c00750a0961542010003440c003c0c00c80a012010000806500c0710b500213000740040e0301c1d00418419101c030404440c1c0100640b000c4c0c0855151800c1100103100c40c09586c1d8148244101070f40100b01c01d01c890a030202d150002e01e1001c01540d03000900c0c0303070822110301e40001c5900d030050008112161551405401c0340c100b60801050001200c400b22506410f0749040c001110b087d14000d84a01c98034030300005900b00305440d4680703100420081c18004103201a640c034008a207071100b04c0140d04580c005000c5600c031a00d492260f5900c11030440041c4070300e04007507045080507910345201d82 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 739901951 1250 739900701 739900849
    0xe0a110108100b2109011505100306050405090f070509040c090b06090409050109020a0b120f0a2c0c1203030f100906060207051e010206010b03060a0302 67
    0x400d140801c2107070b10714900031402000780c0e03c5031944c1c60506400c852020104100d00b519000c01c1c0400144100b401801082696a00380d4070f18900d56040c00304004e104060500e00c0d070308142c3e40d00004a4152158031906003e4016000100a801c0384031020794030f03205194200c2030103405c2d128140000210000c0c250010388030014130115540d400d42010542a009180b140c0b0b40c0a41030252135801d00c001980700e034030414002c1d62582210342e15181207039074a00c5036811800e4401c0d02c520005150744580050a5000302c041040031600140e00020f20308a843d103040d01440501d8940c0326115151000c1241c4440ca0b04203540743c40b240700c50802c0141d100e00004001502c0c4080600003da0207803d200250300103040c0c00c5004110789611003400a59a034564000c00b400b81d0b01c84400072100c0a005258074100b003805078001d24850303007401030350026a0405002180c00c11050240800143e4504080c410240f00e03c85005c10145004602d000b042d0f0320240e041740c0ca84100c801042c0440c5450003060b0410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 739903201 1250 739901951 739901957
    0x1104060e100201061a180a060c0b0105060307050a0309050a060501030b0a0e0c010516032708010b0f0906100c1a060f1206150a09020406031d030a0f1d1002100e0a1101 73
    0x7186101b03908610310203d155200e5000c2240070b03001c902c2c0342d00000ca10b26103a00448058000e0385c1c80300b00780041480183c4117003012840c2440880e4403d4802c1d0081c001c103900c14401e69046142a0751102c017a01d1f000e8004940c41010082000003d540c4ca120310003036070525200038101480320303070000f915610981d8011950410a2140041414000c02d003800d101d0825401602c015000751b52200000c028901805c200b6500300032031038420b8903162100d4100e0303400050401d000b0740c40303840130404041e600c0d0810805102110740303a00c010a00340c0b0760008102030b000254905500d032490805c03c0c502d80301d140b07003481003480045c14103262000140303050b40f0070400c1c0c40001080130f075100042c4100805900c00e0780660300004001c200107505822002c0c050300855880300c4220601002c06490b4001c41d845080024001503d204049201d2040c0f1000300381158400243c81032910040703402c2030200a08070003d40d001031640c5007515590b01c1410a529550740144c0304804065a5010704800700b01b02483c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 739904451 1250 739903201 739903207
    0xe011403040f0f03030e010b19090b030f01060605070201080703090b0f0615040801140c0f03150d0812012d0506030403170405060f1b090d061104060e100201061a 71
    0xb041480742a0048081c0c2103103041405030742c103280050143c403640c0405213095003045100c280354102150b081e407042c40000741c2c808446040c00f003500700810400090035031501c00c604d0b155000340400c1c418400a48955580c10b82e481d5602d00000d0500c0a005e41600101482c059180000c9a1310740d4100790440048000e048040d00c2d0300c0300040e01c0a9046500c2039030140b0003c1c0000d41500154000b0b18800180f6050303201640e80c0b2141254a80a101c1e5502e1503004200000b81d41c04ca00c0a01804107040000c210f040f2070f40b01501e8650498002840d442c03440702c459801400540c0d203c08c262402c100341c507941015000340b040e0b6000c030084150701c035a60180c1e03c044082020103000e94040e80380c000340000307450454903050a05650b65101551000b40c000a013101240c0f20840681d1405030f03001d07880c07001c10300d042441c105000216447ca9070544105075580f141d95150082503005100030721580e55400248519601041104280d020140056a2504208001484260000714065a485100c40792 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 739905701 1250 739904451 739904453
    0x301081b0102120c24390a080a0e0d09030b1510020a03031b080103022205010b0d0e01060f0b0c0c040f0203090d022b1106041a070e01140304 62
    0x21070310201e8035022a0000010416248038030000601c5c007400c20300c952610000858003007038074540303040507203249043d00e19000800c0c01180010078601c981c04044c000044200700303400a100c10359085814020002918201031051344500340c0141c0d20160a204060202c00200e0100035003543d01030b10004200c080100002a841209600c00f1844071b2805090326001840c0711100a481d06072009048001c6071074060074400d0403080171035040c981d0308140c035103080c16400d503000c00152520030100d001800203104002103d406480c0980e41c002c4c403c00507010f880b0f0340104140e4096900151145250f030b850000b04001003c0c03101a41c00885001d108400e50b60000b906406040101c0e0300e4481e90014100031980d020003207a9802984108200e006407008401014012038031442e540c82004840d04c801c2d400e80100303040c5030010768900039003420a00351114007031308003d00b028021202030b69110140010310405005075410039501c81c1652030035455178155180041c15404414a0300c081c0c0c1c400110000b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 739906951 1250 739905701 739905703
    0xc0901090c030908070602090a0b0c0303010504052509080c091b0f0c01060f03060f090f02010e0301020904050c0a0324060c03030e060f041709030a06150e090a05120301081b0102 78
    0x40c3e0329041030145a4504050500c500650720090800c0e015000d052400280100e03400250340c0311034601c8014515503440d00003000701602e00a400003811040c00c5284a10315054800302004080054880e14045890300062078141003441c0c0003107024100700e10800810310b0f000da42c00341000b543d21081d1622a000315402116a00421a449401350b1801c0b0002c9801c1c18030702441070440344905030610004802080420a590042c4c00040c1001075103854180158080c1c1062240100b0243c0010304003440e00340002d0507102c0654000e07040d21400248240050342c10b0051800e511780b066400d100150340b420440800143e181303d11020401c00c85e1711503080510036005080e4640e604400c070b404a0911588030414610300341d90441396580d01181c05000c200c6944140da20680000f8040c2c03031512600e440300d00181071070000890807110900008520b0031106071107280203401003001021325104500e0041e00d0201c05041041d142c88041c001008500800288011034851007011005104445801030b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 739908201 1250 739906951 739906961
    0xd0225120b0105030c01050702090415020f070c031203061d07050417010c020d030606052718090106060309020a031211010615021005060109030f2f040c020c0901090c03 74
    0x1544100090350103050003940000780e0b050760303000c8007074911000f000c03401502d181c400c9079030094102d043c1030005001b0a161a034801e0900c8030354034015242c007802464001140e0310111085525800e100030a00c01d108002140d5605070f4500c0c01c00b008090f04100156004007280044400b50044090010f03100612440556004082d1040250168200c10301c4150180200804400061013462001c0540c03a01c40e00403a0300700c1d0700580b501c0380b41c402000504515692a0060307102d01580300c14000d100703600c840c1352558031049801c54481d0607040000b091825100168010000c140c204191a0050703a1780d03511210403280e0201100c160007617404804d07654032038512021416540780c0030340000c025010443c12400c00102d036003501c0300e80030030400d000101c40c0103842c0540003c015450500020348a4680050280c0c01801d00104030700304440c15a011061000511021094034541d00c00706042c24000c2c9000d2942600280c401c007a1041c02103001c1c0507051140300503a680707079104441d80034013075800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 739909451 1250 739908201 739908209
    0x305151215011e0b0a020f07150e0108010f09150312080708011d22120f12020f07020d0302070f0306020d0b060c060c030612060c03011a030c0f070c17060f090d0225 72
    0x44d200c410744d84641f400e5500c2c90514581c07021500ac64104070007980300e00c05480c140c0b0310400e80c4003241401c01840000501060510070003075176446202001007040e4190302c02d1210525600c618403440d260300020980c44041e40450030802c01448006100c41c51680c3c1c5a503c8a1002c050300700700764100c6008a43d00244083c041c29840580600a440c9076001142645141c1d00380c81388020304a04017001012440345501d05a40c80c0000d0100d0401481c107003548602c6c0a0103032044402540e20382282d50b074900e000354822540c03a039000400e0b5a0107403403406802004242141d6060401e0400422039407a000e005107801300380132001000a002d551456408810104080d08407000c1e0325001c12040075aa01c00c0c054111180d012007c842151f460000031a03114810b400c5540c2d05150080416112a412942e011501203c5041c40803e440210740e400c0100012200c00604250038090402280c40c80041d101e201d0a80016441c4030384e03142c001447d001205132042c086001401450201c8124044c0f13a00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 739910701 1250 739909451 739909453
    0xa020a030c031b1101020c03070f0e0402010c14060109060f03080d0509030d0c050325050f030a1821020624130e0d1d100305151215011e0b0a020f 64
    0x2000e0f000d000c842c0030500a0818282c007280c20140000080590b100d00511071514140b031942e000348195000107116581140c810f05010b074441c0030a60320002c43c0900005060025400140100607141550040c0401090015402c0b903150f030440c1c491408078856a40658002c50b20f0b94041400c0346000c0045a4403000c3e210000c0000201c5071400500710b6100b44c0350031010340c80c00c1c5520034420018103030080354001c480c1c965619000059141d15040e400c000e0104d03513450380e03400e031010b5030240e4840c0304000280700d60b110368200203203007806020500508034030900b1580448100010035011440807a0203010300c03080c000c00307c003901d0002544071800015808041c0e041c01c000e040c0110300051410704034901a101c1c0c2400402c007088407215604141c218a900520b800c0c14400c1c0c050203507210940060200e19000c0c0c61060304030104001013035141c0c0c9013000d0341c4480c0c4d14040c0843c0f1449010302500708101d0b00c8284180d02401c883c82003100740a0701d0211800000d8035900a4002c21081100414001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 739911951 1250 739910701 739910747
    0x20901211e020f030714090316090c0e0a060c020604260f0c0105030604020c01150e011e151404030b04080d0b01170f0c09030601080c10050a020a030c03 67
    0x10412030103006003000009022108840d40706040c9018000c0d10410325100d00c0f094103590b160350084416070402c148020410702c007081610b02e261410704c50b01f4501c1320170040903000d0901e05130140045500341d008500401102c00003900d41d030740ea4007032807104460031864150895810750000580e40c0c4125805542d0070f100d01c0142042c0b83d000719442d080343c1030300780043c0d9031441740303034441d4a03114000f0110b45400500100f0010b652441d1036409011a0006000001345010044581c010350803215003145a0704406240100a2080d0b00c00221800c0d00400400303407022481c0011003854440400240c0040c00801da030f03c6102844002c058600968000440c1035503418103050145275940884042d181d40d81c2403004201c1954098240c000412400d01d40f090002d99500c0100c007100c05018141d40180041080700030442e40d0300300003290103031180201400344044a44101311160b0310351803000741030003018030691503141d4002c9019000b090701804c001800e00d07191704d421601070b1412031248000041d80703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 739913201 1250 739911951 739912007
    0x9080f0105011424162405010f081005041e061406100e040506060c0d0e0306010608090703121b030e0103050c03060a140f04141510050d020901 63
    0x150030a034100c80010800c142e60f54420000d10800442809000000540c21401da00e10a03510758010001499220614a94410b080d50346580340c00e0000303840d0514001e440c00401c1d08007000d1064500400074a1044071b05c15203480b283c2e23a1200c030b90980c0000c400c2c0c0e48000160920100702e0183c0c046080400030300b0128101440c12200501d0303010707100090160100c000608604000700d012004220b50740350300c01080142000c02c070181c08014015900321a0521400c20b56a02c10442c420301c1d20815181c1c01c861802a900f0700d0f1910341c0590091081240ba481404904d40001c00c01c681030381d410403600b40f2103110747c0c0c0d400d581e51421155207101c00c03624000810b0615900c2194203200381401d0f601409030fa16080c246100034002550142d9122058040c10000c000e0400b500c1849003030b004c0c040d0155614901c001404072041d91128890741041c0200b0840c03800d110300c10115825404503541d080004420f0001003070b40c058845801040740d400503a00d0040d80c01603903006034410031510300e0b402d0b0ba154 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 739914451 1250 739913201 739913203
    0x50f060d0e1c02060f04120311040603020702090a06032d170705010b0111030a11010603020406030521161101020a0203010e030a0f0e09060607080d020c030a0e0f030d0e0109080f 78
    0xda2000707901030081c091070100740703803002c100e4a005d24032180052110303848903111210b041110448030003d0580c0c4582c0092200034400c043c00042585072401a1104d14030300511401c198002e12002c0150700d0f1000a10004030260706018500c01c081c80c102d10620b102c200721643c02480d525014000e1030111740122a0803548100420070648250000c0c407958044000540d1043d0108000001a800502100c850a8407641450b11030100c2400003040c400d540b81c010500300c07101074205035065000030702c1090b4805103036a6103194802d01c01c1c82c5585420814040400190b4582d40003c050f0018070034000b015a10070070a0300c0941c1e400600030000b02c2410003241d66a9408043c000c2d0110700943d1320300714801d01400303281a07440c5000e81101d9155440303c04119072035200c101c003220f00700404d1103494490300c00c0340702034100c80201a00542d0750314001c5101170540c0d080c000ca050304c1141410000c00d05600c0118503500d0a074540d05181070080d10303000c01a5040306441d00b0a880302c0c40740d4504c0341a2200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 739915701 1250 739914451 739914463
    0x613090b0103240501030e031b0321010308070204110c010e011b022d1c181703070201030f0f09050c0a050a060215040c0b03040b061810050f060d0e 65
    0x341c900b0000400f80800c07081c265a2412880780303003400a410304108030350090b0402d030002221f03641503a03e0b040d0903040801c1c100c0c0040e10401125400800c0c031141800d40c2040f406581d0013800c0300c406640d0f01d1590717120628896000000c4c00340791101c1d01512104660010b8903202010a0021b210310100e540c1654024400403205010071800013420144086c004981a401c2c03807814541100f080340d01c5d5440c1c1c03580881002d4510001d10498500e180540480c60081e9242c540d51350f903031458803034400740240d410012504102220b01c484903104c0714000b4000708448010381d0a0a0115060130075860f00320040510480f40c0081c1418528a0001c1200100300540480c0d0200c2b0701144a981f102c041c004411514015000542c0c021046c1031103002d0495407060744144200c08110300e07140c45660031324040d081a070342142c090341c004051202520b482100c4607101c0c4c1510401030603628000100c0c1070600e09510403140a00c84034000074140791540d401b00c480303542e0401c00070300c0144011046140d681e5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 739916951 1250 739915701 739915721
    0x304090e0a2a1a16020a03050a1a07051804180c09060303140a0f0c05070503241602060105040902060c01020307050306030f0309010f050912060702012403150902061309 74
    0xe00c91400843c241c03841c0305030104010030000e2210304160380e080349122a8085040c050743d00c030300e016100000040003084000d110a2107400c2c4101010488420901584030107060042409410302a60050700700b50294500340d24400c030b90105100380603132541c1c2450f030708030780010740940e010f00d901040d045000c0d006042141c0c401c0e0303103504030f201c1080540440c0e40900105e5100048007140043c2e07e0a21843e04071081a008400b80c0c0d0b046690307500000d15000c4c210041c0039083e404001a4074000c0c448402c0f05a11945104a5568542050700000d40301c60b4140110303441141c0d1103030f890b019034603002c0c00d40d40000c2d4010021503503803d10401c041d101d9001103074020300c64800e0412036a10b031507011054860115040c3c580803000c2d4002401990940c101205e09034006c0b0408200d051504401c00c0715600449190b00005040c0002f01d01040c003805400e020707582e0f80480d4000400003d50810000d20400d011004000f415040910008545200d42c2215210308061200c0200700c1c8506980178003402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 739918201 1250 739916951 739917023
    0x706180309180203010e01151209060b360702070f1d341727070e0105040c020c12060109150503030313030e041103040b010905090304090e0a 62
    0x242c041d0703255410703407001b405076555082c061001007066000520340b14400505509207062031601c080302d440c044508104c0c0544005441da18105402c0c2004a8003072071541d4652000180c03002c0e0784081c00b407182d00b0084c40c24150707115200028804c501c00d2015101614100ca000324400f665141091200c134071140c0c0c001d41c0b11100c03030b0128842030166452180c1340c2590b10000d440c0c40b80b1a00c000072400241d81031500900246905080050138a11040f600c82c0c0c3c040b250310a150408030014149031040e4402808459011020078000c9882c03204c159070454104840100704101010b1b070890a00c0325040070580c22072154650140c6080e00810a94141d0312100c100f08000d07241644400d001006c83e126050f007581040010800c01a940c1007080080c0c0c1c000c0c1030a0620540305408501114840990615400030204c2400200540320080c2c40c010301c541d400c00d001500305041401e4807032040b0b1040c1e5030910b544040c168481c00c028016600c160342c000b042c800400c014000c842d03241004035103c00185c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 739919451 1250 739918201 739918229
    0x105160c210b0f0412080406200a020c1005090d140102040f0608070f0509011b12020a171218160b091003110f0912011812030501060c020103020706180309 68
    0x484211030078107208541210b60105c00d183d80d81c0090300e05040291041d580390740ca4a44001541c145012400c6041603044141591400450310084c20100d0000455200b088000d8090201d10b03030050568a08840441d01c81e0f601030b400b071801e40007424020204000b02e5002113000900c44048a40d000c2c1100c80c0b42d00d030380a403948d404608580e402c8a00440c82c2c04100188001e401c654419018940078586a40c503000c08881ca070f40f52499003882c03610f0410300680c44005464208201940190f07202940c0010013400c01c0114204104a0280200403440c00000180300f282c444004200000c00041e0905140010944030b64a040c0140d10004d80f550182e01007000d1f02075024460300c5402d0011130545040c13803c0c4413a05038409281c1c1e1100301445e6021403a1030103c1c0d0444401c0c42030034480c541070702d0b0101009070103240090b9060300703007400d400034981381c400100511600b100114680c40d070309190050f03403858685890300c000d06104040b100c10020345920f020030980c0110011080c2c3e0826041c03005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 739920701 1250 739919451 739919461
    0x330315160c0308012601060b0301080106050f0907080c070b040506182d030906030a090c0b0f0301180e0a0f0b010b0f0d0e010603080d0209090c07020105160c210b 71
    0x81c00881881e0003000240704200400c07a00e000800c801d61011a5202e040c0d1028580c00556825220f03250081c800d44440000100404402407041000802e01907a05182111000b400143d068400405803c2404500f10002d80400000011165900d0780a0398061382420141072030340ea1440304503003030303140d000035855010b011010000e40109840d407041038203080550f1100003110040103500180b00203100030b106a006982c2e41100bc0d51107030036441000240c40c6501c0c01c2c4194000311076480591007032000c0100900d4191800202c0b815507000d01c3c0b0154cc100748000c204c90062805041c4c0b0030f00341c0181e246160400c41030783c5490900a0040401903410790300c0e05400385240c4604803180c07801c404108510030440d415034200004400c520b600003c4c44030740d26220090710f907021014649040da400188401286480301038076401408007000a0b080501c02e60001e05203100341d24400c0051103807101914108515206004d01a01c0d000b11079900b0300022080380f850104410ba4104c0701c0032005000a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 739921951 1250 739920701 739920707
    0x3030f0d0509100504050c010e030c040204030506090105060f060a05031e0106120e0f0d120609111306030b060405040b0d080a0c0204061401022d01090c1d33031516 72
    0x38020380c3c1080152030703052047c40041d11004c4030042c0b0390360580125032580300d1070b40c3c80388060801540540701800403803034052580e0703003110401002c1c144a4001b0b40e003040d410362102015640c0c000070900703196a5030f480740101c100038150705401c141c90580e0807000104c5e20b0341e446030544142c800000010721140003903803030250300d407604050340704129880700b0620745e02284500070007400c0c1142154001405a11000c5003000e84c2c840c0360000320009400160b00d044060100b11440c02007440780341c100054865900054020310403481341511494549800141580c1c0e6013244600c100c0d84a000c040e940c0d640e003400036240708038904060784140c3c0751400014880000e011504905003050780504030300780310000d4101c03240d000e100030030300b141004116400280b5030074030a5800c0c080c09003513202a0035280485500c100c44a5210392264042030a0030b02007041102524400900005d4020090220700408000c0d044150511001da0500c1484200c64a12440091440c02031420119102c4c00fa04203410079 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 739923201 1250 739921951 739921961
    0x1713021003020d1d0d020d09060e0d0602090d15060b070809010c05160602070f090e0717160e04050607020712020409170d0606030f0e0c0f03030f0d050910 68
    0x1942110038040c903400d03000e109500400490708944000a0420303042840810346421003106812143d1061241008481d010002d14049121510701102c03d141071150003440340400e2200e41e07004550740450f00042260300c0e010784d8081c0c10007600c6924000c4003414140e1440e00303035401c1d115a042c60900040ba80684901c1141c8030b01e90000061494000003100459028031200000d44040c00f4010b58500c101810303100010061169500803c0300500781000f0012036100c036441141114071384440c20f04c1244e80851883e003101c187c0e00b003148041526520b210308010100c40e6074260b0242c101d03070114003840c406030340600843c00f640c112240350740c610030b0681e0b4801c002d00604e506100310040800041c54503410840c50684a25011800b00c60702d1140c8446c1900302401010042d45c4403901407080a6140c464802460141c85051108442080034a40c54072880014075010b90388100c6a11042e8a00300102d9640004103001c280e41c2c0d444210f204802020b05807040c141900850100030f11320300c514060 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 739924451 1250 739923201 739923203
    0xc040501051207090815040201030f0c0806240c01020c070b13030f0807020909030909150f090c090913060e011e020a03060312020d090b130b03070219031713 69
    0x50240b030040e1071042066403000c003d20503810000b002d82c001c501031000384003030100400e1860b0300703c401d410300c0c0c4005026284680300d400e41161030501c0c089103185e401070000d90805002e407400d04105100d590320001201400091002a1100003226410080150b00404040c100102a540000d07207440ca03218442c4910300c8046400507d0f4903007400803400d007844a417802d81c464070740f45250400320b501080c080c0ea403c8505c0b075140c0d000442c008002c0d080c0204a81da010602d002c1c0d07001a907135520b00250b40041000c825034004d1082c800080c502100303100c115500080c00030620660307032800104981418070350a07001c98030981048089a181c4c5014001c80401c921b640c02428481c03000d94201d400290480d0103c1d0082507220a070020100b03030b0138281c541049400d6806800510041000641134040c90303446001e110804000c0b000c0f060081001b07041c141e07850705544075600d0b25642e0003285400c15200c030028450708000c905604254014911000a00980300e80e280b107a9145441d0074151012400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 739925701 1250 739924451 739924457
    0xb13030207062111070b060d080d0b030a0204060b0403050706030510050402090409150f110301033f020a0b1f05060a0c060e030301140904030e090c0f070c0501080c040501 75
    0x21007070051a02400c12032039400301c0c012542a008111035414000e841503007401c10313680400025a0814072040d841c0c9558410425100b40da0101c19075581d1031400d201e1001c2505030341d81e6402080c0b6845c0d50034000c0105c6035070010418060f1a4940c1311104a540c001e100c111801d00c210040055030901900179940701d00c1160960440083c5004180801303540903c296031740c055514880c140009201c41d90216580106201c00900400f00d007803050216802404480c26025003407004000040e14600c0d01c0341a9180f04040d02d201c0e4220202040e00303440c02620811924aa00707070080d1226600141c52200140582d080c2c403a25250a07120001c5071807802c50059000341c40c201e05004608012004000428041c07a05410109158485504031f850403c0e0181c5140c0000004016034034000c00baa0803c40307003c8502d01c80b80e041c15136014014624800409001d0a90600003400e28840502070301e8a6250f21011a50344241c81e207031440305840d46014150100e00c0785000b00e20b01c8070036a01589c040c0c07507060f1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 739926951 1250 739925701 739925713
    0x40f020d0201170f010f09060302030a170c06010b07030e1c121202040f050a14210a0807050604051c020703031d0d0c0e13080d05151c0b130302 63
    0x5020300c1a0000000d9040e03040c04201144489500c1002c148a4850b00307a01c03070711300c00650500030400780703100013030b8060440303d41040d03000d10141e42c0c08200040c260b5403100850080512591240f51302d405000e44018480c00303800c0001400c18003660003882480c1c440e80d20305020241910030000f014000d8065060000f282d10b10311000038a907001603102c40381e4142000550804402c0000e410ba90003500b00b030581ca52a69010002c0d804d06d2903810026022140100b181403600c10040368810758a4010410400500082c4011000c0c051049080058020b100c580c1d13241c080e4100300c4c5e0303a070106460440c0d843c03260403041c206401c100c45aa42c521945980940b84d041d01c1c549045030805038040f60300350404900b00c9550b25980c0c0d10503000b40014404c03410940e83c41c2c0352040603003400d4002080c02c002c068184201800182440c422039500c100d09070b40021703003502e4100c01680d03a180e5880c1020740201e50507040c020710140b100d2840217420f11940086015a81304554035030020b1400900a003d81c0c466 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 739928057 1106 739926951 739926953
    0x3062306063105011d0f0d0804050d0602071b03080a0e0111392b0215180103110315031005040c050109050301140a0b0d020603150f09040f 61
    0xb5181d6817401c0001e41c40850102003000c2d8042e40b160340840803c1e001c0041c50001e40f006800040c0820002d00342929084000754403110054940926000381403145540c3c544003901501d5118401500704488080103079044c51540443e581804221a800e044140080011020307031b40301c01440c9201e081000c00340a41021460941c41c02000f10740441c500d01351140d0036041d14118140c42041d40302d0081e10040c80800000080007075000da00c0f0756a02da801c07841c4602400e500508900e1012200c2d004078015011110518a0300040240900020f00c07070164810040c201c1420117000c2d0390700800c42ca801d034011a44c0c126011160382040100234012940e00101c220702901c03094008103d00c4c009a0007801e0640da004042403080e545684071020f441d152010200e04403603010f010705490342881c43d00304804105c414081805011040f000713a440b4544001c4050007107410003000d03009203050b = true := by decide +kernel

theorem cover : BRFrame.Cov 739748201 739928057 := by
  have h0 := BRFrame.cov_init 739748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 739748201 ≤ n) (h2 : n < 739928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
