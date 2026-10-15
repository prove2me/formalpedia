-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5378
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:40:26.240394+00:00
-- url     : https://prove2.me/submissions/bfa682f2-3029-4439-b2f1-d73b047caba0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 967086330 ≤ n < 967266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 967087580 1250 967086330 967086349
    0x180306060102010e0a020f01050418050106030c030b0102060601140412030c1401090f030c11091f0504020406050711060c0f070807050d080304120903080a02070306060b07330515 78
    0xc0910007800042c0d503214000b521841c0010000307000d01c000c5a10f425440c0e00400a0306d01400d0000a90301a0030700300b0f090407010308401c0c444c3c41e0109207050718040180d03202e8052540400c106800400c0d440c0c83d51001115154003440031008040c506100200d4407135804521088464060f54035100c0d00c0c02242801c1d41140e1407103c0b01101c9a1400313001400103004044021809074050400704130401c1d80713041900b1a81e86418510380c0c044c00d00d10401031000c0710301e046542e91100311448008240e0b01c400c103010881c480c82c069000400c43c1400030b140014007050a940221801524850030305e161800c41c14a1312204503503103da5074124076414451030a04000000080c40700300c0740b0250030505510b9150041c400680050003150f064145801401e000f030044100071179008414aa488440c0d0f4002515180c01e030100b15002404c02b0320000b2058007003415213a80780d411001c012007134100602601c1090481d900501c001d0b444114208102c10418440e19100e100c0e41c103410340c810184802003011108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 967088830 1250 967087580 967087591
    0x10b0a15030e010903170408210a0507110705040f0f0606031b020a03050f031e0403031505150a0804020307120b011a0a2a020405100f150206040224180306 68
    0x1c4c50b01100c00c2c0403d0f8804038104126000c604144151b88650170f040074103125040b2034102c1c601400740c6040351000c0300704030180714000508080126032503480c021100d020300104160304552080394148040d1805500121841c40c0c0741c500000c40d204152040011303944254440c2c40829620344403070404403441a180700c00c1a0700c52010b009a01c0482d5400780140c050f075a000e24000c000440020304485000000811540e203681d4500c03803a24191038003c020f400c05045a0031151204000021603081c051480c458140c0c2d840c9519040c0303190b8003400c884c07042000f8002c5c0e906104260000812006603541140c0d00c60240103a4503840d030600c0412513000d1f5207042c2415104c0400c0001265456000305414070881100a40c00c6440c1c034014100c00070104060b2010b5803151521041c461080e880c21030f00b078111680502d10b5821585c4e01c80f00c090004000c0c0c00d5990142c5c11907000140140760100e8080b01204605600c120104403c0d162800e03d9000042e10300800000e0030f90304800791404105999000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 967090080 1250 967088830 967088833
    0x150e0f03040312030b120303091b0a0e040b1e0a0c02060c12040b060102030d0c030902100801241e0c020103050c0c0c0f0f030d021e2409010b0a15030e 66
    0x907145948071007942052524410405950320807403195a5103a09451200309a588107c0343ca904000b5046922a4601a0050f0b07003e00035a6107026a4244015001d00311400200403000607a01c43e01c41440000c1d005141210f6500c402034403981070303004240018007400361800009107c21032001c5c0603250003030181c00c0c920000028807001803180550004194442d6106c0110344013501c03034400507031840c01046680b003821400c00e181200305a0b0300d944031203466402156540d080424282064030400750a0003445c90002c503201426400c20000f240000080c12645444429036101d82d1911102d2103091188000282c80400c0c1b48003950f030306014194111a485141e9460b080315441d01d140d80b41500c00d1000e004241030660103c507961441d5041c10742c210081e056501c00c2e6810440251900882c07046074650704966502884840d10000c0d406804458241c1c403001038440700302d4141040d03880240384600d5592550800184c6444906081c80282414600d645140c003948801900340c4440d464005002e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 967091330 1250 967090080 967090087
    0x120809010f0612030f020f030f0c011406010c0f0309030c030602030108010b09060f0d050c0619080702010b09040b0c13030c170f07050103090f0602040b0a030c0513051c150e0f03 78
    0x5043c0001c841006840d03040c189901030400c51001a801c240c500c1c41c0d00507481c000403611501c0e681d810381c018100d103a0100c00801c0341300d400d0752210b5105141a02c82038001001c1c2405140050f4071608911050f90180c100002031030f983c4d0740c0f81820f03178903207400c2124504d40210040203594424000d00042d25012180a0070750302e041808980c42d2000403a4840c0300f020740300955001d006090000300c00d2018090135843d42c1d0640d42e520208508400c080030340009000c040000d8036684184036007120309a008007501d900f03468503150000c24600c05000017040ba2002c00401d085520382ca00141c000b140f0500d0001e03082c80c548014900349001040c0c0940c0d10350440c114180c90300002190501c282c5034242000a12042c880c1441d8540c26007021004020034400640801d1203c141070140101035030999042c0202d19600034121460f010345004100e1800d1042818016498800c145201c541204d50102c4418009a01c0b41401c0305407120300f4402c46669a440030004940c1400702d2944828250000c524 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 967092580 1250 967091330 967091339
    0x150b0a080c0d030f140c07080c010903081215031501031202192d03211406040f1e050108150106090b030702030d0c120b0f0d1e120809010f06 62
    0xb800d002c400e402420040400f18105009005009400c3c580726980082074440c80c041c4c404036a5003005000c0c48860744100091006150300c21003c00040c0d0790b018a040c0c1c00c00501c400030315042c1c00c000d040c6a0018110b5981c2e40902e403810003207107200c2c43e0515101603030f80d4558148960780c1280c40b04014219080100d00c218209004004039040b035602a10b000811404240700420030000194039074110080d8a0300e9105040d842400c00c4410072604015281416604040e00d080390321629103028101d000d5400180c09160a51080c0d5400750003040204404000e5200385505001038403003080070f0740d6240014089080b0401820783c4414080c00c101610394100740002d070940c3c10700c0c851011036400000020340e0142c402c0c415101c1c4405049030038451104a04c902400c020010078048044c9498144100311914062155410091001e0f040c110080c413a900d8042020040d4008148801415510740e00080e50510352089648680e07176030f0720154141154041d080d1150a2504000c090400c0010b00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 967093830 1250 967092580 967092589
    0x23070203040803090f1f02071d01030c0306090204090c150e0603070801030b150604060f032a271706071d0f012705190e0c03040f150b0a080c 62
    0xc0313240380b00729040a803800c40d540000f035020021007061914a10800c400240c0181c00040d11029104010b15000c449200101e10f640e06a60920000e0410748110008002081c0c107035005010b800d00241020602c00103a494100030210154448120a484484000c3c08594009612101c00c501150807601c0c5050080b0000d00c0e118060102030b0000d4000707000300c0c0c451560903000e5100382c1800b400494031103075035020140c807203520b002c0e040c00860300785010a0003000000001030322201b400e440d424002402288100c0d01e01c0400d08145008822010300040b25a1201a25900618000c02080046408042c80c0b0703091590240c00d51051090b544141100108948100d2001c2203060b40d0210141a845004850850744000d004007501071454034465120104049942940c90030b50304881040311032242d125030740869104800c0c1d150300170f0380810110400d480055801500880340102800041d03101c5040d810b41036140c0f0840b903541c440d001d803800c1c14540e0580d8000d00e0300c40b018120300e240000104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 967095080 1250 967093830 967093837
    0x40506090114030a05100204170303090a080a030e010f020c2e020f0708071b0b0406080f040c0f080a0c0506040308090d061805060a060f12080705030d23070203040803 73
    0x200c41d807003102503060003980f0308204088440d034001c1d0031100401e0b100c00304107000b58090b0050644100098076020f81001001041724010015140104101502c68945a020390061000b100426803a01407060f9403003001d020b960070078102c2e1480141e03501c0c44d22004500c2c00c45455510046600c001801c11680205001c0300f4904102d00d0a0141c0d1300d840401c1d80150a00c140704009021040115079030b4103001c40e04c0746500070340b0200c03019042d465072940801882806907104082c0001e400c5000206005132140718141c003d841646000c20880d01c5014041120003a6040440150304c5100c9200070b001888030f200d00204400d4078a00e141c241140c840c080b4902c58000e640b801002c200078290104051580315168005072405100c404001900c3e0043d01e0742002c0c1c4000148a0034a00d02040345404501c99104540507402407142401842e40e42107030540052000740c1c0d160000340204048a19a800780941d0711102c0380700750702d070351040507000e81a000001e001c150440d442800103100d2000d000046 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 967096330 1250 967095080 967095089
    0xe0f040b030307031101050f04020a0b0703050913050703050f06281a0a12020a0512040309051011060a150501081308040b0301090c020106081b04110a05090907033b16140405060901 79
    0x2582e40e01e08dc5030509603810b00ca01e40c01690002404803100e50402c100b940100d000301c480da80c081c842074860b940c51000281e41955856444151800d00c08214000c6009049440f03203610100110103513104207058000d03c00c5001401c0d410310008610305000e6100c43c42c0740071148410411801c0002c0003500810780d0080042404009610ba8085000c0c980259040402894014160b000c0c040b51503000411140410361100c0141c0300b0040403405002c1c1030b00442d120b8181d02c803401d00c40307540b4000045500d90350103013128011500c0c3c2030384c1c140800e000100070805005038021403036503075140c00c042c07408035540703074200c6d03c116450301c0b20510080d8000714244200d1481404070030b402401410000f4006c1001d0402c2805540d00041c41d021100d40003c0a4524070801302e070000c0c0d690b51590015410f40f100004030f41c0c034800010311036418030000101a0903140100791050f00b002c50b6810b00c1640303843c00341e1590b4407080c01d284d03104000341040da0300202120f400954050010303091400c0170801c0404107006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 967097580 1250 967096330 967096349
    0x712110123041a360105031524070506070f0825030e0610030309051f1214070903022704020f040b060406090e0c0405010e0f040b030307031101050f04020a 68
    0x6042c9090200c48041d82d07124050702401c1340b0281d901c1310710400540000080382c501e0505880b404c210070340c050001d8a00c100015203403020500c54a40c02c01855101d4a9078200c0020281d44a010700d201c484009440d180e44204020f080c03d0410075030140c803000d82e0340024030801990a003004034204251400b00c502d080c000b0202c00004840403401d8001d0902d841d1100d01600c208010000b04014060105081b640a030f103507003117416251405d0140500c0d039007480095045400c8146040303030b4030070304110716500c0c000360002580c0c1400c2c4281d001c000105407141c0303000400a00c828410b5181c6005080701c14a51001c50320040704401c440380041480080c0080e00c0f801c0a00c101c0107094503250020512443c00074207440d500c40e01c40402130849985805680611102c40000614000c0301c40d04680a40b00140c540c0030703520201b10704200d803610003082c1035a00706454549440454a0803c081c0c903c42c1d03c039403900135004203400009401c4440c003c08403041c0c03035104000e000158071000c0c035010030b0b5501800c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 967098830 1250 967097580 967097609
    0x506130b030f030c0610060315060e060702060307020303070305071e18030c240507110d06090501050c0d18030f050c03090319051b060d0905071211012304 68
    0xd000a040880300749806600340000104590303142c10208110f84030b650981c18945103203850300c06c1142207035801c5131262402c40c0d1015080c0b2505020f210f2503003210500600551812002c0e5010410640041d1b40001c00343c5d002009125290350180140c9622048615250b17910030510410220444140d0410006102c1001e181950461408040c40301030750b00b0103040f5640d1982d620001c0041c00036407541ca00341c4082c0c2180c83e00180d110380100c6003126000400300d01041020010040080d9030140100c2c0e20f03c0e1741e0411200064000e0190501c500200101141c4402d10101c01c101503c00b00c10078203a208a809180c400040c0e006800f00c00003d44510300300b40c0b0750712070348001490342c81340300e40c0c072503161140281102d150328144018049480c40b5400f0317145800720f03403042c81c007851010700201540010144900c040c00b02403a8000c8809501a200b2503403129901d90101d545a0500c40056510103c91403061000f9600941a4902d40c0014100800d1944210004111034001c44c0203541f000b0880a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 967100080 1250 967098830 967098851
    0x311220209031e07150801060807051b10020901090e0f010b0306010c050106030821071e050d09060608010e03120a2d0e06070509031002030c2218050613 67
    0x10001c40b48140000d191400a0365401d900f0f40c0c0c4d80b9201ea10a91a82c1c440d0420b00c001164458608207040300c81d5919104680d896404068565402c0a580303801b40c003c2201c1c0d080c0c0d460300200141110039120708001a5100401d800061007512203400c8800350140c5501446280700c19a111141128410200c0f00c0d03c0381c039010b004841c04044104080e000b5030034000080b090046c00c03001030003264610020f100355014103500c0c6240c40041201c0c03a0021a05a0a45095211901084038803000080c640945851514240842169800a0280c4030250780e02d406000b5403800b40b0884030f200c61117000640c1030016512203031100103801080020b0180d220000f0702000c96030034044402c4104100401b1030346100155a2400804042e05601d0f86072083d000070501040c014400c0398044040030300508a2402c03048400c1002e54805001080030700300800c00b05d000181c681c207800c140c08050b0b40880202510700583c0e15088507400c03d40c0400c0c949003800b444030076980c030303540708441c3d00c0703110004030308804007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 967101330 1250 967100080 967100083
    0x40c0c060c2d050d090611071a0f010521030408030f0301080106211b050409050a030f110703020d1716150216140a15201e13080706030204031122020903 67
    0x7000310842c94947c1c0414044100070099614400f88124070b100c405041e541c40041038100d0783e00b0310034a90001d240100034196103e100c607946000008c0842100e290a0391142e01e02c1c07a540c00b1005c0c1d06542c2d5004001885903840a01031900103104540304d015071145601c016406e5818500302c01880c0c240050b03a0309443d42a03601c03c40c0010480180204110406410500c1c3c564610007012400100211301e000e400c84e00600442503c407070080018140c050a40d800e10101218401c3c003528501420045d03041c002c4810760081c10320074440541c60200800ca4500030b00702e008041281c0454074010b100c0c0d04050410588114645034001d011100301090801c21642824410385002e850f42c40340000004000019030401c8041d540203042842c89000310042c103c5040c001c0c1c14018100303142d016034004004031094041c0010383c220011400d251303665003d41a207440002d030f000c0c80201ea0041010803e1050424400007249000da0351100662418118101444485c40c1007014041d80890180b4590302c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 967102580 1250 967101330 967101341
    0x8060603130f080304141501090207030c050a0807050607030b03100f0e060c1e09061801110304030b0717070c1704030204060f21030806040c0c060c2d050d0906 70
    0x8005251000b07988a070700384900c10f0b41c02141c0070b0700c600c003e259500d030054000203a07821042246075501e03207036a402c3c2802c0e10069880304105a08000038400c080c2c0c0842c01c1400144007031071040b840c0c182e41d000f00d072401ca0b0820708010300b14000e261602540322059140411000a8030280b0b100014000d01695021402042034800d521082d1041d8401c00c21004d011000421460340c075918000c051418a20030005144510213481e0341148050105200860032003500b00880e000504064000d4078081e183d0300d1568129600984113041042d051104080e00080c401d8030011100510004c50b00d000d103405014030300109801080d5203003504040c0b42c0c01140c03005950166600800c03c0c414682d90f0014150030611078094080751035111140002c8969602c0e08e041115075041c0c40d004016954841044010b154034501041400115500d880000b551403003030558a4200742c0700c0e1942c02c042c20510340520503104001514108001450405180c0c2100a9903100c6010010202d1100d19134076041c0301600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 967103830 1250 967102580 967102583
    0x1170f0606060a12021204170a050d05060604150c0221060f1b04180f020703120c020109020d06020a0810081203090f1501060315030b04030c170301090606090b07030806060313 77
    0x184003017000354442c1200b410302c0303001f107000d1142c021880268100855503849440d03e14400324000700002541aa11030300400d070700142c010041c0f4105583e54002c003c910031708404850000c0c00d150121821450401d100000701c6400b240800d055403010b282003541c642000d4040300e2008003c500290b4282d554411031254040000355242c0c565640b00c0f00d0240d500800100018058140040000c0402d014825142c8442d09581c501c45010324500c1c5040040a01e600c0c000d0455407181e0ba90805600e070100003c11003131180000603500c6002120040040070702078140c0029074900b080c01c102212000a15003143c001468146a0302c0d191405001d2400007204c1e02031240f4007511413103000c280020a0341c40e048036450b850911442c600000302c03036080001030100801e041b1184020402282c82210703680b068507c00d11045c454203104801168840c3c0090740300c09402034aa140a00c440307948005148006c00051707880034200078203503a01800c1080300a042900a400c04000030f40880114840d110405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 967105080 1250 967103830 967103867
    0xf12171006120905010e101a01230403020a1409180615210127150c0e1f0f02010e0309040c1206032105090108011505070c0e01170f0606060a 62
    0x3006100c18680c940510f540e000700140e1400d408081c09509101ca054062023050791910300300d48040103100352000720450065454036062101000603100d4035205e2001d005402c0351400c54070101d104000c0c01c45001000209507441004400c040c0d22000104560084081d950440c001c031080004a0000f05600e510398405800c5081850350007203040d03210f8080641c1010003802c45840f0700e90314082c41c0200d02c0008002480482c5d601c1a04070a81e808046001017905e00b0101d64000c00e070014900303001ca070103080d07100c0340110b040801154101c442915110410b00091100c04025a0030130b0b240d000d80313441d03940103549038250900780900c1201c0c91018002585420400641c03030341400d1045c240b09184451b18480b5003a20400914024001c1d94145041607440710b006a0800b2242404035403000700100c203011051000030f001881c03074021040980a420400c122a61410a030100a01d0480d000111283c0058142070740c07400780890746661100c820b072200c0c0c0ea10403d00b0301c1200d080c4001d07018400030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 967106330 1250 967105080 967105091
    0x40207021806040518070b0d020d1a030d1719110a020102071b0806190204080106030602091302030f041e0f030c030e0a06090905130f1217100612090501 67
    0x7400001d8600ca0302402003500d080005030380d040c074549030205889528007503035407011303508101c0b00c44424010400088946000b5091030900041c1200f40c03201954040e034040004040f0b04014103040100d000303800003c1c5051560b1041124500559038405018000e00c0307611106107a0f2101c0c4140c02c00400100001d103041c6c1d803003e1a40c4001e0003500006402c0302d407854628042c0b070340c048001582106036580c1c1c40c00351035036484440351602c080b41d01410107061550240000688000284580002503010307000259441c0035140070422031543c2c0040c114007082c414014080880d80c00f0074001c0d8040e510038085110b41d1024524103803001180100105800a0030b6880c1c001c0550000814816074400d0300d03403c010301c803003a040010f62141390040c20f001a007194000c018650a0380c115540103c41503540711086125034031000e00b403654961060742c3c10b5410213181c2c0d048650205c031004e030001c2107004900e070906016100700440000d611611040000050740c0b001800e02a6000030300c817a5000e4000c025 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 967107580 1250 967106330 967106359
    0xd060e01020f03010f1409071d220e0606100c0803041a011508090a02090a110f0d0b0306010b040b07020d060b031b01110f060f0426070228060e04020702 67
    0x424190340200e01d015001c1d106c280115007490354100303000b81065200c0040004c0c2c0000807621300e501407800158440c52020304040c0030411454601d101904001c0080380440c103140840d0314201c00580480d02a90001480030501d580c000c00070340b04980d000b0340e641d50b241c50f01e00f0504409074544c107082c04283c480b240001081300d520320f0140340c280c03440d031580f114964400e10b0403500c40402540182d000000000060703100c20361a403001000b03150a401c518100229564886925002007410f81d07001603803060003103200e01e01046118010138074101124a050300305800031003070380541750000307014001c040c007a071040003944c0d00902c0304140064202c68035003144070544442c0e100b0281103107020403180c29401441c1c0801254410750745804030b004007055150a01c40c8103100c007008206075181400084e044114a042040100c01c2c0d20301450525105c1c6040c4c0100038100c03c100c4c0e1403012002803000c040748030b41d0405140100b01c92060030b0a480980c040c2c03010601a2203403d4000b54001940d040340c0780c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 967108830 1250 967107580 967107599
    0x2806020102090f0402030f0105090c0d1a04050c1e0f04050d0b07120204032003030909100e07260403050c0d0507060f050915070210050405030d1a0d060e01020f0301 72
    0x1c01c0c1c420840710540844810f506100491106850f182e044412840061100307041101801da00311050b4141a403a05660f500e040c0110b1384800180b01c1c540103046041b0039039240c03a0080c65003102d944803550b441e01244804032103010440c00c5035031001c51804100010000f80e010700782c2d40140400340119483d204145058610030f2011550100414010001c07210791881038801c1c2c40681b42d02c940c640102c074100b94004008103490f5607600b54580b10402c1000016111000742c24007d00c088030200c2001c60504a80d01c600750b01c014010030420000c500d440003070700c64050200380c001010500e0305200f900c0f203040071a901e1160100f8004030707105a8082c0c1d072005610400a0042ca030240c1010000d94a044404c2011342c1c4081d2000d45156100452002d00b00b680d000c0ca003600010140122401244c1030f08a0005984c400c440a46246d0404540981803550b0383c060b074001c0e41c00250310071003045840c9001412a145440d8098807481c0e41d041c4900d4044401d604440c500031002d100c2a031a5079480d136845 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 967110080 1250 967108830 967108837
    0x1513030210060f03030320072607080301051c050d0e010206011d01061412010608150103091214040f3b010303110a12050a09050d08092806020102 64
    0x110014841c030051441c100d5041d00ca503105855941c4a140a01465034504501814180c00c01601c100f10180303901802e400c0102c000c1800a2160701c1544e0f0007c0a504080b040003a080d948000400c0d00700b141c00c0004180204680c15034108880c4940141d40c0e0110484500078107004c000c046124114000c004150040d101c400d002d0382c241d088500c181e8a03442900500d12003c40c554480ca00c000300140320342400744409018801b0101c7c3d8503410003011045500f00755030b003039014001103203c2c00c00303020b0000700c00072a0a40c2980c0a0070b06001c2950550f458074240192802d201c8100540c83d81000c01d00080d0740c044600901c01c0000703042c015911016542040400f540000e01e12600810602004004030304090280c00079046000700541c2ca10303241642d21400220381e22a8501070196240c00003502c420741c8000068040d0b80d8031340c5501d9204c0c1c020b0909403464110354810903001701504002071241c4100c03203003010b05450100d90080714281100071b503c1c030341c85401c0da02103403460f0108039031f503056014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 967111330 1250 967110080 967110083
    0x209040b251107060504050315062b0606050429060706020301030c06020c100f0f090909051b2202070602070209010b0d0516050a1110090602030402031219111513 71
    0x560f01d145aa4000c241d419220301d200f5541c01d034011030411142454800e0030710b40e0040c0081c007101001a8151200c4040d00480b0b803400d10181520b242c440188145885003c0180c5002c2e40c080100103029241e040c411035890a50325401c101c602e5050410340c5800c400c0d20126030b4401d60030741d2a0350712490030007420182400388000502c551424241c0300d00e8003280d050700d00c903101d1700d0722050200368000465001401804000600603540400220780d11248103181000b802a005041c0000044000c0d20400802c0290288561905443c81035496806014241040d003000c0005983c2c82d0795103806c0c4083d0080c03040203907005017084000503043c1245401840c20300c82040080080b555082c140006211000700b019000810600c0342e441e2050003640c3c802c4c505d80da84801c803814241020300c11030540d40381140403103010740c02006010440c00c003004150030182400d07404604150300d401c842c100544401d00382d1010070220100d0000549802d010605500300310b440e9090044c41c000204843e0759202410 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 967112580 1250 967111330 967111333
    0x3010621021c0218060d0c06031b03110909040f080301060815090f0f04030320041a0316120b15120f010302010e150c03030709050910030209040b2511 66
    0x40c0990701c0042d2449000c1c4865000b0b1282100305488085502d4102c002443d06400505010350500403e4000c50020000c040310740d80030540318803c130040040c540c001158803040c036051901d40030307540c3c00c0c1c0b40580d10b1011081d2072504242d80c1d0f608002104440388200500107800000002c01c03c50b5100301a140b080c01c1c410210300c01d0b02140710078403030b40c040c08641d01c803600c81044011a0709545185102c9400070b000740340106130248c01d120951100808082c00a4908030f001500308040701d00707050903492100c0a90465400d500c0c0c6840b02611a50401e55080c041124031000785039400c00b594440d0680e00406000f00141800341203505143d580f2650024050010000000b03010b40c01650419040e60307030696900c403015220f071051040344152040440a050001d008a040440c3d0401c040c502c0b50009960b5040c5142c41c0c03600740002c0190250908103d445160014405600c65441e00c1da0029801416500c00e6600c240220240d949130044902c2d5290902075501400c55001411101d040f11000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 967113830 1250 967112580 967112599
    0x140601050910361d16231f030203060f031b15041706041b0f030f020604051e030d0c0b0f0a2415050c0a0f020301062102 53
    0x44455518054801c0f500c04000366040540c542c0c0c6040c8a00c400007402e145106140080004258203444d0705003030303100c241d6190a24845480508012401410203c004600c000c01c0c20080700b480b0591404030040511043c100d4101ca00351683d11a507000040a01100c1050101c61900100a076100381c2e00c181c070076182e001c000c900900d008220a501c03100400b20147e10410b4100c280046403032480e42051b0802000c1c000007c0410746900100100c02241c0302403c15450b003072608004142e00d221603044055540c910078403a119100040f0350070303240c000e104c5100094103840000c1252045400498101c1e400085412030780d1100e01e04034010207000c8080c0c2e50b802590910440341c41507201c1c4007500c88010400810072201c0041c4a41d40c011008003004950b683c42903007035040c024601140390307450800c6914104a050740208401040d10028501545018655401c55039112810840035000a00d000c82100c1196403d600180060500e80c0e00c2c0090705000b4404007081c40400d500c01e81c041e46408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 967115080 1250 967113830 967113841
    0x806011d0603070c020a05030304030302011d01060e013b0412030b01020703081605060115030c031e0c0306050a0b130b21071718160302060319091406010509 69
    0x20369440340403809000da0b815903030ba0010403070b148414800706a07040450006c000c01e00761000c1c0000c1000e1402600045030161010707001384903051080c0c1d03c0030743c42c6c0d16004050100303030054900b1504440440c12110428905031248050050280da816402d0038410700410011080600300b03184640d0203441001c45a00c941c11060b0203844101e4500d1707006030007803441840090041805410068014040001c0740700f8150341c0c0074982034080e0000740e4030700c800440d61540143d00d40100715034800d1a1800344200080500014100c01254902c003800d04c1d220461040312620aa2180000388001400410559624a01c800540c1d021400310b0005281002c400b00d03881c00441d044611241c1d200c8240303060302000f00007001000740301030308c1c00c0104107034400080c041064000c000c0b4040d502d0801c440010454848a1900d841003500e07902191385011081000985d403003c058962220030040c89440c0c44840c640c4000c004e02003141c0c0104180c0070b80d440400c2075040000c5840c180e540030307100303141262142c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 967116330 1250 967115080 967115117
    0x31503061008060105120109020a0e1f0305060609180114161d0d0309030b040c320f0103060305060c1207090b09100e21060109090309091503020907080601 68
    0x25805020302c10791141c0010070807802d04e0100281c44005050001079508004c3c0d00044002e140341d400401f11240540074018280e15840301c041009400c4616441020b1841e0340d40360700ca540092400b4852002c080009000c559001148248090340384000c100c410799065002030307500c50960300281000c8040b0060118603001e200b540c0020841c403554140d02c0700d01c040404c0101c2780c0c00d030800c07410004902c40020010300700b05000e07409240704020301c0e1041c908150780904000c100900c4d000e6400304c88003064500211120030662020f10940350b60350303450b0b05080160050309481c1d000408501c0394030b0400c06c2005156001c0d0000c2c260b44944000c8540750a0300441c3d09200c4c5000d40108a4402c028013141c518020240011445a07070401c01050910f0310002a0340507500528100031040c0003503961036004d424030000380500728075802085115110344005003051468020701240716610241c0309001280b0009000c000d640c028150045032503d04001080c0410a40315580803a041030ba5240302c8030030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 967117580 1250 967116330 967116361
    0x42307030b0915010e0a11040602100c09140111030903190210020a020303030708090c0a140306070f141c29090408030f07030e19020315130311010209040203150306 72
    0x50f030260243c541c1d003000e820032007014002e09003d414903560303174204000d018008041c00041150750050b005401d02d0101c003000741d404044a2504104032100d0030700c10400c42001c003202c8150f00780b0b0b00c20341003015600340743d24512400740016031621844080c50345085200c0b5081034179910070f0343e040040d9a8044030030f2f69102080e20009506420900001b03800521820352a903010302c0c0c880c00c440c0355042c46000b04103903d0041c4c0001409000681074941d860504100003a04411946491200c031001c183c0300a00d081907000800001200000342ea01290401c0f000303030f40311503510340310030403d100a008229001c0c02c95041e03c1035a004c0f4402c1e8040891401c0401c0313034807868000303004a14640d00e40b9030309135441000810100a065a07498034000440d003c0141c440f00a2a0383d44021000400d030040600d868210b800c59403664549004026200e1000100406107550604140720010300341c21559000e40551640301e0303001480842000b40c3d400e11000c900030303080300647c155405c0740c49060130300705d4460 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 967118830 1250 967117580 967117603
    0x10c17071511130f0e070f1707110f06091b0609030615030d030c020a0b090a1410060909080d0203060315150a08010203040c050f1215090f0d0801090203042307030b09 73
    0x10603140083c0d2141d011f45045805442c0d81d2a00049402a010701d202c110f1034242e800c0c1e00042c49050003039881880411400310241c076460002c0c40c42e881c203111150f95a85850302004104800c1c445420803540322202070340d81d410002401e4074000d00c0c0c041022100c49100c060514480e11a2101c80007050b8042d11400006072229405400321110307603224002e43d024040c0c00503180e84201186c07140800d071a2020f8000c0481322501400400d071203d03031040103584664208180e0940307090002400aa103510455054030b13101c0c1405612a030710301002030f0501c0250110791010740070b81410450104418000b450384c6100c21117601609a403124841406c0307000455009181850580040c030032450b050403500d01d1100e0061415850740500a81070342880e032611124190f80c403011040c000c02c00c00a100507402450000c00070520582e5030034009064a1040c03268100c4542c0c00000700381409200d5001c40b100700107101400d401492001b1086039101807a01c81a900707208501d0108110003000300c2d40302c5618 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 967120080 1250 967118830 967118849
    0x1502100e0a170c1011210703200712090b0c01020a03050a020307120504021311190e0901180b04020415030c030203090a02011d0301051003030905010c17071511130f 72
    0xc40001d5100002c0c8044560441c3c08001449407040264035181107824103818603818a2203802c05800140070388a10084274244400e07030401f196069444ca07002d071900760f50000c401e01d20307081c4008400d581144880d00842c40010000400d503020620540080c02420660b81e020040c99444269010407400705485010004480000d180068413264100c140c001703000070322103c2e41036502d24100d401c0b0f80e00701c07404e51030f8480c0100302c951621854050101e007c880342c0c00c14080c500520800154010700500407001620407810000344070864a0780000c5480b640540219031311508d40c11414102a1a141e1200c0024101813801038080d110f8001e51740104481801401155040e40c015500c402d0070302c202c80b6601c02d2440030f0b0107141d41c007402060300600c101700e51100303002d0840c100244107032099003005040c810140d0075040002d1135414040109044e91220986480091401100102c6030820100c2d0280c103110304d03182000180401803070740709003100f040b2402965032204643d56000d2071290402070f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 967121330 1250 967120080 967120093
    0x403090e1005040e0c06031906050d02090601050318030a0507120f1b0206070213050103170a0e0d0f0c03050303060307050307030507050f0d080a0801030b060d0c1502100e0a170c 78
    0x1401d03e50003041c4194402000d4030190341c1008040f54085d04200c842c4603496018154101c0f41c2002442a00c010b003800741c40d4204050a55008901c600901810890400c1000400681e40010b00c0050000c040429015207658604914004000307401a03c42616400c591b407201100b09802442c0e0480440815141e000b0242c981c0d251000350007207004801ea03000042008018010707580c0d603102907207101500c40001419411400c20003404072810300600c1004108000040441e50441c420039a051030403152811808014a003e16403107503829002484186200380c003108104000c0301451003600c041e002c45116075900c9042503510003c03844080c2964001c82c9041c015421b00e011404035101014290100c00741a82c0e4450003d0340c4080c1030030b800561880c005108104001c0c06581e0801030444c0e03184000c06a88e10b40782404015441a824103035550b2350004030503070003400310040500020702c2c200214a90b240000d910b500c40c5080450781d036041008500d00030801c04081e03031844440180140034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 967122580 1250 967121330 967121339
    0xd18030807031109030f1005010b2502011b151a09010b030c041206020901170c1228050402090702030f030c0f0405090c12060a081b040b0d0b0403090e10 67
    0x1001c80003a41c4064010030004135881d40c508000f00b03001e00720b4050041c442514005070690446806070000700700200104100680b40b14420454044c003e2030400c82c510f415018401a500d0790803104207404603000c20442c1005200600041040006048101340071b140b4100000da585030680c8001039602004150050009602c0321010b1644134604d860a03034a0320b030b11201910078048141100b00d0f0802e03000a400c100a50307120207404130b02d00b810600c040d0141000c1040e501c0601440080341c0b0b0041e00b420002d2040201c00000e1040d4074900c501c9000e0342071030402002e003d000208d070142d000e04a460080341c0514400011580c5c024403000c810307421600d03169501e42003581b1456180c100740790113000110b46540d0724602c0f02d001d0802c2c50070083daa84205031450200640040ca1a031040a0700c0f101040305402c00314030182d9155040d0704180ca18904100050000c0824802d40e940001810415008020005401da03000740c2c02600da02c4003140e6a8070030740c450641c0c126842110401c03d00c0b001c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 967123830 1250 967122580 967122587
    0x1020106061b020f0d3519020a212712050c041a03010e070501090b0a0306080d030605031606021525020706091223120d020d18030807 59
    0x380124801094100c0a5000100154410741c8500c42030720300500c4e400000d510300c54440b40e54105180540c0100801180c02c110441190140c0e020402650864507e00d4510904c284101208194080f803140050030171344144000c801500c103259000700d400d010a03402071900c4000740341071102c0b20b41d000c0d028180c2400c01c424580b1b5801c900460b041e200d040a140401e0307545016203882d0300c80404620045886e454105401d48480c003026503842e41243c001800541d900040090070360301d501180b2035455144241c01c800410060b40302c0032950041042d0102416032603040402200c80481c21140e00065424500c40d0551440c42414007590104e0203007071808801c0c00d01254000c068001006c028107124a031280104040c80013500141c10000e014882260000b51140140c80d071302d210704000c42200d5550408502c04010340184040c07070740c1014061302c13900304440100150280380040c1c07292405c80035200a5000140100042401d02103c41d001d20f41060226907a681c140e5103030901500d4410040d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 967125080 1250 967123830 967123877
    0x27150c0903080717210f15130b030a080f220b070f0303090501021317030a050f030c040315090b0a11030a0e0c04060f09150506041509030b010909020f0102010606 71
    0x64807000c2c0705101301d50603c40e080b450548100c04810b8500c8003841c1803a41980684d20050401c20304a05824813007c6d0354a401210200c0c81c8a411000200b0000c0c200010b0701d032214140c002407500d0000515519039000134009000b803160680f402d400c5840380b903813101c0c4120049008090780c8075824000840480d4284c0381100c140341c001e080009002d1140e80703c550036603122151015a042940d0380400422140080541082c81c20001941c00c2004081004000b442100305412070102d002c4085000141441d04840085d540066214884040022440702410681c5400d41d0b9184412001501c40d40d086d0088c1031021030361003001440d43e5943e0700494000c1030025451842031052455001c0c82d42c40d076100d408050000d208183c05604e01c0c2207001c1c0159440c000c810141130280e66820006910f8071000e550507510051502e041401440d031085945411560010f00f607003403c0000052000072a0b400025024000e071141e00140c0880001a401d9500d01d109440002c0c030b80c4c00c080602d180303800594 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 967126330 1250 967125080 967125113
    0xa021c050a140a1704050312090f030a180807060807030c050403030503040201080a09021908060a0605030606010c050312100303020f12032a030901230c0d27150c09030807 75
    0x5500032000f040134145003e90480c2c0c2214654030005050351604a102d10383d503401702500c0c004001d01084000c45540303a003c0e070090740c418818240b10025900c0481d0342c002010309802003c844d142d41e80c4080040c0602d0059038084040b03494005294082071041c0211000d8a030941c0b1404d107107450301c0c0d00448010780c000340f01281c2d03d82d0f501800401039640144103291560002c04003c01242054400d5040c00d102501c0850702e9031504004010b10f88001c10901e40c001000d0034a41d01411403801e040e070952240c070f01c455127120154010000c0f6165103842c0c500035680280d003111029070b01188029507a4800a460f4041d00d1000d000040c00c41c11403041c18403481031262100308000511032038141e2613070401c0e146140242d4503080c1409503800c042c940081c1d14840040e042920341480200219113201e0130510401003610f607404560b100840c21144904604502e02c0ca900c44c1c0700c5402c082006042e68400940c50768201080c1080f518400c181602c240e80c1c10540702d40c58000d8a030741f2445c00c108044103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 967127580 1250 967126330 967126337
    0x1b0e030d0e014a0306160c1401320c03090102090a0b0307170705041e0e070206071e08012c070302040f0b0c0c010c03090b0a021c050a140a 61
    0x1400c02148001d245200c0c10508048280005904100c2c01003c3c84412140020b018001c0c0c6550b000c89035a001071416009003000100c841200318944044607544d00311080a004000c030341e4002503402105501200790100e907915035410825110500d4401024a83d41c161030f0101d01030b0216a4104505000355040680080018500708108001c41d14000481d401000315042c08002c02200745d03085070300d00309c3d010070880f10782c110f1303207011500509540101d000701c00c15550b01213900c0f00c820300a0790131100540011340c807075641c0d071a00060007943d411049070b420b0300040b07440c038000b05901c2001d00311040101c102d464620481e800c001c01801c141c025210011000200505441501c0641151540c0074980c01c0d0341c0981d559080904544402d14158400914484100141e0003980008502d02480e1442403034a9801130302c05e410101d4050030581c102000c81c11700054024032007900043c94013100801c00030490741992004406444500941c801003010500841c2d40b502c018203540300500b000e071710608 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 967128830 1250 967127580 967127597
    0x5150405071e030e0111071a100512010509120901020705060f0d02033102010503070c0f0533040f140708010612050f011e0b0d06020703031b0e030d0e01 67
    0x1c07492584500070422070203e5910070355007280d40b50038010001580d40f5200c14a1900445503100b0080c655507040d008244604407000c44c07214080c0340324080007000000c08680881c600002c5080c002d100640e0310113103612a02c03c801030007010b01400d90b0008801600900001440d000c1070041640c86000c142c3c0c0541d40c02c010309804041144061405481600c003001c00c060b240b03240001610584140038074040f00000c600300c0040c1c0c0d219040342d82c007081511b400c82c80c640306440d1922070456100c000400d140580d004625010442c40c85501d0b8801c1a0b82802900d0a5400342081814000703807009400d001c81b051301140070468040d011005030259104a07883e035030356071040074215901604804c81e5a510f5071015814800d0400040c403070030752218020846040d4142c41c1450300308001610010050710707400ca08120b9510085440e0460390080c5080d0b5a55006240c000d00605001200040036010030f009101c0140c8101102c0200420180050500580f0020143d400d1103081300300a04012500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 967130080 1250 967128830 967128857
    0x3090a06020f0d021c03090311011b09050f090103061d06010807090608011a120c0d080403020420030601032a0c060e030903030f030601180e0109050a0515040507 71
    0x14080000103110540c080c042e060b01c0300d6915070401c0e845200510440d4020880320402006480c00d0003c544040e0030b0004800b0360614061315101009844c10540d94070b80b140c4543c0144201c91741680034442d07942e035860384030740f5102042030800001040a8000ca001c00051000400b2984203840c8181da60040115204134021018a0200c003604044541d801411040140c00000e0058101402402e40203000b140c041d0100f80e03000702000d16100344580b00d115903001408609000c0000c0c4600007a040f40c01e951460b00b448074141d40584002c0340924500620003400c02803000041030200040305800d40340d5212000118003074810201c0f0444828009983d826000c54a85049086d4036a03503100c40101140a09044040740c5100807642d0382c40c3c004200790b2210760340c04011100c0c44400050403649070b8981c5001280d5000b07005e0000408003d50001c0402c480076840c0341d050403690105420b0100c1d684103840582038400c20b540201c0c45100748580394070b01d840c141c0c01c6035610030b425190000340607609 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 967131330 1250 967130080 967130089
    0x2060a09080f270a03050c092d01080f0f07090b0a05060304030e181504020c3408010213050621071701080303040c1a0904020423041a060c0309 63
    0x551004840810880301c0f00d4030030700400c0400d01c0c0b1940100c58490700140786032991910f80d541140300501c83c40c10080041d00401c8401c00b48014586100100480003810002102d003006e000c3c001c0e80518130034840e01981105001452110035440c00c8050000750745040d40103070140c8903c1c00a10750200130000081843d882e808041c40c4241d009940c1c05240c0610301082c8090f60304c10000071001c1e44549801c01c02c400540401c03e523a4080150340043c5d403070303190006083c1408058100322000c03c4500d021840550814021202c1611282090b0420940d031520701034201c2c400d000388040d010140d581c040081d441d007040500152807910307100c0c5038402402d440404120f4421a010000300c1c1d04461280b001854500259025055403801140395062a4440f8024840c86105081040280070a0303041c4010031001a10300c1900050f00c02d548030750f1505a08c4010302c94403144810080020300d58a0840c1c5401d0003403100e60b1101d544051010407a500c21310001d40d0100b80306034501d00c070402c549115500c8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 967132580 1250 967131330 967131337
    0x1e0906050c07051c02041b0e10020c0a1205060f01051f1b03030204141c0809011e020109030e09060d02011b15060311101704030c06140601030c090602060a09080f 71
    0xc4c1c01d040a00c203070051040100b12040402c510580d030300c040380d0003103201307811003d06512910200c0b680d0400e0354201d44224913000603900026007000d4550000a500002c03400c2c4500854401c800303031212941c49240c0741c84441000d02c100e680c0b21291a4015507205c070f507041c048091865030b16151111000500c00380c42668941541100000e80c000307410004400001404060f8103011243c00c00c00c6c4d01800b007a00b40411003104080c00c9079400003502c1d012680541c1c0ca0400200010641c140c0c44114404060300906404109402103000f160700b41500e440e0188409100d000014080050411981c0045a1458038801056594040030030090089603042d041c500c0225101700010034114107500c1c100e58200403c0000c00d0050106410510f105508902e05c0004d406003c510302100780d80b01e0400b00e98410080401414152901e0300014414000c1160301c0d00c9002c003a00c0078041815211411600c0250520840d00107801c9031002c1800c0041c0d54103e543c00c240941c3c1c2c02410040c461700308280c15032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 967133830 1250 967132580 967132609
    0xe010504050d23030c2106030c0303040b040e1015020a05150106020d0c060b12010b1309020105030c0c1c02010509010605090c0421060e15060904110d060f0c09061e0906050c0705 78
    0x600380c01081f0b49850204960840550140c3c05507003001e20b80900c0403610300503801481d514050100005110010300528000144000d81c804086c80c0402d08010303480c0d0071001020b0754a8015001c0f00f44042d4803a21311603040320b803d03500400c00c004600c9400c444800301600215000b68480c900c4d0712003aa6004841079918080000008400d802d54042200c505a601ca9014005060020043c0540e0308001039a80c407101b04a4602d0342c4102a104d000e0414107a90309071841100f2031081c0040c403c0e41541704902c40d6001000820429444004000c0141412a07200900c40c40400c000c2c002211070010b122001c1c46550104211074042d42d940350140c440d811020341d07490384548603040440c110300c041303103800c08070595100145003016110028240001c4100600640e450310440c3d0030440b0951043d04030a40d4100c04200489407140000c0c03240d50310784a40000109406820040607030080610201c15155403290744040c3d1404070255015000290b424200d40101c0900084e1500d0740070500d441e41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 967135080 1250 967133830 967133887
    0x50c15010b040603200a110c090112020f040b090c0a110d0f3011071a06131401140a0b07080a08130b27010e010504050d23030c 56
    0xb5410488010110b070302051101c40648014075600381e00500b6502198101c2ca65841c2424101003500a03562804203288a800d4102c0921000007c083c041c20010070802c074400c441000c02c660b1003904100036660301e112000c1d80b26083c200415042c0104400902c88001e56040c55144001340381c2609050018940114020070b4602404144840e804041002c10341c894042202c0000202540c40343c240100310842c03100d5941c2ca00920112000300380984500300e5101115441c0700f400700441c060042410740b52140507601107110703000310301c0c03d50141010380f1403451030041c4148c2c48e109183c583d00100e60302c880d400c0841c00c1c0700410910b2000c0e0041a07000e008541045d52030400e100d000780850401003030007000c54002143e02000400c21001d45801402560300d2251904035070b54100c000307100c0484001c1496180580044540006401481c0310318060304c16100c039240904400e80711240189640b4205106880d42e41c0743e075000400c0510b0300815008442410900c2c0d5005400000196013a0010b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 967136330 1250 967135080 967135087
    0xb090c01030c08010b0d0507050c0d02010c0906050a080a020310150e3f010b030109050708010b010e0a0902071e0b09160b0d020f070503040e071b0b07050c15010b 71
    0x1550700360141c020704682524110a413503140095500f428011708441200050b19000030502103441841950606210b071410380e10f00403110310b00640246031141116000c9443c0440024030749008405895a258080d212085180d8406092400035800145000800750b54050041456400d201f10b2003800101a2503001008800404029409241d03151071280d03c05e010550345084482000c26064800c0003c1e5220f4100500040d00d0780548400d40e00e0903095841d004240e0107101d0700169070750071070300d059008003d05203900c00111a03840001240c65000a03e10381c0401034008158014000140242d2520302d909080c0108255103800c0c0c08000c3e290341c0f80ca4014000703809424005041c03285130958803c1c2d081490540501709502802d01c19050250f40071500921103040802200c0449600801741c2c0d682d2070325803076000007282064070503c00051400d60302600044440905d00e400b507030064200000781c0e41d00081140c2ea94808040381d0307414061005034003102809100407901900b2812200d684 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 967137580 1250 967136330 967136353
    0x203040f03142112010b09130f0b100309150209030705060a030b0d08090f01110d0f140d1b0c030c1515080f0d081e06010908030d02270307050108130b09 67
    0x400031040c0c00002c1c20200801c0b03020000d07030f126580c8d000124881e000100b0401000310b00000105020313804681c002409031090103020f645580701c200b0fa80e104964400d03907410026003c00480c041c241a05416a1151500340003034a46803028240c00b01d0940b601285071021000482c1000742c968408440001d00420841c0b40d900c0e0038000c2540301a42882d2100b480e0340e030302440540c0c4e0450b2030101c0050100042c84041d0b4584590238100fa005517200319242d485040d402c400b0b001780700d06505406081d003003040c1c1005e4188103076403500885070195100e14002030f458645d00204035980000c10f000301d980c0ca01900040380c84a103124005c015074009007919030240351070141030444400500b800c2001400402c40d03200862020f5480f00c0925859102c0150388407001071b180d080140e00b001c0010b210106500541c50004c0d00105030006071015030703103c00d281c41c428984091900c40a40c0380e040e00481001e10007544540c900030752003070001420b2600e81d0010b803540c401c0c0c20b6040e18080c1582e04101c10307948 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 967138830 1250 967137580 967137607
    0x1a0d0603060c08090312040602090f040e07090b120723120604031b0506010905070c0506250c0b16051314180709060311120702030c06070203040f031421 67
    0x2680607113002c1c0a07610b0312250441d4003031414402000104810350219080004d51600500121030307242c040c1003088181c000d85400e031341d41c01e028132494104504001d03a010139410401c800c1a150107209004107901c07403c1600261404400f1000101020242031514a040d516403258001e14261000500403e0a103400c004101548481d04168030301ba07c801d040001620000e021070464a2204000030b041d2103c000c2196500c502c251301030034910456003444640c1c80c000c1d004c80f0907446981c844041d8008002405d0320400005240900b02d1445080020f281c2e008603013840d800007406242684c13805003455451510082c0581001100c2c000200418809040c4040c1071480001c40c1c020741a403c1c6007000c401080f07000b0303034041c80d4201911100c2c40d2042119150a84001001c400304d200e80e28035002c44001d60f02e41006e088081184210390118154500101c2120165400380b4a030003010390641d120f440c108502c500d6400c241e44548a40c1d0000e45501a1114940b0203078030804590300d14041c600e01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 967140080 1250 967138830 967138847
    0x19091a0420100302030a0b090c041502161e03050d020d27050105130317030f06040e0717120a020303100b0a170402040f06060f02010f090209011a0d0603060c 69
    0x50340500307040010a1990b101003070380765001000c0c50056901c0d6240e100f00c401401400c08040c2e0050a14001d0104049005000d003050f01c1640a400c01e103802e04001c200c0e03035010564802c08800400703400a004900c0070f41d080400c03074040581100a056640e68689161020700c030308a10068020304546e00c2140d60007140031048400c2041000098a1604543c00b0304621074491700b4180310002922005031580550258021504140d49002c84000032044444036801140c602c4041d2801c080042c900389800e1044030203801104004202103410304040390814109462400300318850304c0c0900d480c5009803401403c04064030350155440303040032149188040c505400c01c00d00044244103c1022a9204041e5121615282c1d4001800d4441c1d0011170300524061142e54055824481c002c9140354008040600300d4005900810030340001a03d0cc20031500d092000951007a00007004200c02c000c0b51807801000003000111030303d001c085503000310445480f075000300c41041d00d4012040e4040e4112452 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 967141330 1250 967140080 967140113
    0x10207150b01032f0c0a0c080303041101031404230102271509010c0c0e1608060418080a0302040807141e010c1b0506040906080c010509060319091a04 66
    0x303035025102041c50160401d1030207882100640003054a0103403507000c00046400c19003000303c0120f52608e81c0c1d0b8842e181e42c03007210705803101b44048200e403c0c194442d228190039840d07201a801d00c19107895403a443d0701030001c160ba06400c0c80e450702c1060011003c2c402800507441032486501424403002c410f4580c00e005146030f42c440c42c540a04440c600d07040104031340010509103040c5e5060101480e20360b5500005400c01caa420954604000300481030b000082081003d60b10b07001000d607542c0f0200710a0781c215a841410b400c0d9945a054005400d40000d406c850f5601d0401500b0140c41d2000246040c1c1150301c0700710032409690840b041070800a0007400740714002d0f0303c0e0203c40194103002070b1541e01d820f100102031174414100c41034018120501000903000080c10b46a5030f03035881c51448068511030061520318090b0155164440d0b0040c0f040300d00300400584201c2c190768840300708060070140d40920030b103401e03141c1d0380c141d000584140940c03025051560840250342400d09110f80403802c42c480 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 967142580 1250 967141330 967141361
    0x905010b0916030c1806110f031918031703070f05041518030b0c0705010f090c0b0d0e0102030c0c06070c030806120c030a08191b14010207150b0103 65
    0x40c0000b54a8a0b000d01d048140541808600042c680c1000c03101e543c1d40c0c0940485549503c1e00116149520a094022034401181207a411481e0814010345a20940442c3d41c04010120003280d800c60080400c16041d003c49000d00034101d941341c4904c1401c1c0c0c0038aa40391503c0400008102c5141e1b04920905c140c0302280c0740c0503040c01d00708406880320004141c406010b000007076034010a80c0c2c01301307443c490245d544900103510a0500008241d9542c0041c4c40c11a0300d03500780072aa044044103845425111500035251240c224645051600c02d680506d81c003c0303495456414004030b220003400294040c6900c00141e075902c00e08010030398200203014200d58101f1161204620100364070440464101c0c030201c5c1c4024240180358080e41c5010180060183c00d40a00b010007000e009413000074103410b500403101701400d011602000c44800e0960300c0c28819010303203080c0c55000f02e011a141165840e0310f42000610340545525a054240c240c9003100c3c400513100c1d035640c451564507010300c0744850890716 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 967143830 1250 967142580 967142599
    0x30309140634060b2404060507050709050403120501050301020306131a0d05100e06070f0e0406030206030f06040b15122706010f1521110d0905010b 65
    0x609039202c1c10700c41c8011101c0010381c14000c0c82940d4030740c03089800400300e801509841803034070901412040c03c0880c0b00300d000000318020702d0043c0d1604090b03e83c0d40d080661400e800c0850660782a00003070410361b8107108040c80840e0414140c45884c0c001c03030081d1144820f01890074540030580d0f40503080540264014001e000c2a51210995200080510a004202d10246178203244c3c02c0850702000359480602c10282000740b141c00b141071706004100040074480c64007203d07007180d505c40d01039840c03200146c010455074100d02e03c00e5601c6c41da08040280041069030f071700c2e000a08076400a80780321601150242c24404540f51511402d0030a00c01650000580715a0028166071402002507603000342d4480c2000541009415000c1c0950b4881881409070480013820f0b5659600c809005009408801482c080b03141d004500c04403d0a03021075441d4120030030540c803c81181ca80e6520420303105501e910041e6401942c0e44050102101d8801c0001015102e0b800c10030b00303507458800c0c01c1c2d00035220380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 967145080 1250 967143830 967143869
    0x203100f27020f0135070f0804080304030c0c060806030c0901061d130203040f150b0a090e1501060c0204050c07080910050706140403030e0f030d0e03070507090501030309 75
    0xc0301528030725038049802e0700e1800803030390050f248545030380044040246040015035001054240100014104680b0103a681e600e040c0b0030b03550b450303030081008017096110000070f00054102c0c1c01180c1c0241709281c10944081a56160803294466420240214a18400304591410304105400b40c10b102220405000d5241c00009090f0240e0010f50f04484035154900c0119500d07088029201224009411582d034645800c01c401c6044581c0411503002d0b00000e04e03a8800301c0603000d000c11396000141442c840e40e14050714180101103014540e82c8a010303000040c1182c00b0584405402010705032251042142540304020858400405c41a0a044184061404079070128142c864402c4243c074100d81049100f4410307070b1030b03004400000b17040c54203200601c40c003074050b03030801400f40b0311075103003442540241c803411a100c3e040d0b000c0303000180e40103105030b85cbc2d001407070703002001c214545800ba80d00d0103501c2d0302d6244c1413842c0c6030002250a40c17910010810594854890002072070b01a032402c5075100c55 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 967146330 1250 967145080 967145141
    0x8060907210b031207080306091006050a0e010e030109120f08010f03030c03020f010501030f0218090d030f0902120304060e10020a2d06050103030e0102011413050a0203100f 76
    0x5100340350456960315861055071020040500300880b1388013000c3d195586441c0c0440564401c440035030040d11980c0216000303110381540007003660015201c0c60701f0400881c1007210614440002d990401c01001400740d40d5440c203120328041030b40100c04035100c0300304058014108407242c00d061820042c5400042003210060900501907036858540114903c1c0182000c038a0003030b1005101c80254a4400000104000c01d150090b02d60b20070344607594481c8041c50802c00f030500445412000e03401c442041d00e8510321940c445581200c40d4080096410015008514607a80c1200c2c007d14592000406104242e00030502c4050317070f141201d8104503030031041b41c000d40701d11520000800008988080c0071061782100d8040001c5080c60032001c0c10000320b41008000703401e0a1006501040240141011552044c001c15000d102c40990702030031a00c1c0c81c44021034102800d002924617000e08005600142c5d030900030b03000a0307821180c0104000528500764001c48104400d450065600c50b1802d4045040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 967147580 1250 967146330 967146377
    0x5010323011202010203070c0608150f010c020d051c111b0a030305030c040b18100201180807020604051c17120a02090a080d0c030201050c0c12250308060907 69
    0x3054a02c11500180c41e20041c1c0ca10b0243d03c200a04c0071880c08030224030103500c0380d80617100d080412559aa120100c00912941042907081c25002405200c007890140c106040501c40042c40345049804200c005680384400b96890065500011600403095400e480c041100300444880c00c61203592038404c9a0004004c0c82d40c52200406001010000030704200e08401a90300401c0e1480120783c0c2c5007541c0c94240400c0ca144641c0c0c0c5c0c07080c215880603061084c0305100f41424400c0d100c14041e40c5940b00d803101c0304c1c0c64002250483c1e201008020100300d545601c446d400c580480c42c00c2400300d0724518a003517144841c00303141640f103004050000c03601c0700c008035080d950442c2001900580c0c4842c040c010802c9801c061700548803a1050304032240c805a4805180091540070358003c000741c0e02e5900145505228810310f800e507550000d581c074840c12294200034044d10501010443c2c0041280300c1035612079584681c03d501082002c0204501c1d41404031081d6809800c80c40c0107015034040d010084403141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 967148830 1250 967147580 967147589
    0x6030d02030304030c0602090a0b042d0605091c06061503050c1207020109053418020306130e0d1b020a060807020a020402070b060a3f06050a05010501032301 69
    0x3c44840c045c0c14010241e049a046200140070014901e44a1200d40c8460303105118000e00c801c88c4100c0740030346905507004001c2e44506107886080e140c1c6007260480340303500202511980320880d07050320400c0241c00b41300000d6541c0300794800b054142c0b4090200c1182c0d03101c40d10940074142044100071102d011030084034011640c00140c2d10840c0c5469108034014800d48074010102d101d19160003403039845034121404016026a940344005011080101300c808881c40383c128407029404140b50b100811fa000b0750341c80300c800f030030003507103203804030529026903980503d400f0b20390700908008400e19910103083d00180494040840e502e044a42c04108900d050740f050300100711210000c203c61920034001c410301c50790014001d544076451400c160007070220075114070b03104900d4a0000280e01301d401d403500c001001140c0d012283c00d2440419a8101984140e0070000f91800211410001d64184129400b500002d40c002806605110001d0102c400c030076000c545104240683d09407000c9080509030648 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 967150080 1250 967148830 967148837
    0x190f090c0f140a0c060212090604020a1d010b07030e060d090201021005040f0b09010f0c02010b0a080706080403270b0307030c05030c0403031b210806012309191d06030d0203030403 79
    0x814017801d000000b4028409040160142d10091001c0703500f00061950080e4000c42c0e0703103110719076a07400e680c14405e058207a007124035401200410840302080d010740310382c60080c105109040781541c00a131030344e0310025241c000136070369503501419960304001c0950724151041c0c00304a14100303610340449250195100400d00c01c40c010015208000a400c072810720340c01c6080034001c4410402011340689072114040340203030222000015404800a503400454040d41c0764126141c449480c2229510034070302c4040c0c100c02d64039001c8501d840b104e94550006002803007000d900ca0422000040a85004c41c1c0101c0170000180b091021849030030003103070121382e8981131503100d030140020041c0fa4107442c6003000e84896944000417601507480000701085296541c0e4a8101b41e50f010015a01001c50180c1141c3c801c840740400c60344491880000c200c110303c01008a203903004040403034103850700180c00c440060f030010525824041c0d100012550003400483c0a80350524100700001c0d500d010003807016040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 967151330 1250 967150080 967150097
    0x30b0a020a12150b2d191b05030a050307030c08040309062114040507090e1b010210051014120a120512040b0601140c0a02190f090c0f140a 61
    0x507219400705010040141204460311010440005c1c08841450240030140911076401c04103416040c000704d400b6400e00e20804c2d05c0b0040d6540007240c03e220035004000a0300e040081420220b40100050403100c1e1048d40d07484c0e0b503803401c80e20040c1502c00243d50f5605004945042c0300010350041994400c2d200c55203040c807101800b684041400c1030000b061408071600e00300e814100e0580c010703803962190307010b03504485815950700301010803121b5907202c120a5070000e142102240d00c05140224007144144116020104002e40c44011140c0503100100e16003d644403c00c80c03011115942d08403c10101d40c01d075410300c1300702d0150381c8440c040c100040071f11411002c0c0f00d61107401407040c1d1f00303042c216200555491405280054101d00140c0e122030100700380a80d80c0040034159400c03608901c0c2046c0c040c0c1030880e03032035091000e450720307603502c907111011481400b0a4a0420003100801414100004900c080c06102c001e44070030522400c0c0b01c100a40000720b404504000402c4074005009032800000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 967152580 1250 967151330 967151351
    0x1090b0c130b16050f06010f030602090a0b030a050603010c051204062403080d050c030402060a11010b031506122404231b120c0913051501030b0a020a12 67
    0x4070599150482c5103840000f14101c3c2e5100058440600010301c103208403014844801c0c0390a584050074032503401c0000d000c880a000080044d0040c0040c0300f005410304107869119502c800c110b800c11501b20641c10355075000c210203131a09010b40a042c609a0824038544500398030b000401843c0244041c01e05600c600070400c0480f071b050803100700c80c510620107043c0b0a44034034000946a0004d1403074031125007001c3c0801c90004004080b82d0046500420661800d0760402c2c0546800c103031090740c40841c0d5a2540e030704040f92420712680d41000c43c21804110f01d450320f03138100003825080208a07071503907100792a69094680c0015900d4428180d095080006540e0b600e80310f03000413051480000208065003000504000004004801c4d036114910b40c580780c0064014400898000c808072441c5500c0007040d01194100900c0c0349800c50b45150610b00102070030703200c0500c1c0408002e0010162445000100107000c0d42c0903800f41c01c180d058405510f41030503810010000303070980718082e0181c1c1e518a441d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 967153830 1250 967152580 967152607
    0x10f050a0804050a0b04120f0f170a140117010e030304052e060303030f0509160b0a05040b0c0f0609060f060906132c07080a030c151802010e0301090b0c 67
    0x4451754800f24440552500785001803a0201a1100070046085980044c104e94065004903035078104960f41c80315449041d00800401388000b40038094605c1d91001018018040c00c202140078000c2404404030742c02c4084a96400c41301028070402c0290018410b000006e100400ca0b5030a00b51a144e5401800c40e0708004d1141000442800c5803410380391000010801d609070b045290910014901000159180e10540c0d844204107060f00d0100607a42c00181300030500000502507225191410070308040d1205100281a88160072940582d403040a030040703112410072600c3c5d4800e01780c0010300503038208030780c266512400151015101d0038100380010265180d4040701404081d1902c414011048501d490003079501120b548882000031010700100c034840c000a14004444900000345881d81003910111400799160a00303c07540f030700042c0411500182405600600d82e84144070001700d1036188005401104031043c041d02a074107240c0d20f140400d062007403065000070140344103940c45a0300d14105 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 967155080 1250 967153830 967153843
    0xd09051f02104506110403200a170303340309050d020d02060604090305190201051906180b0f0312120a1401170307120305060f010f050a080405 63
    0x1c40c405860030310829188640c0101400d911440c85994404807020f540094144400a0030820324004040400c3c40000c1c1066001605288907032810908150710b030b0340c03901800f081005102c0b52100541c0342070511403a107540b2580060288114130018048009000d503180c4c00014030b0113a0b10100c4070b42607865503035001c914142c5020200030f20190414909806801051402c2c400e0f1080d115281c90007070342a0000800080950481c0c000f046156169010000988148070045081140c14414000382d14500c240e01180d582a035000401c0720f20308078141d101200308103545003041a050900401039400e07103031002050721b0781c088000300e00c800b1108041aa2600400d03d076941511401110032444000c510146c000041c1900f107048142c3c03100410502510309400d655107483d0700d400010003d11402001d6080455004030959040a805854000f6080d40d1038100b00003190721101004480d1414440d20f0491810908118541c010264002005401791040d644140140b50001c24140001001003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 967156330 1250 967155080 967155103
    0x2100e04090f12021b0303040e10030501050106050a021902010f050a0e120309031b01080105010807090b0a050c012421060204080307020306070c02030a02042c0c01020d09051f02 78
    0x403030302e050b00c4510308040e0240350007800500500896490265010f1020801544007000500540c282820714045540343c1c00064000d008a2007940d00010000b1028080e8a008186548130b02c0c1d01d03225250030203428200d000700340d021201ca14148000c01070703800410216624142e441c12544511403a42c080e1040c550302808158000c2245509820300703040000208446074003075081d40c101407110942c00d0790a5052252050200720034000601c842e511403aa0564042101d140c0181c02a40c0c5141007901c903404401d5210016100140c00c8251034002d014486901c5c04c0c0408201da105000107100d002801d06005020b440b42d1904007020301e603801040d2804c000b0350810001c65580c0d0b903442e00c540d03030780e4400c1d64103d00078040c15001404181c018406420b0300c2d07030041e01401c061704485e42000002c0c0300707940b180d06030001e4038400781034070b86424195044500013000c001c00401c003041002910700041c1006040800166020510040d201e04030100c081c1403d03208044907401e1480d10603814140c3d00d104 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 967157580 1250 967156330 967156343
    0xa02061506092e05071a04081207091409070915030b18100f0806010308030a0912020d030614010c0f050a0827090c070201110f150405060a05010302100e0409 69
    0x407040201640c40541203407216880c3d42203007080380e54070001d0700c0300e0181010107000407018509008004010340c2c800e42d8050303c035500307c510341500c02c1494910701c1400d444030800240b510006000e511588a42c007079094400300d410803031500d030640c00149010498052207600d4145070000c110303e68000c1d0401c1460031001002d01c1c91641840020031404842141c0a849100d112900000c4803044000c80005442c4901d025108a83c00c2d80c030307540c1803030744054103032030340e0321b03a903690110110b040b01d884401d0401040d400341001c2d140c5244000c055503480d4002d005001840751351030741c06a030408445c0e10f089a1004440141c0d4100c0c2c1812800c10304510b001900d40f0400054202e50104031020f00f41094079074213400d00c0001403841c1407001d00d9400b141c0c1ca04079440d0410045015600030002d40108401071811940b651209091150811203000001c07801003103060240300420200b48643c07544134066071070400040d803450300091079104e01e00740b1100c00c1c05001c041000441c3c8542e002415110740005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 967158830 1250 967157580 967157599
    0x1140d05220510091b06050703030c0302030603210409021204030f020303070c0807060b0604120302100905031905040909080d0b1801090f0603120203040e0c0a0206150609 75
    0x84444014080c00c41e00880040c0145103880000c040d28503002100c90b80101c0140f45103100003203c3d10040154050a0750002581720b0f40c100032006442407940584070340e6071040d446143d14503024055034005045030301030500600400c0401e4800042480700822002072561aa41994131644640d00c25038002000d21400007841c0c2c85c04c02600c4007018050761195440c050181342c9460102d0b02c1c1c0c00241c801d00001404103040d9008980f1100282c40184c1c0100c03400100c00010b04000303042e96029601c590700115001410f001450f406000070030710071444440c10300c00c01150740e480a0f03c034828040300307144e48480e071500080341d50300c140c00350340280810b0801089442800c2c140030101e5004546201115428046c2ca1285400c0c41400409207038075000c0380c4411a420213070340402070160001410403091703840c0800008900c03c040c0c1c4140410729600510340e140d050885130290714100810343c42c80a01c04206002c0c10b5a0f0025403558048525060340e0305d011100000521940300e0294030703a6002c02c2d4607 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 967160080 1250 967158830 967158847
    0xf030d030501150c05060a0203060402160b190b060702060a11010e06011815060e010c06051014120a0807140d0315061d240706021215030a110114 64
    0x5510503410b8601165407200f00101c019401c07140070000601c028030a1300b0890200d00c60700d8003a000b46400010050003d42440e08a900c602100040341c4400e446d03240491060210140303080603000f1b401200c1030020701c829109480801c20341e10401d070000b4001e140c00210411114854401c00c400000c0c240300038402221004501962900300b07008241e0700d24560003003001030f00c001e403082a4141c0000b41d4900100d82c0b9003941900c40341210180d42c0d06112000702e9500002e42584601403046440900b0b0020407030904401100c80310300c018a10340120407211420640c00400500c828015a000c004283d60b81e40d185040c0010210620300c0550300e2007201002c02580380c040d00583c80034100e4114507034034269606c00459548002d081c00b00b0320f50f1b18060000c08141040c02c003e070040c0c580109591850100349012841680c00502c095030010350101d0f090707118201c4000442d80145158568420400c0060006900c880c0c40c28002001301540382d200e01c03803507400707000c0c50111255483c004a0726001e80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 967161330 1250 967160080 967160087
    0x140d091b0906030804034214071709030415081009020c03041e030206030106210b010c0b0a2414032a01030902041d0708031603140c1f050f0f13020f030d 67
    0x103500120351036003018800c0d40c400c12396250b10742c4240c0241e96840c40041c104000c10038442000b81400c0c015000400000c290004c001e00b044000d14000d0f51040e465140c030191500f4000c40360f800003101e150041020040703842c400402c4e0740c2541c60b6610500b5201c140140c1542044805900080d042200400000341180d041394681170000044101000e04140c034480d0030080b910f4401000303000c14500442040401c640d00009940501d1680000900300c0d8442d005522101c690f4150f4081d071151104203000c0c2c000100f01d18824504c0c01d800501c1d580c010700280e442141042c426503c40840c0c00d804c0b0500c03680c400d4110b640380030f070017401c1045441581c00d2040d124918a2000c071003648200e03540080d50520000480c0e600001a007030411000c40960703811505909032400e40011a0b5062000054024007400b807100c1154030341071140f001c0c0c03640f00303810400e80348010403031011070001100300084c00da584156180e00100400300d441e020b10700e510002e0700411418000e00c1c0c0511551074070072901500f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 967162580 1250 967161330 967161443
    0x7020c010f35090a021c080702030a0503090a060e03060a0c170f011e150810030b16081609050111011508010c080610020d140d091b090603080403 64
    0x541c003140740c1c2da5525610718641da10300300c00d0000c5d0880c08902042d10f4580c0404001e078803a91103281c01c1850101590000ba107040000082034846420001d200c1c43e4904c1c040c00c0c0b00000300090304103440f40d170705030b100025100c40c0c00401d01c0820984441d02002414851006001d0964021151419a050a0300e000032011000d004040e201e6844420003640711031f5600318081150940c036103103400c814001000b01c42144005c0d00025a10590310300203c0041d030040400c9200d4001440b000300d503c7c51180c0000d0410034058403041001844c03180714003945a0107061001071341c0083c2881100c48000c100450300400c07407045458019001480702040100f0190001c07400b2061039610500142c681c80700300200081d0a08035440176038000461500001e009210303449044d18200441418040400780240640d09040e10454000070380c0c03980c0134840c4859619040c06005011000c00c2124203560300d03107189104901000e80041c401d01c500c040e9070407240b0b00c00c1c22049100300240caa25903000039020400078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 967163830 1250 967162580 967162667
    0x105010e0a0b07080c0c1302090f1e0405191d060934030807050105060901060801060906080907050402070b090c0f060a0503150a0f170607020c010f 65
    0x345141a140c4040c03614200410684028884503441c0801555440a4039406405428224000c80f03244005d13544e544400803112428044016a50b56811010805281920301209100b04500400c0c01040549040071a0720b5031300643d0002031984400440d2a110311829aa02c0c50440c245010105c1c070300c00d071524030240c2c0c0380e2140807a151511044003d50311903180e8094100110078405800740c000098031900c4071501d440c40e82c801c040755240d442c0c0032040d03840000f09860503034540040c0411030400c802d0715070060903149483d548950400030010a4980b00344960810882c01c03601003030710440140406401002c1c0200119626000c034500314030a80c004a61f0380340c0d00d01512542920ba400c201c0320401018070020b14482c5000c016107402d440b1508040c0c1441803122882c0c082d034040e070700c5001096002c0c1511000500d80301c1d00e0000c0c26466518444103007142d03500802c040c480500e4001501d03900307281d000d003082a48035492100480710106000344000d8020110030000443c401c11008040c1281c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 967165080 1250 967163830 967163837
    0x1060e070e011409280b03070e090601090602100903021216030219080913150b04150203190f050c011406041b0c02040506010c060504140c0901063212010501 69
    0x41c643c1d401414a07a008650b5420780010a05007082e0f440034401603100c4140c000200032100c00d81d141d58841d07416410444201c03000c50181d1901c2666071402d0340314641e02850900c0e20010840c24030321b00035280c800704424107403c0c07615110107078101740c0280000c011981d141b1040d0b42c0c880441900c1c01556540e5060290007501401004044894030300145482903500842c0c00c5182103900d8040c0844030304107042c0308400030743d2007410007443c0840464403401000782e8000261102c7c1000141481c00003203042207010355001b0041030103500d65400b02c07026030300362506005182d0180c1a40541d124424010041d000d1751078403c81c8060490801e00e2103000740c0701a0340800c0300790500313072101481800c104d1034140840c0342101d0000051034641c00c595403018040c9800e800c038016070741d0303801c0a07140c0c241c40803910807411800081c56201c00300054541080b040300c3e0303000306503d859805131050b2070395603c1c440c0421030001b600c1d074802078200041040e04e0011060703654510f0803010300d00c03c020081c00b8a5001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 967166330 1250 967165080 967165097
    0x30601031b091806090914061003110d0201030b0d0302030711090c190201230906100b031302030111030a0c0e010503090309222301050a0e071101060e070e01 69
    0x10020640c0c0c0040c0c40c14980c03078040c1c00c2414402401600c4030420030100f05a0380f6a40302185070329050003040752840c86140300c000c82c041407403135203410118020465220011040703801c0020a60031084d40c15111010385801088010b9400106c015040040c00540c0082d00f007600380c0205079000000b03208560103081035401c400d02400401c00c0040095904100520041c000140d043c910f104941d140344005000010f01000700c154506034550950254481c00e120040400c20b014500780504bd0344071407141c0401c0e51080c2007650305210b41c00040e250100b942180300c40c40003103440940c050303a001d100e01894291a40742c00440314002d00074143c5018000744084003420100c1d4040c4096030b00884840b405503041112560600c0f1407140d01c0f070000a94110301054400c5a0380003489403400075850440d80400c07011100a454a0440c0e040c2e000f07034081c404d004000c01030b00c4508144c40d5002540d51414460904009000c0703130150003142c10403006181140300b4000341c2a00300c4141c4814000070f8803002c24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 967167580 1250 967166330 967166351
    0x9060c050c06011d0a020a0c0c080a0303150815150a091b1809090206090603010b19020d1e120515010e0901122a0609140d33090803060103 61
    0x800203c40d004c0b16804220008030300c2c0b444e460340103480d4414807441c00c0a000c062603202c1c028040a03581c01404150441e000da0024140c0c0740c01411000c4640010011a240c50403005980e1140740382a1400b1582c10540452007424800803282c8264400078209480c2d1921480c0c000300810b80c110072a0032100d00814021001409900198900307458202041102464120040c02420780c43c5801c9070301440811a240b01582e9001c05117010700f0919600a803940110400d400d88107552002050556110000303001116074880c0c219200080d60591000098614000c15a04e081c0300d0074810907005c2c245001c001068042c108a002e120b0380998442150b0342c07195044c000807900a0007000c1410410210000c0403d08404082e21900050340d0200d0380440140c800040d419000d0b00144000b070195002042864040d40354802d40d05d2045951091000441d5903d0f42010b003c091009422540f555088109600d20079081400000c09502406181120b1522485583c0110341146c0400c0ca040408203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 967168830 1250 967167580 967167599
    0x15060e0d02010c1202070506030406021b0712030e01030209270a060f090b011e020604030e0103050717040303020c031c0608060603070306092f041103270109060c050c0601 75
    0x1040c03034060b1034000e1032091680310083c59001281e91102940b0035000e000800b500c0b42802036221358014400182c0701c80401c1c1d00e00581c00c0d05104601c2c000e500041051083c089118081040c07135505d41071842c11800e0520042c1d010740036001d400d42e440700720300d0f2400980041d030030401d283c154150740f07030400942c2d40e020b0382c0000c88005016052454010000501010b4041e90040740c4040c0c05042140c44404141d54403240ca07920070401500603000071082c4410160412082c01d0018400d0800b484030f46004a40100034452030740030300c0b0203103c0035404201814040d50484030301c03030124001e40380c0e02c0105503d10186212a5003611107268901000041c8800c0007262050007580020003410300c05140d911440b020744030500090740c142225059050080340300c0312108200c041c00c001040c002c0c070344800400044481c61f030001100304a04000304400e0580d12200341e840d006c07005461009041c2d00300704280c0100303950720000304414034240c0d445c0d41d030729000400b41403101210000c65907a43e03215078109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 967170080 1250 967168830 967168849
    0x90e010b040c2106030c0846020a0b0a020318040606090b030a0e0a030908011802100c1704060207030212031206012012030a0f060308070303110d15060e 67
    0xb0b00003e0602070f00d103000314800e00032030074030b00d0314640089403854403611910f6100e00b459120080f25848040721080303201c00c00040d0000032400070100c00e1074942d80f81d11703100b0005648042180315107030a00c100301195521b89440000c0d19000400c29111907255a029660358064503040c123005c0490040c6403c03d00d050b001d42e40039a8217a0762038007900e074941801608190000341003100116124205520618000c201040c070b0103010760380b04803030305107070811450841c0d04900701100c44c0c40c2000c40302c4016803a1092440d10211043c600009a03a644d801c083c0d0340300c0300d142c00741a40602c3c0003400083c600c1d800650710301524000c40f030b14290314580aa0140d80c903c33031090140192035207000011401d40c0a100300c8548100640c035081c04034a40e0f0701010b82825041700180509074804000e203c0d8160680c42401102617500714104440c87c01c41d152900b10b4000d8540060401d034883d8800400d940d1010140d032a042c182d20428031800000c40710901e0302a0080c0204c00c0040c3d0b442d07623405418500070007003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 967171330 1250 967170080 967170101
    0x3010e032d0d0e0115091401030b071103040f0806010501050a090b0a09030501090308011404021e0d02040f03030909050c0901080601030c03180c1d01060f0e0301090c090e010b04 78
    0xc11000c015001d00d88400c81c03141c5074501070384050200703598100c400d01034403841c0c0302c001000084028801d90a20b03582c403ca500801d01540c90041007500c442c0c0024001c0b8196600442900b809507100039007103c43e0381c84e80e21345000d580004100010404012091241500d5000f02610360710f03030f225001104c0b03038090420390174000b80c101c2404004958650340102001c00062410144490b02c0351200b5087d0740c2000c40c21000520050010011811410344040005400b19025803800340c20f285e221b12144500055440da0b00c0001450b520a50030b203604640040805a400f0540d003030ba40d041c06807011a5030322803000c106003031a0003d03d04800d410101c0d203003941c05071110306041d01c3c4c0c04c0045004200b110020818107540b03100c150303071509000d03803426255440303400034520700c0b410304203a048842c11041c0c001c0c01d00902c07040103000c1140c01064950b55030201e03141151403080c541c0c3c00603001d8401e010000d8040c01da1f43c8400320300342005070440d4081024902c02400680952405e000443c2e600065 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 967172580 1250 967171330 967171357
    0x512150420150c07080d0507150b031f1a0913030c06020309100b0319031101060e040605090c01020d0206190605090c1c0911130f11030603010e03 64
    0x1900140c880100d030494860004089402040746002140014858000382080d4820202c2c40d042a80d030704001e02009480c00801070a480c0c0f2041c08003030000d00602c500140b041d15003001030500c441c165845900c180c0001411110360103040c00480048081c2e440e20642030314207000e43c0c40c08180082c0d0540c61000c81c098044a80b590702d8290180e40380c0c0314160110208450042c002011940c1800170b580035a01050103440420b048500220071500381141140c000c2c0c024403102c1081440041c003010110340c150078441301400301e03484000d00401c00d0340c124039400f400540501007404525440240710b40c03142070854440e03024103001aa980d00c0e6040085d80141d11110001d180d0030300080d81e880c40c8800815021561580360400900004012520700035465008a5080c518044900c2c0d100c944a0704030904002c40c10320b0342c0310424108403140685015500c01c102030405a409648248603450410808100111510012000c1a481034507564030a40c00c3c41020040408044201c0d00802d40a12 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 967173830 1250 967172580 967172623
    0xe040206030403120e160f0f0b0a030b0d0605070e0a1d0601260c03047508030903060f04051519050709060f08060a050a0b040512 57
    0xd80c01c50b1856a13110000c03000343d4403500c0e069600241040042c551031925015501703100d04200d05141080210b520460b0760443d4007000300000781c40e007000c40305400782619004c61110350342c20204d009161290b030001c003080d1a0408200d4071039402484c0c3c9540380801c0324800c68040d5a00c0700b1944022401081619070090310000c01c81c00d60207160382500c0440c8101c2424100e5010040340c502c011022140c031050700c04008100010040500ca0f80ea80401440a03040e180c200241d2564400c0f040e030b200e00603982011959600c404070380e209042e040800c0d174188800460302c06048900c400100420b5500844c040c0c503400440c070242d01001303031000701d0390140080c0701640c1c410714881c1c45100e025100f03483c5030081503046000151b22004403445020f254100c065001410302c1060210346006083d4800c00500050034000103034404110b42822450349014031a548a040000b210082b040d80880e80c0100c0310800040c1e11a1510003420031070304100c0e0b084203041c0151a42580310714070803054040545150 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 967175080 1250 967173830 967173833
    0x60507050c010e0112020703080f1608181216020102070e06011d040b030a0318060309080307180503061305160b04030b0907030f0602090306070c03050f25110a0e0402060304 76
    0x4085812410a05260070305c1402c68400c210801c9030720001c802e80008124808126400141009a94104000100800f4040440040108104005031919040e01d40d8541007564180341007003a050068400c2142d66a41c00d180e2805150590150008034054050fa05001542d000104a05440307800180c49080c02034038507180c000d01107003402004039403065032140c0040c2d45e51020031000300814426292540c42001042c110003071125030ba0310910406040c042c044e00064181d6040d80d070010a0b5081030180ca4202c0007201640c00c109400081d0184100c008111005000c014000d072540c0c050400c0d644031040102404076140c5083c002da031640542000100001450f04103941c1d404581c010030b0b00c0c503840d284d5850303040005c00f80b0f030141c40701500803a00c1949482c041c8881034119201e0f06202c0540c2c1801c3d503000c0c0c0503004503800341c03c0e044000b00e00d003d41400900c01c8013420206841c5052503c0301706182c0195010107000200c0c2c02b03130841403004030301840114203403801036800400281c1190780c1c6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 967176330 1250 967175080 967175087
    0x5010b092206090605090a0501030203030d02071a070216080610050d240203151e01110a0503070503120105120709020d090b09101a0109050f01180b04090501060507050c01 75
    0x50100710384024550820103511620503119100107008140004544071385000c04110000b00068018a099880e0000410060368000110f90400754a600096100c0800e41050b1601c28089000400e020100c6c004004400341c0c0401d00450b211100c20703000420301d841d0446aa6550402c58410321500030319903082c0000e2074600869010980715042903100d24210540010705c0500c000916602d0f15004810304c0707030760b040e19645141401d10540c2c659403040074010b84800000c2c0300e01c040c50305200704003082240021040c42000d42031178104044990b10fa40324034050f40d0301c3d44140c070008482e441d10000410300e07150054132200c5541140c0c00030700401e4140f2820b80001c1d84034000b41c82240790780d01c8915001500b40e80040b84aa20f880029260340c0e01d00e40551002d44040c1e0014242c0a40f64009140141c1e80001d85c281c10783c0c4040e24503000d4040360741e006803480301842d1020726642928500010720041000010419030b84402d006000599991600359105c0c0205040284690003419440080d94031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 967177580 1250 967176330 967176349
    0x13020d080c070f080a02030705091302150c0706050904060603060315020a2d080702120412020d080f0304050c09040305070618171806030108070e090115062105010b09 73
    0x1041c810b46004a0356560640d405841d02c2c0e0200c00c2c69000f10880009516052000f1001010103a5090701036141c0704905606041c0748910091048440002891408402a065070001e0381410f007100c0020f42c594002812542044a400c5d2003281030810100b14a4402d00800013200e601194100480411801a4020b50000c2041e0340400402c1c00340003024584000340c141145100c10381c07034103400200c610700414111004164500b554024520111240c0d40750f021202101c52180b581e104110961000074401038054401501c100800709640a160015000441c01070b80300f0300450300d00c14910f90600003d0442102d010f00403070010b011450210b170300c5410001e0102c9032240851003054084e41c2d0103806411400c110500c0310004500199104103100d410840c00201311101070035507240c402d40540d92002030240c07400b0302000001161550109402c6042021200c0b0040c102c0c05456400c003d044100610680070341d0752089214000c86011403144c1810f85400d00400d610301075640090010300f44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 967178830 1250 967177580 967177597
    0x12030c07110405040b090f0c1003020a0302124003050a0e030706021608060c040501050f0d0905060a06050d051506300f16140a0b2113020d08 62
    0x340034075021541c5540301c2c0305191155105901c45036107030174071180191528840180d4003105a020f25114103c80e5a08103005800a00342e107000350341c07020780e86011030207070055840b80400100040300380032104407600d24491403030302108045c1e4145440b1050071480780c0d0b0360b445e881094900020310000402c0c491002060200c0441c20054422400d81010034075068480c5e103c2e00041c0c00c41e1040c907006901c0ca86c48a0001d049034001403046048c9400c10000c03900c580d01ca8a1705000c1d0005031070580d503108609480381562020f00030089a00706040c020348400d8111220301c281480c281001c01c8515104100704500c40d000802009135a07a14000c10311104000b8081d1030340800d103d0000101e107080e030081c1d0316544a117600520524400030026038540043e0324110301c1950020031034462400c440303900c0007044a00c084a01a54418038401041c7c0140213a0000804441d001803140e220001260b42440401152103504946550f01c5400807401999188000c0d0301c00f45045100b000328101c50042c042a2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 967180080 1250 967178830 967178843
    0x40e06071215080a050d02010612082a0f300318010605040c03061509030203060a0513060c0806101b020609040f33060915020a08041409010812030c07 66
    0xa43d00c2d03103c4549414202c8100f22010743c003622051132002c2d82802204c00400c1c4c2c0c0d14191500c1c040340e580710740d010301a070013514055006003621902141b00ca0301481803c40300c0304061351680180007002a8072820544621080640c80d11001c44003501c00006130b11070390034910002403c41e1a2920006109610442000880d40d00d442003c0741c140d460340b04201e200c00d8070303407800149946441411202c901030300110406100c1840c2c1e0030405a1004251964040ea043d04002619906d5410824080c01c0d103010150207140303850311900f1401d41080d46940100c034200d82c08a0281c0c0b9940d0212681440e424510380350403881c0c4c800c2401401c00d28060511888000d001088608403160303000100c810901010071552030112a01410355180a641d55080c40c0f00880c115200d400c120f0301403c407042b01d2040e080300040c4002e4902000e4804e2102e002c11940c0200100d0b5903551303e001104040802031903803445001c08100000d03026100050b642550300400081d94115610f81000a00c1074011100070343d00d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 967181330 1250 967180080 967180121
    0x6070e010e0d110603010b09090a06050906011211030f1f03150e0c090f01031a070f0c080913050106090906033207060804110402070201091e08011a040e060712 70
    0x7555664020798040d090407090980c44141c8c00081107004100503004c107880d145000d40601c0503884c0c08074a10350040003824030340030340c1c08000c144600800286019881c842008001d0001e0000151012400b0302411095a10180c01c68040303000c03002c04520008254000702d144607481a0b070700d600003a0010200a0945041d82c40c404085001c41c0800c41d00d424202803c0300040c0704000c0ca0184c0134030030915204408003c1d240200c17016000200140c0340c0030074001e070301d07100307504000f0b00c0c504039840c112000c0d0a541d0040c0101c1c0940303016010a02505000c00c030741680c085030262440c41032a0480f0380000480b00c1c40034006102e0704a400d0751140175592144010001d900782001084148014a00c580d00d001041c50582031505441d1006804148103500400c118009030b81e00c030080905a0310340d40c1c0310074510030100705210303090300302030b440721901d0350074050203607041d510f80c41580000b0182070720280140c0306c480c0c00d055102c21044071481d0110319240c1c0754002c00b01060344880b070055142c0b0035104c1c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 967182580 1250 967181330 967181363
    0x813050f010f031d1006051c03090506090d02030a030c1416030b0601030e0a051506010504080c01111f09110312030a0f1d0a021f020a0816060501060504060206070e010e0d 75
    0xe0444480c030b8814041c0e121b003410801c41c20640240c0b0303c0c00304640780c01c4480350941e580003004111307540700d440d00c03a1201050054980e81c4801c90240c030182d004040750020800ca203005443c2c07054208007070791050040c00a072045080007140c050503038034041e800d41000905690f60560121001790440303040566900808100d40340070080c4c5200c0c680184001d01e01c0d43d044910b00201d0303e40040541c1d04101d02400700b008520b42c000340c081c01080e400d0812000d08801503034601c2c41c060203400d903c0c0ca0040b4800404010003041d522090020340201c850250700c5492a0600d03a8460316094005580c4500f0800a503000d2010744c4407a01003540804c01040720407480070b80035210b4004454241e095000100000114070b81800b00c5881e105010720a1640703c0c00065000c0c0d1210000c0001521001000400124010f4403003203c488940d4001300c02c2181e035071903140080498000d40610f00152080340003048405000d503541e4800103c051f926001044805000e0202502034400203c0b05d50890f008184d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 967183830 1250 967182580 967182583
    0xe180f120d060f240201060f0b031918031211090904030203041221110c0d061e060e070503060a1703070b0a0b1008041a09070801090813050f010f031d 66
    0x40144405602e00d15031072800c81c00d98090404464546055a14003041003123685000301d00302003141c498000003501c981e1080100074000c14481c14840c6c04525202c544130044400300440d088090003603551404480f180030102003102c1e00c0100c14a1408002d1010420300e1502204040e40a0311074410759007410390b1120041f4070401211011100b4003503040030140e41a281c541401c0b601162850300d080070640140390f40d070725040012102d5000d045030003031a07414482c40f80c20068441c803002c401c0300091111800d04600800160107001c6014100c10081420640302d201034074083c80004125811091600c11043c0e619000700740b42404601091013031102003103440040d18401c88241c01c01013200505d0b00104614075142e80099020304c2548424000420741c030300d2a0601000030081c05003000d8039600074030391a00845a00c020703040d600b031001080c20411658041e240b08801348180440c02ca454004000c883c504498000303001070090788181d05050311035041180c1c1680d203100240a072020f150280d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 967185080 1250 967183830 967183859
    0x1f0e04140715033e160c150507170c03090a0b030106020115030b0c16080c07180e21040803040609050a24030b06190e030d0206070801061107050603010e180f120d06 72
    0x291203a50311031b0400c1010121079200004502e21916000741303403040e40d81c0c880d5940b007182c64205404880c00b0980e404001001c0080ba400500c0043c0180c102c9941d95062101c29802402060b0040d400c04200700b05444095500d4420740341c0c407582034541e658644020382e50540240303030340503902c100e444445004264903000400509034020081e010281c203180d0304500380040e503c519140d00d443e00c599024a1f803c00b05851560003114088108841504401d601c4113020300d4011030f072240800140022a01c1d04078500d101250819503e10400c02c0d40d039014030144042014082c080c01048030341a152507403080d03100c85008140282403a092001c40c81c3d0315981d0004c034520207004174200b030113640304c14501004601050310700f07880101a1842c09810080140b10188540c50a0011130340c4480c54035502440104003400d00540b04c0d584a694030300c500200030406403004420510501a5030203410b45c0814a9180b25140b07100070088501c142a500c1203a90000000800082d55200701240c1c41500810307030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 967186330 1250 967185080 967185083
    0xd0207060c0801060e030d0e0a0b03010807151d100c051b12061e0403140f03060f0a03030806150d050403020a05061f0e04140715033e16 60
    0x900994082010300300b0841a0055800d112a580301c1c13440d81d580c0010300c4c1e0420710b02032078101c40000f0054080f807140c4141c1e4100002154000c80081401c0c07000058810880b40c24004007022404404010f549a030310014441803608203480064065052140407420b00e01401d29100000c0034040d10ba070b90404c0c88101100140001340864500b0318070b03118103148009150800075101900b0704000381444040541000160042e14800150906000f07070422000b42007e602100c0c4d5815403105961019401250098400c181d6100414202e0406000e1b0744260781c0e15440c1d044960704c8500c2003101865150030143d0301c0325402c01030000044e02c2070180ca4001c40c440d4008014031000c500c0c0450503c2402042c1c24043c840801d003001403084036405440890b00f00c8401449a40c81d01d0400c0480c00000c2040c41019200f00030340000c0802e003d01d4545182c8c1040d5800700812105240c501889209040022010b0306000c540d03122040c2d50440001038040e01d035035501e4504000c5019000c84d07a14031810 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 967187580 1250 967186330 967186343
    0x71b060903030c02070b03090604060c1b0c1a072f0a03051e150a0203070e0405040b0613020405060f160510020408010b060304030203070f02040b0d050601080c060702060a140d0207 79
    0x7480d410a41c0400492010744010700d03021f411440d0248003256180740c01013001e451107884010b00445c40e17001d5102c0d4590481134403044042d0000e241413020268006100b440040c00e0b00100042110343c4080980301c80d26407020500c500c0c4d98808007c14003910300500c0f00c490544652100010503038544600000441c400c101416403001c0c118011441c1a007640f800c1070030b0760440080000c9030380d00d60108992100f44d203030707006880303403a800411130328070b2a204503041d0020320344014001444509280c2502c108000c48050240f10107a03001d010aa00a92154940281d800d11407404042e503444040c108125140700e1150700d1212644990340751180303c61003a2041030340014103029480c402e0180200c844025101c161441c00d203550000c0d524401d00754050207048816858a08561303564225140c034050081400c140d2021509202d0340341c200a10074540944a03000200a0f9824140280d030000c030f400504e01820030075401d401340c4040301154080440c1660410804400c09010302c01303014514001c40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 967188830 1250 967187580 967187591
    0xe0f01020c0f010c140a050a090f030b090607030e0a0206030405010225120f0c150615020d1106090a020105030a2c0d170c0a0905181b090108071b06090303 68
    0x80c0c1d5003103501c02844c080c20002c3d0b4440310b0f00850760324011900440040c0c6000ea58900f103888040f1880f40281e0000a821a400c020004c00e21040400b500d014200c10010344e54140c592070406e4045401c20407901c10303d50401e0503000302515201010307580c001d01440000d071900320440681280ca07002082d00200b03030403001100c0400c1c4035030075160215600381c1c2d040aa0003103c2c9048064090380c100000205034225103100c04c0c800100796001007004115514280e40f00d03d81040000e51070b0b0113400c441c100011020755178004004400903038940a82d4581014120b1091030b6001100d880e40300a0244551b242c4802005244281050044d029448860300060244c03079003140c15410000100c407100304200716110080035441d070145003150410784030f1502c583d851015840c15103040080381d01039540080300602a92060104070b0201d8840c4c44d24001c0100801a034600c03255050040b190300c24006583c2100203520580076810303910040164942c481c000d02c0d03182c0c2d95032003507410080d0201c00103034849 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 967190080 1250 967188830 967188853
    0xf0c0d020601091a090a0f060303121a0d060504081207080f0124120b0a03060f05090d05090f040b060c07090b061c020f1c060311041107060e0f01020c 66
    0x1441841d0140007404814485038500c4c0b0070312084441c0020f00079208410500100b1030000450380482c2501c610a80c080c0715559581c107015203c072244c401000b4226041050000d0b8034290b82e03c03401d80441c40204210b401d0b401580b6800c001304401842150090010452490030b0800b00f44250b21441c010b5031a40c0301840c1102e05417001c1403040c1c1c88072401256011042c5120318100108008a15a52406880e18142c0d02c0c400c00181000e5000c03507400c2000c00c20301200f409215044614035402c85582480705031200000f941d9141c080c0070880380080c0080c0302d101c8280c49c10000b034000d086002000850246544800203220b540326042c0c943c520361254a04020f840d00c03c2c050300319041000c80d940e81c103100307a10310110a0381441c0e0400c60b00307a41d4009504600b404198065511400e1504516030103502102c08e903134001c00c071601085d40c4180044000403c03e02e0030740200e240c81030341204d00c5810410381d5507503040900180c44030280b81d0b02902c011400358000c24030260041500701c40c001e01401406 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 967191330 1250 967190080 967190083
    0x306022a060a15080a0213110a03020c07050f0312030408070c0905040614100905101e08120702011e0e060d021e09060a0f031e0203270d12020f0c0d02 66
    0x201c1078044944000b076100700300943c004591031715540d8040c1e4564a40103a0700f03034414020079800252042103030021030701410306503055000d4241030f42460b040f105196280d00c100404a032907200000d902d036005074800c40300a4925001755400134800d14619003803001c6581d608a01a100790402c0d58507980e10404c102c2405090b01400c04d00d00400c20090096080403010525080da840c0181e07144213413540c001c2a03d0944980c1d0840062041859048040011000709182c1124a204094091042a00947c80b81e040707a4102c0e034102e98141c54400e07411b8810120381c079140005001c500144041c9070f4000840d030329110f00900f03889800d1840103a03100920420701d08503481080000449007003e100040641e02d4034021507a0102c65401c00320728001082d001200586580c11210355500341600004450401c10f03009107024042c2c20024999040c1000a001e08034508078841d0181d69000d150b00c20308241c0946445440b500b14480c0140ca0625804000704040d40b15050700d0b14581c0c0b04403002202c140d0b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 967192580 1250 967191330 967191341
    0x6100221031f06050313080c0106080c0a090e0c04110c1e2b0c0c0f06020a0b06030309010f03050a0f020f07020126060103181202060a0b0a030308010306022a060a 71
    0x60b601d00c0480c914103080004286000051048040c000c4074000303070040c440540c040c0c88948405074001d00400361071f061405c2d1180852440b0900404580501084880250142000302c07050700d40104074451110040001810020310701c03001c5103100700800b820480c1c040c0b02100f8080c0030758000443c00350356800c5007850300c5402340c8070351042180c90b150036103c0c00708607130f48209200151038480e545070803030305045006000d5540485c14010f001030002421580100b04a00424007400c03480c44560b80d180249070300c3c1e1184000e003a00240100000c01c07150303406640440e0300400c2c10300300000c9182d00c6e0030060f030880e0712000315504260720110f289002c5690214200718404020501d07560040c1da042041d002c0c807403000e0103050601d43c4840ea0902007840303501c0c030b046000d0f400c03c581038080803c400f0b01a4441c803040d278106000a0a150310a80c1604050355450226070341607684c0d4603280c0ca1510707840025000744a10b24990b0036125100584622041c0044010200d0714014081d00d082841c0c105046a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 967193830 1250 967192580 967192621
    0x20109030b0a32041b080d0309020109050a05090a051504020f1c0212040f080918040b1609170c030a0b1905010b07080a0e10020d080105180610022103 66
    0x810701d02c1203030b034802900b40d1541e0015440700c40901c05104005e0200748800454224081c144910802500d00f168180c00c5108528000c0e2101c00c220380c0ca840c18403805000b5800343c1034110002c4c40100b41d49121950085034401d0201101d09850500381002400340c0c3c0c4251400c20900b800410040c05c9404248100e070451001d0b040e00714504075801c6400c0c0700103400100702500500d101c080103400d101019041380c544040040c10b204002c007102611180e034440075181580d41103407003c0000c0d0003224003103140c21080402d4989400c00c514040d0301c0c501243d40101011040d005440903107070692020071010140381d11464407103d45c0d10305280700880c203460510002c030344181003a00400140c0a050100d82d0456002403030650b45041d050819640300c1c0c01c0d4400943c11078064510070443e60f50119007840410384c69510700f19039980ea0000c0081000c13407000c00d0001002e461000c503080b4075209400010400b601d0040d00c10703071024049132400d050418441035034014400400c014040342d03d640600d1100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 967195080 1250 967193830 967193891
    0xc03040f0c1d0a2c030f04270b030615030c102006040c1505090a03080307030e010b03060609040c0f0b0909091c05130b040f03060b01051213020109030b0a 68
    0x81980300503902204c0c044000341c4c00701022002d05694040c106104070340f5604c17035000055580d143c2d00d0742540724620800900c505000b0b00745411409403030b8540200f0b014008010010512511481240407403017414042c8242d1601c81c5240030700180d00d03040040c60818070141ca07004036080c00600020078248800041c00d40320f070080000c00c80010021074410040d218110801451101c84806c16280e500c141c1c50311301c1c1d10110400c400400c101194004500c100c503a0b81d400d012908004601e5400e851142c0c0c00d50781d06801200005800d820708083d0241d000303004402c0307103800e10344c0c038040120300c498141c00c58510711700d0016000311701d803e007541120b400107010001001034105004c039050011141402010801c040007480b40c050004806403000039001800710070303555650b07403000305881c20602e02c01200c5203424440011401e46c0501c0c207481103051521001080c0f036039005400100706505140072814401008030110100b141689140d105407000240016050404880039664420701404414030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 967196330 1250 967195080 967195091
    0xc0609060c200607050703050c03030f1207090b190201050121140705030d0207180608060703180b090c030606040c021e030705010c0804110f0105030c03040f0c1d0a 72
    0x6103503110000d200740c0303504030407102051100b1815003464205082c8601c0d901541c04102c44050003070200e0f000c2c0449118104403040b0303924000915889002d042c0071005140424440d00a112030041207090b80034506251102c00684c680b021070f94550094403041d00d03402c800b8001401d000e90240300c1d1601600007084a1003001e04c205800300d00d90b22441c03800500c1d20303050441c1007035845820010000a0701c3d00a040e5800600c02d2000250307a12a2441100d01c01540000c686060381214401e42c3d081ea048400034000f55034480000750090020361031081101c4020036071400215940026023405848540e01070b020082c210300030103140c1503002d01110300c07a80c07a08000840306600000e01d845442281f405140050034411003160842c041c920001d0902c2d400c1100081300b1591245510380301e14420b983c40c1c8148007480c804e1001a91000603d2804241c1c200b001c90359012000b00519030044c03140081c0c0d106080d9665405002071601c1e0b00241400340c501c6140720103a207045501d035502200c1c01504012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 967197580 1250 967196330 967196339
    0xb0303070b04110d0f0821010602161205150915040807120806060a0f110607030c080106050408060103030e061c0e010f0b030a0326150406080303070c111201090803040c0609 76
    0x17101514400000c0540c24000781d40b2005550100c441104a410080b94400300d694800700a0b484181450042001c00c0c5c00010118901140410a40d40240c1010043c040c50310384920180304d282015140c10b44501c60b100d01111400076501032a8452840f944103203460b080c4614144111110500105080c0801c2c0410085540c41c3c1c1c0064031f40e81c41051030b28015400108070295010203c1d031002c2609406110b0807c04102c0e0140c0040910803060358400b011a0399845080311103006a001d24482a0080380c01000401d00c01d50000e403600b00000c001c1c0b841c2c8000003102007007030019041c01034070982d29944c1c00c50103d10280f0888500440e010300c14001c0c0600280000d440c0c3c180c1c01401070901600e40c4000c40c0007440c440c1540c81101071101c0b00340060415600720780c80b00318080f4003170340704a09120300441c18090200a4074020110f0b91201a110503050760f9010900080c070f0801034020507480170f12501d42400340982d1000a020f0f0b4000d43d0b8a04080c14100041900c0d60001410300400480400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 967198830 1250 967197580 967197593
    0x607080a0b06041a181008070e010e121c0302090604030f2306090d0903081603050c03070f231002070303060f03080d050f0c07020d060b0303070b04110d 67
    0xd40c0400000c0001074000300c204000b030002e0089401001d410b6041821004120203920000d0800c15030041d03444c020703c0102c0041182500c803503002c80c0b0018030710310003245a4034061802038000b403105042920700096154040f5000184078041c07606c2c075034003000c003103007003003000450105140d001d42c5415458148a10b0202d0310f148141d10008105031101c000820a1142069039a4041c1c803c500328003640f41d2070017801a554070010f0312400507900907000e92818550160900340c0459034000b54460a000b01d480c0390780c1925001c0c58041c0c0500c801000b030403a00607030601c000c04a41b417040c0301c1940c4069103400d2100199a0144c0c1c0740c441150101c140c80500c0344001480d045681680f5005640e82c00341d450304078040c00701a0b2020825400e601004410050810083c00300d0700c0204c5010015039489001107004030005541034400722604003c50702c094200240e01d004001d0055030302140000a00300800d10f1030f48069400d0fa0301e03a04080a0004101c82c0e00e0f60544462011181002c41d41e031551a0074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 967200080 1250 967198830 967198847
    0xb0f0a061505030408120103050f010501051f0e03100f060f050f010c0b040309031b0501081006090b07020d1a0106170606090603060f100f030b010c0f140f071e0501020607 75
    0x1e030280200840001c00304507080c0c01311103410001440885540d41c0d02d29000d542d55605602d50032555080038000300301c900702551514220441121440040c414030303e4295040c01e9250b90164040c040d44002c406d11400c3c600422140c09081940010b10078034000d1030003049201034100501c01e040300108143c0903a440f04040344190b4101c2d881a0740740c0c40c0c40c41d05944014047d4401480820708281d0075034011002c0700c19a046500a884024056540569403104460070340201d9003c0b5810389401d104e0111110040c000442c030250070020700740542d8942e44440043c00380c042a440c5031500044c4000c0743e00040000201c0d1261345551030034180540011854010449002e01554001c4002440e5644080a114820328050252042c0200840380100615001c01441020a081003640c0700b41d5403003441140038480c1c2200c07151000c0703c856503a000090403441e2000304c15110301641800000300030b10001000307190403030021060a294580c001c1c0824041c0d40840e066401c142c0c01c1042171500001312 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 967201330 1250 967200080 967200119
    0x9150301050d061805160311120a1509080301091d07150f0509040f0f150b0f030603010605150a0207060908030a0c0302120a0309110f012c0d0b0f0a06 66
    0x400e030802c904d004ca6440301e90051000d805403207115101c81c0b00480110400341500e000740405031124803164144011505c0000c848a038585c052041d190124405a60780f103c0e20032500da012644030b078070707446500c0c043e0000c7c0c011600315030341c0b100c0070507079102c0341030b140c3d6000340088002d0506140f405441c00980d140c40700c4070105220540c48070410052084049402c0400024005c0280350788060444000b0b0103d4007107640203034648001142076030312440407901110f0206290b80c1c603104609030014001d81010300003940540d00c804022911750b944107042403010062403203440c1c88180350b102c002d1410107036030702c04024400356440034401c402c1c020044402c1c0141c2c0b41003d1020051034503080f49448000c50407141c1d422004640000e143d645504410301c1d0364043d002006000ea4280b081001c103071903003d40c260101d4460801e02c080e8824130f40ca04030075410700c0120009200f0405010a00c2030500000480f041c650b02401c10140c48610382c036041d0448003884081006504141075605c0aa96000c00e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 967202580 1250 967201330 967201343
    0x14030c010c17040e09030309101e11090607291005091f15180b04120f120309030f030506091306110c0309240405040908160809150301050d 61
    0x440c80c850000340b40c1110000c02200d0190f6040d07203805056291641c10a0300c80d43c45900a030300019518004034020200f88503c80050010320b841603c050000404901040000c1203005001c10003481c0e948a0151400c2805901030031510b0781d607204204001d50301c040780060910082c1090101e1905013041c0c480548400365044025034445104503450800c955428a405480c61080460200092408451080d59030740f6048034880300c044442b0458201805855920b01c0188010031440c03405e00c0400031124014400c0d104006e18a0710340311003030b18107401d4000219844407024403c0607406507103481e070074600c0d19080103035080c0127002603160b006c00392107150708988910007482031090a91000028042c074280e00d0303580b40304030250ba544a4008a080b24840d81c15154450910003082050022805001c9601844c0c00d0130b00b41013100030003107100d082c1c3c1d01e0304003801555c4500c07030038a20300c1403141d01178102e40351520140c40400c07460304020b1f00c11907804641400100495140c0d407040301031040e070080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 967203830 1250 967202580 967202603
    0xe0c0309070b0d0e070f0f06021b041508011401050108011203021e010212010f030501061a04150926010c03060e0604090f0507030c08010506040513030e1c0c14030c010c 74
    0x8910740901101540d00100d8040d00d0400905214480e40310000c03201c031f000b01541d6150703440100380d0b00c1304020884d4000902d50b07543c008100d481d10764000c00201d611444110030460301d43c100e65084410000c400b8101c51001380061005682203107819004050032014010480810703a4000d440310711026580d131a4401e0484c042d4443c3d031003901038425103040515120300c03560352141c28a440001510003aa515407900c0c5001c00c03034041c09050070404c00c0c0701000c024a0103180011203915122000043c030100082c040004c10650103101942d034108241405a603021345440307444030308454a203510b80d81494900070080001c65a607812040d0b00c99811200081c00000d942880a80d1006036a0000c0842c01401404410450744101e401c0c290b6072160002c0203a40e680405010888405507101941207803a0003030080002e11400d5449410300014151003204110001c0c003580598070110202c03a49020201c040c4061454a85003403e105400ca00070700080b002c0e000080c0c0068034288001c0d003840300b4030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 967205080 1250 967203830 967203847
    0x2d07030f03092102072c0411220b010914280306050c030925050d0c080610031407030f02120307150c030506012f0708070f0e0c0309070b 60
    0x5151005210f0a2180700d24003401c126900940310b4105001d02a1510b80e41c50600c075030000d50151845403600a200d8040650700c40c1d44070000c4002c00c20380c1580e0700c40d51048520100d034007203094036507800000c6030010410200c010005010900d0907040b4500c0303d1414031100100b543d404007408001d5030300030070040b401078050840c1c56081d50307244c0015000c1030524040c00309102c6c60800443c07080c203004c015226281008184001d42c06c04814081000720305000f01070207580741604800f03031440d01c50003070344110507943d65199045c084101c49002501e80021010024080c401e1241c0e46a0b005020140142c60304558405a030350030001c4000e80946034003180d910491400b001107905071381d080a019468079241030074140190941c0d60300301c0b00080c03c1c6030204072554082c1150007100148060500160a03c16241003080c01501004200c1c610458200052203002404910050700b0320000754400c040c10050382c41c110110140505884210030420000f90701e20202e85c0000380e500b2076050300d0707079000700 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 967206330 1250 967205080 967205093
    0x206060f060405040c020601050108090304060f050a020f01090b06010f0e1c02060c0109060f0f050402010e060c0a0b04080c191a04020a180e0606010509031b010c082d07030f0309 78
    0xb5904066003051400d40b40400f82600081c040341268803d83c0e950030150344070702c41152240128810300c1c01240048400c1c10500d400f03400a0843c007801407045800d4400840d203000d003075a0b001e040a981415540c01405800d50b030040e00d90900381a0707410404000d003841c1c2c0108201501d4102c810220000c40e81281c1308560320302040f03c0511030309074000d0042c529141440c20040c140c84108001039490003c000c2a004114000d0328070a0b07805845442108500c40b043c04141d503ca210b01001a011703405400000034030150040b80261f01501c02c4c039448408080700c040c0b03040444056125060002c0b80000c0c002030040d5070800e00b006056400c001113807036a1000c102d1545042e0082001c030564000b0801c64003801c2e41c083e5541207a20801c43d169900d5100040da1140725402e00d40d9090b8108000484105107074109000c00c600d010714110703035101c8031903c504203c1c6d0401c6c807a00c45240380c480607070400001030307510460b80c1d2005815400e24010607170b07a000d020981d0700c0034514141500c2e034800f8010f0100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 967207580 1250 967206330 967206337
    0xe0c0c0109050f0115090b011b050708011a04050136020f0f0c010b0f0a03020f060706050708040b100b12070c140c03250b250b06090f070206060f06 65
    0x1c0c071a088a900f5240301902e24064803803260401608140390000256441850040d11880700041e11134040d910b00070540b001000d8522041a2414403508800203200781003440764a540f81c2d900809001020034200402c0190f0394182c0c440c010300200010441030f040000001040380c0b5030034503621210000f242c03900e80701030b00941144c100c00f0f41d404203102c1100c003403981c0245030484449008000c400f410780e081005030101507082c81d030420700d446800c0c001818120505490800010a203030f0030928544e880d0010f580d000c440c40800150004180300c20443d0020322960010341c0d03402114002401c00074500d01c5802947d04510400340240040742d1428082c03500840c01c5d07130300000744015210507112405d036114154821240a8468918510b4550800c107180b111085100142044020324081d282d400380d03009020314104100100d600c2411070343d190320310150251700c145a44411440c1c0794080022040c001004150b00c80b95a01c10001600d134045415039010f2011251000003440704404200ca901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 967208830 1250 967207580 967207583
    0xb0a0b0310121a071e0206010b030604090c030f0c051201060317031f091a0316030201210204081f09020a0e070c0512040e060105070807020906221b0203040e0c0c0109 73
    0x2c3e80f5034240060380e580a5020307074600c2561044040802d8010200b00c7c1c0c0e48800f4801c8951280c818800b103495441c15400250b40140100a6540980d8690b11461010400c0743c0044071040ea052030100060305080c01d10084e5400b110f80200049032464480418a113080c807041e0b4a2000000f000522001a5664401d1000c0d0082058113200e03449100c5040146888078608403c2103002c6510007880c03900080001900340c09900394041a442e42d80196031a50409602e06134400002c41c024242090600c05040180504001000e0328505c100207000c2c001e50042c01d00d0342840c281030a0b500580c0b1842030b150b044030403aa804100c1030740c0d0640102c0783c102c0c00d02801041401640e103600400c1c410840600190341010104100d41d4072500c0041d140c522940c9401481e8510074007140c1d01600d00281269409840500707900001113445400c00b404040012008550960302e0010100401146d5600c4100d4142c0340015842d06091015000d0004402895540b105100094501814000390000011315 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 967210080 1250 967208830 967208873
    0x10302040203180f0f06160909051e07051e04060c020f131a0a080610230607030c0c050402040b070b06041b022415100315090b0a0b031012 61
    0x134030400d44107403203911000c1c4902d4036104403004183c074032140c0c180305070b0428810b0322100d40d160318011840002d040000d158003034a4690200c0c03c150100c07441c0440b480f44803259502a074401004029400c90b05642c640d09540d1041800305210303013030b0800c810404150b012a2008010f02d1903000280c2110050342035141c60758241100540607484000320302166540c12990702c21015101d0842e9035844004a84403480a510000200914200d0740981101c2c114909106c0c061040b112000c2910b507444588100d0002d10320002d07005c02d02518801e103001400c8125025840d162034245110700d580520500030f80134006201c003203240b036516584003071301c800f110f460485005c040000c4040e4032000000c00c0c00151040c1030340c007008480542103046100d143d120041c50680818101844100c02001b4500801d0555411406d11000c080081e40001404011004210b4201c1031040c010521603992240b4118402442403002d012500c4c800607042c1c8107080d1144540e01d0203030810461181c0b0020045160 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 967211330 1250 967210080 967210093
    0x130809040e011104090b0f03030715060803211522140a0207031b03200f01060b0c011107020906010c02190b031e0609040201050d06030804091b1701030204020318 71
    0x804012a001d0021210b020b0170070445a10501c05012680e80c070b0b0500c241c2e054004014041c005603401c680364100c01000f0000050007600c2d8000a07155030b00c440c41e16100581c4013100c0210051007038540c2a400010045000081e800d000e001c030301480c0d100a000c0e00d400c0344440201c407040c142c96002404680e8000340021041c10310381da14100075031000c042600011401c080481d80f4103100c041100080364103995440310700010316605140c50b00700d464144480c0c054410814000d04003401030001901e40c4c081069030301c441d0201c140b42110110700901208010500c10900940c0c0d4080c8070b00c1c2d219900303080024041910744005540a00c581c3d0300303100c402d050341c8400b0138070f14041c401951054646005400b0700d02c09400095010440446190f07030701c03c1040000174019480b0300b001d0310395480942130100b101501c0385d440f13071100e42154010850392076417640c80c40b40c03901d21124000201a83c0d4184060803814a0801c0421110f0500002e03001e580c001010541c020487c5207900f84000d065816682e2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 967212580 1250 967211330 967211351
    0x9011401090b15070c120f020d0605150a0305151012050a030212030919060e010e061005011106010909020609060406020a030314070c14010b1807020d0503130809040e01 74
    0x140740e900e00c2c0324000c0c004210350403814407204048503a9190899070781e0603050300d0103400305c198401c640b1084482c0c44101c140c0000680310402e001400d139109540110b094900400255140140c0604141c82441754280c00c01c040b03040454003051407268000700c2c5119507900702d50803c0b01001c6a0108000300c09a034410003e1143c04109241c40364443e40c01c0e01d0130b9220881c600c40c1c45020507500c4641c0c5030045281483c0108c1c201020300c1d60303e440b8903400314038202030300f69060844201d81004e20254000904021070000001c1c2024040c0c0030034201601d04015480000750741c0e4805000e802074065030b440215096544550a40c0c5100300c004150390b0b40d9940342c410017907e503000e12000310301207820b1800c00c81c14a51185451403050100707540b500c0c050361087c1c84900e00f800d4a2049841c295680c2e07420360400340c03500548024100040c21014480b4240300d2002894020340d408060704001040c81801f40e14181211030100c0d0542000e01c1039241c40c889000500200205499140658a40b00d440d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 967213830 1250 967212580 967212599
    0x1c0c030f030f020706120c02070f0b070b0612071e050a0f082e0b180901020301170c01020604030804051e101107050d0c050717060a06080d08040b09011401 68
    0x45006220760346158440d244070005903030b04c40c107500501002c200c9901c0c06141032070250f403040008039001c1c4110345805503180140f001505140d0000e0000303c10001c0c1d00810f0241071182681c00000907034503901625180c10b5440c3e00d80125000b031070907869101031540b08200805240d18051304000f00190141d070364460301250182c91038402c190346400780020031605402598815050146209036610741c80040390f011100a1070a50290f90b44050032500d01c02ca040c494103482403180300002c000580c0d950504a40c2b034550030b000440401d00e540700d2080c041031a42c1c0440d003960003e9150500324560749484ca400b500300f4040d801400c1d44428146804c1403035050005800005c0c4151510801c000050580082450321440d0f10207000c2d80e002820000e404c9100740c542c14500c500a07405d84844c3d03a11215001641c0200d15030626441e8040f0040c0311281d200307403150313400511304a80180706900c2c1004c00a02000b80090000c1d000032a0800042e08412b029003040c0482520304482004640c1c40c1c0b002c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 967215080 1250 967213830 967213853
    0x1051b01060f0e10060503100b071103060c041503021e07111309051c09050901030b0f0a0c3905060f011d13050115180e0d0e1c0c03 58
    0x1400e406440140010490032041d00e00d8014a42c960a03080050b0074174100f5202c3d64400b43c0700f1461902000f0000807002607100180c405944102100b8140713144103001c0621341200035101103100d100c00c10041002c0c04121148401050b06820f0240e06c3d10002c181c0032a20211040f00b4003c0c00304001030003801c01001c0703415200f01da5400c41d191107400f00b4100302c0604030742204c000200305034441f00a005403486610340c041220f030418542904055220000300d0540502a40f040701c1500748a401c0c4025045400e00466100c1c001d2582000640d80c580780081c0001e80190902e4820f0940c4201201c9104c0900e801410002811901c0f068040a610300307550f5440b4226003004c0c2c14140000041608001d4070f01400b441c0d0126201e9021756110610020000030301c16030b080381c0a40d65201c981c2c03c80c42254039039400801c0011004003040241c50b01400950b0b005a01c5e14589820241e0501a5950003141e9940c042e4000d8074580c42d42401045411600010701c0c8014003c07105c0c41c20004100809082071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 967216330 1250 967215080 967215089
    0x31511070b1e13021e06191d0901030b06010c080a050d1107030f080a241503060602030d0b0f060c2b020307060c02011b1206050105030103020d020f01051b0106 70
    0x24030b10500480e000180010307905075080b000c0036000708528070261030072501c801c03200824144e003050400c204000007041035000c0c1401f100c0f0001c10000c034030b02e0a500504c00386000340452503030340511004540041c000c8441400001c050304076160105000742d0bc00c0201c501c649600c54201e42d641d0740c2c030380005802500002000c5a0360750a00320790328450f10f03401040d11142a40341d00c0f80c48403078015410130354003500c00602d0359132002c1d915611b50002d2139910012800842c034100d140d00b0300c1ba040124583c81800a10b000b001494200142003103440e078000211a0070700c80b0f202c400204a040c900c00174008011114101d42d01100200c0c5561203980c004c83d03440301220060b8590844a552000c00d81070710040400c410300540c00074814040071499a41010055008034400040c0ea0102070751260001e45c801040b400002d00041c003403110b10b203214401c52010344824207001e8210343c59079000408841c0603c800a000f08a00024031360f050f4094019583c8443c46028060680a18070015a008141038805d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 967217580 1250 967216330 967216351
    0xb030f0a0e101422020d0303110c03070c03020f090702060a0b061308030904051602071e03120207050108010f050f04020a180b0c0d03050903121f03050f0d0302040f031511070b 77
    0x40c02c90000000d02c4d25101d5980030b042c07082c082406450550050803000c1203045140010047c0c040882014030003000307007901ca0f00301050928114010b00629440710841307540174061050511100700e0300040c002e03a203d4044040031a07541e0064010540c103004030041050000d020700c2c00412440c0001c4050040704c4016076003003140355111443c88510305801c048010141c0c00021050083d112091842c6808480340c807550040a9640d554444440c0e00562241c80140c03c4a03400707100a60744103004600520081c202c00900e94104400110041c0609038031030b00c21580010004000c502071171003040f0300e6012210307404d4203680e01d0610b038249500014000b0020f0054107910720001d4000c2c4149400740004000841c1401e008ca501c01e081114086d1100c0224070070899407222074140d50944001451040014000440061520511304000c0940101c28180103100a0246e0034030050341d0320499400003000700341803408130314031030040642c2609190406000561441408030000c551801004070f9034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 967218830 1250 967217580 967217611
    0x4110f0d060806100b040306051b0c2401050f0d02031510060207081c0c0c030b15011106060906061e270a06140901021009030809070b030f0a0e1014 65
    0x400513903568194003032108070441c140130900200f1b00310b038030079644902c840070a028440c0904e20b034080c8a40101c0c00940c0c40b9803242c0e11100760440174441c045501d101d290a0f0010740d50601000032100412000041d024410703001440b003e541e010441c50407200c180001e05a118102183e181d9801c1c0b030320b4041c0402501c034144d4001420400015201288603891680c403080801e00315003220810a004015240704121203c044042030b2000d00c890b0081081c40c9c1c681201808500c000f40c0406180075144144d904420200442ca403590010b082d4441400c170b030841d41c1d81c014080740e1a502c080b4000d00280e802e80201c0c0034010b04517414040c5100e840c0700380c0091415a4004200500c0410700d009140014201420310341181da0320070003501c0421014016904007030b0700c900c1d1460854002d000300741c000511100038004e60711010b114040c064090500c805141d80b8001d005021011130207444016480c1d44c41120285000341032040d11340780d214992091085042e1401582440315003600e40d802144102c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 967220080 1250 967218830 967218841
    0x10210f06031b0e010905190c03052220010c0501050c030601031a01020a020f0f06071104061205120703030608150103030806040209010c0f0f15020d0506040b010e04110f0d060806 78
    0x6000c050803030301840c218580d00c0e8240001c2170f005d40340180103522a05503402002e01d403029240030b0140c080b04680e600080621740011800010708084500440304411914580b003c50b8540802c07011030104a9250020240c2c1580122100e40340844068029482c00c0e043c45154040c0d40006c0d17000b20720990703040c0040d5204010f0000c203501c8141b08180907030300c2a203103a0014100f20848000c4581c005050ba800c0300c0003074001c0b03201d80c2d000040445000d4980010760101e403801c0d100c0ca0000d0401400c420780d29410a94810740d03550308912803401410340220f0201e040512030380002c00074012002c191018040001a04031011f407081c00100d011641000000f012800d040c4280c4403081c030140c0d6400c481500607215018000c02e8550203484006001200c9804600d65041d00a0401c4202200603541d844564641044440250141e48218140500f020040e030b44640403420266089400065861030100a54010320840c000c0703050444010032510030049965106004803421a0305403145540c89 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 967221330 1250 967220080 967220123
    0x3020111030f0403121104140a1202090408160812090c0118171e0304170105071218060e010b040e070b0415050f040308190801030210210f0603 63
    0x40300d40380504500702c00024080380c0f00b000300395800100c880300002d40740c090000145440d8090b402c20503801c94420344103041414507011070001800c0d503000a070341c400804d90028450700c0d401740000d00002c00210b030300407003950138039000221103902c0341c1c00c4c980d42c007440c2c020010f40d940c00b243c10364240e004402140542d54010f50104102e003102072540c900c01424240040c64000031070b800707000705115030401410103041d80c240c003000280400c4002c41e152440c1100c885104d2140c2c80f011491a4140810300c00410382003030104024400914001c10096190300119805402110b805000301e070078642034283c0c0c5e24041d40b03c4284904180c80501c000b480001c041640c50f1624412106009020041040390002d4815420b02c030640c0352034074600e07040e644103500a16400a8009071550304c2d00141c5095480382c2000800c0d02c012040c106400d840d1f241d90006569100c1d201102014000c1201c049094003400f10140c042e00c007504001001021160441c4c2d41c0103009900045800c4800300c208006ca4400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 967222580 1250 967221330 967221337
    0x60f0303090114040f060818010b010c0201030c030e1005060a0f0302030d0806032e0e010c1d010e133c09030c02100f020c0616020402090a15030903020111 68
    0xa002503140c00407030380045502031203010780c42200e004180004501042c581c000c01004220980c0d0741e540c2420b00c0d40041103140004801080345a1400024190b5a41c020b6007440c0b00980900300040e8030b4903035803015800380681c2103840c611802551080c0c0c501c840c0b07a0340b155001d0030007522a85031003a00caa04c3c04046d200180030103541a840000d94129007882078885540c801005401e98540c0c000c011200342e89800350b620151100c406240700f0080c040f04503c00d80c130080600310000e000310b00014034003420384188030405c1070302c91203042040701049c1d0041040307549002010b4080740132074900c502c450005040b413414100c1c0280c81900c9104400f07020a260f43c000f002c24281c1d00d03d00503a2507080c540200038581084060003a8416181c0141e95200009400c482d9107456000c00084d003280b000f81010b0000218601c520020b0048075032401400c041d1225040e03040c0e400685d25084000000c844c1d0081e40c2c458030100312580307466607002d54103411010603244650000e2040c0c2c00310341c190b0b098500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 967223830 1250 967222580 967222609
    0xa1409061f030b13080405060708030a0c1407120219030e04060b0403031d03010609020a050a02010b12030d0f181b060509310612300c110405040b06040506 68
    0x10f0810000c20003010381044000400341c801c000e03580c0383c140e940010600302d4025040c10b441071340000c4104030f9104468082c040d11034115181011081a05d1483c5d01c8550140b01c201400000c034500b41020721a00802c112007440c10030400441c640c18403442e000346032010140c1d006002e18200140080c0350380d840401c0c0c90544c0d40c99183c1c80c4030407210045403840300160045143d4150340300c8400040c46c0041e17200a050304411540d41b16501d0015030000f0303003558442c005050141c007561018041840e40803042c0e0740b03407803021174000c03070b02e81802d400b034401401c0540e1288004204001d021003c0140c01c480d0141c9500e2043c01c2a601d040d9110f0066520b030040300035260300600c50079220082401142c0040d03006099014012401040251134003040307a16581100640d1410034901005000341080f03e45601c1d2100403840c0e0443e1a10036520744441d909162020a01c06582d0f0414200480f41c03041b8100c404010b80700300728600d010305110540240503210305000b0343ca050007084280c1064808104103c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 967225080 1250 967223830 967223843
    0xb100303172a0f030a0e010c170601030207110303040608010e2202040b06070c0e10090908040510091701060e090a030f1805041406040b0111070303080a1409061f03 72
    0x84076001241d03810044400c0c101d40c08400c104448a00f0b8a84840070358082c506140303001800c1e0304c08903095401c5036080d564605c10701c41c101d2100c19821400d900700c0c1c1c0c0c1c041000c0c60b0158507080c052815043c00c3e019003508542c0b50201203000b05c0d40e9607220403900e0403502d00701c2642c0d4541d1510000781c442c5000040d60309210310520070360b81016080a801c1606500400380c01a464841151035080034000340c3d0b0400398010071005c0a100c01c0360020200c0101406480004005502d213076586c002d114440c80c071a00d4081d0380011040d4220324014140c0b10010220002c081940c0e160b4141c03400c3c000c1019000d0010345801c10008540700260000302c41141940c035454003107440308884001d881400c1443c1110f19140e141e0b001c0810b09480360b020390300025580707039400341c5181401070030841601c00c210882d03810083d5442e03074000040c0002076080100d903058108554540c96110501c400303480303403a108140302c01a2034240a020740b4001500d40c07103100c1100030b202c1040d544010011148960f44006082c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 967226330 1250 967225080 967225111
    0x114010806011416150504050c040c020705010c02040b0103140c032401020615220f0b0603040206040e09030d091410060b0d05101502150f06010c1401090b10030317 72
    0x2184444803134030000502407400240f00d950418005000e490081b40d04075040c0d000700702010fa8506140c000c42c0740c0c940301800540551790408000a041c482560800382c451a12000d82c0c1c501a40242c2c4403c00055140401e40c280e450451f4105200e83d10a503603440741660407030201015038410300024448910305a015100f25140c01030400d050303d08e400800d603403101d1a4001c603061142501c3c40080b0f08022030b040440d024019a2401c0200d40304070740ea0034040c0324100104001a603440c021a81610001c0d00f640b00719031203066039649980644500100201d1610000b1418048042080341d05c50704c09000715079242c00c00c00c83e05070903100140b241100301d580510143e5000d04e4107410443d07101d03407456070850840c0d58820301c101010074004910300141c3c01c034111103928081c0c044180c5a00c094806203407502418403000003020800c41d9040608868543c401502c2040c00079004883d004d034000c03800c0c903914140780b50b4150a51400c2e00c0100c010428800b14a01d0f82012812a01e1069614840d83c1da40d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 967227580 1250 967226330 967226347
    0x7050103020f03160201140a1a04150506070611040e06031009021309050c06070804050909010209030706200604141005010503060c0a09030b1906080303040210050c011401140108060114 81
    0x40c004c981c540200944d505d4000b41158801102c890354440c80c95030001041c00c80103680c816200005828050707000e1800c044410741001c2d000500e06049460540d03c0e03980d9200f09081a01c014041100d65175802c41c000180007402007544803c2a0146104030141c41d045101c11641000712080c0480c001e420030750202d07010a40680320342c03159030079901543c156800c0801c0305000440950201004503081c0e00045420710503414142800b59100014000841c40e11a14800280d0340303070624442e5108001d115100740c1042c0307681f008088010b140900c1210301c5d03800d1520b04065465140c041c101f83c01e216100d030081c08000c01c0d00456040310301c0903001d04880c0c6c4440f032450485512402c40c40052202e41140000041c5014040910600c6402a0190b440114025810940d02ca540c0400255441481400056540d02040190381e002e00e08005550710404001103015040c0030000e50350170101c28000240c1c0d0043c5407048820604240c4c2c4201c4150b583d88015140340107281802107112006201204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 967228830 1250 967227580 967227601
    0x60605181e03160e0106020a03051806090d0302070303020105400b0702060402090c04061d010207080d0e040b06030f010e04050a0c060221090d03050f12071107050103020f03 76
    0x8854405290044001c0101480401d141c052003030603c0c0049204a40100b00984148401d40d0141040e480641280340d0603840c000c000303006500d02648400001021815030756101d2003142d5204001405202c50501c182c00c02940320f0500340300c10342c099400c2200152813502c643c0c0112244800c2c00125007142e0803840708264810030480c4a034050008c140c040440460441d41c0303814801c0314141c2c000c00d0149802e01c14800c3c00007000d00481c10703601c1c09010500c00d1540022a08400117412010000400561070040703113010001da1115140e07000c1c403002c0401003544182140e4803004141d400b40484082c0106004507444111031288107204008010310812091080c4a908140184100c41113208a616440c2908459500050141c0c1c40702004062000c41001e0031050900d0024207a420500c250004c103100e070030f03582d40007030070864005481e035078181d082415500241d8540000d01c00718a08a240540a01e0200e00c00850354829408000340c951f129000710780003013a00034045e03404c5489104506 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 967230080 1250 967228830 967228849
    0x3090905090d1b0611040315090210030b01200102120c131e050a0609080d020f060613020c030d090c0b090f090a0b030105070e010f020105060616081312020406060518 73
    0x4051003580f160a441c003044a5014194121007120001a50f56103035141c090005a8034804402c5280c2c2085001d03005661062907145200b8520f00300414056403010041340e69019030505d01c04207000c4800c2c007010101c0d0550142500640303c2030810650380b10403117034076614020210115010b220010040c0305102080c80301c0b1070400c480d0300c01c244240f602e13100052038681441d00200c0000d0b0481001700161901080705020200084c0060240c40d121400d200c0e4454000034900b41c011551284001040b41d1158125002118840181c07034484441341e00e940c0c007800b034005054072030310f0040c1d8002c034080f8089011520034120060040c90035548110500005440040039000d065a42da240c0c6d00f00d9031802c1c061948644401d654041d64800c5000001d0325050182164a0071a0703d00f0341040303c0f50315803000710f600c007100c16895442c1180c0c0d2072400341d00522400c40c0045450410307140c0002e400b40224074018410f4401c40e400c1c00301c1d82c0c40700021201402030011000c001d40803401034100e18200003400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 967231330 1250 967230080 967230107
    0x3021f02041a0f07082d0d1d0703020f010507060f050f0105010206011d100e0f010521060103060e0a02121609050c090d020103150e0f011d0c0d090f03020a03090905090d 74
    0xc4880c03c1402172504c2c0e24100f10303050000c06e030300b400940c4070a550105c2c03094881d1055821000e844145401040070350340c0c8004e01000b8000c200782410600385d40e008009880d8481d500076803c0c46100b42903400b60002c4e00c1d00750380c000c803155080c074000b01b40307903001282040c140c03051000309120b54403c1e125041039007500a400e02d40407140c3e000021034241c0c001d01d8114410041c040010b07260794904001c5c000003241c8071001d070b161144240000c170300c2110007003403290440b90040c6010803103010780403a0b203041640c0141c00075400480d89409000100300415907410784850042c542030300b590b0b00d130124001c2c0c0d20100c680003141170041211001601d880ca0510302c2590040c500040d11444c000c2c10f84c48030700400e4200311000c2e40880100400f07800c0c2c000e0014090b041d810f0920550842141265522140242c402081c4410100e404c00182c2c0095010303172442038110300660f102c0b12450a0194a0f07550502c01a4001804080049007503401806031900a401c480010280e00c50440000c990095200b10b0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 967232580 1250 967231330 967231357
    0x30f0507080403120e01110a020108041106040f0305010c0206010321020f0f011d0312010506071110030f1514060a050d09080405180705030a020703021f02041a0f0708 73
    0x1260101d01d610015002075441920100459280d42c000a84032148825500b070421000c80118000404041824400d076907081c200681c039902c440c50700b4001d064120480070b400c000e01280008441210030f94400880e4001c03030082100c40c9548008903240c4078240030240540b0801c1c00c503140144115010000749019a10654458819044142c1c0c10000c1c0a035900c00541e46070342d00c840855239403450460408603c240154034140e01c21089141c0d180d01449481c1c400c1501107100f905210b120f0748040c41d9030200410342c1c036500c0310340d45014005240b81600d20b11640c2c50714a00100f2854003103c0401500e080c0c411050498401004100a41c0d0001c5982003c1020034862111002007901500811a01c0340d0800c4d604c65013030400741b01800300342c5070381000720184000074001031340d410501305d80d0802c171502000350b43d030342003403d00340e1409803410b04400701c001ca00b512013456464503501078000e492150410b141400711020342c010b01c40c0584a040014a4820490680059190300090002000701c0b070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 967233830 1250 967232580 967232587
    0x603071106010602010e0d090e070521040b010e090a1505190614040e06190c050f03070801090c0c1e03030608100608010b061810091e0503010e06060607030f05 70
    0x1140340c01c203002039000c8005070303441e00c1601e038455a0504c04803503c0c2c1c40700d280c6050b000e4940003124400801c050581d00900c440002d00300c9001c8003440b69110800034003840040e46040c240707046003a4840c24498440d80c5035254010804590011800c03810168102e10041080701c003280faa40c0003410054541800340f0005e21040784100d4150003180f00800e020000003020b0703c2900148410342e40e020b002c640941d0040010402c5065030781c0c4c1403022180a0135000a4480e100c0c150953f41031054420300c011103c408001c100d1a5980600c00c4d505841c0000c00510446144510955081c0381511300203003242a4040c03420000103030015100c042da070003880d010840035a29400c01c0e060002400c01d401c4400e0300d844042c41a4003090041c0c01558205a6909241c0100510100504071421079164482d030104814140000d118100140103491000c0b0742103d204660090407991003910300c140d0740294200344481c20a40000324245104410140c4110700e406201d50702101c03070460003000241070280a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 967235080 1250 967233830 967233857
    0x90114042409050a090203060301050c04030b1812190908070602300a0809191101030c0e27160504050d1401050a0501050301052a0a21020a140c0c060307 67
    0x1d81c16013004001c1c82e140180c0e00c1c1045410300d070a48000818940404004010400c006040d003200940d209030180c454001500c08503034801e041a02c2c519400301d1a49011400d406480700c0d418030055442c5090700e030384076403558584001c0c2c3c8400852090001580001c03180442e41c0602000141e250304d0300c0700030f02c02581d034003500010b240e41260301c03078000240c1c03001c1c10814440c40070080202b400d41c01c1c04403076807800520790710042d65401c482c0b401410180c48581c0410040c1c018410350070480e000170500c403c4003075480710301e00f10b451032103d8200c080d62817070000c41c040740400707040c0c0005a12580c1d41c0c1e40c03a241c20502405506101104103d50541a40821958864080c40b50030300075105403001007610b514100c00c050944d00003400c444030440200307070308540010300310b003017a40300d001040d42c0c140d113500d05211706030b48000721f00d0000c0c202d05d000615011119001c0b54000c0180020549030721880032a01c42c45d01c5464024080084c02c0ca07803001d42003035401d15141c005180e02c0000c901c1c0c00805950709 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 967236330 1250 967235080 967235089
    0x40b0a0c0f0f0b0a052703070c03050609100b03071401090902040e04060b010503090a0b0a180c0602161202010c11040f090204050a110412140a03020309011404240905 73
    0x41d0020342e10312000004650400510040c1a900400c003441d060280b410036800591051130401c0d40110342e0810081200400f100500540d072801d80c0104224100a50320b0600340d03180e0384122101c00144c002d000100c1801d541c0c51092416242e4003030300901605092401c201500c41e9040d91042c14020349140019038040180000c001402450718000c040d424030b40707421010340e40d090850905100d018020003000c4d00c0c1c00901c58650540204d2a01290303111124210000c00180c16550b0800c0240703092641804508904d0800319100c0303500b180c00380c550311009a191200341340038a01c4031100074103910001d50b00c40c00c03400044030301030b40002840d4010352001504070780030012080401501c80018034251301d014411903034015030f0490188901e140080e0556524804c5004012030b10b003e03450000240960070084008040d2100c1c121a031082c3c0318103000e0344d2500240401070010b001c1e201c60841780b00700003083e1030449440c4102042c80f6031412202441606031802d540c001c001c1c04a1002034140e59 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 967237580 1250 967236330 967236353
    0xe03071e0615080a0312020408060f0406180302031b0a121110020304052406010c020d0503040e0c040e06061c0b0409020604121a0105090f0703140403030c020c0312040b0a0c 76
    0xf100100843c510074500a40000010503091018a10500c000c0044400c045000c0342d21640c0307050300000035078940c17810f04024540941c80308840c201d2108214105a0000020444914500012030710b840a44650301c0c5d40b038a4540004080680c0741200c1c0c0d04080c001c0350000e0120110700250b80320381d01ca071508a4100c1c0c00032601035505500c07080c44080036215120340740c1c0c111055414190380c036242c100000381c007140c2041d00003401750398548401400d02c00d091003078602820040500600606283d01c3c1060280c01600440000e151070001098407403800000b1540c0101e2049130b500d188071460307104140140940340600d41c2117130716103852200507a6840c000340094030101c4444d03070b2000c08030f003089406030b0001300342d0b46000400c00d40188210703541d070892306e079000314408000b4160f41c0d5840c3d01100500030102444030060000340c2400109078154108002055595007214806100c090401d0781d180c0040e952141350543c01c000601c48611003100415144d00d60341000340030842203640c1e8008440e07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 967238830 1250 967237580 967237589
    0x901030c1a0c15010519152d05120f011206091b0803030a0e010e0c04051b041436060105040b0d0f05100e060402160b0f06040e03071e0615 61
    0xd001c03030f00520083c43c0c8142d1454001480003040440c1030300f84200c8038640080c0c82130b160300f400200b5800742c0100d0480070030321170104205000e1184030318410401400503044540d104d8240c545c040000b03400c05888000580c12200303e51401c0c4100c410540326140149607030101500e01076401da046000e002450030015005202400044d076980c503000140400300d41004030f5600482c0d04042c0b00300c104c0800041d1700c038810501118005526100d0a0141c0d84c40300c0c00c65494108031501040001c1e4420310007070500900e4030155002c1c080c0383d8580c9074490b01013902c0c41d5506940d62000d28252002002074011991100c0d06042c000c2c40c180c0c4800218003560060846203030110b803540494a07680c20386000ba1a0001500d0904115440c2041503d1804e10402441140140d501151510301d890096160110f180d80148034400182803100c18040c46040440f4141d01540c02c140ca5000c80e40e100000b1100c0881d004264140a1801100e503404100d52001c0f06441241d21002580c100e110505059001003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 967240080 1250 967238830 967238863
    0x231f1b05030c0c01020c01030e06010b2101080a0c0b03010b030a0c09081f0c140d020d09020d030e18102c090d0206060105180402030603011e0213050901030c1a0c 71
    0xc18500740024507000c080c001b245d0416080118440780b40c00700045072415502102102a01c404111000c0300c02d07075602e036886408002e000000000e80b04404078496004a01803030b41407280e01d48039409907119110a1154818102007040005d80780c0001d40c0c030072011040545013828035242e5402016141460071000c0e818180304a400300d100c031a420344680c00c0c4012813030078064a1807190010761304043c09040000d8003699000104204012081c0d0710203d05036a00401080010302039090050801140f004458010300711030f03840800141480841e035200e58140100c0c84016400c1292500034900c0411000c010742c011180f10b03d1044840a40a41c803401c168401003500c244503c1c0000e01d0114041c00c40c90503c03800300080e68403282e151442142507c400c1c3ca0240c0c2d80e40b100380101c0e0040c20080704d00c588864060000d113441c0451600240800000044a510500c1d00c1d0400c0008040d020300c4000e0451102c0001084105e1484540c80000030140c21038604000300d015010741460a40025009036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 967241330 1250 967240080 967240093
    0x5030609130c0b031509090d0c12020c1c03031524051c050921040530060108010e0106080d260408070204180b0601140c0304231f1b05030c 61
    0x86d0500c41c0845a0103c6018010007801c411054043c00f058040d1901405505101c08003410130350080015099070140030b030414514082800310140d00c100814000c400181c201080511a04c2d03440c4190010b6908450540b8110401d0041188102800345007003004c2c81400e0042075045051400401c00702503031018040703950b10b01003a01c81d05010b0724609250a03014001d030406c1e0640c40b40d0040d903041e250251061618520321200102c052888014548194441286401c02004010a199040710019002401421401075903039090b10001e000c1c8684952040c41964200c62140c010044002c26410f400e403004a2032099240810804480c190307859080040d080c002c600305481040c0b8140380240c000d82d85510240c0d110408240301524060410028684800399034a0b20421038031032090440840c0d580f03d40c1d803e4941321010705011924042c000907080000f02e4100120303104214039101c407544901c210504400c3d14a00100c001546c0301c846400300c80d600007001000204451001f45008042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 967242580 1250 967241330 967241371
    0x110c0d0c03031115041b0816030b06030d020a0809012d080a060e13171303120201020c0d080a091709120d0e0f06190512010605030609130c0b03 63
    0x30f0020441d160075554003c01040d500c0d00c0074440c1454106600080615144103810207050343c0c803e481d008a0810b02071071241c5582000720b4800d41d0201c0b480350354980359030754482007010b8075034800e10103200c056001204004000743c2d1543c0140403002d4141024100751203400c840500102921441001c80c0d001044040042e5420107005540800481014024282403180e002043c1c8130103020900c100d140300d1107401c1000000e2011041c0c0c410100d485940b1000c88514552000d6260712041d1103400f03005c1c0d0100c1d04144180200c684064445004060b000e0080c80201d03281030b002002c46a18a40e1a886100010005844134010340311503802a604e0f10a8801000400c041d010a8105c1540c4010204001150006286a1b003648120761340305291440c0030200310755103d80040e5200c9030842c01441c1078030703a4000d0b01400c142942d440c002506c2c0c1e0f8031903c003030f10300d880309460080d840801c000000e08500c400569401c0c26500c125551501151355900400c00c940040e199400e14408041c000103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 967243830 1250 967242580 967242587
    0xa0b010e0103110603070504050f0a0314030702210303130c0b03070302120612070603092a0303020d081005100201020c1b010e030c0d060b1801120308060d030f110c0d0c0303 76
    0x50b200b030200c800c4d034038500f08001d001c0c241e4861031195501480700d1440c00170701d6540d1a4100030040d074200c50885103081c10481c1260303ca03030100320101d01c00d000f103510303c0b5280d104a904c4507075040786c440000c510790389407a022441078030312844040f5140d031040d040200f5080000c2c800b550003008a514090388604150f9452055084024256030040c2815102c10030280b2000850200f115418100024081142e0a045211854821440345000160b0043c042078403110a810407c40f80240c0c20b0f110001076191003115240d4060311303800104c0307845000c00e000d103203080c03101039101c10840d00005141c00040d8034018102000c135083e010031801810781030399142d600301c004220705950840184c81980d020500280980d6020040500100d0fa2211b00800a03100c50001c0c9101e1207840003110065a900c0f03280142080503003800f18001340303c441c089081420607003114818143c0c9501c41c0c440c41d4414040481d44d40120f40c204841038401c41e00741001c80d8440c1006181035900620f840643c09040d4100038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 967245080 1250 967243830 967243853
    0x2815140607050d1d0f010c171b0f010c1106161e0804020f180a050a06210309170d08040618030512150102212104020906030708030904020c0a0b010e0103 67
    0x103174015050310f00d10b0384151b039002c2404010780b81e02002d01c0b403a0040c402008070341030141c10405c100c0002c0c1030b448041d000300000740c500e081d0341c200300003030008520303040088402c0b000040503c10940e11000114080312540d0444071b4090301107151009904111301100000d24030b40d0f84400001c01c0c609011710041d401d01c01440f1141040a8558a082d18160806107008150003003100c0c50041d0741d5404500d6107c60b036046030009119a16802113041203480b05069004141c0d80300710049003030031000003582e50650a008544004520243c90000b070610010b551185c8000c104840203555906010810090008078440c039901030768940d80c42340f60101c24030096803805807030b07101d4680108170042140c0c2c3e03000410000c1c0302c540201c010850103801da16901c0c03a005800006158500614142c038075484034964680c46a402201c50790482d444280c103150701c50605001d5400c254104100030300050401ea0002e00c1c2d01c41e240b10403150000f086440b03008001100b80c01006d203400f07980f0010002d1150b01d0310030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 967246330 1250 967245080 967245137
    0xa060503160e060f220501090b0a18090c120203160e010605070f05061915030c09090f12020a0b101d090f062815140607050d 55
    0x500060307103590401241c0480c644a04880c0554020001d01d180d1202071103602c110320094081c0701a107410f1710500015444d08005841c2280c98480002603036160b50142c0c042c00ca8000c0e128012107424003a10042c0c0b01010800460915100c0c6c140a0019105942c840d000307080d03080440e000d520b154030405081441c01c1d80d500d200c0c510411014000a10b001e8040740c1142d0007418070f0340d9900c4062400e0008a818040090964081c0d08100030349d0440b1a404908201a146410010b10031040380410b01d800303290001070f010254030103003400300d8040c1d540000c0115005540182c00c0fa41150745000240c10860003000043e0004a0440100f1000070340040e046000300c006849128207110540e52171003010008007088980803800310700d101c0c40031311013010300310200402c0e40e086241040c0c0004000d13600304e038480b11188410309101c481ca0744611842d0100703501a14041c404500e030991043c0180703604442280d2110003000360038000303070080042240c0b00b4100d072180221803040708054020040006e64 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 967247580 1250 967246330 967246333
    0xc07050709230c190c05191218090f02160c051212070206071e121202090a03060207031e030b03010b0402210405120703050c0c03030a0c060b060d050a050a060503 71
    0xa0280107004a000d943d21405503000c00b40c06005030310011106030071001c174050094018442a4643e40010f0b84124420b240a200c1c2c640c0b1181e500c00003200c1624040b0211a40c4c4891003170180103118064106140000a1120240c02c0000281200403c824446000c5644100c0c0420401c814207200140985000202c0090072624140444d83d40d07281c403070a50f00a00c92000010001c0401140c07490101120032600117032420703000341d4a0440c61080c1c004981070042000108003d584101d18001c5400c00c150103084c001006142d80d903214084d4001c18002c806100b001011480300c201c1111000d40c404402e0b650100d42880503005144c2101d909240c03041c080c0c1d004001c200e1000382c2e50701a949919040700c5510a1319951403e0850030a0341380000c5000700440041c401052680c048003804401800900b65000c3c800c0035410543d9a1090001e503502044441495038080707004e9030303c040c0000d40082c1c40b543c40c0040c141802d108035941240c0701142070b03540320207000f032105c558441c130005040b0590 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 967248830 1250 967247580 967247651
    0xf0f0f05040b060a03020d06030b1e0a2913140a0e01051005090a0f060b090a0f0503120307030e01090c18050402240c060907061803020d06050c07050709 67
    0x101180c041e200b5100131205241c0c000503425911001d03584090300039504454251024246100d0881400303135001d070004048401c01011a2403160036106400008100c1c3c5508a00e903250b044151059880a00d05d165000610740040429840f250060050440c1f5400c1c60000c2da1500b03031001c00464040b4841c20a4507032401e4208010314246103500401da41d02183c01551694402006001070032880e145d02c2031260030705000180681c50600178015010084030150741c071a0700c0350b20000b5a0400b62150340e40c1a400550300004054040000b10342028203403901141172203c409540342911003070700d03046070b242d129000d0400a81c4804040c1418507044203205105905254000850034105e08001a80740c00d500d61104001c000d9007000c44200160080580c5c2c810700e8418040c07601c802c1144201004154081c10800c3d03499540000030b02a01c0c0e0003001d49101241e1034440c60000d10b0020402810706104114180108804001241c0103196104001c160414626880301c40401b404155910013801d15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 967250080 1250 967248830 967248851
    0x20304060e0706140a110f01090602250b010b0c0a0b04051f0506090601050d0603020a0f0e0c160b100e13030f020a02010923090a0f0b0619180f0f0f0504 67
    0xd003182c1c0e8414691030203031420851095140c7c1405a50000c1541e507619140c5590304005e01d540140519008803440d010b482a96480614294075242c1d1000b00724081c04c900600a0000c00006444001155411a41590020fa039611031100040e6000e982c95445001d800e003d050301620140781060307202e0001d02550406102007144a00f024060f0b5040c010081103e44051410f64045401190024102c9001c1983c2c3c42100001034280d000740e4000c3d066041c0001e041010f614119201e40010348843c50b0450940d46884127110005081d04a074030b80c1c0c100d000106c02081211450207032040e001c0312203c210003072801606002404005406541040f103401c0e0260380c118082d08211802c001c0410309540100b80c40d01e4501d00c2a888440c2d0010800b0700380030b54000b041c2c0c0820031100c1d42c1c440400c51681e03403600700103607401801328031107010a2001141200f83c2c80744c0c6c40b0721001d4025060300100692100500f800202490700703c8442404001004c0000c1c080c0c062040c0000c2905840420105121 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 967251330 1250 967250080 967250117
    0x207140d050a03120e2a03030901140706060f0e09060f10050d08250507080307020a121a090c150310231c060b12030901030906020c01020304060e0706 66
    0xc03071000f07400e0109403c45540108003640101003030f4107031310342510742038018081d606560300c0344105500e0704517511101422140c10000211b03092164161600c51605403c50078104440e4080d4100b25406900d90100045804041000742e015043d030f0160203000b8507180181030300d40540104031080e151100e01c04d1001c00b28040711020f043d24401d45405c08075090328104020f1a1003646034503200c00d07201c602e20009003c0c00e00b10051441d481a010750361841c0d41c0341401d5aa07030055500181d1f010b03880040411007242c808124821141c41210308040d08500448260400c980840d2000066008481c0071102468184216149021103202641c19814250f103d440c50072998084d4030781c0c0c089040c00c20712a081c005070311312821600090007070340c40c0a10810400903039a0301103030441c0d2050600152105500d8100801e45200700c0d81c00007103080003e031400450141c42400c0b42504c00590800c40704001000c280021031185d4090710001c64100450000039151103560b6110004102e0800411010280c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 967252580 1250 967251330 967251343
    0x24030210050a0c0c0303170106081b0a02010f060906080d0908120307212a020a030f09171b01020624011403040b0603010e01062d150207140d05 63
    0x6150072074590120036000d40c2c40d408148009032008841e400c0020400d684040d485481c1c0041ca1001211030f41e8170081030310000030540351081072070559140408825450300c05048401c19901c00800c82c10600c40543c0200d440e02d4124420842d1508002e00030001c04021030b01010900e4038040c480e0074940b4510380c0e26a2251014500741010000100d003c480c450100c0f8040040e40c468155000c081d1904208002c00c1d0708005c00040c0d52082c503c1035400746c03190118406816903600130309206040d80e50222044026051507209014026401280501011031482c0304100d10000425102d4000e0303c0600b20103108211650441d40940c0800074132a41b845125000c0d240030b48000c50070905200c2c0180e820b6440341001e15031042e804010401800b524001c018060803054008000d44185041160301380d54842c000e400016028549641114000303c10007030720141c81402540c0c40c1511000b001410340d500b45004001640b00300400d00c801d01e52109007a1882100320f5a40041210340c0d0f0754280c40c1c4a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 967253830 1250 967252580 967252609
    0x50f0c0601060219150b0a051e0301061202060a030c050c070b0c060f040201090e0603010908211005010c0b27030a0311040f0b0307020a1e11090c04170703080d240302 73
    0x746c5440424850741c03140202c1d00050140180959041180000070300b40c0f500c0c1c2d4500b03070b511942c02e1200c0061401000035600d5011038026084038a0300b080e0600035400b034005681c411041003410020210542c10500000300a0324102c02900d65894202c04a1458114040e003c05a442401c0e024000141c3c0c206410700c04071141c0f1141d14100e50340e0400040d00410385403802804101001900003c2140c00300c0e8142885803200040c2c04054407485000c0e09480d0a42c0103a501042c0c46410540200b12a0003006034400d03204c42450400d0842000c0e58040104110000340d890ba00c0407803c403c2268146c002c100740401416101c03420545840f8119984604510800c0b450020000115002905c01d0115040c0303071341c002056908034418a640e64089405c44002626404c130800302441e07281c036101d049030380504205d051302c50409081841c500304c0c6086c98104d4149038800d01030000002000e440c00f80c40c804d00c9021000502c0003006201e40c0501d0301504002101940c0ca580c24001a51207144808068 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 967255080 1250 967253830 967253873
    0x20a080705210f010603031115092a18070f080c0a0f05090909061e04110415091b0f0315210b160215070c12050f0c0601060219 56
    0x30b0410006424900c0030030a4440ea542000004010b1641001505099007030304d004407490803203c05c0c070f00506003900f5251007039960010099241d2000fa032240d03800001c80d08210000c0048600c8002921010701d000c040703031a200c0550100315036a40c104c0710100e02c03c01d0505002c0c0c160315214405080030b1141b10038030703424042295a402d030828450019074803000406405442c046c20800740260380c1e48070850740c1c0c0e17034201007220750744c0b1000e40203049050003280d0241d070508088d407401c41004003511390343c500c0d404c0e548421034000440b4170190042c000d420240011005c0c1944000703100820003003c03d1000b1061600302203000f00d25803c10001c00c0122488201500035403901d1800030305070b041d50f4140c044e10a4680380d05200b07a034000d245055091220513000c540b01c01422600c005442c95045440a000c1040a9485c6010030361001c00c0780c00203000382c0b401d40e14000b07100304800d0040e041041d0300e02881c0d102c100144404c6404000c141d658002440c502c28890110341d54440c2c1058031201d404124 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 967256330 1250 967255080 967255129
    0x9100b040b130e040303090209010f050f06031e0709050117010323010f020a0201060e15030307030c02060f0304050c0315150f13020c100609090201080619081603020a080705 76
    0x1800d004074682e01a0980400b07182003070401c0c0c20024080c0060b03c9042e0b2180c00e49500000740c0303611120380c080490704060403801710381080504201150f003005040b440041c0070040100d8403564103d092078440e5001c1c1d103600d006541464001080c02e1500c0c2c0d0b000700185010b500500109a09443d201c40d049030380c601042c03005d140c000465000d420a00201220203002042c144c00064041d007001058401e02200ea21144e40c0e01c0380c2d41604101c110304030741d400d50410003480c804640714424502c50b40d40003401c602d1030091003035031000b101d50003200c0c180d8894008610540c014603043c85211082042d2a07041412070410032038036800126007940b203a00c02c052026881005448846500002c0296023030210340341c09811094541380d85082004410980c940b904c0854888200e10500701c1c1e00b5010f035150505507480405101020060309080900841c00300c0c0b0004217450104607210180402d072095030001440c510601610701075a4008410075080b1003000d00050300c235100a4050244441e0754500d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 967257580 1250 967256330 967256347
    0x250306030206041508060603162a060209030f1216051507030b0a060504030c05011b12050a1425081b010203192003151e09100b040b 58
    0x401a5038002500900042000160219501c10710319020340c032500c1d0400b8658038102004040e20044079070442410300384c01da000f68071344100c03a160841312011050045616010707480c40300006040508413140754000446510740d0078244213001d000d1031080005c207050429690912040d02821070780c824105400d00264043c800108aa410f000c204031400361580c0c202140e000300640310404115004105034200010311b50701c0744003254101c0ba000001200d002d42401d00444800d1001e0070502e5090b54048198804209543c643c5880c3e406c16444203a0356461601c0301034181c5411000086000d0402c2c41400302500c3c41800075200705105a1001c200000343c1d02d015181c6015194400c4c6414161850081c419181507000350b008152220b081c3c070584040803032083c04d0710380e071840a0b980a030242110050003000170002c4e68118411140c10804c4c001c070180441d80d0341607030005030500d0011000b4210710328100282a0f07a00125a038078040380f46401c3c4040b100013886076118480c0e121000148106 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 967258830 1250 967257580 967257587
    0x140f090a0b04050c070203070503030705101505030318090105180a022109011a04110a030b1f051b01050c12062707021006350a080c010b030625 63
    0x450307880014810009410321302c981100b10b400505049000c3c0c80345e05004641468000152903003503510030001c00340080703445036210207001032224441c0300240100d000320b902d40d000c2c4080c0982506045414000505000030030100c1401a4441401540891640280d10b0b01401c40f050740700a06a2000d0381d113041d1041d10064000b000300c100000c0007010000e02504500c1074000f03100b03130181480c242c0541e5403603004000031540403a14030f0090100400180710228042c2e0040d01c0c00729001001e420044102c0c1001c0e0741c00c29005101036001903000500381c1c03c0107501c08510502003040b803000b008285030100d400f00d114882c0e0412100418a0080052404c0d9101d070700405200c41c4c070900304440a010100000c12508060796001c0160041c6400e00c20b1020b240e02c2141e00b16840c10320131180c0f0170041412126054415901c0041900b190740994030b00340f00400c11054458030403040296204443c04d200b1382141c0044c1c00d100d10136009007061043c0300b00303005010055618a4182c0440c09803242e00b05a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 967260080 1250 967258830 967258841
    0x302011b140a0512030c0306010c0c05060c0d09120209040b130c03030903120e0109050f011413150c03080106050309100603030216140a17120f13140f090a 68
    0x14440c20010030301c0c851101000c60b4881c4100d00c5101221121245800c0c01c40650004866800700020240b00151f46907215400b40b201c0340740100107814075aa02d860101d0f030700d0741c81001d002055500050360500c02d40e038007440c200010158440301c4001da00481e03000030441c100c0500b014081d0403040d00400c0e4141d4a251811080960084207001c503281d07203240140901aa511050f103000b404904e02d403034914014a850352200f10705940e4100300a081904004003402d12500841c100181d4504940428107107100410310000044a081d0040b46000d00c40c1c04070080c3c0c200210b08100800c03a400340000d8000800b1810b681203414415181d60300c0c0d111080c9007000c141444281c0c1402c0800010525401140c80450540000d2060140c1c6841d0324a02c0500d030a00520715801104020040004050904500803649008800d4540d6201d00e10b02d640d01d2a0001c1001980072440002e121103201e0a012807540189850705100c20900c14035400910342d070710205032407805040d8020005d0090b452540c8039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 967261330 1250 967260080 967260083
    0xc07140a14060f04080c09060103050603070306270501090b0702030c06060607080f0a0e011112040302060a02030c0f060a05070801060c030e010e041e05100b1b07050d03030f050a050c040302011b 85
    0x25888550314142c03a5901c0180740111b902030542c1402203140e55110703008180c80f525018000b410902d1855603003000503c4801120004c000c03441c161803071100030804807284214010310000c180d41580b03040c40d030036210000c1d000c2c030b0075544100002000c240d0041030036588480c040740c0d8075803640306a09144c0d4036489409419a0000c0e0000340042d001c503041101a20b601c81c080e40d849851101c01c0d040c4550b504003007403103102c9100301130004000603d4200000e0600591506c1540d05001c4003aa40c81e14101c0d480d0a07a4030907030060780400c41c0b01c0103103120301c6030302c006c01349011201035243c000064400c0c010610080c1c10050380c10181c14071640140f808174883d560290040010090b04030300840036406c86110b1b011038030305006c0886d40d072840c0580c0c0d03401030300e840c8240b81c0d16014800040080041c0c521440039817a001e01440001c0640d540100b003c40d407406514003003041d50f0400f80d00d408844004100f038081c14540800d00000c44680c005407801d51b42c2c28201a900720344030b8003404a159010307040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 967262580 1250 967261330 967261357
    0x1050106050a0f0804030207050d1203050a15180b040c1e020606010e090414060106090801141e091f050406053909100f020d05040302010e0d0204090204110c07140a1406 74
    0x9030b0000300000c211410b4030a4224ce6000c210b0341c1c4078101e2039020348150404078240329013040c20606c5041d50038800ca24041003441400100c901c1010049000e0f44c61038000303c4045034203500c40c600c2d8000f030395845202c0c1c015a4400b5000703525180300043c0c04121a20211030041c0403540014042080d007003030600d41d0f000070f1070481c0c181d90303500d92006000100328018413040d5400c001812011202089201340078088502c10200b50815103100a00808001420040144260036001303034901d09492600b80c0114444201003090324040c20150250b510290044062084130031400b001d0003d800e0b01d015480441c3d40303000032000248080902c1d031b80901084154005004881205203039040300780e40c007a4080030340a5401c41c0f404540c0903201400385200c041e003c41d00b0f04500c140c0d1031a00b183c004881d43d1004000240350717421078000c034080300e007850b4106154490005540b021130400b040780c0d200074150845420044600305010523180056445084a0f0112030303540382c1c00c00c2ea83e500c1a00d40c5100e076481c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 967263830 1250 967262580 967262599
    0x2c15040e1005011d0f0a11070b0c041a090108070e030a2021030405060a0302070615031401180b07030605121b0915120c060f030901050106050a0f080403020705 70
    0x1c0c0100140802c0c81154000e06265104e480300715034945441c0e104041c02807558040c0d580d20060f8602074600b030204032080000401a900000c1c00401009006904c041501500c4605000640c02000781c000c401403246034061100c03050aa0b400035555501458526100803240b8a502c086803500700300305001440c402440072011031000b40c042200700c20b00b4088035020480300d88000c040d401c9410120358505280c00801043c825805c0c098010420503480d440d0041c03030075050b034039040c04482c20407801241c2128050800c1050103540460305168110000c001c1000301a544024803121890341e10040140345030000268101d8060340c400310040002a16104040c0d40340b002090b01d030343d180010307545031070b810000041a5040070030b94184140b40114200381d404c54030000f00b110024119080d10301c18403c0007030100468903048040c10a140740001416120308001040c142500c9050300000b08200c01401050789a96010301702e5080c209030380c1005901034407a82002c0381081d2841c0c000740d81010001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 967265080 1250 967263830 967263853
    0xb060f04110a120c1107030803270c010f0203130303031515080405010507021203070c0c09110405040b043e030c0702100806010f031a12072c15040e 65
    0x5496046a01003112040044d00b160030002d45404038071800c4003059500050003030000a03030f08801150018043c440c1004a4451040d00e0a20760b000410786007619040980c12044c156007007405c80361050254006581800c2e01c42c01001c0203040780d80700c05020946c4178071a04400082c00302482001e40111100e000342440c454402419100c01520222100d41c80d040000d00d400c0c0c03011411010500e186100240342da15248811180c4102e4001e0560315400445400281c0400390301c0381807008a41c480d0003588561400041000307c2d01d43c0e00400b409141007045001c0071000e1021a990184c20754902450071b510000d41030035803421b684e40310211500700001444800c3c40200d010700541d40c82142e140300e1001d6210802c440a2209a903410f021aa4102034a07030024065000b0f188520006c00c050b0400761810400282c2000c0f4200c6030007044e42014006111002e08900302101e407001c0c9015003a010541d000701c0c088c0104000744207240e10700002860700e07143d560340e03000106c6003541c01007210300750703000d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 967266187 1107 967265080 967265087
    0x60103020f132c010b03061b0f04030b041101050702630424020d02070b0f15030307020d050705031222030b060f04110a 53
    0x2802c101d8000320b000b41c800c2d0303900302e440483c1c4419030034440d1152003032043d110065181140d0500182d15010f03207000554540060181a0940071212454906940d41c01580034011030840c0001e000810b12550030006402240138501328880ba0f1500c000554040c491140001d400c40301401007460491056440c50340c01c0b1120303040c00d0344c00300700d541804880c80035000e04039007984008000000c1e111404e0041505006900155200300381090388407400c820704c00039814520034203420346001c07030701a66406842600309108170a54031040f091070400358401c01201c5920342c10021400040c0d02c000c0c1c85c50b002c125a200503024506c1c00026409100c10062411001e642c41e2040c00030005282d102007011180d1000031803091303510f9414042100c00c410f40800c8030001100316500c8240702140860484680200c01254002d8860a2840100340900403800d001003444402064241c80f03141c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 967086330 967266187 := by
  have h0 := BRFrame.cov_init 967086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 967086330 ≤ n) (h2 : n < 967266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
