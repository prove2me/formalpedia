-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0463
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:56:33.397313+00:00
-- url     : https://prove2.me/submissions/ea7a3ebe-ca57-4af9-bb22-2ab6132d26ec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 83093526 ≤ n < 83273382 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 83094776 1250 83093526 83093531
    0x1504080d0f030e30030c040501030c0525110301020a020601080613050c0f120f0304060306060c0f030c02060d0c1206060912030f03021b011506050405061e09150a0f02150c03060103 79
    0x744c000000307500214400d44040c02255111407510380050b055407001d480000c10300006000f07403040c00315074810f12200140403090b082c0403540282040d0826103c0320200b150154000107121449640014100381203c10050446003241ea41e440402c205103c03d58000b4116040420f8000c150715095200b401185c0b0005e00f103003070540500500a1134404002d051007859040803504116040d0144219001003800b404d0400000d00070303a4840d14000304100c2c0007020301c0300f045070040954035050142c1c0e00d1424000d00030000e0350b02c812006041040486600882c180c01d0100200d03202c0e1084d034105085070f9070990a100c0b80c20310355500b500d00c5804c503130746181015400c0c4911003c1d4076800c0e40f40a03516003e400001640c03410034041d4950750109804c90f1051103c208400c000f0b40c1c48242c121079030704003102c1c190004180c1036540007455202e90b26180d54408141c0b007603540c4003003490000341007040e15920303141100d4018200c1a61104800c440c7c43d44010a90b0300065108040c01c0300070b691041051400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 83096026 1250 83094776 83094853
    0x1612020109050c2d12060412080a05070f0518040606020106030606080a03051b0a06050103210207060e06070609060515130612020103050402120604050d12020f0f091504080d0f030e 79
    0x400d8905101245c05540c0d0a08500c102074400f5003200c9c856804c40302e02c1c5024000c42c40e080f0000341004d03c0014007501007090000b80c005583c03141e446804484000104140f00641d500c0100034003a04c1540001d89e42c1510748640007403070b5100040d010444650544915040040301562400004040d100e061128022030f0303110390008020307218090107540300b45d030401900755244004003c0601c0d1070400030190752040000348a0035801505d0b60f000c540d02140c40c01d81d5091146840d0024003841c88006103064108018043c00070006289003498500550b0700e051010307008200d000036203289209450710f045440403020050351080c2c10072a806400508815600b4051143c40c2d840c0200803038040ea01c0350040e21a9070744207030b80100404a05e507488135040d4285494144809074510400402148050300015100503035100c00d0031001d00341c60140325003504c1e42d942d640241c4c1c1b904107a150000c0002c42c00070496a640b8000d10414010003949801441e1444a03c9108030b50804418101108036210028 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 83097276 1250 83096026 83096059
    0x3150b0a030603060c0503061807110627060408090d060e0a110109060c081606060e0a02040503010b100e04052a090f03030703050703051612020109050c2d 68
    0x82020344160350700003034031901d1810314400b00d0312080500f8080100810501465564981a00150710980e9100d0007180d01c40305815a6100401c6210003418042c071010442c00c4960841101c0d2010b4442e105540c4089030404d2080c0c032220104d50080600c002405806d1381d5080a03d50910611f108407800070301a9001200d10340b401d0b8042d20111405403410300580c4e503c0d40c3c007004600c018000c40c180300740000003175955682c45010304031038020024a0a4501428400c05030460b600500001e54201d5607400d0518520010b5445402444e00a60030500400782a0406c03402500c862200d0340c2d9054000b510307000812002d01000b6128200310190701c0c440030ba00700440c2103010034010200c6680e60b0340b80103010901c42c55001030040c5500c250401e0081c4400300760400c04881c1d00a6152030001c2da05e01901e550201940605000900404003a0880301d01041c2c05510000c2082e01407800c07114400455810859810444036900d24100f8285103440c55201c45088000d03a0001c00a1900140ca828440c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 83098526 1250 83097276 83097299
    0xf0c03090c0612040606090b0609061810092301091809020901140a120201080609090708030f18040e0c01110703021f0807020c0f09070507060c0305061905030d0315 72
    0x2c0a14108240c1d4004d020402c00039101c3d20008150b0b12200b030190b10030340c600249550250000b040d014920001c2e800701e03060a4030035040c8828000401c140203000c802c140041040825020310740c0a642407016968003109060a00080c1800503903038040410300b0310f400d003881030790702041c03030499181ca4121490050341c964039100d01038140605c0f680310012a0b40100308080116511000c1e4250b9038580140160743d000003007980c416410703125a40151280410301c1e241010a0707000154501002c1454010600c80700020302c0c042d07100b201009203402d0f0802c00c006c2100c42403d4003c0156010400b80680740d4080d000900c01d402e084826249010358a0300440c2442070b09403040005103540821601c00f01c3d0b0080315082e04580188014000314072002c02081c00d55a00c1d03170390580318408030700001e20310500c554200d84986900038801c6c00654400500580904810744502d0b10030712170031003030500b4441c80103070000403150010000d01010020840030340c000c3c61041d0248450001c0c211000c1041180107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 83099776 1250 83098526 83098537
    0x20d0c020102132102010305040807050105090309011101050f012c15011803080f09060c0307030905010207140102060f0705071703190e0a020f1c06050f0702060f0c03090c06 76
    0x340c00250381c0b01d410140031003101c0f00a41000c0c004400103e500b20f44c0c1114804d64904480d82801d0000701500c036410410540d00900e54010100c8d800c040411481650200140800d0102a2500c91403914528034039401d17210119011914059082d0040041556141c8a0000c070b8000b01c0d0420025510202d400c40520320803144481900c0041940e4561968405a860660800e18103914403140c2141d03528205c40c4101e80c0f03a0b805c0260040383c00142541d5400032640c0d84032444044a546509601e005820030605104107400341c003441000240c8007089880c4040050b905034040d08140e41c600c442c41500e603501406540030408184502c0700000e1801e003000c11241c400f01c107000d0712490b25a0603e90064082e01461000743d00b8001281621b620001d914460117038100d40312040315502d000850300690b42002c4020101c08185440e200b4400c6581c4514051041230a008607690741e08841a03940301750075202c02852241c4030300082e80700382c48003000e0740e005194007058a16007100131002900b2600038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 83101026 1250 83099776 83099801
    0x1031d060103020a060e0904030c050712030314090316060e0c030d0c05011803050f0c0a06060b070c05090c0403020918031b01050610020c010509010e040203010608040312020301030c0b0706020d 85
    0x10014000e40c0340c01201c203401000140361051546c5501008030b480d250000c0e00c000c0030701c0307840d80c0200b08000007409200e000e060124124002110f450500070f000e05568521102e26044003000b040040788084100c9084004507c5400782e0030710b10382d0341d140c0101204034800140e802000b124000c15a001d12101100b8000c0ba600c1441c90f90a50510600f11400b4510707041018100d060520006904542a40c101704040c80f03c4946075006032032554240304540c84018456440d100001c9880800e00e005400c0c002d025040c1032a0b01e5844005100c0c6440e1309482100030341100703100410041c50001d010703035880140c208841d90b00c070016840b00ea141d40c0204500c603507d000c1c40806800d00c0b1100b4854076a00000c101ea1003070b4030b12400380c406900c2d811103d21041c100980010440410b0b4000c040f00605544090000c540e60342e59581d00074252207007514201e0002d090704c450111070705514020b0700d0580f50800c4003000d1191422900b8101544040c108884194007801424130b2482c81c0c0c820307032402108 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 83102276 1250 83101026 83101033
    0x1050c0c1201050603150402010e0904030e0307080d02010c08010e2a28050a0923120c030c0d1a070c020402030406060609050102012702030a0206030705120f06010503060f01031d 78
    0x500134209420300c0b1140b103c0e8419036840408000160303030312402029201d40d056400c0002070711207040c00c8942401c1c40c040b02d9054402c80d0307400690f40600142c1c40410301507a038020001301c141150b0803903010000303201d003070403260018010450102840c3d01045403c00490340c0e80160120340c01700f0300e1580e0002902014000d0341c08400b8030552400f9524121191550700d4841d2901900c0c60780036026800d14050518954490411403260107045603440c10480001842c090400c041c0403561599450b0102c0708500900501c0c1480656042805444c00700c6940089000c0401d111031181d10144040203101404018103d0100300158469100960140740515000f0509a01b030040252403403150707070b1003981168034011420031001c3c204013000d04c0072240050460740000b024000a860700e5092503029500250000c1030207000b40e00400140f05000c2c408079401c10a9884a040d1280e0403030490350540407843c1040006c1091500b9140001c03800c20504001a00c51045502843c0b0300c003800107008004d03070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 83103526 1250 83102276 83102281
    0x10315060503100506040506030f0a06180207170307020304060509010903060501030b060f1504091505060406050d050109090b06010513080319110115063501210c0501050c0c120105 79
    0x710b400101401403c010380e040307032906e8030704000b0440d1403200501d140a80c1d00d00358041040721405800c450001d0450300c0380310b4002d42e07554070403100075403280d001100d05654001400902c80114410791380b144400790007442c102440c15600380c3d081e0b403000450a042264030140440000c18511800703018600800303131060940341c01c2040c40303043c4550b054028071804450318064100d01c600400c44050342d140741c502240010b0080b1101000100a40286500c0900032a000c00c55a6000340035002807a400c41d02032000742d07600e0b0315810441c2c4403e603000d440c1c8041440002c01550051008040c0302c504641d804806035038580e0b0241c01c0d604036a842c0c0c1c20302c0580071615074810354058450083c0d6200c2c400200113241c502125032042c0320340c80c404c101c14088804050761041070203040000711514903403e410a00d140b8038440b8604840c090088565400c2d103101404080d280003a0010a802c0d440008811a1810400155181d0308000b118002c1803003050701403000c035150b50900b0718401111200100c0ca90 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 83104776 1250 83103526 83103541
    0xe031b0d03060b19050403021e0a060804020d060e0c120c04110f040e070203070506130b0901020c1002090310090f0605090a0c09151203090306050c1314010315060503 73
    0x112108030814101800d1420502288205034100c89001c11410300c0340d054020400001c2c0e54030b000366480030350f1022040c0043c01e0840a4445940341e8031100310341d40c5203200d444140075541030070240c034081d41001202c145400058107690000800c00d00c1c120854110130354034400a805c0c8440d001d07203004150006071910308541441c0c000c00c403000241c01d1b5402d00b804142090a401d5008912400c04100c0c808000b05c0c1e0304074000c1c001c46036003980020035201c8902e40b141c448180900d8030541100d8403640b440000350220418422750302144001c20103840811451007091000c2d420442d502d82c0d06001d01c0104070043c0d000c40c441c1d0716515200d41c00c0200c1c44905403c1c04130844000400e084030640040707207154002540381c42040d045e6103541d03c00240700f950040460709424083d400c40882c003246040903000341500312a0320002c480c030940382801641d5482c982402e40780540101e0320101e0031192000e01c4010229a070380300701e000062600248112950013054201921544444c011400c0001840801d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 83106026 1250 83104776 83104783
    0x60a020a1b05060d09030c0b040809130b01050a27090b040b0301021309050a060509090a1403090a12060f051f050102030901052b1a0f0a06020a1202010e031b 69
    0xd952140715861203161401001c50103034811042c00000d066915554581058042c10064082541242410780a4030709444e09100c40d0b40410310072803044040c1035201e0b64014a40c040e1500000040e9201400c05241101c2518042c00f242031644076201c2350424615442140d150b4800280000038010694020310b50920045485801d023940c00ba034010051590030741020703a030001c215480640300103542d95800064030003d10542e0007003503000190381c0a00c5400032002a11442841c0181d044240004003151415624030443c0c01140d046090550100a042e907014214084a4000c0c034022820820201c0f40c03508071481140d210030380e4520024201e28011041070310038082d180a0004510b048070440020f002e0380203a43d0514085000405c0c5600003000f0340040f01040c00072041c081c040d003010307810b00011088029103c03500070f50a228100b84a071070022a450203c074016005003628410b82e440e08c48240e101501d4500656494502c0e140c9050001c00c001d01e40000c5440700080a00c008149180c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 83107276 1250 83106026 83106053
    0x1810140c0109031b03140c030f160605150a0b07081b010507080f010e06040b0112060b041a0708030705070507031b050a14010807050c12030c0c061312120902060a020a 73
    0x20104c24000c0d60009400680d40400000d540a00076116811520200c1c5540700b4240800740f401004107007030318407d010302d1640401c40c1c8a1041440190758041d1180b1038110039921040d44407a025070700700000c00a500c000c0c00707071500a0900601c0d0a0221603414a4801d07d4007020f540c80e0741d104204006d00c5d50207164260400742c0d045a1140f95490320031680034206e40a480b443c415a038812030141c1e241c2c041d0f96038000440c2d0109003800410396441100055030003c0c810829086150440003c1807041c8400315013400760722070041802c0d07441b410310885d0943c0000340100c600b4403032440e002c4080f40000c40c4081c4408509410404500d04060611070403d109601060420241c00490241d9a030040800c540c40111498415110040b40711200d190601d00e101c6600300c880300000b440b81c580c280400401c3d565000c5800c5440540301c8000a030484400c458002c1d1842038070f102007031249441500300d806030030484480881c101425400081007580402910030260748509644d030f0420413803040056 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 83108526 1250 83107276 83107307
    0x303030b100c031815030617030a0822050a0b090c0901120201080702010f062303030a050a08151309030201290103020c1203190e01021810140c010903 66
    0x4107000300c580058440544244020148040042c0c418421520815800020401e480c401d80e00d40e10100409002804a40243d1002080d03003204680d11800000440c1d242c802943c0d1603410541d18125804400c0b042810207182032a083c2100202050007004041e0036140902c07162411170600611251400d03101003100c90242c09604010490808980c0341542d1040d02800d20310001ea854090490040c10107803401208549451004a501d00c0880040c014111011090307441d0000ca1100309030b0b4078001c1d0440c0500060003008040c00c4e03584640412a0001f9140c0781c0c80216140250004180011a0401881041d60340300e21109265090290613210100400751000d0301140346110021040040c86060501d6000214404000010000340e15500080c0b4460364603404c0403c664801401c0000b5092803903401d0031003110a0301018402c0f90368034000d107400034410310b0350101401a00d000000c4118144095559a907085c006844001e20a16179000f00014181c1124038000d010b8011100c100d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 83109776 1250 83108526 83108539
    0xd0f1208061909020a111e06012301050c0102040b040b030613060f0506071401050903070203100b010207090b12060c090a0b0301141207080304060804030e040e0d05030603010902060c070303030b 85
    0x1a203019505440070b2003520540300c0c01580d0f4084000c1c0076114051103d0800c0003e21030365071702070388601a115a107500d0700040c0003074420036681c03108070107d06c05040c80400510301c900e10400c10340350f025100510751801c8a01c00542030580e511302444058115500055a0210010070071001e03140410000c1409100d84a0400c03099040203410aa00c880c540251805801c1c0026218103000003107014184c142c903290020312451500d1900280c503900800d0303089009105040e005010002c040c003c1525801c01a4001c00c0010f2a201c40c6070b001c2d046851320950020a40419a041001c0c2070008520560b186800e1903902d07150001448804256940051500c81c030038001030048100d1000141c864040c1103076001c99041101441c5801c0c10150350125003a0f04c0f0020f8000740c403a8005809031310a50090700e80e24600c0c40400c0a0006a445441a03649150010500a00d1050156018640190700034000040e000c0895010031040d902034480800d05901c6030108208155050150146541050b02ea0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 83111026 1250 83109776 83109799
    0xf08010903140d0609060f05040b010f080c030a110a030501052b141f050709150503040204090809030111070b090307020a090b1c120f1b110d0f120806 66
    0x5140c1c034504200440c0b19400061080e0790700655400540240502070307020002a50740d40d940203903c40051140501490602c2c01c101047d6008120300d924120b030544030201a95214090b4a442c1d910091048034040e07038596240b40d03840c18100191010505c00d480002e00355040034100f00703600040c800bc0304107650400d0103141542100f94000c030710842d0300181c10380a80202c0040b1034105000d42c0d03100306202c2d001081e14002d400240e00464061140d58681c5c003849900d80040c51340c001c5540c046000030035001c00225005081070717484110018002e0300ca0074100003002c00024207540e1080003501d4800804901d560900014500035074000d030346500150720300741099011900c03040c0c540c492000003664403003103060b258651712450001d980c400c4940e814181000d1406040c41c0e040300c031404c80000c03c085105044580030301040c8008013024a032502c03520441c0e80d264000d45c08410141034200d001c400f04c010010b15001d0091008622410980c028460304010003030440744020308162180d44281e50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 83112276 1250 83111026 83111033
    0xf0606020a050606040c050f030c310b04050d02060901020c091006020f0c030604120e03160905180c04020d0e0d030e160b120a09021e030c01050705031206010207080a0b010f080109 79
    0x445008d0741d080f180554481c0d940450055150142c413125040c000e000c81800002c440903a102c41400309854a8004911529108451a5030190f40a070380e41001d4440d11101c054a042806810603c4051040324101c004420110b0403012f8151081e10b1210260070701880059014001240e2003d24079008080c031488036030009036940700180000c0c02ca8100701045500341d610943e0410b494100103012140452041464850100c60074031440042030700d803d0100e5241e07803d1802c66102062204014000146d8030710402009601800780718500981d10b04045403042400e101901550790241c9002400d883d01075495030400e00c800610f07403a60701c5c10364400c1c408440d0030300035100303070300d0810b00706c0665651400204002406548006584000a001d1000280b4192100b582403002c0c1a025a02c1d039038007000054a083c000e03100c008085800134054040140c1440d5900f56020f041441110040c03556643c0d0303142044043c26094032828842401030001c510b00310098801040110000c002c01c1c000741c0ca = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 83113526 1250 83112276 83112287
    0xb0a0303030e2b08100b040806010311040b09040206030a0216080705010c0f0c060903110a05160807030206030103020907360e091b130606020703061505031009060f0606020a050606040c 81
    0x1410759080c07044c0040460990f40b454101d0b90064208144c1e601d503625200c0d0070b1b15503910700921040724640c1c1b4804032804c1601b003d00030504d101c80b01520000c656100c2c3d500304841600b00425101d6120303402e0054000710300520810184590251700d17825501c402c94140305082d10b032040c5964041c4216104844043d82e400040e0b042c4440d0800400540701c502460700701c494081000501002d44503d20b1188140100030604c642c411195080d000702903075503800c0320741e211074444c8030180d8444414001040507003402009181d2000d2549010303051040e442180441420b230508004400200ea800c030501e51804090740c1c4405095810509450f514200c18060ba556206200c08612400407050000460722220300456a5410881090015503140d20000b07503202e480780700540726181016038a50302442100b00c081c00382c84000d00a1300c0a04170040714070000d4000e001c03080f20300b159a10340d0503400b500c06200e00b00c0500220350140c14489802c1c20314a2501c04090900b92240703181100041c14580c004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 83114776 1250 83113526 83113603
    0x809060a081e0603060a02030705070215030a050a0506030304030327030804030c050303090d060209030c03062a07030c021e1302040303030e060702030a0e0604050904080405090c07080307030207060b0a0303030e 92
    0x890f000d0782e21b81c3c9e5400115201d0154440081d0440c000c14003414070240300c41d001d180304850240b420445c03a61680c1c80c8200345c0d60141d0350150960010041030011a11942c00340c030365544100400102a8081c0400e801c1c0b1000541c02960110340104e024020068900161002400114010740c2040d414400045040b20160802400564009520764007174409101000c071081008094036210f24101040000c40304003814020901c8081c1041a41071319011002d450a0720b0301940c500700608244e509200710000c541d003210027190380815100725140d0744e1a2034103452500c03087e0f01607101c502d14640034050320601c0300f8112243c1c1100042048840d070000544603503800c0d45c5003c0d034401e0700c01004110648141c1e001076410490030800c0205115483c40240304544060702c04041d180e9600351000305500403a03c0c000c0203160100085101d05201e900642649401054001900c0c10540e0003c0c3c0400000d0380b0440209032204d840c0030f2001c2003401004c220204407212801d448440140001807032014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 83116026 1250 83114776 83114791
    0x12010203090d050c0a20010f020a0503030408031807091407020312041e06020d09031403010b0a0e0112020d0501030b0109060e0604020c010e0d090f0b04210809060a081e060306 77
    0x4101e2854400007001417101071600b04011051001c0e001c00b20903840e102d036401e59400304a660303003408031651000910304aa95042400ba5080d902d45541c1c10000d076101410f04034032847d2007201c0c104500b0041c000000105a05880000e5005403610b0180c05000010442c4096401c00d008058261401182c0c0c50391156000008030880c0340841c9003884035441d50380020300f14a1002c90b005502142070381c000e50104e40a40c482030520820304002c410f4070300c82401804c240260911407050200d000304813080240d441410800420031401c20454120b0700480c0804016949417401003040c05505c03e80d541c05003540340000c3c0500d50400303ca805d00d000000e00000d000e07650002d030500c4003c00079401680c8908004041e85d407091f50000b0024000340c290300615410744041c410018600810341e0484044418501240b0715064810340c1d80c501c85040103c05a842003000c021006117039948000500c0100090b40340c4509034104105001d001603d08514101c803100900d0502c0725603a1b00280f0300d0741c06041e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 83117276 1250 83116026 83116037
    0x10501080624180406050a120b091905010c0801060908070605070501091a09060f040213090c030203030a050c10060515071707030509030123060f0109150305010512010203090d 77
    0x801c024a03446002442d4050300d41d01000c83c0f0000b0209864510150142044809000d00c0e0744910030810015028442e48408034900c1c016500040c4850a00c540c0c41114203080c0c8a080401404048490079403000807101e03659545080d00007142c02c541c1980c094122071920110150909031240d5485890340030782e809104020075101c0c10007100b5040020520f82c0054104039941204000300318000050350070f40c086001e2200011110382d5014400303482a900148407643e59580034011100074010792038103a5194038803030000700c003680f030410050810300303916518103a03940b88500d40c03241010780f0030000c0e403101c0b0308010701045680c3d100840b6204d41c020141700d803640c0304854a4880e600c3ca1810b150000c04c1400400d0107014036410001804680400764000d00514810300081e4019a20b800c0203500d441491102107130103030824403000b1400c1c3c00e06051598255486140034120a68045020400682c0740e2005220302c0c00e0010080c00d0354200c0d0750013581541480d520103500d518000c0e162608116 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 83118526 1250 83117276 83117299
    0x2150c041703130303170a09030503010306020f0c01140604110f0d020a1b031701060503040f08030604020c010f050105030f070f051009151206050d0f06090302030c12041802030105010806 82
    0x10144101d403401c0312035280300f200c5656a0700c0e0107040e045009180c2d0421442500015503142c44d40e005031080c2039410780d03036946503a00710741d1014000d4005075401c3c1c0041006026260343c1440911400360350b04102e5601c81c0d002d192034010401500c1043d112170103005418021201c2007400d68083d80d5090b1190a00942c94000280b011241400403400c0c0c01c582e80b207800e01c0d00303040c550414010740e0311000108000360240e890350f0703060740c5502c07050794014040b0464000707540106d92040d0203943c1007000200090315102c85e4034030843c00e484000000c0f50030310b655940100a2032404000500801d85030801500340c841c5081d44002c90a2014803034180200c6900250b805058424070246010709150070144401c2d449040c07008107a1000c2d1803c0c3d0144900d04030000c905460308464103461698050402c4d04413521076070360400a405024003c90a41c4000d11601180d0340040c401000440800c1b00402e440d6444c09100445010f540001040b10320310400061003181d07031020405038010000c4e01c14400c1c65 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 83119776 1250 83118526 83118569
    0x3041e0804030c0303031109100309030e04020f09030706031e090c030f0b160504050a030f060e0106080d020c0910050d0f05030c0120040f12050c0a06030c02150c04 72
    0x6111410010900100000c001c81000743c4a030420007564060f42d4200402e0b4160b6800760401c0c49040c503400e0b400a100301c9508021840303608000c41c814420300c0c1c4004d641e003d06000c502643c00090300c0443e201000306000949040030040c02d0003c00320707490107008281e0110000094405100c0032280d1071500d03900c9aa06210101411500841c0e00034040000ea11046c10030090701801078440700124040907400c00d002d83e10541c180c2e002c0d540700420f4901c800f891642d54502500f0f01e4203003120b81c191a0000d032080c0b4002032013a1001058841d01074014510598802400d040034100c400d0300c201c070344005100c094855001110300b0399506444166008242d803d100c0da0302026030000515500c40054000c241001c1034208141191002c1c4040605000700a408103650085001e12a03d0400b070b03900c10081111501c1d14030442d94090300c195145100c80302c010507105d08141d0040c50209480d03c520032406581004082d840700031400040e0101e0818066401192003588654000040880100240d2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 83121026 1250 83119776 83119823
    0x303070f0b0c090d0308010302270712150308030403120e0d030b010302072a0611060f041a1e0f09070618050a0f0816151209020603070305160c080304 66
    0x310780d002021a803041318180340041c80303058240000c0f0300405c43c0040710403503624500324131000200d800d00a04065035980c041116642401403001d0800c0351104040100042c00c040210007560081e40321550300d140908000d01405001000740344120715081542c421420b0105040d42c0c100198900171031701107032520048001e4011902c01400d11a080c0508203810301c0030b11006031080300c0c07000f020b201e41070365044240d0745800c4101e0034444a41103c400209010410b01480364480d2103003000c2c0103109400c0f4680714640304100e958001a02c100c03c080627a1100c0c0c0341810f81c3c4000003c210380d21501d000c081c05d50700c403100340c400c03a01809004134002034002610b800740130180a0182c007900e0000d540d0681429400c44a105210341d60050100c0500d82d40c12010504055424200201c071511145000c02ca600214401c15003212a5692102e5001603072007000850041c002a54080395504210349104140300c0c0001c5c0080910200381da1709800250150f094a90098116a84100384042c13285240700 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 83122276 1250 83121026 83121037
    0x3120609020c0c01020c0f130504020111030a0801061e0516080c01020d0b04051015050c010f050109050a1419020f071218140109031511040b0405010e0303070f0b0c 72
    0x80ca400418000211100050f425042c04400d80c200c4001044160610000c440c0b810030170f9401520740441c41b000070003503402481e006407042c504000d00300302c2d405880341981c005500700783c0002c0c60140100640b80e03000101440300c090084203e421441404c101500301d2090311800d54480401ea20b1410902c5558003c1d100f10200150007555140c40c18202400106203070040580308903d800c01240044200ca8581c1082c4c5803040311603998020010b030150b5450304803545603012592070b8a840c01026415014a60082c45803500c04a4141072a00090707040d501c00191010401c401c840821010840e5250ba0340d0502d04000d000580d44c01c6041d10034021403095141c040d1005d0b410310a2034401c40d038004146d400c0c0190b40007030b0704013058a4401500400100d000910300103540c0d03520a001158242d5042141d107070003090300180c80e50300220840c209812179405401e201001241c200519604000c600d2014070040b4085c3d41341c0100b90b542e65501a041d4200074040252200c002a1200244004c452 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 83123526 1250 83122276 83122289
    0x5010b160b060a05041b230f0d0b0316060f0f090b0c01020d141801050405031806091801050103060b0309070314032116110604060b240703020f0708030403031206 71
    0x220441184501400c03581e541c6c124840040d403440c2c1d460038681c42041080c0103200040040c02d1404508180c032880b960012800c0300b83d600c0d0f031a40d0b500c13134039034081054809408981042e01405c510f420401380a68011010090038081020030070044694072056920684034070508080c0c40e030141080d45802800346107c803000700c6140015040b0079024448125206005020030f08200d02d040d901d01c9400d981c1c081d1130040455000b0321403404100d0541e0b250100c00b200151502e800c8c007096034001582000f0300710280240307000090051100b940c1c14002d94000e00882e07200180346003003a2114a940d6542c9102c09082d10003030303540030180d0603810300484829504000c1090350340202c021032036040310411b0700e10b2a142d1180500b0150707517901486035a00f4400d03444000e0710203030303407a501c400e0054189a16081e5010550310501c0c0190071404140d1400c8602045006482c1c640380d1030007034500b2548130b03072070f240075801800d0800103400c0010899007900d0f49490103202500030340380080003032b2095810a6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 83124776 1250 83123526 83123531
    0x9130c0305100c020f030a050313060f05091006031707020a0b120121050a0222020403140c0301050610030e100e10050c0a0507080708040e07080a05010b160b060a0504 73
    0x30500100186a102c2c00c81041c1040084040c155016607854001e0189501180c000b0b011440140b4003400c040d6511481319074180c10b020610355900b0301102d01e05501d01d004030fa510700070310080134410420742c001010b0481702000805c0c1503480da82c0c0c0130b034203800b460106254006210302c115187c07490300c8030050102e00d0086450700190550161404001d003c0c1011000c50750f031402001014031001282c3d0650400c02900488015070240210180c100124101c80c0710b04103072680c1741d0205440104021402030b04070220240c00e001c051030400c2d51b02074072a842a8104024042103546524500746503082030304001400c1d07441e4285d042d0807c0c08070004034520501d003411919681e200440c038208801c2c006402046980d0b00c605c80380c00d050289030000000079105011410000d100fa80042c28000d0041600a0a1554860000b100c2da42c1c102c0e00c2d40d0002d00300c04144021200310f40543c40c050054840c2d036034100604020403100340c2c0c1c40760070050303c50156500418069112030085002908028109 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 83126026 1250 83124776 83124779
    0x3360218041403030408030c030a0e060903070204060f080607080403090f06081603050f070309030c05030f0405030607030e030702040218030604140c030a020a0302040b010210060807030b130f0209130c 88
    0x32400401411034081c0c0e00d46282070401460000084200c9202c0e41e80304282c1c60a54a500755403010726000200000c46841d6140c0b00684a66001c2180320b10800654000759175800c85481440180c030000d0b801502c8034102e2180a1041c0c000c00f00304e85903c40150f2600f9402c80e035030307410308860a003510390103038191f240d0b04c00d00841c00a90001c01c0501c50701040d0080700c2403066041040301210303000c9910040805442d0003281d030f241d209811110815010f41b034030707100d4040c040e200c141c11903000c1390138140210400102004241000d0180c1e940c01511400c08102c40d001c0030740f04a480b0b110b03100740244600e40c0000c000042c401c0e45914003541c410301030100c4042d4902494204494605503141c14400d2044849080b403514000980e40f8066501901d003079541440e5a0900014010645a40e03065009840d000103030fa015502c140402005050020104180345040c03c400000000c1c11404056203000c0801c2c0225000b1845000842d60540d10103c240c0e444041900c01000f01c01d0004241c1440b8400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 83127276 1250 83126026 83126059
    0xc091203050406031d0d1808151b030403020606130e010207030305060a1509290a0509011701030b1b04091806060b040320060d0c02010f050601033602 66
    0x2c0d005a40280e202046428030784499a614156092401c12482d40034042008000b84100c10a40c10b81d40c0441c14402c00301d880300038490a29400410b2400f5400301034080158040c0022528052404840c090602d9400c0c951802034541c140240011b0294110303446030700d40d250050b0f00c01407103080cae024021900c50209140c02409001c3c203551031031050f040c254003c998502c51954101307804241d1748540c94110728141801d200b07520400c1d5042d08020b140300002e18402c800c0d07002085005101e0743c545030b65502c000d002408160801c1c49891407141010014000100b08040050b0400c009292400541803c040301c000184102e4000030b00c030b141000c04412006030207004201a0b50711441f8240411621910b20b0344081c0250700c4060288603030089007604c19200305030103400209016111600d8422449200c509076880d0f503d4003c0140e5481750340c0360150009200d410f0b001042440d003481121000102410740d0f084a98488240312440c9d040c0240007401144101070b001d5001e006220303032004222 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 83128526 1250 83127276 83127287
    0x7020901060302181509010e06070c0f090f051003020f0a030c090209131107140106030f030f0806010f050405040b0d060e030a081b040621050f100611030702040c091203 74
    0x2150b030110902138010408280c603100810503200b0f110032404500386102200111600c0c2c1e2070800300d50704807104000c0f04000c50340404488010308000b028000c070562421051a040ba00c03212a100d4010740342400340090703a200c03515001c0881c0e03011100f132841908000700080b640103059000511a0b503c686001904403100e402600e034600b0121880700c1880c0008004405461302080707040d0034900200002ca002440070003090003000156000059400d8503907840e42c442401600c02500030031000203003010b0711688140500e83c000020700c0c10600c8a41070340e0010b84071b40514060349100d151a0300481703040c0e880303401002803001c3c1c1241040c044204030409964580e40405214000514491f00080080e4400340d00a0b1403a0600742e44d45144c2440d107042112000d0820000301104a000041d02c80c00c08040c0c0507035801040580c00002032814105011035500c426640140103004055192a6201340301000b82d40c5540c0d0183d40c0400c000e21001401c680041590701311000203400d24241c80c0c1410f40c000e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 83129776 1250 83128526 83128537
    0x1709060a0f1b110f0604030210051f0e071101050c04140105030c0412080c0f07050405070f0503180a0213020304020901090203010302030c12030c1b090c040806010b0f07020901060302 80
    0x34041051500c0e040a500a4491014410300490405144040601e2044800c49030101e10002600c860000500006051a00503a001c0e80180c0c48034035441003148040c030410383c001c2122103041c0f03112160819480800f0344503125207024414030341c000580190240902e46140210140200312910345003c803680c1580103130185094000040400d26055401032080782d02a80140310441d05003860f00c400398289403150700089410324424441d56602e130400300300c0c95602c07521031409442185c0c02d12043c4012035600500d801e0411007181c201da82c109400c04122600210038903800700c0300c00800c00d1414640440381034025048030031201d44c004600c0c01c960146014900c00c0b900101603036030b19054001640020300010394160080755040d0300e1868094104040682004141d80c2006659003070581810301301520407140281c10306407111a40340802100d40d20080d045403003410326080490156968405000d81d5450b650000b900810040003038041d500c3e81c941c010140300c100d60319aa030050103074000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 83131026 1250 83129776 83129791
    0x111504050618060c070203070f03060b09070504060c030c020a03020612091002041818080c0705031c0219030e190918020f040b0406030b01080a1203060509060f01170906 74
    0x5a0000c610407482c140d428011403038011000340110b8a0b02d1086485551000c007089a261141d500006921141d40d09024000c5000e4a00050710091580074844180b00082058007048030801c814072030503401462440d8801e80510b05254561250b03c00700c0d10840c002c0d00040e501007000304242540b000300f10744481c80f0f032502c0d00540c1c4c03000c40340044400c241c0c041d50041081c01b44140c000e0003080001d6500845038501030036401c41d00191355440701891984202410f440f01d03000000140b200b42070400031802c840312003000c8450055a4071200075101d080c12900074a803401082042800c0c144500820045144000c0c0007451049082480100c8045a131140700c448504015400710003120014000042c0e94024104654443e0100c0811005011000a265000303070b89100101c08034a0442800d80038081c890000c3c1902a02400c1548098100c100c0f10005c160814a05201540340c1c8074225070071000c107035009400d00030003100590b01c070720a40c030b80d212242e8420b1080141e4240d0000d0343d140034440 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 83132276 1250 83131026 83131033
    0x30b10080a050604290711161404050705190e01030b01020a0c090e0316080a02060606130b03061309110118060206060f0102010e0a03030504020a090501150309020111150405 76
    0x39200d20081d207550a40740094440e80007100040c012403082e100c500442d860401c1c44a41c00e480340c8400203130081d025a0b480000404401c070003c65602c0400000440a401c03180c28030906241107000c0303020201c2155298002d86e20b40000c5185240543d042d070301841441d2400c09020700721500e004101d44c003d4241580001e01b040383c210713140d50000c1068070541380c100e202c40f81250704044800700500b003d280c901c2102e210030070002c108807910318240c0350218800d100c400d0792900d440400078900b00c0d001d031506100b51020403a5801d1600c4103148002160b111404440d200d0b4cc0e110009002d641d85ca403100314526040130b03110300410200c02445c2020140907240c059201e01000d90b00310303a4500500030380b00964010b00101310549080d5001580ca000c0500c0080382d04259480602d080a0501d2000c4021a40710300038403085140000900d4003070030a03d174041181d9858a0b900380200782c051001d0701c060540e556400001d69105681005910113a5012901d181040080d03881302d0301d0046400756503500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 83133526 1250 83132276 83132279
    0x5060a05040c140d02010e01021204060206040b07020304060207090e030f030411031506030304060c02280603060605090a032901080a02030c04020304020904080f0c0d0f02010b040e030a0e0a0b04030b10 88
    0xf912901d603145900014090300791460450b03005444900004607a41d06506c180180c0d4280d81c58039000500c0a421b280e0b026140b2420140f40040d880740c0054002815904184024001c030b0b903000a6038006ca230981000803904c4218458410b003140b0400d0005807141c040003041009000d00f00c401e01024813015030446011040c8002c4071840e03680d040d503281e0341c590400c1000700011780c0709520440ea4240020718280551000000c43e6221400308400144070400013101000b001d601881400c00400b030b81e00b0702c80e2400038080c0000d0b03103038409404014940110602200040c43d40d070802a255503d29000c500102d5846070390140e550f00b45a8001c0744244500e01280c205410240280d9000381da01800c040c40c0e940300c075611a42d42da0840b03468040c2d0884140600c0700241d41c10001d4800c215025241e0100c02c0408240007800d5820180744139000711b04240800c41001000030031a02c4221440c9840b00141240b2000201092010703488000315a00c00700780401440200c0060b98001c0b40405000350300309 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 83134776 1250 83133526 83133539
    0xc080610030b1303030b06120907060c02090c031801090302030c0106090b09010311150301140f04020c0601090c05040b0304060213080d080601050706140906070206070504080c1c05060a05040c 84
    0x901060000410504020b00481d08a801c20206081501c4c400c1c2404612810140c003c9081d5403ca0300d0520034014003c0300f0301510000a00516000d4507003483e02450031400b03900440d01c2c1040c09090646003403000000560600c41440c080780b00144031394000d1006003050b0400a42d6900001c180a09039440c209000840341c0c1c0507c1035849091029000e140d680c0c0c40e540f50350b101c610880e01d840390860741040c0c13400700c030500c600300860290929034403001c0b0810444007401845021441da49000c0c900c104502c404402000503141d04649002e00003040b00003400204558a004079800102d003600040103000c2042100e8020303000100a03c013551224030303551440c450381c903002003540b03a002c2611030000c81c06e95441171009201d01c0d070050030042141769120744400d0400c00c0403203511006030000414411115818030680d0b8114a861404500305402c15840d1511000c400381424032a44001201100c0070b0424400b11a9054205003500c403686400c0ca13096014001c01c0300c00b111110060f400c0403452 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 83136026 1250 83134776 83134801
    0x60609042c0d0c0c05090703021312111206040f05030c0706032405130c03090213050403030c0503100e131e1a04030807050c10230907030b1f0906030c0806 68
    0x541c1161013841900d2810060005800003e445042015000c02620060b5280100340301c3c028000101e07481c48105090404565111010b83e82c0c0744148040340c0c144589520004907980c003e070f00030a0442c85070704039251592440c403d410301455a030151140001b541303601a03201184c15042031a02e0305001c060300d42c40c2d031408549409065446a2113140c1000700099075404642d4004440c01c000540c600d00f0707000a900070741e0b44c482c0405180d8482017040304269050095a071400002d040240c2142001c2c09542e40100003070081d0b410262a4000003262102c5418490350b0607508a5100280007104200c0707000380c903a81031010f41d02144150112003507070b04004051445940c05580700c0200c1e48424500f02c4483d07200e00081100c0748551081e5051900c0b40e3b00c00e5400c0225628421500303108103011117841ea050060104246400205040011079403404685602861814a580300d5080d17100961f00350398043e03003003804610f107000c1004c020403140e00140c100380c0d01c07100e0894083e940c5100c03c072820b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 83137276 1250 83136026 83136047
    0x190201020d11030c0307111003050103020604060c05010b190e070c110d0303021b030919030c03030c080403061104170c133c05061503060609042c0d 65
    0x5901c034112a000d060310821070010b810b201401602e150403624401240b070b68128110030341e00f070a031500301d0599501e09507650200d101454102031215603d1900011081c1c0246c1c445c940a105124401380708002c0d0a5012445080000701071800615804500443c1900b007406014424010780e00802e10309401014400c0302d00fa484841140301ca01c07004203000c00d4554125044040c99020b00000c443c140004400c0d0b004564840300554540f0556810031200300040785054000c50076011052020135a11400f40c1d003500e400d8184200c07481d1040c03410188510480d0b00c00361010b07191031898405103030310100510850346140071003c10310605050313190726500016021783d441010040c00c4418641260401d4580361400601c0e1520000603003c1c400c606c1e41d0412a100c0780e00707400400d414a01e00c840c840c25404c100141d50740001482c07006204405844040c0c105071286070086003025003903442d0f810403010710820f40b01110a00d19084440f84440701c24082c070322050300030092032001562180c03c8102c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 83138526 1250 83137276 83137279
    0x90105010507150c1b060507120e070b091507050c030d080906070807030e030a020601051201050402180a0f090b07080109202101080d02010f060b0306040509010f0e0309031902 77
    0x9403030038501840342c024031362601c0c00d009004440002000c0d03140c000c02d41c04c9000c4e014640c0401c2e40c0c43c040d100101aa000e8449456084c0c0c580410104a0200020241c007582d4803102c54603559140000000c0048100580250103d840090040100400400c0074a42004160202c0700d540f104060140c2d0300000071078070a500c0d5031040340012280c0744903041c5540c1240c00d904000800320440d4842e14210341c40610314002507440071004004500b0855000210000c940c0b0081209007026400103000460b0b4543e0001440703040804680070a91552040764248076200c003c01605c4454641513021000844030180030074087c0c000014020810300a00284480d02c0c0850001800901c04103070b000d4000c0542c584280a0b104810440400c03080c1580c0d003e07000749801803d1903840500000c0c25690030402820590781002001c0009181d0042030700c4d0494411103001c01c1c0c660b104080c0b0b600422410010005032810000940180900840141001ca406905070781c82d102100255078105108410700a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 83139776 1250 83138526 83138543
    0x5070815221104050a060608101a07080903030d0504300309110306040807020a0b12010b0d0f1508070503120706090f0c03150c0804020f010302030a02070803040809090105010507 78
    0x80da50021100c040070301252041d6161100d4030002000b003000c41e00100c4030100c0c0c0b0741d62a4014400c003030300449190f503c520f4418400c51841d04102c0211000d051840c2c0c030144000c00402c0744000c000501301139401118014080380d03120b121950b4030f80050039040d035042c2d0b550084500c040904100050742454660700b4140b1084500140c070104800a200002040c1c0c0c464051a18a03004c1c0d0740d0600066000c2ea0003611529190b0840780104002d1a16a42c03200c8000700301080782ca031030003000150702411240b2104400307817281901068100640f0521440c1c6012502e000421405c00302d005084206883d401802c0302c1502d40c4a20a2690f81c000c3e40c440c500706a1030501103480020b110360480c4c0d490501c03480d003c90710b540e010750b0743c00903c8505410886590915041c2d58240d000544070380d800644031441e09981909240d00450100040c0c08000da0406400100141c0303081ca094045030780645d800102c282c1d4070f00c1c09040c0703d80c1c560403a00079580b00d8002035000041c02d48c4210107454196400c0840e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 83141026 1250 83139776 83139811
    0x304180911010f03140c090405090607020a03140c030c061005030a0507051302040f1205060609010303050a0c05120a030204080f03070b2a07031e09080706200a05070815 74
    0x43d6a16925910b000c01010744074000030098044c10700c00e4500440c0030340c0d131940e242c0071030781c041006840c0010075001c5076a00000400c031003903a000a0184101d90981400130000314070424811013441034bc60800a180310000e5002605540082d440344604e6078503000d034127000e0300d5404050700c801e43c1d480080c229600010042c805486d04180c08030390741104001c014500740e0b0318075503035103101c00c0c55000c003000d0a280f40c100e00601030706001950b80b08404490100d41c56045540c094030500844144104003c01406800304121007049074440120b4413800c01c603149d000114006010307602c40d0144240034080d02c00260381d0700b0000810354030303040d0348180010041c1e0344e40c440b8440000440038601c0c203440c800301c1d0154144c6c40c5410042c1010344c000e41d64062107205881c08650011344801c2c2000411900070b00402c0f1002000c10701c50706550303651a0004424240d9500d4003a5a01002d51080090181421351b07010440001132030021a0f891906039034031454288502d1107400012240164402d000154 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 83142276 1250 83141026 83141029
    0xd031106181b030304090501030b0403030e01111210090e030a02070e09070324050c09030d0e011209211806021c080402130f05061e03150606040e07020304180911 71
    0x4002e602c250026085034202a81d4080d014107846081c1d0064031590a0001400281342c2e06001c3c3c08003611843e0005e001d00d0000303800320f0005103c0c52403804c20440010002c40e000a62100b030400c0140f01040c4284126031408081680743d0b4042c0098402502c81c003c2d00040b01c20004030b03080d01c515400c001601c1c01ea899500e4940503444100c5400c264040d0b20035040c0b107208800d118290080c101c40c48070540319000d20060514103802c856410052020030401000c05a0b8401ca4006a00d1040ca50114216409150140c920f014000c034009803e8569103c0b80c807901d80c480d008000c211100c020305542680d4401d000e0b61189208150200d004401c103486000c118002e08101d50000c1c07014001c24901002104028102c0d01c6074904251032580350f1050003050300e060251454030280713409100b1015501c2000081d9242c40c9a94108400660440054095541d48041c3c6005201c0340325080c42034640000001d44a038824050300400540c00d480c0d016904c1c00b03500c149071009500c07511858031804003a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 83143526 1250 83142276 83142313
    0x60801020408011a030d0507051f05060406050102010b030d0e0d1502070c05010801060207030f171303060509160302121e070504051e07030b06190c050105070c080406050c0c0d03110618 81
    0x30010740d464840c40e00ac0300318980c041c5098442c030700004040001d0a003040d0f800c001c10390714582d00c054110380c1070503102441958040b0303181c0d0118540b810160a812804004140100d80d00103005c0e0198017900d1010b0f480810b240c0081040e9441016405410354407200103440c0d000c0c00380136400061340201800e05c002510f44041c8008503014408101d403103844408180502d6000c0c0040d10200e0b05000020020011180103560b003105804019000c41064582104801032030341c030019101e0740c0701c030076460041c4009000440044e041e4845800c8038242c1c414030190b42311018450280100d103020001200c429014a00f00c20a00e014001500e0079240c1c69011000740041c0c2040ea07522000400031072260030f07800081c4881500302511810144101030400c80d084030710007448034090000d22240500010488801c0f601645c580307042c855195111140c0c404c2c40c01306031005140e000901d0401c0d00052540110354580c00d007410a080703441540e21780c851001e4403a0b942e100d29000307034055200044c1402426 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 83144776 1250 83143526 83143537
    0x60c0302070c03030c02031614190506040e040b010e0106140306010e0a0807060e040e03070201050a121404060c0309021e030307060c110609031905090d06060801020408011a030d05 79
    0x528016040c40c1c11902c80342c5004403181d00c101c0100c1c9249548500314241885181c2403242c1882091075103620788041120740c0022946503c1c0300d01000740c2c0f43e0036940a81c4e24088043e017800340656403200d4490801c0d009561f03043e01c050380c40303030181800004d1100b03414003114180c400c1582d82008100035005000f0440d040a4019030500c1a60014030756a42c448510100040c001c0301e0003800c0d03183c5851342c060602c2007810805030080d400e03d0220105440004100c1c0d85d0594286004d9a03111070107203048800080d8088a0b00340740e070403c070398000e0349480507404a02a80c0202003c11100c1e00c1d810341a41101e41d20000290028005412012066034000d030001060b80050162450680709503200c1c0c003110320110090300802c061070600038100e603082050551001801e00114a049109480d01040c1c00c040c0406004002d00040c503041d4a49482000500040c0e120f0803d00c10381e900c03028218044d400c64080d8030020761a040c2c0c08182d18043c2494104521405006441e5610304103100b02c91aa01c039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 83146026 1250 83144776 83144801
    0x504050d020d060c0f0f0201050903070f150609090b070f0e1302040e0405060f010602150f13050a0507050f06040302060f070f02060712121119030e0304030b060f040606090306 77
    0x45000301804543e41d4003401000c3e4040d591580c02c070018040d00130f000da06480c00c49070110380c034150401000b480008210b90407150000c0304000d02e54060b1808030a85810b000c000301000d410a040080c5902d004c5c0c001e025010302c54008182c0b540d690380000c07918101804607031000200b4a5800e507a45040c800551480c490401d0009464141c960300165a42d54040d00c049615903c4001002060440440304c00e01410040c40500341820050f0f10000880001602c0202c0030889440466090801110500c000f81e5001c01079900d10655810300355141c0c01d0601c5242d000d440d0340005d0400a02e00202220280ca60050045007420071040141046800c00a01110030144160421005d603540b1805031015a03c43c010644510500324801492581800c201c80207040c2015450940000000705448102d08000b400754080c11000300304501a1810040c10040e03800000340200910140c40c2c18544901015074040701e1308205001444100c1c0d082d80b05000000c0d4a034202400010802d801c05214074a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 83147276 1250 83146026 83146039
    0xe010306050402071a0a18030809070e040506040b0105010201150b03041b030b070f0f090302040c140307030b0102011112070f050c070b07030806030d141309111309020a0504050d02 79
    0xc803600030034201da110713480640308840c80c504141c2084c50038251a642c841c6030114140808900e541c001d1020543c581001814800501d0005128000401040c401051040780054540c2890304140d42c0700c40301900e09075400c0706c1010011519500502981c01079180428040803500d240a11092013070f04041c100b200e40d600c1002c541d00c080a0b000d040000914061041036507103040c101809406440003200c001c05101c624006081013540020f21041144c1d0142c2e80030404400703182c0d080f242c40c1840351003101034120101c203009c0b441d43d00d6484410003403807c1c1c00802c00700d0a1071880700c0d100c0c003400c045813500f2440a80098403892041401186001950410a080a424039030756810400f083c0c0141c40f0841c00800e50200303250740304514540021055020300192502c00b0030040c140345902c00200c00c3c0c4003000800421395010301fa550303001480b8070402000356020415500c049540040c440750085900c40c42c0106a61005100300d40b2142a5030325028a841e14090a010680a040b6010390b400270 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 83148526 1250 83147276 83147279
    0xc080c0306010507111e1008060603060d060b1504080c03070f1a04080307050c0f041b0e030f07080d080601080f01090902040603020316030c0b0901020606090903070210022a0609010e010306 83
    0xc032824000b6800740940d4515178400c414400610851087c014a04810020b88409019980d16411704072504800c080d1000001c2e080182000b5003d0b01801001680101e000d03c0304840000c1000007400603212000c094803040e000d00e0040550750070060007503c101042600c42007081340101c044401d13150030103448160600b641c444596045801644040c2c0381d6400500d1065024036103100600d401481c112420030001160302c000c6400c101d0f1070b105034001d0000c85403460300300f990100145a100003801e42102ca00f2501c645485858040c164510808110460007203919903019000b070314854428140849096881d0001c0036000d00b9402d60141c1c0c1042c0d542d2004000768606100782e00500c1951031303042c92003d165107400e60b400e400950014646d52018032511003940c1c0c0c0401e032607070007220071141c0124130313228000900d05620074000003c0d402182c1c21054061543c012450f41c0c013109028030030305601107003608000c1009038001c01c50303540030008210410066028032019042c603c0189400900c0d01e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 83149776 1250 83148526 83148529
    0xf0d020604080607090603020a0e0405060102031303050102090301050a0207020105070b0c0f0705030c0706051908180303070207210f030c0302100203010f03170c061306020c07090f0c080c030601050711 88
    0x80e0310070341042c1282c1c2c00030810019000e411081070380003003400d0700e411490025108401003207010003a014a201e5501c0c1c03004a54580e00c20003d5403600000c162104944541d03915005000b50f0000041c0790095080000181600c0c111340700752240a03806840302d918204080d80c80d032982c040d0050034aa101c072801d0007c1c200e100960030150628611410086507100003051085240c2700703031580160304001041241174281000c104c0d14030680300c00381c1440749640d11008449446401c030244002043d12000c0b040040855000500e03504641000141c0000e1503000c680b00400181c803d0400360000e200d0381c0d0003200182c032400c142403000d13000b0720507514001000d04402050380d00aa111703840245480d2011300511074018440d40c13900c1c2d0030080541c90480d4a0441c26100c80008100b00c0d4588480c990328024049103404132101c4c802c4410644038140d89840c000c0000b058009030780380542d4030344071740c41c80c06034010301b410f502900c03510b40001c0c110b5a8801c0112800d130b012442c103c07640e2a400031201d165 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 83151026 1250 83149776 83149789
    0x5100821190516080c01050f010807090f0b030d0905090a0506030706051b060103060e07080105100902031b040b071e020d110103060f0b21070929071a010f060e0f0d02 73
    0x1035200d842207691710341039980d01c01d094640203007a40320145000c01c01008091000201002114450080031441212000c1c0d02030040c48030315003140d01402015000c058959001c1074400581d2421104015152103480c1c030cca003241c3c0200d0301c6940580c0107020602005008401401c0c0c2c00020035010182030307903140f040a0801c0d50a0340b00b2210b060710398901194550080c03140c0c0c80901600d0008000070f2400c00c55117410840c4c24803a02e90036650000c003003034917460710701101a9800300300406070340d6482d07071042d0806c1d85034801e200641308440382d00141041c0030558164a0101e64006200808078a01a22116030060080320154107143d503560340000e980590386074540040680e40d10345c43e1211159101e12402295100078080c0c036107905010800c815801c88512800d8a43c1010a1000311180300307191841c2c00c800310114500c580002c1852020002c03007003481609401c0300001629039907030b6a040c0c403050100902400340800d94440080b2404d044c03290f4514104000142103d0550006070003180c00d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 83152276 1250 83151026 83151067
    0xa0b062d010807020313120f0807080d0b0103022b020d0f090510060302090106050708070b2505040b0d0b040f020304080316020607050a030e010b04051008211905 71
    0x5031034103014241200c030360700070000581c0021a0b0000c0d510303000301c49010840da41d000340102503070f448642d00404248001050784809059104141d00e60325030781810718815503080040540c00641c100045a111940f09000303881e081a5032220407440b500b0f01c0d100e00e45c006000c05842d901d00315801c1c0403a03040008a40501403244800fa0b1001440d0b070400e040c807600f49111052444515420540200010f07200c540e0614119031080c54a55158040782c507007d0581d01c030b40b00000c0d10b40c01504052005969401100c8480d802c16500000b4195014403815640b9000d02d01c182104400180001d804100c01c030341101c00000b0000b000081d036045401404e500300c1c1c100ba80e0079030f0701c006c001c820001751a42c140b84215809506000800043c5008480140244035128041040588cd12002c5034160001d4000e41c0320701c2e030014424002d51404030300460614040e803040c0c4000e88126040d0f4240f0390b01d60f4540200d03549506042c289040c3e4180064880300d01da100504082020411406001c401442138405 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 83153526 1250 83152276 83152339
    0x60409061a012c011b020d03080f060901080304050d111003090b0907290d0509060a0c230c0a050a0305040f14210a0803181606020a0b06 60
    0x4144040500004207880e250100c1900075026541c00c1c080341030322038003d402207030109103020483d08113001c07107a070350940caa110300030f400000d0160031008141e00580352520481402040050380d54600e8100b003602d89007031144250307a801c1000140440d080c0f07400765640250091900180040350040480c6641c2102819000002c0d921041c43c810061402000c940019491700140205428025265000b20980704c0c0c48503044810040c0400f400007500c140d0380d041200840400980c0f4000c880181c807108100c9004161524000200380706078020741c0039500a09503411580ea4031540d20710590320316409041c505582d48140015980041e07000c22507407031554420303a2381d1611640390420000d00c00142e900411a480b4441056850589a00c071200d0724100d52014076240003800d943c5060304110007180042c03d0414000204001500c03140d41403010012000d04072140564511a1100d1055084c0540c000681004603107001291804800907001400100800d500c2e03107002c3c40c03000c0c18034103454291 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 83154776 1250 83153526 83153561
    0x507080d0311070308071b0f060902011103120408070203031903060f090b030d301d0604020907051806040618080309010905091e0f04060e03070b01060806040906 71
    0x42000d40d40c5401204a0715805241d910304103a240c0d50050b0a111005080b03400700300504400171032002c0501012240c0d190803c80111100c412418008040d00c1c01a009178042582e42010b41c0020800104440440a5510b14070045440300d984900c015882484241d074140b1050141498680000c1e102984210b1152030004140b8540710343d4005080c8143d01c112030b03040c44c0c03090560503500c2c04106080c105620b0b141c2a403e10f8079071480520b195080b000a0141d02c10446000301c506000d5502c5080c2c004155060503800c49a1021800d40c1c2e2102160000e4100d820300f001b14a000d8051005060717032604041d050b6290306294008140c054000e030b0310001c001008010203507181080517450001904119000d145042c40c4000007070036124942c40f44a015005203000203000101c084100c4800849046042c140e034104982205020710f000c2d05c0170740301c00d403412100510000000045803c4940c0c0100102413903841d1034401d40d41d400c0001e100c5500f0a8844003e000010728030320403001c9400a00310803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 83156026 1250 83154776 83154793
    0x50906040c0510140a020106080708071e030203030906370f020f061506160b09070e01080c06030403021c0207091103150f010504030c080307060b09270a050708 70
    0xc9407500c5660300c05030080b5102240106150b60240d0f003100e031049a0100c050b80c0380c40c4a00f0481c0185000c0d402a5014090260041424180840c0c524222010704d4480e00b07a4002e002c00e00340703d40c112488000d5241e4820405813815040840141003400181d12010300031025441200301c81892600e40d1007802c100c540b008440440c0c02100f5404140500d1005092207007021040075070303901c00a0014100144071b039040d24019542c22086810402d0700041101c9880564030382400480000d4407281c90500030700c00c021600040d11402c403030403140403000400c03540c02d00340c0520000307034809041a01103028101501141540100442c0e01d5450036a0042c0021450b0148000448044080300c49011504105100c030113100035180044c00070301118500392100c0742c14010b0b50140314541c001004202950000101c0c40401f1005d08103617802888240440340b00f2408022616600700e8121000300031041d1103e00c90f02060111000d02200c00742294003400480d1242d624104dc2640710601591140300d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 83157276 1250 83156026 83156033
    0xf050711030c06040213020c010e0708010e06041101030f0b04020705060403080703060602060c030705040f030303200405130f0605060c0106051905010203030403050d02040338240d0605090604 84
    0x1090380e040514800594144907071452020740b2908040c1004c2d105248503c6200100800b5070b04503100c800841008100ca107000003c0c0c252100f42d0340c4141c403155403910345025440070b002314005100b82e03401080301c042005901c0c010b43c000e00d003030221580e180395a00f075800503030740322480105509402500103000340c0ca490714006043c00c0c801000b91b010507082440c10040d2a8000400c2508440d02050040d160707510b42904607030b0385c0503c0d840f002c071043d003050000050580690024071f03420314a6560309130762002005140c14904c22440380c4e0b5048000140324013000c1403158005e1844410265010421544e908001038040d046503000300150303503444d03008014a20703010500c4407004041061200c86a4504070000c0d40b24000140043d090210004052425101e0340d81114090366000c0c103404150b034607401038800341c0342400b82c02240420104004010b490403203c1c169110f03218981c02d0380546240e00e009840380e40410207030075402441c000c4a54000034142d0040502c1484400003c0025107450305 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 83158526 1250 83157276 83157287
    0x715050603030c0304210c0b04030605092b031b0504140d02030a030818030310030302010c09050a09091b0806040210030209010503010509130606090b01181d06130f0507 74
    0x40c080c0c0c1c0301c0d50041101c00114400402030301c0450b540c850f201801c0030712441c0c0c810003480340c1c10001040408201c2c80412200d403002d002d80152406400204a01d80d190b028042e81c5441c80c00c0b10f481d1190826240380c1c80c171071184003103008000d41c2c0d25011490800e41d00034240d52010022040c3d000c624046424000721545e004e4032240e00d0360850340c210641c0816004070f512061110405010800365a000a580340e280500300502d80c004402100d0b030320315040035070701c0840105000c1140194244006800000d2250f4081004e9400040c4003551551a12100c60010400f52100300d03800750445103003e030928190b1100030010302d010400b4202d1890300d44104403241e00300d14681002e051040c00707070501c5664003006980c1510010f480c02c10040e100d04480714101c9094460003800c040c00c040000c194082242c00100140100781c9075040c892017901e00e08154941d1740c0c020100f5480410941c507000d070400782c5c0c801d60050f102612030300040314210030080a440345503c0700c1c11b078a526482407105065020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 83159776 1250 83158526 83158531
    0x1d1f03391d04080403020d021f0201050f0105010e0a0618050405040c0801060b030f040b100305030307030b040605010f0804080306040204080a0818010c111210020703170105030a120f050906071505 86
    0x441081101c0e24050359070310300f140542c0c04042c0c00340d26101c11050441d19040c41c0715810303030642019200c2e608048540203000e80030403540c3c4040d8154540000a1035400355203c0b01880340014000341c2154280401156180142d00e65a801130503141d90024460b1100e1103000d00503801039241104185c00c1500c014203550706580b2005040c1d20410402c1003002e544402290040d40c0312002182680300c95540000c0300e03030150806840760000100744424250140c0c020089080d0550b4180035442e9144015915042c2c456507000208651400260014031b06800031507011a00034030041c01c0c961601e501601d04400503808650101001a4000581c01d00c041c180c041341130246003180076840c81d07644d0445100a01d011560003610704466440030709105001d43d04010200361421900c400c0b213424010b01c0c43e0014050b41041c3d03814400042580d05020804a0a9a800215034110200e80d11000c503190110b92a149040250501c071040302a43c2d19802880b003240a0301104103050b01c1900200104c5201 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 83161026 1250 83159776 83159819
    0xf180c08070c11010e04060626190f0e03031003030e15070f020102070512100f0e0a0314040e07050c1009050718020409061d1f0339 58
    0x4108008400e039100d00080c16055210f014110003064030b00050b124111101c4266503c50308003400401d407245e01a000d01070712038814502c2c101071807503299403a000540954900c031905015402741d0464a44580100c0060910f40d040001c00242c00131416081d508280c1342212030600c0740e4030800503d58080c581e04030580b0304485100481114101d101d07003511820a000b08071031007000705881560300a0103020010f01024103524030a1640c80c0349991101e00906201d00740310b10740038a051910001c1c1c800c4880b1034a440006003208049528281c8803480300340c0100441c010108000b01300509104401801005030b51581c503100c584100b4500d041a180358040480a4074045040c6e000c10b0300014108100d55034500700c070800c40e41c0f41c460032002e845190401320701e141c00c010700090f8030310b03c05502d02c0d9000e1101502005a03184c1d094a0164164885500a10405054001e01c04134140c41d0303e0050040b800c4c0101030703c2e43da2850107000c0340d40020070556000c5121003010041000100300310400d1000e23 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 83162276 1250 83161026 83161037
    0xc080910050105030c0d050309090c0a121503020609060d0f020403030908060f0a0e101805010c050705031e090d03021c0201020406080109020703090302060c06100e09060a050a060f180c 81
    0x1840c0c00700b0b5070340b20340304034031403188080c881b540c02448070910448456040282085c2d941d071600010560003584046a0034000401c2e003107003102100c030580f1420012005035140d00c0c800a256400b0800e80b034010b01540e65002d83d041103201c06a000d00d108070b81210b40051f0001d600c8518504001d4100049a88910a01d030071580801001202c1003000c2e55105810100015003241e1140c0b0162401c000b0660720703090744d8034107543c0c409040040590700305a0340c4590001e1148180744a0111101e000d07119008026030700c140218260650b110703013104c0cad69944c254049407c2044560000b116090b80480940140e002120800c2140382003142074900406513000a500d02427406100811040c01441030556035640130590380205480ba5031a100210740040183d45c841b4854510162600e030190b50110305880e110100040342510703030604510800305040942201d98503154500c0107800024442c1511950341e200100d1500e501054004c081c0015901c10358400c0c4c01118042d08179003000da040c109000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 83163526 1250 83162276 83162279
    0x70b030703050109060b0705060604050901200408100c14090420031501030c0c020d05120304080301060815010c0206030604090213020d0e0313150302040306020d0506190506031f08010c0809100501 86
    0x34030009949e40c220400341c6001076107a4450200030300600707640040b808056245031a003500d4000030700190003a210b200040e500740c1c8188500300001c0baa03a0140010105000c0d20300c050203640f40c00c01900340c0d040301030000b040c540d60329100c502011101086aa4000c40c0220601002c401d011b44010754101d001c1c2000c03c021044140050140c00105000034441d6950106a0040210034400040301d0101c4186180d12404d0074a0004840d800034002c800c002064040043d290590081e9081001d0f001a101d0340c0c03580340c1c40c0e021710819a00041800e90415110703a080d000503200d03044040c012500747e42c3d0040c4c6501c0346600c81d90a60b65050040030742d42e0b01c00c1c002d0a0380807281050303240884c0c2803440d0b00340b05901c540030141e001e4091640040d12052020544d402d4925058118a1082e03c0443e91aa40d501a800d07188044001074024241c0002c3c0500014014001100241c0c0c134030705440c8007101d8441d50321001607083d200c6008000d40082c10000c10701070180343c01c00042701040344015061020350f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 83164776 1250 83163526 83163533
    0x60b041416051e04060f020327030f1609060e01140405090a0c03030206041106130e09030c0109050a0c0e0103150c050909040c0303080709050307030204020c070b030703050109060b07 80
    0x540001c544850080394a0241401041221104114540501410034600f1041103154010b84200c2c00030841017215000600e01c048212030726600b219031422201c005114104200040c050201905031141501c1c40b41e21000402403014858013101c10a0000e600b08210070b001d94803180e205001034440907005000f00607070002da10131804025640003a036651000c100518100001c000500070300c104240100606d5404640140f00340e00400c0c1c3d030f030550172015050081d03d1040902c40d20700c0d910221814400f01400441c0a900100004116070400c034160080d10f00311408118100c2e8203a111f04501c0041100031080c2e1001403001505004566245840d00700c00c0c00040c48a210300705503907074565080c560081d004e952050350041c107441e210f440c06241c11401e4182e50300090780414001c000280b4100d00c141140c1c42600c2000d0040e1103564950ba0a00002e0f4000c6003865000703000c0c6030408038020902901030352050b502e540c0c000c511545003201640849142e0307084040050b10422005003c03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 83166026 1250 83164776 83164811
    0xc110c03070e0a02040506070b010312170403080916140f1206190204090f050901050a0522061b0c120503060a030f020d02040509010b1e0109181e0603060b04 69
    0x120341240111800d10b64400300544002d10032600a1581f081d0003040400922105028142c1030b030348203e10704a031011f465001500d454010380701222103049003e00150009110703003000c540046070a001c4070070304040e44800c0b1942901c0c43d0450101c09090100e40e076400e1900b0303211401010000d4a1911103400110700c3c0ea601d4042c000c1c0483c005109058056501cac940c581d045900901116104110980143c1040005814190f45406080d0309001c0850080603442c450a8054100c6800b040a0750740c0c58503402180d00b10010044e1603242c1e45501401c8508040c501058180703105640b000d08503915407030622041c0006151070010080c00b8010400c10303840b003c8032502500c0d040b1101124806051001030700c0701003c010002d4015003480203000200744150044045600b0445a07001c11041c0042001c280d4600c10071154009080359104000400341340c0c83d11254441e5002c1c01103161061004082e01c02c03000a1038241c1240c2c2c0e03c900030414040c2910400124004c11941440210202040e4204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 83167276 1250 83166026 83166029
    0x70204150b0304030503090a0609080d0b1503060f060f030106090303021c05030c03090307050d0201150909020a031415012606070f0f090302030615090f090307061512060c110c0307 79
    0x5000717000011518016040104c918550b501100c1408007804a01c1c0c50001600240350b000080c60514680c00388500e0103001401c907011030490054215680c5c1c2c4204001e81e1081058141c0110040201240054100d0003e5019103115159010403526500d8028508640000183d0720604009103080040e64000c08403908032001210042d1a0780f03410280906610400308020080d1003200032000a541d01904908661000340d81c0c2081c2050b5240e10450a44600d000300039405190035000f0b00009003d0603000c540d89400c50102c1e094401c0c10010702d025480b0a0300302e1480c9017072290481d0a0380051248c4640d4246a035030103040503041804002e007030580364100e074105108503c0c0202e00c107144215002c400a5800504881c0e084c02d098915140303484000d1980c41c0076080c1c0400180035000e907a40d06074000e88000380214a4200c1c0c90300c03110001c2c1034100000502240640300018050b000164034000c0c02d004000000740b200c40710302c025220740001c4500c10b03070940084c02c1c10b03da01e9030080f41540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 83168526 1250 83167276 83167283
    0x80106140703031d060a0501090c020d0e09040c0e010906052e0c020321033103030b030c0406060e0108160504090905070f03030207090501210206130302030111070204150b0304 77
    0x410501d105a0407002c60b8442214544c1d910a400801c0354409194200314120b0f50403440400080085d40e0007261201800d03104003010505c00c000000013801c0243c241940705e40542e100100700780d1240e0f0200b0310180c01f0f92204406a032103020030300c030320b20300405501080032081000002c0305032003046150603036a06460301001d0040e900800402d640b824825000550010030301807002c5542100d031010540c10544055102e60400008030451040c42440c3c04e840e200009a2083c200b07a050f90101c000e0f100d0200902c3e09400740000c0100c170354555001d241c1c06019561505404000c00c04001401c00304000e044201d001108508550700c660000110383c2684c4400300003045040c1d060070194541410b56100c00600c200640c00003080c9035020400a090340d203900e0307050015903030351680e072901d01c6001049214032140c00c10000c8010716241d4010411640800005070700c0d1030741c2c0c5c2c00007402c403000489915194800004d600d401c51409100d0843c004001c215a900b05a00344003104019000080004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 83169776 1250 83168526 83168531
    0x4020405061302030a270b0f0a02040806040b0403110d08160c05060114010f0201050105030d030e010905060106120b04060305030702270405030d0c030b0f010302030709030c03050d08010614070303 86
    0x1072016107a060400b0b42100e0850015503a908005031440f004000d401c00c00480c004009080020510074901002d50407600004401c009445042048601800c0a0b159424141e030800000078400000d000c800d10890042094858514081c1001782c40f0000c50080302c49150040d00820342100c0c1c116640039008032840f41c9440030a4050a010b4804012401c0050190311a80d4000100710400c040c41c10307035105003a61200c1e400d201058099085e6402030003502c0d07050304015501c1d1490340c03195110310007030195000003003100142d40d1142c90501d00f00307070022000511400030000d01744941c0d0040003401d043c29035040124034034686440f51070b4000e016000748106040200c201c144029444002e500814007100c2c0d41c450304182c0762150f5268401a02001e00500381144070b01300d00e0080c8507812200001030310800c2071020410044001398802410b410900101c0e00000c00401c6064900c18065403085009202d404c40c0c071403000c1c100c054140d02c204104607a4003501500300500300151005a0f5240c2800b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 83171026 1250 83169776 83169781
    0xd1e09210507030801150c06060f06200703020913150515030c13020903010e030f03060307090e061303110102070c032105070609020a050d0506250203040605090a03021002150a0603020904020405 85
    0x300d801c03801f511317000f03421142003240119050900c0030010301240d03815191136407070401c0417034880720f203844400b5200910b8000c11010070160408240d02c50f0b00100d4051100100075440d42c41003540291404030800d01641d410401c2012004850b00c00400c078400c03002480300380040b40000b40104450224181d0040d00880d5000c010303102500201c84141700700c0141ca848d901c0c840c1e42c404150b00300312071251281c4501d8030002907040d4648540d00320824001c003d00302c0c03660360f044d00064001002e14210b08024101241011444080c40a001e09500c80c112500d41c40c0e2560501051042a42941440c4111200c00741c0b80301c0e94001084400e050751011020032002441d000151410b130103035000741e410002600b0032604110000c60268403400d6801450249440442420408906a6170120300580e000b00028041d850280b00a00080c42c0010080e00e48a0b8513540854030f8000e69808800150748402400c003030381107500d0320007684500082c030100841499500000d05540d409400640503030742d182c0c003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 83172276 1250 83171026 83171069
    0xc1809120c2b1403072a12180801020309030910020a020301021b2a190b070c150507020a0303030f090b01030b0a0608120d1e09210507030801 62
    0x103400c81d075409911070407003102c0051450421800c003081500e03000440760020351005101d02403d0303901413070352540c6803400c0c2010f1650a140720f070840c495010325a01100045000152021400c1613043c0981e03507400c107140900844421100541d07040712035282d00500801080d0350001050741ca0f885011529405a0480c610382603091441c0520080e41650001451000740b4002c680c1030b031304521500341218140300440c14110071000708554085041154401c200e039080c07418600030200c0c4858201c004124550b913186140f20795025080488200c3d4181c6d40400a0210707810020050010714103102c3d240051641c0051513100d020b000040a041e521b00c11011007004c0d5602c1281e4003584100c6001c0c032035850f803d11580080c0d00700d4681900b90b00341400421501400319001d40f1003900845083d00f13000c91f46000c80e010746058008814501c40041407001005039500600311958010200440103082040c2c5005004560405410501c9401c10021000a41c019151030450740130344112000b001d41c10b030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 83173526 1250 83172276 83172283
    0x207020f0f011101112107080615040f030506060a050d05070b0d06091a0a06050a200a050303100303080705040303200705030f15010f0e010e0c12090c1809120c 70
    0x150980f15642c604299411082865002440e0201703d0780c629400c41000c6000c444842c1c0d4040301d01d9400180e03200c0101c1c40c0d0f4107004507425000410b0300d41d01c6041ca40c07111212083d072141540141c500d40d01010070f01c08030303040c407281d0200980000e0b01e216076100815207409030b844005200388082c10000091529118405500070030107411041000c1c082150401a40d805e4440b0180c90710b48a40302c0000000b500c0e601480c21104084a551600e5130004503071000704224601c00c042e140101e028990341100010014030095204010711008205d6007415070030010440c09000b800941030120410061011940100e50403d41c010341d51b8510a80020115010303041504030340c00f042d05403040b480d10a00394032001c100e07031401c240380d030b40440c0e9603a0b600c1c3c44074041400300d4854405120500381c018070020700382c03001c0c031703940030340d5031400744c0e190180340c0d0003d03844101c00301e0314031802e9041a04001785900e4407032a0650b40b40078107410f4000354100b015034a91a001c4000400071500d8000402c940d602d107092 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 83174776 1250 83173526 83173547
    0x41a090301090c08030307090f080d0507050f01051806060102010203060108040b1005060408070611070b041a040b031302010f02060c090f010e0a031b0f030c060305060103020d0603080a0f030207020f0f01 89
    0x3c0e0303543c0c2143d480010343d5507600143d0f001c10105440d007601050042008102204a440720270040a40c070004180a452940c086d83c0191400d00401050f454040303030074021140100c45000301240c401000059203400d0a40c00703861141107900420a200f0640e80c0010960381254001816502641743e5080c1160390004541c0040d403c00008500040d0951022580304d0446d401a00c40e1301c990807540e618141caa50081c000e0410b94681404148880c0c5464003840b954036030034110084c5003686072501d80b0401c2d00112460071540001c1003003102196840320168480180900042c12276081c0742041103118043e6a20301c5001c0c01c002510300060f030388210340351000204007901f50402d1a8507800d00c06c5002c41048802091a60b9912002404800f01c8120340c0449812040e104005410702c074040b4040c1c0030141c20300b41050740911015559a403a44690340003144102e4015030380d81c1d201030700500f440d0030840070321040c50300c18000c110150321200340c4101e21030030403101c0d0740c14103403100c0046e19900a030303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 83176026 1250 83174776 83174783
    0x150108180615040b0409050a0b0c1c0b0f0301050f0a0c09030b13060501060513090209040b040c0801180608120318031603020606061c05040620120c041a09030109 71
    0x2154240002d540300d01e4400d440c018001d95090010a0440d0180019070b154a0b0b4024159070010b44240b001c110000042030304680502c2e426071502414041da102c00384958032801b460195141041c80d101d15107242002d48850003907000340400d00d808610001840d1008000c8400b0700d850741841c82d0300621514030a00510750103810002380b8180101a0071000241c00c00c1110007030b1501c000801c90501074020781c0c1d0310f0110034000100d41c1c0d0400b0341180280d040103041035001502c2d05200c49441d42c49000301c3d08944000e80d0340c101203600d0100e0391030011407410702a0001c02e1230400c080c0311811000c2202d6260b800128480c80d41c94480d48210041d0320f00929815400380000f1840701407660003070006404e558069400c0340d0b0952030352803c01010f44070301324003842e01c1180102c14900601c2c550f0001a40240a00380000b101c9040207001e0030700c05144a95003400c1c1d400000c042c4014045c0c44015604030041010081c01e02e800c201c4001e0320b5804a420100a030400421700c100e05540075041250120351 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 83177276 1250 83176026 83176033
    0x1060507020d05030d02070305090a08010e03031911030412021605030307110f0901030c090606020c0109290a0e09011703030606031803040906030308090c010e0d03030f0c0809070e15010818 83
    0x407c1d00340200960080d0741c01c00d10540c4119000510b01405005d140f100240c2e20300a10b207191203407005101001e00c1310f15a41c8886403200c24440d001c45200d0044c61249000304901c1d2602030b0003000003418080002820f0791603600d03035a0140000e44001040d600c1b2507034400c900005003803080c80003403d0f9030a069001940000180000700800c501120541c0803250182010b0001c00d440740400c0c0d13116500040c00c10b0001e40481c208014400303209110501100c440360b9403440107000728020145d00c1d4040070903040400c2d040241c0d400c040c201524101c2c01481100b00b0008110183c0c1d8000d078880c440a0650340c898075010010400308107246041250940e1071f82d0031a681c1c1c0f40c3d100e0082d8082c00307640c4401c0e408111402c0c0010b01100001c10840d02d0201d05a4a84a011043e1420407107030a01c202c0381941010b5075440003050124440c801c80f00c410903562210001d40c944001704914104081d000740032001103980601c5901070248001d41e103c000300f400c04c50202ea540410079603c1c5004500700804610 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 83178526 1250 83177276 83177287
    0x3211205010611121e090f030109053f090102071701050601140306150d090803040501091b14010f03020d050f0411030f060112110a0303050909010e01060507020d05030d02 75
    0x15007201a43d0342d40030310441038a0f1212a22500046540595030b840c864050101501145094103100100b0a80c0402000341d00030a10220201f401c6904102e411280e903407090741311040900342c11001490000940e00d1900c6140d4108416064450502c000e10f280200080703941c154507802480300c480130741041c81c1c661850b8100c003001d05007e45410703210540800c1c0c6000c0521090b0f00d1040c1200c3c1720300c801030089040e90200c40800211940f105c840908101e50b550203c00000360310344004e5000d00c1c0250004a0340ac140b07030a00c989000301e4800f94800d500e016010410100303400b04032682c10b940f800d01303203030351603540c05c10080d800381c4201d90700c070000607140030704200d2140315510307015005601401140e549850380d2014180e95090310b4000c5001503020342c004012103545451038070b000303521500040d6448881d510106010b450260001c0f000304501041201a07400c1c03400362503005103c8480c00710155490301c14050400c2c0300b1444040e025403035070440c400a1140070002c40b104110400c40466562 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 83179776 1250 83178526 83178539
    0xc04020a031e050f060405042102070b0c010203010806130b0109090201020a060203010b1c02040b04090f112107080402011e022d0f060705041e0807030b1509010321120501 75
    0x4202c110380a1448138400c1c00801d00c0c03800c03e80300c0d151050768815200f46c00c10300f0100640401154503d2001c007103100e810400300b000c0705054050b1404510307150015840f54180154242482401004405080000c0d203660003c194100000e030b044071540d00c80024280581c0c00105d04280d482080540503030700000c000558117883c0c900512030307021407082041c0c407004500e8814080c1c0c440e500c51040100301c00e000c00d01c802c10f401c0d88005002040c10300c0028103010700600c8540250014404401c40c035810410704222803400d000825880b588602d008050752074140d00280441d90059403680c0d030503d100104101c2e5500030031005150f07962109844151141c0b680600c58001c004105000c0c80b0301448607100394000c00000c10500405950315102c0c01e1908020502d00310032040f90310220504005080095406802c1c80500c000d940100380d54071031480c128001d42e050301c0c02000f68501030240d6070010800f15a009031031004c0b090ba1001202000d0030700e9042100e980300b2007825028558504400001d01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 83181026 1250 83179776 83179781
    0x31504030503061519110c1203031503010b04060803030709090902030a030f02012a0e0307290706060602070609080a12050f0403020405010b0d060e0106080402060d06122f01020c04020a031e 83
    0x86d0b401140403212141047c009001e20341c600102445407560027070000c10150044c40c51500c03921000a400000d4030004007000a054a14a03230080819070400014041d10591040381c0002400039081c05120210703041d80400d50301c134443c20000c0d00300004a1640c0380c80910079081140020036100c404596401c40d14203144000a401e01c1c1070000c124402070503819810081205001c8031020380303401c10b20f0950940305000d26a10114a02140c40080040c0e0000400600c42d40b030281070300d0340c02440c249003040c001404000d007039080560b4950000390301c030001500170364021041207054a0943c2c2c4401050035105210300030783c0c1009500600381400801c5e8000d001001e007480081d440001d000081c1e40d8100354007071000c01c0c080c000024141d400010b0160070900010006000540340006050395104e160018986100100b1500700000c04903c100b441c0c00c0040091a04103065681c3e41e0180c84280040d544061384222540aa50003186000c00a8065448174080100020340300e9898241114038500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 83182276 1250 83181026 83181047
    0x1a0a0506030f0f06040f0809030a06021e070f030c020f030a0f020411131e030606150f05090a06030e07030209070c030801060e0a061206170c031504030503061519 71
    0x78415030981118074040001c00e246030110450182219485d152142059005d411070240e85c8200200044019030701d0410034a8441c80c06030500688640c4a101e078074100c1c100d150080c04000e1410b01248d00440e400c2066a40e0040d0306040101b900c04107403011500c3e94460a1069505004030340001040c0003111482c810031520072282042480014880201302d40034001c0d40c43da030044808018401640742c40350070040303400c1d90f031001490a90f0700e655074015106160081e031001c00000b50081001600502d030a100601c3c0360811904011101c0f020824100140c4204801c0613218070702d440450b00c040c4101c0c00030b1a009016074a0a00e000140a02a1074808000300c2c00662803400001703001e0b1007071049020f0503c000b41f03840c0c0300a1800741d048809081004032450340c1680c0d031800080090010414210006400b005445164401c00406013881401020200303103180c0001004002030707000089a620201c11207a4403c2e1a007400c210740c40300d0282d62180304d040001e1180341c0485c560002d8023502c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 83183526 1250 83182276 83182279
    0x1208090705150a1701030f020d050102130603320a090201090801180308010f0e040809060c070311040c17130503132301020c030c210a0b07020d020613030305041a0a0506 74
    0x40c200b0380342c0c103410308000901b444080c1c41348805108120051078074044094a42d809400094203001600750800d21a114030341c00a03000c259221024481080c1c0c1004440802c001d0741c0940b01d003804580341060704004018001c2522a42d44c2541d00c00b1a03000300010b0000c0c0001070003c12104400c00214101078038003d1060300407032624000090161070030b4240106541c44071f100708029448955420103203800c01d04103154001d10502404c0300014081102c94020341c0111444203800307080714148022110060391410400c0b500d4444030842c0c03002c1c0c0e40c1c3c0e15004003940e0b00d6031080714071504001c6d045020303c4001000707506c00e4400c00220705413081c43c5560f658443c98140c954242d1090010390b5213800320100d080e01508252000d071050320f800d80214400440c134092400e8180e9002c0c1c044d03410032030300101c104c40400c282d405126181e50f040120400c50717965800105440d0070284090a101e8403068002010581c4541c001800c10840300d003005a5049194491581e908107000c110f406400308a402e00e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 83184776 1250 83183526 83183537
    0x1d121002040f17030a0c030318030c0209060f0d0803060103090b0c040810091109060f040c0503090d090e0f150d03030902040b010801050109180219090305010c020a1208090705150a 79
    0x4220f42190a40100004484800440c80c02d180c0c005d066030012052082641407654903c9080c8541602c1d00d016283c05200c2c1d512210310701d095104001c00800301400383d44c02501c09004070701c0c0945034105151034050b040fa80310b03601e036030700c0400480c040c10090200902123240305080c861403004c0f00c80038206a0f03102405039000c50345181000b000721a140c02001e042c1181f10001c2e0421810125292a003140014240001e400c0c25640443c041d107588290f0724000910000422510203424400030714545002d203040f001c6a441c1c41030000c540040502484007400c1318801240320032861080c41c050150019041c500342e01043e04000d1300400714004268080c6051000c289c0486d803040700c125060350016114504000d0606018111040000340301d074185079420451500c02d00c0400c9000403a000c51030707aa6100c120300350710300682520184054481550712086944e00003400020030048082172502e0840c101c1c0c0d64000e80c0354600482903000540010450740300b0181c6c94206401011589081e0312003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 83186026 1250 83184776 83184779
    0xf1204030816050d0c2d030509031201063e0105100509071d031b030706050a2c090a020301060e09090a02090603031c060302040b030a031d121002040f 66
    0x3040b41412000a040300000ca0800400b18014581da018401c9101c0311315004864800042046402c02c1e0742c1002010209030904a03080c6055050094a0380701c100c00c1d01850800d001e660070100c0380340060040300b0501031036542d00400c128034641030002d21840e00c130001c00711358180314a000300c540c804080410f0b00e50a10000032107241c642d6907090111240a012a80341d5540c4a504403194154034659041800c01d5501400700e070703542080009101c01013569448410f012800c06c2524000e6140c0c040420f110080c000c4d401903a4200151011403c9084140d640b40510072480c1c500e02c0d80c0340d0555035480541202401202c10ba20b5000c0d5058a040f80c450326107940300c0c40200b0042d00300864141049600200b600c03001410091900d40d0028806400c0383d05080c00784103992006c0181da080d0a45803951160304200303602c0c05005d9030f03081a5054025040000031070f00c000340301ca40004032022483c901040000e0250f110b100c6050f4411030394000b07460800000010b10340c080e42c0188603d00c01711904120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 83187276 1250 83186026 83186041
    0x316030b09131b091b1701060801050103020f0c010509060405010c02011404020409030207080a0302030c0c09130f03020f030708040806010503030412032307060902090a05160c02060f12040308 84
    0x4400d400380803072054180c07620b212603a9a803060036050114800c16a41400001040c031110300903582c480c00c84119210007a502140e0050803141740307004010f60400c1000041002c00d8204c002941556402e20b005603581c4000181c0031420b11560001081640c6840100107101d03c0c00300d08640140d1007032009000400b22144120f003a11510091104010480c001203801890b0507030104010038464010b80f01c020b42c0e503918240c103208058106a026810005010005800c28490500f504000300d07050541030500b140788400b00030341d0701c0b001056040005201410302d8020412170050108000440380c1e50501403030003220640052042254500ca003000100c2d030b41c42c003c400c0e03c0c113031686034541c1524005a074404581109403101d542c0c881c1c00c0258044003001110400401285024170004100c2103810310500c40301d0031000b0076400565241c1014440005e0001201c014070340700300c0c982034900e075a5500000d00107125045184020b040001410000340c103948580d1880707140252200205541c0e00030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 83188526 1250 83187276 83187289
    0x912160318080d03021308011b08010f0e06010309050705060418050a020c03030609040606081005011508062d0a0305010b03060f130f0305070b07030518070315050712020316030b 78
    0x840d0b07026044201002d900074483c0d4050440a00c0d005803010f1500c1d40c0d414043e0031600400d441142c285089400e8980c0d45800031703a031070300503e80c0f102e41c2d07030f40c641c43d00c40c1001351918080d03c02c03810141c07542002c4003401000c11541015110080c010755449070f40301903218202c05d1100c0105001c0d800d100010341407503411f00c280c0e0700c1c941c641301c061482d6603620400c111040100a0044035015500c2d17002290103001042030000c01c03905c01500088a50410b00c002c83e49080c030080340705c00c000c041d40403c011921085480c98030803456100d91080b0300a1910300c002e0f46c1c0c2d0000e601581000b4980c0d0004140041500302c00400c1205505075030701901c0d000403414480c201103070960300c03451388900c0c2da6000070314202c03405150901070b14145051060580d14030445003000d50b05000081e40780e00c05e000303400f00800301000da01104140104035003451540e0340481c0602a00c02005265651000100c1070f90051050340040d0902140465072841c1c00c81c440340c04801040c80c40340000f458405080d1444c181030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 83189776 1250 83188526 83188529
    0x61403130602030415061e120309050108090102090310020712051201030b040f0203030d0510080a0213180f1a0c040308030a050919050a380912160318 66
    0x4000805900c101a122100a9032003d801101c04801c50410000d0021040c45524094016402e14146002c0f448a0703040b0449155003112034103401005003100004d82056820b011203200382000718180e900c49134458020f01815401e545c01d40203071403c130b0178a12900c1c0c0c020aa080d00c00d11b1190008140c003901200c60340580803803079524003007400050011480030003640364468420280340c1400900d50b07022a055803c49103501515603140e800b401040d030360b01c1c040c41c2d024042c09001030240381c1075034001a45040c242f20128502c41c0e0350b00506001215803195041225400219081c2c007410310b46003610318605c1e81d0795621003a6100e1001310b079294004000702d4080705d4211441c3c506603110800c1140007041c0250240c10548126031103a8801c1e203442806404044c0184d000d4110140503040c0b60818081c0f83d0b003500f0805080b805034680d0031034044040c80b09075108d041d007000705940380c0d0082c1d85072202c9500121410280410030b440301c422565113200d6440d01c44c0d511402d081c00d480e00c01d141c100310725 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 83191026 1250 83189776 83189791
    0x10030203010b0d020f0409060b090a05010503091009020d0218240d030e040902131a04020a09030308090f06040c051201060503070605090406090507020a02100503060319020402070c060207061403 85
    0x8003c41c0440342d8041c0c01420b240c0000c80350041c80c141d0303904036420031651079034440c880000000c03440020600e840d03040c0b000185001e0811900d549840d0b400140c0b42c12a1201d000d55042c0e852822400f0364981580309007100b0b0b03003d8000d440010b59100d1440700d131038048500c031035441050180502c9802010000c44a940f1001d001c1089600d42503a0556078003400320000c41e003096656010901681d0b0385904d0185108480d800060104070f0110500d000d40050824240603a004010300710000398040c4160f0120b9405151065407502c60b6145503050500d191600306881c40b40310103001c14044010100022071342c044501c00c07044e030880f43c0c149090704c00c284101503046d0004071080060074000d00061030041d200420000e0390540b914944011520b069840c2c0c2c0c0140d108081c0391085061140c0e044425040a00700f0a01314903160000030307550000005019041103c0250348000c546803901550b00007980200102d84031610350000955a80740da02c074640020701d01e014100100d1144104483c0030303045 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 83192276 1250 83191026 83191049
    0x7060503060103020c010f0f06140301020f0702060a090909050c0909060403090306050a2702030c0109120f0303020d0905061012170309070e091006050f0102060a0515120307021003020301 82
    0xc0704001940290042000c492140d501c6502041c45042c040c41900c8640900210010304141482181000380d000c039842c007402a881000303031000d40c401074000d4540031076045031040d9481c440488111214000755008035203140c1054904002c02001041c0c80800da40156000d1040b59079220900f0347c2d845007950090003103081980e00b840442e03e1600050b52001c500c4c00c0202c2da0326007030104100d0a84144481d446000000aa40307021803406100c8002003039024070306041310034241a0481e01001c1034400041848140340701e00e204040c001d4050341c800070345900e41044005041d00f00180c950030102d641e07410020801602049a04007000c0c404541900003040a010528100104c580c03640090b0071130800307106280000660b11214240d5a01c1004030300e01619a003c40300340c5410a99250350842c80c41805e9418411405990009a10303034813000e0354102084a841d00b1440c0d0410f400030b2601c00360004003e08244006160010041c020b40c0d209860180d440c10442030304904a00083c091001ca0b0740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 83193526 1250 83192276 83192281
    0x30c081002270102072111012c030a02060708130e090c04050603030f030903120106020c010e010c06110a020304050112140613020415081906030c12051f02071407060503 74
    0x1003a9080c070b140c00340044c0112035545854017080d0081c0d5407220801c2d480a00250400d070704001410101c0c03c6024030a0a2800b403440140d45641243d40d04900820617940c0d6501f080c2500380c0d41005400249500640000d60b9040142032484a030792001c2004544c292a9407000100c1c1810007441612600b014805848541445c0d4100000707000c2c085e200c1a4144402d2060440c030f440300340c2c0254003406a50300156034844401604e1204510168040006d54001540034807050360054070b041803c0d1424a001c1900b40618600384000b012007010056110601007681c001054002004200f654402d8031400004503042d103420003a104051216010343c1c0e504400320b042414039600c06115107008000150801d40c4800071038089808400d102800201418288241501091000c140ba40310a07202484050f0031a1150311802d1540d00c18170401c4100c042c100028045c040c485490310031000900300d50700076246620200a0740200800b81e660845000c0041c50304e41c000990740702200da26896050556 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 83194776 1250 83193526 83193577
    0x10b04120f0206121e04050709020a030e0a03050918060d080304021c0b0709080d090b0c030904060e1b070c140111010c08010602060a020f0304170c0304030c081002 72
    0xc0400c0c0d040311408031161440700140c0d1150083e105603002d50050300c0b8540b4142a041c0410b00104155003620000c0905000104101044001c2501c40200016a65203200f03a4120001d15443c0c1540403103004090125080640c844d00500030f0903000c9a40c22080d2a50700030f680f111500c10707a10594800c000416983c00180c0900145a120b03000505800001e0700031124100120a820000c440d40c0c030380701c4100300503260840c13150809070101d82e0040c203003850740000241c6284075038007924156500c08221a080306404008440f40084046e2090022a40c0c84120f1900c40b2000d581c4c9072290b440c40500140001c1180f8140c68060750480354100120746488011115400d81035076050422800b480041c41d50076003406007001e00d12159680300519850000001d041c004058140f518003401082640c0e00e10045c1e0042e80d8000340c0000302c814010350740000d0f0604500c102005000701c0e01021500006000099150b00c0440d001c2a058542e0314000e40911000c0b031095200d024003803861601c072040130 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 83196026 1250 83194776 83194799
    0xf0606081015031e021804051e0c041a040204030c09050c0a0210020d0f050115022505061b06010602030403150204350615130e0307080c100216021008010b04 69
    0x804109004240c0d410240b85c000c0b40340258140d2044205054800030300c1304004003007245050000e241061200459100c2400a842e02c50005413a44529103400d05441c1030b04071401400160035008000b150760300d03903a10f000d42c0c0b031800c00e1003081082072600d070005d80061810b800300c45409140fa40904000e61480c1c6441d4000d4101445070481c099030360243c0b80c00d201407441041d010703062810740c4140d060020b40c0001d103400d105020381103815440c40081c04240940320300325020344800f1200a83c0301c000b00300d401040100300801282c26445594000030310b0076001300042040d24010100005020043c034600002e130b10a034820b8203522004120600038801044042d12448500526078100181c11006000e20b07151080c0c91800c0d600d004404414641d1818540c9014042c50025090001159512800361640070382c1402500c030036000900840080030030311281a041400071701c1151908090100f034518401100400c1307000346805540d4440e160300894100c0d04942000c0c400380d15090401140c00030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 83197276 1250 83196026 83196053
    0x90f0607030b03010b0d0b220203391c020409120306030b07050307170c0702030106060e01030b030c240c0607021e150103080a020f060c130e070c021c0f060608101503 73
    0x1a0205102e1042380165400e11451012414611880d40c0306100c41c450306c80ca9501c01006450a0900903005d0241c58450b008040e000348840904403452803010700204003c0c14a17418000c0080c4c0c81104040c1102d40c040e4000801ea0f8001d00c4441519500c40900f510603200540307044002c10141c0c5030504954902205003a40044490328550412800e5408a8252046c6401c6000420508a446603803542c0c58070910031072080c02c074010300e0003510500100e9421401107483c1d1801d4242c901030014040d8403902100d01d1182c40800b1038235603150130302000307460f0340f0090304250248030081d00503194010f0000b0490183c3c83d504004103110303440c55641401580c0541d1105043d070003000d01c1a6407000050088910810414018650710596100a40e000440e5908940044007280b070501044582c40700030401040c0d81610f03680c00c071301200c2c034005150781e80d02c600c01003140e07564050b0b030420401c403a004001100c0c1d14108403502c42e102250400151840544042c00c042e1115038100f003c510421522030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 83198526 1250 83197276 83197321
    0xf150912030908060f09060c04120b04020f090403050702150301060e0d030201150e0a0b030a1205090a03170a0818030a0c06020903030f071b06050909090f0607030b03010b0d0b 77
    0x2e840703942d8040042c18104112a018082100c100070001112000c0c0035644d8000184120381c0d281500b40140c104400040c6103024085000581c0020215218510f04080d13109008280060a2030300340340c018211f03800140100c1c000c2d00300c0a003031054007170240d043c0d03410f0300c0c0e840d00c3c2d00c0c0b4003010443c20b0088038954840b06408645d21400f14802c000c101d00c91480160181d4507803968189000419241584d00d0b0144050107644078014880c04180c8019400c02a04110720b040d0380d0780d034182c01c0020603070922a00f010303000400c282401c080032262580203214030320040e25004c01c240d4400600e910000505c0d0004041904100714181000340720b207a04560031817280d040181031240340c00c0403e1550300440d4603d00114000200441030003841080c602500e0807c0300301c44001410500010058014a4401e030b0144203070801127500440306218001242201204441081c600408000d01030511100c1c490b01a5182c100c11071441d0900ca088084040c1d04100b07042c51944900081c9403030182e580803202d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 83199776 1250 83198526 83198537
    0x11030a02040e0120030f0c16061103010603200418200417070501020a03050904091505270a02100207030816060b0603070e0f0105041706010f15091203 66
    0x4006075180d1142c0c4440200381000001c145080426814409203044200082e5541c2030041203046805503220f00d9025050f030452580352222190303440c006801031000106280d040c552a07910030111640514101c900650702030085044429402102003280b0824041c14a020002030181e0820080c40c6031211911541c006828410424403004403400702e00d40450054001a08014003d080f6000b000c50903480000381440750326040000c1d5881d240003400a080c05804206400e140c1c0d565800000b22641041c0880e103061901c00d0300000600381110205040064240903039122004c0010720070118003520000d003602001e603001c000c0c040c000400010118410504003000091100d005030100311100004a01104901c0ca041c90984003540c00c0c183c024501481042103250348510451910a4140c0b403158982c0d00d400012200c0d0f119542050959542e401c1f034241c0c0c80c80c00060b81504850040c11206589a219031400c01a031914582d01800501d2207407041c8103242842d80da03c07168611a0602 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 83201026 1250 83199776 83199793
    0xf071706041509021303022d10030207120917070803160807020d030e0a0512030313063201060801031a09010f051602010b0307150e1212030411090c071103 68
    0x1c044e0780c80305000f001c1811802c1020802c50814030344101f0f0b51082c066040a8100c14064a00720942c48040c006201c1c3c1c0d24030402001c0c81d4040e50440c0c10301a040640c000410b9000040038086156030300c2414a60306485010032950540481d44500b43d0f074041c00035524141022203100c1c11440e010605030342e01c0b21b08100101c0141e45944600714110311a4460510340c09408007042181a015403009014403404000f5a401c641e02000301ca0f48160b682420700700c8820030b42403420007800c10344211320030745030503065420748050208500c800340c040002d200c040b02ea03200c0e00d080f11022020301c002020310355610128802c1da07010100b8903902a40d071400020b01e00001400c403906603501520090b1140210b0a18804002e5086c05100d407401d2080d0002c0500d113241c54203101260075414480804c1203940403098480e60345000e2180f0111180d2821102580c591112050760390344240e50403125141510003211860030055001c511842e101204c00781007418507100c48004050440919a150058090 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 83202276 1250 83201026 83201039
    0x803160c05060703020d0305090102040605030402060726090a080c030604020d0305090a030305040305010c08011404020c01150e0f010f03020f040207020316090b1002010b06030a090512040e0f0717060415 89
    0x54400c46001c3d500601c21b900e5071040280071950050500115079004101c00d10060390800100c0f030704140d0640da1030359030b1011424075031038180398849034030f084045020040404000190241c042010100c81c440d0300c183d99140c045948401c10201d46826410120009026203003208020ba0ba05000307041c51850440003400203020212190000c80101d08049410b005103e004d20989600c0090750406404a504010001c0c1889100420b05031140741c0014840704098429008400d1fa4110040c7c1c440c005512070800000c40c040450361380d124a00103200016001c0c2ca0106680d080f01d4001d46130400e0805800180000780d4480d0005030b82612686840650228a406070f640c018410140300052560070351003013240c18080600100d04682c14402070000e41da07986000c494101078201c1000507440014a00581442000b641c45030611001040c001414054010301d41d10500c49041000195600e60009503840d41d510b06401d64400e40610010b101420306030b1100e11010030051009605039035650 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 83203526 1250 83202276 83202289
    0x2010806011e05030114030d0c0b0a0e010624021501030602031503061504050c1c0207020a150801060306050a0620100207060b1309020312070807060c0c051002040803160c05 76
    0x2c120030009100200402081c210110392001d803070001c40103003180f40a100802412010b010402500805090000c202110300681c450a500011100240245c2d60b5070103254004c2c400c01001c441c0882c002508a090007403003c02c1c8000d0807050385545120503403c0d030b15540b0007908020400000c002e542000034200e03030f40806c00c842c480d0a64048040706078407550184016214050b14030034a40781c003400006d132050180884019803000c2c44200680325103a82c000105120050303881051010fa42c10b2035040da0310390122540c0c0c1651059201482602e6651003444800080c078030a07940000c0600c905882c04403441c81c901005682880202d4420029104885040303900c110390032500d0b29030b51301642c4d45c0e908004041d0b000c85030f01c8200c01c0007059001d0300400e49881440d504002d000c2e60020300e80041003c01421303a4542900440d0400c1001c03250040a4610031155005aa141c8160000101048800e00894013640e400c0c0380a1804c1c10200e07005e04108075403c46045a02845010002c202c1d80c4640 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 83204776 1250 83203526 83203577
    0x120108030a140f041e05090c07060e03040302060306120c03060a090b060927120714011b09051903050102070308180703050703080d0f3b0a0201080601 66
    0x4050340d6142002a0050030580d900d07400c034642100c05024920400c41c6000580c0c00322500b50f9012810703100d4201002400315080e401c025800003000041c055001c0c074401c040d2000b50320440d0700f0002002104501c03070b603e00072071000960103001000098040c2c00e05da0700d1207000c1081c0d081120f828200040001342004011214058a20360350b0039800300b072000400d01a81c01c080103492141481c140400d240458000000c1e8403207a0400500908c5650030040180c1100040324030741d015155a400d1419030407550700302804c440c0c070390b0904001c1001200c400c8201e502034644c0e910b44d491224505010701c20400c2c2e501c2d10322601c440000100001255080c0020200280b09650307034240c500d03200c1d540d250700f040e84111a000c0395200000c24400142e0000c1e90b541901d0f0008031035030311810303d004140041c0c00c00d10401c1d801c203400d000b0f2a000700342c0c07048900329091038081d030006102d240b01007070880f0151580c404001c903540400d54190155007e044110340207101031510003010100c5592009100104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 83206026 1250 83204776 83204789
    0x40608010b040f0b06040618081006050108090615091005040e0a0302250e0a061d15010509061b0c09040c1514090919150509060402040308030a0b04021201 68
    0x1500203803401440e0620801142ca843d41008001e4a600d1402040e4035010780d001c0d001c18058100400000355141c0800c80e002084c1e40821901c40c5110030b504c0c0310182029126940c041054a8040351802c0004112180300380182d044440817001d4040030003800105c05010f0b10217081900d000815035459500840d001040130304010f0905041c0b501c0c00a150440c03411402d1010000190b50300325600c400c0755120b003140d811403c05007140d00c442c0308020040c0280e81c09448040700c4c3d40306400c0000c048107592441408059112200f40800d840191020300c03d034402290301907400c0102c1e5105001341a019102205076004880c3c11024000224403041e0782900c05540a10000c002084690030340d000c0c80c180c41031189009101d90348684980c48444c01039100961051034940c0c009600b4030307065405084070307500440080c007900021340302d2001c0c00d0905000f864011401038001030410700f00380c000c0b1400c41e90b010b1402895503481403c0b58005060382680590b0140c2c00b008480318a8007001d9489018021 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 83207276 1250 83206026 83206031
    0x1030c11070e06030c0105090d08071e0f030207050a060c06020f071b03050c0d1a04030e0a0f050102060604090c05010804110901151d030d0513030602040e040c080c03120705030904060801 82
    0x2c00e1001c0505c2c22020f250114100141000036410315100d5100c81e0b04101d501c00306190300c808182c5030804014081007290503414481407401c0303040c4112100d100611074025001c0d200265100c40c144070444c0386902a000c00708210540c6000040c02d0f40c1d00034059151040061401e2545695400c0c9202102504a00d40074008280a1081c00010b00108540d000100d4802d5069842642c440f1050320451a030b207400161850b000400f4907001d920302e00c2030384d00000c0c183c42c080f0ba280e0088400384a210f01401e401407160000090380d90070b15205d00240c90f034000c044d1080c16490720004460090000b002140d0b078a1080b0203c0d416901d540740c1c601d018200102040c4181e8607401c4000b040406540c14041c985180745590003056100400c41e10210501460030395940c04c2c012402034004000d0b0344c030041c1000d10000340051108d5002040a0040740b007083d00c010003942d18002141d07601c1c1503502c907070391582240301e44060a00041d4010080d0901c60415070b4141014040010200c41940d40031200994 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 83208526 1250 83207276 83207281
    0x209120a12080103170a030e0f0d0905010804051507020a080a02030306090a021201030314070804170c01081b090418030c03030e01020f04030b09030403020a0b0712090b070201030c11070e 82
    0x442201e0600010070303403070841215032560b16210b1200c8280c4601e4055000001035013100340307209070000f0241021120480c0c41070034120380c07000d60303031003044040e000020082030000c1441d601c102003160042c3d400000801000310f05031b22007a05e080010f008401948103038640400007646440180a2000c020b030091901c03440c03d002401600d500c001c012140840c030401c0584280b80e244003c06041d04e07054507040080340b4103400440185d11400001900403d000305d0001000e485061880813642c20032010744040000d17200064030086003c0da064910780400441036a802424140601050340006202080840e000c0c0b280150507004c441e0240e000031103802d045410b15406000f0341c0b0508010324021860709440000441441c09680001450060014046459210100140e80280d50000e02800c0c0040d070300c4802013003a52000e8022580c10300ca10080503c3d503400307180342c0310441d542c568400b0b240c07074070550044008040d42c4000c030007070214212960504000c02c0240201504107407a0412050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 83209776 1250 83208526 83208533
    0x1b02010e06010603090f060c0905120601051005090604120302100c0315080c0d030e0a0e070c0b070305040b01050d0219121704050a061d060f0306010e09060102030901120209120a 78
    0x101c05800c44020300d820840b80e04c0004c0d5080d81c1004145400030030009040c0b064031000c48991810381d200e26404400150b11141c4501c000c9100d82c101c88040b00d03544d1007610300307503019112405040507083d0711a03800e010030054900c00f10401d241c540d1181c81515400e46440e50a1012540300030003060019686680704109940076421050180030300e072000b060030860302d000003002070913146c4008080081b040c14114a43d140c0d030446502078802e1480c071502500d81500c00a28004107000f040d6405003510303020130805402071040c1c6001d16008420a221070b824001440b01105184c08126041054100c840c0529940000068060250600348190b410054105030b0340340314a22a80600794442004104603d90307417022080d08540440c18504440c2c100c40c2c01d006070444804c6c0515800510000350508180c102c0401103101d1003003600c40d01c0b2601108014440f404034100c492a000d64010000d08440d0760043c8100c008500320048050703e4852104042000780c030009140e914294002074465041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 83211026 1250 83209776 83209783
    0xc040509060909100b04020f0a180e040c12080c0109050d02070f0e011707120605010504050a14010306021b07030506060909030f0301270518060112031d01031b02010e 73
    0x42141103a5a10b601d0500c03050041d101c0300800d600a80b255510240b003907942d102c980550390403610102503d07442d82030041003d001c00c8038421900407644501e0101140d0100007025150203140c00059100140d0b003481d8840c3d44400c00d8002c00e4130202006e100d4212405d9003402146126845040a0413201d00360000191405e25941c2200b240702c60304210620008038000105811201d141c01c9180230b107034502e6409418100302e500501440740000380c16100340070b81d9070000350484400b500c08000595803800d1034400c0300c2111200c0072201140000406c007181c0950050410038921000740030b50103540f0114140741908552045034142c000034200301180c41e00c221070f40c2e402203540010354500484500d242e9058031050294100421015020001d151f0000c030554480e007400c10310401a0f42042c2e003d0050221030074810040c00e1141d030002280e0350f4060300441c142c1950589480350000c00040c4001e18200407a454a8101a501c003179115000003c15542103800544d90000581d40d105203010ba0304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 83212276 1250 83211026 83211031
    0x9070302010306090908090d03090b0304050106060e100206040f02040f020a2102030103030c14240a0c05090303040e0402031203070c050f150103080c011407180509060f090415050c040509 82
    0x74114900000c0070041801b0340202c401203401100e442c8100e01151400740d540a0103900a054140c4001c070030001003060560100d401d8038450384071900c8814989003086104403a130110000160010f9000c180091106903200601d588002d101142203407140e05410201e800c0100840f000a0320407042596116010640c2010400f202c030007946190304544014000d40c01407040101410103100c20840c1c0c1ea81d00384601d811082000c48021384010101005a0b00745000340d6004824900d05450644c002c0e0140b0f085560981c4090061410545800707101c110005001308241d070540108a2031400201c80440214800c801c55221441301075007900740755240c04868201c0c0d2100b9401a81322941548815a0160450f54481c00159503a110707803075441d000d00100000a0744018050043c0021541c0002100e60300e500c500b41d649540c0d940d204204040c0020a440585d00410034540c40307c000d00f420003d05500601448c404512409110340c01001c0360f40494103d1981d0402040c103100302e1030411210364 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 83213526 1250 83212276 83212289
    0x8032701150b070809060f1c09050d08040b0c1309020301030807290402060f1e191407020f0d080703030207110405191d0604050105100807140d081209070302010306 72
    0xf4240011503840c164944201c1880303c0c401c070004070716100c180307189008030380b88038162400d210701060b0402843d101400740800d041743c05001e1807180e20201c1d0700c070302c001c0d42c410b9030003544862140d25038454144d070680c03000b00c0300c440800c1c0d8008082010503035070008500a5114014495480c05c007801d0400d02002010340c02400001c545201c44001890380c00310350f801540480c1c0c400d6407445401c2c405444d030b110391100348030000401c5200401429500000d002071822900212403074584400044542c4078100c900724464030001e10550025003402040390303400075005840781d86401c243c0e46508443ea000501c0403000a80c00186100400c00c03074a000c441440e0054a09000c58101500303400d10031101204031920141d500c03c0c0c005000015214400b6060030090140c60480c1007a0814501034181100c1185071100400c00005030707444002098412101d1058080c60409000c8003006900c2c000c2c0c0f074064440105c2840340b9401103400c106140e0040c002403005186052075880054160385403a404032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 83214776 1250 83213526 83213549
    0xe03130e0a0b1008010b090402070f0b010501020d18030b100e1005031605180603101d15010b0406030c0311041205010507020d09030b0c04080d05071403090d0803270115 74
    0x20b407070703550130048060558030319a1a42c0e850707514200114000703018074500584a80e010840b00018072020012030f905072034003a400c3e40d015108828003580d00701c54020940045110480d0104045030400c01010b412403154021030204640e20b540c5e00c4031640041d1b42143c0c1103e441d01042205160400070702c01c5030703801909031b0390b54289010002004100d00400c000e0501c82e54000260751594240400c10320070f8118001080444002d001c19a0b404800d100d04104a1041c171b14400d9002020384040c5048403066210185813909202049020700240c0b21000145900e44400031200f2446501610103040c4c580781e520f884900320309000f400e442024000070250b4000c0c1d95034050440c1c1c01103444007070303076000f09500b50740740c40d801400f2a1034070880e444030107107000e20300c5620102a4007030020003890303001380c0d0461041034180e9220307a100d114840342254409500064000040c6080340556030141906a80c0c0c41850381c61140807550441500244090342d54508121044c0b029004003d00036180702c00c0b88 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 83216026 1250 83214776 83214799
    0x510080c300f1c080f0405010b0a08070f0b030405031b0c040516030c090e0117030d020a0302120c0301050d0f0f02131b08060a27020c0706080a0c0906030e03130e0a0b 73
    0x350000e04c014004403060340d00c5900040c18040309421000350760300c0180403044641d950b0003417561900f0880c02040300078003d01400140e40766449080d03a000b1a00030000d1454951600c21000c00b280c01d0f8400b580c014040e080e83da10030b5075580c1c0b080d60703c65503103040c0c0300d800702c00c2142c002400c0b0703010403961500b8040d0040e028404610508a00380c10b54580c0f5036180f044540c035241c00c41ca5801060110300510f0700001d074008800794160080e203100500804804116115403401c0c41441c0003d010340764001e03031200e4450f400714420510f0700080c01e00509282c60000199000302e000c030b42009400b148400c1d150030410aa42000c08444640491140340c2100703e03081c03c100017030320f140385803048107640403240b0030090040e00a0f004081c003510250308119600c0c505401d0560300c0e40554810705011660b204001f0303810803031038013507000d0811056469811482c2040c02c01e03001080d40c030b5821101c5200602c421282242034810b11030184ca225001180741d1314190000d1010b40e5060301400d406000c44104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 83217276 1250 83216026 83216083
    0x50d0e03011802060d060b04080c0118060206041104110a020a0c060309030801030b07030b030601030c050a0906060e0d0305040b0a050306190503120a0c020a06030203040201030510080c300f 83
    0x90045020b50466130240e907002c8000000d400740186400c001403500000400143c0d410f00040c910303c422200b0b0700c2d08810b8640c540c10f4401404414850980036800003000038002500c0103c1c04104c1c81e00041002443e01c0343d0308465003040c0c1050004101623440341104c2801d00040200d00c000401961605202a07920707503500610307805042c030004040049000100c0c40c514025004841240c1c000f07400c0f2540d640e03480c104480903003410b10030107004140c00d00d800716408490b8000e0300c0607100036481c0da41c00301c00303003006104094120321025010000d042c00b0120300000707580c00416108a071940c0f920b8a80c00e107041042041d500031841e480c9222544081000306881c0070600b4000302d070114041c6c0780c49040911040e1012070050000940c0511a40d0000c60ba083d016409035020ba07000303070303000c00c100e070385040d01003c1d41a0580901c0d8040e40c400c06840b441c0d440d288101048200c0003400700d41c5102d20302c0f42d04030524028040700032a243c0207000ea140e08240300704a1070100c214070341c042c441100c42400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 83218526 1250 83217276 83217311
    0x2040501020d050c011404150f0225030c080d0603060501050d050a02010f03140a05010603050f1b0d1103010305210708040e07022b0905010c08040e0601170103050d0e0301 75
    0x8100105211012485130001d840070351200b45541159044030140c2c0c5070a2901c3c4007074100040045905034580945017601210780d00c20f4850b8283c0480b007900701c0b5456040300180e1280410fa003142008140c40e580e100180003e006030040d02689034001c100300741185070000c107440d016080b445c040e2207000920808150001151300b102c1d502800d000d00035a0b85500d0840c0034010b200c00010103024400c091020b46051a44001d040341c0302c2d59810040741d20f036003038000722040c01941c001780c0340074041a4114880c40420000c2242110072003000408418000017000395800c243d1050740c070703500507040801c2c00e000c009411056003004102c03028500051a81c642072076000f00c3c000c0c2c12054140d4000100300f94001c220084181908241800c440034850400042100003825040009039451600248a5000301c2c0b12551155200702001c1c1824203120125401400003088141000b0125910051001180b420140610301075000762408910207040a0003850916210500a0703160018080e0901d072000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 83219776 1250 83218526 83218543
    0x20102160b0c0c01020a0e04180209010e0c0c0a12020f0a080d0203040204020418150501111f1b090e0f130303050a020f0c0609060603060405061503120c030a0801090204050102 77
    0x400a000b81c88541c000d000500884510744500d610001e21424141c4d00108906610381003103800b8004d0304060007810903240841c040094000c0c06100060000c0d580b00f104855001c40700348007440c1030034101c0002c0c61400800c0002511030b1908044201c05661f414456030308004440c2004001080345035640d241e031881071259940c101c560104c080b40855030ba540444000300410300743d118824032001a090001c15061618140c1000200c0b0001090350041a20407018460740300034020001070810f0901c0c3c00e140070556614540d81d15401c8211945d02c5000018080c0460395650010504102c194544200007a2000b540403844000300480c80d686070141c20002a81840c2c0400c030340d00c40c00ca000010707000d02c88441c2c00d034110108030381451010004640380f050203c1c5c4211412134440000f030548030402624050402d4105400181c0c140b000c00303114020401000d41100c500f0724003d44402030035041002d400c0c01540000a0344040f235540010914050310072800210724003807070800040c2d90794114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 83221026 1250 83219776 83219783
    0x1002040e07030e0a0c1403010b090915090a08070804032006040302190e01090e150f040b0405030403060f0f0507110607030906140708061003060806070e0d05120d0c02010216 76
    0x30f4000310010810144021300c40113a010078010909519282d4031464019040d04440c0030350720300b1400d943e40303241c0340342e842d40202c400700d0140c1910044004140c07282039004005403c1841740910400004004800a101d4603009114054030389003186003901d886140d100f02404140340401a080701680c421003150f084030b0b8104e5446642c0ca1545000000c0740256a101c81228450f5100014081c040703904203003101da8039242580d102c20840c01125a1414054881106600c0b4880c001400907143c1c403403407078000d0701850440b420250307a40d80d80400da40c0350b4090b641c10030b9101c054510070b0700c440b0700410703801c0001420004091404410308580e1048001d02c1442010303181c0240710140714a65200d0380d114603544902c4104d81c40e040c5030281032a10207440c0719024980910707a0022061183c45006c0a54800c0c001600e03103516500012101d0095041c080303984400e40303d961200240040004818100c0b0507a0700035102d803152038a03c1c0803100403c40c04000d5900420031079061001d000402c6803c0342d031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 83222276 1250 83221026 83221031
    0x30a080711010c0306060207050a1a0703020316150c080708070f23030906010b190807050f130806070f0e040c0c05060403020c040515092809030c02031002040e0703 72
    0x4038198225281601229520307110351038000b008100d036034107400c03140941e8010740849400a5685007485002c0800340b240d41e00da1a41c03180100c3c2c0d0024054000c2c40128004d1040b43c0c2803031040a40001e0300101c0394030072214000582080740055425006c0c84c007292103541813080540c60304100142004c8002080c034010032404030b1040362000c2c00b415840504a130426031003035140c8002c18140c0e0056006807850560fa206400002881d0b006503003c4500c01680000303000702c1300030705540030750300f44001030020360600205121300c41c0e11461080141c62140c0403e4480308103a450024031a040c548058140c6003049014440792122a41003002000140010740c0c00140c3c4561200080325104100580144640604810720042c580c1c009038140306010100d604004035290680882002e400c0000c0e6650001409000200b0484412407004000018910660b00c80c510b400d08040864071f0050703044021592078100b640a40c1010410030320412070400381180361609003d00d13000c1400740241070604054 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 83223526 1250 83222276 83222281
    0x2030c010e0301060f06020105091608100b042007110405060307061805060c07080d0e011b170309030703080c03040f140f12030a1401030309140303040510050702090a0608030a08 78
    0x2c400b5402a0700a085640c0c0405140d6152080240a00341c1039503280400e11074008038008210100a0500441e004440100210415407040034040d0101c0084154002e41e1a0001c0900d001c000e046041044603808116642e0815864241e482c0b40c1e00110700340c043c520b000c0070001192000642901628920300b00b90020641002c54010f52403142d82295410450204a520895900048001c155104134090390001002c1090460355001500d0031a40014104042490080c0d58082c00b00c2c2c445024500e46040382c503108128003215801602c69000b19800042d0301824198000d1405400c808034000e00380c07450a1549520a107600f02e880017914540814414104507a42048407039005004201070f206440104206900d02d03070030840701140b80a08003035090300401046814241070308d61640300c6001c85400c1c44500b80c01090308114003034151108120205895484807031044c1300e10220754a15036101e1462052040d000e42c0903050311304a9080c0001484101004010b480c15403203107250850499 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 83224776 1250 83223526 83223529
    0x30a0b040207021e010f02030a090b0c1606080601030b060f030a410106030e0d050c030d0509010617060906060d08040302092a090d080a02010923060703020702030c010e 74
    0xb0711a410009610440c00d0a081910700c0d2220711903004000262110382c4001c3c0c80c14016610b901c03a240180e07001510090b0184034522075080942101003640c0c0c121813914400e40030946042c403080c1c201d1404980c40004000e41e941c0d0600034400300c02d00903100d450400300c05c0c440c41159400080d0050761002c0d140c40d0b90311052152020001d0300008000003440300e00400b5910406200005040e01003914800800402d140d40207004850840b4040d80050540510a1000322002d4000100351400c0740020094044c1c000b82034003465000b0320501c400001d030a45011680040090b0a19241806812410411582a0001c62810f41c410429202c0049407981e03803400b00e21510071a00000c1d417108104040c4800e4041a01c0651440303403034a030f0113490f0340c10124844c215a01440030340c1ca6100038008140400298a007018003161981400081110382c200c0c4c0e12607001d0341c101c840030541c01c01005540c4d145001e0803c00d01c0d80091050504500d00703512500885d454101e10888030341401513800d00d0350342c039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 83226026 1250 83224776 83224781
    0xf0302040c0e130207020a061e0f090801150f21030c030c08180f0103200f070b01230915040207021906030207030206060906030d081906090606180506030a0b04 70
    0x1c2c6407004180389000308480d241c01c4000e401070001a40500300b01100440c0003030082030ba910005003944031320001c8251140d23080f100031240103002d10402101c1a000036a001e0240a03144a040000c14861031650900845080c0b0358403560142c0050102242e4800c00094030700b0007000d41c40c0e0140340c10360000c03209007002d0b10700300c0c4c803410000d0052100198613000500c0c0c10400404848080b0b82188d000340390100110191241881a42e681d007660f00e480c69030100d108401082500c4001e10354608200460300e5842d200c6000740c2c03001100325408000307030f42c00e00302e800a20351400754101d4428021303091000001c12903108040d04540101e50008610040d50fa5500d40301c95800c000704c05480d0404c1c1c96010040194002400c12009407041c0c0010650629105d8500c07032103904050000c0465440340c01c0100d07020a006004085040034610302c56039030040c03600558020301800c8202040342413510500170001b0040005040d8480005d0400703002c540e440e6801c40381c0000c010301c004103a000c0c0b000c000400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 83227276 1250 83226026 83226047
    0x3070c02031c230a0c060e0a060b09070801031509021c03050d0e06010e0610120c1e030e1b010201060506120f0603030f030406020a090e0702060414070f0302040c 71
    0x52600c01c6000807980c044510300c0d220314030b1a10f50344002a0000d07050740046920609540c81c0c10141c020f00c40e090000c1d1142c2c42074503504d4043e100105e100350402c2c040c14105114120180c81050f100c0b07002c414103040400c96103070892054070b8034404a62641e11034001e85040c540c600ca0481c2d40b10f440d84000d542d0b40e00541008800c0b0500c9030341c11501c1c01d1a01034a00d52040181141d03c6003081d0745003500d100301044141c1220300c030b150031030312a503185010030801140015801e020b0000e1003010304641e1301d0f5840303a000e4240c201c2d11800c032040301d122030105484000e509143d00701801c21083d2132441d00003150840c00c14144008400800d410840182c6c0175003100e810454001d0b9000c665442215009010076016039441c0418004685603c0309042c0c0324031502d00615202d001c1000460001000c0e68000d0104a41500e800034003640c0340c1d001a00074180c10781c2c00a0040e03101d0824007041c0f011124801080e0b102c40001801c01501d1300c4183c402d000180d00c4041d1040f69a80102c10710310380140004017 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 83228526 1250 83227276 83227279
    0x3050c1005070311090d060c1116060e120a0f0c0911041d0106020712170c010207060501060e01020c28031a1506030c0c0f010c02070306050c040b03010b03070c02 71
    0x90a4038442035010008100c111a2640042c0c24404880070300000302c400c407500000064102c418003491a11944050460800d100007000800040d0070710440f81800940103c0256078a9214020b18040005002c110212582403184a00b007001d00003a00d00001c04443c40740c0d11155400703101c1105d060040c03407000c1990001d0040b5061074415a030008e00140100240da0303140c240c114000d80c4e4103032903140080c001d00880c405a40890760500c0b5115542d010810b41c184600245108400003030882030090300840d0b20074145a4010505400300409401203a02400c83c034030f844540c0007a1107000075a00c090001a4600500d100c008400344454800e1030140a180e1103200b81da07142d0799a14158619108201c0c83c04150389407038002c105c0b40501507101c14088070000f0206030035505d42c095900440d501001800300107102d078070448003184a0030b0083c003d0807051900607049580c07941c1849003d40d034005001d0524400104001d0001a0035481568151507401d50095101c1d41c0e465420b58070401c4154019 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 83229776 1250 83228526 83228533
    0x1003091407060207030302070905010b041a1c0207020f04091104020c0c0301241409150103150303030e0d020303040f0b18070b04180c0e1003020906030a06050a05091501030903050c 79
    0x2c00c84640000d10002120720035400c80304500e03940d2200904640d402e010388201c0700003c220412030312400d40841500e0040340ca207413903d81041c044520301d001d1090300c3d14000c4940c010550b07000307521b01248505941c280503101400445111360ba090340301c242c1d01501b54815640461801d481c00f6003003080c0044150701800030402001d520040400c00c015006200d45001d905100104486145102c2c40814100c003a00b0b00b1540d44900700071540d40c00300c280c20107040640d02c0c104914421401c41c0110000e5000341c0b00000d6105180c1036003030030240105841d00542d44100140400202101c05440c18990000040d200d16180e400010460311619040c0b91128070510f80003088007540c4000030300c1110311030700084c3c8005000c134a880d0181c4041e60004030100b82074210100b2035003400c043c101d410002509d40189425503030f03000500181c105440c0301940658480c014049800d014031103030042d0401302c1e402400d503d0600580110540d42c1381c12a0304264407480c00108050150080da00c180d9040c2d81039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 83231026 1250 83229776 83229779
    0xb15030603010c1706090c120f0105040f060b0301031401090206040306020307021915110903030706020d0c03090c0b0f0403080a02030a090510021e031308030712030b1003091407 78
    0x4001680040d201035210394038050b05010341900850000d03c0d4031240d01e00d40c41c8290f0380c8034200010030074000c2c0500c03031302142006002c0d40f100030140110301c600c02c0a04002030550404040c00100d908070441401410300d01002030100c80c154105690440380e0009012580c140861041405001010002500040046400f00800c0340b250090340c440c036160303400c540090180d003100e0002d24032948406030440455a14642014060b60010401d181d11707040c4241c50007102d5008a461903014080541c1c0c074680c0404c054150225038020800c82402c0c5290a1142c2c2d0b0305900c0b03841440c01f1b43e00c1003480419000509010300ca24170415a4020741c0c0140c821b0ba121031135068042e440c0d5001e01c2d01d52000458280303001c2541d14212104c0400f2000942c000c100702d824803a09507251408182c0d0b400350b24030080c4241252051a0300e6100c01400742180650344422980c54000b600000c5801c91a05044c2802d448068944a01901000d103448500d030104c1e4004e40b03400e2012140c00341010340d40c514050080d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 83232276 1250 83231026 83231059
    0xb090702060a0b090121020d0c060c05010e160b07060906020a0e120105091002090a1e080d0302030c0f0304150603080301080d0513030212120a2f07090f0b 68
    0x1525807040200d00c10512120f006a020071210b03540034041c083d81010840414807030010021141150300b4800f0340307041e50160310303503c034001561415400800000d10f45101c100801000303004003034041510100801960078806080804216a401b444501174404074010342448181d4201940042d0086002c569801d50168014800c11440a000c0c0c0a4121414140c058060500c40c16105114080182502801d54107042c00654440c0380342c19030080b01000c0c042090300039a500d40f4250b402d1020701451682c64446c031582807425054030142454418400c01088140c4001101d441c075111040844d6a40d613180751808804441886150849240030408420084107100650607654020215040b4020b542000c903803a2140d0100c085080b9032400c010001070820807406015401104140e43c00a07034014076840c480e800c01d41088001134200720b40b840013030025840942c0940114544c41b1507441141d56020361b41c0ba12071090b40541031b0b8503a40405e02001592026008450042100651403400403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 83233526 1250 83232276 83232283
    0x110403020406050609010212090a050909010c02070e040b040615080607021b03070f030204020304050111030702100b09090d080a02090307030506010906090213030305030c0f030421030e03040506030a0b090702 91
    0x4200d024902d003501c0450a07140050a0b94034a4505900600c02e40500d408401c0745030f08082c030b030150040d403443c0020030250713a0341403003c1c0305050400000440143e1104001d00c0c02ca6903510107402c00400c0d000340804190000c91055102d900a280400c0d0303051890720807400c42d02640d000c968140605001e110705290302181c8030300c801c2d007250b40240e041071050007003507141c2c902ca1003800c0c9101c100300000c02c0141000e030040e55026005c0c0d0f0000074100508084040d080d801259800c00503000240a0021000c0b80d214400b0780c45130035142010985004d0000c142e95501102071030052000c080c00151207880b6580480e007181c140902a03414003070303072480c01c03035500e820078000c0c043d84031304003c00425060054429a2001c00e01107407154051480d503102654070303500103020140041f40800410300090640b40055016030300c11056680700300040f00840c1440322741c0003410800c1500388110f0051000e0000705a8042e100100d03602a83d0751103289210006003a216141038009842d2020000c40c1c58022 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 83234776 1250 83233526 83233529
    0xa091b0210110706151a0309070e0103120507050705060f0c0105090606010f0c0507050d0b040b061206150105190f090b0c19080c06010314010c020714090405101104 72
    0x180c00301c40c0151151503000701038422516001903000d41c1407140b070000c02c1c019000110f16410040c0b810700025218003501601c0c10904a030507200e00400014003582c0c0d542000600002c00c00c15058098035411686d030350f80e0b07a05169010f40d00b04240840c0110030f0160500100700180f000400d025903071280c01c2c00302186500000410000c651825001509241c004912a449440b0594500880d1007610000307841400f41c03680241c0c1c0e6803240210108507500c4000140ca4450b01608001ca02440c0030b15018000d0080103100e54021840e625a59805030000a005604000e1340d4684030624003418004031142e004414002d0490340c0382050600c0541c1e0808030b030b1503c1040c203694502c009601d4140e0b00c415481180c0b040d403c0b581c41710307144105101da0300e001010303400d101d0300c0d4161514013041180d6150080a030001e42e07041c0c03184d0b0040d404502c070901c80d204c108405400238291799403902110030034100c1e40d141c0f034a005489160019003000b2041c840e02d0081134542e031041005c400c0401500209070480d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 83236026 1250 83234776 83234831
    0x102090409031101180f170c06010b13140109052205040c0302180106080c090a03080d050f0106170f091e01060623090409060f090501050402150c07060305060a09 71
    0x20650001010003804a0480c0b282d50001e980e0b2081441c07035030b80d07d0034000c1c07541205040c41e07106001801020100380056802040065011a1075080002d01807032211821f0303002c1030100c1c1c8803805030940b5036007180018044400481d00e001880410840c004010490071407512030712454101000100482200740e0003d89000f40c0d1042080440c000d4802c0700000c0a004400100f1b01a03400540c04020039130040410006c081c03c800640b40d44ca5503501d0403034000180d010410b9031a602002051007002042e90300600851500086100905c180d4040b01c50001d000c1ea440081c0d4840000c4910004110340880d1807854011060084e40400b5100d00074212030144500003000c4500c01d403060803c10170b5002c042c894cc0d50455103098142001c20004140100c000c90324a52101d1444280d61070380c1c03244038042402600040b449140c1031041201c0106000800080307002c06101081a6803400209030080c0c03120350400243c25268580010540f40f00c40d030180406908200301c154000340740d03a0050020310304 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 83237276 1250 83236026 83236031
    0x31e043204140a1422030315080114060103060605070204020c12040b0a0809060402060306040504020d06051603060504061a0a0302040b030106030608010b010e030d0c031e0f09080a0201080402120102090409031101 93
    0x40c5582503000031105440c1841da041082001c4030082c4041c00d0b201180d40d209050001c3c5148d07001c0a07105114415078004140760755591404100072158001207503100b1000d19040105608001c8050706c2400f45c00c3c00079000b1640480d208040841c1040780040c13229881da045070b107540d55403a444d00c8a91002d01031400141c401c0c4041000f102d00040d040d80036a600a01e00f60565440000340401000010010b070f0f441800d4511103004200b036071191501400c81e14645200784081c030382c03001e0141c804640c0080d00492500c9420030654000359440070385030f801150f42d550703141402c440c100d019000707641084661000c00000002c510381c02d0f030b10980484004000038086910740c00019030341d02c008a0001505a04401c001194081c07144205103047c610034109000306000c54207030308020340c040000100c089036015030070181042d00070f000500100710040c0141900491680000e0980307401a1009005046c2d1843c1340c5280300f070070740689800740d00140c410401103d041c24002c20745a21007070021403651 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 83238526 1250 83237276 83237291
    0x52a04110913060e01030b0903070f080a09080606060703050a09090c020102180d020a06030b12070305010b03070b030702032b0219080a0c020604080702010917031e043204140a 77
    0x9425000c2e420807100742e1000e10541346c1c40d5448198444d48000c001902c540003c009120002c0c0101382e44101031800341750400e4841101e50405012000c0582002540d50321500802c601a40c1c4d8a044850450b8145420303074680e196400c054035080e0755608070702d16890030442c4415000c0d42c15805032140800b001a4407441800c80000e0118002d0b11240194000c4090007042c0641d0703000340c07c1442c1d29080a000544c010b03421a00706824024070390411510f82e51182800d00d8140350030441d40003d06020071002c1e02c4c41c01c1140300a9034911407090f580c051100000400c40140035450600101c1e820325010541d5110145001d03032151107071842c020404120911b02050009410b88038131002183e01c1e400400340e5844984601400b03130031400040781000417400300440c41c01e110402c041a1480854015038480002c004c68030080143e245031a64014801d010030410f030100420244620040e842801c20f1441c0300501d03580c48a030640118607000ba061184455140049250b42446500100740411149 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 83239776 1250 83238526 83238559
    0x291e0a02190f1b06090b330f04020a050324031005060d050d05030711010b01171b0a020a030314010303020a240603030804021c052a041109 61
    0x1e00640019103803502005032101003003405002c40e029021003600305105400010040003200d0307401c080701240c0071520340855600f0030080c02c102c95009001c85011165208185e403034100c5035036010014405004a0480c415910380b0b50300400701c400100a1300640d690340103910054029441501c8100183c03584881030804601d180c006607402880040c05448201000350700310010700409031003647e114112107141c50000d5030400c007210170402d081e200c02e0340740d14180704083c01c0304602d6101915980d041020784c0c03c1503170f806441d190650688410f0b101d00c5ea19403080e00490401d010710200b5a402c0c0025204060507000a02d209483c0d2081c1e0b414030000c4e108503101e0000401c00e200050142c1c0c001100d05c0c0005206d40d84000c8100b040d1303080c1c0c91145106043e8102540c01c0d5078010f130081040c40003072000b0342c200240400c000d46960340208407036030140e035210740e500d003500b002c1c0290901440c2414211503414040310406441c0003002070025070809082081c260340064101d904c208a41195000c41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 83241026 1250 83239776 83239781
    0x40504060e1504020a0603150f08070503070902030609070f020102070c03051b010201090c05061b1203010603060b0304260405090c0408011515050d06030602130503010b010219291e0a 80
    0x45030301800220780c9620307064083e4090112085035023511001d070349012801c0c2600501c50402460f04200070f05803a0301e0301c41418201189a045050402d00410801426880b00800c036074000d0781d1840c3c541a01941d00000700d0083c06841002004000546400000d01400042c4800740020061044650203840e00043e4222412402c0041c0f51400360a020030052901001030091300c0c03d103042c009540c83d202d400150a20b0186619007010601c040014010183c1c98072402c00079001c6d4044d100c0c603500b8161210002401d070b1801008541103c0404c01d1500c1c511401a2001440042d04401803803c052400c8242c07600280548003a0303601e0010030007030240c003110380c0c84202d4a0591041d06455042c14003201c4a511035040c0340700f415107030700f0000002002440105a8002c98070305884040e400e1904040c259070310b00014504541c41541c41c512008400b6030500f1410391300498207107014040050302c0d50341070000312140105050020402c14050066000c10540e4020b145882c12540c0d60035603400e08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 83242276 1250 83241026 83241031
    0x10303080919110f0d030906031109130b01051903142a09010309080a030b03011103092d01060e07020607020a030e210f01020a120203070816030b040504060e15 70
    0x2d03560b14031150200415002402400c0591001c0e01c0c1c0d5100030700340e4020034801c1010907821000201c074045d08000c8603505205803e60b1000c00f01e035461038400000001000703100b00000c00c0764400e81e01d0402140582c051000c407001891000e806000852180e00050300520f4007007090207244e03a02c41c00040b14010411100615520504091125040c1e00d4000c081560040c0180a051580c0e4941c0a000301d044074000d44188002d039903001c1110341c025001d140c07d5614200201c030b810340040c014828211008034407281c0303c2c4040e0200100c0358142c503581c0340c90300c01954940d2070294a0288003141104414002502c110419000ca410507220f0100890b035584071b80300050001030b2810710380c020314036082c40c00420540a81050004d0448820001c0d4104220031008600380c0c1c2d40083c0c2035044e90342103a02c42e024840b50304402c50841c40e0220001e0000c0030002d00400c80c4a00545062141034000d5110b0740324407601610030400380c94039107000c900821840c088007500384640d2000c0ba10001c00d5014061 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 83243526 1250 83242276 83242303
    0x17070801140c040b0703030b0604090e0f0a120e010203090907050702120c0a17013306051206060f16030504030c0503010b1806040608160f050d030c170913050103030809 74
    0x9250030704e40030b001d0109401c601c0d0101c041585406811b0b01940d103a8000c3e1000d000d02400000e607900408410354908031000d02d410485405c500d0311172000c1a0b28884006442c18036061083c000403d0a00403030031031142c00550303a0300420480900c45441d0b44200034090003442a41d517004800e1802e03003066502c000d01c5916686c040c202010034018500d20101010445401000208440c1140301092001ca4000304803505c8500020159009500c80c254021005042605103145800018a0942c103405001040b00340900030000d5002c1d1042d02d0034003143c05050281c88680000055407500a00c030313600c907100030345404e4030084020626107410700c030b60455248014203821a0510707800401c03c0da40310003490141d21a5450100164080d4184204218030511010352000c840c00c0501400f040d00003034000d14000c1c240c0c84110300000c0e40060811068030340019041a50b18a88031814502c0d20500310190340007051150070304459041a00001c3c141e030300c661200c140950f526100c6655481d01001c010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 83244776 1250 83243526 83243551
    0x91e01051801030f150509010902011404080705062101060e0a06090e060f04020405060d02070210142b0617010e030a05120c091005070b060a1a03060a1707080114 71
    0x1000010060038480413003d11a03d41500010040081c50301220000c4814034543d944030348843c411036900100c3c0100d03000b00c078032507170341441d00b00124299200c0c41c50107850700540000a01201340624050a280c0c1c41c0500e0071103110b1581c542800070030034505089254003503117012030b0206003c3d000d045041c0c150b44860016841944d208800c02c0140c08a194103580c1041e03003000045559102c040003480c10351683c40e005681c81317040b44103218440a4540c0a03c08204540d41c0e90080c0d0a0b1440458207591211100d4441401254071502205807491462000c0c4616200c030010740401c001c4181c0c002d07501400001c0044508014038a5207a1280140540000710100010354825180c1d0300703119002000f80b501a818180710720045114200200715103401300b400425804100a08411000c1d400f0710180c90003c0001c0ca088140001e841c0c859844000e9403902000042c540e4a40d0030401006201c00d01500c3c17104141c01c02c41507218842c40c0203060303913942440111411100c11800d4680502c42c1444003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 83246026 1250 83244776 83244779
    0x8010906150302070212010f0207151401032009070801180614011803051005010509010801060501050a1b2301060f0b090103020702130906020306130c0903110f091e01051801 76
    0x40b0025442004100e921000202131a81d00389024412540000b1a02d0030050b80d03000181000d10740103514450781800340d42400e40001080c0080e901e00c0c0e0450790300c0b01180e00a1000f9904800f0320302041614075070445048410426003d5010080904896805030f182640b40b181e842e1032806c0e074044d40503288200f411128103035a654440c4289030341c401100c2d140000c65a8a903902d03c0c2c02c1422174030103d070f0580d4a03140184451300c0c1403410700d0300401c449402004810300e000b00180c21805840c00a03028000f009210302a186040c0050240c92684541720300d0308035481d440c1c0c503602c4860f94400c5e04020340c07034202d02181d00285181c4440079a005400c40a08102c80390340110045c1d484000c2c101c1c1c025042c000c2a00965103507020700303803005203e0b03180903072203140110500805c040092640004241404140404640c10440040c1502c0d004408819081000c0e404600ba840840300c0007070b0071600d1070040082d02c0c929984050301c040450300ca0340e54266610780c02c201042c2540d9040c01a02d6807070000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 83247276 1250 83246026 83246069
    0x60f05070b0f0901020706020c0109021f0909051503030c010c120e03041502121c05131505100b0a0314010f0501140c1006121104060f0e06030307050d020d08010906 72
    0xd0b41d4008900c200240c940f00f0b43d0359444050340c00064501c5003680d101c40c40c0703904515200b1040700d00d155104903510141910900010510b80c824801c80c0e4031243c0e5800490f01c1c001c2a240038038070145028007181d0b9540071058206001302000302000000959100402c2001c0e021805465a50303180d1400450605040c2107001d81c900703040300c59283c194070900441c0b0800c40b0312000546600000140d07901805e8480c400701c1d000303440000b042401c80c0c1d02680c08a00c0050144408108004402400020107a444460150000145070480f00c0f10080202c0c00c081f1080e0300d600404c0303500c07000e000410b6843c2d176504801c0da03888240f802654007150b80c001ca1400d51500f010007400314040e200040742c1225800701c02c4281280d01981168510b4074460104009100450002c1040d0403800c0d9810841986804200c0210040301c1c014655030070380345008a80d6555080003034840c1290401d0aa0704c08002c494000307540d49800204600c08036032808000142e458003803184c54116440300d080c0740d480c442c0707401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 83248526 1250 83247276 83247301
    0x1401030317160e061602090405030304140601050a14010c0204240509060117090c0a0b0703020c121e01020d0204080105010510050903031b160e090c0a050d02010c030917010204060f05070b 82
    0x31100c00040c0901005170002d81c0d03918004901842c0070302d01640d500d0505003404150004003805151303c59001400411094a0b002c0212045600f07007003000f90038006c00d10040f02d611040307840c0a54014104190455241d03201c869840f0813202810386159180d6491050242038030040340c40340e01040c0c8921a801807007070440b202c0765124200744280c42284010000065070074800c1d403c50380d004003022510408050701003002043c01e0108484000103101084c402c0d69540707040e00701e158201103520108112450f8250192b2300344201c0c0c2c0601f591140e486460b914020002403044510801c21030503e8108240214200c807181007014015503d0016008075210802c1896084036849100751400c2800c01c03403a1000c408050801c60108807002d05003c9900c91903c6808422248541c01100b03080019988a410a401503542030915440392282810b044d51507039029484508503141600340c01401c10010b40c010f0007514107a0315030340c0300841040c0044980e40a4440014890810079000c10080b10280b0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 83249776 1250 83248526 83248537
    0x1150302040b0a17030a03060e0906010521062406070c090902061b060f070207050901090e03040308040e1017030703081b0a0216120305030106080601031401030317160e06 75
    0x5058940d115656820b0310340d4021004142c1315150b000810342c6940303941d040c01603600800b00e40b21500c8940c240002081d03181c02c010310803c1d12a0481c02d80300350052000d40d0b0101469202181a1015441c22218841040210807401003d825483c52031a045103051000d03914a10342003034410503501c3c00d02400c03000900d0049400e0368800014450f01c184d164030580c66075140b203031281c094401da0500012089031640c0c00341540c0c00755080900705206c5500c500800da030440741642c801250130346000100606520030740d003025184141c0054081070340d08002c044240104070040f10312003103d5840d5540404109c03c0d080b0100540c01c2001454082842101c1140d0880100e40c004564110105290300680c0d200c0c540000c0560040f0b85000c1c0301341d50640341d241c020055000450f19444007aa4001d0840c4014001c90090003400008905183d1103644058062210304031000b526584a08001e0000d4665070f95624981c1d00c40000120801e0046441078450742c641e4440410404c1000304011141e00003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 83251026 1250 83249776 83249779
    0x3090312020313020315010b3702070608010603021e0c010b0a090b01030609090c030f14010204090e010b0409170702010e0301091103060c030702060c07031106010603020c010b0301150302040b 84
    0x14640340348031882035200440c0a0b01600e010651481050b01c10b04d03060441ca051180c0e2180c0038030004202c0d101c4108111085440070440c0c01c00c404915000000e00d100300742d003168000788100c48027170103e260001044004d440f41a140e4005903a030300c00e011420b80c850383c0e109034170b051445510545112203050107480600c1c4100000b02d11540703104045000035000d0391100d408241c9074030790054196010f108442c040d1091040c180710f041e48544a0215014031444014100481c02050900b8040060704145c81c26030301400a45d41c941e62102071901400001d006c8504a528281590741d1500d4284540c50195038080070b11050f01c08001e18803441500084c4047c1d0500072819a22002d940d42880f403444445e00c95040881e598200ca01410b24000303004000070710411081052043e0760b600020303026071103a030403040d1a0b43e0750068901201c00b20111080b0200602c542c0d40085082070300750b00542170800110000b08014909002058280c0300320030141d02120f8200c1ea0280b0143c1080d03002420754250 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 83252276 1250 83251026 83251037
    0x2a03090c040f0209040e060606030c09030a0b0a0c030b010c03140a050d0f02030405121804050c0705010203090d300209060403050a06021201120201020d0f0e1c2102060106030903 78
    0x2958012900307840c2d1410a4014155000404c80d00500d8140f08648406142800a01d2a0700e02440480c5c40d5200162034200948004500b00700c156604000c10545550311000c0e58880c1e041802600c0701401c40180305e4800b1905001c44035245520910100c1c941540566400700603001c2c040c0c04c0c06040c8e004515040c1000360803c18500d483c541401080300b02500d4102c01a501e2230036050180c203210ba070394081d1020030070400c00c96540658030051000a004103d03400a142e0300c9800c110720a0340329014004050b540040208484003001160b00100301071242c45414608284103c046064002519000c2c8200b400310f03850302603000070b41d024080c4040b007e4480e5140035200d40f1246e20b082c01c02c031000c46019400041a602009510584a0060480c12041000e00100381e00107074540c0e080c204080d0412403011803207201c052003002c02c09803000001d005403010b24900ca010071491300e0256000d03a9030384864442d01290780c0008203120700315015980a01200d1742050011400760200d202c05808125 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 83253526 1250 83252276 83252293
    0x2040b06071b12021f120608150109020313060506121c0e0102070e010501030f0f110c0105060609090402090a0906021204120206090606010c0501090503030906040b2a0309 75
    0x44400c0001c1025500407100705002000780c00381440c1400007900007100c0188164035020058456034650386861424011015074485a01001c0725020030000701c80503a5810f004000030721860111b15500c0c107980385024210300d03a8135810701805a2100f035079100d485a512540000208000343d11041d04680c00038581008101c001000301c0ca8a8800d0316090ac842944d1014040c4942d0802d042c1e900b401020f001800308030b8901106a60034440502c0b41505040c0c540d0020020320343c095112620f8250a0942000303021000c40c04454141c00150201d511503280401083c054684803003525900d12008014801958940d803c0c0241c900001d8041c059242d101c4c0c07099400070345c460010f4040d0300019030749100f0341e19003818445031610045808030150740000b424485da02501007001903004000382407506010a482c1b41403401807541c04809451030002009001581202003640c0b4011030041d100c20b2102c0e110300380154081214100354480e030001140000c0c2c502c0d08441d002d143c0c058000c0c416224800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 83254776 1250 83253526 83253529
    0x5090f0126010e0112050604060c0c060c050901021504020d120216060f080601030e100203090307080409060f0e0f070e120a03080604050108010209011202070c080307060e010c1110050402040b 84
    0x200c1040072003a566101d44010702c9034078498205a40103000081e080f0000c0b000320303102c844e00c40a01820240c80181c0f1280741d200101d00510701c0d51101640f00000704001080450010040e030440b0100c980103000302071080100c44105280d0f5406142c000303007031012030465903a0b0400d0b02c44203101c400040d402112024100c1c02c1060008074004c3c926610340000f000045000103151800040455060520b0310324040d25035040040e0180c3c012411a030700507921346401d100c00345940280e0800a00400d40054007140b11072450704000111075001203501c4500307485103041c501d840000c5828505007031403040010740d01d42c800c000c5486641000303041d1448699803421072a0070308440394800c0d004500480700780203050510b44241401841100021400d01d20240002801000014040300740e56070049175132018881c0b4010440024040780044994070b814034540034000c0c1041250b0300c00c440d4a8000b0829440303001e054019030300c0c02c8400103400c12201c9943d40c0e0f00102006002070740c00550325002c2c10b40c035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 83256026 1250 83254776 83254817
    0x6201207080d20090d0c08011d011b0c0b10051002010902010e0102010506010c020d02040e06070801090b03120306060c0f0f100f060501020a24020708090f0d020105090f01 75
    0x2103405504a80d903a50380703400c2900282c840348000103d4060459645605004002c2c0907216000c5040302ea14038034a400342402074003c6c60340c3e00085e445518000000010342d98105c2c500d0103d130040f20081c00b042a203c8034a003403d1440395225408a00d403840100001801014082c0d400412581c50035820780d103d074007080c22038023001100000f60f036503213000300f0556030844071520800b40244000d000c03a140c0840020007070f5003180c0000340103c0480700c88104640d2242c1007001c000d45104200d40c4286881100100800c07002e200312030400f032a04032441794505022402c03a40350031b541c020382843d64894105001d03066010115014141c00b80b01c01a071003651003031001c011034005503002010100d44040358802110f400828031200c8500e0303c14100405d98020400d0403a694010140380381c41d01c0714200f603241103143c2d182c1c1942c1044c4001074000400120368090300f905801070310340c4050400c2260a11940d030f03001f0b040180c01b1820074000c658071450300c4482e030100ca48040c0f525100c80c00380351190580307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 83257276 1250 83256026 83256037
    0x1703160303050603011503020a0b07031103130501120203010308030117010b0a080106181a0108040f0512030f0c090f1c08030a0e0607020a0b060f012a1506062012 71
    0x2900c4000b8040640313024020300d580f100d0a49010303000c03c4d1a59000034991015441005018640030a0702c2c000c0c0350191001d0403802a1010549640e145141110300c0200900d0284030301080c02600d41c480349600070720913241070f69440460707545035908040b5000101821606d90000310342d00d4500300320080e210781000c1c030020400403001145150400030189401135105420901042c5011074070800000c1c48009410b80f00c80038246010b186e00c1e1402c1403a00b1724000f54003c0c1c2180300d40e4020880c1d422216008610a000320840c0c1d4002c2d03200c2c9280302400e03210f06a00294040c1301241405264a4440090300ca401a00082c00309013072466520700216410403200510980da550101401401c4144034655201840b44054483c1001eaa0b030760508015001d840b41e4012154102414201c0e40902c0089508001c0b14280b01800c40c04c0855044800711404400c6440750401c4e003040110401900071041640ca450300d458000380e40c4c5c9007034000b8004030880c1c1c0c48810710680d04003c12400c0200c00414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 83258526 1250 83257276 83257283
    0x40f14011e18030c020409080f04060c03020c01030219210f060815010806070309020a0906080f010b122104050a06091a0a05030f04050a0503030a06050415030804170316 74
    0x1001e09880c0c407910100c8084407a041c02410700400040d002030b6000720b6110009904640018120049040440b540d00856600d918014400100030680f5034004c07490404c0c041c03180d4201c0b0b640e9118100118140d008103141e04d1514240704100c140290f00070001e40c20700c1c02c0c0690b04030543c859110200301c250740407030140100301c0d03654030418004030800f48000c0c01d038440d090705103440079454200c06a940340b000900c81410159a01341060841da2003400c40700003444180340a21030310f500e400f42a605c414803500200f01e598602104014141842d440005944bd91000502040080282c5034041c3c5d0b00990310f031200c00003040101007031507650740c407000c80505a1070b038802c445a0306181c1c0707605040ca118a200d00c03554400b0301031039103225840411213910050000c0c4040790380e1110310b4108d18104c0c0d4031800030030a00000c130400c5800d01c1d45901490807a0b50445062000c1d2005810b1414154030348c1c00080c1103403900700301c18850342e0781e8401c00520a040300c0044a03e8824107811076050241194401ca = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 83259776 1250 83258526 83258561
    0x1803030a060305160807061b051006050f0907210207050601080319020304050a0b210705130b0f070209070908030d1b0305060310050a271403030f040f1401 68
    0x500a12508005201090145005043d405405d1255a540d40c041e0303486120100030341284d031a005a40c005005950705a400f074100d41600d509103d18102600c0c4a0003081c0c02a4115035690301305162104000c1c0c001c2003e500c46100641120102c0c100c00c1c0340c4010b00c0c0b0307680380d020000700300020010050309000741540c40155440e204e4891681480307208000009085603c280000d100340d0f80c54220010072905005512a0340320040030103403019440c0c80c1000d090000c1032104009605030403000a1036a50040642100c0c0c9907191a80a0114090301c00f0b18000c001043c03103001f0060406120a9400c841c040c241200c801d55941c18040c515807000b901c14003215101c0804002c0141c1d400d202c1d4030b4401050070180b00d00e140100202c5d540320721041d0551400c580340c802107000c124659100e100269010440004650b00411070003004081e803201c2110602204884245d200c0004800d0b00e010350004003030704405407101e1b200d02d44c4024150006554090084090501301c6100340720b021001c03108051314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 83261026 1250 83259776 83259779
    0xe130218070f0203070c0b0d0f0e0f0705010c03090513090b040f03030506041a09070e06070503040f09151202061c050403021605010c060f090f0b01080729031803030a06 74
    0x14402c001ca00b0702c01003954018060003000074180710641003551182c0030755a80303581d5078801e2907014150310078010700d416103032100c2e4001071400498181c1c42140503400f00c600043c0d58100450700c0e4a5038010140014504c54014840b51501c49903098180301c1600020410b242203840b031141c452010740341190043d0018000300c04068050180a1340030901b104e0800c948a0890344841c140850704112521500c0c040c0001440140100c850030442c20000c1c100d141c40b03106601c0d02a82d2580103024201021655500004e111490740c02020180305103480400d0904d89401c0c401010452107110403030f849001400510000c82c083c128960720441d90180202e82814141030190034500510b04440003943e003540c06126998114000e004469882440010b0f401c0255003500000e180c0018020304c0c2b82d80740c282d0f140912101862160684590005640101e5580d0480c100034013801c10301c08400700e006071030500040d4100005581d001d00e140b0990389000b180d5161a5085500454242140a0751906c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 83262276 1250 83261026 83261041
    0x2040e0f1501050d0b01020a17070c08010b0102070512030c060a1a01020c0108060f01030b0603100e070507050a2a0305030d0f230408070b091c050a08010e130218 71
    0x54010051021200c1c6010703420300020024459148443c99850701e405900510380d20801c440243c00703401200c100c01203a1441c0c801040740c0c1c402c5c40d081c1c031840c03e141c82c0441c2c4c00034188500d0b04a01c405030020a42903180005202e03446290b00208140b03400180b2442866100902009100341400000016001030303040311080310417031030b09109046500444c006203083c0d81100040360405030071178160300e0f141d0140004070090b0110b00d9100c0c0d0004030100600c82004540400d0005651402c0c4442600c1e07903507404110703818094006d008d00907a200301c1e0703d40045500c0210001c40b984441c041264100303200d41c08a1001c800342ea0048070b541d4000520f250141c01c4078450100c100c407440b001803215594040e130103003100e40396076911310686d072503003011a0400c8002c40803951010342c27008101c001840e240c441c0584495400c5140304020945102024046100c0c2c003c1782c2040000703131074110207030b4200707088160103003402401441003148103100c0e180075130b8907240048031542442c01400307401c2c80d0110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 83263526 1250 83262276 83262301
    0x1703130e0a0f09030804020103020c010204032f0108070507120e0d03090503010f0c17100509040c0603051302281d09010f090503030c03070c0602040314070f18091502040e 75
    0x20040021545010403220019610152290b01b04d0780929015032100d07100650307a8024455588020107404c0640e120f410f1030003616010050091401240c81c0d004990400151083c410494580d00050340810540e00001c002a4900d179450070030b1f1610b82c0c0603000da04003145140603614410341c08152101d00400282ca001d01828030f041c0c0d60060300b03001444080d003001c0c00f00260464151606d160359030018008402200074003004001c01015000746050504128030003040c40c1c000c0f080000c0c02c10000605075a1180550299650b003c2d260140610f01c0c10058010390ba00c0c00b0b00b445c904580c20100042c1032401101803040b8030507000710002076050404001b0308450242c100c1e0040c1e24144602c04000c2140070040e2a40440742c10102c9070383c0d990700e00088422800304100207105900c04200401032160010403c2c0c0318044a070701f298046911405008014803003031043e070400500000c010b100010703498000c070112500c41c3c50541080c0c0381c00c002040a90700300d17400080062074401c0c00c0007419403100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 83264776 1250 83263526 83263541
    0x110909161a0703030906020705011113050105040b0a05070302010b03070b0a0e0d050a080a050702062109061501030b01020a0c030305030624030402010c021f020601090f0b0a1703130e0a 81
    0x68100860000360301041c100380907400c40a8281540e6134041c20510205030121504c25502c41d000300030b40d0301c0245410481e0713005065503910301c03403c0c2140801d403035004004640035520344d12181428594004800c0300c503940007540440440d5210544c51151751010880b038800741c045690907944070f07160200000d0030b13000b0405071a4480c0d042880a4004540003050010740b464000c1c1045946480810301a6803500c0b441800039000f240014001034001045048023084410003d044801601e9040c1c0c43c560742c01e416201001021400304505102d9030080d4050206c1410600660700600b0403034682000010a903441940441c00000c00c10103d46400c0900340102000c0000440300022203000701002d42c040100024148018401040107541d80c00c0d0302c007840c602502021031032881480400944540003032041610a600b080e802250f10702e000e0040d0b61200d00040e11518030549800f20702c80b0017200e000300d000c5503030104010201e550215180c0b51406020303407140442007401c0a1480300c0c00c5031200d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 83266026 1250 83264776 83264789
    0x71a0705100b1903121404080607020705090603010218040f060e0f06010f050301030b07031a06160302010f140f04020103020c06070e01080703050f1819030207030b100605030703020711090916 84
    0x3e9043c00c0c80002c0f94002c08581c0c800b003a14140180e0325031380307904481c68071071504081d285110340d8007080403070355001900e03209807241555890744940f01c0318189422703800780141524000e889041c042c8154100784e4002090748a1007000825000d07510014035000c1e14090b43e044003201c94001c07c200007560040314401d400c2c0803d1410510b50f61442c1c44010840720050512000c0640760120485c11a15005280328180300007455140d403107250b00b0400003490003034041103000d0b5081c20110315a240140c4509607030b140a40301c454103640e41d440603040b04880020402c030706040e401e00c02107180c400100f0006110b0313002600c4888510010000140079003e0041400342054103090030000c040d00d9142800f40c0040180b1021a85400c440e0301c4079040982021268054100a141d204240b590003e801c80031680141c2e00498640c440384110110407200303000c2c103004200c041011a0032a840795008045860241140d5a405040100010036940041d82d20102c10392000998140710054101200c00030601e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 83267276 1250 83266026 83266069
    0x319050d0b06070506070c110a150306050a1802091c080304030e0405070c060e0f0d05120610080c030403090812120f040201080606070c09050a0903020d080108071a0705100b 76
    0x80f950f90b499940c00c1c010201002c0180c3d5280c0c5c0420450b15001c58440c6403c014203100d03513951180881e070b0001d200001c1e45800642401c0000031541840c40000f8251010018840180341400c40b00740082e510019090b80c100c00c038a500d44410342e0454007440d803102d10981141baa170f4145800c0003402c03600e50340401c5106600d0034041c00101a0040203510300c0e940d000e00e020802d4401c240d40d850602401c280150454050030307003e00a01e50b07210b001499841c041810300702d038a0301d8103001e00911001000220380811100c41c0810944031500e070140d6449886850003074452030b00d40c09500e0404140c1400100b1056000c40d0040d64a0340c00c0315080c0d8800ca103001030380803615154000030003503c0081d00c0180111070000e00c4d107091041560340303800034ec80c00c1c031002d0015003002c20340d01c001010703202000d030f0050041c440c42c0c842141c4500c00881c101c2d00c1c0070000b019000d00340101400c20a030301a2400c0b488034001c01c25500001d40a010200c0f01c1911b039400017a044003040d0900c000c0c41141c02c11002c2d02c1c0c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 83268526 1250 83267276 83267287
    0x9110a0602070f0306050a0e0609010c021905030406210c03051e090a1101030f0603110108070807080613020702090901060311060403031d04090c0f031a0106020a060c020319050d0b06 80
    0x40002c0f4000040341d130001000b04290310740b00b0343d000003018505003252440c01540104010080d0540081d040d1500301d03422640d080c0350400ca402c810b00392035400180703150400c000c01c01c55144144d40a41c41e04d106201e00c01c0d11145801d09a104680b05121180c0210740c95000300301b103202d40201003070f201701c4440d006801203141c40c603801c0391200300d0b10000030641e8560103456107150744260312103442215030100c1007040c00e440742414800780310782c10070003400148c24000003090188124038542c021703210350711280100d40b40e001c20041d403e820a0b100303400d440d501344807013000742c1e03203403040c180c001c07041d07078000140c413074258100309110364000460309000e464108400c000103940040c546041000800c0d010030017603501c100040c0904034961014007000e0071188003003003000ca00c80f00c42e0112882081c032041741c2c2400d02812a4066070920440d07015030040403d940c0422140d4000d51031605080c410b0780c0c0703000000c00401130024145003904000410200c0c500300e9803101c44c860042800e2017260281d0405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 83269776 1250 83268526 83268539
    0x3050f01050c07050319051b0609070602010902011205070c02040504080a0e04020a17040f0b25020a020a14031005010801061409010b0421020402160302060a060b0d0e0c030109110a060207 82
    0x78071407100d01c4600306c0c0d08000e03414107051140301640e6484414032030303229421945180c61076941c2ca098400c98001e010754840000c0321401485000f100e1307039040e1180041044401c06100c01002d00510450030b106c0030f070501e4401a511486200e02c102e20a0b5130b8151101d0070100010075500203001418066841004550461034000d51803001c048500009102c0750f40d00d600e030001d0010b000000c0141030701e0340c40091010b245100303110407942c2840541060072031000380c0c0d004c0b40d44010f500e20194008000410a0000060b0146182b1034814054110f52410482d42400011280700740e01a10b0703280d644075800c1c0030302c42d01e040b90a000b24400721684e40d2154180704005a0358481c038421149650b01c2c0030fa604000034080c1e80070402c0c20b500108119200c0031881c0070814103011503041100103014000016020744400e00c138038025a80440440d50601c045640e40a000b4501846601e21911880115003415a400d0003456034180c450b0012144e1a003140080c410140140e40004040d50000fa40912a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 83271026 1250 83269776 83269783
    0x9010b0301140a090903020c1504140103090206070b01030b1b070503090f01120204090c090509090a02060d0917040e0106050418020703050903060f090f01060803030c1803030403050f01050c0705 85
    0x10b492005086001804200b8009210035209900504d000c5080140e60703400d1640100300541d981d101610003402d00569003141041c01e100c3e07805000c1c1c0071281d402514400354031a510032001184050300407440d2a0240d151490051781c2640104da06c900d1000420910b1800e082c190041151000c00080c2000902e070f440944034001d1212660040b258111510f096a1082c103a90a00b4004000b00b1982c2d5511102c40101070000780c007066010802c034203000603007428030000c036612910140000c1c1060404940c20007142c1d501003045401c03800d0303e4840e80380c0450300d4184143c81d61860200001d80e610700c0c06201c508120340503840302061100030b001c100801440c10000840034003c181e00141d60b012540303400e80c1d5034018401a01e816200340c80c200301c0d02c9800c005200307020701c0914003100c14544c48081c91501342c07001d50041175404e402c2800464803030082c0c44080d00350b1007540032140d003003c0c90350030102e072858001d0b50069503194004c015940e402c0348280301d001d4100901954543c50714260f0f807920784c1d9 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 83272276 1250 83271026 83271029
    0x20102070b040b100b0309010b04061403060f250305010509060103020a02070303080603281109060618272202011704030e030f0d030b100e090901110a11010b09010b0301 74
    0x1000f601040010000c6400c580048007a0011621140c1c4074102131480e00e0003002c440e01414010703880c0a1020a20186000c1c3c6000b40c0e0800a001f001c0b255038040c3c1030012440081c0c1850b15410005100b0040b9030981c9181029901d01c83e900069650326040030030482140c0a0100ba0602d4030410030235808940c041003810649405050018464a8500200c0e20301400c1c1c480c0715007058200510f1080c480304012160494030f0250740004240843c1c0c4082010802c41560390643c801d1003000903040d00c031070394410250000e100404c103010001184208a9101e0024118200c4950301c45080000042e088070307041042c06003405400c0c07590325070703980081c0c0000c0c241808000f0312034201000600301807254008030034803100541990110007407841d280d90f843c12a0800c14010a080100c100401d0402000c00c0c2004540b5035603842010351050248500400050218002c554846030b410011030341c03450050011000903654405400d022110745800c41d02c111602c50721404110004016010751201604d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 83273382 1106 83272276 83272283
    0x50a0b0f0403111609090204020c060c031b09010504170c120d0f020f061b04030506040804031a16110123010e010e010308040306050a09140a0c06020102070b04 70
    0x1601d40103450824004c59528040c204241102d54010038140c03400540014a4422011784d02c1d418500b00315814407c0e6203000050194080058000d020049440e451450078001da260000740640300d1071003001c400709807419070740030803003002d0103144008040141860742c0303201c0e00c000c85500d80c2c40741040d500100e40c401200603101c0d030000c5003040ca124101800b5014941d907401c1e00c004080960341943d100d211092101100260003040300501035405000c4468580c0c0c550f01e0880d844407106005510f00e81a41e0301401000001c80c1d0002d41c8880c098100307000e030f4014102c0c1441c010014485000d002c140400b050683c0a141024040c1c140d942440c02400030340c1c0ca0b01c2402d900301000303100050401004110404c0814400d034400e603001a42050042040000c0e40c44011000840c1e00820845401c500e080784d00b04260756461100401d0180002c0d401c0110350b403100c0241000082024 = true := by decide +kernel

theorem cover : BRFrame.Cov 83093526 83273382 := by
  have h0 := BRFrame.cov_init 83093526
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 83093526 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 83093526 ≤ n) (h2 : n < 83273382) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
