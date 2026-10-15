-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5399
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:44:26.771492+00:00
-- url     : https://prove2.me/submissions/d4a5c33e-a087-4a62-bb4c-18c1a3f41371

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 970863309 ≤ n < 971043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 970864559 1250 970863309 970863329
    0x100507080f0702060d090f0309050f01050d05040606031e02130b130b19090911030706020a120903120305090708070f061d06221220030a0c060f0e1009 66
    0x80c0c0180f0004403030380a40250a190a840c24450b03000340301d00e0400d0f9154240c0283c451b4131a440d01c60051021a9110000351404190b041280c403004141e598025507100c2e001e41e01c0090321a443c3c0d0b42d0402d10800303044410303020011301c4048030103610301000b00403003001c01d0030303400c0000b0820f030b001141c540c6450b900894900355035030301c49030700301c0d107030301c0084980860302c1a010b0a119490740350751001804c9940c1c06543c01600500006054100004c0810a403240c580052041d5501981c4c5e4028549040c0c45040c100041018004001049112480c1445200c0c2d14040740610340008030500c4d06070140d00072034079039020000401020300407002070016540b05280c120300300328140740c610b11181004808141c00c80d00010740d01428a11302e02120086035416a84540c8555031100400d24a03800c211002c3e141c10041245906903524807008182111030240a9030814581c5d0707150784050001035480318010070811803500000d00e40c8000064010b140c00c48068007401c1990800410340c03035080c0240c000c51 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 970865809 1250 970864559 970864567
    0xa0317090a06050c21040b040b1b12040506130809061b06010b070c0e1b0315040e160f12060b0d0501021909090b090f070e031b100507080f 61
    0x26080510076a0040e58100354284814140380d40360a04540c02840c403500075080c101200d01d00c40a14901040c0607607001104c100b203680303c0342c84030400800c000e00349404040c58100340746c1c2c0c9006440060401c40031048500c0c0ea16203413600340681403183c014a0602c0b041004900040000c90301c00503a07164180c11340d0903070b44481102040644060a440c0306a0040c428040005021145c0f040100f403045d1045840b842c1c0305540b60594013451a00b51182140c040d10b00980032aa210310b113014503401040410245807444c8440d01242c120b9548a000c010103030841e150403d0201040707040c2c3c400800c001a802103d003847c044000a1070401c0c8980109203c0d01c0b0810f901c26543c44032104405143c00c8402195120300a824911220080d26034120100e48040000a40711201d03104000c000e003030107408060903944034844907c44440042c000390174403510030104007650720104800d81c510680c031395040940400c0c4030704010107210901c055a040007810042c2c08001645030b426682014995180389841d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 970867059 1250 970865809 970865821
    0x9050a17150702030d18030f05040b07080906070206030f090601050d050a0b13080d020d2a11011107050a0c240e010c060c02060a051501140d09050a08041401020a0317 73
    0x1107115241d052101c3e6824454900140d02d00d104d40086c58520070f40714504580d1034110309840c0790040344250058544184007802c04503829000a01007440c00625461030b0111076400140d09410a441c3d49242070000e80401c4140030040250a0141408483d5915001540ea84207580c9080c07002000302001400340201d4240c103d2080c44032085580400b1040d1145049042a00290411500c24200a00340398400c1a0700340401310744030100080c51141c15008581d54016a040c514200c100c420565031225000310712101c42020300540c501c2000901091005805c24081c4118180c01080080d50080042c0a41b030300d180e210800150941c3c180008090300e04d50043c0c0341c561a0402c050040d500700001050004d9010881038802c0760b5102003003050b91251030728449058503d03a581c501040c5c042000d01200303c0e02c074000d80400c810781040400c00c480155103071420301d80d40d90b40442d030102000c2000d102206045043c44100c0c0400e01c018904007081f6107006020512100c00b402d0301410410110711 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 970868309 1250 970867059 970867063
    0x60a0e0d0204020c0a06050a050105090a200313110a05011b031e080906070c200f1504030b0a2007030c060c0f092c131209050a17150702 60
    0x3000c0e0002d00454413990140402610f50309040d001711110ba1800e030014402d190948181c41c145c1c1e00203808001203a8500082000406128400800480400e01b440b80201c3d000380c003e502c15070b41900c41038070703408480c64a04d520903040203040344500c40d554414010750b40c0c041100c1d605009140ca081c181da0800c0c3c10185d50001c034070044801030003130101c980200d05400031801805540500c084071695a2140c900f12490740c41c13080c00a05512402110015242c50300140c4c1000d0303000104000c00c1c10724030b5000520810000c136207039920080049401c000b4800400f50b050b6000000e41410b00a401150414200101504100e000680c6d8042140c038240340c820308000c0380b4642d10031401c00c0090110107010349102c5d8038617200c10000362420000704404146e04c0180c420380404070510218a4088100c1107030081e030041c1300c0c0d0080c440d082000c01c0450000c0100d900203006c640c54124600e81044180420f10110750410321035140b04c14058480d60304001512080704402c0c8210449a4503400c808038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 970869559 1250 970868309 970868329
    0x11070b1602060d1107020a090218042d0507020c1c020105070606030f0b01080106080c1f0203130f050901270c0504090c12230118020d06080606030d0302030105060a0e 73
    0x100f5540c50a00881c4900040e10010100740d402142c080c00e169070b0b540c070b4010680c4202c0c2140e003003603186e2121074401c40c00c085d0014400f17000131a680c02d0301000c41d08441c640d01d50407800c9280f1200d480780103201e0b50503018081003000700f2080d0340c800910204041c3e0715514640c1003100a0400c58001000403d21510b82d00c80c0f4055a44080c81d8003840d422400e045409541c02e00401342da652924400181c003032000169a48011409041c0078500e2082c0350004008980030190442980020041115103111036040d040c05070124500150581382403030705110039500142c1040d03001440ea042141002240311719400a4072a601c003001c190700915038800c49040c05158085100d140c10040c0030030300c00d904103031700c0c00d543d00707192400f0040c25000795041c0f0103130000f0f5802503030b403000188018002d006070448840ba900c80c080c20090720708000e401142048a400360300141c074a0f0400b40a11880c0d241c00e21043c3d0035000185001d500719410700d800216507200788012401402a145003100090310307146414 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 970870809 1250 970869559 970869577
    0x201050420061b010f0207080a020136050705101e08010501080412090b0c010c03050a1b35011508010303142208030909250f0509030d090611070b160206 67
    0x6d5443d407100e4a04003103a90032950b040c0000d5407c080d403010f090018010001c21890902c00046443d1420402c3c0259080103800191035030301402e100420a80c4078132495202d00c0c3c0081e070780c0b4003404000942d0101030558840302c0a0401c00c54900401c440da9200d92165001303900901114100c03000110b00381e840585541c000400208040341c001054078065002002c14080b03510140000e0745c81140103c122090300516080c5c1550454950300d2042c418000c03061015000118000b07250320300034540d8010244000f4801d10780281900500910703600b4141c49504038a241026402541144d8001d0698058400c100710825400300e03100811120f030400e0581c10312031416000c04555124107410307481c0d81c0482034007401524040003080301e44c6088511213012528540710840d442c0310300b4008441102c241c0004104200707050001034982d0b41c0500c402c6000f03242585940206038545803000d8513000100100d4052600501000c00907081480304507801134003440c2d102c5041400703910026400740174180304 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 970872059 1250 970870809 970870811
    0x601030b24030a0c0203090a380a03060e0405070311010c23010b12121c0c09060305130317040c0b030907050a09090807300201050420061b010f 63
    0x41000746040d00210f000e01d45181d014450038403e00c4090f03070740e40b04550b656900021003003403c100c90352142d10b511041c1d82c0c0180d0b01408040031880b0b502401d500500c80d080c0c804400207481d60300660140b0407800100560320201e5100d107403640381c082e1200d4a074440a0585805c0c1c81166460b6031045100442d8540d200400714011900101e01d820341d04901d4201500304c0d8a448102c40061a00c0440c0c042003243d4a00100500c1e8080e96202c0d6130703500041c3c04d03210040e04640c42280784402c54007601740405029a41c5c0000c807860550000c040c0d9a000d0314503d1440c0035511b10101003136000c001411038400d49010410180c40c0e070300e0001340000c13542d030000440301000f0041c400c01d01c2300030035910b003201d40440d16510103d0715901e048048170901180103114090420007840000c2c40c0349220f04907103841242c044c40140c80c0181071031070061003481d44401070355980204000c0098011116030003603440000b000781e200d54480411514032541c00040f0001120b040b481c00300f25002d41000070480c90ba814 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 970873309 1250 970872059 970872109
    0x412020f010f060f051503011e0f090c081008030706052e060206100e1f0e010b1308010603020a0b0d180b01050306090d0e01050711090709080d0809060601030b 70
    0x2c054001d002c5402050011856500300143c01e207064000170140c07803810010503155900e00340b80c00342e0060308a038900d41e802c811000c00007003d0240c015014000c14416a0101c5c94010302880180040e0b40144003150311484600700f0f100482001083d01c3c0c01d940d104800041544803100302c80c12800e0884800c079004c61019007030003c0400c081403e4401c4690381d4003141c10544030303200100074205050080e0401103031850300256041ca07000d0480000000d040302810302e40c2ea01c424802c2d240300400d8201640c1408005600039000141c4a4558000c207031032002046004e04581c00629a480345106031620008081411244603202c1ea10204005407081c03019114400203181144040d0402d10419110303000e200c00191b100b250100d04494154100d6443c41031080c0e0650054a89801400301502c5c040c0111407080015150b18404078001d03d00da4a50602c42450320083d10b01c3c0c0807108030030300c08010380542444090100010400d070843c1007402c0100d102441040428440082e0341000402c0055080b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 970874559 1250 970873309 970873331
    0xc030f020301080703050f0607020d1b0f03030c0909060503070e0711190204050c0307021c11030409050a1d070b03061206240f030a120509030706052701080412020f01 73
    0x20002c2c03c0b281b00380c041d0765400d050b89500c2c0d5140c50301201d2281c05600842c1e1040071852050b034990070810203200d007003044d00000c1d4407941440103071002c0843c0401e582e14841d41c41c1540001c014002810b1030b0005100311410b00010a1702c440c1e0034032440103c20441c0c0b000c1080c403802102114140d46c02e00041307403043d0040700d41035003850000403c00d0303014625250104440c2e40940c0101c0f48552240e4004041e014651515940c2d86803001c072801d0200b1a1050608080c41001d100401c010041302c4000b01e80f909180d8216070032155061a00c030764920301c504001510a00101e00e00c0c04861220700300c81d449503501000300d03070005070981184c083d42c0104800c0265030f0b6880b01c0415684141c13507003281008a000810b10040e04114401664142e006004141c0000c111401c0e40d100b0080c41d1900c14106020070000c00d103400101c0d00031202044c400f180130521f01341070102040e2100c04041403100443d0295001800c03403540504090005070072091300c0c01d000c5008101142d0411b03062402008000300354 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 970875809 1250 970874559 970874563
    0x3140304081b1008040807030e030c03032a070e07050c0a0204060602030a2a0b0402040204090c110f03040b0409020c070f2d0602030a08070e0913030f080412030c030f02030108 77
    0x2030305080d100c0e00f4400007068803d8452498148a503074403c1ca024600803084d1001c2c4c500a0b07807e0f80c4940d15201c2e01c2c98294040d1009e10182481e40d545c1c1d0070790f42c1a05541c0c041c0841c090108224003410382d001c800d04102d8075010501c4141c0108041c00c001e81d0305c0e07451080c840c0c1841c0d0329a00103500142000130000f8500e600000401c030100c520395621100c02c220408440c041100460741c1c000032071102d0b0840011440c2d00c2040c58010784020710043c94641c0e1040140140d482a09020001c18003098507050351101c14407520380c03020f4000c0013039441d05003000d42c0696907000358051481c001c1e038007140341c0300c81c52010040072014000003060000f50507968420000230700e07056065100407407034540c3c503245000001c01c9148250344098018504158070484201c4150b54024a03010400c90100100f90b0b903a00d4080065018018050180a40041d681400740400000403028000c000f042d40811011803815082c940d414540c5150108502c1c4005030120007600f500c03491a4001d0b0b01c0040005219000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 970877059 1250 970875809 970875853
    0x7050604090b0a12021c0311162c06040b0402070209041a0a02090108130203030d1a0f0117040303052203081509100504020d060513061a0f19050c03030709050a050a030302070314030408 81
    0x4003100c07041082b411a64144a040b400d4000910010100220704e851505c0c1d0040030b10b540c4080c00041c00c1143c103400081142505403010b4030001b01c428803001d41021040100c0d0b0b0b2019003000103518141c62000000c6c02c0700801032007103034a00d030404211011594140100c0314881d0f9603540600650803d010304a400d01400c0d100302d40704c0d00300f41d070304400554007441000c2a064000c10906c0b8007592540c43c150701030700c0300500c4050418a00441c44200c0410440c0500d40940039a40c0c142107441d141494400c09064008903501c19000c1c03038100018101a80c1b088015510280c5000d6241c1c05050b0340c0b040540015000385612450710b02c03d400b9460300c0703031340140112440d41001c0e111003502e403080150b0301d02c110811000c03040820010b080004504240d800408406890032900d0b00c0c002460060450f041030751600d002400c0c0540030061445c0c038030181d01c0508011030b540b490b452710390354010399529010312004181c0c91902c80c865a00f02000d00c05d841c014100307074003601e0005401c0c1c100a404111 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 970878309 1250 970877059 970877069
    0x1403070c03170a05010e06010315120203070b040e1506090904020d0305040518100603050603060406110d02040605180306240f0604030b0405070905131407050604090b0a12021c031116 80
    0x4106c0b001640640c03182c010002c1000c0c00c10200c48216040c4114000c10b4070327103500c090380c2520503140001400f151600040000703100080503980981082c40c440c583c0711110114140c802c0314140300c00915170360b55401094000341d0444158007100e4103440c003035a031801603078000f45d40004402c1d03113454294040b03160300b840307114221a40c40700c05445507003c0c1c003214000d07942c05030584d21600c0041c0000310594041401e0040c00a0365604100d00c014500b01a6441604410b0000d5400f0550303a40c1050110905848040b0440260140e0b01e81050461100100840880280d894030b40c841c61a40d21128415120700c0c1c0c2c00751500756519102c1c100302079644429a03045600e8071506000140580c00c610803203005820030508100c4a02448d21107800c0000c81401c0c1112a00843c4000111a035821004100034480c008000c100c5080c501c0810020740c4c41070340308401040c01404100016641c0315200480358501004520034880706013021924822100f818412521070b44180e45481a02d245000f4101c074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 970879559 1250 970878309 970878329
    0x8041203080f011d09070b03280606080c07020f0d03053403110c03061518010509010b0304170a0207030c0602032d0d1404121403070c03170a0501 64
    0x51912800e4100b000024842c0c0309004000d410711810045040b80ca40360458604011a5a12512084280407542c01a10f100d400404132240103450950748407280090307044003100400c4910701d07240d00500030003030080c0301176401c540c000b45050031941c03135607024011410060400842c4c07003100e01d800341580d03002004401c0c4444807500c005400c00381c0610380b0703210202c0c48140c1519810b03040e41d05440071180e80b1444c1520740103842c02c10360f0545003082024480c0e40e0b00c040d24130109805405010744403100c076250041458102c030040c0001c1e11042d1015046400e840d600c1130b030f02d58030360401080d81d500010341d45001c80800608114120390014000c400e6a0040046401143d80d03081c0580c1d50384500101880a00305141650480c0d41280c54881d11500f5405020741c601a618100c110403101a050300a030301030701e100306110502500464180220505060070b40c03081c1c030b0400040754903010080c0384a01300010b0411003410180300d1000f03982c4400d01986420346e00d08040b1a65009807209020b464480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 970880809 1250 970879559 970879561
    0x31d030313060b030a0c06050d0605030f060714090f060f0f0f040e0109051608041e03020109060e0303010803250c120209060f0105070b0405070f1e0f0f0915030804120308 75
    0x5480d0200e0605c0c005940400c41d420050300e860303400e480b65007249006041050781c40348000b500f41c60030b0001c0e034180008480501110315204402502428807031804ca400c1035400d1000382001d4039140216203c291040341d555441d11660b1503402850b124100409075051008162801c010301d241b400760082d24110100503c441c4c1e294400b410444200310b41801798a01d52030610a0124001c026183e00305000f90350b4520810140c0340c1981c0e1814001c041140182e64500c0308900344140c46c032404903a210b0b80800f0310700c1d65250100311341d0369010301d0782d40b10541c2250419400180050fa030071003141d203603c40d4580103d82c0d80c603c00703803510b0201414181c0c0992054400900d20b032804450809014005840300d505150498603800503c0f90300a104035002d2051040c08220030700d034054030000130316a0305140c0850071042c1b0310300002c40e4000c0e4003901c03107107c8003e004e020440707030380f010360f0240d0719196000500d0741031b03030181800b1550a40e031000e05009400180442c032290304101c1401d81d903020391225002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 970882059 1250 970880809 970880831
    0x2030c0c01140f1b0f10050133120f06030605090d051806071e050f0a21030f0c02070501020c09060607120c080409060e010801090c0501031d03031306 66
    0x1102022184210840400024032120a02c00190103400d00c0c07112800448083d4842c403603d068640da000030800e0b071118040d07186c0c10800d805900d000d401e0401e100c1450403804042420390a0302c100e90603811002c030070075181c50b0500c82c107074116005ca00281c0c18411510b8004d180740061086000544025003800001000e0020029000c29551401e650b41890540640003c62801d42c014000c558030280420081020918240b07041e82c0014041c445c002d28068070345440c81c0313440200300002a40341c01640038080452204003440400c5150600306840700311200700102e00800300200c03001061482c0511400700e80d9400524030046c0c42e070a80031150907206032010009810400c40f51160301020801603078000481326540d041d21101c2e03604110300040c19996aa003446c0c0c02070f4100502656039084100610040440c00900409a0708000c10005005460310445078016005050526403603515545030015122110300103250303e81c080c0c3c1e480307003045156104c07560401c4000b6110b080c20014103d503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 970883309 1250 970882059 970882067
    0x30c0201141317160902030105030d020d2c090a06030b100812070303062c071103030402010e0f03100518030c151b030411040c050a14130f0602030c0c01 67
    0x7851074140c20b042d4806880c014034151080800c0c51008501d009000c504550034407160b0946028000f061400768580d81044c05040c94070614221450071076115980001c01c1c42d03000800d0035200d40940c690320f90202c2c0f03d09071083d1240086602c3c40d0b007000c1038901b04a6401c482e60302c2070702900d208101d200d86584401c260000544140d010381099600300c551100b100002c884000c10119210b8100880c00694400103400144900340c0c43ca505286403004464940703822007115507100380c1c1c81c107090200352402007400380e413800000d02c001e041c045a00c02c10092580c1c0e1411500c80307004001d08442e1454001d4100d0b0300608420780b4480c04400ca28241c620401c0e8000c0152490701000700010080c0403072607204550315900c0504035054401d030300407909081d007a03004011440b0b18002c0381b41200c0a100c0b0014481169034000d2280c08006041c4814501d695200440110310072404500030340720440b2082560a1144a0340300754062406168006505900803001d4000c02103640c0540d641594050b005503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 970884559 1250 970883309 970883317
    0x70f0b07031407140706200a0e03190f020a05030607090611061e130501092a0b0306010507060e0319180b09100c020301050702010209040f1b030e0a0b04030c020114 72
    0x100108107183e000f400f04d555a1005840e2180c0180e6001c5080a0781c0c0da804074103502086400c00600f02c000a030000b0035038109426040002040d4010b100c505060004889005d400cac800041c00010a44c80c0e10341555125150000904401800e0b2182e42c20300c504050201400d41c400d0201062a540080d8201500880c4040c40382490041404000c41941101c0801c030754006c01d1510030f50001070143c00420002d114080320706110b004042c61100403888500b034140041b41d000d085801c120403007032190708189016281c0040f42820816220901031529002a01d02e143c0038181714071020070074007400f0b40c0007400c00c5180d01c05510303111038611000446080c1c41c0414060303803200000070825951a41818004400145014903100709004503035400603094401c01c1d6250300c0103070340101d9032a8030352915110b2455003c00d2164100306450b4130100041303114901450b0300341410354622032401814820700003525003c0d03000680403901c0c43c0518010300040321054040e4001201c0740221340740f0b541004111 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 970885809 1250 970884559 970884571
    0x50414030c09060904050f0d050a120903120b01050706020708040504051b0a0c02010e031e01360606030f120201140103051905030c07081f06050105040e0606070f0b070314 75
    0x100b681d44407801e224a0200103402158280b040d05078120700d00e036003844408036404d10745d5a1965106d041840c006e003003a602400461981d4904980f12000070303000910400d180d01000c00100e2455030442c0140e8490203510000b0300301c6030000500c03404104955000308180c4401710303000c018540b160b0040300b412094a6072032100200042082c0450240103030305c0040b60701c0c41450081d0004040b0801700c0d080240e42e07070144100d480308420080d040ca4013070251950324900c00c07511100c448595142d0545101601110b01c2640740020903c005020080e08a5005190001c08100383c40d101454640030000782c036030310000154030700368041945903041c0e00000e040702d80000051075450390f400e01003c000682010119014841009081c0e4101c0042c030400700108810000f03814036010440e0900c080e94541c00201010314505502844a6078210045c9c40070384080021110880e61001b01103401e81c807440c400079105d120791480c00c1040000c0365540512480090703a003806011880c04208040c0207080c0c40c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 970887059 1250 970885809 970885819
    0x60920031003140c06070303050a0c1e050c070f0609150905060901050d2c0c060c070612140f0a18030e06070510050903091e060f1810050414030c 64
    0x400c1021800ba0b1203800328400f000c4040d500307013002000000b005648044030482c0804e4840d000c2240340343c7c0c54850905034601a043c646c82c20500551030206490503450781c1d00500c5008214070540510410444020b01008066002c110b030b00c03400094011185032003100c0b44441d030005055101b600c1100440200d481c00b400844c00c0c044004010f440e42c1c3c01c90002010050303619428000c0c9540300f125001d1100f0140f403d2001e03070011003000107041107001a8400d006c0e02c03040110346844c3d407000030080308071025841c0850b204500805128054541011407900e281081014026082c050b03050302c901070401400c00b0480082c100c1d410700142079542d000680404c1c0707400c21507a0b89080c181c005003050703449641540c1e0041c006000032000c070792040c0d804a80070f82c0042903e80640c1461004c0c8040c1c288180203101310707012404001031243c410141d8039100305601144015100003001c0d90144091402002c4104a800340c110041c45500548204161500306200741360b401c0c100415502115040580 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 970888309 1250 970887059 970887091
    0xc12090c03030d180b0a0e070e040b0109050606070507061e020a020a261615080405060402011b05011a01030f110706240b03060103050a050702031209070906092003 72
    0x316002440c00848001304d0001055a16001890702c5642d80d2041204460004008917517000039031030000d50782c20000300e01c00782d0400e010109062100c17560456150a8001c0380c9580c505022507540c0c042c9190080c221f11034218003040c0c06420a40001044107501c0c0c0021080520b440200d0f60f903c03c0a01c06074112007880700c00d10807071101c0c29441d2420081300003d252100c0c90000c80301e1030800e1110100b040360800305401d2104000800e9a4070a061a40c68003017194141512401d45800c0080d00c002c1c1840002c441d13130400740c400c05d404000510f4020000304040702e44a081180704403540390f105030010b4038064589019044138426a00c403072090441190501c1740954510005100264001e1076644d9581906104c0300341c02e80140d8040c040140d5520707100e042c1500050244c50703028000e0320080e03060004100c02c6641c000300740c03401200d10075540300c01511440300450034401c8a8000321660303802c101c07000c07982e40019080025400c07407204240c1903d01c002c160428041c0029280d10030481400740f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 970889559 1250 970888309 970888327
    0x110306151807110703030c0203120415110c0409140606060a1d0f03161a0a080637060816080115030219030905100605150d090b0c12090c0303 62
    0x1120556000382c00341408452516140480c40c0740845551045000642e12403410045080520210f401d11141c0d1001600f014249500e14504c3c600088038081081140c1100400100040000c09003402c8054401c0014850070f0030900040041040c543c05e151040401040756414014121100703560147d0b510840c4032000c1c040c0345554510005419804111200780340d500b80d400b4071a041d00c001d2034254000d1610f180220007580501903071004140c00c00f0920003140850f42004100e94010800c9813100c094540c02d1484a005030610120600301c0908655650640080c2d00704103002d030784464645400315680c060032220003074003004800c2c00041d40c4100400030043c2c4151070f4240f15441b030802500300034004900c058801c9200d8002000203840b04c0400080c003400f8081c40420710249001444501e0a02c0702140c515082c0785000b4118020000d0710450401c00340e4044100e00e03601141c00880c9003440e007200030307140d004109181104c8400e40302145440d00d0001ea4643d008002030069406d1030505 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 970890809 1250 970889559 970889599
    0x10e221517031209030403080a26040b0106030f151401200106051e01020a0308100905040f02090708010e16140a02010c03050114010816020705090411030615 69
    0x3840002004840c03544003080040e800d0007410039001d4104021501d80103040000103081002030300410150304108024408142400300312050304402d42070080400340080414408034141c029a0051140790406000811441d548030134101d88003070ba0180705109580204000325030102c00d01d10301e4600072020070000241e261083c1040400d050500e01d143c4c0d6142e03614548007203000440c5c1c60142c1d5507010184820302c0c0889248512a182e070309040c61a001c0480081e5482c81c6480c030140034443c1000000d4482c25078001c242c030142c070940d40e040c4500d041518007158459543d0310101d10810b1b82c4400503601c04d00c601d02c2075040308c0d107a04000c1d903940c41711000742c403083d9455000801081003886140c0202d15551004000c10b1505e0390000500b04030340315004080340e4040e081603040d0901210341d2032060782c3c0003014135004001c03540c4507a0009041d54040c0c2c60210715030300c01508506901c0030442440214241c0504507901901600c059680c1e1002c00038040d0403202c02546e1084051590414007400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 970892059 1250 970890809 970890821
    0x405090f0703020712020a030f050c100908041806030c0803071703070c06050c12151011071d181903050a140409021b0c1f030b0618010e22 61
    0x1c9410018a09039582e1500c001e400c050512100150340702c480c1840030140c2c01592507d000c6070905e41306003442040c0e6805a01c8101f480000030351f45466100302c0c014440000100ca009060903c00302c69022903040d00ea1014100350712040e00da041300800700084028000c02141c001581c009000440c81c541080001f03120741015003e2010800c1030854100000d1b8588145401916000ea86170340b90841907034451114003004041144003a2001c070300003038580b5200c007101000400c6081180e440c2c4000d003038040c50b00810703900000740307824606000d00c02034810850303890081a12400080c81540206451644c80d50300c020304c0094102e200c240280441d1196014200e40312003451308511041004850101e590004e8024503071055000680714050140226001103924000025041d16000e0b031000444a0742000d03132101b202c03246401c810100c140b00390b0109240400007803455448400f44a20102c41001900f105804140603080105041c5882000c504180100c0000c803070940c0f200500700741c0075090b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 970893309 1250 970892059 970892071
    0x903150609050a1e0b0901050f040f1404050f010203010305030a03020f0d05040b0610091a070302101b11031c0c030b03030c03131205070603050c1b0a0b010501050405090f 75
    0x5600c51000c180703078895000e10341c001d145120340881c40c0d842061040102442215903003101624000c05c0c03085c41e03140d009a00b0b04460040300c0280040301040045000b0b0400301c080b03400e0039813420310032098a0b1062042c02e03000314040c02c1140ea4460701007243d14201e100c203000c0500b20381d005000c24a407051203170700280502c0081001181c01c01c1c031030302040003da8000743c500b194518500b100308850780c00d18401044c0001c40c00e01e4400b42140c0f62007404101e00401c0c40d1070000145000400c482418020019035043c00b0b4220010014003001c1d200c0c1140003480301c410140010703542d02c80c02205140010655691031445603c44c01440b012a641500400b0464005001e068840e480c4034070a540a10151913203403000009507958030030b1124494030450803038000c0b1241260b03103200800411000502c5000341c0e032040c00e00294585420783d0b03151050003140100a59000c80d11060048a4030100341103031003d20841c4211314690700d460064030b45000c2c50043d00d4008490700c0c0041c0d410f0303001d0340042d50815 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 970894559 1250 970893309 970893311
    0xd0c060e220507090819110315040b100509040302030c01050708010b16050127060b01090602030d051b0f0a08070e010c020f0a03170408280b04020a050301050108010c110a03090315 79
    0x2960340d03466035007401b035051180a480c25011150b0003d2048419003100e05100450162610398100c109550030304a01603c0039014910304e100241303604016a1030341c009001c000341403000919140c43d000307560350b00c941042181c3e5401e0401180748140500b20f00c90507502590025400c14071040d030744122030f4150060075901c40d03495440e401103481130750064104030842d0360940c10000e0310508052041c1c0e41c0c00510a810001441d401300700c41c90b0701000317854008280d18404510354840d9800e200c0d400e4511102c80c03095000002d42c034111001440300600517030302c040d202d00806659901043d1682e9000954590104009109a10052070b003001541140d1074018031501315240c8175103450001800400c1440d0a100c400102030080c0081004209208051b61070124188140c0792101007810f00502002427418000601040440d95008581809040701600811540d0307510100107003e00540c06100010540d01c40d24820f80c0c1001050706c0380b4441c1c140d2a00340c0e20600e540e446400507501904054851 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 970895809 1250 970894559 970894577
    0x10905100201090b0c0c0c03070806040f0512040b0c0105070f0807030e01060b0403050106030b1303052a01050406050a0c08041709060d090c14121c020c0d0c060e220507 74
    0x880c5900070038051808a441d460b246c003d141004c0340707065040c40000344294400c2c20304020414001031400e92003980316030180f4000c040391030118a0305988800b01480c00f900030501060b01c49200b0040c148050810700244841d0300c903d030701500c80c224064a0300000070035002c00104a10b0003a0011811111032a000041e0665504a00001904150000c4038180d440e01001c005101c1450045904401e03070b041d40d070700c02d042c5d80d580c0078081d40308680f486002d12502500d4010000042c1c0d00c54079900c410400203100920309894000e009041c22940c01c50800c0c9081e65030075449101d6100703184596400041100074041003085c01896800c01849613500c18410018a0b054801501039001007600c01c1c2c4440716443d080c5565078141c0b00141140c54080c0d0842190038014840008404003150300c0411003004843e0310000490601c1804680150425003404040c410041c46d8035580049a409580c1d240c400080f4408200c0a04100c0c2c1e0310114080d48000341200c40c5626038000b542000305420680c01c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 970897059 1250 970895809 970895813
    0x40b07060f05072312100e0106022a041103040b10081b04090c0317030406110f09150d180b0a02090904061802040e0313053109020919140601090510020109 68
    0x5c00702d08407805400b4162a15081040300e14192000d405400e290000e03000402004d41d0340c1e00320310740c452810f003580841c84021143ca03884542c001e54110107804034190741c034507007400c010030011826504070700d68987e86039000400c0394010039484c06841c00c0303807045800340125008000c040c0c401c04100b52007150041c01c0000009650301d409101d41e68840410540320314040c242582100d0041480f24000341040110481001c08c500031a240c0c10b9085842c08505034204040d80140d010301084c84030000c1c41d02d51809039a2440054640307a00384103081d2201c3d16500c0b6240841680580d140c12508406400c000c6030000d10141c02640e8004607500c072131050316030180c00242c00d43d80000706015454000150710303000c3d00440080e18024083c00d84120300e1904001100203958031604e81c01b91104026480401e20207c1190081b1541c0b40c0c008010340114103224100c800b400d11440380c4408610f207494921400041c400008503c1884141c40d002d061501e01420301611a0300c0c07611404c1195038031860600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 970898309 1250 970897059 970897087
    0x100209030c091f0909020a03032001061403010e03040e0c3001140f030709240b0307081515090d33060b0d0c020f0102040b07060f050723 60
    0x44100b800340191007154400c82c0c1602d00030290384c0c0280300c03a40d0074401c594016072101c0155500300c0340c3c94502440070004850043c418402c00d41c01560751542002000034191070700304644802e20320200c0081081c00c90441a4075900d1046120341128403011400007200081c800c40586a0300f990b0040c8420700d440031064610110380c82801102c3c2c0400e1070340c0103100c0e5296000184803210010758080141c14050300022340e0340c1890303201e82c0d426a51140d202c60801084101e104da00da0707a6501e80079a90300d0300c829003000c840d00202c40400c00500110002100043d602517152000000a09540d0078500c64220034100c03a0b201c41101c980158051900714000342c0c25016900c82204503800b102410054100b22854540000383d4070301c001818514117100f0700f500740048a04000e00c0841c0080c007040707802030030b07400d0080098a0b0782c4d00394030200c1e0004001d1035010080502a02c204070420035181d20f0001c07a0201c91040d20f07641d00041c80717003d8070043c4050443c42940c00103c888001800c090345814019 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 970899559 1250 970898309 970898311
    0x114010c0614190b012a08031008061308040b0f04030f1112030a050d0b180403110c18040f030513030311010e0f150a06090507030903020c030609100209030c09 70
    0x6680c40030008110070744003c5200c805003054509403e1020110504c0003c00030703540c00640e6202d482c5d044000001e20341799200000c81207644074000a44038a031160401c42040303500e11030320303186000d0b800009400509042117180326940c40075000d030a180c100042d4107100d0300003c080503083c0b64108000700214065454030b82d9140e1007280300e420105000014046100301c200841001c0e07500c1444850941d0303811805441060320510000945592401300040945554800c0d20419241141c18802456802000c1801d003c05510031a172000c0806018003884221110140b20302c001c0e05c1c03000c200000c04500030070380018080c1c82c2040c2042000d100305403c004803a80210702051850f540c00000d10b400380107074108628072401074885090708000c0d01c2d0b101c6100c0c40001c01c14154420028a04454640c402d038003806020304104803600d02500c015004000800040e40035109044000c1500d24000920f5446554800c019211840e50701e010000a0341080300b02a915004441145c002619546026 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 970900809 1250 970899559 970899581
    0x3150406080f100209010912020f040c02060f070203040f0b0c160909020a0b0c030405090c0706020a210c120c110a0c031406010509060105030403020c1f090f0e0114010c06 75
    0x5480b07615040c92100d841c0121030048850b0413401480010300583c1c103c004c070000c840c850761212842003881c0c40065144030008001580c042e140c4408081013950000c3d400b44220982d0220104642310100180d0b07a0340140d100d0410b5011102d40709100090751a13001e4034041040500321034070048000f03c8980d4291450f000b05490f6a9070b84051000d628040140074018603220082da450060342e0080d040c1c44e40f1850041c1b42c0134611903404602140045000c031031400b81c00180131074031a070b05081c00400003030300c0c40440141c04140342906018902c1c2031041e50140d00744d544804003402c0e240d42019002e001407075144028400807140230701d20890140401d80311030b485104510041d03400c0d80b238952120011281ea140c925030000005000c103444103030007660085000d00300310351030380d5503071504078600050b0b0342240c2d81100104003001c002481e4001c0045c4440001d4445000d015119015408034207614452584051280001000000e031214041c400000c0103140020034406603481f000251940c1e00740c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 970902059 1250 970900809 970900813
    0x10030b2709010b060315060f07080f0a08010b03151c05070312090807030f0b060d062f070b0117010212011202100c05101e0c0201020712020d0503010b0315040608 71
    0x41018a070700a101d6030489090440e8081d045061a070641c9104800004032180180700004142d0f081d1403003030059564140d8400c99460b6155516002544070b40c2000c0400c50200f08040004100d02e0641425240329050280f000000d0305500c80400a81080e40040c8480e07071203e158404011403401d00481028501484400e4405881e043d0010321071001e41d44518141d801141d070a00005584400d00c0c01ca840d004201103040703440d1000003503450a00c500c2d00400261410801c206440c4040a260806002c4c83d0002064101160803005040c841c6400c001d14010186005202c00301d1400c443c400103038240000141001c0a044041002140030b030040041c061486120104601d003101c940a1418090726180e940c1c5040e980d00d20340d49100c2c84034114527503502c66a0a03481d02800b42882500c143e0140024041442c03440340280c007e520184045e507051084e0b0541c500c1c1c0c580000385400030400582d80f84c40c070b168640400d994182d0000b900d50768190005c4541000150303a1401031801602501c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 970903309 1250 970902059 970902061
    0x403020f0d050a1401110d090c0f050a0608150910081603152310030b0c0c0706050a09081e2e090309030b1008061510030b27 55
    0x100201240100310251061411142080020b4070200c3e1060195522200d1003609044016944c0d01521540c8545000b40401180c48001c142503074004003103413400b9092000140d6155460f08105000c1801420b0300b007107803210700300890b510504509500a01000556040700212800584041d10a0726540140c120015007446040e500f48130180c200c000c4860030700c8480f840e40c1d40701e140b40e01c0d9120110380d54542d210140540d42c07481421101a50664840c0c200c41490413a010004d040c1c91404103407040b41ca1580011403800061007203420250001004240c000e10780309044034541d010041e00ea0410140c08400514001d00300041000e2013184451521015000080c09140201801441500b01f2100c94104240300030003020300f00c00800c4d2580416541102c0c2410b030741c8c113091680014041e100410801c000000e8030020721040d240a03d0650340151111380241d00420405c0140c0c81d8014665110110100c0c081e40c06101c59000c05000c0400803c0191401c85820492602d10114414400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 970904559 1250 970903309 970903313
    0xf0203040201020f1b1c020a091e0b150f1308031905030f22081c0605010504030c0e180a050a060608070e010509090708060705040303020c040b0f100918020403 70
    0x413044250700803000008000e02d0810450b8550b00800c50805280120303545100c0c00d00075480280f24070300307490b0013034020b204943d80c07004130b00001c00641c0d00001d0200066040345150500c1030140c8010b41c0d0b4010714249101030a150b0034480c3d0360122000198040d8108002c096003600c2950050040c45d0f004040c5840c0e81d954a07003462604000034480f81001010803c00c041808580c2c18140c12510300c2d00c60711160fa0320314050905004d4850b20182c082d031004500c20700454182e150000328141854000c1c0507055407500156028012800020961120720b1010b000107401e5020050f405021340740c1000c2c01301d41c4104164104440c034072003903035140c10100143c02488002d0103490000c0031804010080140740c2004181c1004042c05194490182d65000c210000340411040d0302a000e18400e0f5103050500c2140500306a00c144421400b40c0034000048000f451b241c030540040c00030281c4a48001c141e45010000b15020100d40c240070302251000115440d801c2034860402000c05d5200160b80f28194 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 970905809 1250 970904559 970904563
    0x2040608180d031a0402041e0b030405120702150409050f01140f040902041b050705122503170a0e060901050606091207120605070e041b0f02030403060f020304020102 73
    0x10a03411038405082240c65491100194003091940d07586400294906000c40c40f00310009044c100a5001340040740120341044180b184c00c25200084100c920f00650303e51100c4100d000486001c0c04070342094804843c200d24110050128900c000e041d02074030148081284500c0c0c20907000b220100c1d030345004000a0704000b40c00203000d400640b6600c09843c461400246141800205290080703031590100801c5440b82d800c201100c03003801e00101d070301080480004200c1d410907070058030320b8440c0302070100300a00d909044410500d0b007644803a11404032000c50308548001d21030308400b04000c480700b080070710801440803800740e4045400852002c1d0000c50307051034002d001d40800d00300d13458141884015644e40080321044d081c140c070410041c2d8140c502c00e41c1001d0855204801031070150220f0010440c1e10b50144c0d00c07502c85a02e400d141030b40c8400c00d0208842e1406400c064a49982c070040c500c01e8010740c0c1095007801d0303520480c0e251907200e41e02c0809888c0ea128034079441e43d80110070b000440da01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 970907059 1250 970905809 970905811
    0x3080c100905100b06090d05010b01080f0103200d0501050f0921030a090212010f05040210030e0d051803031602040507140304080304061b0207080607051201140a150302040608 77
    0x4080001c0c400080e0342e03111540c45158081c460260996607015041c0c2a80b00c90341511002e1200405426a24100342401c0307010708400301d5828000b0340b442c2c0004040000002d8a00d051700d400c24042c218440c6410704074100915842d0340c1d40d81c807449110340c0b240021b40900805200b501445d403841d0450400f0000a4604044540c5c1030301c03911002c0004412849404040e03d602800c000b00c00300e08000d01d8004503085000c540b154010765401c06085500a80c0c594118500440c82130f07523984106a20004100c040780e08000c40c55009130418148400818851409801e40d900740d62000f0075111502c000081c503550200c4401c0c40c091a0901420040d4038062280b40c0c1d200d001400c00400b100312031011810a44030050004100d090040301203000c3c080d0682c0060b20b4001494904000295140000ba40d100e4003481a111588503010004a4241c820170981d441c03402140340d0301d40b0310b900740380d11038040c0c2c43c09400950b0032008420b000540c03040307100300e56144806035890040c0d8443c14200300800b40c0c08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 970908309 1250 970907059 970907083
    0xc01020c0d08090927071e050d14100612120e0603040602070c18141027090503040b031008010501120b0601121a040f0c020c010f05120103080c 63
    0x420740101c0c001240b00c8104842c50310204580304d044c90380e81e00041c030701c05501c580c26020326103501c41214800d41000103641400c1c2d9280b4014500d00e2605d00842480b554902d0051503041442c510107000021800e040380010080307410309941c03007100d07a01080307812203109a100060760f480c6490460140083c2864080250346180351040e040044040800d139584005417005000c1680014404c0034042d80400400c0030b0002d15103100440d0420011150123401401c00c401e8002c25200d0105944070b070f00350041801c480d60f0581a9070f83ca5001c0f25155a1549042d03080301515885a82450029178140002c00241c00308041140d1a810803060b07080340743c84590840d610f542c0c9498018842c20b4904001ea078845584205044140c0d0b880100484040404e50400101d117801c281444540d00383c0c410916400305800e55042041071001903604060352070f2444003c0c00b503080124080c599500c10f09010292002e24203000380707883c0b0f80340342810a507072099000792400e441c0410709510118040c07214040241e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 970909559 1250 970908309 970908319
    0x3030509010209240c070909140105060a121a0708070f080f0406022104121101050402060f37030e0d09140109050409050c010e060301030f11061603020c01020c 70
    0x30462004142c1c030f0000030130201d2440858038403030041810103000b210402d0a00405031841c1543d500c82000161050400840b1710f60070f50301070100e80c84414440e0034403403040105031a241919001d503282501c00a088142d0304968000c040d20703c0d040a059106004503002d5440d041e039417a11004c01000865070449a900300052403060240c00c3c00c0c094a8140c109401c43c1006948800802e6219441c080c0101e81c18180707843c0d40204000d124411005c204507a0203501c8018a080022031120700702c50b4100c800a43c42801404481441000d401c0901341901142da05030410170801c010940100380d041901c501c03001031050141040b1540f42c040c00c4242e203468402440a400001005444e09696004584000c10352000f9840f00360f110f045520000c1001400801003c030280c10413030307202d06043e40501d000c66181b02c155145820194100e0781201d81000f01809100e0542d40e5841e00481c036405c011307508c00000e004c408840014805160340c9148282c00802051001800180c2803c0020b800e0070311034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 970910809 1250 970909559 970909567
    0x100b060712031107050a03111e060417070203071404060902121503011b0302072117070224070801080f0c0d080c01020c07080709060515090a180603030305090102 71
    0x4449014000c1c0e107411500300881e011004030440b0102c3d02840001404034030a01c200d1205054016a041c80c8280145c0141c440c811700d0b00d08031a503481d84100c01204680e000f040000c01041400c40c0703840030400441880c510780001c03500002e160265036044120042c1c2000c0d0501c80c2d901d01032154100520403800158100500c141000e01170040040503035803020388018040507103070307001c1d0f00184800000f200600107649806800078020342001404840072100c09001c98408503081460b0703c9004020707038500b003180a103170011400115000d80b10806500c00c031503021010b00d4111000c03403000304401e00401035520b4030240051444406921103d07198000c83c0003141240004210400048010fa503c1c10000c40742c0d00d09150544202d0070b507683c00b5480400c503038030541c0b800b0422000b15858142165000754480e10100110743c00361244d07560160102c000311030003010b000c0c094113200100030034444910303948030514040c0d079032541032020440da80c4100500406815110300d0750040d845034021414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 970912059 1250 970910809 970910813
    0x1c020c010c080a122702040f0b0f15040b0706021c0b090112030e060a030b1008070206071103160602030a0f051e04140102160c05010f09150309020a08100b0607 70
    0x101c0d01c03400c1d0441c0e003000420000e41460b01c0c803a8011058005025050405d085883d0500400704906600f0403442182050500d00c040b00140c02544002040148803c003d40baa600410045c40f0b840c0f0151705c0d498609000005040b034814011b0b001c1107002d0503004d6600e2048818503d841000d00c2c03e503c01b041d283c6421002c99403a211071141c151805054035200c41031b03541c10169043c1c401d600361580c6c01040001c20760001641500014104c403420b9908003144021300b01d085e191000e040b00e400d030040c1e12202c0001c000328420240400804410742c00e03031749808400d1003101c01500481006079403c89c1c002044c0910255640b00f40e600c0c031280c505003040700b07090a94208982e800120042030300840920701007410320503071421403204110071030000c6540c1d616440505079000d0185400303480044500b48001582e502030400d04500d5000d5503104092603082407500407d21802050f05802c259468071514010717160071454601a01d0b03114010710080301076032400026900c00112681c0224070520200700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 970913309 1250 970912059 970912073
    0x30c36090509071a25020301060b03090327030d0c1401020f0d090512040e040b1312080405031303030302090913030903030e15040902120c0c0703140307051c020c010c 73
    0xc280d82d00c00403030584c100c0346000441c07040d0088800c0313008aa0f507015456111744003036224400c91284203030020302c400c56803007860700c4240c001110301079001c0d001003040005800c4100c0c2e0350a5044201c202c05207609525a0109191083e56030340711001c10307401000c003c2484001145e803c3d00c0c0c1c998000035486c02c228030b841450356016640200400716158603400e0200502070002c025242c02e49501161500c0e510f40082102200584080d1020320f4240041103402031080040c0400640040e1072014041c02e01c1d80c100c0d80844004c00035680c6010078403500f13a80402d101c0d4484c1c011406507070f0142e224803540040040d000c2000e0100c500d0101c9030400c0c400000d400c0742c4c03801c4c11250541405044080c0c0d0708013040c0c404c40000350411510740001004035010f105039000c1d004440300a2211165540d411101c01003078418500c0c00c5125074403404d0200000b48508000c01d183c1507188090340d0074003105a54003850400380220040780029000351203180b195040000d080020310929021201c0c4500c0d803540c103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 970914559 1250 970913309 970913323
    0x105010f0f09020f04271b2a080c1005060904020d1203020c070b0d0c0c02031f0e0f0601080d050307230712080105130b060a030c36090509 61
    0x54010f402082541c0031819150596004080c0030146001c04010000c2c003844070b5031389507180b0600524000c1074000910701e216050702600000d4171891035145001d4141c210000790a05151045c816090b11140000c081e80050308070403001c1402400d1800401c01c2c080c0507a04020546401003915108001c0540da407066490152074124490b07240719840200308602920440081601038800c41800003080181c2100501d40c020520204114540c140c44044408109008020b945075010540940ca40d4611081510340d00c07100d0301d4001030418440742080d0030030345214001645904000e00403c140041400740101d0124107250030b03840c0d49040319000d040382d68038000d803803184001c5500300007280c0c900b0f000b1036400702d40000c84000c0e940c0750548018494074003409107502444c0400000501c0030303450b0054045400000b800d0a017450342e0f921048000f08032004154040020385d0251400c00b440c0d01000114582c0d01003101244840c10546800c004035031a03010743e1020703203800204050b40d48086000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 970915809 1250 970914559 970914569
    0x120e0609030306010f09030c030c030311010e0d030e0a060e060403081810181407050f040e0303010b0f1e0306030d090627080f07180902030a11040f06090207050105010f0f 75
    0x4045c1020340044121680704c6d10303400081c115130240e1404014000b10401c0242207c0c0310303682d03494140500707000c1542607521240a619843d03100f07500940b00c60703020350440301d401e00d000c0003140c6034800300703480782e0041c1c90380d041c03c1609903041003040c041415400700d03c255019042464505032a40407401d2035903900b924514080102e9a1500c2c10341c030403080008c42900041d0412000d013070341c00f1007003003d03622190320703110395031180d00c0301c41c000702044c10603004001d4100c1800c0b0155003107a2a218034901194051a14802204010440001c641c118032221124501c10490050384030710f46442414501071090864905102c0e0750f5108002e225448030a0303071304064080000084644c80002c3e054032541440d0000c0c1518020341c01540140d20780021084215003903c20010005800308414008440c4e451034044e4164201c00103030008101c03050400205500c000c0c00c0040c460891643c40030884100760003405000e90005041030031f015003400303103074054440301007028040c0389001000400725100b44030b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 970917059 1250 970915809 970915817
    0x80301031101090b0d0c031d0d03050c1303050708071406040510021005011203080a0c051218030406030209120615041a040903050c15060d0f1b06120e060903030601 72
    0x38a0700c1903486405a1001031040c0070410f903c48035445440806481800003000009107817201c0e10301d10154001380c820342d94010700b0141501902c4000101d0150030f001b89103501020382048400000c0c0842c0403014020b500900180050508113402c450030408607501800388042d0030703480c1d01219a1600100e03400c8400460300c8a10540084200f6410a8071102c24480303035a140200008400c410744140300d010501c00d5861824030780d50014000101c4440384844400180b0a1040d002c0c501c2100040c0c81d000828807114180040040c1e0340146140d1254202100194021614a880c0d0400600516194003568050503440c5001c20005d41d1800010300e00314410b50b2035140d8803000b0404801c10940101014206210f200c0450030b019220340d001040c80ca00c2842500c402180c460303200140719000d10801040b10b280c07110f280d00c410100900688094580079800c40380412850100c000d5a401001c4036242d012519540e094040119030100d99400041c0c1c0065080100031600402102e40c000d10900f0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 970918309 1250 970917059 970917083
    0xb03120a0908010e12371b0f020d0206040e0405070906080a05061611070e0f130f03050a031410090b0d02010909180209241507060903110a06150b0708030103 69
    0x85481451986540b24051011b8601c2d0b070410b0b00c0608040a0081c4a25210320114440540300c2c4070060b8541400074115084660340c000c010324003400100000d50000308210f04058030780c11210044282a1001c85907640151004c1024035142d0042c3e100a220800103803115a9a0b500c0c1c0340d84550740144100268000d5000e45240300e0300074900969100d030351104903030b0b0b43d58580d1042e4201d1041600c03600001207818000078408000203400040303c0f0f500075042c140881c0c559406484981294810b4010706840b40000206034411340c00c150f2068a1b0f151149000e28a80b84d0900c04590340c03010f005008100c98450b0a000d41d822400d04012189800c000151b40010054011401a503d000007584905100300344106402088400160700c0f4280c0340c2c1800c0c8040290400c9843d1010124800c54103900f40721080104d00c7d160300488145000c0e043c03a00303004078245c19117800c050311148101d4105503514030300c4070000350140300301d0041d000c0681c90030f00d400305030788481c119800148001803003468000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 970919559 1250 970918309 970918327
    0x5130b03070b0d02120117120f1b0a1403270d0c03050a060b0409110613030615081e030712031509050a1b050307050702040b03120a0908010e12 63
    0x140a0090004036003090303c581d107503510740019600c81281c40c940340c0c21910000c0350290064512800c4c90382140000c081c0b4803170102c0e100c040c84e04500416411003905110429040e0780d80300349440c1d00307448030b0f000c1e2040c070f0340510b0211103ca0607010b51210b284d20502c034020b61010781c562a4031568038816100a82c1070481800600c0c0c0c0d00d00030000903d5a800d40030000304012300003801d02c0740c1c1c62080005005000c180d03c103000840b0112000038001051884801c83c0c1d0f82840310080c1406061505141041a201e03102c48040e02c840c03900c441c42826031110200120b803804e00000100000c0300c0d140c52400c0c0c02940c6040c0c0da034000e04d080a4000000a40c2a07000b40e0301a80c015120b54542e40c2c5070924442d40d40c03500b0002000d0886100d507407582041c0034140543c0b0044042d02e0142183d4480c0303030843e1034600c01145c868002c0c100480e006581c4036007000c1203640c108000049c0000722018150340e049034402c000d24481440e48504490fa0603c800c1c8526810041030f4100fa511088030104c1d10b0f07840c08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 970920809 1250 970919559 970919563
    0x1060e0604080a0503130909050c10030905070321180b130e011e06022d030c0105150a0806190c050d020a0e0405070e01080a05071110150f05130b03 65
    0xb81d202910038450800b036542007240c00300180541c82004240d2403281540c40d00b440040d240701d158024690781110180070b00703916000d0b00280310702d4000c0c90009402d030b00300c0da05c40d46001d0307450b041504c0c0c05c040032210b01191038150301e084411080b50300e4074a061540528004040f0701e468007030340000e02400315240c200c81e00c1d44000c000060410116004495035180d59520950512075540203214002000102c1d4880c0002000c9264440e00c500411070405078a00c1c803034440f840141c0705c2070240410408420080c02c2402400e0040c6120034094407441c4d4a20104150710065030321914a1b60000300030050341000702d41d00c840c004000383c800031070b2544200c1c0049030244954400400311a202084e0343c070900c0da1000801d41c2d401016201044181ca40c94000c1e5a0b103251800601d001980d0000060713403609591700030680003e100e05084c0c1084203121701990a00c001040090462a1794907078405141300400c034000b00411801c10a02800381c1080b000c41d0110025020004811380c803a80c29801c19101 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 970922059 1250 970920809 970920817
    0x21201050310180b130c030c15032c010b0607230a020a03060b01050d0c0827030d0e0c0603070c0b0a0209100e0f03030c2a030d0c0609080316030c020f0601060e06 71
    0x7101c007000d0480c43d22450700000008c0c00d40524a02204003035070148800d4041d10466600c0d45804040703820521030030313031400c03400c01028016820755500d0701e0383d2420b02c1d1203160240c00c80701d1058a04000440100c42402c00070145140b815000b03a100d00d40c02c40168035809454000e603600310001148a07540c280059800744a80302001d02c266251a1099440340d90025501c1d024030101c2041036000c4101011124200c01901890711a54000300302001d0f095401d0752140d2440440d4400f5240104c0e0342c1c0b00081c0c419001101d41c01e01040c820410705040200740a0200d0340601c001a086080880d80d6010801a121620401050018222002c0700076664083c0e9080c3d54440102129a60718003002000e40f60301007200c1003c1c0c0e080401101da00c2e90190301641e81c5a0042c00340007040c101450441c00c03512411040f001780c6881d543d500c4c4160101d1411030045101e101d420646508008182030010100c82956020f00215003154549020940000c02c980b8116452443e20002c40d0f05684c0009040e442 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 970923309 1250 970922059 970922063
    0xd0b0f150613031401090b060d020d1202030c190f080f0903010617010f09023304093215030709050f060a1d0f100306021201050310180b13 61
    0x100100d80601c0303922160190b40c040e6407080300e038141d40c030320609221400e9a1142c84002d020b10b6a01c1c00080311420318440500f1050300041c4041036010454941950b02c2004412420050300300103085030b80d00c1c2c020021440e4803071401c0c00701181158152542040312004040003003c0c03010009403444a0a0110262800700c44024002c0016681d195001d00041c40452074118265083c1400c0e00b0307845500d44a02c5142e560064000e40d0741080803d07801401d24030848030603c481012090726081c6a1451001d4809401094030005625040d22580a6424000d16a103c0050501c400400080c1c0d041c1c040035401001c0d05a034010406d88801c000b03400d0020f00d030085a0014a883e0070004403c140603d118050901a11f00241054482642016515001311604501d41010010810000300e0320b20340c1d41d00800b80413900800755140e544070020390744201c030544200207800c00140414941030202c0540e4600b0f60808019136810703030816000000e207a16014014142c240c00081c8500c150b00409140d007a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 970924559 1250 970923309 970923319
    0xd020301050f0709050406050a090b061207050c1b0d030e030102311409240a060f03060803031303050304110916091406070b04030915020c01030b0d0b0f15 68
    0x11030b04072465182442e040310400c000402c07104c0e0008003400c192007103000b901c10241019076080c1c1001c400c40003909001c1c03002071300324408200c5503002c0d6402100c3e5034022005944e03442c0e51458900100380c0740c11101c01e0a010070b0100c10240824645d0358129499a182d07050a040b5900084800064021f000d10380c003800f2041400144240c01031840084a0000a0741e003c107000202d0b04c03241c40d580000e200001181c3c0008140010418041010001482540d840c00701c400350314600001144010009a0080000c02c0d10489504246a010700645000e085001c1c0210305620b00400d04101d04110300c6000340c14000000b000c0380900c19500454165400003500c404082e083c120f0100075110801031100c40000c0461304089009201c40c5005004100c0050200d810031801d83c46190102d4400b8004070305122940c40c3c00510180b49214005498805801402181d0141c40c00074007035a443c0e1580d280300e140c00b420250b00183c02400d03042e03044102a000204155200384a22425040040c0c0c0c150b0700c5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 970925809 1250 970924559 970924561
    0x507152625030e190c1208282006011203020f0a110a0902040e06060a210b030d14040b0a09120b04031409030d080a090b0108011b02030f03060f0d02030105 68
    0x3650140c001840403c040c00c00c03604690540580c86004d4101c0c03000080445060360000c10a6400e50007102078603c1c02118041c3c5401450001d0024070600701380324140c041c409801c1408401d4008007403c040c00e41c0062041d808680c102c0000361910310501a58171044000d802103c2898400c002a10034a0015001c444030103039035003000340c0015071600d11144641130900c07000c203952905002b0758040340e0341c9221111140d1211410040c1e2a04a44928005c20064880980070000840f6032031000300c0b10f010001400030100018941018081c451395000d12030035081090b000f5410404503421a0189480e480d05c0c1c0c003010104032240c0d100395100f4940c02110322000001e00600200c030034000c510940715901c85011100540c1590701031764400691541001d40003110f800e01404046902c070020000015141c01180d0300d03950b0420307003a080109140e43d00e2106a0102c0103511103c194200070b07000450610409907405000c9210040c641801003100030285e111640300c3c50740d100c101d95402002403100d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 970927059 1250 970925809 970925881
    0x10e0c1302210103050106170706141911010e150610020a050708060f010608040f0204110919080c0117040318030f0501020c010f0606050f1c0905071526 67
    0x180c500b082c0419101d6520305400081e10540b03a899002000c0c000101902d0914a0400e051700c416280c44e20907030380500100104100c00c4552440621900c08503110000414801c0704c0490842d5030440140c47d042c1c1c08060002040424503554692000c0c2c2220308008118803114101d0400110000090892054203000310742001e001c43c1d07092080441720369500f666a660304040b5a500015076018103111320b07107400c1c040541415000040c0070030a017001030f0b02e804991008500c03c2c414510075103036168a80f00e07042c000c1502c02c2c0464038820409107000541030400f100100c1ca0480003910080c1445808920342c442c480540e20000011031700300d02ea41002d00d0b924108135010303600140100307486520b404458003218180d80f24000030b4035110742e5214103129190007003c0050780001c040c00c51442c42d11a818101021034054110140d1188002e0b1007014074014a11008408100610041c0a04c019558214110304107582c00064400a0b0003425a00d54104190155000014401400c150542d807855 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 970928309 1250 970927059 970927117
    0xc0812030708060d03080103080d06080f071406040b120a0902090403050405011b080418020913020403020306181b060c06012301080c0a030b03031c0c0e03010e0c1302 73
    0x1c42580c080d190b240711580c0c3c000070815003001c03035000100460360640050011800d0350015000f404c1c8410000254240c440201515005585801c3c501c80c0d403092000f800000708034204440e00309800c0d1009410642410303606ca09501034a104ea0024603c0c0130009841081660405204690060036100030313810036040050295009000f0f45002c00c12105a211440341000f50050100303411040301c0707003400e05003105551000490400007051680900199210b59540c1c00c14809100900350010307920347c030318414581001402020101c4c480951b4000d11180400030a00e003426440c0c0504004844440b080040c8890041240e0b40705507101c1c0100200d6054550380c52540c4066045841e0341f5002041801101e0800040b11480b50000c0180440704041703000790880e10310590014180c074144623401c40e084080d02da511a1010015440d0000b02030107a4203c80011044a4140e0003844454200c0b40b90650f140302d10205907000e4074280018074000344c0641c0c143c034007042d440d840000c1da200440488032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 970929559 1250 970928309 970928311
    0x16021c060903031d06060306070807020c2107050901140d061112091b031504031b0516090627021b03030613061d07030615021f02040612090c081203 65
    0x10310f40c1c140d1340300c4c003880850b40012158450720b001401040241d490780811240004e0192070030302544102941480c1503680c0751120080c0c0e452028140d444000c0c2691902e181003e0b81d40480e000d01a448014462007400d80100c01c4582030640d0220300c83d0805242090050584101c0410124000b091503041c0010120042d4090710420003180c24102d01112140e08003a00700c40703a40d9040e40b100980b00c560702908410682d000703000b82022091295845001d50b0580031100080710362350044808032a2004140f10180060038501c0c3d0108001400d004d10f1008a500c245081c502c5e191000d00b028822418035012600d100107a00400601e140d00380b06010f80c2d0b600203507072291240914a0800f120300d0882d2103850202c2d034100000109840b4817800d08209454041e0004041640f211000b055611544510b022414910760007080107510a20690301e01103c0500c0c0e031507400d030042008014107580091204030400700080c00151040d514602030f2000101a40b055045004015000e07a40114a402031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 970930809 1250 970929559 970929581
    0x51e040918060e06010f050405040804080316030f02061b0313060e0d030f140c03180a030c0b0f090303011a040e07080f0c03010b0d0e03071b05040f0216021c06090303 73
    0x83c003807541030a503d182c513600d090048614001007084200f000e0f2416800c41070304207014400541c0742c542c940b08602d0565101641c034400d0070400ca0805c41c20150300022200c0b80203ca0302c003402c80e82c141100c94480217241d40303694045030321b001b00101c0d0002070306401c018800c40d4003c0f403c00c403081d2800e165546401401c081d01c00481c1c500085141003011500940000c401070a038000b03115681c40b00143d00581020b00150580490100c8c1e10070765400400603039040d45e0082d02c1f141c0b1103c01da883e10350b0140100400c0e00321400048806e1007a90782c000800d0313a05550000000045014402c8030018041c01642c1c007083d010340300d230800c0c000c92540100c0d0150044088a03a0241a0b9960000c0644144803e104031402002c3c104205509242ea07540006000b44640054916181c80d0342ca680a01c185119084c072294030442c0e40412051500340315000384604174140550606410502e14006d410080030064041c0921400508041015011401e01e0a17841101040141c101f414000c00a22040c114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 970932059 1250 970930809 970930811
    0x70522030302240405030d051329010b09091621020a03050c0f040e15121506012303061f050409060b0f0a11160905150907051e04091806 60
    0x300120000300c52843c544241e8204005504c0c05402c41c1c1008000c0600504110801402540d22400980090b00c40c0e40210751080d944400d1a880349803002503001c06034415552103100b00030391300d244e803102c0c1115a401003e900114840300402c8105640002e07100795504401080d00c3e85580034052145d0282920180c030345d07420000c0c0e9540c2440340b00240b06151880c46815801e002c1000445c1050300d415502a500401050075003503c040403d640074140304403110742d9041075240c01f1880e00c0003802c5907800b140c246021000000c40c5607004940e40c08081c8250001c5030000001807180d19000b000006141c141005589460704440703008000d47c02601600180700d05108000a40c002907109680340d903000010100e1400c03400300c1e016502c0020300051413a050141c0c01064040d121941038030740040404150121785898980a0706045402c15072200e4850010305050241c401c1d40003040c0c41940c00f003940400c1000008481240042c080c0c0d41c018802942001d1200c031414250519031a4058443c0c90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 970933309 1250 970932059 970932103
    0xb0c070306050c0708180102011d060405151005060f0c03070515070c0b0612070503030f0d050a1a0607050f0105072615101b03080405120c06070522030302 68
    0x4040c2071446103484c0074001c81c40510840a0703404400c17100070300686050000190203625850242c901e0702d0210f03048507054014070704003c107004040c0007410740d00c0f88000610009203481c1c010400640302c0780c0603040c01018042158446400c81204540e16900740d40b0880382c90310501e140c40ae945403075401c180748500d1000c40100e8011070207030a8004c40c0b03a0740301c026601c8580d82c0c3e2050101f036150102c01c5002c54030a80d0070010302174070240300a10042590340034040e95020004403107001d03240050040c541c603524240301000e15040c4139070f6450041c1c2c1d080300c144c1c0d550358850402d6840d0008800031006554030b484140078050f6000a110000d42d0750b401e081040038240d0001699201c00d003182d0b1601e20800d4190031801078540b80014806020707d50411465000f04407800200400600c0d0301100454290010f110034444d0412040350380c0c02143c100b0501c3c00006280b03440d192107014120100b40b02000c9074000c24a450342e071151003e10408142081c200341d59090003944c6000918a0300d4076420409 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 970934559 1250 970933309 970933321
    0x2070f0807210b15030309040603030905010f0504050d0f0212060f06100f0c0201110a0c0f05010e1c080708040305100506010912210912030e0f0f090a090206040b0c07030605 76
    0x44010b6940e50700016100f9069031039210495141010300070481d458002000358080070b603600d20030b1030051030180d910b99030075609220001d0300b5038042c0c0c101c40f8203100302400100040c0c0c1d5a24003081250760b1050500c0400642440420300c1d0201d0007000103003501408042003e0b1452100d00d152040100301c402c2c0c0070b80c000e0070405807005030042c400c040008003146030b1200503500640c07103003205860070012100050780310b48031054542a9504105026602000104015a44400c0b9090401c100300c90040d044038080b045117500b15140c0800404004000c508041804050001d5074020341c0c001083e07910084c1c448807208010441280c0039404903181140c041014841a8806030344650701060301c403190210141c0300d640440300301c51038108015a962001c103000d10302c0d181ca10f5010f0b00c00d45416580300580070401c900b00207a10002c03400303000440e00f00b29260b41d4603014281c000345050340002d802ca0041c008108103218a8010145981e00003c00c42004940002e004080f40d0085604010507181e81c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 970935809 1250 970934559 970934609
    0x120d050a1418120309180402030c030f1f0902042c010c021902060d0e1f02030c220b0a2a050309130e06070f0f021204120302070f0807 59
    0xc0e41000c2044803507455002d100d410316540c402c912888040449080003809400103201508a11010340226000d200340021410300f040f0a1000303120440c00351519145036445207a940204134610038041005800b81c3c1c586914a5201c4880240c0141003408070b801054080c401424102605490b900700c8401f0702c174101c58040c4180c10030000a94041c0c4400440000c0b000003c848448060343d110104202ca00b4a0407118800d404000313290001410300c14030355041c0e05895046481011120034010000c104440d004d007000c443d928a04220b810b05a40007203c80b201b140d500c2900580004880041e0000c01070342c1104a05c03039010042120741c001d008a170700080f02240550b03a8001c1440d407050052611301d240281c040700400c2d01030400020034428094171280f4000003a030341d06020890300c0c030030120169407042464603c0007083c0000c0915500c810401c00c82c6201703511a0715107203030204031070400305442840303828001d003014507604500075110501d0645507040b074032480c0f006c15600089000e1520003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 970937059 1250 970935809 970935817
    0x80114030a050c010c080912060105100908070e07121d0d020a020a0905330a0e0f041407050a0815070206010e040803060d0803040f0302070f030f060b120d050a14 71
    0x120002906100b00c00f0401074481c000160801ca80c1c8100500000c000d03621140300ea41080c071211001000c040d403600041c482001080303c10f90b802c10480c0d182c00d000402c000619482103c1e050004030a165454040480d83c190364455005001d506025480148010701c0a040c529401140182c8002d8520400c0c180d035910301c00c2800a41100c1c109008000449580c0e0115512018030100300c1345a90f6001c04e000e408440c40d2a0141883d030703042101943c2802c00b9100000905180f4208040302d0510950480001900800040c2032100b4148140c0b90110706008440003804040c00748040c050702d0302c060329200c10402e00380c8050100107000003100c1d6072002800ba8100c5009520001302520785884104699000402d0306030407140b04182c1c2030001e1107450041d4030940c02650071030700d1884a0300d002814101e01c5d600205020303e0700c41c5e00307001140701040361007201e50740320000144a4203040040303110b040a10aa40340c91703014810742000c2d00c0d0f4102c1c0040100900584d900040705649803401d0302c039401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 970938309 1250 970937059 970937063
    0xe2710061503060e16020c120615040e1c260108060705030709090b061e0c0f1b060903010b030307080307080c040308040b16170c01060e0f1f05040507080114030a 71
    0x10013007003c02c8401107540d0304009003002500c1610040300284010440c201101c80c40c5800a900c044104600020084040c00d800c0600319004e014802e454805103070780300681d400d40c5075002171505804041901410020a6030140008290100c0400025801c24040248103510441c0030382c01c002500280308804032482010750b0b032500340c15142000b001500620504807841d400c480204020043c2c0b005100c0403c500381d40070360380c045e90b500c5541c18030307410440700343c0c051481540580d88610399540011307503841d003020003a2590754403020000300281c05411040a40b0380c2501000507050203102000c0002c52148075161600381203519884040b51261103188009013041744288030a010542c16000244000120311714030a5581103251100080e120707000c0c10350040c80fa030004043c08000380a009010091109101ca24030a1501440c0e02c001001c008221112800c0c00300c2600c540d61a10042c087c1c042c0002400402841c40c3c803000103001404c00780580c00c0c2000d2030401c42440741c035000408100340c0d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 970939559 1250 970938309 970938329
    0x2203120f03150f290d06030201030c020f0607030e0a081801091a07080c16090218040203040f02060903120c062202030d230c0a1a010e271006150306 65
    0x3d450030856401403ca00314605803200220800303c10040440405400000311105000490700d24501c009421203c9081e440001d40d0442440f108c2e0006c00031440d1544074905040c041504202e55809508008040c0e0000b4240640030410302000c100702030129061017000e89601240302d403940114440d100981c641280d0500c810080c80c4005015170300079100030310291007190340c5031141c030358844120f1a0640112042c4c80e03000c500741e503548081840208001c54260303021407039402d20b9110005007103014000030303000756400500c2e4074060310200203600140348025071090300c075010319280b66103a403030540d509000304406961080c6912000c862440f41594003c00501d0041030310001500c0411508070001e039017119485246960029003402480840c40361409040e00c0f505038602140340143e400414518402c1560040c4911521001c015170040342146141d80c0c051000302c44018403140401444403503000d503940f00c0750345030056000101a60381d40f03801c1410562000782c0c2241100d515100e040c0061b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 970940809 1250 970939559 970939589
    0xc0f030402060a0c02040e0a0203010c05090102280c091b0f0806040c03110424090501050412080f07051b040b0f0d02060f070302072102062203120f0315 67
    0x1803502c04001c0021064a0038080d01405081d000901200c002c1d140802c800d07003050050404528080c4221074481e00e183c10140c2c200804040001c2d5500013081d18609201010321490f420170209180004880d94000842c1c4072150300e0351f111601a0400d070344a219480107111015486038000c014075221a41ca41e13560200b940c1d1100d04000150a000041c801415a40d0b0030300c1e920010201700400140030554580700e003500014034070b0740344844900e1228040001c04003041c40541ea02c6403c560031609034030400a081411800d005600b8460700040c01400003002920508010000c64290203e0440c0104500c0d0701140c40c090106890b80344a015074051183c0b60802d10620301001502c21507800034040608103884082281c0c641d500010701940941e025500c10400b024604035104000001030055071400c40c41580485e586008252020200c02005124100b141008000c4c502c02190001084125022100800f4055800c06e407990070010b414120301000801c2c42c0300c100d40840701c03071a5507a150 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 970942059 1250 970940809 970940813
    0x110a050607061503120f02060604060b03130804051003060611061504020a020a0b1f0b0403020a150e1e190e1305151e010e040c1806180c03050c0f0304 66
    0x245054544010610f030344000c0400841c5210303000380e01300e071825101c62148210f8020080d150010051000f4400c609000f0140b00f00c1038008107036034001c4c0000100500d55001440c2c1060a401141c02054000c411160300c110400d605070411811652542c035128600c1d04c000c0c0001d034445101311103120081c00140341020300d83c1410760040c140c901c820b03c1502d07038110050366400c50900e0142e5401e5160050113003035811005946504800801e001400350703140030b15603400320320300914510807104070213511448048240c0c001e40c00d41c078103c403001741070498128070740011443c6075400c210914022505849510400900300c60350301c081e500d880c4050500c6588401c0c00002c081c4055208035107a02801040540c01e404443e03856000303101d80c0c1c800d40c52003140310000000c8010140e210000d44c85002c070074400400e10407081c140945030f107580600e504112610404000d0400303130f4043c281400991140c4c00300c041c4298000104884103507810b000d00c0e19800d2510340d00f40690700110001403401c101043c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 970943309 1250 970942059 970942061
    0xf0e070f05090d02040207060b03281b0e070201060911040b120703020909010e0a0b040902010c02011d1201240e0c13090e0f0d030216230607020a110a05060706 70
    0x200c2c08100800082c0c00303060f40c2e40410140d03006200c00b00c0e4159150b00120f580351901307001c840c0d0ba0340c00b94055181d01c170000c190040300c80c1d600c1311000b52540036101f03507015603081c203903519501400b1101082c22003801c100e00001d008094a02c142c0c00d0300c6280c1a00441503159060444040320000d1008605281c46918526647c40c0064500b0b4241a030801c003511840d155901c010f4000d14442c443c041e40c9143c80405403080da204181c5040c130031890680e0040050b0f8000034010400f035028038080d1101c0036141c002640220030742d5070096001400100d4942b0060054000b404440102480c420000340d104005100c3c828060040d45d0798454800005140704043d00f000e80050b0407103204e0201c40039070301d550002c11603c1a0010340001d0308000d51880d101c2c0b03800c0040219003c51454110300d84205c0720b041503990b07800a000100000e1184540c1a40140c01c0000f92011904c03640c141d44650030104000781d0b407009600c404566152610700c03001c080303140000082040360070240a4614016495a401e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 970944559 1250 970943309 970943317
    0x30509071505070506060307030b1302011110020c28031103041a0421080d0b0312031f09061d1e0a021e0f0702010f050c0f070f0e070f05 60
    0x104510035000001549804040c20180e0062030b515207556842c00b90038040e09205c4c0c000d1031903010b6030020300200001350384503902942c0083c8900c025a40724015200403140403810b0711359081248145500101d0b120030b160b004000d001c0c940c0b000c4540c0c0d04054a410030283d00c03c084150300e4140052000c8000ca806250b03a43c90010110041d01d150648a040003401540325041807205228042010f103c49210080c081c00700394600d45034541990b40c0c03a96100d4062044d2074039080b051391958028501c1e030b1420050348216205102c1000d07181d290003071344148007003035031340c008000c80030700c00400941c440c402d10800c01580c55180031039101d49418401c40201300800303081000340c84481c13a60307401c02250f0703803546502a618885000d0f0f47e2301310004206d811345d642170001c00c015440402070780c49601501c2049501c169420700b06145240722100c82070f5080e0051804108840c0109546101c0402002c600d14068880600f03400c41819103a00c1a241500021600000807e1254240d0513000d40148058 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 970945809 1250 970944559 970944571
    0x1107060b0a0317190302070c03140309060d0c080718231003050603010e01020901051608040b0a0c031704121202190503061804020310051306020f030f06100f0305 71
    0x62444103980760380e140e40c448078880d80108150f0001c02c0501c15070445000000311240702d8603003035042180585499100502d6880300412013030362040480c40b001014004c0e40e01d118401005643c68842302107034080a0302c05008a14002800e030300c0002d458602843c0c20306c070941896034210210034142640c50940091305405401c5000b2045003032001a511103030000080f01140c3e4010800e410302009040c25242c041e40b84001d00d9006010341811a640f04c0141c030032508100900650a08250806030264450764200301c5030100001514040e550f0044045210144290f035160409841004007800c00c0ca01a10003c0c1084d030440070859149200c2c005014105103039901c01413500451241209444150300a40c402240012042140300d01c0c0143d0801506015107500808514003540060784070f120380b40303c1420350780e03840340820b0003c0190103105a0440c0d104800f10740e1200449802031164204446906c0109070343c20002e00c00b41030404a040c1d04114540710b0300e0401d200e103801600a0a030003000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 970947059 1250 970945809 970945819
    0x40f0b09030102070624060e060a120b0d0b0915060d02061e041e0e07080c070303020c0d05071103070b03130f2910150c0204091a1008011107060b 64
    0x9802107a05413043c241c020341c9201c9091201c101c02400889840102d034082c4040c04003c1c00381d235182c0c0d100c41e02158440003040c0ba000b2180c02c0d009106000070f110515096400c9001301d001001002010400c06001d00428011900030036842035080d400b0003030032a01642c00108050144d0300500f41800a4610340030780c034151000704d10702d1700504d00054005078069407030000c10340e0414881203a0148602c0c0981031040c04001d0034541220301a01c10000a001000d5082000400350305061003a07050310840402081030b00d8490204201c02080c9030040502980d20003500b0b000c00d06580340000b0f251003207134111a401425607480c500c010702c10a05555080d80c12222511280c0c0004d0544aa007194011000c89804040030012500f07202c2820010072080c41c40781000e0080c0140c801c0044410f000030304a02d00302c0510103840c03001c64041c4c051908020008400207001400391180706582c903114220500b42042c0c01986e8264603401d958000c1031040903c6410018100460182d811400030041c010301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 970948309 1250 970947059 970947067
    0x1030f0f030302120c0a090b090913150608030d0f020a02100c2304240212130e07080105030d0c0b041104021b06040201020c0411120907120602071205040f0b09030102 73
    0x641d07400c884e2000c803241400b1183c001001c081442e0403c3c1d0760806005134884d0345046c1008103001c11040e0384090f00f00b81802403460701c94010404110003521096100e00c401384603840d5100700140d0750f50016680700b140a810b1200c1451840b00900c00c3e1031a00c0c120303a00038035541781001c5181004010031440d6008108020701c85e0790f8203541031280c0c18041160500c07115903542c40d0904005c1c8003036298440b0014100d60041c40142e603135000800210110480c4001030b47da02941c41d198009001580c08207946200c001c1c1001101600310050038101c030819026203c0c490b417055000c640d40180c09500400119141c0301040204044003411035103c400944010716295110400c05002d60401404c6101640460100811945d0500103141b4986042d02c041c44040e482c044000f00d54004c022440c0c2070760600a002441110081000000424546a030342e0031900d0f00d030030301034081e600103581075074008003240440351128412001c8504894540051000c40c60500c210508603600942415602d590248 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 970949559 1250 970948309 970948327
    0x623150c10110c0102130905070908063606040308010b0319230c0d0e010507080a0902040603021c0201030608062206020d110712020f030a050c280c080601030f0f030302 74
    0x440100202201c6c050309030103443c6044c403400180d03000107002004012103080c0401c0f004a0000e1046c0e007011030840034603114a1000c01400c5801955211000d0a0a85000001c0c00200c0400c03010b02541c026a41c42d01e03941c1c0c844802d4000c3c0d11041c1c4800c0c07402010340840d0b4550002030340c0240b415059070000008a071010480401907440151a111400840042d44807205d5030399110310010344243c0002400280f4000d0300141c00080c00a010b03006060303c2d900c00c0b9085540b83c0d44400b01840c0c1c0104003c8902000380c1c0443c81c80000d039030b0100c1c0840e24240c00441d60b00d41c0010325500c40c003001549441d6800d4040040440b40c1c81541049940d0354003440013001e946500c2c084c0c44208541070841c0d940355801c1b400c00544c6581c90400b520b00b950003010310245d210102000b00d402c081740c0303410020341d662040c03035503a80f030281c0380e003415800c00a001c0d0380c480501d41c0380c0221190050255190544250b1180a0140c8030b00c3c0a1100604440c00d24003200001392415094102c1503009041c0181019004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 970950809 1250 970949559 970949561
    0x6010f200601030321140f0a02070c03032f0c010e010908060f0a0b0103020c250e040f05070518010612060909050c010f0e0f04020c010623150c10110c01 67
    0xa030001c6000c640304081441c0d0340f44041e6044060240d8035482802281e584006c01c0c00990380280404100d01c0b019400262500d5003074049503440c607031111803598519941d0a00034012000e4400c407581c0c507030b00b8090b2400c42d02c5e182e21880c400040205d010303003030800e142801911414040d0300d1341030600c4a40100020703804820310409201e440b00d0920741c42e0618200500504030340f41d00040505141c414803000e415150300052089000081c08071490710010900c190140c807005550110340c4448008040100b0040e000070300c225030a01c5030040300c0b12151104100082008002202105a0071840040044034890044208886000310001034529159003ca5003a120200e030150399a0b800107000380a10b5034480580c2030540389130300d0201150035841e00000c004600c40100c9130320032a00803601b555240e000f075105900a0078032010494003a4840031420706940312402c110b81c440c2c0403424058451420f0a0101c0b00c58650030310141281442094081005104041c3c0c02110010140480300300010b003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 970952059 1250 970950809 970950811
    0x61c240b0604121a040506060d1b0801140c040e07030f02070f0308060118080c010302210f18120a030221010b0c07080304060903080a170f06100806010f2006 69
    0x40075000d200e08510ba00b4a0f132110302e0304203d00910862010204004680e0110300d094200e43c00302ca611074000c01e10304051030301c03401e913031001c08450a4610001410200551050911000c2c0e501c204013a5941d240b481c040f90301440c4250680030000e4000910001d00c00e03800352040d030491500c010708055854450078040111750a00b00e0201c2ca05000340700751580c000c10380d00303480314800311804507045c204404aa101c00c280c00310103040c10780200f0394020310001552010008144203902c00751070715041942c070f00c80c58803c0d203543c0c1da511000b4002c13210440002c20018034004060480b41d24040f40d900d8110020f6000e1840c00d003030040f118140c194401c030901d2500c2c1c020011002519201c1100d6100d0504040c0789620849880d4030410082080070703044036140045941112595803290b068403425540407455004c6c0459400c0719a0070006c80301c4120166a024000a840b00803504962a0065032080c0040d1001d50105403d8644050000d00c104400550141002800402001c0350002d2605d8100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 970953309 1250 970952059 970952069
    0x51605010f0f05060a030c050f01050f0a1806030207031b020d2001030e0601030506070c03050408100f0e2b0228060c02120a030b0105071a061c240b0604 67
    0x40c5070055078802c5940c5004054100f40112102008140b0319560703240550054403c1d50f00422284003c1212603010b9410b0341c103000310f085515503541c45000c0703000300140c0181d107030240c860009a00208403148603109031100141d02d6103a41000d4002860b40105c2d0886407401240d001d5080461100000e1500303411998009401c90642d4000003d080054107545e004c1d0045441c03980304038010004541d00140c0c45420405c28204003031594001e0030201d030507210369041006136104140b200c4052202640c007c901840c0c1400c0d081040c041140c107020780307546d6804000790064070340300c141540900ca01610b940d1010080d0040740c004501c507419115051260703d1140e8206182061580d086c00814043c000907944184084c14121548410400c5a07000b40c5482d2410159a20708402d4503034000d0080fa840240c100302c2c0c08041260051a4944240d03040343c080d40280003031403c040c5907200c0070700d480d000d40398440c01130b44042034031108143c1f00300d40340480c4901039502d554000650f500c6403401800501 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 970954559 1250 970953309 970953311
    0xd09140a1d01061121160506040305030103020411030601050304110301180312150303140d140c13140a0e0c09040e0601141017100509070f09080309060a051605010f 72
    0xd8502200502101c05010b103104d0181c2140384c11480c0b5140c0310a080070070301852092262030f1080d502c0303412841204400000c080e4400c007020312040c15004009507048a20864052000c03102c5181000c0070342c001582d100303020500601c04a40000d0441100083d4a04064000149000c1d00e84061038640222901980401c006e200c4110701c0b12610700a00c61a4824100c141d2291440d41c0d9004000703031280036042584580114480c0d1480000703420011040601880da100c1600b0312351034284e038961082c1d00c01c880e0310100007000241c15126228008010320010815240395103880089c078203a15005000a03011182005a0351884c0d40d42c0c80351112002c2108010002c2d50f0502a400f070710365200c102c9040c824840b10a104c040b041c0d000ca803004969065800d08445519070740c3c0e0382c3c1c240610035040254490000c90400269550101039034000c604681c3d50b075400207a8030140c85481e03105074060150080300c20070203211a6800b9030001d1190784840c21280b00c610b074442c0c07600c41c2150403040c240e6040e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 970955809 1250 970954559 970954561
    0xc173403021b16060804050c030a08121302031c1206060c1e11060702030336090c0a111c020303190b030a02040e030906030a0b0907020d09140a1d 64
    0x196403a896a00c1100203140700070b221010f008200e1441d601500d10858081240c42000501006824440005030032809001c40301c7c22074140c5007050396500040300c490700c84031110001940d010403d05000103603603006800723450006e039118101c4c1c2080210343d1840041c03059440610109400324480c005c001e15003661600da100b1800c0c94080301c02901d0003c13151005c0b8010b80e542021442060400102c1030044a14960302c202d00d2012030b0860054554947c20034511034608010406207038800c001c4154a10a0340000e020540c0400c4484101943e5088500c2820b0004d094103500503207e24088440d41e5045500030400d400d1110818400183c2410041e000801445070356511008000d064030003441d401e0080344c2c60840826030f22000584003030321594131015950b40c2440c3c1030044800300e14029200710381d00e01d400061100900403028083d0300071403c000000c0d91141c404504c030916001c06549166802d858001c0e00d01c800c074018084564440c50410300000d00c1d2422509900d5000c0c5003003040d41017 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 970957059 1250 970955809 970955827
    0x3020d0e0604050a06110a1209140109061b0201060b0702130b130903020c120d0309030e120307020307081603110102120304120f050a05071e0203061008010c17340302 73
    0x6c0d41c25606080500349014803100c48030a030098640c0c4004083c504001491461a0074022810010007940d903806500c1c00004a06110f031070341081e00d001d001075110f991100c4c11148200d0072224507115050080100b4000030006180403151110b100e02d030f500c03020030070203224800035034402002d80c4400c90003a9161004410075030140603000580404468106000e00008141c680f03446040c6554400c0544c2c07038045170300b0540244007000d90018054460442100180100e5036a603014201c160720901c03890400040c80d000008030850b040740089060340020f0310f1962080c90b603c085511240c158042c0d4001c0e05036480320707540510b0bc1a8006c0082c05e0005c1c56400d0050325070740d500260b09040200c00c001c0d0018468200e8126442680e0111660709502070400011107203040c1d2410096050007203005100c842d00f0720301e0501e420340d03102c1e00007080042092001a58004040601211603003404d43c0040d4111580e58040c40030090f000321aa50001450110410283c000d9024600440e80c0499580c0d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 970958309 1250 970957059 970957061
    0x711030c0604083004090e0f0f01090213112d0703090e06010c050303181002070c05130203150904030201090213151e09091403040603060302040f14010603020d0e0604050a06 76
    0x801400303403e4401341c003507164044603440c0c41136001d030403200ca445100c0c40c401030804003c030030442024101234400c8030f03e2681c4403a020700068141a0702ca52525030719481c103483c50380709400c0031035040304045190031141c40d0308010303002c000010907a510082542482c200d04412004100c024403a5a88280c00741c100080c0c0c00903800c0243c2104d0401003000103420005000208490b04801070000251900e1140001d8500d020b40d5a100350b4030260021071000200942076443c6d800b41d600840303005984224003001c2008a000c1255010300c0b0141c42210040c80d420700124140d0028002d100104454403a6008200c559150300c01c85540603503241200d2038a900758250600180289200c426264040c3d0009400700c48002c0c000c0140f0281d4a25030301c1c0c00c010808070200024511380c4284c0ba100e65a41d0f20282c0145207520090307020700d09040181c8007014440c41205000d108440c0c0c017030300c42d90825504900139003000c01c1c041010340c0d5840040460007002c000c02c500c00c52140c1d004062600061030510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 970959559 1250 970958309 970958353
    0x1c02240103020a060302090d1b1d040b07021b0d03170f0402030d050c0a140a020306010f0915120b0606040504020723060702120304020109030606180b03030306060711030c060408 78
    0x102c01c1501c107100b01c5500384e403541c08000c8c204e03400c0741010040401c58060702c5050811540b11010f920071042903483c3d913014040754548500d000b4807804041c1d84c0c1c0e843d004da0701c800c0455100341d00c1a041070307038001d1035182542c008903203e40685001640710304001d05035032a00a09580038412902c030384040208500d002c0151800c01d00803450540d00f4100c0344140782da581c14000342c004103411014480180c02190030031040080c10b07001411120300e541d403100c21a225020b14058000464106101e03511800306503949a011180b16801502c0c000c1f43c9500c0300401b600340a04003a621003001c0100242c1e503a21400903201140c09500b0402c1a402107140c0d00f42081c1d410394024060f07421030410440741a4021608080a00c01680c141d680c0c0c1d80c503480121103414490b000200b9091400901041c008040c040e49107200709803140801004030440105507603400f088503510350100081049100083c1100c19040d1031500107400c4450360941207000070b445411503044007625500c1100200d04052054081d9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 970960809 1250 970959559 970959569
    0x303020702040e030922180b070e0a06050a08151f03050f01032409020301020a08090d08090c0409051c05130b12040204090f0609120f030b031c02240103020a 69
    0x10342c038060495001c90b02c02800e800101c50355000c003c0c080703202070740d86400c568403503800e48195012520071f500e02580a41d07030a80e00b031f500094411000c0c041500303100300da0a00b1385e035480d00d489003401080081200c00b400010428081140c1d0743c0441c200c581c5a680c0c00c04480c5105590810034030241c0e00d401000c468008001800700c000b50b0340100003082028240c196440d0b804004416000060300346540517069415009406610018072502850750200c110380c040d208960903141c600e401548202d89540042d03078500c0e01500b00300c004088500c1d141d4032026280b8807460035520030081c10941142d10405034140c03040410b07030000711000005034035200c40c8054140440400e09050511481e403603201c000400c024001d5075078180c0d840902030503800f80c8a01c19070201040c0044a52803900859903910054a40c0c0401c100510b40c0600500900610200040260050501d003a408803a5403200d490806039901f5400b4028540428a1101c1ea0f8100c003140700740040e00744d035455403050040a030055805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 970962059 1250 970960809 970960813
    0x150a0f0c0f02010507020a120b01060e06090108060f0a0306020d06080601061e03090201121503021e150a180906050a09020a051b120a0216081230040303020702040e 72
    0x1800001441c6102100d559902883c0c61522001c8500c04986414155049422a04032400030b5000b041107034075144c0c2c10f84005a40d10a04c048200007402483d0141038609804034030075200042c85424144660021464001c02c041c4001e03649868543c1241d00c584001a016521090203006020302000881d004108515025006204801002c0018420170f915070f410141c03903403c42010b41e0321031030060822400c0c20008220038a0a410f102c03081d86401c1c80700b00e015031161210b8952901e03450030030100810b400380c03200740035800700e044801d415800820f1450600808031000f852800801038020040c0165240018281e4140010055104520380c0803000d41030040010048296001003070b540e200444110b070244908980c4a11820b0100445641418a10210b65018419030004180300340d5100d451200a581d9241c5440640b9071310f16000700b6004030340030407a030300d85802c041c0d5803440701c005410f0b008003400d0003108144007107140940701500080d40225817103095151501c00c910803101c000740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 970963309 1250 970962059 970962077
    0xd0e030a0311010204151101051b0a080441010204030804270219080f060f0105030a0212010e0a051f09090807080d2a050306040506010e150a0f 63
    0x26520900248014100103912003071800b02d0310250140c0b00036081001c0707215003444402c0c03001400d441c0720000c0307211150b003402d0209068848041c40480c0440c144000585050046142668402c01c040e104403007207c14a01c60003403070041548a01d644500c108000000c110425a04e41c00503224400c45e600b059104000c2080001c181804440031504900c5180f103082d0034a94500d01380e0316004000e050341600004021042c403a412100e000f20700f5250300e50780f506440c0c50a07000e4505000b280c80c15008003c1480400319507009a0180da8000d01c2c0c12405440c0c042d0084070420418001e074040854500041c06020308208203005440d80007101c1041c043c4000c21a400c81c0082d04140d00c40d000300300d81d580e0200d9081c00081021201c8194020344916960000110070000501000919032410b1a106000d401c417100b1070340d086001d070396240d520541103442d200100300c0203250103407085060046010301801c2d180c8842d02401011450940030a07191001c0070b801900500380f40c4017113030800480766 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 970964559 1250 970963309 970963337
    0x100e010e090c07050a03020f0d09050f0d080f0c060f06100e06090a080303010b0901030b10090501143108013b0a05030c010b010309020f040903030b040e07080d 70
    0x94554021114408030351103440c58050701d0320401402500e14000d100c1010281500007888d000226540780840750f0241950004442e02c0509014881d030048902100c1800752505000c2d079141140604002882c0c469951800c0c44a5030002440141c1c40d00030004110507010800300341580712401390f55485007800e0342d00004000c0315807a81c0e41480384e000810a500701c0c2c0c9900100d5400740c0600380445c2d54075612046101e42c030740c02c5800388178006400c0800d03503683c0c2c1c1080d00408100c40c1950b22210022820400151682e2503161000d210503201030280800c0f580b40840d04c40484017003000c0107000300c140c15081c00c8219810b40c0011b8090381c1030200040c0c2000000c0c0005502c60a40e24081030381c00301c039251428200c880300003070210601c126000103040c031601000030101c6406642c001c00920740f10308019803d440040b10069070140103400c414a00d42499000082518424680001c80003010400035040b11641d801c2c103046030340f0511080c0310b0a941000060300c401500d051040705c0159103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 970965809 1250 970964559 970964567
    0xe010b03040b0609150a060806280605030405120307030b04050604020f040902090a090c05220e04061a041104050f1807200d0305091009021e150c01020306100e01 71
    0xe4031240c044c6481e100041d004070aa0140c441c044040100045407003592000010040d60303084e2001e91141e0440410540d500c6140c270f8035203c407600740b140d0104425160400680321504028401d45641c0140b50004c502802000002c3d80b1807009a1400a00c54202030144000c403000100228010741c41004070a51000c0c0000070f40e0200c505000c00580d032120300b440880e40b940790380d03805589050b0804502c860724580082c00380c03100410000d096100ca880325544c40d004030010b4801c1c85040310044000c9400b04d1400e800240200c079240b840b1140285031003000c58100c41d110000390580c00404a018003003850440420300d06204c0455000749241040e05500f21003031000340510f01400001c00502042c4135441011281001c5003805a5030f0112551401901820040710426244c1c0100405521101e129108030701040c2c0d0007801c400b4070034500c000420811840302000c0c03036110003142118817010700700d5030050410038074030800561a42000340500041e8034100c03403211b05100f038103a13000f101c0782da03c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 970967059 1250 970965809 970965811
    0x4150c08010603050a0e0c1e040c0e090703150e0a09150b040c0c02101808030f1201051f210501090b04061d0c090d0501020c0a05070506040b030118110c070e010b03040b 74
    0xc80e8107400723400c081d141201c90304050703500700b5070824209130303101c0d100540110201c0c0c403c5905139046802c0e6a078000003282180c01910340c2d803a01c0e000400d014066655000c0b6002d52000b04440e00048800017030f110090544154100700f02c04035101e076017100c1d5608050160111000b007501307148080652507400901000301040c495000c00503a00d111448100b21083c040004142c018145e81d038030200c0e0410101241c0c0840c03078902c0b554022100018203400c1206000b800700b901d42144601c0040b549004481e0681181040701d19810072445000b10813100d4490507000b4602901d00213801005071703082c401510303015407140c0e080e00500c0780c2e002c201c0c0c280881d02c10360009004c10010b5941d100c100004d0b02c03e107a01d8001508542c4040341980c18640b002503004001401001114540c070355490420283c0d104600603c00320340c1c002c3c001000400031000e9906c0d01c00195607000301e2941d560001c0a05150003075080018a90701c000010400c0503512030350395000d0043c4806041c550315258450644040c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 970968309 1250 970967059 970967083
    0x90207170306030a0f0812010e0c032701060807180b031c03020d0c18080102032206060e0c03040309080309060405060a0c1b08070518070804150c08010603050a0e 71
    0x100000082d103039503080c0143c8407102d91089080244000600300101d17a82c1107840e006403800c1829001203199070190341c5040c89850854030592450369440b02c000444014000c1005d120041d2140500f450b43c0c00f805264090480a4010300d0454070786000058a4440c0700340e401e0079546441003000668402150b460310a825421400d03c4012650303008070001e00c10000b1400c01035152100c000d282ca070344001203c01444110851f4076005072600006409c0f8071060f01e400c15042c41d4031514040e072803900e0021400140c020000041c0c6181e8841079404521070482d203914452900000300400c168114140801810b0010007c60901e031340361000c204644100d000b40c0344241c1c07000c1010598203204001000045600241c11100030180003000c0019031b071030380907180c5103004082c000300b21820325645224100354101c0031647c2640b109201078929a90291050300c0c14074400152409254242c044d200c02c1d81c007559103907001903142040c0201290030180101d66603d081030074140004100107020b880e180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 970969559 1250 970968309 970968353
    0x302210624071a091e072304050c0c150105060a03112b0b031207110a030b070c02100c021e01110a0605060f010c1e0201030b04090605060a090207 64
    0x9804020700e600079001e81c1c0710080400d8440103000d010300c10001945400303030035403000321510346074000c54a0643c0d0903002002601a40f01c0c3e04d04110364980c103001c414071400468860b020900000c00400c0960b501180e0b60007180700c00184001003040e00308115951460562020317201d5505100003d1258407800240204064032201c40c0188405001c084440304402000303092000c08900c404016005640c9003000907991402d200e00d200c1341004540d83c0f4125107400c0c103242c90708480e03541d00d55680c24002a009e800c403091000c003000241d44640c4040c018111916101340d005600d10420001041940b124020021204240c40058980150142408034680812103407101e00e140100c480c6d840f0103440f8001e03441043c820b4014403449611550299900342d0310301d0707580e41c031003001907070b840110740c0004241c00b42060f0314280102241c40801c81d000d105250200d0308855444c00141610030b00382040e148142e8540c107010803460440850030017008140410f50401210740c8880e04030034000852100c0b05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 970970809 1250 970969559 970969609
    0x9070807051011011406090a02040f091104080a140c0f010c030309060e03040e1005030c0102120901030b1e0103050a1505010806180f07030b061e0d0b0301020a03022106 74
    0x380125420703d024500d41000b049030401003105000b4509055458500681e04070011424402c500c0c0211002d032a09100303103160700b902c1e040340c00c0700038803203407122120b0500180000300700c130351060000280701400707401c10810440c00003640038140600071202078403a01079075807125a1079800100b40c0c40d4040d007505002420201c0c90620b60040c000031106402540400580800d40ea00c540f540240a8000d40503044486038840080c140e403410300700900fa0240c1c1c408404860270050036802041e03802018500800d81611b5035000c11000c2034507800c0d605079048680c0b040d100c00e50341445416406582ca41c0d0034001c1d04182416040c4400007406851b04000841001600e15103400b2181019000c2c0101c104819180c0300080400010702a5038944c0042d0a0514075002e070300d4003d0954031902e8808001d840c06440c01101100c0a50044074419145a2155521201c0f40d40a101070400c05007191005642d0b29500340103c0020300e541d042070701e12209186c0074002a502d0301d03c4110010310821151140b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 970972059 1250 970970809 970970839
    0x1b060509010e0d0f080a0c020307200a03080a0f0206010b0f0d14150109080a0203100f09021210150305060403031107061a0108060102031e13030c0b030f0907080705 72
    0x142c1400060a440c43c0300398011100c420340c1c0500c000f074424503241c0d40c3e2201611008022015170390501a5040180d009200c0c41c2c0c04102d038a401002200d03408140b4458084a9801003008840c0300d5209449040010401050700c917044005080d451100744041d1045604244d81b9281c5400350400600c41024085418041c1a080307034880c428002100c0c038040380602e451420350706280083c40c2c103180003a82d82400054000d000160041c3d04a60041c080c11408200582403c0105000e142c00840301e6203900045000d600e0b0102240040391001019000c0956103040442c00d417103954544050388840d107081000860004950341d50820f038185000b05001440651190840c020014003500940c505040c90140388410301c980c40729148280c03613001e000d903907400040ea00c07400303014014035482c60710303c00406151501800400c8082040300d02c01109944907190788680d424140c01c0701001503400802e0080c03800c80300000395889141c080c000c0c0a002d06102409458400e144640c0b80034008035102681 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 970973309 1250 970972059 970972061
    0x151a0c06011502100f2304120c171b060c0703090e040812090706030507320d060e090f01090302070603020a0915020c0f09070c032f070f061b06050901 66
    0xb00a13200c241d0b051284c0f80e101840000201610310469000a084d951410702c19000084090b10035a0041502c41d800c40850340f05484001040382c0880301e416081145180740c100d280003134054401040c4020224501c10003080f854020080c142c0c0426800070301c0520006036000c005a1305985114041e03414039242e0707150645032030241d040309400070500704041100d4410009000380449880303660900c481e0b00ca07000140d451501d034825070300d400ca0f0001440c00c6d001e44032802c0d600314801080750b19460a04020255412500b0640090b042900b0b03500a010a2240800c184003d41080400811450185a8005e980c50600384200342c2410f4001c1000c640c0507001c1d01101d4005c02c04103180102c2d01260f508000e49403006082c05034803072a40e80184a041c0d041c0400c00e84e00c550001d480f00c008030400b51300d09070313030740880344100c00219100442c2c6000d01700c0354484402281000c10005101c05810400d1003035542d04150008820001c8651040303100100b00385410300035680181d8005003540710444032034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 970974559 1250 970973309 970973323
    0x70305090c0103200309030a0810120204051b16050f121902010b04020a030b030d03050c03151f08041703100e0a0b0d260c0c010819151a0c06011502 65
    0x3040c4d0008000c00030f80c0400800100750021040c0da0309180c0e40d40b080c0d8000c1400d032041c050460326110865a000050606500103a00280d001100c810303020a118480134103035210402c20030400c0703010603651040010420244050540e89805401490401034100c441809001104202003084011b49800f070350007036001040c5198094015540d5a0310303150050090071080407181d00904c034110031500028070030300c64030340240414a002c600d507480d01003e0380382110343c010501c1d6205040c003113010b0300303c40c80580101840046460311415454242049184030300300300c0c818803200c80c04108020388141000c007101c0607240b00088107042500e5150440c0014030b0090070a035004401c0400311414800d56903880030995860300c542d0b0015a00d0002c0b0756505001d5518444440c0d44055200807582d0f000b085600e03400b0000c00c480c1c3c0f20314001800040151200b505042103030070804c40382442203841c1d0fa174003c07031200c1400700c0d910300e815680b041c001c1d034911f014410f200c02d003e0340a21910b011031003805a1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 970975809 1250 970974559 970974611
    0x110a1a09090421020102130501080601020d030c0203040f08070e0702030c07030b130b0f1014090606031f09020414090403081f08030f1b0607020d08060a03020a08060609070305090c0103 81
    0x4903603c01d848000c068001c1d4092090081c200c602e1300d00004140d840b4a00080c415070040c1e01600e031032440b600c016000b5011201c01c002c190701003404042481d848100301c2800030840140200591890700340402d0001101810302c00454000700200b0340420703c0010594100c0e9400024030509580e00c080b40e1092400985000788464044c0c428080e6140551030080c0c02a04c0100e5020080c1e0f0f07031901000281d10341d1542c140c0d0400e8000c0009840c0303140c400051640565045842542d880a090319004119905d800c00c0024560204060110182108240f43c20103029110254241810317180038060321802041d0104216042c094440000440301390310b0300901903d01183d84030041c14501000c5600201e900d1320242204d06c0f188035007024002007450140805030007038021100356000407a29580d005000d80d402c00c02e007540002c0140c5902d404800240310500240606052400c20040405400340901e002c140c248014070150060128a40c46c0a4509080000d0003685203810044000010040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 970977059 1250 970975809 970975853
    0xe0a0309150e06030f100e190b0409061805060109200319021305090907030804230d0303050a0b03010605061b150705041502030f0403150216110a1a090904 68
    0x280178000e00581e403400e0040007400d402c120b030780e61180d00d400080a4200d420303402e01c0c40e40d00606c10305001d5580c04040b903418003400c0800d11514984861042e90004034801d03202901854400c2e00344032062020310b02602c01d507403040c80756440e080841d22507003060002c29040040b0001c0030600c171248800e80201550700c2210255100d1004084501c0b400015100e4140030b01c1840001617030001011a110094030b42c0f0030b10712810182000c407213007107007440355290f030507a10f0110104d406550317122a441d207052442542c0c0451035140241c03440c401d48803a050294000d03814170a05100e5940d40d0f40640320390340100000d2800624505d682c1c646096000002100f003030048809110700c1c0c551000080080c0d5126841c2c40d54102c03100c800032642c030700c0307288101080c0d598244401e00000d03d4541d640b41460b80e0864001d0304180c00840304036440c0110080c12a001d02d8000091815400c01c1c0100700014818001c2c480c880d41d0358a10716040030312406d401180701e0a5182e0004003046001070301d012030440e103460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 970978309 1250 970977059 970977061
    0x14090415050a0b030c070620030f01091b081609270e150c030c07240c17040f020307030b0a0e100c1b0507081006090e0a0309150e0603 59
    0x540d90380c0c000481d004542c02200d024801140e4101c00b881100e008201e607a0409180c0341503920b40740020704088007060903d02d5140440c40c1100c1309500614042d8268080440d40c9502d0b0807140d10844500400829031000002da0800059070045915a4424191240c0300c00e010000202203840ca070b5160800c503504541711500c0048a209101071b040c16007850f0b041080070307400c205c0300c1c61b40d40d91012410781ea0038900b280c002a410300040002c1c1d070304a90008000c1d0308105442d913900f038050119113003890406071900004100002d4502070b02ca1404454100852618220360407152040c0005001034412040002c2404c01c64504101308401550080503040d00d5083c002c2d25840500041d900940c92031080301109800f251440c031541481d810345ea01c401c030013140502c0450a10851514043d00d0500500740c00144400c0140010b007140311043c0303000512107042c520803108840300c400034800760768090a00f640c0000d0700039007040196030011030400b9454000090132503000728440f401d00c0e00020080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 970979559 1250 970978309 970978331
    0x1413080a1422030218130311100e06091c050a081306060612060e0c03010e070909060b211515070c06030902031912050a14040b0309070b070302030a140904 68
    0x40d000000f034078421540b08040380080d1000600d940801c1d140c0302c401145603a0104002400b94140c02030b0a6040b80c00d0720300e08154600120200c46280010358405d404c82c400304004500d040c4102881490308144044048413065001005805001d01d03d074144034040c6c0105480349845000700c0c2145070b1250301400000e407110340c000c201414000d064102c45041c60000714180b50f44d0785505200720b00c050a810b09681c68a0306041c134014000d02440f081c401e40000201d07001a050160f00e0103480701e02c01d00ca42d140c031340031449c0c605410b44a80c2c4000d58480e86050000e292800c414500e4100c0088800a40c902d61848610381a44038290006041084402c8001401509034010406141c02102a070f2001580300090300303e84444814028040d81c00300311200036850252018141141c0c2030300e4a4205003189183c1c22580703500907000402003074000b1042000c43c140400004000d03003515221281410b00955010b56240982c22a08051042c1d2650320506101000196034240d00020300910041e5548 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 970980809 1250 970979559 970979617
    0x1e080a2102030a1d01020403020303070201120b03070f050111070311101214100b0703171b041212170705030c090d0c0e060103090803060f0301090b0403031413080a14 73
    0x4d140690461002010801c15264040c4296801c680d00640503600c0c06041d80e00443d034a140264143c00000da40b03089100c001d840421541c0050100c403034401044500b0100050f2400d003c1c80c010210b2540303c0203050000480c00c941c8146064001e076480d40304c4824010303058500c599040315054800c0e01e84000c00c04424640d0b0301e564000c41900e085030740c0241d21288584401e11801d0005800706030790400d81c1405482e400455079001c03040e4502c40381c021401001e8001d040e401070303004011050b000d402032028865030404e440c0b2f005a490419040d44003081c6c40a0380d10040040444050060100018001241d04801c890104100521180c0354107151716000c80405c041d4020204800030f0340c40015101d501034416040210380200500f82555103030b0041003281160042140c0d059500c40c080d200014981461285c0103621985011038490113000c1e8100c0b25500c024480c5c4203204915851401090580c0102c841090032480d000d00e14181c4481044003d01c10b440c1e82e0000c40f49400070f031003802c00c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 970982059 1250 970980809 970980821
    0x1415030a24050901050d0305031305120c0a060b180103060c050d060b0316022e060302060703050c0c04020304021804030905091314010b1f02010b0d0f1e080a2102030a 73
    0x4111844800f84c1d8840082c00003c54180c0e100030007258040011800f4407030b0080007200628071400454041c030344140e00031081500302c01c85000702c503441000c0d44ad082000901a44000b0031060702d002c0c0d81d25010002c140381f04c2006110140001b80e5902c03070114018401c204980c040300402e13005012043c0d64a40440040d072040301e4140c0320400002d0703880302c0d9a01c00b00d203100e08400c400c0a1644055010b62507640381a1203005441d4140e6038039040000113803a01c0e0007401500f4082d0b01c1e03464859807880039640c10254100b0b021440307030b4410010000140e4605000e500c1001c09441c6100466a8524003562030114542041741d1113140d00d020400713202e919070008400f41d40705602016005400050007400e03910790180c2c05521070700760482850203400080c900f040d400180c0c400030490110300c402045021030a15000e8510f45c100700740c0700d400e01490ba45030410003000d14901c42a80c41e10754036a41458069a04440304010544820100344400e00c046040201f0241e0001c560b41d00704140c00d0b03c01070070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 970983309 1250 970982059 970982069
    0x8010501030f0605240426070608010e0117010905060118060608010503100e0312070333140a05120a0302190803010e061512040c1415030a24 62
    0x820301461000e0b036102409070710101e0344050403401112404540c21910090300e0181c00e50101c10a1000158031009038581102d8242c1900c124442214800003031400d048940c0c2000e0180298103004005012a0440360760444441c180c4100102e048404464054808140c02800d80e1040900104042c00c60040307100c04201c0c02035042140c51740d41c0d0401c0d240360400344102a40750308881490f0a034241c450b00a42680e01d04e440c10341e45020090000e102c08a0402d40c0c002c00081c0c3c0e5528801080714140c0a4025520200700070f50603141d5404403022603000d01401961968195000c140b03505454840405010f094000c09001031110302e8026641d42d0f80d0030840660062040310703d24980900d82c00041040c8582169486186a0034015a1010400042d1019400201c10100005014100b101900000d4100c5024001505180c18880c0044d8100e070014107030242c0040bd041016654100c140b20b0641665480940340e0340d407001c91000820166017040341c140e45509442014101c40104042558 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 970984559 1250 970983309 970983311
    0x1b06041a0105120304050d03110a0f030f08060f040b030309040c0c1a0717040f0f150506031f320f010b070803061e0307060210050c090a06120f0204060801050103 71
    0x180e0b8403001c100c03051480d580d01003202d0308200410b1150b41015080394824502900304200c41d41c4800c40e04910f001104031082c2c54200c0f607041d41104242d449a03c00c11200007030303c0c0048076401c0820000314109201c01c0c14911980c1d652500c09525142031040e074800e0000140100700103018698043c00c5181d45002c2144c4a8180d082ca00300010220080e0030701501003640c07191661800c038092a0320600001e001075410017008018032000990841079540c28622420441500719142c4205100f03641000d001c45229802c0f403126035a811001280c03523100d9124145011500c202518a0301c01444424213100440078480c03202c0506102405d40c000b40240c4013176002c3d039042e07030b81c03000c0510359801040c0008040300020000315181c0d2030401d402152003045054602c1404070b11034002494040799610440143c1c21118561000550ba4460a80e21202d000c02c19468002842d000400050300d03401000103000c0c030400415141c485962081011801200c400c40d5101d899000250200c0c03424483c0d13900007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 970985809 1250 970984559 970984561
    0xc390f0d090503060727030f1a09010504031202071511120a050f360f1506130c050c0a15061403060601140c06042a06141b06041a 57
    0x94140007600034402c044644d150103011ba246941583c0c0c8040340d0341e000c4040d0380000c002201103002c400c400e890391845401c0071070560801c000c540800d6080140884c4003030b4036010401022a4004c2c1011810616002c4010f03564100d620f8000c0d1140000344071800024a45119541d12055800060000815158101000e95100b4007100c040c1c8400300c51850f51840d000d000300b10340c0301c0e41710700150324046a201400e9200b01010710740301c1c8411a14240901c1d60744a0f50000812240c140f19004081c00750510402d0340d46400303400306201105450641c1045695406a020068030544c10356040000000c01d503440c0c0405401e00d1940d1810b04e11600640e180380c1480041c04221061140d0407002c0c001d00586240e50f034900c01500c1040790002c0d5842850010003207010b42010034009140b08038891603580e812078540786101d0348086d025221050703d040c0c410506201c0550410141e00c00743e444140416522803070710030260304e440007550000785240b003200e081c0420441074500c40540c40032460320713900362 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 970987059 1250 970985809 970985819
    0x1f08030901180b0f16080a09051002121804150806010311091504051b070812070804031b03051308031e040617040c0b210c390f0d09 58
    0x216102c14401d00e421107a042000f41d903901c19140c00707410102420b0305952800c400503100c00c0655407245800c0303000940038190610880c5490b4100d6200500c0754801040c0342040d81c0d50040240c411081c503690030a603030110113001a0703900c0d00160804442100c1800440303540360700d1607036902e00c20300003181c48240001c10910182083c10500d40302d80182c4548031885000042404010440940441d4030341c0f031008a00052210900010030240e481003070fa56548041d00080e844c160440a083c40c8200078945c0e0501c07001c03c0d4481c100b080c0301c0242060b03a500c00b1000c9d1409480350321914004000c0c3c070b1480705000440071408000740000404100d008620404001204904d6100394001d00c00480c0300d003100ca12401044000e03095019201d82d02c000121a154580c40070a600019200d04551111030900307003181c100620099045000424403a042c4508600062000c0305000403601c074600140d0400d2406e5124010182d4000801c082a2000d210712903040c0c5498100030000c03c004101c0d92100003032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 970988309 1250 970987059 970987097
    0x506100c1b050901080703031706090105090c190e010e0d02033f03012d0905151905031504150b061b0706120504030c0206031f08030901 60
    0x100051a40d440e6010308020380d462030071803981c0c07100d8000d050050003404225520f4107503020b806488a0401090800e1075480d0041c520800c03800c40c5004a40c204007400102e0301c49a5606041d1142151800030982e81d4141032140350041003075240d110003294818240c03054211207210314450085e40c40d182c5403240a001d0080c83e41c003044000b90181d000c105e440c4803500350400c0410074a08414912852206801e451010141d07110040000440c400001007004103500303420a2030b20010b40b000300b00d00c1105036032181c00c052118811311075038a1700c0700001500b0b000c86044e0744886401c010300c001900060b10b00000f8648103640102c41c082c0c0300300a565013001d520180417038403c641c85000c9224120601400c9000341c1204807007a50480c1090010406003500403000d941c0d40320946004103102842c142c402403100010039003104e0481e14103070920020940c8404c0203030140d078054459698076220f01c8021440032048600b0181c480c4c045100200c1d601c0b4011001b0110124242e80381070707038000310f424a60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 970989559 1250 970988309 970988329
    0xa0e090601030207111905030a0602130519060c151401080105011a1b1504050c0f01050c0307030f0908070b030a0f2304030909020c06060301240611010e0706120506 72
    0x5d03003504001105400300d0300e04101030032460035000607418540f5a0301c1c00401d18008000008503485134000c904079400707034201d02402c0300600d02150b40300e00102400310004801031880c01458100241a41c5100c140b24004243d0102c2c004003031002c20039610321078011451310f178080c0a10304180d400d2074000900301120b40825041c0400c514807a030324005c18031580032202424442105540d000d0601441c0c81da80607491a0780c401c40c05070000e01040c619490030001314580103142c00f4140309003071000f50720100d00003040e90350440d1705041103c8480e40345403054800069a51161099100d01781c00443c2c60003603003000d1800352a02d68030900040211140030019100304e176004548000184214681c1548091003541d0070902904000e40403689500115003079030310202030100150300c1681807000b141024880c49400400821000d02d0509086001860440c2e8910800c001c0045004048600c1c26081d4044494000a05c1c11131360b405a5030b20020b40501c03201e40c108075045140c200082d940e41000e00840c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 970990809 1250 970989559 970989563
    0x3070e011505250b0a1e0e190b090d02060f04060b0a0b0a0207140607121b0507030c140102010c08011203020106120c05090c04050f10050d0c051309020c0a020f0d080a0e090601030207 80
    0x5240b40600d00c1c60114000c1040200410883c408c101a0894480b442004082c45500611003001145010890780340362442105c6404110b50111040041c0054503103407183d002a03210401003261980f68000680140381a002031200080000e510444a0f400058007403c54000950700e00c5890105d00800049018440c1c014196110141c0c0034850a48640d050010790309001558810400b910b8032454a40074054000325a460b010410a10a00440c0304115000003401d20007404918a48040284428410310034041c03407030f42502500041500030b40241024085440840080844600707203d0541c55082c4075547c06040390300089484225042d01b1030f010703100050b040303040030f400350014400700508601901b0200103081c00362041c0181e2a0080321282e0030a6070b01d941e12600c44982e60526540994805820103104010400341c5110104480004540403a4583d102c0c01c20360010884185014000900040c000142108007d41220360071954940990f202455552040d0054040b4820002c1c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 970992059 1250 970990809 970990841
    0x604050402070f08070f030e061306080c0c1b0a0b07050a08070602090310050901050c04080a1104140a02040303090e070e04110d0603030e090603070e011505250b0a 72
    0x28801410141c00030001284a4282050060102d4440d202c00e80c02620084450101010440c8185580115038011606080301c0652a01c442110503c1c1c4400310b901c40c1c0800e02091400250302d034a015070603035200303140c5003060322104060030b200c40c0c00c4008221003080c440e5800c0380b0003003503a42c52901039941c40c65000d0300800d50210b03ea1104e948581102d40125840c075003c00c03500b00141c8090140c9034807212100c030003040c075003003030360246082d1800204020156082400300700054140003850b40b0110f904041d05080d41044500031030060440b5414501e4002c0c811020310040785c0c440d0b4001d10489009a1300c4c898000d8494070340070040e050550342100040c0d100c450b41e002500d0300c0c0d40107112030a1480354080c031b44100d400003a01903d216500c00c1e40800d0141c3d0105140f42400b424482d403001301200548081400e01c0704000341c00006010340b040114200701844041130050088035403000d01c1140007464400c0d0071009500c0112042400c031a520312138404140d84280502a907007039072005a00b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 970993309 1250 970992059 970992067
    0xf0c04050603040b1909060207020f060309120f0f030f0403020c150301051c0507060c0c1a1207030605041107060e0d0e0f13050718120f030309020d050d090f0602030906 74
    0x2200d02010390042e00300540005ca1a20715400051503206050381c10303105e198056252070b81c0e80104280700d10750b1a58540180c50070020008003080100d03602d00c0f8000e090000301c1d198142040040480d018600c0c101142d40b000100344801c0310a045500361041d0721a038200c82614100c1020301603031101c0030f000c110040f081800144440d20700000d40f0a030110394220300f400201100e8a0312450030403250b12220101c0c1c00c5880382c0050041d1200300ca00504415015010446015400f1144a20a005081169406000c0400c0846110342c02c03035070003000000c105002c0c201c0c2c1044030304000e500940003100e4482c648400381d10b00d84c9011455000a880d10344401381d80310103040c1480380407100003d2880d401079044405032190b030082c1c400d5a0060445a644001e443e55038248129408100e030004014101000186000202d604800c802200d40c14500418088a11300c00700b00c00e890a54002482401400d00d0302d1015944516480c040f61108640840d4465680a050341c9030f100e01d4002e030f0b0700500200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 970994559 1250 970993309 970993313
    0x61e01050306120313090510060203040821070b0a02031503010b010215060a17030309120c03071704030618030e040b01080c03221103010c1b0f0206040503010c03050f0c0405060304 79
    0x2082c020300d120040f1041d64903100c4025032220f8244655000240704a940b1024031481900128004001c1e03c16400214640350a040c2c201c0d0352140d00c0380004182a207440484840440d031501940c491a07805090000142000a00030019410455202568243d140148181480c0500030407c41c000103802400001da0208481c03c41144001d01e0150051111740c800550203e42e01d10040d81d500042000e592203080100c00c00341003a03502d203200ea004284c14850340201e0080071045508895201c070341307040340840e6140318540b10301440d03001030001d40c81c000000301d070f8003a41c42540070014800d90b1006480c13041241040103c41250002c0f81c0011820310000e000c0c03281410045400071700e000b54800010740c1138040d20f00003840042e0221454a040da066651909090080f19000e080d2814402d48109007a454810300e000f0001d070180c442d0b202c980103070056441d4081120b001d032401030002d000383c3c007002c103016021700000d07202e40405100f410000307409041c040003550181c400050102e881d41d1265 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 970995809 1250 970994559 970994569
    0x709120b09010b03030d05040c05030f060a09030e0a091d2a06040806160801080c130f090b1f0f120f0623040501150302010f030c0210090b061e01050306 67
    0x7401c200096580d1100b030344031035404101400a0044480340480c042c034041c40e09440300ca4890340001d0280d4441150b40d0200c080106880354490801030000032601c036182022115004c0e00005980c02c1820a100072440c005960480400d1401c2c03100c9002d0041018590a69038056500a01d52003003081c1d0342d0011103c818582c040d60003140104004d040646070200241004070a481c0c00401c80400039081d501aa0070042003070050140350003904480201001048200080500c1d54903502c1d81c0c2d4010441400da103501400da241e8001c9000e2405141c60342880c10421500c0c44a60034044015000103885448550750a00f52081c0303d031001c860500715030b20780c0850301d4140d00440c2da0586802203000840e40d000c2a00c0c25241c845034002c1c0c80340c2845c1c1041801c441807001003001040d07441c003040c00541d8100610304495103452a00003400c250081c0200d040083c907402c8030641d43e00b004428000d2100146c050707401040210b074483c8003481e01041550714100f00b800c019002c2041440013516912748 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 970997059 1250 970995809 970995811
    0x3030c090111070e06011b120819060e0a0e0105010b070b0c041d4302030c011a011416110d080d060e1803040b1813020d050709120b 58
    0x8181020030000d12140b804a09001d640c4c1c100a4600c14010100149507a020485e02c400340061a10b11107080350380d840d1028008808400c4400f403000580104a01c501c07039840407011403440308020004c0944505900e01070706004e03078103001d1650501d2641e03002100103102d410f0481e001180c907549011007940d98110031050017050120021802c3c000012200040807a111030031500003040b40320303403504841840d10820710384070380244140300c10342c0203001d44015600b001060307084a4000e410640144003ca14510442240100329402d107405c03500030084100700e0071740240c002d817284420720803c6035007414903001e541c940110381d456003040b400c085400d01d00031020f00784001e404541110a2911405110750100c0412402265100f030200150720404e05001d4109234503007101c5c481494550181603503400396010ba9071301e8030340004114183d0140351070710200b03d0001400d103504103a0340261003002500000b181c041010b0801001032400c034481e1108c001a61403070004901402c445454940c1d02501c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 970998309 1250 970997059 970997077
    0x30c052401052b03020105061806100e0f030a05060a061a07110a030f1103010507020601140f041b0906031a0d030f02100f0614040504050d110c130509160803030c 71
    0x1e00d050403d01e0501000001503c81c90080d0004070b181c1c00c2c0141408002501700d41f4880c051447e560500c00340e0b6880c000d0004116034181303803c40d11420030000281441065a42469051207041402c104200700810854410f90038000200000da41d290030210640300400005403520104000420020f9281c080b155050070000c0c00200e40300d0740380d64424030003601c40142a40e4101d8003603000c810902c2c09009140d4003041602c003800807549000740401e003110a003d04607115100b2001d0705d0405071540c3d40035038141c2450403400031101e440c000b030243c600ca0343c80c062400000d003442004803104103000c000080c81c0901a282440e056138684048465231211b0300c00e8011402a0340c222130b02810700340100780c00f1000c10f110001d160380c07420042d440c120108080c240d0107541004100300c041080070031004800401c03030420340320964880402504280000701c0250340062441d0149a058007103074840c0e40f0070406030003166201c0c003006990001444180c825822260700801c000b5510380d80c06006824448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 970999559 1250 970998309 970998349
    0x5030403050601090504050c150307120b040f050f0a0b0d0b070315080102040617131118091614150a0302071e1b1508040206090d030c05240105 63
    0xe0300c03580e6a03410682c1c2030b800040b149480e40b00f40414050305100c84500d00c0002c4980a08412038185e10b03542c9070000400c100d0074440c1035016217900c1c0d040c0390410801c803c0300030410800e480406050034001c0c40c040c3c50044a802e42e01c0000781c0181c0541c031641c80303211801084513003585400e03982d403031407074000900f54000c1689603800007c88042c0c14181e4005024800c001603196070070464010842c0220507040001c00c1c140000b4010b900c0d039404200300d13986401100d050f01000d030040215940f1000d5111582e1440d4295041221034000844c65461340c0350060700381018940d0700e0482d840c4078101201e0581e400021715601c00d40d9880000010030300c9c02407609025083c0021b545801941100011000c04040080b0808404205401c0c0500f0002d0800082c000078050a000b035903403600340847c080c0828000030201007801d646e128000e88483c81c00041c600c10b0302108034580100000f00340c5204a0702803003180301c49080d103025104054980036007419034120326860001001059100020104624 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 971000809 1250 970999559 970999567
    0x7080307030e06090a05160b160609020a0905011e0e240d05060f01080a0c0e0a140c0717090f151209071806030b0a0902041409100f020a020a030c0503 66
    0x30b9028402648656000340c0031301841401ca080142c00d00285020107090001501820300000c82148140d036420b020204101c848002c3e41e2429000901026002270f510210318100055030b101182c0202d0306852046540300300702000c02c0c1d0402004005c0340518042d00c1d01500000b480c0030761018210b89096146001d0b8900d510204021580d000900c000596880d000403040044210030103101c0c43c01459928010990301503d501c5a14036480b0f10702500490a13120300106a085200b50442e51341c140d0f0f00030300866503080c0300c0741c400b50784d81c400c84007110080c840328841344400c8106c0050302c1d05048090451100c00081004010b600402c84001d2201150706000351640001c203101c0040c41802d4840042041c58241008020b00c0c80c1daa00c0342c084000e081150610001e030100740100d40041000700c010644003124030009024041c00c0a2009000d8401c5d01008025040054205003104401608000342490342034020f00340e12404400d000548e120f100c01d90006032003a10b50421290284040da820 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 971002059 1250 971000809 971000831
    0x52205190f0c0e0a050901050108071107060c030210090206090f03010e011a09010803160611091801090b0a0f0e0910060f05090a1506050a02030408010203010312110604080708030703 80
    0x4803004070341e02040690359005680200d075007040036202c1c0044202c2c1e00759442d0f494100000c500f18070501943c0d0400071710700d01151540380900340f50340f0710701001c1041d46c9030f07a034417098014050b1804c12000d40051141d0381c80030420100d1407040046c03441e00600b004e0700c3c041100c418820080501520560590360310b80c09011012428071800014601416100c1000c4203d40100005001d040e04407400d160010804003c9140368840704613003480d44000046031a1018207141d180c14029103088580003009182c1d10744070011000e00040c180c4e2600002000342444810a0000102c414040c009a01c1280103081c0502c00c01c00619542c030400c01c104980001c1c4420481600b5261603501028211110710024403040c6001e031103050740002401d5040000c4030748514004001c409911920040c800009048550b081c400e00490b4090205840299a1703940d40e0310701414500404880302002803408103030500c40600104400b8001d90704901042d05100039500c41d401680d05c05401082403542c0ca040c0d00710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 971003309 1250 971002059 971002061
    0x50a0c05100b0901080d02061609050612010602071521060b0c011506030e03070b0903090409050705030c0103020901050a03020a09180507200706050708040b040b030103030905220519 80
    0x140c110340c200d004614040c2c6441840050742040e00015a580c01c1800768442031076001030b14a500405868240320008854801550f140e030745030304880e80010380090300113101900c0582d02812912a0307401c444145a407160180a4600c200305028000340c41c40c50840f00780c0c1a18030030b03500075804500c00064a242d44480064090780150000c0c00c80f87d44036140c80140404882c42c48004048604040c044401005d20403501d031301c9900f100600394210a0042440782c0c10030420b80d12080d0340074004102c030200a04010380d07140454407641d4403074810640f0b10026544207000340d400140042c2c65481c140f00d901c12042c1c0194004400d100c04200e5150b1000410f0485020413140b804010503001903242040d40000749a00f8074503001c0074645850000e44201440d00080c24012581d4a28215446218910304849940310700c0d40a90800b03200032802042c2c42c101900114100c920946590002e43da6460034000d4030105c18000417280c0100da810441d0030000d40c4c01455001c0e002142c02150508200c88800c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 971004559 1250 971003309 971003323
    0x6082d010e0a050705010903021807091809061107020d15110a03020301210c05060d090203010207050c100903081e07050d02010c030e07030209060d03022a0108070509090601050a0c05 80
    0x3450381d5105592000c240f21003441043c01909003841c00718641403c64002c40d00c1501e42003406218044410001b400c00da04c2051307204050030080923010960340d003010045000e021031350010307101035240c25a12849440400100c801c41a0701611501c3d41021607240c3d0035051061441410000d92244284c03000d000b605002848407130321a440068503075060030395401600303914014402042516201c2c0ca400305002e0341c941e00840d2812a4180e03075500c500c2081e00090480f4840c003d40640c00400e155080040101e5010b08200090b18400c140840c610b40444403403160b4070010304141c200700001018148080780884442c038100721001e20f0070306c06030f84142c6090421010b160060350340d0702c842d4405580c1805030440343d45071040108416402c5070005010b68101606092203281420300141c105402030081c400c620007510004450032400505e00242888000c0d074140c0003c46800010700414080c00a50320741080140841407195074000042d205c40d400502c0c0340701031012202e902000544204081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 971005809 1250 971004559 971004581
    0x120207081f06061803022404031406060d030903030305070c1b08010e031e090114040602070e060603150f0a080d0c05120f0a0309171602010f0306082d01 67
    0x100c1e1400300c0c080710101201c0c52600b014081180d0100300c0c1c020b40c0035580b02c030340540740c0407607081e0001c0060012144115000280c01c81001c040454000140402c407601004441c5c0d011041e6000c0b580e641f81049009080700c000100402d0404009202180c8240d1003958490507506104106454540f13030300b51206600e042c0445101304484c4280f280c60000e024420440c44020002c500300a84201e040420101016900540004c00700e00d4410a0b072144541007040f05010040300c2d5903076100c0900a403160b00354013031003a000d204080070440d2418054122845150554100c03807185100d4420040c01c940f100707002a038401d0404801140140041c000740c0849180d079160708000b03580720b24082d42001d256140303003680c2850030300200060b110b003d01140c0202d0300a1070001420402450003400d001040c4824012a5002107010341504815114041105001762284401610364810031410b41d4030328082d00d4070503000b24054100d1078640c0010403a4101c80c8042c00d10210940d040c0c210300f103c100c3c14030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 971007059 1250 971005809 971005843
    0x20402120403020f032b0917070c0f0b040303110c0a060c1112060112060e0102031311030a020a141309030c021203030c03040828180b0705060412020708 67
    0x2071004142d0100681d8442d030450802440c100102d00f4a400c0700800c0205034141035002c4d104c1c0084200c00b040d0702100030305034800003c40102d200c908a001a6801c000402c40300c1030b0201e440800d4120303007840741408480c501c01c0000e00d09821568221000503c101c0c00507170b1885003a5501096954100441c009800e450790359000c3e010709801c10076408260015401c0c05282141803040400c072000c04d401d03054503581000c0212944051034100f000707010040c031580c0706500c044203000700c10800302c14910225000e400702c1e2480e0081c4a08154442c9464140254065401c0504000141c820300303220340e403008014900e590220003026107105444e02c2c0b2200710300007160b40000b0403c41c41c18030740c40901d1480050041d42185403440d0103042d0f520000d0005000e8400101366a02c4c07a995054074030a800303d0410840285d482c1041000e420540c80c9000d03c9110441d080c004203030740c1d81540588004640020041426403682c1d101e40050420340701520b411800750b018041005101001107022070300380204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 971008309 1250 971007059 971007061
    0x20a050607021c0506091015032a1511010c0804060b040b04051e132d060c030510090b06161b030813050a031505071101111c110313080702040212 64
    0x2006c41d040c038003003025040e4914038180640f20350b4140c849401341a0790b4001100748051942454040b00140d81441505101c0e800b590f012980980c507141d294801c7c6010f0300c03984a9605c48100307ca082c1c336004e80004c00050300180015001c0340386900621021300c009840081d5800281c00428244c9004840c00032074481c2e40305c609085802001c1c410707030f8030100582c54000000d10554070300c000700c1e007145803d542003074989240701c41101c80100111f455591205041080850b04500a1301401c0f040b10a82d41801d0310840000d980643c6010300449410000c2c6942d00d00030024464000c1080d205005407400c41c0d107040c20914800551000c100a94094080d03a80c562040e001484010742c1c50303030041c03402640036003800c05c0010b460131203004102c0c48200020480c2d943c0c6550032036200b203104010b1081507080c940b41820b500c00d030300c0003040101f034804150480c0f000c0301320511050f10302100400c280c402d810000101c1c250000408554603920842c507041c601002030300020281d80205042940300c01000d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 971009559 1250 971008309 971008321
    0xc07030507080c060306030a0305250f151506030908090409050703061b1b02030c1f030e010516050a09050d0b2706060f030703050601090504030f0c020a050607021c0506 74
    0xf10b076140c0f4500480b456442e625010740441d40b60100c43c0c000038180800490030301c020803240366006040345030321002e161484580c1e0030700300c0c022411802e00b0344003240040454981d15180780900e0f074804200d45882641d4504d014021802420400c00c1a26407800a00a100c810b030b655020343d800030742c0102c0040003440d04504242c0c04541d01a114511603400740705d01d2189003500026507403c240030300128000e240382540040380c18035101c000e400758400503005840602c003603152075102608000796000c0090207814818182298000e036085801c03220140b800303d02d650b10600040000c0f045610b00950503e54590114212079a503840444017151008100940703c105415a201c00c000d00001590340c0f5400750000c1c40c2c0b01c0c08080c0c00c0300d0090503410f06201c15a00d0801c1000011540318041744c1c895a9652079040c01090b0589c0c1c00c80c0020700920744030003040d108156882e5515001040565454034180c10406164440c0500b00d8101e002c0980120304898014081c1c40018041c402600f42e9250803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 971010809 1250 971009559 971009563
    0x8070506061207082a0405010f1d130b0c07051c1106040f02210304081c260709050306100807060315030204020c0a14030d140702210c0703050708 64
    0x41c0c82c101d110366110400c100a01540010035418020b4080d196220b0101ca640d03440103403000d0608078030f8200f810000000740007210b103075145048030000100f20a2901d40c040019a454000b550425002c007002d0720f841c004500945581508605100c89007450070a4a43d925418003030101c40310403c0301c00642d09403c031690003001212100c100d0b20080e100d0382c6001d690f0120700c2402c400d400b07030040355113031085203190034030300d800c865203444000c11130b625255103c0e0980c1e0b90740c810103140c500d091050a0004056401424081880d000e00c1d1100c0c810030125400d80c1d400300c00024000b0f010004400360010345d070b40381845801d004040c05140d01100c2800c0200c0b8510b005000d500443c01c042c60030694550500c40c58080741c064035411500941d484034a49660f0345840030845010b40320032008666010000c41c000010f0a691014500c2403090005440c4481c524510860b44400542c1001c40c050038424860001d40d402032952034807881c244030440202a10300042d54008984135408060144890b50013 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 971012059 1250 971010809 971010829
    0xa03050c010e09040b0712020f04032402090108071416350a18050603010b041404090b0a090516061701080a02010c15090b0406092109051c0807050606 66
    0xf6603220840f41480d50307841181c09002020790081040c0c18143c0f2900c1c40752a01120051108504a1034689860381000b240e40e4413400d042c56060041030441d42e45c07818060081c6c5004420584441c105a07075425002c2d92070203066803004500301c3d02044900ca40d0211080400141c0b4012407024040130804440d1901c00003040d4051014048a214948441c1c3c50200c2194035450319403134502440501012511070203c039540166034003000100010581c035a415000d03104a0f00c40450000b20701c1c5000f401d10040302d00c150030240c044004000041d103040704540106400781c0c482e00850700f40c41c0c06505400c844655a4100307400040c90f01c01d5521036149150300b201e01402201c0041c1c1204040b40e070019121801c043c00041c0401d141d04603c0d040b000320b41c5d129113007950300050b004211b4902846c103007004110b040012034050542050600c0311120f512000666650183c40b10150142020304002030392081d44030303c400903c58030300480d0010b04510b002d072240900c200d004008034140341e4104400324003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 971013309 1250 971012059 971012087
    0x8030c180a050a06050703110d080603100207050d0c050c040c0e040c0e0604050d140601060210060e1e130602130302010915090b0a0c061e051320010c020a03050c01 72
    0x91075607024402d40e500d0a1004040f0355071420425901e80c001c0c40c0c00e4035500180c10b02d030301250044940c1901e0940c1c10500b1a442484100c0c140e84062904120103c103e0042038409010f51b0b01003500c0300003050094036a001610700541c1100c90402d0b500d8000380943d90740003035100c0025101c000442d904e003042e0049520107410380c1004024a480c02010404038020340c49124490700000c0c007070005011100f170f83c405403002040d094401d150f03181d00c4042d40c1d075002d2040e03030151545401e000003510f00c1341261541c020798251041d001c02040d6191510900c00010b45904038030b450301c002c50f5002501c68030041820101480078400120300d980005002e4034010f510010f2141292119203071519401500c580686800b040340035245c0c00340181c1100c21403109100102501d103030800301d50701c0502d60840069442c9401000b40040c0d0b07a0444a541005800c6038000e1448002246260340b1000c0c41502500807030040c5010005c0c42c1650b000200d20140c5588140c500b6046080100041d5a0180e0382000d902c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 971014559 1250 971013309 971013319
    0x30b090a020c1c050421120905100c152405011407080a0311030a050a2702011202070b010b0703030b01020606130e070305120901080a0b030a080a0c08030c18 69
    0x2980351500c070340d140c00c2d0200443c840740f01c0b41c107250851140a14256005006802440301129401e0f00715013118104900f0141ca01c0300d81070700440032642c41141c506c07080d41d8002d0100070420030080c8041c0c0741050140c80172102c200014401c1d6500f0040d80c8030319078140d46501c4d000c014041d40145c454541010a80080d41000f40030360580780031071040e20072a01e8140d0f204031400e954000310300d400c034000c00c0ca14440710001c40000081c00a0b81103203800c00d41c0250543c80007084194001c0004c814195102c95424400d0342c52914103102642c010b090080108500500c0949040c1031a41d601815010036001300b0100c01c000304000341070541c9446031050111080c0020720f89420940c1c0001d81285460180d1000c5544482c5150a00c4a0500c81c0000455020007205c0361600b8403942c0e4152074000903449400a1140000111406407600401640542c00360181c025445d254441c0b869640c041c008420506c01c4111881d0005940e000045108550700c0c02510f880321143c252800e20050b88140040c812 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 971015809 1250 971014559 971014567
    0x204050a1502030403021e0307030609060c0306050a0b0f16060c0909020412021c15050108190215030c13080106152d1418180c040618090c030b090a02 66
    0x35400008030f409482c0c040750702c0321f1001912140c1010f180c1d0020011758260080e94000020000340741c020030501440f4620520282c0e80c001c0701182112030324800d042c5c0c4450030b2007042200030300758401000740d8408014003a00c2c28548111000102e121f003041114002e9940300420105030744400d82c03801500550006600c0e0628001e0004000070f9a824060300c24150f080802202c404200c2031140c10aa0002c0050008003d00c0080e6000b0304003403081d11000d00884a58401c1181041d03c2081d1b440c4c3c0c01000040f41142461a0288903000144841c100020800000e0200c0540503801c03401004400d0010908030708007081044007483c060180d000707010500b43c0c0b62a0100004102030884143e0b03800c3e00d403c51100300c9040342c0b40f901d156803c000c071801c005242d04d00807070240d84000e800c0c00c00b90341020407a0800031280f48040c03000c0380c80318200201480f05000f040c3c4100d40c0048040040a1141800d90702d5018000450380c41e010b1007000300307548400c441c500d42005000140d004018440442c10 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 971017059 1250 971015809 971015849
    0x207120b1f0e01031203140a0f0f0b221e050a0c050a020a02010c031b08030105040b0f211e2a18042307080f0304060c11030a150204050a 60
    0x30b80c1410b000003004505400e40070030f001e6101e40c3c800500c42c490079821201d1030414002030b400410410000e455054140404d81a504605003e114084a4042c01d1a00700790307801c0d54070140d00c14508030280c030040d0302e03400c035811510300e9202440d445402c440070024503420f046101c0d804454181c02c1c8403051100501c4202074181e008601140b2294081c20106c007840414601201c0c0301c2d41c01c10fa688100d5010032448424040001c010714162241540c08000705a80300c0b08100c402806a0b0501e50b00188a42c418816003072800c5071030f0500c0f607031507007140c03000b0103051195501410101005805035204002d80d00d80721240004100a09130301c4086006842c03040c901064202a81c0b201c081d065036444800324041050081030b048554050140400f03140d20103003915078482c9220300c0740341083c0c40b42c00000c125680300032086404940081e01d0b0b200d40300b2420b560360030209a18691041c2d25000d10b12562020810402407604510f05078500180e07190f0401003080502c0d191900031400143c1500c1c0b40c42e003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 971018309 1250 971017059 971017079
    0xc1239050109080c0d08160f120c11011116080a0905030102071202011508100e0f03040314281e06060311130e3a0801031505060315070207120b1f 64
    0x8030403022301d0281481124044207442201005a0b02c103141032410704c18107085a40040d200003c00d106000900c04000d4002c0254410b00503e40804c201c080c1204c00382002036041c0000f0080201c2030f041100001c1c0d9268006400c982044d04240c40901c8020f00f100b02c126820700c24060000142c1d4075001806040c90346982d40c0790008070801640d0384e940c00107001ca006007040042e20316841c10003140d58031901c07890071181c40e482020b600011845111004000c0c510004084100b02900404100c3d503001e058036104120601920300e19600c658407091840403500d14040e400266014140004c1408000300034458081309000b48074984c1c52034035081081015011408004154110180000c0481ca6010150a000d010b0544100310b020040c04580a550000340d8241200e016074481d10483e01d00007008001d480080343d403035a1507006810201d01c9800075074403443d0007629030720442c2e43d0320791a60301490b2140c04405056800c280c5880420040944203140c1c0c9a6040010703001e10030051030006414 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 971019559 1250 971018309 971018341
    0x315040f1806181e03110303150103090c21020310092a050603040525080c0108070521150d0c1403010212070c1239050109080c0d08 58
    0x4084645803440e0b030000200300002c050f000342c0c00103180c90055482c01c07940c900004144e40d04034082035000d4100c0c00b58100100990b4461b00442c0149460340c2c0d03400004500422240c103084400d06d0054402040015940c00600124210410703020070089040c010545081010141401c146061101e00c40000b000d5001503001855600199030700b400c6940402e100e9490250411500100f0100810050183c0041c03044500c50284194107031542c914000811002e2540c00340e4485030344030007950889075102d007003c82c0d4040f4641c81c00c0350500100b60501d101d0b802d4000c502c20407041e40c06090150681080304540100101120034249070401542c807103c2c840d130b540c42100085c81b4030400d4411140c43c01c4d011100f0144500c0d01001440c904210040e04041c01004240c48210940000f514040e00075106245a1700c0c5426480d10035030302010382d0300c10160500d4004841081c181d03c0b400b00080c024000d02c4519403240c102c0b55140d00001d4060380c0340000d4880b018007040410310a000042100c01001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 971020809 1250 971019559 971019563
    0x316020f0c0d0f11090403260f010e090a020a0915090204051804140a0b1911040512010b040906020a0809010216110414040302030a0207140a150210020315040f18 71
    0x701c3c031481c12410b00c3c99150000c5140c1c50b4104000d08200001c055000d0003500749038003151410000540c481e00340e899408421240c8005030f000d014010b00000741c001d4007060380304e803a03101100d00c582d035103501084008125504c90340300c3d0f03030b21407d030742102d0720200405c41302030080311030300314203191604001420008140740c0d00e03880c008010001c54180b10450745103d03c0e29840718101c5440c0455460900f0000c0d4040302e07a015903581c120700003015490355000d018044030042201c1402c090410040248540c00e004600740c10390750314031510440c4e403118003580000c58000c05005841d0400808003030f151320340090208009900c1003228402e40700d4445c206182094001c61116011021100804c0c0103040c2c0225080704158444100410564000b00800c0c04035116800d030340340580d0310044458140c1c0100c020aa100001150510208141041441c1c01c010544111107169078440f03810b0040384c3c400e40f82c92014801084c1c607040e00e814035015001004401920402140355040404482c58082c00e04c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 971022059 1250 971020809 971020823
    0x109142118060a0c06020f03100b1338090f010203070803010b090a031b05010e030a03090e041b0e100e070503070311040503030f030a05060312041701110316020f0c0d 73
    0xf03458600ca11070030540030280e0340311804550b10b4103560000031040d0401c868010700010086004244240c295081d45c024070304451804120504010200144400d9001c0358200c0e41044140200b00001032a0011036081045094130b60300d4030702d5400c0c815060140c0c0500e80c1903510800500d80003422030000c0301d0445078801900358640103540000b80c61150f06070300c0500750a03c0c5454030440005040e44942c1200d1090325280b00c041804001c0c10b49035502d0b000c2c0a00400e42c00705003004010090707442a50300034812161103107085001148152102540d4000d004c5291003401000a0140264614805032401d506800d441d8980b8000081c868400245000c04241d01c4032410040d0f00600c009550190100401342c82d103844040d903002d500741c0c02c2103803008409420007002c10650704010640302a082d0f400d400251410342011a80607514040040b28145907581e407014207407a1032094051402107080d48900b80e03000c40c1e044d8000313281c2070301c2e02d41ea2206030300040c1c40000d1994444640d00c040c184d00009d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 971023309 1250 971022059 971022067
    0x10e01030c0e060d060204060305061e0607021210090b0f0702120406050c0f101e0c0f27030b010501120c1d03070305160e090a030e010302030405010914211806 70
    0x4940d139002c68080c000d00e91742c000b00700810201d2701608014402c440c2520000382140194500c138610422800351a50856020001c0310b0240c03c100540c20910032000d0100c401d00d112142200c5c040302c8003000151040d210b0740040c00100c800b00c080298001403680b004004180b508148040e040c8580c0c8214000e212001690855500b418444880c920300914241c840d000b400d160001d0103440320780340b0302a21609801c1001d0814042d48201c0304a189566140300d109030690701c00f9150015010408616001c280d03010004654541480c500554460700c4140129458000090300a509500700c0030140303801d24210407852503004a0080c0c4082c1c1400c038040203203181c070011a0038500e2a41015115016540741c01500208041203c002c13034543c00e410280a40d140c070301c2607407541403800c001800035140750032aa000d58803d40245802a018400000d08608a81e41e40480307011b00c01c1d4a840e4642010800c1c0c42510708050102000d1907040803a10b180580c81280340140d003502e000c130a07220f040f000c1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 971024559 1250 971023309 971023321
    0xc091b1b050f030a0905010c0c05100c0b04051b040911060306012007030201090e0c0d0f020f0a0c030f0e03070905070e0d03120c300b10090e010e01030c0e 68
    0x40680400950020162110404440d80b40740d1240d004508000101d072904400103400e5115449111134240c01c01703c013419440c1440200800414900d098004100414401d40f02084c1c2d00100386001d203200303400410140500100405041c00000c01440c8030b1407809100303e010078850b005004040c081142c2140d600d55074500161a41401c1c100081075034450210141d551450020708036069078002d0300c550704404c0e0350f0100300c0f40c0148201c0e410420300100748000711050302c05400c925a00059000098101340800c0344c1e40206030032050b001030026042010282c149604000026402080752910003400c814403404242e44d840c0900c10003940507030700c50010b110750f0b00c070b4112180c5d0004024620b003161000d85c10000d04403500c9106d4000d102d89454001e44406004142d8001c801e40e0300e05540c1445103000e00503150484500032500702486d100c82042099a454012040041c610b980721404d0b4a403c1c001c1d0102d905805030440100c00080500510200d103034000500d08854084401c03003042d50350704c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 971025809 1250 971024559 971024597
    0x170a020103200a0806090a02071502030402210c1906020a03210903050c0d050310030f02011110060f0801092a0f061d090403050904021e0310030c091b 66
    0x500603000e50742d00c020901d071103c41c0d80444040d00522085031100302e01e880c1d003c0824124403d640004002c9010f100d14050a8460358029640c405d00003851140c003410395071780b103039070030b14070b20f045030100d60400620304115217440c4c0c2000b0b002800d000101c42c07400d030034500042e6991801c81d00160512a46500f01d003925140c003040040a620101014408040149005810b50b0446400b05c45540510020071a500f4401c5050f00c0c0700f0340b4403840314280ca41c43c5485207103202c4440d41d002c2c1c1c108400026608104601000232416a000880001500138034016401000200c1504030107103a0f41080d0075040030801c0341c00061002244400c01c4c10000c1c22000d225004059254480208482e10350b00c009001900248a0040000d080c95000c09000b405400c100000c041210000c0c045613060201e1219404d01d40d026004001d401d840e2924142c1510040f4110368100301c1e04d00440d40c4042e032041c010030860070000f07002030a450006001c0141c0500d176451142101958410400c0343c03c00510510b1081 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 971027059 1250 971025809 971025851
    0x11b02030901030213180221040308070e04020c060907050f03010b0a0b13031a0f0604050915070e0d050a1716020f0a050603040b0603010c050a020307081612020105010e01170a020103 80
    0x442c100e00c10030007070806c0c0900194002c0541c10f94450b0020b60f01d0318a01c003000405910881e0b00d42e840070b521f961501c0e400d98011071002005500705a09114180a2309c00806c01140143d1000f00189040c42c54402000b40100c014450349000382d05049000e1003548134110080c003940c8400b4401c0340c0360381c2c42d813150030b41d002015400502a001d01c60407900c0079001c1030308418000c3c00511003840c55607803104d0612061340c80968007a07030140e1240480c0d0352148842080f040d000021482c040740c2d44170728040080c2229070400d03c00d50f003e42003254250100001d00090210502d1515410b82c2814000b591640c4100e11048000e40150110700428081307540b600701d4034015107401000786031242002d04055500007800c40e4054020b40c44d001010b88143d000c1c2c41500e40210f010742c011854022140d0b166100380d00484c8101d8045a00700c0549030000e400081c0c0319021851560000981c0c1d0301d4038541060089060b400003590b012800340780c3d010790402240710342c203898080c2804a8101c0d5401001d100700e80c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 971028309 1250 971027059 971027069
    0xf03030c0c0123101505071212060f0f15050315040b1507050105010501020f0a02010e0d02030d020a030305010f15050703090f0906090b1917030403061409011b02030901030213 77
    0x5442101c001030703d04040001d40c0600c590090039409162280e10041c00d41600d5032941010540030701008002a44204d10600c5080e0107242a24030340381920704101c2500c10907000301c040382030804070a1086162040f0600000c0c88210002d80c0007940c33180740070b4040d1101404011a0500c400300000c1261070b6078005005800b0058060501090310310507901642e000080111015400c1c00700028096200050311004890000d01400c850b100396401034910300768007002143c024a02d1001c03070300076030760500c4100a40342468004c2d0030350281c2c519004040301c0c81600040c9490141400500540e000c0c20f404140f050102e080a6956200320300341542d40c488254404e02e203004866001142522254100800f151045030b0144001c9001100b00703c0d81c80103141131a80ea44188190400224000117085250031000100356032a0a460f51102c0003a10051401801040024000d105071407c003481129007000c10503640d00720000880900039101d11400100c81d04054002ca01710144640f01c01d40b805c0101 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 971029559 1250 971028309 971028341
    0xa08040b0726011805010f09090c1d0f07140316050903061006020f0105060d0221011b0f1106010e10050607140d140d0c17091606020f03030c0c01 64
    0xd88401c112541c104824000d20b10680007134640301d504040710f4020300c1d0588190320110750045080a50150041030403410a6541044000002440100351041c2c000b8413500b03003205e002e0034a014240c400d00280050469003c0101651400c207c261040c401d0b203402c02d0801c0004d01e184c0020a500b10b175103002d5851851362500a8a0070300000000e40180c0324101c0c2c6140d000d0714071404c2c101540900300d5400b01d820315008580c0e00704185c01440d00d010800300f800d00c1d0303841101452140e6004542180c1c2c06480714a07106a60b80b648108058003e52440d0300701c0500e150010851034240840c90701c5083c103105100c505416200498821a80c25600038050f05026140b03503100c14590030b00d00d00c03034107000e805600d03140500511506424441c85680000c80c0640c480c96150498a42758032004083c919100010000307004240c1403c100d490110034001c2e0412002400240c210101039100da03c03080d409a0300307541c85054000c600c0310011041e01d0f440a610160140c840010200305070240c404030b1241880c030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 971030809 1250 971029559 971029607
    0x3031e1918060609020f04090b120a060f0b0907020a030f03110f03010e01080d0c170417030d0f15210b0403080912040f0902090a26060c0a08040b07 65
    0x200d900c20301224441c0d020382e00500589070b075200400102e200d4441742e5001c2000400040c00681110f8000d441c61440141c0107e440c60100041d160070089101011643c154445040401030a200d0103032582c2103a0860b0000030500700b804002c3c1d500c40780c0e01e00080901400d14a0480910302aa200b8803414403c1101607a84d4401450b440f00a40d00034050000090356040c00460015400281c44200c00010749a0310142c141030b407500352034150044102c51b40d5007820000401da041400407101224580c0f03000442c0c580d060341c600b0b03005845030841500790103450300e060f142440307894480000481d542d115280c00980b0a88091b1400c0715a024405001c0c0380401c0f043c0000c02d9405501a0b119514800640c1c8141c204d211642603641b01d24440c80e1012010902c2c28003520740f1a83c000d040680c0300801c0d01c0e4401c3d545010038040c0c0380c0c038030084040d0403401e00d03060301890300d00744a03040e0f10071403d8511a00c3c0102d04c0201600e004c80150010300100c1105001505c100e008a0881410101c3d50207051030b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 971032059 1250 971030809 971030831
    0x50d090e1909120e1e0d020607080d0906060303030e0606011e030207080a05120117100f2903100b06040306020309030c010e0106170d0815010903021c06050903031e19 73
    0x20418807012890060310030700003c180340001048940c440170b40090582c1c40100550f020821150000e000035104204100700c15142c0000b0351040c26000380c441c60000c10810b18505003c2c045074078003509805140c01100c1000040da9111403000189264005240751400301504201c2c0280250703400140392440004aa2040c0d0790450090540d10b0044079100c68030317a80312016860a0f0044080500c00d5a1000d11102c1c244100360704240188443d2510001d12243d005560110140303a6020b0010070450b00000d504440c1820b0ac8070803081001c0602c00d1000c1000704c40172034064803891101034980e55010000c00c8030040140107d4416800c040000d0021030400d10311f1034002d002500c1019680001001c80442050340461039003120304194a514050760b4610300d1a6400c2d5107078905242c10060500e030003000581e101c81491100c01d242848a01803203070285000c00450380040c00840c4079170700c20710400c0040103154449662514040c126034504d0388039100314007100360030009100041750403d419081307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 971033309 1250 971032059 971032067
    0xa0e0a0f06023406181208150a140d020402090d051f090f0b04031e02010b151303080a0e040216030f051e130f0e04050d090e190912 58
    0x4808409074001d0240460f2007011085003424000040d40000e2406040d200840e54a03800a040344585640c00c8500740c1007030399003846007021010300b503001c1150007060081131002030598440046003503030400286070070003800190f01004001c200d0320542d10b4500321411515581c040d5400c1500180c65603117029510b117040307138485c600480c2d5207080390540e40310b4140c0748a02d0b015a1f103010f90411003894501c007441d107440101c408c00800079001d0082d0300c14001502e0880c202403014001c49580001261448034040015180c3c241c00c3d1002850410b004401e00080d000e0350940459038031142255a444900000341c2c0c40e100e29100c2c0552042c40801c0d4814684800680d00e54141d100380e44030380c80d105607013201303413500e01a45030480805c1540701101580113003001c0007410405542c4800c0500540e690009001d0184550410004071315031030103200400a041050742030401e26400c0010400c1d060103041d81c500000102018401e0290440c100c0e0b2841440c0c0c4011242500001c03600c508414030100a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 971034559 1250 971033309 971033317
    0xa092301030c1508060a0504090201030e0303070c11151c0609020f0703030c08091b0301090605090d090b040b030705032205240f01091e0606020d11150a0e0a0f0602 72
    0x82d003103a02e10100c0c9076590f0300c80c000d200e10070743d4024400f1881b5824041400001d0900c500100d06050303913410301c0d8074114400c00c01345110340c8aa554101145900c0d1500e110060525101e00d03000380c071502c010030302c15010030054580801e1480c5541080ba0368004245000d000664414541c0b54400524400c10803050b0004000c49402030310240103841c400c10080302c00e0b03141110182036541041d02c3c0d020341103c0d40012814032403030041c0013048040c110345550342298419280040103901074089140c0f2a90070011140003000c0014400d82024030700141c43c0040c0c8002069541000300000c00125400310110340f6039000c00c0b03030b409408d011069910301142d0b03c6079a0300c0c80d5400c05940886a1045844440460b4810b03001da80c0c090038a0791070001041e0180007410205238a480310043c2410b031444107407240c44000c02d00c560040ca82c0c0340003c0806456680e140f00a5141394204810036100c04804544007904060704040000d003e506080c410ba0604130800d000400034002c450200c0c1c14401345802070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 971035809 1250 971034559 971034569
    0x1a04060e030f1c031508060a0509030711010c0c08030d0b011d06090607030c0203060a0501241709011b0c1a01080d11010b04020a03140f01050a092301030c 68
    0x1140255103594200356481a200d2030070070680d445400b1442c60300000310b2002c8040c3e841418045054080d4011a211084164002c44410f030301640800140401074043d554102100300061490701c40f9688030140d01072004034030b85051040d506000300411104844c0034008042d8801a40d4584020180c500081c0c510001078a00041800038903105000c0c1c07501d09481900f4000340141c0c03502c11031405004564105c2e56060b410f1144000700580035840900c03240384202030ba060001055814a81200420003424030b01605078a5040c410034a4039070003146008500890002050050765143d08660140a004610a001c24802da103854901a00461009502c1d44204411000503101002c1c551903218240b090021690054500f0420305003c0c11030230f12a0300c0b40344008109403502101080603a48440005800a66104c420140f04440b814030160451040192440b6a52402c40003e4400c100707400341414a50340c0b0041d240d00c81000e4240d0700d0907082280b201825969413818a220b4810461080c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 971037059 1250 971035809 971035817
    0x409022113110307050321130602100501120c180e010c0e01080f04030806010507050109020418060515010f030e19052109061b0f0109080c12040518101a0406 69
    0x2c0c2c0c40b545030105450301500c0c80a4020086061286103c60001d14003180f40c20303d401042009000a050351102c0310b001d4051a002440c480b504030505408a55050f4801d08141e508a240c1c1400a26640c4c502c02c1268030072408501daa0780d0350300205000300400c0402e09615841c1c003202294440d004405448400302c03d0300c0302e2150ba41c400c1c1c0840b981960403a802800500103000041b0790350b010304044c20107640140000115880c040e4040307800c492031010b03a106c41c0404480d00700d08001c07003400341c50703488211118014a20007000d400606100b840e804110145a128103400300b01c0c00040080c9a0b200e041c40b841c800b04001076041c802d89071200c1d0841c948031403407072044180c4010060012504841801f61a03136141c00c0e520ba1100814000100303e0806500900000c40d00100d001d01502540074028a2026510724903d04014505218000c003401078030b03005d000800c40c13507030350290851074002c4c081004541c5a480d90001b4003655150f40041c00c165840112182080d65000d000d0001e403030068031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 971038309 1250 971037059 971037083
    0x11011d0f0c18040b091e010b040c051207080615270d0507050f010333150210020315030f060703140112030309060204050604090902031606050409022113 67
    0x1c28804040c2918698140d01d034494000b140001e0b0241c00d00c60341c40030108040c0c034491441c040011b034000e400000c039004242c1d1180c4160249192030701c44c104034528142400c610303102e8250802041301100038016010f000b01c1c100060001c0c0c946d0000061103ca54409091b81c480280c1854900f40e41c036554078943c00e6061504000d03150511105070503c2940010003004483d00c0c00d1300b045070700c92048003140e040540702e0010b001c04400f81c961140030138408807103481243e0311555251420007150b52240c0c2d800c006050920101b00d4010840c00d002001404002d45d0b240c1c0d54030710b14462508825041501403040e2009080032060106019028600c1640c0512586a0520124505502c00c0c00b0780c0d00e43c0e1484501100020740030341c0c050912035114000250070030f0f076502d000403caa00581d1007101525228405442185001c1c8102e03c000311404200341c80c00d42c24400002d21601a0b0300600c1560365000444c0f10908010365600f10081122404602e440d1070074810081800c1d10b404004c42c3d860881c99 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 971039559 1250 971038309 971038333
    0x51504020c070918080301080c1513050d0501060305030a0f170402090606090d2004140702030301050d0809091905060d1518142109030a020111011d0f 66
    0x100032250240260740042502d00e08003090301006014014504140320340010743c540010310070750059402403552001170144100050b0500004803055212503140005c10010351000c0c4411ba0401d100f0740f241610000e21a070214905640100115080a0114403000c59400c692580c012141010010c0c0d07a950313010850b01d0460b904113070300341c142c0d0000c0d40030200718000388c1c140c1000d40140503c07240081207521240795584035801e42d0219891001405408522150010f042500071402e2343c444c1840c805505180100c002500d900040c0189803207200c07550201c01c244140c040580f0403000e00284100b03820b0500f080d0703403010031402e180c1c0c00300500d0412001420914020811210385608480c0c01c8180b4004200050014458500070340c04a0b03000040e1341001c039031061703040345065481c04000d00c0d0f034501600c1c0840d59500d681c160449600300400102c1550384002c149094143d90a0900700307001c00d050741c07015024007440140c5048000e101070403969261000a036002a85202ea070650303807204614 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 971040809 1250 971039559 971039561
    0x6020c0f0d0e011d0a06080912070c0605032d01050f030d1403131a0709080d09030312021605011b030603020616020301020405030d05091e220e0a06051504 68
    0x41e03051501245040d000c400b925400303481143e1524400c60b01500f105280007000966804113500501c00003404441044040501042201002d4241c3e0011900300812a81d41410890150040400b0004048085003d00d214845c24040103002103410740641000782048414035142403186611501d40c142816459080200b03400c10b03c0c1d003080c2c1d0341d842c0300313064071150218652001e021b041c5c40c0040711514070b0200e456245980040312080021503241d0a01d6980280760035100d030068242604803204000c1001d401500b080e041303030f9050500e007410017405400c0300020301620720802c500c4c4c100c0030401e00c2084410b500c06045603002c07907843c50654000d058103e00320382903400025009401040614402242c54490f07102c56480180050320340b50f201d4001c00e00302403004103a100460f4000c00c64566034941030312114041d145d040d0141c0041018000011800720105140c4485400c8006035602c0c001402d411580100c6440011901f441d021403900038020b100c215a01c0400602c03c16480c400ca15107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 971042059 1250 971040809 971040823
    0x41202100204080d20030f0414040e1b0303070b01080c01120c0203250512120108010b0d0201120605030619060b0406020703080f0d11090306090a0b01060c02010e040906020c0f 77
    0x243c0c000604041ca44400180c901604011031a40204480070001c0c01c161000c1000b441e40d5203074900007a03103840c074000b03e0094011740b95100b54421801c04984003c424400142ca844503402e6804100c614101d400100c0c1c11480f4019000c0e01c2e80142c40e002107401800042c101041032800ea8031065032038800900c10b01250300e0025141c005820804c01c0000013982c641e91380c807a84c10983d00c100c1c001407455a910740780512134584849441c4001c20910041081207401c01c2c010300b2001d009000144040d40051000d0041d903078000d0500100084036030003621154444406040c024085a019050402000c1501030f200f2500c00c42d100c0c2044404990040508203a030100d17003540c1c00030b006d52403c540da2003010b07810107030820010705010f000b194000c403280c0c002c004c9411440d10f802940c400c4010145030900c00c0c010021403c6900caa48000b00081f0107501c0c40713044603118605115040310301e1004849009452404c56403090070301e5898030034899940d0044c4528042070f011a82c406005100168503000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 971043165 1106 971042059 971042069
    0x90518060f060a02281203060305151906090e01061a1615090c1401050a1d06070b1005041506081902091804060b060405030c27041202100204 62
    0x104800b6a9080046247c20300c003080c150b45036155503400e00c210b500840c00945000600c440c24004060340e000301403110a0006955880754200600355007034000c0d5642d460003c0015a410080c8440b010030841001c5040c00c00209501c240c0d808a10f902c0261035100c034051907607221031164032030700b0b190034460141c0e10900c0b8100030b42042d180581c5e400b480e051080030003400b0040c9030458100c000d0121140b1480b92182c3c049800b00710503000e0528000d20a107104400d10140d2040c81540b0341c207403401a60100141308038500020f140082512600b80810031800c007040c50144800c250008401c0c03c02c80140c0f4006880001c1203044c00707105e404444500410041c4030420000d4025802c05070404c8407000d0a2605190000f0344410b1081e90b9240300720800003003017401081241c4480c40c600706280f402031140c0703018200498510242c11000006010350ba180c02c80120031882514103a807 = true := by decide +kernel

theorem cover : BRFrame.Cov 970863309 971043165 := by
  have h0 := BRFrame.cov_init 970863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 970863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 970863309 ≤ n) (h2 : n < 971043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
