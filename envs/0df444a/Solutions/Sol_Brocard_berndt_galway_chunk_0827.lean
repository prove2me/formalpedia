-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0827
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:01:40.20838+00:00
-- url     : https://prove2.me/submissions/14d5fbba-c790-4c9d-af2a-49157c534d64

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 148561151 ≤ n < 148741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 148562401 1250 148561151 148561157
    0xb03160315081b0a0806070f020705030f0a060c050c030406210b06071103011d1c020d05030f150a0306050f0c040b0904020f070506070f090501020d090b0c011407020d 73
    0x2101d858001100c1c01e0102d2142a0311030b0040d29152901c0018401010140c000007000000555103a403021414000141d582c1e101040341e00003031140694040c00848000d20040300a0403c0300300a450341381d1905040346005001c10364a01111744100e0241003601c03080c0004504403a201c50b19000054428041c1c1d1002d07500e0440c903000819680811405086c4401b48050092400c00a40d0355401a0680e00303404104ea25541f191004c1c0c0e200860780c11114580301c40c4e84028601d80b070380d1040c14105620726000b0310301190011205140020340001c1101c0d0444028176001e01c1540c0c89001c441001c1551247d0301c2ea00c240b505400006224240d0041801a45a64110760441c0c94410804c0c916100d284500c0d042504184900e101914080c0e01410b01c101e6025819850600c4075641c4a0402800300e46210102d20309000c14100b4a81c1301d80c005000c2c18080c00182540c02d218180074101d480c0920495984010020f0440c000304020b401884449640e45901002800d040a01075101c80c4113060340307800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 148563651 1250 148562401 148562411
    0x10312020601141f110d090f0905070c0f0309051c0b060a061409010c0b01030c1a09010c020405040f0204060806010501021014070f05071a16020109030f180b031603 72
    0x5036400d040c035a08550300010551a07014044050444903215014080d00c14010112140c00c1d4428007441001c1d00c5d06101da450302e0040307040200c6420104084c0d044460749d43d2800040020f4641c2045c28006480c2c0c20050070707040001c5a07d0111014a0b01d44c22260300b003e07900800c1024000309420b03a1172480d200750300c43d4000d035541c8401e21147d41c50b0b92042800081c1e4403604500315410840082141c2d440c1890410344252480d04c4a80f500d800c01c2e4411910500291401c0100a4038440d48805481e590310503180f900003404002072040d850350f1406485980c0d03c40206040100c05c0d1680a05c43d6400b801c18071031a55178181d010b440701c07030074410039015000b101d140200085003403140348902841000c400702140c540040892388140415221010f009040040304042006c6450010342007034040907a42172850600e6030200511426021a000d40e03051040c982c001a41018201000125518081582d504800c1310010490425400702d8030b400030000a005201d4140a440c0300c11049988003441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 148564901 1250 148563651 148563659
    0x207110406061d010f0302040503070b0403060e03070f0809060c0f0604020901080d021b01050418150b07050307030e0402091903020a0503070b04090e0703020915040506060313060e0114010312020601 87
    0x8640f220450f44601d85028107490b84410b40c0114201003442c0c0c0f89103001070816403a00042403800c41981c2050f4501800032508100300b010a020b0a041c5555a00242d404c040d00c03a41e8943c12404e213401c0044c254800810607030b641e40ca6042c01d0380d030001582c0080742c40000d41100c803241c0701c01007500d0a90140c201d020010502040c00940030060500d50342c01484284040901201c900c01c50103400c0c2c1c1007041c104800501d40510b00880041504442c1d00043d408060000084920040350b20454683c0790500040000c40d00110550302c40030f4050a00303811020418000030000c0c4102d0814590001011214000000005260200f42da01c291a034a0701c164a0b041010b42e04c05083c4103003800540c04100622885041d030b000081000304100481d141140c60341e0009000303080494a1505481030f048044c50b90b45804c0c007801e81c00103400c1d10f450b03107942003032410b20040703100c0150050300303003902c41d856445045e400754044000480040191403195841e490039462030140c81d01034800510072540045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 148566151 1250 148564901 148564907
    0x60b0301051b090603060a15050c0610050a170a08030c070209060f060306010c11030607051c1109060a0504050402030a020405091f0e06030a0b07030f0c03020903032a01020711040606 80
    0x1c0b528181c4074040c0741000c90500c10800c960340014901a0004400400040e202c0b0345112040145441a15004d48804e48040d40358a843c0c40107010507410038001d4030820070b9031650203aa000765020203006101840c0500c102505c0d044203031200030b148440000c10031000740f24440290882d40e10807600c019041d00c499041144100004520690104041001c07070ba456014400811030b06204100c909002840303807000a0a00c90226100e1010801c0020b40c0d0401c05042c0c0c1c005d545002d0440000c1001c261b8011015205000d0b5483c40d03801100300040004015001d101620001c04009000f90741c0c03894100c00d198040d400c184280c600072100000411410f001c082008000f401980180b0030383d2600d8042a42005080603000c1505402071034110004214802038080c07042d138494401241d84044a40d640c1e00721401482c5800816105100b00b2040e80d4012085503140511f80509800840d01d198410310030341c181c0c61841d4a80d6100181400400400305a41c190f42001100d080100d59580c071015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 148567401 1250 148566151 148566181
    0x170304030e330f040b07051203091b01080906150301091b090c05030408180609040e0c010206061917010b0d0606061803030503040609031b03080a1b05030403030c1b060b030105 77
    0x40c071090007060000b0311416510f1406400c000740598122041d2007211030b5141012741c030a4072403c0940c1c2002c1d0141c4488400c0010140c4a80c3c030070f10f44080585010440c82c1d84405015018030a01703001c01c040501141e809411510f000d03900107001c4c0d90425803441c0341048086080c410803901f84c0c10000450b0846001d0170036240305a810403001c51810300382c101c0b500c0d00f54070340020081d80840d0500922581c0c0e100d6102c0e1030305441c41140148040c858200001e881c24000400651040a503040b1000fa03c0c15003500002c00c40e9000c03500500d68111140c80c442c007510f40d4000c5190001e06c40d00c3c0240910045400c08012a60261201d007072801c0b0700000250140038900016011443c1080442d0029800c8e5104000490280c5030600804011915550107220f031038400750300003003c3c41c0501a40f19514807034200e030030b00c060103004040c1840c0c0001a08502000b0409410301d40c1c0ca40901198034092001081d8000c15400041c100c42c280d8a490f000408203904450f001e0340c80e003000103060180c4c120b15 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 148568651 1250 148567401 148567417
    0xd11271f03080901051b0a020111010b030c04090c092d0903050f07020103090206040807141c021207090213031101090323070e1e090a170304030e33 65
    0x62210301900359216100941d00000d45641001010090080500242c525031502511124003410300c48105000042003100004400d40c0c91341d1404001618079500013070280c8041606541c08100e0b6070041c01d12820f00c11140d401800170701d0820b030015444090102945050341201005202d0112040c0b0b84003080324139110300180416400c01211000c250104090b0503010b1051401060b41e042c158082082500554041001948023840c00c4c0701007101d00e80401040203090320701704002e02040314640c007030220000000e4020405010500380400003481200068075224500703541d00c0703402902c1895170400318072054501400301031034444150300c25243d00b0116600000100ea440c103203a042c0015542c003070440c2b880700380704800000811071000001103114083c5542c0b0030081e031200151040c40d000c001000b0520681000c2950030000381c90b07084100c603c00c0c07000c2328251265200d00d01a686440301d0101164061030100043c117076074090728a9180d0f07242c00b505042034040707402c2c2c042d230a0ba0300079009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 148569901 1250 148568651 148568701
    0x301150810090216020d0c06121b27080d1b0b01051002010207170406110604030804081605010e070f090b0d14010b090c03010f0b0a020c0d1127 63
    0x810410440700b60007030a40201412080140302c4000c2d400568400039050007142d211f1107115080203159040200c1908000300300c902804030001d0048649000004000c000c42403260520000020101180900b410703102d801e80b40561030f94031100c80f03640e1503007201840000500515000324481210070b0790110350301d074055003500080e42840f00700603408159a8034107045641c20b100080210750307034039003403081c51448811042e80d403800c00c0340003080b0310b03820050150160f0104051100087d0310564855002d0b80088110351500d8002940140d00300086001810641c03c0035036800403d48089070010803107010f14460074195a035100b8410070b032004803220a82c88102905964045103804010b0840079480100016100d2048000900d6200081d41d134000c1441c0301000500880440c0c10701c5030087d00150107158100680b690303000350350761909100309018929607070302d56040082c069a1141e056100074440d40702c81c0d440c2000b0540703c129541c14080000c2c2000c000c903980d4038000052100240c480c1c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 148571151 1250 148569901 148569931
    0x1005090a0b03100b1e0619051305010e01020703080f0f1c05062d1302040b0c07050a0f121407060e0f09090c010c05030f03011d06031615050c0a0803011508 68
    0x7002c8200105c4138100203500000100000c004000094100700044645610f4003602c0d40301c0701c6e840c2040c9040315088030f414010b0908218026a0300001c0040850b540700c8901e956818054000701d0060058420b995802e02000c90b50300d5042c6003050f2501201311001c0b204100e10b0755004204140c8006040728610520007125401c0e0103810341800c800c0328064060300c8103d50420005541c0101e92046d80302440200340171a031444c0400c01400220004d03c42100c0c209409414607010405240310341c0300b00e00d00001c034000041c0c2003200140903202d2004010341540c0340780e9036a61000d810810b00c000c00c0e170b1140c0001682c02103d0700d06a03070032034061081c000050020007405001555031080744001a640b03407000740605041a0768000086000e085008880d5100c20b880010000c3c0f10030f07014003024071a421901220020302009240082294448000301a0001d64510161024415507100200b14010350f0200000e000e06000210304072101000205078125806908481490040c2d603c00d040a0384e02d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 148572401 1250 148571151 148571179
    0xd0305010e13060b09040f02030709200a0309021e0f060c10150e131718041107021305040c060f08040305070c15020703030e0a120b1005090a0b03100b 66
    0x41d02002d40d91050500158003543e00b800194402d90803a4120340c241c101814410850809119000080503028000d000740d0b00030162840450b0110720070840c44102c041072850859100b60008117003550040e2658003480e5030040c03641081a04604003501944a83e610303071a00742002c20407680c01400a0010b0110210407d12540160019210882c021412408040b44d140e4600c4c211500501a05000c400e80f405d00d46807503010318540700d403060302296040c0703d0107050b60b0342d001c1360315107110007240d0000d401499844003512500030014080d4021101c900844a4101030f40d200c2e501640c0520010b40e01715955800807074480d4080d01c050320001e5008004140002c0c0513002400c4c20a11869154085689991240c01854021100080181d0100a00300181604140c101e594154180c40001256040c14a80c040d962003402c0010a840001e070001914820f074030b2100c0000c4c0c040108941e0990402c98949030103032036902041c0344a4016100903840b8110b20780300714240044007900880c2c41003c0c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 148573651 1250 148572401 148572421
    0x8030f04090c1e02030703030f0203070f0c020112060b0c0c04090804120c090e0307110406060e01080a0e0a030207061d09010e090708030a03150b03040b04120903080d020c0d0305010e 80
    0x40311540428000f111007661a0009810708080514000303030300550f203a120702d0030003c0035a0728005000a20f10f00c10018804840d50040041c401982241003281303907a0000e20040711091004980b080c4880d203032000214000e07106800500821400408070b541e0008c0c48810401102d00018005003e180c08001c200300d2103d00004009015010701004c0c4042030303076820300d1001c0d10b901440c48080794100080180070049000040060010107480c1088424242000502001c0f002c0c11840c0c1408400d000043c8010b4094116203408104842950000c6c074003881c1c040c0d610241c81c0103441c041234070300e00c02081014003442c4140510000030061003040c1d1800d0540801d02d00d01514544690185007404a5004410001050100703559034000880803000c00c41d2034103801c4140c2190703400000030400d000c0810800c559158101d40c1041d54004840720001d800d03103071140705901c0148442c6000c250b5510844055000e060425842421386003034140f090700490440301c00340201f94581d003047c800f00d410020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 148574901 1250 148573651 148573661
    0x30b0a0626010f0c030203012d0b0c0309041107030809031c0c2f0106051807050a020715090608060d050703030806010905061b0f060f06092d01080708030f0409 70
    0xc0d081e000050900c40380110100303441441c0f84020110380c00000403c480028444021009010001c095180c10f00f0301010054a042520510080c10004503c01e1800c400600445520740c4004004010b0301c0c481c10380c90b51464000440c16400708007614001050164040b00300c9041c07104e000179649500700c50180c25001026003001c4801000002c10380e50700390307800507141014410400340300480980c04400c1c806003500c3c82c90300301501030fa0700d0a150030f560f1840c004045400034245c1c00c01c0c9032101040c0004a00d4110031b94007200380352518000c910302003900401c1d9032003640d1050b65400025550041032154054415400400c40d9000c2041080428032800c4070305d0300050145444006540d075840050302c650000d1490070b49466a4040420108108210702c107075955100019044138540030107100c110180042900c0c6c0604056400500303004008a5464141c071185082c88040310200303405600848000d0007100c45902c1644000304042c2000002c5c0d0321900c011050340f40c905400c1c6180000504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 148576151 1250 148574901 148574969
    0x601051807020c091306051008010c0f0207180b1305060117040b0f0403090503010e030c2509020a12020705030a09080304080d1812050d090b0702090411010c05010510030b0a06 77
    0x14185c078040c0f000960358000d0a0240d220144000c0b000c81c100342195007100d5540703e40c00144424403100100c0d2640200d09031085031003008040d5a030350b200808800103803030081c80007070707026503c0150440d52107000c2c0c0c403443c010031027a40c4901c00c550030141c808441c80401d07603014000e03407402400a600481d400480a500c10311030f01c5e05148d1030f991880442d00b07660600c01d104450f030700081082d08141d00104007d00214542c2c44200b20036a0b1441ca0308001150316005a2001c1500081e10540c0140070700800c00c140401c2000071987c514030750500e9512500559100000200b07003001c00100011700005403000c1c0c82c60b040c0540841c0c0b49881c4140d444181180c1e0460380095180c0300000c010400b9001d00120380e0103a0081c00c1c0c141c1c1107804c024422161600281e036039802c180542c8015840d04201c0fa64440da020b0000094444503030300585044541c2c0710700801e90740c20181013017484140c0017041d100700d03840741c0461915516140103c0b816180a07001e510030071805158000b003020030f101c40038a80d40d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 148577401 1250 148576151 148576171
    0x1080f1e070e033f040308040f08100606020303180c090a140a060602030d11071b0609060e030606240f0405010801150c02060904021204050601051807020c09 69
    0x5160044000e1441800455000700415040510100e0605050080c10f034555130286000c140341e0929064a10500c10308001c20a000500d49407919001c80d04000b03c1d0051504101025101d075640d070b800c80810151800f88072080e014440c80c001c0d80c03141a001d60fa00351000394000c2d500310b51383c281e10002880309010101300c1030b10a0f03a0929266864110620703005912111021410034880d00c1241620391002c1d050510652403c842040055030201c241c540000b101540482c0c0d410101c400b5100074091030310003410480d61071020101c0d8103184201c040c02c42c1d4107a16041c140603034410040e64a03003a218441c1c0d13099048100000c100746040c00801e11500c1a81e43c1013100e00d10449440d002036003040c44010701d41c14000405000541e008030307085004010036482c4403e40007151900801c074071142900240606004524501150794a405031103040c552a181c2080500e801c0c03d00c0d541c0c0b400c00b032050718000e807400c1401c80704800038070044520490b80703500240105000380d814080300c2c15004040d0512 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 148578651 1250 148577401 148577431
    0xb0106030e010f020d0903030b1207030b040305190e010801050402070f020d0602160501060302090f0c1c0b1c0209010b030606030403080405030f19142b02120708040605090601030201080f 82
    0x1609910f1028000b181100c2c0e078001480c0c1303d00e15000c4c8c2140c0f84022070ba480754005042d5108110400540c107401da0744c0c4108050441e0301d55140c1502e0078021001100c26611101c500c0d01001903202c01d0100c0780060990301c4414591340c840a000c2203100d80e00000d040d481c0084940f00c050f04241c00e9100d0610302c01c0000510301180e03001e20350385046045800304d030703a0303515400304105524052800700e811840041401d0708505100390b80ca0003922070000442d01c1240b00d4502d03d07000c0440703640095140c4030f0181c03d004121802c240301e40c0756031034100b00c100c1c499a013040002c541c000a0a003624421500030305000e145403590f172002d640d1403800400880b92407004204081c403030501140030b0100d607020100807010208110b20301821391410352080f4003d11b81e060202c01048049880401c041d100d994480140310684036117004068400c03001e040840a1405042c0608546d1081c2d5562040e409000104021340f240441e86807220428403020780014400008103100000001c4030a0304500154440e5078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 148579901 1250 148578651 148578671
    0x1707050304030f05010b010813060f0603051204090e0309102102160201020d11100c09050907020c011419052503020d1107120f030903140303160201090b0106030e01 72
    0x451a442a04201c420030041c070f183e0000c21400340615103418109080003442844c0100349014103c51300034002e040c0d40d845840b0514401c030f05038000c4010316000006d84440034010b80c403404c6c040d4018410f0203074040c60700c1286040004040195800503030001d14040f401d1141d044200d5955407181502a40242c68a19601490002d440240724031203030084819a059203034000a03007040341c500481810301c4904130b41c00030403c0020400091800708048009040206224200c54040107071b08074030342196154090281e210380024160400450913622101c02016590f0058103d001d0789111694a030404d41d030004ca03190180f00a00400b4007a40700d20b0001204410403440300304510360060b005030704a0810520a030382c0c08862030328480301c0c58004245840c40e20320340c03d940f400079007070180144680e46181310400d4072892400d401140c2000e03110a0211a0b218100e0b100c0d40190f4680040c00040b00540400d14010300a0340e10090b001030310246180e107040025009411648503039280395690f016148 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 148581151 1250 148579901 148579903
    0x5060a03200301060207030308090c1f030207080f03040b01051507060522120306060507080306040504050309030709050f060907020c0d080904060f0e06030a200a090c050702180601050403170705 85
    0x43c001e24040c0c0c014a85103145080141070b20901515035015078110008400050329000b0190070141c0c42c0135911055058444d0048000303000d404170050003041b00013990f0700203243e030002560066000b89010302107070740e880e0300300154a1010181e051000b82c06124a01c0401e11a9000d95400300c00d1038002d0681e19441e100c48800e0301845081201c00c840240030303100c500c3d5032500c50340c00a0072007030402c1c91a080558440c8502c85c080244240e21030758940000404112061041d5440300c0b0024003155880750700d030360006001d0401251071001009550001034407600c3c02d2201c0b01c0c0070708080d4010300103102c1c00c01c2c00d00204415280c41655900420848001162101e10a1000500660a107a4801410111101c1007035501400030340c882e5000000142c0881c18911007400d07152501c0380000b00d50601900402d9a182041e448129074a04e0f1158401c10306800c08024074400c0d108490643c1c200c0f00c82003269000c440203a0b452800a8014441480010800441c9580480540b48224244100c5640b41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 148582401 1250 148581151 148581157
    0x8030603070f0b1b0c03030d0b041d03030f070804021318080d060810020909060d0c03020d110907031514041407032a05030a020f130b0315010905060a0320 68
    0x3c148540000030b01c49040002c075211845000a520050710012480000190340e80c0600030702030b1501560341c13000380025070351903000300c69079251038154949180e901c01589489400450f0000c41d8200044005103180e4403030314005209590003004a80d0b03c8072010400c0e4010a001c0703d08a148080f1f17001001c0100c0c040902a21022642610103c0c1039820440040e0801101144a0406600501403000e19989019030f550740034000343d504140200d41814440f1034507640ea400a0741080c294049801403004484401551060139140700075640c4032002c08404030380d01c400046551146400090003648220f0559002c9075400174804101a000941c00341244a019502840803965a00d055000340407101c1e00c0248136460b820700030524101e240000340c40c51000529040e0520760000382296140c2e0304000790ba0801700c1d200c054600503911100300904075482a03c64146c1c010414031003084540c41601c810342030b254064030950400c01c440b02c060b0b0140c070103000c0e00c91038284458401070410403040d000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 148583651 1250 148582401 148582409
    0x16080307020c0f030303070e030a1b05040b06090f060a0c05010e070510080702060c1b0102031501080a1112040201091a131520030f16020406090c020a08030603070f 72
    0x16964104050040c0c580729204259a0141103444020901994088280c076444941d030f0800d1106c05000310006410050040c02c004c102900b26141c680300f140102c25070400384c4000362030400c102c000a60070003680307018079641e40c0d600c000c003201c5002513818030300701408030160302d07040c02c003855070041c2d41c2c150941c0c0c0d03403c07002c1da540d41c4504810032052400c3c40100c00310541c0b03400c00c01041c2c01c5c23400780251101401040141e401c1800200e224400c200e0700c2e101d808400f8450000c54580c00e1580d0001c843c0b482c2c8800c10350000b001680801c1040000d4402c41c5204000701150310b02d040841d40541802c1880200141d0504c14998400608810044068101c0c804403040c4c950361200d800c0082240003146810984800c000103e01800680d0007501000080c0c51100b0484000c500d001e000f40d28610651045002c201d82c00b203000240c0b1904000c4444003a48220303014400c0b00d0301c8019150854000d4031a540059010345400e8021441c554015904908090243c4580b1038803116014416003013540 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 148584901 1250 148583651 148583663
    0x4020d0506040609110403030305040c15020c030106050f031b04020f0a08040524070c1b08030403020102190b04020d05190807110102010908222309090723040216 71
    0x3007014034a0a072046034054045031908004281d015007008180f405103002c000d0526540304086003d02862902149c02002801103030620000c2d180e40080d11031101040743ca0007503013405400b0803946000d48c1400d540c40c0d4058028102824903200c4100c020000349501c41d00940d0070846450604407003002808030a805072503003003040c102440d00c0351402c0110084500800041e01280c820a880e501c180c0d504900c142c1707003d40c044511400c0c0042c00b000391300152080b90000344000034030030f1408005401228000d03000d0300d0b50306500c1c0c0007112041008450090415894100003001480d1102c848031b0054001c204645041804162440c58070311218420ba40b1044049000020051080e0748071110800a10003404480c0c040da1302d2010b0380c082c5888000c1040c0c05003c42c40e444096071100400205101130082c0c803261105c0f401402406d1107448401d0060001900041030b0520000c0e48108896000664802103101d80090b03014201c0443c855540c850303001c100020190b0480c850440180380a05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 148586151 1250 148584901 148584911
    0x11010c05032409060f04020c07030b010f0605031005040c090305060a14090f0616020127020a061e0e010c0209040c17152a0a030c020709050408070f030201020904020d 73
    0x1000c0b00780d030031441d08100b0180c142c0e4101e404030070307216142000d410010650741d5060400c03500700010081d01407804050070a11404c400001400443c0c00140c0c101c80010301b40a04641e26244202e501e88412107000b60a038800e03600030040307400e00b5032103140701c0300b114a4410400358803941d03a03d0400ca0251414440d440d221078203103868100d010340581e082101c80008000080c0c600c004e081d1244c03c014118800d0070022a039401c4098000e400407207401e0f110030100d030881400036007501080044514180e01a824118010840074001c40d41070f200c0385081c043c11013481d00001340840d00b540d000b00c101810001002d201c01c0058488100c00381c0124400e80340406410b080502d00c84031242d1000c04100168440070082c001d02044e1003506400c0a00746401d40d031900c070a04054820700c8040c3c0140c0500d005c0005032162a035a16a020302e9040e500d560a4441d5a5580d00c0e421055407401ea4000d1310a00040040c0d10001e101c004a00e8000c174030900015003003900c100d00141c2240c210ba0120a072450f120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 148587401 1250 148586151 148586161
    0x303050709050604081b0a0801090602031f0602070e0403170f06031006050d0618080c030a08090d0917010e061302090109050f04080a090b0f0702030c09010303050a050a11010c0503 79
    0x4241c0c8075018000989805042514240b0055580c801003241c0612203510002c003a403003501d40c40c0e4910041c1c50200003d000c0018540361070802544100d0314400000c1c11411621000212031145100304c0f01560300401d4045d06005064900c5440504103d0601c9004c141c2070a18101406102c2c0c070401c024000000685424003e050905464000810072185030600c2488a50758001c0d6464096820210010740103250360909115002c41180c00303081d5a40101d80e4010240b8004014440240e4650f50b0901545850f15001c0e039a0708028840c00c041007520383d05114072800385240b4040d04140c1d100119002c5c00d0904018207022003542c0103a1012810900d010541c180101c0d1240144903031101000380e49000070281f0a4002c010300010315850002a145c1211445240108040c18071070405503507400c5120b04a5030143c0c803607482240640a40305554050b413400c1458141202d4054450a28040c2c1c5900111410f42c803000140341809444902685010700034418055000e036151503075692800c103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 148588651 1250 148587401 148587407
    0x1303030e130504080409020708040e010b03061903030215060613060806010201060803030907050105070203030c0d050301030204050c07020d0204050a0e240f0702030a0f0c0f0c14062a030f0703030507 87
    0x1914a80c40d1400c05040c0f00029200104a1381180d904200050b04e5440f1441c00d000e95224951000340d030400745d48004241d94020310025402140120b41111440e6034110441031001164440a000358201e00b401202c10300760810b6199201ea030003000300b841c1c5280c041076810800d4442c2c01c10b81c00680030400b0080c16580900c64000074208a0004508610300740e0185559903583d40a2a81004004504d031021500c04100780c41450010740f0580e00c0307404200c1d074001c045400901c000da219a0800b030114501185a204503111250041e03c0c004215580d41c003484058031002d42600381e01030740c4400340c1401c00710034802c10401240e404500303403105104e5111758000801c050315428030600d907481030112035038000086070001001404d016400400c00e4030145d8507500241c4002d800300046189110030071810f2440901915400c00d00c05000790000c10501001d400f031601d065110311040d01c09510841d641d440f0544040d03843c4c0040720702d081031481c111200c681000100f20003103a1541e05010700950 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 148589901 1250 148588651 148588669
    0x9060403020136031701180f0903080f3d1e090903051b01150603050c18060c010c02070602120304080409050613020a0203071b080607050a02031303030e 67
    0x1403031184500049071540f102c500c01c100310b80c3d11008039554a40c40e41c3e00b014042d401c0031669140301054036030150303500c549050140c0410028600302924107444c00e2070307032041c1303201e08131115405655030182595407440c01481614041e01c44400228441c7e058550040c3c002001e01e6100c1018101c0400f07a260342114213041c0c00070f82c0000d01101c5890140c02c402013401300088048881e4210045030315000c1c0d06049d82e44c5e1003800450031030b8410301c0c0400450040705400c04220b884d203455102142c15503d50003142150010b40c2c0750b00301c2e00d200b0062001420203508564001c0c440040c40c1e81d1a02101142e0282100c1c1101c4846c00075801041042007000c0d014031225200030289003c0c0c1f40b940c0350a03580d90202d4440d9000f00000f903a03441c000318690380c850401841107040c400c00308540c2c8004602c030107983e07508441c1c1c0803504044000d100212850001d1180802c9800c1c40000704240d4540002c20b850701c0d040226010b04500c82804900300c07245e02052240001d6019890301031550441d8811b01030800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 148591151 1250 148589901 148589921
    0x607020102091302070503120a02040306061d07030b0310021c0c1806030507020d1d031e16030f080306061c0b0a080336030a0503090102010c0212041401030b09090604030201 76
    0x600c140700000100c0c031b02004403490900d0001c0380402d6940c2d1359412000a0082c0d070005000107140010110341107020265441c040c40c21040e43c10942c1e5204141281560b150525640e0150000d2403c02c012119640103050280d0004252141c41d007550240343d400c903180c5a8003100022811140b000c0f5500b03000b60500003038081ca02c0c00384007600c2d20139006965600460090010440c00500032038141682805140c40c800e4000d0982c0e4404800c080c81050044e0001c21061302c2d40030b010b03200b00c6600c085200d5007080740c1e40700c01440d0403051a91599211a04000c00b144d0700001d08000c0d0100d124001c0d40c20425100e449a00050714948586c180030301072070603400c0441190310400802451a1840da205003510041c039028400d56002404c0421650302c0e820304964140c4985d8100c503007000004406400100020307802040038460300740e01265505451075078106c050204000900046c0541d10f07070381424013418100861080f00800205002940865042c041904000c1c140401c140d8217003d610a14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 148592401 1250 148591151 148591189
    0x403060c0f0507030e041e0903020c0d21020c0904031805100c060506030f01020c15070206061e03010207080c0102070309050609060f030901150e15060414091305060702010209 77
    0x440e103801d6000d440d51003000009028000d1003074803c21544c0e180d8100d00c0e616204a0b082c820001c1d070010001e000340c80d820100318090700070300901440ca0f081c5044616040340d089180040e22616090480911961a810319400c6005003076103c200c2d03460706074066015500c00e030750b07402003403220140c801018880c41d00024400d4200194024000340e00009100c0c6054014000080540b1640c3c0002d00c0c0071104000e4950a500200c3d01251501012840d0409005608840401c030398440904036158417003280c000b54060245d465403643c034000344040044880e00500018a050038076111049583c0016024541c16900007560104250744100c0800080209494650a050f20500002c5446c003d541c00381403042004070008113190005d41120314140402c2181c92840c94070340b134aa05142408603100308505180310184621410705800300e030110b60150819110740310451040140180000d494058007030311100030000450b07424880b00380075401c0c54000594036200f200c01e00070001e48042074074147e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 148593651 1250 148592401 148592417
    0x121005090d08060f01090306050117010b092205010608150106020d020601062111070c0f0b091e0111060a1b03090b0109150b03040b0106110307020d030e01050d020d020403060c 77
    0x1c9140c11051032a0081412601c510f845100c400040b07078645250b0b40043c080034201400001d255004441403441c60304810001e0150741c0701901801014501070f60310901c1a00c40e01e1a040904400c4070502c100d06100e4800800c0090356021041d25146440c88140820601000104281c03a010042e0085a00d81400580702d298540701020b401c0c9070707005264961440c2e030690400910134aa5010086840444c198591a483c1c24100504982e841e801408000303800c07040007189081002c02030b1510b920f001480100d405828000400740d0013000401e180c140034400c0d80d440d500c0001400701c1449480c2035140000d0898020748128108030200b00e130041414501411030380400c10480b13055064401d0301c2400310b607c00070310310750b400e0300801b079400014280e2001c004c4c0700c20000348a9696048a03140e50b1505010710b07005100c1d540341e00c01d5141c000e500060b40414400040d018603090052100705041c55400c0c0401d00800c0d100380c0c0d005240803080b40fa40054140104410340c4256041300c6150f20b80556 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 148594901 1250 148593651 148593673
    0x108061206010302120705130b0f0102070e01030f0f1a070806151e0f040f03050c04140a1a0604170d0305040b0a1a04020403030f08150105040506070f0212100509 71
    0x52292010f00029000b45003214141c088908100403000c01048054004420001d11042840017800243d40007480794a107401c1c1607009601c001400f01c00c0e103410b42211580750340780d0ba541c1010380345d244004039000c010742070788900070400c1e44807400a040c81c000041140c07441c20242c020141b8400601c40c510980003d00c05021110480003030b2891849003998245101d180041740000a0041d4510203500060006001c11807a40d5021140308492081041b51070340c4105104000a40d602d03080888100c45c1c3e0640001c5040b130050700704100700c0001141002440000c9000f0480079405a04682d10041c03650014041d000d10070000c00304170441c2c0e4681000a070400d55109000200041e10362070403540c81e01c1c41e500354228a043c1b2042800f2004008640c1c8580d0383c540607003620310740e8440d0303004511081c000400900c3c6c8001c4000f1200c00582d0b5044c51326041c0000c11409401600c1c083e20410512440d40b00140c40e90800304410582c10001020036685803a101ca099441c000c0070792189400030f554100c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 148596151 1250 148594901 148594903
    0x1050102010e0d0815061c050a1e0c0903082703010903230408011e0b03070f0b0703030e070f03050f150609181605040f0218120703060e0c01080612 65
    0x21041100e19001d0304d44c0c2c54109420205805010045910400005005440d41401c00d80d8818080001905000c142d46601200c400c07101441000c022580c140d4460040483d203a500c4502070444504050700383c0c41d2280c03600c2103103405c00200c030032203d10403020022001000c81100c070711880c4110002c2c400d1904680d80102004412030039040b001803a11485050604141c0c00e131005040920001c0254010358405c00381c0c8c003d14450341652082ca0a1010315403400e01040e000181c6140c1000c440d00c0c54a4611101c015a01068051b81095a606c04a050004c401c1c0f00cad80d00103090700c1c1c003000001c905604000341404510500f80e0001d5100501222100d840e03050f401d03601140c11110506150b6900d411241c0d0035002e00801c1c04c0c140160305006004506000700402514001d440c00c001d542c2d80003000d0000c03031044020402400e00d43c800b1410071441d15441c52803004100e00d043c0c414159807640c0e42d600b5a95000350000e196003100c03450b602c1d6540d20484c0c0540c4954115401b100d11081c0078103c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 148597401 1250 148596151 148596163
    0x6021308030306330c0109290f13020a03060c09050901030b060d0303020708030403021606140313030c1a010603050c030103020f010e03030912060a0f060b160f0803040305030a0501050102010e 84
    0x11500b81c005031003111130400720300729016007203014000240d850140b403c800b80200711610040722100610203070605d000b00512680d11a144103902e0b131103180e40700c0c4003903000038680c000c01031003840354101200740040e101c14444000441c420800412a800301e014050301e454510b4100a00591108004101140c607800040e03422001c00d036003180900d0640c0c101103019205402000e06002c40000a200c20160300251a100001d4104007c4440607100c1200304d554a40684440604803405d10101d40180d4405022188103486030820b01c195004669070150340082980c000f413a10a0390134010040c058040c0a100d074014105500c003483c543c110744c006200c01a10349a0b050400159403100510bd89041045485c40c44000300301c00d008012904125a580404841c00c1441900340100d0414080c9036001780c1e41910201b60509003071840e07a081c03140640407109025180040d02120301c50103e03041c60002c6005900075a82c0507603914003482c3c0352040e40d106034007250440e0300d04506401c11800120b50307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 148598651 1250 148597401 148597429
    0x316181802010c03080402010504030c0e0603070608131e06060305030301080105060303090901090b2206050310020c0604080d02040e0c0306031603050304050f0301020d0f02090901060c050601051203130306021308030306 96
    0x1281744580c41d03a000407610b50150740c20082180544180101c1e0701840090124402d2034102c0032142041d07150801140c0c0c814041d00c0004440c01180c0712340000501004400c1a40e503400d50325400c00d03441e5911100d0907150a070b481920a60400001801546000c3c090b66a10010a4004602d0701c58108045824800144561041c60b556030405c00200d42d11084020781b01581c4800307600e251041808050300412040c4903041c42481642c200700111a01030096415410320140900310b16030722a00d49034090b50101c02d400d680540c1c04c00c0046150410a10f180d4011003200080c5e07501c1c3d00d0908281454400c034591170001042c5841c800700b000a1001080b034060b220f003501c00c4000c41c45154042406802a4002150428108084400c480585034081c007242e040403102e00000c2d90741d568003642c01d40b14400000c2c0694000c08018061428543e1217a4100d0f0300400072286001c01d640040500740f8041d41044800719000581c04c2c001c6038128402e00050528040554554203100b8005084200c0e0109 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 148599901 1250 148598651 148598657
    0x503090d030b031c02060a0f0b061b030c0106060216060816050c0708070e071709030307032a0c150b0d1103070e1306110309060a0b0316181802010c03 66
    0x30081d100c1d510181320841c280d41c54400315091519407044040d4686604843d491409464442074030180051402100110340300544003a18020401e880c655006040050800032071004009074880c0c00400d109040040000c2d5001d041c9000c04203101c1d00700c0900f80d51103201000b8580e03041c48500603082c1c1407a1142c10003400c1c000d940c0d2074600740081c01c049042e0b100d1000c1d8000d225002030134021500186110340d50390b640303190092410582100781004140c032650642c1d8414000140014043d502c1900550242185401040e42d6420711f80c00f40c201c0e220004001a1307080100400f00402c0b001980b2180228000c107009080c42e00c400300702c942e200c07010050090309030581c400d151500d062150340090920b120500300107107000000c10400000001c8200c80d25031601760030109442c00752044c0c034001e00900d03000d4071203a01c0b10039401000d040d0b00174841d40d15008003940383d50f1040004185a0040c00388810002001c03028420040458001e034180403c80c5090303450050050380e2104044012943c141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 148601151 1250 148599901 148599911
    0x70f03090507050307090e01060906030c1203170403050a08370e070e190207020a0522051501031a091f090501120204180c0b09030c0301050f040b01060503090d03 71
    0x410220b14008007039205a8140c000c0b0900801c054816400942d400080031009010240d59840d4043c00c03104030b0320003c0c0c990704010100740001c4100d100c210030124064500201c01c1c203181080c66280703a80940b07040380403a10004c0c0807130945412001e8990b1001900c4481d5810303034244142802a000c0031a2022982e90042a01500304a540d85c007411082c0340d0740003141c007001d45640c3e00da01140d9082d5020443d07103070350000026140696000310380c0559400342403c1b407650b1815083c00015060754554a00300e603000000c3d94118285440f8847c41502c601080b10b030103491b0000050221360321240d540801411668a0b10034903140d0102d0281c2010400684040481e151010801600c40b1038204040792402c02d800050440d80c039060010580d8000c0301d040040c40c8502544110340c0e83c030098000c100d10b070401c104110540920029150002025050b2aa601b50040000c0d08455084a000742c407100700c1c20a2005100e0306001041c05840c0c1c4e42041c500d5400c20740a440c1d550842c404001040544030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 148602401 1250 148601151 148601153
    0x1401081002160609030201200403080d0c02030910030c140c060105010f120c0905010807030b03120c0304050402040906090605030d1205102103081b04050d0f020603010e1b03070f0309 80
    0x1100c0d0000e00070b9040380c410131604240d0302d4001d019003c1c4000000903c42c10451008605841c6411502200e6212159903c1c04800512603400b0313188045018040d0702050041d00220344400c104011a0740050390b00103001000311801a020040c0c44105042a80091248104007940042c5080c150313103003401c10714208804800102c034200060219480a64284505034200d25000000c2e07406030b410036216183d180e618850f040f01260314966076561701d1b6012100d8481c20100d40d2004000442c581025640b40944402c041400e0ba80b082e800300010b250f9030b420800015080e441950050b140440283c561030b01d802200518041e580c035009240742c3c6c0e507030000c1281c9050300c942203002000d4035202c02002c90305d5281c20720010284580c040d8003269020300000d141c00c0c108030550100d600030300c000d242014140f01c02d01120184010003150095400b11910001d0303640d100c0514000d101c88002d007161441d00941043d041840b90081151262052041c00780c06a0402c040f01e002056520340081c8401e06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 148603651 1250 148602401 148602427
    0x604020d020d17030f06060a0206041101031b090305161805130f200a051023270312180325090506030601051005030a020d020f0d1401081002 62
    0x404000a0144000e0f181c001d5078040c2c0e0402a5210b0b03034100b840c420840d84c40c0b07014007403d0710800c4403400040c1c00c0700e0009400280c0fa0b03003003451113030410b250005502c0100105100107810280003600440c100040c200b040107800c1000c2a21032200d5400d0303080480c64081070030304038444a0040c2e1240ca48807000240c07500051a440313000345400840f5003034410750504001c29040e0303001640d20301c03035551a800e15201c3c0c00c0c03400e1810116040035200701d400ca0400d14045a2300e02c107a64062805115840e41c0c07075000c2c0002005440c02500708403081c08140070744010150701c4e00d40300d07080c01e01030b410034441000700060b25000c4d10449560300c00603185168241d00020706043c0c1208500c3d4a40b0180030f05080701d461400b200b0b109503490405e01304000e460783c40805940b00024482c0c6a032040c103951514407010300c02c00241d604034540180140c24103682c80043d1050b604540803241904002090841c0d488860b80610407000321000b6120815506010b400382e00c0f4040c1603c1c20752801d800290024440382 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 148604901 1250 148603651 148603669
    0x10e04050c06040608010e060906030705060d06030f050705010f0801051c020102010f0507032408062a0706050a0b04020307020c19030803010e060306010503030a020a060b1c05070e07030c020604020d02 88
    0x20002c203410b40d50381d22900041c14161302806071384000101a0002030090038076807103490040000a0003020898030f0041040059400600382084054a1f54000030000c0c4c1c9a00164480c103110340082c2200c0c0381000300040680f540103c154007003004a06c0108019180c8440001d4083c002c2c0380c05003001c501da400103038003400c020b15044500c3d41c508800c204036140e041c0d100d41c5c400654890108100b038008002c03109540d0781c40c0140250b03908480c0100d0001030201c84280e448120302c00b00030003291210b0100c45016002000c050343c0960321035040088460b058490955842000c8800f1800c605140100035965000d454580703000304503464100d080c2480301c513004001183d0224a0a070740350f071180d40c09182018144c46c2d00c4d000b8030640700040340503e004030654100c511590300170400d000440e00c4070b0f409040554001038000c42d1f07001603080c0503a5119105658640120003c05015242560601080030001c3c0701004061800314007518641d4046500c58001c3d804407520a1042710750b0001440f200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 148606151 1250 148604901 148604923
    0x60f050f0c0d020703050c0d021305040f0f0311060a06031a0a0209030a06020705010c050403031b0f0f030e180112060b040204122616082a010b090112050303010e0405 73
    0x480b031200309040072640002c00c1001d8a109209030f66900b28420107121804109107002503001004290790403281d0003a80c012603001e400764004131000f4019441c0c0b00c3d2194081101500005d90610000b08884400c00c584d64000030340c40d10410446166846043e035204080d1a80070000090001040c4444c100740c05070340c0100c4004041d5110041e851900b43c2c020f50155404031641d500707004c511400c90780107005840c201c0340c1580b140b801c580b011203c0c800880365004030440d03070500b02007550b6002c50003500c402c0d100b080c0300791100760155480c1400c2100c1c007035030143d02422171982600148061301c45048140c0032541c2c080c00c042202c035407810008029000360b41161000c004081d05540a0021803a49501124200c118803540c1d1060400c8108451080c0e00c0300e404500c0c501401c1c1c400044014008142e140800302d09a800400c240400c014003441e402d400003a80e039154114402245007070018540108060015003032404a250703921038a0340414401e00c1400c00d0403c002505100040c40006854 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 148607401 1250 148606151 148606153
    0x110f060a030b030c030f0307060f0c021903030908030a050103050c0406210501060b0f030f070504050d0b06041e0b03010605010e1309020105070b01060f030506010c0209010b0f0d050c0304140601060f050f0c 90
    0x5094041b0944e036a42000e2003d843d100e041000004042019105d0f6250719040c95010300b10210610341110107001c1c0d40001182019590700c0c02d0008900c100e00554001e20724107001254552540c10310034500010400c117944110b103007100030400c002800500a4181040361141c0f4084030035810000d0041c111f5500404620388009070b40c90604010000952203411903184049040c1c60b6100210f8841c000e1703001e05500410340480090108000d00c2c01d050340700500902c08200c0046040d000881e503000c1c9014000110744400f08210503107400e02942018003801c0c83c0049003600b0305000206954840701d6001c0005545a8500d800d591041080b41e200a0300905030240380d50f540c45000713140c900307800703c6400000d1034070010075119841182d102400030f0300188204910b9007040000d10f120b80c8400c0e186280c01104024403403500c081400380910802c00c5540d1244c81e403a05042800507007008941c03442107038101c00010302c4a6038128084882607640e901e03183d500c4d03140c80d03512000b01d88034105d17a866103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 148608651 1250 148607401 148607413
    0x10921320c0108010608041502030c09041d19020d02060c0102090d030e0901061106071119050105040b060405010810050705280f02060118020f0409020703050304110f060a030b030c03 80
    0x285100c00240020011400e0741c034101c0c10303a83c403c022603410000361801850103101c00e50042d5440c04580181da0056812601c2610b046203d0307000904403484801819201441c514003000314a074107204207200111030841c1e025003860350780e000030b41c011890f2034003c0c800c0382c02255191941b8400d5041d200c0d080c101928124025a8908003c2d09894404c10b65511400320b001c00400e216100d9080310501860071002001039840d4520141c0b5645001c0c605108a8400c01019002e50860f0300c4544103014050000015a03050908101003201c0000b0200c5005a0920004101814000442c1ca0b40d400b00990000384a8495a070225614850501e030064004041c2d070550750481c22142031800ca60019032203e0080041e0140305984804003481400c031018000320001c4617100307079a002080f04041010f803240c030307181e11480804100d03044030805400081c4003000300400c02010341850000d81c070702101c0040b10700d15900c00080c07452041d41c1c11501015159440b0000c0e5803001c1003840d03440710004042e41c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 148609901 1250 148608651 148608743
    0x60501031406091c0302090f09010b07031103090123070c0b0a110c060a0f18060206180a0c03031b02040504110112020c06151906020a02010921 63
    0xc980946000765107450700540d004101c030000006070386202071065081c00fa82680c0c0c400c0d0b080c0c000f90400750080c4d41004904040524036940d1200c118040c003044074a094a41919040c0100044601d03409208681c1c02040701100356a080781c140145031b81c4d8101040c0c09c4586540c0c40700c105000d00c0300300801600c8080c101080072119000507041450b03070b40c0e0390100341851400302207503500d440f5149590001006c00000c2d4085204a011b4000c96070079007803403281650052490040c00109074440401600f110040c0040180480c10000c000c01000c0000c00f032030301c400c1c1c488111905d81480000d051185450b1404200407501e4107802d407450b0010001c200f1403805041549860100b07886c286d001034103c208034038035030f83c240c8241c07066245180c0003401540e03034010058000c40c6000342e045510030141e13030b031241d0881500050140600719640c05040c41019901c0058132100d0f064129042121058640107428000340b0b01c51547c4c03030f03000072800d00103d1441c0600d0303861403c1c403d1034984112400c00580 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 148611151 1250 148609901 148609913
    0x50f010e030403060507080402090604021b0303090304090b030d02031804060510030608010b060c1f09151b050c03190905060703090311030f071202010905090f0910050705040b07080706050103 84
    0x44100e13401100c060104e070ba24004200c903c0c82040307800950003000712000c6881801c083d40500700c00d0f11000b010094807420b01240c0b038034617001141c1ca540c2c1c50b400083c0a104403901e50080c1d10100030103800070a02e005034034901940302c1c011034070041182c840e03481380e031078141c2c2d00c64000d0380040402601c000581c0642020060181c03901c0e0080061035824868a440142040d2048404000181007e00308450700f0801d0741c0c0622502c00200c00782c0c1e42d110003400c0c001c500c0000008030103c0c440754002408840a00200c4050a103100c43c2d1801d0150a01810000e60004030450754406c000300c4812801d00320b0306030140e0382c3c00016080150010301c0800c0810815800c104041c0c00d4a00030008400010340e814101035440c4583c007400d02558212100c00c109801f0720300d241c2c00a1610505005031560340b00c4d0049030b1485400c80300c3d02d00c0513a03901c05002c0c4c20035040c0902e000840d801641403100f8540310300050098440c0384540c445a001c00030b6654144500c0800352844254094014021565a03042907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 148612401 1250 148611151 148611157
    0xc0302090718050109050312030901200301060207060f052d0d0218060906040302090a020706050f07320705011103011707060507050a0b040204090605011e05031612050f010e03 77
    0x1403502e4090340c2c1010589601075000e401c1112402001808015070301450400107400107010312100d507488912204446141d26001490240b0602400c4d40b20762414130003d20b01149940400e041c0412404034000e006c0d0301400b1a01d10129280304ca442021442d102c44200585909609000c240081012001c1e10407607001800c0340d1842440490385410300c402081020700c124004d0951080b42000b0400043c01c05d0f03402c3c02d174089902d050042c10080c0ea070f190030041c2e42040314003054031942e0108000200d07801030324000c4081407401c01d8030103c0c100c000d0900042440e0b01c84600d20f10ba408112881001801d4210401000369902d045840c0d5960f42c040b0340340e0301e003a80e03404103503030050008c04038003980300b0029a228560080c004212100e800e413600441441c01402c04e0760000d407900c54140103c0e03994001d46000386440f4510448051010009400c902182c4d04510f100382c01500e00108141e848400c0c0ba419145981c3c0e10030040007a5190051400c941e0705001e25282d402c020060416603004030203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 148613651 1250 148612401 148612427
    0xf120405071a0c06070e0a081f0c0c0c050405062205011508090601050d02040e0a0f020f040b060301051c051f05070504081009110a03081b03030402060a05070c03020907 74
    0x10718000c0b42c0003491828002c41510540d00ea104000003841c16200e40c0915034110000380c010080070b070710350640900f414048429a505540c0c2d40380f100119032102e101e9201c200d492032600d000f6500312503950f10445c400901c241481161a98003043c21039558a03110314281100135810005503110b0700d0100c028060034854000ca008170110039402c03250060ba4924840c04a041c06090140e0a1900308282038036442426a0801e6864481c9102c200d01000401010780c01444164072505140c0304004004c401801890b0040d41000317000305143e2035007800c1e44d041d1503088840182c19140c4c01d0a2500e0030320100c6028040d440b410a0410300003500c6c9102044480425000f44001c3d030710440103aa0a21480c03040750400e50000101c1d110985c4035600c00c81e54603108440328030001a03510002035103905590400d03148028000341d61000710903c91200607401d003850300030b0340c154540b5400058203801120110803c0c004000750b01d500300400010080c01442d801088401e090900b150002c0c6540583c80c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 148614901 1250 148613651 148613669
    0xc200c030d02010b0303190903081c110436051608070302120412020a0b07020d020106080109030827060f04060e0f03040614040503010204030809190e0c0f12040507 72
    0x40401c151040c0650460b82001400035071405011151081103500710110030b07820000180408400903010760001c120300d140d0b4031800000416540c000808580e10010307016101e100c2003100f080b0f18a800348003800c014894040c50003138400c0c40d0003000364807a42401d0b890708040c9444100303c00e1607050507207208800d0075a640c1d0146541c41c02000e4040b0311502484604016001000a0000744003003050030348114184162030100045a44107040c91200759590750140e089204207000440e42407103000c0040103003034000d02000070b050318054040c00002e0808000c2d105894a0000c14000c1403036140c2610301c108003115401d180c90211603920240c10340e411501c40e410012109510b050010f034489050ba0034101551034140707021700036141c0ca000d460a09146150030710000805550178400740c002107009401140d998a550810041c0c0340d030046202e125002c124032402e101c100e80c60347c0340070362010150ba85d05681c2c0c0303540c0d604030b0300b240160300c480c40e03a8280d4001000200701d404500e2500f1151819 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 148616151 1250 148614901 148614913
    0x3021507230304050d0609020a09270c0911130f06080f0609070e0109050d1a1819080904090318060207050f1c050609011a0d05030702040c200c03 64
    0x41491051210301e4900301c0903841403205200c0c0c1d140ca00c5615440300c0c400c420004081d5202e43c046506c030b900d294400c90b00e032aa0f42095035202403555071144104c5411424001180c80e60b0340d03541d60580c00c2c9020b0441c4880d51000154a00c01e4004115140180926040001c49566210301d140b003060314004c1e070f00040c0050b80800c80c0d202c00800c5d05e80c040c2c00014a6a60282e40b81c80040301d5140c40440f20a0402c504040c0020b100d40311507100280f500c5c0180d184014001e00e11114050500c40503201009210b550507a80002e87c2c8042901c9111804040c4050701504103803c01000b03a006220415030b00514042c909130401d500f2035071640080c10800d000c3c0290035990002661605c000d44240c54208454134521a040c0c034084802d18a800070079424004107070704039120185488401c0f00c911a42e40c0d500c0907403c07401d02458095892264080710030401203591550b0349512070041440003405240c54031400070303c19010b00b080d410000300302d400141421107040c80860351019442c011601074002c2d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 148617401 1250 148616151 148616183
    0x180103060b03210d0b061b070e0f0f19270203070e010501050406080405030c0a030215061c0b0a0b060d06060e0a0e06060a0c05010c030f0b0907020d0302090a03021507 73
    0x3014820520f03c10714070a460410400300e403548042c00c1c01c0300c0026441241042a06425507148003040f03c40c015101c0202605800d1180c00c0084110141400d20b071512002d041009581c55203000da41e102c0300451a040381212006034600107803030014054408000c02842d109106900004810035280c0200d08840c81942d07265000702c0c0a031400c1c0240c0340003039010481480513a0013840740316082072055084a14002040ca4401d0810280540c2100140c0000810382c00d0b0b80304501840c0d030000307811648410300c1d17882c00002c007441c1020f01c400100345070403240001e01040741c558400901404050039255881c17200c0c040000040c02c050103104007040c84041c9007d02c03420160325102c1612841145180d02d502c90303108004c01604000207c0301041422a01c00340003130000c0c01455502c0b13a00380c07004188012140486c074240c41d818601a030280203801c08001d28030341d0014424000b01c01c241001a510716203480402c0780e000c8150006500400500d501c00e2000501c1c80c0144031160241c0402051401c01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 148618651 1250 148617401 148617433
    0x50918010b0d0b093a12050708010f0902040609060f0507060905210c0c0103111c05010f0602010207020d030f230a110a12120f05040c060f0c0503030f06180103060b03 73
    0x3200c1000e807000e17218018900c62180303240b190900c0b8082400c100c410700004414000a0781c01c00c07201400015500001000311500a0249134080d20f149182942414104600100b17880b220342b180008001e8011162912680510f01300c841035908000c2c02c0c0031140c96400c0165440700081d441084081c0007591344502564140180e81070181250702911061420800440c0503290003013804d110107404100007140c031780500c0601c0b8003405c40316030081065803408a0142c28000c1a910000659004124039001a902d503440c400d072040d41418103a240c031081200c1101e005c0210004269108100c1450402c18100e0601810300c201055a80e00a11102c0710700680e01c8010841004106c00c65414280304182d000342800c40e00030494070f1001490910040420b001c4c0c0e04140c81c25184482883c2c1c080c80802e038080400c61044031203041440000a60303584541d580d1000500020045c115400440c15503600c1c0034440102803003c1c10004100d586906004000700740704456640b1a128200c414101060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 148619901 1250 148618651 148618693
    0x40305030a03090215041a0a1107090e011505060304020d05071214010b010903030c031101110a030b1f090311031504030801090b0d0c030305031902040b0a090e01050918010b0d0b09 79
    0xe602c2e5514082d001003501d07c50119000740403a2420300c1240f40690041071400c0082c4001460768403000300c2e03860340980000e400c49031a001480f40048624900380003a0301d46c1c0003141e8015505503040070700c1035024249213052001640281408280c00c8119005004a40340e20142d01c22001c0300030041c588a8800642e00c0008506c4010301040345130454001181c0200040401f1403000000400d9040c04401e84c000d0941c49802c4a0001c65902d0351085d00c58204041d18031034098401c0b45030a405420810003501100580c40004c01020341000c01d40784c0c0d91010b100c5800d4181076024079000500306443c003d0103030300c3c0c00d000c0d1443c45890402801c650380b501d9224276110f1a04035a011030000d0035a2021a81c60b80010401044102c421090f41a0500d0354030041c0014440120400e4a40c090844001d003c5ea13801d0744624541e07034244c4014001681d91043d81e075008030750030349000f0001550b92501c6000d00301b26074015600056980d034000c00c3c0b104c81e50f042480360090000b03640c54868030a1410600351 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 148621151 1250 148619901 148619909
    0x12240603070614070605040c1502070608011202011418120109021302030411131a041512031701080109060605030a031d01050d050108070806060303040b03070c0305040305030a0309021504 82
    0x2501c0300c4001c00090340500c18140030381d282e044481d0302e440303030b50340340c0800341d40090b14200d404520030401000032880d0002844540203262000c0c15800b4604003005180076018018a1118100881c840701103a00072944200b0740d40c2150403068494501044039640d40c6c0e02c0b402214042c0d0001d54110a403400180328001820341c0c010310f019844030200e1a030500070b4000800c100d901c801118a115400c0c0d82c2c0581414200c00c2164002c00c800c034201440e143c0600019402e540602e040612042e03010000c03640150a644404a50400c5000d9605044600d42c1100302d003001e07003503441d02c001b00310001e040d040811701600a010030300030682d0b02c8080c1903a40d4082000540040c114802d99803501e000011031000143d414500705040058030039250003159404c0c1d0003403003a03901c01c075402c028024050120603482402140a18101450083c0720304582c8002003a847c20040b121407004d040501a005890207140c06c0000c9a4484881081c007400411015100360300c6275840101541c80d05140600700d8080e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 148622401 1250 148621151 148621153
    0xe03070807030e130513020118030b0105060f12040c05030d1706040507031d0303040c08030405010206280e064002061917071d100c0212240603 63
    0x31400781e8070116162440410020742c050312503070465900751494011540100011024219540b52600c00580034840d81e400c00314034207908100800110b01410a842c1c11190103441d455600c100d031071080c03101413250b10840f05489002509002c10f105003110080c0654500380e04507503102003184011381c0e0800304500b5058408800500140c690301306500000d411180c07908000c2181406501411590707140f284521038254004400c000c28411b0503404e10008140e000040c4d8601402c00b00000d4641c00001e182c55100040141c1c8181d8643e154004076192002e0368400300f12111044048076240c403000d840ca0503a60340034003032050010024000d1610140c040854502c451594a000c00f42803200202040c1d038040814000c0e0000411944007004080300180d40300060880e0344019403401e80303409407414041044000f02d00c4034000761418035408111003100d0320b00344403070720340400c83d080c06111200940103800003d0801e680c41001660114200a405081c00417200024a03840090000c030b03101685 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 148623651 1250 148622401 148622407
    0x2011113050f0102070305010c03150e04030503040b070e03070f150f05040501030b0312030405070305061617180a030e0a05030c130207030c06141b0a020714030a05100204090e030708 80
    0x314a010b0709404a1840180143c606030355894403490f0071a00044d40810110782c85101070700598440741041c8000d42012403e03500c090400d0b460007411400000d100900c140c02000108080364001c82c01505c140c480182201d019686408040001d0038140c4a160660404e000340c02480c0f9000704a030300c0c24180c0582d0b41505051402c401140035042e080340e03542c0c040c05400071050401803808021449070f40604001c05489165117005072070070400414461500d0800301505840c1580a0b1300c0e00302d010f4000310a4000e680307481344c00303404181d117440c0180402c0c405c1c0c881000c10140c01103210542d0100c00c89a0403e401e070346105042e1151640121035500800c0351510311031407101a806029158060310301100410102d6841c801100d10001d43c007800c0c140d81c00100000300da40540200701c01c45d0b15004442c10005081d0000c0c1d41d6040500445200078502e00c04401e031528200900f141031a00b103421203400c0d4400c056058002c0d44035028004519040c04403281840034000122441d2551001c10940303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 148624901 1250 148623651 148623659
    0x5030d020c01031d060c0403020108012102060708161101020d0512160201091a04060b011b060b01031b20060403231606020d0608060106020a060b13061502011113 71
    0x184440a44549040c5400704d0405440004009440c440c042d00594603641e5406c600014013800d105174800003c44214114412000076030045e10091542d042c0c490319201e410f0340c42c00030340340d00817460a10085d0040140c0e02c4188003680240e00e20941003a002e0b1114181d00312030440340c41c403440300310355001c10250001c203040c4a000c0702c03020162010340c80000750144071f9a4488848404664401c0c1e064a0000c0600c0180309440c4a0315840c48001d0800c138940e44520708000c9809a1070501c058446540c5400a0049900940010380b8082c811001c030260385016000207400246912000580e50103410a010444600010400e015039095200c08040250490701144c8034040c2415113004240b09100401c140c110150001050ba80300714009629286504110811100298050902684032200400890f038012803500f805940041000c19514020303404580020029038151018914000c0001400c52021a6140090020f0390003440100150300d180900f5001c0c44580e08030341101800c0c104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 148626151 1250 148624901 148624907
    0xc020c0607020f1f02010f02090d081303080301150809010e1c0e090411010e01020a0c05010c11030a0308060108070806150a02010915021b060c0306040902060408010e0a0b0105030d020c01 82
    0x4150544003c04148500b5610800310b038810b0b46201040d03001d0141d8803050409913130280070328070300d041c032000007142008041400608880881c4802911042000814965403080500060095a00142080c2c1d076541c1d501e8258841c49026000500081c00c2c00000c00c5120030180560500c09501d48000c0c5602c0008100c0308c8a0a4014112034051103100421029a51541c252403445a4080e0007028090054030002609045000d00c5450440d000920560300040c0003040039002e88100303203840d80c060062881c0c81c1004520320b03d0f000354144a00e14810b420190700804d0103105007001e0762078079030546400c44280c85501c401c4d10031950003904140c821041a411202808080125200120390400340e81c4456107400e03600b2a00c0c2041030340024007c4500f0603079003860003030040c031500113000340e10300b613040c2400a0102600940c4500c0d2500e400c8002d40d6102e101352401b40003c14001c0001981c545207207552009003000844601c2441b20000a0918002c600c401003d1216000781032a080d41074011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 148627401 1250 148626151 148626157
    0xd0f0c0c03082b0b0a0815070e1516050706050f0708032d1518010513060b0d020a0e041b1202041d090f0712030509030c040f0902130c020c06 62
    0x21603030040e0382915035402414a11012601c0340c40c25000581d5141450a1050f5030700203400c2902d081c4e00c49410b04104c220180941a882a51032a061020000b480c000038414419a044d2b554602c00219910b516958551201d224880c07045045a2100c0d0351a0b0301076650b401b607135140c10451402406002c010031a11002198807480081aa541140034001a609900c0c00200c100c1d250b2402d1004010350001122a030380c4040c1c0089900c0c220004640007003403400e0405015244c0030340c42c1d02d07801126429a58001c40c01400402c2d10264a40340c030a0410002900401c4407000020640000a10241032a108000407030140c031a14548a03001007030700351254500500700c0d060640c1d0800001860504070503030400740d400d40c4c0d00c5403c1c0c40d040903682640380c18068100c0380480e421440040050718003642042107041d074907043c115120129800002d040c22558011141c000f410710843e00f03440321041c0e02450046108031207aa050750340311100c3e00f04585040304c030900076074400c04030003d40345400405 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 148628651 1250 148627401 148627417
    0xf15020c0604180603021507050d0305090c040e030c01020a0f080714070b070c06020c01060812030f010e040c0312030912110705040b0402040f0914090f0a080322050d0f0c0c0308 78
    0x1010130f10703980c1c9074041080c0c0710505d00b0043c81c180003c00d0610801070280141c510080c4207103018400c40c101180559260b0034007112a9120700c1c0da60310300405200301401039545001c0c004008548070003034070401030f041c0c654108c0254000b40318100040c2c1901e0140c820301c829400182151402c01805540d40908000c1c00341203d024031510306d03140c10000303595000400007240d2090021940500e0000c08038035120780100031841c40081801045503018040300d030380d4111aa40e25211701a5141c60a0001c060b0721150405810f010b440c2c0a85101c0580580014104912540308001400085401182c02d4a43c3d04a2542c403900a020104074502e0160010002280b00820061a155440c00c024541c005580d10401c4000c0d2a8807640307402e08201d403889a4421016409409050750000c98180c44091404009054000c04400b003421526543c3d00c0f58071002e441314000d2039050841c00c10310781d540410004840001d04207100740d02e04c0e604c5500c000d400706500650b41400c050550b40e600841d900b0080c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 148629901 1250 148628651 148628699
    0x9020340170d0c0210111602010c080d021207110102070b0105130f0905060604050f010303091203030e0109030c050d0311030a11160305040807210b06030c0a0f15020c0604 75
    0x451440000003503c1608880c8200e6001804942608840d100a55441d501908907030281400788a8100e00d11034200e60666609182420b0000e031585070000c80c034000c20300440c00d0a4404900c114040140c503104500464090b00c1d021040803140c2c44042c280e104807400148110f0201004001c2801e0500c0c0003403074548909008034014681015090440b2808082521980e01c020144452800d040c400c554009004000c03941096046840281c8400e54600c510120310300030000460506100354040011140b000f0000e001060b80703400c0c020503a184001042d2130a00401121401c0b40780684101c08041e95403100503404d44e41d40105c3c0c000101040f14408001040c00c20088032550b0380780c40d20b800c5861080d25030685940c1050110381c80c10200e50008aa20786c03a8400c2c255059070300c400c0050110b5130160900141c1ea44603008030f818070352001d41458000d4600d00c0c001c00c900c01806d00407015210100d0401c920480402401c0380d403214030756156500a0002c01c0144010030045850742441084e800c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 148631151 1250 148629901 148629907
    0xc110310020a05040e0105010c0203121c0c0804020906030c0d0809150c030c070501020105070e040e0705041b080a0c090e0903040e07030c180509060f01090902034017 73
    0x6690360080e81c1c440c40703062000400c00201840036407816103100f0b001d0b000070b1800c40c00ea008240e0100350f603259126003024091f240864032043c00a11114071401e4509203070400d12011694410280220500b95412441101d0900000f611400c000514001401000300000283d403001c1e10381401036030200b11043d400080685102400381442c0f0010f21040925000865403590a50344090803e0b03a150019411a41002c041c440c40300d42c00f1a1845800d0021a000600395081d40c07003051030245642d000c41e0f00282885031120402c1c150f40465100d030400c07910f0307105aa980340205001100e0b5a0002640800c482c8072007170160b2801c841085500c40c03c0a01124074107038a4070006048200d0403116000000d448090507483c69070700c4040074a00308260b910031040c5070b0800300095a200c500420042c050702040c2024080c80e071142510000600c01c262007107540b0700b80010007920040c0503a020b500403402180d1020805400042e1030100d1b001828406916401c0343e40d80c0d10390903010010a14402d40040c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 148632401 1250 148631151 148631173
    0x111002090112021204030f030507050f090303070204150914010e010e06010908060c040323100f060b040306200a020a0602070201030b1216060f120b0409080301030f060f05070c1103 79
    0x151000b4001c135921001c1000c0d0344c1c03502d0b24008013441c030310b29400c2080604040a002066402000b41c1d20101411340d0131a855550790404686580501040a5880b03802d08000b07102c09100b5480380c90980f80c5901d000d0003807046070506840003d80c00e10484c1e00c20500c810040000021522080d1740000051501040d001e5648413054900502030354840d1310301c0b500080030000c00003844051203034030388540c1c45481000b16280110303171900300400c03440310040d03224040c41001e0b1525a102a014040041c0e050361501e450b03040c00b5005000c02035019810310100000902e900b0000800d0342d0b4000400da00a000d01c4406588105c065048504120b0615807240e02500b040c3d6210200748510310001d400a00b481ba10381d42503604a004a507000c4002c0c810419910401150301c0810452040b545d60b130003050325540711011400900000c280508000740200010040105d40d10b000b500d4140251824840544008010012504203483e948046016064244001440c80260f0800c41e030700107043d58414000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 148633651 1250 148632401 148632437
    0x8150c0c03070c0e060109030506130203010e01111c020306090c0c070b03010603050f010e010f03020607050c040507110d020712060903030915060501180305030a12020c0d17071110020901 82
    0x100a1046500074007441c02401300c03140d2403181950060f403d1a20a00540c0f0b15120240c452501805000022107440382646c19500c0942291a40b0021000200031402e20240d030f44205130031007550000010041311016550760030b54021780c2d018000080c04400a40c6070380c0000031440e4031110702c84c401c41c01202400601690490090b40c02803a0986001c00d11380b82c41881c602c00c446050300025640016080140290021400450103482d0305480e26991211241417480c94807151244640c0d0042c20f04041001940d4045503c60281e501c1c0000c130f901490718008180c0e1110f40d070b80100184030303002d00c60400215455401c004c07403e0b0301078203000845090544801c2c419070b00c4a83e00d080740940700c64041107996070000c2441840c51080c050140c1c150708699410b83c8038820010300004110000e00a4071588291340d04a480c07440e0500121400781e140ea078005005490400c01c8040b00c1c0c1c2c141000202c4040c080d441d003c0c50840b40901a001d80006510000029005107489078100700f0500c4100f101594 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 148634901 1250 148633651 148633657
    0xa0503190e060112020108060a03030e04020715061e150c0f150606200105010b0304230304080709060905090c041e05130203060c0a020706030b0f061804050a0608150c0c03 75
    0x20072100301d50040c060b03170001621000d00901828000ca00031281000030950040500c0c81d0103204550240c2c0d54005814203212501d680304040c841a03182141c0040c1a410185100080c502c096007010111907840c4c125a0500f030080c0d00420114006882d02e800243d2200075116a141c0304143e40e2951f640c0b04c1c02010115100c40d0450008181c0119000000000c198200702d001c0b10780390700903c959810030382284c41e00d00001e88020f007422045c44e500b80121598200320154503c0c443c0c12a503e0710fa584522070740c2c0303417624440c82c0c1c030092a09001017184201d81c0a200d2040140e600100840c0c0b41250520008040c105030b20422a4110001e802814615000c0d0f24010481d2042454009030300e80100344c14564003414400c0e0301c020410440881680110700d0004550b203a080004c4d68038207007004038603007401d40244150f0000740055001c0080d600c003000341460701425541040b0310368440ba00101112075901030403a150317100e11300701c400050000880c0e6601c216030301503c2c0c1c1000310101c070861442d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 148636151 1250 148634901 148634909
    0x8012a12290301060503010e03090d05010e1203040c0e0105010f120209060a0c110301060e0a050702100e0a030809030301230f0a0303050d0b01050906030406020a410a0503190e0601 79
    0x15035140344100042c50b0900800e4045c00044008118101615409580d00e01c114070100c0d00501c18000000c06205003036208009003003044040e0744d40b45809040080c06640100d40444c3c450400d6840401c6180320031040b54140c45041e164562500c00c61b400c1602c0300400e10041101c1c035602080008091344600b006040c07118100d031a8000345800a20b4403440f8500c0c00352140740a60301d07014040005041429090390410222000015a600c0d10300080b0300700b03600309040401050a20f0f241c1e5260303260003e18143d03005d0090742c81c1803290f2516100240c40f8402807207103203913078404440d183c0a2562005203001400e42c00416400c02c0f00951804942c111405900c254041040494489601c2d90380d03001da01c07000d0381f00f4a8440e1820b500e2034000350341c0c3e01003c0e1010309030682c0450441c071098020448041c1550325580c42c54840c00d001c0f083e2007406030000c03000e603802d1910620030384580d00f1034105840420040d902c6803401d42c1c3e242c0c040da22158903005072481006441e00d0340303048c0340c032410720896001e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 148637401 1250 148636151 148636211
    0xb0a050415050a0b09130209090117010e061305060a1406190e0c1201060503040302030a14070f060501050a06050309070302011b080a080f1f090b04020c03030a0608012a12 75
    0x11782d40d000c104419a82107202c41400c06004104040496403070700036403410740d080c00e00c0087e0320038150001c0500502d0f90403c260320b51300c01d0105000c503500c0059440a13410703200301c04035104c0f07950300b20a01d02580d10070a09140f1341c0754241c01080851030001c100181b00804400b44c0d0022680d02d48140341607c0702034841940d44000080c411004155000945005d03041380e041142c55802d140d60000d549200c0d000b044803c201c0142402e65582080b081210501c98024641c075450f40e9982c104480100700c284500c40c481c0e840c425000070b00c280a8000c3d203103d10f1420b00035100c110b00d140c006640800d2940d403850815424114000005500c101c068010190703107580313803007507480d008030343c0c08039a800582002c00030485654070b5101607001004403000d803000c0520200b10340e000709001c80c2c0a0301603024035040340d01000c000c0021021072a8424001c480001009100f080c080c0d8101402d00c0d075800c900404c050100e01e0fa080401405003500c244008120240000d55191078500700d0500c1e00310300543c0e164 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 148638651 1250 148637401 148637407
    0x30c091a0903031809060d0f0b0727080f0a0c1412060703020c011503150e010f060e060f041401060c021f030507081b0d090203100e0304180b0a050415050a0b 69
    0x1389060100c2003d90100050b1040e440940c0e881e1506031080203001c0c00241010340b0f18001814681c070030310490080131a0403000340110354030201e01d48800303400c0e17029a0074244500401c02c030703102d4000034410f80d106410000c4284c0140c108104401990040282140c00a06081d2180411381080202610815165070700581380d020a0201c1401e581c550340b2003d040d2507040f8024000710301c3d441c0d90000c02e480480000034280b8151104180504010704003120749078540700c000100346291050701c030300c40d45081320800000d503c1e0104020460761a0318510320482d140d01e005000060003054400001ca0009181401103031605265403c483d01407144d07000001d07203400500c19031329080302c2d07245c0d003210125000c030881b0300c102c0c4403840c024000c01d00e0318055251101080819510b060003114808070403000c0501c210428480d1040d83c0e0360041c0b14513140000070104c0710843d0300091051441c843d0b030042003102c40603d040e040101811350580204c0c01154060300000b0340340c1e16120f4100080907042c2829032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 148639901 1250 148638651 148638697
    0x303040309030c150f030e0a0206210603010e1c0306270b0108250507060c02070609060504050604060806040b090403020c010e0904020d02060310030501020307090f06030c091a090303 80
    0x41d00110340d92201560795080c24401401c207030040c05d03600c0408994603000450900b084080c6203001040c0714003a41081300003c403202522040c40c2036501c1d0300c44a041ca07801e0368484900f450708175818481f41c0a0b060304003994462155200d42851b58881e0854a4003141390b68540c41c0c07003d12017403c50300c550448a2404003d14900703200d4021143d142000f420820103d28202099200b00c0300b600c0302e10501c18500310a18140305d8000c0e000e030384402e508043d00700104910b020303001c1c0d56450300f40100000302c0c540020004180d8403800845003174420140c8030302e0800f898150240c1e0352000113480aa401911003400768600d4a81c040180c0c811402035000f0300341c0d0303c0c1c4ac070005041071f02c8410b82c42d0b004402400030031000da12001000382c2d00c158181d034001d40c2c0781e036412080320301400f0681000308154000418407580944c000c00190a0320078503005416416680e42c0184d04032544020301e40b006c2085200d0800c0010030140f60205040c1500b05014541040c00f0006030840e0301551468450300c01e8004405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 148641151 1250 148639901 148639913
    0xd020c1806130e0a1b051504030309140402070609061407091202091b04080703050c0a21080c03040914010f050918010906051302010201050901060f03080714030304030903 75
    0x4040404503812003242004030104081d1440c1c00c0821115640342c02c01040b51000030840d41d1240d07a00a400d2102130000b0030016818000325105041c400c000e01891100015030050480301105d6040d160404900d140c181c0e210100c089440c503041c2e007c0d5090111401140ca58000c2c1c510842c41148000f4074500300d08401c031240e1801605041c10843c0c04181802100c1454505900984d01220001d1607503036150802c0e03c11080f00004203c0210003c600080c0c05400018541c00342e0b4410019100152581c0c414040c03251a07034840e081c44c1451a10b54045901e2180c0065140725000301021450007102c40b0b00189541c0c406d52081036000e40e80c0c0c2c1c44d40514100c1045960150a00c6030105c59070700d140c4400206080400740020048075036040c411002c88509500540520358005424846490184600a000c1c1c100c030310b059001d07508090024007044e0043c410a026030784509040901030f0b0450321007440a0b005407000700c46400c901c0464800440d81040a9071045110346c2d00c5550721403d40c5050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 148642401 1250 148641151 148641169
    0x230c0708010219081b04080703030801051503040f050c062209020a09031205250506070206010f0605090102010f020d290f041e0c0806040b03061005010309140d020c 72
    0x306105901c10300011240c0f002028072005500a507140c10101c6444282c3c200000050050301001e6072400090005200c1e1f101040380400c481c0244c0b6a801140c1e81c40c1c06101c1c02c004c5e1441c0300e4848100c2040000c0000e908503088540c1c05000340704a401c3c1014040101c0c0440d800080001150516021070922858034520300d00d01920380880b055080011201028002c0340d0705001c018491030421800b504454405d0090b601c104542e84030900141ca4582070305c2e41c40842409098842d405400005185075000044c081d0403518041c60f8070384401e142c820111010b0304035114440c1155266803c1c000184128000307000940000785001401a4405030040c00007002c600405101079603450300d0f240250f46103514184a03403002c0d100810b890070b0000380031116013201912501c1d4185403444d40b1080070f0b40211030510031902982d0420120005e201010740e155001c617010205805841c0c810b2101d54483d40010455611400c0102a03030b002503082c40d81464100c0c2c50364001039018071040d104503e06241c00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 148643651 1250 148642401 148642409
    0x60c0a0506040b220b01030b0c0c0d050403060c080f0c030a020909090c0f0924040b090f0105010e040e03030a0c0201060312050c0106061b02041d0d0e04050a14040f0201230c07 77
    0x3041280415aa44059000c5c051001820f9400da0f80000f030000789841e0f08072400d0342222410380c4c0b9135607183c01d0081c0c5103400c50301090700c5080c540105e03228524050302c0c095002d507a0002405281e5559000c000317015a05c010414110366400b0300c020012502e4800403680910340d910040e2900c0c1034140d050220f040300b503002d80d5120300d0b2810144046842e010f03d060b9024480f0300845241400d130400420064140e00d400b564214140404025620090340000c1e8181d40d002d80c3c4059102014a0070041a00d4008c2031140e0f50360401c01c082a0031100e540d1081355000d480f800046034036a501e1b21601d0710400521140e101048000500010004083c800c4c1005030079a420b203000118681408010f41c2e440d101030080c0240c0d9078000d0b40300c4120302c0345c40e10500ca0b088981141c00c51000c812000f0000c41501d50003900413410140842d02580503401151b00070904c00e02e4918055655495220355040c81040c10781c14020310316845800700560303103900f9080060340750b40242c2d100c034812405480c00c905030380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 148644901 1250 148643651 148643701
    0x1b17010c031104061412010b030a0b0604080309040203040c0f030c0303020d022b02070e010909020111070305060c0d0908040e0405100c091223010e150402060702060c0a0506040b 78
    0x1ca0311916201440943c0c068034428070b030803000e441c08032822581ca8030416100c030034a690258000501e0b8501030300110711070742901605115410500301071000074001c074010907104c1d8109110015480c14070b90b0103168000e002e070410110040da1421543c80c0b181c1c0c603401c2600c9101e049241031003030640412009040c2003681c4002c041c040801c49038220a802c80e84404141010b0000ca4010014400c11480000e4460b004104100307503541c1d40104000c040c1488100e0116918114041003490003007040e10850350800c0103040250f81d401e11070b90580c0c0c81191001059907450340d01d03030302092840c3c0260010f0001181209010708140c10414940442512120040d508011403003201540c03284200b4201e508060b074003411031520345002980003804800e00031821890040540c92908150848280c8080b0042a0340c0135400d0a00518601e900803074003e500316034104441030040c04d2480c001c0940c200030754165518500c407560342c5420034009440c240c44d0922202c0c10302c6000c96810080071051301d9903030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 148646151 1250 148644901 148644911
    0x1f0c14030108030702010f11010606111e060106050a09080d0801090f05070c02040506030312190e0d02030913321e0c0706090b01030303090b06090c070f1b17010c03 72
    0x35070415a0b80c460180021b0401c60300740ba4807000b841c0a40e003401f010080e60130081c880c844d1610401440c0c04030801c4009c203180b007464111000f0401e802000c0e803425401034003401281c6c1c00c201003940c1c1617100d210140100701400600094100c0240183d044680b55a907030102d241d450302800c10252102506000322032464082407040f40c0d038004512001480c1d059802003200c1d61100700090440c042c05028212212b030103020400c41c1d014003400b0320b20120318500108444100c800001e41c2c0c901c001941c2c003001da1310800c00030805190070840d511030b81c140358030301142207071390000e600004821200d150520003022603203000c8807500c005040d59000c0141c2203881d11107c0500d207001d0340400c000d4100000340200003100d1007800320980103042556000fa0072142196504e1a0003402040c0000f415030700c846206010400516204c6855401003840f4003819081c09221340b2041c02940300030b40308841d0010942860030640d4401e0300c0d100300030f0074416209441d141105e50380c80e081d16201804001014506 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 148647401 1250 148646151 148646159
    0x30301060822030c0201110102070605090f01020a021f06170303060102070b0a050d09050102040305030304081c061206020c010608010e01060501110102070c03080f07170d0c0806060a0e031f0c140301 87
    0x54030000802c80d8151920a103d43e8007800140c40c5440021507014040d400025244207001040c2c0025000e00c0d0a4001c50741c4000c02038050341e0803400f82154180c0140c1240581c0100c181c2d580000c0441080d0541e00083c066a51302e20000c145449112071404580000c810040300e50780502055009000d001443d614002170048001d28512a10080c226255507407681a81440803d606a8003e560b10600b103030750b80c2c100ba06103800700d60000080d05180c21240b460441000c80e44e0f00640c01196001d06010310350402d00d65401d0301a4214409050300c565031280d0019941d2024000c9180211032040000b42c1141400c00040c0140c0c3d44010b4181944c0c0100492000981d04e60503030801c82c1c0d0000e4100341c80321000c1d807410030184241c01d8081c000b08030f820103008910400400424802001c0b040c2002141e80710501074500360b03002c8844903803084060003101010f5008440f1100b245d0001815600c8040807003070400d40010b03c003504a6002560345e010f2124140d080142e00380c41d901031182050541d858 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 148648651 1250 148647401 148647451
    0x3170f070f03090f0812011701110702011b0c0f08010e01060503031b03071203020301050a090c1e0306032907021209060a030b0d0501050a050a0c02070302040c050c0f0303010608 78
    0x11420740c80406664010b03000034403010b85000c07441107a101c000b1903070780d09000750380b280c502d0320a02501e28406122603503010055814401d4158030481400460308100564005540302098142400e240000b0f2500340e02c0010722940b082c0028116a10f92102000d091101ea64215500e01805d208a68500b82d02801a0391f40082030b11480200e0301c405c0030038004142552425806074020080100034a160983d07000e0390181c000d94140ca030160b0f41a11190b40e2281420140c510000d520b41c0407505a0609480703003601e410f402401c1103101c2c240414003d40c0c0750788246010030903903520760000070300885421660000500442d0001c540b40b0081c80f020140200c00c001da880f40611641c8a00000600c1e14000e40c02a082100e0300c04004103801326111040c240b0601a080840d40f4107015132910300040c030189500c0c415520071402d00c0d4010b18044e400d43d0300384401400d0818500080c00703070500c0f21507001035082160020480d580c070003554903075240000203050480c01404511440c104401c1c50b80d01c03241 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 148649901 1250 148648651 148648667
    0x102270105070f0219080d0e01020d09051809011d1005090f070b0c15010312080609100515090d0309060e01020613260a03062606040b040311060403170f07 68
    0x80c0444104516180c003150900b0b44170340f0340d0b0018501e8041c1f18604024a1f07000030042c00e169400380c080c1c800c2d0722a9020304880203042ca0145c242e01121155404050281129500b90700038000f0000180c1e100e40c0941c3c07000608030310884090264850030403501c00000601238141c100d10b0420042c5451604900055240c1415000780012848049468400d003101086001145003101c103082d44956180e00b055000001e017000c9800114403410003160403400c2070f1240900c14030b03d4500140b1964100000c100c1a03035040140401084400c1c0001074440c0c0c0d5010264551910944600d0042d80c94010007030f0003082c1b0403850070b055400580c200080d026420440608050340403070404c3c481907403010500c1440000508075004820042400201e00c3e070503510540954002d1252541c0d00c40c4030600350032015070716003480600342d041000414000b5109502542d0418400c0c10001c081d4401c00c440380b8684003080700c3c10b50000b401e0b0303d5142e103a240d0062900790800754541d20750030381c0d01d0b094002503e100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 148651151 1250 148649901 148649903
    0x160c0b0306030d1209020d0804080615030c0d0201180e06130905060a2a091e08070b07170711010906020303072003070602030405030307080115081b0c0102270105070f 73
    0x180711303814030100741c25842020303100d6004109552103003203410300039000d410901900503103101d0440410400c290794407034403a82140040050048071144010f000c148108554100c3c10300110301444501ca85d1402c1000000c1c01d42c040180c10300307103004000c11149005580c25104d05a10341400750000c600302190690740008101b801180345400c044920ba0911005064540c80d94a5034101019031644134048808481083c00500d003d00380e0b03016004400c000301d01c07603420359a218103002c00c0003d10310340291120034000d5907000e4100c40702d1494200701e64060841102c002c0e00d2402c241c030856070003006c00340140c02984010350461810035009060124000301b103a00d040540000801d65940800440f08059800602551603052070f20b041c1340e8940055035000c003c42c103980000f159044088207004056056036071015040e846000d64000111000401c00790581e0301040040740e1b9500900040411113002d102d0022a034035140c41039001000042c600a04001040002e20080744140090201031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 148652401 1250 148651151 148651157
    0x3120309150e06090705100c0b0714070602090301060b03130f0507150905030d020a150e030702040216060b15070b130506180606010804030f05090a0b160c0b0306030d 73
    0x1401050815024014050819070707140741c2409660300740d500c004100113004002d0441200d240c0da46902c00c1010310055020500001b484048080020070000403613143c004006084c0303901d484031400780c44031660740500015520140c0010b1044803609091003840018001035034103604500301300420345980e0150359800ba052030905e1142d081481402d2103990003d1a1060141c20004425040074080d00210f205040c07190082c42254040300d400480d185c045a40d0044500e2900124061000b00414408041200318403007404944016100c40c8010035107003030700c0d09406040400528214003501c070a005a00d000714030b8030f80480c0c4490101030079102c03a036074441115405544d800c0d6a1a000f0241d030359020308544102001d0003000341e589081004802c10b06810789006542e00300c010340d0030290964000b0b00190716070a01c400d440b40b14202034218503600505550400d41c2d00d031002d08075508954042402404440b0303a600030000c1c03d000798802021450820340c21882e2450029031690b5100f400c40c028 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 148653651 1250 148652401 148652411
    0x10f0608160c140303180705040e032218020c0c0a031509030311070c0608090309030a030305041109090c030709111911060f160c0210051b06011202040c0801031203 72
    0x4000f00400d14000c07011180d01102d407245030030300110310b03110418121003004c2d02542201080f107041c540110516526080021072401c0e00c4031605007049201404150b518482011000c203641c0190903041c800350380d0303031000541c07074000c41c80c039090504000c844581e1107a1074600d405c00001d41c0841258280d4400c16000040d2040b06080640c007401010109100c1240c0004000040242014164050365a01d99a0b552990380d0161074980c0c91058100c0c255041d4820441200001d1007034001c650302034800d20200303841520042c0416480a0203540f24801c940213000074292900702080305100038030320b0710030a000707100101031504820320030315032640001403001450816890007540c2c0c0b901c020741d15100b120b04910b00400d012810700b00585190320617900d0703240c030f4011080c444c0324034485480e0010180c050204d00c040059445600c030504484445007160034012070038000388021402402904c0300446003005a1041000702c6807101c12540510180d980140f02144d0302454080040c41c0310700700094 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 148654901 1250 148653651 148653653
    0x21008070c080c12130305070609030807081606020c010c020105160815010c080412020f01091d0711030705010605030c03030307050328020703020a0209060f010c03050d060504090803010f0608160c 86
    0x410140c0c1410103a0780103a000501e00b0f613111712420000b084034041c60945100c0c540b2654121514021072101601806043c410140400d0401c0e00420400c1c0c07a00d01c0402280c00103543c1c00301660862101c848260b5500c40d1109032845d02802201e41c081568500c10490420300e80c4094012480601100b407502d000d8820305030264080c40340805003d80040032640c803682d6450300d2040306281d01c0422800390111075450362040d4000c00040c0c0c1600c01d41404c020030380002e45218540a240141460108016605070307c0d0f00410920050041600030b0001049650030300007030515200c80b031481d86019510400401014036400816260804c039170b0140d8024542c485a0081290f00300c10910604042c0f00155000800d90002021020030388252550420b558981c010040394601e4500c0c44c0e07000c5016041407a00083c840c2c0003c01204000c040300284450f20b030004102100e896003001c4400f600000010f02203000040360801c01070600389400c4c0ca2901e000c1080701c0300810400c01c03075030600a41c0d40b0014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 148656151 1250 148654901 148654903
    0x906010516021c0b0916060903080a020a020604090608060603060610080702030708120106080603011a04020f0412030c0b090a02010e060f07210e0f0303091207030807030804021008070c080c 83
    0x1c0310500d802d00d140e0003c20142c148400c203a08243e940b40142d20485032184100d0440a1403901150000e0300c030b8240c803501d1906c451111754030081d100e1307007180100910400140d0f9050058805040500c500052090805c03219503e001e002400451081c0e11110030082c003551100c0c480c00d04d688403403802c00d6140c2c0351907401703174654007540d03400030509003022501d401045129142c4a048540d140e498803402c0d241c150a1600f00d420b40c9900c143e181d002c08680c2c0c0d0040c1441c2d0010555442c03c41e11840c07506030389031400040b9040c056421000103035040707400c45c28030500214503600041d41c03401400704900198006040c041801240c540a1000410140880800300d41a81c6c0c1e8182c02240c1064250a00304001c00c0301002c030050a0702042d60503860310b085060450524a4040d0007800952410a0b0305041010340d151150003d02c040c468020080001001900a00320040c841d440c3d03103031a42000c0c8100126590744a1040c0d00b00203510081002e9144c1c441c40002403141c000040960720b11303180040d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 148657401 1250 148656151 148656169
    0x1060b041412031e0901091e06030e030904060b1e031315090605070c15060f050d050c03030c01020904110c0a03111c080609012111030a0b0f0a0b090601051602 70
    0x10424943e022004c03040101c42c100020449540240e1b5801d40317464640209800c0030001e2a8100e030307003030840d48052080c6802070380890103611100c8101da0521501d080000c050740c40a800c5a40706803804542541030a03064a86004441b40d4021442c0c15454042040440242103410207000b403c511522448000f0590b480b4003007258001000340030600e401c0101810007800031804645425520480d605001898440c080039a18170003c01440c645c54401006950301c0210700c00c1e00c144c054030b1140c809a9508100070009040000000750311001130504200485143d050102d03002034041064500861012a20805855040c03c04000c0c01e80300101d40e600e491240b00720400316107129802c01420075040344a86200d180708131490461a070700ea114440071890300000c8140c600c5805003142c8009a40300318070182c1742c9406021640004070079100d800044c2d0041d0760070059990680144801c608440c0540f0070b00d5241680c28034000c1c10900c00080491092105400300b00c0080ca8846007103645000403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 148658651 1250 148657401 148657417
    0x7080624180a121e0c141809070905040812010e010e010936060f060e090d0903081c050a05090c010201090519020a080102030a1e0605030c040c0e09160201060b04141203 74
    0x30400c60350740790700b4600c440045007106e252282c49a1400411b9011000f14a18480c03851480600402c1d8034201403040504406007089070400001d018400c1545013032030b003443c02041c10b5800a000c5503d0100640c06101041c1c0094a105d42494500c0010360040900d00318400b6a000003128180115070613494400700c806801020b080c140815400420040d41001041e1750400b5440c4440340c0701e01c10344542d1401c84041c1c220210300d0300442000421658030160401070a0881c05507a03400b800b060000c03c940d42210b40c2c00030b1581d12424000800c0e020020f210000d5000e0008001e04582034036290303940c217400c4201c040d000b201a694481151100ba0118000f041d010000750740b0303800c1403071b004400341c210307902c00c0651115038001c0c0e00e1441d0340c2c50040e0000c50704040c0190102c00c80c00c400b0b110280840b48440c100388201044500c500b52030b142941881201c0c51400c0da42c0034042c1420083c00d55480b98022030341e01e1801d100034440c040b11040c041c00c03400e80032075820011014a1806600354054566 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 148659901 1250 148658651 148658663
    0x30f0b2505071205130f080d110c0f01021c0c11060c100f0f09150513080a08151801031713150c0f0c0e0c0a0807080624180a121e 57
    0x40080e01c444000941c0091f074075100207940051180e1a001c4036980b0040300b20700c81941c003009034443e46040c101580d642c09841841611511184001d03801010300c503a00404000079000c0a5820a01030805580e449a0000302c4410b450f081d101442d099503240c1e8084000366282d5103481281a03a0360540c02014440300c203040130b01410b401804c1c402806041110b510078a107082c03100041c0700310740080e4440509603020203080d00700031001400312440103009007030108000032002d0000c030710754610306807045003114101040010360543c0351500704584540001103c041d824410000b0954002815005541c1103044146419201e902c04a500c81503015016091203008000f00041c448029118429038074100c0300340007944c460101282c050303c42c400e00f040000d2100c4000c01d45083c410b100207a0400c0b03000b4030441440e0f0420a107680103401904458501000004940812480584900c103584100f1211000600e01c2c0c06031541100c840c8020040044010780600c0c0e80b00c00d4a80003411035507070044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 148661151 1250 148659901 148659937
    0x105031605041a0405090109090218060604030204110702010f081005012303131b0b040303121b02010b0f030105040b040b0717070e030c030d1e09030f0b2505071205 72
    0x1d5107400060340203004041c0504c006c600049085041d40c000c4100c0d250f4080d0007a9245840f001e5400350810000e448682d03c41c104100010169139076015000248440008a5548951510014265002601c210070034026a40c1c00c0140404141d1094000c070341c001c2c200203080d1054015080074441240365203503035104010050000311075941000c045018440d070700340e01e000b01800c80b0031456504144913030b030000101040144001380c4070720000c0901600d13603c404580c0315811140c00324002ca03440c203030b040182e66030f030b9008456261807581d990440c3d405500800c443e042c1a2074002040e88000d0014110340d004401040c070039846016501d140310854041c04800b818003060080c60a8110032200c0e100b4480c414801071a0310300450140000c09864880709130078401340d0058807012140c5148a000c0c448d080354000007040c841d070100320340e041c0f20f0030345002146801005811100180c2d18180403030034510484c404010703000320894088a4000c030904040e070300d031071004580720701c00c891300154010040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 148662401 1250 148661151 148661189
    0x607020d150606020f010e0607051c0c0e190308040621060305060105100305060f1e06040f05040501080d0c0f1103030d0c0e0d020105120a150803030406110306010503160504 76
    0x755001c142a1410f030ba0a07030344024042c1c0405070030784030003642c000b94a80240d0b020a541034012002030071200070001010031150103d2004c01d0454940581c6800443c51003034030b0702d610b46000206269148081061a11110708545498846019a004c0c030000c0c8604246409000664520080d100b00c610010030320180f0388074070b8185e0703d03102c00384500344c01002c00310b4041d95480d0103802058444c04003d041c04403041b0380c46040100e240200901c212248a142ca0030301d41c5a00c1d420001e1020342000307154158006d00d0502480304071081680030f240190040307070030751544c0c42e801807a1400240c1c100440d01424109070902c2c40480d0520500c40d5890720001440b070b00e0075000c03600107084101541e1104030301d8070f00d40310034031060b001d2880c0001e00140c0100500c549500ba45040243c00c04101e103800100600751324030440740c2711540d0f00728001c0d603480030003003204015542c040c1c0045840c611f0b8081c0d0640c103002001929030700002e450b00141c035140007200e451540c860410365006100d02c04402c001c84407e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 148663651 1250 148662401 148662443
    0xd020a030227090c070506060d03030f02040f080f0606030706050d02040e09010903030c2a1403030c0d05060a2102131107020103062c0705040f14091e060607020d 71
    0x664290b02d4010189140080c418502d800c054910a94000c0301400700c940c7ea4004012421002c11811003d02d0380d06d0022840c004400d10240c4050401d14040c2c1d8000c5007442d0250780760200240340d61950354402e20421505840204200044880c181080c42d22490200c030000003900440e000762503500e1000d010440c040e01d054000f07411640c002d07101003000094800f001c0351a11021403e00250100e500d141e03c1c000e030340e0005496405400741e5261300400b19412801c9085510607200e402000e0800306243d25000e149100302d54100b50100c400c804914074000e03000b51100c0d00340f440e079880064140041c809544034030030301101e0031031144c20410025108040ac4513294118030803c1e070009190220105518a4034055034040c2851400410900c07081c1040901c050407000b84a074003000824440028040014a400c00c00f9000100100c03030b001c803550090040310700000780016440100310404142524281204d19000a000d554283d580e0355140042421580300540c001e210301c1008100c0313581500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 148664901 1250 148663651 148663717
    0x90d060917250203030319020c1b01090602011803050a020a0506040818010c0206090613080f011a0904020d0b090114040501020408010c2607300f0608030d020a0302 72
    0x10710b220103181e80c2460480500241952000c0094140d4401c00108010044002e81e203d140400c80c1000340c0713409042d412079030500d900c00110443d0b10641220181d02c96820040f000098415440204100340c00c02404042078480468042c041c05000100240c110b80300340001006560002c08445042c107003031a025800768807141e8150f089a059400340c880544c440c259004200340c0040145061610a0042281e1944103074140b5480c00290b04002440c00d00611203802007070700a10000405901907102e8580c50b503980c05c2801d220309400010440103956182c103042005800c180ca0007a95540d01c084117004003000c46940c1d40ca0851001000100041500104141c540d008000d0003170400300c150503196104200c801803020801c0b03006002503516020300a82d41700f411894501c80400c498045c02141032800d6101c40c0c20426142c0301071003c44034031301601091200c100d034104502840d0400c403c0d101c0c01210903c0115540004400038458884d806440102025000c1010511000c10000700e17940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 148666151 1250 148664901 148664917
    0x1060e18180c060a0e04020906090a120201080112120f050d0905031b01090c140402040515030901060b0f0a0813120503070f090e01050d0203151503060a0c0203090d060917 75
    0x3110307034003030a91241020400c1c0d900c00c1c43c0517100c4031321450740541007101a420100005801220034403101c450313075444402031802048034050130190500790740001010084160080c0c402043c03144c0107000001c4a91032a00388960b0346240810640d544a01c0c00ca4061141000741c0c0701850130b06060740c042c010044010700c0381c4141400c0c5918402c0441076450b003600c4160300f01500c0c5080100040090b5102c40400c8045150002d10041c03805131284000344101c40d40300010070303a1420200c10040c00c04003d226120290203a103407004d051a01503a4030f00e503070344640c2071828100704209000c144644910f54442c40030590040460807131415001c0010160340044a0901c0040c50f0007410948580c010000002036503401c20030408103070b0a28040c04402099450101d0709807190010102003811444001802241118820f08460b46807104061030841c2c00b03440c100035507180610314190282c0020880b4558141550800ca0b10032032802d001e0000c2c81c81217405407184200b200e01002c0d140c0c3d0786e0b00400c623403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 148667401 1250 148666151 148666153
    0xd05010e10060507050309030d09080c0915010309050c15030403140903030706050405100504080a1103090306010e09120c070f080129060408030d05160804030801060e1818 75
    0x640c0c0e85010510048405640c1100c008400c4101405001c2c841e100801c00b9a0160f002c880c034016801c00400e180007445041140011410300c81031001c00d82c10b000559890108030340f03850b81402d008101001c1092031121090505544035402c03800c000003400f82601c0490010900d1a0070340001c01981c010380c0c41110110000388065800c0100c3e0f00d050415a021a4000340040d4203000b0940d4407600100000340c01514240709801d4036807141c7c00540226071103070b8469000580c0b140b62a40014003012008041c4110b1900244850344c03030303074400246581c11588242c00294180d00e80c0c0351444e040440a03000711a8106001030391040d0081c001a22100725807614400c0250302c0d136100c02803404c03103507209645031440703800154005d2000489681340c40f48410060800340f4080e983c0c100545140c1c081d50741030b040e00352900100b0a602c400d88641a030540c02ca070030a252280341035900209151414010760040c419091080d540b20744400d80c9106800446424034501414040310f0058009000c0c15100c40c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 148668651 1250 148667401 148667411
    0x4060605090403050304060507050415030b0f041e020307031407090806060a03051c020106171501050a03050304030314250b07020d0207090f09050619150b0d0b010c0204060b0d 77
    0xc18189114094440d94140c0e503054115243ea80d221005800c02800e0700040260502021902100081850784200420344001034103046e03035420b02c403011488181e0b0b60b105034580341c030941e29207402c400c2e82550703442c04e4100180d9036a40c20310260010000b02c0080501c4040310302c1000301d00e5801070000c80a032041d0b00d089800940c0c50108020300e403c0c0600006001d500700f11102e052421100c01410302881241c000820000e4850a9400c80e0480780344a00c0001c5d4044400b41d4121500310008501414050b2800800075040d921920794900c5139200c028100302004007000040c0f41418140d82d103c215a040503010940c0010102010828482003034400c1c0001d080443c50483c00003c00010302d0f40103030003604905260404020003445142c0c00800f01d55100c02c803500004405000316445070005038100003104000c4501502101e954281e0766000802c500d4060240c003203850191528640584008203002c02d0010040343c160075090002508181040400f007021054131003c0c200c0c03800e00800c1006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 148669901 1250 148668651 148668659
    0x15130b0f040810020f0703050a170702070303231b031204060b040b01021f1503050a050d0801060c030c08030c09210c040605090601081f060519050307080121020307030b040606 77
    0x3c01c9101d0f040c003510703903643c0070404440007a004e980074152006150402e001c0846a00c0d004c2190070108a40a000607004000c041c801c00d82c000c90295440585880c894103107040b4803252500d680710380b21000380f180c03004084a01081c1e004100300c0707814440598122001e0300301841d0000107490f144145903c1a800c002c9401b4807544005286510400300402e0940800c0030041e0340e80c020940d411142d50840100800400800e07400c00c60180d03590301c101d0041c500141010001021468183c014900300042d8550302c102003a4022000c07132a00e41c110740c003c1c4e500d88400408004034851a40355580141c950000b0f40010410480442c0b07601e0104e5050305c08680c140c0c8108400c031002070158aa01c202002d003c5034440d441900e40c80da0000107010340050010711601141d10203c3e40e9880940040d200140e14040d5002c0000d4524409910341032071400e5080040014050b900c05005907420903400c03140000c0c00924a04451640a0f00034054904080d200d00b0147c4c0d0760841290140c3d800c1e802c0c244002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 148671151 1250 148669901 148669933
    0x216050418060e100e070905060901060c0303020306010302070f03020c0a0603110d1a130c090b0418090215040b0d05010e0702070b0c1e03090315010515130b0f0408 72
    0x20780400c4605081080d65050340e503100106540601c0c0390051045000500310070540b44034464106070000020a0341c580360000c070400780ca400400c0b42c1d000300119401002225001884c4030000c2e94941005a125540e010040b070090040c10005044802d00207442d000f0326802041c480c16000d4151108400f19440b6107090303064030003190300482c2c05802000311502264081d4410b4504c0300032280180c9c02801e45c2c0000500c2d900780120303030088142e6508030022070750b50444500c000402c2048149801d1a107020804808924003260711004c19440d1046e0a045690307080820542c5021025019255615070611000d550044141c2c094001c0c5400c002251210846810601c41c0c4455801080018107101d1b444c8465080223808240c00d224a401ca00311040c50324081001c0300d15100019901c4008035810540f03003201820386d0b1444000c0e6a801406541c44d1a000410000c5102d82d20396076410380c41007102d1601d4484c1d880000001008941021220507090003401240d00ca0300483d1100d0203000500307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 148672401 1250 148671151 148671161
    0x80f0c0309031209010902041b080604090f0618020405010b1b0a0c060507060212131b060e01180b040e1e0105060a0e040905010507110106060804020a0303030e03040b0a02160504 78
    0x9000964030900c440584942c03082c8006130300c00b002c200040b5095419a001c102504c0e915020044648000302d0390400c1658014015580710404950a00c581a491348440d040351a4110380505402c0e26508a04000200442c03580046640504100419a0345a0381400180c004a8220b035103c1c0076400400001c000020b071203803906402c5945900a240380890a0782c1c40e078442c0e8801c40f6155001d008000e04111900881351003a5200c99a000407880d091a02408551100c204516800b04402050103c0d640c0171010104400e0700f801c091506050550400380000c0d074540c400c0a9207000001c010030000a8020b5860040c106100c0c0010074021003540340d44000e40c24005d0361380200d002d0003403160030303445485550346a501c00b420001e04410103880742801d54030222029408034000c0b02140d15a00800d1041000400780f515100c00c0034102540054441c007540d100c0a420980c50b030884058400083c0308840040040c005501d641b42c4142c003010b902c07059800492044540004400180d504050042d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 148673651 1250 148672401 148672411
    0xb0603150c0d0e0a06110901200c010302090102030c1c0806030601060f050d090812070912030504051915090f0905062110060909020406050a03030503040b041e03080f0c03 75
    0x1c0d01d4102080c100003100105800c500242062040707101d88404240c0e58401c03000100b0041c903205a0b588154030015001002c0c8803102581800209041e0340302c00d101180c9650348420918015079540e450f03200403880d42c041c980741048240940c86003034a40c00c03400c16440655000a44500d0328541e0341904054640c1024403446002c560030240c980c4040f4800c0006110708600503d00140170390349030321003140701d401c40c011001c4ad840d007800034041066001740a0600601e405d441ca83c224812554006145000342e20505000341482075200048ac5036841e083c0c006005c0c01c1825a0300d00300d000c1303001801500c5501c5401d0820281d44004192056240200e0740b0421001d04801039450044140740202c8500d04060026801003840440d40740303803c0d019580c0102800b14020031416010300401c404c0310020760180344611041d19040002036000000c0e01d80c4a078010b031a569481d555410001c0e240754140b840141c203040d04401d01c200301504503440701d01581c4002a02000e40c0c0d210602c056041c802a52 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 148674901 1250 148673651 148673671
    0x21f090b060105160b0402010507060920040e0a020906040e01110a0e030303010f150c05060a0c030e01020c0d050c0a05070308072003120703051303121103070c0e0a0207050a0b060315 80
    0x180c4d001158504682e11341044c810f14141d0715041081e00c40f103040342c030140c0c421a001c58105030b280001020320040e040c9289411581000420910410642d031412a4a4000d0042d040312001a240d980e035030b403080e203000703803600003d00c01d419884055a5860384010001004a8601480c8505070305001060b241a01c80703c0c80340300d90746400c142c42c81c41030003200c00e0395008021041031400002101032091500440041c0d4000c1120381201c0d00180a680d85516104c000340e206101110440c00009865140c0703000a00b040780c0c1d02c0080005050910401c880d01401500c61400b00004020001000f00036990284048030309110484410560900e206220290306503c1143d840c402c2240c80e100500640b0301c00d040c40c0b0310345000c0e010740303032181c04480c3d205035860717090910302d407942c0c83c0c001d0030700285600340764040d5141180316038a0221074070480c01034000400c3c07101c00043c620221641201c14240c0c200c0100c60154641e07141c0f100034040100d50485c040e0040c290f0b04042c5240035504a1b000f4001c5075 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 148676151 1250 148674901 148674937
    0x51b21060c0c0c0d030207051c0b01060804050a06050106021f050403092d0311010f020601080607050f091c0c0605270d020d0b070914010f0f021f090b060105 69
    0x6401201c41d5003020014505030301034a2100c4119603154254050010b2083c3c014002d040c1ca042d04100424084022283d030a4140d807805400003500490801c1c1520841c1c02d182e8800d8036141012494805e03e803c1c010078152400c1c0010a489070001203840300c50000c03074110b00010504041110075a04152001401714440030030900181c034918410510803c418102d000039041e040b50301c4440f47c0b10b10741c01075405403840c0074909802e585c009540c00001e0081d00042c5030a51400404aa64640c028400004c0020100b01c200c185401001203898040c00240391505200c0341c15075031706660030300a5003103407240859440081c0080c0a5000da48035252086c18441071090006011885407025181242c0d104a900d00d0b403800583d00c0e08400c00d5200d02401d1002250b02d0607076006401320000b81c0280b104000030020601d1103a03800001c5000700c95440c0f8051000700c2c0380c0034042c0d243c40694682c010809071580c9030200085802d91006078014080d41e000c2150b5110000151214400c1c00010080e680144d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 148677401 1250 148676151 148676161
    0x110103090204020c010c030504060e0303240406030c0b0307020f0d05070f1b1820030117100c020a0b060604032d081204020906150307030b0409051b2106 67
    0x95000c525240d0001d400989800107240e844da013107030344500c0c1d0080403903610700911080c420365100303012640803417200a6256040405602c908218180c050124210b210658005a610b0f59006035008607449508905282d0b10f406001c84170b81c0049500c5001442801c824030502d1500060070710a0b08000c0e2109460301e0384c25125078031014015007094031140c80e0485000303082a6001d034420001e041601c903000305111030042400903101403403031402c01040b014912100da80881d804903411664241c0e840b0360300e59600c8114030b0401c1900118a40f04c0c40c030b011031038030400c0d8010900c12042403145041c41419600d80d410050240076601021308101c1e08404500e415080ea146403c0d510429500062120031071076a4071212588040902d4001c40d0100d41031004500745210004e4224800b10742d00c00f5880c1c81d189003d80c4601004104504240c2c0301c0c83c215001d511254071401c05e094212040e2003d944115403049007031807a24030a14010b86a5074005e003400c41e0760741840402d00310300c03401402c0b00c2e41760 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 148678651 1250 148677401 148677407
    0x140a0b0a0b0102010204050310020417060105090a0f090506040309080d031404060903020a060603080d05010b19030c0905130e070602120703030b01050904140601030609150e090c0604170105070c1101 87
    0x45260242e05566080002264540d010040c1e58058041050302590702d1f41024070803407212240d005100160b40c0400014001c40d0b40d042607445c0c4c011000200012440c50035042c0c8000b82c01202e101400a000310380a100615034040c40420a0790f240c00c088554400e082003040301141c10a0306e1403900e41c01c0f01404030b0005001600504040d5000340304072200340010f40c41d0042221003039441210804000601c0140c45051801101e006000742d078942c0b8184142030b074542e00d5000c2440300801c00c250345d480c2c01072141800340c12600041c1ca0060407043c406500d1b05180f00081c28050444003087c800c1704d4000526500c00500340181c0c2440b01c1c0c03020309103800755070250068100030700c0c00340c14440188400c00361607c5070300c503130301a030a440c0c080f485e01070a0440c000740840d9003d40112440c141030484406030076031790b08034502c200e800e03000521083d9a40d003d040c07420400c02820390350340f10034001030000703041004408408881f4558030080009403501c0b8410360f007000300707030340c0080000f00380c40c403803144640c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 148679901 1250 148678651 148678661
    0x30314030c04030b01090e16080c150d023007020703031d22050c030105010c0f1703070810061809020a03112d0306090c0d0908040e04140a0b0a 63
    0x94201101c0e41015100d0307407101000c120907000003541540d154141d1715111010058a040061500e0034004000e0800800c00c3e15140da084141b030003030a0b1a0804440c80700d600d800c441c1036100c000c0c030031511203002451907108801042000c154041d000c0450500c0d460034103090364051000354000380840303859650180e07848916400e40e142542c2d24250014510349032034002c0e40400c041c0d01c4800031901c1c80c810b4079004480c0080d0500d22509001d000511151340c0100e00c025440d90441006c0240e120300d85402074112806050302000040044180301c500c680084209001d4801052a03144050f1200b1742250708020044001100f00201c1101b003040c1d6002d41d0040426801900e0046841851408085840d178400c140300800107041c55000d14040b02100d1003280d0a004500c0c5c1103265044c0440011a80b1001901d03080d00c0c00c40000c0c0d0544a03500b180c0c084000380d80d01042103600d841d501c8500c0c40450000300d5050365003200344514081c60b2080802c02800c0c66600c000e202d807180c1c03100015070380104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 148681151 1250 148679901 148679911
    0x31413030311160605040303080702070501140c030903070b04051503040f0605060123040609090e03040b0c15010b030609150d031d04020c1e0a030804020105160f060c0e010903031403 80
    0x8003d01521424030701c09030b1041005003c0c2522042e80c0c1d240f851030010041c59005182e03604540200c80705000580e8448403401c03052044034030964403860b5041c480d40c118850340300702c80e43c9407155810010310036441401400840b5002c644c02001112600c10000103480125402040030612009030000034403180d200e0340d080b01e4185070001240c3c07a4904608009554001001403000c000300781008180d5200b500700700a04200302040c0407a0305101e401c0355403070059004a003140724000c05e45102d0030320100520840f01c0c2490440e0780b12940d69542c80b4095500517500a4018000c11000420b00300c41005900e00034040500a40e0018040340c404845601100501204031010054a040c0640d202d001038014060510090070412001c0710f00b0013045640c0500d01c1c032181d04010322900100750003070481c1c2c3c1c0c09902800c2c40f65a8141c0100405240c4462103002054041c80300e00c40010b001c4280d000c40408a42900d4040b000320240d0015100c0b0000c84c403004000035100400c0d1002140e904000d10b40003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 148682401 1250 148681151 148681153
    0x3040b2202030102120a0516140a020f060a020406030609020f1b0c03010f060f0e090a15060b0c01020c0d090f260f150a0207150b0a03060c0507031413030311 69
    0x1010389079002a0030390380020040c004035403514040c0b0404500e58031a080d042219840020411412548c02a1002d100700c5141d908045000c65048c01ca00d0081c001e14490080a1054691b103151443d000340007500300740240000249440030202e10006103100300e68140502c400024142a005504540340b541035054600711401407800d43e8110f51400d005100600303003044c8001c1802c40c1851840401030007142d010340d4291200e40140000100041582d0440301c0d00403a850408401300382012000d41001c0e0b010100c1c1400000300c0100007038040d8007500c0185201c60641c0d102007a00b45040722405441c4c024012088400c0c1000c20201a517a2042c154080d40a60144442600c01c25040e050212041c900c0c003054001100b05001d00c3c22043c0300179801042c191045060900e15241d26103080340c0d800c00686016602c0c0310b616080d43d500c00104c00295417042c014020b049105200900ca90099001100031600620304000000c20356420b507004100181e540111491460b1421200e0032006c90110b415 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 148683651 1250 148682401 148682461
    0x6110a140901120c032a0804020d0302070810020d0b0904050c01051e0f0a091e03020d0f061a1005070203030f071e0804050f010201020306090118061706090c0603040b 73
    0x2a440c060f000394040a981e42c0c400003011b601c80d007030b4046111018a428090440c00ca80f844072400d400016a0790015015580d00000c01549d14060b442d01d10300d40c1000115110359462240000881c0e00100010f254022041c080c8421010506c00707100b03000daa004103a81c10000d411401c6500c07a5001d00b0043c00c00d211b00004d41c4051060412465004041e0305000690006080d6061030b00440500002d2a00c0c3d00c0111081d0704401000550344040d010003072041603141c5aa01c03d0029811a05000c0394109004219000c041010f0010b444200d62485014001c000c2480e04006e00a8069070785464010b0302551420342d081c280c4a1559001c0e2138200c4214511400d500441c005420502e00e41c1807154190545d12800c00041114074850040301314110382c010410000f968440c43c07601411100016442582c00a5070301000028241c150025880760908070801d50015000055460082c0d40c0f50701950002d550040600c0080c0c44102c8020780160b9059012409402985c40a0902c80810b00280e0322 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 148684901 1250 148683651 148683677
    0x90106050d0f02030d09060512041109070804060e030a08010e0c0c03040b0418020702100e030c0316031202240c1308010504060b0907020703080d020d0606020a06110a140901 76
    0x85003141000c002d4491030481000e05045040070409040e8610f550b0422010b41c510b4154014201d20518940b0b503050001100810200804800c00f411440070003401144c1a15107104c1c0140000c00c1118149c40702070410a520b2218600802150401201d81d0f0b81c282c9580e0802c140500a14030180111100c0c5800b0000d031085440180043c20150980c3ca60465545281c4002c020041088076900604035104000d540c0c016501c040076684245020b060400c220300c0060b0000b42010f01c030307480d05034060284038400e000b10005101581c05036840791654101c076401e10b460032030b0380c2c00f00542d02e4078601e00145001c4100e49204050941c0c030120f030450b89841c2001401c64108031070265408503005030b44940511003000414025084a02c00030340345001c0320718190341d00a540b80c407680702c0900362038800203103403903001890340480d0002480050140541562100000e6070f54058076002d807075107882c240c40c2e9240c1c0d54180f021103078900c00310741c1c4241000549602001d031540c040c2d8046410300c011344007044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 148686151 1250 148684901 148684909
    0x1302090103050703060b1509040b0a0e090c09010909021c080904020d02040e0a1a040b040902150901120608060601110a050f0d020d1b0605090f10051e10050103020309010605 76
    0xd0186200b040581100c62861030703d4030581e16208159880f03690018407116441405005407800001d045901041c0451028080f562030281c40d040308400000000420050341c0b000200e40c900140242c41d0046140c0e6184015030841e020a00003d5000c040203502c1000d0f0703505000c0c0d03581180d000704810761901c605403002900301d80c4113410f00d541081d004103081040c07010100354154402c104410a102a107a6038031b07100f0707403242e81a0a141c842da9540d0300348103e6032207e034030070003602d0780c0600000b0782d1166a9442041075040313400c03031324006a0424129200c091990143c041180c184000510b51500d84800541d00740c0c88200c1c00319110b06c5030300203400100b88108141c1e200714600002904a80031300120090502c8014050700e010302501d0003441d001c0029960201301c405030092000501038481d02002400d26414828170306080c8160319140702400001e600c081c4c006c400070805240054071604152444503030032100010742104011080019502a8006541c000580b00000500c030352900002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 148687401 1250 148686151 148686169
    0x80c0405100b2b092a0b0a03020c0703050303060316140f010c08070303061505040b090904050708070e07080f0108062707240302042102060708030708061305060112051302 75
    0x5100300d0b4844c07055200b4400c2c200c2001c3d201381e03112141c1250b03124403803080c9000200c01c2d10482034040c01c009040705400d4801e07415510320011300310940c1c0340c1d941c0d242001c680d41c3d042900d50038407d0242503000f540302018080e800c07044a01002100b120444400d003045491880000c109040c850040698000504039000400300c00d03100751000640a421320041000c0b00120026a03410b2100420051018150310415600c15034012103040c10245c1e9245425800d00c1c0d041d0340011203500c03520700007090701003c0342141c03482160255110020b0382d5a40d6080f86280d44284254222504030780042280300700c0300c0390900b880c40750f855000e8408070741c403550052a042c0d4643c4044d5107444905111502c0c0c0100f103038941660f1045182c2941071604062001d108440d003100803150321509000c0420464450b802540c0c00d507074100a50035101e1515100181002c042110054071074140e40750303545007041c4544601801610103a44846000c401546000300812001e407894410583e030740c21810040e034604c440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 148688651 1250 148687401 148687477
    0x90b100c0206071a0711030a02070306050405030f0307120e0109080405040b01031d2506080f04030c0605070c111801060e0f0409111804051507050c0a0c080c0405100b 73
    0xc139a460301e40072100425202c49580344140c01c0e00200803800c0035aa00040d4502601e411080c00109030f1580c1c07400d1891072003400340000701d800010080080f5550446d40d05180e001034588188080301580c0640c5080301c468500c0100340782014401804203041c198020030001c041230400042204140d040c0c0308040c1080300c501c07880c40d84039002d40340c1d91591445201c241580b0071500c8032079090401601420800c4002d001c400320701d04200000d4203041c4038007401d184513900210100003a0500b41c5008080c1a010031040d41c00150304e020f07d0700f09080210502c9106503140070300303041c16400d00e00120f4040ea40400300c544d000880085a64040e0b90b5803080e1071000c0d101d03131003a01c90604d40005101108591036208424041d80d202000f011500c081140c0b8807070782503c00303640815512040c040d91180610045002c0d41e1040660440c204104c640103d130a9580e89811968100c1a1030204001d5072811144020f100c102c2003800c03c00c054900002d0000130180c0c010740741c0c032419660b6043d8541000824 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 148689901 1250 148688651 148688693
    0x203010504061707060c1a0403090510081605090d05031809010b0c070b1c050915090313030f06020903030a0302070c0f03050c210a0c0f090b100c020607 67
    0x10480c03032070688076410041441c1000c2d080d100f115214040d84980d910b01c03074402481005058201000f51a4070224204403003401c0e03801d41420325043c0241040320300d010f101c0c09924144600861b01d80603c1c000d41c4500720380300d0044100d490380300040700d140e00109900c45c3c20004100b010b4000039000e2000d0000c40800c5d10051805034520b80802101d9201a8823140c0710100410881c3c0400c840407407400283c1d02d0004140359a400c0b1481c201e0f44110b00460036620b054a0241400030f090000f1900001e143c103811601501512001c440030b4403445460141c0c880220b0b110301c200700180024080c455128060507005091280e000042410b641c070644203400000d80c0051103600300716a521061000d88407400a9029560840e40c42554440c030040300d01d03101d880c00c0645145c1c46400322840103854462402900c6030704806d40f410000d004420f0041140c0c84644a1004c200000e01d4071034001a010002c1180a040c5101a0162542040c150040e0381240081248101246542c0d40003c24003810312 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 148691151 1250 148689901 148689907
    0x11e0302030a1b02030334080f15031e0304030602040f1d040209060d0c0801021b060114090f180601030804090c020c0105180307050d0303140c0a0518130e0102 70
    0x40a02c00321450383d884108110400c0c0c42e4041000c1d400029a0742c0540082c050005425031580c4245030304811070b0000b400c100703c41c050100459400166a40912000c2941210f19240c10140b000d858400524041c1c044d0300c0704541c003c80f50485800811034040200540b80f900740c5a03103d1a09076442500481c032500d600c610204120444206969400720810b200500c0e142019400521441e2001d010684290b014403401401c3c03260071900c1100414065008541e5050641400c0921264901c40c0b66134a0103450000140c5036200e044c80c03900000300424a112581d035841c00c4c0c0707840c0b40020340362101200c140c041075504034008200300b601860090321a00e03210f51400302998156207091240c18219000038a41c5440350f40c019096a46000c00081010800603030342012030702c0c0000b0703a4455540082c0e000c0c0c0d000309054255003e08918070240764400d0083d9521600c1c45058468519101d0005904202d030225010100041c00d96500703008004802c8042c40b20040d100b0b48204440001e02a5800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 148692401 1250 148691151 148691161
    0x903020607030e210c0708070f051203090603100f0e010f17070b0901030b0a0308070c0e160f0e0d0b0a0506100c020f04270521030403030902011e030203 67
    0x400030035a00007030500d41401607000e10100d458450602012200704070507081c900340c4070400d07840d041e6104400003c044440280d500e80c03000da43da1403184200e00814a800c040401d150a201218100c8800c15000540c504105801800340e6680010040d8804821540c000306030f0fa050125404006c0c0207070254041e00e54101103826001e02002c1d07000303d142811809885401040100e400c8007101e4186400540f101048070040e0050321100543c164014004403012041009900240c044640240402850151034503d800344220098800d080e0042200f402c8034860745c4201c60366104602035140a0403076801000104882c1ca000320f5080700c4030380c448000c100301103440707108039a403181d000c03110f601c009182200080c2c240d0300035420181c01001d14084298442d11a5007010402c041007d41291020f51910b40c407410180c82d00b8811511805004000350200d15005a182460506008245d1071510b0300d40d8150000c040d4140101e040c88030111305c4410449802c800510095400d8502607503038a08 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 148693651 1250 148692401 148692403
    0x6030d030605090f0406021b16120803010b0310030b0403021506010801060e06031f0308040e09070302091512030a0512060a08070608070302071704150809210c10090302 74
    0x5100408020945016010060755494209480d013000640d101141651201e04045000c1e100e010301101030000c03210742c00721002c0c2000500e0a1900083e090081001c2d840c1d5047c4500d00d03040c02c5000d00300100610042c42441c4c1218001c50b04001c0a0200c0c10701c0076680d40d240d141c00c02088030164003581000c026007010861080c2101d510160920300500300c0d6042c18005440c80042c0d001d0a401914040001500d403c0c07410480900b60030760203200d801040c0e07a4541b03044141d105000381103030902860085000c4500010300702e07040d01c3c1c0c020300c60400350f55010a01100c030017204141a0b40980d10080c610798051041c001411000708607910107907660400b26200f0056600604400e00170050000c027086500d41c0410302030265041ca25000185489680089010380030703910001e00b408401d0710003103000140100c0100100c400c0052040c10b030803a1840309071200d00c0e0480da4441d05400c030491203090f0400102d54080d900480001107800d105801000903d013441c40c0da070702c0810741e44d920a240103240d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 148694901 1250 148693651 148693663
    0x20f1002070b0a0c091e0816060215130807080d06060315050f0d020f0d1a071101091a060a030b0a0609061205190201140a020106150c08030105130603050303010b030603 74
    0x1d510306013484026541c0e400203014600510030400780f44041920306c11040d401400e0381c0010180c51701101c510320600c018150603070041d440741c3c40151007541d900c1c1c440107040310482c611444001c0d500300303428441340d102c91030a07a0000f601160218001c10020700421030030b10520b005000c0c6650700003204403080003a0b071414a959040580301c0e0319180d102a03c0d030340e506401c07004003a5060311107080e01101030021130020941d0710402401c0c1c0840310034032034810310340380071440c4109440e039100252100c41c2c010302401c0f0303000848043d200c016800c0075030f01e031400840f004030342061029004600081d031b03a494501503c0340644408041c6030302d0301c074200a0703204a03016503000b9019861560f00d6100d25960b5031130b80c4014400201035060f0300c601c400800c0d0b81c0500d07886031002050ba802c20303a03034410052000b402003085000c3c0380b03516400c041c00d0b01e005a22500d102c15000d0f80c4031001c0c601d503909101c20045041d04200300703007080c0d50300c0d04008000070340f041c4040c41c000d2000c040207984905110081509000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 148696151 1250 148694901 148694911
    0xd060f09091106070507030c08160e010b030718210b06061314150a0e04050709360e030301030309051801150311030115020c0301021e0307020f1002070b 67
    0x141060815004980c04614455141c501115619130b520039a1030b00a0500d402c50b403000e449114540400143c0388008034410b06001c0051aa00c2c940ca600c0b01c4810940c41e6003801000c052117401d10005407070502808495a607001038030010510380380d0324404000d03031068034400d003040368114140039410480f0900105802200c00c0340c405051402100003810702000300c2c40f8003040710b0302c040510002031319050450b403c40e01600b08982e50305d041164000e00207016058025010303900d0b107000200b205100303801c031b00262110f00b45412009215000c0c91502c00400400b80e803c0700303500040034040b07a50188180d600d8403804002a5460b98558100078100c07410f55407049005212040c3c00089200d01550718906540402000caa4410315400e0100c00401c1e40e26031220b9888000000401c4d03003007a12240c00040021982100e45034001c14040c1401e030b00640005064511040710131124900c5024040e540c400a64070448400d0034600156501e4402411280e0b4119680000e542007404000074a040e03001c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 148697401 1250 148696151 148696169
    0x2104050910050907180e010909050c0a0501050d0221040b100603200f0702041e0b03190f021c06060608091902150903030408010e0f0601080601060c080d020d060f 71
    0x10b140101168880d60000c0c854000c000407101081c5080c1e42c4e54107030a0150080c00c00455007507860f07a20f0100100b40c0c42205860764800c016140c0c1f01d601e4900044020b07500107035542814007000040b0701020f900941d0070040d003c0e02166041d81c0c101110030559200700d0180d001c00201d03080c03d280c500a4400603400140400d0300748992410300306a0f52201c0e5030b40302c0e100c0c92219520740400c1d0380103109008810000350700a040070b108244161800c44017403c1e5094003481040a102400d04042c1e840d000c21404d0801c1c41485403280010842e01e2000200c160b0001e014030007a1021324070008200510f091080382c80300c0c0e4aa0040c4000d6034898581540f000c2c3c9000200b00b0002c2c291212040c2001c1d144009224032071a1801150460700c08045d20040840942103d0f129a121088070b4044c0c0703a0301c41d4060040c4104400d600004100081c641c3c100e0b8a100b0103040d1903402c1030405c407501c071000740054130001010842400c001101d80b00030042050b02d8240001c5a0341890344000d00c840c2258444200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 148698651 1250 148697401 148697431
    0x40b090a0c0308070c090f06050a150e0d03020316030f03110405131109041e0b0a030b15061207080403020606010305090309011d030712061503030804120221040509 72
    0x181e4444038100a07241c020003026240d00d0a450704180380310180e00031150300c03070409420075400755003600501c0c1913440460f40f0034481600c030b500b54a840300c840001d51000a05842d0302c40d04030b0a0404440a010703003c1c1c07044e80d2801d00042c0710103243d42c0140f0f0048000445134229080c5041d4184039441985d003602111034600740c5040006103510503a8190b0440c07140d80ca40e8400708420030f5504a0300c030023078041c0091010400818000030360680d00389480b4a07483c101191581e05107015581142500d44c824886070a948604489026808500b40d41304e4128908002c9040c9822404100d1751007076000e960f070041145007601d0000c0c00d103200544041e06050400080c009140004016035104900a03e00650035240880c011700c080140c0c815200e03010300070000c010805c44140c00e07440f80c81a01a030350911212501400404041c070701d5100c041c0000302c0c0c0001150008840d5010310582c40403510403902103120038007117822800c201c540070030302140e0001000c0040b41004803142c0d0b440581d101103010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 148699901 1250 148698651 148698653
    0x905010509010308090111070302030d02210301080d0f0504210203100c082a0d1d030a05030a110d110301080d08060d08070201090e0702010506010e100c0b0901020c1203040b090a 78
    0x41303035004480c0164144681c0441c5845051303401c11101e802142c00500300c034507107184403202a45681ea140c1090075900503440ca402a20602d07802102d0494807034400800100c0d001210456000d4101a11141003100811002808444000f83c0045e8040d64042124104042d441007520b030110884280c203a8604102c00344900c40c2e00030800540c4403030491203c0621858075004140204070808007918000004941d0702c550b4441356011204210b1264600101d13503004000550f03a034005c0c88034500010300100700003107e00040b0340140d08800b1f1500c0416040409070304200090b50400786107070f07174040804801001b00200070407400194101a060080060810b0000f01e903003c60303400c200ac3c2c444800096600110791040344100000c001d508030703101c060b00f02200000c2c042c01e401d0318075600060810244c44000d1030000c0404d890005144c0310020050390341d0f0fa8162406100034807010072550b0902c200540c0e2007092087d50703404c806240910340d42c2c0c6803614185840400203015900c559002c0303001c0c03070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 148701151 1250 148699901 148699913
    0x41a0a0b0f04050a061205010212010f08030f13091b1d0a0e0601050c07080705010e12100c0509030f210705100f09061803030608010c05180f10080109050105090103 72
    0xd10408142c5010986a486110601c007602c03195010b074401142c910010b05c1442010340c09041c1003881001004800d990710b801100b60a900390007003502c550000c204000c1140107440080c200c40c102e81c3c0740000706690324a01c1d1000c13110141c404808020500c00407007005a8403a0a0181c076030f804a00e00c100c0645440080f0b500c00a10b40500080c400455010450302e030b0140781591580c9000b2002c8801203505c4c3c1170095126034081c860036000c6440c00d0081c074118500b0418008044815400419210071104a40c8020700002d400c01c50a12904100c440290740b07050142a40204801004000300d000a000d0000409500e140781c3d00000c070144400e400044000c84c400b01c44215602001ca01d006081d03403240001c10b0b0b0903400804161a00c03400303075070018144c1c81005865000303803010080701d55200f41490176541d40000150000e00100310340f01d42c0040046808032509405040c42c035a207004000414501e40c0300c8501030b400708200d0801003280308440c0c000d0f1805042d040d262003201d54510f035510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 148702401 1250 148701151 148701169
    0x6041e0608071d0315180c2b0311030c03090307080703050705061308060a050f070807080601050f0d0507030203010515040f030605180106170d1d2205041a0a0b 70
    0x2500740c89400d4008084655080180304a020700603100d00c01c0600300f89446e010054542c20010805019103031a40086150001202c0c3d60342e071050b035409030800c80076040342c09002c03115481103083c00341041513640d5148042002e4040c2100e010000c1d42d6a51802d02090315100e001c0d4041078080c0d0190400b800003d40114281c0d0840e1429640030b5120110f42011400306c4007182c00c040f8462040c0c0040007401c543c260000340c028441108061829240c0c50300417100c9503412501e24010801000c08240154426002020b803010b41c1404182001140740c1c0c490140c9509581e030000103030b0003100500091034140b00343c900c0d030030101e120340386024940008040f1500700d502c00603141c96034440010b44000c08407484140c036020070034001c10846446400180c0343c3d1001c1d401e030074000e10601700e440001c1d900800c5407c0d40c0400c0c00c0404002004614100860980440c5c294209072940407824485c0301d03454082d1500961082082c84003640540810314002280101082111800c1c12085101c5440d400c440c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 148703651 1250 148702401 148702427
    0x906020d0b0a120303200a08150f03060708180303040c06090806040b0c03070c0209040c03150209090c0706090f03080415141f120b04021203030c0d05060301060506041e060807 77
    0x1000c40c112104180440c04106d40c514006403841e40050740c0d54483d0380c000c0da8075115405800150070600b905400b8810780081000026030117500c01000720300c140340a0317800b080c0c1c84105450764040700c1030301454031800e581080d50304403041a41e9020501c0b40d25000124540541810001040c0e0352500d034031402031a81c009000799801000020118080314400d4080b80000e9402030b044404a05103880c2c1002800d10750300c0181c031b030795800102c1741d10030f141a4000c80342041070042c00e00200d900e8102120f41107900600e8202c40241d6203401d890001166410b80741c0e0240d0013510b4550540c503040c200b015405070034038402c0076a20300d044c00a140e00c41c500503106070412604880460250700d980310140b16019142c10a1a12990100040c0d041250841000348640e200380e8104200307050741e40d4016135a00003550440c10b400070500503904411080e90002e58484401000032a0080c0e5802c0030881551080d0044040e612514441000e10141002d00200400461800c0c02c400c0c80c01c140d00800c02d00f01140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 148704901 1250 148703651 148703657
    0x6010e06030307080705031c0e07140d05060709061d0108040803090f07180b060c06190207170c01140702030306011101020d2a0201020a141b010906020d0b0a1203 71
    0x8120141ca08005403003c190b4000c030070070380d61180d03824025600e401503400101d5041500288001c0c00250340201d50f00d4141074802000254200380094003510b2003612841c0e00b00c10040700d280d01080701000010700580c200d0f20b941c40414105100240408104080c80314468280c4007540400d907404854141c6c0701c3d0b00109600c0c1c407616504040d40c05c10544500b10070b02c500c500c100104424203124915402e42a00480400000328140e00b8803100e030286651001c4980c00050001c1e00d190500f040b00690504140300041c60240c50750f440e0341ca200b040c14100c2c0e891034004155680b040c0703424864200311401c883c010108501e03261100035034030310005000c94100711028503082c1c1101c0e02501514044c01006505129a0600f075102d000d09403e05a5840d00003a2a0788404440d640188220342c1c609041d0707910840008604204840e10f0341c015545020300b5000300e0200d040c3c482003841180215840f600b030150b59482c40030398003011380300e035331000a125004200081140411150050090f1a4541 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 148706151 1250 148704901 148704929
    0x70c02100e0316090b21100e030c0703050304090b0613091505030703050a020a0f1a0901050405090f0405010b03030901021e150106110d0302070201170606040f08070302030705040e0601 81
    0x600480c0c144a00312030354014143c0104004190010746400060f0740410542e10b14204000380100c440202a200308451050340010b00034100343c03171450300700d01780d056021170840b403410b40078a208501e801850740c006c0e2071541002ca024080f0b45d040340901490460110740840c1865881301460141c0d84243c40f911550542c0c42d0f80003084800d0495200d00104002029144180c0ea82d0034102c0c1c450300c03558000c03880760b280346c1c001213400809820b600c800c0e11500d242c0050302e01c1d03190b6540300081d8411204181409000d00c00014a07584407404030b44140300400c400707890350425141290a5550611480e88640c00502140d001c07642e0004a55109205040181c904010050360580c2020600140c0e62441e007404000818025000a0490300026141c403c485050300c402d0740c00c034120b0140c080020700140904420310340602d1588405600624000c1005203082d54481401254130070652200c01c1e40d8010a108000350b140a0041c0300041405039814042c038241894981d445580501420715003183c54 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 148707401 1250 148706151 148706177
    0x90503120405060d09111507062a1103040f06020a060f0b030a03080612010203040f03020c0409020a0b030910061401080c040605030c030901020c0d0329090a02090103020705031206010206070c0210 86
    0x2800002d07034000c3c045e000340342c14016449003980c0355002c14012703520107051820049842988100b00c80818000101400001e111810110396023010030745c0203001407005100204006164141c200000c044075001400d40111a1920809441c9502600200c89180c0090300d481e90300c000c501604e00691500e00740c81940d45000000f02c9002014004104542c800b204010410071180300d09003101d4040d0f02200d044150300000c200c155948018001d4100e400b07620100860380106002c0d5800c103c46406451200003490072200403182035034454110350780c04030440b00607540c000c4562508010300300b01c0301d4a070500b0020302405521002e0001d441a900000000d64080c01c20342c140e410540310071095540300d0f000560010040c0c010740c0560746501200f0802d04090400740400d031020150702602540140d940c44100030003d400070b921043c1410707020808070000540610003002030b00c00c80a105109410400002458030500808031000c3c001ca009907030b8050b9030342e603610b03c50940c486e10340a11841c1f11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 148708651 1250 148707401 148707413
    0x20706050a0e120102030a02090909010603110402030405031204030203210c1902071805010f06030507020a0312061715070c0c0e040204060509100302240405040e0304030b07090503120405060d09 85
    0x100d400c07140e0f5654400310500c21114900d800502c4082c004443c0444d203521100c40c0d281c203c600354400200220825000c0e102c1c28102a000b443c0d0140c020800d503400c10030740058880d01090102ca0407001130b00001026100c10143c68209200324540740c400c1441072a040011191500c00c44085244501140e0b141d88241c9100b000f02d84060900350341390101c0034a40b0150034024010030f0081402c8401c2d45100030820703d2007440b51030704c1803040d6402400c40301001c0d10b0035180f41c0740400654102d103807141408100304500004032a43c3c245440000c1c84a900c00c090003100000700a0018410070490180f0b00e030101e02c1550340b83c0c0170b45500f0030010906858600c0001c0060030542d11240d0050090800c0188003800682c1403000c490007a9450081c045004440805a0003110005901c40e01309000038003041c201507020101040b600c10403a481e103a1682c4400a519038225100e0000407203001040c0041e041c01c2c800541508004600d0038245400d0078005459400b852280420881d40c81c5222024840e07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 148709901 1250 148708651 148708669
    0x30e0d02060402122509060509060d0209040c080d0215071b200a1203031109060421060e030c120a1403060a03020a170610050d1401020f0a0c0b07020706050a0e 70
    0xd403074441c85c0380f000080f0040e1030004800c0c8074014460340380100003d824101150b203548070344801001c03141840d00b16808c01900840c041d0099440c03020840000c00c3c112800c120468480c08150020103040740c44840d00741c00181c00400500411594071100300030480341417682140198800c0180b019403400128100c40c04880f0046107a000740703181c80010302940408201da1401e03010f0b0f542131241c03203589220f8a9241c810b00f010700347c000c2c00c1084100a10702402c08001806c1320901d101000e0241142c82d00300541d080200103041a800000383c101807150104190907036042285016403c3c2842330001400541404030928004200000003170101e54542c800341d8081c5900910f501c20761a103601e80e4156000700003440c00341911444020480200c1d60021003011644010100e0302e5001003691801e803690803c0150a615640900111010f0741601e40902801c030504c1d0703030348640f00360a410024102940a410403065400814007401089d07800030803149001c801e8105138480c004c422001c612503503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 148711151 1250 148709901 148709923
    0x1507110303070812041b0b09011107060819060302040f02091c02030307021c0c08030309011d03092419121b080c04030c0b120c12010e070e060c01060501030e0d0206040212 75
    0x800320074012516007c5d41015103080502aa90401007000741c500c1c8a0b0340d0b8030075025040110300140001031105d80300340c100b040c0c810718800000c17960310303500c0e4042020744803041c08014429402107200c0d12103040803909000028200c9074425901606030b0046501ca2192032006401980c50000318000752910010034184554080100b04c5e001b9510501d0980342d400a4491030b15550800405e828080816458404480d13440e2024624081c00c1e80e003000440080a07060541c03180c1118010541e4050b400e0152041e60302c550110b508125101c4001850403001145c0c04c44148d1074051080300d0040310305000a0034402e01d00304400b017a141d841d164a81800345a00041080000c080041004801d0704040c004104160020301070603220340c45900c44500aa00303070924203202c2200100910000d100d10b00303800200e241400c1240070803a0012030084d91100882d9090790703440305010000c559061040d012036440e002d0240480e52083c0c000252a034402500281c07088040e01080ba07191101405401030748 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 148712401 1250 148711151 148711193
    0xf01050307081f12050115080106081c03060e090109020a0504090b1306060b07080909070903050a080306010e0d030201020c10020405060a11010b040203090d11030a080a051302150711030307081204 86
    0x1101c45c0c505580a0481c050744801c0d40310640300000b074020414054001610b4511025006005070f0006418040b14004660410140c58a100280d83d104140c0c0d05c50083c0d1084002140007042c60050043e42c000507403080e0f00643c03410740400701052801030842e402c0ba5290418030709050140c00d003a0301425150304034414045001030200200828140200700d0044280c032035441c5a030b82d0f490141c1d410003c42c071010300140c0180005200081d00381000319031142c01414100b0000799120089030200751214000ca0240c2e42c0012800c1000038104483c54203c40780d07480640c80c05060501284040c0203503500c1005020b038400703c05040c080b00b90801e04801e00060411900d91516020240c1d0340e010152040c804200980441146007401004a40104140e83c5503042643c8031003081328000d150040c6498460728503403141c000103a407192100c0b204031466507421600c50b03100b42040660324500c00c0e81944a548200084800541d02e20b05a8015003203246400916079203d0500340c0698881004200f84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 148713651 1250 148712401 148712429
    0xf0b070215340c06060b090319031103030a0603050f0109051b06040e0906040201110c011d0105070b07020c0a050f090714040909060f0509010c0e0f120f0105060f01050307081f 77
    0xb0300e81d488a08032401a0113668240700c01c513a103400d4516180709041d004c80d055081910000b04c000e01031b04800c1d0700e06101c0c0c5411039005401800c00da045400c1a078545075003988030780d001c01c2400010021181d0109000b0000c02241401d66940341d9583c04034800340b9601d6900340145c402c00d50b5482c05031401058007940b0308000b843c01c0880c058650300708503802c174003080c594428400b05900010348410b1384041a12203141041c90300e9802c4040d00e4103000c880b41004400c00c40b2100003241380c050700b401040c0d281c00030300c002c0c4016001c110014036583c21160086407900c0400403190780d0003040d40d4200d00c49007409014030490142d25a503038495500114006801d0020300c40c20004140c4c002e82c1c1c03949100340200320741d444059280f42070b11688079102001883c0103003401d61512307181d800291065002080200b80080a00b04e09041c100213100701c040a96594082242a050035000400280c000f46482803451070200300241007214040c1003401003940c0080c5c0e01421507805541e40014080c03060500a13 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 148714901 1250 148713651 148713751
    0x30d02070c060507080306150f13230d080306060c07030c060f050711130b03011d12040602100504020307090906050a0b031605010315050a030f0b070215 67
    0x102951150500300d400080161001944511400a4981069000c00350601e140c44030f0003008009105281d5a0040360010807000b400030030084000d148030495811001d086602d407204172030b88501043e400021a2800001c900342c9942e60203221020250b0209181351203894400c0803c80700e004e91016400c1e184110440481804a2070f40000d040350b02913940c0c10b12115404400300d4480c02501c3d00204901e101c401848440d240c403604e14601c0341c541c040001910f902603c0001c0c251000001055030402c02c141c01d20354150014000151100034903c4030310b26003480d200c402903459070026030300d44460390b41d0340c0410210f41d001d0280b2401002040414031405285003000e000500d800d40306540868541a0040c079117080c003044070054100f880004051032883d00c0b0054001c2e07c00c3c4d11070450000c0d20603501040d103654a0515a0203140075190080c01c50307080d0314200707444104c00391071a025540190100145044c04498a0b5802404000302420081040b0030051141d10b400c1c410390440454550594 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 148716151 1250 148714901 148714927
    0x3702030618060a18060e010b04020301090b03010506030a120f17040c050306060d0201300509070312051303080901021c121802030307030c15060603020d0b0909100f0b0303 75
    0x111014805800da420320344448006404507580210a034000390710100404c400f040703042d80124225090b2000100750107418500290890b40260030220700c01c0d42d161105051400d0034891182c2c00a4150010080214141c03100d03e60714200c950868208218018060007103403203204442c1042803002c2032440d260800d803515082d05400c2e802028007a200c2c440020310546401c402c03490301250182c442c2c1001c10007010701c00310b1942c0903002e6101001c41081810009031f0036482511b00c5280389002074440541149442810601c03804001d00801c4004e001c406409120742d00300da070440b42e10a804640d509072400042c2d00308407941a24041d504042d843c0e035540c081c0c1180817081243c1071401d0030450014070314604140c0301d5417018080d406031300038045440064002c03071485140300d00516501544806c0403900700c003529000d8110100203a00400c020700301b1a410300808581c040126902e0040e481d140c80c200b9500c184900c3c1c00d4099a4642080761200d4106505c006203107a000b9007540c6c3d650962045074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 148717401 1250 148716151 148716181
    0x7020d0506040f11030c0108180a050a06090c061404180908120402030609030a140304060b030a05030a1d1e01050c07080307022806052506050a0e37020306 68
    0x40c0d91820035084400c44031700e400316a000d2a90416101c0d0691516164022043e420740403aaa0032a481180c0c120804141c7c10490510558070450700880c5c0e18015161500598419600103001d10801e40c500818002040080c0d40503640040d21030004604c1c1c0e800d0342c10141540081c05030000800050200d00440354148840c03145000b070b01110b58039100d01c0310b469601d200310014000040c078180705110100490600070340d045801141c0102d811501040000d0410440c040704540c1c0d0343c8002201421290030000f90400010f283c0010315010102e1004540d0002c004051600035850051020300c4030307800380c0199a9070030101001c0720300d0030b07860b1000030fa42d0703910024040c0d02c28110343d00c1860000840c41c0301401c50b60407080f021240c0628256050351541c04c20000310b81050b4946610504030b0380c0d05c1203400003140c099140452a8103101e41c050040b1228070100300065080613406100c4007400a0000f40c0c000301840710000808010121481010b900c000c00a5150044109100020800d1141 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 148718651 1250 148717401 148717403
    0xc050a0803092b09031b0314060a0c02010603021c17040f0603050903090d03110708030f030106110601031707060b0423011409070c060b031002130b03010302090c07020d0506040f 78
    0x410101d415003014981a0880c0803c0d2a0000600350007051000402d2100b031030f03828005407903580c07818503240e076601e4100400b4420b080150342c1c40f4404101d0410004d002d0270f29500d0580c0000c024450564020078500303428400e406142c509000c0100c000c00940d400081c41c1483c800f00c005849a45843c402141d24100e0f11501000a0074040464580040403080341d108210043c1011000d0f4040d0b607003513649440c1280141030b1405a00c000240c5d1007814002000040c032040252035070b0350b041c02805010100c5006020140b80e00c00e50061000500f03146c403410340c1c00e20055103152030b00307060302c6c0000140050501541d08581040d041d82c0340c90080c0002240001662180503410307a0b00c50620300c1d400d202c0b2005c0d00f40d000140c400450690380c003403243d81036241d0040201061161041000c41e2a2500e4640d4a01d8440d6000030070100b111001410903001c0d00c8000c220354030355490f54000800034080070300942000000024444c08548d985030031a4a0349621509642051500c4d040461990070b0b0564 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 148719901 1250 148718651 148718683
    0x901021f050604060f0b030f0603280b070819110d0207060606140711040b010521011e0f0513090c090b030c040c0c0b09070b0c010204091802030304060c050a080309 72
    0xc0d010501c4900305c00741030300351204580003500710b60740c108903002904800b420f0340390103000e41804107540e001e21030003600c0a480004140b2041d418586000c2544140c010105000c0241c0503040c81095144058034410134407200c20040781803800340211500e0703485000007486600f840050420304000361900241c0443e208d903252503444a04034105c82c540351092440081c4210300281c20924685045d9120001803481071510b282001d81604072444810745104446403010200001008402c00c54941c0c00d80001c050107140000c5481c0520241d80715403240202c1d1300c2480c4207000740d055641c0a611540700942c02c1422604580d43d40e52038440144144103426000b07010306060460241458003402103042415070b10003102c062a500c2e050041080540015018000c2d40c2c0c0004000e54680041d01c01080710714001039545207000c3c2003108541d404080072110441902c8098050b030b9000c426241220018202919020200d14005041c0410310340010200d90001c402d00072880f0001543c801c0c2c21801030b03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 148721151 1250 148719901 148719911
    0x5120c09010f0b030106030c0c0c09020702031209010c030e031516020d05090a03020111010e011e15081504060e030a0509040b01090f120204230403080f060d080901021f050604 77
    0x22944095645060243c0c001c100010001001000d20a81c4000420b0140d80743c2410380d4840340c0e5488010045c541c1c00041c0c466000702d0001705500d01030110508410781c862440c0d1500c048080043c050405080014003480750945503450b158605110710081c20410404650f42071408101004400800b1909800140302c0d50945200c1d040c09501201c407035160040c000010186144d0044078008111100d441c0346540715108941061400d019407111120380c4980c1c249060200e84690301210030400c04070600200e01c11003000800d1000c68617208510040301c00303030543e6650382481405001c0b207100001c9203110001c0d04c403031010388c414041c0581d0314003100c2c240510710500c001110b0302081402500c80c03064040c2c404102c1004480c0b0200074080c80a400031074804954401005c41c81c1003504002a201040800c1000f01540301c1c02440d44401103400849160805101003174042d184508000c001c2c800008100303081360300070480210b484222914a016014a4001090141c0800c0c0d130480c0c002c038140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 148722401 1250 148721151 148721159
    0x60b19090b061b0f070909051c0e04050705090f0301090206030c070f0c0b07021f0f05211e070c08030406150b0c0106150c0809060d060512060907090c0e010e0a05120c0901 75
    0x10700607100d0240e0040024142c800c103074152032607048080e22050080c4485084003490ad9261070160600c5408991100b40c0c8915807a01404410003138200c280c2e201e41d250a054800580d159000d598000c00848401e0391110746502d007800035901004030113010884000d400064000340b2000030007030300c1c0c403d44050850607507143c400304d036044180304950089501414001d0080e0321a0b005001c1d00700d1040c001d40000d0f49000c4001001c14016103003640b96541c40c0500c0b2100d085512982034000b9801d203000704038a215078960000034000a0300c000c0c920360301c40b100014181c0b40e50001c00040c00c03104001d80c0c0c0d1103000c070180d00d008000a101e1090510240d100140889000e181e00300030403900499914a0900d08104200131a4420000251601c1d03582d04040307865241d600d0340070040c2e041100102058141150340e5840e200c81c2e9030042c0d00c0c003403c040c44101d40c0c561202c3c030324144503828205600d03c0c1001740001b40c0c080d41940c1146030019001201e205d044031001801c407490440980b5210384598803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 148723651 1250 148722401 148722419
    0xa0e06030c040903170606040f260d0210050c0403060509030d05060307050a060804051e07170d0909020307110607020307030905091b0309011b080103060b19090b061b0f07 75
    0x111101901243d80b00c2c40705591790103c20401030744801c004140314900354486010159416198004c0b1035000d604411480d4102c0e8040c1c510300c0d40ba40b42c02c0040c0000030102200a580314122000c40c81181e80341e001003000806a00142c07405140d2004081c00180707014800703030742e80c6c1d04048002503410b814040803c8103424040380c14016a4000740280ca001070811405890810015200701c07114030501e00c00d14030ac6a2440480700c01451a0405003810034640307103070754810040c0f0025a41441e00064815006290400003400c111080703100096201c0d51124015610309100702c45481c810301400081050301030f400310007404118820307120407912030f44450078454400b03c2144c6c54480c8005001c219448821102d000c0d61307114140b6000828140000308841c14800802d1403903502080c007207001441000054090002d40810903654041c007005102c802800c0029540f10b00ba0350103507140c4000080f52143c0003121b08106d807116004840c00d4081c02e4141d40c1e01120301418185000c1e4150100340106 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 148724901 1250 148723651 148723661
    0xe0406030309051207090e0717011104150519031e0b03061f030c060201050f09060907060f0909021308010606080c1206130903030b0a08030a020a1101030b0a0e06030c04 74
    0xa0035507650b0301d54904150502038802540d1100e03024a2142500000d0106d8280c087c100007480d07618041c0c0310300e515006441d09000c0001044d41890b904140c01070b91030307e80c12401ea404031030950501041314101c0003415946d5204800c4407800001c69410000562130301900b0900036908a0100c444c01c0110240c103c004039905003141c1c590680108000ca011048107500010075075204044500c01542e070ba68a085240e00d039a4003e0700580d458000700407201895030512507220f1a0140a042940780233039070541c480c0c62a0003001c00340060000c507140c10502c103d1141001c3c084c541c50841d540d00e1041826407040d8214800d02c0201d600741000480c038288601e40c01ea01032002840c4050030a02e07074bc420002049402403a4682142d1407048017000d0000034054a05c03224002d440019400124405010780e010041d04042da50b98410400c80c100950300003146036400d80c224640d800c0101c0302c00d004a024103103442000350f104004c04e001090100039030140d0b5014800031412110162940824401550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 148726151 1250 148724901 148724903
    0x3020d12232706011202150a210c0503181e0a0b070c02091303050d0f09020102010c050405031e03040504150f0504060e0c03181911040501030b07050703020102091f0e040603 76
    0x181005004000303002c40e000056001c10b10045c2000002100007c40500c541c200c047c00d08001119240004000107280111000d003007202001884180280c94020340780d813101400c80d102481d01400a400302a10078844281440c0c0f68404601c4c1c01100558260f0307680040c0c2c01d040e0380070360b40500455500c6010361044040b55070302502040040d03031000c4449004a003403440c00d03001d1140410650109114501c50700e5501d98141d03800081c1880540002800c440ca1401400107120042005001e1030b1350001d1880703088034224803001c0000b074028103842d00310f0140303601094010f400c0181c800e940303240340c11001c41900d800d540d100140c59604d4040000b50b500c6441076070344d5540701e00c01180c00368513003030015a400103080480d12040300340024181d21302261754000c81d0004541144100c20401925007035000c50804440502141d41036445d03c0344d80560107804c8506002c070000300d00c2c1c01c060007034065a518080040016541c02c2e800c08142031000412200600000c411098505080c945803103080207403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 148727401 1250 148726151 148726153
    0x303020f0309030604030c0809090f01080114010b180d05030c031c0203010b04030618021504090c030207050d0e0a0906180605010c030c0209060112110c060f0403020d122327 76
    0x2e45c845031800e50740d0072241201030780c0080c4100300450f240e03100c008201d0b0040c06d411110700110341c5811007503400c6844d911050000014030303000400419103100181c030064000c3c003202554010b00500003492a0311194001885400007060b04a0342d514040090035241e50701e480700d06200020240030703030203e01c42401006a022002e0005002158155100a90407041d83d040141080101e4001480d059405a90004c0e5040c0000c0e040c469001207000c0d46030b08400a06056082034002c4d1f0b43c064681034182240d50400401081115081e605c2c007800740001d05006401300815074031031200402c00b101040c0c183e100f00741441400102e6503c2100841c1e00c0c1c0e501961009400c40c503550070000f00f00b1028001c0b0f0b040080744402c01707584288510503202e00030140c4030f0306aa0b88030f01129081c01c1c04401452511030500280c03c101c0802d4000c103450012048624214800708807005101e40203128201d030a6452a07942a0f15035105110040e6903802000c0d01c5120354105186c000301d034008601c20107004009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 148728651 1250 148727401 148727413
    0x209090a051f0b032b03091e0c0302060a050309011109061c0605040204080102070209060109180f02070b0117070b180f06040801020703080a0e062401021509070303020f030903 77
    0x1441400b07486940c0881d90080041610420040000d03c1c01c040350380d40221003c108040c1001d8801c028000303495015a509080c000b2284640b140c2e94226412a50f00844d080c0400c2070504210f48080600040c1d90b0051640f41c444980000062940e002211041d00d55032900c03540c4813200205400303903041580014a000d103000040a071040000c43d40010030041c2c01d0700d507038011916540300c0c0040e2018141a000058841c2c4190042140300100605035a0621084800500c290140c0b6070b403201008030146d00100c3c00a650340c41e580b0007403294010241503032001e0800803074000001c5494151445a007001c442c10305850b00b040c02a24841d185502d6042420114003442c4c038105600e070310641c1c00303001f00f0321410282e40f006818260384c401682140084e840c40e007002a1601c0e5071148044102c0b0b071200610282c64001c0701c045024089a960a019060051094105a10801c02030000003450888c117006410b08184095580c2c01902044001d0700407200800c40b84403000013505c515610080013419 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 148729901 1250 148728651 148728673
    0x130606200114070315050a06050c01050606090109031e02130606030c0f0516020a0305030711010f26041509080a030b010203180d1b080d1d010f0e180903070209090a05 73
    0x4024000013125885d41010903200192581e296550403000300819240e0f151fa0760483c00b00c0608503400242010f1062400384030400944c0d911141d40c0042d43d5000396130001286500d40152401c043c0c138078000358040d144d0014a6000c504642220046840a407000d0202485d0f1820a42d520981d480c0d0400024800303000e20115100000c10460f06580003078202c580450b26a00e5850030b42e4081c03801514074100741c0c10103403203a581c4094010140303000fa2400350a4104074114112602e0b030034407000850b5030001c0c00402e0610504c008860307000d11540d1810844c141ca9843c043d60a90042080003010a2421b01ca840049d40003104440d001c1410540d620b0000340352004106804045407000e0380c4141040018038607680d41740b80d8480103884204010f21100c0d0041800030000110052a0104082c0c04c0c010080c082e40c0000ca504481c003094201114030300301100c0442d0700b000e91f008034184401c0c50103082c800580320100c01000304d9402551a5001d580d180c4c01c5042e0703144043e900041040c0d00c1040400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 148731151 1250 148729901 148729907
    0x1201050f1f030618050105030d0504060f030c110109261201090507050c070e041101090303050306090903160305030114040506150d060e07050c011b0207031113060620011407 76
    0x910700c40440c10300249081c0c48400b8050040404094201c40540c1ca2005200c43c1c58200070060400e00c10703190544c981070030f000004000c0720034401c05a003403580b140040015140a41c0383c40382d801003184000c00000d0050b007460091104000c08440320425074000500b02d10304d9010855a4342020501c2c01251a407030078814070001e000c01090301041020601440300e07400c81c14400341c0028003c0b504070007587e00b041d081940c230710403510862605201020380104002504003041d2603122800f250000596a80c0546c21402d42c456010001801c0040d610080b04040c3c000011750305071403180c60010a040280000c0c4411250207035402130348104443e5030007081b44a850014101100f4003c400b05400e5500c1040e80a6a5010303960a80405c2d00801d002404100903c41c0642c4543e680120300c101000880019407288028000a0032017000000c1d59040ca072034030035488100302c0403941d08022440d540d21008010010744045180f100f846020f070707120b10804c1401400301d0100f91320340c0b544047c0c41e100c0c015 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 148732401 1250 148731151 148731199
    0x90606150304060b0a0e0a0606170106030b01020a0804062007030f0b0705040306050a020d241206021c060807060207050a0e0a0e0a12030f05160f090909081201050f 72
    0x442e01d81da25044c00c105251950800c0400a140c480005401402c1c03c00240050701c0282c0c1081d02003243c0101550340c50709503031106504440c80c0d41000104035442c400100c3c14105141d02c0a0000314001400042103580b00f06c600d00174540c1204c00014080b071030104540c40300341c580310151240428a80c1e00380030803040c0032001e40040850030302524003503803540c9800c1596403c807154614940c0c0415800301c08600c9000d264200c02c0c40360007010032800003d9110400700d1072402541d600341901200201040701946c1261803401c004211a50f1a045c6100c1802c00381c900d9008103660307030040b0ba0002980c0c50000400106540d0000d003407103d001e0400200a5480c03500929580400b03458510209044130b040c04031514460049244d165400c1003624041d05440603c1125030006103010304008a0300c4005e140700702c09034042e15151600403c400411100840381c0c0d04406100e51910300c0300d00400844600400032200c40340b1003100c1c20382e0b9800402041e80300301c0f840c1541103410b015444040303401180c02 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 148733651 1250 148732401 148732403
    0xa030b060d15021201170a03030b01120204032a08070e04030306030b04060b0108131e020409051b0108070e0102060a0b130f060302030708010b0319060908120f090606150304 76
    0x2403200c1402460310b0381418500c03103030302003440c0583c001007005103c41000d1100f40944400b18a8440c100d00d0301040ea81c0da10f420325809001c0550b11010a141680b05016043c0d44040106081d0340341d540b642001400000030f24003200001b40c055095162907054403098004aa40080c0900220391034150389104111008000f1010075599450100010390321001c0203029901420f000100c00d00400c0024200368000340000c1d40500d107031035040b00040c2c0750354000040c400c6011403d00c101540ca201050151110040042041c01000e5144420410b06501801818426a070300c5e070081d290150140e07100302107a0354241c01038200d1000500c40a01a4202d44401ca80140c00242c103611450200002c58800d5150b1020283d1180300c1081507181c1005124082c100c560020085d03109282c00003a9544807048136030031030441e000c01802c28001c40741d2201e40c880360426402030b0b1751034103202c03200d0110008807080070390010041e010580701480025260302c070395000351450a10484041c100026908001c0c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 148734901 1250 148733651 148733659
    0x206041101091211100302041401120204240314070815031606020106060905040b091305030408010207030509100305091e03090d050706080a09020a051e040c09230a030b06 75
    0x29001a4000742c0405044180d400350074013a2120568204115804501c2c0c2c0f9a01c0c10180144010702c0003800e4120140d41701c102c2420002621a00721020383c0290059910150118103079444c500f2065840c0001c007a490308169804202002802c200203802c01821348803c000141075000080c540321003e0700e0034017526001011680750b83c00c5407d2040c003080c09038010340010703512184204203071600030030114041c0004507000c2c803017004a0004100303207400041c6084008840744100105001040c01100d019120903402035544400d6810041c155600c400c2c241400f54440918214595221b0320840740204001c0f000303401e0000c0c12070201c8500c0c000158500700303680002c2103452025503e08062260103880360b005810b01e10300e0b02c0380c0603220480045c40d9815081c10b002d480d800503070b6980718400c02c0c4c039411124400203200b0400b49130516480c95600a800503c4e041c041606907421200c1102111107203101010828240d1120381c0401e207030000c2d03c2e60800c5421509000040c04183c2c400e900c500060 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 148736151 1250 148734901 148734917
    0x2070c1a09031b011206150c080403080c0601050a05060c0c010e0105040f0f090e030a0e210604030305040b09030c0307060506010e0a0f0e0c0405030a0f110d05010b03100c0206041101 80
    0x1000290030300490078100a41040500360f54085941c01803170b032840441007002c040180c90b240900c039194240718400d402040200e007440300802c120308d000179034000e5504a80364684642d00c1c0740a4980e2034800703010b501e01c034401e400400241032502c60110b403501417030080944900b00c0c03800010b403101903165200d82d050160030b120120309210700811404c0100011221214000d1500c1500b5044079a01004694241c10030440c111485401c04182c1003000c00a4071005070944000440d5803000001e2155008540501424001815410340050340924001c0040a5032900d414080c5552486042c20500c2240c00500540c1c01180250713120b9a40040107040510805101e000060304604458014451000300103100b440794000100c40d0a502060819040789040e081000080c0c0e50310305420014040c02c0294201320421811900c43e40010402910500510312503141284c0031700a43c01007140a885068110b4003800c0340c5001c0c03141035441d29001340c101500d5680f030720706000001c01b00701c5050160300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 148737401 1250 148736151 148736167
    0x190309060b06161502270409060f0c2c0603060d17031005040501060e09040c0e0114090a0501030b010e131a04020108090708120a14040806010302031002070c1a 70
    0x84000700709200003c402010344840d58a819032071600100c4a984065205200105442811110040609500550340c0c0c000c03401c900001000307840c10340b100031f103040e0612800c0c0c1e600074225080491502025141e80341805903070002c140d40402c080c129141d00a0003151f103404036080810040d9004280a440038000d88456104e03840740e11440c0781048103412002040190601a95106602400f41200c2c244200d501d00080106101c02c0c035542c2600c200804004902040442c1e662140181081080143e1940e074a0902c40c80402907081c0440c000d440180000b43f8150b440e2107854180e0340e2007810741c1620307424503a03081410301004101da844440d228000d03d0201d194404000c01c80c1480b1480300980c1c0c58030b40b000415410015100c1440c43c0d01c0510144054400401c02c196900315503214680c569140702d500b2a0644034910b55041d6000380040c0210b0a454081405410baa009800302d404115400041004a100c0c069018010044901c0244607103c5041c0040c1048110305101500b86424 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 148738651 1250 148737401 148737409
    0x1e0c1803030c031403040807080307030f11030603010e16170f030403261204060e0a080d05070e0604060903030309020112181101050708030103021908070e0a11190309060b 75
    0x24a40080e004640d80b5002c010406611030820290007001044190031030415039210191750142d21402000547d01100090000d88280d00c2a800ba00c0d1400c001e100d020320018400281d82d0040d40e60501135400e00c42d40c42c8c0750080000b20740c1c40b00344199840e143d41c01c0c6000380c90604c042010104030098000e00c000044040e804101400c0070798000c4034948501c0d008620440e130108000c80654034252400d004690100d1001c6204580c030980248011424100b040078803800c0034085140101040c40200719815800c1c03e6034009882004240c4400200e45004000c110743c501481c401e05002602104003800020f01c0380c0c001c4a4050b10604140c22072a900d50207090540c1c1e9055011030300100030b00c0c8250207010440190040cd83c0007801c181d4036018442d2590f03a20f038401400045e000c1c009040a0304d4600b098040c1180061508605407941c0c02d444401c0d03001000d0081d903d14820500b41031110310610f4a110444104240c61002185910036400058010b0611000c0950f0070682e00c606107221920f07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 148739901 1250 148738651 148738697
    0xb03090d02010f0c051b0f0f0f010501090902060a032003040f060b01050906040314030d020f120c13090e0c03011104061403010b03040308090f03180f01031e0c 70
    0x860405000d921265503002421a510210002d5885090050440c481a081002c035902d1500c10b0410300004038880c45418608901c0e044952854404e940b505401c1c020003080c6d00c420350103510001c0c015a40c4c3d4400030001d41e202c0c4100650b10000402000c1c404901a5109601c800400b066a14090a0403584105983c004030303800d6400801e070068010030000705201e15401c00809082c0319090901c5100892050300480c04000c100c0c990404004610b42c0003042500c44d410090b0005558901364043c07045010b8119440c0e102a000d0900003003006105104183d6400e940301910314041946044001c5010f0880402d105480c0d009416180300c0c0c81d01c080c095107113400011262550394511344000140303810140100c2200540060005000d08a03079941103940203a0145000350f07a9440744d42800f81001c0c44242000c0781403000140ea00074510044041c160300074000c0f107001100c410f001c00190252801ca11030360262000040300f03600000300c29401207003030380c02901d0421a500c209421003102c82d2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 148741007 1106 148739901 148739911
    0x9060703050c030a0207020f0a09060f09110708090d0b090327030c04050c0f0412151424060f131706010501050a1101020a0c060b040603030206041205040b03 69
    0x148d114004002c0c02c02006110141d01d5982e00300b010010001c80c814451381c64503e85000828140718402c40016a2600f03400a14260141d595904a5440000c070b40303a2010580854601162200b00c801e4460346061000319507c1b138140401010009440c82031070f5540843c0346c3d9000309900e01042000c0ca0400584002c11035440b1416020518007404003120b11082000c83e0000701c282c841031721200c015000b0610070880b80c01d4000b0f14003e480746a242040b43e40b07aa40c0100300518514400e04054075041025950303a5041240043d0762903114150040204e90003160704090700b07411480040c010b00c2507501107040d41802441d5a03888482c1441081d06120000c1901140940900c0da240400c00c6920000c40d03451403980b00251009002100039180030b460540b40b465182002d03c220420790307030190014503440e0348030750b40c0103802d40c006000b9008000d0103000014000850754099070140c = true := by decide +kernel

theorem cover : BRFrame.Cov 148561151 148741007 := by
  have h0 := BRFrame.cov_init 148561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 148561151 ≤ n) (h2 : n < 148741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
