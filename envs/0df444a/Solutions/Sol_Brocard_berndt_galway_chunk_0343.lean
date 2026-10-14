-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0343
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:18:48.606996+00:00
-- url     : https://prove2.me/submissions/43e26bab-705f-4b39-a712-49cbdcac80cb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 61510794 ≤ n < 61690650 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 61512044 1250 61510794 61510817
    0x10f0501090902250605010801050106030c020c2e08041401050403140c01180809010908120a08100308040f0608130309060c0f0203100212060603130b100308030c0c0d110c01 76
    0x8448021050560906400c104c8050041c500300e4000c0c6803d100e4031006510700000466071230f119004400310b00025500421194800e6001c200c5606042e89140700104e01442e01c0d003800ca052560554034500c01525210140d142c642032207510403401540b41903c2e41d261400700400a9003181912003010500c6400c65100c0c10440d080600602c80d841c0d079405900500c00042c400c111800c001819066000e9075002e81ca56500c0761000d654900f5400750002c0440c042c44801030721441a0f100c107910030003408145120a07642e445502c1583e019410881c07108111140901c009a005040760b84c1040c621f9010b0000010b03191001070001c081070180c88200b11303d842d1500705200c9412203c0e10641d0700102a1100307540c104800e0350007584600507143c1c54035010b20000e891850003009891140300e5410450140070655604c6410400780200140c0070000c1802000c0045103040000d10300c02c4130480090b5036240031036848686072841c100721a02c10001a4118849490000300304400030140078200241c1441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 61513294 1250 61512044 61512067
    0x51f0f0504210302040b03150102010b010216090c12020c030a0206070503090d031a03070f0f050d02061b03070f0b0f010b0316050901110102031f0b1813020c0604050a020306010f0501090902 83
    0x12032039001c107002040100900284094000f4081e442302800d800801591100300016038540c00034503811519030840300c00c104454151600710170700d80306461030500d0b40b444006120300100e80026120f080c5d19440447c0b8080da25404000c0b49401201c50b003041c0c3d00f0b41c07070301a0341d1903a51140344d400e120405480e092202146802241d060101800c01000c0d941c0094442c0f801031003201d2207100b480030b2404103c20001d1203040ca1101c1c0101c0d946c026004c603103405481c00d20100300030f01d8180d000b4864442040402c000c9a8081c0c69900510303c42e5220107040d04204828504100c410707007281c1c10243c1d080040c4a118141c040341c05524000c5410000d0b1100041300068602401c102c040402a500000400441e4a040d0208260121221414400c0305443d044160310318064160101e401045110f92800145403c03480d0000305051610094038004500c0085820400140c80855441e030050006200318542400306c07a015080d41206143c2031460304000030051700552060002041d4001146281315 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 61514544 1250 61513294 61513297
    0x1706060d020a1d1b04230a0b07050a02031011070204051510020609010c1112130510080f060609010e010c05070b1303030e03070b0307050c0a051f0f0504210302 70
    0x3407a041d0000c080f0604800c1144501e41c204035860004541c0600d101501030500c2420b4405948040000f1218410002c400ca05466101b0900e030340e1100200000040c1c01e0003403c010300e0160300c114040c0002495510500d0314140483c404182c1c0ea0b0304104140d0128500d65080c0c3c4c09050301203030042400d4a80c0c808041c5980120a0203e070000308444500480a4000402c0343c02000d096000f000401030012044a10a1204c029240700f500300044145251075131402403da02e450944600419690340c8001035144015500b240000c52030040c1041241c2e485c43c80d10b260701c41c100f580c03030f1498400e000700020301b0702021100c5541442007004143e01031100420041018040000784607540d20301c40301a0650301c0a407884110b00041c540b00802807581408904082181c0d880c0c20b4842c15512095015140e54000c45c115210038400c90440707002060302000051041d2129040d4510804c006a603103006440980496094140c100004c4c003001468540111600c81c500c0f108086400f410010101d019 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 61515794 1250 61514544 61514549
    0x40501080f06010c060513030206060604030c030b0901060518091504050601090e03120103241104090e03070c03150f0e0606090c12040507050a2414040e0c0301050a1706060d020a 78
    0x40d46c40c2c181040003160031210142003003806a022242103545007003c10403a4400d90100034000701d00444108001758481c940c0c55001480304001007880b41c4c491001c118501c50966500d241e102c2940188030003075000b880a0620050800100c2d0203d24140d15401d9440d00c040c89081401969003c02c0c000b914010f0050710441844900710000715656801d2031b254412020f6202d41002a0030100ba20042841c0e00c9a42c4041f004500750310f04180c13900281800601c01701d80c10000c82d000c10010000040c00c1c40040c000030b14072900183e50807001d41c4095600b2140025905031000345404501c0891410010b60243d101804a80752142a40c0350880340e440f5001e0f4491010000c16000144000c014020440710150f4030b054402c2018907030f540030307401152160380c00030040c009180f06922580c01d20038100314a0504e1760110382868a80d940002c444416412205403a44440110052040d49000f105c140001c0c000c0b5808681e441d03c002000e036840e83c00c0908901e2045003000704000440d03c40c82c07941c400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 61517044 1250 61515794 61515803
    0xf0a121d060c01150b1809040c03020405040201170a060e090708030d09020109030507080a0203010b181b0c10050a06050402030912090d0b04060c020f0706050a03052a04061103040501080f06010c 85
    0x7050383d6100001c2117150000f030090340780040008000708080c18102c80301441140c00480b1869414507540900004040290090f0b0400030b11181d4060b01d010480c0e000c5001e40f441582c00180320b440c0c070358080c40d0210054040011500314020421580d2400402d840c04450000c400095002c20b80c40140e0303d403002c9600c0141079000e40200003512590110f000c00c101c500030340081c0b0005140e542005031b4604031078411030401021001051690036801da1600980b1480040f17503140c402c030410b440f0702e040b1b241810005071a4840040111003202c60040030001c0c02c00361070030740c00c1d400c09004c3c00740c45040407200322018000120300400180c0c7c0340c1c010300305c101c1c0d08800c60441d94109400c0c1040a00070350308e03108026219003101c104031341380e00181e4241120201d030b50300b42c01d11403e0300044010340360291a44000750081c4951032545099240d18003104000c20111603a0346260901c003602c3c44207803851015030340d0070038003007001940d80004201c0c3d03201002c541d61a0103a601c640050f00c140403004005403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 61518294 1250 61517044 61517081
    0x2203060603050303010e01090501050d080a030b0301050a062607120303060b0d0c26060d020406171c0216090207051c050c0c091501050a020f0f0a121d060c01 69
    0x1c2400780202c0114140c0b8441c41c0700f50103581e00c1c1c006440642d00d0078030034250032032a00702064022400302000740a04481c1c901c0d0201b840e0308840c1c002800d588040d141c26a99503540c00c0c0800c00c0121b131170810410403003501c001c000076050514010740c40d1000380c0305201c0149000520f01c42014820b900c41306c05004007500b6151294800c1014200420210400b440440c500c0c00744030319001b1585500d01040d0940da000311a4996407001400070880302c2400882c3c00c25190400420508411108110700600400003040c00100501c15003200301142d40507a029500444412825884292a0f49041e05d804150150f03491000c0e140051800300709003c0d10210111007a4100c441561110060104807021000c42d89480900c03001c10440c1d000c1618a280310142103003e0004070f50165015202044a6005417081540502d201d141040080c00035070500d034000c00b00e075004100380880b05642440c0d10b0301d040c007584c081e1a00510100e102070891036200e0384011407001e0500c03d0942240000101c60030142c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 61519544 1250 61518294 61518299
    0x20105040909110a0501020a050c01050904180602070308060d20060c010c0c11060c03030a05130c030807050607030b090402040509070b04081006060309080d020903031204110306090607020322030606 87
    0x304420208800310b00c2070404c84030001d0b0962001a800700010780180141424101000041d00c10307901003071140c2e801503154121244843ca440c54542031650040700056135a1209290041100d5001819a485181d0403041030000c10000030454131450700300304040041c600c1c007900182e6103000c3c5c509848560341c03d140c514038900307a101102110b401c1c0702d80c0501840c10303011020080c0034060018028516841440043d040180642015820000310865401003a54545440030440f0607500161683c0000141c814204101009101e500881a10b0104400307024400001c840d88006000a80f01e1901c81c004a80c07990403e00691005100c4201b4503591079980307840c07090b1100101c1010440c2e581c40c040000440302c4c081d00518242c0c560001425103840d5030600743e0002074100c180c0403501840305010520402007903681e094040c50251010300c260261400405151404c000d0030381d46150049024805401d8000096441200440d01800c081010b01985041c00036450341c00a00101d0500d0b900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 61520794 1250 61519544 61519553
    0x20a030f020108060108010605161a0702070f08150103060e0705040e070806090c060406050703030608060103030c12090b030a0b0f27010b07031b0204140c0307020f011b0804020105040909 82
    0x10010040d100f0b88402a2680d60040151004c400900c01c841c0440d804115402d2265008584020301c10311070340c80340000904208c0c840e003030303444121740000159119400030300005540a040e0801001014000c0c000d0202a101200e60814180b000900f8182c50760b0001c888400304ac072502000d090b018008109540165080f507543e00070031300c2101690301a5002050307040d0008038440c864000041d26152a00389082c00c1201c090784140e0301501050758400010031034410510a9074000d45c0265502c071503801481c103100c2d4503110a001904240400e81404000c0c070460402a01e0b4003002e0f12310000381c00076072003000c80c071844103c0300160703031259079260480d090740d088038100821030000800000f4143c1c1c03100d844107005e1050641c003401003420701d120700c0740d61000786505115040c4090300100f0346508181c2d2126183c4c90940d000380c156003000c003c02000c958100444400070721013000a0000d01c51300d81c07803184601a1484180104450900082c065901600490300200840c6604110350001401d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 61522044 1250 61520794 61520813
    0x10c12030605011209050a03050c12030a06140904020d021203090a08010c020d02070e04020907090b03070c0203010b0a0506030606030a0212040f0204110405060d0507030e070f090518100203070c020a03 88
    0x50b80d001c1406103144820078a05803095025242c0d00c4002840c030b050054500342c47c0307030700087c800d0301b554030400e8504214103940070043c5011b10304465021452904113800c171800b900301c0c0c00300540903041c2da030108030240c0e0f202c0615010301501620110400003100e0103141c01d6200e85a41d490300102003140000c1e40e903005500c4185041e0881c2d090300c030074600b606e00c126142d454a102d10111704940001003405442e05140d00c2d60030040c0703401c0c000701041d600c5105641035001102c401000c50003008010f815804c3c28003403074070500e50848125070210700b090001600c602000c0c14103401414003200091182d00158100c03480092680c058030b425203030a02e030000d131803000400208d024030308000311001d1105d50724003030360250780f030050000c1c2c2010095581d100c01800700519407000c0640712203008000390000d01104014010700783c1c8010440b401c1c04203a9003940c0000d046401107078035010360004a18070104100000074000300380941e07261101001141e03a8003003040080d501104403000007082044010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 61523294 1250 61522044 61522049
    0x61305090603030a05070b0601030b100804030305010e090706120207240e1209010e0a05100504091506020c09042406030303140412140417030318010603031706010c120306 75
    0x166001241d54440d4149526030152042c50000b1840c00e11aa4000030307009400103500200614000a11200010005801c800805c02c0100030410380c0b424402410717410300400e80904844a0101d0313490404049035aa42e000500c40e13501008050206000e10040d29011561322a0304070a58070741c41d0000c8048800c0310790310b400c1808000741c68601d48500300e4801040800c003007400c01c056541011003050041d114107503500200ba5221501e04000310380d03070703907034920600c00501c6076510750752a60b08000000d006c85203c030540c0c08500c04915010130020782c1c0011000c264030016202c0c0c0d207803901c8500c3e040c001256403614a0292940c3d900c5140c00070300130740e0b004104076030007640d061207144051200d14220500548010f00001185030b50b60881501605410541d541c00844507072501e0b036a41520384420f102c45040c05100c0d0070000600030400c900c685034038400c4003030100801482c2d01c0c540e40070305a000c0c09800e40e04044c803181c0002e0101d0b8000c0e4014481c40741c111903020610041100000d00520060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 61524544 1250 61523294 61523299
    0x1020307050a1101050402030309040f0f05010305160e06060901140d06090c0314130b180f01020408070b040f06120f0f090201020d030b060f07020f1207050102060601050304110d02040b061305 84
    0x4440001c2c01043c140189801182c010b4080c51400c00344030180406404140c0383c148442d0381314105d1494110a44c49841e00841c0142d0182c0f240c004100b4851508884940c000400905110300380000c1f40e0b00d1104441422500f4240510f108080c14411400790103089581c10500b80780000000d1503c166822500f400c1503241d070100000034400090481000065440000b060400751040380007841c2c0510709a080700e0f540c1030307c00114803440c1c04c823450452042c0418070356075008030f0308001d03094042052402508101d15075904040c02e0900c80c10845039103214890810203000c0c00311116501c0e50740641c0072440d49130014000d4901a2010102400484204038014400d0920100c9114072034855217681e40c07801480c840c81c106030b11040c04115001440180e80c8086c1403200410030b03a54035141052003610300c0c0c0103884040d1a100000e42402e00c01455a414030008100300400114a1128070010860031100070b0351180d11400424001d206d031044141e000940000c458900d40f00104184c0e0488008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 61525794 1250 61524544 61524557
    0x203070606150f030b01020102130b0408071a070305090a0512150c03090706080910021c0c0302090109051e03100e0f03040303080606030a020c03030103030903030315030308131401020307050a 84
    0x807110b04681c0884180141c0380001d0f2200b030040742191094000c81580f10b0305100140c1000546044100c0342c2d0038070b9100c10341d0f01c0e1b8005020080e0480610180d40241001d16032080c01480641c1d5005481c4502c80380101088400200c150700c560b00c1700100406050003612450799101c51420b041c2e600c84181c51001c203d0f10f05080000c0c02000400704076807040301e00d50054280c481c908002030710540c80c0034000800900443c01c240078170369100c0c4041c1c0450010140d607403400d000100202402c036804410150109401007040c0e6855036001904641140d40c15520130702001071030000107008104000140741e0600840e410528203405940140e920400400241e5508116400c2c50642d644200c0c4001404180c0e55000104036180c00c00265600c02c89010015140a03075400070755045038405d800440100b00201818000e0503030500c40c0b16411503907024411001e034191b0714041c4c80e5070402051000d41031040d92a2070104070882c040c103540210303064005e549a06044401422076040300864130006400e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 61527044 1250 61525794 61525799
    0x1204030809120d020a0e100306050109080102070c0506091f0908010b1f111c030606030b0603150603070507080705010e06061f03020f0403050f010c0e030c150304020a0509070203070606 81
    0x2c81c010350b24641024000b4940b0000c01544006500711583e00401e00c11503180f4141961142c003100b0901d81841d50b400580d040c28000050040e0140780c1101403240e1040c08840006601e03203003682e050f0b0348101c1d200c4e40c0303522904001507003c2e80c2c60b01032424801998030320b00f015a5004036a4200f82e42e5070170000c2c85600360250901c90038020652241900000340c00d60541c03198000e051900903800b060040d98011008414170b02e2511058014800000707035144c2040140d990706105006c44070100312243d51450400800d85d0027801104c00c0c0003442800000042020a8040c2007110180c55100180540315203140c2003083c020035010100712407030b01802c03001861500d00a0004000110040550020341d01c00003800c0b0003e40201c0c0ca181011300d03003040b021004c95410041da00d0000d030400004506200c0d103000c010400102052484c0c0264003550b5800758960354040c51a401a0701c050700c940d143c0c3d0703460001460001c070710350210b504507410030f0070302c400b082e404801040c10398050700003440000d6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 61528294 1250 61527044 61527061
    0x8010c090503070510080a05041a070504030c060809030a0e01091205010506150f1605030d050109020c10110406080a0216030207060215010f03020105162a0503150f041712040308 78
    0x180c545d00300e00021704080c0000d840400f040c0c6c4400d4000d40510508c001c100039100301d1f0050103000341c4250001c100b0200d001c0040180311340c4040003a01e40d604c1c00e170965003030002200d5901d00910f2032007001d0000280007406664402c10144005185a059a10480c130a90500398000c0106441c00c1c0c2c0900501c3c40301808141101d0115092110007504143c50203140b41c0c5c4007115110342c0f040031240c45c0010448054114090300403140600842200140d40c0c1c02120101484c1031400c815503540780c0e09200584020070510010348040f40c0c1c0d00d04000f1100d6440301800fa00034400d92a2240740c40c100140d81c5018198001501410354915400711a4226440c036072180d9542030910070001f194200320400d00042d48600c020345200728810b10494402c1030b4036504c081401100150022841814510031040c5000d1010440000c003410b50160a08403040709044510b424020911840f8004090200f0100900c2e003400007000c40c0140070050b240c0030032500b0006840c0703041c1c4081d0300046100c0046100300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 61529544 1250 61528294 61528309
    0x17100602011a010e060c01180303241a090102030d1401030c14060304060b01030207050a061a0108090705040509030d110901110303070c031805092d07020a170408010c0905030705 78
    0x182d050719083c110104d0700040224a500c018950300c0517549a8001035164000f10010b13462203446030f100481e03005520b45210101c94208192846c45221402040100051768246e0340c0c0c41701d8440a035981d80301c04900061745184200342c203407000b40e490120904075125494010368180c0e44617907890902e40e0307628441403001e00c503080c1400da0710290800202d80025060349c008078442c00107040c05030034801d26840c0e40c0d00304000c2402c00e540c5c503501c90b6241007a440c4010700c00203813408242011091414030070b0180e40c5d00e80c01405444d0090365944013085161400b041a00c5907190054001d10210f1070604444059811024034030340400c5254030004c40d140703000320980e4460400c5039504001d060781e83d1001c691150451107840e8110001040c0071505440b5400f05034400c8030301a400161200c044001801c100c403e9060a60541d03241c842404451640071803103045c3e2540040755104003115a001041c840d1295900006a540ca0803403903490503500141704d242194021000c3e2540c0e156250300b4003404 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 61530794 1250 61529544 61529591
    0x91d030c0d0507020427141902040504030c080a030b01090504110909040311010603060516091a031b0c010f110a0e060304050102090607030c0507060c0f121710060201 73
    0xc9801580d41038079a50302c81c0c409020f0b070700d0006001060812821030300b00c2c0035809011a03054240300c3d07218584144100180d00b011071035041001004100099110710301d06103900c01c0020310440d180c1e004a02031521030640055400e41000c00582d03500034181d40036004044d6150058046042c4000000d82442e062080f00982000d100116103405403a501308032800c4001082101800798200060749000000d04c5084080d5110304000a118240204403180907041180b407041001804030052042c001da1007a45d0302070488002c11389231292110750503608519030440c5001d10020010605d0450894150025203444031800c60402001c80100c1c0000d5036403150300d0303c01c4c5c007180c50302c0340d042c0c0c85007011001140c1c02409400014281141080043c180354818681500040d5002c2030312010722100307000000003003016041030700c840401e0307a4038101e21700c0c45180081c024951440c080180c090158015400c07100a69190f440203141807588100031204601400700158a0204860b039000c0c98004260721 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 61532044 1250 61530794 61530817
    0x70e010801030813090e0a020307090e030a0c11100f0e100f0c0f02030114010e0a06080a02042f0415111009080705010207030c06050a02071a15060301091d03 69
    0x6003a801c2d40c07100c106580c8044074003002828142c4000600406503c00d01c01141101c0001c0d140c0301042e401010301d0800d283e040264401c0c030b41092107900c02000011078046e106a41899446902032307003170940105840706c0c540d40e04203846407600354005074003049190b10000e458541100440c009024000640013010f40c02005c244174600e5501b5140c010704482c0700e65403042940d44101e100a6021900f0b40d01c0b0f846101581d08040001032081a203001c4216500c25000c01c42000f00d00d1614501c1550b032900c212020740255074415020742101042d602c1d40d0300e403849082e10b1080d10440741e07031100140e622503c110031400d00207010b0442c03070501c1a181e04a200c8810002013152041c0c04d6049401015003900494481408100e1500087d03820300107040c2c407901948504c1c80800582c03c101c81501c1e00141f5a03000f69104000810001e83da0f0440361500e14007807034000760165507108840202c903a0600c7d9041c3d100342e0110000490300b500340c011402a040c50642c0c942c0a0b603d0000c1a43c4d40e01810030003c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 61533294 1250 61532044 61532057
    0x40308070f0906030506062b0c0f02060a020f0405192309010302060a03020c06070503060f010e011709070b0705101a011b050114150a0806100302060d0e0f06040b070e01 74
    0x30f9540b280d005181c00c03040c0104200c1c5003000035061400c0142280342c0c070b000440c82481a1440310340080c482c03271a50400b5800c1c402d082c461903400c0251a054024010000c1607030100b0852a0220700c1c00c285c41c0a440007400c404500983c49201c03840c2d62000c0c0c41802d60510f640d22034030000c1d90400c401c011010101030620342d51a401c641c01c111207900140201001c056007400100c0c240e000070480c003030041c12651070301580d0782000710510005018008a06045c088000d201d2861a6400209241c1d0813040c1d50320440192122044541044403aa00940c8070840c04030b500c03c107100e03011034030410412405008120443c1e42565091016108007999408102010040d02d504ca00300030001c09118882d00c00022004038910380c40c0c06054080d1000d04500c1140e20f00003105080c0115010050f1000000400340781c507001c0e04005940c261400002d02880300800c95225800d241c0d04500008070701d400654210b140300002095407444102c40595010810002207034007180111902045802c040e511403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 61534544 1250 61533294 61533299
    0x14191205150310050c0f040f061103040b19020f2a15070803090102040e040f02030f0f03090f030304121b0b0301140607050c0a030302030a030609110403121412040308070f09 76
    0x900034640102003a00060007009840203151007140100301804030031950800316428030270011f002110340c188400003079008120501c0846018001e40b46c0f0600c82d02d40303644201042a804a06180d01601c2080d214800e500d0000e244031101846040201d403100c1c2e5031071002581c441082140b084c29072000c04041c40802008010800c2c4038001d5900000700c00025113010390341d9007801c02c819400c540550700d00c1c402c03a098008500d01801103155200141d402002d0801c9899841500c0b8450924118403d05d1018510354458805006550040c0f03c0340d104c801d044400341c10000c000090420034480b151b0f01c90800410307965880e20950b1b0503104003000202c00401a402404055031008070107690310711420300d80456641d40c81c00c0320801b8520a0713000c0c54030340c1c1c0007031405001d441a54110600039401c015440c855442200d0949044a4200c440c0f0590b0203402d08050b502881c64081d041600980020030003001c0c024002d4946c011442960b6a01003685d034a542101c00c4649826468001020036504 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 61535794 1250 61534544 61534573
    0x9010c090e150a030b01151e0801270e01020405100801061209060603050607020c0306060409080306100e0901090209090105010c1e03050c0f0106030605011212141912051503 76
    0x50a08284058040180f640d1262a02208a4030903400201e5a0007101c940b003e9103030b8400102e014881c12240c83c918500c51818016001102c14001e150034900c8200608840c1c0030700c030072030003c20b4030301ca0410030207404a100c92501079032250040c02c1c0102d40001c040c0b11428800c1000a040303e01c0c6a48002c1c040d20400c400740c0c0130f0090178400780c90150f2107000200100360281b09944c0110059001000c51282100078581441e20062507188154036007580079010440007000c44c1c1d070007041200c02da84d0b80810040b06440d000ca0901c1207a42100c075800c00419a41516401004100f80c00c88600186070f03a9a80112800004003c1c0140500740d1207014034400840e03030f030f004906c6034800d042c96420300d03011943c2146403a030360503c8055503a442c0d400c20814000750b0b204d028094100c07000786180108091319001485005002c062003000201540390310120142c0c010b8400d110003449950b9840710b0407400060480306a020000b030a94a000e0201d404200040c0c03400e407006038042d001d404042000941c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 61537044 1250 61535794 61535821
    0x40c0905070905060f1804180b18011d01050c040b041e030210051209070e04120201060e010306050103120e03071a120a0e06070503060619020316080309010c090e 71
    0x481d03801d110140c040800caa43d6480054009091034101841d281d055100c00c10011180400402d801140340881c0d050111590b42d8107194036581001d60440107440e51501c803c956403203a41c200049501e088611101d400f0b03c0500704d20f002c1c020100a021075200e03200d50342014412841140c008082c204000c000c0c0c048030705640000201070207510680035642c0e8002c1002010003110032400941c000452901071140340780c6158004c40804010700c2182c0c20840099401030000c2c001130441010040071a000c3d034402d4014102030125005c0c0510156900c8c41d001c000341c0001c1c001280c44101d500c000403e514499000400101002401800070501c0c107422101074280c02c1008803c001810003034440d040c4c01c1003d0080c080c1601c40302c00607105005865650506201034000002c1040410601000ba5904070545407910b8940002c400010416075060789181706440304000396401c8a148003081c803100e0710145100700c600070b0003031000c20b40381d550842e0307580c90f075014000e868041c8802240345a4080f05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 61538294 1250 61537044 61537051
    0x609101503120c050d02060a0e0708070e090a050a030e090603010507020d120b0a1e0806071e030b040507120c020f0a080a03110705070503010b0d0209040308091207050a0b0f040c0905 80
    0x4003441c0e04200b80c0c4986090641110032880968043c1060082407231187c8110b502440c0c01e00042c00c185810b0004254880c0402e106151030058010081111200184403050320305a01030304451110880b4034001c0c0141c050041380702e100380c0c8404000f43c1c4504060103214850066a030140c41e000b005c0301c1c000d56403031640854852515913035407107400b22078071048a0000600740510324900e2a00c07014001a5032410141c0003017810340c01076014082100e40020044641ea50040b0044080818841040b0000c01c0e05145840d40a410841400003580d0458440100c0c0c841403003050003d03074420f100590340d5408050030400141d00c52254400466074280c058448240c0615011850619800729101c0740d07004840300b66035a0304401e20030002032400740704074105220290b401242400741c54002800f100401840501400356410024070310507024000500080351401c0303099104d2440381040c503070342d800042d4111015030140010504141c001c0d41402d00c02e640c4040d801d040c15040001400c05800c010f07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 61539544 1250 61538294 61538297
    0x70201030e070504090813091401030f0510090f050606010302040b090d0f080301060f11060709170a0804230906061603020304030512030a0f06080c010c030e04020c060910150312 78
    0x820000c0f80030b41c0c40e40550420580a00825a00d5040300c1080780048100ea030b0180048526040070107200044c170000c20f40c11290040d141c035145031310905080342042812506000c2c0b07c1e141c00d22007030800808080905101d4001c10450301d40381d5511005400324400d40c0140b9645075014890110289460311448800a214154400000030942e803141c5007900300f0707000a404100d000c0b49030361003543e008803001000781c0c000001301480d0400d400040e1040a0a0003608903d1003000303c10680e1000c108204c07035107503a200100c10364a44da9194202d5900c140068124021803224519003003074500000114000d001c020419440c00c61a2001c2e141a10012034040303055000911000000c86d009102c410400c1811101c11581d13480d00103200e01c01c030741006541803291031400d1000d20141c4000500c100700b509003800e0451500d0b189040c16070f0401741c40201558030a000061101c440240819014003502e1164101e580c1c801008907004150744260b10003901e066081202000820400300006000c188103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 61540794 1250 61539544 61539553
    0x9060c0906130605070b0901050f010b0a1b0309050406050a03110402071a090303060f100c061503080705010b01020607140708090d06050f090f07030809040507051603081504020301030305070201030e 87
    0xe8100d40c030b00c40d440f80d00883c1000c104002482003440e00d140d4041c1c1050000c00c00e5240000001c039880f6010301940c030103003e010442d0102103010300182d180f82c01040c0c1190301406840c1c40c0050a8007050b019940c01682070107800905814155051025694003000f03030041a10071000344030003500901c0064411401505500150002d2610366a000748803d074007550362450720106014074044c80b54106c6006140c00320340c0c00c0c5000da011003030b03018540d440a030111b132442d0305d002c043c007034034405400c0541404400103000c4100f2105501c826091305c000e80980d865940c03006010f0711842e10660720340803103940820121000030002802800510001000031039040001e4445070101d98048400d00030950892040c0002d14908211008100f860385004050050a5568045003409102e0025001e283c4403401300340314600510a403402c0c0403070030340c0c007000e005100e0038000c100300f0054030740079071070703014010550841d00b094002c481c10380341c1503191685410042d42c0110b00400c001c00c0c0c4100709004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 61542044 1250 61540794 61540807
    0x1503020702100306091508060604090c05100201020d18020a090e01020d02030c0c0c0405130b13020603070f030513030804081c0c09030302010f06030f020607060e15071709060c0906 79
    0x110b10303030311510b5801190307000a151414055994111a201603106181e0341480500708100840000d5080d031003042a42e000c03804441c00d14000381050110707080a540a150284d42e9280940d055001e4544015007003000d105002c4000c0da02c0c1d10014980102941001d02c00c002401854034640010303212182c0d0364001854041030034403030400c980040e20702c0d103280100000d804001c6142040312020700241250204400d040003142e071f800c0c81c014030200030301e421040c03000210219960a08240c003c0d401800c1e40340d0340c1c43c0103800103010109203d0103501292520000c1085000e2611020304a6541515050115151500c801045801803a0f440440c04517200000c940219940100b964606a5803190103809055250103825200008400f24605e0f16241d81000461007880c814030310580c050319541d50b2400c1030305040015011861807840c0511440340407119114100c0d05561180d0144e5854101c0c1e201808000d00000074242c8a40c1c0e156800300e40070071400c00c03404004228848009050074501314 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 61543294 1250 61542044 61542049
    0x3110c0a0308120a0b06030105100c050a0303060e0f0403021203091e0c0102240112031e020601051c030e280f030611030c070809010504080604111005040f1503020702 73
    0x1000341c104880d0362501041410b00103041d03500c00d641145000405025002407040441d8450005110b100d100f01740d00b4031000310341401804400025030308101603d000c07940c5401d02401500813845024126443d6000240138003100f003001034002c0c0c0c0c4c164007400e000c0e840c403400300841e40c2005e001c0801c2401041c444041011103909a414401c140304d000d024010040030001e4284544000d10003490480000407000245807040201c3c1900d403052007d040d030000c3c44c1000c48240b00046c00c5600b0009141071f0343e005980d0001a011b04031f5070304503079401001803052414010000f0441d4001c0103c1d0202c42000040d2030f00c19003560344801130540d40729902d81640c1005440e134005511900c6003d042c1c61090052024038003030101240c2046104a1540c20404001c00040c0f28100f0050500480402c40612980c81032041320000e200050441701942070604028070208a401a42481541082200011a03001d0815601181e000022010303525251240000380d09490203424410503038200b1502005a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 61544544 1250 61543294 61543309
    0x1b071103030c06010f0f03020d080d0209120c09011508040b180106090209120d080a0c050721020105160918060f170c0103090b060105220b180d0803010303110c 70
    0x1c0d2100302c000c01c180d5150005002e80918590042070b21541c10f43c0d018005629408a0f45002581c40440f103030340c40b01d203602124024050100c4581c0c2c04120000c8040c1c0701507001603140d4030150211511803a699031040c10002c2c4903c9844124049108100040c003c90708201c1d10903031045090780740d08107044402c61003d0840e9103075003050703e07041d43c08034288006003030910008a0051050001301440852010080c05200e0014807208400d40c5034000c0c41d035160722403010380f1000c44c1d02126070080c000f00d4101c000103401264007610010342c0f130720000030850158000c003403890440c03940300d541d03c00b1705020010070990b0080550032030b0b56441b0103001481c0d4090300f25040051501400600036071820250490406200c000c94904060400750604007103400424455046182424050381d1002518021582c414038140f0380060003440708400903d1707142d5413004041da00d251340e03540e2030950412401c01c080f66099480107081d000f0306000601c000b80c090440e442c040800141194010446c040c000b4480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 61545794 1250 61544544 61544557
    0x40c08030c15090606010c120c0210030c020d030b09150f130606080a02030c03160c0507060e0a050909030708090105040305070303090f0e070c0210090306060308090f01081b07110303 80
    0x80d03a00446400d5000020300e0201c980143c2030034081c11050604600081c694201c2c0e06000e4505560b110102140f180038100c1c10540f07590240c1400000f074403030003000e40104156034111016010707014440d040644a84152103450b803009000140da0f072214810000d0048001d01c01c135802c000c401ea100d0b003140e81d40034003e601140d0302203130110b00b082c1080300c02000e4510181ca000f00542c014014440c940b001d04040e00e90100b4641e40c0010000c0e01904200c80600e90400003038801e015680020448641c0400d40c0c6401e010142c40131150a42c0e90811300c01d403084226032281d0aa00144160000140c40c01c0042a0b00c4105250040c28561251115410302c11203a00c02c80c0492900f480130000b0101040c0428014298121000c409280100c0080c0c0f0702c4010321402881a03a11055600426008261000203503030884010072140780c41c1e1500042507031005902904c51a140590b0b032600c0d612601980e48240811000411403500b810490071041c1c001000444c2d0843c2034422090712a142080907125 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 61547044 1250 61545794 61545817
    0x18060c18030602090a08061e1302181506040f03150e030c030408060f04021e01140a020c04110304030207031511070501090c05010305010f05120102040510091401030209090c03040c0803 81
    0x91310016482000031039800d5a10045047e081881040040c84d00d820020800d00c0410080301070396903075580341c03484040700c400009602c41e03805031950208250f9001403030303c0351013001d40140c1c280c0c49440810419006a204420750030440510030b000090b82030044402140d0300141c0860881008dc0c44103003503400100c1d03100005d51012070101b0400208202c021b80010100701c0f113001034100f03038012489111a000740d1a00350207250f00440b555911411072203100524040c480f9881350f5000314000e4482c041028440d1146041c00d54010b1886443c070300301c9002d668581c000705210b070b00d5507903030780c0e400b00c41902a910301980e2000106403404140c0001d0074801d2083c0c000103030022203450810445c070040d401c428100340c580f0b40148800551800c418080d0385048070340c059440e011700c8125029214076000b0641001d4140d03101c2c00c0d00341d04642c466094800c0e681c041251800c210004408a00441c0c5006034420240c001082c0f24000c00001107070814081c075003001b0740741d440c2e04180d441c55201014061 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 61548294 1250 61547044 61547047
    0x5060f03090c0402030411040504020f03030c07050102070f0e1909080f04061b11060c0726060130050a050106060518010201051603020c1e1501080118060c18030602 72
    0x140c01c0034009100c0d1007904540071400c40c185900c1c0e240050521101d188d005556940c08a000d43d591042c1c0f80e828040014112640d41070480c100710744581c4284101070140c842d4034008515105180320031000c0c0e4501004551f819556080c4c980151900031850b903a070140d4501c800740100c0c03c1e00c40280311001008100982c0e443c0341c1a4024029210410306c080140249220300c00041c4d40c0c1035a88000e50022aa00c0e5150104c18480c242400d05c5036101d185094091003000c0c12a01400c10781548442d09001a9041d0b81ea8a40801d8100c0102c014000c500c0411070400c1c00020b40840c00600101c3e00a10817a1481c2e40d09076501402c42e0525045180441c0c404505205003a804892817444480203100034031450804100461140c1043c00c035100034960081123400712040100180f07417000c148c0d03080015070440c1001c07081d45c54040914180000085200010820f40b105008003058501c000c800907003046000d0315001c0041040600b41404c1040247c3c0c05000e02006500320400f4500440005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 61549544 1250 61548294 61548301
    0x5030324010e10030506120a050105070e0d0f03050f190804060b060703021509030705030d0c080601031a0108090102161b0f0e010902030717041109011e06050903030405060f03 77
    0x30910440001116040000035454000709444441d10040488050700300815240c844134002a80b01781880d4000d0003030300c201e01e00041446015000300b4020305e4143c4039003100800c1034081c0140c00000007000f50000b203040405900091080300140707007140407512118242510a40c81c0c07202540c0c4d82d4113500c00291b401040c0414043c480c8149815190220391303403803030000550350103529030703640c40c440d14030040901c0000351024409004540c0d090f54020240c0340c0d15034850340c9002c000c1c22654441800101b505000641c154000d21540d104401c0e2010348900c061851001143e1140009010b2010703550240503030900000144000c0300f0180c80768030072038004c500500350081110525404100c0c0e8004200381082500a61011941590a8488056940d40d2900030903035940d060780301d200400940d000700700010b2040599403541028012504040c850b41e03520855140c2e00e0307080d000780118a11514040040500400081c0103200018050b01d0905175181c000410075004505102003058000080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 61550794 1250 61549544 61549591
    0x703090311031c020310030501060803070c050307060518031618050f070806010c0507081002040509070f0f0509030a2108130f080a0315170708060f070c030903050303 73
    0x15031000e14801c07008600f040000c00c1d100101c040c40001c2e403074031168000042442861010401005140c1080007880300c56542e50116540741c3c0080c030300352050000017401241d68a00410303070070b080b03a040340d81d041c2c00c10262a451800c50302802c03001c02d0b414442e810850f0b002902d84040000141900002040301580071070b000304c15240020f01d03c6000202c040100080c00d40c00c01c1e5200d170418800e2030242e1820509283c500d10b00850394001c0e85843c071494155184007445034005000351201560074100649440000351a0b04440f082500003064000c185641c00760700c01c2000d4800c1070401001c8510240140c1c03a0391030201005c00d90580148686400800000d0300500c2c1580c01010743c018403014003003242c88544260039801002007070110002900600c00b8401e4120203442d06407001d080040c01d03541e00c0c14254649103600b0940090103840ca00107071822000c0341607441004050080c0c00c1503030ba81d080444d601c1f01c0c03010b411400d0108004000c0080b51040000e10700c205c0d420f00083c0d1049500040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 61552044 1250 61550794 61550807
    0x1503030e040c020105040203060408030408070c0905010f060e0a051203130806040b13030e1509040507090609050427140a0f030311030403050d050c0d0c02060105040b060405030604082107030903 85
    0x2c081055a05200a210058500045155001d078000e64015100c0d112131421300c003a8800d0410180c00344024a00119244aa40e84024122191400b41540450352481c0c00e4501d10003090409a0128229104200c582401076250500e07000e61020f49260010030070711240c90308840e41140100354040f10030001080202c600440e042011a14040c64400c49650010009064440d04c01e0088070914620700c00c0e030380c9510a442508000038414000340c60724410080508290f4403510000540d6020300141608285c410407100d00c049070030b1144096102c00121410141c06da1085903110b0031a4010344000f0800d01a42505900c87d15004070b403400c0900f4001c05a03202d0303404000031341d0010420b00002942110884040e40c528480228507551403d50580c0d05000d108402c0c140b940c242000c4902c40e40e03010078078505a0760f0445041004100000501086000714002c03950180d100d107000c0f50100d100702d0043c1840c005d07012403a1381038501d10342c00710980e201d09440780703401700c1d0300c81e07900004160704500e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 61553294 1250 61552044 61552061
    0xf0913060509011509030b04050c0102011104050f0d08040522051e070f141c060f080d140d0908070302010b090f13050c0301020c0c1003150b030a1503030e04 69
    0x50040900740000240c81c10410302c0307440c0010802007920a104c1d40a816400000c5402c980740034107515090030301035124245006e80c00d0040d440c000c2041020800101500c1c242c07800580000c141881c040207001c0035954018ac15102d0020038440024241d80c2c000c003180311003003000301111500309400b810800342e81002c6c100b04080c250180c9009030040449008940c03002861a104034402c402c5502a218a4105001e90b0314140000a0a001800b010321084000c1c4c40b54620822800d5a506011400456540100034441c1c000d503146265191103000ca01000d08015005580351450217107078079003127954044084541c080042801d41c145030302032084914102e0160b0711882d09207070448a074142d4130001088071031910311207141c2c3e1041c48070410541495810140003103560380c08812255542c0e021110f1110711952800c1000c0d20014800d001f5240d0041013032584030101c90a102e0b105206400003400301420a0381d40c4545060941c03120900c50041d8003d071100000200032074103010a845014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 61554544 1250 61553294 61553329
    0x2f0307050d020705102106030636020613080a03031d0607120c0e0301021206030c010f0807030f0f020a0909200316020c030d02061009050c09040c03110f09 68
    0x80204101c19120705060711074a81c103602d8038410801d5040c1848402c5203d14116506d0a46020004804c0186583c083c428410800321440035020990704201c4116041a5002100c840e540d20300700018100f0402501240f200020440015030719850714030720b400d41450041d0300282c0c64900380c014a201061a030340055010401400051502c038001501e4000421b074000886651454400e14040c4038030a01e82c0d404030024000e650b2000c2c280d01d148000c080c1a5002440381c012039455116942c001c1c0c44020602d40789441d803041a60b1032034400e500400900000e000b00640702c1e80e000b803002c011480180240e0349252100e00b01c407820a0381240c11502611914000400007503100301d644d405404c16207134000c1ca500800a080e81407084128104240740a0150f01031040380382c04080e0701e4002c1a410721644106524a5100e6a1900c002003651419142c001b01c1800030481c1e5026804d0a8000a0036941d032030401050a0f204541504d584c0c1e40100b221400c01c0c070300824517003101d1410b00384807185442070303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 61555794 1250 61554544 61554553
    0x4050405010f051e1f0e030705060304030f0302070c030b0109020703020606030613061e050103081801020604120c03020a0b010b04050906060403020108010519030c0905070206070305010e072f0307050d02 89
    0x821001c0b030300d403840c14404014614200c452604640da1005904940320245e07100454410002c8040501603204191015220340106034001c5443d05202090360b216a4150b070703d210006404007402d070025031091000ba00c4540c0012000301c00b040341190098000d05081e0001030792a209410001d0410301c000d41124032075046803003401910110b94509159140d04164000b503010720401c500540300e9940784908141342e0801000100f408282c6000d0002500941240d203c0703c5000e2004903242c800407a0024942001100b101c2c150707074070807000500303c9031103030044a07541055500c812603804801d0303200100070345000500740310b1810700503031243c0c10503810764016041604550000c2c0416005002d818000c00448000c01618a080c071324160083d5082120300c402652a0035038003019040c100d80100252080c0d401258409100780b00e2075040b1242d1001a510a40f0303002012291a5112000d60040501d601003108030740143c850308800e500304000082d40d6554503071a01d10b0906206074691810b5401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 61557044 1250 61555794 61555799
    0xd050f01050102070b181e031506180403050c0a0809040b0a08030f03060604120602130e1006051804050a090c060c0b1314030307030506040608011812020a050f0304050405010f 77
    0x80010b11038041c0c0302800440c58075698503124080460b403100c146987d12000380500d8115082009500141c00c0c0d4041e0251a05e0385106000000180c409545058001000010700740342640ba032a62075800a00c40e1030414a0100300c400d801e8541142820240d40d01c5100140080c142e2070244180d16000009a41000b18146800340c61500c034021543c0c005142c142c00400103038283e680004440140c0044100000c103020700741070803002900844d41d17500b810701d0780b10343c045440c0202d1501540b14040700111b0f40300c4e050400c80d00310307a03940103011641000c01c40414003039030a075214000d1611840401600244a440c282001108005613a02180a0258040500c0046021442d1565010a00c003151510513074103032802290803580b550941c08140008401d00c4a050b0381a00f00f24020402100c040c81410b851341c440600700d03041440c01d00c1c900b00140e001c04d4001102e00c120b2a10640d0a030040d1000c007031887d11140d0a001000015680c0c40d000050700340840d18061094601408250360034500003030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 61558294 1250 61557044 61557047
    0x30506040809031509060103050c0603090d12020f04120203011b08011707030c08150709080a0201080a090506010b07170316050c0a15020405010207150512040501090b0106050d050f010501 82
    0x16406403000c0e000355000994a05a81c070104000d0415003609141d8001910700080100d07207861081c001142c0070b00811220702c0c1103213414800d0fa40500188009080d00c0161b843e01583c0f08a41c0d804101c18160302400750629440c04407000e0402000000c140b0454451984105401c41d0001000781c40808a424a8070603080e92001d9030701c1c1500d01910880001c001e400028510701042c0364801414020700503000700c0c92000c040b030404c01800c05c554401203e911009426920524140502000e5034001c0c0000009580b00709901a040000c000c00043d05014540b94641082001d070030031211090005000d40c10000c4c400e58110880c00e0311050036096091818418190258000f00039040100115240b110142c1c1030200b20000c59000c51401590701009031f48901a4105225160244c01002c00000d186180989401c1c0f40d40d01c1c50344c520345400d0340030340180c4940d02e0180007035940350750700d000110015541d2211240606132945420f42c881a1010b03c4009441e070041502e20180c0e00d1500403ca144d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 61559544 1250 61558294 61558303
    0x11107020906090c1b031c020702030d020601181a030f0a020307091109040b1c0b10300515010303020c0406051206010306050a021e07060608060f060616120806090601090305 76
    0x1005040511782810500102c02446c41c020350764103c4034103207240345aa80740d503480e40c01451510710960640d00c072019002c0e4182c0e00c40c4002d11882590000d400c10404040c281031b030102c000d0800c0c51a908003401d082130003291a000c86440100d070302d540000c40b00000d5181c1040b1800c01412403250500580140c594801101d00503450708a000740d07115071103070354983d032218408a0f80c0c51a280e1101c094800606100d8840202a03512a000304203000c80807682c0c2c084114000f012600604005800342a8101c040100070030500303042e625070040d111201c1303420050082090080d40641c0c010700e00800c500e0104421200b503940020311804200303400451a00005c5606411203420010015180d990084d121019101d420883d904080d010414880b401c0e0180300503041050040c6420070000d41c40e152080d64810f01520280101d0001e840010180d1274180000c04452200502c0c101d12501d40356107821807510020104804502850700300070140c103000325a11360160303007441c00c814400c2c82c5807540b0307848 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 61560794 1250 61559544 61559557
    0x3506040c060503061c063303170c030406030203090c0406152f03071709180621030912060114010c0804171b010c08040905090708011107020906090c 65
    0x500c403001c400a9003560b51485078045100171070004d02d09602d414a00b4200500b952103049190440030441c14110700503130002520b07044a02c20102c03890074203607155581061800c111410101d4410407502e200c50900380060320003401e15031805a205e06022510a0030031503c0046180180d2400d00b04200c9046250100180070303946041c4071050808641010a0b43d22840087c06030486550091f000703042d00002c0209078050003000c140c0e1560480003a2000d4a00c10380310443d9122218186001d0304400c80c0c0407181d0004001001000000b101d641c540c0000c00040c449041c0c241c0021401d24a00d0400080034000191100061309817581440c1c1d12189040c80c1003007650401c0280f01c03619042103070300c0d42194058840c0c074000380a803516101d0000d60b40e480303007030341035204400c10240658654086c070580303040d26500c083d42c24106070030f00c0e404400410008060075414880c01d0b000199404d002c1c481c0500031555000059a40d05050060164860010b403c1c40e0040381908100a440c00440065910 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 61562044 1250 61560794 61560797
    0x4051b060d020901030b0a1205011d15130b130320060109090606030209101701020f040504020a0201090f080307090f080303060d0309090c0c110405190b01093506040c06 74
    0x8035440f281c001200180381d421080f03a0084050b04000c1208802c1d041c90300d242c503100e00000d0100c0412082010311010a0410034240c0358015290000008402150150b00000540b107031049500300d6115145865010307600d05410407100c51400301070680c05566210b207007000c0c22400c1c01401c0302511543c0e84420500c90b10b0040c60740d40105004114040c0c010900030368000700003400c541070407604089109101c0c0703c1d51301d00701480032008241d01018000c0d1108922401e001c0d5041600e48000d00002c1d5001d044a5000c555940c1d24100001c0d4500c0c0301c07000414002c0c1d48030354903490700c01e2001d0520742c0c0980040d030004552020400c03442400008403640820280d400ca0804041417400b074458490a8124000f070609083c0c6c0042e5040c3e0028944103014003a4100207807405911b818402191426a1117003400313080d0a51041d021070041e0002010940c0c113240c651021556050b0072045032200c5681e04410039801d1440600e02a8140c488060392407805000d0b050034246035a440c0184078051203070701e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 61563294 1250 61562044 61562047
    0x603040506150a0b0f0c2b030c051605010605100201060f0b0d060b0408010b0a090b0d03030e0c13020315010e01020d08041506080307050d050a1b02040b040c050304051b060d02 77
    0x402c0c030344407000c0703d10050450b02d0070395842c1c0007240c007406560380141210343c00d94410192a220302c0d0b1190001c510403003020b480700ca0b0000510380e00440203008602d1404c02070050422146104a410003242c403080c83c020000003c1407402c2104210250002d80e1a00b01160304104040c04001d00d40c0c8540802c807020039100664512945c503003000940743d254424124080f02140001d4052019081680003150444428800d10340705c54900017122030f450281d640240721144800000780c0242c1c05245460310420480308505889000940050b00e41564880c50a070003000b0720020802d5020001d12410b0242485440c00c0340b5503000030360703d0019030003140c01c0044070804175041c403010f0f4104840d2508007010a03c001a22807481551b250b215a204551500c142031030601006e10070400d0340c0c05403d031540d410b040c418a024014a0080b0f400300140e9002e5a204c0144c0308a58451181c04600701090300c0381501e0b480d1a00f400382c2000085548100304802065411589503619011280c06032000c40006 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 61564544 1250 61563294 61563331
    0x1505030d080613060617090102040605090f030709050106030f050901020304110d03180e071d090a0e010b06031e0703020703020606042304150c05090d06090f1505150603040506 77
    0x7604540108103902407452904c0c8001c114035a21102c203441191019404c0c1103680c0314202224203d1045104000000d6420701c40f116071860400e241c0d44155000030b00715100691039440c0d000480320281e10040100c0d03680d8040302e207240514041e4039441541d00c0001c5045207003d40360980c2111209052a110360241c035011810580101c40c4446449040c0811003032140e1559001064500b00365500d80103d107806650115500503040300d80a03e250180110342c10380c9502c09000080c044159600a0319501d4101c500620744800b00550311400305e40651360030500715048070740c514085c0030704038000300340c010083c100c0401d07000605036802c00c0d010740300000d80840b02e26102d2940d503a081c2480c1c003803803a104148010b20a404030b0782064a00804c20400c0f01401c5207900790780b07d10030a40f102e60010710741031280c404240b50394011440c545c065140100b5003441030340d43c40300c1c00c0314580c40040101d5540d0280320030021030b40302d80c01c0440001d6440d03e10b141007948030203a80d00c00c0240340c2c5886036080d1401 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 61565794 1250 61564544 61564549
    0x10b040b0d0f0305032e06031b0f0809031e0a0311030c030609040f1208040303180302070302042a020307050601050d0b1503011814060601020604030804031b17030a1505030d0806 78
    0x242200704040c1d0b080c00c64130b1807200000c031b10b90342c414410400003904050006003460414409901012802d4542c076215003c046401e88200c1001003511165000600600a030a022844113028680c621010b1613950303000007e01604403800c500002c0c200200c00d204101d44e21040300d0440b90402e404444050041d926483e200340b00c0c0d0070088000b0075000444080d15902500a140103005a204c0c3c1c40600c03590071a81c0c171040c0891142c81e0f019006a02c0703481c0800140c201584403003100309a03115124002000501d0207825500038061020041c1e10001d206410300c00c041c4540c0b40501402c41d1f0003000104a619603d0002402900f10b6110741024155800c6640e0250301c00140024994008018844682401a0b03c1044030b003154505004141c0040c42c90341c40803800c136214070362507140c02c8052307100c58804941880e015458100a14452651500492044180a14003c1141154903541c1c6001c600090503145001d600300c0c1d8660b0101c00601541d42d0104a01c002c0242c58130388407007695580c000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 61567044 1250 61565794 61565821
    0x120c25080712051608030a1101021918120506090d030605090411030f01050106050705060108060c07080a020a08040312020c040e071e030209010b090a0605031006260702010b040b0d0f030503 83
    0x94a030161351303100006207018010018004651940e280d1020208004811600380d02c19803001c1d2400062900e800427107d4018610900d09a5681030340d10603840d160003004c2c2619440c10b400341c50540c040020481c1d80c250801541400d640b06150501c0101d18100119607914800352005101c5801d100f207401c255103041160101c41000030009214550750345e0405051603000c0b803030030303641c0340120000800c2042000601074060798190f134880c0d1400010b61500c0180d500700c4542401140103840d107603000b0540c1c14000d40040d5009a02c600c5440321084400707481c04c1c0c031104a46000300d0402c4a4000c824401043c81002c0b02d250030000d19003102501c25a581d4100141c00080d442308490001051000e4010044e0082c1c01040d01c07a100e03580e850389400d41d4a40400c60305210b41240f020001e201da0f501c506203032601180803075405400080745001500b6030807070840d140ad0051303541d120300d00741e51b1a180c040e21125140c240e4140009054544a001a201c228038001d41800f90010226002c40c0d030181 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 61568294 1250 61567044 61567063
    0x50405242d07050408010c08090601050d1505010306020a080108240915010312020105010b0403080f090a030605070f030606090b030f07090b0a080619050d1103120c2508071205 77
    0x1e080c0c24a03440c0c10318000c0c045420501580d01c481d0710b0103041044883c001d10401f40a0b40c0000010152030b072825040120320b40301c00404442c1c41c194180101250021405801d0286101d030f80701503124425144000c10b003143c141e00c188110380c480741c0001c0459001c618903419140b0501c9003c0d1155450030900c610f844001d803103140c507500c895400081449510b4025008d044866802400340d0b0366100d001041b140218040035201c0002003040000b958030110050648190103012110313070ba039890303c6580849100b01c1700000031510b00481ea400c46503041c85007070084d000904000100500b0b000704050103010003010014280200c60100d10014040c003150402007030a40c901310b984c0e424140b0300800070f900035100309008404000c0c0c900000ca10202d8018280c3d48082c0c000503020b410341e202da6075055950341c80c1503014082e4560080040d8444d0009004201d4418000c244403158012520340300b400c110702009001040708400e1107004c60109184040754403c80400340c8007031180c10810b01780030602c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 61569544 1250 61568294 61568371
    0xc0a031a1809010c02030c070b0c1218040501050a061b061805100b0d031d0d0c0f0503100c09030f05120301030605070305070201060501230d020304030305040524 71
    0x480ca1070950060000510301c100c090200038022090400c4c401e0f030303490040c154048400e8004030400d10080e02144050413030101103908a819032025000c2c1c507260391f400340d092040e05922800ca00c11050500c1c1c06003a006090039651002841d10341040100340e00d0302d8903801c805204079100c04000703008142c1c10902c07a115407103440e142980490315005980748103042480540c14100002c0070410b20303040c180da1302c8907a05520780400303005803103400e010403081203c000c1d0b500280e601d58407000305034000311050280140c01c4403608038500b0b010400d031912903010040d003116030a1091018a245c0d12140507812640d000100b4011400103140050a00003c0c0d981c21035840d1021000000b800360b9500113a016a140c0c0c0c0f810055030311101d1089080e81d41c10700640c0e020903680f003083c02510018802c64110811166032050401c03580707038812420b07a807051324241c0000b40c4071010b1100744a400c2c80f00754075222403403038141e070744011040004403081001081050488141071040d4410b45005041c804140601d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 61570794 1250 61569544 61569559
    0x20903060a0506010908070803040b0d140907090605030111120601050409050405060106090b0c1e0106030804180c0503090a0303020307050702120f0c030f03030604020304020303090607060501030b0c030c0a031a 92
    0x64039481c1c000c0204950990008514690000e07001c080494010141c90141d03002d107140c40e00f40070a841560340701904202c5501e07500d201900c10803040c2a400c5004031034200252a41e00e14101360101074600b5030300603920992404070444401c102c60012200c448800c3ca081441c40e948040043c0e80d107008903808002d043d400d1008000400c100490118140c0c0e02c1034441c1501551106144513260213040b82c01421a4400242500081441100010164444000030608503101da6808072260002e41c44100c1d000300d0002c0c0813a846ca800d0052448101440c40d04d0f0f41107141c42e1890a9441c1010500501496400008607218034070640460341415001f0740401c0d010000f005009560720b04507689010706000c2c0d242c02441c41c1c03901054041449401c500203504585582d010003000303600c090401c0742d05200c100329101290300c2d244054120b01e4000c034000186907145041aa10140004001c450142410070810a80502c4c0c401a036043e4006403400054a80b1101c0c2c440c151111810b0b020b0307900904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 61572044 1250 61570794 61570801
    0x304150603050a0605060a0e0408030402120f100207063206060904110d0c0201020f070308060d0f030503091002090d060213030516030501110c1f140f01060f0906120e0102090306 78
    0x40c0c0d600a170b405060181c942407072480d510b2000002441050710001c00404041001c00c0c0036150520342c49000980150036a1561010072000d10300d41130b10010564402070300400c0d0407041c05018803601902041c0030580c22080d255500c481039120b0715a2065220039052070010940380d850b039400761898040b02a10400c040c0344011007048241d008170103080944c5d030400e01c65607290351060013641d03214080c0015090a182c4903030f0781520841002402c4603001840c0b0f441e083c0129441e04002c51149010f038070b4040d03987c2400c920031800c0900740c414051101c8c3c010404011a41c80341d2145245540d080750340180c6400104082c0c403007090080c3d10152036885007a6040102469012800702203900c144020000d90032107050b508094007400072140742031341000017900c145e915503014120090343c03069000500101008020004210165042e100d030305e10800040c40b403140c01c030100c0800201e1740d04000234550710b8111b0092584100000b9034030119200e60300840c0f00030094040d070341507020003810748500c0e18 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 61573294 1250 61572044 61572053
    0x6061212031806060a050f040906021210030512090901090e0a02040603050102131e0b0a11010f0501050109050102060f01060f09031e030e0d0c0308070218090a060c02120304150603050a 81
    0x29402502c0c6803d0041001042c110300e010390051085032400380001c420384140804200003041da208080d552940c08210f4101c00324800104c00b8802c000e1240900300407820350070454903042d008900090b41100400c016000341d42d80640e541d0445a060102280c800030b00005241042c5e401074000350860300b0035034048200541174000e40b00200ea803908008050b03649105009025010390f04041512038000c80504c800b440350802084404854200302c1c02ea0140f400082d400c44140c0010808034556510040c0450741e44090440010082403000342403905003241c0003940900188150710501218440306240503020b00c50441c02550010502100001007480010316201e0220080700083d01002a24170545807202c05d0143c03450700481c5114000381141c6c0d4401c0c86600c0150285e82c09401c401c81000540039190341644138400b504081e2049000524080d01928000c0000c0710541d0407101e0100d0015003841d041e00c1d4010b0f04001c644c242c110003180d07010001c1005400250107805203009170030901 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 61574544 1250 61573294 61573321
    0x3121906210b07020109020121110705010506041b021905070803220819060b0d060c1106060105190c02060408030a050703020705010207061202030a060e07030b040e01050601020606121203 82
    0x1140218440091581d03850f008908035841030a00a020491184007003001303a14031140841001c162510001d9100f4096181d011b02d82c208000c00c450981d140c5c0704020141c2094014490b0301e886540507890030414940c406501e84044140b100210000392110205019042250200805410b400e8a5459000d801d40d508420321180b40700c41910f10601c0700040d14030700083c0b40790b5880c1c161016400c01c0203003581ca0f240030701068802c0306d038002803403180000892854410010b002e00661a44050781e40740c2171000b414800000c01e4503040c0001841443e1790408100d0354200a03280740c1c58190b003101c00500c00141c440c003407a008940588008540603007203036088801450358902940864070742c80d544400481ea2900c660140100090340c03151281c01440454020f0358000d060444c0100d643c40e1640c829400180d030031954030380000e880c3d0708083d1a038180f503c108041c1c914084000d000c1e074901940040d40d03681020303041501aa80403144844045004c4c802140d07400041c03507400c0d44c2d03810115541500d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 61575794 1250 61574544 61574609
    0x40f0c031707211713120503091501180c030905010507080402090c0408030f0304050c0d06020406120501210f050607050a0801140901180908030c1b03121906 69
    0x2001d41e00140f054100b40300000e00742c40700155210764900c000d1502070300d88000b010b06080c0710800030408010010f50800b4040303404559994809440e40750a101c01c61030031100c3c9803a00351000d007841c01404000c007044001e4039605100d01c004200700c14075076011002044949406480d84d440d00061000d0a58080440c9001da80200e6010016072110b03484540345105500c6041000d0b442044000585081d01001e1540540a58140c501165050340420101c433420031080b101554005000d00c42260410801c414801204904202c95810041c03405944202402c0301000100f980c250798041000d0080c0c580b81c429404416600301e41031281c0040c0c0190407480003603000c941800700204203101ba160040d202c2e8400144040200e91a00c943d2107610400c0a8540c1d43c0b4584510805020942c1d400040d40100c0d005c09820b95520300400c4950355803034118603030803e40c6d00304019050070401128001d54208448000d10720790000c0c0c00310903c00903c91584503014252a143c0b00321201d1811a035100c40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 61577044 1250 61575794 61575803
    0x81207030506010206070503060f0a03060207060b13021e0702060c100603060b0906010206040f03052a010e010b0d081c060b0d05090f0307032601080d140a0503040f0c031707 76
    0x916242c10005984502044503501c0002d40c051000907114500f03c12941e0001101510f00301c9103503101e8441c0b02c240d0703212501c01d03140503845036256501d608004d413010003040c100001c02c43c18005140f455030042d0301c005028000100b0045510b80c01c1d540c5000407500140d048400700d490214106c5654070152881d4030003507450f145403000d00d0031907040800320702e84a050164003500380382c2d440795510f1669500929050b001c1000c28010005c0300c8951050000d550003144461004140c40c10039114252425500015403e9042022100454036000c010b04103856100707004a45400c82c500314168111514102d1500e003074202600084e02501140003071460802a000901117541c5610001e43d40341020a500c1d45945d00802400022070300c030b52021500101d00041d012400b80076001c060032100801c2c0c00254040d08940c501410a40d007004003034103640514400d850412680c1c0101810900008001400c09501c11030b04da01000340f08000710340919808003560308004103501e50450550840801142c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 61578294 1250 61577044 61577051
    0x110406170d0e01052113020415030c0503010207050c060a030b060d09030e0405060901050609031c05040e0919020f04090f261810092c0606130303030e0a08120703 71
    0x3034055205508448a00c41c8a00b4905d001e550000021412480010503c241d07910740526400c005035214007030135000000c41d0740d181248070b0460a00ca00381d2612580203511a03031042007504000f5002107161181c296044854a440740000c40b01a005401d0001e0600d9000d0400504022030421a074030800c0d0941c00b076078a01615941d508203002c100c51055501c0c0e5801650140101b141e0f1821034010441c0c0040035080ea851341c0490301d01c4000f03088003083c000c0301090b0302203002c1c000d02d215545026070080101e0300800c0c00043c04141c95200b44a00c60010740603107916016480141c41e650803c0c01160b07480542e10b031b6003000a0410a07554840400e00810035101080c0304203014050f9001d8400606900c0d01c2d00d00410101400c115440000c09c0b00e840c00d01082880c0052044a080c01c4814262a403c0c003070b2086c8161928940b0340b9440042400c0d02c40c51080c0480c020800c1600f804a00380c81d498140021070281c400c031113500e040480c204c018221040020501d80d816403441d035440c018a03ca840c1070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 61579544 1250 61578294 61578317
    0xb040506151c151404050604110a0e01030213060b0d1a040605210a02090f04120c080714030405031e10050c030c1303061107050601060912110406170d 66
    0x41000d041c0400641801c002c103144140124907800d8500420144030400028180055090340b40c40d8101158255a5070700711104002c2400750313040341034220708e01c1184c81e07a20081c240700d00c1d45149441800042d01611840e002301d003111140b81d00c244040c1050f54242ca4907040782c010341c0c1c4040c01681c01c0307402007a0041d40d0f9a0304a1706060240505540f8000e100900408944420383c031204c40301d4240f0400c5100e00a12107000d80c4500389142e00480c6034000003555171900307003800009242070168a40800100000d42008900380e002603c3d072403a44480b640c0b000b1f44034a86694510b000342d4200e603616016403000c0e1001d5001310745501c1c1020040000b6144c40300414844d140844004981905c1c0c00b600420026108841140045c8940d1864150b00b04000341c80e52070b81ca0032144000c4003042c0030413000416105100d010041c90340142910314000c1031281c01c1940c0b44542140f0200000c090b074680b0841c08070599501d40092014014030220b0241d4040607004040c1c0d20b0a050002401003500f04a03030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 61580794 1250 61579544 61579549
    0x604081b010201020a17040602040308030f0103170a08010e04020a05041b030608010c090626040c0305011a131a03030f040614040302010f0c0501090606090c090602011401050906010c0b04050615 85
    0x3511211006502d4003001b8a0f52050000010000284107c40c40c0b68208008000200440084c5020314003070b0441024641c1903140c00c20003000c0e00c500000800c0e4050203000b40281e032280c0f800d419201100c1c83c0854544a610100b10f143c840c5410441d03109083c00c0201c80d0b52006158144030300400c2d0740e0184140f503620b030201c50072101c0319000072002070300075541840b00d035000751948050f007c2c90030b1040040766220b101d0001c804400352011500440c14200c1002801024040c42d08031002030301d15502444000400980a5a512812428420b4484036491107403040b031005d1000c02c0380c0c06000c1d650b955402031410b904584c010b000d403001140c0081040c04404120100759400c0d2581a199102d07841d01c44c034001c2d9010720500d03504403010340d21007452500050160150380300400a900011481400c8103d01400f00751041d040032045a1428103446880d000c1000c01e90b04440701601c1400140d200c200040f18025000440a8204071051042c48104400002d14500c1489101c11200d1041c03c507004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 61582044 1250 61580794 61580797
    0x50309010c030e0705150d0203090a03030e0c2d0306130618030509040213170a140c0f0f010212030c07061a010c060e03040911040906060305010302060708030903090604081b01020102 80
    0x5030f9140320781c07283e4410720035410f1000501e242000758a103014144000a43c81c102aa0300c121010000d46e04010107031420990035014030900c0084000c00780031000034010105a040712180d460810180e0000e9200324441d0544902d5801d01e031000d01a9030b051f00e42004040552031000400300d455038034201d9012094802c090f48415403680c150b6500345010708280400010350800400042c8040c015103000038440c0281000802e03001c4090090500a410740c01c11001ca41c805200000c0181c00001c1c3d0148180e8500002c2c02007880c0c00c0761b4040ba030040d6040101c2c50548196190300c484c04000003440000d00001c0b0181c103d1900c920404e0001550a25504032103982c0020214089a034041440c0c0000340c16820041c40e00409004607400c150341c0c1e2007140243c0d10140801c4560301c0340003a0901130300c1c0c2c8a005282c003034611400c0500c515451a80400c00d14402c440011302101400b00c00300d50060414001c031515408000d295075121500c9054090700c500c01400c0d041c0384c81c2c104410181d8294010b00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 61583294 1250 61582044 61582061
    0x8030318030705120702030309041a041a130e010207020402070b1006020705010f030e0111041710060503030418060317030603012306190b0408010209010f0201140106050706090b07050309010c03 85
    0xb009004d0241d0720100111071604003042c2281e150109000354101d646841c8103007501c0c2442c03c0d00e118500c8490740d00f0302c011600052130b0441038984507031715410760380c0750030b03620301d05080c808800007422400e081042c0c0c2c024058800004e501c5400080c81400348407010344000e0240e403130b054011503041e82e598000e0340c4d20b044600c00c460110b95140f54014003540294845040e0000c44400070810a1300361410116650164008804424a2000407055480708212070844007102d80d0003044900d0900c00029600e0166200744024280443c407c084002c0e510340003200116406280300d000c0d8040c0d89070541040e00102c962500035071901e40e4054014040351200c1c3c050070f28000b0b03004103c1e01e03402c00707008010400f282e8400d01054540c0c0b0000b41c1c40550401000100a14000140c5510103d400140740700c0381c004e080f004580c10204a42002039100d02d00070304483c000c2c01c00c207546d88041c0c17030514003401d8181009009092960100207082d0703080001148111a028001c01c609080340205408840782035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 61584544 1250 61583294 61583303
    0xf02071a16050702030a0210110106051909020f040b0406020c1002010203040c030204020a030605060f03010608012c07030b031b090705041d04020d020a12020114070b0601120e07080303180307 84
    0x4120281546001c2c40040050324005402e0794101c616580101d03145807118a1240d0020b0b007d05070541814400384504000740204550150f104860b044d03c1e0002c1142c036003e240f050942c00110300904040d0201200c00500b142c58800e034407a0f81c2c07441d010751070b54210003d281c000c4404000360b5004920600c00c40c1d10480d030140ac2c5901e00340c01c5409110094001e80580f6080c15500c00c40858a44c1c1c2e580050017418075980c50980d900d40c10034200070460141a442400d00c14080c000782458000c0b0350310030b86a4000780d2000b2020760780d502c000407005001d0014450386c140c01483d9141e01604c80c04180d09095610641e140303d090b444154003140e0354401c40c403c04807241d52f05200d101501e20b000c43d0258106000400001d0300403019000030300080c4642e0b02c0b0510468040c1503410455802c1a1540c41200c05000400c0c10848251103660b100d0000806060401c00d811201c083c103020182c0c8400d807424880c004a41c1c00341c0d1aa1500c90f601d40c81600c00d10071500c0d01e00f40d03002c3d045200000b00c80c03586610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 61585794 1250 61584544 61584571
    0x221011d0c1b1603061d0705031903030b0607060e0f060105060a0305090c120708060105010302070b04060e0a0506010f06030f020405033a0801090c0905010206010501120207060f02071a 81
    0x800c2407280c0a0580c4442c24015001c1c000e03814241c491140d02500107140146000242403195a2803451408800c0480c1e0581d60402d90f0104486d607004649402020503c1ca404410000c40f454102c3c002c0c8881d8025983c0600c0114900c01884155800640b480b0700c010200c50081540080301a42c4103400d101d0b03543e2001040100e14103482c826041280c024a5802c1101c011150b504000364944c80d0800c4040d40d00c1e84250410400d80b50200100da00501c000e00f4218980303002511818018000200050050341e140d21202c1305a1500b00030581e6203603086401e8580d156180c04503820402c03014429040040d05001803565142c80381d2084034210758004005080e88036004141e0101c1c40140d100c103040c05101280003892401e08150b4400510816607109100d0b581040c20500071201e020100508000d58484181300a903000074016055070803d003070415044100e000600702922540b04c00800481c1410700c000000d00f09a00501441845286968100541250080d15000d001c89807581c40642 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 61587044 1250 61585794 61585807
    0x30109150903020c1302090a0b0a05090d1e140123070e031e010902131404060f2901080915060f0d0503130509130f060209040221011d0c 60
    0xc655228600d034510a0040d039041c00501400a4810181c142411062580029038119140341a03602c4502a245046501e8100030440c4e20040c101e01480d1501401992540c407a10140107042d03030806840301014401040c1c0b01c004d840c0c181891525040124aa036084c81000720221140324031065444560700b1868450f40e42d001401c031412802030b13442581600500b030102c88220040000f4141d1401000300102f00c02245105000e030b541d50b07a40f685c0e180d6514048218003140709225600e0f8000360080e00102d007143c00c48c1000b100410301401c0c0e00507041040d4408203015802c095041170844000d89917820755940d4005204c5d11094950500b024500018000510300d00e00030705c611400d100c02810b486000506c65840714915800903004041810101030701700315501d413020000b54001041d2442c090010b409603034a4100b411003220013801241c0200e64a2604c4e1a81d50545034424145141403d0703807031064168651804003170050240c04844913807003000c0ca0000d00c0185000740f00c1401c04629011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 61588294 1250 61587044 61587083
    0x1b23060610121d120304050613050c091f0810060b120708090c06031e0c0915030c160312050916050d0203070801062309010303092903010b090f030109 66
    0xc40d40c030f141010b91403075020800c2d050420004440700d9407005840660b40d04003810064640314009080c040c00e88a009030b17441c001800071600741c0b02280195041125900c84000e80c40220007032065402c59103155040024401d4070010f8400860040d800080008a449172418105442820b020301d07410501040840c0b2000e2148511a9000000d001540c1100e51a44e0005000303074029100d002c0181410030602414000310408140c00c00c101c413120b13500c0c140369400482c40b0308900544082e080c0d14080001212110080111741054000d42440100c0b07054030328024114400000c0c00b948042d14040004011031030000e11880c5c1c5031108500c01725024a000c04001203403a065100b02c7e010b0089002c00140030328240581c0c00a07041c840030702207c2d802d090041001213540391110500c560306490041000c650003000c2c036415079010203031210a10b42011281401621026400701507040c00000008840743c0e244081d103020201152031094502c10700003010309031781e254040500b44024000c00f40100c403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 61589544 1250 61588294 61588301
    0xb010506040f12031b1118091b1201090302011b080408070204020306012601060215100504020304050a050a050c01030b03012009030106030209100e0f010e01061b2306061012 76
    0x1500c03030319068244205a076210702490707084160031507040c1c585508580312841c10b030161070300444041c0920701f807038588000410740d40c41d0040c1c0a80f4441a0340ca000340e409032100c0940f0200300e0f03c0750000340b1146a0b580b40090082450941c504656a0f9401c50545084e1080c010240100c0c0c1100009081012a4003000001c1d84050a40381c140034111a402c030100c111445005090780f282c7c6040030700741d8503008000e820030985c105c466600c40e800c01d041040c082c078248918070542d002070303c0041c1c40359994a440d528007a807041c00585184100180d0341c017000800125500501400c3c1e90500c030310b0300c04000703060030703256040c4003019400d2001b03074041c0701c55a814002d0f0166060050002c40c00c0365070ad0300454032100e001d8504100240d41b41c0c009000c56804680402e8018050f80c255099661420900e00f41072001800b40070200480c50340003240c5589182901d41d1050b070410902c4001070901481a503114410420b9800d590140a0002e041e0f031400c00e0840925914589580c034260b0714644507003004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 61590794 1250 61589544 61589579
    0x507060f05071b0920190c05030c030a020d0c030804020103050c1306020c030105090706090303080a110a05030615040b040311030a0602030106020f060f01030305160312180b010506040f 81
    0x1003201c02c0c080500800c80c4603c0451036440c3e1004025000c0342800c00c09403d84000401c180c8031445410078034912040d0750402c40b50030846800401e1000c40d50307014205c81c8407149030f40c050050300c00480c200b180c116002c002411182d00316001c45891401103201aa50080207134800f80100c2d49450010300594081e4002652005030b09440c207162640c4a0401d190002c0d09030403110050340007140861860034240305594000720b000c0001c3c1074042c6881001001b800b82d5000040810803082d0104a00d48001d0f00185200f0b1010030a0340e85510301c0c031800900076003003241c600e80f01d80d44244034500308a28090440e415640c081a900d13141a09540b1800840d10b80c003998203825100703000fa6800403550500c043c41c00b800403a400303800c01c403803171852141c54100c0c090031011110051000400000b41c0040c00c4030030b002611841100e07440043e090503182e0606103203c18014600f8401c10b416a0007910706050085031051105610990b259024001140554021104045403410060000d0801c00d201c1010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 61592044 1250 61590794 61590797
    0x170c0d090501020a03020a080c070b01261b010e040908030c0f0d060308092404030f03020a020306070f020f01020f04030204110c0304030804050406140d060509010e0303010e040309060504030507060f 87
    0xd0354410340e515582280c1c0911139074000282c1c0490161102c0340d01c403410303a811804002c40715040600783c1e02c40820120341807180d801c16199a440540b89100321034490400e07075a68109480340c40e13154101d58645290f51012103400203821000b408554a072a12421510b503400c0f69040341140c1d00c6072202c440715807006200f500e004030140000f80001c02240223540c00f440c458094a0703214082c900500540484000001072121180c015091007086000140c4041342d40150845000c01e0542c02c003641001807050000e50540182401c1181e0036400c400c02003030165243c0c0c01c40d0196100000814202c1c00340080b40003814808110400240c906908540c24102c0303a00091480c0082c403003c081c0c51544164801c582440700454104040d140c81d101f450000c0460361444c00aa820700d00015800608003c80240300940c2e8001040c80c200096002e840500041000c907aa6940c403088000000b4200300c804a0001d5540c0d800410003902c00d40c02e0302c0413650b200009100b65410a00d040e2205211004202e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 61593294 1250 61592044 61592051
    0x506030a02030f030909010f081906090f030816050c0604150608030c010b01090501030203150411090d03030902030705040e0d0c08090402030408090a050901051e03010b0909060106030606170c0d 85
    0x20050390301880200910003d2070000c40d56084104140101c51300160f01c4048142e284060410800601142d13400025042889020080c00b0714508500144112040a00300000c0a5803c104042d0441032083c041c6a40000300f4156200000b4102c5003882a050b15035041c0c2c02c02030100d40020b111000300403030090b01c0c010101c5c4c140c0c0c5454810b89075170041003180340c050f2344480d007061195822600c0900581020318040d03285d484c010481000f40720003c030300c041c0501c2d91440d070240442207075030548038000b000801e510200640313030800601800c11001c041c1e10a004104000616280501c80d410b8090081c1001d009c8000c507506095a0b0300d10000400c0d20100800c01035044a6a03c9100452040d489501d440351113901c0c0c04213000c80c0e440d098101c98025080040140007954400b4202e84103000c017050100350132039aa001013401341007024041a041021141400b10714200860103906817406076070100b0075a0b6682000707c1c0c480b04600e40000000c0c459001040044110400a108203a01d142020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 61594544 1250 61593294 61593313
    0xf0714010c02070e0601020601031709010c081c0e03070c12030302041a0304060c020601061e090510030e100b06030a05040516090c0e0a08030a030b01020703060204090203181f050603 80
    0x460940301e14005074001a003180303805100d0300e40c43c3c0e80c40c640c00000a1009000c01c0d030443e2b540a980340350903c4c4500440341e01040ca010540c0c030072072540440aa1280c030268603201440026407114a94541f404035007030521010301d1481d2000416500030507000320100900c01d19040c1d00071500e40720803009500f099020800071032a030f0722a8030580a40c480061100c0d6891604d4181101200e02d1442c1c408115084500108041030380001c0054400c03052100405040e0344500c001e56004686a03c065000341014003200002038059200082d100040419a403008840c0e0aa10f4100d1f420500e510380c0c002e805102140e8041130341c1d800a64070030b10a1080360b0081340e01100440c885050740d8411010203490342d00e400e0b05260b102820078200d0005403100c009960824201e01d460340a04039440013016501c201902c0141e100b001450010754000344c0840d1b0715615021444041e41c0b089401610080350716103c141000c0700011880b410000303000303810084803440c0c80c4d4900039020140085134544a001303c0c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 61595794 1250 61594544 61594583
    0x50312060d0614060906060702030715030f0e010509120a080a091403121006020f060a020f190201090201090e010509130821040b010b0a05070803070201090c06170f09030f07 76
    0x2510039103c450241480340703103029010407600d0040244110300400e42803140c80c0058a0000d40b02d03050380d0007845080700100e82c0f600100c0040554202e00c0140c5418079049003607482042d40414024400b12040e100142c8a060804450384600103030039000803440000078810722510303845554002d00c20006080c409480c0d80c0711a00e0358111030312038090b1645110600c424500110a00f80041085c0c0c005005000c800f410001c1d04c914008101d070341c180b1b40005a10103071026520844480040120f1410304e07088e803080300240208030084040740450a08900030480c491032058035070407070300020244200d950360125901500a0b110354122480170381400354403109160312107030305a031180e18080f111803440d10742441480241c040c0c1c0806c410b544208042d000c000c0d0b1100864003400d07017181c825680d07a101e0f880c0880c0144400103024004151405c004203860354014500010781049251041281e1a51003814820100a8554841c0b035402003103510001090729024041041c0a01c190b01012040241e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 61597044 1250 61595794 61595801
    0x60e0c0c0303010614040e090606240d0519060605040807090524030f0706030b1c1211070302091905091b10090e09061006020309010503070c08070c03030e040606020307050312060d06 80
    0x10520f108c1d0700b01108000d030a040c0491400112006180c11080000c4d003000c10a000d8407440c5050f408040e2200300041c00300107628100c4d108080b406004008040e90f941c00108590002d0040c014039004142c800140459a800303814020804429003d001c02110a1605aa1100c1060305034040c02070b0407007000c1c0c5100c140141c40091015482c0801c0e18020b2000b08002d50f19140c070910103000c0b445c002040414031590b448540c5040c9400c1a001035243e29141c40d1510701d0b13980c002940405028100582040c550404081c004034480090160f80c41c1c00c140710f5150400c62120200003460a80380e0074040c500030b98021710000071400e0500040b91902400b0112500444208090342d0185d0280902501078072500c2c00100b0192009e141404100e000080c124440a00751f90204409110480140002502100c6041750b2095240c042e15580e481e01400900d400c1501f14072940c03505a0010ba07850021080b10744259010010f546080245140c04400c0c40000d031005030080e05007020680000c14910 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 61598294 1250 61597044 61597051
    0x13110d05150c03010f0614090f0a0906240c0203120f09040203091510060e04020307050c0f1011070807121803060b1302190309051f060e0c0c0303010614040e 69
    0x1000380d502c0d81000c90140c000901644400200f01f002c808040c1c1c404602420740305890030407940554500800030001c0c84a00d540c0c0c0100440a18119000071840001040300c500140e403981e0b0004096000c0300c045e074689444840280d05034100b852125484010500107041440400440d54102a08207002c101281c00450b140300702e40d480741035251542c03e615401540e0100215628029041c10843d000740500790450302c040c0100e8000c40400c0e40c1500950030b135481ca0141d001101c140840002203203031350b5005c132101c001c40706203010b40d10b07094050a002220b0300c00e034005003480d26141a41c1c1d1080b03502c810f40c1700000f00300305c00000100409503084007a540294003840010511406500030010030807090890a1a0103204010080a010710000c4010305038106050000c2d0350034007810900d080c0b0050380d50062652513500d0104040c0400d41e03000c0340c155100078014016035901c0f1041c00040d48100c4415000a502c00d000401c5000d2240c4221548640d03c400b9050030140c0d0382480345032030101074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 61599544 1250 61598294 61598311
    0x10c080405100612080a0903080d02070209010501020606060901052206270f0302040902042703080603010b0612070c050724020114070e010504030b180613110d0515 72
    0x100a000c1070080400000201c4512108100031203032415110390076161040304020110311000c0741d50304040340502c0b1003170300850b00716580b2039a50101d114001c00039070007001e080344241581000410194400212584246000b030019494007540d14015141a0480309000104081100e00101c1c00000031803201d00400d080e0300c815400210500040d5101d8001740c20700481060011020440a01d80811917070849805607000141ca03a09400800d014000c81d003541e03441030040c41c00704407a02c3e02d088031890107940681c1d01c14200782c0300c403810182615101c8201d2540308030240003130b540c0c06d20340154290304070301e0a003090131100c1e0f00c03662514100041c0780c0c400c2028003005101c040302940381c01c618103210320940c4002c00c8040030450b1040030751103000e0120703010400b0791000c420391030f4010001c0f14091508000030070140c2c501111042e00c4004040321194140c010720011076809815041203035001940110f60900c89500042030110580780314070246e6191003089480104094a4014140601c02c01c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 61600794 1250 61599544 61599557
    0x142806060302042a020a0b0105150d060f051003050606030103120c0605130b01051807030209040f060b090a0b030c0a0e0f090a0b150a0509040b01051b0a020406090b030606010804050f010c 82
    0x9404070002c1e52144403004c42550001070f2280000341035901030506542003110454185003801010920030f0041c1d80800386102d19000f0003065003140d034150f83d4111a0110790905141804007021401e80d2001d13103815410410078401400004d00d20b0000f24076010b06454003110800c1c868071100c0540d00e007640c240086400d101d014005000c041c58000380548800d440900780b851101e00d0510319508001c10f074200709a40030030890341304d81c0d0341e40005900c41c091076400e001041d1550a00c00565101a04d0345114950700d0000207500c0000005076031240015015490910201c0c0c403096401c0c0b5498443c40f0340c011605c8201003802d40c0d582c2403071405002d204000180d0445c1d900280f03c4114108a0b0040d0080b000b80034005540394440103c5d548850b050300c020460706512001600c00c1d00582c0481801d0134100c5800318100f0100054110221780200e40a010f540e0b522024401210b01100000b1341642280e0001070541d4000e040c415000b84c410320840b82032202c500042800c403840203c201d400a0365 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 61602044 1250 61600794 61600841
    0xa140702030c130f05010e06010f0807020115030605010915030203030a050d2d0b09060a1202060c0111031515160c180209040b2b030c0c06090314280606030204 70
    0x10305c4c41107a003d040d20701d1000d145810120000b80c4407148080016082000b5800001c401a20030340150041c4c14254072402c140715200d03d0f02c000641402d000b4461140c3c903080030783d4002c802d444180d2013160b03000b4010f14a41000036504440507440041c02c0d00256441d81f08142007848403c1c0072020284000c400328840d6400c21503041c044da403840d980c1074402e840c40300030f0113580d03030382c40c8940402c0700c41100c0c80f03c09002c82d0b803012075490300801c44020815481c1510044a040b010300007548942c004001e1044545d0301c2204000c2241007290304200011803c0c0440d209011544800949445c06400c00c100310690b0340d050046601d215844105030a5000700e4a1807072400c060041c0c001e98001100c143c0c9201d00f5008400048041050070b0200000f8400c08520074140140318000440c0d401035251354456440d40c9025086040b2880210380302c0040802c10f001c1045c020515400c08405040f1502e100642e941c011082d1001d022010ba50302c55460340f0000c01a6124400d0003682c001c8070303464051155 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 61603294 1250 61602044 61602071
    0x91023030d020d121a0402031005010f0203040308190201090c09061e030f020d21081e16030b0307081501030c0503060c09060a0c060c090513020a140702030c13 70
    0x10071480d000c190750014092201103030300505500c1c2180c11440c0001000b42d0784251030045441900c0c0180e410510000900144014800c1d21506903070082e2521022041300740300403a640d114901c4068400c65090080c404d007228103584818550307a291001040f500709a46600101001c55442941d1840d41c1c0e10081202510000b1403c801c481e4000340d4045080c551744810744038802c4110005e2041c0c0c5080c410f241040151680c03502c0c9000035541843d02028100d00c080c0c0301c01070a40300d0504058081c0b000d240c102281d20000e0703100f0344071101900324030014044c096014200c141541e81d40340c0543d000120380010704022426018101d003071605103e5155090504840000c1e41109000350403890030000205042c4084a0441c41c0c141d41a541c1d943c00b45004482a80d44880024600782c2001c50b10f005a03640244284c0598030102c07007813514880b01c000030408900c142803120001c111010700c1c24101f0003000b00503000040c000b0341500c03607411889000403110644a6250003285669a031074500ea41c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 61604544 1250 61603294 61603303
    0x607020d1b090f0c0903081e04030c0801050a02090d02010f020304080a05011a0409030801030809010c080f09031b030c13020f0f03010f08010b061c06090606170a06030803040209102303 81
    0x301c0d0700f0030070140115082c010700000041c00040c001020001d90380190f18160312170106022004070500c1d84650300da1402c3c0000344064420400c582d801d00c004124402e00c1d0344200c0750350510003001544286181d6005440884026424100b5400700740400a4409001d110410b00c05100d40e00006e43c3d01007c00c1540000408000d805003d40d00c2c00b55010000f94103c0703c4c1c1d50560b81c02404e000c0c0c0310b215000049441c01c004850080c08000041100c20080390b4201c040c200c103450480c103444403204456210080c00038029440c0754180d00415500340da80c00e055500018a01c900c84000d4a0100308460180840c0d004800400d5840c4002004212a10100b03100402414541c0020f024010410f400510359016607104904500c1e190003080e4100042903205800402c0345400502240382d585401400e00c004d50000759108240d628009000c03202c96110700d1054950005140d030441c0c985800307011400d80002c16800c0a00b04042012400b0026030a050404551034654001400c078003a080c5400c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 61605794 1250 61604544 61604561
    0x30a090303140415140f0703030e0c0d0203070501030218040603030c02030f010c0509060918090c0f1c06231314061504020903010b040f060905060108070206060607020d1b09 76
    0x150b009010134401c42c0d5001c9048003070809a850035008403d483c0e00d074800b00384203081400810b03010000d4030b07100301900341e04003003442040f000540d48540200b6050111500710010001d600d42c004480c03d00444d80658044c2c054140405101034501108202290071603034140c10030380102d15941544070440c9020441c2a039201a900700902010900200c060b0aa0103108902485600c000c81d45014585441d48007224111140c0c0c00c0c0035060401c50380e1036403203520030b518150081084400701600c41c00c00001c1c0d01d0351002541000b02d0007901d15150071000b000c24004030b150741c81c0b04000702c079054130188400500030b040103c1c0a1090b5001d514000301e034040403100000e07040e040381042105000a840720704000000a8030056660060340c00003c4c014800c0080560340946020304a200603a000d07403201c000e07500b00788410402901c3e1a4015900e01c50700300d4841005a001400150f050700342070015200c400d2018018403040081540c8da107d01c080d08040007503d804241c01e0400c440c001a0040c00c54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 61607044 1250 61605794 61605827
    0x40501091d0d02071211060a03050601030b0105070215070303090206030711010506042a03060b040806060a0906050603040609080910020d02151314030903190c050103050c0702130e030a090303 84
    0x90350202088084d403a00a203104032158006100c02e51030030701511080b0f4442450b0f000b800035a8520f03542402900514040d80c00500085c038002c0089802c1d40210100e8012035001841000e103403034400342c2ca03071640d400090224105501e5900007130040e1a07210185004000548404042d07410440509003110f9000342242d20a80c20103035840c80780c1058880ba259100c0e1820a070b03050120a80505030042c2ca41c551141000d28800200000e21120110750745010b070320211415280191740b000c01000752402406090ba100307008201080004446038000c2002c54421b40c503c0d8207081d041800030b01036040003240600035030007440400c00070607414440110904944009107406040ca822100c04c0701111050081801c1c0c1c149104e4428040b040043d11b40244005044901c5500d1064803905080e010482c115024000c1c10000b1400d0f40c024040d00c3d2059841600300d505004031a001c000040ea8030b2400340c0c400d580ea54a003409d0801044c07001740f00b41c0800b522150712152441c03a004040301c3c0c03003124521 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 61608294 1250 61607044 61607053
    0x2010f0203010e0601050703020f0601080703051504030f12090b040303020a03050901090308190f09080a120b0312071a07081009020f030403050c0f060406060f080c030c010809010902040501091d 85
    0x2e071090300f42c0b4550010003c0c40d180d5154940da01c0e00f80d1600c0c1d00c007001140f01d81304640000806540002d080001e59104009442607100c40090f0310101480549008010801d10000c50b040d82d032085685008009a800c00800e04080545034044032050540d010fa0010350000303280c0380c946800d40a100d8102ca111380c000c00c072650b065103008000d0035000d01400c4521140d00c0c2e440c030780f074a480d400641c0440b80c4c90004000044032440d110320030b540540e49034000303d554441d804000490500c03030a80004c10240251100b4410700b00c0c2421160b100b518200c0314405590b61103c680101d40c80600c1c42455035803640c0d011420704500340c0041001940c0450000c40c0100102d04c504402c04003a65082949400c3c901d8844c3c0d20921000c0c00d0800726400e440103489008100414880c450304810f007125488050401c189850704050303a00ca01442011075016070000d10f030310f02075503c5035004951020910300001105801070740000c1c2901d00c01c0c0e101c0300c0c80e651200007540001c02400b840600700c840110040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 61609544 1250 61608294 61608299
    0x80c070f050f0d0b1e0109020405011103040602060408030403110610140609030309090a060b070f031803050a0f03020c13060905060607020a0306020a03090206030429010605040306110c03041502010f020301 90
    0x2862919051500802c010100d038046202c1e840c09207113101222107055181701d650741e114040c240c020340140c81030600084d090482030801100100455007500c0440d03010b03103a2030f41c5a44a803001548050812010058120b0810080d41400d01c40140900941851000342c98940307290310700d80840511280e48190800c0020044a580000803518000815a9035804c165074650400006103c070fa40701d07101c01e03000051603808019510840e9400d03603110391100a25030407580040c4a400c4614000102103034429440e080102e240d220004450910a10481d1010550880412540340d54900ba00489540f50342d414071103d2000c1c01032590110703041d030740e0508101035600000d0043d4140d11000c0c00c040e03800a400f00800e07103c2d8004400181d005400e95a503410300c1c1c0782c050aa0f150303842d182c0408030a130a8403041004584411035048a06a589030b9052900b1616188014450240004070741c080070041c0058112080c03000c0c10003414240e080240070f0300321040180c25900715003010300d119031040005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 61610794 1250 61609544 61609549
    0x60f0a0507021905070305070303020d080108060f010b030415060602160e090c060c0712030c060c08070f120b030609150a0605101d0415090f021903090807080c070f050f 74
    0x644880700f999101442d0810420b040413410100e00303801c041d010b03000d02c0e0800702c1415000101408995101e40e0b034003401c1c0c1c2ea03d00d4455250744007950cc01d45020a803c004100d4050000007441d006070045001840e140940d110540c200c400c2948080701682100b41000008000e10b01e60300b00030801010501ca991030300709c03059911446400c0384a489200045811103a4072820481d000150421401d41900201c45060203010380001140072108107050654011840344a0600c040c0940295107031840084400d04c0d09403590300c0010003801c4129550b4903100081e03a01044000e026a4059000c0e04261846000c0f40c207030000300401394074015062141c00c00c180d88402d440100310008520744004503140110048600c900c1d600d40f007582c8103090100c8498200d5503082c000c4200ca941c0102040010b4210301e206099000f584403801d071a1102000e0219494001c1c1c200c0f032003141c403500b64145810901c0e52040c0d10303908045001d40e000c5c1d12440d024004844c41c400071070043c02e000c40d1002d81030000f1400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 61612044 1250 61610794 61610803
    0x70306080c03061506220b3103030302160b01090203040201020606010c0c0b0d0204090504060b010e030c010503150307120602040303170108101109060706090c050406031a1512060f0a050702 83
    0x880a0040700001520f260510240341a014002413810030003c481c0d9031840151f1240e00241c0800d140462038001d0048000d50003a41e10001c0d034000440c82d001c040c0b031510183c009401c00161000407400304200580007611101803180038000f40f1100680b0b908180c0002490160010583c906001d41d044840001c110706116540072108049002d658540180c113454000e40510740c080040c5600700020f0100b0404150400c1031200020b0765140c1c40394090f9801c05580384051510b440c0813031010408a504041c1c2c0c00a807a040c82005400c0f02d110f65078400d0664849104d41c141516615800304003401010307032102044420507440d07850044594181b4441e20786400b05101031038441275813013a890500390041c3c800e5070b414020041486884280c0c0342060703000f030125002e084506000a40020030320b4600b900c038050649030009002c43d4140035415075021010340c050800c001034602704012007440d5851b800c049402d601d640d400b511a41c145001d44040c000b5010313188078160f40c1488100154980e0018 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 61613294 1250 61612044 61612081
    0x1309020306010504141f0206040204200a0507080403080307170a050f1f03120207080c04091208100e160e120d0c0201120f020405120d0801090207140105070306080c0306 74
    0x983c151103217442800174a641d040c0c1181018400d484020744149203801048651069000340c80a203d0300090400da0701d404102d58181d41201d000a00000120138801d8000e018041d201c3c0800d00e29054803502c1c2d070b1003560412600000055205400b4100580d040244542c00244a503024840360074030001005100c400101901032a180f44180e020701142c0c0d4010303140056070045800b54141c1c1207210000d4407101c641c001c1480e580b24004d41e44002d401d241c8242200160843c1c1000381d00301c004c43c0c0444034004c01401244c0740d040502d80c04a0b00300303a40005030b40a1b4000310703034110525800110280001c410308050900c43e04c081c0d01041c858403000f09180500400754030781840d80700c24520040e24a5442c01280e40c4a4034600000400704169550040c01641c100f1075801e8442d082c5240510750700c0c2c004030b5000e4002041c0e02d0042140c0d180b581c01074410144220000e50314416191001070071124102c4d480740010340c44c1d003000c004580c0d06210200c0c0f001816000742c1039501d0301c00c00d0f5038481003801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 61614544 1250 61613294 61613309
    0x2190f06050304060906050906070f020705030307121202040602010b040b01050a170a02070b0f0411030a080a0f0c061a0103180203060c0901050c24070906211d031309020306010504 79
    0x2c005400c0200c3d80e88284181e580c031210400c43e9040916500b59103e8040300c143c0003062500130072a500d10b000007a014100e440003070084d860280155218404201c0d01c42c0b1010500003c850440c0c1a0b44030f600140c800380c0069800081c00341070040400c820b45941e082c0060600000300020401980e100150510300c0c2006020346c042c80d103808012100900c100403010302100010310911440c5000d4141b183d0007075000e0f110107640c40c03005004154803903c01d2440207103884001c02042010500852282287c2e0900d800c29000040351604d4910035100b01c1c40e81703803c0d02020031003081d100c3e62305442180c0c540c000700400d413482e44202d0350210b81c0e00e1601070a00100700201040c0c2c1d0400e81c2c0702d441240c850030300c0142030f68132840b064013074403101c04003045454542140c0710000403000da100d651800c08032043d42e03417002210fa00c4642c6000411904904958280d0f85400308280c16910301c4080120ba010402e0007507030303520012006801003001517006440c0c05030041061180c0e583c0c0c8202034800f07603100c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 61615794 1250 61614544 61614547
    0x20a211101020f1504020906032d010902130c02010609060b0d0203060303040909081c09030e010e0f060c0c01030506030a050307230105011410020703020907110a0c0f0302190f0605 79
    0x1034000503840c0420300d403041c080c644030301402c180071080c0c603940081c0a60310950700078a140c1c6903141007603202c1545419000702c62040d40030403610015003010340c001d0040c50b1000006c0c40310842e0089911690410a9001c0068403071100040300ca60902c1150011f0258000c01c010042c00c010720041e061180c6044654110b8010004c42d01580e81801220010011180104150205894207580b00e40180c0303a00b041d40c1404482126404080b80296105207034555149402d0a00f00c1780196084030300d0f000030580001e036041d50050141c0b2420002c00701150350800034040107108900040c20f444006000600a400c00d101c00c00002d05c002040e139038804d500440450011110300040c01045100003500b141ca50708100001605601c52151040204016903000603000013420080c0c0c3d035521144402904603644c01e000500f40f600c50391244500140000175240d200030240c072150403a040680205501c1e03203c18108004610b0541900c94180243d5200c03508018601401440401c00e507129201c14400b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 61617044 1250 61615794 61615823
    0x5060f120114160906020607090302040905011b0207052b0605061507030c0201031103061e030a0506090607081b040504021b030d05040b0603120f09060909040302030304020a21 77
    0x40070740014040a0b0aa404854249090f83c41c0010840030600b4003408a96501c0300441c1903840481c0591082c000f40c0c4440400d01c0c0f56030300744030040070380304004da50715507950720a50301c1200030074140d02101e01c071b944c001c150341800d050030011950312559254289410301100182108013103050070700603641007080050306a5032078011a564001e0126000120b4000194610815801000011405000380c0e400c2040020343d001e0380707901e440203845032580403030b02d00410780185c11040c104211704503001e4182c0750790b0909640c030185800400da8100c00385030001000c019a0550003440258040c2c414400081d850ba124100d45142d80310318020103004a800103080c502441180c1481c4001c09030140449030b585c040314458800410069800b124030320a01e001081d05807400061b00903881105002151400c07040c40c40494082d4803200a50350819420301901d081940c910780301d18440c40c001e402650f52860a4410081b43d115680c100c4040d00138500589240c1e41102200d090304140d0001c9400920f65 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 61618294 1250 61617044 61617079
    0x90201020c0d0305070b07050412020f030316050705131803081e0403030c030f020a0909150e1003120903030e060a140f0912061b070606091a1305060f 66
    0x19074241c00c508203490850805920200909100d030180354070144036240c0d42d0f400c852a2085100c1c1071450468030740040058540060b034519102c0008040b2071030301c0c400f541d05040c8d20300164002d4400d600451020030990030f099107640c8051561050800904143c0c0c000c90b051820040d802400300040d1314005048441199915221550742c410001424507061030001c02038101a60b045c5c00080c10420702e071603041c10798026035481c0142501c5801249060601820090202c01c0752401003840c610000180600101ca03100d005100d485160418a421400c1602e41800c00c40e500d4420845080810808690b000481c08002d50040710f0a40d9610242d4504540b040d110001800c800d6600144800c0c000410100425003000c2c281ca51620040c094031009031035072400c94081d4000c4a90100034109000048020159548030720400151140c46012084c00c881c0051011014600030a002d107506180943e031401d03a050341c9400610142c0ba01c007001c2403a10403c00300d024010b414109112034210b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 61619544 1250 61618294 61618303
    0x4030509130b04150f170c04020c07031a0c0405010806030a060c23030903030a0c1e020606010e03010e0c040213030f0b180f0307020105090103140a0b0f0109050d0609020102 76
    0x100020006950303880000302240c01800220020b03446689004009007032550030040340d4080316001c5094003c0185070140445051450340c0c00e8615500a079032104245941e54406005004071540040424504601d849600445c00384561032614407044200000b021a00040354103441003841c0c18101a203e1002184c82c0c600175003001030499090010406500f54051102d103102c2d81859901d6906801401506c0c0d15844243d800340340340c0c2c00c1000050200740d165008504201100d00e001440c1110301e4a062480454070308035100140c00150901c6081e683c0f02460041c0410110b008100242920341c40307694450044851501491f00031400010200340300303050b200210b4108810914076102840c00040b1f20a04803120040802c424494000303461000035002203109201c0021850504660010b40740794101d120000d040684891a4010107401425814040c4240c08000304040c1081e00400082032821360250741040031840081059030b40f0040389500480e0004400244401c0a00040303091 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 61620794 1250 61619544 61619557
    0x140702150d0f1a041a10020a1704150e0306071d03010c0324030b01060e0301061a09100201020c0a03030f0603020a0303020d02010f0b0a030b100503100c0201050108010b0a0e040305 79
    0x16607140050b000041c2540380c00022821244801201a54065104120407540002c8148041c1100032100d0b4400b82400800711410400c1401101d18131003403036941900b045480d00701e10692a03000301d02045181c0210700c1000300c002c0e181c10801030b542c80310030202c0d6540c0802400c443c10483c0b031221501901407003010541b4000400b5000f8040010301a01c05800b4102007010341e5000071902803403110148604a1601c2503079482000303940664600364045a403401071b10280c6605551714000001d05815010800c070141c2e151200345901c1c0e01600c010005424203040810095900400901c00030410115110100310b0781800c00080c00c6c14800460402840c0340d0700002e4200315403140101c2410b0300061010380024542d0300904c144001c880452064510342d94440307410410740030003800002c81000e11035912441c0b92a181546c07590305c400080c42d0080c1000d00c224000c0d170780e0044030106a828041d5078050b140c0e2500902c0707051000303004600700c001680b28141502c03800704013140c20148a8030440d0070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 61622044 1250 61620794 61620817
    0x14030406140403120e150c0c0a05150406080901020906040e04020f04060e060d03020a0203030c03042405070209191109040f020c06041e050d050306040c0f080a021b0703050303040b0714070215 84
    0x8444039050700d40c075a60340803503548c20310500000000080c5458111809442c06040b08225800e280c03805400365400701000d40190b45c2c554080c0926621354942c03c01510090413101c560f02e11506150040c4408040c0c5201240d005a0524405120340c07011b2403a4640c0100069812402904580c2422030426101000c000d40c580000541e250001c1c400102600581d0f0450900f410710b02c03041c0700035510350400d0750300ca9000301e2410300ca40300c054901075400741e500688000d4100006042d240300c890440c0d4002070001030401d0085548911801c00d0301c42c0c0002507100c10320851a0810341030810350b4070500184010b101c86d1569465488012075280c3e60b0b62a03503804801c480704070080c03d1001c1c00c26002249c45a000303500c0d100e17900549610031020300b40c29500c1d540702d60a075034640c03254880182d80500041f2080c0c02a10180400345801003211500450154000d0754407401e003460900919100a4003c50400c100c00400300038628a00e0100c8480c50750403079616101030540200c207403050080841c0d41d80c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 61623294 1250 61622044 61622047
    0x806120129060a091202040b06070c030b07020c0102190303020c070602010c1b0f150e070305150601030e030a050a020c040c030c0210050705090f060714030406140403120e15 76
    0x3440034103148444190340d00341a00020340c078041d18103000c40341c041c00c18070100040c40884200041064960364144140c006080812904810008107540d9444803208850010b04080104244005e88803101d41210141c80a07045040740040000c4d52480c000d1400710300c4c0742c0070310420300401d802681240c00048030355083d200401d96801f0003070700800700458494003141d0720001c00000790b442c207035412031101da2004480180c00002e4513680c52003090b4956840a441d03598000030324244040117003100441c4644000c001d0510600000c100b04e09010f440c441c181030402c0c9118039071040c044291090b591041c41c01544881c81346400b249000c003403400c02600302c2c0c0b400306034440c46030741904003000403140350b000c880030400030030800700498000f25050b0002920612000443d45441090902c030808001d00c2603003401416100c441e0b15003039408040140c5d41c00058200041030708040c80a400411250582e801c180ca0364507a0b8643c0d06410f030140c0d04000800c000844240d4a03444421764880c981361030507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 61624544 1250 61623294 61623311
    0x60f090f020d0518060a110307030c02120d0207020f0607030207050d050114010e090d08070801060c0204270203100e0c01030506220e070503010b1807091701090c090903080708061201 80
    0x10380c0446031104645084d4000e040c0000c03020b810358025940d02c6854a542d01d891540c3d2030b902180102480792143c421806032125070032401e104980504613141600c0c1005035120000d104101e0401801a60300e40100030501442012907000703c4c030075080350800c1c1c0354280c04407014949580100451484044070b00031003800401d180c16502c0200344105d5410085a0350003020550507620400c0458125001440322401409054070030070844080d2440508080340b0a0b0500303404010000761802981744414802000708103504d001c001c02c00385421200010041d0300c001c02500c94640790f004400a060685a0011849070384803080c030090300104031503034960080c1020645601802c0092000d038810301c68001d020a0501e010301c01c00c0e03100380000f844018032454840c500341d44494024482e505016640300b00095840b841030000310000d4507900005000c0c100d5242941c3c85141c02e411024100f032800c03001c000000c1e0171800183c0c0005041c00c1c59601c55a13644005200c400c42c00264044035401c20088 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 61625794 1250 61624544 61624561
    0x20612130b0126150402120708121306082406160f0c050a06081f0b03040309080111030f1305120a050306030c0102030702010206010915030204020c0609070504060f090f020d05 77
    0x1200074002100c400b400420b20356003d1144ea80558205003d800c10060b4085401441c0400307010386c1105182054451719951082d500b030401254440c5a981d8010000781100f0503207414901c04051b1078117041c5079185d406e1440c400c007203500040d10f4550100441c3c8003806046e981d800c0c2526600450001824401d5009141182030022404400c030b440610214011495140c07000303c0100361900c650f129500742e52400b019000400302c01c400180601180d103404241d03100c40764015403003540030f034442e41003061912203201c5c01c56206491211002c0c0c020b1060100c0c10300ca000081e5002200040140014030b102e01f03040d42400e403900481c400045d0005580e0f0071060300f04001e18403c00c1c00b201514401c0c150071005903100d2056a00007070040c2c2001e401031007005465880784810720f0043c054084100d48039404a070480c2d0011818507050b034401030030000409010001e01010b001c05a43c01d11200e4500300c0107102a075042c0c0103d8500c42d4a942d461b8032081c0060b8103a4400c400860420f01c8a801c11641 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 61627044 1250 61625794 61625819
    0x2060313110603060303122e0e070504060906050721090e0105030703051203090109020a0605071103010c0e060702040207150504030f0804050a030806010e040603060b03010f09020612130b01 83
    0xc04844050014010580600d8100705076841608040e000d1842d000c4003020640f030f0040010000700762487d41805290b400380d003a0150400d0715140c4405680050704004041c100e0000041c212310400074104024805194403200d10300c12039009060007520ba100c24904450f030115107860040441548031a00c3e20075990000c100c40442c2c00000c4080383c581d03222810306469044c14080540141c2c4142c0060004510a10040d81d011850f000005400c03400f5900180150309075030b10007400600082003940900c200e501c031540b9403101c100e0080000c1d100d0100040c140844565919200d01c8001c901c04040d515141c0490f1035280c1c2c461000c07100d9401c0c000404001b4482900c0c150009444148120506401000700c1030144d03030030100404400c156030b81e0403510354400503c894100011604c020055845500403003000c0c5109042c04150b004e096020300d400c41d20000d01030481c40e8206041000561103010440750100b070603003040340480c0c0e5280602d882d03e101013040104815915000090316100911 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 61628294 1250 61627044 61627081
    0x9050414010605030a23011b110102070809060c030c06010803181002060f0705040801091a0106141812030d09172d0c0a05030706060504230603010b030f0a0c0e16030209030a020603 79
    0x3c27103400d15000802d807402d080b4000ca49000745001e104100c454441c0c41e043d4050718a000310752044920b8415642d0b60203051682c01e0b40700424581c4041001654052200c901003a050401e80344001141c03040a4000d40c1c400000c2c11050440401c50045490a071240f001c8601925802c0001e00c0078490a1034610050528200d0680000c00000000300d00d440c85180e00d00804e004104032141070034200742c081416102d00d24582d690285107241001c40109050002c2c00c0901c0a40f48005201c11050404d10048100002460040308040002c5940c155514128003070101d042400c10455441c1d0702a1040540305501c45460707240308034200e1000700400080100031403480b9150074071440e5540c105100c1520340c40f0070014266500d01c1070703815203144405010740d0b01c442c0c02000400c8400060000c281800340402c44c00c50143c02c14040c0d4001e000046005000804001c0100d003e40e04d0300400b070310a80800405502d0400d80c000984810030341d020414002c2c1c19400a080d00e0303403030400d022040003032002f0380c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 61629544 1250 61628294 61628297
    0x4080c0f150c03131106070c0605071104020a14090d1a01030309090911060a03060308040b091c0f02090403020f0d0504051309051f0906050109050414010605030a23011b 74
    0x5400080d41000c070307001500e002c1c01e210301c901c102d1502e4a85d0f41000b10a8048101600801c0500094004c034a03401c24043c010562629419901e0505041c014840c01c0d400301224001d90042001003045a8000001c1860110344480140c50784040340000d400040345600162805200c40e2044100160400304141241d120b92102c045180d55641c4040039034007403640142910076150006050707070400400601000c911841c0001d540d54883d0f071601e5003030f00705070050843d02c000894181102d0410403200b004206220366448070010085d030b14803042000301d0700300900445c0c40c0400314080500070404510140014030540d0040005101c0040240e00300303114091195420401503440791200c0d11428180079000f0020340005940e5104640c030b04214014802085035846d503100c404a042c81c49400e0180c54180000314071400e2134108a040b08058038002a0164500182005290f900080d05100f107640403546116820803d0706c1660ba003d444609200254240103e20340b10004010088100c18030b103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 61630794 1250 61629544 61629583
    0x3020901090603140c03090c0d03090f05011d121002030f1e09120f0d15060206010501182c09010501050310090c090209030a15050406050a09081204080c0f 68
    0x140d1104406441009014403c051340810106188036007803c000d541c03000340042154400380036a07002c00c1103044000402e07800510740c41c03001d00100c1080758176800204000d10b0145406000441c0c90300034040c0340301000e40710701a50303c4000d41c401424000303d440072800e404210349900d172508003100581c80880d0100b002c0440900121140310b0300c0201c060040c1180303070040291000c045c20000c4075910006050858407018000001072002601840e4104060402e50343c41291600310f010345450410380104d410701c40c128000304400c01001c0e030781d0005c54500c0c4526400406040484030702088002c2c600400b1061042c0811441d94015000f450403944150100c034a802a5503042000f00d0b44030f28001080d410f80128104074441180e000791004041c000e06440721807600d0f40e280c0085070070038034800401e1a03e8008200610640307200e02c0b41c0c02030321710381c080c0a00601980d5066907480740091205400b4854804541407192500c240d078109010001151009041c5031001b40d952220085400c099256 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 61632044 1250 61630794 61630799
    0x30708070203120307021005060a1214070602060124030207200a051002100b0a0909051506010504030305090607030c0204020a0203041e12020d0501091b030203010e0c0306150f03030a0302090109 85
    0x122075013160b10441450b80a041003600d0003c1c8000075000c0038160b20703480000350f0000709825102186e00484e4902c103031810703a42000b41200c5981064010303030020003590841c1c0010041a0110310320310680007205032940c015010241400c0d0000e0203900340140c41880da4005105035607000661400c1120002c07035000004680c0c6104012001c0c0c20307898100300603000040481401e1803203800801400400a1404048a0300c980d421021504421800d50303895100c2ea4411541e2a404208260080780a10309a440c043c19501c01a0040c4140b42002d4021400003a01c0b0007414800d000382d20100764014020f542c2d81c0a0790100a561f90090302501c1082040d50707601503940c80f4078131400c500300d500c007008820340c0702d04903000c001c222180c40409135525502c031841c00002234902308007900142000c2240140041c10350040c942107036000301c0890f5183d40701809000c0603503000208981e001007000c400340300c40c1c3c0881e00402c1008030b04a4009400d0310000c210b40c24401e800d43c0103071842c04002c0c0d80300080301d907 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 61633294 1250 61632044 61632073
    0x1c020406110d05090f030c04090c1a07051e011b0206220b04060203070c1a07080105030a051e01020d020313020f10120902010912050705040f0605010509061b030708070203 75
    0x4000c00e404a0201c3c40070420402281044141c03c002c14000034140c0d41030450075070208040d6041b48000322002400150300344140c150b003400100d40c2d02120750721f840c100f544581d6003940e11001020786480901800418014864013508100b8880411024070b0074003400c003403c0a540c1c1c04c015a0a565900e0100c0059192084800507000f060340d00b284104145403100e860346002580058110340c00c0002c005014404200141c00001060800c4a02803a05140040009010340b00c180c00c1644603400c01c0340d0b5400072400008490804620030f0044684041d4205085c41c0284920b408103000c07640080300304050040480d0742c1178542170095a030070040740400800c0080007503810042c04003280b0000004041001c01c1d50005032003a10604049035000e03191810180c001c0301a480803950350384514000e002e1401c15010b00c881100825502307004690604001802c03a00404d00c800e40549001701d02000004e510341c0075180f56800c4001940c0e0351f12407505250426501c00c82e01a8002e10034025a01c0041 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 61634544 1250 61633294 61633303
    0x12060e100b0d020907020114160815030a1106090d0302011d2e020d02040311030f03040501090303110102130e1f051305090f030409090b01080c0d030f03021c02040611 73
    0x7000074412003161109500304100d030070000d04010119036a401d00b0a04c01484040124007600c1c0e011400e036408242ca24004000c3c1d40000c041d0700d510015050581c140d601c2c00280107445692016004049444000102d00d0358040e03031003a9a1b025000e801c0480070b141d01948100325000318000407022030b00c1d00e000000c1d07555203c1d04446018a200184800c0c05010201c2c010804455240e0094130341000708100c001681c005420564440302e4486441d1500e18003004800308468100002d942014600030018114544502c4041c0c1485010b01c4549489c3c60f080d8119401d000a00a004450755100c4400c1101c81c802215034410b00811000584010141e05641408030f030720082465100300d250715035a00103060043c14241c424030500749461641501400a40007801101c0340c00035030a10325050104c030320041a0f2101d1070541101010700c11035144d80d1400c404490300740c00c00c07040c02c500c20741c0304030b00074401c1c0d401c40390f080e810b0380c0d0f0007144009440d0000c0c0b0480710103a03038540d8407200c40070807941c85 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 61635794 1250 61634544 61634561
    0x6030e0c150c01090507090b0f010c0b0114060c01050405010902100206010e06060708090406080d0e0d080304030c2f041a010e010f1101151d010e070c060612060e10 72
    0x404601c0c0d9901048903a0001441c0d024400c0001085138021595414070380155074005007a11030b01d030480f0042c1c03418460707503c0d04051024600322241d01420b0700c0312030301040103001e00340000a00c4501c55400f0b8032110b0450b400031001d8002080f1038030701401c0c454000c0c1160002240f1440d03025401408603440013841074140c810070308020700d070b5072240300410409078048402144c4c1c448090240e40c800755607502c505d40043c10690f01411a002d03102d14024004010765107814424248007480001041daa0f50a403a44154181040e0000c80100d051000f50007103200300340c00040e080b5041210444c1280d83c00300c0c15074036090f10240142468080015402860000110700045080c010502150b11075031b00e585004a035401c000010500100181c0c0c207580d070350a01a080703104080002c00c8105980305031040c802981c012507811550609000c00080c0318050005070421410700d03055010312245a002e21f004240c1042240030b807010300c0c50120060424030080121501074050f24069905803400345404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 61637044 1250 61635794 61635799
    0x30a06080705060f03070c030c081207020601060906020601050904020d050706020c040c0c050606010e1f0903050c0102010204030203071406120108010b090604050106050406050d060f03081e070309030b040f060c050406030e0c 98
    0x469491580444401a0b0ba11080c3d08001c04000c1315404074010300c0c028005c941c50b01c50f2f48030040c58a14800392030024103038012010446510020850598042200c5040da102180c041400b620340f800083c1c2d1400d40c0690203403090140c0600014080c0c0c001403140128502640d05000c80a2512410758102103040c030040c042d80c03c5040010025880303081c01000e10140107040031480456203454202e482c0500702500041249100203000348032003003285804d44002480290300d01400d50740400d89400d1a4800c5940404800103211342c2c60b07840c0401da6a10300014a24040d1941e554100a8080d024906420b0f00a0b1b402001041c00382c20030740501c90581d503450703d0300f03031a151402104075130315440214001143d0350f6039500800c01a01c180e142c0c01c001c42c003400740315480d542101c1f04011003503024041407450b44000c003c02c5000035041202102241d4101c40c030441543d175907003084002da0719103207001842c00780380c01d034850308c4190414050400e480e0036590070000c42d00f03140c40790356031801ea03c000c065 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 61638294 1250 61637044 61637047
    0x60507030515040b010c21090506043206210f06010f0516020d0b19050601091503090203010c0315050609212407030e061905130206030a06080705060f 66
    0x400034145030b000344c1854181850325909880d429103c50044143d4458600c1011a407400c040c80060b5106030070401401080b511186060324005030704019452080203034842c072240b4501000d18405040c2002c0c0c230700c00040d084603582e405c0441d440300c1000581482004514620020400c5160040d2515102c1d00040e140d1000d0076030040420749894000000070751502d00c030b06c1d40c8030005031a00000c0140080c440d2501ca1a00e091102d695072501061400d04240b4501d4202000816a40405824204c1e481000e80c03010100b0f405204034050305018034060b4056091140800c546030345903200c80c001460484500560540b10300800c000c500c944118a030384030645035844410000a013482941001c1200110760181030500340c00415844070341604140b003081c440030042480d8144c001c0c070948094440c00f900c0c1600d006503842d000e1103c4000d665000543e580000b0f01000d410300d2a00c40c400360003c09060702c80c03900300e8001c405170800b8040c040c440d002e42e150000703440c1049015100003941c03124071036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 61639544 1250 61638294 61638331
    0x50309092401031802120c12030a080103080901030f1d2401090203060a0305060108030702040b01030501030b1b0904060f0f050a120f030e090a020a03110910030f090215070605070305 80
    0x44004d0700d0424020700e5a107110700700303920040c2c0d562100c0701d000804042c090241e40107520200801d0a03142d41003000290010801e000302c59070300c03a602c05c6c1525484848035403128020320040303009000c600b68014042e0724210101803e24041100304084140040c121030b00001c491038084c21040c3c0d4a0082010741d218080148211070103900a10f61002d0007600720011555030362a0750307150490a030310170310041d040001d224095007414002c00e64120350a080c14849549940d48006902400814500c050184210780314100032180080f500101c00041081c031003180c13a002e40c0c054280d414840c0c0f00704490308560015140c00c1204948046804104404050b1000340d00c9030280c07103612031001c03020004903841e808119503413950010b014a0340010010b898242a603c094116004280468424941400303204459604d40700d032542040c54624000c12032610202e0410080d000fa814000d50080800002c0d00d40e403002e8102519103280140014482620b40071000e43c1120b109407004405c0781001c4100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 61640794 1250 61639544 61639547
    0xb040507060f0e0d1e03050d060801020712030e070f0f05030f0d020307030f020f010c0503011d0402030d0c0c05060c0607021207110609012f1e0606010c02130603050309092401 77
    0x40044c0c2074011501c414100ca24041c5240c034030400b0b400e0072000304401103000064151603104800143c901c100003140345c10321a407503441a80705040300710340c10151142e401c1154000c05010344030003083e000720f1800850381c5610f904030410f2200e008550081c85010300c1480d11020001d0070603490007407900910301d04461505e0449d0901c03020180b1105601c6a00c52500100d0700c00d22401c42e0401c681d030b45950312541443c100c641d06060b81070301c1c441c4603070790032040c07002580e030115081c00c14482d907052065503032406240100288880303a201070750101c40030514031a65280401c5842c842e07075280c1c6c02e444150b504051445005d0084032070281403130310305d41c1fa0303080c0e5030410300300030026094141401d43c82130481040d14030b690740c0e108601441946540d0a0700c0c2d2403202c01c01004e07254442a000007014255009078030351381c440000302198100706040e0f001c05c096440c6d60581804820f90b41d482800f00700d4907030816961360f600522000d4000d80140740010140e60303030100030b6403080300c0c4580d4410b08035020200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 61642044 1250 61640794 61640809
    0x1b0606041503110f0307031401020d06090903211107050a0209220201050d0b0d050106090b03070501080a0504080705030c0604051c0507030e011407060501051c150c1205040b040507060f0e 82
    0x4c01c90340610a100e004030119400011110421154034000344e51072400403c902c0c1641c0345070b80540381c154280480d40c00020b0300100c400c804181d264441c2141d03501810140c0c80a0802c0343c0c0804050309000400c80c05010021400840c005c0c000c0da41800a61a00d21410070f50110031600d4582030b04078441118010343c4a01b00500700801c103418046030b0348a10000142485e40c00100c100c0701c9079500c0108100c503144034002c40d400150b0032001782101038503003000600008030043c400703604d03656540d0004d402c01407060140d81503142c200c01201d032070f043c811540300e0703540c0c07070544e829a41c45c81000d42c424081201c410001104400c5d80d9101e40c20420705682c1a1035258900c0072490500c04410315442d103030031006019010035070103004040707400d51610003440503564038a1203507039140791000700e2000030031b0580f40d411962040342c1c0c00000b00d50b06040c82c1104e182200080c03810486007040d00f07000910070311148143c0520b0044060750030180c0d4a075001e441c0c0b94000c035800b001080a140b2103034928900a103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 61643294 1250 61642044 61642069
    0x10050d180b090604080403060c35010b03100605090a080109140f0106140913150906050105040c0203220317040303030f141602030f0307080f0a060506070209040204021b060604150311 80
    0x900c03030411000a01401c210801a0030312502c202c114078034450f120034603d0b0149004cc01103080c4a0f00c0c60034154211501e4a207a4010502480790002c2ca581840e1600780350f09006001c00703070080140820394603145003046500007a0185d00d05c90000c1e442c592507818802c40040b82d13865800d4540031440d034020f224451750300030625840380070002c2c3c1a1010844c040c0780c03c903500407603480c00210b40ca001e140c4001298810380056004070321700030f10031170380c10303000412504a95251003003080b014005100c90304041d02c1c203410040406114a5541800ca18160080c1c010780e07101b03072801e111012014110008988c403100d84820419680004107908801440101d02d00c0f00440c030640c0d283c01c2e0349000040941c0d000fa1115400121404204041c805003410480e0300140d20710700600c080c91509000030154003c1442c023038400c000500114085503540d85c1214102118a00340c03000304140c0724a029141da06c01c131030103405241002000545c10700240311440a4a03408203001d00742c00d0300c42042c8040341c1c1061 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 61644544 1250 61643294 61643297
    0x528021011190302130e060a091d01060609031403030f0c0903030f0c060105030106050306070f0f0509040c02101104030b0109090611030108011a0a06020c10050d180b090604080403060c 81
    0x30440640d10030240c4082c6a21074445450142c1c2d03c580342081d01050b03510590200451480a00c2400403d5070b031750300441c08485c960310010441d014106035200ca03028101101c000c4030741c030381503001070415042a1040200ca00810428203081c01c03600e002905d0703120032154480000c0d10140011205e44600c0058200380b04080d041328186402c048004843e50f200c124042d960354403800041000d031400f4042d110103090150007406250403e860040d00d0301300801210003d00c8125100448031a1054082d20380000d00200244918840b03108065107c0d2140704581c0a084d040030681d10703070f08002070b04131030031a940600e5042c1030360320300058803000b00301420044807030341e0700e5014028203e174112019501806d004400005c2031001141108031004140807041c0c05861a581e08100003500440d411002d00800d0b00d11041c0c00481d41d50480c0c683c801c2c3d000030001e00340b41444001c4180580c480d690002841800d100d9107680710010100d0b5a0801202c00130300c0c072a000c010078800240103401200011485 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 61645794 1250 61644544 61644547
    0x2c0c07030f120f05060405060301020901050304084e0112060b0a030b0910060e0c0304030c0213050a0e0106090e06070c0309081f0f0e0601171006060528021011 70
    0x6a1125010b44098240e100f034100d0300c1e0703030074002e0303c0ca860310031107800c0f800c114000c6180c2550400040d02d00e00000708040e18004001c940071040e45180310710303529803030483e61800e008020035000c0c3c04102c030140200d5441082d201e151030340101c01040700747d5040e5040303240c0500c1920b00c250b9815016201101c5c085400030003481c4008000fa0342010b80600a0096170041e081d005102d00c90007048944690200c0d110315950b600b4042e4001680088039041905440d14040070a620f0001c10a2101e41e289945820f80c60401000902d07001e80e404000000c002000a00c0085e90f50596502a121008988506900003001140348240640100002d0511a08080311510f54800c0c0050500d00e040e07450300e000742c4624041010410251103080da04031481c02081244a100d41c5440b0307903c207014081d44180076203001d00c62a00000c1000406c2000404820038000f00303485410080442c0c1050003204404213010b04040700c000d0780010180407004180c0e000f1700300c140c10f421141029003014002940059070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 61647044 1250 61645794 61645817
    0x1508010c0e0310140105040b060c10020d0b01050403080a0503091905010c030c0c050604020609010c050303130318060512040213050708010618060509091e012c0c07030f 74
    0x1000c0c06003a20200541d22010710030142034041c5810308030039415a5118500e000454903080805641c0a419254207440014a1042c40404290180700c6d034030701c1d180c1e548035149814032400d120340c009106c05000644188502d00d421801503800d80034038000144521401d22135512a180b040018543c4124560212200c44400702c100e40d006485409054406035129500380200341d070075005a03a0f0262413841c113004c41701400e807a0640c5452024100900c0344800141d0300c04540e00c02c54a002180b074014013500d03603e0a1043d00f40e59001c0f50004100c01003140c61101400c280c040f140030408445043c0c8a261802c45c0d4076001c0024030400038412603004001c40782c1c140c0707508100d1060700d01c610301070348580606505200e0084e0180c0030100d1003a01e0b901c00e0247c148189980702d41620540741c0141c031a01c00944034101407441c5031030300038104406401d46400004e04912070240703541e07955035403d0341d21111036800c214110840c176045900c0c401d9044104846800648921034a00300c80c0400d24003100c9684 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 61648294 1250 61647044 61647059
    0x803060117070302030f15010c02040b0301240807060c0b0403080402010519050d05090102090f010810050d05060f090102070c0b0a1808010e0111090901030f08160b27070915 76
    0x12003502d54400095021042007401c264648038142c0284403298a021a00c200000081140003e8280207001c0e030744444600c0e045031803d4008020040c010304205018154010080344000c030148500c048612903094001600c0d4010080007100940203146082c2c0c69590391002e40c6d40060140c0200c3c10030100f00728000d03031a800d2411140402003142c4c1c49554400d060703110181a0380004e00012400d07441040034199507500d070003c0000100c002e09141ca629510800c0700000056242c0c02150400d682c00090802c00c040407451a101e4a001c2580880c51b4548180890807070044010041082041c40300c180f00b065070b8040a00707468a40b0b0314000c40480140c02d9207040692103035102803004d80d15615071042e00c84083c022401c41e040040c070001d0400354581d00241c000360040c0300180c141d000403024a0244065041110789a401c08201c0d0460342005142c810703100c140440f01d5003520610320349460010700340800c0c000710038540b1000038800541001403183c001c1040c908158080a9843d20014118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 61649544 1250 61648294 61648337
    0x902030f0702010b031552050405030a031209022110150509040201020304030501020a0903030905040207051b0d020a030c06021507020604081308150402150901050708030601 76
    0x4480d84118040581003010001e825200e03054080c070b120360000041042d1b1891501d07602d9038080311200000c1c60120301c100c4800010720640c070307902070869141040c0b4052440844144e030f030002c4201200e0344156000000c03c81d03490080d8090194550011903a0300d011a02c141213000d1821151480015801c91a81c0041d01900290041a021505281031a00314002c184140b122180208400344030000076180181100102030040900c00d11102000c1001c0d03910170420b5030041c0d94014001c540e02c0142503030280148416101c11000103031045004180350516000b41c40401d50300c580100400c4181c0740a0350300c0e51030840710240d00402d13003030040000741e6100544840250300503136807608580d00700b0100030b04066075100c1400b10410b21409001d0440d0380064010f074059000000e040d1241c140514448001c0e040b984103c1c9544104843c4c0c0031301e1140100c1e510b014500c00c40d00385071410b0303900f208520744d07010b40707001140403c005000c10790126007003000865214405140101e40e00c0c02c000380b11300c5807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 61650794 1250 61649544 61649551
    0xf050f04091a04380607021504030b0702030309060105041b030b0f04020a0903050c0d050604080304080f030901050603071a0901050c0c04090311010605010201060b1c1b0e130c05041707090203 84
    0x30b040c01610f8001901395a0007840b88000e0100281203130b44a4080403603002e10035083e0080c0280b00d886069041419003c003a60302071640100080d150341081c4100070368a41080c1d035440c01d1030045000000c1c251400380715086150500c42039410360411608000d5000341200382c400c43d0481e0100d4590011381c6e83d544000c10240c8140e03200c020215040d414401d1801d46a200c01e2070250641401c0d4601143c1c000968aa00ca94083e03111a82e81c0e5440c54980020700440c02c005495003008024881068010742000d0f21401c400e80455118541d11010001c086005112081c182c50007000040c8543d41310300c0090103804044001c503503209042101007800c9580c4034009900007000c030f200400762001c0c00c0c0120401080240700074451a0300f015100800c0303204101c00c000072000035804e80040711901d038006006010315090800480d2018080140403540720301c400d00c0c888c9406107800d51548016202d99a40486541c3d80c0764205402c0117901c1c0280c05517040e01c480c0c00c1c403030050001181c0100f070000350310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 61652044 1250 61650794 61650821
    0x1051e04060503421315050f010e160504090b010e0a08061008070501020607120b030708060601032703030e070b0d091e050a020f0a0509010b0a0f050f04091a04 70
    0x103503031004070034052180c4c1d501c00d01c1401d0324140c6020304022000722400706402005005007240003849501d403140002180c101c0d002501401d002c2000180c2c4070b0b4081480c120b8512089211245d5541c04104032002040034074100072a0062005110a02240e40800301008041c10580020300d00b42001401c4a480382c1c1c082412540084100800c402e10440fa100003024400001d0000600700030000c2d4607220002d0101081000042da1249622241d81113902ca40001909641d4413984852181e03031a8a411120580481d05048800d00c004012019070b414080301c281384030f90044640e80d801c6002e4544040900304510600d00c0106202402c080103003c0d207405c90724000354106252502d000f41500b44512420120307044000e4074040780c004540c6080b12340d4111201c0703070442d030441e000403400390207900034640004101002044400e0010014561080541c643c010b01c1004082c08440522410350801030f9100c0610040180a00c0d0350810f860b4100c04e00da2681d07040d65802e01103800c50385010622070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 61653294 1250 61652044 61652083
    0x10920070b0a060f0807090203040312050708070810030f08090d0b0c0a0905060301081e0102040812030f0906090a03080403052502010e010203160b0411040c0203180901051e04060503 80
    0xd803042c058030682c00140507000b002c229144c5040c014640381d4206204d08107445800100080406100b00782c00c0c01d4090000344104030310705003024000e002e0034048942d02c0103d950784001c50300c4c08051141c11012681e2291000d400020142d03200035090700714041d200d070001c2000c6805400100200c0b0b980f88034100440f0010b880d0700360368500400164031381e840f490090b8410030060019030f002040e450008800030b4080804001209103e0340280302e42e44c0103c05038010541501c0050340880003c1d4000c4248038000b6425441d080c0c1c03219111074094519001c3d83e0301100c0c400740000d008003859944503003c2d08209050040d62000d500c0e0406890010200c24101e401c040021580c101d0fa800800072000c3c4011800c01c0b000c540035221a0346544000340c00d5168110000e0304020406480010143c030140051044608047e030180d034941041050000010507003a461003142404035132181240c1000f4007011809103001071080207041c1d0042255001034458802042a0320100160207551b1007400c480f1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 61654544 1250 61653294 61653301
    0x810050607050f2a04052e180c1d030a0209090a0b010303050301050909010c1407111c0b0f040302030a030b030c0306010f17010911060a09030c030503030403140909010920070b 77
    0x116044600f0204d500c2c85246080c1c24003001d144501968010050001a86007161002c03049112641c152580000c0303040c090084103401c207242c03c3d00b100410344c0450300c51081d101c0101e20880d001d11034000301c181d016807103100c1407030152801000094010048a05660300410310707032100120080260000c0d00072480000042004e4105401d81d1a8000f50060080000c2d4003040c5004101910300381c0f0062042601203840310500130407203503c3c04a114020118041d40040c5c0e401e0315000f110003081a0742c07444080002445c5955035024045c440c1d5455030240d0314040b09000203038018030030900155058894483d5104940c2c0b0100b02d41d0380a0034044c40d00f500301c0d81c0380c1155545590708202c40392000fa4104005440000d40001000102c100125101c2d522030700150012034040d009d550000e408035803800000024010013000940c01340b4000d035205801c8515800e1001c03810b125004110ba0096260750041000d1001c550000c44038100e0028444103030540480d0325544c94018002c1912405001d0052 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 61655794 1250 61654544 61654603
    0x7050c0706030b100f020d0522080a03030e030c03030109110702040c0804051006060537051e040e06041116050f0f060106080109050916030605060406060810050607050f 74
    0x1361070882051038440c40210b40100700a440700c0041d0500d20034060041070705942c080030b007502100c0c90511203c0400749207981d940352a50320000d41209502181c80c03c2c10150124801000300c0713641c00070280056141d070b460302c0a60b8000300415000a00d02000074031030007005a07500d02400f105068296116200c50900e403c0c181c0c1014501c01441a04600e00041009290b40141c16145005905c489103082c55070414900d40c060300c81c0058214105444480442c000c41e001405800103c0c04c440b128803203d0b0622400b03948034402d5015180c0715400401c00114949469007080b0240c0902e607060a05000005101104c01c0e10403110445258000e4061584550381c100050100180720b03e0040c03d56515195014014503418004c03030511030b80791000100021001c01001840140491804c030030141c0c1ca0800c0d100030f04080d10968031460801d01c0004006209514072801062081400c0c1c070b483e4646803c0200340e5104000445031800784a4004a1806042c000c0e0b008030024194980c0309031014000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 61657044 1250 61655794 61655809
    0x20c061f1404240b13060201140105040f0f0c05040801050a0209010c0206071103030304060501170606030d0507050a08210109050403020705040c0e030109030201020406030606020f0c0103020307050c0706030b 91
    0x10144440a4210204880300810100c6a1510800d41c0c00107800f403120410303003198105154401480c240c010600244d5030346100014890300c040e070242c051040d602c81008a007a1070b5400709400001c1c41e140c0042c0400c2c40c1c6644100c03003404610303200045841c100d12000b4141d0710801c078060f010820100c0c1c00c00080c2c1081c0502c1e03a010940c80f00442c588242540082d00040d46c220f80030780524000304d900c0c010000c1020300402c00000c020300700e0381c513841d0926010020780000d000e0509810488080b0340171003c00010402e02400d0002d003e08072083c415182110a42c200d10020b8a441c401c0200c2e00c0041a00c240042c4106444c1d09100800e0324002a084010703244107038400000c05181c801008046980814510181e0341c00312008180d0b04040442100d503000e540a505505500c1d0042c1c5800b0550154024021291142c500303011550b61480281d881c4c40309902202416084880e44815540c802d5005643c070103020304145081083e80743c6001d02e44406500508082641e4030100d4070985484603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 61658294 1250 61657044 61657081
    0x10905090103080d0905030d0603060504210e120102040b0304060b0f01090b070b0604020409020d0b01020c030d020703060b0a030f0c081e03070b0901110a02070f0e0702061612020c06 80
    0x1280d4140d81d514640e1104202e02c00c1ca140481101d603603100103001c120080c02180c40c40c0d05141d600340084d5840c1e05054005000591b401c03100c0d800c0203154458142e20b65580c040060013580c551030413000e84d082c24050851105a000c0a003554200004901007076000d01440c05940640c00c009040c100800030301c03003040400c80030207040c00305010003000401208411501c0980e440f00d00c0310603e4075450041000390045801c4007038014000304021504180d650b000c0349030448242d08444a40c406c1500789621915070b40594801038019060074804a0010f40200300808005042407400d0f036900d4454140230313543c0d00c00803504819014020041c0f0001005040100780650f00da80408031032140300f1036a244a0b0941c01070030080c0b10000240e01000a50050300c59060404615989060910300207460344c0b0280600f40c5040720b03c54021440d05928001c8501c21202c0e41c00411158a55514446141002d0a8564200502c0001c540444081c9001a003c00807000740105081e003059030301d40c0700118051 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 61659544 1250 61658294 61658299
    0x21c08030901051f0b0904020702040603060212010b0306010f3504030e0f010507030e030c090c0d14060a03023c09091c0c170a08040b130b06010f120608030405010905 73
    0x3900134810086801d00c001107a1305002e50315500d2802d000854081d00807064040e501901d04103001090003041c2d0010311002480704860305140c2c1c2c0381e001c0381e00ca03800181c81c400e0004d040745d9440d2180e503010380180c070302007000d25412581b06d00f102d030030180003240c550984020302c1003010706200806800200e4002403540854000106004160000b07045001e86040901040003d00341c06c0750b262000d001003800d010300a0000c101b6803a00403c0079900e41e02900020b45420700d0b1a81c2480100315490840e07000d03400040c05001200c3c510b40812403c0c3c04d83d4001c90610082c01440e010201c20b240210b101d20102900a07105070850420800c0048440100344103015002040b00480c40401480801d04500c0395041000303510100d400c0c044840c0002d03242d40e8150050005641031003d41259286100d03c0c801c1c444009207036600205600071001c03111004124a54200c04150b40350300503034004061032603500c6d021003c3c130081d5200b1026140c1660100c41207802c001014401568403c0c0d900313000c0d0105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 61660794 1250 61659544 61659571
    0x8122101030201053c0901020705010206060a12080d050f1b070302100c09030212060906061f0c030e0904060c09060201020a050301180204030c06090e0a060302030d030504021c0803090105 82
    0x1141c001070500d105031202d90f20788111170440d501e82904255941e941006215202120b09031050781013865a51000e2040c0740580704841000480d0361000407010b102d600e0142020000d14039000c8010828040002c1c116800301c001d01030521040700f644102d40c0702c2d54182c03100b204107040100d00a04d40d06400001c000c0500c808024542c0840c0e00051405008004100c0001e129601410f00f281d19100b20b4000a41c0402c642d200c0c243d00c048005045800340c80640709031a00c80c1c40704010822041141c0b807114120f5902005104003282c05005080c8406d802414206a001101000101101c0c0f0485040316800d81e00e141801c40c0d40d6100c0c0000740500320a00007103240008080000d400703804144640c2c0c44141c1186205d0300000c0d000e40541e001541e100304010043d540360040601400b455019607941009801d00156614441d80243c0c0f08481d0054003030001d42079541c400310040d1000130320907a08038002c1d800504404039240440740290303000382c2d04280c42c0d08060b100942951000341405288194 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 61662044 1250 61660794 61660799
    0x103020a0509070503130302010615030f0e01022802150414010e122704050103050609061b0702040b0109030507080d11010b0a0e040f05010c030506040b011d01050702060408122101 79
    0x4012080344c1d040510191000146d840138a030803030252507150450745040300f0105210140f40d4043d040880d011020719828000a5021001c840c200d020700c3c42150008040001943c803054010688003041220f2841a184850070341c200342170346c5d0b02080c4e400300d50101d921030301b03c2c2e1200001e01c620000f6000d241e01900035094489403180c0c190051800c07540e03000b08003920807402010103100740708100001900500083da0340e070a01c69143da401302da5807174150190800280c2000d021030503203403400c0102d83d00c550a1000c03a8083c0b000030842c680b507030307030621001ca1000f002141c42000710b000246255001804000c11000300203010a10360341d02807180d82c1c10b140e03c0c1a40da640e1800c04034103942c1e91040c540419911410941c081c00c40030700d0060525440c0120144a01e0780c0341d04421700c02c4070191018451000030342c00440314030a08003001d903886030510042400940c07052004003081400241040d040c1901d4004080c181048d100780442c02100c00100044c102c4c400d60a92104460994130010781c962 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 61663294 1250 61662044 61662047
    0x705010f0908091509040c02010203011a030408030f06130f020a09090b0306040b040222060e09030a02060105041d07090902150319020304020604090c08010f170a0f0807080f030103020a050907 84
    0x41d42c0340151040040461800070941960117544401000a0040c0010600501c02078000d40c820b006001d80b6407c5a040c124810000604a03400b45510005240c40e66503404201251414027610b407591085d1005010121038006004482c1d0303807106444016610860050080c115035000e50101c003005091280c0300c41c05640114809a1240e0092000041951107200050340403035085002200006001242000040658044803c0d81c00d40c44081c5031070740f680d80d0b1040d0f80340900001d01005a0152005015600382070704403c0c1d0181070751010082c00d15405400c181008400d80200c4130055880b00c0c0e110035454414000900d030300910001c3d038514100108000c1a03250585000141035400001060071034584604940c002c01c0d0252041214810040c001001d140c400c1c0f044455030640c5c44c038042003c000c0b015111485445240080c9002401a9141ca0000000100680f91100148441d1000c00c44000040c41c610106882c10707552581540304004003c0c1039a00071134040c0c5a000c1c10005101d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 61664544 1250 61663294 61663297
    0x6050303070501241809020102030f07120801140d0f0312020d020309060a0212131104060308031509090d0c0609050106080f0f0a080307030b0a0503030c0a140f0705010f031506050705010f0908 84
    0x4c00d8200170114914804d400140c0c40e51040c1c80701c980c0c05440024200082c014000608007810b040b0350f0f074944181e640c900441d103a21001288055100c0d1100d104940051031518001485600c241000c18481841c201d19030300300c0c3c110140700b0b02c400c1d800200304003614800340032980c0d200540840841c1004501d400000082c80001d1010003448031600d000b40501100b21030300b41001d48001c0c424041c0c55260b10f81818913400990314000d400768440040d00170741c580140b1b820700c1068050000c0481500c080021680d641c282c410507102c0c1648c801802c004180203028410152100c5001020040d0309161002c0c40d0105221a926640c1c000c408540700180311942200c0d081492850049200d4100d41c001483e0549590300c4a43c0c1440005801c566509012412078081d50003545005007070410508640d407110f0054400e81c0c016082054184101d40c00381030071040640051500040c1500d18a62071301c003c5134180c11420220f0720204480041090034011003803011752400c01405800318654412419 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 61665794 1250 61664544 61664579
    0x60e0108070e070507050712051b060f07030c020d030c1209060207090218030706021f1104061b060c051306030218061e0403140c090108100506040605030307050124 72
    0x2d440345000c6080316200e40c00792101c03030360424266020241c1d581d141501c0e410701b4039022980b074042c613005001c4c60702107515404800c24015200034030300014541c41d01095440314a00300c050011a0160202580714810400d0445120f5240c1c4110043c282c10700309030300d20401102508101c41408103003c00c0d03a000c201001158044000561038041402d2050005201d8121441c0c252282c1c0b880003490f25400a60420840f004800241c043c5030300100180c241d6010382e0100440082c10002000304520070b0044400140c6055202e02c02d000c00d550300d41c0305440c201c1d0108000280045000842a98040303507420042000b410f0840c600320b030100d410b00c0382a490304100c510030a008a840704929188100710a2503651300c00d00709541f0b58503131924000e0449145110782c07082c03044244111042c1001c00b959410303515110005c01111101801003c003801004007116000382d1030342c1e4005555103003003001e090020301c1400089866441000004101400040c42c0d00e10030a105408000946090000703041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 61667044 1250 61665794 61665809
    0x30201030915020310060f0203040e15041107030e01030c03050f0619080708070312020f0709020705150115030b01031e0515090c0703090608100e0603010608010c0c0204060e010807 79
    0x40d01d03200c1d402c04181030b05039803402030400d500010130040102d21800151041c0c9036251109810060038120480e80c030301881c082c80003180c0c0786002040c0082c403050b80c030000d403490081c00410015605051524143c21000c002c0340071800d507080303039020382d0703014041c81c2c0f40407202d46020802441d2401c0c0800040e24081d002d1802400111f120000240384040201d01912020048400c0e040d580d00b1010395403102c600c41070b81c2600851102001562012461401b1510003100501440b81044042d80007580b003060111003612030140c0200300e0111150807580200b201c103000b82881e00d4000c5d001303002d030b5484c5201c6904151411105921200481c405000641d100d00340004143e48e928200302c1039a4820440154003140020401240d4442d2000070400b0510070b64401e8005640c4040c1510801d0069810031095024460140306940000028a903c104c004002050b40c0d03907034400060842d02e40c0e000b044c00040d8500d0100c402e60901e030084c40700400b91103a80c0b01e0150300d40b00c40c035a1101e007140280c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 61668294 1250 61667044 61667051
    0x9071413050712051008070e0f0601120e0607090501170601091503090b0c03040309080102040e3705060411040810020a2010050903070f0b0705120103050105070801080604030903020103 81
    0x30b0340030388110300c005050001c480041085042030301001801078000e100c0c015142c494000d011070b140054400c0036009260044030394205840d0720780155210701c0c414041061540da00e8035518407100d01004203500402003034954100c03160600703000420300f4011090301c00d41c2120f83c00520040342d13880801002207d824a584409684032544110f02415403400040c0c0b0a00d80034040c0080990342200031400356209444040c0c0316661662424240c0c00360b03108900040c00b17010001440c0220b10341340b406c00008900b184039000e1140d1210360420208048041503002e641e642081180e05062065402c1c8002041c841c5080030302d4208002c0c2e03900115910b40003169000b06203d40907034021580034140920301100720703a81d5554a03044569685d5454500000d032811724003c41c4500e500030044600c102d800c01074070354400e001511800c0440c1c901402c103400300807041055070760741040301000d24003842c4280004a62400c00407070040540030181c0201c41507070005010302000940240b00300d0200e030750a00340030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 61669544 1250 61668294 61668301
    0x1e090b030c09030a060212070f0c110d060c0201090302010e0c0603010b07140f01140703050112031413060c02030c03070b0409090804090c0503070207080d0207061b06060e0907141305 80
    0x1d58003a2070512509489410900d2040103416000780586082c007981f100003d0748c90381000c40c0e002d0030b40c03040d0101040c07503001d410340801d981c0b2a01409400c40030703040d520502a6a954101100e074041c22500040c2d560340450008c140d8280100208441400003c15034070131940001440ca10042c4215000e806c0000340301d03002c01c0540030a58501c6190703101aa80329001d0041d0480c0a044918200c4108a0001001036000e9020303108090503200718940c0244000041e54041e509882c40c2044400e2096081c0b06818145110342c1482020b06819904c001144400e84141841c20341006d4040748260007110060080d2140d0105580441f64410400300e1039010a082040c650301c034a81006d2040c500348031010b1107494010004600484139035080b00c840036680d0002545070b003460040d0b0710058001500c1080601c1c03040d220726901c0d400c060103680042d80c4603610303401121030304e0380800d081d07021050070043c0c1c0c000c0a010f464003c024400c51680160107880000302d80340b40d41402c03090b215540301c011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 61670794 1250 61669544 61669561
    0xf210a030506030114010b030403030b1c0204090309050a060c0c0e01150c1419140a02030c060901031107050a030908010e030a050f090a080609010c0203070c05120a050102030114011e090b03 83
    0x10011100d1017490303040d107540c540032440c0300d80e07100300e5058001c68100b541c1064030303003088802503018045015000302c1d80b580350390802c000b0308440303001a070800918141c0880c07141c4d603440fa0b07080180080c2e1540c03185100070f03240c4050080c00e21f0703000d4a0740309048001008245071061101d1100300d082c0c0b41c410b00c120401d28189841e05004404d0308103078869034a030718a0340001c01e03d000103114018409012003a400002650b80d8080c2d10000a425410044603c150781c100440039211816050501068080b1000c25480c8160403101041c1c42642c0034902c01800d040e000100ea80160008200a002d901c50784114280e40b4802c4000c0c0c2c0040140000781c0c1c00b46542424159540d401008002c0c2c0e24042d56140c007690b503640103990001203940f0306640008071500000449650540c0118081600307031801d002c00445000d80f440144240c0909421600010401e01c0252301078078a40c03041da10090301440004000329051941990340219600c4500344403030300001908110b034041040503a4903902c00c1070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 61672044 1250 61670794 61670801
    0xa03020f130212040201120b0a0501120902030102031302090f07020d0c110303071505070e0a050603090705030607020d170103031e03020f040303020604110405040206120c0f07050f210a0305060301 86
    0x159074854400310b0324000c1e20b001406801e002d14000d07664120240c01c001d2441040b55980500103074003851a1804104550080d840a40405502c410003d4107141d2030300841e080e03a000f01c456000302d44412640c0421842d11071045600980080c002c030b2241d14124002940c0c800301d00c0294401d20003038090003001c02443c40040a01c244028094903111a11440c040c0703010744008146a803050304000001d1061880344100d00c242080062040120702d1510041c0100f591020701000541e00418a01103002d071410014a40188426401050410700ba160024105081640c0182d0045d0300c2e00010004207a201401460410207a4520f05481c82c5005094001f0b220302c1000f034980040100c0c00005142e000704405105038020380b030855925440400300011107000b168003e5121400b44109100541c109600986c040712070700703480b0b2400c0d1010040c69219003055800f1104c0b0340c001594510140340070300526110903151a480705840300c401c180c500713440c0120701e0580101503035080002c0d00c0350380942 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 61673294 1250 61672044 61672069
    0x4080c01270212010b0f010c0c0b070c0305060601050a080a0209120601060908010e010c14070c09060b1809091b0a050a03030801050108071b0303020906070210020c1309020a03020f 79
    0x101030388603a60111603045a05079400300a920690361502c00540d410380602490024245c01414060380017030001c015a04091b40c071030b00362110b100c0c17240b0105008010f400148075040c022883c642210380b0f135262245c9005c1e0b0003810300e0b041001c04d0080d440c5480d0000c09103900848088409038070780c010107001c103c5040880c50b803489544120000000c1d00340e0442c44040559503000000d0051882d04100f1600f0384100260100010f40302c4504a000c0020030000360107001e00c11991169001e80c1c42d07030104d0545120b50080501e001000404400c920790b5842c1004240000b80c0703813414240361080030a6120504001c0e0380850524104208070315580b6000c10030041d12004007100c4406440b42001000321009005403404a070b100c00210f5a040d0040d00344e02d040d50b100ba9807032601209281c2e03044001e500900411500401c0510280f4016640d44c01120f152000d1a4018044821500c080000c1212280c010014042ca40141b42c0056111040c803603058030740580d4244c0f0031000302c0000c104084c082c0c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 61674544 1250 61673294 61673321
    0x22110050a0b030a0b0601030f0e0604080307050408120414010219142d06060307080a1104020d09050a17040305030f03070509030703050106050f0928111606060b0a050304080c01 78
    0x1301490310400082d40c000e03038060b10003079a0400c43e402c0b100301100111019a028401240e11040c00940002c40d050000c59000c031191034010704043e5201001480c100d10500103000d21000404c0922a1403406003004980c000244020055040441d00d0003c110000f24005482403074103004000d01404204070031131003880070100002040141125010350b45456000c051290b0207100c1c04204207180001717688041da143d4801404042c40159a042d94580113803401d07540040e000e020028407080103200303950000d4081e4015082c07010040c6080407050301d00b84180510706005000c01c0c00401d2001003640d46c20300300108490343da0727158040d00740c3e824010008420b030b0610410703001008020041d04a4011070b141690364580501540082000051080303070014104002913521034600078503e04982c2442c581610002440c0c40080300150083d48215903601c00081d507101800c2c208400ca03c01c1e45c0c010120301040a00300003030150020300318400034102424440011503003004081c02903101c5505a00311 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 61675794 1250 61674544 61674553
    0x609013b0907110d03020a0c0c0801021206120d050306370605070201080708040311010507020c01091401050313140709090203010b0904021c06020f0406020703022110050a0b03 77
    0x28801003540035204480034074003400c1144003140c0d24a0007203010103c5580c070b40014040c48060f2030011030007908415051400c2010048210000c1801210114040d00d408000513030f8815000c91449110b100243c04980244800e841d462000d86002c0b64682c0c18000c0e80c540f45949441b1540010480203840b140061101d81203941010303c1c0d6030541481d5a404c2c01e0307909600c0641ea50f004140c0ea14001d1004c0a03000c40c00c07060000d03040760320480f2602d40c040c0c442c0c2003036155400c100e0661400c507070084891001590009298600c150381000d0550024003003419035844075004840002d10f0b071700000d48005038001c880366003a003c0100c00d130f844e2030000614200700d070102952442604041c0000303820a030f020754604440d50703d0754140661003e100700d40142c2420400802070308804c089542d4000141c036599400d208900500c41c04e070b001000103107280e500070040b15065004004a100142002609002c1c0d0750f4858007500d8404a0200d02d03419002400103155a140b0b010f01014044640405506014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 61677044 1250 61675794 61675877
    0x6100603200d06030c061407020d0510050403050901112b120903020102030105010f1d150918010509090312010b13050d0f0b010b04030309140f0a0e060103050f06060901 74
    0xc1c20f600140450b4050090307007031000c2e0303540001d070740c1030b0040e040030420044100508800340c1407083c4d0030a001807107101102e5558410480d8001200c10645088000500010303110311150b03800341e0741140080700d00028001c2c600e07000400d50204c1c0b140b001e2102d400302ca110880c0807035602a00f8442000000003805000204072840d009001754001d0180780d0106803040155884588603a104031030b80d0185900030012039100d1402c005500401c1041c01c074901204003c483c9032521481c080105103d55520a2072455041c4002c014030214014490071007a40b0902068404c0090f40b0802c50454400144d62a41c8500c0d40c58000080035041d00100d403c07140c030b1035604007084000701d001c0310041c4c041c00740359820380d8841c800e010040c400c0e03101c0500080d40000042c000008058044214918000d04941741c030400c2030045680300c440303035101ea00680380d014200405542c1500600d035202c030400580030001e05e010400180e1a018071000c2c50704111000d000e03610440d8150b05004020291440792007514403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 61678294 1250 61677044 61677067
    0x15010903050601060201051f0501050d05041b0b070b0109020a0503220b090c090601030b030c01050d020405040516020f3d11040906170705011101020d050109020c0f0610060320 77
    0x14142c0d042115941d0234400748a284d906081c8142c04da5505944080c50902914201c00180402900541c0c15082c250403d102001450029038001c01500c00c10b15111002810540103c1805910100801d80104003c0640552107400c172580074050015142007039043c1006810000d16490b002005e518015083c490b1082002480c0d10714031200720740300d80c0c250b65030320011025140b10507030300c40d01079020b0b0700380109030f40c01240a003290b01045500142041d0f510800603080e500d040e10b055141006580c241030400d07506011490380040a84024a003481040d03018030781c1c100740d00d50b0340244c1403030314402d94013290200c60301ea000c0101101414400c080c000c040341c82c210752251145810941ca4288005640720340f0030070661200e828440a402c80c60302e0b0000640320140d1080a10703a0341d5601308460318103000c0d244251406000508401a160898035250b80c3c80c090203084000c1e104c3d0300c10f1082020803034035104000295151132a01040640c0070000b881800885400c6a040310751340400c0006903507 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 61679544 1250 61678294 61678301
    0x1905040906090605060a06080109020c010b210d03110306010327061e06080601090504020a090204060309170c0703030e0d05070305240c0403030507030c05031204050c011715010903050601060201 85
    0x2c034050303507080000e51100e40c00c01001d00305030f115800c041039640c801080011401c2e40039008a804880001ca030320b08400c40010ba2088100c2c0d00248130449225400403c130001304260851880581400c10149101e444484818000200558101500c5201142e00c00c882d00b40d40548220185040da0540340710b601e0a0400b42148890401c580040a003000b01c00c8200b40c01140129000c0d400644441d9007000b1761003000d03142c0100181d810080380d00c0c1c00240d40160303100400c000e21003a500051114018a0400d280940c0000345001551003405a90507607800458003c04495042c10144000003954021881c05240703078002070813501a1241c0041800404036402c1c1d00030210b8030120300b1070040c0c03050701101d07110195249800180144010700000c0e001da0020007502d8002d04006030035542954030145560300001040495280890a003c1080350810041c044010242000151381401d50650b40d90030400400007000703c0003001d403c0c995a40074200c40c1c00a9034100d8107039803281d1785403040039000e0b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 61680794 1250 61679544 61679561
    0x15130501080a0c05160c03051f06140117070306050402120103020312030915091f0c02010b1f0c11090906090c0301090803010504090c0f12020112050103030c021905040906 75
    0x201e003046000411002c59403240410500158658038104003040e03550391a00c2e64002c5080307601452200010011542c01c020340410380940390040810301003000c90038401d0b80c802d50f200b0107060a143c3c90f040f950f40c1c1c006101e00c0c0703024041d01c004021551420400c038007030511980701301d402901c00680c000ca01c145601040d41600c2c02501256030b804803070019041c0320300c000ca9064109030810400400c400340705011083e0000384400441e0340c50810f412840c0607400c03001070b1002e0b03c1661341d01c900040e0b40d02030141d401b02040c1100c4400700c04003074800052100c480b00440d041000a40d003606820030017401b0f00510149000780445003140b03818402e0b169103000680d603900d1603201c2d0050000035842d05020300c03000f46600c080700741d0969182805100240021040440d030780c2038003480100e0340c58501c1126400904107440b40160203030709400098440400c100d0710780d412504003c0148046900480000301046d4141c03800704c00346c000324955a9007000c5540003a03074490309004c3d0325002c2c03003110340007441c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 61682044 1250 61680794 61680797
    0x606060507170309070b0d090816050c01080702030d0f060b0310051201090503090d05010b03161a09030d0c1401020f1c0203060102251208130f0f0504020915130501 72
    0x3a0460351042d81401804200d40d80059548840d07803c0c450100f43c0c00240c8003a506c071000101c2c02c810155039982d2923030045904181555811b00f503020034010308001600c0064400c0c01c21103994101030030700949a02ca49400f01004070746034140c1d951030801c40d510000090400c68500394072407c05d10040c00c90b10409100785403144c001010b2500d80014188944006203501500451804810005200300706080c1c0106451700d5681e00e410261948081c86580c0e0846401841c90400c03a080810503101d0068440102540e4002801404416100003c0f56198000300707003046003a03000b03140340c1a84100f40c0321000070b503994008101d5510302103603c000f40003041c0314000b25000605081428400700d000454041d801070703010910818207959541c6050341800e50304030810303000713a445800c0c52101d058080030031140e00c6000600780c500301c03840c40c020002801210b00c042c401d04c0c0c41e001c0a100c000d2920700803940300e0b80d03002071944000c3e40e03030901810781100505201038440d400c9018044918409121b01030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 61683294 1250 61682044 61682063
    0xa050303150604121b0801050702070503060702010b0f060d060f060203070302010b1002211608071208010303140a0302040e2a0313060506030c0415150e0108220606060507 75
    0x40500d81001a42c0035650200281c0301c840125031907500080440c045c0c05070130f4010558020030444001c1c0034080c80b5180c0c90b001452043c1c5841c05051501c80c0c020110b8046914085111405503904c10901d001c2507411100c00f522032a500c41007100420190784200c501c1214248002007141d00800079044c0c02e802a002000802d50540c1880002104c0400c080c0c016049041c003018514080c0302d030034480c004030a05107410011080554801030b290b1100c107545c0258040350b1602084001119030a08408514081d82a54034643d405840050700500071003038084003282c0007501d2403003030741650020485101607180c24100410b8200c4181300038400d00000705d035000380190842d031100d01141d000310305562180c02100c1c2a41c59000c01420b000d000581d1500034100d40c00700c0365440f40600c0741c070301030f0065511000c00c0c039210074480d40c0d000d1555540203201000c0400e800983c0c009100907449a98502040d11046d146008101c1e0340311000001004c8502d841740c0071800a0b884006403242d00c0c46400703400e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 61684544 1250 61683294 61683331
    0xc0109030b071d03032214010512090a0218060111060601020d0507030e0d0303050907060e031b040b0306070f0912050a0f0213050103080307080606071104050601110a050303 76
    0x4485002890101600a51884010840040c031850072504002c80c600341008400ca014000a0b04503032051600090540e40101201600b103540710700d0b440282010302003c01c0300b07400000080d000c2c6c080c2e400c8182c101d8003102d000840401043c84541e10346075004004401603d1b180d403080b081c44c4020b6958500007182184422a80400029a0fa0041205070000c0200492207281150b00b944002003c1f010440e0240e07050500b5150003981151b0b8900c241c40100702458070031074544c0790110645c031140c20030005900b20141a01d0105000300c11682000d40850b21810101c0450050061007034030980601c19201040700d9aa03000b910004103540381e9440f07255081d030b83c86070200c0700050310b1400b600070b0b04400d401700c0004140e80b41c1c1c1c600d03680c4050032141030b02c82d100140320100c07030099006841c2c04500004108206505c1080160700510440f1401e04000c5603032904c01c0c8850001c02403a001d2a81e600210700541c0c09050b000c25600544001c845e440929845c0041e180d4205444881881407000d0b0036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 61685794 1250 61684544 61684547
    0x60503070c060207150f05040309050f010201060b030901381908060f07020f0a11040207051501032a18090201030f0e10061401020d03111b0303160809070e0c0d090308090c01 76
    0x307c5008580541d2416030660802040100381c042e0700344114190340d40d80c0300024141c1041400340d1300c11119103000060790b244050b0b944010880c901c8180c00384c100c81c40403c82d03c403880030301100342c9254207460100c0752843da403070b18190300b01541d0040d0000b48a90000c1104996040c07486034840c140e140c0c01d0b52000032032285002d554841403400148001d11a1824450a02b8254081c00c8075900420444031301c0c00714040c001d280d219007038009469810007900c1d032111608441c01250b02c01c0c0c00341031441c0c1880c0d1030b012440c04406558403404e40003e840e07404002c00d684c400d801c04481030350240c0d8100310340054604604c0c2e0301c404170341045002d07504054000500070b002e030048805448040c0c02a040c00c1e0b0a160b003c40017031a4007a8960042d0b101805080880c5c1a181d40034042c1001c810005e60380c9040100c0d0600d0b10300c0d101b40c04242000000002c202641e2400f080320030454900461040d0aa120f040e0351506e0350083e1a80e12070f04500d00351005052680c0880d006001e924000161902c4080070f100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 61687044 1250 61685794 61685801
    0x112060f0608100909080406021510120201120c17060303030105030a0213200304231f02070b150a06111504080702040c02010b041d0601060503070c060207150f 70
    0x520600815040e10410890b0b0044603116403006041c0180401c25840722410411603c491105450400300440c0901080b80c040110a07405070080400c001c1c5840d280d801c50600e9900d500900c4620b00e620720900c011640031304144c2060324882c41c1c05000c40e010381c45004201404101182070f1070515503012416030708010007201e0503664041c001e0458000707203400b40049586401407a0b103100e56a0030318111000385c1c109540d00c801d43c00410803952810541042c40b080c0c00711440039002c1880301c503c01520203600185101981800741c07841d8100702d1115251b54028000d2010142c0200509070802ca0683c101c1c4030342e0300c401d020845404d014640c83d030404458000d030f50841c069040c1d203c08048200c0b00051164298032501c40d021052074188640d0108003901c41c04495030000d40c0d12110700010030700e45405181140b4107082c40c0c44810280c46030610b5501c2e1010701ca000f0500c0030010105400710b100303001c3c050a0320b0300140c3c00d5590318100d140c0641c20702028039035120b1162408911800780301c480d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 61688294 1250 61687044 61687049
    0x90c0103140a050c0409090b041112070510030b060708090306072c060f0c0105040203010c020d081501020c06040f050907090b19020f10090b01050105040312050c0109060e010506011206 81
    0x168418410341e2860b00c0040100405004450a1074042c00000b810000034010080c000d032203100c011250f41854986041004186424580f00d00c42403500103004550000c3c80b80c013154812250f0314041b03e840c0c0c60540060100040741500007000080c08000d204100c0c00800034103006030300700c8407a0360b01d40c04102d0354070104010080380c941c0c410182070018211903d02c0c2c0b00b803210080c070641ca001c41d0400b10b00c002c0d034040c0700740507101c1c1d4440007000103611f0300f0b1103401c054050900161011a18a800007482d4050091880328100c5094019100e981d100b0030000d4800c0030701915440c2c1d0303141c179070104101c050100d101302482180200000341c042880350340c004007155a6013040c3c42c05c02a1003403031804120200c840b048210b00c6200c1e40c0013400b502c204400310f4114011000000c5041560400603180c00d0140c0001d41070010400c010400100040c1c20001004080d142c8181c8601c0c407116103034098030b40540e0203410b65080041e08820801d0641c00140110b8098940c004550807d0720074900b0f840c100e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 61689544 1250 61688294 61688321
    0xe0601150305010b07030e010318150c02030a0f1209020303161205090d02060d0902040219020111030601020705010f090f1d07020d12111e0a0f09080705060a0512010e090c0103 77
    0x78025680002d00945280a1f100b005040105581030140d10301030b0800c0004c0801d0340c000c084074161101c400c0d550f1085075800c020a20155103403030f440c02400383c80002c08240e03010801003600c0702808004200e5000500c4254010b09495440040326081819102c00c400300b1b44e400761034010034001c054040c5045584200700a040301d0ad2038a41c503001c00089030452850100d5490700c0318810700040c2c4e1148000d0903103d000300d22002440440220081c02c40b0290700004918290070414020aa84c00051940465200b441c01c200001c450010071900690180e100c0200c040e8010804a142d48040c020340d00d6080c00c090720036403d81d07204041240e40c2c2c000301400001180001c40d0a41d006001600071a0107a150148001d1924142a901412070301c13040240890100d40805c0024110307071301503084072240c800e516120245034240050240c84002d24818a4844e0390001149031455000340d00703546510b500d0b07200103101980d640648864800f41240c0e401c1d13150098000d401c00e10340c001d109020a03071211 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 61690650 1106 61689544 61689547
    0xe011506030b0d0b06040203040f1202062e0311030a051b24030a0902130f090c050301021e0901020708030a03021201170a0201120209040e0601150305010b 68
    0x50140903849183c9040e0320320042214841020b40001d0200c40041c2d030f0382c41d14980008091140d20005000444a40701d180038030b44c002c41c2c610b110314440141c2001c501c07009032040c100320b0b80c06840c403000d40070020011f2002c80c05c0c1840b9400e00420207801c580c00a101c9880b0540707400441984941c141094a5141c0340b5805d1203a9885603680300d0f00740a19150004500d084070324000180406041030b41e5503078080a56036800001c656100021904005406034560701c02e01a051001d400e54150308003d01c00a100e0405208584011940a81c240c074512814000f40325107620046542c4e0440c4204000402e1000c0140014690141944c500580d5002070784018011072005038000500500310b90301001240502003071018025609280400318080b00c0009075009006805000d90410b2904811001262001401d01c0c140c0c0d5290340303c419110038031a012001e03a0003d004444240c1c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 61510794 61690650 := by
  have h0 := BRFrame.cov_init 61510794
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 61510794 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 61510794 ≤ n) (h2 : n < 61690650) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
