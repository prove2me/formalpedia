-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4290
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:08:32.802266+00:00
-- url     : https://prove2.me/submissions/09b307a5-e602-4aa6-839c-2b11bdd7b6a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 771402877 ≤ n < 771582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 771404127 1250 771402877 771402887
    0x302040e100b2a1633110a080d0e100209030304120521180901080c0409081e0a03060e042003121305041b05040303120e030a0807 57
    0x10030092518803444410030070511501e04862550034554030000254400d040e4180300b125124a0429461084a103840c080c000e20021030015225035031014802513140f00d5003490080211420f5411030401415101407407030003010706d1010f0081c0d550513105501a0768503114801e400003644d130078903107031240c040c2da03001c680500154401d2001c0840842c00d0808920200382d40740100e008030402e91401d81003000174804100302a00c01c550317203451810040c0c101e03a9200000354200c503020003002e412490038040340785024078440e8181c0d01d01c580200842c1118404002c00b400070700350203030f41800003001955003410441c12151101140c01030f00c1507550740440e9004080301c105510003021030f40918248400640c5100894281031550f1400c1100e804070040040e003014415100d802129000141444051800403120030455808880400900305050811900085902e11000c001a8108001d100213400760801e030f2030440313031002c00280c040090b181c00c42c81c5600402c00ca0707010a07280c1f010400590f51207 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 771405377 1250 771404127 771404131
    0x1d06400b12070e130c050d030f08090c06030a090f05070e1906180f060506071a0106090b0a08090a17030f0907060c060b0d0b0c0403031704120809100c0302040e 70
    0x400800aa903d04140d0000d0300c44094107265444070f019001205000300c2e1196240501401011100410110719010701001601a020004141010009040d070000401d141841e81806000130b032035030380e80001c0b590003001d003070030200d03403d9034881001804078104104c43c001030401c44480c00c45906003800c1b0f1800d41100d007002164501d007405400c0c0855450412004c0360034140b15404103141c0016140301c0040e186036004240c01c0030012030700e84d060025a9600003400700000150303400590300c0340340480d5400d0f50350042d441082d0041052204039449000315a6100000000b92002e21020f590f07405100c07003103034030303075003040031010043c0482407000a40e0b50350040400340050131094984500a070041c0c1028a020745055034a01180c0000d4440d50900c01002d03038450082c2c441407405035410355050300240400e50000798601c043c0040d19004010312800340350040ca080d03c00a080e01c1007110110801800180745e4024100690340c00380a6026101c0222150f440160b211414080955450000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 771406627 1250 771405377 771405409
    0x100f1104260d1704030c1403070c0504020307091e1805060405060d0b0a0905070b040305033a0b04090501090606061d09010306022506061d06400b 64
    0x20400842c210070781c00c0801d44002482072a080f042c1070340c580c2002d940346070090030003814140200c003030b15a511401000070103040344200b6075150180d0300c07403051108a0004590b608086030001070107200e40401c1c01114540c0c1c02843c00740054a94440300f00c0c02101c00c0742d0100381c2c44603407104140055454180900d80d803040c001da40b8002d608109403500d40328a10090403881500f81d9461a080501c003040c07000c2e5001e0a0742c032540b16542e0755207182242c0c2c1d0358881560303422000b00b050001340e000722450444404a51805400b441815400800310300100043c000c2e00b03501540c0e88405500098081c043e4110080c010200000e046250500142c0110745260b448403030076a180056450559030b070480a03064a03001000142c0f1041000b020350040c07803200f0520401050061006c5c010810560000b9040d1500003142414400e0603040840c040c400990340ca03076000c040380c2d17144800b0903400554503903881000d584261201c81083c1c903540708802886c05504070103403150543d80031424901d642a0950303131 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 771407877 1250 771406627 771406633
    0xd080f040623090d1b080a08030a060b03090c10030e060a15080106050603040f0c03080c06090d05160f082506050609060a0306150e01082a03100f110426 67
    0x503c08005180f082110000a04c00c030120460241c250f103044c000d036000b03000c0f0360089480114184c200407080c0e400485203213110504100700440d4002d003400c10380f8010040c1000910120303586000700000e1154156101e000c0580d2110365200a440130800356006501d0700d03800241c2d0080d03203620300010072401e81003902c3ca03a0420108116079102e4a00310b1b540941c20100c4a000302903103180c41c03080081c02e030f030024105060104c1c10000d541000b040490040320224100c1e50440c0d183c18060b102c0d03002e41504076090003d03d012000c04540702e92810440b4910030320350540341980d0128000c03040352080910158400400e0151000c1080d50311030310350403d404440f0301d0058a0801c0000340c000d020390000034682601d42c3c8061491001c0f80031058060000106e10600c40d44c1c41b0f20354240c3d2002c5112070002000380c0d40d010712511210003520100700394001340c040d214070358a4008140240c020001c0d841c0d942c90392142c441c101301e0b01c1c40020304040c043d1010f2142d190401c4090420042c1c0313480103420b8543e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 771409127 1250 771407877 771407887
    0x1a0109050a11160201030b04020705060702030a030e0a020603010e090c120c040e01410c1908190c1107030812010f05030606040e0102090901150f0309110d080f040623 73
    0xc035211002c0c4800f0741d092801140b4888001c0104010b07004040b001000c81c4552010f2046464000c4058401c4004030b980411011190420329540c4109040c400b80d00040e04000501400c0c00d088002c5600404c0070084400c0510404040382840760001c054402c1c5801c01d01c00341003030b03250034028a5040700c1458000d00c40b804249185540d02c4051440c0c03101121102c0c035146400c00d40c40300340c0c0412000a0840d00c0e8803440c002e0070305281da0784080381d142034190109a03e0041035000c1c240c1d2a014204107042c8110120319000500000c03c1c0d007048540a100d404840c92101c10b0302005140081c61203001a15182d802500c5041a181c9041c0c006a05d20090800706006c03d490002d4030a40c000001ca03000300d81800c099000c140288910902c7c01d400451102c00440d02c41010401100c00c0b460030b98803881c804040710b40407002c0780d20641c0c1c01010341c2c0d005082c0e1441c914100d40103020041c040c04040749000d960500c540340381c0d4805e6100c0404a0b40340190902e2225584102800c00c5181501aa26003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 771410377 1250 771409127 771409147
    0x3031b09011e080a0e1f1e05070302130b18040b0d0c0b0d0507020d021011070f110f03030a0801050d020316090e0c011403072003040305011e1808071a0109050a11 71
    0x806d514440c0e460129075030030109194030a0030314004030f040d0700386100700002c0c203241c0c80081c06544802412121081c0c142400520120660308440c40c440c9401600c0400309a80c10402000c1c0c58280c00c4964044221080344010498095152000b40704030389800740c0e00c460900075001903400040c0100d0964104c444a5812541c000c112894034805864000441c1c00460180740b5aa0094400c068030090b0b40b03182080c1040080014030582c60f030110346084c0c20406140c205a5a0722035080c408002480c00f000400860801045841e12644010203503041a0110336038040e03503480503804402d0703198407220342c038004480c1804100801042881d108a072600340d4200c0c0481c910000d00305ca01000048400103108503503400c01003190f0081902521341e21070f500c0c1891400303054000c2c80c05c9581e8419890b00c404100082c0f1503100b00064014031880b01c50703015151980c41da008410b00340c81003543c0c8502c000c04058081600c50280c45c5110300041c50381042d0102d00122106001d1043c00c011082010600c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 771411627 1250 771410377 771410413
    0xb01060c0203030712181206050108060618040f0609030207141503070e01020c19051e0d080d1107140c010f020316020f03070b1b03031b09011e080a0e 66
    0x42904400c030702c075902104280444206c5610b0803602506403103a0004a0035103400900c1b001054005e500910a990305e0714881500c03108140d4407298012080c8040c40124041c00100c070750700500aa00314050714415448020035510340200440050b00306490521a00015101e81328254900f40c480b04215160440011560300c13010381100309000c10014085140d070b1007041700100442001d03140d115074982e0301c80313280c4201050340110361003440d01c0a500800007039540c11490b0303c031a000380482c944c0d840c1c5450f21440765000751841a01a41c030341c003040e40b048808000a140e5180300c1c0340c2c00f80000c50002400c03820950406045d9041060b0b03481c907a20178990000035940c408400754400302c01058684001542d2032080701603075406000f0944c00181007403003540a06481d503a452070101d1042991442c0781d40705d202c2140ca94040c041c900c403a4280c0303a50703c01c014000b06030b0103042c4031404580d2600050080602d5408401c0060301c84402c0214804040c041d480c00b038a00b040082c0060007031143c090035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 771412877 1250 771411627 771411637
    0x708070210021b10020c0d0e06040e09070f150801061805190812130f08070b090402090301021314060a02281e1b030807020405180f0a0b01060c020303 66
    0x103030046a004204040310f01280d410740b04030003c940440344424844806504941c0510500d4004d0084074802240100e5032440c0c0d1000041c0020324060424030501341c01c4602030000304203840303203007404a10405040d8500d405001d9003003944020040300f030740c010300400d4160850410019081c0301416018610344016041d588120782c100510034490841f52080c000c00d610001691041100c0210341c84200390042c244420030001901c0b0040c4ca0f009840d0101c86180314040f80b03580021010000440c0440182100b4000107002619041c8000700007030a80e0041c02000710800703040e4100700441b1b05010302203000d032407040c1d5025040014401c006900d036960501510002c00070821103120020486030f600002a500100700c01d81c11035500209025400010400c40d210a0340c000307081c07100310400a500c01169400700da01c1e40340090546c05e21010f003601038544e8440100c0032258642c840d400b80601c145135144600149415616420003800320101070b4016004e1003081005000940c9002c000c40e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 771414127 1250 771412877 771412903
    0x7150221070203160c09050606090102060103080306150d0507030b0a180b0d050a2301050c0409150e0106020c19060203040b07050c041a03010c18140d080a1707080702 73
    0x42960318040c050741548142c41340c8140403071511052100b000b02002001040d500b00c400104031990343d12082c05001d100303c0c14810b000d60700c003c1c0100006079080c0c1c000e550010000e030050030411445101c500403900010004a9800d880710100554582c1c5031094403981d8a04403098441185410b9400c0d010082c0c401011143d907840f1110b10096840d0101400541c6511400301d0780d00b0406c1e400d203031340c1c401954000140100d00382c020b030802c8031405003e02070240c109160b445141601e090f566000070300c02e03194002d503030701044000050560b400d000c0060007403c45801a02c4498103090800111110502806141a141c10001d00c0029400000c1d01d09070744090714100d54540395030904500d800141d0203040d90042c205110f001c0070700803007070540f03150744004d8000707100c2c00ca42c0300380c161101c091140714014920304140e030400255250034411420300c035000d054492001500d4440301d085500030110600402c0503201002c3c140d560410030a03a004209140c12030306814441320094440c0e402c40e50304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 771415377 1250 771414127 771414187
    0x403050d090f08180a09050f2214031321020418050a0f060f02090d320a03020f070f03080d0e060906070e0f0109090c02070e040602071502 61
    0x6908012524104081d00b40c0c2040c3ca05031665034090010040c103800742c9140c2d0281d1500070380084c40c840c0704c2c02800c1c00303240d244002a40c10b6868000207140c1d4a4440745041000030307040302d044003284d0b20128150b05454450b001d135984408905151021820543c401c000744050401140c1e0341d000c03095481600e281e4102d40c04143c0300038840d01c89003090100500a01180039071000c801c02c003c20041d00300320041c071032441448440390145250701240520f00c80301c0d80007021440744a00044400b943e00b040600950b00c0c036840e9283d03c080004c0695130307400c09591254809000c0c0300a01d0f8040069410340710828004204d07040c14181405890101c620005220403c0403440141c4a02548c1068103d2180c4200721100f0380b61440c4160350f1000291255404111500e107604941d060014101880140685400300428500007502008001c0c20400c0e10031070040c5400410f4081483c0365660046009450241c0c0740c50032400c0c039242d4000c00ca80da41c0899841080030b5020b4401c07000f141b480c80340d020565 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 771416627 1250 771415377 771415391
    0x30408060f0a20032d041101120207060e1504080409020d02300a230a140903120c0421031106070504031505041a151009030501140403050d 61
    0x1042c0c010340700c2c146001d18480308030000340143c0c50394000030354401c0721455051541d2102522815443c1380084644d032094000d400c0001d0b010407003c580d020000d00061610b00c81c108212400b0100b2a004200100c90040e180c08480d008a0800c119081041524000220450809a8404415210b140304807085240c02080700a126056a03068a55143c10b5003204620103040444c40400c4500c030050b550010201d184c0422945c01e86413003901140b500c106451003254505540b4205010310080648011686440c40b020640350300b0801c450103540c40c0070003552944c1800603000c05603407000301b07507002d515411f200c00c00400700440c046001c1e40c10303c0f00c048400c0c03404030300703048942400e07aa006035030610408040c05060344d41700d0000c00441e402524000301500c0f1a9142c002036640c250340150081d45070710f400e460702c44a83c4006a80080c0740b4001c110003010074a0204070040d41006550000ca40d8446d401c105200c402e009040320f02d11121000101460181d4000e04030380100407000341034a5581e12 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 771417877 1250 771416627 771416641
    0xc0816021606080708151302070212010c0f1e08041101170f100909020d020609060d0609020a09061b031d0405010306090614040803040209060604030f060c0e0102030408060f 76
    0x90304040750944448204850b00c0e074802810000f802c0e242000010030400005050002460b0303807140d425001046120b2215414800d20040c0d042080143d0707001458510745031000509101d071030481c07d00754859086d42161130102811b140a10b00103502005204801c003004130f980310604c103901c9a8008101d010040c2c038000101d9035080d00100c8e003101c00840303106001002d448008414071032094070a100a1807500d6900003002d60700e4600f0025006460404c980c0300500e03103240600603000c6e001d0985401c10f0710144440c026100c10354000c0c81c1407640000d0300e202d030960050180340500203500703000c09120703081c905044d0f06a42e6010080c0030072494844c00300e5912000c1d00203801040b80108240001d58490070000d00514810004841030340c506210154250107040007a032084d500480e038035046554030f800b440f01e2210002c1c019070b072260003007001000180c5124040c40c841c601603103001540d10400c510141c09020480802d41c15940184800c124244001846c0c59218400225988103503d500c0c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 771419127 1250 771417877 771417883
    0x31a04030e060705061602070b09090a02090a0f180603080901030c0201020903070e101e03030309021305040f020310020c1b030a02030a0311010b06091305060d0803090a0b01090c081602 81
    0xc900c0390340300d4000030710f12013441000124a40603107510740c01c000101e0302c00b01c02071781c0e148003034404c00b80196014090b40e06949440d000055000c002c0d4900546400c1b003040003d43c00c5507840c1c004c0501c082500c0300601c0721894100d5a1002081c4112040107082c4c1107440391034081c00707810720681c101a120100c8001040c400c1d0160b503421000a02281e074a40d8560341ca40302100422244801040c1ca81e080004010748a66803903d40740c01004c0f42e6a0000d811610110081d142c010310581c2c0145403036004400308007661050b079214074012104440684090701c10036003885000c0510010050052102940b2000d010406034224500075107000c0807501c0e1400480e0800c800048080d515010710ba41c03081c20305400810b00500c11540304020400600060100092806100d8901e500103601d2840040d01d050140c2c40301da0001c50052608814030559680d040e1240d000b100c1180b05ca4200700e03101e0302001400c0b00a83d0161511030000d12504192007802020060028a00b41c8000401200c0000040c000c2c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 771420377 1250 771419127 771419147
    0x90a050d020a0b1803100c08011806180c0e010207151b0803010b120a11030103020427060e070e150918060c0a0807020c010c06050a0b0a18060f031a0403 67
    0x3c010308640b610704082c1d604c140b10760b614510a000380101d40b10600b5001c1c45100d64500031000e0f80b2018116400c0c40c154001d810b5207040b9a111040ea108004a080e004203024100045503450b8049400c0049040003000108c408071003d06651042c082403110740c404000400c2511401d1a18203030030035200240140401c0c4407140907200c0000000041800c0017090001c0c941c1801040e02007125449514000c01251012500412608004d100500062030660060f11159042a540c507800703888580c01151042ea015008540039959588060800c3c2c000307005000c0209404414030fa140d29040030385a020380c103001c104500c1002d070100003038080e0712100300a40b12540d00708100c0d034283ca8244600074041d4010000c65000c03c1c598000200000c0c130016a0700f0701c989c0180d4500081c0e100c281e80d00c80140c240608504501a16424404800c2d290f117500b00000b018030010300521403034080e5000d402c03500130341c00c5000d180c4100c031011b02c0411b551135040103515802080200b042e54850038210f03840c5c100c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 771421627 1250 771420377 771420389
    0x307080a050c0f04030c0f0806090613020a050910050103050a0e1b030304081501052115060f10020a2022090c081501061d0d1a07021b0402090a050d020a 67
    0x4c40c01005002c1d00c0c150000940c0d14650b0704242c0300c2d0716001d0140d5113042c220344500d0540c1c820000100c0d034142940460140e80d1020348181c0201e9124000a901a04203d80290071480090700400c900d607898011036400010755071081029a0346102c0143c2c540f00715074a2101584d103001c0c05000151420403c55009010384419142e9400c11202801c1c5040c3d400c0c85603c0c40360825015882d540303801201c0f2041d5500245008041c91808120082e8200c840103000035408981e100080880c0e8403013010741e001c507a030301d07501800c0c28191502e40804074444402c0c00c14084c405181c00001c0b25142c06007445001f022000e09000c40321419504c42d409047d1520004190182d07240000610000024107810112035955400350341ba80c071407408450f414000303840610800800e82000c119420034626004419026a0140f00d41c50008100c20101000540e03013100181e01001c030300308442e605a40000c01d404400c480c00e62a014a440000e000a6041d0082d5403145800d2440700b011540c036100303034100904c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 771422877 1250 771421627 771421657
    0x1e2111120f0c15041104060501050a200712060e0a03050f071b09020702100824040e0d0807080708060a1502010912020c010e010e03070909031b061b0201020307080a050c 74
    0x103c440300c2040c42480940f02111880c1a20746800414502802014250303101030759034a082840003202207504807031285e81c651401100c454141d036258018001300d00942403080703402079041420724060b8102c0c0d1040c8801e0003560400003070600001d0b4404c08a41e00f42e0842009075480b40c21609066a400c000100d281c41c010840c0000012101a96005061410300840c1c45010510700c180c0e041e144520212443d0120f2401000c8485560402c0c50030628600805080010420031082001b4600642040c41601044041082003011507020040d07641c00b98451a01c086142840f10116404800e90b020318403c1906001580d10600d100350b00100101b030f00052005410038007550041d494031004212140050350300000c507903855005081000c0602c901500421940b890030910500400c46030800314104403c0c0c2401e0700700c0885c20444010002c0c05208002001072010040101c0d0000046d08001564014020002e019411080b82580180300110105066441440103003542c85864107007030070b0300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 771424127 1250 771422877 771422893
    0xa0609140409080a0c1a2508060d02041e05010b0304060c110604020423040605041101030e0304030b0402040b060d0b18060904020d0804180501050a060203040b03131e2111120f0c 78
    0x4808000a0b1030544c1c1c1c4d0140001f440b54401150b098101312003d5400410102c0b1010040c20b05034400c10010140840c000309a00d0701204001c2510002e900825100030040140410b1081c184123400d145207450900f031104c5500408400d0f11a50001c00280c45584d4a04840c0100114103402005142d003030396280c9020b113000d2038043c0080009035002e86501c80d81039008140b0794000e100301030600b4403003030085041510310780d0b030441c100300000c00817030f08140c80e4481c98200e6240c03d4054031a81401131004185140210300b4068030303205c213030788029400c40c69a081c40503036207800e0f0420703400640644900b00382c1c01c01424400381c2c078807841d031204010801508003002049102d50199069500444031101001e5a50a04076507900490240e40d1004a080000c00d008809429060114520038021480340c0c6004d800c400070f819501c158141d4202c041c60304600301515081b030311072102c042d950030400104244003d925a442c51001080d00741c150f4002008502521008217840030181c081040313541d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 771425377 1250 771424127 771424141
    0x30c0607030f020622080f0f07230c18060a05130204090e06040203030a0807021009062705070902071104051501021c0f0804030e0a0609140409080a0c1a 67
    0x203240c1150b10000500403000441d00981d01c042c0128401280080c045000341540c1d202c034504ca9012060844105034104000c18048120300050040d0500400301100c180300080160401a00000140481d54006201422507a540d202e190307213004d0441c00c0126156074482c0041241005143c1005500c081001800d03441c000d61900180281caa84441c10b000164000f0001d690310502070b10000d42c103410602c20740b10020300c03401500c1c0c0d0040052040b24000c803449040042162400e180a841450300c5e42040180100d030704894150b01c0310400134104040a0b140c445e20746614646c01040d0540350005a005c0c18006100f91504886030024000c0015040041e51600c440102c200054054003500b141d28500011200141030070301826210045c648104c810b08071031505005000301d091250105246119480b40c0480c3d8014245640311450858207001d09a42c16142d420714640c8501d003040c41080005947c4019600020030608000c0b003444c0c420b14010001c2450400b0309220710441310104100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 771426627 1250 771425377 771425387
    0xf0c06060e1509040f0206071e150c05190302030703060320010e0904030203090d0f0503030f062b1101030905030c07061206060c030c06271a090d0c02030c060703 71
    0x1c552002000d0195078542c0140403c0c2042202c0250114151030a40d0015007040e80041c10420300c46d24903180304000301c5020113003082400000355160000710180c0c190b4180c00d031003501c408141c0743c00e149051503054002c60560301ca4899241b8101038002c170201c0c4544d07000f5008000650391040200c03004802c13140da030b081c0c80681a00c200340000c103001c4640701c550410040003030140350103a014510f440c02d0902442504003a0030303011204c0030318401004e008241c082c005076003e0b0407011f43d03585140c20f00400b04115030320075550b8024034249105a16110001c0e4100d84449581d11171b29807040f09805030016002080f03280c3c4017400c030b80030005a14100910114505017a158923071561031400b480301c04803030203c07841030003030501188500c8602c601290207100001681032003800003140744060100341443c1c540e0b040308404c00c0015103c1001e8204500310802c0c504010f410641000b0618243e6011903842002c01411801d01920f50018015074030b09200300e4210388809041103035941114500201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 771427877 1250 771426627 771426631
    0xf0b0a06170109090b1605091c060b0307080d110a060606050c100b1e041b030903120c1e0207050414190b0303041502010209040e06090f1c0f0c06060e 66
    0x7107465200400458004a144558072003103400c5410b004503036803404071090a0303500192400c0e003808403c1c01400b10596a0803850042c0c3e00007845038800c20540c03484c03d42e0568000c0b200c0144a0b400141d418084030310300140c080f00102140c03520281085040c1c2a10342003000c081806408142884404510581c011005180b081c070040301302c44070002e075181a00c2c22941075035805a0f102035200250380c0319a9040d031b10101801c00041000490a0f000400c28015039603042105000c00e0300d4055003800c5c035801c0024080c074010300032000c3c44180076800005000d043c40290700e4a0b242120703003203145110301c00c000c542d014241c080d104100030282c01c1c3c425034030070200b2204132824200c0890592500c3e002d0f4003900d000342001030000e5050909041e149280c064400d00030004665080c000301d0820b43e00d82c046c2644c0103180c0000f4205030304021203146c2c200b50008a00040da07900604003212030302c030011484903c0c0ca04c1c40c03a2081c0d0340980488210341c0d056100502401c0c240c14184041750a240c9440018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 771429127 1250 771427877 771427907
    0x703020a021207080a0c111e0102010c08090307030f0207080327030307020a0501050a0509220b030d3507032c0601090b030102070c03060209090a06030f02040f0b0a06 73
    0x404002068181e501c00b442a01c000400313003002401115100c81c0112004030409104514400810350304002058001490300c58010100303168003805400c550b028854000c104185d4079204c1e02c1854010922580c03841500c07002010842c0c9000700244847c402c1c814840549800380940396602500455028070310b0319004580c2841800d4069000716203000000c94405039409003601e41c800e0316000041d901c0380c20500b059000e0000030002d201560b03441001d255007009000145025401c1c4980b141c0040314103460003140240e20000401640d9608030280b608090103a0300c1001c51802040601200c2c3c0108084424080c0001000d00480903019040300c1260448180082e40c44522100410181c07000c051010b0020740041b0014010051160000382e010403010700098584080d642d29007181c20744079482540c1d040d070301103100005031409410080d004814504203005090542d00e51880501181100034403e55441c9a140800400c580003991402002030440340581d0307450030301800426007030001d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 771430377 1250 771429127 771429133
    0xb04150e03030c04091b0c0308150301021605240c0306041d1e0d17090a02060a020d080109090b0604090201030b0a0f061404060504060c030207081e0114070e190506030703020a02 78
    0x8002c0c24801400c8000d0039040d6580044005c81fa8900741e50011020303007424542810040880d88a460900042c519a145140160900b10301800e0503400c02109220520480712600c808843c040c0342d8005840d00118030000603543c984440000030000c0c0340c04840b500c042c41000180c1c1c9a07900002c00c0512568544103441c160303d40c113902c100c944408400311410041280f43c2c8030034521b40e103070203c01b030ba000c03a21204840c500082034000585581000c411100140e1040c1c04800800c1e501507180d40c0100006c010901c40004140e58910780a0350040800b8003441c2d860440d181036a05ca90042500d0a0000d80100301480d1611101542c4039a54000c04000c6083c0030260310f080454031003200c049038116581c0e1800e10f0305042c1c084400720039011003602140b00350500481c15900621405030001240002200303404601841c042c01d5400450340f002d0f440c045c100030401d00c0d9130866411443d445040f1072417908061403100000c4c5004403a045550414808000c01c014684c141d401030084d0441c540172 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 771431627 1250 771430377 771430391
    0x18050f1203071e20131109130b01090609060c03050906070b04110f010804050a020904081b0a140309150904090b0420091303031a0603100905130b04150e03030c0409 72
    0x10002d04003092207450300552205c985d41c24007183c9601c440c8051190170b8840e0305d460040740000f0300040c2d0b640c29540042d45d075080c0100c401e43e081080d0100400c01420a21b00c05460401c0142442c1d00e01702d40074040c4a40010041d1403940e40d94204e4481d036500201c14002400d060034800c40d200c83c00e4405034014980e8148074540c540c05200c40342d20496004c0d000740002d000c10741c03c0c086480d001520480310b105061001c00c40c03603103101c101d011800280200400b00c41e481c03401c0c00381805200a0260000c1d03001000000229214401c000c0140314112a600703558260141c00308006202482c400342060215074248010864480c0f000d10041001a00d20b0405406003000c1003051201613071440e2107081d6541491001038025003000301600407903000113000c2042c06001c10380315842201d200b035000c941031006000e210810310410390004025015000d00275555500c0304003580000e0000fa100da082445804810b45054025480200c620410f607500d80c20300d2000e281e403903007190181078886410646 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 771432877 1250 771431627 771431663
    0x20702041d0d03180f030e030f151806070807050c0f0102120603070e16020106120f0201020601090c0210150b1b0613020f101e0c0318050f1203071e 65
    0xa00c3d03520a1294030310b118400541d9175540401d04148500b14140201003900180d55075050000145100251000e0003d413811100b80c9450058010302400e800751004071f1180d86503070001030701648480035040920207038a13403000a864a0103000040d80701445440805c035010581900035103066401d0703001700b1100f51604020992a2078490150001c9403000c40b0029183e640842c0e5551058500d900000030403507110f02e1a007800804130b203c01c1c2e46504680da40942103580c1080484d00415415104100032046040c0c001c1d1500b0b40207154101440e00c41000b00480a92518580021b1421140255079060300aa10f03104e141348a0310703845030501540c000203841861079541c500e00303070b6401014000c00d07070175800c20002a8011180b40e00100070f041e0750000010341c2036088101c1c00500703030788034401050f28614000300103040c11040e030418650341d10310401017138443c0c02c0c1c01e10817280c0855004510050503840c482c40c5009820000d00410b101c0300f2842034180300c0760311001265020321000204036000705 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 771434127 1250 771432877 771432881
    0x40201120510140f1c0303090f080306033d110d05091903080a18060603060218180a020c0f06100302041a0112020a0201061805070e03210904020702041d0d03 69
    0x200007245c0000720321706011107801c6500545441180700b42000121040c540d00c1d800341340e6400040440d208040001803010758541040280e404408420110360004071503140c0004034040942c09850b1a2400355500c2d0208407030790044641c16000031070740d07616005000c103500007400c0140c0700c4c450a401200c01c4401146944405205401c3d0183c480103d13644070240d4040050922100c0d0b4550450f08180240c005411406100001e600980025071100c0340039080038050300b40603424600c10041d0102c0d404000c0c9209542b90341c419070450006032681c0c2d540780344605001d4460340345006406070300d003008125070450030380405030307402503804004a01e404c25091100c070002070034550210f5082c2040200c006030a800400044803144008038030117980340d118402005000036008200340e140d900b00100c203a4031200c410340c0510304400030a03415400d0713140e180c81c4010f0585000f4000300300040c8a0b40750785654040b03074040c03a80580308116088150325006858084c120040d502c074082e0200d2140801d100c2c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 771435377 1250 771434127 771434149
    0xf1003050c010c02060d0519060b070f020d03110a08041a0f090f01260f070503190203040507210c051e13060b040b1b010c09050904020112051014 64
    0x1010050041c505404010744114a40030001c83e8010010890082c1d482c0041c081c450040752020388600341840817407201020368030b240d00b110030780740b005005040201d07407511442d600c02c680640d01c6460002e91401c00b00c1341ea0011902d45501481072089100800082600500c1200c1842098024070034042e5188500e03442001080132103003100340300070607040c5030107043d5500c440307014109501070809141c1189401d11000c15195519a4030104011190b400040707240d5220780320345800303491842c0c002003240b006000b1040341e201a0754040002070800104001600150140c55510720008100d9644940420020542290340300e80707825001405003800c00000b512064204880740081d8071200500802ca40c84400009486440d4540061461011001040a0407806491642c0d91100c001c03410002e041c00540400d640c4c0c940391258150b5540066041c040da0411610b03d1555115400100d072408150720b5515241c40c80c200c144603028003a81102e2044035280070307852010661002c1009440401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 771436627 1250 771435377 771435383
    0x60e0f0c1201140a0801050c0a1d090708040503040504022a0109081b15040302010c1d01051b0f06070f030c050c0a030f14042c1605180301140f1003 65
    0x100502641c0040c2c0031101c12550064a410092603035040111b00b07568050302c9074542c6290000300488100d03408610016421110100c1b02d401440134004103c420200500a40401ca51030b00803c013002424400c8600030280188150740301c9542c216511007210712901903010381008980c034140c2d0801d042c0070322000340e5000040c85051002c1881103210f107415042915115010ba040b001c03200c140000c074614003d5000b0740c00016a4407082101500b10803c028280b40d4040d40903034284940d80c0c0c400100d0310003144404012448034600000c0745d1400800c198a28003c2c000c01d420000c0040c2d004d224803c074075040e07035024409600008003d403000d00c01c803410090180c0080002c0000f090254210301540c3c00d4525095080c00c2d810001080315802641011040508000104001901146015000c000a40c1005410707003010b20036203c3d6107070360300402000c3c00301c08030303501408000303004900c0039500340036009014020135000d084044420031916541d020800c1008507644914850000d000d40b58 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 771437877 1250 771436627 771436657
    0x70216063504080c160311040c08090d03090c1d0619061403091606051e030106051e1c0506120f070905040c03020a080c040e010c141309060e0f0c 64
    0x44a0f1180211a404864002c4441c8150114900180061001d410007540200751a290310a0f5400412040c0c6400f941c005007045500e0301403103040c100c0440c800600c0901c500340080c4880c898500380c15038211582c00801e070320400d0a404140d010304804014402c03803044a100c030b0f44108034001c075040c0c100c4c14007981001032500711000ca092180300000b16000b81d540b100301c031001241040110443c582039001800003520100b588003d5800c1c10740302c40a8441100380013410b56040080007029401410501d803030f60f4103181416000b80d0940f5049507141000e0f245200310440c0d494031398401070601a158640a400d07255200e0001c0d05021a030500690484005821300616004040000d444090300a5444c03420104000006a441b41c005400600c3c140c8040c004408500c02000100c03a40f02c4000005d5034180140d90070125440303002c006942d42844480d41d140e019151950340d0040003900606030080c600f071004038440c000c4011b01d5100d1491960301000c40d07520388401c00b2460151143c0040350f64 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 771439127 1250 771437877 771437881
    0xa0c090e1302010e0402040e04140601060c0f02060d0b0402040f0305060a1103161b030309060b010f05040b1303062a0e10110a0218010501090506120109050702160635 73
    0x340c13145410184104006001605164403690141313000030084d10100c0e08140302c0c00c1d040703e01c0c050074000180182168109404c0210382c5480f1282c5100e503044000303102e94000544020150841e42c4400f1007003101030803c54680392142d020f40ca07201500c1c0010385181c81807a0005e0003e5640380582a401001d012105085841c0c0000d00704003411200c0080040c82003050610001110605036a00704074060303035000c43c2021681c14410116552114001e0402c10034406000c4055000012581140d11520607943e03500e051520940104c0800e4000404950400740039038100c0f50302c425848524548842801007541c011041034414541b0410b00307980019081910b208454011541a581305610340152410000760398005a441c218a03440200f140c44804014811546c0c0305800d440031301001c2e03e04900d00f0100000928011005100c1c098481c1c2d01d400010350118428000e0351441484441d000da896511020081c24104c03101c0700003d0010102c2c039150240e04030404001048203c1000c0c040c0f655 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 771440377 1250 771439127 771439129
    0xf010e01110711010215040f0b07050901020a11030a0203241024140d0522020901030b1b0403080405040f020f0316030615020606100c0203151009050a0c090e1302 71
    0x8078071820380703042c10740c00b46d83e4028005918408030030388501c4c800c0e00c0200c461051450030050200f000b5081c0c41c10444103100495160340c0008000e143c0307941000032209130041c1c080c0000d103000760903c2c00a4060046131010101c00080c075100c00304803e00821042c0c02651215801c02c0115118814a0458000c0c05003114105499201e913040c4d011440c500814850620901e9110302c2d0b02003010010f082d55104104034111540e10729032084c030074024288500c209000e0f000a01c2c13400c4180009420016140045032180300d100c04824140800d144000b621580c0c0e0b802e00b205c41b500240300e19402182406109180003c10f403007141d44800407900002c1c1542c582d580c51111003022010907200345641d804000c10740c84030030005215200540d074018a010b00c1c1000c180050454038000c82024851442d4032840142c1d000304605c200308000c042d03580b14a07902c07000a250b0840c000d80c010790341c6518120070310000207002c0c2c001c1e440e036820644404100c141c0c0c030040105603d004135890080341d03203908411001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 771441627 1250 771440377 771440393
    0x30c03030e030409060b07050616093015060b0a05040303110f160f0b0306060901080a0906090b0603160308180f0301050a06030c0b0c1005190507020f010e011107 71
    0x9144088120b0b42055141c500c440b0440b10f850300708101840c004100c45040010401a066220741c513030309071410040d040c95010f003988002c2d0191240c00140142c0078030680322040b4001402d164a00c49503440c41c022424101d4030f04042000425006040c20300105105801a04803507a200c45d030743d221481e091079520103d62101e403a401c518414014005845107a2108000031115500c5511940e14801c1c034047c01202e61410a40c446a0390840900c100111542d4505c25500010b03000c2c2880700840d0307151801800101070b0b030720004125600c1c000c0c59005001e200b201207881890309808585040a03180c40c55042c001142c0700040c502c1108109005012542c40180ca0407d007020300562070340031250002a094440032900540b91581d560b400f0014007140f680c0200003005058603951514050000b01c540322940500e00c4c000f20b6803104041072895003411045298041034040811450520b801e00070348450b040c1c0540c2d405507003040c0300b10b6070400c0c040c404c0c51001c041009900c4d1820b2056a21450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 771442877 1250 771441627 771441641
    0x2e020a0518030a020a0303091e030c0504090317100906060813030e0105120a02030a270201030b0a180e0c060406081326040501120506031b0a180e0c0d030c0303 70
    0x240500501c3c000c440181c41d90103032003028500c43d0b107642c1070036400c00341d100d4003840941240c0840c00c2e080701e0080010a000322280c400307407007007900c000c9a47c0a0b80d081c280c0c0c00f9150f1420384130350320308007001700142c2c40030340b4071407000b03a4070b010b602408001d98440045660310401c0d0340740354200440151400c000384c090340f0044600c90b4103042641c02e02d22211130803840d880003201c0d10180145c0000030805c002e007080c81654601c0501c0304110f10340b15121408890002c80600c002814950b40e91014202590b13913003803150007401c6803801b001200d0a4403040b400600f00c007400451951040e1504915186044401e130307020398000e03a503506c581e90350305103100f10010389000083e124440c01032401d0070070130040c10100a08449001e00c5503525031801c5c00040c101c1c1d01e0b110010785610714000c180455a0350110700d00020031440794200c50f082d500701002850b403921550112000d0050407580300700351140c503080300c049400d0240980f00781c05198801d204240c0c1d100030000700090902004400007a009601405c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 771444127 1250 771442877 771442879
    0x608061c061b0c1103060c0a0e0f04060b1c020313170c06012403090819030605030f0c0f3102040306090809121501140102030c2e020a0518 61
    0x440d00e008072400036040c0d0301d80c00482c280002e24100402040c4040708500c4c1044a0055005180d20318103038181d10228004c2100460030460900d9a03c40190b84600c04200c072080c00070010020981d0b55401008540c0c0700200d5502c041e6407001c0b9041c00c2403414402c1e0b074400d0802200300b078460051390b41e64242494041100c0d21910070144000300c20544100100d60280024100549070900aa81c010030a80404d9115078209810030090b034000619200035101800300401941101c0300310160194003a20030340d0411340d014410035030301e00d081204c00034031004910020381d12610321100080030704c000c62038042c1d580180100702c00010444480101241c50030040c804200508040d180c0c0c1da094180c3e101700b9010344a01602085042e080c0c502500d20580c2d6910070340081402a070740d014141000b040502c00e0b5140b03210140050329003640203004030780d8a00c0d40c590548030600b500c80c82c00707401b02c0481c40d0403006101c080940b80d2000c0a40d482104e40b040320688810b4100402107100f440d050000e20042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 771445377 1250 771444127 771444131
    0x603020906120a06030b01080a020a14010219061b03090209010b03100803130306110309070302010e0409060f0203100b04030b010b0d09050d0806090915010b130506040611070608061c06 81
    0x38010000b071800000d40510440600494140e107141010b100460041e000560a80c100f2a843d10042ea01c01011400b07e883c40070703600e03144008240c01030f400c1c448160082c142c0060b054a908040000039800140038284d040403c1710b4802c030840c03003181190b10b1524000e4104140100511801a00001840c0d000d42c45094042513a502d41c0256820f6070420f400a901034503a10034140204201800394000c4a000c40010300d0451801c2c00b000c0303960351214030000e07061040c240940708003600c841d0409890103401403020321608040700d244d03000039070048035442560081020082420303440c090444003183e40041c013034007090f400c1a205640580c40464050700c0b187d640d011b4500003d0040c000c2082d0f2940c1a120b9088600d004024404219001401401e0b60f4000100401c8500f8200e100941540e24040c07155841d0303039444221181d81c09483d0041d90384460086400a1500e520a0a80801658000640d413006507116002e07610881e00713031440d90717020401c0020800c85030308000f03103002404d001e4280 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 771446627 1250 771445377 771445387
    0x3141614090406050a0617010b0708070201030b0f0a1e050a2718030302030601081f060e121204060306081f020c210c010e0f0613050f10020c0c010206010602070603020906 75
    0x302c45c2941c0d5071009020520718151005e49040c08401280105201514940740180980c0c40051a204483d0000d042c90754400c400c2c1242e03250b0030b02a000000e8080e000d41c03002a02c484030b5070716014078001c1d0107940c44007400e8045410300b4103407504c4044802d070060300c0700100e41c59000744d103c280ca00c2c0c0388001195034031218001c17240c10700c07800e071080107001e6100107039642410700006040100041c801c0f12403440c0016050341c0390804821000881c0d505181000f40c1400c04030024903040c100714420b100b24443c591028213280c05000040c030850300291800c0007000c0e580c2c40d0741074540b5480c24042c03032445000d40d14541d0502c00e540044c00600d0031941a181e420a035101e4083d08284120b100382900340f004200040704400910591800c440b4220007801d25102d40940d1658444000340054250b8400c00c00507410040208a590200c2107840705965020140d0301cac20f14001c0d040749025800500c0744847c5040954004942141a11080e602410b941800d2080c02d030041d51054910729013200302004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 771447877 1250 771446627 771446629
    0x303071e120504050f03010903050301061803050601030b06120616050304060e060108030316030e030d18060204061e1805240d060812130e070e030109030314161409040605 75
    0x110740d1a55555949401d078659041205205108a07403540d40c6001c1d80c508800500481d42110542f81190003521f451502c610f6103000e01c0000211a41c802001480b032040080b0030032484500350740c480c0000b40d40c00102c50b011720001c2646d0f10020744100c5440c5044c1300007914014462002164002d0181c04081500303015201c5c00303850b00100341e01000840d0004014030000f2000c15101e00580201481c2c14070145c1c00307010020b0f03100d118000b04500300c582c0d03402e241003542c1018103040342c1c000d80000045403180c0d40c4e01000f03031007030001103082da460440a01c1e0b0002c02900400143c00542d560841030795550b400e10083c800811100c4124010043d0b032940007551080d120b03030007410032503440b1030086103e070301c6c04424a10705000c0c00a0f045440c1e40510641c140e00301c401c0a040c080321205407134005c03203440c0c00c0707002d071030f00d0402180d025015424007070504103140e01500306005105d5007034030942c26503680900e1440403000303201d009800101d011600445075900c072030150544003030080000501d075940760 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 771449127 1250 771447877 771447893
    0x3170712030b120f0a02030d1d062a03031b070b040215130308131d07031107120c050c1c030e0411030115020706090518040606170a0501050606090303071e 68
    0x8199142c3e10384c17100c4109811410f0602100f410f0b01d80c0da09048806403d9011034a00780d202005845002d254041a8003401060718400500710246030784602855150001c610b9403070782d0045540c2050000da001c5095144130006d0216040c03960000304c141019155a07003000500154561010420360b4240b0505042c010307039000050040d48074103241d5540300503403e020709120940c1d500040703c043d40141c481d480c000c410005180c1c410250318000440c0c281c0301d1240007940c01180070140881c0c0042c12085107882d0080768080005019400300c4005000d40010060340c100408d5540c0c2d1821b02144040c4000fa004030900301d2208002400460614040c1030006816082640054001c0d552814007064068050180c100504000d2a04901071401c10b030124122088101d4140614aa40710002c3c0c10b0110b1070740303e080031700b00d42d10502c503520b0b02d4070403841e6848078244016906546048040b422510740312080355806200a4051420301a00303449100020a5281100c8d4480c00d048002d8800541ea81d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 771450377 1250 771449127 771449143
    0xe0d05191704051c320c040e0706181d061002060106021c05160c06110c090c0306150304080d0501051008040803130f060603170712030b12 61
    0x401a0100310060606082400503003006070010700c90801c0005105940300d01502499415602c2448103072515145070011110841e004480c65045100c1c050700038503965081c5200c100421941111100c0c4408401c00007280c200c0f001200090340800b4040007041d025040342000c840c00d544a501805a60707507154403a41d8820340e8461214140001004002d161087c400107507810b0703500c010440c42d81404ca02940c1c4561988000951941d8582007030364807031103002112020760100c1c040c120240498641000a0065400386101040c1c8070281951407500000300c07604203440051240d5841d468081d840005503001901480d04010703100d01041122027100011406035200d84886035079014151500c1c4100c801c180c11803441000038050803140240c1c4020070030b070450303004019195a521103030008800204600744c01007a503031250280c4020b1004d2503100d4000c681c01801000303d05580284d940410340f044d02801420b03c49071080d11114180300741d001030041803000d8101c2c2a800501c0b41d4441c0351082c6d0f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 771451627 1250 771450377 771450403
    0x70f030c081f170d0912080f0f0403060c0c06200f07030504030f030507050606180f0709080a060f0b010201060503070b09010c021804030f050901200c0402030702031308030403020a060e0d05 83
    0x3902610314051750000000004080c54204a52014516030303900c9130314403812030b11208002e004078a1004800d80b0b4000c480045a07c203a0030007900b0413a51000d818010122010b4503002d140c81d12144100305030f00100c2400d09003c0c4000f44c84e000c0c442081010582026109404001043c070001c0001003820301c0c0302c0203440c000c0d2110394031010030780391151401c08000c0006014852000110303420941040001c1c1d0008030010302107c440e561108112003c0d4038580c045e010b9481042203120a1040550056130030f6020031000b409a0020000103900769070507841002c1d0107601c5440200310800080024081e0244149003440c1480074940000c0c107a02502a044c5448502c14410700c0304240c2c00000311a041200d5017011410008810300207020382014401035001344469120508159a007807040500500c2d0040045440b03007420140203590703800c0038a00310b00c4418031982c0400c07070744d074004107031002c482d4020205a80310b82044003c071449650001c040750000207400b00c05002400510400c011405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 771452877 1250 771451627 771451633
    0xa122102061605040b09123d0b0a0501050f12190f140105120703060905010501050118052b150b0414040b04060b180f070f030c081f17 59
    0x1020341c1c5420840020b086014244102040200210144007054500d9140101c1d2004003a80071843c000c2e08003588901407a8582954003a1070416100228400004143d004030f00c80380d060002a544044a2003000555070016454004000644c0305500130300d810b1201650b41c6045c0360b400700e940062120705494100848100f1101d0701200405840788240c421490030b0305015040020390f034a00340781c00c1070155034000c001480c804190f607001040080000e40e40070408000c016242e041090081400713024150008038541d0b0300305072648030205201e065034070040c0004210340c000da42c8501409160a107441c0d4440c2a84d8503c00070031001511112a5007080f600468050004401c1200300ea200035403040111a0030028040450200c07600240c0c0140d1207040020103c0f40c07400061026403d034850301c50f45100002c10040082c544a5650340100810348a8111440300e00070b007503056401400380ca00000d504007000500020340403980c18031842c840c0c2e146070812034507102d00c1d200d040148030000d1111343c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 771454127 1250 771452877 771452881
    0x90405070e100312030b0d110a0308160c0605030c1903061d0108010e0f120f12010b07050705060a022505060406170c07050a080703030f05010914150a12210206 70
    0x1205200110a041c61340d860b04121860901000810f00c00d2514005808416840c4001c070141d29243d05410103540c011700078984a500e2207001100d420520701c0308880802d07050b07000242090055042d64001e03003ea9840c103042c4000d20402140d40c2c0c0f404940441010b841d01000074550071402e06c510390230b00002104111960420741d9842c217440d05003810310b070517500c00d0042040406010640391041c9480100300ca6690741800100b00403170044e24000b41081c00c0100000600d04500c2c1c0c002c244851150301541c5001da640c03000c0020310f0050171001405a0021a00c90380c0509441458080c0c180078003124040264503032010680a4019400c04c601141e0008011050081040902035000005004140c41e00d8015509e09450301d150100041014101048a800301070007600320941006071214200181d607901d042c1d81001d8102c448802101d18110404500c1c801c0c52094114180b0b44c02402c0300807450f2521102484e01401c0d10780988101e02200c1c8040902c506000400e400380c400b90f40100300c54 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771455377 1250 771454127 771454133
    0x20c0d0815010e01050705011b05130b2502150309010e070b13061101020f16120306030b06010f030e03042405071112010f1b030f110702090405070e1003 67
    0x100409003030605800e00800e00c01c0c0a582e400a070740c1640e698280b030001c2e1940214079245000d080b03c4040088080c07281c1c810000010b034484c001d40010006141444082e554410130f110031486040c0081c0e909810040c1c0e0314103003070310081d0503050040c03001e400181503900000030103e0301d40003900c2c07865059440d07080301410004100001009040c2c10b1482914100e03030003084500030003840c440e41040c00a8001d886000c0c0d0001c2d410746584d040060101945c1c1c0380204c2c525180280b924004582401c0c0f040c0c14031000500c244104400c1da68459054402906e03024019202491220003010426880d50a452040001030025000409412804010f0140300c0389418580704080044102080828405180400c00540a204504409030342040855040d5051517014150b0b0030384401000d401c01d4080c501c140b48841b00d050848134566010015080d061901e45c1c107591543c40201000181800a417026150039000c403a000f601c10001c0b0340704203a40315001c4d041c401080f201c9000c40201401c0800c24 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 771456627 1250 771455377 771455387
    0x1401140108010e1f0b120706050d0c020a030e15160804170312010302090408121009050a110405040b19030506040312182a0803190c0b0106031a04020c0d 67
    0x80050b403009424111003910310302c11098041d041a0f1000d6071101001d950a0b01c900c400c6000549405081d50101f54507503002078171550024141440309440c000407551154400725002e00070170780c580e4030b203412950741400300801006100440045520200b240042220b000408049a24803030030321079807251718101044200d8800c03c118070401d604100b1060b520440c0200790181034990486a14220352140d0801d1030a900624842440340c41c00351082c41341000144250324212012004207101d10340c2d459100c002550b01220070303080040c1c0103120900c50b5141c0358002c0d071107050014281118001e40b010140d200ca210a40c000d482c2a08401c00b032009156100002c610341c0c42c1150303401d100fa00c035810901c50401005140142003000713401d03203012200045c0642814019000c0c1e4100c0045138507443c4154071780c0e00902c440844402c2e00c40b42d400c0001e01520100346c00700d40010201d10941c0c6081419006813150817014200d80c514460041800c0d038461019005034a100702c02064a40d84000020704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 771457877 1250 771456627 771456641
    0x15080105010504051e04050304051e0a17151306150608060612130221162907030e0621060906100e0406080a120206160813140114010801 60
    0x400382c0d0400080017550343c40045409541500070b41d41035600d9503217013803060450069410035036220142100c0112022541e1011030f10210049801d20341495030b035019070380d5403a98140411080e030000d01040381c50440340111243d00200061900c2d000400640d21107040b51002c0100700707007140d83c0180501a0b0340e4480c0d2116880002944c169142a14031050440014001064030140c4203400c00680d0071074a841481820319070221741150344c62100e481040303450300201c0d0407403404604c04040005034401c00300c090038403038031480545850250414250300c250b03900502040e8144074148040c43d245032201d0004040800d01c0c2010b00c0000700c0520f00308542580003410091282c5911002c0c081303d41d4070741102c041c02c1c504a003014005082c6000115010b000507074084a018003c8a21002c00e01004c1c450850500c10b043c0d09a84283c6d80e540e01504020f4000011180050108400101d06100a460203041503000b24580418070000044913429600d900300c08200c10204240100078008090103141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 771459127 1250 771457877 771457879
    0x121a060706271e03030b0406080102190201090c03031b050714120d0e060306010c08030a0603050d0f080105010516051c02010606110316020d020d080319092102030d150801050105 78
    0x1a002c2416601e0b182070b0681000103840644400c803411004242c0268007416403c04c0107002800340c160340303100e103070b00035002900c0c1020880d01c100c3e070854503d41306118610700300c1e60102c0c41851160664400f150f984044548a900b0034501906850105900b00075100080c40f1800071403140301c00303c106000c448401048a4500c0d40d0100c0002407035160441512100d07048140d03030490722503949000488071000340344009419801c00000f03001138880e2907044a029070303006004803030107400701c071800b114580515082c0c40006040c903401446558070400091441440c0c241c4010000540341e10fa1500300700503681d41e9081d49008101c20250203030280030382d0008100307d091000c0c400900a03801c5480344685410b103a103c40c81c880d01c44c0e0031951113031402505540c02078082001d52001e4940440700d90301c01d85207d0307031f4503581c568005120181800f400011560088050035481c0da00384640c2c04202ca01608202903000600000034940014400d082410041c6054800c09a1a0110090848206030021 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 771460377 1250 771459127 771459191
    0x2011b030c030e040b040c08060a140d060f02071e0506060a14040b03030c06160305090d350c07030305090f0c060c0a320c01121a060706 60
    0x2000100ea000841a540d40390182031010101c40c400c40080d008010749602d140c0d1091030f100c5120345090f8040070040c480c020589503015142d48402030040014400808558084508011600001c3c17480e007245080d900095000750400b116030340d41d0f4130703c9900300ca00003d5080d0403056000901c0010480c1a420100c1907410049003810204101c000241c028081d600903501c0d0300042045882c100115000032417464183c4040e8141110a54806140d4524803800a0304000c0456141003001c00c100c2402c22803034071906903c0401e6541c2c900111001c20005c000384280c101003e00c41e03c21a00324070710a440d124880f503a5007030940780180031501c002d405c0f00b100707600c5506860004140000c3c0005a038004032105501c0300b206120f0146451415000245589500d6240004043d2200da0321200394141603421420280c4444000c1e80c0d031050ba00f00303907001848641c10243c221030242d001170844581039940c00190390744a00851900d900c954400c40e015503403902040c01c08201060030080b158905009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 771461627 1250 771460377 771460427
    0x117040b01050d0507092d020a0203030714090405040804060318020918120f04090e0d020d0e0f0a03141c0507020402310e0c07080414060915070201 65
    0x100d2503484014014640074005842c00e07031050180410401e40103103888501405243c44080d050443c40100c0360414010058200c11303c001c0b007031a40252224000558010f504643d00c21000b01c80404201076840b5a4140400400700b280c0c80b203000701031050340510071a0342d8076460030400904503031600d01c0040d69900307850030a00040e176584026640080300002400d036076800c000b100c2070030301640e0344040c2464140015400810200e8501070b1089404086081083d61420050561255240c84008005030000c40da4061a54000c030b03d0503491800c040e0401c140b20300e2102c04a02040307819001580d600d00c81c2e00402c0003100b010040c071541c100c3d080d03407900480c400640c000352150140000082c421a00861007030203030710062041e00b4030b01b0590082000075030510041852003080d14080c81112454450015024024000485101a511003552840c2030f14007142074080c08101510280d000b81c08001c50390269450110750020168499200340e582c2d2014400941440e4044240c803420f03202e00c60b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 771462877 1250 771461627 771461633
    0x30206060f0f03100b01021203040501050108061b161704030c0e01171c0c17030601021c021009020f04050408032a0901050c1203070504090f11090d050705130209011704 74
    0xf20341800400f021300c0483c105411100507810806100d40300c1c0c1e034682003c000c1005110381500218125000d1009991540e240c903c980c04803001c1102010140940402c540d051490420b0718408910740201c0c403034840311843da804840c1680c400e038030070f64040c80405018804c0c92443c042d402e00400c5000400701c022500404002d8803210f04005204d4400e4403a42c2c08004180113140315074013035600c00b24444000b8001038901c0102cac1c10035104680140f182491000d110010300c041c014640a8030303001046500c2180001c80f010700f09030f0800b240c0001c101d01d42410141c47d14040c07140a18070034035205480340740511050787c4030309103a68010f600024502448000c0d00304070040340c82c1c102080c0f800c0ca6494083c41c4103075150003c0c41c8000c1030511000403c00100d2903000300070340282d61401070280017103038252419100f079400a00741c180007003400b00125105841c1045001400d148183c0039500c1d919511030018072040850400000d84a4000400384269a801148010101014505844941446e403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 771464127 1250 771462877 771462883
    0x804090c0801151b1a0a0606030c02060609060d0201050c12071502070b07030e0a0210020f0c0111030a0f09150c0212061e0c0d020705010b0901060903031409060c0109030206060f0f03 80
    0x2410000384c811200402c00b0034409440511403615150040c0034119040c4125408024000c0f442414002448d101c4c40003c0640701084880c005c403001000107010342c5035042001001c0c100041e0480c107000342001040c00c1401d0034004905042040306013962180c1c0c0504080c00000c414040e41c1c04d440d441000640c0c0003456264031160400b031940390005100800740f600e9440c1c824000e90183d400300f484402da81c1042d90004084000d6000d810580390400000d90054bd445079030180d0600e5503800500c07003400c4151141c2c1c9410078402d018540702c000301d0340d00c14001c3c0c9070240010402c0d000800c5261002c055050003d40b400223a0303c444000c151500d8240300e03c14801c8410003600b40403c00c10404240b407400824155106160040021940d8100c10710344a402414850000c1d0b00907481500002200c40c09842d040c001c40c0d17050307121040c4001c101004400243e00c03441c10168800e42c14444840003907802d1280e484d442d482500281203a04281c01004034902c01c1000b00d034460800556003120544001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 771465377 1250 771464127 771464147
    0x94c0503070e1605180d050a060b0a030f060b011e050c070b1603030c03110d0504020907091a07021804140f0d050f030408040314061801090803010e04020a030804090c080115 76
    0x9141490312a0101c9441005480710002c038681d1008171a41a00b0030311001040234038240b403086400300192200c003c103115021503a0311001e045441d00010780c802180c0709410241c801001450700b00d41c0b00315041e9254844c0a48ca0b05044001400805c4000304d441007040140050017a14903c5424010340e0075603000c1c88a44030710300908168840b000040228042e4205280e10464040b101c0d0b114002402024000e000c12142640305500207404100300d40e01072039680d010b0b40d040c5240091b080400035051202940920400ca800030745100041c13001012656045000c0c6205072101e610410146d041d591500d031a042004202da0401c0c3c1c444d03040c2940000445089030100340c44e03503842ea60f4504021040d07025a60001d84601f0f4600591480c9501c00700d2601e00c035141074081994800d0401da0258220343c0c02d2000108450801c0005210b0940da071003d460b4854030040c0400540e0740c584d907da8010b60802c0d844030f082c03180c81d00b0000702c1c0f558010f07100502410500f25590b02024000400038510795807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 771466627 1250 771465377 771465421
    0x9070e060f10052107020a05070e0f04080f0405090103080903010c0f050306040f0e101b0503130825210c0804090510120804060e094c0503070e 63
    0x10009403801388056100428070240c041803114205840d145101944a0300001822a000e000300c40d400304461103c00c513003e01030791511030000703040da4803581d0300b04403079100b141d41850541c2d00f400000340c95521800820702940c41501e1464440030340c0420b140c25100005240c5090000c0d1071a40b00c0c21951042c00c4d0f80d4440000c840200b00015900c0d004401803206e4007999140d070040741e1320780c030b2940c000c0d40111152005291000300e4482d56100219110f0005542c003444c200381000360000820400000740074129480304180074444081c81d408084a282940f044031800c40440b4450f0220282846e5880801102e080800700305402d592904803600c0f590180c0380c00c0907500d02c045a02c0c00c2e00005c0300c001030150401013220100f210300b0100c00c1c1e5045846071100181168502d8582420030703280307035806400c0041140d02c034040b01c0070704941d96684049880303040d241144441608008807078051100d0710007070600080b0041c10001450b08003006034002406840b41c000a01042c001d0b41e49001201c005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 771467877 1250 771466627 771466637
    0x81602060f0c210414033118060302040c1115090a08040906091b120b0102030d020f0306030d020d022104120302030d1d0a260309070e060f10 62
    0x3689103403416080c010396800e00740104034050521800114503603c90f0141d40aa000349250310401c40403d65070f44195403201030140740c04a03000440f81c03803611081120084030684240070a446079543c2404508500c07001c1b8a00e5100e0300c041096041034411800010700c58a419000605002c258640e00e1010400a07003840c58000e000070031900c0e041c0401c0b43c05c0d6610a05544d9200d54030704282003d00402c4c0910080d0701c0c03a042d41c42c071a01001c104841c0c2010210b868a052400001ca441d9008080d09900141903010400244039421020b200901540c400412150b031241481da0034540b425140b8042c00040d540440c01940e0007a0300001d030020400039802440c2d601e01f880005030605801070f03501091411480310100c808041d0040090f065a60603000200805294900d1080d200d08030070400314010340000c0c1c3c246c4045417180d000203140c2e034500300e02c4481c0170000301e0b0440f4166100321801e40454000c0b00090000e002001102c0303800540c200e40c507146600080380051074003d14210200c0c1400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 771469127 1250 771467877 771467881
    0x1091505011401120e1518011a010f090b0c01021201080303040c030807050c060f030103052e0c03090f0602031b09090a1e0c030c0e031c2706090303081602060f 70
    0x401185c1060080320107200640e4074094481d02c0101c05650103440c4070341100d100e41148803051005204007824030041716540c21901241c400103450303444507540304104200950302e0110754582d0340401071480c8898100010780c9e0b40c500741c20f0300462400c181c00108403038204101380408a04510f214a0070359401c0510565280c0261520345d15000e510300346c0075000700011440c10701c3c406064020318100d038091020342d8000401e401c0300404000201c0400000785ca100900c3c00200c0e149a406044d0041441c200021215002d4440096650030104c1c1250758580001c1000301190171047c0050000c0880802c107403e00440b607000403160800104401c3e06180c0c1c482151020380444100005060701d42c007001c004008280c8801805882e0200c205804105112100b003440c1c1000520b444060640400340c2c018824204002c075440a544d10550070001d0381001c1001108000545d44001000252920344146203146000703490400c00404140081d41d00c0c03282c41200b20303000328849600180c1a802000c0b56 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 771470377 1250 771469127 771469157
    0x30108160503070501141e030421081603060b1207020706081902070305121f061416080403120e010f030606170703110d0218060c0a0f03120e01091505011401 69
    0x28001d001d01082011f04030760500d4485058400110700a90081e5a14a0098210710716010300d071a5a901010001d2500c0000444c0700003022020a850a030b10714000c1074017131341c51030422050b800c100da15a5900d2400418000c503e501003000c000117100505105a55180080c0b00d16911744182401d0003d20303400161560070548144100e5080811030302d08030f0a1401e011b244243c00242400b041c804180701e003240032031240e000d4a00410410100c1800621744842c1c681c0410004010b90320486484806100120000f580c2c210500c034020510354843c640f080c003080c001822548212140c500b8946448010721006c3d500611031201010401005200e94442c29012401040e92176031036458150003103030000d02510141c0007000359540c5000d050816400142c10040f00b8429075042686035807180c0070b080001110031910141480c0241002c800c02215640040140ca861060344986039550710f0b4820100710344111460021041c15004000d20340c1000c002c001c030725142d181818180301d240c8249440c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 771471627 1250 771470377 771470417
    0x4090b0f01170f0a0b0d1412090a1412030f07051b1008090c120304030b370f020409050915010b041716030303091a10090207080702040e03030108160503070501 70
    0xd1881c006d0100f00e184840b504004181c511203800020b0070b4041e0340c0000c0703c0138048a0a9071070942000304441b40326854807249210090421000a401100742c0038240c218140c240081e000d000b1440e070303c103940d03840640782c40c40c1008200c0040e0040743c5200c40c0b011604c1e0300d0744070200c02840b00e24100020952902c541e03c0b0b1030509030322000e961141000c00030f8401c84c400071002d403040341d200340385020080e102c0032488141102c0807000d0000070946180700450702007203000780601220714400300065510100024406070ba009410a072078880d11103041c0100008200412005c00440303002010103941042c82c01c1c600e5110317900c1200451306144042000c00c170002e0020307002d028051100900225902c0c42c000d00504460941594166541c02c5440e000c2070310842c0c10b51049025207141c0d43c0306410700240900941110300255800d420911000c00181c899125454801003100002c6440c0d40c03400b070703070545030002c0d155440009030144101040b4503200000d000069660900704400082002c200d10f000d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 771472877 1250 771471627 771471641
    0x1502090d020a0b0c010c020a080d1e11030f07021b0108060102100f05071b08090d0807140601030b10031113140a0b01030c080103050c040905011104090b0f01170f0a 72
    0x2d8010000080041c40718141c1d002000515034000003800500c80201c0e00b030b038980c5042da00141040303504020001410340540d0110b0706070b00e4480503081e180c0e0701a81502080f15103000144624000003c01d21009811b516450f540c40022440200480e01240744214080403a9040c1d460500c0303190804912282e0007400285d40c11003000f4010404090f0b4443d005000d4141550803202007000c281c131250002c000a860b02d0081a00003000a1404010000f0f000146407a20001c0d13500d00001e220301d00001d081c9942103c428482000204104d50450030b04401002d0060010952400340890420004601e800d003000b00140466441182d0024103048101920b1b0000d10b4044c40000754041040760082d17544040900c0c4002c0c0d82c1001914480f01081c3c6040401380805001070340040d508608034500b0390004400380384540000310b28000c1c8903000f00400e420542140501a0f1280204092070900281104088009207002421441c5109000140c04030160803900010f89503000225590482d8014035 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 771474127 1250 771472877 771472879
    0xf010908160302040b0d080714210306040c0516080c03070c031a0916090b010905030327090402060a1d031b0102010f06060219030219140d0305041502090d02 69
    0x40364007000300d800354010860360104a00c00c9180181c890058100740c040c814013641d0140c056450700d4240c0c2c603003580d0300103461000c41d050712829010800041000341303114460701c02c1d80b090300d450b402c003101008280d0701a69002d40030041c0c10710925003186010520840c0311500320180556a1114280d03070303400c40c460030002504020785518000200034080000c103c0240c030141901c0c5060b01d800c13080a888203468031800031150850101400b0088180c0c0c4007480300c0304141401900540e882003c2070071a04480c40310380000c0c0050555903440a070030142401122001c03202c12419160a1b400074406015007070021003002400820300400d080da522054078010720080c1100e00440720385134481041c1c0342d603485a032300550905030014400f0300c103805400203403616a0050302c240000704501c05000140c24a080d0110311514540c0c01490112118401495000e840c03c1802c0141c0e821b1514685400340070394004051a20b410400880c1c080f98aa11480d9074017400943e856171140d002400d0314209200203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 771475377 1250 771474127 771474133
    0xf232e020711061801080a0e030a08070e1806040608030f18131104050f0d0f020f011403010e04061b09091119081038040f060207051801060e0f010908 66
    0xc0e401d44080c10101c80b00c041c0090b40c0b50546c1d1b03504e149a24080d02c556210380d50f0130f98014230640c084c9038000c588943c0d00403442c0c0b61542c4044d14001c005680c05e0100001d42560420041c00d20130705040900800c4040e000100c002d5140c40b01d080700040044c070400000c41c1c040304c00c3c51b03101d158581d9001103440744011136403002d1290f64a4024600200d0380944120b511410350880c0d0201030341440c040c3c4c6010f03140c0281c060120420785030240300078807500b540020304000c00c90800141d1416894003650213058044000961440c0520b400c01c1181c54042000315100e490010b002c0c610b5502510034015203401203030201c2c50072000e188199031409880300c2c40030100c05407400031860b01c3d40030702414800c1d07030b081621600d5559940c4002681e503005800d80c40d0007000c138000c3c03490401400a001c100c84c04250a00600e40b0360f03038a40c03614003500280c0000005804c5028200890300d0100a18000558112040c1c00303154034041c1c02900c0302c0c106484003800382c00302d6411040c142e030040c0b001d90014110101a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 771476627 1250 771475377 771475387
    0xa06180c02010501050409150c0509030712150203010e1602071a090f040e0318030a0516091103010e0721020d140c031e040f232e02071106 61
    0x1414016003640030020005610389000002d0030b107890b0059154440d00146c81005003401040080080c1030103c0b0300f1402c0c03140810414a086d20300f00001e500600300c2211409590b21945491400c0c8450104001440d40c01400180207210451580e03a80001e4020b0040008a003540000c0e03090101c16400700405280a105c44d40e040e600d840018144040700301e51480075412400208405c03101a421106041d82c01800130311040403061025142031040103080750034840007566100d1403c51070648049100711000000c220108030350248401c0300c01a45003239030441d0305110b079584036641c00610380000c03c00d540c500300c1c80020b056204c2c0044030031f01340e400f55507810307118868070046c06610304150b070a44480e40003c0c0c0040700240950b070183c07014010042850b0703140c41a417100401e01070820355044103802462800280580034188a8541e00607601814000807001242068040700130f000c0c5200d101c0c006120424152034840b028241100700060b120000e0b0700740030f480c50100390005d036001540042c2d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 771477877 1250 771476627 771476669
    0xf010e04031407150b040603111504080a030f080a0b0f090a14010605190509030d05131220100906031d0f030403050118171e180103110f120a06 63
    0x501c070783c502d2240343d02c18030400e50a82c5c140412075049101c054250740010740080c84500e4002c110026401b901c0c0c580342d0038680c0ba0100d1501b44030b05400114007041e22401800b23101034000d540664011040c1d0010482d2039840c001080b00c2c1c0003540002da2080203130710001804030740b040d48507070550284614000140e40e1503180c00b070090b41c48224024200c000c4142e40b031501c0c83c45070007103880710b10010307001e456440010b00d000c0d981900002001c0c510f44000070380101e140c0507504483c911490040045041c0f040c2e0040c00000085c0704000c0440c09001e48084d00d018840d0001076800444242d890000b400709040300642d50018a0418003050303a01400940c1c1c50b18aa0000181040d01c1c0114000c2007440d907800304450710f20755401001800218544000201000010081c0207010101850340c4203c104c68003104440c0d50041009046022040500130f4139540d06d449002101c0101700510340c83c049003010602c0c094010f2030790009600c1e419000142540c03456400402c002e14a4a02a200c0c242c8244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 771479127 1250 771477877 771477893
    0x130c090303081003050318010903050a052401060f081f0f05030609010209010804030507171c050106140928030c03050c010518240f070302150f010e04031407 69
    0x100c01a80002c50801c00b00d40d00b007030752a001d4070440e58000c008500c0d011000c280c1c0d082e038900000405050006080001000c5001800364061003441000901a004203c841329649141048000325034107482d00018404150098031442c40141d4078180300004d44d03141c4a251244d140d0180d4038010f884600f13034000408145407035103c000e0320300032415202c0c0741c1d5449084900f00e001c0e0302c021500107071040700480c2c0401c2c000c0c402050740074043c0d008041c41c1201d00007403640325440280d42000307c4884000041c01c010b050b2040e60b002d000c00b85030140e51001c0e08000c2850600408214500c14270200f800c01c01c1120084a801c1d461600c184046100c00d5500c2c10308e82204802c601c000d03543e40c000c4446000703003980b040d41143c150342c62800400010f101c0c513100703012110240903c40405942d961900007045ca07002c04c0a00347c0032440301f2409950300e400c0d00d00241086180b8a901c91208042028089401d0700840d089055480f8401c40c040d09680b941000c941c2c0c0c07241d8401907a441480018903201b800700e49 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 771480377 1250 771479127 771479129
    0x3140105010e040b150c0f0a0c030f0f0503030c031e01230a0503060c07020111070e010603090809031c0e0108010b0d0e120d020d050c070c0306182117010e060d02130c09 74
    0x80c2040d55182c5a00318039a9072100d198400041900007800f008ac000a90440c20f03103034015010b00007545400b42e10f956490300d5644142c502d680c484401104000842440800030600c100780d00c00740e64099490261429002800c0b500c020340c80302280441c441c016210303605039800410000302201c1c00d07424038500410300c070303070260006900042d039070f40100000c000005901e904445c4c40e11180f0350303a6031a102040b0000c06584000700c900302410001c0d82e0341c80c4d80400074151651004030256590301100325001c3c1210300c00e0001d003418070403511700412100580c0c0d015105450100741c0d000c00c6c01244243c2860804600039040da4a03120049040660f00e6440e0b0f000d40183d5204c41010847c03501c030000c5500c000c0c024880010304842a821003840006d000d0b4100110b842a0320104540006150341c03041c0c90720800b6010042049c43c028505030740c440e4800d280301400340700c0c49492180c3e5411303c00004800d42004002134014070201d403d910454560310f41074104c0c503800c80420041404040c00c028030040c5d103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 771481627 1250 771480377 771480397
    0x131112011403070f18020d1a01030e0d02030d020702120729040e0a150510020f010605010507080a2a0f0218070c0209040c0e01180c03140105010e040b15 67
    0x1032074501126003400250481078038610442c1404903490541402002c03d0100c9140340310a4003841036008190031801003c10032034a0501c101d481c603100c080010100c440c01410140564055491603800b140c000c001c944010034980070150b510511030000c030340c0800f03004c0c0441103c2e209600b400a040160018401200c9030580e07c00c036029600f2180d1000140110301940311900848004104040b07011782c4035280111388481c1c400d28255075000090b07900c1840e03584100c050313004144141103c09080c40303084083c00090804600b02211a2a07108640c040d43c1169030600c40340340152141c29040c1c41c101041403140981004100c10b441c0351150041c500440100e006291820300681c1e6484800711480c415445652207400008098007041034010001c1c01c16102d94008100206403c0001100325003c6d10180c3e841000d000c0317560421804a9a04104820405150550300500c490581c245641120704c2407030301c145195103a200041c01404651240e951090401e44a21191040e03103014203d1011 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 771482877 1250 771481627 771481649
    0x102130602100b01030203010506090405061305160e03060c030c2b0c0201151a0d0209060a030b010207080d020303040b060f03100b010e0409020f090405030d02120114030a03090513111201 82
    0x3c8608019810783c0804c6c007415610a02c14040c40f4401e00f019800702d0350000e401052000401d58a08080c4112541034405e8410381c2408a68102d149400c4281140e00c00801d50041040e450a0480c5100c1c500000d803860158101c000303104c40c00e1f410102e21244c50070790000d03940c0341d806514017140e00080032018110fa009d03508000103e10611100c040007400c807614500707403100703802030503001c009258403024083e20310a5007401807581a440e600040c281c4000248c0340011903034189000a8030b800159070100032581d03c000b4403070360325680c04400d994001d584040444502d44440d40041e042c450980030290700341c481c06103803804c546107907004281e0402c020b0b00c40c4054070542d502484203a03404084c02030740107480c00f5000115400c1c12440940e1190003481501c0c02c0400740e400c030100382c0c3d11107880751452100000041c401c90511f0610620440021402040c600c501caa9002d04586840d02c500f600c91242241100604c4d5074903007000c04507074400c141c11a81c07010300c105201e400d2082809a054221 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 771484127 1250 771482877 771482891
    0x14210615130501030b030111040f1a180d03030e030a081b0903030405090a061706010f171903120e0f060105031203160c020a090902010e0109060f0e03010213060210 72
    0x4624103089414100310a2003100d4624103050065000d01481001c080e0190340e41c81c480300c1c000d20000050000303004070394030209580c0c0c50140c43c030709461020100c18115003401c0000041800212002050319401a18030000e050103900b0250300a00604031001d1527404005150b0309501d510030441c038441c000c40146519031010140c003001d2a030250548450301a88200003d20880c94003504503036000d801e854001c21501e890341e070036211140007101c0c044101d03408103005100e907152045d5840b0250054029450014100310a0f5a0343d48045078500c1c003d401c42401c841003410311403a0a80044c010b210703000d0003886e80c40c4042c3c0d6900e14109140703681500404001040910300818546800c840e4400d1040c1075481d0042201c0b810305110803550144200320200f42c2c01130f01c40840b02001040001000a0404210f00014142002c101c510034100141c2a10501415404c600c136200d00405a2411618074499800400d00a110300148100e815150b0640000d02c142e00090903645001c921405120003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 771485377 1250 771484127 771484159
    0x91208060307030303090819050a020c090606030a0b040e1e06011502030304171c06080d2a06090807140709020a0e04051e01141e0a06142106 62
    0x18140a59000d40d16030422041000802d1298000000207030081c80c019185c2002d42100408801c0501100c00100c1e4001c0f8050480300d4040c030410b01c2e603c106491a8500d0314207400001e800c0d2000800c4c0001c070a50f5103018030425219030340410200c041d143e044aa01105803680c0c001803d005030403418051080d01e0011416244501000c1c400f2250743d00114290380381c0e5034515109a03055220000700040c02c0c0b0600d94207011707041c000103030400355000003e04181055402800c020041071070006000c4050001d4041c000080c0c0304280310740000d01014442051481c01d440504020361001d0500c49010401806019241ea0800f4603190194126000355584180003810b900982c0b0f00309012138116800000750f41010340016610006480d400403089402203407010001c03000380c00041c001c2e0302c03080030740b2842d0522880300d03004404446040030f400580c0000244c845100c5005001c1003280d0950000750602c010801d40b20007900d503008103c9900300381400d81c1e000745001c07078095100301d07600b12050141c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 771486627 1250 771485377 771485387
    0x40b01091a09060f120619050601020609151017030901020705090c0a030b011407031706060405330403030e090a05042303040b0d050a060504020901210f050a0912 71
    0x550003030002c003034a03941d000401401021211074990805850255100e0761a018481036100d2400407005155000c00710b80700608681005107020b06540c41001840103402001903104000f450b08080b002496940c445c02020f81e01c0c0603884041c90303005510313070b6104003a0003101a11400341b003a42241c002680d518100498050300b0390301e41d0080081080803210710740c03290700240d818000606005510b80600d0b120160194012103065000800f21648000e0910f6a62600d50304404111201c1d0700302401c000c0041c600e0307891400040b440341012412860b0300c1d00034a90001145070707080301e0940c41d944d4a0402510b514417078508144110100c800181c001506841994003071034021b909500e00030788132003855900b42e4000014003d5440144000120b03d1036000043c10003116401001c905405c00c94150310070b40d0880d0300011b101740e00500c06282545d03841240680c501c1c503017410a61031441c1c10203060340100803414180003505d003030404116200106402240ca05485140d104424a1643d481128 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 771487877 1250 771486627 771486671
    0xe0606030d08040b04030219031805061e1e0406020303070f0503100b0304030c02040507030b1f02061306060b040b0703110a050d1d040501120b0a06050303071401020c0105040b0109 79
    0x441c4151000c200413038410341080d0760181c480c0c011500c034030750b00c1034001000e212051303022000a040c00070005a0320f96120380050040034265a660308003110390540110f0701c08007043c509a03e64003c80c43c18880050b06001c5684a4001da40c01c80d5983d441d11402926540304440d4040401c0741c80c0c9800d801140708034210381c032903410f50f0206809181810f0901200c2d510207023082e400c00440c440208056174403886000d00a841549000842c65840400d110800e83c842c44040300d040c9882c50441042ca0300443c0c91544502080154084a0b10b585404001410036410549920348040b13000324481001c0f000070151140640ca0711051200025005030b136403501898010110f400c803c00d607a5102e4060302401122000c45910181d508041c240031800711002640b00f08101c007075031a03034501031109400c0700940100804000b4440c090424000c070707649105d442c0005050b0312404a14514004003076055450141c0600f000340014101410854140b035000c1c02006502482c003141d85102c1101516402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 771489127 1250 771487877 771487903
    0x9070305040b010f2301021509101103040f0b07050c0d03050a0f0c0c020f1c080a0e062146090f0204020c150f10060c0221100c030e060603 61
    0x56218540096640c101d00043c801e103042d8482d000c01e40018423251354070306e407260680c140140780c0b01042e07516030003e55150044001d1820380800a000128a0303009106d41699040455451942c95146040300c4034440c003c0c007906c150152a01c03050215905810050160f20381540a000414506098008071140c002065020900351407a0300c0041c01c100300c210356951f2005100f178401c40c1642900309803440510000302c807884000542c03007213600e800000c0008c4000090780d6680c2006e0302800d940c4115402c4a1107601c1c2c640c9507000007012100707a60030800d26045400705c2c6e0100740040e08040c00c4600c01d020225019040e446605a165080a00c00c0b0144c01c3e4004034281a811070342e40900009512000c0b48583d98016a2010002c90b060f050f9842d004582e220ba440c8030914103005d42c01242d481d543c00900401c04070070019800750b540e01022207044400003d034401c440307070406006403401800340d80180e0b60368144840517a166403d0381c84603000d280d5603401d0b12001c0e40c0301410141c0301e803007040d00a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 771490377 1250 771489127 771489149
    0x405150c0d0b0a0b161a090d0509042307022e050a06080a030203070b010503030f040506030712060b04080f0c09070c06090803010f3f03020c09070305040b010f 70
    0x28400440c2d0007059a0800103440b19010300d0711522820501c0d0320000c12080e25040194856003000005101c0d052062480c080a0410f828296981d035100c3c8451390b122008c001010400e01420742da507038409000042402216079160245601004209002700c031000e0160103111780d0300310042c0005400001c0701c04401031200b500860807200300010300002d825414095074564004ca4020303030811805003124020703001107440b14075528000300300940581040e802a0820710107504031101c0740c4142c40c203589040307817510388940d106007048604003400301d0400c2409081980010b080301200d0300030070a5841800c242e075061140301c1c0a280d074900e8403d0350980c11650450015205130b22500b050003265100303c02c0400d07a0030441d04d6060454000b81c010001e01c00186c0801c2048203900c22802410400c000c1464158107652161820541c100d07503000401c1a030850a04010544244080c64030700c1070040c07403100c4505201d60028006e20084030101c80e6107150b0300001c942200c1e000300d44401c480301d40b501 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 771491627 1250 771490377 771490387
    0xe12030406031104030c1d01090902030c060a0c05120301300803070519020706030c030c09030809030c060d0209040b01110a060f020415030f0c050f090d0f0206120405150c 75
    0x3100102051682035920380f40c24800480002c4103040403400410507945040c10041a90103641e496540c103900c02046a46804071420041c4c501080d148860384084400b10380b5080c4485003500c00c031426103402480d5004602d021401000020003031410380312032001c0500c40d0802400d099850081c511541201140e626680000048403040203644c0049585407040c10040d0f500c00380782ea0b0074808100d81001d6001900140110f550611031030b03400d04058541031120816450020741004010700002c1c0400100140314012900d04004100e406900580050355820304c1030301181c025004401100d103d80c0c1400c8145000c1d40c445e5400c540004e40c0c0e80d001c2d000380001030707984000074045005005081c603028000000d12500040c01640c012000352030100b0200103240c440011182100070001c1070103820f1012051480044c001d8442d141d50596022011301098140500b0300e1841c0c20009501110002d0140310880d19040d50724090751250702110a0b0700202d000002c010b100c21148403500e00e0301404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 771492877 1250 771491627 771491639
    0x90501110c040908070503191205070e010309051608100e0a05070b1c050414060a050720070f061d04061404090f0b0a140604060302014a010e120304 65
    0x4001007030f140c49540c0251401300b1a41d01d003070841d000207807101c40e03000c0e1085041000f40d4202c031860881c2007a44504210034600000d0280002c00340891060400da030b40d0724854100141013200d600c00080c07400c0d001c0240c0b9600c501240d030f10b5850180f440f41a5041458003480c2180010303904076010303800070240c80d0b0a0b0500700180410307040800a0303007484109101c040c041c682d035032045030f0142e4090b00003800e01c0042400d8140c0380c4000a0400112a807900040200e810307400142c11500900311003050460f200c0701c000c1c0500d008a550081105001a81000500760b60089040c64400766201c900103c0a001c45080204031101486081c5d01d03110b070003403228894907146d84020303962441004d00107070325440381d1991808240c0440e051800d66a4400e0800007002040c5e403003d030f2003102102d06010705401c582c0000c115144150308060240010128900c04031240382d400d280d01c3c0701200403c203500e06903101c0000241080000c440c042404c8031262030b03442c2441000c461207024503400461034a0b180070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 771494127 1250 771492877 771492881
    0x608060f04060615080a0515031905071e15091202040906020d0c050c0712110405100905070c020a06020a02091b041809020f180412091d0403090501110c04 68
    0x14000c64602d40d40f4030300072420005890240c003034a0103a50310b0f451540703080080d200c1204c074050410000070100c2c00c50840340b80d03400109003030062008172a04003c01028a8981c0c64120140c2003003079045211680c00d515410030240003001c451138404080b085c2c0601210940300c118080c040c140041c0340840780e2401600705504100d0300b6500c510001840e102c1c01010300390403150b4a40b4181e000800000d11220401420082c800c05820301138400e0100700d000d90354940f1015845200d1a0007103440300c002607810449840490001c2021303035400d00c20381c0b40400000f405240c0d0400202c1c490314078240082001031000031079030740907907014000c8041da4850569695042c01c000b1121280326074204000f05000200410200800000d004086246002c82c410271900d400e0140c02c03c1c0c0905600000720351701d82072400c009908183c01c00040b654029004504035031002e040d40040490a008048041c040200750007803901c9a402680c906600300d8a4900442d081c180124006010b075104044025052070301e9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 771495377 1250 771494127 771494131
    0xf02030d1e0c0f0204020d06170c18060420090a09180f05031c02070b071b0803070c0b040b190608071809021818030a121e020c1b040608060f 62
    0x10543c0041d240031550008042c1e90100340c0c0018a55140c020030045080125544200e54071240040d0201c41526800720303407990b20000c09000f824411780c1c0410030320b896681c40660743c1d1900070201000152a000a04c2107503101e00306c094042c5031100b200060003001032003111000240951080b580c80082d4403200c0a1903064101641c0368042004046103800c0013504004c105140c00c4400740e01d81c08541480706042000620103030912008418a42038600c400151040181e8000340310344d03e948410070700b12014061598000c12104441060000b4403030030044403482070394843c0351002d141905e5081c3e2002e80301e003441841e003a540419400c4c06003240c4214814040c03034400700e002070600c40c5a000104820359007c2c4107a41c209501050042c1d000b400d030036026640c00326100a52030b2612480d002080485038030041c40205654040c42c039150020412405101c1d80503a900359100d484240341c0b25102d01d01e5100503e10481110020800c07420203009110449203084043c203865610007007050524080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 771496627 1250 771495377 771495383
    0x301061d030708060a0903020c062a0106030f0b090d0c330615020609150103061107020409061a030a08040311010c0501090b15011706060a020307020a030f02030d1e0c 73
    0x2032034102103500f0b101082034510a501005010032181c0281c100a07043c40c84601e81940030b25000c00c001460813414410341808000302402e80406a035296580340d00501c3c90b034200604690594081e4028010b5000c034090084070b4410680d0110340d46018192848030300400d0042072107400040152a042c1d0b11908021030003e542040c0c8940800c2c02d9144040315060341104043d424110150750303900d60f04001075a8070072440d000400709046c0410204800c1c00c0140b0006001544070360481d94801c0c6800141e0707002c1076020b04180180e00242c6040c03400f03019900071103885503e1201400a00780703400152801c9060300406850710701800c41d10340410a40b40544901c1c18008016040da0000318240300b04600319000305140b5801d4107021059082c03030003844040740d04010388040c48403c0301800c2c1d49099001f10342190320b0b958600388010140c4c00c6004015002c0d41c081c404000c00001e00405007400828180300301c060750307604420208203640213036002e107820840340b50300304404510a000e0400a0340c0140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 771497877 1250 771496627 771496633
    0x918091c0512010807032901051c0f14060601050a2a020d08030a05060d1509020f0a0b0409060503032d19051305010e060d090f06090c0e0702030301061d03 68
    0xd0400c0010410b102030388901c820741c0c010182081130040d03580d2400e1560300c6001460808040000c0001011501802585c0c410303c0b8000c01c01c40103410412080e43c0c1d5650144015020320000e04110b011240c00c0d1040f4000d03400f9410024078950f101c0d01c2103d03825060794580c5180c0611003039001ca603160055080210031814140d0034005070f520b0042100340c651040d4645036480c41c0400c2910182c0c0c5000e044c882c0250039a1050b980003600f49410819070690320400014a11041e0002031805059488030907084612a507000c68001c9001d002403082e111f1509050101558070b074103255881c89103091206140b01400c0c801c0304c1d914044443e00918228040c26181406540605407070000c2e40e082103140800d41c0082d01d03a80320001460a08010403003400c0003a08040d4000103d41d4903c0b80861070071420b50340d4a0860100120780d42c0842c0358540241040103c0910307807130302c2071200c603041c046d040c02220000001410a80f0000032213051b54a1a0b8a8004080140d40750458051f09081d030303154540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 771499127 1250 771497877 771497887
    0x3101b030e0a1e05010e06070c0213060b0309010e060c1e2b050f06010809030d0c09080307050a0b01140f040b0324010617012105070b0706020918091c05 67
    0x81c031540000582452181450f09034030341c040c540182110403c003100b01d616002881048101c5400410100640d50150740070700e00c0c001208050001840150004401c445004c8140f01c0c401a0542c480e04041c41c0ba1000c41d0029202c01c4080c501c24007032503003d8031050481d24000510010414050212001240c40d20849161031003441107104e081c00701061419546c410400880150f00301442d504403000782090800790408045c0c4c0c44d101d01c03840488001d000d45a4041c04115441021444001c2c1942800d4036198040d41c5030150725050619000d80340780320a18004100007a818080d0100341310b006120061044c43d10090002030514104420382c5030140702401c0c8810356141d07050495000d9514901c1c09590f04015000d00150bc640c0c2c40e00d406150403000500c004d042401c10b11030128411341c54031500c40350b00d1908620301080394008a01c0c411010418100b04503194002d024102012146c040036280030102000c1c451904461400c4150300140b00c1c10500ba01050b001440c401052800c28500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 771500377 1250 771499127 771499133
    0x4050f011704110f01031b030203070c0f120806060313020f040b060d06050109140d02151c06050f0607030e090a02090a14032811010306031401090203101b030e0a 71
    0x180750100d42c01c2d140e0400c481c60035141031070100000541c0d54000d080c20801810b6000d01c01801c0001c5001881c281030380000807600641c0110b07007840e040750f8804900007140e00d040c0f4023042c18624011180c8041a40800411030b18588523060302d101c3c14500c140c0940804082e000c2050b002c4140c2c8846802c1a40c9000420041e140c1034020680d41440302c4000c1062403410000409011581e40b2151002e00f2020321040d0703658402c4001481c0c039404842c0035182d48041114403089101f0815014092000801003244500c01500710508a900c2103505016202c0c1ea102402814400c0c020000d00141c058148420b0500c0c06502c119040901c407003005003040c508501140360140c4580100603207000783c1c3e03511042450204816002240307a0105003100c80100380c400b100f00808010028880070214588111036446903016900640d00701d0003150200307034400710f101d000340f444001c1607000740101c2100520008250145000801450707a05030b1245103225012001080c59508646e8180507000103d004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 771501627 1250 771500377 771500417
    0x4120905100e12070f031728020705010c032a120504080c0d0f02011412042117270d020717150406050a0228031a0604050f01 55
    0x41c40d40d00d4980c40340203002d20041042c44842c41c00040b0465101c00d0080c0720442030311148030304481d0b0240481d0141d9054690032849030191202c569000841303500c0d0004404481e0240a0f51036006801f640c180c56151001143e0040c850030020340440e103a1040192448181c40c1a446080211100d03841009800e9550a0512203620740c410700103600454280100c030b8060000d44101101140c02d10040d210b103a403000c0e82c0741c2074000003038140880c4003240d2404121300c4081740c03026a01d90741c000d1506e141918205029003038604d0360300303070144820fa402d01c292802070401c4d0b2001c162072015541103a071034a00241115141d039500b9881141270070040c459032401000008080281900a0000c07241042284940300440340900c9132140e018280901101003664241038029810080206d2195203212450700a4400e9610140b080d0fa0700c80d005011041000da200041c902c150350381484400c001d0003441d001900b03c1c601d00c80e03101500b080300300031626104000b4a1805010b041c201520045000782e100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 771502877 1250 771501627 771501649
    0x17030901090f210206040507060f02030d1503030807080624070206040b040618060c060c050c060a0b010f09050102060f07020f030a03020306130c020a0209180f1005150904120905 78
    0x5030950030000c2420f02004034a00201a0409070303c01819186407540b941c0ea518003041c410041444007019101604510920840341c07104c00340300c4140a0190744220500307056070144000e8002454000111f41d10030700c180846806090020420324002c407130b46a101c0b041c5021a00d204140c900f04004000068541c90b018200a21804141a0716246840c1024014a448040600720824003d01c04e002c00c9800141c008040350308104001208241d0250554883c8504100030307005100301d400704980080650000e004400080c0d80b03509140c0c0c0243c4058409000c24050140540c0241c8000f40807050050301142d8000402c0c811500388080154069007160f02c64203000300040c1c0c000040004034100780bc01645015003070042041145505c00e0000e4490500c808001e101d4401c0c1d001240d40302c10020120303102c001c140016168491041241141d41d40001c0c035814281da03080000141c1203c0c400000c2c1d0300c1c100d201511004a0741c1e11603840304089550a6259001d00c07a80210105a60700c5a000300e131 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 771504127 1250 771502877 771502883
    0x50d0f02030f0601050901060e040605060d0207020103060b0c0307110f180103120c03210e120703081311011809230f0105010e040f021207080609100317030901090f 72
    0x5011495a00505050482c41038800c03800c1c0d0300c1040100a180c40e00d040e028111400ca1800d15007804841d40040c000d425035511180c0d0140010a004405420960041c1191071007602c0030090fa41e9034860b001d00c9801804d001e002250000d00c01c45000ca94080403000c042c02c40109030004003404140000d0301039004048904001e00e501e0014010007030418020f041d105005d08000b040d015455800a100c203030101d6854201100701c01c04034010311804e8103c0200080c200090360003420b14104201c9003a049080700780c00168645011401d500c8001500c1421680c110340003003054240d050054405d150401040c3c1291100d81a00080510381441954605070303100e00e1841c042010401c6000c044040600031b240d00008450040140d40e070804017140001070152004580b02d142c2c03030881402070107103809143c6509c02000802c14203a90101200d8400d00b02101e030884141c440002c04071484005020060400240390100319941c24840081e5607c82c00c0c3c2000030480740c140307a07034225150180480407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 771505377 1250 771504127 771504143
    0xa06180c1b1407060302070503030420040603120e041a060a1b060614270c040308180102120301030f0303050a0b0310050601030614010e0d030e090108030a0f051804050a0204050d 78
    0xb086220060068000505192030250704000c0700d600c07290b07105d100c00380c0000c0594111003121582414014402091000300070006c015556490500031054401802c64000003403803410705062901d040d00c2000041510407108407618407640c01030100591140d040300090140315091501c107480b04100c0e80c4442845810f0114940c0e01e030031224040c3e905405c1c10716225030544000c21890b081a68040003c08403031203003c48072500d5001d02461944140c0c1c002034001d0000103034501c6690711520165191400c02c0c0e003140d960880c07152505002d80000c0c080280344402855070380001c03d100e500119009541c0704000922500f003140003a181040121401d02581c0e110010010700e9070701441050300503c1040f610b1000880e14000090101189118543c402c00c05803102006140c46620180300c268005400e40c0b8027540c48503081685ea0300603100c0703500000c0301c480c40c00c80010302c5081038034201c1c44401e00000c0c0740d8601d9400c0202801000f40603a02c200d502b48400201b994880021007201da00032785403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 771506627 1250 771505377 771505403
    0x12020c0307051c030b0402031302090721051e01060504060c0503040906090b19060e012d09230a03060c020a060203070513080c06070b040f05030406030f050a06180c1b 73
    0xc090300359103005020500c01c920610420903a00c090b4020180e4843c0c0c1100c1100056a0300d83c41901c640c01303c0d140c07201c000d04052800c049001010341c4414002c601c1030078044985403000090f200a0fc0c02409541d00190007403100300b0056015500d800c0410b413164059130304094442100c14215070036984400c0301d10b51601034114060a00049510400b44101d902503900344c10001c02a02c1c031811400e8490404c1240d0440c6100022030344104e03601325000f130003508070a80c10340e03000038401e800c0d9000c1d08022201c1c3e207946107508801d60440f480e0305180509a14409440c585032240101241c2102d00c00f94069440001c0000d44039100561055140e519031603180d00c01c141c0c02910241c40c0b46c03c00c0306c5590084038080c4580e5034007402d6580680d40b001c040381031544c0f6482c0c010079450464000034001d110201c0c000c0307035a91701900201092150382c0320800160350b60100724015601144a00340c41341021803c0580942665040f202100e60b841c2014800d20409940c4101c083c0c0c013020069072400c0c5150a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 771507877 1250 771506627 771506683
    0x507031506170c01020c130b03012307020601030c06110f060c0c07060305061503041a070f08070c3903060603050106291308031c15030312020c030705 66
    0x41246561440c2c04010a40320b158100080d5490761300064031880703260303411302c0000095196000f90305d00030030180c000e2209407078400d48201d040380c0d083c0c19245406030300400983c01502c0014118103c80d00f062580c00030619114040d50346282c04070880c09540a00f81d1125203018081001c54003c401c17200115580341e551189490034103200360409420107051600f4410559aa2203030302d00c0c00c401411a40ea41c03505c407407900c032480515107904042885410f1b010424801d030440f403c41c1c0245455100c21126988030242225913000303212004011044003011506101111080101d0024403003928000328102e00d401c03004081ca10b40e104445258561300d060040080a008000c0100300e00180b03207400c0c101034a4800030100d96030182619030280800c2d243c0c0d00028043c4110028861101a2552204c0c200039603050700c8100c1401e0741000b420442242c401c0d04040c1410000c4035056500d2800e4a4000c24281c0040d5001e140c85414904c028844800400c00510400b0070080c8260012502d91002030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 771509127 1250 771507877 771507899
    0x33080606060408030f0a110a050105060108010e060d0318050a03050307021e011b0f0c0e18030903101a1f020706050a0e01030b030a0827040c0e0d0507031506 69
    0x4004034012041400708010f502c00000644a5400802c070040d0344641514000305c0d14046142600500c0c1d205d000310310b00900070706512280c043d800a0783c40d100c2907a2984140401c10b20b003620343d260000a80300030030340401e21940704d1801107503816480c181e019594034001034150410350016161900006404011480c0000f081407603030411003c01c0380100d580b100044c05050070746403c656048034003d43d140070171040010400320a54440c01e507000342030321070300ca104617204216040354410701d00d038201452000c800002d54007003030340040c000d02c080d00c100d0028001414015072003640c03a0f18840a070b011f1135035071180c41e01410300c03005117441c2c584003a8040003464410164041428400d041005081d004d40c004d07184011805d01b8200030400300d146c900480c2ca4030f81070b0b060240c602c0c0030104d22404501d010445038045040c1c03080701e14106242c440100812601003113001408113a18001030851070812814414460380101c0070748506564035240e00f00c22010700818603044940e128402d000364101c0c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 771510377 1250 771509127 771509131
    0x9030e091b0a090e1e040209090a061d010e0615060d060503030a2604110111030d060b21060a0e270d030c050702240c0106090207030e22330806 63
    0x42d00c030400c0001c0171240100100000504041c3c0201000d41c0054610141000303a00c5603c0d034040410048104da04145c0f140040c592803102880d0350070581401d0388008005842400390410707002201d9400c1000c010048594448401c04060b56200c140010703551f60244050224010603444130f640040c500040743e100c0c0c4a1070b40e0480c855540d0310040c800441d05601c07094030405400e0a0441e25654110b8a55186000e1701e072a15030658107120300441c00010782000b900c0345a900c855400c1d9040e11003035800268031004c9486e6508010864410415110088150350300602c645611080c103050f68000300400c040351581d0f85102d80e120054100b10b00c2c0d814400d1480151240c600f44d82040701c65400222001c03240c3c048484500301072120540303481c820304200c030300d691999402005000d60b58013030400650444102079000c034a11000707540046c2401c15002e00244e541062100f00c407040042070350010403900340070800100d04c102d480300d90310a40c0d903100095a10714901c45680b00749803542240c07500f400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 771511627 1250 771510377 771510391
    0x70f030801051002030405041526060c0f070609020d15230402031f15170c04020a09030f0503071421090a09051321110109030e091b0a090e 61
    0x1c41c40c180d0f001d81c08010f440c25100101c1c1c001c101600d02c0304108407010202d800c420070508142c43d040c210024850034146d440c41c2c0a03825265942e403840760303064407409031004407944130008001500c0010041d44c4a1254984000d03c28101e030101d0380c84480046d5a65200c08948a5640003040e40d20311000c84507400c1c14036000c10360003451401c0d80c0400d44a24003081e8041500803a0060030160075030640040400e800c410340c0388100181c0d9074519803403c0e003408296013410b0140807100011401c16008032450f003e00750702c80c0c5440d80d20319615000011402141950507000501c0980f0008441c103203103003401c0002000400300705503509000105005850114226036004224406103600c5d9271800c01d0489600e60400105940c420204100d007039032492009000585500c49010f61840c000c1b80e4044000c400d6480b83d4201600c000380744c1c22902103510160100f06809031600c594039019400c26803040e550204041c040200300e43c00d0380c1d95080343c603400b008640303621400e01841d40d00308442984010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 771512877 1250 771511627 771511639
    0xc030324060d0513050f1501171c03020c03031503010f0b0a120201090305010c1806050702061905071b141f051e070c050111010e1506040e03070f03080105 68
    0xe0080002809440340c0c0c040204100c1d222400100484404881c21107429080b0b4242da008009003030380c06496003014a210390614104000114400c0c2494001950030907102e0010006441600194907441401c06d488404068081041c4222503006002450281048010032001c40e1080c42c201030a59a90180b00b01c0424a801d00a6115648600042080300d054031160340c0e241c103090004a40030009900081c01540c00c014103944010381c820243c454038401100c41081c21519190b084800b441351150107940060140304480e90341642510940140d180b0f801c00307529050082d541e60800c03000b03031000078042e81d0041c0002c0000c0e0303d20300d0b8811800c000c2110389440004206044401044904810104109000c5030208660034100e82c1c2d221a084540640307502d0380d6692514000d01c0e1750b18083c150003c1c0c520380c030215115205005010007207440c20050a00b1006009a00c2403074880108120ba00c01c1c1c45503200701e14100103200900340c15019080950401c0042c0c200601010390681c4214041c035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 771514127 1250 771512877 771512941
    0x30a0c0303180b0309100b0109050910050406060503040f0b180604051f02130315060b0c01050a110a0206040308150409030e09090a0309061d121b040b01021b0a09020c0303 75
    0x880200d1075083c0c2000e50f020008580303000c0d60040b82c3c009c00e02d8002c10781000c461001c1c0b25100c182007004004461045805202082d15840d048030103000903070307005059160049005d4001840b03010794661000d00c28191030145845040c00c030345009019102503030f25403c03940040d100440019142100000e4600c4154507280020503070803110621840041c2c0004010400703051125440e80110380280141c04149841d40a9103025600914081d603194408a15107819007182102050548419071401d401411550f030f140d03181030382c10400042514200b04151840d8606950f950300c60b01d4251800303640d5100f600781c7d40350144001e002005e010445154405000640082c2d4420019001e8402c03038900944001031305941d20030130f600e680c01019400301d056180840c03413000000e10b078036201c50401404c41e0040200c3c001d2100729201090401c1c01a00230002660324140d501140c3c800c25503014000070280750f981d01c610800c0b6000700401c18925040007090181c41c0c0d104013822100b1545842000c0410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 771515377 1250 771514127 771514141
    0xd0311010b091504051905100f050102010b060904020724091e0b04121211090f0a1514090307080c01080f070801060e010215010806011706061e030a0c0303180b03 71
    0x404aa0792030240f180d41c4071400a46039540744521b44204041e092402d000c1400d010985454000c1d9502880302511059800081c00391303c14090750740809405444280f52054000034440a035000301000d440941481d0000b000182c5041d200d00040c000d40d00c4002503c034007501e40b10800c4000c41c1e9070070711611080b0b0b00400c0070880301d403e65508a58048499005401407480655018800d0401c1c0c04070546004103003131418210100400320960215009000d09405d001004400c070f842e809080c40000d420a003540c000c1c5c0c0074641b4814000b4600c0038083c10420355100003850003071150020225500400141101e65801000c0290030518460400f0003e10300010700a20000051040300c040005030805402c0c640d00034040c000d03015420701001949580c4400302999103040c00e01c0345080100d41000c0300221041c010501c036005100c02400f11f012031041c0c070fa02515a0281904499041c0a1480382d40300007088800c42e50000c41c440d032590704071000f03901c0389200e280005901c041d0600750100200191 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 771516627 1250 771515377 771515401
    0x6080c03100b011403010305060411220b03070f0b090405010614030f0c0d0c020c0a061b020d170c0c130b0d02210d120609060e0a0216020d0311010b09 66
    0x1607140003a034005048001c0b000101e525591130309101222070b00000020050080204500c0c1c400d602691480c4c62482002d402d000d02d0000105210229420716900c2c000d100c40250000c5034400c07030041c11140b5071619070350710048840180d40004c03022000058224400c0c1803601072035004102906120301030140c00d4500b6282ca100003065070381c4505058000400001c0c0c41d2060310702c855501007041021320710524000c3d60790700f044203165200d100d08600020311148280306840740d803160a401e5981c583c48660a020303001c02038580864540c0d41c0d08a607411011113410103807000ba01d9110052481507009000e001901420313048001076076040c042410240c0d2580100003c1c00c0d681503070042c50021510a0701d205540a90450509600844006000c0b86038803005012000441c41d0040014956a09401045036400c1c400c4003207030b0760304800145030400558050708219104401d40d070360b0b81625a0000e00c030040a0b02c03040300450174090b00e451050000b4440d0441c4a10241c0703c0d012a42400c100e0498 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 771517877 1250 771516627 771516643
    0x12090a03080702010201020721110c18150303072108060a060809161706010e3108120f16020c0d021804050f0d050f090f041b0504050406080c03 63
    0x400900001000720031139200354101d03038209402c01901c0148a038000b0074404c000c0d4220186800154207602ca1000f40c0c3c80c045007007010000010101c0605d12012146a211200010141020184020300701001a24244000d03c6428422021411000c114880d00708645490714140800c01c80348004010b0544c4401600d00140c84072800c206a03503541d4000510300d42003006407000a50802e41600056442141c030007011480488001e0701c00503a22280c0712001c10b0301c100c48074050200c460f07a10369a01015103103600c86850891100b880b030b01540fa01c0d1540140e00c10318001074006030303180410000000e180c900e039412412030340500c4042400d0100080d6100600c2608510a0b4000d080d400d0840d0f0301ca100428042c101e0704292801c915050a02589034203000b40c50120074001c464488000034802d8080b030b20b04084140c0c0007810605d00c0c00a20902c0f00c03142c140f59400a41e11800c001a8550800a24001c8240d5503501a640c0c1e08090900041d40c0c1c46a20884041c0d11049c0d8100c1141c1d000305000d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 771519127 1250 771517877 771517883
    0x1031508031308010e2e0e03090a090e1c020304090e1b0f03070612090221011d0d0813081207030c02030909040f06090c03050d0e0108010b220b0d090512090a03 70
    0x106c00154010005c00d4039105001100f00c6181c03401280200402000c009007003810001c655901d03405076100c441900340c40c1c0305c80e40f2601d20740103810f07103450741200c0e10126900c4000303030f00c11203082984800e00c0c00226030205e001100c0d03580c4a104142403080c20744400001c001e000b41e4600844600680100e65a1203190103100140001149014150400d070351000d552181c0042c610341c1038083c0076240180112404440742c12950a0000f4481c008040500b41d07086c0016980c014010210070900c101e86445015051b40600e5003091209000303d12020090040b90b80242160310640c01c0c040c0028045a03120355100c0d0a641080c00086101d982d002c0c038440d071054010500175030302503143c94207200800c2025001800c0041a80e03002c0203001000a800c07206005030b0711450301015020b0010740703039864244181c0d188007204001148000e801d040081c12445102d0007050704c0135844604c56916600650b44102e1740070f40e16041d5030140503080107954005041c0c1032501346490f03561000704040340c907280005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 771520377 1250 771519127 771519163
    0x503010513052109041e05010b0f0301030b13060905060f0601090803180604030b0c040306050f13061805012f16120e060313050606030c1e01031508031308010e 70
    0x260140500c004451300941d00500c00c000079000d01415100098003d5504c401c5a440c1c0b60002c11014081e004840300304d401251039078110382c610784da07551540b03038000e00d403060144030700c95600001245402000c007607600c988050319140c903001d00d9814421400405590400c00c1e2800300b0004941c011080b2040043c070000741c102d15002007804180c0c14440c0381c0c0001c2030512400108210140410080c00540e48112000e004940f502d83c1440c03500c900550341d03501a40400600b140008016a03c031610949421407a4060b02ca0030340c58460131280d20300590703c5881d0310070700ca551803011005c3d000010b103d48400401d0a10301311b41a180ea8004a0307080040c14401708480c1e80038914000c5003514606800108807560b207150044880d0035107543c82600712818030450300420800e00d404070301a4010840a007404a0302e03110542d0307081994840002c2c41e818140d80305036408030b401e04841c1030360140c400500116520001031030100155086607100d5807169240141005610324042102c2c0c0c5148043c400d0313 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 771521627 1250 771520377 771520423
    0x9020102030903030403060c0207080c0f090a0e16060210061a0304051f0b0a0503062a0904050a0b01091505040506130b071203050106090308070818090a0501050301051305 75
    0x607490352095803901e43d410700c000718001040004542052042e113805500351210a640c5a041711f9860303900c02c403080d50121000921001900305180c3c4a0f07844030360002c0204100c40b5140f001da060020b0b400110802030710f04682030003840d804008440b9680310381c00003008a1442c20302c080780d8499950010f490300c0304002012509010040000c0b40c45071004003046600a5020300a117001848400c088038000c10340001d0004c2d85140c04030300f403849071150400603013842014403500c00c00303070000d505c1a03544903500307024000c01da4031a0301c501446014a40400909072007983c0000d0400314165200a440113500340141c10110303803000583e001c40d20207840c102d0310b07000307810018291000d40350009602880c02140020921401d18000001c541890701d040002ea42c851104440b644158000608030f44030030010300c40003506080052004101210390b800351082c40c040018a801c0083c1c901d07608884c0c4640041c03005242c01e104050f004001e0300c0201240d40c80c150366240c0c072205862041c81202c50700300b40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 771522877 1250 771521627 771521629
    0xf12030509100816110c04050702011503030c02040b03010203040510110702091e18070501050903162912160905030607030c180515071a010f0920030a0902 68
    0x58441c0464002d1200c0a03003400c0c104000e00042048552007001070807034000b218818003c1d82d1640b05064510007502d9594080703410300000d044013600d04030441d9a90070281a18042241950f009117201c1c3e91754440c1081c0300d00400042e40c209a55041c07280c1d01c10018480010b00000b84020901c00980c1c020401510007d0f00c1102d600030403201035000030003a01004076a00988036042c03010215110201034646644482808150500c61503495075403041c81c0510440d8080c07009454101c2c3c0c010125415408222a543c1c40c1e584580e02c00c0f4011800c1c03500c610400808503036902051060680301d030f403c102d0320314806010920003a00001d071a0307800010210540740b18080300c002506e0003800311286400d08113802002020460407110014402640c109083c0d00005070400460310300501800b0302c0408551014115488100c1c11031b8080b0402c242ca02501449000142c0248041100010308600d420000815101a081c1e58100d00705c034295071030116010304059070b800c22801c0d072001a5a1210f88 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 771524127 1250 771522877 771522887
    0x190807050c1b03190b0601180b0c0102070c090b030604060b03160b0310170a2a0308040f06170c0d110f0405040e07080303071206090e01090314040f1203 67
    0x204a040da6000b402040b1454444095070605001c40030340403142c8955060035011104c81c0d0340c1c100148101440e0000c950a0740c0700c0c00c1d5a00d4258100c040b605a8144d40301c01d07a50b069442403104490694000c00c1001c00c1c8089940541c0c001d0489010910136022000000790b21040003e00080003e90381e5020741406403410440016006041481400d4803521a08400300346e4200b10703035040c40084110300c080f0b04c1811200c10701a40310320400061120424596540603500b03050511104119404003c1041d82d04a14010000450045400c181d031141086014007180441307800542c1405260101402c0461b9a502110780c040402c80000740ca803006030000380041c0ca07803650b060b11409404902c03080b14002e044014012610110307003c01280e41600d0742d05031102c0c404d204010041d0002d0002a0181e4003a030a4107800c14100d00780003460b5500c0d48440821038841c051000d1050395250030100805400880301482619440510341c2041d00e040382403440c203181c900400d0001e001032280c40702018011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 771525377 1250 771524127 771524137
    0x61810150e0406091403040503072309100e16050304031110020403030513121502091c080318031303110d02040203190501050607111e131406040219080705 68
    0x24001e5040740d81064103124001c1d08000005075044421030300e024451400000441d000c940f00a80603001061a00c0407005c0d03030b4040c0362034281803002a00c60032840707969452402e07480f450b1880d0000d00c03210b082240150359104014039500300501c01c5007014000c5c54001d0b09a0b80d0190381031601034001a0340481180c106104200118003450001c14044105134010001c0c01d2071049101b0303144c0e07080d0764401d140d80390155200b0015100300300010815640004e6074005101074035024160602039007005110101d10b050400d4140c0300042c002c0140240100040c1c480310156407040015420710410fa81102031072101c0c0d1000824021544000f003000380c43d644161500d10750000c10442d12407030074241c0508401c228113000b0032200d00d02800480d82340752134401d451110390408204a05c0003481001e1103084410780000c40180342d1044061b00c41c0d070741c41c4141c01d00391480740031000c100707007081e01083da002920251020340b18500510404804d00a0240c0c00c0302c4100d100e250030340d015100d03503a09803414420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 771526627 1250 771525377 771525389
    0x30c050f04060801050a0b0f0a050f1306050310020318160504020d06050d030f0f2307030309171908011505090105040801020f030f0612060f06012d0206181015 70
    0xc5c00c00b0000c200d402644003035501c3c94180e8a000d803c1c82400b04104076603080c1e004580d403110b029103903041d0300d0030000000144008082e5000801a07101e6000900c1c1001c0380c1140404190000f0420852010481c81e9003c1032581c2d40080180001003101011502c0c0d641c020b20380103e5001ca00f20586040c0c039086000103000c0645282c0002030141002030050103450700c4040070498440d041c0e024144180e48404810901412036480b503074001c8019030440e480418281d08041d1a0241400410840e08004c407901107601c28041d074a000b12010054602642507000342800380c03d034010804051172151600028134140b800350782d81c10b1083c0041e43c0d1030240f0b81101006610105441c001900329a00441c00b4180c4074403031500903501d0350100a41d41c0c1842d14145040c0c1c0000300459105d6100850241e003202050500d0030141100081045203100203400203600f40031400004070900b43c0621900d5044213188030106641407401c4819641c03482045c421854040d501c18841200590301c01c4e040000d044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 771527877 1250 771526627 771526631
    0xc0a0204060b04260307020411090405070305190c0203030a020c070b031609050d080a230f03060901080a0302060403143105101403100b03091c0504030c050f04060801 73
    0x34030741148030b0090b0814007400c0c0304156010a8031201001240480c2400b80a240055203043c4199081c080501080e010990b1560300911068543e503031035000b41d83c8645210f6500241074940007041480d01c40c00e5403045100c0c1481e1000c44281c0d42da010007101e41c840454000584d41d0f0608031200c07407030015141c0c0f1103000644088240000c2c40c000300500303400303086543e85c1c842c24280c0b14001c05c00d191002c51402000e0800410081c03086078040d0b2940303c0b139000302d446d218944184501c0004c11692001201c011081400002c10130ba80ca44412007501428085000b0f00d105002660b010350b40300d10182015045c80540700c4102d14802c1280125031555a0f0f41c110084170703010181e01140301e8889a01059684082020041107034104009503000e034900c25a202e441781920000c0680290748007500035244c101d030818001c40c411214000a6001e040e48000038035035400020022070605035a41000020803208000801c0403030282208038054510807a030f80b1074203400001c00a001402240d00c1141e81d94 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 771529127 1250 771527877 771527879
    0x14010903020f060a05061c0302070503100e0601090507091e0b0a0305012103080c13081516090311090601020316030806030c01020619020c0a0b040f03121404080c0a020406 75
    0x360340401e282075064039880440b01580c5a402d001d9090310b02c00c0307400f00e410a002c105c0d0350072030b4a82c41e60401c00342d9001e4015644540e0b12000828144482400850a802c0c0c4401c40f078008075034204807150062207002001c000c2c034101410000d080101911840c03d102407a074005241140000010100404180d000c480d41c1e034810100c054040c200910801900e48817642a140344850b40c2c00171071480c1a0b159454440a59608034214550342083d00c01e18031044504c9800300c1e10748000c01c03140da003c41c49108100302c5490310420306110003404a107403100b00071a40f4800c100182491200e803120324801c0768010310039030354400100e1a40c015604c0c1400041c0301c1c0f6200009054004220900407032042d0300340c4a022041c1b200581c0d07038500c1507801d1079489408071501c80c1010040e5014044190070340d02903c241d1082501c80401c4900d01307482c1591035080d00340c001401c05411211244001c6401c00703003401024450704030300c048650300a0024020b81d034002013200038460140031240fa96980180708028903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 771530377 1250 771529127 771529133
    0x4030c171c050c03040b07180f09050a0e213405010b100905190e0702030406080109061d041115030a1401120809012a1218030609140109 60
    0x107140645141954540b03000301007400103100400f1288a06d82203180e449480e124041d003120303000d80e9585428400c03e0300000100d6140a1241c2890040c100f00802007098140b1714854012a80c44c143c500b21b160740f100c451901502092072000d250b032404801502e844a41c0c180005000ca40a2000858220264a840320407000448425152140960300803c266141ca500384060008003c4514002c5001e8450401c00c3d458801a0074109102a400804c0c1041c0d0700d0000c0d50704010162845805600049414480c1c242d00041260050910207000d025079071621100c0c0310b0312030200f41e07045e1940b105000060180408a01030b62846100545680c4c12042c6058500f002c6400039a4080310f16400c05624480c44404160420305a070807041c40d003000101e003a80c031154a5844080564144607102d003840d025034502c51020040c403000134010507a9058640303402d90a00041e0040304e401e11040c2540304406d030b1603050b840c5064a901c8803001506c05014104010200c0d138407008030050358213201d401010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 771531627 1250 771530377 771530407
    0xa23060c01140903090d06180203120a020f0703082a07092316110a021305070e0d03090b0903010917042102030c060d0f0507080916050904030c17 64
    0x3048004908048583d00c440b005941c0764842c41d00001e9026030408080800703d5a190f100041d4000000a42e4201141ca80e000c40e081c03100b40c2040c6100c00740042954034140d0740500203203d50b010000c1c05001d40703030f085035170b0b01c46240a54003500d0111003160500950000480354562422070801d4200c2e281c650390f805d2404060f020442504110b0f2041c2d55a41549480c0d11034954094103a21681c818104c07000da030104d8040c942c146440c40d040c425105228003680b140100380c004410151400304e5a89080c0c4006818200042111401400c44840c10380109501505c070f03000341e496080406a41e845507400103800741c0141032001e0100310001c18a00c1100f80c21000034011101010f0354800001401e5141c0e18500300040c1d00a900354004050002c0b440c0340c828002d00d10705042a400203031110090030b000341154000c945410105040d00e00380300e400c1000300505601200d880503024165030414000c1414072801030001814411110b11a9042144032240e8140326100c071034966489078040c03000b040d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 771532877 1250 771531627 771531641
    0x515010b0408120f180112020f04031e1505130501020c010f051b040b0a0c0b0a090501050c160803040303021905070c05060324240c0606010206060a23060c01 69
    0x1544201d200c040050501e81d02512131892203071011a0420400205d00346030109000c0c82d00d410800300b210761840c084090310142100303000b50241c182e140c0303045140c0710202c400b5405800130080c040001540020711804100b0806a450540208441d210f090f414005071981e107100a007a0350022a850022100542c0040d5900403c0d00040c40203498901c07080c01445c2801c124100c4104042006101c5802c18000412100880d8074083e02412955201e000c142a42555041d00007520303030140409001c001d005080e0041c5200c001a0300e0414104030b0070120500e82c0200610405d00030000609050180d41a69010b071008020242200240c6030001d0141c1c0c44820100e03004100f917100416641003d6050343e208103400c40190700f02e210074a5218a01c8045150011b0b4422110041c5850200c00d00d28200415240b55203560348440804400d5424a14002c0c4032074119884141080700680da100301c0c002c21188032580c0c100b0031001c0d08403070500f5242e6a500d01d581090380010494581c000541c4011 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 771534127 1250 771532877 771532889
    0x4020a050a060824040c050a02060106031116051501120507080714190b0a0f0e04090b070807090503010c050306031509032a070f0f09091e0515010b04 66
    0x2040440d125000c21032030010901070440007912030000900e410752050701010001011300040c1c0850116800000c00341c4802078080d0000030b0f000308000c9000c070740400040c0e001d8082810107008241c601c080303841c03481c0110110300c0d10300d0202d0710851042c04010300141e6804480c03110700c8503d44da112160444040c030a44411141442554000650035101080b1001550701c3c5100748184904001c3c108242941e4250b9100186107030703000c0000d43c00018500414076026144c48004070004542409400400300d900c4030760185081588050006401e0880302d6401030442c20908026111034a0485480d02c030f0b07070042ca030158a844201306180d030f045005948102d40840488140c00c00d95103461000c1c12090399400440d41c0280300c240d03010300c011511548a60906048440070418044070b01c0d280060640c03042e402d0791100070302400015018007818010700300070f034401d00801801d0350350030504030031845402808500d280c0441c001c0007000e220901c28092584d0702440039584408130a039044e40188540 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 771535377 1250 771534127 771534139
    0x130225030914030a030809030c07080606030c0d020612040312060e06040f090c06081e0a1a0a030c0b03130b16021c051210120c0f05011b0212240402 65
    0xa41140c031071421502d088014001c0c140c40718040d40c080e00c03401e1000c0c01e04050344c0002d02119050702010420003005001e110b0040130039052000c2894181001240068003924603525060301603140c0c5001c9a40c00e900c0506003d9103960745041c125841a4080d50360010301c0c3c00c140c00010403c6001700c03801d001d00000c1310200451811780104030211008141c00400c3d018000e0401c1001030f014540c103a52240000008a0540b01408482c1000030001c03640400e0740350f5504014900319403403e48859417a401603540300484c078150384444020103003074030030031407030300c0d800000190740061b64210200407130341c40100b0008a06008114030181c900a81c049001449048444001946501412802c809190701c1d4545000b1142d0188822900001c2c11500ca0000240d0b0001d24840f1540c1d001c01c83e00d0241001070f00850402c1d103011000d22203540a02d0402c2286000991081400f850074512103504644500c4c450402c0c5106078140700071140d00b51000e19040300d401d0719684000501c1c43c4140d01c01c07a45 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 771536627 1250 771535377 771535379
    0x319030c03060e071101020f0d1505030f0601170c0907050912010614010302070618050307120e10030f0e10092d0b0403020a0b0103060c0f021b1302250309 68
    0xca00300e810510603c0710481c3c003000810300650150400300200722610f00090700c0c000700b90714107107002ea00450483c0307025a40c0e42542108a4a0029510043c0070118007428140320749000c00c990b9103006004030904911200e2440d400b0740c804000850000d10042e001d4909480d140c4000340c21500f204141502982852181d1111000103215020503240c000029251140244004400030740210030101ca1140c0c0c0e5500c4100349141281d142012144106c000b990354649038070b40921402c464400030002d004000c8115106a5202c0c42d034400300c601c4910300020b214614026400c040c2c0350f0321010391004c1c01510141c02c4248015003109a14a000d05103209104030400390600d5554482401c2d0f200c04030340c204036540000d003541c90254100d8000e104441e4040d10648600104200aa0044030403030381d40d0f000d401000390451a1480b9003c0070380084c224a0011003902c105450418840340c1c8500410028060381e80100c0e4160303803020780300c40c0d40d901002544503000540c0b42c141400640105485c908 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 771537877 1250 771536627 771536651
    0xc1a0601021b1e04020d2a05031308030405011e0f1113030209100306110714010b030a080a051e0d0e03042d05090f071e080411060c031903 61
    0x3120200c0c85002d050840c1d001c2c81e400d50080f0050050701941e070b1080d020403803c0320601950040400a45800f000315a00c2c905902d55050740c600c0800190007403000900811810000181b080542c594104051507961303600c524027280102407a100350b0382480126030044440e244141d04c03450540e0540d08003041200f81c012154011405030926107800c0003080c540520050070000c40c640c0d0000c2e01300144000240d01c030342d600c03002d460141e41003114899000c503c820600c00319044968801244a00801801c0c1618011948070704034020301900b0303845c0c0055840907031481001200c10b100a911029078a036000c980b14640c1c0756001428048090341841c1e41280c2c410404411901160506102010b1075600c000000e500401028441000310344101c100183c2a00c8907400030f403081417156524400d41c82d04140240c0b881040315040700003807034503220701c07a441504031071000c0d006a000080c0301182032041b000108684140c10300640d05000c00b2070412106541d4440c0c902211032162801e022240c8020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 771539127 1250 771537877 771537913
    0x20112021611030a150f0b12161d130311070f0e0f010b07031202070623090303010605071103071502030703110a03050f0d090204020f090a0b0f0306100c1a060102 71
    0x2000078000060003070f1003d1700c810304e9501850b040d242046010440d0344031040060443c2000580100c440d4000c940c04140550b660b0240c00068440d02c1810b0714079226880007a235201e00018900210f0030030b0f02c541c0f8001c0c58015440d16038000303014811140f0f042c0e215000b981d410102403251982002c5000c010502e050042d180b524141c5003100745050130080180c40443d4101104003140c046590b0810034503001c6005801110020b0f22504151609041d04003e041300b400340c01014443d50380c0040c00107010103940001201c80064000f070350710180d1426240024140b01c00340c0d02c0761a04030030050708100d1058010000e4000302c1d0180d102c20241e00c002440c02511800e5050000703001900402000807101c501c10080c1c0301c0d0008400300000c44c60015030200e0226404001603080011000c80d0751881c6d480e0203882600075041c0040000e04080d00c1407101c01e0b0720b0001400d202e00c90340b0414000501c082c400d102041105820480e10362019440416584103124203540041c014004c01802c820000221 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 771540377 1250 771539127 771539143
    0x606040209030d0c0f061a10031b050c1002030717010e04110904060b0907120b01030603080702040b0d080304030906031109240403020d05070503150f1302011202161103 74
    0xd030181920f07038a1100112030741150741404544034840781e41c1a5000c01c00034803400c1c0710b200140c0a0300b500405883c0400090080c142011800c1605080440c0c0060207100e4030300a6003519401c01c5629000c00c00035850429a9521181031018030203c2002007a07a4030a00c8041080c0c8400070342126039807145400080c401c02124090038600138510800d02d03604040049aa10901605001550644800010b80440c0e030584003000010182c0242c034924003041e10400c0400c1d60242020031149183d556501030500443c08044c3c4120740d1100c0920302c640f1281d001c41022640824030f1580d0b4a054035029103a00e0140c007950001034030306076007245075036890b4007100c1a00d00c00400c0c0649040c0c04d000310060f0303404200c0400040c0041408000f005881d0808103100182c03040c00540106070820040c1481c00b00d00e0012416803040b90b230140306449824a030055005042c0540046414901c0c1c00184e514141001018819520006a000208210154004a440c8942d850040070702050080655490917 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 771541627 1250 771540377 771540379
    0xd020f0a09080328120c180609180c0c0804120b100506390105091506060a0c0219030602070b0106030e151503030a05040603061e05091302040203010f05030606040209 73
    0x300d02a0413a030004030600340000e883c540f801651190a004686068584114481e00403c4980c4101c8141808440456018058515110501e85c0c90044441480180301105010041da81d83c01e104e1b03043d204100c41400c054100d2100c0d40c0e103a41ea076601004c0202001c80c140c0701d8500e03030004500b441d01411364680803200c0042235a403c1444020780b1000c020716202d0140c410460501c803264001d240c0b144035a00d00c0340280700004451511448113810000101000c8420000c0c8030b04201070f0b9075494050300c5641030f440c41c11141c52401440031079900d64440d108003000e508500000810440300360024841a4400c894140702a640c46900b6026100010400d40c032a800400b4070400c0032030001011548201c24000300e20382022000e01080c1194044a41c940024100140c01c0c0001c0740c25001d007070020181102c030703030011200001c2c0c000540200f9026192107284200d010407504580d000443c203c1300e400410865982d65204001500016103101c1d5501038010600003c58ad032a05100740c07a80c41c60 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 771542877 1250 771541627 771541657
    0xa0f030c0f050304150608010f0b03061003020102070e1009050a1a0d02130f0f020a05040f0f06050a030b06130b0928210f03020a02011b260d020f0a090803 68
    0xd540d55115983c11480f0545c0d0519541c914001400301c0e001d00404202c1c000c03210340080c9400e50300b018107041034002070400f400210078800400041c0da0000e0824201c6500b00c8d0801c08036210f489c008084008241d000c810b02c80d0070702080c00142c3e10079501208014607030500313850940d140317803050000b98a01c41c240a0b60199400400c5000044282c214003580c0d400a1000181c0c04400c0c0321800803a0000100180040c0c80801c05101154010000502401c2680940310000b07150410041486c402d10608504240d102c5400c440d06072078030307400d90340c9030096400c40883d6161241604086900b043d5120b521444203138501d011203c9984452502c8042e00030003030914141800e0320303533502c1e2040c240b010843c255001701b00c6011a00000054004038801d6004e04001e10582c000103010701800c090381c2d90511215051f03040005c4012913101c070044195100618000405180200301d0301500501404050001442b078180070f20b044018440300c0c031182c0360b0a00e140e1300c0707072921581c0340110b282c110b480b11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 771544127 1250 771542877 771542881
    0xe0610031a060c0a05061f08060f370f0f1503020409050a140105150103050c12040c0b0d060f12020d1104020415021e010509190c0b0a0f030c0f0503 65
    0x308002c001802864a83c50466040920305d07030354103207041402c1301ca111868904034034070a542c066585040004064010091043e418070800005003000c01401001020f4607402108d030071043c1c161640b180c1403030307032135868420350100c21307c0d1002521103000c036041c049203880242c006280441c4100880700d04000403009140d400c60342440001c01d5002410b4410380700d1000f9000c0051212094041e540000000104181c1003800d1061010490036007107506160910f010008041c4c0b103501a140300c5940d0b4070220505844504200c2e56000d16a0440c2e19565000141e400511001d40c0082d030440324940503000030240c0c2c628001d50340d48002c03140298400c0b9130b18298008203070300d042164115140208014501a0740c0d540c0411400d00340360511740503030020f04c2805401503a1142041040038003000a01043c50f1421303000b81c03a01c0d800d42410f120b0402900c01c9500b40b1102c0e440e0040a4940e184105070344500849010b0310b1800d0900c07a2000290070001c4030508988202d901d9051564a43c81e05400c503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 771545377 1250 771544127 771544129
    0x4080f130f031a1006020d140d23070c03120209011101050c04052704170d09030804060c0822061d0606120d0906112a190f1a04030b010e0610031a 64
    0x1003142c0c60848e11401400b4440d0400021041c03003000085007503407948007541d0280042813100071500402031000e210000310400c3c0440c3d008008080c0f048002280140d4416260300140e41074402c6280d02c10241d03280c00108804010362000500075580203d40e44454031074044901c2903c01480d0701c00520280314140803600044611070000d01e4400d54002c49030410090003140811294400d2003030b4005420401400280901807140905072211854100d1582c540340013060b141e8064502c058220301340d0171801710144001d960099210500d1100100258409800c0c10359440c03006a074107500ca130001c0100404180710015001d4180d894540364080c94a00d0030005035144201c440613050680a4582e007240240b02c20704a440e141043c0d0351030440250545400c0c0401c03241c0380c016014581c4181041400780044400c0440c00715900301da07602d04c1d4061800035034a410300840d84018400c2000300004514016048030083c481c96040c0c03482c0c0018402d0f0310080702910b00402965030700310280c003078464031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 771546627 1250 771545377 771545387
    0xf061a1e090d050f15060103180305090f06040f140d0f022202030f250207181d0102040305161409060a080304170c0102030304080f130f031a1006020d 66
    0x707180c00c0244a49944445a19801e00740b21809440600756007040035844600e060400c1c000303810900030f10f802c1003220050700d4040000000c04201800384070300800e580c0e000e50307030303001d4400c2810002601c50b030b803107580d101411030030b100c0140141390703819143c01d60840950070b1426180d6112030b040814480000d0741a001e020300400210702645149515001c43c8415006600055018090025001580349400e0031748c030a0030a05854200720341940d1141d8289502d40c00280c40050300c5140307401180d0700c000750420b6001040001c81650144000f000940003e100c194085c104481c064010340d45800000150440504418098185640e9040b00240c20074106550000c3d48840060808072156449114051550300503600c885507409030002800702d03103541413000d040305002c00c0c00151308604003990740c0410b1340109281003051900c00310700407040081d074041120081c10400c520001080e100d00b085e400704074982c0f1032003095581200111703641000f01e4403420122081540906030b04d140300c85040f58 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 771547877 1250 771546627 771546637
    0x70801031115070807060b0910260703080301090b0105030606070f1410060315200d060b0f032d06010f170c030613060f12060f0f061a1e 60
    0x3800c15286804030302c4400324000208580d03405441050303298032403071402005071101c400c1014000c41c0044240090082d0701c60012050b10302608050082c46a80504100c800c4144030f06003006101d80c060020601070000004d50588079401c9090050003140b1005641070f210680321035401c03010812518021501100601c0206442168090015024030306c1103864a07280b11901c039401a959281001002140c001006582030b003402d0070710040010200751500c003010340c89074108884002502c2c2400d91203540c005005044c00c403130410348820f1038204849440e0005c56403016112880304941c7c0c10440131640900341c4e0b0055480301c59030355440348011910001a585140103000d1031401c2c02c0303107141c540c2c0031803840350390802041d40c1c5901e00041001842900601010713119860840309000d81c03402c0e896401c0568803411290b0304400002d00d041002400000b210000d110b19040c07015088007540e801c6427003207601481c0c800443c101030042c228214801e403941039414941c2c501e10302100540141c0944 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 771549127 1250 771547877 771547879
    0x10812190507020904080417010e210f04030c1401020c10050a18090203062125091d0c060f04140a1503020c010f090b040308041104020409020903060a02030708010311 73
    0x40d0a1078959800b040704130000391802c0341c4106001c1014019080200b0300d200280a1010003808007000351203a00351914594801003010068119200c0c00e04803c4208484064040c59038850303480d581c030700700644241c501d07014210610b00060030f6002d49610000381014100c00c01014400314034101e42003a1020340c0807007540c0e41444441c0c0d030002d2082c0c0c0108100f0005000c1c4c40030140e505d2502c0340030442c00c2c0c00c203450002ca24401c1404801d0044500103102405035055a09001c035034001f81480440049c0700e41d212243d031505001c0026100042d0700000701c103400c4420101c5804500d80c204102c4680034440b120710320035900380310800800c201e00b00c0392200f50074080e046014a90701d600f01c0c3c500c80144004003801007900060085004c11091042da500070102e440100244a1241c3e41d00e00030080c0a00086d040101c0c2e64007050038014540c82c0c41c29150001030003191388c3d81e074076480c0d103001c0e401c1036080324840d02070035001030000055402100e204240954071001603a096546101503c01044050b0f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 771550377 1250 771549127 771549137
    0x3070e030f0109030309230d0c020301140a0b03070801020a02030a1b02030a0f1a0717040203010e06090a02010305010e070c081b0a0809120d08071b0f0c0e01081219 72
    0xc80d808441c00e204020129000b0b0b80c010401c00900d003801e405042e0034214030480c2520030380d031000d5101c00104079541d11500c14030b014019445540002400740400d032003503186c08103075141403040040e181d42c00300200c0d980075001d4528265403500083c4c00c03402030001c600d001d43c004001649286104d41601d050044d4180103010b80341640b900800e03d0310204400460f2212004020002440003000b003120f13000750b20703900b215400c0c640004014018900611101d41504003000810119542904400801555070044580600d444841960365944c41d0300c00380e0100346048000329030390307050b50b0181d441150700e074817155203c9016580304150b030f60000d00f0503145442c850000c0c0c0d81c1c00809000035002e582c01000c0c415141c541076000c0181504642c416a84030340d10002c1030042881d0400242580b0a4541c20a40030303105050818015002c1500002400301c2051102e0900700300c800c02040056442000989040744c0e01c03000255540c400c1004000d2180c001408140c202c100000340b4a030300c0d0300305443c0c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 771551627 1250 771550377 771550393
    0x18091e1404031e1205040503130f051c061d06060f01030603021f051209030703030f0c0c2a080102120702060708010b0d020c031c05060a03030c020f0d021e0108100b03070e03 76
    0x201c4c41150340584044a09410026044449038907002495025150f042030170000146400c001940650310840c80a44219250004200784440e079482910710902401c5842e01d135600d26801c25442d11000c81e43e441c440c0d06c2589003512107508c41d104210540b58080d00407401c0c2801c046031100c0411086648408101041044810203031702007070401c6c01210002c00450300c030985450003a003a907808001d000002403803d07494203182540301040d685141d070800c8071400ca03510420794500054a004d0b01d0520701021075400081d009005500410800e883d040213000d580d03c4050080b40c0b9071409907410f0000030300070401400402d051000401c454640e4040061601210524090460300300503154031081010b030186854919541c001d20303070302c0002200e03400c2d112410b40c2c2d006020b0b0007030500d000c1d00a002101500f4036540b202821920100e0700240301900e10040c400090410952495016000880074800f0031051850007005001ba00c484520305070a41c0d541520072a00100f03214209a231520031420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 771552877 1250 771551627 771551657
    0x9060315060f37080a1a03160315020a021f150e1605090114090402040924150806010f02070b0a0201020c061305030a18091e1404031e 59
    0x10030500001c3d03030842220098003000f034403120210b048505808140700da905210164030840b0503a104c0071030040000c00012100c042c07a000301c00011840d40620820003811882c00c4240810411688100d40c0704150040703c901060690041d20b01c401c001d6030061400c0d450748480e0240010042d1201c0700c00007a0018000720000c8443c0441c0d00c080c50440c030741e50a0003080d8919800300c0c3c00800d00c5003800c1d0718000003a00021b01ea246c17124420581603070007040e804825502d0b50100c4004280303000081c00b07801c0381c101c105442800034480d25042c40307803045400915402520800010744049880310320244c0c0e90308005580380401103e1a80450040c40c2000c6051501340004d88100740103940010313221010ba500c1e8615103200501000714540340c0b001e80f180058000011039561412070f2808840b10148a40420a4200d0903004204803a040426800c8003418926855200440c0e94100380030445251208501554040c0c4001e17000900741c01e0062000c11110298a039580d00398500b05441d10b000507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 771554127 1250 771552877 771552907
    0x1b0d0314090603240109080c330405031e07030f0f1202100b040e1905070902040306200304021807090b030a0606020c030601080d1d03150703050c0906031506 69
    0x1a544078401c4c00c5402050013034070354282e130080240c02c20b00307124424a040c500c42a82d540001c1c080c00d0f00c6102c2240001c01785132204050066001c1c0070720340d2905410801095024180c015005080c0244100c405802c904c003045030140414106100250003e513003161035440302c1c20405170081d1001e00b080130a90300002c2c0019141e140c2e10700254054003001800ba0740079400c0d202d941c03058610a41c141041d240ea40705002c0b6020040032035058001600102c0c40c600f00d804c189590317004508187c0f002c02c0000910000380c101a01d001015005080300c00007044054415002c161400303500303d14061821160401880ced0020b800010301d0400034901c9035500d039089034560003165041005a145c21040011503010000710b6420b140440c0a0002e81d8103101106542e041259100c1d81001203c1006440c880c000c48503440300c3c44d03c05801e40300b20b92681c03030401041003015111800064030388070000c1c03205161031047d0b5456080041c41e461868803000740c08400f015200c100d9550101003002000d069843e51 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 771555377 1250 771554127 771554131
    0x40e040c06030e0a0209010509100302031e010c08070804060b0604050d03030f1103010312180b0f070506010e09151e190b0609060307111005010801020c1b0d0314090603 74
    0x15003008140503081040050650b0107851802805a002036000310069803215003441c1515001d481c120034640c0c4000304031040c07014650021390140594110003004002200a004548907448001d210582c1c000c4012a4186400c80d005c4000800711004180080c1702034100d0180f1070001080b45007002e0300c50340050070000c01400114040703039a942e80c0b03c40000440c0140c8012640328005142190f00d181c96070022030030422a00c0f0300b04000b44084c1c029889038005070b00c02a024651085840d000d800810140c1507000d9102950b2a02c503c5000050400b6207078412ba00c0342c42c160000d42480d00110600c4960700e40040c021080c1800c020395582c10030003c208a0b58440d038200d040320702c1030702c2d8051840d0045545486600d40a40c900300324041044c0c441e001266045405403510b1072a002000d00c6c000c1c01c04025414000c00c2c0760401d0000101003005402030107a050041d002c2d07410030f6041840090400c600c48041c150085480d054003000b2038010103840b007020706d488036628907000d50540000d04960007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 771556627 1250 771555377 771555383
    0x40609050f10060b070803010501080414030d05040b090a0309050118050907050703080c07020913061d01020c07140a06080606040312050a090e100e0c130905011a131208040e04 77
    0x8100c1404030514070f01600009040444ea9076141c0b50366600c1780c41441c80705000303c6040c82440c40c04202080180c10340e12201003844002e41c1c0d01c40810300328203409420250340a945a0319080f000c19103030031011030091401d540c10b880e81d6200e180f401c0c00550f8501981e0088541011144600140503195181001e203d11a035980e01903503603075a460003515422020305010361b9010103000610041e01ea0317400803600140d4000d9810000c544502e014030140c8101030190b80e40301d040794510751603503005401a20810304800e0a0721045520f030040303c659000030000c401e9106410784020403c581c0124543c3c4e070008030282083d89041e450b41c030b0f40310b44a0280307101c103030014000158024a43d68040041000b9040003035200c1914107125042d414207030001c1c058240042c8511300412070b11010001114070800d240041c02c03001c0e0f0b540717012401c01002c1c00d00c18031400e404c440b658034510a81d0030b0100d40c076103200310052104840c10402200c640001c0003004031020b1108220200d46003515642d12840f580c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 771557877 1250 771556627 771556633
    0xc140a06050f010306060b04060507030e1c0b0103060b010521060102010617030c061023030102130311040e0c01050d150906031202011d070302010c0c09110d1802010c0308040609050f 80
    0x115528080c0121000c03a03020387c140700d070280028445690700908030382c450ba8140c504100202a0200014131341542c0b00d41202c0010b0000000c101003000c000030b000e04072030041c481006603000c0640192800e1041d190510564050400c039501c0603240d8481c003a412083c18800050030549810f444000340454620500e02588003242c401d14102d400c21450358405002107140070010300d4a00018241094000c10701d40500c8005050031540c0c40c02d40c147d030026035910380019005076076414007100760b516400507075006500304112030b01400c80c002941000c440c0c043e9202450804818080001000031002c0c90881d0058944000350340e50300c50181e10b002e540911488408400c07a0b402c0642114405c3c001c4180744e8404c0034103500380040206080c0c00726034081c01d040c1d4400100349401c0c59000000d0f0080b00350345103008208014a01c580d0043d016644503140108000700104032070042050920000030300042c0316020355000a4820301c130450f049481402e01150b400781c103503901400c04000b0710b102d4500b0740c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 771559127 1250 771557877 771557879
    0x405040c05270a1b05072f0405010b0703090513090213020910020c011e090801020406020d2607120e01090b1b030c0a03090f0f0b10090203070c140a06050f01 69
    0x141035400b42d500806000000c0000d4001c0c0349640f20b402000c04200d07400c2c014042409420300590100e0005028815903e2400020440032080301c2060300c3c1381c1d01400385180c000086030708500507044850300d1b6016222500b07201c1c54182040400c0300d4840e5240700560300c92025000507240c00010140d440d024201c09a282c0d000f8009004000494154403c00c542c0718107004045c80e40c0181e290ba4811800e100d83d225442103d0106aa480505074080080c941c400500044d034958081000d03d031249440d0307a0300314011181c03681141100c1007102507824440d04503000c5010180038640398441094110302c003181003840115142d08584400d6400e07102c6d1038001081289070b10058556104005403440c1041c11400d058541011500440f10403100741030f44c99041c107080c42890070348528a290b101c08050458407040c074207941c58a0040e5000c0301c0f1040740b4100840c6400c61750003640d22500c40b9545150f0070702001d880300100f42d069003c4c581010300514444001146040c000d5500c41c2c0d04030352000490b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 771560377 1250 771559127 771559189
    0x2030c0316020f013e060c280509010309020a0504140108061e04140a0b1612060506070f111002010902100927291219020405040c05 58
    0x10820f0403800904100007124202c504400590845a0002c3c10740c0c9411560b20300240025150103403145074244502c90307203003001082c2080d88020a003481449071014914401220b10102015485100a010403070611942010b94403903402040034900003410f80100998135030100741220702051103046100440e00060080380c80070008181c0040c8039922048042240c03020303400032a440603000401441501007510000e40f001c2000c0d1802075001b000d5100c8600380240b1070f80900304e040c41042c022800346200c819210340d041c420301085420217000c1da403030180c031070381c8100300d2410006e4225240c0d000c08503c0315681d01c40d0304001040071015000090080200e00402401a004e4200c803820021001d606110700b200002501c40195400c1d07104028900c5514200c2001c0e1640a42c031001e14204540d41c0c0c40c00b000d10b4071926039800c405584a0000f41010004c268503092000702909903000d0300e5906e940182082d03030289034040e02404c088115243c9400007e01c4207504440559007185514401c0005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 771561627 1250 771560377 771560389
    0x30702010e030d0504031502040b0f0d060806040c170f010f06090f110a050a020f030d060302180c04120201020312010906030209130b060904152c07210302030c031602 73
    0x758004800524203084103d100401c1d0788100d0100074009142d240700c010611030103406031303006408140703a03043c0c031114a80343d52111500410b0034140c0342d03410500e000a40300c001007407c0d8000c07500b000120101a0401c0c100f50030100c0c88441d01040e610035000f072550281020b22403e0034950521002140316071030150400c068940c801c10319501c4500c1e10761042c0351a6013103c100c4190f41c00354100181c56584c2e8030b000b07a003080820a001700a900002030403d00820351135004009891003200c00006035600000c41c110441d0040712500f035407075001c210030b11071402103007081f42d601441441124648441c0b9004441c40280a83c00000d0241e180c01c02402180b0300964000d5000c80d5140134032400c05219210000c082d0005401c035405005c6090100d0203100791042c0000d01d007140e92205107d6a800070038001080b055103a521260b03180c4078540701c80340090200d680821501d480a140391950441c00000160100d81d0307004a00b136100400000854940c144064800b01c41d884074414200c941034014004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 771562877 1250 771561627 771561647
    0xf071b050d0f09080a14190609061d0d0e060c0312061203070503071203060b121501090515091909021c0e1005191a0a0501090303020d081e010803070201 67
    0x28065404000d0061380c10000c0d15000d15900400050180c5040c45051403c2c695910301007a40072510042c900144801a0445038207184904800c001c3c07900070a0307000c0c1c0700e20082400d101a54110034116071185100e1440c8401000004000314075103801506001d1555000110280d401206d01c020480d86141401190500c11800c10165140003096039401d522445400c1e4000d001941e00c004d55201da902c02d500c860301504041069540c4c8000c581454940702100b1200300d4002034440242c6000f5501c01c44200003180e81c0900103204074401000824450b400030415141c204d0600c2c02c01c5030304101000418802405404401607a4646a0f00190303000c080c40ca040700342150504075007101135400050010040c0f417103000001015140c0298200040e040c0b912034250392402c00c050413041d0300d00c20000401e070102c11114151402c0da142e005460060143c4005800b5170846116683c10070700481030154410388a00351a022051402d100020341c030802c0c0c00203e880c0d480441d2071011560400d00c4dc00d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 771564127 1250 771562877 771562907
    0x10f09140f06070f1d0d030503040215210a0902041b08010503010c0503070c050c0307090605010801050409030906050a0207050319020909012d061a0c21030f071b050d 73
    0x2c80c52070540400341ca00b2224103103003070801504003405c48a0200713841003082d40843c000e0040311742d140d8600b0010309942040d034050b8410104c20011240d458001c00c200c0d520307028102041692030f03ca515004280d054010400703903816407115070410040c0e171036126189144840c48030490310036551003001004280140c12090190385824841041ca5420000f9030341d001d01c10f46000e981113890303032500c00c1c00c003c1d0b0761300c0882d05441009000b2030301c000c040e0010401c0e141c080e40c4002c8541c0e41c403c03c00c002d44044850240200354042810b01080c0d100f00014aa007400d51300490396036654481c04070346880300300d00e040c9100131850000b01c401c602c0c007e80851342104120000b0300c207814401c50180c1030304c40c6041c110100c02881c00350307549010000e038002d0300003018101030200080c01c00403602c000030f5010001920322030041540c06039849901d0410350160035403c001c0941150394150580d0441c0c407003e85420148800d481d000a900800d1503e41020944a000945030042d14000c0240c610741c4080108 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 771565377 1250 771564127 771564133
    0xb0a20060f0f06090a18020d08090f180109020f040f09052508062103030c070c0501050c030901030b0a0b03041202010515090a09030e0603100311060906120405010f09140f 75
    0x1101d43c036a20f000c58260458000c450001d8869007000c100c00080000c940001e4005000e510184148081c40c0c0180030030702d00030389905004500c030008000103101806e104003042c6c1d14000061142d40810b0340034005496a20400501e13080d02c502d45007126002541c80480349544900400880e4a000308448034014842d03449081c04d102c400102910450004101f103000d058003504101e07024081400c0111114441820350740d5034240748507580c9865112a03c15507141564280016041d403007401215000c4000f00701842c249010400110090f01d4060311141c0d00030aa01004200554581e001358040c0b403003940301d000e8059040b100642913400042c43d0014155406580d540c0a450b1440c4031a4080c10a0a000403c818185001d85040908000141e00000e000c010402c68401d44003001054034050025049240f002500b04222445528083c035040380c8144110340c8044003001c0c2d0303240c02034401d0001140c024000c1c07826800301e9078001c200f039486840b04c0c140e05040741e2040c0010500e07a0034400103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 771566627 1250 771565377 771565381
    0x406090209130e03190c0b0601170a0b011806080f0610020705010e060409050c13080c0d081332040e03120a14040b010305010b01090501090b0a20060f0f 67
    0x40790340c812030444101d8035840384032210f20f0b45014411a900360031540c24221204000030b01c01001034042c0b9500f1104069a0800f0031002c0d801202c1c840b4070190b80300c25895195541d81022005040881191418880348141e1003410850404000024202660b234229040c6480700d5800103a400152455006202032030802100ca680450148280c0300c007820140303080e8480038085a040e1103135900c030070300a81c03820050147d03000095009202003c0c0c0003104150080e1141542c0c3d880d003c5009105500c4042c45003c0c1001038400700240400650700d03480c00900c1a9185810390300c012070340404610103501e450a1078248603024168480005081e10f042010500c102c1503a0f680c0d104154920300740c0c004071000500c3d281016003040c1003c8450003401d90440c01c1c5032408011501c4280002c490035420803503400190351150982208483e8142d403451203403868500d041e00182e020340223404c200303d50602d5890100301800560020010340e40c00170300e0b051500c03007141c120348032001c0c144081000440c41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 771567877 1250 771566627 771566629
    0x15031c090501050f04030503030709061107080a03111011091e090f04050a051906320a24030c0e130209100302100906030507230d021b07050406090209 66
    0x1000d04141c4000707003810780d51880020000f5040d40226440205144800030411265681c0021200203c51881d2141c03c6501502810340340c030b880c294000c4100540c082c00780c400101303108403a10b0308420300000507900110850310140b030580b101c0303d50001c00804002420b02040c103000320340010340011801d00c022200c0c00c002c0020f0340150302400405024003030502080500100380980c011081e4000d04030340040c20700301c802ca5103841c1442401d681c100c0c640b004510003030801e940c0c50381101201c450307815600c424502d0b40d081c081001500c13011550344d8035607090a03030003090415001d035482e60550301500035245260000344500c484c3c1202c1d100740b441c10140b181e0510300c070001c0c0c90303500c0d4111100601d03651b81800508406003590300c00b95010025000e40b2070782c1d5811042c00420760320300f81d90510050780c0c2d4032010b070303407040004030000d41c104000082c40f00079590341000341c0982030000402514003003070f4801005102d10804400085a003150310100120300c2c0601c1202d00130640101c0c00c0d420482050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 771569127 1250 771567877 771567887
    0xe10020709020c1903020a06060906060206070c03030f0618061706070f030207020405010603150803040b18030109052512110126090d030b090f01030f030c020915031c 73
    0x700c81d0822480d00410b022100000c10b100f07951081190b038042900300400c4d030900a43c0c50241000c20340d00da6103000d00c04103000582e4014802554040d0300201030a4898200c11101d05a94400540030141e44140c010406955402048010425046541410841a038440040f01c0040e881012003290008580e04200f0010542ea507003c0d0070350400da12036010686013a4064450140000d50013440c000001c111241c01da84005145940f00210f10b0310f2070740701d40120741c0d61701c220700401c04a0352062040c0303d1001017904903114607c00103800450f1405483e074899181150381c440340d5a442002e80c1782100000030512440b40102841507420200000b1502e4280c0d42d0b541e03100c1603c0c100505013000e01c04030743c200048031814041d2031307408090f10b20b400a41c0913220000d580700d002c0041e05000108085180107590903009480c5900040e0300ca03440c2d0381d0313190007010704118124148400380b4410005a50b41e121880e100d49400201c01d5000e0742a0810141401014014001041542110340090a9000c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 771570377 1250 771569127 771569129
    0xf0111130b0d02040308120403031803051b07090603050f0d0f05030a092301060812070b0f04030909020a02060105011403040b0c0a03090c1716080a060207020616030f0e100207 77
    0x42001c42d62034400c164079101920958001402c01c0400140806c80d44084251981c4118060b0758200800740d00e0034020b0400d5410000043e000407410f0200c03400c81c1d1404100d4400045d090401c44040c1641c918402041da0410f0f8019280c5822884d80b01c80c00b00750034056030000312000c1c6014403d00c03000f480080d04030701015025a440c02e90760b0340d0181c100219000c20584080e480c41504046181ca00d40c068040c042030f0081900900030805422440321450702920704159111a003000c841d91561058a16200005d2040e020002c1010000076001103500c01404407a00e9070313000e410b80d507041800141401c0708044118900318002c004010100c0c855044094000803642e15140d66000b55200441c0a0b00348610041d000284400b00007a8a078240c1e61803075051a050000c1d18510007500603e62007450440c440c01b0799541091884000048265000700065880101498240202d0b120240e00c00060007100303c0c0071a0501c0a159a6290800040502c20340203d880d04010004060020340b6440c403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 771571627 1250 771570377 771570389
    0x91416050406030c05070506160f032d02071707020a0501110d030b0f0303040e04050607020d0f0804031403091006090c0c0f140a031e0c03140306010c02030105090f011113 75
    0x960108550185d2140c0b0454a41c3d0b074000080300c0b058104203040d41c6408010039030700300101d480c0f090010021406401440c1c003a1f0084400c001200c104114000010340e403c80010329156400c02240f0001211800101c0c10200070705905600c5038218810700c0080b280d95088030b81445808044506501c00020744802ca0920303901d0f0200e005204900411400700105840c2d036070500003c980814055a8201c1d1148034500840850b4065114000c1c2a6100d6902200703800c0010303001014420280d0084480c150094420700d0604244c0303410f0344030160150410b650303555460704000c80c9804450914020300019000780301080000300c2e1240f0014145484c11840100000020404035052100501a29803000d031440d0035558407000902d0010007041c3d1590320410001c10310002001c00f18171503c2114902581070f107890000340d0544a07003504681000f00a603041017800311102d401a1400c0c0500341c02003641000508140d288140f016080d20110720307080c0030082080c02a0010031983c055100c0841300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 771572877 1250 771571627 771571631
    0xc0e071107051c0c1503020703031a010905010c080408120a0f021b040b0609030f0a120c030206240a0b0d06140609090408070501021206010e1e010e12010609141605040603 75
    0x800d1300e00700b030404100350301c08030748840711441a04000b42c0540080118901c640d03020000380038011020000142000100d90004041410521280d40aa900c400301c040c0140700c00c0703080075030b21010603280c03100e50542025640e00202e045400250800420841d80100340058090a90b070707a240000054200c1c45114800c40d15030f0829103540e200c5104603a8600d10140a580c2d50b40110701c0a1982d0f043c12140841c0d1035480340f00080903082c4190241d01c851545a07024108039103c0c0258040c000701524510340c2040e03180d0614400c66650410f1a00080814130344480d203440c1070340010402c48210f0707404286500c401d5100d50026036119400c540c0102070407144481d2644a504100c04a40180d04008000750b10015101c1040100c00e50400e2141600340c0c0c0d5008040b00003410302003040a070030003051a501858803442da240d80600741903000700b03a0180043c020640100902825210380c0e034810240550754110b1b080041420100c4260300007240c0c07203040c030582004040102580324038491070080607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 771574127 1250 771572877 771572929
    0x5161e062c0f040501170c0102061306020304020a0b030a0e1606020a12031404110f040b30010903030b0a0f23010903150e0f16030f0c030c0e07110705 66
    0x81d42c0c08000841200002d00100f01c0740d070311040031030828a5541108685441f54040c8620590300c0041e20522a0300c540c104030300d44414a50f1228042d410140080782c0c03002107440b001c1384150030540990300c9411480e07004501d02d003041c0d849506203400c0c1b0220700200c0d0714450003400340c107400051a4461275406601c03050507503000f031022070007000c40410b00c0140e03142c01400d003c24000b800300c503042d100c9030488852500010810400c070480702d00540c3c0c40c5d0040d6204c240c0b04003040000b4145540500101200d20b81f040808900350f08540041c1c50850202e540c03180a0071030f5080003c02c8502829030704800c0388219051880d4000c10007290341c8003c1d141564590fa0041c80d034803030007418000390703031040d809201d034548008041e020f001c1008465069201d0844000c2400000041624078800c000400c04940380c1142c503009548003001b402a5441c10b510030b030000014803415070030310090460300d20601ca203040008001300300859410180c3c00e241d002d8141400990b480740751003d40e084241440380c03100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 771575377 1250 771574127 771574129
    0x20c0a0b1b0706020d020105010602013b0313030b010503120322171908010f2309010602010e06010b1e090d0b0901051b0f040504050405161e062c 64
    0x22050341c010031000e805184000510780b0780000e20440490082d0300203000030f80c0c80307040407800c9030038038141e01e5800700041c0800000c0850042103a1300e140d0911080e035641e59440b0440500d140d12940140d40084299101041400242408540941411405400b401c40c010309920900d02003e0507814050403000d08103018040703101d1070301c05100d62291780d40743c40305030a0b4101c1015030400c00311010b4145c5d8001c409441284101500c0b0305135194041041c250b903040941015040400c0040620140300c580c2d801039480d034901c0d603c2802040e6035400840c50200c40103c2a043c098103911031141c9507818000d00c1c101e01e80c010000d044002003060080d8031403206500003288440c8a81d8082c0a18604806000c2c410368190452481038018104d0080703c050904c40b508828800d1203581030035080107010521040c68990405034105000340c1c00c46040802040d080324043c0400d43c4221000c4800b500d41e0194000c0c564201c40c002c0100d828150104030300d40c03080c52807001600702051700e540c80700a540310503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 771576627 1250 771575377 771575407
    0x31b09181e0103051005070318060f020702040f064e021806010906020c13090f020a0b071b03110d0204020f0a02031b0102031e060d06020c061006020c0a0b 68
    0x100906598001d4615652030404a0b20342e40e5044e082980e1505007000285414000e00500d103c00501580817848410b05071101401441c0c85c0c04000c00e00382d000c01291015035524003549114012002001549a181104a481580d08850845008003a00c03819050000381c082c40e50401e60307109000182483c000300340b640319035000080c009501c4804030b200d00c030f2500404001d40b40301e00802c2c0c03140b004007500d91401f0390303661010402181d4080c01039003600860380810703080202c406220f00c811002070002540020011111030300070703480074100400c1a50030700034030503261014010b11811f0400c040d425610f0341c10800381e094032081c1c050f00745002428119184d0780e04888008110300440350700c0380c810304030080d1280e01003100320440c8402880b111308102c1040c42100d0046501e01c0100c1000c4011840c41d2107010390080910b0750021031220301d0000710382d40c1c0c001007d00d84c80d404003070601c6162028404a854450350440030455000306601c0302d640e01c2e9031003902e058900e6844921307100c900741c44a0b511 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 771577877 1250 771576627 771576661
    0x60304080d0f0c0c050c15070602090a0f15021006030c2d090618022b15060806090901090b0106200f030c06011e05060a0201180305031b0918 62
    0xc20303450078040d418002ea214100aa6135481030b01a9615400e55508100c000c0d2040710521500354001c01200d000506607500500030100090030584402c1d40c0c0d52000803511aa07540140300000c00388480060482e410b115103425552601c400300101030541e1204065025180113044c60440f65042880c0b610717910702c0c001c521180340d000117051465242e2501c603000e03003401c1c800c60800001c02e20070300184100c14002d4444a0204860240d07a001c2c0c03850001c0305100c406900200003a42d41c1c842000054030240c9a24094000c07a03c0d040760b03d00342030080c00302d0300d64020092082c0f0b03494410b0160002c2c1500512a04649003441c208540e00c072023500210350b43c0080c51882d802d5200d00808a044403801101412000b550041600d006a9851851031006c2e490210315411040221500717004074036007400500f02c8504680300001e141c51070660a10301007100642d054000c07400c04410800103640c514020032400341424107643c204111140828a000840c1d480c007001400b02d440000d0350003540f00f02001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 771579127 1250 771577877 771577901
    0x11010c0503091e100c050c101209030306050111030a170a0204050a12020301050631060b0a1d03010209060f07020f060f13060c0b0402041d0a05010609140105060304080d 74
    0x1500501c0020890f00c1c0c844106602c0034080c51500c414850750502035001c420703407642c009028000c81d00f8a9000c102031680c00355940c2c01032200b0842054044100e40c4144a01e00744a03032800202c507800c2500150007410105c0c401c007000d500400c14002c01941c081000e600c002c0806d0107250580d258440580041c0c050741e04003a80003480c01c3c4002a07030000d241c426101e071030f000364001c0000d62101014000903a03501d44001118810030440d0a00d121018003601100200912001424640714048000d1f107a00c00c5c00b8020001d02c01e1070f00c0a00461030040040c1504404a008518200001d804100c031070007440310210b5042008200d440554039010f0415030041c000a0006c1c0e0344248200100407107400c00b1a170044078280c200008282c69000e5204688a80e0300400c02d0b42e0250b80e2a820800a440d1646075018071048010310351582c4a410030119081038030800000c101c490034501d2780411a040e035010b0000a00e82c0d000108510346a5030100ca410a0700140001c0d5961b100006500203080104100c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 771580377 1250 771579127 771579139
    0x70213110f0d02122a0c01091a0709080102181c06060324020a05030c07110406140916050304020d2603160c0203060c0c0c03030c011b02010911010c050309 68
    0x31850005590f0040c03001000c62481c1c15026120400c02040c1d00321110800318980038082d1540720051a410040c2000a03042d0002141c0300440391740d690720010a0508c000300d9000702c2d10a100000da0010000c10103085100021810b0902900010391840d00710400070340103228505030103003040c00311103015152603080350701445502e5403483c3c02c50001d00001c1c0c0c11010b00610082c4010309441a000321907002105a9400f030550315032120707000056100010484e12050241640021504d582c065a401056403800d0006a02800f0f010702015040051151800304e1204128070301e901d07000800d4a0f04140c040c2c0780c400024000c4d1810706844181e032640e45180a0f00d0394200318503444090029840b82d40404440011614000d009946544102038001e42c540c010000150f030104070103002e8103a0100040442e01e0b036a901402190655001000141117a511841c6a052421054540d10705560305803008201d51540c580361709140c00080c800140c10031080b0001d04c814404200151000300000400c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 771581627 1250 771580377 771580387
    0x50f0114031819020a03020906061608090414040c0605070201021018030e030f0d0e1804050c030c0a080303010501050d060e07170610050f03060604030516030512070213110f 76
    0x1880954000200b08a040e41c45030100050301c401c1c0b44403540040e1540509000b01041c15170b420401407080017001660028400e00080b10310501d500b50001c010360280c11800d03601c129450030f10050fa5080d41849500708800c1050000058a59600c0d500b15003180c0b407d00d4030341010707100403800d0000007040c0030f0b9840d00306011800319080b2080ca0419041c403d40713400d5109020102070585602c04140c0c0641150000303c032441e01d250150000300e801c90f10082c0b866400304903c2d00d41d8070410105446c2510180d1081e07030001058203040120b2a590b000c03c9482c4070000b0b25140d40107aa03480140102230401c50045035903098101302b82c000ea409001c0a0541c048686414000141480149a03554541020040c0030900c142030000c0c405440c04071680d03c0e1403030f000e00c000781c0712000c1c0d00142040760040d008010000114401740450900b803150182d4400d002855401c00914201044000b02510b14003081500c006030b031040c10404c510800580d0106801c580341d000801c00340100762840c80d038a980010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 771582733 1106 771581627 771581641
    0x170402060904020a270b04060f03020909091c03020405012016030b1005011b03031d06010b0a031a012c0d0c151701050f011403 56
    0x8000d160070008800b0404a81c00310300c010700000d0b00c61400d2406800181d4030742c004a101141d03217803c42814200700404901c580c1c41941d09100000c185420414001d40603100780920040c205020b500e4110802501c1d035400c8500015001c81407011010960b01a10945040d60010387d42c07160051030780b01a94094440b0740d40d04174424400c540e07240b290805100c0170280030354404c03c0c0456190600d107802d810080c110f07030041418001c011030030108608522000100e01e035014030f03012995012015400260ba01580340112a0340901c00010940c42d844900500d20040c0703955040080e40a0204002585c0d000004410700040003640403022504101c02000302c11000b0903d94944460b8983c0002e14440c036a4400b21011300c1c000c00c040003404000d00442c1c00f00001c0d400c202c42d010456100390140340005028442c4030724074440c00000164845c04020301c001126280c09903490074001 = true := by decide +kernel

theorem cover : BRFrame.Cov 771402877 771582733 := by
  have h0 := BRFrame.cov_init 771402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 771402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 771402877 ≤ n) (h2 : n < 771582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
