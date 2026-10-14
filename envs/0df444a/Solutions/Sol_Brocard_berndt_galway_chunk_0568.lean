-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0568
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:29:33.63101+00:00
-- url     : https://prove2.me/submissions/5039e179-8280-453d-9906-b43bab9a82e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 101978417 ≤ n < 102158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 101979667 1250 101978417 101978423
    0x9090d080c4905040c051c050607091e030503040e0915040c1404020304050a060c0509040501180606050c060c16080a2a02010c0807020f0315040302120c0309010309 72
    0x1400304001c22401181c00305402502580100c681219140c03580351100c0c104008142c07801c1404002c002182040418141e8000710390203154183c44501d480c40450600e10000c0c06803103a0414440d141d9085030540c0e045410340690344101c405401c90035083d50426100007081c5030710a0006000351a03440503402e034060f144a045506200071440080004001900d0039100c110b5100300a2120403c84d0406064000301a0341c15859070810343da4890ba80c141e044805426107550f44100050107103e4001c8610300c5000400030310642d6141d0703da141c526084486c1c1d45581c240340000c0010603d002d07406954a1504180c05071103141d0325001c1d049540c0e80a603203c0c44500901035040e0000640703000c00380807201c0aa07540c3ea8041a489208050045203140c010001e00441c0522400180e9001400b446c40590040c0c8142e1611824030114410b5221140840e5041c018080c8070002c5102070004948194000c1d401c5070300c044900340500307249224489120f45103070002c1001e15110350280e0031a5120a00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 101980917 1250 101979667 101979697
    0x120c0503030103030503150f03030a0e0604050301020403030819050106230712020105100806060f0111010603081603090608060105030621010e0a0213060506030615041508040209090d080c 82
    0x40166546825548240c0007140822404814403040b00c1d10244c00383e840e84010748200e0301c01c0030008002030b0749028070036031001000000e44070040326445000985009010140c02592165164a400f50900c84100c41416010011070f02c0c0d00245000d902929040b1001a241d90780e40c1d1000090400300010000c03414030756407004015140c000741e9411a1000d05030002e90000420742000103030344298004651261126500200a01840760b80b003403a0302c0d002810908010401c480c1c004ca03803e016040541c000b4042142c0072640d0955644000c0c0482613a6200340d40e070003102910b0320415544004192815400984103200080090501c3e0750342014031880300c1070b4440c3d0107407610009400d56100f04c0006d00280c0040921804500701000184491403030a40709110040c00c0c0b02c0420b1650100800440c03040b0740384c1020006034412441201c1c054082c29001d200006402440604490419a4224014569040046d09400c0082034400c4104500e40d214009034440d4100310540e90052800591a50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 101982167 1250 101980917 101980937
    0x30807050c13090210030e0304140312030a0b010809030c1504060e0d0509180c030a200d020927070e01210507020c03061308030c0f03090705030c0d03050712 69
    0x2a07240d00190003800d2950078003007000f400c18030501c8101594018404181030812032040340110000c419181a0f4a914413491144c040c503c0009160400d04404064240f00000a00103001d042e03400404900d0b80c280c803885030544400050640d24403540ba10029a90081d49101203015040300d1070541190140d24081419005155940e040071409484100410f03800501440b40d41072010702c00342189007922418016217003580d0710034014440280000d140d540da5000c1003003200c2c12882c035030642070740c5d5203480c50325960010701c103c00951019040380c1c81110280c4030248051648011919a0324020903503c0355078031840000d4908515101d0528180001104000e47c441c00c0c0741c910300c20b074400c04031000c22942000c0201a04003036460f01814003a403c1481040640c400000110341203980c02208213503039940740c1c511240a401035a03134010088070000184402c4080000d01c030015104110240c421200b502c10800c100d034241c01c100240458801d018060224034030164085507404036050400c495 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 101983417 1250 101982167 101982169
    0xf0e070908011e0506030d020a0b040203030705030f0304060b0a03030c030c08090301230610020601151202030a0c09230d080d020304050f06060a0e0a0b0102010b0307060e0117040c030807050c 84
    0x580c8000b400011800d01080c03c540b26180640642500020b0540142118400300350000b51a040e4a00000d4040f8401202040454a0400c1101c10058211051301d071140000a1480c4c0568016101503507001d081600509061a02040345011668192108888a0320b141e8080d0390400c5012015070f00002c0c207002d01c0c041c42d00d00b030080310500705400392142c005d070340740b40b18480040d44040c0c0303900e0081381d14940b03004000e500040c00505407850318645621001180804540f590714031781c01c614a07180044244407180e10315400c174a800c4405602c600250743e03281c9400041c042e00240b0603040e110791410560400b03081113030420080c0ca0142c20043c4c0340c108101c6495040e640156812125940050010760881c5005c0c008075400074001c9030b0101c0d0a526084151021180240000705c5072640d030070441480707030b000350b00c060210200036080c0d0b8003869447c4800342244e402c01c442c25012815008049402084072040275204650101040d070805003980c640c1080c1e508115011945445818081701d12 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 101984667 1250 101983417 101983421
    0x1050301361a040f020901050406270b070515070225080706051905040501020c0909010b1018060306050d1119120201030c03020c0604171605010506040e03040f0e07090801 75
    0x100d001100c150340da0360111601030004445282011303050562052182c1ca12aa0b4882c086900710380042c60b211480d0300d502d0f100d143d5207403151041c61140c1c83c600c50000511100385c81c042c03c503850207042624091260168240c001c404229040300050308071107001c41480072030019003405518410380a6410079110103805181407503d40014010407004911040e007400050b46100c004010ba1070041d05040c0b405001030340d0303550340100362440303006060700150300324400354085031034200d005180820f2400c2071500545102441800740069003440040811440c1c082e0040340215540070304259020306031501c40141e007411341c158030b0380c0c01145658074080351443c0c445134170043c0c1040701c01c0b06465106c5200142c103c49404401e0b4080c140140103a040540000c1030803507000f0f4116640742b110447c01d040100d0180f08280302c007001000300744002c07824004158005442140f0559017003041580a0544556034000e52048454400e00c03200140f24041d28015459080303ca5410b0a04100740c036804840c2c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 101985917 1250 101984667 101984681
    0x12020f1c052410180e160305070b0c0604110d050a110405150d08211006020705010801030b040b0603010e12040f08060c180118060f02060c0c0307020f0d0203010510030b060105030136 80
    0xc90681d50b030f901f8011b200c4180007440041040802c8280f41061021283d601c900300184040d1105100100c02c44250300d40c0341d0b898443c0e0b41c0c0030f400d5684001a518180055039030300441c240c0214900400110003e490020041d50300c5401440c041c801c040d103540d106410391080c90106800d030560003099500021922604d07000e000e007070b0038190070981040802843c08035180d1215040041010040000c01da0a00c070140c3c0042d0003614190599a800300440d0250a120f10040745620800301c03d45921aa40b40c00f0b00240c80d0b041004012459440312a01d40e02e4600356041d445401007003110360005004100c881c0e00644042c1000800c801c1c40040d5400fa881c580d5000d000450001e00441201c60742c1802141c0d4000305441d595410309440146140d5a0302420a0080c0214102500381d980342d84d500b0003849800b07070300400a1190b4a02609a10600151840300302c075115080c0002c1002580140e080c3e9041c2e0b610304504038604c400303548480010351f0358507155440c0c54043c00c1d6508543c141c6401340c0c2c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 101987167 1250 101985917 101985943
    0x1e0106050301081506060d0906060f0b040e0105060702010e010f090f0b040e07090614090f060f1213080a1d040c030c020d02030412020f1c052410180e 66
    0x50748a6142007000d5060107081907010070601406010400907944500c192124882c0070350300025491442e00e8040010549030f0450f0101761f2480400281074158040140240c949168041910742d80c2c5200344082405003010090115032180d4820317150b548100e18160175004140b41c60605640d44585d104540d440b90342290000c21030015003849010181c10000e030300407159182c0200d0b40c52408000501e0342000300c81040902c3d01c00034440c01560f42e00003210094050003060341d66a40034803e2145441c0d84080d02156004407180300042943c540102c1801d81c3c80d070402245031401c0155481100d1028203040c4145104c0b401c62074010b11621103110304d012500407600c0000c2c00300c40f40390b0041d1804040030388807811540100410301c00107101180d03512103168182d8000822801e80300004402d214050803d003000e0084565040500c840010090520320100d40d03078400c83c0108203a480700d00c0c00125032081c01415584020005d40d0484001c0d80e801c0721103094001070f003a4000038158180005480311f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 101988417 1250 101987167 101987177
    0x30402091017010203150f03070b030a020912070f270528060608010f030213110712020307020a060c0503090f030c1002060108100c1e030b0a06180807060207030b1e0106 74
    0x1b119041c9401044400310344101d130420144500341000a5651304180500807032030001001060180d80542c0660701c24610040c541e41c41c034810111440d0340c80000e0300ca0804039050f040707000205036803a00b90700020304442102c94441c07015468203480250202410320103120104c0900400c183e0300d0b5400004500040d00c4020420303a1030000001c00c0c0d0281a0002d121401000e4002c10040c1e8580c00d03001c4410070062b0300401c801049002c3e0b82503074005c11101801e4051102c942601d601c1c1c0c08070041c09168030031548446226180e08049038400c0c031007a002086580304120701281c503d40400d0100100c1401400c8668140384000070400410058100310b01581c0b2410050101c0c1a051000340041c0e210a0401c000c0c42540480041864600f2403a500d007000c40a600c01c40094400d030801c4240c580050040340503ea51020002d100e021040703681003001404500c0802c081c40080b403003e08960a503030041c01c0301811500d5854280601030003100d132885580c8820554029503135901d070700901080e01c070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 101989667 1250 101988417 101988421
    0xa0311040c02010b1810031a01030c0b07020a050603090705040615020f0a1a100b070b0f07110d0f120c08041e02180703150e070f020102040b030402091017010203 71
    0x501050710106a0404156410480c000c8295110307030400802000100252042689650700d07140c54442981c0c00c09010000840e01d520268004494824100c0b0b21030007140c0289551903481c03840b10f024400009621080400c1f08111520301000907542100c070b520140c1e14410396440c0002e0889556501c003881008400701c13031140c81a014480d80340f42410000c0a010483c009645810300e1815a40a0f8030150201c4030100b007031000b018904d400076100260083e40ea0b60240d003000c0200c12421101007010b03001da10000740440c0e11410742c070019040310000400025012074030540300c59120340740c20030810096880400ca0913016018003e44403045032200c061034102030030030b83d07664050410610941d0320008a4280140c03114481000200c11082c070004068a40704411000741c40088040710084001c62404180700f603146200d20302900207038448901e0311219203426400c1c1c2c09248030303000c0c0d40401440040e01500701200c03940e0340068803420b4607404640b1180b20304086080680f440c10544c0d030200c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 101990917 1250 101989667 101989669
    0x6070e030d17010308070c0306052505120c0d111201030c0518160302070f0506060f010c08031614030903040f0906030f03030905100e0f0d03050123030a020a0311 71
    0x101e240e90034003151421154441103020070b5803440d0410700c0020445d103400101c0c241481035110404003d1548031000340700500b0040c171440c003250035603584c210b020006008040c4855000300110360301410a0b006062090750b410b500301e101e40d00b103604d041d101e46840f90b840c420800001401404000d016400165455041d410020a02e805d5900b100d40a1480b162444040d40161038600fa4096a909541c800f09102000110040d0051800c0100300c42d039050444010088003044031480741405460030095060180011074000240c008042e00c00501000070452a101c2c95080c451001411304107122442e50340710000d019a031048806030b216810202c0e06000740e02020840e4002001c04034024003100c0d082d030f164440b174410003220040034107a41788094410803406024031214040c0003c010002c0e120451490307501d580803200030003030501500b00003030703c070f00d006e1302c1100d05881030013404880c12a00030400007140000100110781c90301c03074180420016036410009202442c8102c101040642c3d40070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 101992167 1250 101990917 101990923
    0xf0f010204090f05071b15090b090d030506010516020a120302030c0d05090901090b120708071409090d21150503010b010305091023090105100e0403080402010f1106070e03 75
    0x519107050181410180045c4c01d81c080131041318141d005140c280340b4181d52600c0b01c910704000da41c04c1c8846081281d4807051000c90700c1d0252041d803520301035400303005a42c001101100d008817803041c04543c00340000803401e400c913040c0455a070f101501142c03010381c544005541b1b0040381c1c0c4040b00140d2000030045020b0b031003440070030501c007414106103040450520000c0c0d00c40768140207402c5007e684084012040c0d40d10a0000311000500c82500c0540f501c0e0040d494448030940030314241d01c0b018180c00040c41c00c0584000c0d20445220018042d40c00e403500b412210000d0140240d0803445512221680f405128411004100e00d0410f51840c414600024982540c1451b0340700e5050610340020484402400709440c0003100506000040d16403201c0c04040c1183c101c0201041c03003500050420600910543c0440e000c0d407540c6034004031041d501c2c01d104403416001c03140103000070713003100210f80103500808505481201b0390803d910750f000c00e042c20038504141223620800103000e402d803070209070a040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 101993417 1250 101992167 101992181
    0x30209150102071202100305070e0a08030d0b01090503060a0e0a1b060e030d02060705030702070f0b3708190c020601090c0513170109020603010b180a05130b030f0f01020409 76
    0x10501841c44d089403500064100c880036442081815114000274148620842e2524000d000042820240b180c491000325502d402c030861140d074284c9400742107100c40d03000c0c540b040b0440e10300600805840d641d00c0c1c24000a002c142803030240078400c002c0e20b80005a20091030304000041c010318070860b00d1400c640103104000103001c1d50b01039005100345039130320707580800c43d5a0b10805a08000e5603a8072904d10881c86d0441c0c3c0e03800500e94041104021a0020307402d001403024200040240000d2071014480744905408100444001403c50841104480c040c003140c9074403900e0022040641d05800703040070280d44090f8549801a00611f0050200040c1889100302e05599850407a0916142800444856105002e819141c401d14412a03103402025040090040c0d405031132907807a941d5a042c1415250408010301e031400e10f00c44500e003001d09011140e1401c55100810329901b504c1c1d410242d00003007400d0070780c00c0e81500648054909449007000003411040b2024001030f6128646a0030204480003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 101994667 1250 101993417 101993429
    0x5060108070809031219391209030509091914070e01080406020408151006050304030e010804021203040b07060e060c040512010f061d0f2205010603020915010207 71
    0xc07107070501240d070f48000250360b80002c1c2c22105649030b854640c80c0f01820000f19508000241c1005808030000a240c0481d85c8880605942c1160041c00c1c1d03043c00640342c014481718800038208100b0420346864513002110001d001703003402864405204040382c0440c00840f126001c161014512040384034540c0b040400c10a001c00c4c1507110380c140600700070300808a41220f41e0400105001040c180026a81120020844541241d1035280c4581c2100240d43d012615500c240b0b10682001403124060170482c0e12856040e0707513001c0101c000c44011b540404018000341d8004200c062850103062080005201420001580347e8407600c0c0b0b0b107090740654046024052a6401c50014040701d160040c0648058070760032902c54952a265072000c1e80100010860902d00358200b0b2000110301a030008903900709207201401c64806e5440e0b080c9140020020384aa4881002480902110320341d000d41040c0d44612400012540c281c2c3c0e500002c0300c0da5002c2c1c8150b011040303c44100d05103903804021000052072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 101995917 1250 101994667 101994677
    0x605010e1e0118110703080403020d02060103050709020a020309030f010203150f0a0504020715061410020d09030809180406051e04050309010c1707150c0e030a0f080403150506010807 80
    0x901c8801c00080c012040c42411640308501840d440c800e01e00d0380103d56041200700e250f0b902d40301241001810b0400c151001c7d8050b0141420486100e803021607694103982d0410b009200c0c075450460800f00075488a444581140020f10100c10196001e10425840300240c40016850b030600009182c030038040c0004091080c182611528065120001d1000446004540042c0c454100342010079000a0081c000c40b80b0b02c0c43c100001c00c0000a010300d4040084040e203003407207440314010f0145c0c3d80d800c0605031140480c02004007080020800801083c5001010300710341c560198000503030010020a0b513084407210345400801601004035030b424145013080c55121440c0c3e041caa1182d5840303110b10038070907040240d80402807040c0816000c06001c11032070400800d640782c8080c10415403407044101c0b0201014100812214117038419400c540140e2002405009811425640c036068407103040800c0303071041c0781448000041030715598581d45068860300003162515141c030005008160003000141484 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 101997167 1250 101995917 101995951
    0x6030708060a20030a0905011d3a0c200105040e0604060506190e03061603051801060b130e010308090603060a05060f070611030717150301090605010e 66
    0xc500040381ca420100522001420520900c80051100f10f9210710f0365601d2000014045105007a0740700b80034640c000d10080204440c408c203611038580c5c00002d0b5210380c0d0b0000007000340c2e9609400d101310901c01e641c002c03201c030b2480040c01d810409003413000800c007040d8450341c00414083c146405c801c1b2041440c40c0c0e0300d00c030b010000001c0c0c0180110302400031031003c2c00d0300280040d101c5030310178005400010b00f0706864848030a030116503102c1110070800007401001c20f400c000c1c100016400d0141ea81c0d000301021740180a00304038020203005002c080c80e641c0c40903903648260403e20980e07020300b8202025075a140100c00314104941800da011801d0898090010000b04c5c0b00c40e410388010103000c0310090f0780c03a180c2d07000240c802c0342c40303400103503100500140140b842c014120080007100c1c403950b42071146005a8844402501080f0b4400022618035880320110343d08070401d0a502041141200c4058803144000c2403c40b081c80b00708885641e613a000501c000101191800d5002c003803101180150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 101998417 1250 101997167 101997179
    0xb040e01090209010f0e012105011e0f050105150a03060e070203070b0c040b0d0f15060306090b0d02031005130506010f0311100e01050309070506030a0203160203030c030103020d031e08010905060307 87
    0x5401403142c000c60b07500023061101c440da00d00030851540c1d5004030092203600c0180c4940400ca40000004440a41c40e04038180c56180507800fa0078101c0350001c01e4040100383c038030180c1c12103500105000d02010340d030300c0b00070984200c4410018010400d80c2c0c000c0d92580c0e45840c103000c00000180c10091440c40a00081000c81c103030310220342d000391034414081245055600100080c00c2080d88c04984480610303008505540d00d644070301d040341e80b011400d11001c1000c5d41448600d007040f90020350503401000d40829448030782d40003190001c2d1403d255440304046512054180078083e0094807031069018420400c3c402a01090b250f83c4030200c40350000041c5176100501541c40d01c000c02818048040001110841c042c4145001414007a161340e50368a003c1d100304000f0350048484103101c0d9104500c076114984004241d91180000d8003e462542e402e5800708030040001d49021400c0204017034400748103814540c88910b1049168a4110155040030004010f81e840204454000e81c4441810042 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 101999667 1250 101998417 101998439
    0xf0d110a0f020103020d0c2705130b030705100807030c21050405030904060f030b0a0204030314090604050402160606080c01050703050d020c0d0c030906080c0306010e03010b040e01090209010f 84
    0x2080e80e20040c250700440c0d10b4401640030380101c9106504540c03500302c071410995088000040c07d007880d0b0b105414a180301500000d5520b02e01d00880b50401300f48d40501d092100907502860408800600700d41245582e00002950398540c490901e00240241081c004180e030940a003003022800f0b406e181f101d20844103400b14040e0100c0b501104255110400700d02400018002c030f515640d000740003480700c00e407545908009406140b104480c048440320014104080a1080c0d030b041c1c0340d065807048810000703800718000e5070704080126548240108800039041d40c0d80d10013400c0000300881c003004050402d040681c1114843c0d449180785411811050280c0d030b0f408411203105507454102651500e80c1c03c0095002030154040240c2644909101e0400c0715030840000c1c260603100b130f99002485622004200c46e4048185c45130020010180080f130410360140c3e02ca110a11000b0300002414407040c00090180c1d60500403580c0f440e551030a040d015420100c1c18030740504501031070b2890051604c807515030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 102000917 1250 101999667 101999683
    0xa0e09010b03280c05071a0c040329040f060f0605030c060c0708070306020408071e0608060613090f0e010b100305090a1b0e01060e1005030601090806090f0d11 70
    0xf881e008009003070f10603220000c929900609a1a50400c040200020040c0281c0e103c440103540141c1c00c807041c0140c40c040a1762a91050420b16521070411740780d680e032400702c0914100c0e42c050703102c2d0000e11094440a92105d103842180100b0000e60003411034201b0800b02c8000a2f4075074842420300e9024021a10002510661100e00782c804668940080311100c0c1091800d40291010b0b0091003400000d10503030b50082c1041e00c2e180300941d41c01039580c0c18602e1105c413203000c205001e080200c1e01000450300039281ca03030344031030068000b42c1760580c6080c5500c80800d00380c000c451401e40d50190000d00c44014862001c0150640c0e00802200c2c54182c001220140c07255000300405445e800001c0b40484107105480940f60310113407265520446c1000304090f44000d01400700700380c051600000e032a0384101800680000061310600c0700140040080b5180c0d03000425090610401c00e20002d041076080121910a0395942c014ec89001c0c40c2074400d0717040080380340c5401e0400c460f0600341680305801140c051 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 102002167 1250 102000917 102000931
    0x60d050f0303101d0105060c0705030312220506010612020412060c090b040308090909010e0607030902180103080706050705040b0c0604150905071211040501060f0801050108070f030b0d02040504080a0e09010b03 92
    0x2901c46942301807403880d244250300055010b004c04941e03c1188044a294213001c2e41d003048074400700c000000300400c2c80c0c1c04e0a1a000d0280d50011004001550060f21004550301040d003000d440e15898080d116070302c80c040c58084031001c1c0d88094140354298020001c0001d07250840305585080d103152940007440c09044105072060440001180c0711200035400075100c0904807003038490519044402a005080e002c80c10381c003407101d000f60030003d56849100181078070b80c8008001d040000c07584400d0010070b00100140144a02000086006070b4544041e1038401180c1c00200381034036051408031340c056210341800f9030355401d01c00e50000141c80882d4500646049040c0e2103640400342c20081060a0a5045e40d13402c0303450a000810216417040c21004015401d40390301e010303a640e40c2d004665110044800200051803440d154a041d80f281d023000441c40d000900c0b1401090703540c0c00050403500241c50450310242c000076041e118541041c9020a400011074001c01030358900032a0300c9061000038454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 102003417 1250 102002167 102002179
    0x60e070f050c01021e031501020c100f020a0b010b1c0c0519030b04150303030513120f090f0b03010503061e04060906020d0504080306130b0a0e060d050f0303101d0105 73
    0xc82c03142025816101084800703081140840c1003a01980b0300c41e401540d80200c607000c060210141075000240b1500c0000002d00480040c100301541140c0c2502000001c0085019440410010610302030026018006a8010f40d6943e829a0002c00421040d07004d140040c60a00c038a2146031900031064890703c0d0740850001c4103900804004070005c000b0412500d50003450440086420748880716417000341c910a842c100241d403141c1d001402201c0d0741500003001c0f03c81140450900d40d21561480b03004c481c0070b0034003410150304e60b081c00034003030030507000001010004401001145002c10081e40c00400901c0c8403d0b18a06050405080ca88002d001405050f25015504100035180d8101d4800b5000070b1070803c02800d0900c3c0400140d03000b0780b4007502c070348a143c5029000400602c228909c481c4014220071206113000b1251405135001800315522a001c0e03030104000c9001130200420847d8085d01a617580e140c803032401d080c1c4a6503500241614100c100140900302080b40d01141987ea044400d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 102004667 1250 102003417 102003427
    0x806190b0702040527070e0601020309091602030c060c030406060f0b07110f06070501060302130209090610030b030a03030c1202030c12060301150e0a050f040803040f0c03020d15060e070f05 83
    0x2146003c101e90100041c021050b8103c080052080030510b60160303000c2020001088e10b940c001240d50307000f041c18070303640004400042902c01d04076030346403903c4a481d030051701c1c20034000d11802400c084080b10015a44840042000100074080c4100d0000d00340d50000c4920340c50a14074806010300a030700740146500b10820421403141e80700180340400480041c01196202854501180a4032840c40101d0043d40c401c03c2e500c40c40e1b10b10f8000e030b41c20f0b648003806401c160f680d0b500400001c004401102414140e985c800c44107951014480700d20198000e0710081082c441404008014180720082d98a03a00d01c10b105100c2400900001c44d80c0300c030f0466480d10616292200007a00500a00610402040032400c0010704404104030641c85210042c00c01c108564400c056100d00c010304075002002a40100001400118070501d0300c2c200310300ad4003a00751010b407242d010a19400112005440c1c40709403002170103c4c40c01c24005c09018000703454003440345003403040c4080e11088e01c03080d01070244100070031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 102005917 1250 102004667 102004681
    0x20106030320150405010207050601060201050705070f020d02060309060f0703091208100b03071107090912080a060923093007211701080607050c1501060806190b07020405 75
    0x146042103a80c074070b00c05404c103450103134000d502c5104100c545000d4000000381c9140103204041c4030f0303d15500e5180c588642c40e521881d06083e201003c0741e201320060300c0c010150311170401461007514110000d000500b458610072a807090010083d000701418641c1e8880001d00c210000e084001003402c1054040d21041c40903610b24080780c12503603010b84080200880c260b8010f02007a4400d010380180d5644a03121644003080d200408009082d2050324080f510720544074400b00e41d80644030100006109444103032030000da50945d0000d50106040800c4041703031703070800ca50403070b044120400100b40780d1424815001e1002c02030000d071941e010703c819000c83c081e55210308466000750301454030f03954480503001e4203441d07055060b002d03400a00380c20f0306415804043d0880b6410303141e0540042075150303a45c06045601c0c0c1c0c01a0b4a01c4101e0003810001309803002002d06e6a80a0991510340191518140041c404203100c405021000c1c12284001000700522400c12204419016200032483c0d5650324 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 102007167 1250 102005917 102005923
    0x312151a09040504060218150f090307080f010515011d042301080d02060c0f040e0402010917010b01110109030e0607020d0f03020606010311030126070909060204080d020106030320 79
    0x380c00c054002e070802c01007104119140d07005101c0148488038007955015141c0c00d00c0103115126500d0590142d04020040302ca0003c88080c09412000904035941c0ca07032990a640c2c10b01c4454042c0342c4440c8c0d120002c0c03020510340080c02881c0d2404c00c6ca490110803050381904c2c01a8000c128005000702d64490b001c1403c0e007181180244a120b03000c82c8148196500c00b10643e41e980000c82840040c00303841c0100700500c446808a5200074400e41c043c03410282015001c0f848040058422418444030500020b400096041100c02c2031501000014000f6640c800252103880b6102c112525645420394100020703400248031102c1c0c0c40d0945000f603c4a21a1000c1040c940c80c56402800740018101030004050703001a40c688501003ea806002401d00a2050081400213014480d0301d9180011081c000b80a8104920704c0045840110b030021a40c03640c01c0c00403184201300684440c0e03000202406510f50810140b40000d2251000308112031864400410b00c200c06440348041d4918044084d800420030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 102008417 1250 102007167 102007177
    0x110910080a022505010e0a02030d0305100509190b010201020f07030c020a1d0a1404110d1505070e01030e0303010305120705010609110a030515130c02070f0906030312151a 75
    0x108464145500707090509001e0b40c03e0b0001120250b0070065001034004000c180c10710003980c060010090700429081c1500a02401040d0f0100315004410015113659102049070103140001c005460340041e4401e0b04041c5e40c82a046070b4190fa0040001c40850304006049802da681c05103001e48803810740d40b000a8580050340e004000101d07601d15003041d8561928036640c095146000b0800482489a1a20505071021500030304030f1100c41c61541041c3c144007401025240c4100310080c0d091041c2005607045800a56a03d03000801c1c00412041c603581604ca11588100c289009605561442c1c0c0d0340d40c1d580c201e40c56075492404020442e002084401d400c6a40030b807800c49070903c0701014603804003c107600320404240c0028200b1000c2915041c000c0ea10180a05c0041e000c8806a03400034116000b03030083e10005411071203482000030701d41195101312006800800c101107845469410b00a00314000c4000141d1014548019020744480300c4201104490900407840b0b0000040002c203040c0f4020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 102009667 1250 102008417 102008437
    0x807050124140f04020a17180706030e0a14010510050901260f070b180d030212090a051206060406060203040803090d02010c0b0a141503120d0908041701110910080a02 73
    0xb18800391b425030031001e01c40b0204401c03180a48250f8404983c80720203100d54217480703001e0304014024808107200717130050044d03100720300d0850311051103a0b9a40b10f810b07000c085040c00c00365900d82c2480044104943c02030010441121001e0195040410b20704128000840300509890612454050003006010820002c1140030595098960b81c0008070281c0d40408500034a24220f5130688049240c00506a15007a80550003041e00c81090540c3c00c14982c010302d0401d6120350741172000583e90b903c42e00040040145035002d003015040000910050382d211f504041d0a5400c1840140300058000007940e046040c125a1105006a6800113850010042d070010704010740c200c003084040e40541d04007070341034400c515204101d5034481c201c01d140c82e40081c1840f98550014940c1440c4661580d000d0301480d040c03480d0009801e04559541d034090b500c15844041c50031100b0011901d052420b10650f03040340c2e01501d0340761030103001200150000d05000e2001c0300344503800c0085101d1940380e0b4103440d00c03035070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 102010917 1250 102009667 102009671
    0xd0903020f1e01050109020a0c0210031509060513060501170c040b0f13080309011d040b040606171006200c06180319030813140a0807050124140f04 65
    0x1020224425030a030100341c402d41c258288400024102954800c840752000646c0e19641d00300020340c02c12042150604c41c0404140d180c0c202c0c0741600a808055500924281c1000610700d4038000074007095084011003a28075602d842410801030360414990704900701040010b036a507950312003030031009010781d8000000c078100c080b5200d4007039600600108451594818000c0c1125a991286641c900c00e40c0d5400780007640e031075400e51400c0c40f941038440b901600244003003241040c440120702114016481000007600c0624214101c80c1c8a41071a60002d119100811641d814007401070328508010741010001030503984180c841300814804504119802408a0b43d02d031031401c190008118050010351190281e148041c4200800030f0400007019459165482590340300b1101c0080e59070841c00690340250900f000c1c122040c020b20820036410322640030181c4075102400c11501b100d0114558000a0400c48191982c1900c03030080035003190300d180c00076a24821004042500895007184150f0014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 102012167 1250 102010917 102010933
    0x303010b0706020f03011715090c100207150c150504050303070e040f0905030405130227011202040b030f07030203090a060c020a08030408180306010308040608270d11120d0903020f 79
    0x41d20140a80074408158088880000510442c202e44050032740e80340c06550310503110918182003100308203108175058010384100641e00c0111680d401d048440180000d02c4021208082004c10f00740c60500200e1500108803501e05942d44a51300e20025104c2c405021907051115601d81d15508150b00c0d0030714000c0c09100d44c0000d071919a64a41007400360600c5600c003480e00604411062090701c00d0080c2d000c8040309141c500d548103100d482000390350340741002500800e21001c04130740e0000348000d00b0000d0307160343e0340d182c0080c0a11111101809580c02c250040090080c2900d0006094580381d803c00ca0000c1c440740f50f11800c4e447c0c2031401d00024500603010080009026600c8084d01c116400b1100720080d02c100b0204050f22080709001c002e0000c0710911051080c0c42c40354035801d601c04060081c14a80a03a9011400d0192442640c2e800682e400000401015079015540c0010f1540403c001c02c1c0b6148800c03104140c9000300559000f49070781c1d410302901403500c00c107d5440840030040548041d5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 102013417 1250 102012167 102012179
    0xf0206070c12061a04331508070e04140402040e100608010b030c12030a0f020106091109031506061b070519080f06010302060307050a031104080a06050609090303010b0706020f0301 79
    0x580351020b200389a030311464039038040b68207150103200102c01d0500302e03042c103803079070032201006c82900248012a40e142e03101e40490f41c01400c1e1413452950415448600647c602182c009003124503070b0107001d00440c11b105560784c420304900d648903000759049a001c2011006218003600d4110301d2800d146405040940c001068039040d407003040f10682c2501555800e18945003800052449400140c086502c1041011283c0380300c3c00300040303044141d10000c01e0b074070388d2052074130240d07241c070706495114240c005210301c464034041020300c1e00724200c2c60b0103020500c0c041c1c0c006921030161202c50488070300400b9900d0124041401001c0c0500320003003268000084401e00010000010b0244485601c620354a2114132000050464101d980c01040a4a5503035880f200304d034140c0141c400034080c581c6031090311150300c40f144098009004a0001003140301058100402a20005440207020700405070074440e24400200490b030640e8500b0364000d40d01c070300c01c0c030744034000b03118110b4080b54105010002240d6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 102014667 1250 102013417 102013421
    0x50106030c03050109020307140a11150a0c02011103011406040f0e060a06050f0f070317070201051b04030c03030507080d020304050c0f03060f0105040c050c0304030813060504030f0206070c1206 85
    0x3a01d007030303070303010420350780c82d203040c50300300e01c0182c800320301061207100100006407480b130062280c2e0b003251600907200401c903003016240014100820b00040c8204c001c00903000141d20070650164040c0c4002e110661045860b01c40303510040c02000403222200c80d5100b01600e5003021680207142640156505030365800281b6181401500c02a20903a080280080c1030f0f4411001c0c2c9503003203542c400107894081031840c0d0512a9010071400c13018041c0c02c1300300780300840b07a440405100e00308980001c1110b1070001a2051700580360100784400b29001c0c0001e10100f14030044442c25a075040c02c2040d0754070b146040a03045401101c1170000c0e820300000400041190101d04d003a0044010382d489003070030080b1000c25480d4075048803442100045140100060700d040d0300140d580410b07605049140c40c554030f0f00d66003107500581003a00d0010703000170040c1910303040840304001001589809230030542140d0b50130a1803a420740c00079104180106014007403000c40c0020400078422060040c070000c100b0b150404c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 102015917 1250 102014667 102014681
    0x11090f12012703140301031a061c050a05010605030706080a050a020c030406050408010c030b1807030b040911150903060114010e041d100e030703120f020304030c0b0c190503130605010603 82
    0x743c222640c0707000b1242c044d0203403410380e41d228000c160b060010404081407610010000c65014806d00060603110f03462480c0ea10100b0b0165028040001035401d06a09443e4190f00c864000d510a0008124459205408a8104034504408200b680b180903d45007e4042e040d03407910741e80030010340015440d40090080c803c0b200d104000788407554000380300b81c00f21810f50f440c4d650020303500445050712101650303d06d58400b00300c0c1000100714040d0340200b41250101e41c4101c0d0411500903514441d03140100500340441100d00116103442070100c0869107a040600c6813081c829000d880e03485450b801800107178556100500b01b0045007604410416603000300100420481c00b641502d078020440c85e004031500680c00000542c5030440a48d011a2005d0401c000c131a0240e07980c00e0700403054002c5000844c0202e0003a41d800541c0c220030308059001c0a40907101d15000002004441107030781c5180740c1c0362520b42c503a0400f1074803607492608114640c0c80c2c505e4010041440e120000c2030094159025003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 102017167 1250 102015917 102015923
    0xb040303110f071e06090e04020f0a0e0a0f11040617040c0302100c201f0c0c121e0506010303080612010908030a0c1416020a03060204060201020d11090f120127 70
    0x70700039030703034130181a281b0090314014040d21310315140014000d814a001020044007003d4030508036640c1d68609003c8101007603410511301510342860000740040341c040e00c2603800d04595142d151614240010f0420f4513070300141110a030507280041c090042c91030304800119005480007072419401d5030001c02081120004030740813007004442d1000100104455403170040054810108074003280c6001701095907002c019810408080101170001c3c0749400040021f03d580340d080304c0d843c04540351001d000c17890541401c442135610941d0101154000500c0b904580e01428030b404140c84090105035030f8255079819610b50341c24000554100504039000710f109001200382080541220182181d0800401e41158050b40342030104003820090002c0900c101c510080820036001d95a41e5240240e82259100380050707503012625030300002c01c0c1e0103180e100014510b40b5520f0014801b00107440300f40c0d1110000d006510328aa01144448254841040c01c1840031a403840c14125468400106c64000811 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 102018417 1250 102017167 102017219
    0x30709061d060d06180902010e032418030712020601050105090a031b0f061701050405090a060903140c0703020a061e08130f0f0303060506040b040303110f07 69
    0x10305984039441c541424848074564810906403032040049a810008080014a0751100d000990043c01d842201c001d80f22840041001d500c9400054000d220381941e0714001d800850100090740b075001d450390784034511008840c0d1036845102c2d5003440002c240d05100d00c0e522000403038809000c2c0600610700d07241d034603500312020744c0c2e05e80004540ea07020f410305480c2c100c00043c10038800240540801550810a83d481d03118003a80d800c6117020300015a4031a0021860304541c0000c4410242c003210f000d400305580a1006042c80c466480d5102e414510181a965a5446030700c105407003940301c202c0041c1040f03d400e0302d440540d0407080e16401c00e440f049202d11101e000000b01c5034000e0f1000800e1440929516240c2c03201a101a0381c0c00308000c0c40c0d0003841650b0b0304441e000800d00c8110502c1a8001d4000c5020300c0741c1d074074000e4100c8140307400680c0310b41000c2c00100802c4c0758841c21035082d02e90601c0d0120300010100102490096040c00900c0c85000b5000c0c003154180d20400140014000e942c18 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 102019667 1250 102018417 102018419
    0x3020c01060b040e0f01091a0904060b060a0f020f0303040309050402090d0b0c04050307090509031e0c010908040504050604060803090402250b06100c11012d02030c0115050a03020d05031608030709 86
    0x1c000c0403174000b07041e00690800223400642d42460a200700c5540140920000b01c0d10001d4000014299801280c1404c046010801c544428660410202c6005400d1400852460034940c50203403070704e480c5101c0c1520450700010a81c1d95502c030380e060140d00983c42420240103050590404040d40c116000e0503029109210001820001e6070260900465a080195140208007900321455200f0ba502400316800d080208a0446078244540f00d1801e0095000300d442c1c07410002008160b4802900042c895410404103100495011084603412101103400598880d80f60f1040500e600d14800140d582d41c080003005410b002134804800e00c6803600f00c800480d950305158040d19007034003600018111400904d18409103501a00c0c1c0306c9200c24816010b64001c880c580000203180c42000c00e0000140c00100342d0700d0480e0340902850500c1c13214618000750050504001c1603040c0103d11001c0e00c6030612240c0d440c288441803044030107a00f07019850311030455180c281080b01d0b52040d1100310010b01c50380c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 102020917 1250 102019667 102019679
    0xe0112020301030803041b0b0a0302180306071409220c03140f0103030e060f0310080c0307030b060613030f03020c0a050f03100c030f0905060406050a020c0303040303020c01060b040e0f01 82
    0x10072a0b040c1d96100064500710344440e00c801000341866030f81710007080310404006c5844081f04026000244540d42c1c0581e4456102d0032020000d40c0c0038003201c1c040d80c4500b05000d00a03401c010048111810402e007a03840f07001340300000c0c04080248100c8103030b01c41c24082c607190300305994003c82090740c1aa101800060045600040c080004a8207107130040918030040c00007d10564000c1c0a550f4004d0107241480c4508000541e1503006a40da200005a444070802c40424140500514444114042c2a2461458641800340d41004104a2084d10002030004801148a410344050744d04004000c412200130726010f0350b0707010200003151052902100010386441c04050b40758146002034003510460904003030800150400e60400024988c45804820341607203c0c1c451801c1c03c500420050040341014144003003220700180c410a41103004000d11648444004112904568107240c01691440102c000074010445a0802c240d05403001800180020000000b6409810300491110b003590780c0351 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 102022167 1250 102020917 102020921
    0x61e0504140309010906030515130209030601061d040902150705160801060f0909030e0316090b04050f0f07030e0303010f1e0f0504020c011b18080a020904171204030e0112 75
    0x3e00140c00540005018407001e4030075000182c0114013107501d01c9031031080600154003101d4500301c1c072450503408030303400c8009d240410134a801481503082101d842e515003c20490040f030101c030b1040c00b0740d4481c10380e281151a40b40141d44110805c0c51040e89403415807502c40c1d169012458100d140702c4e0003001c0450025410300c00e4008403401c14144142c00f0789001c61240152407202d0f01a0107000c02c48504588544044c40325003070101c10850a5824982812946411641094000b2740682d10700000c028020388510030040e0042ca207185900d8040d5200c5004502404420702041200d00000c0300010380a50f160080f03c4c03d031000c09103011140c45500303102c906403901d03e1042c1556125a03a0003000a810300e43c3c010a406062140040b801800400c034000030842c02803084400144682c5207000729402c81c2206202401099000d0b00c1c80c01031a40007c3e02035900904054268440e140303900300d9400c5034004a41550035100c0d0070501d60701e45400e02808141c4d90090080c08105130303c1411200101d14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 102023417 1250 102022167 102022177
    0x11b0512010911090a0b130e06030d0e031c080601120e070510110304080303060f03030703051e090301090b01050a0602031606090809030703060f060501090303020606010309061e05041403 82
    0x40050200d40d80e02e0494014041c0100e02c200034544902008203010340d813a9250700340e01130102100955030780e80c084402d40f004040d0540c40035801181070300a0041c0c950300800e030401c0400f4586001440031115100007800c25020342e000400e0890400d884491041d00020010710500c001d0b280c1e016049010207040080d00c400030b100300ca4503004180e091061b4903020441c07441c10081407401000040d4030140c2a461640140c00c41803040d4804420014a843c00103070130b601e042015070103542807103c541e4014201e0b0241100c40c145640c5806c1300c521181807150141d40c000d0038024028081c4078014100500f080d00c0078041c3c2405141110800710b842c50002007144d814071a13503440c460050400341c071031000500307198038119000c0708104540c0e10550b4003007001001450080320005064820100040111640c0d0780c060b074144032080000f0400700b0340114003968000e1081c20301107081410351a0450040c0501c0c0030700c45510ba010a01809002c00d83d5104c1440b5921840010704d903904501807250780e074020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 102024667 1250 102023417 102023437
    0x31303110405070f1e110f0717070308040902030c0708070b1806161b0c0b03090f1903030b030c042313050a080a0201020c06011512090809150403080a02011b05 70
    0x14441161346202c4c11144003004081d46850320601b9081d100c4105801c0c0400000d55032425070054800f030006030b03941050011114000d500074409141317940c0d540022401507100d0700c49126400310008000c80d100408850140740d0001c902903883c0c00382d1601090315002940d019210b0101030154480c035800c0018040d02807038000c2114040001c0c0d01d0b03001c440710500b007a500000354400c01822000070320340101303a801070b2089014044e1246080921689804885402c41640c3d5022038041e9001401c00c00340300410130b41614002c41c0450030b0801090bd40300388600d05507006440c25803400508088a0600808031142851400303d42e100c401400840d04c140490140042d008240401c00180d40034008200841e1140005410700314604003403820408244d001c10405120b1030001100194010a0b0700411340d0580d404000210807a25110380c28091250724600a008040300f011001c5482c8050302c000750750000d40e0341e0f038951000e180280a845071548240c400720b14110100032a9008100355512007003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 102025917 1250 102024667 102024677
    0x40612090b011404110a0f0807051206010e041407051305030c090a150806040804090e2e0603050303130b01050111030a080a1b03050f09030703050714031303110405070f 74
    0x10911800003a1207150001055000350703205c1c11000d50700001400f511040115882d01050141c1c7c0c43e0000d44969402045582042006c20400c0704102004124581040c0c0038a4030709884580140898000d0140d00f65259120069800f00b10141c1d6202004001d08a03035600390094040c1da400070b01d9036588004400315441003120001800307024460380f20224104c10070705d031100843e607266203c9041c12001c2c0ca00361a82c0740009800c2c03080000c50b0007010a42d5409100908251b10010529900f12400ca0400141f0191140d845620180700b0340111001d55046020399640f420440e5100740f030801c54402c00c039250244da0000141940c055851050400c40280240d490404031240c00c40d25144000c0040c05902c4d640c4e5010011100c1141e081080f42031681c03000241420036803107140c62244028840d42040d40f0412440c030000c0d61120983e03240c9580410018a0300394500c40d000c2c2103004100b0704005540d20341800000b030146806420310504001c1d40d00b0802034a07140c2045454072501240343c400300f6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 102027167 1250 102025917 102025919
    0x5060a0b0109090b09220803070206061503040f0f1b14120a050619060306020a050304020a090b010219140327010203091c11090c07061401030f140a1502040612090b01 73
    0x50881c0603c0c5d441b003403021414481900c0e80c6191054200381e81220060b480307001003000ba8100307241c0c0d202c1c1c1242d22002e12800c503d406d50300d070309002c03030803810090a114a191804041120040b5100c80461495204c200499110b400c89181d03050701030707980b51040203c44840b076110080130840d96410b913000340107001c1950700c0c07514030b9540d01545002e116100b81d550340004045031591018003400503e41c0da0301503503410300c1e004100300f15440c2d03000800307403524108400c003a0382c2e000140f90541c040c800f00c00300480001c9003003902201440a6508016000016005608200013500e078010604c3e4803403e80c2580060000499030780c021901d4250300020610007680d01102c44000006140d40700d41241410f003d02840132031081141074408040c050070105440c801c001180c01030040001610f8608034a6600d117440c0d40303d1400c1021400f40006800310b128030010786041c805655003540012044c80860340c0803080900a511a10507000061480d00011089081a0142c0040e068100721070003880d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 102028417 1250 102027167 102027181
    0x11100c0f08040302030d090f0605060901050f0d03030905060108072d030305090d1a090c011707050a0207030516030b090a020f0f2103120105010f0c11060705060a0b0109090b09 77
    0x140c1c00c06401901544424401d817011800e0324007031a10405d200f0a520316413210149000400e4410207031036244601c15140040c0020340715613800701031841c001c442401c0401034a0a00703400034000c0c1c0700081c3c02030141100100d40354000191200807103114140880c0354098404031014001c44e0b80c484034618007070030241000484e10a8016000814004142c61070021342035407000840d1032019000814902c4110400c1203405050002203c42c403020b00f820703031000090680d8044141c2000b02080d0a021011030038030040340c400c12401020756801000c4480c2ca141030f070300b204c00c00703962440700319000b12104000803040c1c84085000c2c0c6607103501402ca0740e002d20303004080100c8002007109480d00902c6000401802e00340171440a55191240740280d0342e5401462101c1840c03803030581010f4140102c9411b40214a84d101c4452104070b40c0040d055036a405603000011882e10650070094105d200c0c26040c40720184143c1d0160140003070989030205107994612801c800e80f040b00500301d81c4070b684d2034006800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 102029667 1250 102028417 102028427
    0xf040303020c030c010501030311010b0d0213020702060c0102030a0f11090909030903120c060106030908070641060102120703080a020f041d07031e02220611100c0f 72
    0x10a10a04015080a1080848038a140c2120841c001c0c0c40c4e442d84010800d00d40c0101480c2a4581850000c0c0103000c1d01d03d001c2014009800c40081c051018085a4041c0c0111541a28801ca900800d401d0b610344d29413071064040c3d001a500e40b10010f141410b58440c40c64180b040c6009441d0321400d43d420329400b082048040d1200600251040c00200425035240c0e4007440b0074117402141d0300c03040d515911342215851900c1c4c41600400145440c01002c0d80c04103006038147e072100d540c401c00100f5040c0c81030490040d5640c25051981e024040301c41d00c1940e58010098100b034400081350303003106690b0354000481c0e03074141100744600240030411140c00424031030110994417007000307403015180046510723030301c50281c0c02948045140b13250080084401c40000034000e801204501e405c0c0224803000d25080c54154030544600a810790018550307202c440c051122000c1c0d42401d20312159049e5480744080c0c016403c0c010540c80ca80241c00a64840c0c0010f80701c0e00134040c540e5a02d031807003041b4112013516 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 102030917 1250 102029667 102029671
    0x4032a030f02072606150d021005090901030804030615030209180a0b01150807090f05060901030b0a03080c0c04090b010317041a040f080307050c041109030a0503120c03010305060f 79
    0xc00c60050703600201d990140184036542d1804c1c103808002d074600d810705180d420410003804441698030b043d0000304003552010b07100058140c0448403601030800b0070006a5841c8101240d0907040f82d401c0000006101400307001d441120f0140100b441004101c01050840c00c0c000d01000398000e40b02404100061000b100e8004200040b00807900303d84020384810446100036445046030b42010855000032580c0003901d5900440d6501b0f09400c204e080914100d240c0c0795a018035030040c0c0303020079156a51380c4a9040a004e03054064440b018080e1a8182090340c5d50021411511070700c10586000103a081901c20b26149070b402c0f85255005900b0b6540359901114111554001c0550074070010030704100c0442040c040c0321400400ca03903660300d030140d05032034030b5810b40c400b0089410500c0f1203000315202040103145484120b400040219503841480d0303003030007198084c58040c8610340c002000c01030004014050240650700ca40200c1d516444542d502c1d100074000107103a0b40151000c13880413040b290800da = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 102032167 1250 102030917 102030947
    0x2509061205071809050a12030c1103090105030403030605040504030e0406230402092107060207120206180312040b0c06100305070902030603100906140901020c0d0509130207030804032a03 82
    0x31a840b0f15039245d952408007200403c0d01c08010344441c1510303841c1c0610490000060341e060410320032151200c00c682b20302030b00040e1814060b0010008003014800d5000401070180100104454200b03402c000b042d90801e010400e008a1504070041041d0240c01c41801100c024104003001d100f01c51401c1c003010703410080090350420716045000c42200f400402005504104000030030401d881c100000345064616400030040702c00f00d42c4054003588400e0304403a0403507820100d001001c1c10340c0012034600200e427840341c0540c0801103008200842000020f068054030703041100c20648403869410121841c61000078800c1c4d0045200f0400d140b21500030710b6101c0c1c40102601c0130075000010103000d86d4003c0d0340032503005135600e01984056200c180440d2b0044c943d58021420301c0c540c07488550341c0e81444160581400804620391941d980c60039050446070403d002e00f503441d00f5007031a02519a001c240c80840200d41c0803500c1118072101860f0020282c500782d98650b42e134042645007516244e2540001c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 102033417 1250 102032167 102032171
    0x100c0f02030601061107060c0206030609060d0209010b0d06090c1e0e130509151005120a0813080f0102090a0303050904021201030c08150f15010225090612050718 71
    0x8000980d400b03218075030080406480303485104031320001c0031703040003440e4104009020b2100c041a015840710019694041402d94101d549600c541c03000440f041c03061a4000d6118070701c0710000c502c000111011704086450130000340940f94482420074242c88071840f501d000203030a46141d020000708065500a9000a4142804003542c2c2e0170120b8044008803e007072031b0440d154000d00c201c0703000c100400b4601001811b0013104d14103200000b0506800c140c03050038494007411007050092407040c8084130140d40d018406941d80c050540340e00c10003451510400010780135280700440c01c1807040c022641c0b0020000e10100e90039082d039400b50740c680c212090054000d98248080f0304110b0b200c070071981c0a580100d03480000a468001781520785140b5880402d4400c1c2c0c07072011711010f10001c0750240d8105820001e48281488500c0c0108c4c98840742d070b111030f208260100208000d800819603104141d4860141c10b2003895210720f00c4019040050400a2550784a0b0204000d409500e081080030f8011680c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 102034667 1250 102033417 102033443
    0x29010c0c0e040305040626010504020c030c030d06030507050a0b12070c0203010f09110f090a050403030207050a03081f081e0f030d0209040e0703020924040c0e0111010605100c 77
    0x10584201c040b203040703001c0f840c0041e00340041a000060300382c1c1a4080d522a65201031b40c200705401e22441849828050341d004640d0300400c2105000b030b109440e0000c400c894440c2103050f402c1002d4076251105843c0c0c0d00401d000030075542401070b594000d44002043d11440c194080001c3c600954006007504104007039550030000595080c0944000504441d074007140c0820b250501d02503100f00c0c1c00c1541d00c1407401d54402000e6480e000c980c0c56111280c518000703110340e07035410160302a2081d07004c000c04600174900c102c070030160050700b400d024620720084035102d490a000c3d8064074103c01d0060624540c800620610413400c0350552484101402003640d030320f89011208280703150800c290349000300d42c010031500000e041920844038444280d500400409166030081100c0d900003804501103c0c01d10244000050300c540d00b80500c000002d8010046070052480040800080300e0070180082d642d80300c0250008014000c40064810041084038120340d4442c06071359004503032501312494000110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 102035917 1250 102034667 102034679
    0xe040f11060703020a050607050c07030201110709141501050906091e0406080127030c020d03050c06010b0706150509070e01020709060e0103032a060902060c10020c0129010c0c 77
    0x1504010f0f200307400906820078103262103400d103d0001d108904005003806015420400022108122034082c00d2124650303c180e5500c80c203040f416000321810a00b030040e4103001c0014100b00038130807010b442e44612101800310045500788940c0110a5100d2010b100c0720020b1304e07007400c00720800f005100c040079400c0c01075000302d020380c1c2d100c0d4804420b81c0d54803850400720916820301c60284210415240d4001d0f20590f82c0908214039480010340110b01100c441c2d0201401001150401c060360000c440c42580d690050344041d50140c0b070700719a55802d0844400b04100c40040c507109980004041c5041aa0b40380f10444042580c00382e03075411440380240024808007540f0982d0050030041c6a480f999604504003c0c04640d0303454003125841c501d0244038051060740801407800030b40d0240c0301041c0102a1b000181442c01036a00c00d00c414014941e1860310380d0441d5006003d800c403814000c0c0a01a00000313524809102059041900480040b0070041580b0800884188600c1240540e40980c0c51700 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 102037167 1250 102035917 102035929
    0x71205120c04080c0102120a080903040f08071404091101110114090106050a05010206070905011206210b0a0c020303150d0f1a0c0c0a0201031104051e040b030102040e040f11 76
    0x10340c209451020000b014440c03e1000c2c00240615002800100101010030042007490311440d2074800400c06960003040c01c9640c24400c4500500c51003c0d00d8403d5130700c4501c11915640d80e4410080c0350081d85001c1051401d150041800c0140c12904640091807150015113080d503500c2c0c2513090315540c4003041c002090724007605500030100740c000020818141700900c00380fa51075400041c19940110100503805a01c601c40b903040c1c032400e103000d1406420034503014001d4185c0703801c5103950006040281e901c0c3c034042508002030b9801071401c225140c076001c42010442d0200d100704030040c0c10420008550100b400750544444101511089540c0550f48a00e0010714021000700c0b1403000141c50f102000d0440100143c000514144040c0340c1001185aa0780e105d40130070b0f0081c1030507110300340484110203200a9400134000075104130091801032a14028082e80f60b5241c038880c44c0b400305848100e080500c291001d031855000402e1142d03c0d0f94480d0b254041135040102c070f50040c40c5403060384c2902d1741 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 102038417 1250 102037167 102037171
    0xc170606040519080c010302120106110304030204052415120c0415020a030e01030c0c0b100e07030902041d060105091312030b040e1203060d060e060717010b03010b07120512 76
    0x3e03030001115a0902c48014144900e0414007070400d170041c4030300c2203004ea840c0c50b8141100c8e40e6040c0610035900d10181c541c114020703503001943c4070345080104030003151130358850003260488415480b42c1c50404c5080200c0d10b81c00952008640c08140076520607400e0b0076003000e400c150795180c4582425520380ba10491131301514090801a0041e0030300404254102e038204040035006d00b01880f84140a00c40100f82c815200000380c51381d4980750114407019085103464000d03059103900c020352440c08841c00382c0030741007014040f40110b1412b02d1400d00307202d2084641c010400c10380003a00181e46000c1c10804002c0010b452604800c1174902c00c075000404000130521b031040640c60108401568400300300480342050b01c1c034030040d0403401b0440c0354440315104495001c801264080382c50740702800c1801c02019026402912880707484244803a640c1c10000c24041e2000303060102e109aa200da0321041540002c2c410082e07c071105122500000d903801c00c008150780810b00d041c604112407406d04403086401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 102039667 1250 102038417 102038449
    0x20403030507050d0806090a05040f050f0106080c240307090b03010e0a180203120c030409151703040810020a031e0b04180f0f0204060803070b09010c030c1706060405 73
    0x92207804202d028001071080780c01303030309209a031480c00e20003189629a00030040c1044a641e40005010020a0165600040d41060445a070180071881050003082c143c000d51b0401d10030124004550f05c2d042172a1a42c82c04010800303080c3c0703400301611007403d800240281080c0f04440c0d10209074601084065402428035071345415044c208602c1c500100c51445810010f2325050761621405030b100040d00000005100d8000b42d0307103c10745442c003800d60240e40c0001c0b000d01d04118a1440d4103035500c5445e01901d000901e0304858001901207a0307924844c80c0304e007401c0d42e00107118403501e54a40d940035205141050030702240b0308203c07100c0f4201c4031000c0494855850707951044080b4900380751007451000c0303000807041075904226440d20640580134102c010f284d200358a1400c0c0454580340c00043c000c186103801c590f03d80285181145840e9400c444140031507103400e01c40036400f4803a00811010006540304c0e4084001c0700c510700410104002c2415802280400c8000359903243e2500300da0540c50 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 102040917 1250 102039667 102039677
    0x304080a09060507051506060412050606030c010903030f050c010f0c080405121602060d090b010e0f0f0f07030c2001060306111213050a021504082b0f0c050102040303 73
    0x100d1000301a1210040c1d4000004001c01401000e000860001c1c0781201d194614168503400c0da40d91001030940e00c5075403c10081254134074052020080700150b014007407031040703091713032010070b0304100456402640307110160002e0f41034111290154001c20040040c00003080010414400401c45501aa020008601c00090510003040103003d000d21400042c220380c0d50342d01d1300c1d00c03040c0b002c82d50650680041c0680301d260002048810710010b42d200d4a0295400826440b0f1980e4946000c4803804040b0784501a4180000018070101d0340c071001e06100d0000c0a012103900d07212100202c00a0024043d188148014440c000c00280d024814409501c240d4400100c0c41c0c4e819031411304255035401d01400c0d03a0002c1400103006009441e003d1944c4400c21500b400780b14561400c01625240d0b1403203010f900b142a120b02040c00c0c0c49048010003e5541500840c4e9411001d2140140d07480c0c102d4000000b01e400051003483c443c0d11400381140d00d0281483e0010200300151603440c00c984c8a5401200865 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 102042167 1250 102040917 102040927
    0xe010606080f07031506050f090405010b04061403010303050a032c07150306050307060e01050d0c050306090106170a0c0905150408010c050309031e0f030a05330d020a0308030408 78
    0x40b1001441c10b61050f041d242c1880001c00001c151600b0300d01c01c0c02840c00784075012070700006841c84001175400d00c501c010306c1070225507034840c1d4840c000d900034029440018040c801d0050241e00036021a4100c0350306070344d414500314071028100d00520080789400e5410a041c601404070f0540c82c002c025004c0705031000f500c000d0b0301d00b200101e0724680d041d5040c0305042c00c040d420052a86c1c007181460403140d80c1e040c8004001c821500480d09032050304617001005240000030030400364000040c0d40318020540d031014440e621a41c043d02d40950f922220688442e101d80001d80c00000e58100c0b0790f9042807801d051003601e48940009020300030303100141c8190080407800300030f03902003400381100d86259030400b5031450400340c01a545a1084042800d60b110840002211a84a25040380e107981da8555126440b818411515000f41000781c6044101c0f0307000c8002d8400f0710030340d1003182d001d10807110b84d41c41c150f2940d0320034450540704100003030341d1041d9900000004038990b080154071652040442c04d42d52 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 102043417 1250 102042167 102042181
    0x305040801020705060a24050607050a0b0a09051b060d0b030c0d0f0606140d080a2a06060806101404020c06090601060f02031309020c010e010204080703020102010506190611010e01060608 82
    0x182c0030002d4203ca25140184500c84130340301d5461807c15203500b511416600c2c40142082881d0081c2c010340244007142400804c08442d205a12000d2024841c81c01d071500d00c003840114100380002d14074000d50006003000312600c0414641c1c400d80050301c025040d5541c42c1503601c00503180c3c0c68020f00680d03401040441c804101712552248202400e01070b070300d100d84030036004003240d44010003410007001c42c4c0b030002c2e4450702a40501581541c0c117201c486201c03071506000c1c07109482c008541b0ba040b6130841c1031150101e0000300101d15140311362040c41000590900d480c886000741e8407017202250700140e003003003403640c4000c083c8480c0d449416403000510055140120081030500c90300e84000031034109000029407080401c0e400300444800742d50150b01c8240b800c408600600c0c0403041c40301c1a41c40001d00045403480410580c084130b00076002001a660f40b0340600104c135034116004200b40c2d45d03d420030303c02d50340145d1324061804420400000c100c3c549480716406c40340150051001f06034040704124034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 102044667 1250 102043417 102043421
    0x406061715010b040b0703120902370803031902040b130f1a09010302030919150b03010612030c05120c01050f01051008040201140d050f0a0501060507030504050d0305040801020705060a 81
    0x1080920722251826261105c0c1070164003940700c000b0100032540141c1d1903010300f070760403003043c864004081140041d0091800c40a004007500802454440d0301040140300110341c803c04c0c1195843e2f8091807a560b0340c00001040c1e40e00142010440c03036824040071603089a0075002d02014500c864807000d12600f8483d81e4400b01c2c0c0c156110300d0b2800c000140c4129280411b4003070711801d40c420b00b03001d40c403a115032003c0d60400385001c2a20f01102d5a44080d81d0501080c010551030b080c14001b03041040304408420315090720700a01440990710001020980000d200300703036a800d5640650140c07402c0c1501011030340015800702c8001400f9a44070003e00481c100e11140c102e006040c110f94404a944003080c01401441c40208080d050004c140c010381031b03856007907040310070004c41010200703c00d10b0700030201404c0d400b003a10110086403910b0004103149005508032581c130f9030036407681400c0ca0310301402c0018001c2e902d80300b24100b00b81072100240071a002d001411240703100d4000750955282045110b02 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 102045917 1250 102044667 102044669
    0x9030306030f0616120b0409050c01030e070609170c10050405011e0c151e020403060506030c09010b0a0915050307020c040b100c11060705060108070e040305090603040606171501 78
    0xb03401d03000380b810b01450301041c1481c060742d100c45003031900e54904441501001005298800c90f0072038107100f181c0040081c0403616042c400c030309803020400301d01031205030341e03481c0b20a005000120b240c240c3d0901c03808081c040410003070307840034084980c0c0501e101c020520680d00200e82801184c00402e042c0a80d42e040301c041403014851003240c8443e0800d10500a28501200c81e003d0080c8147c100d4030182030589801480004040c00d0360300302011100c40c0b984000394000d03c81550101d00d0a0b0101d07080e890045804204980c004158403050703400d055a5801603485841000d0a0102803040081c0300c0d50205485541c1803042d445003074a92400d050b029051a0700e038040540b10300d10b00070182000755280208198952a64a03018030518114540303c0d10081e007030580d00b603104101052040c204980000c0d454142c4803000c0c01da40f22207075541c1031010f07241015500140823410500030041a82031036409160300c107028610104400c0d13030b65403030840c8800d0400d0b900b2140c1e420182d000345024108a0800b4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 102047167 1250 102045917 102045943
    0xe0702010b06190c0221070b0702060316020c09070903030809062802070f060905210a0804051906020306030c01110309010323010602031b0a030c030e040906050903030603 75
    0x110441c50340400050607481000c02080900c080706003198006441050404040c56002c1c0080032075020b444c9110705106514a50116a403080d03420108004206100ba140c0403030307001c0e100a00710740300d541d8941d2808240d00501c5046124085042d14982d5072603407218041c003a55110004d00c142103040052209070024050615175000741c05000000e81d609400840340c0180d41c950414061800344660080d202c0d0200c05818455881c114001f88003040c1c0c00600801c1c880c1d021600212443c1d07140c0300840e805510390300400c503000c1c04810407a6008080302a44a071041c015a11680640020b4805102ca6000c06071403407503000c400c10000e1700b03080042481d00402403c10f881c402140e006565604c0c400d000c0c0d0a410103448421000030714208803214040502d24500c001015030311002c00946d01e03008103a1b905401a401340300d200801c0d10105d001c00300650036590302d90204126032000e50f07488031150840350700299140d8140001c00c5c103a1160741e01481071071010390760f43e0070b000080500d0101c0f950040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 102048417 1250 102047167 102047171
    0x9091104090b071409030709021b0601061b0609051506100504050d080d06050d03030e010c03050115080c0d02120f01080f060a090201030b06040e071106060f0409080c0111040e070201 80
    0x400042104200c000e0f600481500c0c3c003030f003c9900107003118544e010f030040c1507400d441015000301d041c54207900940340e00c51500b11a40d24050344809d10940e18107003071040c400441c9078000c1c40c0551510020200030402c3c054480800c000500d9900d16181c2042c2c5120007031046000c00611005240c030310041a8040d82501d400381c102800d00340000c0110b107400c00d0050a100d800a1006112422900540020240244180b089030047c0c01c002c0c0280c100170358141c00ca546840e649001c514080d100300c9050b1003200d0504200d09500700c0c0f0a8a1410300509448007901040c494942100800d000410814502607a4541181019400100b0071030060300500350035004650704c00c6a000000500f2580610b028002007070842c0a80010780007040c21164103900302c440020007140c01d85517aa03840340100c2265035828210034030a90740e103840e82c2090710000d030b101440d0404684070340751642000403500d0050340054544a40006441e085640704040d03800400ca0100b01041101154070b04988d0104650000f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 102049667 1250 102048417 102048431
    0xc020a0e150f0d0803010305031c060614070c03140109060f0509032b0c0806010e040902031b06130603090212010c090b0309030d060f050a050a05030709021606050109091104 76
    0x7461644a024061070044036000d880e882e4a0390741d0800804542d402003420f5640756128240980c80c2e910401c548102c034127840c3d902080e58407941c4a071804035902644c0d221145011030425604550000c2010780e41242100e1012001c0741c0c5128801d040003804070000a445115464544141c40080c0100202a450a0100149140c0200c00ca41c0c5048207280c0b01025011040040001c1c01000508071040c503141c01b000c0f081050300007140c0b46c010030090302c0311103003610308400700402d6400084000350142c1125000c801141101c00b01040c0ad16402044141403079040f0804a14501c40341c0c1c03103080044c3e1152002000d5003800c010000d02007031000c0091200310b0b00d4580c040c040e507241d441780d0354605000000140050406100b0303030703000031140101031084903581e040d82e66000703405000e0a0310842040740001280c0ca82160031004998001d400380004a2815000742c0083d007184003c0c154440040f62614001011032044c0f501034a04807900280b089103508206412140e0300307003110300462801c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 102050917 1250 102049667 102049681
    0x15080102040f050f01120e0d08060907170601050f0c0106030c0e01030803040206030c0f07061b050a14030a06030506040b07030b0d0b150301020408240a1e0b0f100c020a0e 75
    0x41400181c3d0f00941d00c980c007002c46100102d074158000ea544d14041403a00804100c220384c0898400c11841030760b40d5000140d12500704100d800a8241c44413804640d2410200200f001e210721100d80c0100e0504240e8209105010300c0203090707110b0300002006964501c014802c0001e0308494038098690f107405003003150705607a00c4650380c0c440034101034410740001c4006020303448524111440910083e800589600191801001514a501c016034031360b204903421421641c03140c009d8900303000b150355841744c0701812508450003a61000d803441034490780340c82010001c54008c00846000394412415929585440d120084c11100c40c00d0042d4468002d0b90104004500740d40c1143d50002c1c8241440b8801a0740240003e00900c5681e101c2071003070003211110040200c078000c4a10416401b044a5035840c0e80303805042c070440d200c0704108003039003a052404402946090748005648807010782846544450500050000205803480c0d40020301100544402c50812000520007060462400c84250502d20307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 102052167 1250 102050917 102050939
    0x30e0d02030c16060203040902070f020a090b030c150403020405060d060213090f09030c1211010e0a1b03020108010b07080c01020d0c02010e0d0210200711010807080603120f0c0f011508010204 84
    0x1110b5070080d0727078004c6034827000d00000602c150502c80d03006000000c000c2e0790b10a01170142080040b15840380c000c1c100110558140f00004c8010054807400c41840c1c14256400c0000500c00500b40d04e42000090165100196240c4002d03e0f040ba48600100000d070f15203110303201a22590460300038a58100011100044e130080c0d00c6850f62580000e248007082c0d07921904450003040032418135915820118440f00c000d20200d00e0104d00d80c0104814142445a5070202c10a818a440003e00185500004000d030312100801381120070710501d0201d160a102c01a40c41c26078008041100d11141e4030480000c5403030302442901c5055a02e0300c0501034034854050003035107400b4a403074009561503d45e59a070900844088118481c1150100304070b48074009801e04801d0740640c038100c58042440d0b640070454060045070000e108500041c001c044a075480c0104607810f07003101c41c40c014405d50a10071080a98814000f03503200001000000480783d54600c02d012104070750307078002881030340b04204c1440584540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 102053417 1250 102052167 102052169
    0x60a0e100c030903150e1203090c01051908130b010905071106041101050307021e0c0405060319030f050d0e0609011a0105071b050a03031d0a0503060a0c030e0d02030c1606020304 78
    0x401200401405d5040e101000340c081c0b21010806d900034240840200c801c000043c1d03000d1030f402001c44009111032401034884d842290010188100110400114079100e4a04942d000407242c070050007480c81c954698482c807c0c00e070021080103454204000010f6842604403101031140001010309040c292540c100380101d03aa2000c0c10003a00000081c0710600802c080780c240303c128454040c50000321110710b510341081c1240c05210390b003000c005c180140f0300041d200d90021104900300301254a155005d503100c0756005800c509012045c082c0140c01c0e01a032207041c1410805402070f200c0b034a41100c0d09421100e95508482c2040440e0000010503680002501c1d03070356900500f0842102040352452003c445184c0c000342c0d0042ca020400b004159008803540c000481c407086031010115003004000c181c5000d0b0003a80e405911030800903846003026040748960070880e0034000b401a060305449410207441ca004030001d41c5c000906c081c0c44c504200300c0290850307058500500d989082c203400039202c0c851 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 102054667 1250 102053417 102053423
    0x70b07030504170403080415050f040902090a05060309150601030606091e090509031306080408090d020a090507110c1206010303050d060f060c050d0314160e060a0e100c030903 77
    0x140d01c00107020040450642020000040c0103280c86540ea80b828a00e107502c18061110404400500042194004d400f43da030035003410030341941081c2c102011400207420102c3c56a40c040d008002c0003810780c845000441c020150030300034140102400c0848580c101c0c01500c0d6038109031501d0b5007040f0f0540c0c004c00c06001d545522844c07084030901c1500303e2015a0381340e001034803107520f01400e1143d1600300000030800b000c8036082c210302d115a00d40050741d1060007240e014000f42c030308002d41003075464156480c4140700d1000f4001e072891070f101c0d410307041114000c45284010500d4920a85c0c444402007010f03006501c4201e4003604131801405100c2d441d004103220003018044080350308001c0e0724040c2c20090203031548507a007502c915590710f00244010f90000040d01c0710f0141ca5600b150b0a03109000e111482544c14641d50115100d8000190726040d000808104020b4415a400450b5a8881c010400d400040c0d98034000e102c90802040580340c181800ba60510080c031004200090704410000e04980e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 102055917 1250 102054667 102054671
    0xe03030405060c150f0105090f04080306090601120e0619051003060e1011040501030507020309010f0f0e03060f1e0403080a02030709080610030309080313051e0603010f08060c070b0703 81
    0x40003410a030300c0c3c11000b440d82c0313107084d01e20002c0003403006000000c2e0381252001c458141d0a9140d00000c98001078041c1ca0181a2004c00c1001880c03e05102e459540c200006142654500c2007180e504021146441c03103c880ca90008010302c5545030075400c006060000c00d110411031400c01003d5007216a0300e82c070004111300e440328200d035169601404104403604090509114900c1007120440742580b00d4003131540031928120210302c9042c40002a42d08681040e1a20013610812500135500c0d0300e8081013600070030140d5555121503881c2401a240902080c9040d04410308200e102d10040d042c8044105c81007506d1501081b000c25402940c09411449140c00181d5070348520000f00c948941c644c10001c03540c440c900030300801ca01c3c0810740c2400c4a0084e501c800f0800d403030744c0609841c4d21415031071515108440c0c07400d0000b840e081600c094040c410420362601d00f0300170000306000da0002da12881030010003a408100041c02440105d070300945036800c4074035000050f5540c0c082050b02074021002c04da = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 102057167 1250 102055917 102055927
    0x11505120a0f02180705030118230903131707080a030801060804260c0c0a0f0302120304120507030b0f010b070605070c02030105270706050a08090709020d1b0e0303040506 75
    0x144130004119048900c0a0031440c0525184038094003590081c45902030021003c08046c61000540c0715035940880ea150707180700c031441c608031509040c21004d014800940400c024241c2207299000341603008014250340c005035418414142814100d0329030200e00e158000c8222040025401111181175414609008040d5200c9040241401285100c00140c80f01140b0b400040d68882ea4007416000c410344089406184004080c400102c0c0c0c0f622500d088100149400d00041c500385100b0000402074a007141e0805a50b01e10060301e03140c01d51025500d5801040c001e10501050001c05075221098501a20ba00c2d494078a2402c6140701e0140082e0031542c0d600042528280301e0301008480310340040003803026043c101001c5907c2d00c040b0301030300440d026045041c3c03903010300032400b0012541c0f2034a40505249842200380c401902c0140b50042a000d110408101c0d02d0326413014200c1d13002c64040000701205028801d10042d030400c2035440034010050700150003580e001003218103036a01070f00c100d903e030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 102058417 1250 102057167 102057169
    0x4060f0609121e060f090b0612070602030306100c0b13020909030906030414010e010c2001090803060108061210140f10062f010c0305010e0f07081b0c011505120a0f02 73
    0x81c00e20007a0405c140d820300c2e0140d014020500c00d26409044201d5812a400102c2900d543e590402ca20070080560402c0c4000360040c03800868941317400007141008085002c081d074a44285030001c4528840c0a28000155001d504043e8081c0b41c2c0440c00200039442d0104c00d200280150000030001058038585074000c0c4492002074006154400124000b8403c002100601500c8000840942034074141c2c03138208020240c1c41400703050060340d00400c0c03c40c0365480e0000110344d0303080000c001d150002a40b031080101e0200170400c50066000050b400030b010030340c80d40316144800e800f07072400c01c1c901803190070300004140240700c04003120241d041450850461001841e0460280d0b0784541604098001c1c2410000c010341001d41819450741d0100302507070302c0d29030144400000340c420201070190540022401800340d4041a00a8400841c841c4c00c11016101140580c0c04a015282d0a9444500c20340340c8085045641026100803140543c2d107200c0012103e6a40380c81d02405404c02e45000340b55015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 102059667 1250 102058417 102058421
    0x103050a11130203070c0210090e0105090903040803040e0f0109090308070810081209040c230304050c061c0e0f0a1b09020703050c0705040b090105040f0b04060f0609121e06 76
    0x40b00d054103066440c1d1402120107401c1103000d113810390240c58034800f14210288212440c40c180e40e00c0b695055403690030304c810f000c401140101030f41e5451104100100d08540d040000d0402040d0300750201d40c1c5460700326107009015606038809c0c8620b07801c11940e540040c1d0002882d03540100f07249454142c60ba506c0b00b024a01519035448101d05005440360b030402c3e2001035000b031000c18001d440602c0300000c040d90444070603150390a200c041110000414503180d0251004641150041007242c000c400b040300001c4003030340120709850b1036030000c0201c000b181c80c6a02424072100356a8016010202c8400c00b46510b0307460b9090024411010030300078440510b204107210019141d070f141c0031900c5840f03e00e000362403a40b02c03181c100c45a1082c440d0003e40d81c07606004a0b4042680030b0441d50300c592030003043c0b10181c045c254844054540398603490b0090788982c41510020580d92005211203450070001402c0360a50340c1202800d00301c148000c9e40890300f540c11039102e45d0032101030318010440314204500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 102060917 1250 102059667 102059689
    0x151209050106051c02030616021f02040b0d0219020c10030b0a080a0605010303080906070c0204090302010207061104091a09041209080d080a0609020c0703060c0e09131a0103050a11 79
    0x79100040d01102844d0102c80340c1e82c4d0504500c2a400c445680c1c46071000320001d07400515221005034000140210003021020341101c6000041c20051700b055118405c0e01255085014548055603010810598101201361041c0707200401d40060020a4040c5012130700c2c0e0580c0c40400d5007030640750505099280c4902034a44000c200500036148003002c00e240130001f40200384001d0700050b440700081024504003040c024004c8900741c0b00d02e01f80212039800e01025002c029400c0d01907550130301080c404120300c0d000703e0101d40d0300c1421040d9a2802e1001c600c0c2125880b1005144d8100e810b0256803480d1181e08020b80c01c150403800300c1450480400085030441c030070360464850340c0114141c031035082e07030000826030142801501c2809006d441d44017a008900418441d88045d03809032500f0404105203900c030382400001c3e4900552241740c0140414007000d401d03034201180c150045001c0701848010300700500b03960f039008446159540345458169481212900151040e02140c07282030345a55600003000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 102062167 1250 102060917 102060919
    0x302040608010e010e0616080c0c0d11060709030314090607050a060204050a06050c031c110408060103110a0b12130f050a0213230907050a0b0a0915120905010605 71
    0x3016094a410455003c2d10f400d85038005598200480c41070808000700b0101d01c03d00ca1840511000e05130801c04aa03070007400f03840c4200d03c0d00e0401042c801c41105001d07180c1075400546811440104c20440380c1e107002c00080111080000f520f1003407000990000a00e031514021100035921003803408002101440354403001030891085110010421290781c02600031038904903000400f503035840800f681c003441501441a06500108001440c8426200700040c640810380000151410f11a599002c26409600001c1d280c0e40028010010048024140030350f407182034542c0c881203450030300600c10314092003500b07144400b084070014800c056513043c413803a0385070492021605030903c1d040c0140c0302c0082c000d0a0b40600c50900900717031280c2c482d0040300305280000303011300d008042810801e4032000c40a80780701880e00441c0d100180326598503a00902810010247c00c3ea15486d0480240c2240c2c41c545c448000d400e440c0740e641003e503030001504080c0035403614001c50100a2880d01c02d004140c150412 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 102063417 1250 102062167 102062171
    0x807030309090e07030b04030c06110307110106081903082d0403080609040503040510051204060204051e0a0603020a0c0506010303020f010e0105040203070b071502030108030315181b04030204 84
    0x38540e000c40a00200d40006200708005010001c1e0192104044d0202a01c02420b1001040000c3d12036040c1c02034880c014140010f400450020600b240d600035a40c25000408806841d8100b0300203100e900c0080001d04000c18030090398600302c0940c1340341204041c0510502e032000440034901c00c4040d0451a52114081c00516944110802c20f6002030750180c0019582c040012641d00742407401e240515001401103003483e191200300301c514500c3c000c2c1c1e582084010320402410b082040d03032040c052072180300d01580311402d00341400b03a1810325504070356580c80025041d41076038440507244015107415180c090303510030104c03134203aa0400c412100109240306102c0000240750f0301040c0081504003860007800041d189109140c01c1c3e0720107840180d8550410f01c010820b00720141c00520140d44a08504001400541442402c80e003099020342e901c0d42000003004922400606e04483c0c8203c11107a40541111901d218103c9810003440c40150140300c0341d900d09400040000c0d10700440e130003441 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 102064667 1250 102063417 102063419
    0x3090b0c0717030907030c060e180a0e030c06041202030a08040314091801061404080712060e030406030903300506040b03010e01060e0a0209090a2c0a02010206160c060b03070807 78
    0x110703c0d912000d501c011f40b146803841401003034641c442c080d02071424100410100140704c4010384100851009005542c14540d5908140344011303050018260705d00040016180510341400c08207205064400c0860031900108407130b40c40b2981001d40704d40c0050301840c000308690340c9508000301c1e42c07081602707055004805c90b90102d1006404504241604c4441d91902403090385402000b88070b019502413400580c00c2481c0500525078580d80304111107000700d01c08900c4100501400d403c56205421540c002034840c1042c0081c1500070345910500c001d4102029000b03c0c4218a812103801060546800e56480d0310228a455641350002030400c0b01c0207000300120012a00824000d0259100e08104a580da000242d00395503517100359080c0d030101a20b04007456403410012002040455902d01d0700c50903a007403480e103905000c0c1d84d1110001c858402044d58a80f01d0001900d0060020170400030a034030a40740449a5620100d02c01c4a40e511140c0410844014030029007002003c3e00071090314410640 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 102065917 1250 102064667 102064681
    0x509041103150f100f080307020603061503010f080c010206040b060103240b04061815050318030d050f090c0f1002120d09030906030507020c0d060f0e0c01090603090b0c071703 77
    0x21a1902404e1005800c00303845030f48024102c030040191041140d81d41040c03043c5405410904000e40d8131150043c104402c0005204407000640c01c00c0e08031201a0718403c01c04d0003101c00c100000008202c3c2400200032034502559035a8441d240100010f04140d1a40000c0409401f13003941222144404002e028007161614104200c80d0031500c00d00c400a141880c0c00003c0f001194080003c0e14884803d80d036030309d001880309a440391b0001d40903041d120340c12203141710020000d201800356582120008600740c00c010b04012181000505500305541003101c21900f00d0703a414403441000e240136102d4010502c810403041e4207198143d4031a5003075420020f8081c03811540d0f948404000c80c03181d1a02002c89072107400132021154101d80610140c0e11140c800311052808044205200748160f2001c03e0300c0c4500754060b001d88a40b030202c01c000c1e0340880304c501d007e582c110f56640054100c524040294148548400e0319002000d4000c002c803900000d10201401140001e400e05050074000565690030080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 102067167 1250 102065917 102065941
    0x6010e1b210a11070807080f07050a060603021e0a05121e0a020a0602031306120603050d020606130e1504020d02090f060411040b0307030c0e0310020c07080601050904110315 76
    0x42e0b0700d2200d07a1078810306814500052007550b003e079401c805d0560925283c0c0c6ea42688951088010203a40c8405004180018808020610b51a482100301107850b51541c414801680700c031004007160804500e075252020f4540303d21200480300125032241c0880c5e1a1408682046102444031010688910a40e50f1000e0001400840c8910a032441d2b0203d035030b40d0b10201c0c0c80c2d004828625852403a18501001054454400d04c2101d001c003440000d02c003a0350381e580c02c1c40c0940030f40441c1c0c090b80001041041d140b130030048001d41e1000d09807083c8441404841541e4803810400701186001c1101000304055446e424006620641d010701100c3c01400c003c940c0e06103414080300c14030312560030410120031120004046c1d9040360760b07145c441d50854545070302c260060329a00079641c3c10404421500c0001e03075010443c3c03127020301c80c0840059035803c100c1c2e203181c1050402e420248181d070000c801003041d900c481808962058200311408841d126480000f800e07c1081000060840c0030241445002c81c110 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 102068417 1250 102067167 102067171
    0x40b0706090203060903090a03030f0207170d0e0f0312030c04030804030b0103150c09030213110d06060e0a0503121b0a0b070e0d0201093003050406080906010e1b21 72
    0x310100d8204e0350324511280d0780d80c4580791845410032103c0c0e80810009001c0c031a10a5200f085005481c40c480c0c98504003840c000700b10600200941c801c100008cd0746e0342107941a90304090603100103400090307240100360b440010100c0708070b880030008001094511808107590185070300c40c0352a6030380e6660b8241003540d200d0a00050f01d0400d64498014030101c4148114034042075a51140c0c0415403841d0200b091800442216032003881e2034012444248880d28003c248041103014001480c0d400e0400007040c90303141d500fa072402144014800e01c921303640043c98040300c4040d03840c0c43e507a80340d40b4400c0c1d01a1882145010040b03202d400040020031281d202420b1240c01140d5401074400c10315410003040341801c8401034081401c1400500510541201c0d103c0c8e140341d04590b454044140301c1010344080d1480c502039002640208040c0a40359000b03e00d0f0b904140080010074003541094401c941402000e00041110003007c0c544416129007401668080d10915011014001d00825a11500001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 102069667 1250 102068417 102068419
    0x90204030c062a0f06090507061805010207030c0506070f08030a05180102120c0a0c020a1203030510140d170706050f060d17070f02120a0c05040c0e0f06040b07060902 73
    0x181c20085907026892010082001040c01e070703d5400b10645540d945a01c0c03110741540c5040e200c54018010490810185008150941c3c40c64620144418066a0413609820a40c11904043d2041000c03641c980d64480030769104540c11a62480146090300840e1503440c0002e04642e40030041103040f4850340e025034810001e5810001450b04101c601900b02e01c01c0e40505001e02e00c0100208400900890250071a241e036404c0c0302c00340d085030750005108548654013850280d040808990b08140e1f01d80904c641000140c10609902420300150850b010b0740124918051495100e01d0340c14000c4061443c51800066580301d9640c1d81ea6040c6940078240c01c55180c0c3c0844400c00200e8a941071603070820300a1900400c038560070703640c0c2d800340311140c0c0c0c08100107866441c4000b03284e80240c0c0c2e80e0404006d403040f80c0740084c40501c46504d0003004005050317002030310407480c00245450460b008803c0c244000002c441c00901080074000080d07031409282c00030801c2403c08180d20302000b42c50f0b8056001d40340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 102070917 1250 102069667 102069677
    0xa0201060f0b030a150801060e160f08040305030c070b0c19110d080618010b0a091a0f03090f010e031201090504021804050a050a06050f0709030b150a090204030c06 72
    0x1803150466001007141e84540c0700740e60750420004d81c3c400e800b6031000c2c1d09203e03800f0001069a684550303050a503a000c2e04418a40d81815091003802c0c0c01c00c001d05000440e5a06000c0741d1400e0300000a0f15003a40144041c05000c0e0020000c0c075048100c404940c046035120401c030b00b4500302541409001d8001d140c2d525000180c07080b00c901d03424020107201c4042c240110003032440c6500c0a0080742c001c440038041d00d07040b28140707541c4101002d010103007501034540c145400340c1310350b4005402801214594001c43d060403903002940a210051800c43e440714031450313190b036a652586647d00d440d000c205c14440815500c0c0004076459210040018503c940302d40e00c4060450362104004800c881055074000c0d4005141c099400c110141a00d65503400b074080c0781900c4022229031540c9041808200e802c0301e6040e07980f8100911030400c0b0030380135005205490401d8410341540e540708119200580207180c2c11160300c0c0000070320b554645140014000c2104103540b2a40d6070714110000e00114010440030075 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 102072167 1250 102070917 102070919
    0x204050a0c0f020703050303070e0418050a15290d0f050d02070f0509012903040308040c080619020c010603150203010807080a0f060c050904180c05030307030816020c12030a020106 79
    0xa4400113550003903d42200c0554510b40368108207450145a00c03282d141c04c0794544100117900d4a000021002244c0160302a0200c04607510b02400e5011450b40d030990480e1800d48090103010b009900703184d140009481c10b0b030448011200159502c01c004000401c800c0c074179190700e41000340211301460b60a010740c00301c0da9026214555913400083e00c2c098980c100b001100100980043c0030b5480380804401050340c516000520014081d07076104440560106074580c003804104090003010b1001004880d01034011424008d00c0c0034164900380302030800d615004a18400720040c00c0d40104001e661103903000003440919038004002c0d410901c00e11a1a0003008400940464081004850350ba8841007802c6e0451596650781c006000c00500388041180074881050270b521f4620580003103d200c080400f02d1884140703070850503000360750800360003500103010110000b41c011216a400c0034440420071491644140c04920702010822100d43c00044c194400c1040e50f0080004c2494030043c4c4c0c0280411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 102073417 1250 102072167 102072197
    0x5030a1d0a03030c1209081204060924080402150d0902030d03050606030f15060d0207050c0102300d1107050105060d0f060b13021c0f0504051908070204050a0c 70
    0xc10791070710024004c24407004142001810000404212488500b40700124076126101245404a00714040b081d10343c0000e0103100603074100551030020075020f124800304407030b20046c007090b180d40e1080300700c144040100810115641c0d441300315607440d480c0032038075184d80c40d04803000c000c2d1111640680c060301444441c101d915209000d00d910640000c0c00f003520311b441da5240c00000b66001085045628002015440507a98880040038440518400540c0741c01c04c0d4240039042074490442581035501c2811041e500c0e0a01340f0302100b020b8890b81101182c1c442414240595100b180102c10805203018100c241c0403824002410109000d10000c20007591480c051250b80114894041d1450480042170f03400036807141c100b085030440c017901e640c4031303c41c00391540c0f01039070800c0a20101c101c402d60340705c2c11140d601d841980000a4124428499401c2c44d03181d59440d6820b188001805503004502d00d01070001d0b0804603003002c0d501600c10001c5107402c00c9088024412a00350b08001005003604a90f9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 102074667 1250 102073417 102073429
    0x20c0103110703020703030c0305070506011403011b0801061101020f070b010f08011a0d0f170307030b01020714061312050703020a0503010b01120e0a0b0108030c210a080402010c05030a1d 82
    0x1660b0b144c2c0051009504584040d90426498035088003002005c001100000344244003c3e40200b00000790000319030440ba00700340c00d407030f2290a8100291446240207410962104203c1d0450304c06007040c4503154403210000c2d0181c82140c400c0b50f03102e54006008010049030201d040d040341d020310420110113440300089401d848200d11880d0314210520000a03042c80c26903d00480d0610a00b52041c14880c81c0e035032503c528a400746503880401010007003001e8146c06000b100135212003480030300074550500b00d09070061100034581c14042d580203e041140c0c56122035000780600016026106100e58510f4169034800d0b031400124000c1c07290843c00149414140120814040140c4410322a0903003800720748000d201c0000000040d01c5210b4003640407402c50001c6138080e01c1100080c1d50303100c00304240540703004000742c4901692a028003818508000352410f07a902c502c1503283c80c0c440c680303490004803007a01911001404500001843c1d50791240c201802169420051800c800031151407010020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 102075917 1250 102074667 102074677
    0xc0506191b090918140f010b040903051207090e090c04270204050a02040902070804050a05030303060306010e09011104091e1503080c0307061b080f010b16061407020c010311 76
    0x80410795554040c84591603503004441104c8081c0b0312a503101c02c103500c0343c0031480200d0700406070641081c80070b50f548940c04e0182c080001000d49050000e040d8558004065102d5800400032142420b8041040d0381d10036031443c2d000740520741d1150503d06210107800d4840c2541d4800d148220301d410038841ea592003114550402c0e444026884480380169020300028201c018444900b00f80c1c20880814105d11b2032018211290107112001d4580d41000300340095241030f074004902c40e40c014410444242e8000401d0fa05603031142d603055401d0703141c2807800e40c0500b903000034641a040c404507020440d001540c1c412000100031400381210700103016024402c480688081180c002e00d40c49040c0301081211000f003541c0c0803401c00b00c034989031903511050200d03a0350200b48001c20780580c120040c282e5001d041c694111841c4030503680c4551500c2d4507a9120b12407183d01d44103401d00c00408800b4015a5800307003802c0300da100c40e03840e041d01d40508000d448621034288103000c00e2a001010506403419001d40e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 102077167 1250 102075917 102075971
    0x3021501090b0d11040b13060315051312030b060d020c0607110d0e010e0a080a0b09060c07020f0612070909240b07080f070503041401020d0e0f010c050619 68
    0x40641038494444080f0400120b80713641d041500c40c018144aa11100c03c40c0c0311004000c100017034850300314a0b01010302e4522a40920800c3d0402e03040c0224118403440320f00c0c8455018030000c98520031041709801400c45e0a480d07541c4002e0220301d40000280c1500217040e4801c40c0000da44065440460a4030b120110006c00c0d02c803540501c0004800d680205640301800c80c0505080c600041000001685030300f40380c00540440d000b5000340010010781c020f03456042408840903002914100d41039048900800e00007270b21401100342c2c00301040c0c9954003140c0303800e0800004000c0074904143d000d003506186100300c4400701e03d409070044c290740b000d02404e124501040f05048019160900c00410f0b60003041040d28108000c01002c6820894a00205402e900c0340000d0342d00d603444c1401c481c0300c0925140000d4150742113080b08446c0e0790340c825010504014100e402d10017035845800122180c06252074010316521500051098104640e10180b8540c14480f205010641c00c1da222100030034840d811306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 102078417 1250 102077167 102077179
    0x8040201030c110a060e030409060b04030303151d060409020d0b0f010f03020d0605060307050a06080402030606090103050c01200d02010905100912120b0604030f06110f0d02030a06080a03021501090b 87
    0x202001030007075008106d001480c0422a070600382c072190b88004590752588044095280018104200342e01070107001c11a804200b0103441c49442d060340004a0f91a000d03340c4003000000000641d583e84541c426010550007500720328040d40307985000c1c42018002e80d2000824070001c00002450000d140250b015268041c0011a100103e59208000340c500a091103506005d80c51011405440d201d03488000bc0550355107030701031400d0500602d410a0000341840e030140410100602c00b0403070000700722400f5582868810f40200c020b2007a88013202080d00d400f07505000c3c4c1c0044c1c01c0380c0d1b41d0540004000a0243e81034550212080040314100c0e40c04000041c41c0d020050b800c802240c3c05504011000c40316001c0100b01410001d0000c1c40550140d0011595504450683c0091010300c1c81843c5660101441c072600d04500f89824080300e02803d01c08428440c1c00000150307114105801060092505c8000c07105039140a02d0040e449000c065001c00141101300300008400b00e10b1b002e842d82c04080a042 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 102079667 1250 102078417 102078433
    0x603070e04050a0608030c06040b06030a031b0201021609140105100906080405030403170d0b010207030c091d10020403140c0a0314031b0c0102010b0105070213091b0608040201030c11 80
    0x62001030803000340f04241c0e15580300340024507244240014881111010054292460245800714210002130031540c042e500c0340c0307032441c00290441c4041c1d000b40006102006036031071903c0101e1604018140c11814800810340001e1400d01036001400340d0907441544d01e400e683c03202c05100405080401340000504404010000c180c0101c1c0c849410074022000e6074a45a04e9480d00303405014070701102c44503540b0000e4917000c489003038030a91a250f0424405010500c0c40e5440342e0310130010780d0081c00b014950307e10f00099007401000c0103482e400300141c02c2c0d4140c0800440d400c00290050b04c01951420351000c825445d4240200d07458011040081c8084c00f01c0d070454640910f00421a03552030a1072000308807140001c02842d8140a030710464500a2101d01440d400084c03c2d00c001800a81c10300609100b4000184d50350b680080c80c0d0410343c1d5000031600c02908215a5005240d002038007440c4081c140860b140340d010b02603a10032030007078070306200e00d00d00310004071070000008644210703175001200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102080917 1250 102079667 102079669
    0x80f0c0f090c030709030f0b1e10060509010e0301060803070615080307060b0d0206030907060f03061d04020a0b040e0708060616110a15080405150702030a050a02070e240603070e 78
    0x1540e0009142d29089000b151242c0c0c1e030701f01c0e44101c030f50107072900c2820904000350310740c800400d0b034440040149011a5401c00c0620342d112444c1c1030045c81c0a1060204040c40c10f40d220740380c00341c40340c00020028840c640d940e50720707540c0f02e502200041c0d1701d07103081560b2001c0c000c442c1c0b000d01c0c003101e64510041d4904400381e210300d4010240f9013049a400704a482451300075940700000303140101d02041c064400d280c5001340c042d000d680e000d007481050508210081040e40354a05030000952903207035220003203075a2440080d802002941003003041840c041000715550441f031603d5403003901c0c26150b09105840388410030004d801101c03000c0040140203020b8400180481041d945160b10185c1001350064072041c0ea80340d01d042d40d990f40b80014620104120501c0420041000030400c007202030b030040e04010800035100d02c84e4010030018031000140030b41c000e601c2000108000c00148028240340d0402480e903d0f00c9038507041404c440110740e03105404452801c002100c1c01030409844100000042c24 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 102082167 1250 102080917 102080941
    0x1020a1205060102031c0b03010f0c0909090c08030703050a09050a0e0c1602040501090e01240e04050307120e01110607090603090c08060a0e0607030501050303091e0406080f0c0f09 79
    0x4100c03a0440c042800806240f10701284261040300c6c081001103a2040040305045c2110544024004030f203042c0342d1801b2205400511000942d200c11402162954076400c20107540d5615034044c446a100002d185411300d5400b5016102910995a40c03540050f130b0345003040340390728443c0100120030f480040410285900e0f180105504642c0100c0d4551000240e00001c003210350907840402a9500c50700404000035081c030841d00144c000850000d100c8a5440d49035080040034020804600b01c540d0224081c00000c01c25201e040707600c400c1e20b09003515840b100a140c50071141041e400b1905401806000c1240401c2c414031454296032603000e024507103503040b000f07088501d1007500d1403140e400307020800000a000c2c10741b191409010200381a4203110050b8a0003000500c00741c2010700d0400107000365500802100c0070b03071302c0442c1e50107440d100c030010b0510b6000d80d8110b680d40c414640b84000420070400309400810301000e009135403100f5a0700081c84075041c04510213030703403000b009000141a11100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 102083417 1250 102082167 102082171
    0x3050706080f0c1c0903180b0c100b01020f0316020108010801020a0807051617120603030406020c0d030504081605040e030c03091003090821010f061d0102190c08010605010201020a1205 81
    0x1603084c1c00c203001200e01149085841c80a0140c0000c0c049102c440c2d070170f10829248030010109001042c0c42c040c078000b1402e46803141003207960340042e1540c1103000d96a10802c40320780008540801d5981d00c010300d10704401c1103400c10a0483c0801ea854000280d20b45042c82940c1222a2039118003801d50768980b0308940590085660005581d0080590800b00341c0d022a508001001084101e80e500300c2e440c682446504000e1036140300f40c1c420801840300710341c0401d440705000340584110801c0741c0d080c542969940510b4215414900c0707a00c1c0c0c80c1d030807a51030301c199804881c4240c0b03003046880c1c28210300586030b00c40c900e55201c440d402009400c0b42c90074245044040d030f1205186c0010810421340c1d502d107042d0710610220030b40311552854131a81002050443c1d00404d0b0024028000614150b000f505011095110441c014240042030446034001d10805403007220001030a00b0420031442e201c0701c0d82080d40a200d2030f66180c4000851035500508c200d0f000c00c2d100b92260701412841241d803101400300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 102084667 1250 102083417 102083437
    0x90f0f09120e03030d15050a12020a0603020913050a050f070305060a0611030c030307050d111204020402182809050106020604020d0512031509060d0c1206090b1003050706080f0c 78
    0x200007480141015103d100b006800c80c8000c0b42442d1f10b04410400d001005030003004020344a20300304030041e602d10f40751004881140c1809a107845050700096000401d003944100c81d1400c0c1230801038a01140c0d4866407003400703149000900d070b8071140340403821504215001904600a20030900c9078900681c4860402032901c804c032480d000441d06124119003041c0e071540041803001c58a502458518082d843d088030089148070305001c1c07400c1085161210283c0064050b9900140068050307c0d2601e2801886501910a00329288a0780e0b00c00551156900000e41507881c1c1040451885036070300480b41250501e070b0003098191600d400f041480041c0c2103080f1054498001007110030407004020710322400c40703052020421809802800702c0388500828a034440c07081c51070b1000005d144003000b0310a03a4a0916160502c111918018000f031800c40e002500380f85100b02000007001c9441000009e59214005503040c66544a2094a507284107841c1c1c4131100e8825030029001a603c58094030602c05 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 102085917 1250 102084667 102084673
    0x3050f10260d020a03020f0a0302100f09020a0312170415240e0f01080633030a060204050a05181501030605060a11010e0d0e0402090303070c090f0f09120e03 69
    0x5094000d03103182c00b10110054015070050f0303020300180b43c2c0600040e86081c0000014002d120345540d00203468658041d503044200d59650040c407141400e680c0011a40c55029248904903510303800d080700040d00c103da01c0307400680b0300000200e90740d0500300c0d4140a9544030489103110050402041c0c06022014080c2da4061031901001295000c07140740c8500906114400c203220303082245019030943c005810001d25a40b01c1c0042c071005001103041c11130b40c07420002c2c1c20031016802203064050240c52480d01ca5262241a4220050080b550b0080c0b04403801260001003403595001406282e0801d43c45803007000369040c0010b904510310269068007004140740000c0c03026122400200f0541003e0922070016101620f0106000001d01c0341941d80f17550b0320020074400300e0042c0b004014010301c4601c1801650041138841c80f98400b0029658082d034000141141e8540b14400f1000038442540c48010b030504041080d0012172040c40b442105a4014407104d1110500643c280c48400d1b515015581500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 102087167 1250 102085917 102085979
    0x90302060f120a0608100b0315041b0f05040e0d020d0513090509060412030b030a080d02040509010b07050727051302031905010509030f03010e07090909110103050f10 73
    0x3142c150344040c8610040c4070009045802c1c00c0c101443c04901310100ca010f6468030703002d40d0450303400140d22070b490414030600c0038080c1e80b180f5200c52020360124849810540413100420320621100c68881a910103441c104000344681160313079a43d80045003060050b0708402d0a09d43d10f5885a0010f000300d1041d400c64005556031000b4800868070b046884881d07035001242400108086003c558202d03190900d03040c0081384c1030500082d102c045418000744440b6001030012403d440b10340549008040080c01c495566030b66400440b52136000c120112000d004000000c034410a400000442c0f041d607030b510803172028600e504401c00504002c0d00f0f04982040320321800300182d804120b0141040580406c1e84d50310145450450b0a5440150401006810612100f81d140014001b43c81c11500d0002044145803500f00f02694100d611b034001030042410101d40341309101480a0540c0101402e1b07800b0003856031103800d0b40c4a40c400a850480e00842d44000400c482210003211005482034440702e00305030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 102088417 1250 102087167 102087187
    0x415021603031706030109020105040909020d060c230406050301060e01121d16080a03031503050f010203010e0f040507170102041d180609071203140a120509070501090302060f 77
    0x38480d80c000c40014000e480000300c00b6480a0309140c104030260000e000081c180d50003e4114002d50044509243d56840340b441995076023280c102c100d82d0408001c01201c0e40c1e0020040c208081c0711403004040c0e0ba02030400b20300b002d060b012142154a981d80382030869080002c200c80300222451041d04010054201044007915482440007940c4602c07003400800b40e02142440c14072450020300b5036580e9004808102d0440c0115192007002c0e0715280025451800400350045000103800280c640e01c2000c0044510140540c01507060300c001c4c1c0d000c201c3d80d554804100a240c0400c6900500c1da0b0032000080254818000c02c441e610000d40002600341501c40284580f0345681514000701c2054410622250745106c1441c50180c203031351b4026054500e00342c828507595100911442c01c0211304a28003d007450711600500c81e8498000c92815a203202c60a8010407291141e820210030618240208001c0c00c6c00040c014119a81a111300340c40d1885c58081000540245d1450302401004000e580c1729 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 102089667 1250 102088417 102088453
    0xa020c010e0106050109061103070b091603050604150504020d02041a0607030c0215040302280b0307050903010b12100e0c10020703050124170c13091a0705041502 71
    0x4100079060000034441e00d84800105042220750080007030141d0300e00303a141c01d900003108448005402000c21f01558503640300b640e14045070702c0303261040d100800c18040100000401c40700c2c01180101001c84030a46660013500c200d4000f039a0096110918614880040c14540c10981640051801000d9400780d0700340800c2c2654002481240042c41d14a500e10452402e039110b608035621510020703042c00d08503408a141c00e600c0c0d500c41c07600c10680320840b0540d00900c808080181c4800060241c49041a03040a07045800060490344030b0b500b010441c07009420032105500d039147c543e000410f4a4a601d02955005040c8800e00001a028002038030106403514480403a8181d80c0340d00070500300c0d280d0b0401d40e08603014003a0380b020035102c840d1549091220910300b80c042c2c1d04a62164111145c07400144d40c94015400105a08240d0401c00d03031441100a07800f6629a5004a83c5919403000c0b03144480040c0c0000c03503910303020030340500c03041c02900300c9440c202040581c40e0040307522030f030451160150 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 102090917 1250 102089667 102089681
    0x70c1a070e01080f010f050613050402070c03210e06071b03050d12051b03090c090c09010905060708160f1a070e010201020a0f03050703090206070503040e07080f0f0a020c01 76
    0x1010030040c8501c05080e59004032071a60010000b02e220266504000303254103010468401c1d1031040da004540b941b2030303121302e40c03090000b008001c004540d110903503d0101d05100c02c40c030055070216614000b1070300050045003007005908542c1c1d101d00076242c00f902007107100e40000c40155030407540c0c480c0d440c0304041c40161940c05540680024118000b41000041031155040d00d40c0000c2c90501d030901440c1300c00c0c520780c10f41c06012100300340c0c0c803556030480051610648090340741d80b0408904c24401091200c100420306400c5c2039803001d61098842d018008288200d68006098440801c010a0b0400003510302041140c460062048004400d4540344405110080d07080e183c095180309002005410103c400c0d421780c800e000039030400240302d82c080c01c0620b17104902c40c10305481d800010b41d00341c0303e644500840303070b0300501580d10750009080035940c1e90031034000c640c0341180010104622502481501b07201d41e6008184035559a540b16000c0b841e0800503000030142d075000c0c088981289000c1c0500701e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 102092167 1250 102090917 102090931
    0x7170c0f07150b010f0c0201030c0e1306090e120409051b0a0306080115050907030c050c0708061006030e03041a0d02040e0615030915040f0605010303080f0c0f03070c1a 74
    0x41d00c01142c0848404481c0c6040180e414040300e134000030034031608004030001e101c4c1c0900f400146c501c980c0c417041d034002c1c10100a40c0c5c0c0c407215402840c065000e00d076101c9804d80d88035080c200b12600d0310041e183d581e03941c20407404d141003900b48401c02c80541a60402c1c0d9000c01020407042d1807070204d84102070f03640c02048180002c61f44800c0d090100510034403443e45615118a09440c030381d4a000302103110b03500003400320810151170342c9468016a000d030049503d80406070046840156440d90101e446d040d0a481a281c1400404000030f8643e10038021100d8084a40c0080c510b03080c030303010301c03101038aa1100e8003515100e0302b4840c0c094088894030103040106500700003960f283c500981017081144c4c50a25190507050207209202122000180c16008556a802680b0302901d9a05180410940202c0c004100c07900f420008810150f01c000400e000d4600d4244070b1601c0d4440c1000154207001d484000e40a1039800d200107040144102c0c00395981500a2040710038030100b50f02c110aa50904444034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 102093417 1250 102092167 102092183
    0x607080114040b090c070501060b0d0c1808070e090c09010e060108070f0e04110403020a060f020f0304030314031f080f0c060403050a0308091606030606030f0507170c0f07 75
    0x4001000c1c80c12200324000400b124200328921442001866490014202a00340d040100342ca008010003540080047e00140b038045850380120141100130300904501da0002030b1661081e14039491050010b1000d649030b000280500328180f03d01e80340c42d1400106400d490344a410101d0f940c03911000315146c060f04100c01c0c1c44c0c9240ca00840054034214005e01703040e041105000c00309071819030100c00b0b1031104070200c9020540d15040b002c8645180103507000650321007c1c10308000307441c2d60000500080c03e112a000d44440440780301c4102d84900441c807005c0c0221340004000c8100071040001942d00c144c204550310400005880d4215004a9039080602e80b6403000740004082c0303404205468000380210765280c80d040c02c2d540c1d443d840307401c15040101440540404100c2c900400d00c011071021140300181d085a50744c40d000100502003a01ca10700c0440c4c504654032010b01e0341401541d108000940b2030701c035412041040d42c60088801004807901800901a101c05010010000c1031403078011481 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 102094667 1250 102093417 102093419
    0x50a1e180605030714090112110702030f030703120b01051612030b12030d180506040b04110414130203070506181801030b0103080f040509091606050a0912020402070506070801 77
    0xc506140c403032030341040e41400b00901c1048060395014a41000200d640420640c0358554407006807a03284500c00b40c040c103035081c170030702c0b003d02c5084002800426008400300c9680c0940040880e4a070f1040c41005000948001c1500080d4601ca810181688406140042c41c0028254039000701c50707004041110b14940c010340d8040026898043c0000c3e5003422502c40d15080f1026407001d42d00d108241407038840725114414460804035441140f400b103a0084180c1d810780ca01440e14100e80401290200c40e040d0307052945203a142828440c1a404010040318080151241542111003010f4003008076454811407401280383c1d00e40320040c2900007030054070300e410741e00346a0401038444208148054040d4140c80100082107d1240c49811640c002a60075900d100c0350000604611460308010341100960090150b010000541c440e8000c0000e5020000107441d07010842c2c0034411849000c00040d480c03c1d007440380310202e00140c200680700510041c9840d00d42d94645003850707000c0b01c1c07000c00300c0d0000700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 102095917 1250 102094667 102094697
    0x305070c0b04080c15010f06080a061a0c150408030402010309020321040503010e03160b150a0b040608060a060905061612050a1b030203040b090310050f0a141303050a1e 74
    0x30080606107098081107401d90304295148030160b1f914481e250810000c4400302e02c4114003a40028003401c403841d0355a480307880b00184044513074041c03100c0e00b00c0381c45000b01551810848440c824003e590200b16207186860766001100504005041640d01d40a80e04149800d01e6560100e4000700c0c0d0150203e0303403501e243c0010142140e14148466006820810654142d02400024003640703030390128015820740c540d0400c1c08586680c04040c181c00c005101e001144003000358020340200e41b0690740d010000c0d81c45d041440038109140c031070000401c500d55028421031420001a00289101074a8942c00007243c0c0c03228903080300b001090318049900003801d40751480d804040c0100c01c0c03414650419071040c640c2d900a55911a43c450680c0a8801051f10100c964081c481c00c01e1310840c065040c000e604010a88030003c0d5426100507a8051038541d4102c80005005ca0451194854036883d5038100040d4505a41940c00030014904118807040d070181481c1c216403140c44401020360340d8050701c0903422 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 102097167 1250 102095917 102095923
    0x706020910080a110c030318101410061722020402070c03110a06170a0905030c01060e01080a0804090e07080d0e01020607080c0a030e0f030a0809010c1b030305070c0b04080c 76
    0x40307041301c90210030440404141c00003c1202d80001c005031101c1300030450704040d1400d040001070203040c02410300b80842003040410b41c0c01c038040e4151040218485680703078426226040c26900301c070b0100c0180750000d121a00c0d905400c0d905031040c07584c1080c44450700d500040c00c07a88490700440c0e80e6007100d601030090100c890980c41c0c1c408412f85200c01d20314248400685204801d840c0f648820400000044508115402801d0200c1d8405c08a03500d40980d007030b000307000c0c180c1406a8025051010000129000001601c082d01da8000b02583d103000e0a00c58550080d00c040006100b4520401400013100315003042114460280c590f9040500880a8002800c0c1940a08003604110081050200d601c1ca640b00711000e90429003400035510107910005810800100741c0501c0c00c0c00003050448140c1d4102e561288034183d00c070002c012071040c0c000d09481c3c2d210281c8241c51070802d04410b81000a009a000d5504a915030406040c0781d101d60b41c9508002c2c0084800b1603680300c0101d401c0819140030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 102098417 1250 102097167 102097181
    0x120f1d061608041d0408070f030c08040305060601020f0705010516020409050a031d0301150b13090c02070501020715080606030406020f0412030f0816030914060108070e1b0f0706020910080a 83
    0x24007285242c2401d8036146d0850040c813001a00f00c019442d0800b040500850a1418103940515800d4440c1c0d528101181c076003104650990260150a080001081c8040f98407000c1d40c0c816100c0c00c1c1460060580c0c21107080c0b103900200d800c1561078800001042c400c212040000348a55a14160803120b219160190308580010901176818220f000d042400c1000581d026070701c0c500c10240c0c076a040134800b1011a410781d4002d441c054a061016183c640d400f168007001d1b03903c2a001c0fa000c2542d2003482d8200508000b8140e00051300c40d001061480c07a15100070754210b400f5280140c02d0096032182c1c82203580c0302d54003010b540c0c1d04c0310344484101a0805140c407407d01860410841134a800810b262000d045070062804056a40c01113504110714404410503002c15034080f50710560316120300360380d00c00b45805240346094100f00068a4944000340207414510b01a088608103614080ca071107841c2c0144004030361840e02800141d0361070721402291030500110b0340c0e03510f8160030400c030b91004803000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 102099667 1250 102098417 102098459
    0x5060a0f021e01020c1b100302070206070b070806010e151902030d0f050f0c070b0402010f020708070b03040314040602030f090f041a0a0906081e0f0303010b07120f1d06160804 77
    0x40211006c1e146c0c0d91680050100e44640c240582d55101904c000b4521b480340200080c0140e4910003841039055010788a940320743e03402e8840200446d54a4104000701424000c052801081088201140ba070041740c201c420105500490b428058107540050a6032065141000000d40e110100042007a00760700709030304446024440b0745003406513200c1c0300e82d401005001078148042c035442c0020b440c2c801c100440003003801c281903506150304c8a00d222100e90050710f0035400aa13103d16100800d04080c0d0881d412503105400440c070344041d401c148941c9030030813425180d0080044481c0400c0352503900a002203482c1511211003a1260a030400c03507040d4072601301b19220761410701e080c06503900c0040e088210750f08003070144640040c00301c0220310707245468002c085103001c08000058403089500140c20712903c100403020108010200c00ca828400100c1040000b030403800704d10f0072101c000b11104618010140c0074501c4c250188101216861a082c0100c4802c0700000b000c100b940101c000d16446005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 102100917 1250 102099667 102099703
    0x50609070306060e0f060418051504060807030b0702100f021306021f0f0e1f0c030c09060302030406060f170606030a02011e020102120406022205060a0f021e01020c 72
    0x100b810f2000f0f20400c03460035014000e4218074002c04844d42c4403004e90b0002e040b41032100018000d41103010000d450190f45006c4016404941860285054010841910307100001402560b103123403030b00010344602030b05484c01d5000d201401c400b0350500e0301031030007142a4920050b0340c441010186042e40c0e4416413104045420a0400d00d02c01401090301416904188a000c10400000100d81e0000c1103001d40c0f114503031081602d8190583d044249540c030f81801050b003005500e4184005a059411506440e000180301c000e00344141c50180e4051900540200b20000300303a612038100306200c0d41e150f00308c100501c6213a500d00341b041604100180d800305055007d401c0b0601c0a90001e0080c144008840e80381c2042034075001c114034801d40c1a0764002030403a06058507030801d41042c0c0000d5010480e017803402885085804101c044070442501101c0010740001d1070400d00f040202d4242000011140440c080c0c1e180203404a410200303244506201f040005a07603102000f28581b4003641c0e11440c0341300f80 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 102102167 1250 102100917 102100919
    0x130e01050f1203090f0a090e010b180c04092304081314030a29011d07081302130905070f090b030a121b020d0b010305010605030f031801050715050609070306 69
    0x2c04001d850240805655180c079a502000015003c1541c41d0081032100e4680340c20005400c4c415001044444005d6940110180490340c1c512900d690403a80a805040c08000820101e20550320400c003200300754200000e40d00d80e40030780c424031900c151400e6030080c601140d0f181e50090680e0a2030b008001800408050b41e515030007007a207550389000094200c8440d101c107028444008041c405403d800303c4400c061035a15510943d0070095111201481007285000040d261030041d092540103c202800e1610000040d90801c001801061100c5400c0c6854031040c00004008102050181984c407400f9990b4a06000b4114100c8041c042014441d41c44501403002083c0c5a070b01e032030001c560ba4a80400c02d1420740d4040707540d120611a0084d00203c801e095042803100308101c0505072807081c0028005c5540d1030041664070380002080300c2c61070b0401c0090703025041304810080078000042c10002d08188c4241c540381e00c00000e001c2e00c815044d07194801c100081c5844000300d540030040b405c0802c002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 102103417 1250 102102167 102102199
    0x13050f0114040c091a130602061b0909060f04020d020a0512060d02010f0f0504050607030e0f060f0d0b030c100203030406140f0103060b150c07030c120210050f130e01050f 75
    0x102c015104141d01030a9580c44140c1850301034048410880114003940c0710170703541d407c000b95030311000c42c1c40d40c002e0003002240400007034000046039514040105980c0180d03d4000402c1003000461000310b034015400c0043c000c0c80030306800170f003000c0c010940701c80d41c80c0d150700038109606902c01001a48180c81c0014070ba0010b07a009100200121507525002568045040003070b50603101e84c0d000301d540020003080500416510032800064188280c0d85084002215070502c00d41c7d010303091030f0600c030b003a061001100c592181d5109034000c520040c12a010703800c042c008201c0a031140001d42c13005030030000801007030004600035510f0003a0820100401840c16546256030340c3e2040c00024030f40c58a4841207416551900320201420b140c2d1000903584000d4044842e950f40103503c81210b02c6040440d000640066000120b54840c1c1c02410303880040302c0d5080e04440c1c5500c075071341a0407024410300001c414001c15880c0e2002418003408902c520754148400c00c0460600c2e00d48086c030408a4540010070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 102104667 1250 102103417 102103427
    0x30a0203030f0c04090501030c03062f0d0f050117120306030a0209090a14030c0d0815040b0114030103060b130c0225081b010806010c0309030f0213050f0114040c 71
    0x80000c01c105048400d440f02800040d282c884c13070b400140d18034108030010081c45101030652007264840c2c072040000700409051040d056908004c240d001009030055442d25007101c0004000c0d8010381980048c8648074a10b031001210000e8107c6540900682d007058a002c00801802090001c8001501d081d45404070001c3da843d004544020701890001c001700305840780810480300b03a1540a0808680003030a80e2490350350707410541d079216a52044001c070082032030007140307040d0140030502c039602200b034204c81c02c0c0300180205440080c100040c041c05c0c4500c0c00c02001c085c1d13020310722802000c0b806c0001d038420040300c0b400c40e200ca8125240ba04030032003030712500007989611041c419441008102590b4410f40c068415a0340414401d0080e090000400d500380f00359445210000d807146100b540307441c0011900440081d4000f80030840c00f80e02400800c5981c9210f40c0b10302c0c030003000a50f403002d0610108050716001c0c0c590340c00b075041c3ca00061190390312008019100b6a41075600300641c00d0301c030b440104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 102105917 1250 102104667 102104671
    0x7080405010318060e0a020f010f02060c0c070f060c020406050609010c0b0702100c0203040905130b1918060203070801050405240609060412030e0406180c030b0910090608030a020303 80
    0x4141a920212000d1030f0900c0940c0f81d800d59040f000400c120311240404640703076011803c0032031048084040e401815800385050480f00703c81c0b81e008041c19a90f4400786d4525900a130740e6120a4440c80800103038842000d207010014000d95a1558039024031481404199a040e030803582c803403d0280421740359031361300948440405400044a00842d12051030580c2400d0a024103000e1003401c03e000e048007250000000d1040b00c500340740400081e620341a026100303070a8410300070028040a0080344041071054006005254a80b00000754044158900010300252100c1250a641c0100030056801e0308440254018407050301c0501c040e151002000c03401c10701000c6209140c02c004880301a440d10780e081520081d0102400c0140d80780c1e190081036905007908241100020406074800b1b0642c1054003511341212121180800e1001c189540341001e80100c40c00b08080540d2114060115660030641500654030f108a00003450308050600050340e0003500511569801003101d411259400004c4075 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 102107167 1250 102105917 102105919
    0xc030a210512040f1410090b010801051e0403111906050609072c0a09060e0a090209010e0606070512040609060302041409040f060501090f0509240603010603170a09080307080405 78
    0x1461070031031404c1107a00c1d600c5c1d10f0f04003451145c1d0420a04500e06a0710042c0d18601844a2608580c0e0f1030106030300341c5030300301c0d191341002c0541d8003002207098000c07a40703d4003e4443e08015186054100c400c5181090b10403000d007c04000d140044103001151003000d402550a407481110b51424680140154501d0f990b00b5146506001c165640348010303501c9850086030007409222110395030540240500070501654400003850400705000e0155441006281d80c0d01a1044107182c0c0380800300360034030b00020100354000d84100040c200241c014002c5a04080c0c80e0041d0035125400d00000070b10b01004c1e07800c17107003d041c41008240b000045402e03580f44940b408075019002569a0315002075000950300300280010308041c00401d6054254121010745855a841008180e440c00c40c104d6079001c100920904401c4003007000400c020000e03611070b600c0200a4008203078541d580d56003030300080c0317040151b6901280110388044190b074400181c0c4010b120080085003800256180d00301d5034800c5120741 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 102108417 1250 102107167 102107183
    0x3020c09070201020c01021803060717060f0a090504060501030308100605040b0a1107090903030c0801150c030e030a050703050705151204050106030c080a0201080a05010b04090203090c030a21051204 87
    0x4107140d100b50100c81e4007464103c001c1d5110448402e048141c4001d98004900c240506000100c0251080c2504c0d000c0090ba03007010201504d80005100e102150341c11910381109070b01740b020943d02e1030b500906010310310980380000e0642c55400d0007001c518014290b0701ca0303500e80721002c1050070f038814280c1d000d407110400c0707413592a205614296400c011002c00c4032403c0c0611000010321440950117120000c1c003d4a06205581c4000c90403500b1000900403508980545008041c00718424103101c3c0b1060310a0520441c20902d01000030b02e05400074208171140d0380000030610812505100e180b0003041e040d01d441c0700d5590610082d034440d0058004c44840c002003500060107000003508610300841e0400c00c49104152511115034030744c41d6141d41640802c10100c0410498011441054100c5030005c24141c1440c1c10030a113031001e507001400035403040c4100155044286d070140030b20b4001511480300345120207074103c01d0f0f041c1100c0c2c485050702405070a000103040f15142c2e065080e403240c2d1054007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 102109667 1250 102108417 102108421
    0x1b0b070b0a150b0a030608030703050d0c02010f02181804111c08040f0e1003050d050d020c0601080304080607110c0d02012f011508070519030807060906140403020c09 73
    0x89900201050301144101d003104000010f040c01494001300300300042c596081c070049071030b1101c01750359201c1c2380002000100100310f00911400785510811070703030342030f440042005c00f14080c50300b05036007021205102d54000d2513982d8007a8034040014a00140010340b01c46010b240a49401e96194050000d1b60b0144454041040c401c61050842c00e8840e0390240e0b4490b180e0740c40d60301201164140d4041d001d26410103101041483d408443c0003421a617006006041000e842d02c030844180c1c03c10008401c82580a20804880c00da05000c098040c08440005545891800701450724103417015241500707106c0740c03102084c942c19000c650440030b11403c1d102c041e26001075100490700c000220300511520001140352a02e040b001205020f88255880c0013840b01400c0701d64405a4581c152040c5c4445603c02d200401c000e0900304004043c04820000902000d683d985400301c1c150711041c011140581c0d0352001508101403449450030010001e44800e41c2480e15641c08ae540c0d04461800c0c2d4814100800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 102110917 1250 102109667 102109681
    0x91d0c0a02030c1b04050105090402090a0213050a0e06100507171c02070302160f0602100f11070602120c1c05060406090606021f1104090e15010b071b0b070b 69
    0x1080783c081c031800000703d407014411203046400385007010300361500c520b00b41000002c403854a800100d016a40040c001d0300c998403001e0f902d000a50160060480c2c0001764100043c8a5072610f241c9802040c82c481840e032240760400c00c06c40110a951782c40000d002c400e100500c0400c4064407102d10f4007850350a40c0f5070301e851401c82070310b41c05440480b112107180000744820403d5070104800c1080c4405400402d0b591713464181c032a0140c4124028100103a0011a400360058402c0e04200b41c5031610400003c1c1140c0e002101c511142c2c40315800781c1c0c8541d00060140e0441040c946016848005100958206000108590f000032103050400b050076460710041406590f0350341c4108000e009000c0c080051030b07900c0901944400303038154802c4150742e179540c03400039501182c040c4252110020051514050811030359100a0004800d1055144600909407001c1c1c49040c03101400b0340020b00c81251141810310305050142080ca154916001d800d000030818405030748217590071254040b0700895181c1d0b80e07075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 102112167 1250 102110917 102110923
    0x7060209010507020a091d1b190e0f07020c040c080a05041103030316030f05060123070602040f0305010c031104230d110a1202030a060518100b01091d0c0a02 69
    0x1a20195010011400020b4031a0300d942c007ca402d0b240e882c0d02c2003968040784003a580c4903900c0902144070203511a0142805151026403081e1111040c889050042d845000e41c078440711048924180040c0b400c020b00c59001c0e010403222090203001c43d014440621140030062050790041c159429040c0c481021501300025031019402d2010003070100c94891500054040120f180300340154042440c00b40180100d904900425115060684035040150003540880c495095000209128000c043c402d503c005a4140000d00041c0714440a5100382c40c158200242101c036640303808024940303000c1e04d491201d4528015103046400c0080d034114600c480400c00c0310425260340c5070a50204d01d1083c14000c00003002501003054106440c0004083e8a9001d00c0712058014813000c0e605904c0203070702c0d50000c0e1598005660140c4095081c0c00c4c101b001000d050b18104003420b50300700c0c2c00d440c0c0c21f44200a5a10200e520020310f52203803c148041c0e80440c140c1010380014014420146c0c0016481081d20300070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 102113417 1250 102112167 102112177
    0x51c030f0e031e06071403060a0b0313080315090601032009040204180903080912090d1a0405070315060f0b07030219060e070e0903091908070801050a0b09010308070602090105 77
    0xb460110f4088081c05400c980c450208907041c13000300d1140705864810b15a02c0050741d2140001410704920b041c10103503140c1c083c1e08014004c2d0b6503420b100080500140d9144003850141000d01000f40381c2d036040d41c0400c00300700d0740200284e04051401e0140d03481107003443c0d451690000d0842459035101c6290340414041d05c20f80d00485107215130307d4910341556503586c4c07040c81070034000e0755400502d4035104940c0c2d4451200b8416403c001d4028080b948041c60090407a0240c4c501c981c800c00440d10603801c1420034400c080b20151910f80210004100780b00d036481490030480610702d000c01205080c14000c1d205940d00e40104c0400d4000420325404250080200072804110b0020404003150a0720b84500500841081c1e0152409501000501514041329481c020500400030703600b0035041c1b4051000c00c01075903e044500e00014400080d5102c1e051010001070620440045910300d0141580803d035200401d815005916680c01080400c5840301a216140da1004000da40e80c21030304012681d502032 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 102114667 1250 102113417 102113443
    0x402090609120c0d050705040c11150a1401030515070513030b0606040e0f011701020a171f0801090203011b080c070602090a06050c0c09011404090f06090804051c030f0e03 75
    0x9242c051301c240080022580d003210403c940900a005090324200e841c40010140f5280aa008900f4014034a1903411502c1d032015000074001045000102d03000b4000e2420792003550950440a0420070000c4a60003540e401011814003902d4400e0414102138143d00d2440050800c6004c41d010034056034840045030000e00c0d40d00100c01d1141024011031076201e6003880703103078840d1521400c1c0c1c0880c403034180251060380b05a074a4025030215401c05d08001e20400801800d21500108002c41e40222010b00c0e11b4054003919000140540e050700c141802c55480d0b9040402064052200342c940543c011582030f40100d40c0c2400343e0305c9004500d45a006401103881c03640d40500c0342c81c004100302d98400081d0000b221200f0403502c81c100303142d0912607009001c0c0580745034401c043e29505d01500741a00109003252040500d80d200d80c1064036810200d9142140494034400000340402451070006466078240d90b140307000c00c002c80a180c0d405050400e43c2a80f000c1401080c80581c00c080d58240565201400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 102115917 1250 102114667 102114679
    0x60c091801090b24030c070f0f05032a0606060a2003070b070f0e10051e190504080607030f090503031305010501060e010504140312070501060e060402090609120c 71
    0x18581c0302003800340103204203440c003035440c48002410050780828101c802800355600341d4510748a1014400103540810002d5070103424038500c400000d007994902c582014091002f460700c421041a04c0310601d400c080c00e2040c09040d00c2440d01c04908041002c130b402c640204c400d59503500000c2030a49285411090318094140858a03009824078003100604181e03104404c00c5005503940d074400d80704086141c02140c0068200442c2d80354500f4081810800c0c02c0c1c0a0130070b1420178001c5034060380c085c4807136006402c00ca14081820500380806003d03c260a400a090003801c0500700f540ba5507540344020089000c0503181d19041003410980c1d4080c05030b20750480103a940d20701d00990060442668110210340702d61902000003030592081841881900d01695002d00d028500001d540507640e000340c4d03455050150400d1003201a00110040c1110340c072038000850300d00d180905800c841d0b440100290b016900402c00003015554650455160200c21600344024a9003050342c5840d02428003940d0390402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 102117167 1250 102115917 102115919
    0x201050f0a0903140c01080c04120b18070906180e120f0403060903030b0102070602120906030901060b04080a05060a0c0e060310050402030a0b04150b0417010b030102041701180203060c091801 84
    0x1100400c45e5005144c081e21000040d85900e245121284140d00c108100b0245214030a80069283c4001a42000310392000003030000840040d41c3c00c4c03203096400010401d83e00c401c01c005156814a90304408084548108070484c1e640c44103c0e1541c050019400c108003000840fa8110f0325804182c4000e15004101049411020b00d000740040100c005a10f016120303034031000074030034030000c0d0040b0300506030341d0b2403130034011210300380039140d000039090300001c0d5292031010030740c0000140540300400c00d5800410001440d4141a400c0043c080e003074a0065041000111000390414400754003148180c0342079660744e0314403111104900298022640c014000404d105480433107800034101044202c4082003440786200000104040030301c41c0301c2404406200802030b1100d0040e603190350030101000800c41807071450000c0e0881e8050340048c5003200b08030f1368842900800740b0941800508828042d90302128640000c5d50740d200081044965510001d000300d9191100c4000000e000d454005070070041d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 102118417 1250 102117167 102117203
    0x50712050a0813080d0b010c06051512010c09060c02220e0d03050421110607030504110105090d02130204050618030c0612010501031a060d050109050a090201050f0a0903 74
    0x30341c1c80389940c94000342481e004680309a400314031552100d0341c4038021a181c0042c0440c1c0300064407440e002e00741405500803000300418024010705128518100c00800f00c070515000300186542c03407182ea41040d84c5400140340c01d150b005502c20041d508c050034001d02c8101c03a0720008880040480001ca01030b504103c442500442c283c00c00211904600191580414a56401c4003100d2084501400c11080310400d25001e10512800320155800d92030541d003261350108045103004d0702507901c000000c0d5140200400e010a1800c5030342081000d107040707403800c90200009000240b40e423030040c0c407035000c000c0e10703450751151603044400901c80600802c4e00c40c03440b000098221089003072000d004c0c1c021070346802d010303113449422200740c9070100051107502c3e42030000440c0241004007403056680140d4844124950b184c80c040e03d40505061004038096040c0307a030420a403800502044807803410490340704010b0317130000e09803441f0754844100d035911002000001c07110220b00340c0c07000d0080e92610305e02c0c1c810 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 102119667 1250 102118417 102118427
    0x804020a1e1a091c050111070305030603010b10171009090305040f0504090b01090207060b060f1308121b0c041104210c050607110a060f080105030d050301060c03050712 74
    0x201c030102c9516450510b01c01800d40b4291141184460340192098103200480b0318201d10681ca490061000203802d80000300c000308941c0c0034a4068000c900040200719140c5000d02540a044200744d81c00c80f50414101409040002d440c851a0b82c0c0c1c0d00d0100000d80b00740710030140c0c030008000a00c8140b0a544883c00c004d482c44c3c3c082e000b01550000311020201d20303403c1038043e4900d80c40d44404407404036881c2c00b10174002034100001c21286180c40b5008142c1503529076000d011004043c0f4065560303200003001c400800c1c05990300110851b0812201c11094900100a54003000810f15070175444a0a80300b145050900990b03005a0040c509030154001c803103620094000c1c0e61400e450040070340381102c850301810f00c0b26840189490901d0f402032210b800c0100181441a105500115261510303100060404c0c015030840310010b540d102d078011106070b000004900520f400d402070400d51944a100500d030f4401409020144100c00c900e25040500c1081203800c071542100b002c1c2030200101c440184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 102120917 1250 102119667 102119669
    0x4032709060f05010824040212010e0702010504171b0f0106150903051f0b040603060531030807120f0c09080d0206070e061308211602010804020a1e 65
    0x180e090324280010078a04400c030380030b1043c0d4005864a101d03581d00c2d0300c022030710b612200c401880c4008805c4110005504c0d00c2c0041c15800b800c40861002c150b050102580e51094000c0c111421a8102001e120205400c0c8035650f01c0248042d50640ea00c880749000f141c100508603d04038914483c0030100300500070198401d00030749202c440c886040c2485407071700311204052408060400d8000410401170300c0148240c411160300000c001240c51609000083d0850b00c2961017034541580307403010800c907000701410b022008540712a02c1c08031006101d05005010b10b110400a0500034507601041180e0f0042103070000000784224180030801610b001e1402501c1107640000c0420039408010580030b0300480c607204420810760040000755250801200c8030300c030003400960004001c11240e41104008038490010b840844010071088403100c425295002104ae840307400e80009205c90f0020304211079003810f4158091070704800036182c034000100c4161469000c442002c140d1603400b200b08948840180c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 102122167 1250 102120917 102120929
    0x10c02010e0a0c0510090e1e0907030f020409020d0209090c0f0603010b030703050a11070317060f0d15020d020703030902120f0d050309010209030a030801030c140a03060203040327 79
    0x200911a60006041d0b6450b00041c004102261004080c04907062810000c01d04070001d240c150380c01540c0ba41c410001d00d80c1682c112040400e18890594032802503101d032500925014000c140091440d1111a0818026003000707211b29200c401550070355580214100109170010710401c800e0604204442d96054031117142c0b4010000e00054000620b4904140d90480320074181c0540345070743d0040b04400a00f001001881601d50340c0070181645071944010f40358903803003038030f40003a18200404080014500107144038890342010700c9102e99501d909081120081d03111984042c0743d81d9181c840e00c043e015510841024a10119001041c90b0b41500003001c1680240c840d04a00c0650254035920f40d8061f4448841c55031283c0c84820881e4400e50040d41d206c0c00b20750005003002c0c0c00c400041d05110343c00109600080c9080300500c180200507400d8001016002e40620720f40d0700c041c01103421031a080c0300281c4660350200000c0c0906008644001644010780d023402c101007000d01140400c101e0501440f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 102123417 1250 102122167 102122171
    0x10e010212160302040303080c28050a021204030f030f031103040f0303050a0e07140d0803070801050a0b0c06010506210906010810270c08010609020703140313021c08030108010c0201 80
    0x1142e0024080d108485c2540e405076030340d0750b440e590100320460f164481e844011070001c514003509409117a01070100d00c0c20401e566480d64944058800a02e801d681810711091240100410000103e280c941c00c100e4940c03605041010400014051b0010803025200c000000000010002044000c2080101c6d4902c651810091500d0390035003d4119421b401c40708105900110052040c10940a0303154280600105080f08a40070f907511a80a9002911a80042921200180041c1c41d0000101000c0d0a03a018400d00340502001d059944010601c46d480c025440054088000c0b0b03492420840300c0d42494210892a080c1011400c1ea607407403d01c50075a250060ae203031a205007000b07000320440185a01542100340000c07060190001c07007008012a9500001400010550313000c0c000e0720f0051400c0080181c0300d22490801411030005007402e00c1c41014100704004102000c000000400b507010354600214016a0844d500c4071110041c000d0454800480006002001500071517044c1c4400e0b402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 102124667 1250 102123417 102123451
    0x7090609020a0f020303150f12030705030304020f1005040e0601030207120206011503090b060609120f0a11011e030b06040f1412030a02030a05030a0f05150a21080c010e010212 77
    0xc80c1c43c0e00068890700440a0000b20120244c0b40c18023076036441000003070040c81c1a0801d22031242c51a070011000301c4558202008100651608a0800f1240a000d50741c061002c1d10b0032400510b14451806010700c08010030000c140103074401d0781515501381d404040c42401403241c120207542c41100340b2440107685191200d05020350312038018144220fa00c01d12080701034a0b0380c01084a00d400000c0c400b40c1240304403608111990080040f0304d84240c250014056a0907942081c203180707644000740605100c10083d42940400720002c681500c0b000791710300002c422081c080056024455684024403103003440f9070200300401060382e8624036440841c1c0075001c0c0c4085080071a00c9000700c03540940580c1007807040c0341c00c0d0350040c00210f07804002c0b03940008a409005503140200c481c2070720703d131002420318007a01485040c8000a0009410382891b0181c0001ca01e030103850382c068010b040100445008500d03a070040d03e09401400200440740001c0d500c03070451074460800d280342150440340100790845 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 102125917 1250 102124667 102124697
    0xe0d0807060f36170c0d05130509100305100204050f03070e0f04060b0a030812070206010f0b0703030207080406030b0a090203130602070206090a0902190912120207090609020a 77
    0x3050070a012a009802d0f010421407405420b40005019006120003201c0410a00014042c41140580350100c0d440380d0703114074660320440d1405010380e99941c1444000c02103440000d01071080901101c074100d44484456840c5021841003002c15400240f0034490080d1549072030440c2d40140c0159142601d01042541c400f40c105665010305110b00a00d1101400c04201d40a808100c040d41c03003402100c0101e69070740c0c60008148c1c810038075801920890008900e00c007100240505464008840388020325440d4100040a1610307800307489008000c0d5000502c4a08050207901a640b10315082601c007500c580c2da500000d00034144013040d00303102d10510311001c14a442c00d8800d80c1d0055943c50206041040d00c3d0f9600002036116160036a440740003440422005c1da82c16a80788080c00ca0340c0c0b009030710745000c1c82402617018840c1c20041c090041e0214280225602401c0d0009840d4000201c0d1100c40d500140613424854650889008581041c0c0080f551020310b030018900f4810320760781c0406226a0007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 102127167 1250 102125917 102125921
    0x140718050a15020f07061205150306150d0b0a051b0315130e030313021309050307020d03030b030d080601140a0806011d040204170601062307030e0d0807060f 69
    0x801041da00c40c40c0c0030001d000d0749903528004200b601c07160040303c0154401146041c40c06000e94400c60004103520001042c40c00540a542d400c083d0690795032508911000019881d2036005061601052000380481002d580b1001ca000c29941c1040c40d440b4071703050516000303000d4001240e0310f9a280e42440c5c0c1c14035040c46003508a0748a040d1b44840080d00741381440800c000b50010103540c128081e107d0502d2080e00206000842c020410011030850400c00d61040c0701201c0c440d012280d070903a260012140c04a03c011085800f40c580c12a40421841c2140c038040e0000c1c04100c1c10542c140c4190900e854030030f070b08011103600880e02621500e00c40120041c409048c3d20455040a001800030341c04581154000e51070528a00b50810509400200e40f002003000c0307800ca80d00c81c181812100101c46071741e040620025025000c07614104030016080c40340040490128032005024610000e00f05040c14451101d5488518000300700561034400c5041c4040709811844041c0c4006141c01c160b9110405a4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 102128417 1250 102127167 102127169
    0x12080d050c0f120c130e0601030c0e0a050d14060403080a0e0303041a090f011a0f09010b0f031510081905070801120c0b03070504061202070c0512030c01140718 70
    0x81c140c0f0707000c400501d6800303584015005060445052080c2d03100290403100500c0a8942010096824603113003000400f035601041e404001c0c0803000c4180140d03030300c401360010192002a1041d00c201c2e6207901d81840c4042c40c00d550400540103140903c03041580c0035250703a000b95902d01040c800d100200d0794040d201c0c4815500108180710014a16000c3d01c03c400c50a540812001d0035141101c190060850961b865082e81d646070008103a4180c04901d4817814034803258100b039070710b12411360400c800c0c1051881183d4032420041c0b804000141a007000300400b1428641c0540719150101070204060a2068103070b03200300b50500782c42e001d0b6105840521071540f00300919a200342c00c80e444c1030703840c007030a084041d015104541010004150000a0001580501015a1030b60b68542ca030180c000c2440132103c02e001010f90042240740041140300c610701082c1c920846d2821050708100146516521400000300304a50070b000c0075020954541d1050341c850815034448152608210250030b00031001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 102129667 1250 102128417 102128437
    0x70806060304140c04090c0510031428061d24100c0f050a05010c1106040204020f2505010605030c0d08070f08031609090c0e0d060612080d050c 63
    0xd01c0080d001c58400004041c4550000d000d840807408548045403c0d07829018066038840328441d000c00082c05c0102d1110f14424007803804200c0e20444400ea070305104c50160032089480f60801c411503c0c0800c2c15201078245041c03203000c005aa40e0b880011013200000240701000c80c0460380090b10208801c00062500d40c0c660b00441507803141c08041203070f400080604141000460305c0c12000060025a5208116010b80c00403e101003a80c41c05900707407068075444008000e00d421074006a640b0000d007241c1c220f6411500933854442242d07407500140100c45081802e10051004401c1c418003005078298000d004900a1081c1500c48081c10341e11040c0100454200c4010522280450712103005800040e118400708a9403540c19214404035410903915244c6210821040034007650300b08043c0f0008000450050103908000480600440e5042002c68010021009014100040303548040050300c28000340c51510740503410210b84942002c414514034904d08000325942d906c2c0002a9085688 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 102130917 1250 102129667 102129679
    0xc0a050102031e0c0a110f0f010c030c02150d0e012406030902041805030c010e0c0105070209070201060504021b0c030a080910170403080702160b041a040308160b070806 74
    0x10901d2420b0303880c3c640040390420b15000920014084450511a580e1001d0143c54020414201e403000c10200445d55070000d07200d46d445803901c250b544d0700b18400d1160250942801140c684040c00402e00c199034500d203400c0f40040004415014030100e600001c81c50840c00d0007004082c0707040103901c41000d03d01e403844205001c2c100080200a209402c03581056101800c04150f804810303041d010a20340c0950102d40981000c40c181c4414a0f0900c503035001694071390000c01c01804002c0c0082c01c144079510010b40243e603581c0c0061030550003504200c00418000e0070440da18203415061988003841428100d602c1c0c0206160201540380000301c03001c000d42c001d02d00310310f402040420480c00f0100074104a0601218092540401c8901142035101d14000c0c1c9800c03900e0701d0300d024020b04107400c0389203040210350720040901070b40e0010015102515202e03507100e0003418803c06819800d00a9500040c0a01800a0054131001142d5204c0440511800780e0504507100d002c0243c503a904120b4030550400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 102132167 1250 102130917 102130927
    0x60906091213090203040b0f1f0501050307051b0f070f0f060507050a060c08040c150e0405270708010b010c030203271201060510170604090503090d1101020c0a05010203 74
    0x41c403228010000381e101d226000140e555200184800e1360422101654042103040c10041d01c100c0e002c0d01c2c3c83e446030000050040d1700d03034072501c10740082d03240d0700600d41080004000038048500074000c44141307040113180d5040c0440340c210416542d4540141100485c0100800016403400b0101a0001d0b00c10602c40c1001990400a0443d000e800c90002621503100d040400303c0464854420300900c4485039450010794130b82424080c09410281e0702c07000a580328842c1c0d441003298010003400540100f103e010510341c41e00515030025044800800d06e1a0080c066244a42c03000000ca400c101c8030004000d10240c4c84001c01034644111004004d07001d6002049480402e0300e1030070400d02940c4820741c0400c20049004082b03a5082114134220b0080d0b9941c00040c0030516000300d00100001c20352030204440c042c6010514001c0e5005409140200d4807064403508110083c8180c0b8a8001e001e07007040004141400c00c443d00d07105442420340035015402d0045414108a8020030a481060f0001c611f05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 102133417 1250 102132167 102132193
    0x10b030d08130f0c140406060806010c020103111b060f01051c030f0203040b030c0d05090606010c0605040204142514031602070302120102070c140a150201020c0304120506090609 78
    0x3600002003110f2141c203c01c010700016032001070a002030b0100c4460082e0100b603207000d12049840541020701403154010401c44203030707848040e400460380d080ca800f190f01114186428402d001d2542c0c044102051075008410ba49400100680319000c41c0e99540b0b240c4c0d90700c50a0040f090600754126125010343c07416000803d0040c3d2400125562a2044a00c0d1580e150256449504281c1c0d20804032880011807a051060a004050700321300c0d45806880035081900c0080d041c807541680041176140c4a900040c195a650352001d011210380d010151f00502d4117034020188900c40032107d52000121001440032244994800310600e45d1175641ca61460b04c0f030034807094024555488800c00c5128021010005032202c1c400c0450031121a8005a2107a41c58541000d14030301c1340d0060164402240c6820b4001e54030700055200305d039029030070030b824408038100032070180c0302d0600d0040c02480009000103140c0380d000b42c864482c5000303000341d800c40d482c0d005200e034495109844c0700364680d01144800200d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 102134667 1250 102133417 102133441
    0x1801030f080409050c0304051c09151202030f040210020a0305070201030f09140616050c100203060613030b06041b090501080907080f010e060106051e07020a0b071202010b030d08 78
    0x30280118211814103690340400d209841046918040841022051104101d4104070070351202c0c4803948000c440b41d00c020b2004000001501c00c02d5146008000440d42042c0203400d980c5050381d200c41e09540da86401c0800401c0050150b81c101e01070030030004c021500078404500c41825580c181e590510b04216900111b01071b0000a050300c0ba90350b0b85900c40070005140285e02c0030304051030f501919540c50300300341d610440c454601d2060107011040291803140c0b0800304410140d0f0b4800c0200603101d403900b0004c01c58038041c0e901c52010444189102005200401c103085104603802c0b1404c1c0144c3c0c2d010f03184070740b1801e00380c203a8502060305000c040c401c40d80220000e03a40011000115500e6540c1d5110795441c001a58113602c010780d54560b8030010340d82050044601410850600324038124500c02c00060a40c1404c404802c1c01c0d5002c1502000c5569900014000302841d9111035141c2025080ca4840d860005051902640c81c0902c001d12a040110360240c40e20003039220708207217560386404816 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 102135917 1250 102134667 102134693
    0xa08070204020f0307030c1d030601120c0510090305160308120612010207030c020909030702090408031302060406050c25030305031b071b08010203220f05011b030b180103 75
    0x1c0e0040d024003060008002503009107225003c0d43c0d50104d08514101c070007420541464081c030901040c4e00d14040890b40b00003400714119140c000107007944050a08154980c0d4060b60086a4401e5a0480710300a060303201864009903402082038070030081c40714040d10041d002d103106c002e05042c414001d44030141c1d0510166a0b104401400c0d84100e00e030050420340c00c90b881a00210041024404081d00354103180c0c0c06250301010403001546040c11a800044400d04010001051050000002425404200d103180c0300c1a40c081c09041d1619107445000e4040e40040c0b090a00c5489040c22041c211000c071490300f4800c1300c141940f44c0c1d0f91400c588040310103034001050b000d02c00719082c0c40700c0c50001c464801844018081c9004010314050306000300c50500260f840704600d80c1c010b00500026a102418080c0d40f0860540e01c203442c0543e0b03140c4407005181100019003503502c0c1a80c000b9106189201c03540c91030300507a03001c10604400400b0400713001412010040903441440040c0002600254042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 102137167 1250 102135917 102135919
    0x405010c120c02060409090c080601050609060d0b0306070503090606030604020f010c020607080c1e030309061501021c090f0609080a0303270f11030609060402010e04020d0615020c060c0a080702 85
    0x10015640caa00842c104d58001e80c0120b00705559a000c3e0b106101c2c0e0a9402c2e00503280402c0900519450300c400071b9554000c400c1d80c43c1c03260000060f1134440315071a500c5071481c0c4c0400f809840c40351400e0703840940540c204860301801406140300260321890041040f502c00e660040c01c800210000400440f90040e5114003240c000070104601000b15200e070000e0010310210400420080c1c1c0c03501c0c50b100d001d94010621070929801842403086480d00854040d43c01141d4000075011208805c00403481c1011a0b5154803c4420380300311042e40540c0a16a08103941031100b45e011000c1e500c88089510401c41c2c440d0380000e0308044c0000700041d2180d00001c1d15a03d45441500c00703403024010011008258190849485803005808400c00c101d486900e60000421000fa04040c500315001d592200c0f4001c00c02070400191200d10116a07445506861550001050410045458203901c1c14441c03850301105000d8440c0750200003041c0b0b0014111031000b201c0380042c0030391810903034400c84241c000303003012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 102138417 1250 102137167 102137177
    0xc09150f0f12092105030103080904020904060e091507090f090507051902030a020610030f1101030e0f010b0307150909050c120406020909010f140f030c040c050304170405010c12 78
    0x804440d0580d0b025842c3c400c2c0c011444c840c40202e0311601844000301d90450402845018001000414611029214844404e0744e016070781d0008040010f0090505030480110030703034014103004403080005036039919009017002d2504191507d140a55444004e4401c02e030182100e903070140040396071a08490b4004000f0700f005401c00c1c030002c04041c0720303e0500c01d144005071b2000c1028030040354104841c030b400485049407618180e08586170140d050488070740140c6400c96102010049034400c0d440103905442c41000e5a42c2100d02c05540c130f0180c0079801d0010f2007482110b50100d80102410b0301044401059202c2480107807918040d100501001801c008402d40700f07204000424a481100520552045600603615a21101004414070060b0000b000d182e002e9113084c05000c0d441c03040c4c0360300c40c002150f6402c195401031000901c1c060450003481c0e00715081418075901c840d00b000146019034812413400c0300c810b00011296003140914421140000c2c40e03074050700cac0854501015800300c40b8183c03400c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 102139667 1250 102138417 102138437
    0x6030b030c300a03020c100c030c17031f09022a0f031207080907032a05031005010e070c02090f0601120e1e0307020915030313090c09150f0f 62
    0x802c80b4520442e1903840110340150010804060b41072100071290242101d00300d164400280c402002c5200d102802400d1114041c16403051054030221150050580b21304160340e490034030620318060186d00c2c154a00c00440c0200031451452074020f44158990f8001c0101e00e8071121188030b50400b081c0d980384a00c41c021101c4030000030390306200034400e01c0c692110000c2e0504120000401c80c0b0780003440c00301c082c1c100c0303031090000641c000b082004158114a40d4041c20111001e1600300c1c00c295802290305105a44c941320b01d040003604118129084501024010756031281c06481399080100000d501c4203202d80094144140a64000c0c0c101c00d040c0350650018061800b0700f0b0440302c0c1c511181c1c442d64003401a9415500f6140001d0b504403800704042d50800444d40c0c08246044400f42040403e40d040c11100441510108107849080241d0782e50040915030303aa211100a08006194100041d009240483c0c0702202a8102000c0540d035a03854810b2003987e00100d41d0380141e05091002c20610b425 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 102140917 1250 102139667 102139729
    0x6030b15090618131a12060f0a0209061c091205072d020301090c03020a12080f0906090303040e0109050f07020a030c060b030706080f090d080a0e010605150c0706030b030c 75
    0x2c0744821010700111103580030b8100c3e17000c01c0074400d98410030415036400b150400c0112491500070b144c0003c50008096100c1c042e490008082d406080d13002621000c4018410041f0305540d0072101c4400d000e9680c28940240c801e00440c0c0e1881810405480b9035024000880b1044c0502d08000d09000c05031640990254594002425070384449015039492210340d0081c402c7d407034804d00490003488090000c050455050780c1d41d10300c1e40140f095181c6107003004102c43c840751b140c0d030040343c210104c018140c0e65916100c40440c85040428040c3d40c40d52883c1000048d504581a00c045000750b034160014028001c0c1c558080300d00720400082201c1c1c25468503107108154400300000310140c026500d8141d032a1a040281030303a40701c402040c00e41340d80d1101142000f060b03000500e098001c0381c002c20118032110255082d41c05000c00c0d62000d90065201c411002c204482e902c09001c442062400b628102541c6d03030021000d440200700b0059243d0401e00c4845180e162118100400c0c8800561910380b4200d040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 102142167 1250 102140917 102140921
    0x60607030f141612050c0d0804050304030b010312032004091505090901092a03170c1b030d02010902090712110708030f010905090a0f03050c0706030b1509061813 71
    0x68065202c084407000b403c0800605101105454405103070641c00c0038483c2d02107580c0c0314540300b5200c00348244100840c007484414400c80d0090b541110074243c45503524a442444491240c0d0402d0000340380845c0604041d0000081f01da4042c0c0c0c104803181000d0038824044000e000c2441c5440034408528400500c40e112a40c03410301c50020400005400c8100d400c01000035000c069408040b03080d0b14540404103c0085850030581c0d802580c02e80c007000c0103502c020564400c0301401621413080c20a0b5511150505130f085800102c15400d81e1020002002d0590a07506015002588401c8513400a02c0c000d2081d540056031358040100460280b601611428680c0c1c0300c03050550382c9000020400905034003c1d500740380100302c0900100498505001e039561a114552401840c0840b1007011505140c86042030399559842c0c00160b6004030342e80c1401074020112007001c0d60194039200940300000c00444295804c12001600407485d24411081da2040d10350780c2840254492044401000217251078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 102143417 1250 102142167 102142177
    0x3070f030914030a031a03060a0b0303310501030e070603020901020c0901030c0302040e19080f2101060201060b0f0d0908040f030305040806131a060f1003061805060607030f14 77
    0x2e000c1c6a403907215010042c140c1d0400c1c40b0000000c4401c00041505440c00031b90306501207100e50703002031084040300000303041d44502d55016100c112502c0141c44208400d8a400443d1011b5030300d04002d45170340b03000540503180c800c02045190b800842040060038025002069031800510654100750115030016003a81c1003030b0001c2d1060038800d00117000310305151042e0340310541035030004e02c02554500800c0c0d21101070038800074121000840c400b10b030b566900042d205205841860580c0048007080c3c0060451400d2140b00010b600b4044001b80d0042400115854144107031200361130032005011280182c001c8000031580c4200820001403d4000d51201c103010f144640d82d0300c0d5607035281070318152030400c0c041c00214a00703080e103112000045501d0240f01c6400c40c490740ba41826526980000c3c80c505ca1041400d80010b46010145002035042d070110302035070101d00007841400002c4513041e0840b042212504c2d00044100000404a401004c1120a00615141c03620300c104a42d030125502d5003013 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 102144667 1250 102143417 102143453
    0xb01020a0b040c0f0b0c0f0102040b040b0d06030614040b0c030106090308130e010602060912030105010f11070317121501020307080d0b0409080d0b010e010e0d0f02150c070b030c03070f0309 83
    0x6c81c9001d0b29190038442000180758600003981010f007000b020f068a80704900c01e45107000d038000380140d01c000362a00064021a001141003044c0100c0f451800c11024007118115100e800b8503002403c0d04041600382e905a40031561002c10550440c0d5370194958045040111102d07401140000d5a0300b9945a03203004c0d210a6000d40321a050450342e180c902584a040d480954100303000502269902c040700b030114400f58900160750200004101d0301340945600060801114244d03080f01f078081401c0100902742030540203800c240e403000c490101c00d03444020b040d801038100f084910045030650001c0c02e000c2d2039002c00080c5000c511400201101d0b0107003001c5560043c007044e125840da196114900150b0000c1c2025480340030040002842d000d80c2d1650309209041f4114040144148551803010f05070703010701000b8081350913002c24202500910110001c500c01e26001196002ea03101c01d49000e202a240e0240c115190303035000307a581a0105c1014410169102c51100106442000200f14907030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 102145917 1250 102144667 102144689
    0x20903071409090303070807030207080d0c020c12010e1905100501080c040c033c020d020301030c05010203040803030610141323030c0d05010204170304050406090b01020a0b040c0f 79
    0xc4400a20650080082030f20400d80c106108001d105e580080d103d980c00f81140c60010703a18551440c0101e00307401070b850342c14120f61901ca192001c842e00026281c003105011140c6e19400e112142006081c0c0b40346a51000840c0c12076900091348010750f01002c0501c0d8070820541d80706400200f5504220340c001da1081646900405444e1440d0625210300e8802540924091001c1f041100d82c0b4188800e11b61200301204031400e020220204040303101e415841c43e81a010356640710300046240280d0000e020541e8054501d640002c0c440d03000004960445221902560542d600c00003080000b10410310701000b4040042a003640111021004006e140610403414900358144104000b006c10700221140704469600c0da5001141d40c0020340514201007210350141044052a019000e0302441d0300440310740c1c00c0d120b03011299010110240c402c0d1607007a24200089541c541c9003d040d187d2241030346015801007140030000c50003442e24554040d0107030b100711000c195a001740ca200d2404540c85191001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 102147167 1250 102145917 102145949
    0x1203060608070e030a1b08030d0501090608150a2c011d060108070b0c03090a031505071404090507090302280e0915090c1e01030b180109090602090307 66
    0x540c000010580003a03007807401e0001c8a0448000c03950fa660000000b42c990444e04d03100c8032041d4100e40001d0007034050901501e403107581000001000cac0100307004256241c1c0c01c210001c40c00c2a00051a03032903030102d6030303808145a1503403d03040004282e46851400c000c01e18031444011465a1055000030301c4406000244140325541d40021600400b100941e40b034010800400074000002410020340e45215203042c5d8541e1020345007455413046201c500c1d04032800d20b43c00001e0040003980c0039000b07050b0310f1b020b01c002d903a000411500110701c00104001c00006100a1092031040c1e401260300c000c0d00c0c01c0198034140c0320780000d84066495a04a10f00c40c01d61a4100c2c5010806103a41c0000c00720700f20140c00394140000c0090300c4d02c04d200c030141403000604001030401d100400c080c003041c0401800318250044120508040411680030690219003480c0c41c140e075908000d400d440003480d480340c109001d0b90070002c000b0090702d0070b088290789103031b02400700801d1580e0a0040c10010008066042904 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 102148417 1250 102147167 102147179
    0x18060d0311030f210702030a050a0903020d0311060f01080303010605070f0b040605090708070308030406051b0301060203190e010e01080a0f020c030307020105010506071a04080f070b010504051305030403021c120306 94
    0x11141c42c445101d980300071390502014a80000680300389046900f0090784484100b042182d40c10703a030340c0c806940131038200e000a00307050b0080c180300d44501000e800d907952903607811501110600d080c480c41c1816441000104010341c41007020701302d101d10841030100318107000d0302d401c02e000b6419a810340d1040d42d00c0080c0603004038208501e030000e02484007d0480c031840c40c3c41d039010300d00004202522141d2200d0001c0e041030303e442041804560a0399200f616941c549500030342e240c01011f0500e0942c03401c0050000b0080c09200f400c10380d00c3c0140d4945140b04a034100442c1e40c0f0b032003d0098801c030f907212240c413644944c103070010b0104d070341ca4000119100e241904000b425160180e001c1d50194404000c0b940100e40d80308080018103400c44060310550b1102d1030120410301c2a00d0030182031080201da407200700100364400030304031042242c0900c1079031102c40d11400b07208002c3e80020102d40c800c01c001c200509088070000496001100d4600d0441e14645403142aa50742c1c1c2a0000000d0b0b54040034446 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 102149667 1250 102148417 102148447
    0xd0c120314070206270705130902060315090f0103020f0d0302010f180204060902070f0803070203120403020c0f0105030108031c020403120207030c0906050607030503130c061106010518060d0311030f 87
    0x740c006000c0400b00c518081d49510340c480d46d1170301074540502015900c0000710351094200092159000d02199901d117071603555401000d81c40e400c0c55115903115008a540c0310b140c406143d050b260003c01d251407092442c010020380301a012070480a6548440d0346130b507604818402c0d002c840c00081c504450781101e92040108480c5240c02c42040144180981804034140b0b40413030640d1741c2d01104147d969283c4210507031031400358250016001d01d4150402c8109a80418201030303c000580710314410418030001503900d400b0034000e51a96902c240460710038464070240d5000e10201c816001860582c990b214101d100c5090f88182c0c01583c09180c0c10000c2003081003141000385900c501c200002810700e0001100c901c00c104003e13040003004004550042901b02826802d584d1124060701110b83d9400c010300803d0341615680882d002e001c0000515040c208000802c42504003843e690580d1107404001d0b45004548058040003128447c2d40c1c90410200020000030b501c5a1a980d1030f24010280c0000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 102150917 1250 102149667 102149701
    0x203071202040e010c09120812010909110a060516020f060705030a080106020a05030d1a040501080c121f05040327090e151612060b03060405090d0c120314070206 71
    0xf04680c9841c280e4038005501c214000203a40200080054000842c02e09002070f01072011100c103466564000060b840000d6481100300605c913a40721000340241c0010403071031030301a2003a100454010410600d42106c242840014035100900d8a005030401c2004222135401038601101d03240d03c0052651852504885d03403600400c0c4610003040204070729130350703d5104d014236058185001d4584a24050c902e23a8900c42d505100d1002d8003c00c41d07036940e440229074a500b4845103a0248603040790661080304040b901032243c21080c00d5603a1101404241d4500504004200360b0402c9517041d00c1c0d698490800d5001c2c00b60b2414400ca50304ca0b541050074480442d075060310381244603409010b58134440d0034011469640078100c98060780d072003104100191280c03102d0a84220415181400102c0c2c1440610091800390800703580810050395090a140e54465103060303000089407134150080300007000641b030030361980002d04d000b0480c0c4459040d01038262009a0b03040015800810412138a131100c00d202d00 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 102152167 1250 102150917 102150941
    0x4050a020306180c210d02010f0506010e0604050607020102010e0d03060f06090e070f121e060b0702060f03070314040f03110102040b09060d092a080715050c0a020307120204 76
    0x80076143c60807580c4034020144075010340302e01604100c90074460304e443c0e42540007060079200b226202e42030090080c1803c1242c041c04601d40008513030654490b01103641081d1018203071525150900341001819040018100d0441d902e40e030300d00c04480c90611040301c501189860208103e828610f60542d0344030070342c001008100c4a80c6003040040300c1d005117103030843c01504000081c4c6034001400c94403504421684803000b42444500880410400304e0480305c046071070010450342c1c2c0c95a0310440d8503c107c8d04043c0d84144240007040b41e0011540056401c0010381c05e000481c1c0c800c24605000c52030f0300f1a4282c0743c400038002c0361001d040c2c020102d01003000402008516003800c10040da42d01d0300491405901906021480403100b9455500c482c5e0610340000c0322502005569091103034100c4441241c0301442d104203000100c0c1100010981c0555120f2588910b505401e401c040b640754100303100030400c40c800d0354cc0d040c01580742409100c003d060400e2140840c800e03d03005000c2503900d000c40c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 102153417 1250 102152167 102152191
    0x6060602010504110420040f061403040201020a08160c090c1d0a140f060408060105030f0106151407060e0303012c060105070507030b010902030a0c031a01030513060504050a020306 79
    0x3c0300080c103041285400640803100010100441800c00c1da2503904480d215141482c001408a0580149400300c0215040d13a034034420015840340007201140001c4e200240584e0100b40407000085441c405800c03210089080303589003c4054652084084a6a0102803c1a0f844042010440d0310607000c10844040703640b100b40b01100c070008289082c50921400c00c0d007004c290f11a14040c0c6d1010807102c0f110000507d00d5466a8903186800d48a07042881000d00c01c0c4181c000ac01442441030007aa07086444640c0c01c1c40d141c2c015a48240d4880b104661800e03094030302086035400041082c440d680400003420011516507051013034040ba101d00070410a80c800301c4002c0c155118250804850b80c1c880d10030700c0e1180e1104503c2c50014680f0710135400050900181b13000120b18602c80c2e5002d14070555002c0c80c00d0105030780300f110940407141010800003003070603000134650903035000340c010541220161456403903400072500c40800319001600c084500e908000d070003605510b001c001148e00b195600e055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 102154667 1250 102153417 102153421
    0x50a030509060f04021002010f1104090605010c03080109020a030e010c0207210506042d0f020306010506040b09010809030d0c030212010e0c07031404050a03050a0c060201021312050705030307080403060606020105 93
    0x5121a402c0040c4001c6c851064400401c44a901c00e40158003079507044981400216102d0f8003040d400e4000e4007802001c03d141c80000541c0f903100e041075004403070301a111010b0590a0a507200003a6100c05400420b040e00c079030f0f059101d4002403140c600b0404155000c0d000d03103400c0c0361508010300d0801c034130003000120708400c140100d40d0109000b0740081e40007500703a1001019501d10307101034101c668132004000140301d0120501c204881d4010b0100d00c01c6081d910f0f00e03a01d40b010011107029901a000304148148070b040c40c00c0d4005c29885400c500c000d01203e003894155a4a001a40d00d5500c403100000d4010070340344407500c044165180942200c804000ba24074080f00b1200c1c00340103030320000c0c0802080ea100d00381903501032022500600300c05803074408119141e082640e501d02c2008021500d0841ca408001802441032080d104d62404070b05840c180d00e0318240b458141c41d1500d90b01980c61b40500d103030010305642e04100074124648a9061503403664610b080ca40102e440690000080d641071400b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 102155917 1250 102154667 102154681
    0xc0f0c0609030714152719090c0905060f04091803050f03130c0605120f01030c050f0109080d08100f050102121b01050c1312080d020f1306050a03050906 67
    0x340b0481a80c03111009010415034400004005c2d98005010042c103110008450b90071884582c0c400c1000c4280d049602075000e1200c05010315404d60841d0a8502c5241c50f2083c40041e116801112900e001882c04d0b020f002d4540300000d100782e220b4206003145800000b800c002000050091010350012000600004031030307910301030101d105001e0500e05070a400400141c00142044c02d9654454200a15101c000d440d00c8001d844d560204102514060080c800640c0507100c82d030300310741a02c0d401400e107021980b134101441203035510b5000c41410302c1207a00000c198010300b0010030100e60741981d5440d02d1803e1040020f403a92049401014071040c0b405020300907079800080859420543c400065920104141c100008600d086280a110f5003401b0900c0b0341480d034080500a880c80603521520b110740d456142c02c011721141c480c0100740c05018000040141c110781e02030680c00d5258403070705107458100703c1e204a040c51031307030018008194041041910141d040c03054561001c06100280980e0030511 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 102157167 1250 102155917 102155923
    0x3060a0f0606020a02060304140703051005040605060f10030519020c01091407030b0f0c070209090601030204110a090e0601090807030f0512040825050d030305090d02010c0f0305100b0c0f0c060903 86
    0x900280032030301101102795980d0001c001c980000d54100c4152189141c55190701c80c0640f4058400392550b90910012459510b000c2d43c00c6290400002c207140c100d00c160742c50940c0940401804903060b508030101c0c61000c0c40080c0000c2c485003205000001c0d800c005480d001640342602c1d142200300703a00900c030a0002400101816400103540c0e0b1050100c0c2d03650101c0c0301c45512440b03a0081d00300c09194284405c24800092250592344215810b010b4a508003000011038024032180c10000789a01c0003c000d003080c6403800d9604150185882a0717501e844a49507464140e4070351044a0203500d240f10141404404d010401d65100940405803506d49000315265540d200c0d103540c0a0800e03201c440c070803405007030f0400300d03401490041c003074010110482c01d003c1c004000480c0d24a030680150b4103411610340c418070502d080340c441a100c0802d501100301d811402464014261072500081310404642150307800007400ba1001800000d000c05038106a101e420880e400c1d081c5805410b084c13124640594000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 102158273 1106 102157167 102157171
    0x3030818030f0a08150a0b0d050603030712050c0f10020705160501080403080a06050618030c09010807050111010f0c020d02070806070518040b03060a0f0606020a020603 74
    0x201015403a4400c8407000121040c2c2004410364042c010700c0c0d9140c00142c0c019421000e61464804035100406581012a0b911004140c400c11341f04540105503215005401035414051f00756699076400c1004040041401b001140061071004d08020f00140090020211100c442da810082c000a512102056070140192001c0030540341488441d10112030060703441072050307540e50302c044400c0c05000d858266142c0c0c4603000000e465550001400c01c04100740700d200400701e1a0b004061030210654080c5000f002c581004115070840420140c00719070b0b003030918100094110144900600c68801c080c1d900e18907026001280d01c2d400661070075000c815808542c442c50b200d1406a83d41d100444010740040e400300001740c1241d0a10400f814260006400411450040c00010b4209401202e015240e03e595411086606c1180d000d0301c40100424000f6110f04450307500800d50034440 = true := by decide +kernel

theorem cover : BRFrame.Cov 101978417 102158273 := by
  have h0 := BRFrame.cov_init 101978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 101978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 101978417 ≤ n) (h2 : n < 102158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
