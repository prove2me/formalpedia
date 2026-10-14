-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1345
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:29:39.622498+00:00
-- url     : https://prove2.me/submissions/6e744890-4d07-4521-8361-b2753799ca07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 241726618 ≤ n < 241906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 241727868 1250 241726618 241726637
    0x170103031e03060509042306010b030c090a0f0807081b09060411090315150301021c02070f0804030c06090b070f1401060f15020c030604051005040201140d060501030510030c1203090305060403 84
    0x7c072440407040154000c03207a01c034000602c01702c0e1100c0f060b6134204d03210a07095600e0310b103942c0019189031259048140c941c1142c24000890a00000340d0300c080b640c0110079541c0c8080059103092a1115414650390000184804036565007070030f134404110f4010100d41941001c1d41840060b05091100540c7d4000840c44030601803400c0c004480d10080c2c5808400071072074281d604266000708c0c0e003031b440007112495020030200140145c040c8280040780c0d00c8000c00e071781c1e583c90b4030304030f843c070070940c091071000070b500c104040703640801030702212103031078000308504030003500c0c0e40d03e8204070003014180c0c5185540b141e40008184501e8100e801c003405044c1100d00340041e00503402480c03e140c0d00c40c100e2003940000203001c045100802c0d46030404500003404500c82d9107600068981600040ba5005d0128000554031442c01d0154060710580300243d80a10054440c03025446568a050002918440001104010040400400312607a507c00e003442c039034031a525110365007042c100311015400701c1e107000b2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 241729118 1250 241727868 241727903
    0xc0c03051c03110a020604171608030a050f07050d0f151211030d05030a150e04050109050601081f1802060408251a0c1606020d170103031e0306050904 66
    0xf040740250032000110b04003019001c0080d80c44070007034000382420075144007060000b10141c6c12900c5902644505010380d02c2e961402c0549c80c0d00803200c0d0503081d89010046902c072001d107807440f03010b011503584141c1001c103032801d218024010350030183d9106030b5803405c1e4009030b8042d201050007090411b0440030000c2080c00e100c4201c00e09080341510030b42103950031006050700f1a00782c9401540c07050300007a1b40c86003401410140419504611000038844040104000c03054120400091055081d500240d3ba6414050754500d2541c990404111070f0070a0300c185609654050030408481030200c41c07081c60141c021408551050300f040304983c02c007001d10b10b0644031141c80304001c01210542c804010b440e0035000c3c0e80011070091103003003541d800101d00031031500404c180540345070712100e06096182d40d00d4000c0d50f140c3c08000c4140204070400c540401c1240702d0307480c02c2e040300e4040d1100741e0500d0804079668942c10030120000140340c1d440f035011504e502ca1484162042c2c0c2701d00c014440304010301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 241730368 1250 241729118 241729121
    0x30209070e13020c06041203061a1902060601050307030b0a2d0e0c0405040f090b0c030603010605060310050f031504030207260c04020d020c01090809012c010c0c03051c03 75
    0x28500d02c01c490042000003210309002405c80c1c1e02640095070003001000d0000101c0c05019141c7c001c4540f40c1c030800f003401c0c9039a0209d004000040c9084012405410304040a90f103440e011103681c0c1c041001480081c4120f4043d41000340803090003460711319529160700b9201c20f8502e03401c504412050402060203c0c09203617074200ca014064540e2004180d00d04103016540f10301c541c0c05001e0145480f1a007522b045e0000e9000501641e5101c00982081c0c07424110080407078208542d1390344258203012000401e07007880011a401000e1105403092a541040180a0510081d20a240d0103218a5001403490345003859118041c074400e60103417401c20b24040340440d002c80c400d80103c41c0040a15518400d2010020301c60181d008103560240e1a0380061034400d0080c0512895000f055081c8220402000380d144024881210242c030b524540032400b00c10009400360302d2600a0803e500003a001d801e82d800368290b11100c52081151008060301d0f940d5050074204080c401c0164094088054040c0d00e806 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 241731618 1250 241730368 241730389
    0x30a02090102061b03070f1e1d010c0209161b08030412090503060a0c02070f060e090703110313050115090b010e030318120102040f060c0c09060b040608060a030209070e 74
    0x4c0500120014080e000d00c050b080c400a800ba00030300040800c80c41c40240101c5000060399151460302d9101e411600300544884040300900350b0744034104074402d400d5070240d9a2985c00c2500680310076101d580d85200b10114401560011092044204004144181c01c50172640c0319480786da089522802c1c0b51508141c240a004005002d010920406100c25200012910391107562044c000c2940810070b0b1059040c010286c20400e80364071108004900150002d8121504502c01e071134500e540e5648480450440c1c2110100c02100c0301d00700081a9034059101501c001603018034000518140b4000a900c1c41d0406a40a2802d03140c031907007000c584e0360b004460048006404c1d0081d40c40c1c0407449000c00c1041e41c0b101d003138030712030550703801c100c182000258180c40280075000b2019400640343c040180010841e00360466030480c0490300030a248a25000d04402c54003c3e00d007560802e410940c058441800040c84140c0001c0c2c0e00074004056520341811901400035600d4022406070701e03c0900c4600d0b0310 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 241732868 1250 241731618 241731631
    0x204060c060605030303060603060609041104080d08220b0718090509012406030e0c04050c120a020405030303060f04020c010921030612030806010203130b19030c14030c0f030a0209010206 82
    0xa0082000325141c8c003040701c1e071022017190001c0c0e4070000c0c0000540100320701e0070010040b910100e400708172034030300285d4000300203110f03102c0700201e940e000ca00c0d46484c6800e1030803000880300b4418502c0000c542d07002c107035003042c140c1c140080040054500d60031811615844070384c0003074449040c0500280c0070b110340c20780544510500301182c245102050242d549034441c0c0010142d031214601900b00c020712541c5141c44000700180041c0c02c10901a5003281c000f0b0a00031089043c2c6008954000d42a1085030201c540140256082d541e5290410044041b194001600650200019100314001303216040c806031203003c00200c0084810002c0706c030714055000c1c00003030500d45542404005401d00c5419a04e07503251a203500d056035410700403401d6014403640d080034406030b80e00200f0700303600f0840030304105800c6210350790000c907642d042182610b0600801c0e00114089000c3d0113800b0341c400004542c0308074800c40e42031500301210445005075004031640c1c90302036400f080c0b03802203690510803240c0080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 241734118 1250 241732868 241732873
    0x907060905060328020705120307022404060c0e0409120306050103271b170c09040b0f0901110409060f090203040213090204060e0c0c010e031905090d060204060c06060503 75
    0x504500c0d100d070707001c84c0c00d02102e1802c0180100a049921540c0441c1c2425501005881607100101042d503602d41084d507244001d40200656040000d5840100005403c020310903481c00d521a40c031850300900840b803e603820030403032508800c096240d50140300c003101d00c150690081c88181c004014216075960300b0950426003420761050038014a0380016072030302403681e41d4484132040b0b890680500810000c4810000d0301c84500000e014803c00c80442d03000b6a04020344000f00400b0041169580040340e0060400802c107000c10190a00000d08a502c00e80140000603c0145142c070364040780c04c55800b002507079413140d005002580340c00d100c2500400f0380d03520940c01d41c241a80010f0400740351562140019642d40750110640d070b103940103480100300048141443e400c12050300984ca074070640a0a44660a040c2c0d0705084103000400c8030400e0080600c15169001c0b520000c842c1a48080c000560000300d070b44840f404150a80700410080c101c54485001180d154500301c800d0b1462584118031a8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 241735368 1250 241734118 241734121
    0x21005010e07141303142a0904030810081f06080a38041103010e060403020c12070b0301060801050a06020a03020a1e0b090d120504110120010509070609050603 70
    0x960032031035034261110200000c2d070311040b484c2d6014100c1c0315140c1c00689115162004d1020110021841503400300c02038140c407500a0038000d509240c1100d808245400484074030020b00440d21800381d064004048007400d49185540d880428074003649403146525216018003078460218a500c1114005c00c8154050801d51215494003011000280104d00364010881300c00b084003140850700014481c1c0740d00c0f00001c941014101002d480c003189030054040e40c60001160301c1400c00098140c811a455070051200c426648240000c0c100d0091103421240700d00715000c500200c489000c0c501070451a9a00301c06076140c0010010200541d511080c00c1d03401c01d00c4500040307640880c03280d040c0c80c2c101625030a41d082c2c000e06d100c100c0c088600301400d20803412052181003003020803480d1b5507299581d035010503480024124811554281c40041c40385002030020300055024404820760b95554000e02007241d9840020b050075110201d9031038082d03402c403000c10f0002030303008080003018040a031800e07403c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 241736618 1250 241735368 241735381
    0xf050105041410060e01180905040303050109090b07030209060705010204030f020a0b0c060f06010e0306040b0421050403020906240909180615060d020f0405030d02010902030a1101031803021005010e 87
    0x80c00fa8a000d4042004022585081a64010b0301d20080c10060346444052140e030b18601c80c00204030548088000074103000000450038064042c0080258000101080548031644264000c2d804100c46680008060190308041482131026000a500810101d070185107688100308002007290462009500c041c400c4410300b680004805500501c130300b01c00e010b2034a42c68016150717420600f4032580d25210300010841004504240d076402036100e040c0054482c0d60080405402c5d0441c8202000000c1d0f080c00100050319140c003450f6001000039003030012240c261034812440070b0600a1100c1f80e01c200040641c8c06052000320b031a400000040420111440e80005a40390031028204442800b905451098190750302c10885141c01400d000c11942d0306280b0300003403a940c00c0f6206407846401001d988041d528018020080c80c254000c1c0a044505030030740d92000c130184043d407164100355032884048200075040015000c0716001e90013703e402440300914506454050f000080032070000030501c01c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 241737868 1250 241736618 241736641
    0xe0d0207060c02010c0204110a031116030e06070609050f0c0301020405180a0e010f0605040608070e04080309150a0e0f0d0801060c11130209010215010f0b0c030903010f0501050414 79
    0xd90700280380c25000002c590004840d200341203070020354040e29061110301480d903804e0003000c081e0100d0301c0a10400d02040c450031028081d110300f4010441e0810201c20000740714943c580384500d00104924208101500e40c80e00b203074403120049509500200700707220140000c0040c0c1030450f20482c000e42c5000c2c1010042540414814202e5401d22552000702d011490513070081c030080e0b45c04d01c1c0200544140340b18044083c01a0784501030103140390040104d540d11020a4030b10a0340c501e02c0d81d80340c05880310b9079420300690004000700d07540d0242420710600c0088120440e0f00940c00f9050203c0c04c0866140450700384840e019041d005075114800020400344c001d48654112542c03070500010001103030404d6580c0d0801ca0790403d6018020200c9400724030100d601418881c402a0300721180024803900019a210003802502100c158010b0100501c1292400500c00d82e2603403415a8123250102003c603003034400103030010701c240b80c031a40180b2803814240b1a280c00410180b41c0319940742003100d00004c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 241739118 1250 241737868 241737883
    0xd08071701080a020405060d02040c09050f091e0601091a03061f0c02060a02160b0d060803041a0f07080a0801050f03030703050f07051203160f050f090d0201260a0e0d02 74
    0x740031729121000104140c0d40c08040640030340e009071040c4600503078203000810549950043c1417140445c0c600c04002070074040355042c03080d000c124048010170044420b040060301e00030b04260401c600240c0c00f00b83e200f2840710b1000c403100d080302e40c1500d0b811b200c030030000360400300d0700c1c1d02d4180f0501c40c443d5101940d000850400c031a03010754a1a98134480030208034145403075540c2c00901c000b040100042c901090700300820408070030200c1041600e07107803960140c4921481c03040300442c035210041d40f1071b041002c50050044590440c4e0003840c2c181c1c141d4500308160810509003000c200010300400c0b050808180110004800702c010303603c2d01c1e10654001d07215000e159000204118041ba44604200081001d646104681c01c0c46135228a000c1e03041100030822040e20740c0c00038860102d22902c01d8050030a56a20282101041e8200300c00f41c41031041842071b10901381e04221aa4070a81c800b102c0b02160f02c203134402c18440c034000c50300e01141c4c008142e542041484c07140b9480003204684e03043c1e002c1980d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 241740368 1250 241739118 241739123
    0x3030706050a06080a0b011a0a170c071e060e030313060b06040819140703030806190f080703031d0a0e0c07021e04150f1a0c0d08071701080a 62
    0x401c1c1d1942c904480042442c2c0d000710403a40b007603924000074002800c4085048400180c0782c20000141d10b1031703550700c90142d40b01c2c01c00130030104800301d442070030344d500c104c3e80c020240301b8418144440c54448156400216190a54000b100c0d00804103000e054058604196115002075285013130540202ca1025130358580900701581e45c69034139071a5513071041201d0082c00408101d03000000141c100445802c440001115002c00000402540e1040854520103c030780603220703d601550b54206000a01c1c0f170404402e50030b8aa000da012170081207214680c00a00b040c038009190072801e500e07001d808407c4030030182c03419242c0180301d000070b90748030711282e002e59030780900e25103550b194024a06640c0c00344110096002c2d07107400c10a0300e403210340e010000007110100e50a005c3d40c2c64002d882d95004541d03024841000002404c24000c841d07400d00d030000000c000d6108039140c405100319031400d00490340d0300140000c2c201400c2c0400030307034030410303810010065003042d050b41d503d07040e5070303540d07800320324800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 241741618 1250 241740368 241740371
    0x1a06100f1b05010e0a0b0709080a020f040207030201091b090e03090f0f03190303020909010e061e01020c090901091716150605061305040614010e0f19030b090d0e03030706 75
    0x500003044820341201120110701300c11101442081d151026140e20100c40c00800201d06810003e840100003c40c005101d80180c840d261582894007800041d6002c518140c042d9900d030a02c0000040c218003c1a070301d2144c1860340b105540c100008401a1110503007090000c0d8000d1082700902da03541030700c0c809180000c58084111200000120b400e107521030a050745600f0520048400707054058008280b4403608503035404d19683c0b6407400c2600b40754191017441d0031508001c0039000715404116000b540c04414012a18640c811100040d94500b00b1107030400165101d00201c400c000e40000c2c081c22110701c581129003841c5034400e46e4403d05549403400f0340344074441c00e40e242c400c17031440c2e00100c082d007809420503580309010f124074103000040b03111313a9010b10f00d02000050081c0384500c0c0c007581208140d54480b01a441e490400c40f649010711603496120068803010703105182c5a0060740002d601c544289601482c1440025007085d10710500e82e814468680c0440b12a503402000711038009510200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 241742868 1250 241741618 241741667
    0x30201020c04200309160f0303020c01081e06130c05180d020112020a03060e0106021f0203060f09061f08070305010509010b40030507090209030303070c06091a06100f 73
    0x81c90380f4203100201342c1107100300540306c085242ca4807020300c041664000d80880e40e03009003100046411180885d04038004d884420015620550312010131a0001001403402c00190180d6586808a802a408a074085480001c07040e403000b400c12845080e09004584010060043da00040c00902e0005800340d240c0d9400254100118000ea10000c05400d41c0e075180001d03581c5420303020350b0b5901103540c4c14008816031880305101d54020f0003100e21800e00640001c0c80c024010301404030204000e40541d90103081520420907264550002c0c90000c105559008140d06014102a084647c1a080b46003d403000d8001032000036240d0045504841c0711340344020301c40ea404440004051000c210f540c1c11034914071002d17119003100004607000d90740944140c6601c01c3e40e811030724049100e881c4e20070360144c00920005d1000b500401e03079281d44a0180e600401c2d01119031340c48454250b03505081c07100c0e440b200700a10100e41040000e01c0151241d9081200b0440081c200c00f0340420406609d017044503440c0f0a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 241744118 1250 241742868 241742881
    0x15030901020403050105070e03010e0616030209060d240b0c0a080c0c0a06020f0c0301091112100905010906061d04021009030b0f0108160e0c07020a0e10030201020c042003 75
    0x5040702e0003550054002c000c60300700705d40700816521404011512030342c02c140c058400305002046040c000e160404100da240b071f00d501404c0c2c02079040318440540c42007007407003051300f540c200e80620140c201c07802086144c070360290103104c40031694a42044004000502c10410560300003d404610150880c3c4403d4890701045081ca1406c0e49007200d294008001c0d00001030503540018100d0b46501c044025661f02001c9a010b0508803041c1040250250b54040702002d040d040c51310511356100780880a94407205502c1000d00d0503905401c00c112450ba42d07607075080781806618030600002c1d0038110200800c811142083c0540c1e80400b40029100b400e0321074110340c42c213006010500080d6031051044003140b400202c07442c8a0340d000d100d41e541900641c00c140c1c0c5109081005941a54a0400042c907540c179440c0c4100d025411485049070040c100080100303450032140c41c1c0c544904440008007001d1811403000909044000d51098001c41c10080c0040b10034200300420708003d07140505081d125a20700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 241745368 1250 241744118 241744121
    0x20d020303191d010c12051e041205041a090f010309020d060c110d110c1906030b040612080705210405010503190608070303080f071d15130302010e040b15030901 71
    0xc0000484030f601e0100c05e0482c1a4020104c000d2070038011500f0801a0b0740d034034148105110701e0b220000e140001c4000100041c2c0d0010400608286514000d0b09203502c403241c81c585100b864045006505001c15407055518042c03072000100310080c6014030802405a01089050301560001803500b900c0d0702c404040a80318807224407507036079081d048841c034844984014105c4100702c110403115014245480c1080e00b0b00c0b1440da50920414002180301500d8154104e0041c2141400240d01903203032000060400504412164840d0103a520035035a021540380180ca0700c1e8461000c2e220003110610144003c40e0040b080d1800c51340203080440d0b49903540403a040c40c01402d1a03c811300903113066804100000b0000b041419288030f41c4900019456802d02801e80080807100040004d001010034145104207009070102d101c006010304004481c0724075100b8180d0480c0c1c3c00c066000300a014100300f0f640c2e00072120110010240d07000c10414007070a010038029a0002c0c030303158a00a00201040d002c0d00f09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 241746618 1250 241745368 241745411
    0x106120c090e060616170403050c0a05010e01111f0606022505011110060314070617040609050a06060b09040f020906090f0d1406150603131e0c0e040201020d02030319 73
    0x4086502a508a095082e900342c000340400e0b155032050b2b448440301418100d4a05069030816128546161003031401100c0000b07141a4102090151581501d1007241c1d040290002d00c66040000c1003013400d102000b40782441c06080341a244c0030200100002c40707218000344003a1002860003951180c001c00b2410f280c0080e901e42020707820300c1c01c0c00000c144400c0e03910030b020603041842560002c1c0c0ea504011078080d1103c20524141e00c0c40c00000c2000500c00d9070000c641d09114100340d940c80344082c0c80d0103045480755809150380c02000211042d09140520071121b01b80c48140b001c505240420010070918040c0c1c01c00d081c0210409450390000f80d441841402d4400d900c00c141401c25988a800d1a803110801d444000c00180030003407400349032500d003003540e203e201650322842410480b41c88007042c141900203400c0c0c881100f4211000418403089035580a009000100c2c582802c1c544002071030300c000752418001b10b420520074440c4800b115481c40e040351078401d0000c580442d840d000d104080d4038 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 241747868 1250 241746618 241746623
    0x3050a050c100c080c030709050f04060504090c05010306060207060c12020102090d0305040501090e010302240c0d08011706010b0406030906020f0c0109020f10050a0311120106120c090e060616 84
    0x1070700d030026404520b80d030009200d0220a540300a240d0329510803007149404113403098004030310b42d4082401541003051811200c0d800082021482d140d580d8041401c03580c11113000d07100364082e800140540c0d6010300551008100c544010031296140c010010300d0140200350042c5003107501c00d81002c07410300c02d405a039080000140190740c400090710f0b01900faa44144585030124441d5500020340740c54039019581200e03009000b1080350b000341c41c1012000800b4a5100746032003810f111100c40c07160304112161942c0100e40311a0303c1c43d41030540d000c0c1c0c039441c54114007000d9880382d401407100380c0c1c5040640e4212200d5080c040303407121017464a10040c1c0900005800b1301500030460a42c40c0f20150410484c15000b9500703220b52100f51000d01c0342c0fa2402884c400d000c600c0412425044500c00c0d8090951400b000f19114100909040908500e410a0b440700c000505046004c000007002c0348200030325191141000d2400ca450080100d001d000c00a14091050360003040d33554540d1068000004010b5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 241749118 1250 241747868 241747873
    0xf0a06021b0d0b0c0316080408040e070c061a01020606060901021905030409110307080717130f05010204080304170304030c0521060c030108010b0a08060a090f1203090b07030b01090303050a050c 85
    0x41c100f1138041490304100d40b2001155030b020700c203c1e0124010090940541d41100c4858505410882103440305600a000d280410903c0f00503500881d101d44600740c102ca03c9004070340d0320000b02c00002840c002000c0c004a11998080110a031b8036a00012102c035201550490460000302d00e09026045014aa2001d0304160411204820304142c4000845c03090f1450348510149844482d42201c0d01e80f40212103000440d081d2020401e0b0058551520703070018400c0c250406580240d54038107003643c00a034041d5440341c2c0045401d21204c40c0200d4001c0511034206c1c0114100f03441d54495140e0713402a4885d0134014418601009054420148900d40110701042103c1e05810448038105030340e0f000b40b1440005502c2d00c5d031030241615256810030100e03003c83c4020101a200c090400d00103003100813046507290010000f060028810300061448ca44d55a1000a546201402d0004030f003040142004101840c1542101030b0380e1b040420070058940600c0c00300d4844000c0a810f88091151905010319407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 241750368 1250 241749118 241749121
    0xc02030c0d021e0613030e0402090406030c030302060105011404030b0a1803080612120301090b040b030d021506041413140111040f0b03010807032018060f0a06021b0d0b 74
    0x1540000e940d07484076040719114845801d41443c00b5403528401d40e940c103201e0f0040d22248021034400c501e50070f10044020001480d10140034006405c0319070f541c0c0b049031111124041002031540602401e40180028200340303030280800c054a490342e01c07139400020714007080c07180072511a030301c0c070340c4034003032034440c03440c001030404210700b006410300ea0b040f00d0603071050481c0000502002d40108451110fa020103600740c1c01c42e400d00f01d112002d420043c1d0f80319003244e62780c00601504d40e000c01600d50b048078150007400c4c000d0030f510035001c04003000400d8680154140801000c80c004984503407035000d0030380e151111a0441e9440d00f0b0a07040c0c0c80350905207842d0300f004110001000000001c10884034002c51030100d055954202403200d000034420303002a500805c01c10004602d0740c0b907501c0f0416012400411840040b080029407240d80c48103404810709501041120504191100158a10301155000d10340c5142510080da20303102c1c420b0395617084814105d50007860700e401e0035160100358021141c0740389 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 241751618 1250 241750368 241750393
    0x618090e030d050a0c0c031d090115031808040e0403090302030706030c02010b0904020a0303080702120f09180402090705070503090a0602161d180f1204050a0602060c0d0c02030c 78
    0x9a4002d01d4622a060b031402011031000003d40c801c0743e00e136000c50b0301c440c901c0d41d5854909407180f40c0000304004c50405000220f650070b03038600c03885902030010411100c045208040c070080840d000348268144501ca500d5880c408181048151303030455404610002f00743da0781d403804446d50320340c50f44002c3d0984134840020818503015001401c0210700d5500030051f80c4004002c00403403c0080d180690085442901071003c0703440b50303d5065000e08140111180c1d0005141080400d038040010b1940260b00400c05c00391514010410700005900521030703842c40d0a103600020b40e406006000039040c46000030300f21040105c14800d4840c0c80a006025900b801d43e81c660107500c511503040200c00c40c9a855502091200c8110f1700050052019a200700150303036062140100354481c220f60410030301c60740505100c0918204400d20640c120001e48a44a40ca030106008069490350040c5003550130010810208400c0c030016600e01803609840414403061540050f030551143c900000164080c85010603176 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 241752868 1250 241751618 241751623
    0x6181419060809250306110c1c0e06071703070e04110a03061a03070e01030b030f0a2003100b04020702131a09040b0f04051e01090506010f0f0618090e 66
    0x300701c2051056440ca58001000710407031000c24503e0700d0b0700905034101440403403103070351003100708079000540b1500d80b061005082d072074000d0627450800c0c04150308901c40e13a4560302c510051503440c000d4806906160841d075a140603081130352050030b100c01010002805052181000c42c11160018108000f507008004d514442035010000d5000400e040a01c0040d1b0144081c0601c41103a50414142e800e68884403030403103841c441d041926041680301c2000000b156000d210510b84070103400d0003011203d4051078070545880d60301c0135200941c0108600345810380c6010802c04034004100350002505400c440c00280240a04400a5042100400040c011035480e520101c0d810010709000049000120200160784204480080001664002080c8000e03640500242c01034030490903198105500081c03008080203070085c4010130380d1500c034410280708090008a002d00084244900c1c1e40d0704010088010308403070310601082001c0760191081481d0b02c0c1c0265401780500c4042030246040039105c07981d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 241754118 1250 241752868 241752871
    0x3130803040e07020d090909110a09020a030b0102010506010c08130306020307080907140604090b0a210212010504080715020c01020a11011503110d080403080d0c09061814190608 78
    0xb080e004414020550450000401889030311340d40d51100312035400d107040940030b0500d50000300ca2441c0386245910043d5100e14158018110702800180c83c2c1c1c0301040e008041c0e8000ba100e041c1507914013401c0c490540d9201030709a82068002c603002e07580b01c45030340311a00031449603030000c0c00c418804814042960381c041046401101d00e07800301c4185e291a482e17034401d00025000110351003507042004100621054002071599800140700003442a65513004400b1140c0e002c540c0340711400c41d0400803046107081203080041c081c81c080200038034501a0307101d600c039100b000405010740b1001980e81d0f2b140500c6030100c4045154203002075454545451001d01016140707103070381da01ca500740030f4007002d100849154181226006001c192807001000144004090b407a102030305d030482e003080040081030748040107000501c0a2040016001c526020007001190250071017820003520900b84070041d0f04100c0e00390261313518140803200c0c0e40c1d0840001200000c43c10303141c80ca400e410040c0000d11a40012095 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 241755368 1250 241754118 241754129
    0x12060405070f06022407170103030f12020f07080c07031a04020a0602061504020904090c0b03042f0f1807030504060606090f14030c0a03060f1a01050316020313080304 73
    0x10000c1c0c0751030303e4043e0b8403001446404c40000d443c10080306030000d00c403907a654000c182c40c10180b0400e0fa00341181c01c0e44050903042903020610740460000d21552003a84842c106c0c08031a1b0031405e2001d842c090b11080d21034103001404500011030045021101407000e80003c41d8420100e01100b0042400c0c4410b01d0b100711b8003680700d03080c289800a83c1a00103e407080c861088070003681a102e1100c802c010094000301d008d15046a6122890000515648100360240840f05031040d01e910701480c00588012103452400c0c01101402d40c1e001d0b080030111112a06241308440c003090807d2078901180d4103d158080340d81d842c10010341804107054055000900450240b4002d0007601d803146070560302e00302c0328422254203584428040221010400c4103407100103000b015195813070329102c00101c001d00781c5e400c01d450309039a800c84102c0000541c403680e4021400c0c252120081c850800020781540001048032014001d8010501e41d1584240110b491102e00800301d07905160703e84940c1e130340c0c0f0380050051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 241756618 1250 241755368 241755389
    0x6050603100617040302340b0d0c0912110f040f05150301380409080a0206010905010b030a0504060f15050114092101060801020f070303140c0d0b1206040507 69
    0xc0709070300410320b4140c0700300c0d0150010044200d0488907401f101346003804a10f0a82c003020654506944108402401002c1c50080c5a80b00c0c0d0844035003004070358140e00144184024041c04218004000d40c4125000da0020070084040035501c0c0450600b11640d07001c00d521138075010011100f0550396210074018a5a20070804c0084d1200d0289400c07150710418015020031708030007552090b0f1443e4859076500c90505a070700e001e8001d00d40414241c41000f0400c0f01c036a0b401162001c0c96590404c410340c0184034506090000754034181c4051301e144009080a89110b807108000350900110750440140f005400c0d2040000e81e00841105110f950103004242c00109031b00c0c080b40240701c801007035400051000700060b0500e036001d503030340e000840c3c1610700182d03035500c4290001c0e0000302803002c1c00c01002c1f111000740ea100802c1c980103084401c00c02c8803c110404680501030090000400e9584010075207000240b20400c02d00002e01c03014902400303000c14820705e0708000422074041740b01c07811188400d12 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 241757868 1250 241756618 241756637
    0xf1b090307060c031805060f091c05070305060a0216020103090218040b01050f01030506030606040902030a0f06021b010c0c080d090c1502060105101b02131d06010f0b030a020706060506031006 84
    0x207840007401c020700c1410787c09803061000e0503044051390020164003800400a80c0b5801800240c442d54440050055a10381c0007088200144082404007581c003c021504c01c502d0208045183d800000e001140a070400d50f481c0342c6801151a0300481c00340b0400f0b0346101c2d032810320f0711307240580c071008003400b0300b6004182d00e41a501142d40607000d0a03020b228004c02a00c01c6d80d80d15424000100103008081c0c0e814828843c08070041540360b40159516800303403c01580d03881514216802200340b070b41042040d6850b008001201329805140d40e21003170740c000000c940d10803040d4a58005800c402c02d02404804440000185d004a1644005014000c07a001c2d03507a980c0ea40c808014691105618810208071341249030b940c40c2c24003c1000e030300c0d02d10040160000c00711050102c0112a404c65040b201070070000700d456200c101c10403005004000f074031311011143d414003e071000c2c58000034141c0000740303802282280400c01c06400a0740603080141c41c0750380b02c2ca070500b82461007485a10070784021659040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 241759118 1250 241757868 241757897
    0x22060309081b0102043b04020306160324030b0618010b0d02070b040b0901110903030418020409090c031b0b1812010509010c11060f1b090307060c03 65
    0x111903416802158107424614140304048194011081200d03941d5030810001c140c452000d0f44013035640c1680c030f0130307003601140700002100000015000c040800c00104100401a5000a507003a403003440428440b030680d1150300113401900b0140c05501295500c10050070442d81d4001d074601c1203902030703044609a601d4106c00c2c002916619034080d208016218014070051007000c0051a40a0500c0e400507c0e00b034240d160a403d80e081a03c086505080210900c0300c0301009004501c0d800340503500b81468048041c000943e684520b215004201205030700c2d4041043d803950682e001071002c00414003400f50700b4580b4100075001808120b62035080600f502103010300400c444401d4a00305143c1c1e616118070241089404100400790503488003002c3d81d5401001003c0c05240d024162001c00490800e1100802828155614103098007a03800b050400c00a200c004660070b410200810210030700001545001c6000e1180d40802605403144032400904140c0c488601c03c8028040e40d01e8030030006004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 241760368 1250 241759118 241759121
    0x9112106010206040210051303140d031109010f090f0306021207081905060d0f060c090801050613090515091507020a0b0601080a1d15070f091217220603 67
    0xa4440c140182d01c0580094011705040c503800f820000f05007426820003036011100100034680d0340044440140e002c6601c10301020810141040c1c0d81d1a080c1400300c00003481c00000280610b01c0b040b4100481a41481801400303900c188000c0c2c0401c03044080300d151a41400e078060350140b0040c1449000705000240c5161280005a00511403022034512100019541002600014203800d81c008008491940040c40c003241840c41c092050f1400309001026800290004190390b00c0310b0000d904000410800c3e5540b01c05803044510f000a0000d44401141031035442d107005298a802d80d0708104051000d5024000744005102d01040100c800950391450308a0316403030120002840c00c0030800c0807449540c0210603440d80000081c500059080031000a400c5112141d075107950386070004c020302c03814680000340d1241c2c0134a01d82080703420341c46856030060030710550b4800c030ba144c0d00440001008100211814a418120faa103185450307004000f951180000c003082c005182601d01000001c551340203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 241761618 1250 241760368 241760371
    0x5150a030506010b0703030f1d06090102070c1503020f0a02031206010504350106120209100b070f021f0206060316080709020d0e01060803040e0a090c050415091121 72
    0x4075002c1c140c66403820084014030781281504400380360f2a4110b03241c800c3c04c0f6200f041e003405001c529600206501c0603e4a08100f005051480700d64010003510340441c81000e03100c01184e44400008026110a02e001c41c024007410130803103030402d00054118011a8000040c000b40b091840c4440540d07140d00300151082d105601c10151000031f80440c1c005122102108445031001201300c183c1510b450b01021400c51315141c000300c0d1440e00240c80755096080c04800c050303101b4a00c076951002d0074200625020076008080c8010090001d1407000c108544400d40f004480014104814141d180c240c0c030065244c200445070280030344141d580101602c101d001c00300040b40c41c0c1d10050100d19040030b0041001e984002d840c030440640b80c0e20310150700202445000014034251014544272410a4600e0b11250030142c40343c00780a090030800030105058960200071228101c50010384a078804000035410390160348000141c1c0d2900c881c4000404001000740031030081803810401002000c4025a0690070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 241762868 1250 241761618 241761623
    0x10060914040207020a1502030c06090304080316030e061c0b0415061803230d0f0f08130b0726040b010b0901021c05090f0105090102120d0b1305150a03 66
    0x400c9200100541010b6004000301c41c0003812042c50b16071034805410182c184642e0490041e80000b407120164902884440d41200844d00a9407a2a14000340c540c0d0364090512100607007600f0440400400d07020b018605150400581820384501800000000011b200c1c2e0018541383c1c10305103c0200340c54541316014040303183d6801c008400c2d091600444a102c400318040f454181ca072040807010502040f0b81e40c0355010342203510313641c000303c0d201183e041504948401003407003010321840c81050f4001030240c0440d4880d107054485583c8407620b0f181e030103500b0417000c0c140c40c9a4009201c000d690025045041a96500982001e8580e18a6081c00d107042142c026004034910750040c46584810f00082c041c54034148101c0d2032400380c0c07840c83c45019110941c008d010400005500d20310b4140b0003030080b041c0c8000d013881800c001513100081e440b0103428071501e00c05030000640c2c20041070700b40d11030344a010000c0c1c1072022070020039a24100a0034151080c54050010101459031031038502a840156507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 241764118 1250 241762868 241762889
    0x201080901150e0705040503010e0303040203150403050d11040902070b0714120411030f030a0f021c0203030a0507050d1a12030304080f0a0903120c021e060702010c0204060b0f03100609 81
    0x61906410f510704110180c0200c0c1080001c1000068654090051009218450010b141d9a0400b4810107240441400340c0803030200b0198200300200f074108050316040d6006580100d25100c41751022005032085400841c915880030403030303200b40040500f21a102d10802e44031403141540709400d00d2414042e031848140c1c6a8607590000300015500c0d40c000341c1c0118041e040710944514103090307a00390f40060040b8000114110340303401c600d503810004201b824100c441000141040d02100949a1200a0801070456240e401081c2e10901c070320300712084400d011104101c00300d40940340f04221301c00301244c42c0c859814990401d80e482c50200407a4011980008000d2500f03400f6201c4401940000c2c0340314050040c0c00c01f0020208400d040002441342c030550352410814124410400c1880b51184080301800c01d030b2015192949402089139103150302400c007000440c0c1d0300d10008014044c0b5401c410304150000c54003040e0ac0c100c140103580030710b092010801c401925004121040203142c444d41e400390 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 241765368 1250 241764118 241764161
    0xd0c03030518032107060b0d050303070201050105190302010f0e0301020316090506040509040b040807020d0b04021f0834050a020f0105041101030f020706050c0306030706111e03130906030201080901 87
    0x484032400401318140311b0319001c40c000c2c11020016001c40855201a20390f5040002000541c540c207100700d5024040c111000d00316414034542c0400051098040241880f02d134124095207030b801000d50302000c20000b0000d5581c0c0ca00305450060039410a1004000b1526214001c41d01e440d246040c0e505580029141c401e0a40d195110503000c164040d20903940d17088100060005038540018000748107000300000100c6050900c1807000b45200114a41c04ac01e800e0b400f00305903164400303121074100300c1013007181140c400034091020201d0064541140800704400c40381c51841d4029020b002882d0441d000d86030007940c02c403821803d80d0300450380104501c01c1081d040d955913020f070707204090075007002e00c0040c1403080395910400ac481007984c00d5603c50802001b002041c0c45c0411150002c0c20081c508280352981180c65203030381350141c022501d241c0a00b14a4508210b6040082d80c0c4923000011085520326620500c6034010a0305000903800105448002451701e8014041c00c1100c443c145c640e1b409a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 241766618 1250 241765368 241765423
    0xe03030a0302070c06091a0d0207120f024308030d02180913060c110f010c0206070203040b0301120f080d05041b0b040308030439090b091f0810060906150f05090d0c0303051803 77
    0x108480140f6140ed611035940c0c0801e15000400140510b40700d903000c016603a8610100d03108241c59002d0449116070900c4007041207680c40c80c07514900b103a6000c100400c8014425a069907010807036461444540306c3d6114060401405401104200a01e5002e5421507240c22804a8480c416401980c20404003040100401c414200307c0000d524021485441e14142c03940e41c181080d40b108032500250ba850b4002e000502201c02c07407001c16003d8400304181c40500d40104091640560710016149640101c000f80038400e551080d010302010800141104112001a8403540e2122800c001c611201602c030100d038003031030361240162a4800800f0100607a950090500449052a01d0794049800003030002947c20001c1088400c0075844000c04941c242c00c10005004681450307100d0340d00005640000d02445402903c0708020710b10501c1c041c2e40e40e82c001004030303450b01e43d1b01d04010031521055400000381036005001d058030762101400342582c20b0b030000404d0340d1116100383e050341100d142d0600160 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 241767868 1250 241766618 241766713
    0xc020307032a0803040503091f0207050d0204020c0a03090e0c0a0e1314070522030b040308100315050403021006031e030e03030a0302070c06091a0d0207120f02 70
    0x1280c590707140085010880c10f80c0c500c0c64039001903404131403503400400d050901b2301d0111100b81a4062020f0300404c20340c02224000e50310f00ca588103107401409800142d10564440750101c1d1580c010a004583c0c0c408a5841c00030b11040d07451190302072000b02030021450b03040d580f504030b4010304031035030360307032140342c035060100705040c4e8a5182c1000104e680d00c41080c0b4140305030a4141c85041c081d22000d4031018032125070910407903501d8034003404410034601800080c0b20318003001d8100c2e415140546c402d68030b15403120382c0104a03803c09441d4615080b40b4075149201d075003000344220b100e0341c2900d504528481c442000d480c09800010f2040e0100b048155020302d008141c546424041d01c1c003003101d41941c2e03001c03900b1a4054070240300001e80010f40b440511204000b43c20090015192074426917141810003105900b10601e01e00003007400040f442120b0190b0340555241c0394020b00d680d0840e091112006c0c0c00540c3c03598440003d4001c00001400080c050051000000095200302400c41000c424145 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 241769118 1250 241767868 241767917
    0xa120203060604110909250809070905100f0e01050114032404021213140d080a021c1509060b180402090a180507080a0b03030a0c020418080d0c02030703 67
    0x8903812003417217942d0855490011050080005012015116441d0440c09400d580b014103400d003070003242d40c180412200006061012030b00e99060004241c0c480030f25220b1400314a500003c92000c95580c00302d030720154060054101c034803d0b2900d10001000c100c0d019940d004c01c5480388410324080d82000401007103001416800030005000500d000c09030031141030090340036121202012082d5010404011140031403403074691a070303002481c0d003001c0240d0040800380c00030301d00d0000c25000300e00b03012956400710003980c03040c851500600c090a15820030384c1e000c052600c24080e1541c180500010a5040b44013205c11061003070229041d04807170b04003440007940c4144481c94101c002800300040f04091079040c5c16000320f00c041d001c100703401c0c6014010200d00d009021504054900703030750401076907030001c11510a1100c5003805203180e0142d000240007003180e240643d02e0400c004100508000306407008000c001500b1408201001c44540203d0b500c1c0101c80300140803422452030480281d00580304034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 241770368 1250 241769118 241769141
    0x190302060d05150604030b04140f1b03010207061803180501090614040b0316021006050612070e13230114061c0c121b0206150102011b09050a120203060604 68
    0x309400d0b92040844c80650042d40b060700c222816500f0320040118150307420400300304030b100824000d207444c0c42e180e0315000d03000381c0c0008449041c0041c000d1505c00b9010b5419554004078104590b2034400c2200341110441d440c2140080c510320751050b10703584030042103025104180d461412150600f401610080c6c9500406028114240000100400018000c512035009030000c1030b540c80030342c100641b5000c20000c0500a41d03007841c000340804d480f0502500d0400c4002045c44400fa01c0c1c602007030750307041c1031004000d4002da181c11510030103041580040303400e1241d000783d800011049400408070f049080c0681014600c3c0c046502a6034030704000035041c807401740107058101e514401c5004040b205100f42410200d0205107121640495910034121303442c402c4c00c461561420101002916172000424041c0c0441e1544071000d1582d20035801284007281044410141c016403003005031a020081c03003101d200d0845920301280c0e510300751650825441d40903004020f5a00c0e81c10401c4090040707000c14 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 241771618 1250 241770368 241770391
    0x903010f0207080702150702220e01060f170f03030402010c08040b0403030305060f01030218040203070e2215060516060b0612040507060f0503010e151002030405190302060d05 77
    0x80c1100450344000d0110b140f256126540c0d40d101481440300c103205864090304001c00a10400d8050307150003481c0e0109440c0e400085058003e14400c0700d00519683c000c00301e02d5860800d0200d00c403440b90200906450140660144070000d101b01c69a503103449401d084070540090001c540103500540c100c0c0c518030700c03550440b81000d441b0028401150820f03401a000203803100c06022407030074a090020a0b2060a20b03095203480380c5007084030224600c0c80300e84c030b002e60340c0040050006441191070400c0072000030110041112200204141c007201028419000340c44c0c23314464032500b92810321003c07034241d0303162541040707298140401c0010130a50300b520340540f81c450800403030b03a4060007860340385025040c01c4000c0c10320f818010301e800215044101480362075881043c21907000003d403411100c801030084100da44007100011042d0344480550380100c001058031b14101e4000c405081035601c180e50001c030351017a1004401e483c6185100183d003003001040100e41500058200390b902c444503521 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 241772868 1250 241771618 241771631
    0x304051c03022b0e040207050624060724090f1214030106031b0203130302060903010902040203161107060504090c020115060c06050a05040b01050105181804140a1502090301 76
    0x7004403500c200d809003006105080b02801c0f244a40215400303101010903101107003031191550320203580740005418002e20030000344500708600000c611041d0700110103000f01d030311203040d4076040001c00002c660300000000030340c0a16403e81070a05c03070120201c0d00189904007240540e2100000c68400382c20510400c440c003040400e140c1c1210f001180200038980e000515203d2544036222091441844141103420802241520102502058055a8044038a69074450b00f00001030300410b13031004000d400031f001004200c03010980000055a00c0340544400c001c0301c4200100030349905450003800003181d000d210030300c910074043c0d2010300d280c0598000000c049040285550400d4816884080010107034200e0400b00305032030140300d412150b180024411820240c0d500080044140100c6042020124a0401100c1000c0000c0140744000c2c2149130440303102c00d210501c04104440540d0b20f070303403a48003603040050005074020f01c00381c010400209001000060784069840782074941d601d50740381ca1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 241774118 1250 241772868 241772893
    0x40209041e06050c0a0f1d01030f09020409030818030307020d0e0d0b0a050a0606082502030f120103032c040e0307151a030f06070309020a09020d0b030105090304051c0302 75
    0x80f48600400d1a0200f25485941008004041e5000341074a00e0070400d0305083c620392502c1400c0401e8003220300742800b00741c948a03550490028542c0f0b080181d80541030035020700502d41c00001d0365010300d0b4481025520000c255586669070320090b42c81e10300590090b0007030719035248110f00f40c07031403d04020130750801614076455000b0f40403020345e07006210b15680c50900203c0e043c0c0380b0030304004101d181080d03a154903002507182c0c46004080c0e0059070885075000c04503440c070b02c240111004010a0403102d41c83c3d0300d0484d84110864400d00044001c0b816640140b1004410b244e0100e50002582e03c440305c20300360101c244000381c2060845100c4500c018410b00c8001555040038885201d428800050701800d445500180000c40c0200580070390000b90003006101800304035640d0000c0e542c10003113007055051021034003886180c0c4c05040f00d2031000c185000e410344260008018480200d00a000e0b988911441d2900c1e803103a48101940080a803080c0b1160001800030f4240b440d020380151480e0700c4858 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 241775368 1250 241774118 241774121
    0xd11030d0f1b080306091e010902070b1018110c010c03141503060406020a1b0f020301141005130e1e06010605030709051306050a121a040209041e06 65
    0x41560300d01050340301d8038000149602041c41c402d400c1c92066140300d160b109440c0c07050140b0025081034065010100051013a00304003554003001c04400d8140a100e41e5100c00400094118400072030703c1002140125000e01e803000200d405444c000d60a04140104014028005000b1180c810300010024820001020420720604103410303095240451030401032000c507544401c0c000d194454002d40c010070f03203045440000f403c40d0300603440940180c0e290300250041d47d0084c100a140649084007030402e02c2080030340010281a00d209500030300900c01c1200003003980000c201c503442159540e16500b00801e01e485011030030f50450201c40028408a000652800e01034500c840140c1a090328241202c181010040ca40c01420076140ca2819030505540003000c2e0038580c400d075442003142c15241030030500d4a5021a0040fe40140014989595aa05d141840d0444181510000450380020030150340405503607205660003000104140e4a541d01d108200c02c080c1583e4a4030401d04043c00001400c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 241776618 1250 241775368 241775383
    0xc0e0307060e0901050402031e040c21150507020c010309060212040c050901060c080901030b133602090408250c210f14030c03040f03141204050d1103 66
    0x11a655a02c1020400b8140400034038103a02c41c0340110301c10020050f010603401e5a2000114800003070313641c2d035100c47c1045000c6134110313009059280d1085c071a0301c194520351840780601c144102c4500d00385800f80840803044450454490016070840700f41c1d102558402d07400303425407912031100107007482800e0314a048414021034007100c00900000e400d02051901004e000e00400140c84e000084c802141c1e2020001d0007102d02080c1810b8440c03512421700d58491000303083d003105031401049a049990360803180c000d410107183e042c0148604010700c0c0c10b141e00c0941034003145c0240c84ca080d00d4a90340c0e540510f50b444482040a00925120340e100800703194480000f0950160324840c0d03056041c42c42182410a8204060303101610b204504000518900441c09401d034010780303100c80b64241c0d1070700d003400c40c400c04004002c1070000140105030000354810140590740a54128003440f403e40d100c0544e592a215040f030701c01001400204914680145c281c004544501c0c4450840c030020008a45040e03034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 241777868 1250 241776618 241776629
    0x1f0f03050109020111030a0e04092d11060a080f07141206130504051e030c0102120115020607080a020f070204060b0d050604180b1005031f0e03030c09040c0e0307 71
    0x1107500340c00b42990303400b100349802501d600d03010350f02c1c200c07155001802c0e0140411015000355182c602001c28440100740b40145ca011079100d0b0202400c80c0c413030401c04103a03045011070f644000702d0107000c00c43c100002610489203841e1205103490300e40070808081000000c16500401c410071128180c0d130486c030800b0b800c8421011202a030f86060410420044180036017080d03c08500d4a002c001c0800c0000400d50714954141c018644c076000e030403032030500f10310417911048040d41c000203801015000001c440b50488995140c5141d501905030000c036140d5905a6400c07000030380d0100800c00240040d030092581428148000d860030b0800c1d03011400341ca1296010f009000004101104c040c4030390702402c3c0d07101d1412502005040844001032082d9109441c028250306000c2d40050b94074402c01c44100b000d424010203c2e0130003821003805501200610109000c0d050038400c259075014400010f8900410b800d0440e107040c0800c41043c000140102070201d2304101c0d94100e0291180c50a019100103003c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 241779118 1250 241777868 241777871
    0x50d05060907050102011e0b0a0e10030201030f0b0918150c04051002010e03180103090b0408030402122b0309061509140103051914010501090f05070c0b1f0f030501 72
    0xa02281e6030307401c00c4040e5203c1410769040034075034400c01c1014120b0300700c01401d81710b0008590390a4804034410742d0940d0030120015128505018003182e4190030902164800d13601400030072107000c401c5081c0d0f42807116042c2c1109022010a108803010048440040c9600044452219101020b9401c9841c256003c0b908018005024032440c01c01500208045940c0d000a014980c42007144583d2440303000310343c1c54089042a03107003416a1294024242c03407a040071707040d001820300d400d151409a0041d10124803074580410920b0f0200d102040005240b00fa0302040700307504502c40e109252060740300c500d0104040c2d6403040b040004a15215070400360201c0364240641e80e042040e40402c48030340d1482502190785040c01040019000140415481200c0c00400700000580ca0300382c0c4800c05007010300300707a942000004079540c0031a1740880c03821003983d00140043c1d1690706d0b007034807008154000540309140c2540022401c240c01c550700c0e005002c3c040c00c900c80e910307543c1e5003041c88211203400441e181e9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 241780368 1250 241779118 241779121
    0x3140f03010e010b16030f030605030304030501020409051b030a0504020f030a0f12050711120114041a060603040f02010804050c12030706050c2503030924050c030c0d0213050d0506 79
    0x5101070010b50303015100da4040603140c031041d56115280490100d000400300b00c800c600c000c00481c0709402c03170001050040c040343d40b2581c40345041d0b07010f9000390080304142e40c074103030024100c2c42120450300c00184280d1b290514548900d24010060280140f05981148602031820a1a2400c104695001d40588826203140445140c41070750b5840085141e4100700c0244000c0b0301090680f244680900800c030340c80040102000384840c0503100103014080030411060400007803015054428243e00c150038070100c000e0352000200030242c0070681d03014004c0d034000480c1760011b5005140031500240144100c403100e846150002e51aa9110503000c0002d41000c100841007002501445800186118001d81054490025011400003401d0507040d000782030340303006003454042c1d405001250740100c1070209504540c1038460945030072040c442002454000060420f850312030640b4010111048410300d0a00f0149400010703400c40301154000003451140041d240c5c2d0794130302c07004c48648900041d080c81d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 241781618 1250 241780368 241780379
    0x130509060132181e01080d09090c030b03010606120b0907020d0503040804030804060806030d030507050313083f01030b01050409081201080f070605070c090903140f0301 74
    0x604506034002c1a18503940644410b03460415140c2c0d01d02d00d40c80070b11909500d0049000141c2c0c3d003102d0f010501000180d0f406110758100c10f0491580001261446031119990ba4804250350f80d100216450009500702410301200c03460340c01c10317004095986800300c1d02d034444400187c01c4486075848040840c90040d42e00c81c074508075000d207840d4503004603240c0816280c881006501e44007480b145070200000000002d08000440c41550065034004000680301c2d83ca038580a8031120042d100240720b84508861024480d1003802200d10402455807a1400e540340c11815540c0c40600d01d004940d0700c0b50900c2082800c3d950700c0354808450000342410103009440d28400c2c142c0c044881d51044510f0502c0d0010700108d80b0000905045403c1a2000510b0b212503003070a49540c010182040440e1407400c0000802207000168582076940c640c4c150390455541c1d20b0155514412a0320091141d0340d1020108600c290301c1c0d000b1038006009060021100303502d904210b0041c1c1c0440003400c0744c480f0201c0148032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 241782868 1250 241781618 241781623
    0xa150f06090f0b0913020609030a0c0603150909051e0a0209040506010e0c0a0504140406050d05060103050d05040f031106040f030812160507150e03070506010915060c080c0c130509 79
    0x203841d6019180202103003405174094602070b0008002074054040040c0300003460b18200030500c140e03500501c01c1492940c0b50b1900038060711042c0d0044485000d280b1000c91030000030710440d00075560000042020000386035000e14903844501d544030040c09913001e16070241e01c800e0310072807180c0e2254014007955030400610310784100014040f44045401131281210350381d0000202c4050380c00c00810a03030304400c500e002802070111030b007040f504020031020100420000203522416244100c0642d40c8000750503c088840d8007540c440c6d010944aa42d40c2000410040f01542002000c0585045d10f00341c0c55102144400d10264421103074200f000491000400a1040c12074120310840352513018030b815a24010103600401e00050501d9802e40314090591515a100001e8010f4400940351580034504209480305401d110300e008a0b42404d4441c11034000707a02102e002d9940c552148040481c01d5114000903800136050030405200e00c0c440502c0c50703500d07010b40559205100340003142074500305000a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 241784118 1250 241782868 241782881
    0x2120115050a0305060a3308061503040206070501020a05040305070e070504090b030c030607020d030e010b01050304030f03200403021819020c030906120601021209030a150f06090f 79
    0x6032129903600c0c1160807503000301200d4080d01d1030720700801c040d200c0c400050103c0d002070b40040300e03079440b542055039228007520342c007a6070215008a200080c1c0320000306a0704000212000c40c1e10100c0e40480c8001c0c0c40c030b01006550014000380c546810448155121400ca034886200344001c41d03004182001040340c1081010090b06a003480d44683e41442c07540644240580d0203001881c684841c1c248103030703032002c000300002900300400319802c074200340f0350103134444042c60030480c0000d0410800725104241401400e11401042e500e0a2840d07403140c070212000c90001a41d401015143d44010303a040e50341c079005a40c4001c0c1a88159a120328610402101d02031407070180d40c10320800c030104042014000203154441c07103102409640c524000182038151b1040b040c4156200c1c801041c3d04182c000b01a42e880e200c6d610a800f2074071b0b401d990f19291306190054203034195140d44034410050015000c8050703041684030848001c0380b407925404502c0261a06900200e40d5650f556140c02101003c038041c85 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 241785368 1250 241784118 241784129
    0x3040e091204031e0302100c0315080102040815091908090108090c01021b0f06070b011d0c031f08060708040c14011202030601170c09090f090307020d0c05060d021201 73
    0x41c41c1903d103995064080c00c0c03034840490849041030006041c90f000b130140c450400084042005100c05098001d0001c1c41c441d0614251440e0111002c1801281403080794140d450810060015103101905800300c1c90300109040380d940240c256000602100c0140003442e0b078841c003080340d190701e284000108036600c020400341b0680d200140c0600700c0d0341c01040060314001c521410300d14003454800410403080c00d026080b0782040740041c0c04810b10610b0300c0c125060300c0c10392550f100c88501c8071403041da003480180c5180030014001c00201e4084003142d1441c010010b20000510006070b03954501e9401c061007120200080b40b10030007000b0420140803400e0002d0145440c85c0381043c880e940009004440341845410015800404150136030702404200e02e400d55661a40c4200e0f10f0007a220003626044130140501901d0240c0c08100429145141903101c0c110820045041c0813003a0200580303030060b040241d95404007150045029120f020003003184180b031410150391840d40156400c07500710142d010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 241786618 1250 241785368 241785403
    0x207150903240e0d02011a040203010302010f0e0f04020a030509011b0c06090804090c1e0206010612020304060921020c030d02070e07030f1d0c010806060a0f020a0503040e09 76
    0x9000103220240e00d41a50700c401040d8100e6400307000b4900d801041850303d4040544070700c04418801560540000000710010008100024848020703c0260700003801700a011422180070b400070244100041d41c8500c90042141101c2c5000001180499120503003400004e074442c3d04222401d007007401403030380c1e80c030f5410219401c000300144001d0070703154442030081c80603481381d5240e420b11544809440107400b2042040001c1000c150010b4024284000544a1948401100c0c20070301c3c00401d47c28101c82903038941c0d059a03a41607200400035070000307000311081580c0c2c240c8900070139206801f09503480721100502480482c0401d0103071800603100e45451107540070300c0304262031070750116004080b103142070a210510f460b186030a802400404140b400030f01e14240d05074584c00784d0780110a40d141442002e80303400245460044958900c00c550a64101e03208100030110380788101c44150300c0c012071340b05941400e10140e9900742150b0250f401a404c0103109400d000c4102d03401d20044d460060b0444c00f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 241787868 1250 241786618 241786637
    0xb010815010518040605030d02031309020309030d0915050a0608011a060702010c031b202e050f0d060e010b070f02100c060213080c040b0d0209071707020715 69
    0x2c2c80382c441e40d107800c1003071060f4211451550b1604c1c0c1041d0082c0c00d000b01514110181018020350700d401a0040c11145401001300007400b002602c21240501009005076241a042c0032418000d400d008500b168100400d041d000c045100c240b154a00891100c100412054504003d0303a00f03580d41226142e1040ca195002c03450030b50b8a02046500460382801c6c8010711213141d06058461140c403000c40122030000d400801e081041d103100b1071100580c5900341c110f582485030305010459800010001541c0c00018000103440040304803903850b450103207890f5141003110120304186802406140f410306840e0758042c403075450381c0f24640f409883d9040700d907818400395898641d4010200c2c54060700518818419400d00e500c92500d058040e60032500c150350340d0808034407411b00000340f48141822406848810080d034903290107001a40b50000f04054945516602041071b6140c01821003001e1111940e070000704203d4155402e84241c40035005482214900400d20000c0d03c084620360b402c1095204 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 241789118 1250 241787868 241787911
    0x2101060e120705040902030c060a08040507060e03030a1103091003140906040f14010f020307050307020c060a02072d0e040c1202090f0403021203180f0703052a130b0108 74
    0x42c0540849104075030110f0195460300109040c07040549105400503800600f440c4550b0300050240c1c00366106104448084e640d0341422601856003420403a81038204005622149204991960340c26036104d090340e1030f1003051000aa00b11113015000000b00c0d0315000400031102506041d2903001030b82402611640c03500b952220800390105900070054121000000070040382507004410f00c440d0300008540c0d900380a00301902607003007105c0d2400144540b020310b03401810302400352001e44032030750010f00e4007904100e4070441ca03403280008495101c030800c21903108414041400c1c001041d2129020365a800c145c180300ba219500b50300a04ca080820b044544010385600344190b0f805022071251030070039103492804a003401000020f03e40140408000d010300e1400c481000d80110804004a5551080348103a40c3d449034032a00c009022074000c0d2400f1103507080d00503441d8006500013000d580d080750000c000603041c1d0100d110301d02c410659807500d100017540c1080103660041c040b880030703c1d880c16648 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 241790368 1250 241789118 241789123
    0x1051305060f07020307030f0302160303060e060a0612270602070c12030e01050f1e0c210a030504050708010c0201060501080c1603050f04030f0b0a110408060c09062101060e12 77
    0xd0800a040114869424850278801e606541e010031008a00f081011390320706005019040074021030f80d0300221304021501901d00f110b0000c0854805c1e840709100b1840b503160210081c56040b10324082d004203682c8030703c0520420b540f00540755204100040c0c0741c0306503062000c0c83d200580c00c90a12020b8115044010035049002454094002d191060381e8070725001e0b040d01b00d80181c905010303c0d10043c8405a00420360140a00810310790901241d100f40da1401c0b10b4103010041c180600f01500c820800c0000c4240f10f40c11195100d401141101e00c001d40d140a61401c5070800d038203c0d00140d6680c0c4c410f10866900290f010740081c2ea500c0028145800d600e056a00204034101c000c051000024680030459440c80031344009582012041c11140c0d680d08150020300c034102c400c5081203203401200f501285100d0180d40607520400001c100e55903070755000307207420307400361040316130020080c01007194072100c000c00e103804016298cd502c4500c1d45414806003090030158552031041c40d01c11807091200200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 241791618 1250 241790368 241790377
    0x16081201050d26280320030a2c01021305121005100803130311060309070e0405101d0607030528110a020a030e0301020f0406050309010e01051305060f070203 69
    0x1c0d210054154003044010a169101d212540d80401011002d880c203414041c070855484404c043c1c605203e41014082002d03610307500d500ca46d41c2c0d0740600740041144400503a001108000100c0c2c59600040f9550310301c9040e10000300d01010240c3e4000a400000c203580a82c5480204000d890024201c400a1131040d02e407800c0b61011101c0d41da942c000111441900d105c40d800404241d41906d54981d5000074018644074140000d4401d68180906814130f410304101f283e02c2009044c005e402c406080244a00c00c0e244060030941d502d108041e002042203030f062080544841412200c4c1f0710707103203c04642504200e8001c081c1701c1814540020403274a40c0f441800c41031202d040c000240c1c03c107081c0d4141352008042e071089080c81c00c1408a050f0140c1030b00010350640140c0a5203504040309880010107003030740f103020411801c6a106200800800740954099074100f4a80000413420014102d0b01f103003107400481d400c001c038034980304601050010038420180c0020801d86510301c40d00e400705010756a4400d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 241792868 1250 241791618 241791653
    0x51190e0715030b0d150c090f060c12030b0402041403061513150b03150a0b0c030a0f0e040e030a030b12070509041a0109050709060f0906110316081201050d 68
    0x80316543d100c1c266a4001045081310fa010310240300d01780c81012403100400e280e105e01004961192808a4003000c22801103044070041d03a00c46102440030750300c4240704510155420180b58031103000800c80d54990010b04050040b01c1c0c0710010966409041514010300605004403d4580c064140042c4e2100c0c0c2e104103550401020102e007600280301007401184140d8803248501030040b081c0f15644001c079092114010741200da102d24140c650750040c959105840b00c5c81c205c1c0d401004805810741c002c0302800420003013070034044151003d24010405584095036040c02d590000201c13a18555094400c44403400403c1d03500d41207060012590300d540b40001d004031881401c1e2200010b040101c03004c5242c0c84481d0901403102c4959441805a0203440e06403402da0104503158404100c039031240d0b03c0041c01c011036907943c4508a10f0002d0559051100d0028010306000070080ba825002d0608881d5032524030819011f0b0342c91304649101500c1d0841a08501c3c880da54006840c0007040b4040fa4070041c0c404c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 241794118 1250 241792868 241792871
    0x70209040210170414010b12150a0f0911011413031103120d09020123120601110a050703020901080303010b030c0a0909140951190e071503 61
    0x10601520040166012001d4004403e4104005c000d0403c40103c404c8080d0301c002d0042da03500c1c1040080c102c1c000803150074154044241d1115000d900300784c0c0c6070421400320000810480708000302054500c6000d00351407840a45c082d030300b01c0356031000e86601541007207a9035504101c1020303042c6070500c1103484080c00c01c0c60034910351203c43c2d0b000e100341d0101e0314008440d00e55a54400e1200009450020010f80c04a214106d01d040700192406403a0240880b198040d403921618104034054800e01900761f0381002124050603100c6e020401c008a5050b000364000c0c13043c0e2740b945c8104602e204e8140c110010a40040c401040021a8002940e400ca0480115540c90f41d8031828101c2341701c98568840b201403030820b0f0030289156404010b0034020202c1340255803d0b60081440741465000c03100c5068040c0000b8101103604403002e4091644c20f40e06420f010004d0200314a54400800c425111852012484c0e101d0b00301000c614031842c00810029006403820703501c2c1c542814040d104a003000424107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 241795368 1250 241794118 241794139
    0x2e0e0103260301270f140f06090601050703030515060d0609061703030105060f07051002030403080601030c08061210020a0915030e0601030209090309030615030706080610030c02070803041202090a020702090402 92
    0x4d400c01e400101c1c500d100c52400300010446080a88016001920307800003103155800400c0c0b050401f60b030031034072079030040c0c681610348821650202c1c01070000400c1c0800118190724959615500c1400414104074200e0021603007030304000200c03044402a034030038031341303215180c60303d14041d0004800c4ea41120303000c4607180e85900031070036070b868540b094000050860250820515241c00e15501450155001c2c2c4c0e41c07800c1c0e9583c1c000065044658216040002c10600e100060081c074018042c100300d00c00800a030f8000900008030141660003100e50140419030080003440030320400014401e20305200d182c1031044140043ea82c42e00c5500600000c0d000d0201c0000041d400c8108004075401c000300030f403c035140c1e0b02d00010060303182c08000101074030a003e0150000782c11481010349034000c03000144903640c81c0e04500001e400400c1000c070034034150302455a000540300c1c006c3c00070b030005140d400c1c0b9070700303403c2600d10400c011020b004008500d10352060080002503220140711641c0640d0548804400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 241796618 1250 241795368 241795439
    0x3220f03330f05070c02150306010311070f0218010311010e04020c0f010f110a0905040906090b0108030a02060c191d0d0303150b032e0e0103260301 65
    0x51042200a146407280110100414000680c05203010380c0d02110104030540340d11400b11a5005440d0f07020394080f8000c200090b9000074070000b150003050504001640c0044d00480015642002c6030540b00e06241020802c1507080c03c1c0025410103502c450001050741c115510f11094600180a450403c800e8000c0000c80d41c41c0c0d6030454405900c008200e400c03501d001c0d034070980603250725004a580942041c40030142d02e4018070603030300c07160b40356141d04500504000038800101240041980d082d5101c1c0c15000100304001c0d1118040c11208010719a50f40c0440d101a1a1020180c0840d0143c4410841c00210b003170a5a6050035441052a10082e45624845800076400c1c4640302c80d9406944450343d44105501a80104003100381d0214807031446644a0b421405804101d40560030131400050008480e441103802480c0000d800a2406810703483c2e40d80c210030b00e03200740c008030f4980404201401a207010003101900d14089000c0d80c61540d03051071061540310b032421408001981818140411 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 241797868 1250 241796618 241796663
    0x8070f0203090d14010606260415050f040b1311010f120c053004080c0a050d0e2805040207030e031002070b0a0c090e041a070203220f03 60
    0x80140b0050a0040200315800c050b20151014140c5850640c60400b00013a00c60151596071450007102c140b4102c20309190f000114600c4d070041081742d5004c80091079410b50072940c460075015980c0c0980e00d4489103480d1415258208010f000ca0800c1426a455a00094160101c40d8070245003031070013080d40c0b00190030035940a41c404011010301030615100c116074030b83c45009000d61003609820309a030301c9020a0b1081c1e000c5c40e081c294600f0341c1c2a40c0001000710b54410300401c107600c0d8110864412900300e450b035a04150a4050a6000500003040841ca40c5020b4900108507a030301c0c02c0f0301c54010461280100040c4144c400d260249030045150020715004042d031002815001e002d8949914072458008000d52000c402100c0d2050240c0129507410320510079010082402c1c2c9071ba841c2c440c1400b0003003c103050000c100b00c8400c500001c16400c0e100800700300c24024032294000315194510500040701c4d100791481d907107154220761041040710201501c3da01040704d401c0701508001c601444081c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 241799118 1250 241797868 241797877
    0x7120209031923010e150c0f1308070602070905061c0605100f0b03071119170903031c0c02030c1b0103060803030403090602010b0103091109060301020d091406070f08070f0203 77
    0x1074086031900400f050140c0190400181c05101a098070035488070281c500e0004e030000d4807558480d100510122500d99180700040c4040d80c2c1428072000305a540d0300303c0924141d15604180b0040c2c10005082100e40301c00d0040d50f4105400710f41d602d03580b40321038035107100269108001034000e503101d1010503110b03a481101140540180041200d80d2034951040c440294400d0300c2c510002a01070a00e505030301004206203220003980d40101d0560000f1303490700c2c1681d040421005400789010803100c0304540d03080000b41441500100300140941040041d082211075034500002035400c1040741a0215402040b110404500090401c4040031a08012401070115812000c01480300105000034503800400082c12035405034000e0040307094004c0110107071145500000c5c00005456541e984510b4005038960b4485006800141025101c1d4000780581d4005d407801c1da5034502192000400740801d0203450303400001d41c1040c4400030014070700201190360082c6040c0c10000da04103040c00d028030900444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 241800368 1250 241799118 241799153
    0x807050405120309030f01090c18020417010b010207060207050102031b0f0a03020a120905090601051b03031305160b030103080313020301090c0e07080103031d0118060206071202090319 81
    0x595000b11600303080c3d40e0b40e00904107107201e4411202000c217601014007440401903404000300005500e441e02c0d0341c0c0800c1c44494041e203810780902011800c1f01c01c0c4031104481500d61000464812850400641800f409810140c115000f0340c60910940e6000422910691038402140e1114178007440d280d41409e800300180007403401000b005030f0078507a000030f00700c1e4264050911610190400740c001d5230b40c910745e440784031b42001d800300010382558040d1001e0301d105104040b07210624003540c4801400c40c1e00071261126038410300314801c002d2040411400d90042e041511411940f0b06044000c0e100380414400103015080c000006034100f644c80411102c4107501400030312603005d66260200500107107000300c8102d1181d2a0001d2403a500c18282103040b650151540000d492401a0301451590f0403d2000e0510505010114020284c0c4010b03400401556001c0c100301e00707040c1c4004000b0808a03594180c89070046c00800d03030554012440c10169641310382c00c0190700c032451910307201103080305040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 241801618 1250 241800368 241800379
    0x90301060801020f040302090c030f070c050a0f03020715080f06060a02031623010b010c0210090807090218012109031215080106050607080405040b01020f07141c080a0807050405 78
    0x1c0c1390424001c801500a50b407003210502d24550300c480346800180411a44c01000d041100c005c500c041e40111030014810b0302400948002c1111030702c802025070380300c0004030016807100500700001800d07884420410394080c0b904002905211089094051003e8a52071280400081c0d26000500820071507000d942104a007410003000b5080c0312a08408000c000e4031401d2400a610300c50034010b100d6903405110584820a15804503001d00c00d44c2c4480e21100014040790190200310790780200808801000405005a41e4415860501069240707c9898605003c000c2d0050602c080440b1111020005110000122003c560074100c03068118450102841450404100718012070003003440152690900203004150361841440814031645401401c21070017440b00303010340d01e02600b00c0600c4800510407907001c079013003002042c100070517603101e2201c4841c03540c080718003410058101c0b00216141c5000721031780c00480d01ca001251144032012010020400f001400b401d00131426107000d028064032 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 241802868 1250 241801618 241801627
    0x150601180602101a010527040204090906140106020717010209041e05060a0506070b06031e071509030213020904060b0408010606140405030c10030207060c031b02120f09030106080102 80
    0x70351105041e04031070f07008900b400300d14003582000c581c44801d2000185d540501e800c0da481c812142c003503c10b842a0203200d92400340301c20195583d00141c40941408100000e4070307007041c039201c01207440a90208480b45214401004650740104105040300c0030381004492030b640c2d03242070134024810070106a60161500e41030228107540444558600001d201007001980c4a207020001741001500c40c07070364465030030401e078000034000181b62500004064102d812520650031620400060000c01e2400713a032002e9010040044962000d203001851400c010640c0c900b1600821054442014104402030300042c0e68515502d40ea8840401000d80200c07044e21992180c0d60715000e080903100f9507000440340a80b034100500381100701c4084600050040c00e00884500610140000741c14214042c164248012008560305005005040100f55030000312201400e004508802c000042407007194440385441d811984000c3c01c40e01240c4204540c0c070303103a00e86080080e003d00f1b207640020500f9400441e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 241804118 1250 241802868 241802879
    0x120f0f0c050d3e0f010c020a12050d03140406020c0a0c0312200a020103051003170a1d10030b030f030f03010e01061404060804081215030105130515060118 68
    0x501400c0620031039440ca18140001580541e9092401031100e843d400003550305140b03040500e2a0309980103044c4800a0b801c140c0000350101c260ba4410074200b0100001003041005c184544c1001041502301003003009102850160390990052000f04540d9000803051001c880400c042104503500c00300502c502e980340c2c40c2a528a940743ca41840c00308a02078aa01c10b0f1003d840c81030050b10148000600005619400440140070003030b08000ca03410b01040c5c04008540001100d80c1440b41c3c5c0302185e030ba5500f4100f0010030500500040035000d814031001540c00380d8030310845140c0c410f82d500d804a040e4041e00000b9050039030f4803200d02154400050080002d85540d005541218210040038405a99980003030b03849901c11460000c000c40100010310026005403055500b2501882c04103040009039405070f64040e0058a0440d016500e1a600140c1807600340541a40003e041030340d0019156655515a9104500c4c0d2180c01031882d0800000c0340d507440380c0c081030900704035201a20b25595070381 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 241805368 1250 241804118 241804133
    0x402060424030b15091003020c1b01080c160f1e03090503010e0303040308040303051b1c0f180303020d0e0604030807090e04030801090506280f120f0f0c050d 69
    0xc081403400300f0300f000710350003440c80e120001c20141952240c00916180b030031420000003d24280d20380d0305055003030168202c400d80402480070281d003115441d40d4104889400034120b078500606070030b44c0e4031041155100c038045a443c0d1980c8141d0148104052440c01e00e001c840b008541c100800c6c424544410340d07800c2c151312801082c02c17914140c00810a5100302c03000982c8a00c41268064081600784c80442c000030301c20b62050b9405400343d000c6102241428143c107800e54426586450401c21484008406001034401c1d48102ca03001102089041c08107003000084211117140070f004d15901142d17120100b402c5810803564900810150b8180345840c1c603020701000e0098070480d0001d40e20300004661000780c840e00b01d00454040e00c848945a00e4080c580c2d0241900400654100c03000350031075800c18603c020202e4031480c1c2c400051281c10b0800008022400141c0c0c003450301c402445001c1004a042c2d080301d0618281c00c03c201406024180c20329007410031085e48030f41c4d0000102d01d0a8010310004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 241806618 1250 241805368 241805429
    0x7030b070302120f010303140a03110409020304050d0f02100c050d1515020a08040e040302030712081807030b0705070f080c010b120c0306010501050c0a1407031208010602070e04020604 81
    0x14100c407103104c1d00c80c102d0700c101110702400000c1c0032a0300001080c580c040100d0107820011124500829450354030208503c0035081075000d003100c0c0b0380110505c010008140316118450f0f40e00e1070402003150454900035625090022100340c240d80c3c4600b00e294140c840e07022a11040d010701418001311502e40903003002c002c0349209940104000000500b0101d00c081514018036030000c0c1114140303402c2c18107107056510060700c11415448200072140015041102446032008140c8030032515103450f6004003000607509d200c401845d000301e24242300040008400c140c10861600c0d01c0c3d9140d41d2186403808110b04021009401e000700490000d07000601500241c4001c14282e070845403155203480002d689007500803500341e1580010700188250351003500030301100310100c800c0b42d00381a420b4032501303490051520b02c042c0a403c000781c24400e01088054010355102d452504000070340c50318074000d48840c0640500000149414085070a55032010306a80c00791101d103111440003050000c59040c0500d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 241807868 1250 241806618 241806637
    0x32f01110702180c040311041b092103090b030c09031b130b2d0a0f14060f040e070216080105060f0301050c0f070f0506090a0c090c1e0207030b070302 66
    0x1070700b0f0710700da800741a070340da43d82d00030310244800608050a41e580c044507515034880c150f80056070b40e28412802e520b4039a580510b4445906e45c1c105441c1054880781e071021740c68080c071000c42141400000001c2d03010701c028044640408800f5103d0321503814000c407911482c126940d1500c0340100004480f0340403e5185c400700d900301e9646200f8040702c40f02e0030560f45c2054a59030311521301c3e4800040104c864a41001c10310a410360080201d01100c001080c0704065005850f4144030310758144090301070700240c00061881103030f4443c00c0c0007500100728050322490192420908181010400b05402000702000c4113003204c4402035415211407209008083c100d603003601c00d0801f403d480c40300342010b210b101c3c0076400d0b4244841ca00b544060f0448419442007a00311004044001940042142400594025a43c00c00a803c0c02522810592490181e070307004010407034500316600c6c42c8507800c17a00d24550303a80140c103040840810001e084e410041140d10281c0050150400c00c241c1d140c0c164014070f050740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 241809118 1250 241807868 241807879
    0xf06060906300c0b03161815090306110703140309060106110a0606090e0615060f07031103401505210a0e0102130e270a02040501050d032f01110702 65
    0x810465080394500ca00301284407c0700500007042c0000142907950800e0780311541451034150382e0780e980d00c1c02164542aa0195002e4000c10707608101039000010340780450840000c00e0860400e164580c0e144c07203042c8501d206103ea40c0d000c1c1ca0b48440280454a0969041001005816580d0702c082d00581030340c5580d51910b002d001d00190541e0700840d4072144585024210500300500b0b280c03030030000e40c003083d025000d07c03c282c540400000001c000500900748502d4004407424441030741000c541c010201840703212580c40d20744003009a45030040f1411110082201007000c404820117176002d100348400444a12001d4841d00d00110b1940d00d024001c08035010100321652024040508070700441103204045214650308002e50b901c0c0d10440e035044203000a02e0141003100e00740031784003483c0c00403030540c050300004010400d501d4039102d100c2c01003500303456040c21690655030013428000d111184440700d5040407a20045c1200740034807000c1c0003981500800c41c40001103410fa070301f5000a10103c1c410f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 241810368 1250 241809118 241809151
    0xe06100917030403060b060313030f03020405030f1507091508070c0b070f0206060a0825050306010e0129120711010e03191106040f02060d05040f06060906300c0b03 72
    0x40c101f00301240d1060148c0908568104c1c1590f0301241e90402048030300c82090f400380b1011886640500888003100314113401002d400d8100e42c0c05400814004103a40c00340200a0b408010078800841d8a02141c48240b800410030b80c0d580070241c030400448400585a003c104080007039082c0c104000031a840c0c041d400f191895a9442c1c1007000180c028046d10001d50010050203c41c00c2034a54643c001541a0301c00d50100c0d510b0340d0200c0d2808100340d000c402d04120700d1004000702070515800d10002200826844111a100c800803a030320f20a01104442e44d01d440d500041005125070400203042e48058000d1000c00072000c0050390703e82210044e4002d41c031a02c40920a41c034081e010160203095a48003611090390ba42d19814440d10f04030400366005101001140c0000490740b25581c8560300c41d039003c28207000d6500b40708045807101d401006280c1e1034100c05018040c2041a40000043c8071100180130111003401c07a440c3c0705201c800142425400500480c1d621800c4015603c1a80001001c0001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 241811618 1250 241810368 241810391
    0xf0f051005030d0c030c050307121d0303090f0f040f0c030c1209110d2603090f01060b040519031401020c0f0703150e031c020a02070e010e0610091703040306 69
    0x482401d07524900114200c2d404c000e0019015100103442d02d405201035900b4100107031222401d00020124141c001104006c181c8105002c100340b035542e020082c0d000318241f006890200c5d44403441030000d584180e200c01c00c04146581d4507007018100790307030300c642c1801104000000980034002003440003000c500807240300c4a0913107070307482884425600205041d40f404c2c03000d0180301044e0556801a1445c5008503c2e512681100020711f804a9000c08400c3c2d5a231b00c1c15011590401072090000340b09641041020401c5400c0c1405071070030f50310111507030b402200307070200103031283c40669000402c0c2200282c0c441a0160065010b40656401841550094402229010703213526450000400030174a07000c030000a14a560f10510703a4940c810101c81c50680b1060b5021800380c0a0148000d03041c0e00000da00c60529414400e102c01809040101c1c0c90550401090300e1081c50014a1240650041c41140d030086102d203815100400c49010041c20003000d660b06181c4030f038068007081d03801d18105400100c6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 241812868 1250 241811618 241811623
    0xf070902040f1406180607060507080f09031c0c05040911122503020d0608061005010f051e09010201090219080606010e011205043915210f0f05100503 66
    0x801c0d00004101c1307460110003c12406140f030158030020703084442480310b0000981580300741400381c5000d4591005510b01a02c1450311850001c10550083c0c0080c030920800721035043c03a09070800c0403403101113100c04c01081d003290103001d658803000816040c440030b4584084500014440c40150000204c0c032541d915108600c90a488000550a1590401c0d8400018480e5000c2d0080c0c02e1100c4010491550350302019252001c20360390b0034440303600301d0f0081140d076806c1280d02110101604140d0b003803041da842da880c04209410011f107944540021040400d82c400c0d800019459801001030702210b800210b401680400c50140303046a20880001c200d9540c0690014010f0a005968207001c10320710005c118007901c0050021a001075005100c0100100c0c1e556038219200901c411810326200090300ad001d00a4640d4050b00d2001c203d0307024401c01c03d500190748541e0341d10f00301d68584400d01c0c0d40b40240040900300303100030f0b2242c6048410120340405030022805608002298000d85445504068 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 241814118 1250 241812868 241812899
    0x1d0c040c0f0302090609040207140c0f0d020d020607050f06160201051003021207090519060905010f052b0c090b01032a020f03070c050a0f081209030f070902040f 71
    0x421201c1c0d0203001c0c51446a0000c0c4401c0c200640298240026500454281d030816102250207034111500320654000800043d01c0441c03081328801010140c01011800000c2c120300c0c040e0040c08840314a9040d034039204115000c00b90f0010031140000d44d4494099240c00c0c041e40c3c07901081c58180c1c055260300c0c3c414055240210780000707854403c00c0c81c2d5401c0001c0003006c60784d013100034050307210f001030404054807429120301d01c07203000c10700f4009a560305413045440c41c0d04043c0d0624a0140184440e6402a000c0019a803080d2008100b0308403d40d007400f1506181d1030010041754272100d18904018100224a0844004400500c2030120340380054082e01e00f14610101154000c00d01c04100130201101b01c2c00386422801640c444050301781d00d00b82581d00002090741c004e41d034002c041069042124401004004107480707001083d0802000c3c80d00c445003008144454030b00414a502d81c1d65051014002d80c0310840c040301c180d80d5441c1d5400002c0d40051050284441c00c12100081041d0110a00d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 241815368 1250 241814118 241814141
    0xb030405101a04062615010e041a0c070c080c090406020901270e13030203090105131806080f0708150912070c03060b060f0702221d0c04 60
    0x1409092000c0603000e008020b002a2410000026070802059840c2e42c45228060031041c1c02000401c40700d220000390703107074200e10029115840100256070700c5202c0740803035040d981c2d61010166640c456090a04288a13480c881e60341015030081401a00c1c40d08200500007a445203c18009081e500c3c02d4881d1100e04280c0d8458010100c0c40000b00041c406a0040542e0701d01410070308208072080e13003062102c8045400d020692032740d04030240002000c404040d9031040c1001c3c1c001d000074100d550001d48078058612014103015021520300b101540420251001c1c25a4803d0f44c0c0e82020038266003401ba0240e8403079020307a806040150340798410701082120985a00e140201011500d200044804500003020440c1d540942d0703410040d4007501000074032100d40030341c240050a0382541850812100316488061041100300802c00140c01c412040d604500d0301281c5032419100d05c403880c6d9005041c400c0c1941c0c0030514040b1000b41d20800440031011074140798048840d00d12031001400115000384414 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 241816618 1250 241815368 241815373
    0x3070804030f02031b010209040e030f0f0d020f0d0903120c0507020904051e07090605030703150c09090c02030c010b181f030210030506010206060f060901050705190f05070b030405 79
    0x3a001c0790142c0c4891803020700c5441102e05c0c040c40e200318002d010140b0305590803d07035000942034016140c103020711031500003030501861034040031000a0b1590f1007680c03010104000049044007815610380d064409201140440d9030390760303411030480001400c4140084010880c8a0051810b5228504ca401c01c088150f455146ca0040780e5020001c81c0f1500420807203031440344d0001044d851302c140901c1c0003400002c6006116241c01c0012103010b50f03480781c204a000b540802c40800200d54400c1800f1a01380c041c0000003807400c02140708032101020b40c0c02c0b4032500c80c2400b01c4103200640c000024101c0600e801d000300400f0502c68104a55018400c401590200804011039040711007074012034295400b44e0001c10460f540c2c0d82c0071503945184078812201290740e40e400c0180658061000ba0f900403401c0ba031901840701808001102401030000680c100140440c0d55410010b0802c14051810f5500c840014128003d02d45100d0001c19071030700f226540113091000071201042d20660340107a038082d01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 241817868 1250 241816618 241816621
    0xf04060e072303010f0c18090c080103020607050c09071206060903021305090a0f0309090c0203070c15020106050a0e090f06090a0b060a151107080708061b042711030708 74
    0x5480b0401c4455a1500b035155607142d035107030101070b900e12841d58081c0254a61403d0514aa03070306034581c49156216001c1241004580d5100517407007199107064a604980f00d0742c444885040c0107141295100c2c2d40e50700881c0c2c100600c01c42d60340141d048444000c100e8010300c01d054685034212400141440000d420902c900345000040002d034000a40c8201c074003048507060882c90302c540300c21140c034030002d80204071400014821103241e4001e8180200751400250301d413480319628208018018440e180c8081200030802125602c00e400c1540102002481c03042240d448400300c1c869031105407541c019134403407002c03c00303841900030540901c51150342025100e02c403042d4a031843d015100910b00c42e8400545070340840d03090300504a007030b101c220301e944148d20002602d01151030308070700340c1000b1215031240208001d406000100640d1080c241c01070140300c113650039001d203801c0c000c9400055a038030402107000f84045a88401110300c601c500f00c14001128031a10220031403005907000c0000400120 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 241819118 1250 241817868 241817909
    0x2100309051f0b090406021305010e10030c11030a030e0610030201080f0408070212060402030111040f17011506080a180f060e0c03010e0a170a0207060c0c0302090f04060e07 76
    0x184007808070042d4038007040080f001c1e80098501c0008a80803100307254046407080c1d501d9405500c05018020a080825090041000140c2c0741818080f20804164403a80c2c00e024003441404084031402c80c81c0c08030790700d9582000000d070184c0b402d2500d421003880b0310400200b030b00d0045450b4102322501070f129905035844008000c0b403050401400fd80e825441040044016128aa040f455019040001e414181010b1041500b0354400c02d20b4a081e81e0000d0209000754146068644d044400b000300c9001c41c11442040a8050981411904d449218074a40004d145811130f01e854881c0700d04030010010303d08800c0c045d204403d0074440c040d080d113260346608030008089034044150074030b6010485100a07640800642990035001c203c0703a854000c062030500f0000004000c00d103a680485046045c0f80203844c00a44d40c560b01e2060400300300383d41c140301e8107004016040c00040d54002e4801040d86ca0b03c0100e071214a43e00b905c0480c0c0c007c0c542045680d1145022843d141035071900300a11151070200d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 241820368 1250 241819118 241819153
    0x100506070f020612040210030509060a0905011401030605100b0c07140409211b0b060103150803071b050103021905090f04020301090e0c0303040f030b0c190c0210030905 74
    0x140d5003150814400d9100502582d2040080e20203404c2a580c2000180341520502c001d0031142d0440409050070702e020321140d404081501603203c0c9260b8000200070000c0d04041d80135108580c60324910240c0d0000100c00d010664100c5413140d0452201c0d10030031541d401d040109441550400345c0140c22101090281082001c10b031b1040100040001c80c05111644840c29480042d90550400550804442c008150418045010101c400d800f4401d40c20181e2900300d110000184507034100340d070758850381c064082c0c03000000f8080e0184c04100ca444030060300c0c20100020300e0070030032009404011030005807036200f4000c44102150480d180724020703411410580c0e881e003100f54034603802014565401e44548030703031001d103000b0505601c0204045404074801418406821a014080c2d00108018400d1840c3c45280f40f00726035010142216581c1c0c1c0c02c454280c80c1c041c600c401c00343e44805882403401c09a00404100020b07000b107403031001032003a42e0320543c22101341403801812034001c41c0e00038040501c0c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 241821618 1250 241820368 241820377
    0x90a03050f0c0a0803070b1e090708010f140a0b120312070206150102150601030608100209150c15190218030d03020a02070b13090203070215010909030e0f0a2301030f0203100506 78
    0x185230000301c022a07102100c46404080342c000741c0c0b99010351030820400c902401805095040a88104078403044d4541c81829218000c2000c14141e81fa6202200c060b21142d9018010501c1035042d02c0d00c0300100c901340700e0f600b402514a0340040c40b4020100d9800d0021403000c203481e0300140c00812000b1b4140e044088103000091825050640e24540041c21301020b0106280c0b00e010007000507030307403001041088844201584d8000761b0740e1042c040d00e62018400140c0103008024804004d40c6640c1d09680205408130030841a001e142c0082210f1000101503103c0b40110182101903982050988104804a000d4545030303100607444800100702c0f04400754000d00c0c003d074100d040911515200ca2800303007641c0c001d0301e9503001607000d504455803182c83c0307602c114054800b0401c240620002520300410700a0050003286c400c009034a84c000807a80d0781400f0100810003030fa42d190300204400f0b14050703004070100301035002c80e0a10485107030080461080305d2242c600540c069402c40d0421017408a81d410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 241822868 1250 241821618 241821631
    0x41d04030c080a020106090513081e07080f04050111011b0f090909051608030403020d02220c0201050601030b0a05150a0c080f040906080303040f110303090a03050f0c0a0803070b 78
    0x4218541c0004110024000c0c0483d06641c2c001090461400c541c0c20112040100040400280e103034110000070500750485418900105501340e55860780c0c201001548141034004001c60740c002441f03003a8500c090094812a20241c03100021501c6114146081e110070780c0500440032504103c1c0752629000d801603080c0b0b11441e2400480076a00c52010b24100d5100c000140c9061b84110003059203a46143e4054000e8010f4102070b40c02c0c107280d0b9000c07400d00211184021320840540c8102008080c1e0071040410003044000c0c103004040e010b0102034000e10b010385103140000d04003109074000b420f1480c0310710125040503090340128080c2844c10441604841044410080800010b81c003049080c005081c51101c011a080d564602d81484201125000c0d4001d8030650001d00c104000720704034400c151030064024580070817503c0483c0c0000d08500c1581c10231940000000000701c10320600003001c841c4441d50000b2034071041110820003040122500c00c20711554020070101001456401607a6000708 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 241824118 1250 241822868 241822877
    0x50711060906010302040b01020a03020d0f03020d0c0c05060703021215010309080d0507090f060206150f030d0306090501050a030c030f02041b02030904200405010318230f03041d0403 80
    0x2025854454103200d0107452644540d400b001c010f00c15072030b091060b02031545090004141c100d03040e640180d21059402c1001c0144001d034800404024040d4040320b8480350603230410001f5104100307018115070102102661280b00380d200003032215000f407080301c10341e00e41100d07110362a582e40050107080d1000f500d00c650406072078960403070014a024018003440c0c0b00202d400708144c94191001484c3d02c070070b42d1014001d40d0079100204207803600401c009070003881040440c4024504980407d0042c1a8a00c1c6160140b10710340c9034400441d40766100e401640c044007001c0c803243e40d0340d800304098002d003400042c054401c9810200002085200342c2d1203680c1c8090700201f5421821401d070120303454a031b8a00c0d40542c00000300f00701e040c9484e01c1a00a0300e500610710700160b00c43d0100b210b00c50b0155004090502d80d840121840701991030316880030032640121015105440c04800c802c081484008225051280c580d00c141c04520200a880642e01040380e09150501384950301c3c3c0d00d00724060030690602 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 241825368 1250 241824118 241824137
    0x11040f0b0c190c0303030b0103021c0b0a05100e040b0f09010522020d02030601113d0203010b0c150402031218030a050c03190506070f0909020406020d030c020115090507 74
    0x214610b103940b01c00d6030b00802c040c0001e41c1c030f1400c000d004d444004100c2d504062040026001e2440c000800c05600e02060800194203408a804610400c007681c020341c0d8022640d00c2000b40c403644c04800c000119000f81c5042c0821100c040070b010020b060000680c1d80014200010310541c184141e44040c12003400d524200d000c582c1c2c6000e0401c90b4080c00c42601c4068001041102ca56001002003900e038440710024071101401305071a4102c5010031441c41040801214004001d039440741d4032074101c0d540043c0031540d0b5652031080d8841d941c82001e940300c003405144100105031a00a00d042e1113260040c0140c00c40100b40010320005a221004140314041084450b003c2c5807020446610294400d8009014086c41d00e0105880c4c019202007160120780002d07001c00018201140c01d0340c002032603091003a60302e450260291000354031608604081403000c240041c032543d0014030002c20b05000e0320100650f0210304412801d0303848078892030440c213854900c2045440000d6102d035500000d0343c0707440e2003032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 241826618 1250 241825368 241825393
    0x108090a06020a2a0b011e060e151809180714040e03070f020f0402090109050d02010e100c06060b2b0b03010c0c0501230c090a1809030311040f0b0c 65
    0x50303180e004070720780821101c43c0e1403130100864a8a00c074050408050000da074583d9004002541c1c1c64140a20000c010b01c0e50320743c03200c1c1d40311600e00300d000c4401440c060307855650070100840003100180200748201c0100c0d001c2480b50032806222592184100094100e141c03d103078010f0303424603404202720b400c0756588040002d9510103001404090b4402c00b507802c0c61102a004100035401c104090920a40c410024414103a800021a03c12110b0540da050140b07281800140d681d02646000e40d9000303003020441c8082c041e80496005822441000108085500d0b01e040301c046015000384420043c107030800071114901c00b0281d01802612034100801e00300c42c5100420300752a200c10429000ca5400306201040000038080c90540c1c0482c0c04c90314121464008500e0402440580100a41c07030000409c03118980399003282401a0200862403442c50f01014040c0000f4919a181600000c0c9020101502d41802000b02e0b4119400c100f8848005c505050012030254032210301e604d80751240c0001e01d10b1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 241827868 1250 241826618 241826657
    0x7200315090607030608070f090b0a0e01032103151e0b18010e060f070f0512070f060c030b0f061b070803070b0708060d110d05010e010c030b0108090a06020a 69
    0x401c0032030501070035150070300f1800601551000d8000050310b4000ca0b805102005000b65203500b00c0d00030120124020420301d020404000250b00643c0021540c0d200100a0107594181841043e050074149000f1000720340b021400c850307a008040708110381c0030070f00f0040c00c0e078407027032550500744000189440e49a07204031070010390740140220b0603d4149021600f10940e00072003907800005040d5826450140c030070100054030710401d200106440d60b40c1001d541840020448150140400e802e0160740e2201030800c0040344180300011500d10f41040c04a2903994807074003c84403000c0e006010a00306110820410101d134010450390361803900700c0143c0710800c2c1030400c030501c000c0c00014007a40e40c89105060000c14504010606000e101c3d00e078050200507200c02e820307035100c950842504180013a0440c005001440b03007940203401c560030b00c0041c0111400640c8401040d04c5c03543c90800000701560015a101c101c01c0712600c2142d0440081d1002050168004200008082c50080447c400441d1075a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 241829118 1250 241827868 241827871
    0x616031815020c09010e010b030405150406020d0e03122206110403210503010902090a0b0d0b0a12110625030305041511090111010627050c07200315 65
    0x4001c09003254207554215010b00400389800402c0d6054403042d07050540402c1c2005041c8646140f0410000020b014410240641d01c034880340781c6061045410f007802c1441c0603400410300c1c0b20f1128501106014018030000403203041c0c2c0c010240e8441107a4170170f06000c1c14020000460005802c08200c4500001c4d414451444c80402e40031103591903034150f043c80040d0384024410000c02e00c00c00742134400150b410030180c90445090b0480940d513100c005010402c0300d1001d078007008096401007110400e601c100d0b080340910303010644d80c041034203a941078000000790707441b41c010f40400c0825150710b00c0c90400900500010400c10181502c00100040c10800e03030b8090308041d00007a9580040c4800c004072246010082e03000c000c028405d1411000d0b55202074480c801c2c499050144d901401c0c2401c000a40060004021031310781100d10340641d01d500d02c1050050b00e030302c171074152801001840500c4030f4015203141a4104680b610018171421000400e01041c402c106da25101d1251221510320701c944180f07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 241830368 1250 241829118 241829129
    0x100306120f140307170306010909181103030301050a09020315030a0f0501060e04080340020a1e0e07030b130608012316120c0c1703040206160318 64
    0x894100345410800c400c12008242d02603141c0007001000080790881c2d882910b4402c807240c3d060794a4070342000688450407540d20818105041100e0b8001000c01c0004c000e10030382c060300c80d2030310400c1402c1c100b5449110034040c01e0350041d40c0402c18031000005502a41d880101d01c01105002c80305403001a18000704483e04580110031000d60608010083c01400001c0800708000300f01c8d0b06284c5da42a07105c0c00010461304005c5100e8010070f012810032071182400c0b5406042d20340d0b042040c04443e113202d402060099005103402d0000041c0c0420710011030760300034008518403104e10f080c544009010342002e005042016220303c0044000e56424900c12111580303d0700025245103854242e23801e468028013829890743c1c01d4019030040400703459015501108050010a803003080300016a0300c203103002030a04000345807203031b48802d4039040301200e000d56024080d00d141c12410082140460701c01220006e40050040c03001c400c02945408508140911034107040c5008455203914940b10b103001c3d17014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 241831618 1250 241830368 241830383
    0x6010f0f050a051606051b0a0228020406060f030e0304080a0620030109060f0504090b0f0901090f0f03110307120302030601030b06030f070915050313080f031008010c0507030e10030612 81
    0x1d0001042140c0e2080d09044418005181013640c4118081c0d101c1c031408a11203550002c50700341d40d0341e5442b4081c0d128120380c1c0c001c0c01041201d40b1640001e18404035540c0c0c22000c2440d0940c541d1455000100b034404130b0350300e10000c0c00e05011b199180070240501d43d0a2030b1011103018104104240404043c60280150000014401c0d192180a44c0310301240c1d40058059032a25151202203681b0b041c1d1a60f101c010104900300b10f07103030112801d0060a4821000e080000152015000c01c01e81c41c0030000341c24041e94075089141c00f01402161a4800c21900070007035022100381c002c005002c0d401455110f0014100024400c0400d00402d500340d00460700c0781d00003141c06040000d0150030416640c0030700300310709040c80c0340c203010f07000030703040344000b03050000400861000e03802000001d8044405201c96050180d1b1241025060400c990400780142c000c1075081001203603002d841581139074040d03600765580c01c030a6044001404a800c0300750900d0410983c40c1c0c0c40100307110640400103880c2d144100341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 241832868 1250 241831618 241831621
    0x9212808041b050d0b06030708150f01080609071a0d0603080a03050703110906030a0f1b02010606170a0b21030403031815050307020a021c02030606010f0f050a05160605 74
    0xd0003250607071860042c0a4100c1041c0050100351500b18401c0722645c2e100002d8689038441900080c60141c04da03014030308621885565805000300078101601400309003c4c1034481d40d881e07050b2140c407841c00310307080780c11544241c0c03042250720203114820000105006249240c452041c00c00829140e090b081903400120005c0c6107094154980305050b4442c0180c60104690030202e05140c801303210f88001d1511591020000c00e1600c1c1d070a0380003500650640e40308005004043e809089540f19902c01078025501c1c0c1b240010b40103004480f0f071048683d014210208076901c48040d07034010070301d5640140c3c0113400c0040b90040c0801100141d0703151b0a10703600954480d45549001050f90003007100c00d050341540403000300a80dd00c4021031200d05801401d04544030303a81c801003245440058030001c0e50001c60080d03801070001c1c2c0c2160756070380d83e030003507065074810f6580c0740040d03451140c1e2003400b8001403124800c200f1201e00ca14058181c0325850710f08540742c021031030011150b020380c409094070707400e03a02d10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 241834118 1250 241832868 241832873
    0x907080106080a0507050a0c17160524070f0201140903130b09060409020a02120d06050901051012110f030c0307030b030d1202030601110307030201060504050921280804 74
    0x19002d40d40001c0c641420310540c540048001c000b805280c03030b10b40c1031108003040341c0200100b044d0140d1004131013401c85521140e04140e8042c141c2072040c030945840c000ca040c00c009040350b03c0c034184600e102d140355001c03031030b190301c0800c40d2910356a0210780219540c0301d036103c90380070308244020302802840008540b9003441001c1014042030300d912030184041e007003141c44040c0e02ea600030b403400c8807008800140c48100350030781641071030349601c1620340d80000058803110540d41c23584070340c050b6001612130030043d03a02d69003070080401d07900c0d00c10300210300929019005801560449144075410104660402e05400446c0f20150070503603910083c84404020040296814450920040e80c00c600900c007003e010340e405407614640e0700d800961203070000b0000381300d40d00420501081d17000e080110b80e600d03292030400078020041c90190078070035410b081c0420b560341e41c0014281200c5c40d2081c5001e030000100c4480c541035a00202090103040441d4840226045194170360712080850f5454ac2d241515051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 241835368 1250 241834118 241834127
    0x21204032a03020a060507110a080406120212270f010203061e090c0a05040302060c0606010207140f010503090124060f0306150513030206031003020a0b03090c060f090907080106 78
    0x240c070800040340c0140c041c030000c6540090071400641d08841c00040326203840b00f0480d10446120031540807403045000d1402041170150041c404c442070360760b9850203101c06003950000c1c0c1c0b091b01143c00720404128041201c8001103014060100c000091802c01c2c002031f560000d082240030410100c2913540481080420b0401d0074000d0919550403c84461869641d80050146000607000800201c1c020600615090054084502030b54005299544400401040641d1040101d402c1030060054010000c1c00c0301000c003e45e44124001807401c217011410300c3c01190700f03801c001d001403071075902d402100482c081d807a4040101c9180034200fa5120070700307012018001e032100d0b4070f1180405280c03110801c101c0a45140b42d149420f0f061804031381e1444601403526040b020703900060343c00700c0b0020521000c0c508143d113502c00c59201780d40c198686980c5010701d402d240030890380649240c0040d003000700c807440d1500081000f484e0301482a400c100c081c3d80131549503102100c1036404265280018000d09410 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 241836618 1250 241835368 241835417
    0x6080f030705060403050c0c0d0c23010504060309061107050102070c1e0e04080c010e011a0303040f0e100f060f030f1a0907051c02040609061403011802120403 70
    0x2588011407401c0115070b00c4a5903990028000340411802003049003883c1d0080c0a5100c9001e00101103203d5554117080501211070584070340c4c3d0681f032640e5049003c40c400070588000c4404161199820075280c514241d000e011070103c00c5078850340c1d9000003442e0f13000c4000500340460151000603101c615500d0400e00301031705030700502051055a40d114100c2d100c002201000d6480c02d0a800340da948480c40d101c0c03075600801c240c0b91015428600030006500055200d100c00c0708001840d50550802d40042c5a02da22660040f40c100e000c601c0c505000160080f28030640001091231820b44071030713690890340b4500040c0d4001c000004d01400341d890620b5414080ca070f4401d140c0c100e0401551308003482080301c0300107441600303011b000e181c80014480d50250707040e110710540d0b0030790010030701c010b140d08000250f01502814010030700c0e50700041038880c4201e0010b110822443c4085141d0b03420803c800d00e0500c032030a19000f415408000007140c80c0070a40b4481c1c02180709844102d69861601900c038004000b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 241837868 1250 241836618 241836643
    0x7030c1a041206090f02041b02070501050412120c120801060e060c0604060509010e0307050f2e0509011508150c0a0909050405030d060f0807080102190e0316090608 72
    0x24244010b000c0205061039070000c80d0b0348035000054090035403034003404010100320081c0d1302c90725100461521903281c1c0380aa001005c180e080c1c501c0795031a60019243d601540c040c7c08500c100d1b0301442d00000f0124420340c03440030007900f0201c2d4501d0059071801c1d014485030340044000f401580040285a40040d8070440707003032080350058102030303038120480d50320103000b0400340c0742c5915540440c2c0707821001e511000d1110011003c0d00e07034800e000c3c102165117160790418203003644100f5244100c4610280e80304080d036543d0b280552440c0c51005090300140c100908100c0c00395507200424202003205481602c002c3c4501005000c074040404d4440e1100d120041c082035164004008444c12030f83c0c054112415605003000024841c0c03990706110f81f46001e441110480c1610785a00071072441800c1c06d203141107500a50803184810385840c02613007130b801101a07815910488060710b24110b4001c06074011621006001c0302e034003010b0004ca0f42600f10701a07202d4400c00c5c3e900c40707042c004038905120b0382d080c821 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 241839118 1250 241837868 241837919
    0xe07080304180b010c0210030908160209182d060106080105040e0f0c06070c05121c0c031b0609060f1d0616110708070303021516020c04110c07030c 65
    0x10f00100000c0e04240b41c2213402449030350140310540095019a01c500c4400350000e01c002e441d400d103800000e12404440405030702c00c188101c0055558602d481580c400c4500304406012210b82090a8036146042a00245c020524504052030389040802c280c6000703208550741c0d01000d5140c4418002101c002c107501801c180c004009490840000044000c250304059072070b55560b43c240c0c10221402e07002900b000c0c5c3c2c880510312011100300b500180e42098070b1000d07401944012079a40090340d408219250050100c0c40a4084503040c010082c5102c0da0325004034004160428180c1c4c031a011100b552068550860795254403242681c01e11811400101201c0300420341410010f0f2050300007070800d004582040242510320030303c41c41c01c1c0603400003421000f041b15109900d030b01d8040d4a81d081001001200a140c40001d1007010108055001607481070300a030140c4c1c2c81c10410322001d4900594080e080c000204001111010100b140e0002180140241403050b404c0510071000d400003015428040c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 241840368 1250 241839118 241839131
    0xa03020301030605070c0c030b0703020f0c0303010905011d0c0a030f02070f11030a1e020328020103050f010308070303050402062101170723130207110a0b0a0c030806040e0708030418 80
    0x140c7c00008200989410100c46440c0c0d80d242c1c00100d0192003100c0d400c048072a00810020004013002000d141a01e0030014103210f140c3e20740c0c041d440841849180c0001c0c4841d00808504010560f00083c504403040d880d011441046019041081e40e004000480703030a22500b490b2020f00ed0607600e214800b04048014021080d103a0321040e80c5560f09140800d440f43c1d0780d900b2002155000c000f07801e409290780d034203035219401841c400d007580305010b0010380c0442d041000040c9040d8480f03440d0340c16651b2018425050070b01503101100104030080c4100d80041007048140019120312540502402024500d101d00758101100c00844d003803c10300954032644445024000d2444a805100c1d00b00c0040d4000304c801800d4200140180c1c244541448039540300103a5101408015254440f01502c00e40c0d101844584e80d02d0f402c48075220390402c0000081c104008000024071030001c036600600700400200b46a050483c80a060807600d50119180ba4400101001075010b00707225980001c040321410001b2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 241841618 1250 241840368 241840373
    0x50a140c0607020405090a05250f033915110309030a0b040507180204060315050f1309020312190201050106050f1b06090f01181e0203030409020a03020301030605070c 73
    0x314082c0d8100244a1a11500021102d030810001c8608150700034045407500c000c26290581d8814031182058007041c13000304040340456442421604990348000c10301c02e07a40d80119100d90703010b4151035070102c1d60703a40c8078a1500c40c0d501940da20060201c3c1d00c101003025540c0e0f400a00542d044150810440c2c00c140914200b0307950102d40c3c0c1c40c6a6402c201c2000c25962503161050400000b074000034441034005c0120300c07c5200c05d5015106440250b1020424000b0303450072203075000300324482c95030311090030006000e050414010301c80c00d0540c403805c081412a030030303070020303007002c0c2100d6810401200108580c221b00500d4042809600c4460008001650401c040240343e8441c0c4805100c42400000e51942c2024003181c4000285403220b06440c02400c001c03c00c2c03034891028040c1011070390b0070b0ac9040c4596100120890442d643c1c022008880301e980080480020200d00c0000e0343c0c140018400014000349030300052060340c40c46d80d401aa00d6040d0b01c0c3c21411640003400b118100408030555000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 241842868 1250 241841618 241841629
    0x510060e0609060c280c05121c23090a121a180a0b0a050709140f010c080a031b09060507060f060b0c030c0c0f1309060902040603050a140c 61
    0xb00016038905a03a501040c900314a8800200801203d441007402c0c3e444901d01c0740c0c2d14105089101c0c210900036280d64508100075000c80c440c01145541203001401e17070b9540780c3c0419803410106403c100b2210300b0250002015003c060960201103900010703030348440e2400d81c0d0080b014208005841d103402007240c40e4100b41c115004280204800004045580039440d00b401001c0d54241c0d40844000d801e8610b018901c10a05480180089007404007250f032040c09540c5120035a100510484041e0314000c1c20464480305800c2c1c100d0512500060b104003051030303030004000041c00c0352004144000e1a948544503101034103483d00c20000c2106040c0b042940c04000c42d400680c0061300419210100c0c0d0268004001c030354814000c0e1400002c012040341000320140105041000c162116860303020240540044030340c014581c00320319407541e08510f82c2244e0052003980e0003814000750107080c0d070f40420125885900240d40d1130303002c0c2c075100082000c110550002241550058600ca182c036001194 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 241844118 1250 241842868 241842877
    0x6030c12021806042403020c0d21060b03180a0c0302010809011401080d08061e011101060b040314010b01020a0b011715040819020a030f12090212010510060e06 70
    0x12030550009200c014103950368a81040c41c08008040c260ba0b80d94500012400d0701012007640b150891580001c040135000b4403d80d00c070110200050052010101e00c1107444040d0880c0e0300c06400461407022006200c10301c18000648890406d250340d9050811100150010800094003a90b1240c6044000203203409440011a90f080c00c6c00c0c052038503002c5009000d08801350b00394001c2881c03000001003640000135a50440289074490340710075190030080c00300781c201d0425000c5a807161601700158951041303003100c45044001000180d0141c0f9050101140c0d4000c0d4019140300b4044165000b1030078083c4034110b005a003d00050a4085095841c404001e01c144140d124210030702403034004480c402d20a00408812503888090a49400e184c1014030380c10000501d015884e12600501143e8000640429044d401d034880c030300e004940101c103ea2220fa41c480c000e090640b254402001a10f4001411002c452010000b103880c0c58510007196080000c0d9014400700b00720289015120b4030b5990845 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 241845368 1250 241844118 241844147
    0x1a0a020d0809010f051005040e0a050a110d05070b0a030e01051b09030102040e01091b0503040803040f14100c080a060f050f0609060f040503012022050303040306051006030c 76
    0x4801c140e03030b400c074818010003c03030104410039818901000740c00d1004901c0b003015100300301c2e820031005001070340301559605000002445540600300300701c0860545010070540d980010b10042c1c0300b01d0302d40d03100c07410031304a903020644592000ca0b1411100380c00d4010140700c0e81d03a0100800041c41d10b02107000201e1100012000148400201240d86890a4040380c000d810704011078103095940e044401d00078090152032003000b01004600b095424031503000c60b4003032a00402000d00303680711600d03144000314550900700c581031844108541b01c4101448142107901e40e4140004070110300032005000c0300d00082500c05407500d0301c40c0074884000411565020380340240c80c1d0402c4482c07404042100b03846810b207003a03403101022031200040790a0354011710550303e040d8001d115140309407420f50a22040d10385e210303441f07000c1400780c076248030411102504a4202034465400c01540c4201090441d44076400540b03a098441c820030002e5607044036200c006000078134042007040e07040749006000b041306642d00e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 241846618 1250 241845368 241845377
    0x804031d03010213080f0c0d080301031704150806090105040c02250e012310080408070c0b0a020f010e0f06070f021c111e030d020a030f020a0201061a0a020d 69
    0x291030152425810384800c030501d42c400c004603c1c1c444031056a07507105954040900d1042601600b03807810301c1080100c41581c85507095042da400c6035500c004000e503482c50700441150034000041c00e071420f8603c000c1e800ca4280c652040d54140181400a4520142c03c000e01503800c240c84920300543c0010032a080d441c03a0000b00328441b4121a1340090401c1e0b6a200f007241e00816000491000c02e604050b000c045404250322400460440078000f56040490501020800340c600183c08a8981d5004149943c41010419201603c0340540f90031501303d21940401a841030044841c07101d024802d00001ca02040010150718007004665544d03400010b184008000041110016890007000103000c0080354103004070900c03001d81c8000b000c1c141c11506902c0c1c0c91046400c22165200d15203102003096558102a40c0380c0040b040301a4080d5001e18119000c0503030b140000b004c0f011451028080f15a120f41c004550680342800002454070010038403001007808009040d00103400142c44000101c3c0303402d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 241847868 1250 241846618 241846667
    0x9020c03161208090c060703030903170a05061e0d0f1703130c0b070201020a030807120204030c0501030e19030305041112010b0102100e03031b040519030b0601080403 73
    0x5180c11405410700c1000c801080c0c00515007088600c503035a4000e40303682c0d0341c0d0954540e03c11110342e0791452443d00f071a0300032804000000101e0b200307400112006009084c0f216000b404803090010100c82110f481c28030540d100284041880c2c02c98004101d251041c004241e000c000100085244400c0748008044c4283c00902c1d200304890300040c80301c0c0c10481c400d52516460503851600e10710305141411945a0104000400d50030007000680301f2a1390103900500110806540c15910020040c3c051024081070041c407040305c9403a4002400554441c006901046141070b001405481c0204030150300c036006007005d00403241820300e940d046260186008949511141072040c2c40341000000550031050004451428030701c150804a03e900003a4222030003145000c00d13400440f4507592070b03000c158200700701007005003890394040000a07000c20942e521f450754580002d2140018864628160507100c1400c1040c040340090250f07200c0c0082c20310030410f1800c1e40d0b00a00c80d40d411000e5107010041a078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 241849118 1250 241847868 241847887
    0x8030609040c0305030c0c040f0615081503010207200604053102160b010e09030f0904111207020705010806090a0504061b0c0b010f0b040b0a02010209030709021804150902 75
    0x1510310019038000c0180c0340c2c1c030b1b10500c040c3d9071141d01d140c1a1900a906180030800308800520601d03040f41d00c0000f041081100c0c41c441100c0f00203024081c8241e16100c40100c041598080c4004c0c00be40d4400c45802c1c64800e14095956201c2c515806010f1141c401803100700119207030503441c040b4940e0000c2c4040205000c0c5a0f000d00311304072071400e0070152880032501c8204c2d410000a040103e038040c0d0341401c00390380c0e1000109941802154600301e59007050003040d00c91540d90029214481c0024404103001d24050800c480c81d802c21042d5004804031031040c401001e0701030001101404003841c000485203440c2000c00e54003080035202004c082c0e65140050309011482d070000c03008984507402c440600542d400000d190030300b002d0b003d8400c007200070000552450740140c000200c410b006449810580ba200c3e40d0f28480d000607200c0c03000d65401300031070705007981c042c0449405031602250040c2c8444602e40d505140303c0300d9016244c080d900e000c05000012118883d45030841d00c10302030150b40c2c2c1d103941 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 241850368 1250 241849118 241849133
    0x1005010522030303091112101802060a0f0807030b18061903051605180406051b0f1905090904060f0902030f21070c03030f031d25030803060904 63
    0x4802181015038a074102008150741500580712240c09412961080c003107400c1004a880c82500e1390a0b010703809010450407805081e000f41705562036064101c1d038145c6983e0003003151940100d04000c001001c611303001e06000c0c1c00290803504481c50380340401a043c20180030998001e002c803004882c004002000a0003961003001440d035034040c0b038082200d0303103580c0e1034026907803c0380380701d0f60b0f000219006001c00c060402043d550803d515001c03040c0c54a0300c1d9034850323600400020740051841084007102040312030b05000204100c040aa082c2913442104d440c0d22880215104001c3c02002003c0040c80c2c1c01d5561880c2c907035000b6800420004800b0342c54000c100041803040e6000b5010f024540d0a40340310540424980740e8241c40c160944c0030f02c000d003e0203501c0c40c850a14020800382d240e44040c0301082c8a80400c4040d00c00c0c80c1000104800340c0c0c0c66441000d441310700301003543c0d4083d074204000c00c00f0344104000e452808580d480001820750380d070401140001408580114031010011302400b410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 241851618 1250 241850368 241850407
    0xa150f030f081b070501080105150f03090304080604050f010b012d050904110405040b0f130f1d0606010f02071406030408071a0103030e0306040308070c0203160b0a080f10050105 78
    0x7488803c0750050380500d18140c440800744142404078004400000e2a81802c2c03106144815100030458030304404003845803e150000381110740c09200c144004501148100481802540034100070845000701c41071090035988903000b00d030704100303c0039503900d01060708209000254440c02120031411720180e00848003801980071560b8028244400c841c4019105002402507440030f4506000019045081c414000c000200c101e400c280d82190044054090f640071215058040070301142034903240709540d05056214442c0110341e00300d4404e201140da0052032044a068050000c1c080d040c0c0381001c1200d55051b425003140c0103020001c009010058a0011103030710f194010300c50510204107603010441c0342800d00084001c84d07103840200b80c9a24001900318840d81d80365480c00c1103130741c030610708803403070820310700102c0c0c140c8070b40c4203510400c0801c040c1520203001000d507180c0d200c6580010081014030081c140d00c004142580500022034845000041600ca0a007802a03546040d865040d140030320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 241852868 1250 241851618 241851637
    0x907050d0b03030a12050f0603032203061d0124050d0311030301080607020f0f0318060c06010305061b070f02061608030a090c06050a020d081e0f0a150f030f08 70
    0x1040b01c10940c005c044603540340710a2404000d180e84050449500900641c0c1e030f0f5a16900500c459000c0301501c0c200c1c4001c0d5003034004c030941c5043d680e54030b120a8405019030b0540f840300343c07288500076840900c10041200700b028610791035642c821060040e2001140241030040424403000000d00d030140c00d850360f00d204420101d036582d69450840750307203801041d10310600500a06450302909500010707107085403c02c000c040d62910741c07412001500b0300f5040c1041c0380c200384144104000e510702031024070f00070340c003802c003800280ca454006941010400702d40c1c1103010405021581c045103036540344901c226410384643d40d032910100c07800c11404030000d6008190040000070006940b10b42e0b0004841a40b00d1030440840075100d1400340c8403809400316071001a840204840f009c04d1003110150340203408480520102c5006074103001002c1402c88080840802c4d01050081c82c811501c07540c26041c50900821242c94107181d80b241c1c80b40d805100103014000f00720011800d0040c01c2003100d12408 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 241854118 1250 241852868 241852873
    0x2130e072606030606090705030c16021c1e08030112020612040f0c1508190e01090506190b01050a050304020301140403020c0405150d060f060306150f080102090907050d0b03 76
    0x4070201148050001190058000c0c02518041203080c1001c0e044140200b9003a03c4043c19030740c800070100c001d6003000b190b001081d040c1215034009a211640040d10b01520480c0d1805035a0b22401c102d54410346061141444010300f09400700840c606105aa0540351001e48110103130555000241d800e004400c005a2070b402c01030140010445101440041390b071080305007030005034ee1110701452301300c1e003055020040381d68140094010b4480c2d0106075400b03144400c0c0000c1607100c05c18082d003114005c0b002198140d000d00c081c40032100311703075514164402c2d0001c0144900f08074800000d0040c05050512000c0c00404400f01c1d045680030341060085040c1c0741c00c2800c05281c1410020354456241c204940240d1820b400701d031518410740d050080c4540040c0203007562840c2c543d42c2e0707401091500081401196504008070004406020380a10f08460750300c180c01503801d0090514401e00703aa485002107078410800c085507a143c184000741d01171400d0401a40340c1c0301c01c1c40c100010f0075440c0410341c1e150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 241855368 1250 241854118 241854167
    0x180504020f071707080403020907170a0209040e0d0c030f0311031017151303140f040303020d030c0c030c112206080a0b0c0309150c18030102130e07 65
    0x8498220181510303601403075040805840070300310f0b0310075441000c1c405000c01c0c00030041400503042c60200c5030340045507403620a03551145a0000050440c0a4550301e1800c0e400140301501e0b45058090015516550000f40080d00d03000d500152005d2041d020040a00c4803100f8918003640c006c1d40016080d0491040d8284c0d280790141c50116440c1e45800b03141c081d0b520862011281132800203208014440c039803202031b015110520b50140c0002c040004400b004968060012a240100050200c01803c500b505031110304625010307041800049069040600d07002a20a0f501c0d0700110b00307c0c0064141c00c0045140c43d072810080081714560000c180c1011940810b00e14410000c0e0603506a0741305540c080081544841d0090388980260001400c201c1d54480410200c800c65001584c01c4182141100c168078140032150a60b55021030710b40d07102450204006a000c030f9540480c80825030704400841c942440003014075903101a0780100d140030780d640d4000410742d0f0300910007480110020901441c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 241856618 1250 241855368 241855387
    0x140f070302070f090b100e031f05040b07051e09010c0605101e0602070b03071107170714130f02130306020702040606030902060d0e070e0a020a02070503030a050a18050402 75
    0x503404039100e91150700318140b5000481e0314417445900d00003040103101396200409000b04a90f40d90041140d0340d41806200c44800a02e03445911101c02d00c05841c0c1d011a0038138181c00d041c01c0164009152506100d820404072a102c1354804035564030402403100c0c10340f2031900000484140d0881c10000381003500d845e06000b010382d9080c0c1000205ca22402009582c60390a00406003005510b104401c0503900418050250281030710103180d0000e8bc038075102e070f00b8416141c2846c0c07a180c03844e4440d11100c0181521600000018455440544071101005224201e41004190802030000750b400071103a80e40d9029107414201d4046646902480d04540e0459859050481c025403050744128800c0380303410000200180a4001d16400c20780081c030003030608014003145400340600201c02d508601030480302140500f11210900d0182c8401c520068035a4880035020f0329105490300650322070b500038460400159401000c42d4030f03a450525021041c0c045160f030607600c106458011a6001e0300102d01a0309 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 241857868 1250 241856618 241856623
    0x603070305090106050a0501051219090b01081006060c020d031e0509010e0a030f14030412110909010905060c130b07060b011b0f06050402030c0d0c050f01090b0307140f070302 77
    0x24540c4070004c000e0030340c1d640c04105c1104014400c3c2408120288042884201075416140c0c2c0078045034143c05001007400b0b0404110307010210212428800100184401542001a04200030844108000040c1010005815203608120082c42111440314000826204a00a0b0000011082502641440c5080281007608520380080c001651080300016074988805400d0440e500305052101000c4a82ca92420310040081003002d144001c1000203a14010b050844103168015100c02c2c4d602c204000c1046241d00000c3e005180b16810302c1524404144046903580c0c020070410b003110794817a42c11b00001d884ca00c141d0300c035000305100031980105114036a00b00056882c402d176a4804d240e0502c01031101c1c1104003490241030488880c50045c00200e040d07100d5500716000500321880d90300c415000884a4074202802c481041c000c183c104141c1c10105d604140c0c422090174a8030607942450342000840c0001403812003004031007000360118000035421503000d040159940da64a10072814041e6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 241859118 1250 241857868 241857871
    0x61e081c020f0628050114040c051b06040c0504051501080702012a0305180a120c1506031101020a050a08090109080a0b19020703020c0411090a0305070311010c0209040609050a020603070305 83
    0x440d076401303010b40407109524620415050303441c1d80070144000c0c0d8044041c040140800302894050010800a040407050146650760104443d0001030002d480d141c54154080e080d182d000c14061414241403054800c1c51100040e1060402c0c03030710075100d0b91581c1c012409040d020307512800c2140035002010040c00c4030b5100303029840311a2000e104684441028180103d01c003c0c480641d03801c43d881507000035100e1840ca40210349a403034220000c0400761918449100304099401909595413000c0080111900e407401101b082400600610122501e540f80c0b580851b51009190f608005403c2081e030780909080c0300a0a03250f0101e6240d5211441c000c110024242d0b4001050074111900b044020351900845402c59030580c0900440070000d828403003d032171500c82c0740c81105010f1100001a80302c01140f0341c000c6004200a004107880c40c00c0c02c14a00c090a0aa14100442e00403190301580b030b202c0b40f564009901903c0024890320303a040032070a140800c00001d6100200000b0700c0035075981500030a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 241860368 1250 241859118 241859161
    0x9050304081e07122310060603020301080d08091615180506120a0f0f09030306090203010f050d1a070e011d030d0e0402041701061e081c020f06 63
    0x700c01102e421103410442400450304034059600181080c0221080380d030303100580d03030700c0340d09007650b10505e41041c40c50f58120721481d2040c80e440b000380c110410301c0502448004080600382145075506001090380c40d20700c1c40c90690240035440001c10b441d988204161740700d040d60454013000345e5440720200d800b240c05810311640001d00d00780912060001120542088443c0100034514120350500c58402040000b4a0f403d40107540388200040143c040c01410712038806900009111f0005190103412034526400a40b0020310500062252545141411041e2241164182c1c074001651410100205000300410080340b0a00c00303000360b05400840030011000244c8072828150280c02d070034158039202d0300d0410f6150780901c4401849901444444103082c0c3c01400140c036003a20364000c50350070005d04c43d0704c245a07076540c5420007055411b4008180c209e9039000280c042d0fa454491102e9580c1c000074080b425004520440d2500103000300400a89118080700351899441c14002100100c400480350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 241861618 1250 241860368 241860373
    0x170c18012c0a1e0512010f0c02031c0614040e101505040c0203030906060f120703080a0e060a020709020d02160b0709051203072940060c0509040905030408 68
    0x89880c0f00011606040055000f05410f200c3d0301c3c0408100324101180051105950380b40c1c41c1c03007038692041c0039400c41d03034186030029503403403420300c01c44002c01c01c00b24400d5140c4d518003802885182e40484d400040c6107401c03a40072402000d41148682420192925103201916241030032540780c00c80382440c0b080301c20807642048160b00b0744000b6030302c91004969903800c0781c01000000d4480d181055822440c031101a04503800b01440c00c1000345800e020b5042034481c0400402c0c011100d551095179024922010340d101410040b881201950b41c100500901c80726540104454028280030350607111842201002544ca188441c1000344c1c0008003541c00000280000c080459142402240e044946c4a080011441c2c0040c60321500341590b520500300d503001100d04072040240c06402c4407140203074021080820008840c140e050100c451100c107492600d8160069010030f404039180000340340340c01150114250260100407256803090f0011958001e1078402080103000000000e801580c251408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 241862868 1250 241861618 241861639
    0x1a07030209011b29070e060306130905100606120501060c02030a03030f0216060f0c180323030c0f06070e010c030f1e0908061b03010b0a050705100c170c18012c 70
    0x740082231008581451b0000147c012050100f459070f8801c200280c000c0c0140c540000d152941101582c110f44d0103080002c4506622100090041c8a428014540c0f824640116121039002c03d07107070011007001500f45580c405c07180220001a404644440b01066500d001440c66072400500610b00016031307012462038085100d8816000b05001242c0c17405c1e03642000272992651f5224618081a40650038480080030300c1108c000da030410180401d901405c0142480c090102501ca02c0d20300020300b00c00820404440d141c400c1c0c2d0f04481058035558051418003c4803100c03800136924030030f051401c401c021210001c2e6144096014070b04a06a94a0b101560b20ba80c6800703082c55414001900c2c480c0031440104010401a03882100a0007206590b041690401103551140750400300383c40340d50200c01c2d403078106d4a0f81c581d50110300c40801c4910200e03842580d080209003840f083c02410000311881501c84080700281e07000700076007941450070886103115891500060354030201034041c42e5004000100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 241864118 1250 241862868 241862897
    0x30f09080115061e080a0b030a0204050103080415030207030818150109020a1107050a05060705070e01030b040212190605180f030c01060501020d023003041a07030209011b2907 77
    0x6180e00742132a02036445a51603140c92402c0c400901d002071845506120b08441c200068445014150081d4001e60156403114682004201100c6140145104043c070411a040019802c00441500032203071080b04002c07498219511883c042c03080d001c660044180800000d400b4183d90020701c0c804883d5035a82006034000f85546581d84c603a8000c03198130500c203180c01e100c20300b041d030040d21150740034004582a2550315841403192160a8001362404540030080000f9410031141e1811000b0900703004002d41c40d85404251500801070700000c00d02d03511b50010800c3e60074205d008480c8038071a9404e4622002c100c49607181e4a610400c00ca00c4a0750030040009210340c000320350200324a00c00c0d0003070030a0440d000c04040e48000005000680d500340c05081e052206800009144a00c1c4202e40e902506440101000c1d000c1c0b8005090070708040c010005405e880e42d100310880040e08010344d0a244d14142ca24050b0040152003282201c5601c8000c0d40c0420b12291b4804203020308181e49451440100c0307031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 241865368 1250 241864118 241864157
    0x20324010306081903051b030403030314130212011e06080c03031303080d06030c380d05041104141b04150507020f04020c010c2a030f0908011506 64
    0xd03c070303400e201c0c0c0080c40d554540354901000103070300038483d280003881c0115105910008600d040c0f0703091000d90011a06008050f007511510410030042c4000400a00d0310320038081100745807510090103140070303026050103000c00b50040d8590007419942d81c921000c13010600c134004c0800d8401e5001a01c105810110700b42004011200d88101c04004c1d04080d90940c0c661002a41c03004c0100d01e06282d84100c0040030980b604a0742c00034200d20b401804001b03207240030850010845229444288101941c0d5001c5482c0031000c5419480c00c07004041a01d80d201e0400800400c4142241ca07041803d000d03884030380d07000e0102d46600c01d680d0348402207000d0f445c5401c080c0342070107a801000b0a50615440d900c5555000380c0141c05440d1000702551030102c80c0401041c01e980140d00a032041c0da44074443c07024000e41150004010302201c48101926000401c098403000b00782e01c0019090110100654401501c20680b52024002d040001d016035182c1c5c088500308040d42d0310801e000a0032450030760401e0f0084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 241866618 1250 241865368 241865381
    0xe03060f04120507170d02030a0507030c0f0c05012403050f0105070c06110705010e0705030c06090a0902030c0409090f1103150103082a010501051807050304030c0c0305010203240103 80
    0x1c00c960051642040905070f41d141e0254406482c414041514500800d80800c018130b003410100901584a0525404003000d42d1300140c031110134076080003002c0200070360240d0018070700c031083c0c0b0304800506d2070b038140b460040000815494200d4801c042c00c1015504856480084a206c0c408403401409072441c1603080343c509440d034a0011b08039041c510042469500400e20048090740d44c0e916025555a940782142d41e282542d0348075802204080080c0d24061040c5144010b050356501d24041c4107000095080f0240d0240840465000c008644212407010656016007a184820804480c0604000150003241e100c11108242001c10051450401003800c0b04d01c2920b00c403011000d6421562501c074150402c2c0e099000c2e03400281d0119103202c0d075141880110700c500c80000250755060400b40702002d960350066800000c8203030f081c800c481d640001100c1e40941c0601d030080c040a42071400c0885c2003420f40c0302501c558000710902c4801034000c1c032141454038170003ca05103000e4030103006400f42e440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 241867868 1250 241866618 241866623
    0xf05031506061b0d0305060a380415020106230f0f04151e090e06130203100501030809190b16061803050a0207060203091f030e06070e03060f04 63
    0x30880030a400e81052009801000c9243c40c0b450641c0ca81c01000e9841c01c0e801409100020380c40710144034080c04c2c000b0010010300701d901c4a0b45a00c4007000c0300000b0842000340d040400700c0303101ca41005140490380a0314050888840d000600d881000e8000303002e051180655680c50316040312810242c00303520a070f42090240036220310101d040b01810020800d10180206da0042d8480030f08044001c250498480642041658041d441c10030225050800005800c1141074502d03000301903030b00020018015900410031400d07c0013017803042c0b01180c20050380c03c003140586030a00b8004800c0008640152009010030f54480c4e520780b2105c0d58a4040021502c54440c07034890400400e83d50b80c0440b840c5445d0280586800310711041131908520004190b42420307000110003040c0300d2041a0f0501484005000d50320055091400110000342c0c216000741d400c945a03503400c1100c0e002c060190300403045020607501524032900d040c0c2c0025000da1905260f4900c02c0c0502c50004034004c19000fa61030013a82c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 241869118 1250 241867868 241867903
    0x5030c011205090c210c030307031b0314040603050f0618070311070507060c020306130215070203210a02010b09040b0106032f1207020604020102150a060b130f0503 72
    0x40600104005000240046606000d0a01c0400301929165070140e034158864000c405d501c00001c500c0c5060600341d900b102d00c070b43c1003000303590702081d444a0ba00e0a101003030071a401024030545000d441c4911210f071400d050120100d40056a103801d907000070b01c030b20000704d421032540c2c0d5110304116154000710015240d000d070210100e140e8510951100f4600711900c21003e1521000b9141c0c0c5280c00100c0d480b680c00212200c084208604051200c0c070340155110026140301e840729030004c4c141c01000f120f1403a003520081555001d5540c100800f00c950714180d48001082c0c101c0c4a400b000503400b071401c003005982441440c07040c50a00700880b070322585c0c102614904a03400c09000f00c01034808841d15000451a41c40039a0041d02000d048411180c089803103290b9502102e80301044d0384100400e11029500038600300720160340c000c550912640031490320501142d6440c6610001800705420840004101003130200700100420244000d403a04030a418005541d00c0e010190b541605100095498 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 241870368 1250 241869118 241869137
    0x101106010e0702030d0204030b01140a0b0702010f05250b070203070c0b0d20040f0b12070309020a090908031f0b0d020705011e020706060609051008040203071508040c05030c01 77
    0x22440941c88503000009032040c1e0745042d192840c41c0b01660060340060b0744c500c0003480100f002840020001c4031140c002da41392034a1b1132030185640d41500840b10003030b0601c46103602002c441031081e4206c2d145200105c030045100b4180c061071038044502c0e084c2c12a2140c420740c0102d16024000815102d031a035105060702a12410b07d800c030802c5410034250510034035100c6003c008210b000d217000046000504500315116858540e0100107180240d200e0315101c001000b0702111081d00c0000250300c45c40307030b01700811803190303620104810b42c01a0b40503c50051500d6240700800183c138005501603600e109201040702c80103c1d21851180c59889201100b0384104411020840c80390050602e01e800760000040303200380c42601075142070021110034240c56000905404221291041d04d0240445207000141941450301242c80182405620b60620028000190440d41c3c100035082c0034003903020400703541198504005c0c1031508140c0c0d044440c80601140410b443c20001100d140380d400594485068 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 241871618 1250 241870368 241870379
    0x801021e0f0403110d140d080a06050f01210f0c021005010501020c091305011401150c02010e15040f06031e050408040e0702010b10020c03010b0d11090c04032010110601 74
    0x184d19803800e9181c111400d035803e8130100d44c4000302c4101c58111180a004001c500c01e100409101d03008281c0640246008070a000301d0f101d4950a0441d13110a0a1200b141003c2c031110401c09107038403290070805410311040c061040b0051b00100c241c00055001c446580640512040035107509005240c01070348000304d90211482c0900e04207402882c02882c00b04490702c42c2c4c540600f560810180a60011290001042210300e04161104407640a2a1982c440384440d030008108941e01c0a07020710451101c1c5400146014150495000300b40d80c0d4511000300303941c2c0740c0241c0a07100017040755170b40348104914140c0800751030040922490b4002c1285207010b00301840c1c00b0300c003803001e0444001c640da96002811031b6191101980d80c13440031500104480b800f4a81054299280709101d6070169022400110000f0b064109499140c02d080703942c1010765031030070101000e5000f40c0e031002e4045880070103003000e207002400301c2000171030301030340c00c00d07205520780e0401d0b1040708040c0754080c4245e1059004010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 241872868 1250 241871618 241871633
    0x60c060c090d12030501030212030c070603020f040504020304060b040e030c101104080105190515030a170f03130501050a05040809190503070810050604091e0f0b010801021e0f0403 79
    0x84035000200070a12501c026203d5030b0640c0c01d400c2002012a07070b15401441946801c1800c60345100150005514220044011036213460303091296105254001c611a04c81ca006501a64050300000d0021901d038a040e00b0000050483e41c1e111500640c43c04044c02540305000c0200d54110800c900104654201c90b200a4010942e07800c0c1c44d0380b070300350a01c030100f807001c02802244d0007075012030101e0b207103941950161400c45401070030103e10303500c4c0000807070150344000c1440303e012500505800c0f621000249201090710600c060f900d0f4000c000420816910b003d950000c116a000d0002000141c6e56a612501142d07401d4901030280345050000c1c0700d403480c001c1d4002035000c5900703ca1000c0b0070382d6580440c0c60000203030002d00c8940c21a11001c481c0800c41c0c071138203070f01080850703041c4901c0314140c8444403500c241c3c003016072603104c1885c103010500c548408024100e0f6403180000c1010741e580da0815000750007046051a04075501e030350380d24040c04d8101c250b03000c4020b141140751800780785654444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 241874118 1250 241872868 241872877
    0x2030a1d041b02060601030e3409050c0403050c0f180a0605030106080a2108060d060b0303210a060609090c030608010c0806030f0a050703060203060d0f0606060e060c060c 75
    0x6a0240e100ca10310b48200d500d041d680041040300307400404003402c00b000050300340c0385040003014595011880320078640b105e010f2513840484425422042c42e400207888054200e4458021500f4141400305103d00c0407010b600030002ca1740201d082d1820702400740c0403c91003403c8592150703400107420307804200099040d16415004550340c000010708079a540080303801e482c007640c0540b880344c1117002101c06101d50700700c15440a0000c04084512044103a03009080101c015116500902c40042d07100c0400203540d110300c4144500a0440361101000e03044441e403040c0b460300c1080d440b51040d0100d903030780200d8003406090b50000d0310380000503810285000e00618a034850001003545540c0000380301c2c2000e1241c1c13a08110166a20101c510b441c00a2510b442c0f4203000407440b6900c101d483c500481c001003030341c005407940b050001d03a0f82d840300f03000a00401c4017500040e003481c003075101450070849564001f1084500c51f8070764100f02c8001c07804100c114024440da45c0f4140d003140d40000c61075100e010040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 241875368 1250 241874118 241874177
    0x70c0506151207060201020a0e0901030206120c0d110405011214010b130b04030812010503151f05030f0a06062702031e04110a09020307020a11010221030a0c02030a 72
    0xc000150458500c2d494405540c0c042c40150b5400030b1004112a4000425000e80100340c504901c1c65143d58003003001485a103a031001b41d20910404205c0804a400888400c051181c0d01841040f2410441036280c1e44a44030320f9002ca034114003080c400c07810301d0286007192419880c0f4000c040c1c0ca4516242e200394008589040746070f0032040045200314644014001950150079055281c030440c1180c41250036068200b035109600c2180809403c800325072a142e404901e0880044140302c802501c40060388981e080340c0c0d4180580e80d2850184540001c0508086002d0401400001d5440803031403a03402010303202a1402010308454202100542c00460700403800620801c101403000955241c1d449060320304580704506942c82004078500100618040d2a40c40e90031869030805100207907842d4010400100000b5004115a0381a03000b448101b008120b808203d841c0f5140d0301b82d10102c2c95004036050544c031843c7c02400c901a91000066800d01c2500e0b40311100007050300044107910008a1900c17 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 241876618 1250 241875368 241875379
    0x141308040b0d0207140c03070b0c070509190b010f0507081b010c0903030908010506060415030e0336032d07030305030919080a0c020126010806070c050615 68
    0xa06080304078020b00e03008071080301c0181ca64140f49403000800071041c650012562103510061100d540201703c1a04540c1044c0d9190344d00c500b03c815030340c1010070f568021517104807440100400c90074100d05645840300803003000c21585504000544100a00300c820b940011000e019000c0000d0150000300340e11505c240041ca0301030081c148a609403117000360b4010004254030410001c140d0000243c10103860030310001c2c005440e004011030ba280c0501c1c850b00420141400074624002d001c0d91060041e04100c5003a20b945500204544814048000101c4410004402e24a01d42a0041d070410380e90440200a031104442c10340050301749402d035035040d40c0181054048030f03240c11320401840000754440c0e00c1e40c0383c403450702c01e4405042030f90f200380c180c0c040c1441c2c60174800083d581d48200d92851500303080011f8607002600040790615a90303a585c5090071040e4407189100034000348218122600501101c0c21913450000071118604102d038010b1680c1e01c16400b10701268401c000c083d6121601508 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 241877868 1250 241876618 241876627
    0x14151903060507020a0b010b120a0218090f191b032703020a150b0f121e0c09090d02060103020f28140a0302090105040908120f0703050604141308 64
    0x844400312001501c4420140c3c1c011070340f8008011003d006c0a0050a4041d04541481342071031515402480c000c000401d05503000a561900032043c154500200c0c1c405070101810b0316112008000413141601c12400351001d100c4a400c1602241c00303456401d00c607c244c1ca0307981c021900401da01038142d022600c4018160f00003103600528614040b513000b64001e038010180c0b000c10382400e00b0000303500d15481c0f0089040c03034141c4115854840c0c045006180c00d452840326001d49842071424045580c0c0200c1e0240000c1862400d83d1000007908180420211034814007a200d44019a644440901480b40035070000d000401c090b1401010b05903550b00040d03d40e500c1c280d035014001984400c002c400060901d100142445203d114110131480c2d001c0540e0b810191900756000180682c0c0140324452203a501c1c1c1c10101e04221400056841d082d661014000b140e00b44401c01c00c000c56012074003180020b1801002500c1840d15004100090620405170100341d16840e46911605503401c50036540c1c00300400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 241879118 1250 241877868 241877873
    0x10f06050616080702151c110712020715020705040b091902030c0415020604060506010906050f0313170307020d1418030f06070201090b0606030405030406111f05010914151903 77
    0x10300c2c111b166862003100c030f548948880c038408016000c100e8040c0034924013500b20b0f0030564084200d800c801d80080c0c00c08014480d0071022480c280141e00002008440ea08043c0b03022a00040c1c00d0090f01c90440d81800301107844803e120112108403000c042c0540c910380c00b2100040b043c2d0003180c100e603070f034504c0c580f4181c1c0310700c1c000100101c400301134801a40301c50104000c0c804980300310760f002202440c18000c1c603458034078010014010003003001a2101c000000c1045000365188041c1c9080d4464041d0700d20f40c420110008990f04200d44010250081040d041200c038480c00d07040314403441c41920581400703080d506106141000c402ca40d5018070940900b41000030040001d14402d44c50b580c004210365000e4074040d80f2030040a0a45801050184103010020354040107a6040d50030519255a2409009802034a0f046c01a920040e2000c824109211080b5458002d14180c980c480c80510401c10071b182040345580040340e500784c80c61a14940b40c0c4482c54440d035414407003002c84440e86040e98594 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 241880368 1250 241879118 241879129
    0x51207050405131a040206180103090c060207080d0207060210111606050910020705030909100f060512090d0c0201140906040b07031b1122020c01060305010f06050616080702 76
    0x3e030f842c0da0b000b0107182c40d100200410034151480c60548409400c60904107903010682900420f00c0c124884c1c0c0e50001a04c210341d2081d07021901c0150000d5081406654482001e501da00150140e601d1500070b801d41e1107400c030300004114007150041d5005008003000404400e0085c401801d5000a5000030051442d00700c034018100c00013540603207000103513030601d41c00c2d0310f00d041d94000b2810380c1d8a0040c00f000022440101c1a580c0c4600c050318071918a035100400c80404181941111842c598640e4011038210384c000050013140442002040c816110340c50b0360b070764500160b0700d07000009040510190055218500110a102d03201c415103040c1050040083d440d50081d412542580d4404103420f0185036100c21181c42080d1801036046103510703140c490050b07107440f2188440c0140e90081000380c8400303440c080d030502440c605030115122060604258043c165922042c0c0309507080108501a141c3c1921854088a80080c45a03240868840300300b500c0054011050750000380500074100541c580c0e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 241881618 1250 241880368 241880371
    0xc050408030c010b01030c020106050904080703020f0f010203040201030506150304061e020a1d090108060a020f091002060601020730060906020f0a110d080a020c2805100209030304051207050405 85
    0x42c1c0001080c11000000010308075002e807040d030411681010002c010325121030355103030781168001360f00c00c0d5039054604007a840c2409404045510344103004102150b0b420650145000b14401d9034148641c0d100c0e0341c200803443d0000c44104a8122003007002c0303800a400b45e444084016440544403001e42440f00da028102e03001290a4404240d1000c8201040001210741000c140c9040301c20100b83d5040c07118076aa6a1b80003000c180131150b00291001e000c40380b080a4452021008200c44180101408000e4507284151681c82c054400e0940c0865090118100344c084505400324400c246040c80c0800c8103041d032002802d89040b580d031001240410700c0d500080c00c0c0c4d0240381c401c80c3d0351400c06d0003008140c2e400940b02002a904040c11380c45400b03600411168000000d4000580c444171090006801c0484c481040381e00c81030380034115001e04601c01c98040038540034405403000070542d140002d0603846903042d01e0740c0c0760f00100401d11451030080361500b01d04484900b1224143c0e1500f02082c11220b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 241882868 1250 241881618 241881637
    0x160b040810020f040302010507060902040f14070c0b070309020112050a1d0a110906190e01090c0e0d02060307020a050601091a010f12021c0908070b16020d030c05040803 74
    0x2405104100c01000350948803007500d48110310348851001c0c00080f900030350200a04000c00080d00b20107005003600b02000d9540c00601c00c20506903011100801016808100e03942d800c82c85c00041d11080c0500000e408181e0045c543d211681e03248003080380240b055003001c174103210102c9100114001c031846003a1180908040000e58011030541c09445180380c07180b240160303400003101c030002541000d20384071228020348210046849510000d089403c4045402d4400700d902c420000d010115029014103c0340035080401c201280702600701d4506180218054210154a40b40030040c10130074003c50784400c1900c15205c00d07400300e40c0d81509181d001c0c1e000358402910f90b16416105600d910070070040d0f107001d080200381040c00510240c0507a440040140c2d07981d901144004940703034407640311802494054030030040c04550f440c0060080d0000b0300160780d580005400201140f200e501403404c844071680081c0701d040300840088002c1c0c002051074104200003440700181540041000d0710a010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 241884118 1250 241882868 241882889
    0x90b0a0221040c03150902120705150c120304230f0c04060e15040608250806040206030a0e01022a1605010912061808071a19050916 58
    0xd10100c0503420700000c4600e0780c4915940c240501001980c00091001241d80c80007a10606052205011008020b030343d40c06074110000381200400c46a002c550901a140c0c00c41d623000a02c2c640e9516a0323000c0c00f41211420707070ba03400107811380700c040c1c006030140d9403180c4102c026003d908080046846410b04100500002c3c1c0d00017a0b16401d442001e0042d4000c1c510140c40c100401440c0510440701d000000e0401c0e0a024034201d080303542030720385400c10f01c060010041251b42e8845002c512101e1185507101c2c42d0f4800e420000c02141c10000850b0070303405550010002401c503120b0840c02d00007441c20791000503440d9420402004420707a0071070b110340c0e61145030302c150341c428800300b103c5070424500e50000081c404602c0c0f024842c90380c10010443c00c1c1c5945010740d030346c001600d2400000602010b1094150306005640280130004a140103121143c455896120b42c650080803070000030500703a8882085601c6859410218001303944155402001907044400d035111100b00c4a4000c1e805810411300c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 241885368 1250 241884118 241884127
    0x6010306060506032203090801020f0d0f0e1c0e101e08012403060b030117160b0a0309050a14030310050d02060703051c02221203080118090b0a02 64
    0xc00c51160700010502524810702d10b1034100061803060315404039010070894240440307410f152085183c400602182c0000319515003010180300d199810400b025445e950400542d0030111441d4020b4083d004401001442030494141c40702c0c4d090544004c07a0410450210040780d02030740c844041e800c00701442d80700c2071904104000070780e10100880a0200601124100401c058000440c0104002d100c1000e020070040e042d04080300603029a80c004551000044004a00c0407641c00d40300b010300e141d520071140c00c0c9240ca20b114101c00c1c03040c440d811040c0790a01c141c40070720f40030b900441c4100380f1a00650705182056641d4020320100384824039040d03440442000300da860b03801032500241c5411141c52140510030750010b034851040030b40007401c1210101d090305014450740410302c191040244295100c12000000e20381c140609900082400221440007400e942c035501038460a80d01a07031103a615a00b0145221326942c2c54901052400360b55644902c041600c5c83c0250b800758201d01030141c0e44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 241886618 1250 241885368 241885373
    0x30021c211a09070c0b0705090102030f071a01050d1a07050903010903030b0a05040e0c060c03120103050c040f0615110c1011071a070308100f080a0c140a0303120b04020705060103 78
    0xb4903002044503050101d881c02d00b10100c0d41080000d58403619501d171456a1795100b000403421401412038140c500040410301004000e4903c1028281c5110407154488503a65a001c0000402180401801528000c400000a000b40380075441e8041100c1c102149049102c0011a00315032040384164002559107072000c40a20301140501e000340700464040c001202002c880c00e440e40c44804c6004e1154030b000a0150105030144140e0724090114482007400e581e4a042c00d684035038840481611441c0352108009902c01c040c0b2815090312100c140300481000e040d9029520640780e030941c40e403284038408825441e60359005861100c90625507544903004491450186403035159000000c2a10850100592400c8818182e40310640c061074000401d850703404416242100640000740840c116100114500c0400202d1615103441545c02610b0300c0d944844605107200d806007952f5108044941c1040400d202d070010b64041e880200002640c0310700078001030304a03400b107036044802d90441d1004009 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 241887868 1250 241886618 241886629
    0xb07080901020f09041503020901080303090c0d110d02030f060a0902180105090c160501020706020c16053006070c15020a0801030f0f30021c211a 64
    0xc004150318025410103035071082091050142e10070050290f07984442c44103080d8071078403031040203503000f0f0408407413561036254154880d4011106c0c41068456141c40c0441800c0140e40612031503008604020344000c01c408010488071510b80581c0c1c90320540a400328503410601c8000d004001410001030104c40e68418007000404041104c5001c80031b0100400a684038905c40c103900c11881a01265514201c90942d403601e0100c100103070a56202082003410820a0f6004180203241c500880b80f09104200c0328901588840c020650040441030b0261458034409050100780c4d09500c0103100c2c01c1700000c140a2030a041100c0b9680010403841c4407001b03004038480e0b001004c1e210a1015482c09001c0ba50250480e18180b100801081010224034140414080c40420603540007a108581136490000401d00f00080107010401c0d100411603921024000035194242e0185018031000160038a5015900030b102107181d002c60500c0400d500c4581701c060320400e9032454083c0640c0202e02c258000f4040b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 241889118 1250 241887868 241887871
    0x41a2101080d0306031e150e03040e01140d03030f0605040908120c0a021216060c0c020f030109110f150f0c1519090c0b0c030301030204110a08040311070b03040b0708 73
    0xc2c141440d01c1014004a845084e0700000c40002060300c4072901102e1816038001c01403240c202075005d10701098055140d8000c07009000301e8411809056142e40c03100c280250071140b80e01110380c0300c00310064880c000f90080e002040340d24100d6a0007c1c806540f140885c00b0b441e4a05801c44420340b0000d0070851500b00c41c03001c81d0f040080b028906040001ca020065560320604040000307915000c40c220080600700390a9100e203c0d40100240400d01004902410054a55800300d00c243d0300c804035203801b4201441a0501e1a0b042081c920022100c042800794401e0110303155034110034031100000900c0d58001c0203094000031403004030b030340750b4403401280d007401b41711004940e01600c104c0500c600103680b4030640304800300d40140025094041e20700f400c000300d015803200c00c0040c1e0100d03141c10940000b002550403203009860071300940d041510021444e21515032040007203004c245c0402c0200c0c2c4100400d0090211160885080d140c0325000038807190400c40d012114684008100410541e0041005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 241890368 1250 241889118 241889143
    0x140d05030403091404021c05271002090f0306041410050105060406050d0e0709061a0a051b0a150203071701080d0e040f09050d0206070c0503041a210108 67
    0x303085042a540003041c1040a114200c1e5400c401100a0140d94a80d4100c0303c0301c9550300c011407102000d0481c0000541000c98002c0b0340b080e41020030858000301c0c40702c5a9000308641001d00010f1815200c600b00039000740e03e010b5004002280700e041c1d035480401c080c502607070244407000390303c81c5902c803010705d0009481e84070700f00a070074480100442c0c0c030342c10182ea0940d00c46081c1240c0380c02102103d00c008016000402d400303803240f10000101203420758401000d0b44e41520040c1e4000d01c8030101e4034454800c507030f03d400000d031040051009004074a914504544440c0090f00d02c5042d5648412802020840f8030309000b56001003842401e035004076180e000da40d014165162190b140c00d03105621002d0500c480f03828454800f0031030b912a40c43d54491241d40060b020100806113980c20300644e200510410400544a480081000c0728020380c840c03010141d10000071450a402d2043c441c1d1055903042806810b42014010303d46180c42e03007a58a07040d042c030752800c84401c1d8940290145007007030f140800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 241891618 1250 241890368 241890377
    0x8073002060d111303240b03031605070f0f090e060412030506031905030301090605031b130207080328020c060f15030303090105101d0a0b0616140d 65
    0x100161034540c00c0d40d01e4100b0320300c00020b40c01404946503100b4841c41029000080da400008010001c020714025100300740340050303894100f1200700031001c80740f00080030b41d4503500c1880f41c0c9003031079200d14071440e0080c410310640754003d40c0d580103202000c0075600511a0190800410303c066051403080c804031141d41c200070441030400740c89615009648800c071100b01510f900000e012a03d04000020014019030304100b9460034508100351a50800c3c081c2c0181d60781000c40008075850001203a0f0050301d40c00301842c0512070444100000e06d0b42c0380103160b2070f66809100c00ca000c51128009184280288418074440c1020b8445e07031440d10800d6402d0803001881405010a0b5001c002045a0b0164410744001d0064030380c44560f8080f41d800f518003642c948000401c1282120064001c90701402c0c4d0b15000d00061922041d03091700140c0079245101c048e1500000044591909030404107030b01706c010703003460311300592040c4408441c00441c00c1540d20380c0206500b0303c46014100004030341110305240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 241892868 1250 241891618 241891709
    0xf0e040b090402010e04020c030708070b0a0504080301090e10050901200a090b0c01020405040507020304060306080d050711042021060d020d060e0105180d1d0103090c0807 75
    0x3039101d8202030000380c10441000c03041000d075203c5a04541c84400e07502c049907111880c13440c100000e81d00c0b080e011241100c84001240f01c6904a0003024084c070390010741359081d6030a0000d150300401c00071a48102d00e124007060041d03a1103d038030815000b84151070020800b0050400c0380b50180d1800f00c0340ea541c0c00c508120368030185038000b03040c0d4155940090103680d600d1440183e81d029000c0c9410655005240c641442901500000100704a510a84003845070035902c40505031914407042004001c508100898800108004030300384225100800019000c0310841008402c81202409160000c030005102244010400305208101c0c00e10381340c481403880c0c8800820000554058002d014800000c929001c01520f50040c60b00700070300030000c100603e4410b0380034402d000964080c00e40c038054049203015080c0309500c1c00f88105143c03080c2e040600c26000044000f4404020256280e040319100400d8580f802d000c080014240300e40c516541d046441c41070712002c840340500c0d00b8401c62400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 241894118 1250 241892868 241892891
    0x40b07022109030a020301050a1d010513060504140a0c170c0a03080307051b010c030608340302120d08131104050709080a03020609100905060105240a0f0e04 69
    0x14221040e081c1000507030b4440c009400481e01c0d1007204c02009505500b41005c0120450a507480b1000c0890030010420000203030318000c9089403025180c0364444901440d00001003009600016003040c42240341543c01160290981c3c1030811070b034401c40e003203115117804010f4014254900400e5081d0381c13004d4101c580740d1f000020b111480742c1c4001040d4000100005d10502e0060081d030300d069042903400c0290740141c0802a009001c08060f40b404a85410000714040030002030030b400f000070020383e20180d1254580880c0381d010440752032586242041c5008001600c84000a20690503050020000c1951000c0094a0000024460b81c110542c1400d00008070f4400101c0c601c110000f55000140ca44801e0000c0320710312601e802c07550b06849013001003000c050740000d2052084130410184d0b0f030800c09080001c1c0c1030750103d900142059001030010f116a00e0494810384821107094010481c50182c111a40ca03a50000d4be00d00010034076a0300345260b003607001131001c200200100c82c108400b000d00c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 241895368 1250 241894118 241894153
    0x50c0f0303040e040c0b030403050901030c090302090406090501021b1b01080403090306020a0302070c0b19050f07020112090203010c17072303060f06030a0207020a050307060507080304050304030f0b040b0702 91
    0x900c40d64210703050070303801314003400001d800c9807001d010b00b801c0301c40d928941424050015032115007414000381c0303030182c80841e051040b00000c0681c7c4e4010b1044102e40c80381d840d07203400b4113940b480554035950700704151104490b2803041079070954040c00141c50280010303140001d0403080100b0190501483c0020440080c0d07014900b0b005817680520016200c1d00566421002070050b8100101300d000c07045004a45e5404030070182c907080344140300300709071804940400c44460003a030316107c0760001c0500801d0015030080ca8601001290450001400412500081d09482e800100394010030f88803485c1001e110414419180e00800c1e40c1401243c0703070301c2d010b09010b4040b6041211b0380111400f01c0414920350703556898042c1c3e00030003440c1c2d507164101202e200e0025840014220301c81c2100007400100c070306000c2030720800c4803207031b8840f1401c040a80d01d614240d036200a004441500082001000060746061034016440c050750030b4000c44d10740351030700800318031002e03190781c1c10340d88021200980b80001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 241896618 1250 241895368 241895377
    0x31b1e090c031509010b0c1006030c171908121302010503010e07050705070603060801060f0828050307050106170a0506010510030e15150105040e1317030f04050c0f0303 74
    0x75a16860b5599541400511030340d9001031010354030200500c0005608001c00c8094140ca007400000e40b1103040c1d91042110443e844c9201c001e10030030304103800300a1400902d40c61305e180c4d019401903800314084061000078850105904903005400031500003011840e4822440d03011010b0705040960300c10580001c0e0060105214007010b4601c440b0001d1041445402030302c089950003c201c42c1c1e03032501d90b94094003070030f81c0740109901ca61814400040f04410b4040d10070403a0b4903034002e00651109104003520700950360100100c100046442c4400181c010402084c407107015900014a0506081c141e80104180182040c4103a0203072040c2408204003080e010704440044404020100d40e000003076000e0a0f880c030700d04500f4052100c0451104200060491140340000c03011625104490019900b0b4022402140b60544aa03000100342000c0500c108881c2d41c0500d8806603d0720a044800324658801c0f03803642480d6018000703001c100030701040500070380320081b50042109010100440d560b80207 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 241897868 1250 241896618 241896631
    0x5010f150203131401030b0306040b090609030a051209030c03070b0105010905041e1d03070b010806070807090902070201120204031a0606090607060510090606080f010f180207020a05031b1e09 84
    0x1604501c4c07401e1613003e540a80100c000280c2592210315050800303403a8080215250a041d0184c03000283c4a0003010040341c0c92194142c0341c031418441c0c2c1081075a511400100b80072240c1c40100195054058200043c28503144100c40e8002c0310360400c0300042c809032803544100e0007a802c00341a12200b881e110445481e044680c007000405002101010308070555801280525010001c2d42c0d50500c8038600f001c0b4142ca661008944568403117510031252041c0848401e00001c415a000f480b00c204a60010600e0600514200c2214101c00889604a074003690080f10701c1d0920141024102c85c00e901140e40c400c10848180b41002c2540d00414000d00c0340e560002c2500d90ba03980041c400d0250a08a100a8a1080f03c00c0044a450703403406406000140c80080300860908000584000040a80c1e41540c0c1402030310b22104864400e100040e400141040360310030916500030a080d2810007040e080101d017103a183e540c072849081400046403007502c48036401c42c000c200c822080d03103c52240c02d80052 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 241899118 1250 241897868 241897889
    0x10903091215020c01091a06010e01080c0717040509070306031113090b0108031c0b01020d0e010c12090603060b0c0604020f0d1a040c170a020405070302090405010f15020313 76
    0x200c1c107242102d15000410b8400350302e144046122070000c00158020180944254000780000d650441d01d41640d03e011185103000828040380b00d800355210740035450300030710130198850400321250703a50115844104203010213410046400c110900e095104981c00030840d050411409080d42c50301801030f04a82030f00f5002d02e10179890340c0c10002d29603000a030302c5500060200182c0d42c40d40d60050300e0ba8443c2c0c1600d00340c82540e00175a0302280c0701c1d204903040008140c0042c175030107200c2c00c0305850b040582c1fa55a41030003041d500c0c90700420640d201030f620140c2c581d03842c50070b403500700355024040712801e41080301351040503c00c10640d60b10016529030000e404803851504007000d503000600b07103101c407070006000346d04005168a0142c60001d410b07015510401c80750007001d80702c4200c140228884640a90706512085400000d41425405944c00150303030f00d000351410152001080540f0403c0c0e100c64500d1800903020442c2801005414003010b11300d01c040c4d8903000c0d4a144100c030300380417409142d9401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 241900368 1250 241899118 241899149
    0x81b070510020c10110d0c05030c09041109040e010501030b0a0606090b0f07140703030801150f030b01020f0a0323030c030109150317120a0204050319140715020d0201090309 76
    0x254401c03c9840a41507405200344944c40300c491440d4074030742180211654107420440c421581d2070042c4243ca1062ba61030b07014600b440c8441c002c205c00740c0840b40107003507803400420411032076468502441101e46502000414030394594500401c0107407009020310301d4203181a000313020340e1358485070000c215122610b0b482d80b581000024109a8811a0b030010441d400c2c03864403041c00e042c08907159048a02070b88070500b041e81c0cada00303c0480c11a40c0c030000d10001940d07a210084940e029070302c0f038444408d040c41141c903102c1c0c40001d1545450380400056010030080c2c0f0001840100b030561238883d00c403003820f859065003000c484000c2c0030302042c000c8085094942130781c484165013012110005581041401c0000c004041340c004440d400803a02a541c0071410001419246c1140201e4040701c2c2c02030020003160488a1707140107844003200085419505034418680400400c210800140107650142d803213900d80c403a80a0300d010303910074043c0d0569040c4800000840d4200074008101d5401000e4484e05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 241901618 1250 241900368 241900387
    0x2c0d0513171603050f0c03030a05070813210611090a0611030d02040e0103021206010f1e0f0602060708070e010c02151c020c0106090513060209010908010c081b07051002 74
    0x8040e615141c0c4014850b49102c0001803080010391450315040c000291942c110000c41410b4803441680c003620040781c1c08015031800100307001c0041c41500c0c07a40c011745490a4440c07010160303107180000d80c081c0714619007070b15005100d140e01c1b80380075000e54000090f1a0410b860302041c612222881950141301c50740312070440324001441114010302c0030801c119500d580301d286500000c1000e01050b4000c02c08001c06075158000095400c0c181c034641c03026005d490b840e00454403585602e24000d01c401143c000c900180d0b441101c0d031080c0c0a042a03802404942c54041401480c0c400000c19107030270020a402c00301004e0760089051800690156030710100580c3c1c800070700169124030006214500e44001900c070720301c1c1c80d950180c58400c040740002d0000c10782d078988403401e890090360807271240942c0f030141c2c400080b010350003410203500604085951560b0382c01c910382195030883c560303404034608004000943c0c8500410100580f00101c0c250b080c81c2c080e40f59244c3d80c0f012144180c4030241c5c0060f03130104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 241902868 1250 241901618 241901623
    0x160807020f19030f0507050606040c030e060a231b03040c1e05040606110c13090507090501140603090d0e15040602010e01151503050403032c0d051317 66
    0x1074071201c0744101c500d1050300e0810300c1107a0400c18425000104d8582c2c00030041c0b440390f0f007104c11480d0443e004001c04c2c0c4078002080004c0100303840741001e05940d103044118114040c0302c46840341000d040c00103000340300c55450403030382d56200c0c9100c02030342d6a883c100700041840a03410001c2270f880c0c5504e01d84981c0c80c0c2c41c0604468240b604070710140209050481d10b1a40c0001480e0241c40c0b054a083c00425518203056a075403440b5400c80401c1e0300502c8124190303041c030030102511071004110205001b141f0b51201d900309521508170500c0d51384c80d4001440810b611007102a0310b442c055a14514619002000946583c1c030704881a0800031940b8403a1807541d1261906a20301c00030039000c0340e9581c2d94a40280c000e103083c4c1d591382203039402c0c0110300108549000d8880e0442c0c01401c20094015010034081b0000e04005008070b0078181d03960180c424040c03443c1042e03401001c1c881030241c4ac031114040942d1900390f07030b4060401080002c00000810503445d0944a045460340b4282080300b032000500e550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 241904118 1250 241902868 241902883
    0x30c020f0607120210021603051c110a03110909010902090f0a080312012102060a03060b04060f0806040614040209030109150219080108061504020c0a0302061b0316080702 75
    0x40c0d20078800b081080503c080b84000c04001c0c5519022240003504070100902a401494076070070860441e0f10540e00400d010310010821102e43d142040049000342d0b103004104c070050307903000c0501200450003903420790f014460110b445045a42c42400c00e80607000050401c01e0500420400c0c03030300030a0380c0e18161140880488002c600a003240c1c1c001d5100e40d482607687e0130090195110441160001071400308201132022030f8842c3e69610b0301c80030307080d400b03002c3c640c0c0c882c031b04c00010141c0e030f404002100c6410700d01400c06003c0603030381c042214006520043c01c9030360107040c95100302d03c0c0480811408a0b8400c0a076040e04058078050385640c5400c00007401403000c40340280a4207101486019101c9859000b000380e04101d162410301c1c44110030003220030103424041c00286500c0f560110310911400d82c582818100018800340c504014145158140342c2c00b8403045015900c400144101440000404004020b209441c6400e40c90310107a400422203c0050500c03d0100b1440843c070100d20a00c4842d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 241905368 1250 241904118 241904149
    0x1103032202031f0f020903030406031503061b110c2101020c0a0c0801181101030504141504050606030f0a110a05060f030a06151e1206060203030108060105030118030c02 74
    0x10703240403401070750000006141d18840180c403450052130040004c558800e80e29a02d001800541c103090801c0c0c0107070020f00d4a0300d510304103440c8020b800800101d482c012102a105103034544056412609406030104503070318030034a80303030f081710380c400780c031a00d504a104000c0440303407401008400b204505540240b14011a5001d00d000300e03008681801904c02c01c000031114900001c00614101481c0014004001c10740180303160210150070040d58030070f40050303030041c1c001d11003248018002a40945080072402e1200c08400c0303048100700620105101007a0700c0308050740544290911100b406032960031039880142030240c51000a43c864031540d184030f000d020041d2900383c1e00d21040c00e00d4100b542085800d0b03046541480004101a443c881405400511545840203040000a1020110719480c1c00b01e00820018440d00c030f0f80407525019040080c04103802441d641e50400c03a445080090581040d4041c0c0e040c061440100314100e043c00912235014600f4a030f81140340c3c40010340034071140705103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 241906474 1106 241905368 241905373
    0xa080f06040b04020a090504060902101b081308070f15050901050d0e1218011707050324060d0501060e090103050607140c01050709060f110303220203 66
    0x700f5081440103010a200700d03281c22850049032012a030545940d62100010f009500740541720744906045441c103581403d42c64452400c400040f0f00d00101040400614210f608181e11080300c0640a03000590300105d948403003803040c140860080c0140010b00c078030303071282d1640640103c8000740c0c010b03107529040800da800c00c1030050112101d0b8040a009242000b160780c601c0300002c005030301d8000c4d00f171950031503080700060421410b00d01c83e483c904200d600340918660000c06403a848000c0140008905c00401c0f062200d48134400149600240d010075424000d900503000305d0f068070420707070b661b0401d60070602c10003c01120031311006d48180c001e41c01050b0801e1007170080900701c00840c41000d00e419007421065003116001c64010002640025091003d0703540280c051403000102d18002450001c1c103490583c42e0304c0042c00c0e040010302603003400e1428211400b505540290000d05 = true := by decide +kernel

theorem cover : BRFrame.Cov 241726618 241906474 := by
  have h0 := BRFrame.cov_init 241726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 241726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 241726618 ≤ n) (h2 : n < 241906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
