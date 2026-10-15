-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4460
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:41:19.729604+00:00
-- url     : https://prove2.me/submissions/a1b8511d-2158-422b-9328-003ad7191cc8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 801978417 ≤ n < 802158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 801979667 1250 801978417 801978427
    0x1905060607030c0503040f03030c0506071706040f0e01020301060e0f0a1d0705040509040f060506010801051f0c0516050108010e091e0c10180906031a0c0409020c0a0c0506 75
    0x803458001d01d1005000c014030a00d07607104110040044401a003509114141d40303554a08e00100380c2c0d908182c045130180070320700205001c01d018034000d1203000400c00c800b03c0c1c685c1d03550003400014180c142c40071031200d0b1121124005200f00f840154042c0145507034400304000e00d10140010500001010350080031403c000f0800654154110340301903d04901484e01d9882e1010100e8482c095038200e164824040002c1c0700c1000390071151102400e110794800d0105582ea4001525080c01c2403151036040107103100c0a00ca0b5940c1e014003c4480c22050070a01540011520b802d0b14200b10521400707521a113901003404a0343e01b00d8000d500621000465002519141e0507d5480740460404050440f00a01e01c0002080003844040308110003d0310314500f01490300c0c0000c00484c0c50318401920061414400310300705086001e81001d59400a03629083d004080e1000070001c235006221081c01d24082c070010075030703818a000a1942d40c0c0c2c1800240283ca1741342c1011030041c002036015520603581042 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 801980917 1250 801979667 801979669
    0x408150610110307051009020f060703140d15090509010b03030a0215060411070605010f1d04021e13020d0f0207020f040c0e0d050102071202190809190b03190506 71
    0x50044628051868801902c400034042d852640c025050002d00b43d008402d004c020310f4403550301014104c0d0003100c4040201884c00c003131010340e120b030880150005007040180540740c4140780040003101c86002d8001759011149141c0002c0354996003040c410350352035205124180609000d14045400220041c5151624100010b5520300d001c040b00c1004040341000100e0030b540701e0b407082c0b02c81009804019950724007441d03d04010142402040da02d900314400c0824110300003401c0034044402d010301820281ca0340d4007000303c200f0000168003c1c2c5201c42c042000c16884800c401000d000500a01607180c0602869040641e140b00328448000d6105120610140e40c4007510098604d00a513800100c81032840e40c00c840349224a4030107034008002140d480200081540102442c078022010000c4121140d2012a207407448401d00c1d01112207800e0810020507075200060001c1e45008102c4d01c0014803002001ea0035500550020408800120400440c0c0b01840589008410040d6040000b807034014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 801982167 1250 801980917 801980929
    0x3080406200403121403090307050706020d05041205010204080d0801060f080609070305090a1b05010305061e01110a0b010e010608060a0f140a0302062b050405100b040b0a030804081506 81
    0xc48007070310507000b142a1240710783c041c552130b05d422030000c3c3d001c1d80d9900d024003c4075030745c2c0d2203170700308a0313107032280c1c190000380240302103040c3e041e0403160b545041c40e151411100e020803100100e400e8500c1c1d542004009047c1e501005000b403400d440f42ca80022942c0340c1034001e040317995100b442c403013440440c00802100d5030303842e41c0c0c19601c1180f17400d0014003601c425002c64038008107004010309500300c0301c0280c11343c03104603240c0004070fa509036001d2256079982014440c0740e10030100028011801e0740e0f07034015558020004020461026001c40e1007410613500c070184061801e03800300e000c054015005000240e0301070120390740410152601c05280345402e1450000c1a42403003454080c0c045417003020f40a60703039000d001b4021030300101066102c410b40031400c03180145020541c00b48880700c114031505011345000d064402e43d082030140410403034080181010f411710816403a0b229070744603d00c10066079001c0744000a9409640e9490325503040000543c40c121a0744131030150b990780001042116540c00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 801983417 1250 801982167 801982169
    0x60306030519140708030d1812080c120408070b130b010303030b010c0512040f2403020702151215040603110d02040e030a0e1c030507031d0409030804062004 69
    0x540ca12440d01c0380c10f401c00a004a01c00150b054a0380a1008001020740d07000000c0c01501304240c2d42001740c6010702d00c104142c5000408024200d580c0c0058101d4082d01075400d00754001c401550551520303c1d100201c444450044508550120000c42c0b00d6050090003d2010741c008680c03000c091054a07141c807034004181052100408041e212406860b85910488130016119403100480d410000565008040d0343c02c640141100341d0800381c00050203001001c4011662507074480083d900340e401040807030196018140c1660000d44411001d840c071480c480080c08008240c40c2e400b1000d050070499480d56401c48484c0e144070354140202400820580d40052050781030072036003c100304d04c5510100740500980c51442032a0300000c03494080d04c60300b16181c82d1035800211110342170030303880d06040d8156903614040030b00022020b021113030010b405002d4442082158040078081180c5140001c0d00740d481410b01140059542e20a0104101c071501954640300d2108400580701006003140044c01e000d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 801984667 1250 801983417 801983443
    0x30c0706090816150e03030f0f25020d02010501090b03030f1b03070f050d090311040f380901050906060a050909010b07140c150c030c0102041d010603060305 69
    0x40c03181c50004000b45101156541540002c1d05903840c2030508085801044034a00340341c0d40c0d0b0400441c0c81580e2004007c880c4a00c001340103028464641845645007510002e160a59000b001e9080d03a400140314481038001140680c000c2c510300801060083c251841a440310003800d051805480c0217a81c04000d60b000043c0010a407611415021034584040ca070b075204a8480c2e0100242200c140b1020090b0080014098011200071860504007141c01c281c2c1403002402110030b0070500d130a80d2a0580098034514200680071440740c4030249810790141c2c18480991081d11032140e4881c00d0130241c070a14440368002c0b00d44507545c0d898100481c42d184401403582c2d03c02c00c1d000481805403070160003a141e0405016166214941c0c4607039142d80143d108000640d01d500d5441048040703000000f0b007441000a024203201c07040c010031801c030395003500516090788282c0002d000740303048002c0034409070004048000001c400718202c1c405400406070103812841c00c00d414000240040b600002d800395080782 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 801985917 1250 801984667 801984671
    0x61517010e160b0a1716020f0309090609151f030606053406050c040311060a020a0b07020109082809060219150c0804060b010306080a06150e070306060e06030c0706 72
    0x10b441a0304480c0c407217081c81c0b14615000428140483c88141d4483e001c05002a03400f162401d0a08014460fa640a003504941e4000da140000400d0b9050007a401c0c1e40200f009507868806000b070794002a02c1c1c00b03402d031020888000010304c50301296458003460004210310304000313103440200c41c500f22208030b14406441890409080032842c0d1440c1c200a8020540c108000304041d0034491080c02a0764424441555040f204e40d42c5c00b40c8600c2d05204646410420390014018213280f942c078000003103401050381055550310440030004c502404020300c0b43d50481c51304004035040f4140400c0010303030880c80b540d040000640341445210780019440800010b038042580e2010b00501c0c0003850203150044c0003140904107404800500d400190282c011446600d05010100113040114200d62040c42140702941c0030b0403a2001041c0503511161180014400340008682c84011000c40d8501c140e03218000603690303400801119901089905e4829401c903115880c5040c241070720403e030f019070500038050b9a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 801987167 1250 801985917 801985927
    0xf0608010e090f1203090105101d06031f050103020319030503360109020901080d0c080903100501030f05060108063102042d0b010219061517010e160b 66
    0xc541045244112000e40c0304030703038200031320304e62003103640d001620080c2443d8200000301d100112410403043c16512082040300c03828000e410300c40c07415200a46410b416010b246044c1400f0f034208540c48211b01890b0202090a5245106040c0380500c000038890040c02c26078500c03000607902c9011640c00c1102c0d014141c4100000c2c070500010310301045820f0110780d50b200c200440700c01c01034101102e00e0b030013280c0d1021281e9031068039545a01c04c1c040303003000003800701d205100001c00300c1c0090003425a010b4126070380019985104070441d0340a80082c0d51200b054004101000800c100903800741c0b4111010344802d050001d0780441e2406a0300f003403041e4500340440c049201500ea0130414046400030701c1400b0080c1c04010701d059102d0070381840c090f2a800c1d0480345c000e00d031181c028201a050181d00400384403002881c0940083c80014045800d03985400d015226410403000f004090070449100c1142132900038002804c403175500031540d0f4960064404aa04202260041401c48400741d6030103a0316 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 801988417 1250 801987167 801987181
    0x305070e090601151e0306080f210a0c02030f0a0b160212030618070f03200f2107030c090608040309032d050309090903070b0a09031106070c0c0f0608010e 68
    0x241140c800b03421040e0301d01d0000030b402c141d140c0c00c042d0440d520b102c10380b01270f4402c2c481d0701915500b0303140142ea02e4000314900d107101300c01e00310000d21602c0b040e49054070242840e5400a400c0c4003034101c409000340e018510400c20302548907003898000d608c9000d014130000c0c544c1c4000c1d4a07080f0708044403171500c0c804000146552905078505070560200900903505141143d000b6141801e080c035400c001920340a105c2140c2c8c2841518024030600c840000c074203107400041110090340c0000d000520000b034000041d046031141c00d03180c83c01608507440c042100100c00700c005144c003030340794009401c00480070244000300760090020019241c00c10417035500d003112000c15124544103003020032401080c0a01e41c805111012011b40b82c880f4040342c0e144881d840e0005842da89028000002d0261409400032901c0d1000e40e600404403a4460704052407020000103031513050000032200b640c0403400b54600403041240e103403041006404c002501d09040f60410400400b2880c050045000308401e0070041400c07 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 801989667 1250 801988417 801988427
    0x90e0a021605061006091703120403020109050706080a0b0402040302090604050a02090d03020319033e040e06030f01050c0f34031206030312091511040305070e09060115 74
    0x2903160071000303d40081c00d04880a1a810b08a0702c585400695180c9012504002e144a89036a0300840401941400e00206280c03000000140088056650300c40640c000a802400507200401c8140c0310289146061040c02c0e0030f5848660510344260300c1040144016960344510300e070001c000341c4002500d6507a1441d104020b206400919074401106500c040030035078000000c0101c0d007000841c518a01801074405c0d815680c030a81144900080f40030f0000c40d1003a140404000f85103c0fa00301d0043c0494408000b2641d44203400a02e1294071900802403581002c0048881d101d41e00e10003080315242615080550b40a286001c1c104000001600712000e40720b80c16003c0c100d840c183c0885041021b0004c4110401c0d01c0e100100c02041541050500c9013000b0701c1079804894060b12174101d90406229150010f24a0768012039074250b00030040c0100d0140e605c90780441018030355483d580e075425800c000b40342c409a54841640841d807842007080e45c0b00c3c0460320504440103542a080341148444050f61 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 801990917 1250 801989667 801989707
    0x303180203030d0218041a13021e030a0b01110c0118180203090607020c030a060f02120103030e0418020a0911120c03041e030906180302061216090e0a02 67
    0x76241c400840d186528201c10360040085503e4000a491145032440a020a4501061028451044c48819000d41742000300f00c503400030102c00401440c10082c41592280403a040c1c2d80008102c0c0b0100801080381c00074412442e880800742081c9010090071504c44c0c0d507030306151401504201c61b100004401c1d080c40d00a110203400e51031080000a1440000c10f40290030031034100905108000228a600c1d0012510004005015020f01254070551f1a210050901200030301229a420450000d01f5040907011601a601c20381d180c0d02000891000c12040d00e03241500b01210040c3c41d0004401603031810031a400707e801100000c620500301c0740d242141d0340107201410300000c03010010000c101312000c0c021072085100e9210075100ca0000d0044603100c010440000340880e85090085c0242d50088105400c4202c20a01004d001901daa0200e0170540106507442c1c4280d041c2d0050203046c242140e028038115146140149090b45020005054140090301e041a415030001341c0f20b59119038424100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 801992167 1250 801990917 801990919
    0x6100510050912010c090f030c15200607030e03040b07120507020604140a0b040b120a180c030b1803180402070b0412080a05102303071d15090403031802 67
    0x120030402803000b82d000c0e110720a4201d000480014022900b103040040e00c2090703a41003003032008500d0820341c0c07800c26000f02500e29005d11449480a01b80c00f4003204030045003000b0bd0340a80384034103007418007074183c50b00110b00400b40e401c244418010f5404d020142c40e06185c1101d6204010b01480e10140c41174480d004000e500070300300207000718907406a070100d403503100d40680750201c146554840c032001c28021801181c06110042286420382c0e0250f444554100c403a070312000450700b40c610505400144800c4080700c400844040c100b003440b2501200d01e0740440e46400c9080000c0701c68015540b02d1103032044502c24a40005d17681c0300b9036152a03058882d004e9120b040d00b8024107144c103028206808000f040f0000880000019044080d41d02466014001e04540e10340d03118101144260200c55002c105000142c0303000e45003801d130785e081051500420000c0e81100303120b0034900b1114800d82005040841d0007001c030340003c20030340791f10161590142c0c0502e40050850344c071048101841c1001003010b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 801993417 1250 801992167 801992179
    0xc1b08060711070b03040218090705040c02100e07050d02130e010507050c0c0d1e0f1208091902031e19150b010c08070f17070c030308010602061005100509 68
    0x101d0316030031000380e6440864031021940038582d01e11404c10759100880e0001d40015502c0c2c6407081d064001880a9080707807190007a03c13681c40c0c446001c2001c945510140c140140e010520080d0750000030310801a07002241c3e8007810401e410311005c41c0c40214002c00c0203014850b0a5480b19051021307501c8074000000c1d0b90024029400c0041e802050703a00085000d01a6004c2c1e581080c02902c0c00c14241000c04d603000c00050040030902c180c0c6007003082421001e640d01111585035000041000401d6080c180c0389403110368280c01c0c400da03103c1c500981400f42c085506600c164000c090307a400110800204244c000200301d4101009041303040c146030381c0030784080c02c840b00201000c00a01c50042620440c406a0070014282400011260148043da020300005410480c001c0460488001140303094011500d01e0354035289246045c08035070048400f80da0600508a050080680c08074465005055501c003c00050800201c01224070409110301071088040041e020f02060046082c0c2e4813005000300342c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 801994667 1250 801993417 801993421
    0x2b06060203030a0c051303030f170a053309220506150103091a040201021f060305060717070c170c0c04110406051206041b0e030d08070c1b0806 63
    0x1075a00c1c0c100351011900c6604000700024220321800036200300b9002c1d018120440e03440c5490035640b03507151721240701c20032400c0c0f200145401c010101b51405072581c10710008092030041c03211181d16220702c111032407044000c01c80d01c3c1d150740600240030540b0412186a0038a85031042481d4031a0100d281c21183d001651250005022000c01c10500c10341040201c0001001d00c2401101115080320004142030045c04840c800507096494803503101340b040c01100c0402415011050707510130110310384116151103940501c00c00005026240e000038142c20005240441c95110905c2c41c0310007042c1c1c508102c160301c0b00300d05110541d4419440c03413040d00c0e61140e440b81003441d035a45500500082a0042d824054004e40c580701040460b402c513111942d07200d0410308030030003074695030754090995580302d500c0d140d031a00d000c000440d0306201d14406444014111040000341801c00a225000c2c40078401c0200c10410b03002d4018100d60055a0700c008a5882c04242c0780340c89011072455004501c0511035801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 801995917 1250 801994667 801994679
    0xd0b0406091407030e010501060903080d06092901020303070503060409111e01090e0103020306011802070c06030c1d150a1115181212060f0312030a0605030c062b06 72
    0x3802d50180c0348a0ba000c0c010310f004403401d58240d86086c4a044d0024210490400210b01e407070700074002d60342910401081c43c583d10b8552070241c800c00408403010003002050b9805a00c2d811410004d41030023030001d141545001040034106000007000742e0702442e100e2501d0f00c10400b05100c02c0310411801054007003010445818201c0703500720703036013142d01054125102243c4a11340105050482e94001d006005030f80c20b240c1d4480c081014520490a070680034040200010410603210b005447d050303600140701c4031100c40c007c3c01c2c1101090007040881d00c4c240d1690841e01d80c0d809440003105901c401e06c1d0b403810f080e001104c04041c0030400410900030001c030906e524071154510303802802444e044004241110020544402188549004581c0200714295028212000450740070350010100c05104001c5400329060000208144038030030000801c01400c10100e2043c1230142400341d004216204080001c1211840341c0da200d5a4032880d01085462100c0c0c00b0b2307504990486800c403050090942d512 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 801997167 1250 801995917 801995951
    0xf0905100e07060e090a2003011d070c030f050c0705150a02011118010e1507050d08011d060d020a0f0303210516110f030412060b010f050d0b040609 65
    0x1880e81c445005520700022081d110703414502c1e44210041c08102d5540b035119a032801400c007590a001503c25101c1c4901004180c04050b500a118a10806c01e02c6c00f502400305035100c10041001c8117010030b8210b8140800d51152005041458a0a00300d07540c0302c0f85008140b6006807503100340e0707002544140000c80304d10507001920140c02c003a0024419513804054180e854012a4105000f00a50b01c103401c110350b1180d180a808403070054449014104641c3c0c00c1030340c1c0d03030115905270b40c01c1e80107180d0029203617403016583c0e0044c9803100c00280c10282024514240c1c1c2c0d40074107074174411803545a109003076584883c1010700901030781e640182c3c002e90f20314000d4080491911035606045420f85941b005915074084c052192600322850000c1d260303088000d8420310361640c010302071031007080f402055000e02040200080d008a4500c0e064078031080c545a81525001e809103410131840a109080c03040d00802a909840c6907034002050703070105400814018449540701038025030811000e0f00501500c3d03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 801998417 1250 801997167 801997181
    0x30f07080c0c0a03030c081c0203150910060c06110c070f0915030f0204181e0c050a060503060d14151f0e06011413060e01020d0f050405040f090510 65
    0x14800b610704403002502040300745403482c8405008280711070030542c00540110000d040403140d483c41c070760149981011420807a0402c4800c2c3c04081038095441050b8a8048881c0368420380c076421241340c45003401402031540c41d8044008143e0386d141d0701445042091101914010600c00d4100c03100c8540c0c640d020440702100d4440d01462903c2c0810300d000008409513010f060300c0d00940d034203c0e01241a400d101c0202440850076581a540102c0140050a0a1030110f140100c050415803101c100d82051500c0c10066880035102d06503205042104039041001c0c1e0b9440750b0101c6480f01c0c5540142000314010300d0001c4501c3c1380d402070396440340101c1203c40010380985100141d0003607504048410b14074a00c2e0500505400400000020305150300c500c80818041240c070840f14103014070040f903c0701c950007582040010401c03000207805036580c100300030b40340b000d80c86c0790a066918903e04044e0040c840c03030143d90b0145440b82024141b90303070507420009610b6032001c00c8552100d0000c009400500714 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 801999667 1250 801998417 801998437
    0x30506070504030b1602033a02040513020309100e0a0611030a0b03010e15100315020301050f0a030b010b03040303020f03130302010c0207051804240c080a2309030f0708 74
    0x11500070078140032182d080501e080d0040d40040d40f0300588c441c004143d8000b005407064403031043d2146810030300050400c2d003c000c005960007503211030900b0100481900c840c44008103445c03041c410000003440002d8811054420194001030741e506070a062402c0c8451840702508850400d810104c0f1010032400444c4a2410070004000c6c0204030703020503080c2d40721038020361580e03807202d074091005030500c0e46156080030700c00b0401d13154160b80e59038810b50301a1440301815026408401081a400e203100e03001040041101c94482060031607079100e5070f40106005030b0b50492008000581007602a43c12282120ba01d40300c42601c1e89440e402e04400b0801504d030480065003407007448813101d400000d03154107940700104400320440348500e02d0b00300c00344018010b0711840d110381140120248030484031a548114603902040c40c0180c0c220207040440013501c2034140d5850448001d24011003208a42c1e441401d202d904050358a89401207843c50090030500042c44600245100402c00301030020420686 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 802000917 1250 801999667 801999683
    0x9110921120708030a2a03060807050d0b04030e040b3f0d03090807060207081308070308030103030503060a08061f08010c0504180e01060929101803050607050403 71
    0xc1941d481c45414002c4003401403000f0341c02d00c04204079030101e4122502e110b440c80e1a49110200042c0510461500d00c1c605101090781e4150a01203a00d050060f00090a425140032100c80c02ea6500d00d0a4400020070113400c1040c0310381c0d03103038460f40c031078016013000900107210a007018801d0110150207050221f00e0345030301d200d608908061081c0e60304590260720825000d0080c140c81d00038150060f20081c0e0040380d00b000b04119040c0028002d101400c1700a000703182d0503440d80c403c0000c071007582c5015042002e880c0d0201c102080002c00c10421241501d50518007580c0f29255400400c481c0c6a9640240c42c00b405104200014050907040c90700b2200f00d13094040c4012079941c40d03128201c65486d0540f000207a420481444024200155010b480301c0e14000001c2090300c0c40640c03421111543c10040d80280c861819202e001e0211001c12503564480803103100c8042e6074400100e1030020200b680c82440b05500b8081c2c1c80e00c40c0140c0c075234000d47d040400c1d0b800c0c51500e070038014240e41c4980800c80e1130103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 802002167 1250 802000917 802000933
    0x9020408010605095a0f06010207050d0c050a1d0c04050d110105120f0915061e0d050d023304020108060a03050f0c010f091805150d0614070302090a09110921 69
    0x81c0c2084680c0c7c014803040e005044840c1c20003061210030705060005079071000c98244000340c81e849031180c42c8000c01c8441c445400c07041058040c01c400f09006810840f0300c0700148024171003591241042034100781d10a008102c5103042c3c2d00140e0309806000031348200c00350540200720014403240e101505c500f4030401610b00a95030b51040000103882aa21142c100b10200d269814055500c80001e1a12174001e02822240004c0d0ba1054540306000040d10f006803c5018060021414071242c07080c5591030074041070108528142400f00650014000b9040200d07600108030f06444208a11010b103810405948022007240e06543e520f41800002c0c0e0b0010301400f0104014511030310012044d42c0005010b4804040d805044101905018020500d1200c0103a007002c040d6071042c400346003491084002207001601c6030810002c01500400d04000e250040001501645d40c0ea00d2510039941c0551001070315000c9540040c0c40c40c003807241d10076003210b0103422a108014010303041c0d414403030748882103032405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 802003417 1250 802002167 802002181
    0x90f0609020f0436020307030507060905040e0316030302090d050a14060903030705130510022515111203040b0a20030412110709020408010605095a 65
    0x300c0f40103c03204800040740c0403c001038043d20710001468104c42001001114143e00024100289075104856076131003001c007000840d030040304050042a00b00c3d820001d2610310310b01551203100b9104038281341081d50310000c04250081d415650601005410182002010710740a40d1300c0048241c1a07501c0004044103141d0203a00080d454803031254100a1419a01c0d102c000b5079840d0030218900d0020807a43d540454143c40d0440042034004132a802880390340d5042c007500302d8043d100072030126143d02228040c0680784a03d05844414822454442404041c82d5405070518a8074128011440030003c01c0c002840f4a04448501076441c1c000104000040401c6100e0440155803440c840c4000c24800200070640189003145100070700e0400e001c05099000c0a142442ca5513041141b0040e40890280301c7c1402c00d2013148060f1409441e0071a0700d041491441125010ba95402820203c0302c0742020318000c8080d00e00040759140c4544d2084032035030156410722144124044210912400d400200c2e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 802004667 1250 802003417 802003421
    0x307031202152a0d020f0a030203010501030c021c0e061908071101090b010905130f080c0c0a030b1810050403171f0b03070219080304020a0f0b040e0604090f0609020f04 74
    0x2403086048500d50038507100041c2c1e1940c04c40406240056400d00c0b0748803000b28240000c0282c2107280e50300590301c2d81008000340072142582101c8045512845401e0000942c2070724a101c4a410f40c2080414070220000042240c8178a0310204000120810081c400c180c03c480114022482603c9101c0b6900030310002908035024044060300e0f0901714001001245160b6002541003000511145030920007903d40d80c2c00281c41c503108468204001440784124042403001442801003162104000f03440c41d1a2011080c4015010200004500c04518104001000a400c032902071a0061200d4509030502600c1450900340d82c2d10011000000202422421444180901c403040691000d96051580f200200e8000620050a500c10041840b402c3c80240011a0b03445101c3c100080d600d01e000d1042c049035200c558040850720812640c28805c16200106072015030f40d09021814540e502c1c1c400280182c0060700d009401c2201c1c645109007881029000010031038026581092484118018402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 802005917 1250 802004667 802004701
    0xa02030301060c02040b0306091e0d0e09070c1a01051e011209020103061a0310080309010206041e0f08180303030610050d391814030703120215 63
    0x160400c00040c00918000e40460300e031540080c000081c82250040480e160417810b450981160388544415204800410b9078140c4149140c40a0480000309440203041c0070802d9404030300c154140000240d00d40e100b5044c0c00c03885034100d016099401801200c0c1090f01100b801801d004822280c0c0b61402c3c005080144103c1010680d50640d1a4086941400042c800781408a04040d20783d0800200040c0780400c0100e4400c0f45040507170f80e814010108111403d9551058071590418003d418050f03801044a96100f03400032014400c0e05218030340c010009414410003400e02498881440621040c0c030302500240c140705002d4016000303044201030703681c0400c582c81d90f4001c1d2001409425244100040d100c0e650190602040d00414841c004a40448448514076030342d00b07043d2600141500d120300041100c4c1d2505002040d03406282c0324442d9000340f0701070016013030a01c0c01c42070308a460821603440215041003c0f0000742040c00303002501c2e0a040954401c2001803500491010464021214 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 802007167 1250 802005917 802005937
    0xf050d110604120b16141b060702030405030c1509060715021605010510030b060d260702010807051206120a14100b0109080322080d030603060c031b0809100f09110105 73
    0x11b40f25261546034001e0960000012002c80c0b140202c4241d0110000c0142c41d0041c60f068000d580c0b01c074100410305160203d1200d03003d12a020301100781504200707100407911500400c0c2c60b060742d190302504001400c03a091701100185207100083c4940304024541442c007845200710000d008588a040b6004004e203602d000190007140c02c2800724107580380c002d0b40c00c0c00d07051192003a80080c0f03031540391444e060f514030442050b00c001c0010b100030131980c0c130100f0158400c207582881401e00d2260114a602d80d1402031107113004908070215020000340030401d80c28a00d510a9450400c1002c1103045034940412003650f03040d80f401d0440409166004211140a6510120003981840fa003085103009840306100d1006003c6e02d1100042541403060220340291040c41d01c0100e41949145845012500c180c0400001c15150010204400450100c0761003543d04902d42800c0303648500000f141404004008032410602e031000e10280036041ea00190707034039030144800807040d190040c01507036a07100b842100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 802008417 1250 802007167 802007177
    0x1c1709030c1b0d060e030307080f0c0301050d020d02130603050106050a06020c0f010314040609030207051e0112112214210307120320040f050d110604120b16 69
    0x1d00c4101800005000d00b54000800564012642d5110f0200f200e40c103800f110920b4000001300012140c0061504d6044594911803481a1800c2010503500b804107026052203420180c80020a40d07035007030403428106030018107020000c0b0000f2002f80050620313100490700755081040000e06841c20710f4000b4101c81c2c1c250081c154102c0345404011310034400c282c40c103050654408514280c0d01c8003851951085229060009401c0200d04010389890704940c80b2920800b401e5252140348000400d40e034603a03034004c2c01d1120702c0d84810016100a050b240c3d0030380c20003400106000d0800c8040504050085003200d046040480d2959650320014050b0400b1503044007554090205000399400400c03010b580f0316056a042c0203160b5203050502502d0840740300043c0c0c40e4100c180400195604207900c0301070500c0c03158641450701e44424407130100d5115540c4680c3c4108408020310070041840b50382d15500030281950341c2d44400e500c8003501b400704419100310380040c0000702d000803a030529926000312601c41e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 802009667 1250 802008417 802008433
    0x30c0f030c0a08070515040f030806040618050403030e06310c0510110312010e090715120e0706030933020c3c160501111c1709030c 58
    0x10f400400e030320004046032188200910702c070880c942d0f030341c1b800d0280b84284240005030070349060003011001d0160100d40300313a207000810440082c0186020451000302d010108031a40c40741400e80003054075100025141c0192800c01c0b2921a502c00501070105081c040e10b25010701c0045000a0a1844800146404c448100078802442c012181088020241c980390000b03070001c5060b60300356000300341c0403c070008415005101d0110145071081d40094000e00801080d440c080c07002e905048403c080d20140702170640407400349016504207910045074030341203030723741035984800900600e070324007056600313420b2880c04a0303086c0c00311100c0851f41d9010f910752540c406d508040c528025440121500158801c00001609004051503514110100861241c1601a40c0b00429031541c001c98404c0086421240003011414141000501174502c00e00c2d00c1c0b582204a03240c80c0e0301e058610400f03002c41441c110031016a1652140c03020403102882402902c494503103203c015600d02400d6600e00c80754101401c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 802010917 1250 802009667 802009673
    0xa0320150105061c0f0915050f040615030c080d030c0c172a0f0c030f1507200705040f06060f230f03160804020109120201090b0309030c0f030c0a 64
    0x90000841d844d4140000d403620700402d1001c4402042c591080e06480b80c0190041c824011500c14502e0800c1209010502c1e14000b001b0090400030230080c2169a00c0066900440404e61403e001d5544544141c174510b8071005915502c94a0707078030100000b818001c4403c000ca1007442802e03501a072004034103030030000c02d400010b40e64101ea2000046400e16204074022844034003529203032008020043e040c0e41c40c208007001d00b004820301a942c040e512408020894040008648207a25404060000d45c2c3d158110101d0703039514400a030f401c01541031213580e9602503002c12807808407801100e040114580520100098800070720841d03000c6200707e6006444640185402d84102d401c1000006400d105000070000a4000e45020700c462240070003009001d08c0d99241c0d0604180075410180000d103401d50008240b0280ca0103064041d04044c08540c0442e4003480420026107000b01c074680c3c8030b03d084c0e10801c1d42d98210028145003482a407284100a04e008400c444183c0380c11000b52084101c952 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 802012167 1250 802010917 802010929
    0x1401060b121f26031e030c04050d140c100903030e1f170a0b0a17010e010606030b011b030905040b030a08030702031c0b01020c090411030a0320150105 66
    0xc0200d00040c40c1103074080c40580340804104040c01d9200740725401e2583c0342000800c010204540450154820006800e8072078140b400040d0001c4e0120a69650f681c3c0c0003c0c80602e4040c55000542003600580c1c101c00b08102100300c0f0000d01c4440040314007854072141040010800c0a200c00c0114001385002d201207441800b460142103009807001400414000b0911441035000101200103819140042070748280035075413503040000d01b0801c2c01081c800310000341640c040c1c1d00c00d4110424500c5040082480b007134000400c01c003901e070000c020310359170307000041c0190202452050000e4144044c1c890301901445c0803400c582e42682da00300c0903070704060a100c000c2c100741389444e074544640f00e00b0400040400d0015480350455078007840e2035800800d038241d6050808540c5468460802040b21407903640015441c021140c111480306441d211802c010380c070100014041501401086011001e1540100407030000301402e10715010401c40801e042034882e070582c0d21086584a82d0070040146150030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 802013417 1250 802012167 802012171
    0x403030c060b03013c0203010503191e06060e16021e03040b220515190905030607030b011b020d0206070320010b0a060804030206040201030504060b06040902071401060b12 75
    0x80c00000350058401401003091a00c0202420302d0074600e1789841c12040780741980070059400500650842d4100b0001980300c0041e01c03079240265200d081d400044c440c4502504040e400000104880c10381d81d410414048d00c464012600d90501c408042402c142e01500c6180c140f040c80e0b809046203c2100b4088035480341c005401c2c41052100740004135461001e070008050385001951003000355403007509841030300f0115074401481102084182c030b100700a05000c541d03c40031516000054900c0c0584140c2c0c88001c107401c030a400d40700e014100b000d02034042e0710a508642090300e8001603068907580b07412044008140080d041484942c1c50001410300070082c2980c10700c00d041000c1031074440307102c0307900044020002c0041c981d11482e003060241002c00140019100c1890000d400d498180c401950328040503000034101a0740d46c00141c00c0c400660300c00f81000318001d01099135103903103c94900c00382d040400e06441542e0340401c0c0c1c042555052282a0480d20b0358030480d4184054113440024400c40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 802014667 1250 802013417 802013419
    0x9110904020619021c0203030108012f030613290a0803090616021818013b030c100e030304050607050f210711011116240608120403030c060b 62
    0x5102e5001d8014440280701c01e16a8501c1c0d80115280c0d8581503005007907030b04203a05100ce111b5140e802421040040003008042c504c1d200c0300a07669201c82c00440d40d01c0c14541d000320000d516081d42e00038240010201454a00c02917010034507201c5601c0e0070001e2540701c61207455a644e104100c65840c504004000d440782c1d000410003402c1c18091a000324000403d603654040000c1c1d0300404001044907400c26111303180f00707040000c00000132a40d1038500240b999001080c0c1265481d071803170307602c0500c5030464440d82c800d07007042e40d07101c968241c14590395603802000740a40d0360900303044a240000000980340300d260070400402854a50039000c1d02d00794080c1c1c10f0701481c41c404200184c210318003038414604519102146e03030098501600d00802880800080004690424002c2280c003092541a685030301c20443c0c1c0001e400c035042c41c0000707001010740044059015429011800c449003540724a0850b41c004e4280c1e44161645100000b151007180402000300300310031800300214681c1d911500b00060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 802015917 1250 802014667 802014673
    0xe240d050108030c120909040212241519140a03050708070303080f151309210311040e1914130c060c0203100e070f06030911090402061902 61
    0x2a18040009031082604154125840000c010040030300411480d8080448050304504003441e07040041d81103076010b0006403146809918800e40100c0c00d2004a0800051100e50140c410b192040006441d00803100c0300544440c08000c881c9078144000d84140048036040102c241c1b90071701c007090200b00032040b401e03a009a14650003100054040108401920440c4010689a851841c0007401c651004150440513800202403203803140107158958484a001c42c0d0003600d00000307610100041c41ba50304081c148411110f010007a02088024958565440d560180715015581e00d020101b4810342c407605402c4c0d6410000503250b4450b500306003c0c1000d1852002c180c80c001c040c40d0400000c42900d0303026290381d1402c00081040034404034070300201000c2c03c0064000300d2070780009486245d400d8410680303d445040c610701194003484405c001c0d190142080308065141c100090040440781400c50360000084d0a100c0c061400b410028880da80c020501ea1401c1a00e140034144c91442c000e001c42944 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 802017167 1250 802015917 802015927
    0x310150c0308180102091008090d05070f14012909060a0305030a03020a0c0602030903270a030809120a0b090f1906020a2c090a060614032206020414010e24 68
    0x280d1620254070003146a0340c1c41d240e0300e09249c84041d0400e0290801c0c4018094200114400605d65010703110b6000d0300000c4a00c60b40304182d00107805481001401405800c40c0010505241042c429504069000f562003204070b6950341c00303020100c8440e010180c8941d0003400b8a0091030312a070000c0194410f1407502c4401c0d85900c0e41c90900381d0b041942e4840f01608003203164600c00701460802040d40a035007105401c24441c035008200c1c0c4050f9400702500d1943c0000e80485a5110100c1d601d100caa0035408441d052901e600304201e82d00b03c10384008509000322002414101c0000031070896510001580e59410111962218000d601011031001800754801c0b04a0200251140b442036a250315032004000702700d0102085101c0c03200a1050b50801e14210741403003203c0c5d0080e100b00e86d59010581d042c2d80e03a11855001c3c400e410000f4550110101103c4002d0304100094000d072044030400c1a800c004901040c0c010b440f06209640c07115000401c4407030701c0b02c4d4801030f00032010011410130032591a107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 802018417 1250 802017167 802017169
    0xf1209030b0f010905060f2d0d05150a09021c14061602010b09011211060f03010b0a031a03101505030102070809010801050105030135030310150c030818010209 70
    0x40c141102c1603480b020b815001002554501d014465001d2011600c08100a942000103039031412140c9208160954001d000c5030051643d0380121103030a40141454210708031460155070b20340b00f0304c400e070810300c03400c0000c0340c18a1070f94090805620341c002d18490384c54503101c0b00014003242d11501501e600081c2e03804203007021410300584d80505042c508208680d0a903400181c00d440790035100d280640c00342030040080070740c07035008050b44580c03214504a1800d0038100150042c06040440c10103034000100014450480f00e00030f2030310f41d8075034509100c50341c40f050004c21280080b00a00750107421130042034502c0710319035002001000041d42c4004005480d000440c1c22138108841c1100c003d800003d00c0841da6030010145401802d0910382240307590306152403c114034810740a07402c0300701300804062100400a10481559440c203400300c0f5140e190564280b801e00c5181d101e00040011017803d1151034510484040c0b01c140d40540b80c0720000d8590084800c5505404580450380395400e01c850f85c12 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 802019667 1250 802018417 802018433
    0xb06011b0f050606100e060705030c0601080109020103050f01060c0b2508010504060b04060f0c030c150219110c010c0204060b0a09030318060c060e0717030715090f120903 75
    0x40c0c0d034000da85020011a9524206160007005810140320b080c00215111905620482c80824800e003564815142c07100780c54003502d54000c01045103104c3c0500e40020488140560211800c1c50003664144046d88034201407001e008028014500040c00440031a0080740403a07108542103083c6104a05003000d12060700c0404410302d5041200141205d40100b040c3d1030a4090f840280c07802000240c60980b4004025214910441110050042c100c0d0104117143c001c0303681b000351907013007181c2003401599907241c800294000038050b000e405c00440e409a116101e640d03807200100502d0000c051100507070340191005200808126802910340780c010542d0140d0300098001141d1a0303c1d202c800c1170071482c0142030070f41d0200682408410000041010f154030100c81450715410810000f206186440501d0404c6407540140714420007280c424400c085000000301346d00c5010b0002021029407241051040d2406200c01030420900880103601050450481a00700700c800c0c1007010001e660703640d45102c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 802020917 1250 802019667 802019717
    0x41e02030a1a060909071b051002031905010f260a0503032a0d1112070f090608060901090c2a120f080c0a030225020f19030b0601 57
    0x7541c6900b6940700440e1050703015040c41e00300325025401d1a41050118070b5203000203011100700a01c4060400b800c0580c04038102c58140c0010558404951850f0400081d40c001e4520007428640000400c01100003840344505807400c10400300e11003884e050040180f59019000080d110b2414103051080100402110300c1c1ca43c41800a55103030f140c144940b040380065840480c0400c5400c4e42d10380703081c80d04a000c07115152411100003c140340c131481101c45500408003410f40c1d841e440000c0c000940d40142d09100c001205070348400c1d01ca80c03110000c49001806565141c0c0141e9035000501004100e5040000004018900f20084001d614541054a05269401c40041c1da03214018000d20514400c040071200f01401d00340200218004010b020030b00082c0588503202c2d0104040c145240300c0d4046990003e4207424150404c08001c4481007001d89408080340700711007050708513205003000003200b440701c551000801981869070321000c041800080c4402d04002c580c1b020100355001c0752071546 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 802022167 1250 802020917 802020931
    0xe1506012109210804021302070501090c0806100b0306060c0c0a0e090d050c0c1905060a020609060a050712050402040908040806061008191a0d0b33041e0203 69
    0x4a1801a18140b12080700c0d00183c0840e1512071003441c0192058000300000d820a906440074800300380da51200200030300031103000070010b50800d071190081c000410721940a0380d0703184c0706480c1e1507202c03424202200070f103911807030f1040750003880002d034203140005c05840103001e00300c25104d580c8400300001364044800e41000b8208141782062041c03502c0c040017080100c000b0fa040c11494040501d000c3d95481c2400e000389841004c0310b4005440000e0384504130801054043c01c6203490792030b101c10294881d031084070000e0040c0b06490001c1c0300142603010727160141015403944061443c01d804603101078007005000780c2c0c206803129409400200108010b000912200d405021107050100130010128205d0301c44008010a45003880000c000300740b141040c02d035194400188400d450503051698414520455510002c1c5281003014048000c9242d8420900e111a03582008822040d01b90703801707413520444500707441c5403d000342503090a0b80050b07004549118156170540f4001c2c0c03460b0903070384100da500e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 802023417 1250 802022167 802022171
    0xc120a0917010b0d020d060b030f010f0b0306010f031202191218180c02010902030f010501030308090a0308070305190c0e030c010908030f0f120906190e15060121 71
    0x4010031848078401c4a041c818040090001c040d41e540010b142d4040001c01920503600300c021340302004065449481e101d0005401d440344030f03020324484e50003003011801603010700c8e0404824001d2843c000c01c0c1c1c00d042c3c8000c0b8030408030007411901c45205200441d030500c410f502c0707030441c07110780360840c144201e00781031250401e0a0741c1c0d000c1010042002514201c072803464040e00074117000381c441810781d04174100d0356801c0000e40380d040600c049000d4610808042d4150085048140d085e41064220074140c5c3d000b031300c40954170b44411145a1b610752003054061300043d21000460074952080d000190458126021110450030400c5102c00311580f50035102e0201d00301c1c5400c0320050405006003418240d090814070620340c40e0080b481c0e200e1280b18031a04046d10000395414035005e540b41929081d2070a03260f00c0311149001d0301c04c9951030354207890000144007081403000b0f940c40c160040504848084000d440a8003c600380715440c0b04010f04076505000c0c1e030b0410340095802d8400e001203081546000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 802024667 1250 802023417 802023419
    0x30503040906090c021f1512060b010203120411010311030a0905060a0207020a05040c1704080706060506071101140405101706032116120f110303100b0c120a09 70
    0x210340110b822540c8152038950402d4200000301c0c0d004115030180d00080030100b01d40c4458072102030000c001140303580b0b080200e151b1000c0b038654030103101c5080c00c0c0d00c01c52040140048400041e070f41c038003d2080300c4510302da0250010b40005d242e00d13174810358210103040c0450004c0c0c0d100e80c9a80e00d500211011050150703102c40500a0003010085150030038244141145899450303000301e250701e11240075881c0590f881c0e50103040120300c03d404441041c0c040484014071414285401c02d45d6a22203c02921114100200810580703400000c84100662007102d0b07400d0340c01c42c0b20066941281e405023103401403506000000341610380170040c19507041c0907034500034803008244039040030581c007070038490033a40041100c0000f0000314001102000501c08004d4075880c0b4000c1043c04e6021303011004040b54907160621b01e0191f002207101c66041e04c103843c0c54041109460302c10360350740400c40d100e981088036241c00300a1074007943c0c01000c184010000303603080c060464002c00d80b164409001040004c1c803841e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 802025917 1250 802024667 802024679
    0x302160210171803120c0f0a050c100c09031112010213050306010e04021503190606080f07080c03150d062f0403112205010b03060f220e0f010603050304 67
    0x29455404502883c80d150101900285544d49000d01800010b400d10303d400480d8840c5010001c2c1d1b130001e501310044581c0c132503130780c04020500c0e0010380446400d8407800d64111107454803402107551107001c9564101c05245561121542d500003c82800c0d000800740747c400302d40e010b081c001803428080004480c40380c94a02130503d864010143c1c00000d0307019116082c4001665400e01080d4414110941540c40c4e071201004983e04043c1d60702d011001900c1e2581c0000c0ba69003044c10548140700c20340610420f583c4171203040c0e4042c10120743c0341c02015010800101c008134118805140810042c2c40305c4045486542c0d00030845d10000f100400d85410070704000c0c00c1c02c00240000080c0e84c906014a8100351940ea9030303026103c80d40c911207104289505220940d4032946204003040e0706403c8041c0308a507507840300c02c019940141d840c507000e0084410100c9950070306040107203120121079043c8044001c040d414200906032207031880070a000d44031810007264824014803010718018405181d80741d28141c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 802027167 1250 802025917 802025957
    0x60509070c2f0a081c050c070e0a060f050915060c01110f070210020a050a030f0c02060310140406030b15041e0e060f0103200102031c0504140106150302160210 70
    0x64044c04107944808410300305200c0b0030500344c9a20717513681400c03910762040300d1015041070709680114640c044036038100b18031107505800103000c503207103402842411600c407410700900840031240340b8501541c1c01e00021950600c0e000500c001d2000d5000011440f10703105411316542c2c4285030481e1468408110b113800d503e4420340c51201200207000814010320681e980f10303119407845030b0140a104100d00c030907c1e210f0148501e805560360052000d40d8a2414510040075400c40d401844114500e551700c841140c01c0c0fa10844d400d1300d4109000d00c1c00e030b07030307440c5400341d0181d9a10540c40c0c0c0043c2c440c161007004048003c46001450744611000c140c04201d80c036128a0004000c0488542901c2140100b012a020903100120000324440310701d011b128550050f482c42c4128a40412840050341c000a2176845550056000d1842071800e600e201110600c2a0300b660aa07016204000c02c6220300b11030803a010348c1c0140480e03210103080440c0010140c0018103001d00031510348010503002c5820760340c030007004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 802028417 1250 802027167 802027169
    0x260c011109040c02151303090e07081006080106050711030f030c0a03080a0605130e0a0227131a04030c05030f040315050408180a03020901060509010f03060509070c2f0a 74
    0x191000300010f903080450880070170710190005442c100b00c0380c008001d05119075554030240601c603003c140f150401090007013070b01030205c50152643c1c01840300406c0c1d00388034408a50407038010b40e407001d04181c203540340d41c61611002c44403661305200301c00034103131500818130140c03009030740240c050000d10000c0c1c03c015010781401003510b42060720301032080c0581d5545400c04910060b640c0c0d8000740031040c0b40300750340c81c180070524041d611841c401100d4440e900344890b5104025808407e542c41612030b403005005000500c0c1d070040003507004440010313150403403010656105000303141111948245407900b81c11a40070342c14009200d40001014028802460b9022550a0b00f0400420441ca41622200040d0050007010900d041d50343c1400720355a07554002c1900956001881004556500c550203032444c0e100401150100d0280c44905480c2c6000344507150840e0f00c040c3c5002402e50b1140b5085840d2849030b18101d82003000d1125220103840301c1a460007001181031042000e003001101082000c80032 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 802029667 1250 802028417 802028441
    0x503072006040c1719030e0f09090309010f0e030d0f09090c080105011b0c05060904020708040b09030d1805010f03060305060a150b0708070f0507030213090605060d260c01110904 78
    0x1c50240f40d105c0305c4180301c480c0b895641510b00b100f80c1c0000080010342400d01e04e920258404003500034804840d10110007040e1081090303c580c201c01004403130a46100703035040301342640340e001881300c44546c901500300e803107090b011450b204c91126154020071048481c00c955000c000748607840140401d50b0426003004244080506102035441503035a140301203c2ca83c02558000c074404103030908035444036016a440b030340e4843d05c220b4441e81c840050f40000d40014a11510910520502c0c3c041a8015010424400400c000d24625941004015612401210072a0041603a54203000000c60010720840b40a14a803050104040c03c0c500ca04e4200c10103250440c02d001e4108100d10fa002810322012070310480c1d408035100a40364150700b0b020341450100e13400030750010403400b440f50303410303001d40e0200c44000d220319410440d0b62070301400e1000c49400850002d02c1c4510f180500380c00e00125034008000320040300ca480b89001603c1d4015401c1d1202904140d01c131081c0071444991a02c1c4c540103c01520302 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 802030917 1250 802029667 802029673
    0x40807050a081c030b030d1806210b0105070c1202010e010302040b09010804170310030605010f061d03010b03010c020d03110f03060613120b0a1b0503072006040c17 72
    0x104000c00740380c40e6844092421801c8400f80c0b040c1010340d0103a0030031002c1d410020306a43d0030004241d4042c2001000003400e0b850201c1880c40403903c4c0740181081c0d0703446030b180442c681e070f104071003801500141074681740d003410b00a051007080f00248a225034607002c0c10340c40a51000d4215940300141c00702d8401d1500d1410305005010a01205003c6030640c0c41e00790091a003091a40ca450600070300f403600300c44007400c07420f800004114103043c04e0a2140e0440741b055604009903070341e42c101c450282c90a4050740d0006003803040c0743c1d80820b501c000225043e80d40240001204041c40c7c0009085803e94190007000d60460311f1b00f501210741512614550081e03030b01c0d18038540030280c0b0802d0384078440109464852403000c20411850300f40d01d4a030310040d0445440d01140120541031202c01d004045503811700ea5400c0c1400d0440440b0030b803100300c990384035545915003180c440000a8440c454000301c441c0e241c45058418106000c0204207071030056000380001510b843c1460140c0904144248500046074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 802032167 1250 802030917 802030919
    0x30f010b031b010e03070324090b010603090311010c08090f01020301050d03110f0f0a2901060302090f03030313120c0f0f0816033b0423040305040807050a 68
    0x1d1000701c0d00b60036280307410342d0700d12030b4580850050b6021010f041e400303901482490300c00b004101584116481d41c1031600407110048a07161104416202d148000915504d800c1c80104021402504010003181c400c2c2003401944d1400546503003110450201540010001c00920020000034840c06071450030300320082d89550305041c00f18445041c481c00c02001c02c404030940c3c403500c100600c50341c0e07030445140003690700a45145d20300d541d0390440c50400f55172204c10041c894038042e01d200840c0c144004241d40e688042ea10f440e20a50080d0840609140c010110203441c003140e603401d100640c400d10454603000c003000c1c414100f0012035401192408140a0491288030200d80c0300b40ca41c19130150f01c40d001000b0003805140480240c000c0306841105c2e0705000303800404060300a83c4070b0003441d452203200f01c45076044900468018261141800d41084018441c440301d0a264104844400c403009109425418010507a04960720869003500090000325060144d200103100120003010101ca50b08455 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 802033417 1250 802032167 802032169
    0x100b0a09060e010b09190314100203011409150604061d0d0f06020f190e090f0601090603151e0e01120b1306061e0f0e04050a080a0e0a14030f010b 64
    0x507018084c41c0703800003001c502203802d075a40700030088418904040c0740c55882d54914004075030a2101206802c14010011505020015071081d01d0480300d60110783e14a042901060103240a006000207850703000d01c038004e01c070381c0c1c032490003c1005050315070b91102c02e201ea00003140701201300400d940b48690b20510300000850b240d218175024440e000703e4010b90320355a01e420086144030703d40c0b245d400304000c031054040d281d0b00324a862444140c103580362245980c4102c140d604940c07040360564042071700a8014824a846507200800703888a01c400f0101e5540c81e0169558000304000390903d030f0744450360050003120500c03120280109030300b004050368580541c0e50030b101a41c004080d161540407a0341d149060241c580c00c94001808402c0d010b2000100d40c0c40090040300050085409540d054940003440c14180e84080384500d80010140084200550360303041c01d503000c40c40f280100081d00c0700d00da015982e16101c0400418105c0740300c030601514101410b081580c0c0e00c52000e5640d240440344066 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 802034667 1250 802033417 802033439
    0x605030a050a0206030705040312051207020120070201050c1b120105100e13120809210a2102030a0606030c0206060d0204180803090f011401060f0302031008100b0a0906 74
    0x40342d040300e60f26101d0383c5002088a0034000c552015280c070700c402b100004420340003070040c8041400d58003402119030303442e5026426101d10141035500e00182d1f070860b40e110705602014114003841407404038600780c07140e40b1007447c4ca9054ac058074100b039028160100a80b800707881040d040d100c02130003400285822100a407035205140b04030001010290f001a2604200708910b1007082ea00c1881c0050404240e44014481401225000b0042c45500030072070001c040400d99600c124800020145802e140031412903108009000062103810054105100e08950780003171807040c1e980d80b400017105454820b0040c203540750030440c4419500700005012075511002c2003291010f80585002c1140b070b140b480701400c43e01910354007600400011080c0321002c000451403180c01480f40b0004d100d590400104950501805c0c8034100110b00180c511414007402a0007a591100880c03400340202c0d07990b10740c92820301032440524142c00380d4581e0031502c0d43c17409150301409890500c1e4100075807420241c01c800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 802035917 1250 802034667 802034683
    0x316030314071e0302060f060303360d030c150203090309041e02040f08010e07150807020a020603010b030f090f0a0318050a080f0114060a21120e040605030a05 70
    0xc5501c40040e040d4140403803441504484014110700014071105824025100e540075603284510b81c030b4100104503549000030039180900640818145408012440e080605d8081c5070568a2002e11a0f402800e0b03030754280343e80d814180251124058895113103803d680240b845283c0356061841030050161920001013500d070000c0c1d0039680000d0752110081011114040a00700754401400054007141d4010520b40d1039003141c182d41c0081c0300540c0035201d81d0351101d05900030584000e840070078402510703105034503c035005001030040c0c8090610359000304280342d000341c110421142c400000d100144d03858910050b4810030b100043d25141c40b40032904c50f2103039075812010f0200000000264040303200d1002817801000020400d4420a50b100c0015890f47c404c6028020154a004158201e481010519034441c07000208030a000e6414003d658004c074000201c0c05600080078180d001c001020220412414901922500d072442e41040400c81a04c0850300304d1b6019070050307003407040000c1001070340e41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 802037167 1250 802035917 802035947
    0x40b01030206070204061e1a070b130c031a06090610050409090c0b19022109060a111b030c030a050a06180c09050109230c1803030c0c03160303 63
    0x1039540c0c0e0140001307006000181c0002124547c800d580d000c40c0b0503040200421200c0c002140040700301604001c9040c0e000c3c518000d81030000960000d829002010050392009209224050400340c81e43c42c1c0300403c0303007581c7c0010410f11000c028071450703107020403181d580000b045445004046000c00000e05500a500c1070700303d000d40715000c0c903041203c6944108041e10030b024082c0d0310b41460080e828000250250410090300034070008075010706c40000202e1a5a802c4011549006c0404017402a1a8445002c035401c202000d10808602d05040c014190002da1752040c001041900204041c200b96108181320300c6940060b050100049000c41c8880000360040000039200110802100e13078000800c0340180f81f12180b010103e411010390340050b06072074500c10100005820514013404c41c01c1804007141462090100040b551030b4520300410540c0e041044442c441d0a00e600400e180d80c02000009001e6089001c0b03451290a04000c0d2101e03040454950f01e51803445c5032006841100d64120f44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 802038417 1250 802037167 802037179
    0x1050709051005071407030c080f030a050a030e0613020405092e240303090b03040f060519020403111f05040626070519051801030209130207030c03080f040b010302 72
    0x104540318003400a5950850f08070b0a200c40100070029510b48400d0300f80405c03a648c1070724140208100b00001074200b00fa0780c000c00210300d09007070040c050315141c111049035020180c440c1ca14440503d4240143e50007030000340c1c40b00f00901c15910410080c0d0308000c0140c10701750712058000305035941c1c4025018440420b41b0280b10309100044025014201c581d000100400c1c4c940344003001e0100303244c911002c80340280c1d2400744082d1684a107400610041d1006001c3c007201100f01000b1070115131109401580d003c030030405140b4480b045800381d0300a58002e60748410a09009001c07414035600c1500c2544c00d40c03050340e28910f040c9801a0481c0a180103140403c8038940c5166101883c00a40041840220415060381d181c080c0c0010195030080f1006814000c1d0720b403014038244e01503001d6600b5642d151061035030b624558030044000f5003003d1441640841242031181e0841158402001c05500a41c1d40040503810750602a00d014006850070012003074050411010440300e03007540741503d60448031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 802039667 1250 802038417 802038439
    0x3030309060e0a05030a0801060206070c0201110c0306191103010f180e100605100212040b130b040e010302010206180c0909010207141f1b05090105040902030a090b06030105070905 79
    0x180000c101d10b0200071260f1041d8a003031014440c000011b011260711980d9408034681c5c07a540308a13101d490075121480828621281e0300700560160260703001a9124208a513046108034002a29100e42075070001d942240d92000d4041c0220203016490000b1000300806103154035105020031101317194880c0c0d03034900d103074054000300321a0b468020240d1301c00c503641212061000d1005640c014486841014410130400c084404118004550903411a00b05145070313042c1407405005444560200b01d1740c045048140301e0215007001c0c0d031409040503280c043d109020540c11440064540000130f000d5a480c200880300914007110000349a0030a480c0a44030304106071a48140719002e4060200d0041400141030704160303281c14000b400300d418880c02682d5001032000e4207050011540400803020286544019076180d190169006003e155011b1401620341035a6440f00b40232600103035248400c007078403000d0300c2042c0100410000d4000504030b00070070807800d00642c0500456201d00c46c540c081d10903144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 802040917 1250 802039667 802039673
    0x90a06030b1c060506090901361a180613020411120f07020c042f040f08030a030501060518101214041506050a0b0304022413060e01050403030309 64
    0x1542e440d04848252034484000880c0340c00c4000c0c0c034080391060b0050f048200001e206520500420f040014000110501150400303410100446d14444031a49854a002848002219500c2d02c0115154030003000340c16040c90310368698800701d4010750354000c4c0d10010601841001c02103103140000d40c102d400154881750281c0e0b040c2103000382d03001c0180307440400040259545400d442544101055829180311032a40810070040f5040ca14400303c24640465107040d0729400c90a08210030300308221242d04040d82c031600300499088a03044060b49070404114130f00c0180d01b40c091280503205600748142400712601e80611944207000b0460700c2803001c00c84041c0a103016894a064815004d80c091204001645d05a01c0543c015138044404401c08070841c051440d09106032000c2e68001003074200c207030b4a003008030f09558201510680c2d00815061400c490788c1e00315007003040041d082900e815110000b110042d801900d45620a605001c4241d00b03500d0103a9104048030709a9503d0f085c001821030481c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 802042167 1250 802040917 802040929
    0xc030b031f0b09072d050d05040203010902060c0f060108060c07120c060213030309050f03060708091903090503060a0903020303060d17030f0f011e09020304110a0e1605090a06030b 79
    0x1001c1d9a000f180400520080e030b0f40c0008916606891040e41014940d031a8080782540e41c401d0a0110004209100040341c1702d00d2504140d401600080c00854240d00c59000a5600d51003400070071580d900035544031584000520040d4010304040001d0b00407442c1c5106070200500c80d01c03500803c0c04101c494110b585500030b1503004000c0740c0140b130454646a15803001030550020340800ea005c03031802040025540790102c03510403100c40141c050110ba403503105054403a10006040c00d980c90044030543c03001344414401c0507034024020f030b0314545403511740700505082c600081c000380301050410f4190804030340c0001c101c0c3d0700124141c0d00c0440e480d905003041c880340310764885a0361114800000340181860080800c5005900070600540b45036030f2014282d406804030000404010b038040c6040240d107002e039020310b6215008a0380041e80c81c80e40b0300001c682384040e17004001405640010f00c01032030988102040b0751b2800f4100b081c078141402001a1801c08503102e580101a1501800c0f88151918 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 802043417 1250 802042167 802042181
    0x3030c07051906061802070c05040c020a060f0209011106040b04020927060a180c03020907260106031a01170705070804150e0105030f06010c05031b0c040c030b031f 72
    0xb011100e01008503890904040c15082c8103100d451007481d810000700003814401c6400c5580c1c40803c14806074505001c3c0005007802034003d6055010b0070a07400041411802503045251210000603075640c17600d40090032070300745070322b2405090348004200f0000845646045401640460340250a55100d102c1c40018110810000b09500c14083c100e0045240000e40a800744100d100300303000b00c504803084000110700c496000340c002140100108003606080b50b0068002ca03103440c0c0300d901e909884460280380071101a80e0515500d0b400c0041040702e0789071254004507071041e640041d1500303c00380000e1041c2503111640c1c0884010744041075040e402402203072184c55114503041d403515500c0c03800386510104440e03000d020030011518044c05612800450744104040746140a02d0f850749801107802036000e2404549a01c010040000130703c0d4900f84402d810380b40c5074000d0904c98003040c02e04c01030303c4000c1000020305050103040400c0c4c0d540810080350078090502c24030001040d90081d2400703003141c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 802044667 1250 802043417 802043443
    0x20616020303041d010f051f120b1002060a0b04051302041116050f060106020706092c010f060e150a1107050406030809011806051b071a091008060303030c0705 70
    0x2004042504020513500c024100c0b5503071015804080e0380c2d0f2090002065102410f2040035903054a40c82946000d0509102440e4003400005074102601001c1000c0401c8459414050380c0140b04200081c640360160f401002001c1e0340c00d0015043c140887d00c0120003500009114070745480e070a94440081d401070725100c0600c0d07290032200c5000b50404503118402e9400c48072031802280008030b000c500020310441110107555560382e00324074160200300454540f10740e021505809a040c0f4448001c21242c4034041e100804551000501c1d2080190500303d280c004e0902604000c890a048401c0c06019071395182e40750f003008881d603141c1d01c0140b82010340d6500200c1e4010302e0070402105000070100501004c600130380f0313001d200314124030b10265599118420140060703401c02000c03032004480c400c0e030218002e41c1400ca5040944800d03042221092a0105c19008100882d00d424180f50175402922090780b181801c030301a0814401281d00d0780700017411007050250005c6c6103000c02000b0003000080c004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 802045917 1250 802044667 802044689
    0x61a070305070b0c04030311160311190b0a18080a03081e0403080a0c321e0a02070e0906040807020619030e0606040c02060f0c0f030103030909050c0702061602030304 73
    0x252580749413015800070300081d03001803005500300500c07090024040d05c4900c000740c0e0a000542c6150f5410744007c01c082880c540000d090f0b000b1101602d503010301b1401911140017040c0c0c42d88035240d4000d10010400402100ca03064000080050060114401c8520b0703416281c0fa007299903c117550002550002c09a800c0030b172204204010030f050780001c80310300403c180301e014001110b4102d41203458031a2a2049100c25210b014011041412180c1c035543c00e8408100f1a030510703071280f486810303660802c500e240c1d041100280c440310305030f41848140054904140094000d0420704a08e5944040003480104500d0b8002001c0007555186e0782900c4414200e04100c0e02c0958181e54028043e02e8050344800701c9115010124802e8a0a4050201c1e030319403d500400d11565980d80b400e40b1500080e1800a50031400c00001d0042d501040c011400303180a40c54429100c0e240101c60821520300420003a00c07840240440401607448000b00ca070501d006001200c0c003016070340006415480f4131303444480c0f484 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 802047167 1250 802045917 802045921
    0x2107111603021305040503030a09140d08090d0c0b070e0103140106030b012312040c0f031406010e10030807020a0905010f030c0905090c01050c1915050901061a070305070b 75
    0x2201092100094034420f840a4500d03d901e198400203035181510010072580080c0001090716001d5844101800e001e000440b5a100d107240e122401d20310300040c03c0000950b0801000050300c420007202c4016645480c000c01b0f65070394bd4403440d80781c05001e4081400c02034a00c2c110b01d1640e101e604010701c11030303410080800a580d42c9030068001d00d4001640d9010901d011030030116101c1c02c9400c5040595054151460003a080340240080000200103c8000742d00345800f182482682040201441c0320780509441860441541c0c0d1925105a00150307036440c2542c2004903440351003104008907940010320a884920602c0042c241c0c040039000905030760f1802d0000244521040201000c40703009038401001d040d01e58100d48285d0708110740381d28980e40481e0f020213946d4410002006850450025035040d00310301c164100015500c00e0702030744d9408a19200584080c454800c40342c104102500070005e003032500c0d481c00c00302510032a02e1006040d0120b000d01c1030501403811500c51582c8804240594 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 802048417 1250 802047167 802047193
    0xe25120c0503060f0109202208070e07140721020a050114150312040e060a080a05010209180709050105030709080729030c180402070f03020c0114210711 67
    0x242c00740304104001c0e0030071003030240003210390040d43e410100c1044542e1606511540700c04036689207000300200352544800001c0d168404ac4400c2c0060031000c0aa00d0050400c86c2e001091034005454050314540c0c208640d000161165041c142c0d180d420781082d08144c0310703441041c2d080240341400030b0000d5007449051042004100b2040b80710300b107207868129941d008d0005169550000680844060408200a101b100b0804440552000006014040380c40e1900802418148202000c40d0355039004a0220007a10301540c81c11346114200711043c42a1800c9100285a80098800c041c103100000008c14001c1c2e200f90720f8200a4100542168601a44e070f031901040c50300071044407600544a80a040c1c030080d91481240c0c01034009a50090604034000c60f2200f00a410240c0700c1c0d4015030030040c903800200c0940140132420f020350058448503540b10f001401c401e40300d401c1c1c030382000300401c4040c01144100c2c52101e1800c04440400010b03507180c81042e00e40904d5003004c001039102e010385039151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 802049667 1250 802048417 802048441
    0x102120106020d030c14030402040b27060d030f031e14090111040501020a1b05130e0d23030a1416020106081207080702010e06030a0e25120c050306 65
    0x40711400d41c00c0325505885a1011001c45000c4140080028a4428001c0729544800d000d1a0010300003000040c003550700b1000145d00c00b0518280600300400010310014034070250702040d03802002922000540c0e07100d42d81c024001c43c01003a00c0403d055076800c0da2440ca401c108aa03e121410740300d000c100d42c204669200c080200100c64000b035541c02d107800c80c001c040100307081d07904680c0c06030010f1401400594440414043c0c03505a41181003008100190303d0351402401000d64114841c0096880302d0340c441c880c01e25020300300310800c0c0203000a40c0d003150720b04440c13401c1091201440c490b440c0e072a103914080c054404144a41c40001000d41404910900141d6800819403590002c02c11301c2d0303640300c84079102c55156011010b201c03024070500c008a00144010002c6600c1450300941003849003000800540066610503e07440c0d030b5800e070702c100c04000c000d030403800c2203070198407017550f450230784001040303403c03400341e11074540010302c0000421010f14400c0000c1d1030020140d5000f803411003030000b1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 802050917 1250 802049667 802049669
    0x918170705100605030601030308090a080307030516090501050a2f151e06060a020c19080106060905060702240309010504020f0906150901050f07050109060606091409040305090301021201 82
    0x900b8061046001d24000c05442120100d030f01c0079016201d03c2e841c40d01c068402c204000d200300110700031f564008000881c1030006510807505074030b0015007801c01c204207100d2801000302000501c0b0f0400028483e0740c0c1c0103000d03a02800b00d10b203400500e52254101c0d005800000403642440940006034200040201040d02200d108191050010356500c0112540d40e0040003440b00780d42c00182c0000c50164200780b40100481c0c1c0090044510720303007100f4082680541e1505900c03146c2a071001080c0f040c0704081c080da0004000768600442075605110000d9000c3c0b144800003442000060001c2c42030804201e0300c1c10018580400250322442d128074460b01030401118103d204021009401413280f400301006e90007118041c11080303818480e100700c085164040007005040c42400e0088105c28000c0b10b004100207485400040707844a95460b00c08251a811380120041c4000035506111031000d8840304810032508580b4050780d03849505040c1c1d01d0340303d110011501035000140011040f51042c01440c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 802052167 1250 802050917 802050923
    0xf581409012003040c140d05060f01062003090d030e0d11090f130f060e0a031706150a0503040c0f030609030e03030315010c29010e10050a09181707 65
    0x4486030b00901e94603180e910003200d00500c9068210b40c28800c9540340a0007645010380644920400e908580701c05150810403110158100399860050040c03503032200803515a06044500441d019544240e459224007840c04980e00503030340060300f07009052081c8111a00c0c88400b91101c00b410b442d6003002e0440403000389610340901285004240420304180b4558412005520145103160403030741c03412010808010181d80e816191092000c03240420300603090500c0c829140c000040d50030005d01010104000c10141c41114108003000001d10442c040711244000b52810950300d41c1c480c5402508121260001c80c1c203022a20304c0842084083d501c1420711300d000c3c1d00c80880d01c1b91414109582d030300c02210807060900d101242c44060754002c10b040c01d07401d0304c5480a251031304d66101d4540f8240101080c4407200c0315800303004025103290141000d4000090901054145042201181408090f80302e450b075400c7d0b448550070b031103242c0c00545030782e450303480040c141c00c443c0006442c2c0f44540002c0415 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 802053417 1250 802052167 802052201
    0x2150a050705070e040b0708190203010803070201121418030f0d0f050a09170c01020d05070f140304050604030e010e03010c050307020c1804060b060f58140901 70
    0x4c9109070091100038030a590080800116070784504c0200c44546018060150904d1a4014014606910700285020f0030184004580f2201c83e400010441071480080100c21841c2070b0100e0506004940c0c0c995220309071807030000c228a40540c5e680d10710f11070344828100040c004205040d90901d281c00588101d05817440030b10036510b4403407642003100c4107102c00078039080d1604031115502207141c01500321140c0000005080005a4040f541640d404640f03030800122860074031101103400903408114174224070400f81c02c40c5001e90360700340e41d00d601074005010702c06180c40e103000907032058004240602d000b80007400071012810003d0025001680c14101602500d0050811402d200c03400a901c00501031040049456503103e4900416500314402e400600411200360102d540000070509c02054100ea801d4010350300e06101d11081c00c0050840c4012017920f4070b89036040101d0018002000a62003000c5100320490890000b002c2941c40f9285140c208420401c40603410b5008d409d82c1003c1103a8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 802054667 1250 802053417 802053419
    0x108042109170c0f01110c041401170d171003080d090b06031219030207020613091407050a080601021e030309071a032409010e04021008100e0402150a05070507 70
    0x1039644801a1403905030300300c0181a00300a0715031041b1820344805440c80241c420b203013200d4001c64191001c0c15129811f510a40f0010041d0306106c8480a0740740814201501e281500c2c000001d00c408550090b038400c01e030044020690700070091484000441e440141030342c5e9910600442e00141c001880240c8031030219000045540c20081201c50150240c50400d9140c00402205824109007486440040550038441c060046e1142e0008000c118030f1490799640c01c03840c0038084819610b0f403000282c1c602c0001024400d1094100e420f07141174035170340e0416100903510140101e2038040c000e1600f0380768484132180352034480b00110013140186482c07030580b40c1650300e80380000001034440c040b00790342c0001000081c4810405203151150216000e070403440366180400080c0da015000c1c0c202d040c0c0040f0190500003146410503404c40354180c68108640b003403a2881c001c8600c0721481c0f10319203d06001800140c1159601e00300b9426610310140195214a03122200a000d5042140c0481c0c1030320030094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 802055917 1250 802054667 802054709
    0xe1311121e011112091509100b0102150402060d110a03020a020c062110080706031a010905090112031101020a02060609090703170d23100905040c03020108042109 71
    0x48681411440e5442403805900001c6030040113801041020503004414101c0c5a0840441c401c2d80120f120200400c88510003806d01c00c200c601848019055500000e001c00c01c603200908040d41c07142d012140b40e42c0760f09802c600c2c040a0720314400140300700d040001d0042406901035000d0f100c0040319500322030500f050304061141c14482c05030030034004020300e05050401491140d95592101e0601d80e01540940e56600312450318281d5041784010036180c1114032910b20380410004040e00d02460081c9031a440d04000c201c3d80070f81070055186400038090a1018903004075003000000794044002c5540701d000c940d0080d144d21307040d10a40d01c92014a0b021070008000040c0705019242c00290342848030300313039418080c01680110012240251034040041c51010709902d01145400500080602c03850141140e0655004941048110518020503c004a440311504405990317080c00e10b0359942d1210f007013800c40c509180a110040c1008032214000682d0301500d002e0884216161141400340184 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 802057167 1250 802055917 802055921
    0x100c050d111e0a0605060d120f030b010804030909020a0e0a0b03100b030c030f150301090605061c030210150f060915050a08270d030b13060e1311121e01 67
    0xb1011102c00d030310104035440807951640c040d5420034001400516014803d984500c0ca8900392840c400c046003a8003070107202c2d02d405005800e03801c8801d10f07081c00303503117003d6038050f02004036405441942075003c100801054000c5040d07030320000c0300604075002c480c9c2d00ca200c56100e500c21a00f10000c11200e4800080040d40d00060f60b0040000940c0541503988400340c800d00007c00070301038038111f1203100d80c100c0252000c2c480c04540074014072000c60350345003240c00e20036544e041400a4194180500411000c01e6003c120301451080c100b00c04508081000700e018480381150300016000c81000d02d000502c65085030b510b000701c554048400e062020000760540d454001d030400c400200e00060002564581034080c11080c82400600c44110f0444041400f49000b454042642c04039980f002424070914200c03000c09010449500184031050525400b604461005000c3c2103a1b4000e0240c0c140400039501803d0940c0c02d0090503213511300781c40041090751000c40c040c01880000c0040314280d001c003418 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 802058417 1250 802057167 802057213
    0x30904060605040e16020a060504060b040506120a170702060c1c03090c2c0106020a032019080c0604080424020303010b07020a1a03010e0a0507020c100c050d11 70
    0xd004c020074950307854040e031402981c01207540045005204040d070004c0d15a2260b180164014400003c00c0030103c001d1204075800501824801d40c05125260100740b0006003400b580f660140c4401d01c40c0b100000c13085c6150140b038800030340c410300c081200d100d82c1030001601e50514070011201d4040c0100d00b502681110a82c40d0044c4c02800340240034811509000c00f030202504130703084124a07409968104121f140000c1c0c20250058103d61036860505512180c000066100b1600c0c82a0520824002940d01d40d0b065a034103070309100c0d2040705001c0c480100140c0d011820304405070b40380c518044c6810415070707100303000310a291148180d83c0c408030050041519585c05050b001545503034208602000b0741c2e003010908a80c4044903a0012481030008000350004050541c0256142c1d414001d0040b440440141441c05041c9000300700040240d0000e541080140c013990316190518203d40d044550f080390300805880352144e2011041409c0e40890010113489400c0103845001a0a0303401079015211 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 802059667 1250 802058417 802058429
    0xc031d010905071418041a040606060e03031303060e150403200d1d0d051209011e0c02060a050426010b010203040e01090b06131202040f05040305030a270503090406060504 75
    0x3800c81404e02442069000e0781d0091f01030602c800c02101a102034030641c0104603800c0301c1d010f440e0541040b407640c00464030312141504074051420030030410000940c0500e1480060000764a0b105016031101d4140503041008041d500c15000320f15107070030040c0950b440c03008185641030b240c80c030302ca0801002146000402d074050b514032070010310b02005012107003038900a40394419402507104000600401c030110400c14007156154441d503012001500d9943c414040b01e030450440155501c81c9a031024158801d654100e03852750b00c6401d01310f0100e030240500d4000700c601410180c0d1007078110000401006101002000910040301e403140126241c2c0218070440060740d0704c0000500c1040707402c2c9c01c0036110807000b825140c20250140e00400e0719000c25402000d034003007003190610544c1042d0140c000040b20259044c001c5c0d0503c0d40d0001c00c1c030b07c40100070401c01980e9000d105010004000390300311108000d89445071b07059240c02e005880780e005550151240f8900100001c99034000c03810b903412144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 802060917 1250 802059667 802059679
    0x90501020607211d0c040204080316080706050a09020a2421110703030f05070512040c08160e0a05010620070302150d0e07050f01030c031d0109050714 66
    0x4510b01c0035144402e0480740c1a440c1038000d451407039010070078810314080d000892407030001e601502c8100340c01d00c0d0764040c041c0d00480c010003092120b401c002089404840e44661500e0031a503032414050a07500819400902c80ca041c10207010100e01300d80c100d2500140200c502015096403411524054680040400c8610000c00700c0505c50303074052000b89620600e841c00c504a03601c240b02d0140c01715800341e00000001000800d02c841071551600c24a1515075090300704003d90f090800303000d4003d000d07502c603030038101801d140068100701c00c4119240040c502e4504503190034040a55594080c005402810b580c2641e00b400112201050301036181219581d0322160503200d20400000000004800d5118161044003800001038071200c080100b03c0503c40401d6031115060906c04098a04480214109510520301800141d0395402c040c09010001d090008034414000d038160040d15900384440d180c40703903c0c075158540e8141908078104a40c850000c1ea902c03582c0700c2244034000c8a0440800341c00034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 802062167 1250 802060917 802060921
    0x91a090610140403150e06070504080c0d11030607050406020c01090e060f0303311403060a050615030901020a1704110d1713140a14040902120d030b100905010206 71
    0x141c003a5201d1040c2c01d8540010b10b107015100d494102900a1800380c03081c40701c1d038440c110303803000205001c0260440b481d403030100e24051410b40c1c2155a0b0451001c100d1040e0626503c60080082501040041120281c162103441c81e241c00003a140b9042032141030054092000c41c8150366100381182d2080e10b040c070b0041520790300e03000140200c19420070703050340d054801002400c01c00d00e03410711801c08015116810300f5040d401c280701c901d5103c00030382c00f0070140140380308011140d58000c5412640140720800000d0305541e0f40d00040c006801c00c800c03940c003446c0d000080c0081c80318190002c0407010782d075898a143d074104600400c00c0c1c020080320054200254042800400d10304010001d03051030007064451003a40446440740d80d00c0d0321142038448a4131019808004014480461200e1443e04a40001c0d00f14900401c0c00c41003001c1c01c01c0309100d07070741d26141d9200b1555515503214142f401e44080b00c50036040b40744090000c01600f114184249a0645103082079403040d400f25043c1d9406a001d45226 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 802063417 1250 802062167 802062199
    0x31a21060a09020607060b1c0f030909020301081507140a09141f0309061d060406050703020c030403060e010f150311031f020705010b12010204061107030c1a1201091a0906 75
    0x521003047c00302e601c40908101e904501008400c04800b06000c2c4040c0116060300c5e03d4054484910356011100250050004000f03041000c50a148400da1120701c45005680d80c0d0402c80700c1c149281d440d0041001d011a9003da0258440c0c002010303500346031548004d184900c4200004000d6482c49845442c2c1d03400f0100641c01d100780c00c6842c0043c0300301c0c0041140000656404000d55100500c058141e01c68000c00040c000309001e91070b0440c40b1810110310340b045c95040148c59120794080604040d8070386003c91601c060035805000c040c1c4c506e130720130080c038031403400f010800c0c4040740310541d8580f2116407088200d290214516600007107031031001c0b200002c01c0c68a038010350466002500e0365541d44444440986650200c0740c032400303d200c001655035040050140001d40250656001684082010310024001c1c0c101780007603950000344031802151303412201c4c600c1e10900c1194404031550780b000003032590031604494000f890802d50043d420102c0703414030506e608100ca4140d806090310500200c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 802064667 1250 802063417 802063421
    0x90906050d05061f030c030305090108160e0120030a080717060d112d03010f050603030f032a09010306140906040e0a1a0f010b0a0f031a21060a0902060706 68
    0x8110a0b0301118813910b50f40351107241450055600c10740100e14001001000340d039002c0c00d91170303101091000d841d0140c0700260008040e5140c0c0744ca060705100c042c8840701043c03e540d420412410070400d003100d80c0c80c02881d500812240050362408041003840000707020140385440f03043c0c4a484094030311001240345445004c0c81031200070b4403d03000700d9006c4c0c56450031400c0414001444005907412740c501d46468061508441c1020960110b8502e4001806a135580200880d13040098801209071245c0761111007080c2d1202c1204180d003211f409525049400352184050322441100b40c0301000b100b03a899151241000c10401515401004030000a12500e0590301201d11802c0600c200e030030308030b015a40c9019145e1500002e02d08443c6000c1085545040d04442c240580000c207619820408a50390250030311869010a0050607100c50b03000c04140007803101c0a80880006101261611160340300d060031701206412000d403409081300060146005000f90600076501034680b500c1e002142e151000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 802065917 1250 802064667 802064701
    0x915180108100c0e06030901060e01080d05190207120b040c0603060b190e031002091306180b04200d06080f030d0203060d06020f040806010e04030801050111120a090906050d0506 78
    0xc00c0c062104c0111000d500c40002461045503040f00004807581010203080041ca8140e01100c81c5511465281ca0050b52000a440450102900c0900740208840c010390400441e03412a80028503d095080c05012008400b00c1c001c40c0200500d03081607803151001c81c02c1c1c81c00c900500d0308520302045148004040c0445a40c1c000e40e1074903101c003100b00b1402c00030341800101d0503c4021242c01040e00801460300c00400b01e8084400d05040003c1480c10f480009100145090b02061584c2d4038054005c540302c54001c0c1d4402c11503030605286e208175113002400c090300201d0040090519008000c1020302c800560944e0307250b192f000850400214000c00350295000601d11391300071a081c0781510001c1c045002800d82080032141c10382d1507904200040345400816401081c89141c0d41c010300c0086504100c0c2241542c2c028a40320582c420742444062030000580c0c0c100010076400580b81c0e000701c1d8403202c20410744812a0042c820995a0f104111084494900161813600960301050003801c07814040702d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 802067167 1250 802065917 802065941
    0xb010302010f1701090f06080a03090e040f0203060a0c180e0a1104050405090304030510050c1905071407091409030a0f090f060905040b060c070b09040b091518010810 73
    0xc400d2402c0d11503180f01a9000b0703805100710b1519620a413041000c0c600500f4007074509100140044030301c64400809145240c8180f2016800305000320b030a22205044540286401400701c503440d08001d0868001170a045810100217120260669032480e01940d0039411585c441400d4a03640c0c50301d54800e030080070065141e04070020304020010302512107003e00d030711414801c0c0103961902c1c5181030480c10111800c00328030145180400700100c880301e00d4144e4800005008417058000314270702e400d444500ca5050054040408100652410103002842c0401c0d00c8a110b006e10070b412114140380540c100654020295400621001c040c4c80d104010034010050300d4070b4000b03003107551003403603415483c01c9070002030020b0030884e07040c00071303003080c0c0144c840c445420784010f803a0003103000040c0c0c1c41d2107440c0101107080200040e030581c01d0f036844c4c021303521a020040281100d030401c0c00001104148011485018000c03a5070206024543da0b24514100c030f404001400201041c209414001e1250380d0640d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 802068417 1250 802067167 802067177
    0x60a0b0105040503070b07120f08010603020904020409020d0b12030918040302070e011205070506071e02010521090c060f04090c020717030a020615030c041e0e21070b010302010f 78
    0xc0f1070354200103d90090841001e0b80e41d03614440e0400d68280442c036610f6000740440d00714222075140e8452020307170440e00070380f070016254541d003800980648503981c000301010f40041419a140d030910703440307400c41304001c8a420a8001c1e442000540300c1c0515074465a00c8680150710398181020024513580c450321a105545240d0f4440c10102e00e0f10070282c200c03401d500c8810303141a0404c132342003020b400503180807100301d4149013040d6640440041146034541d4409807041820f8116401001030300c404c810345506900032620034401c0421502c0e01141c441045118040038080342c2e0600200700c800e203030543d912062802d030514040402074500403441c5021880b90190001c0c007801200d9503100000c080a014598038000c014000f450210082c050521407c3c610900091523500001c180794020002d803408190040d0b00301005a8a4400185108030142010103905803000041040841441001d040c0300031551030040b00d00da80d000b0100014009080400184059030181303c060883e00d02d00d02c0d01e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 802069667 1250 802068417 802068419
    0x50d1a0a051513060f0f02060f070f02010b030105070c0201022a09040302120a1d120717030405100816110606060d180606060210020705120c160b12060909060a0b010504 74
    0x6940325200c02a40141c0025600c982d00b0380c2050703806a0086d254041d94401013a46003007901c5034921000b400340901081c0300e6003c1211050600039041503003280c40060081009180454000d0b0400d118403404a0050080c2101d000007601544501c0c44400e10240607a055604120284140008027500c10b0701548a494004000700010000078030440d0f1440da60ba03682c1019032f00d40e218039a504501b440344a01c40c84c1000005135000042c6200841c1e8400c0143c505205d0b2031440c080c1540b040342c20464003c0c030108074035400c99411005250092498180c1c0c041d441000d600200e070013958403030f03c070002c41d009400402c0451078050050580c5070fa9a500008800369000b55102440d44c8502089506a4668508110590301801001001000038100f5440d110286c2d86664880c0158540c46503c034402040d181c4a10b10104400c40400444042c580070094032076100c4151034000e001c001d6040c00400740000c1d2181807100029016102e81c01c02410140c80360044200985548042e2604000c01480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 802070917 1250 802069667 802069687
    0x1504080304030602042c2a0408010501030b07020d0507020405100522050c160b0903040305060c0c0105070f120b06090d03031a040b03060103141c050d1a0a0515 70
    0x51005500c1040e00581c1c41b480d14500c01b0f203010304004c3c40c6030b0489070110300890f81c8588071a840e0348a90b10000311b0448400c009151800700c8140c95407090403680100c0c1c0401c03000030550209041c0c034051110124030380c2c3c1d0b2500072a5204002c03075085001950611001c00141443e42003144c0201c01402500365494442000c41d070b06c180d07841101d00580c1105030140302c24401070700c185038200840000007860035000d03642540ca0740c012558000c02031054030001400303c0c202030080c1c4000e150b000040d1380d0217003000081044290016402010694a00303c0414540740c0181c2c840e0a6050b11500c811200b100b501b030800307004020400406400690802180f0503d64507400180d4132036100b9200040d00704601e59460200c400d5159006004601d000250302881c1c0c1c0000c0c0d12070440381e001c2124280c00000840741410645202540202990710141e869141da420102505107217000907020481c0c030700089030700985066800041a08000c500205001509001c0e55150b05003003650644c3d4501041c0300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 802072167 1250 802070917 802070923
    0xc0f0d0321020a0201021b060c070807020301180f051603031e02161d0a02030c0403140f01051509060103060b090f0a0302150a18051c1425061409150408 67
    0x40f90300c40180d500251103001c480403150000300401480000340003d10344941c100b0300c2d511960302d024000f0040803c07101c1c215076094004001d40a03450103a1a02c5602501d8070300b40c0c50180f80011200c0b0700406404851081240902204498055499500c100d9004c0c071043c0b60396250100300c90440c00747d00d109409010f03c0b880a02c000f42140811140c00300106519184650405090040c0c51030040083c40300181200e01584c00fa43d03040203400104041082213030b480c3c0301020100006030b5003040c04004241c00700e0129081503075010b6850400e07690b07803440114100c540310b0040e0384c2424020721030f0200504000c1d01b03040040e040903003d2a81243c40307800090168801100c00c51107540001011907800342e00951a04400d000f00f030800140070b0038240080c022072143c038400d207101d115030007281003408542c1100c1e401420545050f11581811403694407120342200e2032002c001d40e0784500005a070f9204441c10345070b41c800c0001c4507041450f840d0402c54042c0b41042c070705800c0181800701041d925424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 802073417 1250 802072167 802072177
    0x21100b0f0306041b050105180402090102071a0706060512060f06030c1201060504110403120503060402090d0b01080f0f1c1e0206061305090618030f0406050c0c0f0d032102 75
    0x7800f13070b0b0995004a000111007600b0160059410420144152041c02c1000426142c81c039008071070150f03c5e4558940100c1c9440d806603c400f11603219020154080c0c0c0702c0030018030003540030b10428015661203c2c1409507400d8803044001c486c0d0f1104002500510202410399040180101a01d0a0300c082200180111161040e10020740c1d5440904100c503203450b118041032103114108241c101440c41d11654481c0941d007140c0c0d800d0200010028489588540c111903d04400916071100350750b080c00c10308090002402041442d118400f2407415140c000500d070004004010010f0100300d00082c0c01120807029440000280413401e001040b802413523101080c81d89030654000c11140c5401001c20001c50300d11038102c08505e1920081c0a80c0003404100b4a40c490451a540050040500e17901d918600c90001c080035411008074001c500e075540000200325020304042190800c40c1004100200480c0716400c1990100030003103c0d41c00a4028184001c10601c15512407098940403040001a680f01c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 802074667 1250 802073417 802073423
    0x90f0b09280b1b0f060403050a0305060105070c0b03070e060f04060507060e15041707030e0f010e04050a0b01080c0c0c09090f010c0c0b0709062109050d0c0221100b0f030604 76
    0x351005590a450802c2500213680524004108070700781618007400c6071280341d00d81001c05440d01c002400590182049441544e4064071010b680c55803414400382d9504184c900800162a0090140c007914118094030001c01c0d1705540da918081c40c1c2081502c80b030344020300448038907444040d003d015000034010000c403a40741200c0034031985003625007c0f0502c078070001007003882d14080c071503000403941c0240f030581078490980714070402c49036010040c1e401c03171a0012003540c06418a0100120086240c1106031100000e03290190252200034000505014034403003c00350b5442048003681d5803400c00d040365000300e110700a8940355403880200030f094402c006008004207009611900c20400b682e85101d03408502c0746001c3d642d090030000e000b0458960b181050314101a10007a480e80400194041c07a0210340c400101d0360744e14015900a41040781c0d4980a03071040c5019860014100c00c00d140d50b101c02440171000c0c002c01428408120020711500c481180c2003401c105c1c11040329241003041901484c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 802075917 1250 802074667 802074697
    0x140103020d1d1501061419110a050d2a082a01020909070c0c1701020d020301080f21040521030c060a06080a0201020604062a090f0b09280b 61
    0x2c28403003003100450103a10201c20407901c06d030001210400031068a00501145107007007141c0800201c05c80d001c440d941109016402801000f10822000046804100f0202c2d201c84600d00e00203e80da403803680c0201160304901054039200c000091810000301410300000003200341c03440c220000c0200300030044200d09096940040d4044462a103510306c641c2c0a0320510b0407250810071a61500319a00c00e5108540141e007010140e00c0303082c5001e4050765a03001603944115120360b5901c0b42c1e159600d10100524501c3d02034080320444a15007450f00d14000d510620b440d0345002c1c80c20040c4200c004048806030748100058000302416041800103214180826000344010b0404402e228101e070260751011b50740740d105011000050743c0115130540d003d500108001419071100500000114000708404170706103e00d00304d00070f00e94106407600c081d1030440c0c001c9841c041c0c40d94401c040300d103c1d8056140e8801b4001c038080e0f00380103028240c01140c01c200030807502c40030303600d1060000b81d41200f004003880c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 802077167 1250 802075917 802075933
    0xb1305030c0d02060d271a06030303040309140103060b0301030809090c040f060e120616020642041505180c07290f041506140103020d1d 60
    0x89010051640c1c084411610071041c02c0c403590000340c85104408180c2560380d100d098000003d03d1480500025049514041d038440d812494400080c5005040c0b2000c10107060020800905000080d24400d0740c0c0354031610038582c00c00503112102161243c4581c105a203030781c1c01255003812240954002d500c16134540e034641d0451400c00c5a80780b0014080da08074103040c0030030802501504030003400c450540c00c00300800c43c2e01c00042071200281100a440c50710400050001410b00c6400382c00c10001c1356400d0310066112650700180b010741c1403501071450000d060403054a5400100214604940c2c020f190240f81c8404c0089801d54104154414410282400c1000141010552a6405040d520030240c9916142d451000c0c03d00421801a028417102c010160051255040e95000d24100d061200c07260f140c030245004807000304640440b1300281d135002c41d00403248140503580959110305400c00c455149000110700a400034840c1c01076903a268050360134108103800d485030701d151030702c0042d140603 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 802078417 1250 802077167 802077169
    0x3712110c1504051003060e040503070512070314030a020c0708010b040b01080405070b07051f05240a050108150d060b12060f0a1a030d030f061401170901060b1305 71
    0x225040502a5019040310120040034021040440b0296142107441c0d0046101c5040114000d2143d5000b20441c80856400e000911200001078110944100115114181d440441c13160501510341c00401040380a80e1103405940c08402866100d81d002e0001410050209502e0307107880307061750000149175924440440e407414140642c1c5050f030401e080000390341c01c060380c40310f80d1081c47e8070403141a22400315420041190902c00c501c55500e031116010340c04156001290010002070380c40c4007100c000014008400d640c2039185600000c0d005113001c101c50714160064684020003014020292204600b00d4416503440c3ea58070380060290300c00051100d141018804070b0f00c801c0058402a91003142048000d42c110042140d1200d01e00d0001b140c1c2c90780303030341241034400606401c459250060841802d0003c0c1c0c103600c101c40100346070406100071680c0f400c4103220b9016a080b0140041c60b00e00501440000181c9225000000c41c0000603800c1d940700304400840d00100704010504055440400503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 802079667 1250 802078417 802078423
    0x30c0609031e0c08030c0d0209060408011e060605030f09070f1e0e09031b0312041b05090108030909130c150807030203240406030c0b07060e371211 65
    0x24190483c280b01010500da9207424a503800000d013070342d04500e00003d404840e980560103589601b88054407181c0c96544914010b03000c0d180700005014000c180343c80480c5010301500600080710140c1d03c4091440e29454815100840e0042c14000c00b40324403400083c1c031074118180240109070b041501c0702c0e0030f0b035004c00e5032806141c981c4c0544c1204042c0001d1000a81022003200d5180640300011000070040f142400d045000fa11110049948e1000401040c011089400021008181d48507880c4640b1002000344802003801601616401400002d1440c14515191078100d4440f01740881d09804c199160326425000d50844565014116050301c00d954204e00c503180c100c10795042c20750540c0342140041c11000d129560b008455000a02c01580580b1982c0c03290001d07503004854070044949441c3c07801c0c0c03a40d00a4800310364080c40c0039400b100303d0740045003c0780c0c0e2a0790b81171301c200004102d081c40c030807e41c0d103d009131040c40104000700c800100304080c00c4080c01c60a440d40604040080113541c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 802080917 1250 802079667 802079717
    0x1806030c020f030405031221010f05010201180b01140f090a020c06010f180c1106090c010906021504020d171c051e0a0c0210060902310909030c060903 66
    0x42d16032080c4010f115598000c40e13044c0e0420389500495803960303020b441c804282c00f00150714103001c90038040085119502041307100c09071072080c0c0090081c100c00070712038503040301d1182c03014040051301d10060015154558882145d43d10040174040104280000146803c01c280c504821a5a00050400d000c201c180000341c010b0001e289074001141c90100312100060030b202d1036591441d51100d4805000e40a80c941076043d140c0c02d13041718014030780700800b5070342c90115a0040740401c03c400f41c00a0401e20005004c1817603903110a9100c403580702d030303400d01c1440c0040034801c0f60b8008482101820745d0080c8009444100210b020a1440c106440c1c0004203c0c0d9010305986887e002408041150808010219030002112100010b030001450002c0781032000c140d421442d404e09000d4001001e00b01a0081c01c100600004103000c1c118001d001d02c2d64804c40c5500d00110484407403400c200c3c0c030000e076100418450103400e050000641580d661011588219001c4000c43c41382e010019100c003054603822 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 802082167 1250 802080917 802080943
    0xd170d0509060c07061523011d0a09020a0507240605060a1e11031216020606030d032f0d050a181407080f1005131709011806030c02 58
    0x2c0014103160b80040d5862040d003c0203081c550300d840c0d0803141694811480c900500307584214060340248011002d07601d4000398221800a0003a070942c42a0a9014585682205000b802140403d14000b1404081c0d0011400c0000707000080c0000c0c0c01103000450045c491040c0d0002d03410303903035082c00c07502c104880d450781283e4003d1078180b1043c040150440c0c9141034200680000c0d44000c091407c08960442c5148071007003941c000412031000c0d46094140f054000d854401c200624180d1030740041f80ea851040b10015415440b022030508254020740c80001e02c01c0d045c280422520f080c04038040030b114a8101d10900010300000e03026017501c8184960380d008141d403c024080400c0911080f10409041d00c070140284400150107030700038804102003002032001c2d40c190350302d5200e55148a41c40c0d11008000d46d4039241490f0000301160090702d2540200c951041c071001070a202000038800c03030741240300200d06020329491500c10860260310000300400103aa40410903811400c13000342081c01958040b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 802083417 1250 802082167 802082173
    0x20a03020f1c0309020a0810021b01051611030d02030114090a11041701090b130308010e0603030403110d02120105150d0503070f0203190b06011106040b150d170d0509 73
    0x2c85a1100581000040780e41468041090103050000400c3d0700d00e01d62104089114014004a0010300341d0060303c0240a00340c4007500300d401c020042c5098030070407101d16035600f21101c401014180a0506c030702c00244030324122414443e1552040c0100d03402030704542096141521250124a00040345030b511065011007882922410007000080b4012405070821890016040d0504050300f5400040096041100100282030000c40440c44a50099050340043d400300000f19aa640700c10919010788800760045151501d5520360b40a00700c00b0340c03085540020480f102c440981d444110306407004112a000281170700f0164012000f01955842482c040c014a24000010070000310a0b603004580011a40118203d680300003820243e1510308185a669451141403d0000c4a0f681502c1142c0a888684520041007201c0f070f500c650450380108131741d25110018241c0b111004595030580409047e1410790001569aa1000c3c0160384134041145004a0501c0f00c9035190700507107400c5410072020f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 802084667 1250 802083417 802083433
    0x510080711060f0621300d0f0605060c0d0f11030d06090e0a050a0803040807020621010603051302010c0503090a080c1e181f0303020a020f06090d0201121b020a03020f 73
    0x2120b61a070b240001400304a04050b4029104000001603004003100d81d2500b01e540d401180c003140c4020b21700e4165507085985409d8002c141414803030102c522400304a0018400c801019074210703407100700614200c04114240751341c0810171508002801c0302c005043c0d00840d83c507081021810440d00020b4008030f40d68801500240420004110040c0c16a0050045681da65803410110024482d58800079007250700005c003032000c002c0d041400d101084c40b00d0f070000c006c0d980e40c500071001e42c3c2058405d001715418894482c40198043d59040395034610400580c0c0c02c240c1641c000903c09480c0f54002403884d00080d07102e8000f8034002990003074480c1003c100c00d030414400741c0130502000b040d068200504c41e184011580e0248800d400c0c1b070492022000311601c0e96103034a8000d40f94040740308100d025054621400810746450401d4800070000900042c00000950f001198000e040f40e90303041c0056520214489401c0031078645828046068000f00f10034003d03840c00900d44402400c00740425000743c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 802085917 1250 802084667 802084729
    0xd240605060f0705010e030a050c0105010b09090a02161e0203010b060a050f0c0a38060306070309020d0c1203080c040b030a0c02030c010c020d180510080711060f06 72
    0x686a9221010300c0254840303c2030300d001801032203680814052480082403c004440e84007000307143e500b1650b0000d0200c1c2e644c2e05210f500701c1c00f071505c015500441d4400002c0020040b9406440c42012414440441031100e44600b1485080d50b450000a02d070000044010350400f4065800c40c0003003514001d103000000d1000034024004e4180190407460001800d00421908000e4185041d801440100f80d010001d0003010601c03441007140d0943d00308e000003900d034181103a9001c0c1e00c200406009080143d649400880003062070b01001c9a00c100088510700100d42152442c0340900060f00c00719a07280030070308010b001c1c40d01c02000c103070745e5810400c8103100059864003980e03048a2401008555582d207030000743e040d801500581d0311150304c4c00001a40540e030000b500c0c480c80310300307456407042c1061454000d00c2c200b132a07001d130a4100d100705481c0b5015600c81d4507540d0b8490040d2078100c452200d40d8070030030304281d0281c5a12500711003460511815141032a09a41103001401c42180280c5012b6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 802087167 1250 802085917 802085929
    0x705010b37121e050d0503100803032a071a04030206090a111909022701020a03170c07080408011e141303091502030304050d090317090f0d240605 64
    0x84005260301d06400c80e02246060800e0984402a13104040e40c9000c41e522400801c03d0b00b04480103404004400400115030a020040f64024006414010100c4030180441a0343d104000c424440c00c900800269000c03603800d00d280c107502044c6230121036040c00c05040080ca00000a01807442a4201002000001d421030001c240003c8055400540307940800300c1c60060700070070741d01020f2220300000e00c00c2141c800041c80000b0799400403034015804090500126a10305200f1001030102c1c200000700001c0d400300180c00340e80600e0059020780f800390240d54105d00c0790801e0f4000303070107603440c1c0d21812040044013480c02c81c000c081c0c00c810020000b0124001022040107805480900d03420b004001c141441040080c0c0504041e0380e44403040848110029944c0d401100e00382d416016120300d01d11700620403500d002c110b98000500d8181c44807507850007040760b0f209600380d07640407010b180401d49546a080c61030420354054440406200084503444140c00c01189500c0d40662404c07100740710307540c1c40c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 802088417 1250 802087167 802087199
    0x6031508010c0816140304080307030c02060603030d050a09050d090807060e1804021915080c0a140d0216080d050f100b0c07170a05070b030603070b0705010b37 70
    0x201401c151003078600d0203a82005d010000802e0300c0a00000f000700f880b48a00c019400340d0902d5500b000400300d40007080703803100d078203a0303125030315070070421014402211035041310350130280c40400020082c450381c0c0e480d880c183c2c511425201184803104100320400f0184a0392008000760305002004980c02d00c00500c0c1400702455a03a1070040c0c1e18013080c20354890786041505003090500e4034551907200d04825000b0914601440c002a02c0000010320f040c0d5500c00340c1d0b103590b56944030f101c5015840004032015400103c1c0d80e402d656801e2265504608440400c0e61000707002e002e040b42e8442c2000103090075544020700b5048660000d44c140f040d41f002c0e0300c0b0040101e0701d2035150107803607035500781da00d80c24a803072940010b40e00c00000070a900c84403808071742034250301d01c160300b241c00e0030303036104c00710321072800101c41160303154000180c1003050080300300040c01514451400082c1203628480002d0345004440b500d203488150f04d094250064a624110000d1480007040150000d882e01c2e02000c401c060f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 802089667 1250 802088417 802088431
    0x4080f030a090204090506100816170a0501020307030b010f210b0d0803101d01080c060318030c0d030b04140c070606031a070e09220804050a06031508010c08 69
    0x4000000380310940c80340c1c0880c420b10381c000c006200c0000c490400f580d840400303035407140c80141100000140c0b841300050240304010340f00300c3c5400b001c0c80c00b001c42010200c021070410a5010300007103100064801e01c010b51140c8202d03240011030600b2200010092401b80300d110091100c0a54991106080301c030010300c001406900120355000c1300d07800b1a400d0025150000e051100c040180702c0107282d405c400005803081c0d03240304018005131024060142c0428415a07010b034200849286090030004011640108440056169003440d40700507407a60f4014030401c0c016411403550500100d9040c00340742030302d58088a0911002e21410700c0c001030954054403200030904005950707010048103070040d00c011030300101c0b6161300358800440f044d8010000c842c8600003600c0d0076072140d010300d010412180100c0300c0c00420031003041700c0c1c03088103071800b215001558035200500001078a550399803540b4002c0c100c00d6601241486072458110203500450700b01c8c4542d64108081170f00c4c01503000b101258080340b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 802090917 1250 802089667 802089697
    0x30c051008041502090a0801060905060f060a0507031808160602010e1203060a171b03120301120f060e0a0203070f060507080a05070c03030801050906010305090616020c060d051b030408 81
    0x3c1e40808034000d1161700e015a401040d0000001110034041d4443c50485110340d1060145a440c1c90801c00145200c400300c03a40010140902d41e00b440c859030151060078031a080009101709011078074800c1c000150700042d81c0741d0111000300c0d100c88100800d10000c2016000078070845a403c0700b106d890f09042c9e02011070415000c00002e0050742c41119020040c950b10114905503000300445544402d40d07401d10b000c14404525015076903040000d04d110482c5510352203d82140d080844030b4041c2c2401a0341950004690b10300100468002d11a0300c0344461400010528110184103240c10580a68802079070742c403010311b08104060700a000c44034402d0703008190b1a91348240803000d0b0b039940200c01014054600150700801015081090360741aa002201d50305119070700c4100448c1581d03011036102c2155000440032482481160104a6941c0c1882c0113845034003d410000c500290001c400840f085030f1030f00e06029030b202e4072038007940034404010380071451407919072507200881c4504807260315410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 802092167 1250 802090917 802090943
    0x108060112090305210907080a0309030b04060b120105011715010501050306030708010501080c1824060928060807020a02151603030603060e0123091e07030c05100804 73
    0x1502c11000c031980070080c1d682c1c0442441c110141d00706100d00c100c86ca48918490136070041505800001c030300b20729690690b1030003002400c55448034030305070000e40304545060716041c4080c50399071041d04070303040b650681000191a40c1740c03601d01080100da00388a005180c10000303d0045468440e0344c0b00381941c0080c2030807035498a40b440481e2404000b580140f0055207800004103030400702150614080a0440d40900d442c03100181000035460259044000031202032141c04a0b01c519a404203000c48009014504055500001c5030703010705001c000001510300701c040001c0c56a114003044000e00600e14000d515440e208030065a034080204000c0c0c400c020302146104100040750442c1d80c46030340c6941c40111140c41e0310340a0301031b00e810f0204940c60750900c5881030682c00144500c800c00550345181000300c40e900c0b41d07c0104028003600c40c0c13005018041c900008640b400b00c1004420102a0091840520f9401c01c2e01c050310094000500c41c40010820040084e07118040707980168201222589030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 802093417 1250 802092167 802092173
    0xb0301030206091203120910020a080619170c0a0e22050a060e100c021f1a0d0c03110109150f020a0209010f08010f0209060f07061e0b040b010806011209 67
    0x4c41e450212042c510000034001000c00d5540d205070700501c00101164000311358000c800c0142d0041003070401c001481d090003d00c00d851300e1086c030b80c081c074809851256550340700c1a60403141c440c400703407403212640a0b005c60f1a9600300009080000c0082201480d0b032070030040c00703841d0503003c5003000c02c8035075610610340b00a210b41406103018040e8451000c0002204038100d043e2564174003881407079000d1510031364050b0140046070203101c0e21001d024692140403140220030082c9010031408c0948022a1507111f100d440c1c40c003648007018064076003110003500e07503d007003c00700580b845142d0402148900402c10740703015079690301030760700d8500784000c10078041c0c4005c80c600144c98001a500040a10000034060300e03519450301a94030090003845010344080140c07080e840303480c880582001c42045041c00c10b040440c00b8202c0700e0301c200804a5840c45003440c060b015003a420241c14001e591342240e640600e0a03100b4541c59980a003844109403400c44006828101d2440300510559240c0b0409020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 802094667 1250 802093417 802093429
    0x360703030c080415110f0c0f060703170a0506281205031903150905010b040501030e0f070801060e06031609020f0409090602031012120f12090b040c06090b030103020609 74
    0x140c0850315508100300808138000301001c481c4091030405005130050401c0c00344011070407500084014010080380080a07041c00042d511141d02542004098076a050400c11003550b0300b0f008590384d0201003040d00b4441c0070004200310203414044a820700e48014204c104000e81c820044400e40da4000c0340c42102800c00070b00b148035044008950b107071060048034445800d80d1065801113044a180d410850300c4071200c00031038600b8055150f0f12601404104050b6200b50004003501149000b5528500580b08026241c500030750030404680c0d4540100780042e5445c1220154888001c030020a200c03150301100d035a030040103000710071105400003074007101455500c0403540280b56249007040040f640f401c0900003034105031051003000120360b40000e0184510f001a030801d42c2c12141b500003901550009403050011160701405000b00304003c64500707469445880155405113000c10304a00e40340c5411144108141c2088060149000c000e01042d400d0205503810340390b060f9001540c038440070001401c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 802095917 1250 802094667 802094669
    0x102060112210903060510212f0a061e0512150609060d050f0604020f0f390c01050a051602030109080316080109050609040326360703030c0804 63
    0x17143d0307800c01c0d040c041882001020101141c10b40032141c40c5100201c0c0b0034250441d410000508428000d0040c00c8000b0348101101c40e04a801c04506000040b42c90049400103c06500c020042000c80c03808540003460841800f440c4000c61500c14a030ac0c3c1117611401d241c04019000042c89a1030341c072420744640301c1e0800c59600000060031a61206480c00340600a8107041b41e50101442c40e040c00b0440300e081500903100e450404039404c604080000e281004541c001070000c081c1d03240000302c48a036401c081d10180f41c003070003010352150366800c143c105a850070004201789410040100192459198003200750b489030724800072441c080d1021400084d001d001c07024000b5042c0080002030080b0540501654078058002d5103d10002e47e0342c0b000500116007085510641041c041c50003c0c0000f442090032000507102c102c0703401034285000039441101d24044890300c07504400456404d4011403104841d1221a800184c840709246100d4003007a112404c500c401002d00c42c680080034200321000003510 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 802097167 1250 802095917 802095923
    0xf181806130c0e070c2a152703170c01141b0703090f091e0603030503160c0b09030d0605030a0c1401121a01320d14040f020102060112210903 62
    0x1003444120004040c0d10031080301d0720301e507000002c50800111403144480a071fa03400070a44602d441441d6101ea0789065180004c6407060b40300c98410080b0000d01101c038015880030300036000948881030f1a9440c4c0c01c6922003014802507048036020080c06040403d010300340501d894074070b1612124140340646201040303400c030342c3e44450340000c0881c5001d09948120103036281000c0d03800030b910a0768070a0048401500002d8000350040000440c0388409003071403542e104080c0381018120505031985028500c00791006d0030741e50000241156130000038000c1002070201200500030124103965170302c250350b00c0c13482400c80007030304801c61213003a03801900100140c41c511a0280403944041c541191443c04505500d408103038104001d800e0611480715039030540c0070442d45440070038803051803070f4901e810040610f030000c0e40342c00e4209944800184903900642c031810804490011920000e0306044050f00310b484514130765040440800c05065024aa50750780114401058404c038108071419144d9030005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 802098417 1250 802097167 802097183
    0x522060c180e04020a0605030702071509051801050306100501020a021c0212071e1512060b0708040905070807050a03090f1403031b16020f181806130c0e070c 69
    0x604076000ea010300c2d10440c400c0b05c0f034005041d02c402c000c0e1440d00054a100d0300691110714140304120b8071127580c0d007140707610381800b6499959840004484d41c0c1d4040501c04070200c1c2e0310040009080800c42280c2146414605c02c161900f000c0000b941e80d00e0b0303880302130b20584803046c0031001000078180b0030100c0c41d00036101442e101155100140d0390713038981c0700e00040c10211a0313035009040203802184040d900e1180301054580340d040740445448420501c0e0f440596520500010a00e000e4002003110902c108041526640703404411021920002c0401c01807044003410048440d81c0300d422502000000d040c001004421410150010384070110010030100410301000590240040035502c0703090115405e101d020700c840401e0b210b0b40922a120041c605005c070846e40180341421449806907400381415100c10018040b04107016415104402c603102520040440f0013418846240e0098103d003043c50080c543c4e075035145107022a842130092080c85000450300c02403060350100d04131070b00301143c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 802099667 1250 802098417 802098419
    0x1c0203130302012a321201050406060f0305180304080a1b0303092601020f040306050907060f0f030b100c0c06050f09040c05090d0c1404060f12021816030522060c18 72
    0xd03038144d1b0300c18a54224025a00701c000616454035010310b0054076210341d106103040307000b07a07025805400080d0801d030416161209410800004201400090200100800034001d090401030325031108415001c580c10f003007101c00d101103600400c1d64011201c10b02484049035181d02c0c120000088051003803200c2e94000200200d024004001070802d03280214010400b5488804505568070058442d41000c01c00c528801b00b00580500040f144081d854100170035010190b4000031540400f03000ca0001180f0402a80e90030302100080103800781000303040c031a10302030542500a20300d0080c0140c7c01d21031340c6c0301c2c0c440340090342c800c9064500c501d4001d051644410640d1904000900c420702480c0551000e420031107810f46040c1c080d450480d500600c401d041ca90400350700d02005040000281d8102c1d902c0c00d0b49035508584208080c0c4181a20060b036001c1100482d80142540d401a020001140c202076000610844280c01d40c181e99500c018000b51710b0301d0541d0182d8880611249101e001800b90070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 802100917 1250 802099667 802099757
    0x1704111504030606170a020f06031012080307020c01020a05100207080f070620120a0902030313090501050109150503070806011209050a021807080c1c0203130302012a 73
    0x8210180c84021740030b00c0d581c031900d0f10b20595816404034081e6001c02c80d4901a010380c14048001d640007403000d50b0107044c540d1103400c001e04508410b8001c40b00c1d01000820001d000d6418081c109000b1024070190a5418203900e80c1641c0304614401a80e1442e8000b0b00102046520000c58541a41d0a405c4503140e41160411360010010310900e044000c00000c40303101c21000200840d50b00b685454338000c0541c031658955001411030322022a0148020032822441c103a90000400080142c000b01080c6981003000040191140b980050700102401d00170000b2580c0080589500c1241480d05008655407040100c841e060201c6660001c645000c102c8814800f0104504802c68000d44114001c64500310141034140c40480b0482c0016442c20702213000c41c0d42c103c00902c0b00038480107196020303115007183c0c10100d0707109844808440d0f03440c020220801d5028051400d100c1030420304012054079000c3c280350400080c543c400c0030000c1c0888060300414030958042514910b0407840f0040031010780e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 802102167 1250 802100917 802100921
    0x150a08010f0b06031003060f09060213080f03040f0b1315020f0613050a021302071a060117073002121b070804090207020616030e1017041115040306 65
    0x1e11140141802c0c480041d01c541080c0e41283d004680409443c07003100d14503103500c40108500400c138440c00780c6a16081002c5400c60000d098121080c9046607481480e203d20300f89404880300c010007813900305000422001d900c0002d8032084403070030105079581d03c2d1038103000d001107886a00001c0c1000700d80d400500d80c0c50350006803580c1c0b12040404440268907620350304000312490000050440c0d00541140e401814488030110341000403d001504103082690750152504a4000440070034400000300301a80da441880078100c0020804c01941d9802d01d100c0c02402500d054007001f440201c0110300184810b008550380050320901c5808548802c10342d140701d88004030584050b4051040544852400320140040b590b4550384640d40600d01071038940000301942001c2c034103903400b000c1840714011a420080c42e100f6018031030340d02c08041211200c100030700034000b614080e04100140b190341d07403242103155106800c65088120f000907041c2d0301c0002030610b16400c020f03855900c80410f001040040135 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 802103417 1250 802102167 802102181
    0x516020d0b07020106080c1e040e0a0606080319081e07120204080618070b0a0c060204030b0a140a02210406021e0a02070909051b03010204051e1014030f150a0801 71
    0x910607510212041070400c170035600b64024510710074259004035500d81c685075001851401c2b112007501c1600310144c03038480403608503a004145507003001071050640c3d000b281310801d0305201402c1ca02c1c1c079410300d003507202c0b1103500c03d03419461110441001300d00558003a42e4100c034014100a0155a150384444006440300400d6a040d2444c141003102000004008941d0301c0a0b5801d40c811541050301c100403ca5003406800c80a645842d400c10000c00071429189001c0c2c171610401002007201e46800c0c50680d4a0340c001029801c20506c140308000c0c0c1e500700309000c00d98032000400540c031540c4490400c04000d104108800c0c1e0f00700c1720201442d01061041c400307000240819002c0c0d03031030540d50b03407004415583c081500402a42002c206c02030b00b40c0910390700b01f100c030401900041c180f039180e1010800c5c60348107103c1d1840c004e40c43c020300c05652810101c0d11611100600d00244009044c070030300072050001a003168281400d5a001039115004c0c00c20000005070014081d030445540c2d078089030700030188 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 802104667 1250 802103417 802103429
    0x1020c130e16420203030708060609030a0201030f110a020601031203090c050405130b09160f0b070213020d05190f0c0f120f0f02120a0b010516020d0b07020106 70
    0x1515010401c85040034101c03012542c1c03400f41c01c82903d03225007150a400004040c05034105151004a8006040c0c0003c0c0d0106203441e500103555034200f696002d40030140040045220f140b0410200c14030780c9000c40c0c48000c0c00e50a003004626450419010700c0500010000030302c0e8400045480114143c3c00194203040328001e001084031100c84e808114162001080080d001c411802000c000b00d0410307a024907440741c66681403900102c40c96541ca081e0100684409503e580702e0f021034004084c145400b031f401010290034221000b460041c2a9031140034958010f481030711100c03070030303c04103882c0c1d0119500c00d50003003130800003440c00c4441d480442c07050050b40c43d05c03545014205c0f80c203200070b485501d0040045440e403100302032028004a03a050001c220740090903484544480110b10b050060306076070b103c0301102607260808030001c04507810005042e003042c241402e00d445400d0b60005d040383c100000514031903446042d035001081103815032401c0180721702c90080800c0391041c1e06501c10410703244 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 802105917 1250 802104667 802104673
    0xb04090c05010807170f07110d0f0f0e09070315150c060b010206090a0b060a09020f07050c060301140103050402150316080a060609090c1b061407031806050601020c130e 74
    0xf18580c08441d0000c80045105c0d8182111000c2014199104103c0364011480c1c58481c07004c02500000b42d0900903082200004940c280d0601c411884e0031008042601e40d0303502c0c0c0150000d800c1d20024140e030740090040010302d0b82d20f000c0d4411002028540c04040c01c008130038807421040300d010007460041c80c1c0d030702070352500e25001d04000c0d10744c404a80c1d2809803141d580141a14160750300c0d01402e04001408180c0d22003512040003030b5400150020305800c0001c02d2450303480703450b0350505c58208540300382541d00c82c000400050020b0406040f00c42058038003840c00041c903990750300c04910301c2c0c81009454804c228000c010030104101ca0841e16612070380e166030301001e503142c0340c86042c02d890142c0200004907000105c1448043c145511461007110380740b0300300c24403581612591440443e0030006a403900d44400031402e0516604040b503800c00401d242c2045010300c0c0f004010f02c42c6c4416030004119540b6100440e005a208218141400701c00408000d00307070001c03441e6807000300f1050342c1642e0140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 802107167 1250 802105917 802105921
    0x2b1104090f030f0e04020309060a0507110f0106151103040902030a060b040e18070b0a032f070317010b03060d020f270c071a0702011e020705060f1014040b04090c050108 74
    0x200b17242c001d03240100002070042285880345043d8002a0400501802c10004400303010342c030040d030030007114544496035000060428107041c070315445214401c6c050028031101005296128000000b1182210042e01c4010384945408441c44042c180d2a0b02c10340c1d20356404140490b0f00a00c820341c4600401d1700801d0500320304503070710901d0744600d02031007070901902c01440080103581c0203401640d001d4480b8004488241034002151130b01c0317802d00d900300341d451401113081000c1680020b130300c0c00410455a041c4e6000c0d0702d0030400b000c280c0700052800d4021450706003d6001c41d100d0000d150703a03081c0020315800520074203c079982c00784909810301c45080c0440c4401316103421007a42c02c851119070002c0d4401a09059801c0ca2103207070901912040456503078550000d82030510b0161380b203200d10341410245c3d131041503050181c034060380179052003402d821240511140d1051003202e8011a00c2c43d007100c105100d100000240185282c0940c0f607002414440c13410200700001d82600150750003601d80c48015 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 802108417 1250 802107167 802107169
    0x10608060d030503130804050a0e0105030607020c0a0b0f120c371b0602180f01031e0c09050d050f010612030806040515060d0b2b1104090f030f0e 64
    0x285500c0714010340402e5080001c41c40081c228520120124000c01d901d5190aa8880c003040c4070b20303100d03441030780ca035103c10006120030320302805002e8104110703200030800e6440200c0014a6124988030710b40c0207080003d11558030707035107480640e01c181d1500081c4214a00d80550f480324640d12854802000c48040f10407480324460440c41012a035030040c0715040d0120b011001582d120159680d04a01c004035001c0d01000200203000030100103154030414552904101d0901044005c0ad01c50030f8141811300f043c5501130105604102d902c81c001860104070312240d4a01610342000a40166803c0200303c030402c0300b40000090900307201a94000200642a52254102019410f10200400060700c0030003203071407450940c10098100306082500e2600f00460310000d0754903444601d05100380f84e02c5154000207483c01c140c0c108108482d007201600e038240d0203100b000d030144519200501248418548070200d40b6654000c9000c2c40d03204503900174818841c00c0184c0b50172402c200520008400c00507880c62 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 802109667 1250 802108417 802108429
    0x50102070806010506070336050a1203030c110a11180702070311131a031c05220807031b060c0f150902090c04050109080109020a030b0705040b040e01060806 69
    0x807102618080c1182d6400d01e01000201d0b0310004050701080f066822100c0c0400c0340c4400815444007032103484407800400503035079101840c81e610252140035625020001003c22403c038410403039043c0750010f800d04100b107041c0d0705c204d90840541c7c840e00c6011650f00410250b8468107080600413510546508004840c14a100d1422980980144c00c901c0b020000101745c0581e15240041c024005080b0021840c011401c07a4107040218034140c020103030103001c41c06c0500c080040760301c40900300042405030340409000c038030501032450480500c2d10170946440108030302d0003024050306000d50306c415030749080070044100e11091442080006500024555005444002e40c150b88445042048805a00c406600704882007840400b241c0b01c4c01c5d000016601d503000305100c0c5083c50711a40d26641031600041501355241c01400c103030780c03400010101580d581c911003030850b5401210702c18260707034030881103490303000e00c1d804028046004500400d9041290054506070341e40c1c1d6445aa1a0740c0300820026 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 802110917 1250 802109667 802109669
    0x2040e10051503370c11030414060903030406020102030402031903021903120e100c0302030f0f0402010908011104030b130201270b0c30160201350105010207 69
    0x684003862100c001100001e20b80555031064038449102c09454040c9032140c0d0614101e00c0c1c02d07002000d0140ca1010045061103010321001c40ba01c0e080802c4159440e106507280705a0084506000c2d070000c0e00500c076513503034007210558480541982d07140ca070395440c0a4044e4000781ca04a10900604501401d43d10790048050000e6130164014007140c9810390602d0b05100d410402581040b182e031a0b04034045105015100c40640004000c00f0040c0c4a02c030810210703202c7c240c5683c100350041040c031223003c0b00203030342c107410410103045007095450b144010f98001c0d6150784030f91003030750a01c85800840f10250002c2d0084078050501458140d981029803c04020034030300c024041008552220100031600d01c6d0000c2e901f80c0400d0082e6080d03115590402c03941c00121800081c1c1e80160541c01540c10341c6000c100366410122100256107403407200c2002140655480b1a403d0303083d1099440071340e131003a0714052a45210030121030008109103042c0420081c0018652a150b0b007042c00000c0c1d551001502c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 802112167 1250 802110917 802110919
    0xf030801080a03050f0d230124080402040c0c0b0103080316030605061c0b0d140106051909020d06090e010b2d040b1206010611060705090a03030c060f0f02040e1005 72
    0x180303440d0b8805c0e640c0b162500f204140b58083c80e501c01d00c50b950b2140400b068070204050072481040d640c500103450110f0741e89900300c0503042c004070b80d0141340310f6045069a50440d0341281c001c658444c020703800325030420303420708080c000f01d404400000c00d0182c810010b40c02036035a040d01e0701c55054101025416113405104194001c9410049000300741e000c40c040745c40c074030503141010076003800d0b403400941424002d1b5025103000401c1c0030f003007012410922901d001810291750030642282500031a0004041512528200507000a200005084291b0101018101c0f028040180c24080319906009003240d0345080d00031102c425000503030400c0703125055a003000c1540d902e010100e41d00c0500010344406c42402c5d400845640c050308159a040c00350a01034403065586410a11032400020319000b8068a0704007031140c10800d050362610798020100950b900b6040c01628140f1516003c0014104009035401452601c1803a5489940c3c50300280100c9600c00d00c1003034141c4411821940c9619140f10741 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 802113417 1250 802112167 802112177
    0x1106040518060301111b011401050a0b030702010e07060512060a0b16050a0203100c09060c12030b0607020a15030605120a030825080105010801082a060906070f030801080a03 76
    0x2403400c1e4901d54035102ea01000250020905c24a001c40c81c40040c1c1016074503200c5680d10203c2000c403102c0074420490840f0401e0b06084641d45020041100780030140281c140d800d00c0080010005c078005d4010145004220080b070302c0d10765507040d000b445d5402c41c0c0c0e0b02018000e00800854091710b4021944c60a0351603943c0e40500e0641703103594003054072010b601e0885040c020301c451038015a80c288030255030409260008074400c3c0c0c0f80000140170a0580c1c0140d000d010721110744401003050a540c0c0150070486080c0024000c0c101c0303000901d240102c00b0001e600076000d40010902154a01d990b0f01000750545090100549400420040c40c140195050207680900e654802107407154202c1500003201031a4031880d0702c1c0004034001c950030145020004148014010041560f11003070550040c026a405400e40c200001072560039840a00c150300c1855000105901b040e5075250100c3d0641c0340700900c000e82c0c034800342c9021200d1900c03210094010801d440000a03880202280c502d9140e903050b40c803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 802114667 1250 802113417 802113439
    0xd09091415040e0a020307171528110c0d03060501030204080c0d0602130e010f0e0423030c1b030105221e021512070509010f0c2603010311060405 64
    0xb400014035920380030320400d1094040e0640940c84c02d21171074014048204e41808000d14500300c0516207031305079600d51440344480c01004116003034204141414184410f40802c81c81c1c1c1104080050104841110010000040e98200d0b4a500203070740302480201d40c03814800250f584005604070300480c41850ba20b60015140c07604d041c81e20100b609a500e10a880044c2051444011030003415440d8015107050030700e20006200c1c9960068040005103a6952070485610b0a6501c5050001c6598030380e107a03105c500d181c44030361214240181c45e0300e0744404045a0046080352030f0a5031444608600b10f02035440d000224445280d22041c200000b076050300054401c540c0e039621504290392252991781c01c0340c0d80c401e15100590f909070003142d0445000320415240e003054030000c3c0d20f009010b003610041c40010010764600b0707600240e00390680d14190814559601d000d00703000d5040f40d40007051a02c458803000041010490000155060703e0094000204041c406028403110b48240d00449030b0003090000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 802115917 1250 802114667 802114669
    0x6110c010c06020f13030303051302060f16060c0f17040b0c0f16063e0f0706060f0303090807061d0414090c120703020d06020a02030c0d09091415 64
    0x404074000340324500052601500c000d130b40325a40c01c0407001c858102d0794040d0801c02c0c50b030325010799504040f140100e1203044100380d00051031031048410309801d0a5021a03482e0b41c00895800e00d281007034000f4403e112584222500070030000007144881c0c086200006900320041504890030301c610307846260742d00305803180c149482150f00030440c0c8a0817880100817065460300d0080341720900320300c502d6000c030b2b5069140d9a880350140060b14100400710f81e0b411800382c50042801d900040354244001140e40d541c0b8803020301546c0c429070360054180d5081c5040015041101d0650704100e90090341d82c030314681d4503981c0072900e0740308038850340c0001031080030010905020100b1140d0011001400080c0044460303140c800303828801c0b00c03010016002407040130070134207161064440d0740441d8005810ac641c1103034009a4614940480680050350116040070854000c1080b40c0740d42c6000000c40d40e180302180b100802e0382d0200e0251003003280c01c2c80303a420181050300822500480503201c43d8090300300890 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 802117167 1250 802115917 802115927
    0x6091116110a080d0807090902090f0906030a2108180d140408010c120608120d0203060a08030c072c04033e010b03030705100f0204051005030604050106110c01 70
    0x225007540e0044003018002a1000c08110144c0010825104c01c2514980b418014003865401c2d8041038a041c0104018900c070359494503600303484002250306400a403070f200c01191a207074491400820100b45400300f1010045c00c121810000042070741c41001c1d903a035074400518000184041e030280b1b03038840401c1d00b85150241d4040015000310250050030a5a80c1130304070700b500c400342600d00c00f0464180854645150780d0203040c010b091004004c2c409612803c088030040c0c410510b5a100b500d5001c4041202070362080030f041c3c01000440d040b2529840119403c0c0c1d150090b80c440e00a0506040001c007071482070028020103045103003100f60605035103e40302a620440d80300e8800e00280c81d08118441081090030004c0b25450303040001003501e4441c2c1da1414210743c40040c10303510039401484203600145002a204009004070400401d110944144c13440182c0219000720f940b16861640a040e4298800055842130400300c8041c44070b44d81e0340b00140c905480000d810711050b0801e0814240d00c1d4001c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 802118417 1250 802117167 802117193
    0xa030b0310060e0c09032d0c010f050a0e210f06010906120b0601020c0405011401180e13061104090504110d170a090e0702070f1401050d09050f1006091116 68
    0x14007070f9130304440c1c03c10a40b14a0b4118012481c0c00754010745101f074000504000c8901078000a081c0f4105084110401800e503024a4042001b00f2120790002030300c684640414450a02c100203501c11502921139200303803074502450383d8480d0340c444c41c000020108900e01a0300308845418171182d60751340441e1144449004010300d5107040d03201f41042980152202c0c800c0d01c0c002c3c8a0010b0340ca000b41000400104120402d1b8607220340100404018000d655090310300325045202c120030341030301c40614540780001c0d259042d0003510034040418001044100e980101d48120720405c400c0310040c2c1d030702c5c04000060000b807901419100010003240a94140d41c0300500d09070100f130500d0080b85640c0c5500b600001d004031540c2d801030f08140e00400c2036480d10409000580102107003030b82103030b130f604c40000c000b0700404181e16043e03031b10380c0c070301c0028400c05200b825890001c41050300c01030a220041000680300034420901c00700e16282514001c884484140c40500844034194921540140c0300c841200f0703c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 802119667 1250 802118417 802118419
    0x31f05180a170a17011715060f0418060c080f06041e050c0705030409060e06010f0c0f0f150b0f010201141305030f0c01050411010903080703030e01020408030a030b0310060e0c09 78
    0x135603005040d00380d10b442014001c140c442c1c100403080d4a14041c15040a82c4c000c4002204080d074000d010060b0b542298a001d2108141d50001c0c0a841d81e181c0c0f9000e840340c601015000d28038007a80c0c1c0c0c824035070080013180310316080031526003240c491000703003c200c3c0c04507100710160a10103055040014101e800c0207404c031000c00c2c00c1500b00007258407081e00359403259100d103101c15602c1f00100404008241841d620607401d0810740c040a41100002d080c80c2d01c068001800e2201c0c15081100300194101200c03401a0000000101d9180d1000684010405010700c41d11a54007100c259040358814040d450009504005214550b103400c11204c210700c8146070102c4950200b80700c050340f8120024003416000120b00004106800c10f07041520070fa01c0546001360400149260506c00f00c2d0340c110072150000d60510f000950b01000d405014028002d81d042021180000503030003042c503a164115990051301142a07039842d070300c01c0d5080d00449040707124180d426840c1c040001c9003400c0d01d0020b4440110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 802120917 1250 802119667 802119677
    0xe0f03030714070b180a0e010e1603141f1502071205030f070507290a0507050c030105180717070b0711131b020a021e031f05180a170a 59
    0xc3c0b50144021103170004d1140711341090000e010902240b5081342d4180c0105000045da038080d5050a40c00c182ca00e0b0010300000030615200340e250038481c03203a031022850001c1c00392407600509000000380520400d0400c0144000000e00000c101500c45903070010108140b0703002003103641d00e4907080740e000c8440c0c010143c03200d00040c4807100302e9002040c020009144902d0190401c142001d0402840c016060514414005000c14985a401d201412100e04841c24140b81c0d854090758a403040c50000c0943c9600c1c3c00d9401e19081c0000030007200072840240c815081941c1d121b9442e06c0445429840c4c018800070705520500040100610b03110080420602800d4808140359441780850b10510030864100300860740c0f41c0320000340c805840c000c41d00300c9500d071014140b1090ae0b40c0001c0c01401c10521238100c1414450003400707440ea82000900d02045400080106040b0624802401090111160492030307030042d40f007039030802000c1080d160ba030360b000790b08022003650a901003107a508a10001c0003401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 802122167 1250 802120917 802120919
    0x303030b1914130905010b1f0e0103110d1d010c080f012c070f090b0a0801030305090406030c1401110f07090203040606051903051014010e0a1415010e0f0303071407 72
    0x3d0054082d80c04518010f10011070500c05900620114030030313180341001c0e921706443c1881a01c65010f400b0110400e024640400d0310040b54070300721203a1140403100c440d91450000c4903c0700d00c425041c2e990b0720041c20b00082255202210341a43d040c0800c48003042c15280ca440144020409070300c0c0f084508100428014000341ca02c0c810031a114802e4031444085006821044c1449030301111400180c170f080319681d42446801c0d80040c01c114010f000003001e2260100300f45240ea00c40d5840600251b40128103908640d0b5504841d62413440c608021a0000d905400914012100040d5a8140403030800080c82203034502844440250806030041f12925112800020b0030f90301d48202c0480706450040804041d491407a229160012880842c105103041140f840001105030f469141100c1410007442566a981c0d000c00005049020706400d468008001b40200c10f41c101d0f00c100440b0601ba221880c2c004154010450082440e9009980c558001c10000700020040e40c4054410140745085607945 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 802123417 1250 802122167 802122199
    0x1404080a0212130509060103091101030b040b0303040303030212090d0906320d050f010f050103090c080d2114040f0c0807080d03291215010306060303030b1914 70
    0x50f80011484102460008000d2100e03192106016070082c8003400d0422444400b40c0d034540d0005440000e25060603515000c5030702c103803a15040155014001010381c0c0c2ea03541c07030b4a800740080d003240103a202a0902040080e14569001480722502c0d41c60741c442071034061402c60101e501540000c0c6031944504801d11008015040540150f40704400282d060303203803502a80d544003290002010a41949001d000400030f025201c00d0000985a0a20380407444160b1400c18040302c080d198007141440c071450046d24442c60b4062062224070100c4d44407102c402900312007100c10350f0814040c1c0c10320242c2403c0802c00007a1030380c110010301441140c44084142e5207500e400d0409600f42c3c0400490340240301c040b000c59615100b0b103000303c681040d9890b09000b65a00f1040d10321002c0c1e449502484102c20230741e12190702005404090a080701290350250f0316450b1503000b40c12030740302c110086030600c4200e0110b0b25100343d8110b00e0905001401d01145c0c5040f08170090260350500c178641110007003503e0141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 802124667 1250 802123417 802123453
    0x60c0c0904150203100303031b1d1912140307020102070521010c05181801050118151806031e02030a0204120f030e0102070e0a0f0b0d05150a1404080a02 67
    0x82844480c10184140b0321b90308014043c0c7d01e001c602140303166002c55540d03d01039000303035408452501150074960821207071004603e4518500a40110840c1c0038040028441d284211110307643c1d104085803440c003e00c41000c580e0740c0c044c81030001e015820007841030040d0306000d1820750010141420391580511101149801c4480d0421901c0001d00700103258440e0741c2003c001c081c64002c0c1942c0701e2162601c0c8031104583c0f214180245d604106025005909507805020350304040c0021880d040280c01c3d0041025240d1001008004102000310380d0005040b07001c2e1058500451419101c0c00c0c0140000002d10000c1d440188202d00d0320f9400c1c400071498007601c07a061005d1b5482078901c4642c0d03481030304010b002c1d03100c15900a8115408510140448100c4504090700540c60203404603000c0d61701c50718000a0050350000580129540b1035120038460000341402e88114119544140c54440011120540f8002c40d01c010340f0284510200d070004452500600d5143d0391031040d600000a40703566015 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 802125917 1250 802124667 802124671
    0xa0909110f031501030e03040e0a0b060c0601240905010c151503080c070b03190b030a0f081c0b22090b090d021902010e0d0f12050a0e060c0c0904150203 67
    0x1c034a4001507601201e5170984201018141220f00941c1032600d800d1aaa60a01c0001c09103080c441e25060940c1194442000b501d2180c0002400d5909960b103900c6940c0b516085207850141d0781a140c42e100211a0040c800b00b0141c90781a0340e8140350800c140c840719000d07503406012000035aa9428a5a83c1841150540000d075105800d4155100c0e80702640b6403620f6041d402440d44800200103000001880242d1080050916100424002c91444c0003a0514008060244c00b03c062400c01804204050000704500480342c0751515640301601c00c141c040700c214002d45a0444050075030001c3c8a01003028038101c40001c5c9101080e0700c2101d983e0b004100c0b2060b2442c51069004014a140c1180c0611600d03540c0390024540402c0c001e13081d00001c3c00131000e46026401141d1140621041c0043d1103050660b081c0c000500283d10008030400a1103036000021800024608107600d280314540f860441340c00e42c000c00000c10103100301008000b194140504211010442100310a07120045800554 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 802127167 1250 802125917 802125931
    0x31b1506170c010f210515010f02010b010210090c150207030201080108061b0901051e0409320709030606091506050304050715020a020409050a02150a0909110f03 71
    0x1194103498440d106907030107002044000d050304403604074038507664085880c2c00b07200150b00e07040c8413180d941103030400134010300c01680040c0380c1010100701039800141d441d044000c4080e607544169603e4100101e0880e51803100e21801600300400d11524511150450f10f20140141e4000308420b43d00d0848000d036040740496400503812450f020015981c1000300740d0300500b207007000b80a040c90011140380c191001ca000b04403141c040401c001040e40d1044040d0317402007184c2c0124051300131140b407407040c3c590400c0c407134030480034100420034071211003403580c20021040d05c400d82d4180c0d24003410074140500380209600b040011900e00080881e00c0d50080f0f81c0200310761400052071031104640d85580d18104c2c0c010300103210b8100f0520000a50010320603045800e04000300c5080551a18201d0814070b0304a4083e6001d030a095581040c480c020403100d40c0c49200301c0c0c0c40e144001c1c1da034031030b0038060085800b40d40208800000811954030dca030003030290340161035a41e601c0c14290946e00685604141c0e034035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 802128417 1250 802127167 802127171
    0x10c120506191202180c030105040f180c03020405160206040b0402040b06030a0c0305070f020a0f170f040e0622090201091703030907060905130f0204030807141216031b15 75
    0x54001e43c10110018540c2c0e5559464031007941c9032150103206c0c03504c010b108041c002e6580c0e000515413a40c540d03200a40c00f1003144413249513404a414400041c1140c1d001c240d00c1035140c0000b11b020440407840a6084411a401519699a858440e0201d0941c02041a6006070b02c03414400d4586e661740380150701c036440260300010f400b0302c8040300500311100148040c081c800c1000069000540008800c080b040d408001c45d561040c1c981b40c8046c0c00c2d0403026021154002c041b40c88104000c480001c1e1050703915070f440c1c900b6a541e540040014040140b90f441c2a03000d086040d030820240b00d6042000201d006041039031140d56106202003420602014440c4150808010b00800400c248043c4006000324584508071900b040005030540c0e07070080740c00010b02d607903003c103920004840d01600d00a68000b410151a4412410003040b10b00102c0c60040b0b65005a01d454400392175200c040d5241160447c02c00f40400d592541d003502c241a03c00003e0f04030320b003038003225400160040404d1144510030900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 802129667 1250 802128417 802128449
    0x603070e01110a1410051e06061c050a020706150f030b0703060803030406050f0610050d0b0112020708040509011a0d0b0102010f090c0617090c010c02011b0803070809010c12050619 79
    0xa176800f1100041c00e40e001071050510701c0d49440e04103020040e0052000c981250f940d100c90f0214107403da00149040111754200010020140300c540d014156441c0600800d200d81b035041c0c50580d0788100140141c03c8404020702c000d0000c20502480325502101506000039450341b01d00e160351443d00b044400300c0340d036034031442000410441000b1031074208070242c84152003210b40c0040602103004072810550041e42c0c3e4003600d842c0307078071a0540c201070740b150300380c1150341d900242005000e9a0050007224010350034a000050000040140b15a10699484049007010848841070740508658928541159200c8181110307140c6648100c0d24450b11817204c0090380740c90144050031418103400c0103194502ca102c01c0003000b40003c50038600d203210919061021101e148016920034064050200241c04441c000c00100007250008600419003510342d11a030340e07640c40499013625a5114213800007071040003207424000c2c580d0441c5410002c0103158841c4840720742c2d070082d07440340c8542c0115654101400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 802130917 1250 802129667 802129693
    0xe2208070606031101050903060f1e011211060c030904020a032d05090a260f040602010f05061e010e040209060a0e0910121b0b1603020c0603070e01110a14 68
    0x30800491084c2820200c4c24120184002515208010700501e8025240400103940d410760860100d8a03405040c224030440d40c40d94124920005207820403980d08503194403080640c0741030002d80d403442140000443c035101d50042400069041500402c0c185500d400010140c20748080203020842001e1031401510a0300305030f1441900d0b0041d0a20f11150014041000070481c0c1d4000e240710503414404824607084401d80b00042c80c40740000c012094500410f002c0b4038544d06401c400030400c82241c0c18486a2128002c2186200003841a51101000720000e20404c0d40145e0b1290303445034004000604080558000c1502544443e01003070004004601016141c40c1c05080d450300204444465003a003800c00109040c25910300b400078042e0081c001450050071f07807542007500600300c4150300341d45807841015204110303840c80708201e01500901ca004681801d003482960b104402c565a400b9458195000644a15041d0442c0740b0060060860320404203006000108031400360400030864080c4c02c403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 802132167 1250 802130917 802130933
    0x606150c050111270a030f0f03030614090a051b1918030209060904050f0a120e220905121201061202040605090f0609120708070f0e220807060603 64
    0x2816000c1061010720107136600d01c0300342e007541d4607000032103500460049004000418200c2a1383c0000c04c01c0d80e81503080c07401c025011602c0c0c2c8070144a07850501540351605030801948016141c11070b00654414001802ca4115810040c0c01524900022106442d00d00194a085e031082000322000c5070100c46a015050740490b03400c0307140c040e0b850b0215120342550b0000c1c48211021f084103100304114408071301480001d10010840702942c00841c1c015641c03900d0700030418200d011600010900711a00c800c60f074141602d003100440c64140b40d540310111421900d400030f14032464291401d100f02c50003100303181e2078030000300804501d10032a90f92035894210024091440d050b0321201c2d40c0d006010810806411005a80c00004100d880c0640c1145003000304400d4001d20104591080c0c0702c00c184144100c010a001003918100003d42e040c150b1103842c1118142000d1144003200c20107200080d000f241006c8040c1d804940009001400004c1c03529081c0c40c0c0e4101c40c10568809690314000c100f084414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 802133417 1250 802132167 802132181
    0xf0d020d171e040819230c0f0103050928080705030409110c0601090209040f0c0306050910030201090509060102160603020405130e06042604030302101406060304030c0606150c0501 79
    0x40d80880c5042e00b0314403c0c60b116064100202d40c140c42c0814817034204011041c001d03905002e5400304081c0c402c035441496999994210400b80100d10700c0d92120015440703801042d100e032a010008140c040303c82c4c03c50420b4140c50090700f400406413580480001850710b00206070190141d002151207d060842100407602941a5001d00c0c3d50200710100c03602c0c0001c03075400d045880c6104010317110541e21340428040c00c8400c070072402c0a4500071400001c503806900240c1611016078581c8865aa205003204403f20540006404548a00004c008610f09914850751102041c4190b94804c05d4000c504030078400581c0244000ca0b40100302408581031030840c01c000052103040502c03044000351429a10303060b01a1003e40741d182600360341480b031401000022143d805141002d56200e590f400e0082d200d07103580400403000d9050076a150101d2505180150103403000400840ca152a070707984c00d4a02828031b0104981050329042c4c0095800718107400d0700f140c00301d00d4039504091003091a18078212409 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 802134667 1250 802133417 802133467
    0x4140c0d0b04022707110a0606060309060c2102031506040609080c030d1403040f1704090e0a123c261302040212012c060f0d020d17 58
    0x102c0310340304c4143c24020840540101260410010032038403000d03500d00f840b460070005080c203802d14000141c110b9042d400020140d02640e000c0214a401d0304e0308840c1c040c03820030300031100a1256034144600c0d54a80c02950060980b6542c0011a6440d0010a806401543c03000c00407070042e0104000c40c0500303111904c0440e004034054005a85a48030203040200300039201c0c4c04001d0007100280030000180c1c0800c00c8a50003807030280f00201021100503032680103018007140707a410140c00c0503076080c0006500710502d504c0a00300341c05803c0c038142164a20b00d017218a40c10907860040364103101c524100452080201d40ca1158a03e075800c00c405440560034111440d520b804005002c02d02c10800907845800030b42105404503840c000d400090040d006182c001d11000080800002e0350900364031101c52102c1e2804001c44d901602c4070301a5210f440300b1036050740c0040711020408460303e016a41010080c2c03005000042e51403442d1209010350760101100c00002000058010784c480080e8411100350314 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 802135917 1250 802134667 802134709
    0x4150608010b120f0702160801050a0e15150604030606080607030c052a070b04170c0904030e04110c011a0a09090c0314031c0227060304140c0d0b0402 66
    0x18000b8801c0490410080130b8a0312801c0a40114a00c20b01c20701c0307514452072410b003c0b40942904e8440003402002d090ba2041507035450300d071400c44501001704403040042c03190308144400355540004812104281d2101651200b800c01001c00060380611814010b06074000081c0020700d01803201600b00e813605000c0e00140300341840030400c2c1c0c0300140c072429401c805a000144940c0e00c600030b214032b056074a410842d03040354049000303e4031400c42414003140e50007010403510010080b005001c00c1050030741e0054001014a1100c6000b810701d50403c0100034007007229540b6100220046508603420200c2d14603050001d0781a49a80e86403480e4000f000e8500120204100403040d0350b000680c02e818400240045520001c202648600340161103190000d6042c80300a0030070117000f40000e60103012355460669400310401103042005d41c0300e280d2824040c2816144d511240c03991031000ea04c401a1381e20314030610403070141b60344910b00e2030140c95100b10030310101803c01c3c0c4108601003900c0002440409 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 802137167 1250 802135917 802135927
    0x50904050a140a0c031803020c0f0405042303090409060b01080f010f2315071203021e0c070305030406110f0109030f0f1b0807050606041505040213030204150608010b 73
    0x2c09061010b412403040a0005410848698150060403140b41c5a0841c03068a5002c8410b0540104004841410480c4c400c0d1520041e101007008484040c1c1d000b4055034951450615500704400e000807000c4101c108481c200018600002c0035280388920403610691910000e03445c55070000c000d280c020b82d503094030181c41d40c1003030f10783d44503903da5206900031080100104207042a02c00a0714041550150000014800304520241c8a502c114000c1700c1c24410494900b09842c464070a445001c0450860280d4000034540c184000d60410b108848150240342800000110104001c10003045c15440342c40010216502031810040c02e080d403440d080e418485a040001c0c0c0c0300e54112510b05103070030010819040342ca0201d4001c10408020004c603203d20840700d01340103480c0d002e000703042d11590440782e8a503507850070b00c002e0316000704900020b6140d900c801d00c40e528040d0041d2203440002080081d185079243c0000e4140d403584a10419403401940060020b980e004c500580034103079034103c0074901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 802138417 1250 802137167 802137191
    0x2010f0603030518151206030d09081c180f0512030f0f2107120518070510020f03030a150b0f040b0703030b0402070b01082e021b030a050904050a 64
    0x207204030134070f148200b0b0200e818040103a8450302038004040604079181e807180c075503401044031580305031040d501c2403244007010700c01c50707201c1d405d05410707076000f01c005e00f400c401c1003200710641040180074030b000e00901400324a40c0d60042c500150080195542c20b000e601e03e4881800300c501c0c195403041070b068008014540d1040c21001c2110940680e0540e010b54902d001510301031442e0440d080950241055003c0c41066640010142c80000e0202c0c020001d039181c104104100c244560042e06036034110900810032468043e81501c1d0140c0c1d5801501c003142d03002da40c200d0540e84100c0c0d015004940c1c4000042c121134000d10418054060817007860700d006110032100340207000364130031003820b04800940303201058070a030420081c4010140040d5140c11080c501028094802d008466061040000301d41d03100010b0150440c040008200c14409424000f0420001e07500c0005400b03444130901c400000185c2d070410007050450080d54446481340307540e0f81040141c80016109500c0c49040c80c0341d40c146 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 802139667 1250 802138417 802138427
    0x50a150504230c070b07030203071d18100906060531120f024c0815030d0f090b03010302011b05010617010c090b1201060c05030c03030109020a02010f060303 69
    0x2040280201e42c4a060340c880b03143d15864810040010300099040e0240140650150040c50140c6100d440c0c1e504d40c02445141c0071044404c2060884c1d00c18480310240400e0004c03c100b5641150540d212400381a8a40b0802c0050300e9031039002000003540020701c031507138074000001072203421030912803c0050b805c0c0a00c074031820880d902a40c3e121001c0103101c0307020400983c5d07165094543c050100f40340d082d00195056101a1a40c0306440c00c205c2c42c44081c0c1041643c6500c01c24000e05030b40503904001c801100465080c2c90081c414401660815094290750740c1c01c1180002c00110303130351032088907510000020203034030f050b41c80500190418001480180e80143c940300a0101901e1031138600721060401c81d0140000780e102903039000314405150740d07201042d040601c2110086d00c41c0034185564140a130200d225840f140c04265500c0360040c86250300c80d900c00d407011030152085904007044e0b41d141c241964002c0e4004642982c3c0010741d84101502070080600411150004000341d40c40e6403800ba02d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 802140917 1250 802139667 802139711
    0x2031507020115060809100606080c0d0603170c150f07030c0e2211070807111f0201151d010303270906050901170a0f03050d050a150504 60
    0x9101880004549600c00d61029058800d407084405000c0d40e07800c4080d1940c07005652074104c07402420102d41c000242c0c0d0181c2c40440d040d5549a150503903c4050f0914690440f40780c030040c482d242da000201040c9d00e203509a00e264100c2010307035035804090078801c2c0b400520701c40030740c250350300d001c10000c0388104680350b40d6005440b03040200b0b030158400421210060300d441499400080c01d1540145c03007054240c003c011400030003080140900300c1c03075030301c44e54001c043e4028110001045902d0000f03881e000d411032124000ba048a07403080c829014504150800021540140c2d0348000401d08441e4a0140b407004000c008a1074444d440101d020344801c180501000e4148499000380311340c000c0c50491035248100300110310803074aa8580c060007000d4803080c0310f03662150225400104241001884100040300080c1c01403445c000107545140701c10340b0700c210990a1010500000c0d0f0845042e0007154031850f00e071600002d0007905807004258400c050f4101c2d43c011894051032640010354a4030b908 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 802142167 1250 802140917 802140943
    0x717240a06081501110d090e07051303020f03071d0f0f010302031e0c0307080f1c050406080601020109020a0801150605030621072706090902060909060a0e070c030305090a0203 77
    0x142038000803005817901c8813401d0b201101d41c4180c102e8015243c1d80b0120312410341d1104030341c221203512030390790884050044031040308004901d26030030070040c80c26081a84002d4009001da4045590300c5945d04c00700e520078005aa210202c240070400080011684c89503c84021094001c2c103504603004642d031181d110b207074007501c07641c0d41c80c40315001c074020004240e0010006080710034031a29948003c1c0c9402c107250150515200c0c00c0f02002c030024040e06d04000040082d80c07400c4c142464500b040702c9412000c0c0025056540e0b4036080c2000d130b00d85585c032601070003d82c1c1c000b0448800303c0300740340a0b1000550007881089403d105110080d40c0b0700440580d0034840000180100110300300c41c50601a481d0b10a032242e003c0c070070040b007000d104130b61b03550711000d0681d204100ca1035a985545054413041140298444010000d8440300d25202010903048100905145001520f40c0c900040414050782c411020030400141c1008040e41400b450b94001d1400c80a810400c03000c4e800f10f951002c0e032030012 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 802143417 1250 802142167 802142191
    0x1b160902030a0e06071d1c1704152d0912140102160c0e060102150c07051b040b010c051e030d02041202010e030114060103050717240a0608 61
    0xc68145811030f0041c0003940360480540b4504d04020501401590088584041e840d5005142022078030b00320301c071b202c6400c0580304504050b02c05a56490b40c1681340030001c504004050201184202c05c9000726098001551501e029100e09050140c2c2448001000305460b008500010450183c1c010001c104640341440140c1280e1068a071040c114034001c81c026403a588041507aa100062403111814154003c003000340744552039a6003a04622002c031045405139000407200d40044040140007a0700902041e61a4100411541e842d402c0094651811040d1482d40b001091580382c01d21414656607400d003012a411103c80da03480e40c85d03150944820303403100230800e02d03001a001c00340704171400d041000c00c1c1103542da500c0e400303d01040804e034001640094100300042541f8101442400c00040400340d581045681c0d040045024100003003091007080401310070961a2017030500194011043d000603d41e000c1d1105258103041a4064a41c500c81d0001060401c482c80c1c1102c0b40c103410045002130 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 802144667 1250 802143417 802143421
    0xa140a05060f0d0f02180303040608040f23010f1b0e040213051306090b1008040209100909030e090c07020a0b070c0b0301170d0203090a060e04060306111b16090203 72
    0x294942d9000380300c9014009070503c400c8030342c0d00e5001d0b40100b02c0102011040701010590700d0902d0307501d000318000c10000c03034183d46c00b02c0c0204184511004080f0f200f801603181c0c1a000d200c0810b03446034220162810383c0e4540700058030390711060044000805d0040c2220b541005c00700300091a240c1000c140c18003460340001c2d4800c1031140000050701030306000c0c0c04481485140c44401c401003071075110300051685400600c00c4140f800240000e84c91540384e40b11111074485408000100c103000c1d080a04501c050b80c1c0c00503607151207000d0550424040d03183c030801c4894034018402c120364010811020078508200d031b2170040e0340c0d85287c40195503c0045254666001c2d00d00080d08007003035088210002008400040c800e520b844000c440172410b9025070300c0d10749d0110800e036580d010341c5090a0380144259028860507100f071120006000c40140003186c40c9070340392103441c21070b041d070040c103840000002410310484c2d001000c0c0140c1400400300400028540c521100c19060590007a104001c0e00000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 802145917 1250 802144667 802144687
    0x1803120b0d0c1403030a0507150617030705010501050901060c1b120803072309040e0a0b0907030302070e010602120307020f0d020601090f021e031f0f050a140a0506 72
    0x1122900c03036940506407100d40701e030398144070804000520459618881c1038182141c1400c012081d1111191a030700c81c9401c00b80709640d084240f400c50b503241001940d90710000a00141d04c900f4074001c003502000a542c1d00d0200741015401d568058000d6400780308080c3c0108070b0b10380e00450660036180c010400012016a4245604031030b00154010200c0340c085203600400d0000ca1390085020b0fa0058417076401c2206484200103172a0004c100c60402407106100c000350900340780d0062804000214282d0346a0403465480c484015001e4031001076030b52040b401030082540400482d805400400c2d0f06d001e0942c9131560096640e452514950101c80f004404211981d0003049242d820f044a40103907600c60210700002907841c5000d208521b0550b051110000600c0c24500c00c9610300c8030700d01030341c0e00d20700040705985050343d102800001c0700e500301c91001e4510700006403005c0081c04136a900801c0c0c03240341c0001c1060142e0309400416030a040f49449a0060307079140c2c0001708807102680c03956114240d001d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 802147167 1250 802145917 802145921
    0x603100f0602030a1b020a0510050d0207050303040b010e2e08030d050a050c04030203120711060d05040203010c0306080a0f0204021c0b0a0911272d04180312 69
    0x54040c01a8895158020541d181c0110103800c52901560300d100900541444d101205100b945d0043d4000c40007500074030803401d02005d06030300101c4504215240480b000124030807a07004010a07540c5070004418002004003080100380100401c0c84403140ea4141010034581d01c1d0344c82d500104200703000402c4c00b0340804201d010f100c0140444401c0d00e03120071000c032544025140c00c07110804c480c2c0c07034040003940c0c0001a170280c506581e0050020540b212008550303243d107502c00102500d55608100f9810b41540e6490020301c1503800c031181c0460603041910601d4251105000200181130900f0000e01100b440014403001c2c454211030308850100d540d001040091142003c00700c2c02a60140340320210140c00d80103104c0090050750131300205603072213511104403402c0c1c080c0750314101c0c0c00b000041002d214180310508040c0c50103004400c005e1582000400c0401e141841d1244003880c02860003480355011040c05403c1e000b80c070244a500c000306a1000c9050000744001d0034080c0d529044009501d180e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 802148417 1250 802147167 802147169
    0x370e090f0405070b070b0a0605060a020d1d0d0f060b010c0b1909050d03090506131a070302040801020403110f03010c0e21010518060a1514061c061802070b06060310 72
    0x8050000ea0300c170440d00380b40c4403c81d000c039003001c007032410040006045c3c1031060445401c40304541c003070144610314040440300d000029004000b41101d80c2c442802da65140036881300304174461b4202600c0994640b401c00b0039607030300e85000d6050102a6800b04045901445c205078041565102d00c19203060900d840c2c00108100880649a80b042041141e041505540413840c42802103040307503040e6540001481440000510050010410010402144120f4070039160055010300f0058182034840480302d0880c3c202d6031082c4c851014403104007619003440c8054140c0c40340190020f000c2074a84800241c5910580f41000703014030032050440a450780100412400c80c250700000744a10700388205026070400751500c01c0c00b003a0042da000305044520341e108201402400d40c080e8440146008100d812110320083c115420100c10414504503c1d844000688100030644000070024102003010f401a4444a031403901030307104000e580c000c605920001940030b0000c03501983ea80ea00d921801c5207000007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 802149667 1250 802148417 802148429
    0x30409022a03030106170606071101020703050a0c23030c0f220204060e010512040b040c080f0703060b01050c0c0904020a0f03140c180a090602370e090f040507 70
    0x1c0440507401d04000031008604965140d03a034010340e03c2d44140200c2001206a0360b282e84108100140d50000384405400b0700c0c0550140140e504c1d46549854030781c240043c2140c1200c00280c1e000c81404800c40c079140740086112a0140e03000701c081c120010956990401a00c1c1748a050302144504003580c0384c41d000809035140481e078040900505e0301e2800650414040d0001151032040000681e5115009584a0603000b00b40308040d07032919243c40f098240041c00c03c0d01d1031071180c03e0228650303104202410803046131310004c5c40e0851071824601c045421000c50300e41080b20030440c0c02c10744c0c80300191a00005170300721200c0425032074034400160b10060035400900400c405110000902034000d21150b204407402e030a803000d030030a40e010085c4130094400c0102010807840702051529921364003002c00305102c1c403401032800065034083d06640290130312414644990f054a112540780190014000b02c071542044000854003600261250a0041070f90b408000b51000040c00d02c58100164030003010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 802150917 1250 802149667 802149727
    0x1d04080a0e031e07051e090a02030a021306021627020310170a0b010906050105030a020c0c1207050102011413031107031a0609060a031130010914070803040902 70
    0xc0f02d0342d5641e101c6440c0d114440c400c803500c000c3c295803644400721121000a009000881d2030b6154040b1500130341014054031881c50342880001950394500e0000d90140950ba0000c0151406040b0900c1c1c031200182c0000c6050000380080c1e106003007040b581a041c0c035003440c01c09616546c9074844206001142d0f8450f03da81348102d500700c04038903404130f5114007280c043d18034102c00f40e80b134030480f10646015214086c0096020000115408895070103400790a140c00142c9960420f000c1c0042ca183c5001c194118203600000c400b0805503070240f14100602c00000044d426525280ca0940b00c0905003000103000d12200603000203060780240200c3d0040c6602a1601820800200e070341566024101c4482d40100791000114030300349404c00121003281e84c0074919103d90104081030106115100d02080f00340300001d0390302c4a900d031954086140c980c400d8800014000c1d0a41490f201c00b07541102d03001e8040e08801024000100088101c9003034901d4034002581da140351502502d1440e01254411840762 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 802152167 1250 802150917 802150963
    0x619020c0d11010809030a0c0b150307090518060603070605031e0f0105040e0f0601270f1a090c0901050307050d0e0106050a0f0e0414030712091d04080a0e03 69
    0x485480042c2c0203129080e80c03020f000b6035130120525641c1c807404050328046503c03022500001030702c0800c1140d0001030910140014114000400c0c605500c0e9088100b43c9a00c400030800c0800d07500c0e150044030740e50b42005050a00f41000429140d551900802040081c00030008140c40f0b4140240e220b0b030320035034400c1040b07494282075030b5140700000c1c0595071190b0304102e044400a6000640544104210b50141c400c5034a041d180910301600c0d85c10b202d4a00c030303141c84140380880c090320988180ba071303640d0b00114150420481c84090702d10065111482801d864003842000110348050304d00300c00c020b09199940703840d050000d4400c2d006110721900ca035030910040041044c010b40001c02151015500f010040e500c48416001507109070003040400e10080001030b0214000002000f4140c2c031040035240742400706c2e1200c1d1404c082c8558040f000c911365040401a943c0740c80501130704d48a806880703510604060f900e21100f803051804060810403000381d03040041d5018010390703145013944030001c6014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 802153417 1250 802152167 802152173
    0x7030e030f07080d030e101505150301030b060604030f03050a02070906121b080325290c04050f0909070b031009110c071203020c130b030c030c0619020c0d 68
    0x184442e401401d1907402408910300c6070a02900466202c00c0e4518098450b00117062210742c02405000000e018600c1c9003038002540e910741c002c040b00c9e0b09103000000d40d034075030460400307480c5103001074501030042da020401000401ca20280c20308210342d0600d041c990b928110071040b440c010040e00841c00303480c80c0000010700b90240c0602141d00030b00ca01214000c1c8001111910030388002807088441642040100c250700d030200d24802440846401c0f00300d42c035007050ba140d1040340341d0300c0981c041c45003008408002080d07071a49045a40012198a4103181c5824000424460040100b030b450217080c401c0089035508406108080150158800d00c83c1c40c0d1400e40317007580c00b003c060300c2a0032149250a0702d8000c44010303801118680103204009101c420b01e41045c81c510100924800d07411401400c6c49020203607035035200d04850924020000c207a048501017010304000d00030701e403d481395100b014054129218802504c0c07203500745c00c0c482001c840304017100368241184d4005090348081c10036028010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 802154667 1250 802153417 802153423
    0xf210a02030a0e010504022214010e0702160506070803270313120f3903171e090d0524090a03022e0e06070813080d0207030e030f 57
    0x4a00a0b80d8020f011150007600b9542c03c8400940b806904068400801ea04064115600d0042e45078200341c002054900600c42d05155542030b00105070b40c0001c41c0c2845042641000207410a8032100c1041c0c1000d4a8203000445921599400411120010000803071b0600365617010b48400500342c1612181d046881407880d103e5100b101d080e6000000500007249140582550b01891980034207510740e81651601e5000c201002c40001000e8101c180c01000290a081480299290f00c680811055642585020130311548801c0209085080500858200c1c0304a030401e101640c01241d0907981d140131010100d82c500f4603008000d011440341080340e000003c1703580300c410300d809105030000449031514803d0035202c1081d403e001d0010b903c40d802c02030304011105a80f403640c0c01111059141c80f00c0016a070410f070703100002c40c140030383c11040c100024a900000241c0e400241081400b440214954400b803040c010b00304408016603000c20300008150203034201c4020060003c0031201c242c010031380441d075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 802155917 1250 802154667 802154671
    0xc0c020a08031606020d0227100e03031606020c071404050105011e03020a09120614090f0d080a091e060b0904031b030c080406030c0e10050f210a0203 66
    0x80906400c690000752001c01009441c034549803403038220114101615544081d41046086482481e030030800c22401d01010f800300c29000304c8190a82c14803101c001e04012010340603203040d0050000e0400c001c0300540e00801224418600c0c28400c0501ca82c890030004000d0059001d075940601c9084004078480501d000110101002105c0621a40ea00c84004555081070903040d05503904034242c201380000e0198025221045880c60030030303121030b540c00c0c0040f0010b450000503241c803940d64a6103502c4801d000c10b80c0c0e50103151a0b004140e0b0031a040c8105a8480c02500d062341080403c4000c1141c0030030341e03001482c04540010690780c50080440305c001010b0341d41d01080360800d00e40401d40d40b050809800b0f803403140f17405458565168040e40c20780042c04840e03483c200c040101900054002070000303c0548007801c05a038000524071015400981601640341c0c9692080341c4501400c4038a9610400b102d002d8421480103d4643e050084040c0400340c40362444104450324104000901950340e01540c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 802157167 1250 802155917 802155919
    0xa02010b130b06070f080f0406050c0f060f060607050c03012a08010303080c160f0b0a0c09030c06030b0a08031c05011707031410020304110120061909060c0c02 70
    0x8160480740c950510440700900b0086400400c144100c502103040b030380302c41c040940299052890541103940c1600306510a0700808007043d000328414003109020040380c003c0024040041c1410b0514009440c2007080080071039224010004d007803007c001e030034002c0c5003a1520240090051040b50036181403500038a5402004040c0c24030500480d1502c0749002c07078101d036055143c040d003a848501c0a1441540701010341d14484100d80a484002103107a540c2884040c000c0d8840180ca08001510809564601c01c2002c10841c1c2d00f102030010a0b03092000c001101d03030b40d04000540000c040702140c40d10082e680700340b5507400082000060b60125013103011003201a800104401e03030300c49000441c1c0c03841036184100540d114000c1880007906100b11026500b04640880c0c2e210b42440340300320140c0c4e0007114204c40500d02c05035111845c1d40c2040010710b9405581607110b000c82c4001e0a01642e540e0b006003200403801d001c1c50404071816440d4820580150065014041214004005403914102560803 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 802158273 1106 802157167 802157179
    0xa030b0607150e010506010309031706040605120304090f09030f081f03140c03010b1c08070204090624140f060d1517010507091701110a02010b 63
    0x1441842002c0d0003044042e149101c01c1d0a48201074881c13410726080c03030a6500040d81094410301c442100441c00c41d526507e907000a4040c00d0141d0003140c00204800d15441070480100040c4260707080072100f0305c40d40c051006041d04072148240040e0010351580d02c4440c2c1244100407498200c402e80d40002e4407180882010380840d041b50340100c0340030318045c01400320600c0500c0b81d82d030080c17412402080b554904001180c21480001c50300b55085414803105010004400c007500d8075203401920420006001d45010700080111141c0030110041c2102ea20a03c00b445040200580c2e501024840701c110000301803041c0c0c1d0b042c04442c650301036011b10089020286622405415100b0b00e8414604a46022410041305002c01104841c46c2d052038200640d142c0c0111654003200c01c0340c0d884401c4c071040000d40b50700414103a0701920140900094492407940d054000c104000011214 = true := by decide +kernel

theorem cover : BRFrame.Cov 801978417 802158273 := by
  have h0 := BRFrame.cov_init 801978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 801978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 801978417 ≤ n) (h2 : n < 802158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
