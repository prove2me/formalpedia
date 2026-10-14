-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3337
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:55.547533+00:00
-- url     : https://prove2.me/submissions/f23ad262-cf28-4f29-ac86-2316fa708f11

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 600000000 ≤ n < 600179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 600001250 1250 600000000 600000007
    0x4060c0813060b060405040f02131505030c070206091306050310090b010308030901110a090906150203120916300201020a0b070314010305160b03131106040b0703120b0105 75
    0x10465801e168000d058100340003044082400c008601e8a00c656080580c105051203c03940c02e0300390075001003100c002c080c0c0e94003000c165907403924040d504a40f2603442c0080c00c101301180030b201854002d41400741c0010552071621030041c0000c2c540b55003880c001c03080742d905c032030040201e454284081010355000003030500020301660784202c1ca200381400020700e00500440800d00190b004d40c41140070507228180c4540c3d03454040d80140c940c0107180301d01d8214a0078404081500c040c44190041c6103c0c1c540c00542c00d050b00d40c00542101c1000400b10589071280103100c5902c00f00208c80c0600034200d42c8486161503188885074060380d9412802c241940c40070f2541c41c0c1c01070741d00003007a11040740c0064054501d40c56a000440241286140401030024a640048107212011400812a81c1c00c00301c1031044554a44081850b070104650131600004040300480102d2031251f241c40394298010600340c5400d4a603819581180c201e00d030160000351103c50300c41c990780024440d42000b10401d083c410309 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 600002500 1250 600001250 600001261
    0x4050a080f0d030e0c0105030a0e010e0625051c0e060109090311071512060302090c0417061b0d2910031e0b01110f250b221d04060c08 59
    0x5d89082480306a4104900040014036203940b660000344240511002070240c544c40c0c1044942d1403d081d81c00310b080d020440c5840440d900416119241d290306a205e103400d000700505240c18007400c00c01c0501c40c00d03444513504450703500e040c4002c0d03000e045910000504c0e06028100141100d0f030b4680794000e1580607200a100100324604040b4015802e440d00301d448180d840c4854000d03000c13591001790841200000c0c02032074285500600103403000b480110340c01c18000f48806030344000660f58240c00510940300042080e035508000c0400400c080408288000c0011000140c041c0d841d81e800000301d02c0450f034403803515141381261004102458180310745646d2542031000001e020144078006540d030361440d082c590084070303a840144451801d07a040442c1003199103032101d034170801c0565404002d19400d042e00e20036103180c200340c0d0b0381c9c00052814004907100301c0c002c0b28003640403501e040c1282e08001030381d00344108014500c400744106100e21800e0030315094080d145112809014041c882e4200324 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 600003750 1250 600002500 600002503
    0x21c1205040f120803040b04021c05030403110315010b030c041d091203160c0f080307030f0f141602070824011406090f060408030a050301080606010804020102100c0504050a080f0d030e 81
    0xd806c40c3d08410b1043c0036132614800901c0840d1045100d8003081400d003016400d000300031000e0400c40340a07402040d40b60841c01c0c1016241c2c1c1401460340100b20704440140420742080c0701031a40641c003010014646034a5408482c540b50905245800000c48002081a2080e040c0310100350b2980485110b030950a090441d0003043e8081c808540821004e083e004051200b9200c0b0040300c6500030708005c2d601d0a1903000100034024003001c2003085410010000110480e52086402a5814440184298841d00d41071001e501400d070004c4114466004042a046030a0003406d0000800e0280e15200c4a0b00c1c007a40461048142c4c007200c1d50107056881a18240c5586080f200340703800403076661702e500350a0b10000d200340c01b858202001900c0049011500385422030019816110484100c549540c3e4200044a402c142210001d005030480400d41c0c0e1965000e0b00910202802414041d0800f0307110340200d40005c85542c01281a603125582d00001d0b1013041c0044142d402a030b00d4280724a00c0300410b8103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 600005000 1250 600003750 600003757
    0xe010204170f0106260705040f0b21070b0313020a061101050c09010c12110d0c0b0a0b03150a09081303110906010f0c06021209010234021c1205040f1208 67
    0x42c0c5003d0001c103c290a20701081c0300031006800024020000427100d8280300c0018051980780a00a1403040c0c00c0c1c40c1c00003050301c02c046140101c10020860745003054071408580c0c10251001c450f8900030607103c001a030301c9110600c050945a0360f010403007040343c84102e0945902916552641400308082161660b005200805030350700700402180840b403180c012114800d015104581c4c034024214580380482d801220700c0070040c05294044d1407070706d402c01351200301c4404003d10341c0e15500241d5050140c00c4034840d00d0b680410b09840016000d100340d166030031103600c00701600c040c2d004421340a02c04c000c000751203010191000e50ba400118505180064200125142c07200184820f50026030104142d44d012a41d840d50150002569420649101800f03504030045000300b1505954007642100346200f14014000d40780440c03024560303000c2d000d000311030070b83d1850f118003196049000e0f808510028410b40c503030007a90361801e030350f02d10b0601c400800ba50b054020141c1c41808640507808501800c065 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 600006250 1250 600005000 600005039
    0x919060212030408070b0f18010b092205010207030c0210080f0402041d0a0606150807051e0d0203040302070303092c070201090c0902070605070305010806070309060e010204170f0106 80
    0xe40d507500c072404c14480e1800f82800c0100417130780042c02c05c4500380c020f800e004c3c025a1028450103c51280444039800d86a8000700070381c204401c40c0003e00e00c0034980e89900d0644002c00340902103010300791034041c01d81c0e00c000d605402080d2404070755000c50401030a02e510b1f0703242c6850036903031908116031103403400c010180002c1e00c220744448091103540088100744100d00310301e40484821107030520f004c0c03025040c1032080c0c0e6007440c21080075050b250301403c00700c0d00c614515903800c1d142c9800b010120b2408000c0d03020450040200b03208142d0201b009200030f50280d4003d400078014985549002480c10f020740d0030003008150000c01e1503900e0614407001140d5510081508041c9540d0014100d00500c91103401400c51125041c0004800d0310950007071140a0180c4418400b0b50341d003003410390994000780325521180d030080c3d000600643c400c0d8405d0003018421032010503400114413400c2d0030ba03003141d0030050101500d50801c0e450380e0420422200038041d40c0000b808031030b1500c1c04c41c55484d070f00082c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 600007500 1250 600006250 600006283
    0x50a1403060f0405191104050c120106030903050f0d090210050a0c03050c160f060305060301090f0f020301150b040524220306060e0118060506251709190602 69
    0x8201000f10500001021042c1c41c912460545141d050001b0400a26200c1c140198900004602c2039201c213800c0b0b032505e804691440000c6d0b468400110024074800d24190200407041c080c0d038030300c803070b001000b07024141c1d000002050348003281c0100518100d40342c05002c14440300704255044140c100b141d000000c1d406080c525103450324400070900f440c4a6100000b1820010b000c013090004640d10f015080d103103079580401c019502d40d03060508a82800303801401007400c0030030220010318000800c86c1c0c900d20240011611151202000182c5005070704000040440800c00703001908140b1008204030301d1400c008030150701380e881d80303108921410710004e1005003c0c10b020000d210074580420003c43d80000e0801a007039a5115032802400d00380608a10040506805001802640554030990b20000c00c0c80e850103006074406254545040c000f1a03400590340070140c08034440105547e091105452100e550354289020441c4040c1c1180344880c4602c0a4001404155030002d203d0001035042c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 600008750 1250 600007500 600007531
    0x5090d120f11030f0a05090309040f0b040f0606110601350604120e0117010b09031f0605030717070b030601120f090b062407140703030801050a140306 66
    0x1009001d14051610a10342461184101a90514010340c401c0040b12003141990300c03403000940c00d646046e40d0321f07201c1c0d500911659002d4901b82c0c0c4403004400340305400003022031100010505a030180000c2c500b00707913559030741005065001181d849070713107260703c014004560602c0d604d85003c42d40c0ca5107019410a5034080a4400e0011900210007006070008949642c90b0600c1d260344407485507241140020310a042c24130300c0b54000c1402035006441d03010a0f400b16800d000c041d4140b6001000b1071030740340c03140e40741d008040c030f030b4411030700901c40301b40d60f0003140c02820030b0107141c81e000151380a00c41c103040c402244040d070200818603d0507150343c2603101d9076a40715400126030340e46212081c0415503180529145400e85994002200c40344504c003190482d9540e2400c0000409801c1c64045411041c4c04c68102c0c250036850003003540c02c1c8210044100081c816000f0341c5031000e00c2c1c0048011810034001400203241400c0e40c0801818415060030f0460440000700b6280c001c05844a03480c0a0920b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 600010000 1250 600008750 600008777
    0x70f031404140a0506090d02010c021908010609050702030708120a0902130c110105060d170f030106080a0612111003110309100b0d05250e0a09031205090d 68
    0x35440e410302440c406652035201c644a90300803400c0480c1500d0648101000c2000141900f44201034551086000309481c080250076001943c8c04940d04004a92119010b20040f500ca0b44c803a10000103000d945000150340382c2007030f44810440700e010b060201994020f0220400048a42d012034250506c45050840e80b40c958900400280c0000c24000f94002c0340c00c41e00c0110f101c03a6600250408445541e55a896900034a4941c01c9480580d801c49c1c11a03078030559103011a01440281d9100c5140d41d803280c2c6050340e11102c115142d00280c2054000481c1c110a03c914034586001d01006403004c0002c052040f8056590034030f100e050030765840e00480d03621100014603400396002243d440218010155a0715201e20040d03150718030740c80c8820407185414814080340c28500061408540d01000803c2d203140c103600204400c40d441d1a0007041481c5105000ca42c011004000a00649004002040c20015454044c4c0601c2c030080d4103c00a624120401124240c0056100702c01c8003141062100000300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 600011250 1250 600010000 600010007
    0x80a020304050a090903030b0d031d030f010507030917090603280c030c140c071221031b111e0304050406030b0103021207031a06040603200910050105070f03 69
    0x4903400b1551100005000041d03080c0e8075085059502e12a660420441d0008000c000d2070408002d4041c1c000f0380c48180c0440d80ca4050f00201d160750310010202c031070b20a00506960f0030754031700725200400280c90700050410030890b201a6a10002c105807000d04083c40f4502042640c000280001003c06240900600c00400901400c240e800205018802c4440003070005d0060b1a20095420009208003005007003030003c0d005650706240c4280141441c10710b4055a100e408001030419103841d01c136001541c1f143c109500e240d034005c000742c1e10301107004030042d0f26100c01d410b0b4504041052049030441002c2c080d401007001e145411051505080302494040c0e0b01e0b1560244c0e030042c5070050314004c800b00510241032511812a4400c0f106c8a60809108841c1e0b0780b0341c401c601c0010001075107900707800100c0c080800300540c403200103000000e6a81c3d50b5210031f4040c07004000100c2e0290f22124a040031340c2032544140713a03c00d0340180100702e00c503e8900024480d00c01ca1901030121203491070401c082520 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 600012500 1250 600011250 600011257
    0xe09070306050303070c030312020906070f020a0b03090d0f0804030c0b070905030a06290303030411040f090f05010506010806031504051e0f19020f06070510020417150112080a0203 79
    0x83d0440351210711615020000c1a050300096012130810740d800311900301113008588911102900803801c00c22181d0310204001d01061040341c2c0514200b0001c641042508040c2d40304801ea40001d02502c1d08a0300013505a500007072030712040201d00400c102c0460f0b0414001001103901850300c044a40c3d414908480c640483c0d044281c1c107003e0140c7d03074014070429820070a201c00d000303946100030914440008400320480720240d034164100340001400b0030020759034004491f20141c404680d08041c1c5108404547c580e8000b00c035800081c000d1107007409000d12074694440d000b030808400b40d00700440000e96403200841140325003441d00f40000d0401600b808061120040540c21190764089a0001600c80a0013014103200d440f44c2011204548240d050400d4125000750031466a1000c40d0240700030341e808644c0541b071600c6503c007642214101d910007040240001d400d44862941c02c030303107400d040240c0c005c0e201c106001840700500000c08417044e0403640903030225805a40d1952800160304500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 600013750 1250 600012500 600012509
    0x114090d050d0906020601050d0309060f0c061e0b0906061b010e0a0b01080d020303040c05101e05180909102a0203041508090d2001060b040e0f01060e09070306 70
    0x40c0c0c10010048a0300080c06800f51390064081c1c0d4084d80c1c03114144100364111100240c0054051481002901e000f021000c4900c90300f1b1400c06103d0300507803181010b490b034100b0844000440c9000700c1e05104007a1148034071030902103c80b20340e1818540005411401042003000c1480e0207400c2c404900ea6003507000c0804903508a042d1540354015040c0780300590824801c3c103c090007103458407003c0034400f0048a10440e0301a205d554494203040512400002c1c6012003820310903000b00c0403031050300741c0300b13003200521555070340c280d60f81c1c940c41c000040001d040c00d181d1302078420001846140040400d000000c20300c040c5000404241155111030401c0748170b00400030011041040141d07180e80400100306032018410140c112850308101150007000032100c0c110f0726008444a21607030341c0704080b517082046403c43c4180d44503d40c1c1701c015003102d00c564040c002000d0b0022b0104442800e503440e09034401c0008400100300d62620340040c021212100142d0b00c01c0d00c410300000e84150003a4020300182 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 600015000 1250 600013750 600013753
    0x91e100e010f0e010806090703110f0306040506100b251112061b0909070c03050c07090209031908030c0c1e0a02090f07090501050706060509040c140f0114090d05 71
    0x75656071800092600b182e0140600c01c0c121200046108540014914001d0708407000904083d0300e19224202d0400d0a8440c19610002d20b40307200b13215590410205000c0c81c0218082d2045060030a0b80303012100301540a80b2800c8028008618001035400071904000035116000180c401d0500d8010a8400000b00a076844000c5901219401800140b01c6200c0c0c0301c0c0051548440300d0448504105024404c0303400d501844c40400603030440d10410051002074441c1c20180e06111155038034504008c100c6d0410040c1d42c2e80400c03c10100d103010416441c40344070101200f856410241c84803100c0e444002d092010580e000103514844800802c4041103005080400055104049004a40360160401c1c107034441c40e05440402d40c40540d0100e0701d401240c29484446101d8600310040d40c66420481c1c040d11601e640d61701c0051036482c1c00c011244034a20828581100c0381c1071590076024203941c5044280a2402120114007503600480ca07004000b13012801542c8130946000001d00b064910340d0001e025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 600016250 1250 600015000 600015029
    0x618130204060f030b070801050d060221010816050613050d0c05131a040b01020c04090501090609030917030c060c0c1006060e12010b0d030305061c1a06091e10 70
    0x1000f0081030400c1502e01c150303100585c0340c0b204072084420722020700507580d20140200c0c074000010604d038014210142904640d000030245010408504142607010b4200d07a040100c0052010190010103406050212299411f150880015929200e110301880c2c1c050140803106009100c14515900c1c000c14004001450030600000c031900601045d80c004000720600440744010b6152601132000174a506a00800c4054021130400001d03007003030305040c0d90f5556154511004103a49025100049000384c0f92513184078a810320382a80144c0c0b81d0309490782d0790803e21021000d11030105d2441e03000a00030440e541c960000c0d510480c1000207141d0030301911840d210380050041d410400e0388001c00e0f0220391002041c10740f040f02c0c43c2078a106050340c5501904440400002a00985c800c0f50445000303011490445080d09071040c030405400e81c213032691420f00a00000d427004500c080341e480b620a81d03803074000f0b0911960324a0316078200481c100031141d0150000c0c0c103a00c41d0610b2a0b0041c02c0c03000d0b01007074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 600017500 1250 600016250 600016259
    0xf120c09091204090606030c170f07051201031a06030a1a04081224040b09041707080d0209040501060f3c030e01050a02091e130906050a0b09061813020406 68
    0x40101b0b00c1911b0200381403109504083e406002058641440d007010409250b07540380803803d40c801c00426a0091160a01c030940780d4040d0f41030014083e40c410b0345401403402c0b030b01c1146100494000d0801d03202e1740c485040100005d481000e0650107240303000b503844a5444038500020b05001d0041141911100402005920261211034800511100c140c56651440c8182448181c0303102c3d015040d0400c40b120701160000d2032111200950640e000c62450034003140e80d6402c41164400c3c101c0c0b21300c1b03e0300811520014a000e2084500400050510413040560558080c00003003a0005080a80e9902071402c099081d040402e62001410b19060076481107181c14054010000751107403440c950319040002e0061847c5100b11000084001c0050300080c0d445440c11150300c00340c0002c0c540040400351101c0c4c0c2000d00c0e02136a0b522a2007040003017101e10b48606800d08881108465600c41ca09050074801c85440e0b07131041a404030149800b1351440d0743d950031520395030b51002030001d4100b454844000f5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 600018750 1250 600017500 600017519
    0x1101021c0c0b010608090d050904180f03030509010605100e191d102403020c0105150f09061f03060314011b08040c050d021801140f120c09091204 64
    0x1240c520a884400b50303a621844100c03000303401214207811680c407842111124600400140007845002080415a0842610062070305203140300c049a07014a101450401c064060040c0e907071110001c002000340d03070310300000641440c840c94400c400384014a82d0003805620b640d2032041d1b80a41d02450312710550b698481080b07205c00441003000c65911944045489400d80040e2001140e4510044a0005071015440d100030020702a0640c140f40c0d081100b050b006c1e0081c000e4520078a00c1d80f00040c2c034400d40e03074280082c40300c5003d05c07031f44a10095400c00c11035039a400361441c3d140700000540400d040c600042500100195000603018001d100b0b40200003a2054000e441c4501103046000680b50381501c00f640d480405450090040c280d0b083c2c24086400c115a202014600042403501d514440401d6513403488002c0c5c10100c41c25a240104030a607007806602d840d0070240c1591128040500c107012584c49121420b200c40c8030f440d01c000481c40c040010042c940e950401501c5c101d649940c0c900d40d44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 600020000 1250 600018750 600018767
    0x90712110a0f02010209090c0a11011401090f0e0d05090409081204020a060903030504090f020d0c03140108160504050411130e0106050105030c1e0d15030c090b06071101021c 76
    0x10000071070b802c1495081e00e1060080d03844d60803014007038030781c0c50f110006800c401d504218410402c20450500140540f1001d000b03d0b01101d600791000001941420ba07014190741b0780e40e1212a94a0802c0c031b8040f00400c00251403401c0040c02c0c58119180c4030f06400040c094001307008042e11940010403c50f0341031014003a202e01aa10845160000701e40e070f801c0a45014005100190215006010800800601d40c200c602003005021005280040c000e10240132070318141c2401c000245d58100c11802500030209085c0901003100040c60a034600b0140246090028040e69000300d0711b5a012404100c0300003030360b4442210041501d8404031104441100500003010300300002c2d820b080700000c0b10750165048038040d840c20700006140514aa42244840b2100c083c11030310088104014101c900452042407130b140142810425054914144004145080d8001c000c10502e405500034556036200c0c2200c803400d5000c65101018000040140d00300150003449100090822021850301c13944214113 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 600021250 1250 600020000 600020017
    0x1812080306042313050319080709210201051c0221010501091d0402190b070525061b1a060102061509060d020d0f080c0d140909071211 59
    0x2005401c1c1c006100720003180c07031006440164000c03c40800c0c1d8501c910003e030100a40210205d13450510440e072040550196466035000241a8000340045c19611040303d900800c0800285007408402d03004000c1c2c0520301c004001e052080c00079000741d4001c201c103c03079100440211811074030768218400758a0340d0410307d1182d20740c91501d44000b1400c0d40c042c00144040d11000412594005401304071aa00b060001d44160790200c0c45010302c0342d000d181c0c0c6030320401504c0044250b9496101030310b4001c2c64070150240740c2070361100c1010781c000c1c400440c4030070104807001c0e4039285060400502288441816004000d00071049190007141080148022540505020b80c02c6580503642c2682181d030004800c10f41c250b01c05080001b20b05035203000541d041c0704c0707400141042c048014030f0380d0b0032802c0146c10208507004c0c0b40106400080340c0e014408412402c0480c2030400c080e0701204a1741e0b10b41e200703084245100d91070b8500800c11092003446000200d54210b030f01044001180080b84885030000b060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 600022500 1250 600021250 600021259
    0x507090513150b1602030a122003030a05041e06021905270a0e0f0601140309062205010c032f09040c1814011209050c011812080306 58
    0x1160310352086120b2102110007114440864a003800343c3e503e0554400700000100f403843e401c00d60b02595040c40f520304980d1042c440500800000d100c094880c0000030480340c2d0304190304407a05d00240005c4112940301c0c440180005050b82c0351702c0c1a2620125400058140400d01a406001c0008940c0100705007805080003540055080701c040b40c02d4411091500e41c008602550000800301c4004540c010710340c01440d480c8156103807184001814401c0321015104480c000c00c4c0304195802007201e15a13041d40d200490725520b00b1142050b03807031201503c1102901800303c0101b07511103542c5ca0001c101b81d409002400b107950103200c018080c00c5500d02c054400203408000c100040704001d221000c0414002e0020b042c040d940741000010304442c43e10740244104d0300440d04c0010710f4181840c02a10180c0c0d400614000702000050256460844e04074500f8a00319522012900000b821141c0b4442440c242903a50380b000e40d50441250300d80d0280e8040301c94000c210041045080185200351420b94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 600023750 1250 600022500 600022519
    0xb07030f020309030d0c03060b12160305010b0322170a020c01020f0c0910050a1206050a0c120b0d02040507270b1e27091509011404060905070905 64
    0x10103080891200391000c1046503c1045826003e400682000c0a4100f0f03e080000e945995580d45005652111090201d4a07658004000084480c0c44100c4401e4040d072804000c0c80d0f040c10b52401c05444050174204c0d124029689000d0390000a68245010950192444000d01e03040403a00a1941224000002602440d047c00a0b82c2d4030002c0c0c502040c200da640180320014000040c00041c9901900c42d101d0103680c00070100e0309071500d11030740c00140703181d80072060301d10b549041040c1102c4014004404040c00c0c14480081580c0c84034540103c04551b140006041c2c034a0800920300c095130200007500281030804220710260484160341c02c071805001c183c10301103040707944070001951178000d42031012400d00c5038100c20b1071040440110402e201c4032807890014030052280303141c540c501070714080080c040711114030380c1040342d02250400243c0c207500030321002c0f076000151006814003d0112440441d66100d01d140d40702d8010b28020a0300d11070800c0070b03040056008010341c442d401464014500ca0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 600025000 1250 600023750 600023771
    0x60102060708070c0c0f0b0705160b030c160b041b050f060a0809100e0d120b0f01120b0d05061f14040f0209061206040e010204050d0807031b0b0703 65
    0x4614940706180654951205582c2c1c580182c4040303a90b0039080da1425001c00000c600c0c403101c0c10910019091501c00d844c1c40c4c40c40c0b481c0c82031800200c01c0c24103c1e101100c1e9406c0180400741c005582d08400c984801548546401512040102041c0710244c10000c5503018041840030f10300858620841e040c84142045440304107010400900007036640d003200f8200220344040340710f86c00043c3c0240c05034050b03442412205c2e1202044e141441082aa1900f0480c1c1107141a50040443c00c540c80b100d91080c000c6020403000981030204c441107150500c41741c8003c0082520b1990f00c0182035034001080c6070241c50321410926a81c3c0c00031581a400e01507103a90a010711201e0701ca0b00000c4980b01a01c840301c1e03111100510014140f00702881e101550240310100c1213a03101801703000700d034401c4c01e010324240c54008201300c240e40d89801c0c0c00300d140e48104824003da171035040e03440c00c9083e0031908581e5600c03510b01d82180e4850800d0715031381d84a00e0419002c0200034081c2d41c1ca0380035117000d603001c1c02000c109 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 600026250 1250 600025000 600025003
    0x705150a0608010e0334051606092103021e0a1101020f07061b08030a020d050c0c0723090403090e100e010e091c090501090b04030c06050c030d06060c0209060102 71
    0x64130307091001e507106004040b00c480b400c04030f02d5025060b5004036079403082d0307034058010700345040c820854070703900103650300d0702d0b003580c0840568018200d034981011541d04c1e0200f144100c1550390411610982205050740515000704140700705c102441480ca92807244178503071603840340700d000f00c211078140e4001d911000d03c0d0701c0091078100080740c180142884510300b00040c0e034200c0d0143c01c6054480901c1c05c140c40842c5844015600c90900e181c1c015075210302229401040741c030014803030404490309010303000d41d0300302c00142c0304259060b00240320710645006000301c44803c9400c41d602d6200b4541d1081004065000c41c8403000c450302001c1c1034071243c481030303844810800c10340558500070551200400c0680d8071a0039040d0440d1003c2c09071901e5043c074008030b0000c90f04400c0f0720b2000c100b690358100b1065a1058203400101a00400141410305580c2c445644813032a100d000c04000d00482c1c10001c40a040c030841d1901703070070350101304031195442401400d02000c4172800e030310507000380d000a20700c1d500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 600027500 1250 600026250 600026261
    0x60c140f090405090c150a02210306090f011a090a150306060210050c031b070f1b05180a0905191506050d030c020114070b09030c0d1d0103110705150a060801 69
    0x174001d04040d04001001c2c070203c1960031418104003140b09003451848000d00e0310b011890843c01e5158650b640340703000f4061006d01c0704040c00e450000070384403004204005149065940090511610030341c0c0d50802d8000546a034410340010012030095201006600c1d019441a001c480c40ca80036140d4440400481008691048440c896901802c0000403610458680d00d1009038011000d031a04285075900c88018101c00c0d29030031110303503a0422800300004400c0580304010300e000c403400c101350403640310300156035000a0a0f404590380c881c20014104441444a08001007208041900d45845814484ca5503107d06190010346441c001010845040c08a40325070442c0d05070300d031480c03e1403caa004440c0201e07591406154544188a42400203407900c2085000b000801c4c02107403188c0b0310004481c104001c9141d0340050280c00c044407000d8810521075804604003d09000800724030b8600c0512103442400c10060090040907001250104609801409101c0d051010824240c0f54014907080f2078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 600028750 1250 600027500 600027523
    0x3090d0801052b03090314070302210a061d1515041a09041b060c210f05130308030c0705100509070e180d020f010c03050c0304060c140f09040509 64
    0x10ba07420401e0b07603c1100c452045070741911070300e0142d001ca036a079185c1e204598038010601c0501d4000d01410015481c10800e2801081e1030491034034400340c032189003a640d80085200040c40c1075101c03201a20016651680e0035148070311141910507904104010b02d8076003d084407005085549420703602032a060500c140c01c0d0001c1d190003818454005c070700c10490b4101c4014400c8a94894151a1022201d15450305900402041c0c4078005030440c42e140c600003a40080f020b0703907416034964030150216544111481d429000ca401d040c0c0c1e5032040c0000ca15800e02c40c43e04050a080c030000188640d41001100400d02180100301b0780e01c0b0b80408054940684030290340314055036000000502c00280d0910305660030180300c1c14001d101c60203003003400e8200a1003080d03034005600000e00307245c8514800e00580c40c4500c100d20f0b08118071710342410905900c0c0001b9001078a525039881440c600140500f05517881d950040e100c0c0707500c5290121011455074002d01c0180d004600300300105020301c8002407507035500f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 600030000 1250 600028750 600028789
    0x1c080606030411040603080a09030302120306030627070f031407060909110712030903082a03130c0f15050309100c02030d020307080109290906030a0803090d080105 72
    0x140c407103465035000448403003d8190f0241d92500c1c008000740c0b0180052881500d65291409094514100a81003d0200d413081e40b811100704100215a81c0201d156035101081c0c0341c2c10403074005400a404548014154000306503c2455004140114030085035011248100039160f662480d108415489186522805010847c140303420301c0340000c0d607042032000850454040d4280b90560729001c440c80a00d510706030100341c6d01c500c04010b041d80540265440000e1400303400c00032140d0002d8072908141008099503604012008c1800ba585507404084490340102700c4409a60b101d01c01c20311036a01c41d00c03d55030402144014030310320340c0c001c1055074071a0b020000070345a800c03003401e0f241001c0d00001030301001f140003c00a15400b46254400395001c1c24072039840340d47c40d60410a150044450140300754200c0103d410b042012001c3d0445d0407060070b0303410365440250352a0302e0003282c50095401402481180040100081000001065044c1c01d80303554840c64075903030f41c20500c04d486c400c48403c030488 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 600031250 1250 600030000 600030007
    0xf14040c02061602101d0d09150518040e101803090b0a110706030903030b06032a0405040c02100f0b10030903020c30012c0705040c021c080606 63
    0x601403c092040c4400d00c50040c0c030641a0b017100c0d9030040310301d00c84458a80020781510b0300316a40b0b0400141c06910401e007040442e071414480301e2030030a0305688084080043c00a1050b540452102c0b044640e8000031b031041c0300086101e041c2c1600c030000b80010000491034140102e008480350582c2d002425010344403041c0d414100341d0b00d00c0c1c480d4130050740c590130702c010900c0390100c1c00003c104850082c0030a0350006604059403400a055540d48854030307200310400c0c4180540c95400700441201d4000c00c0c4e070f005140c0201d60b4441c00e92802603038003440e4020324281042d03c0d03c1e500440c2c04003240c19004000c128550070100490115030b450080c01e5040210514041070180c00307540b04ca42d03146d020340121211013211200181d54440f1f03803403154542c20030644030103418a1400c803090f5809425035000b80a4900e10340a00d00b40025005050002541c040460038049034051010310094800030b84140800841c81078040d54030340f0728681c0d030b44420281d00720b100340481c070462905000c1d6a0041c0340d64903 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 600032500 1250 600031250 600031261
    0x4050c1e13020c07030c081006060909020a020111220e0403050403030f2a051b01020606060d0b0d08040509011203050a030c02150906100f14040e12040f14040c0206 72
    0x70020303010030503103a00d5075081000b0050500100003820081d440740032000c1a0300e0401c540039061049805c2e6020388241014414040c29410401210690359a07850068449664020403409014880c0641c80c0c6450300240e5021000780b00301c45102844074600c1400d81d410741d110341c00030310018211800741c0011401d10062001034401c07400b00094a0403890620086818405d139903901d2600b070012000781003015100002040028041403010110600000003000b0003040080d44801d001004540b141000080301c114104203584002102400a01900d030703070070a68944031240c2d03407050040c54030511002000141080b04e0f0446654441d0b4156901070402113603403010341c080c4c404e02c4074840c00c0d4011010b204160b44100d01c2d00302d214a040b44000c103454148201515400012a04242a41250840300b88049440826001c030700c1103090302c001402814202d42c5034240286059500d1584100140000d91403003048c5c00c64080c0c0301200b210382248041a001c01040312a01c682038005030304010006070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 600033750 1250 600032500 600032509
    0x5011b1707080c060108100b0d02010903030e04020d020c10060b04030f030c0f021c150b0306040b0a021201060c020907080f0a0c021f050a0605060c0a110a09060303020604050c1e 78
    0x341581c814050315003400d032a1001142444c209030031003822540300580158500340385002c1c1c0542d901054511104112301600000c29088144c04041c05006108000b4800c039102c550464501c40c0300b00c1d00840d1208000d05220b6215050301e044046010b040002c0031640e0a0340f00202d400b16030f032200343c00507050745a039000c0d5004cc4400400742d0715801e80c03218a40260b100d0002070300c0c209a14040c01c8403452102e140100a0070110000e10810318544191030103541c400040c2a6080751b04010303100c1295480704d6540000e80300e0a1440030416010000000c0d0003504402d44040c1070b48210341082550351501d20031100c8800c112112140c9140046c0030901c00803065011001800300c1d0300c10b070340000010b0b0041014035007440c6004100c803582c9004000c540ba9507841400007601003100c1c8a494546c8804403d41e81e4442580094182082380304140c0c3c103031b565581544014910b0f0710081c01142c0d82d80c14042d49500d000c0b9030030f680034020001450110702e000100c9001030801e400034086000b1101d001e10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 600035000 1250 600033750 600033757
    0x1b11100c230702040f0506010c0206090604090903050301170615010c02012c090108010513150603020310021803010b060a052a060702070e061f020c0a0e0105011b17 72
    0x36020701619001d148070110004200380d10201c034440c0240e90b01c94480c41400112152800030041680ca40303000d00050340c1c1d101806c45142a011501d80b5162005000050350903c21503002200c80d80c9050341e46010150010080c6048480d100c08526000d9043c540c02e613142c101c102c8440f01d01a00910096000350700a0718505400303401890007600940c01140c54042d50501100789022001c06058054824a040818540580350040080c000c60a100c03001c400c000710b00c00c0c0c00030400d030b0116100c0070f50040594084401190024202d40c803080c05800000c000b5030020140d6411100108050942418140500d000341a400780a0380e02e1700304030200860b0a508402c603035002583c580b0707540115030380e003910005c03a40d00a03000150501b4140b02c90007a1074240590301050420300c50038108003440e40c0c1e03540d55003c14440d40c000d4031407141492400701e042280003a005507010803508400b140f0b0743c00049c0110b043c0c500a072070380c0c11500707100070785022070001c0544010150000f40c00010281500c15000c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 600036250 1250 600035000 600035021
    0x1110a033c03050907050a0e1839180c0315120c010201060e040305120601090305011e050c1c2007051f0603021806060d020d1b1110 58
    0x70540c03800240c1e0446803100841d115141d00094540702400154142440200c1c0180b50849034120070310725000c490610424000e000012040e014083c0200514050000004401401e80c0d0301e04038210500d00451b01c4070200c1007880340d01280520400d242d00b000503140b900c800f03041c030598030303d03a0b0392448582c0d0303503440280600241004407441c4a81901e42c9645d20000303200410141941071980b5000a0845405601c041044807100013880040f07508941250b500b400c140034080115513402c001079032050660b40c401032166291405c2c80b40910305140074960110036103a018840d54441021400700f500648420b03131403842d0481c15000c0f20360029400103140c4071030441102c0032400f1040845c07419070454141583c094010940c1400c1400c08107540c00501001c0c41e90400019007103402103081541403140d00ca140301c6010021500d16a260829503204504091041d50340324141380030704002d86140000c4071170744441480d00d84101405203203003160f81ca4540d4001c00b041071100990313a0107460444e14 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 600037500 1250 600036250 600036317
    0x180507020606130f1a0405160504090f091707120806100e0a0e07020703060501060306152105010b0c06060414160c050304060305090d02010b0f010f0504050303070b0601110a03 77
    0x400c8201d822074010300c080c0c44144400e026172004980c061000341c6000a0400d03d14800950b1401003068002055505842c054400010350f10480130340400100303031000015107041b0b066095140403048610081c81c5651198508601a60404105440b01441624a141d01c561490703241c142852040541c1200741e40c00a0041e0291036032409003112100302501c04100581000c60184240481401401d00400c0a0302c0c040202c00c1c50b000b45c040000001592070fa0401981d040e42d000c120205c0b0003080c00c00114801d0401180d65140514000795000c152a11064050400040d1031450248102204420008503140c00341d620305140011801c1e100462605021405000c0c2d80410f40410150000d0121610000303182d04164100c0e0345840c038510040411681485800300790b81d1a031040904040d40282000741c1c039950546000c0c1d0320742c002d542129416200114200b42440803611749280038030720a0701d03010008000814071540b2040340e5000035004c95010074000c11000603614241c03c030640d4546 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 600038750 1250 600037500 600037511
    0x150a0e1306120c080a020d061a120c03010c1b020d02030f0a0c05041b140a0c1e0b0c0301030f0803060d02040216020f10020c120102040b031018050702060613 69
    0x20300a040340c40581007000c904440074694410803000741600c0028000100040c5500030f826030006441108803e80203114503142c141049903070044440d60f0040d5200103140c5044200c004242036980c003207628620348290701707104205103040d020340021303507603401ca1032581f540491158003070000005100500700d805206010f07024070b03c0c1d0814480c200d501d030f11825101c0c1001346420300b00002c1d525185d2107a925102c04c80100003030300c0d4004070030a220610a2400c9502c1d08541d00c8141c400f902c0d008400741100110142c501f000c019071030552005e40c0c1c459004201c1ca80c5500300a92041d0009000003070207c0c500404880105800501555002d00d0081001d0707030311401e65002c517059800001d0450640c0e648000f60b00304624003076040c0a0001015615200b00300600d0340c0082d528415921840d018100b07416030000d88008c29011200a13001141c01a5600e0800c800c42f400c40241900c11b0030b90243c414447c1c280180b20902640c0d000700c400da0b00414887c1c841000f040301000d030000c105500d055440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 600040000 1250 600038750 600038779
    0x114010207030b0c0702040c0f0c030c020a080a05030c010606050a0c06090501090c030809090f100302040e0f07031a0a02041206020306010c0501290603040302250f0e090c150a0e 78
    0x80c103c0a100c1d05030301d8a25a1194045c0c4103020555045141d40001d02031314508100340c540d80a00b0240c00075405140c8a195100903001064130340d001074000d01c20f94010102d04a06002c00000209680100e24000708403040ea501001c0b02d06001d2140310600056030044490b0104165406c00c1d5880c45c020000013030090000e5440324502c0e2101c0d4002c40d21460b010404145501e4041d0134039074815449100010380c0e1410f0041c808044050b408020311a82d56450030701000c000402000c400701040d0b000f1208aa80c581c101740c02ca403da65042d694800c50150009007102c03480b402a0350844900e13a078041c50449595075004040d400040140c1d04101842c40e03401c002c41c409000e103d60501c2d400c021140041c2000601040a09824a000340a94401c0041c000043c0e40022000010040214003100a051902520000340d010b0307030000700b0842c0e100340c01103600038000102078003030358000003140d5220b4030f80c1040c4a5100300060008100310410300c034180c0114000c4070310880c5a103000b0b0044035a40100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 600041250 1250 600040000 600040013
    0x7060e210303040c051804020f040c0201091505063102090f31110433180603090c090b0a050613031b082d06090f0d1403011401020703 59
    0x101c40aa440300000d6074100000d0420061b1081c01500c0c2114240251070680c0118150700031039407046014603aa10212074481d8402c1d407241900951003048034075080c6560001c5000b038901914542d00c070b4001c08103061480740036059540d620503202d0f4559003102d03100079002402500490f4405400400040081070503990b03c1e24240c40720240381019841103418840100903040f44801703c840103901e009416060b480000c41a82d0894584480c8180902c0e03021704042018002084044150110809207002a40c0c000303146842c5500c0d0388042000c0c49945050483c1a40c6100d0405001c5a800c0c2c0000e2140751410b4005400464020300030218403a510004141d4030341c003010802518a1070100700b03000b004091460401c014101245042d640e5051509444d02c4509048a8006404401031b528048050070003900e86503591f0030056034860700d0b10014603511174a002036503109a015a13100c1440d10b90040241c0c0807040324588050742580e00749040880e07059043c4030090f05502c103804000000554 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 600042500 1250 600041250 600041257
    0x70503090a020f0d02131b0c020a1701093e091f1206021806041a03150907050309060f010f030308040f0b010602030a090801020909060d0204090816110307060e2103 72
    0x1b00f5200000d10724418002130a021307041c00045404118100d107001c0c015940d0321680740700f034032003180c005807507034003101700c01401007511075801015502890030456140c3d84407820980411003100c0703200043d01c2c0d206010655964000001a80054840040341c030549000007001c070711120b8003004448054550a11034095081094120307482500043c0041c441c800741046101014402d80da02820181098510015040c4401e0980c250400200000e1203c580007084000f0b2070130081e1141c00541007496000300b4070f52044036014841e1252a01007404240140c2c0075038100c0d00186441d80d041411681d044515a40180041d82c001451542d14804144058010b60007040c40d50001c541d150078045020340340f50010703130002c141648144042001c54484103c043d6200d9400c5404110b88860361002074002c140288024008072001f0540140005400740103140050003240034014152000040540d40c0440340101d0002907040c001580385800c2504401854082c40d0b50483e0030300f000003400310324580 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 600043750 1250 600042500 600042529
    0xd0b040204061e08070e07020d050d11040e0403020c0a032004020c07080c091008060a0902010215040308010f0f1a0a1e08010603110a08011710060308040e070503090a020f0d02 77
    0xf100c201c002c10034400d042044c01c00410b06400d445c285840d0243c0041e403a41700003103000b8140200040e1440c10011540e0002c214042c2440c1d14540301d90f103031200003c40030001c841c11005031003200010b06061818411850840c2d81c016000c0f0f680002c1c1c910604e41710b40708401c246070030179001d100861100500303002d042e001d0301c0c1d038030010f1000081c0c5504011003500090002018145c4840041c803003ca004201c0c10783c0a0924100418160b4640c03004074a17100007180300200000240e414802016030001c20281204c0741d540c0b00e03c0c10303c0d40324509094100351503c20301602c480182c909074100b180e44000351410340d8981c14a84950700c4032202801c0032005480341d190009100d24018443c075071701442500541d070018200c0d1400e000280001818206d0706000e0080410550b001c4440c182c0303010041c880b80d0490007403041c000715550346031056040d04039001d05e048401ca040300082d44c01d48180c05480c072940f800170042880742565001d200050510468142e00003c10414001c056103030030300b402201e00e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 600045000 1250 600043750 600043799
    0x402180a061103250206130509061507020904020109080609010b040c030b0d1103030d0e011a010c020109031403070210050a1d150309010b1f110c0d0b04020406 70
    0x49110801600e94010703080802801a00845107009410000550307200c01c1000034000c143d80c0722507018040240303a081000703500c410b001928910403c1c0d008003520485400f9124103220b501e81c041001217100030030154002e181340500035903000d45800c54045030410b00604103170400e43d842d00d2207d410030f01c040359422840c1e91500340d0001142840c0c8108011040c852800700b0512034454005422940d80c50309c05040d022201c08507a007695000e1044411012004504110f03444c03680035450b01801d000d820850780c9200340c0d0620f04403540901c202d2084241d05039980e007074403408c568600f40c034030308000e246003441e11040c0702e40001070f2210301140b012040141c03500d41c1c80e000115130041c009401c4207600e02d042d0141c92a59401e40d1910f20540e000250200b40ca40c1e203e40d5002507450040440a820560101151074a500e00c0f0011510b020b8940c1c042c0d80e50488680700003c003966540307000c0604590841001d13540507001c504100984c0d07030010b10003400441d26540d1600301d0a40441d4032100e04004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 600046250 1250 600045000 600045037
    0x1d100f030807170f120a0f0f1406064b03010e13030813020d050604030903120806010516050c0d0605010906091a27191103061e0406050402 61
    0x180080380c1448014040c102e080946450313800400c03510300b03000f15070b90141001d040c1c01c040703203841001e40c0000308508010501045800d88880c0000302400284082c1080b0303515610110345203080c05012500c90100b1002a09a900c070003041800d05400307014000003800c402160304030b401c4040501c10180200c20000c00a490354105072002440d40e50181c241401c41d40c001304600d00080d007040d041c131383c45400300255a900f00200d001284001400714802000f80c0514803c0004141d00100c06030300b600c0c0503400d06060165a0f100a44110a082d150580402d0003030041e54420503c03150102119482101501c000c0c0182e20081003c01101c9482112400d8541c0014050b4581714401c4a00810748050240000360003440680802e40310b03d80d2070360050025035040d0313444240710040405181280c05504440d03191682c4450b4602030700480e010301c098240b2816415040c20340003a00d0103040300134070b20f0308440c184a62100d40a03a00d04203103904107840712000101030b40d6610140c000c82c0b9100075603628 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 600047500 1250 600046250 600046253
    0xe0114100302120c130506040f062601050d0c0b03070f020c03030405010507110f09040302010504020118180f0f02041d13030504030803130f0303090614011d100f030807 74
    0x10860210420a0109403041c00341c0049460701d444507036007001130010600d903148035841a00e40c5414064101a410010004e00002c0c0a0551a80f8000b261016a41c40c040b10801240b41314031103882000003021803c20303070014400c81c0741c0a078010082d01d00c9002d050784100d0b030718003c03011181c10803201000030621440f20201030030740510803480f044ca0107c000e940b4043c02d210000e00a17014001d03000d8860800c1d02041030040d2601c0b81c40a00710900140084c0706880c0619009001e0302c0201e03001c0380051145500300354044004101c0c030040d11032100c6460107040150654200600300013440700300280d140d5031180c1c0f032011035100410183c5480d804425040c40300c00d2140b00b0610380030b0281c00781203a01c003105102081d40304042e903068a0740302100030b50380e4941c609483c1c084000c42402078800010040032004040d00359005501803071042800340301d1940c0403d07105094020900c1102080131204201e6000d2209429103560b00440328101c80600d59110101a4400262500700301c0300000002840d00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 600048750 1250 600047500 600047509
    0x71e0c091a01020102040605040e0a020d05190e03040b09041a101106090d08040201110102041e03140601080c0409030c05030d021c0203090c040e0109140d0905060c0307020f0102070e0114 82
    0x400e141c000e0000b5403a040c50b186008050b0b00c691711441640080c0f0401245002d4455011506102d2031540d01b0720003420060080108074001c0040035040c24038140382048510001b009486c104e82d00007203034900340f80e422014400540203004003070a000544900c100325aa139105021031800c61076641c0c0309581050082200e20b03183d4080e0410035654001c0707420005a81c0d10071000c075030103582031800e02e044501858520307002e070090b03820446e11522501e511003000e150700401e5008032400340c000d041100c40c0d0200e01c603894450038051100642c2101601d00202d041c5504680c11a0b482490015410001a09c0307580c1550005480355245607000580148070000103500354101e00c02400c011072640c00c204410782c1d92a610100c001d030060392901d50500c0c0d1a1829400403510a410890031100d030a00007002c1c54a561010030700c0e1010a000072008992401c019040c0d690701488031b030003149095219000c2003c44d50764501c5841c118401c240d008146a200d101c207950081881c3d44001c94000344200401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 600050000 1250 600048750 600048791
    0x31202012702010c05150108340b160204020d0f0507110606092203090608011202090a0207111305060a06142b02041707090e03071e0c09 60
    0x400410741a8112a0800506032046440c4942c24202080c1c11801c601d0150304000c0940c0a1b401d11064a000000310004089040031480f07000c40700ca620030f07800300c0d2000b0854503032440300f007802c1c405802400d00c0038441000091048844903030b458107d907032550f400034040ea4080100c1c801300300d032030740010300250780140079080c0c01003030754244400a29642441d8503a181c0000b40705070302c01d091072401300f40d482407800c1c0c02c8810586000000c80c010311160401410200242c0b10302c0c4000380103000001010848050810100e5078024054102a2500c3c0c0516029400c41002030b40c1c0d00c0102c540c0251150754001c0701c042d10040031040452149480c00402c010401035501c050b050081e01c84449401c00101e1081f60300042c0592002c02920780d541030720031000031800b010303001c40c0c038800103002c140c04200c6040102040304d00c400700c401090301e4080401c10740389502055265036006014040005400b50301d51080b034203284180e500315480340c0e290b114244000381d1050801d01d94400c03142001c841041200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 600051250 1250 600050000 600050021
    0x16121e060b09030604110d2a060306180905030c03121909110d1a0c0409050c09060406050a260a050f090d230c0106080601080a020a0e0a0b030703120201 67
    0x42900342071200003c603444110040c0700500c045641c40a85005039074a882c2039010303a8025204448109450f0840d40700072440d03541260a00041c0400080c41a00ca03001e441d050382c4286c0000307100d82c00a00040b0010701500a01207402e80004d01c0302c900700e8001003014000801c42401e26005505000f04006035501c0c04a41da8402142403a60360004240d010418013080780e41a40d69402d54411800c04801098908040c13403950701100f0180003095a42002a20648041150400113511a0009130745248500310400c1d40141040c0002c01013a805000030340306081e00d03420b001c450706d541c2c91410300481c119410602d501502001c02c0c0848180944a1264489414020f043c0b480c140104003a940e64800f6480008004003620b00030401230015070300c01050110404456150301e4042c060b0f6028bc0f17003074001d40c2224030131100009048a0000b441c01000750f000b6101c844464105039500203581c0c401400901d100740c5415540c0c2c07842d02c01b04101c1c0001c600038020104035500c212002829036251b29135 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 600052500 1250 600051250 600051269
    0x405122818060c050c06031801090b15010305100902030c0c06070c11031b120307140a05010c020303010612021b160504051e1611070f08060109020307050316121e06 72
    0x240c83e0005080007074440419201200d40507101d81d6406089404808100c040000d15400c10b01580108888928100d0003544681c41c0d49103880c111200460403117a0807101d100c002d02202608003c0048140d000715085107075a61018600440c10940f18a01601542e04100250324182c4141c28009086c21000344000100c014042081c104098104004044c1c0c1c80c0c01c0c4940b0011100800340e003004c0088900e49075000b400400754070b01d00c500180d10746074104000d0b00c5650078400c1c0d41c80128804812281031301d505445c3c0030314074140da4940a00a4100e01e0711000b002075031307012003900c1000130002000b0031070b01a06143c0ca0181000305000a40d0809091034070580d24540e144000e14080c1890250702c10010803010017045541201219842c2401c5603d54560003410800b21364000c00c41205005d403412407084130361590342c0c0c0403848100c0c803003103803d540014400c0c8049003803601d1207066448001040e1800030030980c0501042d001301c501725500200f410702e0029411004004501802000781200f10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 600053750 1250 600052500 600052517
    0x90106080702072103030e031903090b060a080a113f12090405220510112106120304090605031e120a050d0906020403110405040512281806 61
    0x400420a4403134020044c149916004041e44591041007034a01006440c104a1608154194007038010101c80d0030a0301d050741d4907130018400703040807400e0f81c0844804500501104c03c00d6264500300c403080001195000c030b0032540504d4490f141e62165144100601140c4010156641413024810030320041c240ca0b41d04a4114030100c1012901a1014604140d0380032400c3d640314049945488801c50035443c401a45001c04d10a00600156003403111404010800082010f052100c40724000d400c003603608603010620501490302081d081d41d0f0040b202800e00d54507621030000131411500542c00681109170f40300c800b0002c6150400c09030450000c00c011180c1403103504420992601c0d0b00f01882c1d180d6000004503502118429812502c0b1050f00e0a001c00112a1a01e040b038044e600c20701c01524140900d41000e030103480c1a21035240503e5100000782040540010860390301e80102a003100031032040511040621521003000c95092120780c0c1d0f03020008440724000c842c12401d03400c94010801d242 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 600055000 1250 600053750 600053789
    0x3021b0a0b011203110a0305040503060f1311060c0a080901090b09090f06010c080a0c030f030218150d0906150b0c07180f0e0d1418040b0f09010608070207 68
    0x22007014103465103c1c920044001160400381c1c0d1036040350f00860000d10600c5c115805069005019000b80c03042181510790a0b02c82840040c0141c2c02643c0010300039800040c03000000e540c0d001600b080b504d000e4040b03801c0082100c15035051000054088c1c84840c0001038045040d0b80c0406a43d01402c5c1c2d801c07555080400c10004105030754401030450600d8821100442c20070381c0075200503800c25030b00c10420f0b6503d48103c6001800604007140480100301c1e80304000680300c5c060700030b44491603042c001044105480e5410841e40440e01290b1a9500c401081482580310b1980201840a800761380041441c200340d0310386810301030b86640184190501442030704003485c1c0c003141c2d00c4100c4104900c020314401e0103110040061091000800405242c0031215021a0001c80c00d0f03501c40c031450b00d070f402c0035841e18a42600306201d03420821081d1810080810018585640306034a1600080c141d07102c03c4111201280d6010000e030000d00c040341c01e410410040d04c2d41042102c025254031041415001982e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 600056250 1250 600055000 600055013
    0x5010e06010c051009060908030103030201061d011413060906030b090f0f03301501030f020a090504050c070b090a120507110609010333080c091b07060c03021b0a 71
    0x301e01c6000340561204417540074401e07280c010308030172030700035001c01e5880d40c0d03914010780288200d20a2000c5821000c00a084a03011241440c0c1202c03402400d900140382400c04020074403000d401c0301d00c0030382d9a0b85e0340070034800081c1c0308440c003451190700c4900e183d05088041c81c2c500414401c59450603880041e104540040c0072003615100000d515a0100c059080801400419001c0722070303502c060003103410864208407031070105111240a0f00c040042c2d003d14203002059208080e071410100341041400c01c99070509500c980d50225089207200e040114540e6011451070007601c0c000c21940c80440b10700b0a01880d07111001564419003401d9140c89040d554141e0644018001e40784182c50108188850340d002c0c2c2c00c8282149912070400c080202c0f034004c4404007c141054800d06065440c0001c00c0c40038000801d80f8120000400950003950b4a409030041002881c51045803c64140700e41c0740003900e107020b024850350150300c1c09a110316250340181c118200704042103d45500c10711010000c50705 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 600057500 1250 600056250 600056263
    0xe060d020f1309021c110306010308190216060e010f09030c05010309030e181602011112040804030c0b0406030f0c0e150c19020307062c0406080a0605010e06010c05 72
    0x40c241c0d501c0c1c402410aa409038020954008045c0d08080b0010540ca2482d0b002e4200e4040c091041403a10003022404007490f0303a6600034040104203a4082110144070042c24880c0500c0701a03d20454000b451080b100611456090f40840c0104103115415541982c210111055117401d6241800c403041c0340d91130b019481c28143c4070700e0f4103148c4e07140c614206040c4a284186500b81c40076210b494140e40040702e980d4880b07000c4909501440035540301c0ea1800f403040c00b400507108500100381382404255400c03200045006002150b560310200000000951100500c80003410304404040d210340c070300003010701279800400610b4145440c22541e103101d0703500002c132504060710a0f90340030308019602600914511071000603440364481c0302c2c031500840180c5090040440c3c030903030942c0c50050350b800e000d0b1224984603410002186404c650b5280304d529512010508900050010a41c2a95002401e04200305603206460040c1c4480051100101c101c2c0280d400190038170340314240e44071a84071f0070345400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 600058750 1250 600057500 600057529
    0xf07050a050a170916060201020a08060f2205011a09060d0f0b0d050703050d02031918030c120314090d0b040204060e011e050d151d0f070e060d02 64
    0x1101052100b0b45034465010303026800d5100c2078540150400144859580764012034114030740e4403103140440c45074418025141085c184d0744900429489403010482600301e140d281d40d400c0b00d259500a0a80901d119050001c0787c0d529400040550406202d01034012021002c42014081040b0614031500e51034100c4003c6014a02c1c00035650b90708420110140090850442d88a03003a10014820700c1004075280086034440c5040b03c1c0350001606c0140c0e268059450640b288a0202c601e5080c101c0c09110545000b4040c07075441c928250b01d0355600c142c0301003240c20803140703001d010522004040d044112060030000c1400da403030070104c2c0100040c904000c0041c0042070a104200813404544550b08210041c0820748200311184d03031942001400003100340b841c20501c8109101c000380743e0038001503c5280c2500035400b1104c02c2d901045007c00b41c0000300501c0300d008251001865901d40a2120000c03102c2000042e100e940c0c608140201078100c00344c8036a100d20341c1d0b9442c44006a0b07902c1c0c645404d69 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 600060000 1250 600058750 600058757
    0x50a060807030e0304080f070f150c0609050d11060a15060e120604030e0910030302030409050645060306070309050a0c0b07021003020910030b0a030f15050f07050a 72
    0x507903a1800803800341420b100104020300c804500070903400b00119212110880000840308015500c03420300c544920b00b8801c40c10b0359421303c54003000e43c030300c81c10f040649180200400700d0b05008559800380341214580741c900000d00310082500e8081024040107407c07030311226080c010f501044000d000d40040c2481101c0074411100000310483d140c1040c442e22030aa803078180c40f202d203450305014040b0410340c0d0201d0300c240654800616519003ca901d482a80d40542c000e50400d07040c03049100040c18050b1a01d40e010404440c2131200741300780b049020107030866515110450103140700d4bc807900c01101a1012020400c20108500c0d500c0004100341c0c800c800d85400300b415955400c02e41d040c40c0038240c0c084c0841c102060b02241e20900030005080d0944241d812010100b2001c1c4104c0c2280100c442084e804104180c071822881c0c1b01e60000345903030b40c1c02400d40240b165641c1c0d032134044401d94402117800d020010076464400d2101d11481c2e034042e0f030340d05600c40e0914242c400140140300e12059603040c03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600061250 1250 600060000 600060017
    0xf020c0f0d240902011d0a09200c010506040b180703110c03190e0a1d040c0b0a03020a0207120812060310060909050d1b150f020a0c11030102040b0405062520010801050a06 75
    0x70300c04440c246005420027514203554a5840c150443e000c0c00381290018011810550303250b150382003400c00358a8011902c3d01d0041e9030303119420100c01400c400e04030081c0e034290900444400300b20074401480c400d02c0c1d40030f069a000740541c0c8060700a03400e00703a690741306004590040080f40c60140700c00d0025180c1c000399040c0c2c1d40d55464000492400c81d0000c0035088404501d140300300780c06900800f40a81d05400b260680c65a59045440e03a60001034003c03c045003d000e102c4004030302c14240742d0408401410380c1ca1a002c01c20b2a9822504140e000d048003c0d107440301c0c9410f0260922000c1c038030908074680180301d1221083c0500051805440080404c241c5619004010800c2e5101e10340c0d16902c0c60f07095540300c2440900614070b0341c1200b01503d45448c0e5110941151605100710750440c1d05c81480c01e41800d141c1020040550818600c038a800c0d0481114140381e13041070368010315290310621001b408011b0f9040e41e120f82c501880942c03410b0105160050004d5582ca880000459441b0f10b094000f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 600062500 1250 600061250 600061271
    0xd05221e050106121e0314090f040f0f050606040303091203020c1806040e01140a0c03020418060e0c030105030a08091207060f0f020c0f0d240902011d0a09 68
    0xd0900500c030380903009500e030950100c0c0d503040b013151020555029400003038401d50000100440d0800011009010800400880d8141c00c0000301030103803800020718541100c0d64003000300303090304c0d401c0b05404806641d40c1144c41c1d0204041c400c054014100b40d440e02d003443d046681c003a19108072400740c81c00003200075117034104143c4200f00682560102034460468071007180c0c170b9040307002c000b81ea0183c0326070309045003510492414440c240502150540028160302e90029801c002c000384400601015000c0001042c003480d85082c6502240145a001404134a045102c000340400a082e600818404000400c80c0d6640014901e4500e80c01c920515075a080b40d1001500b101819442e0009034007800c0030008142d40c10030035002d503411103500d55154480d02100c040341c403420402001548051001e11084190421110b90040780703114030520603128a02c040c400e09001c02101803100c0c1e441d00c0d1242d0303008650380710000c400102e0505080384100c1c40c40e1270008035411828010807404030703590311f02c101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 600063750 1250 600062500 600062543
    0x240d0605061c062705060103020111031b0c0307050a0e0a02090f0d060b0102010606030b01020715031104031209060302120406051009021201030516050306011502071a0d0522 76
    0xb0b00140100300281900010b00e07060016058040c0c4210409005000165402e001c070110441116030000140c5616070956005580c0b0195061030b840031340c4420300200380e01000914450100000c91001009a22400380805240c02c002c1d40020380503440100007080b20b84080e035030898204408220158031002c1250100745660340d1000041d9200d40102920024041c465112010100c000c0c1c0c0207200031394540d13409400341c03000348200a0050b884828100305006903c1406610004145004160f8914950200e6815003184d001660f820345003d1405030390319003000f03840b80144a41d060940c101344501101c1141c01600900152101d0b840740000340c00a601d10b4421000381905140454a5240b540c014100c40882404204c07082d111302e1090120320b080400100085880050040426a003400610201100e107404820194818214046000303420301c0c1d200000e6003003c15001d40c403040102c224005550340034180c50b500404296120f15214442d0180c04c1350260410180e40a0049070f10313414 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 600065000 1250 600063750 600063769
    0x3050402040b1e09090d0e01030203091e060708070216050105090d0233181903122a12030908070b010e0103050f031908041b080303240d060506 63
    0x95070003200040ca405150840c01200c600e020f1090b2046000c0d5500c14000980c2c42107100090030102d8107114034200310b90700c030390011640045003505661078011680300711380f82c10400c0e60b4424500c0d0000c0c4104206c2c0d0b640400b40c00c0d801103141c402458072525000c0c1080801340320f80980340c1044ae00141e9841c450700e1f040c080500d51a4050454184189200004503508a20710031100e5109010115050060039550640d501c1d540c00301101c0324110301a0080080c042008102c0c0b520403003c04030000003003102c0425200001790a40c941c011700c552400542c0030f0754440039040200b064038000c01d050208070300000d03682520f4010b0900060741c601504055645002d00352004200003011000401d0140d08a0744050403644550122842d54081000d00350702d0b8040c2194003c008100080d081000314401d416071a000313405004800c001c0181016000c01c915582d400180c2c40e41d000106110700305200105103040c0d60686010281503a5200f030001d00d60800640300940300c0307601c50740450f00c19560105007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 600066250 1250 600065000 600065021
    0x20a1106030a0e1623030c0105030910060306050a06080a030806060a1101020c0d08070f2724090803070c090c020115180f020c0d03051503070806041211030a0305040204 74
    0x8070f5a0541404202c000282c1301401100c44100f01121400206400310360070051000740100540a007800e002c0045806800c0200309048900c240d01c460252080d061240c10b000d18001c07000460790380703890250039041d1015507000714aa64400b0b409040426803004046801038011207419a4a0440d00c804841020102040c200194030002d000710f140880014128a00340168462840c41c0e5218001522040d807810325441c041549001d00f0f40e11585c003000b0015a60b070a250318800c2103511f0b9204203961400e404401010024010984d14046400c040150020300d403100081d40b034240d07244d40700110040940f15031619130f0b8031503051030781d5035000790000c241040c502c2c50aa03012680d1082c02500c561841c00f1036683e2a0b05e0143d81c0601003416008880801a141e0020179521003100c00803070042c03000030031400100e4a007080c0b905441d541880000002e161000007414681024203002101481e90301d00342d8280300540d1031001f00203401205030740152482d400d00281c0d599450010401402c400b141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 600067500 1250 600066250 600066253
    0xc040b0301240f0605040f150c150e100612030804021f26071704020102151006090b090a05010f14030a0c02191e0c0518040210020a1106030a0e 63
    0x11840d03031403950341d01c1c08680303440343c80d000440e0781c45101799018070503806004072078200341200703001921741d4107204c0280b80007500d000715424040c0e455070642c2d040c0003807580c6982601c1e03860000440a040000c1e0700200701c0010b080080c1c4e0320f400581012074040e40802418460840c00203429599455240c01424045201440080b410248020305816107000515583c05071b81e000d10f0078040b604546144941a180c4070955805420210a5000e01c0001d00490452040d500d551000c3c80c000d40b0501e0054291541c0440ca003820002c000d01407844030f400103018080705002c091010703522011940d00300c503000e00b007101040680e9001102c0300d0000c10314000441c04c0c0003090211400381e680c481ea0240c40554207641200002140c40101030102000c060056100e5044401102204072091040c803441a04280152581c2781c011880901c0103c03080c040144a034001c00c019400c1405c0126806a2148040e02c0c00501d03550714060f0a114092269000c0e11011001070383d00502e0f0360000442124000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 600068750 1250 600067500 600067541
    0x1803040e070f0215040c0302060309030c0d0e100302070c030b09070905070f0f0c120302090105091206151f03021b15090f070b040b07031b0302010606031401080c040b0301 75
    0x1000381442c000c0072121001480342d031841c04c642c90000d940075070085070b2004c0388010a511715000c1004942001d08184e0307142c001008144503035141000196441d80d03482d00c510a03441100c0c0c04002075500c15420b4103041c9801000100c0004018a0250054941c410130030780007034569020a074a00103203070300068400c0e89043c007803091880d00f0565540e260001941c46940e401640f1200f292200c410f028010003600c0e80c0c2d610303106a1170081c1c000d0148510185000e60403d040788001508074450520903a84a030068028410600522040841420020780b06a60100004100c914155810060401c10503a0100e00d80c040d00c0001101c840e030740f1b910403003251000003050618003802d1809507101522445410390061030b542020841c54200c40d915802d09040c240380900c0d008842d4000e40c0110204482c140490040c1e6402c810803e10b214020341c0009601c90070b24802a084079500a901081a41428010480c40400007004c03000c401082e10085894466100400e000d00340910340e5146813203820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 600070000 1250 600068750 600068761
    0x2071a090915040c03060608180c03240a060312030b0a030204020d0b100f120b030a14060106080901060f091802090c0703080604090c1703070c1202040c020d05031803040e 75
    0x1d2101034520000322401c0244c80c500001c2030b01282c0081c4224004030309182d00091304400b01c5100007402e41300b41d0f0181c0380502d02c2d4500207800d00e103c2c41c6480030b094610701c2861207980c40d01e07069194081c03401001004168159220041c030396040881e6942010740300e401151042d1120049000116070140095481e01c80c290014400360100d800c1ea117020305c000c0c0d80101416807140407c244807560f140c80300c9446502948200010b011100c000c5505440b508000f00c001900c0c03c0009010701c210741006c2d00095041040c01061107001625940280c0e047c01424440144191f074018211820303d000080c100c0440c0541c9a00304405200103503006440c10100500f05161000030310b00c1c50700c2555801110f0742c50310100400c03124421000b600d2000410703014031114559030310300102e5500380d2007201e04082c1a50b9510300784100980020b40c041d6a228807000460405010300f0b48441c0300e40c001b4040c60114250001c105001c01030080100c03043d0740310720a1040005204803009000140c00c076501c0361510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 600071250 1250 600070000 600070021
    0x2a0709020c150622020f12071806140a02160305301617300415021b01020c06010e0c030408090d03120e062502071a0909 53
    0x1041c400030035010311480c54440e080d680385034a228001c000c014004007420000340d150f20760400c0c4083e0340301e00e508000401d542103459001d02021040386003040981d16065400600550f03020799520f0040c11041000e00440390040841c208640c0b481803035540718552070784e0803032070600300c0d804100d01192030320008414020080359100084016280c664074240a600f9030310045a03140c0042040d80c00705010100550040320b210340b500d0350080c1909200d484030700081164550145154114114007484c1d0512031b42d1811103540d11034034544040380f00a140c95100d466192034499040e543d401d5000031b80c0d100004400c1d0b00c1c2203036055900300171500c8101580c03006646910a000b08820f00481c100011004001c0104072440b59a000040506004010040c04061101d0500032002d10070385030a0b41c020300c61140701d564804003018000f05410700f0440920080a080355100013032114001c0c6608583c2c6400088040455a00000380325021800b0490803d1500804800da0750042c002414003401d46036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 600072500 1250 600071250 600071257
    0x81906091b0305010e121b280203060a0c0c02010e120124080712030302091f0309020f090112111f050706060902160f02030709181401060b2a070902 65
    0xb00300b0080104940c801e0610340d650307003c00080202094104030308009040861f075400342050381c180c1100c0304041e81c95441c42985407800d080c00c2c0001d0b52115082d0640c03404000b00c603040000c2c041c0420804c2c07406036004204804c2d09502030f040c0402c111103d041501d40511105541c1c1075203000300b0094034900400741404d0b04a0740c000300048490000800d0946010804a00711800030700300325040480c0d030794183d01a400c00d9421a60043e0717035100d0800c140007109550100300c44581c1d0002a66000303841001589021051003134000da064500520220400410004041d83c1121401c00411a8540000d044401c0314110302d854801d540030703400d030440d04240609a030318072030075090205c140c0343c080700800c9018460484c202d20f1a200d4504c00880c50f003551007085180082c0984804030b8851081406840185c0c12b09011040345911f40c50a2000704454000b20080c44c0c0001d004480ca42100da010320b00034425680139a4020351619810500000c40b01d14000ca540300030b1701c9500e551460b1060081d003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 600073750 1250 600072500 600072503
    0x100c060507030b0a0806060a031704051e101d0103091106041e080303040302120a0302070203160f0e01051003021b0d0801170f2104030803040b010306060f081906091b03 74
    0x1803480008160005c0201c3c40510a80000e00a0101c0038550f40b100e2020942044068070300c50410440031800307803290b21490442007600d10304207a00e42c0007201400b03030002408007800c5c00c01c40c0062001c002c0e01402011009003c00910340442c13100d03c0340c04e102c0918444c00403d0750788036600050008505050030124860b05040510000401d80ea401041d40c83e48005c41d00200140c000440c41c81003c180e003409002c044000f4507005052006a50110f4502041500d0b500501c54800100304028848400c40701c01411026170070030381a51510703000c510584806601c2c2000d168002c10040e400400d15103200060186000c02c56030294020000035040344402e0245034070b40f90f0340108031040000300007642840e00c01000010400c0e0000c041c0111490a8102c1020403841410400000805c2c85031010314002e90003000301c80400c1d499468120201c0e055980082c0b03c0600e400300801c0f182402081c4d120003400d003000d0345030184415240400040c592404011301c100c0d40b07122840c400c0c040100c00c91094a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 600075000 1250 600073750 600073759
    0xa120f020f04031b12081e0417060a051305060a02070620030106030f090f0219080708031306020607020307080d021201230a15030207051005010617070f08010302100c060507030b 78
    0x3203445c0c913100b20f294034a400d405029454200030301000e50003801440e0b140b4683d240511814291544514004090b844286c8034a41d4001010700003c808140300e9203400c200d41051035804030000b903582984516006190507015540807030030f5014003000d030300041c1c0714020704d46030100e003ca0601c94070781190300280200030001c0d26000e03d2000303d490790322402c001c03283c001d0307108084048940c0c01c00540300d06c10302d00340c8111042c0060018082108001610140c4a000301568494500719540600c6aa80ba40080f08650145090003103180c0c01100721903800ba040703e05070740e40c0d00d060214140640b0502d41a5151010050000585040c000408840c845010710080a03511100700030004002d5490141e1880e00410589140c10b56000750300516200f403041017a180a80051641c08045407002d074001e07400304600304180b4020342c5051280f0356203c912400e0400c00344a01840040506005020083c004c80c5883c210400711400381c2050704006034840414011803800c640010050000b0048047c001e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 600076250 1250 600075000 600075053
    0x102100e010e1e010c05032202010216060c05160609060f050c030406030501090f050601050901050a02070e071e0815040902131a04060b0c0a0605060d0f260a120f020f0403 75
    0x15a201b8411070b030140c1120103a05a42c07022000740381003448000341c03080f41944107107010054030038100714074a0003c2c50986c072175081010807810140e0814254200c2004581ca41250a204036a040060802694031500e05407624070802201070b03c43d8481c49203040450f1101103800035a865054000a06881000e04248900034562100000341da500380d88607030201310240441e8000f035209101030418541c0302d00c1200c42c00365544980d2400841d003600d441c4001000f950311048800341c40111014112080c2c42c2444240c0707002d601100202d804114414480c0c0c2d25000310300155a103854019481c65600c00040106081c42c40051400100202c00c40f40124140840040d04101b140266000e4051032806010544503581d5010010700c0020f008070761110b400002c050200f80410010900641b00c3c03800c0816800301035603842d0810034445207030034481a08000b180b00307a5600c000600115001d101001c41c0610742000814007030300405828141101c40840d000090110268014190f00f0701642000b40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 600077500 1250 600076250 600076271
    0x209010e0c2809080d0e09060f041b080708150d03111c030617060a09050a0503040803030402091303050a0c050106091a1002070317160204050a021b03090102100e010e1e01 75
    0xb01d50030f8205071790011880c140341000e441d040c410b41d0140d0201c4014036044915540000140841d0600d41e11b0780135404400380015520794116410603000303103050514108510b402c6003c1d801d0144070030380f07403130050307103424a00410940640c2c0e5030300c194001c102c1951554001011014655603100c0602400a07041c001c3c0001c07407000285102c40200080c00141046070f81e0340004001070585514122040c3c4161003281001c5a018006440508031001c017459890074103004012140f8000f8001d01c8840c081c440c44600007030741020448041d954681482c09007191ba81c108540184155409510307554106108807800507441045010000c9007100d504001c1c40200f442241d81f07461b00e00009081c4280c3c11540341038815000b0190004004501181059502d15400700e41a200140d038800384103034020400e90f035006003030181c0c85c08044505004604104207240002c2d6a00070440b0701449180c5ea62400c0341c800d200c20340080503111014412a00d0b0000d0300d86281a0018120a010801d03510300100d445 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 600078750 1250 600077500 600077503
    0x7030c140a05040506250f14030f04030b040f24050901060e130c05060417010e0a030e0f010201090b040503070b1302060d0506032a030c0d0209010e0c280908 69
    0x116070011a54a041c2041e040509200b01076010050f811038080e0711000001c0841480482e0078500ca21035032103101549254a840220000e15040130203641c0c0080c40f500000341009002d035402c0765080484020180c0b0f580c20604044084000080c0ca420188014440c0ec0001c4807108141c480c9002410041c640d41d0b0b2200b03d080750b245e03001e22000c61038858040340d00e0b2050003440048240c091010152410750303c0d800120b881d802944040c000040714003288102140c20b100c2c004103d01420050482c0b00183d07540104501c0790054203d1145603202c444000ca64400d600034901c5d00c0c3e01800202040c02c040c00e003181c0c3d940142204031101005240058078014040482c00c808903806005030b800c120640340100003909000708102d426200710107500d03038040c02c9100c040300e018441641016800600000741030519955040b03c0d07000d004400c1011005890341450241111407560742c1c035505464852503004070744113489004180c2c00398015030300e483d910041044041c13801e8a80310a16669a80c0d40f07000d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 600080000 1250 600078750 600078757
    0x50a020a020c061207110f01180201090902160201050c0a0506041424070c0303240608060d0b04060207020a120311010c080621070b0d1a0105040302101103090907030c14 74
    0x44c0126629030000c01e118a0040707141102404e080d40658407180b01e41003003c2d007124200b00350f5030341003201c2a03590300955800c86403143c081c0003600c40940c42d2490540040b218400b80302c4000b810018001014007240308213200c0d0030016a07003c81960074a060038200805d502074080d40c008442d0103040c24442804000d005417149000c50311003c0310a83e5034841307058a00303070715001050341850348500f00032540c0b0003c6496030f801c1d0000300c51240c109a040c100d0080202100802050042c0c0b801720b12000420320a007559603201d41e01440241e0703698070720300c0810b00c0049a60300c0035021042084402e400c0580081903c8031140300000200100500101e007102c1c21001070320031680201050502900b00c6105000c0c11400e030341107408a0391825520110f80c0c2069101480030740781180d551040f200d440815100c0a10000c01c24a804c600302811034002940081043c828902484001da4004100410078803e403210040f00070056455132508810242c090300414075030200051148800441044944059 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 600081250 1250 600080000 600080017
    0x932030f070209220f0f02090103080c0708060c090d1a0126190b060103200418020c030a0f1710050414240102070f0306060e09010912050913050a020a020c06 69
    0x15000b4060068a1711003001c0e18040041d0359411881004801603154929417600842c8074164041c6d4070700c202c1c0f041345d05045103600055040d400941c00c1c040400a00c000351030148070308440400501403103143c0440e103c85c4c0c1c03d005070001c0c0710b8203000107800300103802c04045c000ca030803141c0b084a1192101d600d49030590414000d0106403003001c0e5102141d916213415900a1060400241182039110510744180b0b80c1c0000307071900b8000023001d21019004c44a0003643d88035401055003045440074207580c40703001c0c4c60070701d008010410701344c1c03080648102202c2107504107d110f40b08060030701c10043e12400c6c525005890040b404c0800d880860b414500fa4039200f28404100c411801800784440003294070498503c60452113002800b040000e40c850841004512807800001d0241c1303081c1113041d01039002400c000e2541d152482000c08a40c2030b071003104043d1100d1070065a901490400a40707401803000480300006e1800d410045541120303801010003441075003c8800340c100240811045120300c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 600082500 1250 600081250 600081301
    0x1050c0304030f023d0603111c1205030403050f21060118140d470703050a021605070501180b090f032b080a0932030f070209 55
    0x19414096500711840d101005c3c07540300150814940c5c07407410b00c00d8901d590000d440010f91100f09075411b14146015800c5459018403400b03a8011710746a80c10910300c402800d100b40702c0000009010503100f40110350465403d90722107a00c03105101c48055030143e003440410b525038120300114280d0340c045c408440c2e00ca90300303140d488102810300350300c4407411041c00000358000038925209000509424180d0029242c2d00d01c80d40c418040746c14840c0301d024500480f400c130880d0651403180006144592080d4420041e00340400e140e112846000002e200b864810313504001d03102892010000045419021541e09076925202d00c3d401c06442900103080d8412440c0688041080e1501c83c10249a2a12129001002d0314000180e1219881000001180308040c400001c1c0001600a40140506411060b00b540c2004141d0032681e42880c05c2003880d00712a4228100720003210085807102414610721039440a480d140c00c1030032440101900f222408034030441140c03000844444056001d943d00080d00c0d02c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 600083750 1250 600082500 600082543
    0x40f030b10170a23031204051506130c0912210311090409050a0204060305100507030b011710030507140a0503030702030a0b04080c060c04050102010f060302100f1101050c0304030f02 80
    0x140c0d241684c0c8541c4006003d07070b10340303032154060705407081c0f01030444041c40040b040345626081c60801c2c2000013038191054800781c11411302840d07440711894100c1c425800d10300001d018001c1c0b107050701d2040081d40610142c07182200c800c820410514519284209600102c40e06410704000a800351010058801060401445480c80381d1a00c4c1d0850042a800784c010b41da15440356401181c1910050f40065030b180d03020844607800800540300c1c0c140e0045061800b0400340712410b0008003075510345417000c2c400c100d00d1400300e080b9401c5582a4802158031000f201c82e0307517942d0801e407084a140e1500051046c40c100302d000403a800c010046510456004002d04072011866171000c8102002900c16a00c101017803205c83c40c401c0301000300354080d081c01c900e96519649000002030030342e8031030140e088509090500c06c00c0141ca8402e4a5444550907050014020540d110216003802c4000b00110783d540c01d2100380080d8118610040d4007540c082d42c0c070007880c0100c612059a480e1958034861100707a00c0301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 600085000 1250 600083750 600083753
    0xc0d020a1509141006080d09060e0609040216110a0806090d23040801050402090c090d060c030b041d1c0206160c0803040b0106081305060c0708040f030b10170a 70
    0x194841d81503a8070404503243c0001da01025580b03060043c0182c094042d64410050202c1d82c400c00c08403010510b10319042a80a04000004000c4801a002240162030104017080c03190786035019249a0054607054904114580c18030800c0c907286011a14094110900c011078000808101c0c50f200c1c500c988001d1580801840c2e04440143c0800016081c890110070301c1c00160305614010402040c0319800420b25051a0040210186000c0c00021400300100250120342c1c0710704081c0c0b000c45800c0b00000468054818094024003121510140c0c002d180c4030303a480c50442c00003014a002d296010844440c0e44181c1700401c00c1440c80e5076440b0150703100303500103001c04280c01c0304c0c00c1400000340760515040c0259910311290382c00655007201c0c1054a44c0052161941c0800760543c003286012406003d02c0550305c507551a0340014180803d4104001440300500945030304903001003140485040680740c4d02c0c1003020400b001940c0c41c07601c03042078200000c3d580200141605141d5443e0000d0302148466 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 600086250 1250 600085000 600085043
    0x4060f0b09061b060901060f060e100c02040b27010509040c090506130905010e060604020a09031e02090112051b0907080402030115060909060504020a08010e0901020712050c0d020a 79
    0x25100c04084141d0351501c0383d40c0800a202d40c90040c924074001284050a0500c0d070102018542c00100411004008580c419540d9010305507414a07141000da00c00c9405001140c090106800000d1708142140000182070b400c040769021402c01c450040380d8141d0f07c0b942040a4001c0690300901000c11001062240c00b00d82e5000c60303000703040241840c00040c0c010241d1401d60741d000005a480380d541d0700c1201a1105e00b4000b280d88141c3c1120b08526001c540100038080c1c554500000d408d42001e008200c65401c0440e0508901c40d4000709811465a903e064030600c6280c5168101d0b0756003c2c8008404808401c0ca0000200400042071030100f40d48403501240d155900900036681903407542d556800441c0e42076188000b9155503a20021030504004031141501c00540c06580994410046050890f86c05007506040d10203030b80070144662110b202550190040e00d1b07010340400c20ba0f5007800e9003150000024040f180700d500980e518450140001d98550320b045001034028840c007070b501c525007001c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 600087500 1250 600086250 600086257
    0x50f01171306050f011d0403080115020c12010c090f0509040308060414070305011d0c04090905070f06020304060305010509060d03030e19050a0201140f04051e03030d090204060f0b0906 81
    0x1222803000e0301e0481261145029140d090762400c24060b10140140000d811392018403040c1c03400895201521704207941d0003405200c2c148202510f8401c80e4040c822f0040c800c0c0420315400a004029070351980c00c010f1682e000300130171400305c000b081c441d29000408111074140d032000c0300c41c010010003042c2c1d5036032001d03968610006c0c03116a00680d1140d60201c5503440914090180c1075982e0000307060340c1004055400d1380c6400c500c400407260030740d040210103c400c0c41150f00b81c1c0c6089402044045035450070710707e80080382c1c01a01c0383c00d0003500c0100790141c1c00409042154210f035014084c50f6030311404c4c400b9401040c0e0740c841c4c11501070803032000841e0003604901e03503907000392080726028141045000041c100e4140100c40c0382c1c009881800940da0b010b55031030508003c4003031407454104401a4801c0c1d61142c0e2250500a00d4220000b4864101e2016050070244028090341d940d04142a6450010200703403104074412840c142c008104410b03e0000b0340260341588220515040034103041008613007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 600088750 1250 600087500 600087511
    0x40906060f0e010e0105040b03041a06011106040f030903020d08120105010516061a0301140a050a0e070e090109081b0708211e12090c040506060a0503070905030115060306050f0117 79
    0x802040001231301c803a01c01c0158801c81c040c0c0398a0090b0f124801d507000c034007880941060304000007a40001c200400200c3c1e200d800590081e985a00700540380750680d800310301540041e40c004070512451040c42581001816001e040008000b0141e80781c50043d900c90080d041424002460040841d0014801d036022a0f03041488a00f03080c140e5414400107402e584002003052814601e02e003d020300b1500340c1c06180d41151b0b4a0030203024202d00c07480ba19a0b103040034410856400c44940c04501000c030203500442811340c100402950310b20384080048500030f400740c8405298810401700143d00c06010034030740920413a040881c0341c164050900744810b5003001c0e107e500803101c00d04070303d11060aa200104104208141900000d1034000c0c9075908050101503100d00990401c01003005564400c0201d4103402441d003800c90716911420710032078040e4035a40081d5055881c2c40040307110744a110401808a0301d0070354040c0200f0751a007043c0503d0300715064a040c0400c0311101410900f06803014690b5012 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 600090000 1250 600088750 600088757
    0x140409150f120b240d031e030509061e0612120705070518011206050c1b0601090e070e0406020705030705060c0304140307050c040b0d020a0b040906060f0e010e01 71
    0x2035440d014030360314881096008005840da07812580c02004501c1d1510380d4044600c481d0500d40c60010fa044201d041d18001005100705110600700003054025049200500891010044241c443e00c00190040c201501c1d901c41034030400c00045d00c500c0010200740b2241300d2050003550b09441d01c0c0c003484290008000303420610301595048005800a000c0074010140c02400242181c51504040c400004207034030704000c40ba42010014006807181c69104007143d54003200005040e522802ca04007a4010240e522101c41c011449403e103d10000400a0680e010001c00304608010740502c2c3da0788400c00d00c02d080400181c100083e0105610380d001d005064042e00983c2e2034081c1680e20350341000c0c0c0489103200410404800c1c08107008110200299001d910f100171440c0290302c0c1c82c0c0700d540b0145061418442e54840d480a2003e03250224600c0c43c25038040c052505e490b4844541d40c680da082402408913241c90030320009002845156140400721290329081d0003c0c00300030044504084502156041c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 600091250 1250 600090000 600090041
    0x30702071e0b0f040f06020304060c170c060406050f09010902010c0f0512030f04031d2107170a050f0a08030112060204150201090c0f062a0b0f16140409 67
    0x80e0700c400c0c0000c0c59801940e4440b41e03038517420300355038205120494121008562007800280501c81c5c02560b01c0404a42004448a41e03140b064207140071803241074182c00e194040c1c0418001040342d19000781c0c0c06002d52900007540f0740d880846560885a0351840a80041c0c46054050049811a0b0a50190502036000d503141d84017000e0880e05203070b1003642c084005107068800c000c00d25900818a50f124154035500c40f148120031800908582801d00d80890402c000d4606800b08460030094000100794901d0a24800e0129440307894070f03041d1301d10003501c641c01103900360a1040f1000c608501d183d83d0103110b060a40e4202541400160300b0341500300c0340503900300404030707215610703102c903040c0480c0c00da0010802e0b00c00c1e071501001d4032016501454040b2907200060141c103403c50000c4400c0b180e900206c24144880d0240070100e40c0d00c00d18082d22404040080c45640da4000241c1c40c071410314502c0c08140c0380b5083c001160520304a01d040c4c6020720003880144507060040d003002040e4900d00506045c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 600092500 1250 600091250 600091259
    0xd020d0501390c05010f05040506100501140406030f0e0601120201080f0105010c0b220c031214090409241508030306090c2a0d02150613022505070f0803030702071e 72
    0x1168008c0e502030310f05600c032404100c002c03040c040c09600038140a2800d03009904a001c0d86051030302130f90041e042070549400d2080c2c5422a564440400388911000310b5101c2d5a481000b0410559451420b900042c0d0200028091403160007590b4101c030410380d10b01c3c40b91002078481d11544600a013040482c5c01002140c1d900c09404552280203890141c0c0c1444416442c41c50000c0d891142d0703c1090045c0221926214580440314090700c010220541c0c01041c40ca07418580f107141041c0c900b100004092004140500c00540d036403060541c0ca0b00303044441d000c40e45451645503640400c9802c1a8840c41200004501100820243c501c5100100d10340d05440e1803450341442c0e255141205008580c4400d074095101c030340c10050552502c00600049885040c10401700d9040380d54810100079250300000c0340141045d2000c0b49161015000c40104005400c0c0d1801640341c0e0382c0b41c031505801913000800460b0070440842104d00510094000b484c400d85804492808920703c45259840711914180019 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 600093750 1250 600092500 600092531
    0x705041b0f11060103060b010e01020c01020a0b1306110901020c0109121122050619050906060f0f13140901051804020411181002070b0f090d020d0501390c0501 70
    0x6003e5489000041f803200754a400041c00070814003c41411035000020b03014041e41c0100313018140c1504198125402d036100d0070b03c1d26608480c00c1000f0081890031031098880c2c0c114801624032840240d003543c4441401500441d9801040d004800011811030680000103210814444c1c4d503403070181c040d0b10034050602c0c4d0894020301892601e900d15803200100f11a501d0403d1300c41c08583d0b4103c0f001400c9508002c0802c1011500a111500881000941400e0420310006660402c014100340a0707450f804107041000340c4045220b60242030001c03060700300591414194560603103a024140406005403414082000d5001405c26038206070303244a800054510700004082d0b449820000301601c80101d0140b14808242c5825a01150000070080c02600c008000711103880c1c103601c030510744a113081c00000d8407481002000030352015520f07851404101e01904642a0a080010f107081fa43d1050115076841c107d801103103111300c042450071000942d0080714030461481c000c00c00001d03044200346189 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 600095000 1250 600093750 600093763
    0x40c2702040b07140f0d08042102030d11031b130806010914060f03060c39010f0b031009030c0219230a05120f0615030705041b0f11 58
    0x40414000983c0c40c05003e0924401036103c91031800401c250544a403255845402d0322203a68100b00107400811f0912002e000028011101c04202c2203039119075040195483d80403000d802302303c60070f241240002c0c10303512040e00d1180b020030007140310a07a160f12a840c29540034140700403e00ca00640301203a200400c2040310b02070710401d000011000c0582110843d49400241070611a00ca0095107104984021079001d8100710350580040c1c4a40c500110201c1103190b45040f09078180511035500300360b00d294070721841da51800900070072189542005450543d810440c00fa41c165004100044c9a1076041d0300800302d290082c42c01003068200c070382c0051202562104401900904030100380318a082c20091640f00742c2e9400200641c0c08041c1300412600e207003611136540710340c85195505c16050400e0000d0620007012400390be0061504504054a6400b601d55485c060b102d14003000c140c030708151082000b2007044d4141a0610020187d003166010586203a9008111660f03400406004040004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 600096250 1250 600095000 600095009
    0xf02060a0c0b16120531080304080703080702151603021e0910090e01030f0c121505070e01020709020a1103040f09150302061606150e1905040c270204 66
    0x5a02004000c50010103840c03040010340c004e00e2500c4184060065800740300c5119084804058060694100310602c00b01c44100c0302038002c400000404c001c00052000401140748a070311413060a440fa154200d03910b81ca011003040d030026018021035188240c0c107003070781180111403030058a40345180e038a032000304414000001c100400403800f80590300d4444450200d00c0c4840c540a1443c51800500000c40342d4103202c080d000d03030310300c180c1c10041c80b1412142c030001c0c0c0040e000b60700840c070b01c40c0360903030003049507903104041c0302e1414012550aa12443c01100400016070052070000e04140992000b036002a074604188040e03418400c9a840c03090020b0002440700e80298210285050b003e0b20503540401d03006415182c80b40b41c184010303030366403080e40e5204010300070502801e1010318011006001d400310038a18140502c90000c0e040201d0501c40d131007035003114035581c0814244498201512000d03600100b1110b40301c00c00707001c002c035070f40c82e48c0801f05d45981ca05064588148000400c982c0030703800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 600097500 1250 600096250 600096271
    0x3090d14070801021603030b1f0c060e010506130203090a02030d0908070b031b070c05130c09120b040b0705070f03030605040b030d0801050f0a090204090b15070f02060a0c0b 76
    0x10a0580e80c00c1800464000c0880500075842d00400e2100302525000c080700090a166850300b0200300303a110445e030810062a410380313507142481881e1014001e0581e84c4804c0301c020b0b0a00344a81c0d44410b040c003031107004840c040c103070610800644a031080a500010300c2152680314400006015035020440c0c8a100b011546403500010b007400c0304981460069007122101c481e003082480100200d4080440c240e9940701490b540711600303403030040c1035040260300c503c3d80301c42c078089221b008a085a000c06103034002070b103403000410381d2071141c3c0c0c160070009103010b008001810001000320b40c04040c403c2d0b11050920300076180c004140d59041c00b4007035001302074000983d03c0800f030002c0e05043c4641c031003407071b000c03002400b1041031440020a0410b050003510b00411010721500041d45603600c0c014050700c88070707800f55112625030084170014842c10180130311a070382d4440007000345407001d02194010f98200403140d019640540074054145d0002c0351034400c100c3d00d05132490110300349055660041d6513011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 600098750 1250 600097500 600097523
    0x2090403111c1e110f030d0e2808040b03090a06180f1202010e071805060105040b16020d1217070201060f05040b010309120f17040209130503090d 64
    0x300c0451030514000e1504541010006054150540114005103203e403885400c0000214001c403c850441040080710b04ca0312900c0e641e030103414000310141c41c00300c6004404000071444101d038195504040c0761341d070101c1c1741442d65012021488050480d80340c2d0040449030b141c41c2d030300c001043e056402100e95481d150480b800c014204070282c041c40c42500d1010050601100343c80d01d45140a0385035031001005842684a81c0200c14000e4000c1101403102500355034403159200c05421200e60100380340c000c0a843c0c140011240c7d07000c2c1c000e540c15182c600300842d0a103181c1882c2e4945d0051419810b9034800031120038000011181c09160fa1200d0311991044800e0035500d00310070034243c01920032425a41010b00512071500300c6072904003112001c039000b04404407501d0060300117001d6000050440056407c0c00a031540d08804200210a26039945103880861000300ba98018026a0020350100d8554042000305400444903980980203c05992608200c400010107003043c2d0817040301e0000001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 600100000 1250 600098750 600098777
    0x40b03070b071112030904240e0114060307200c0909010c02060109021903150b0f250b060f040b03010c02010b03120406020d0507150c05250c2102090403 67
    0xf8084010040d5003902c5903c840050800030790344900500c85803601840e612800080b06070001c3c1500c50008038406000c01000381c4801582e1080b5509010f94000000b460302c2c014103030700f40841107030310410440c3c2c0c9840c06408540c0d00d400c40d0317541141c4400200e102c5c50030500600d9440c0d14071580940f0000c2c000281d12902c0ca10041c5c140041607010b005828418030091650303d046048100500d5804e290004510282000c80307035405809800030000e100012070070700202d014442c0104115510f43d1085607203001a007000d041c1c203108240c0010000e48949000c65014205030400d410f03c03403c001c101003005a80720022030300b103c150b0011180140c0d141d40d094415800c0078044010b0045424014605d01400c0000180d0f0300c03c00c0d4500402009000284c0c4001d00842c3c03100c6810300030741d0480c14032142c04202d000130450380042881584800007a0015a0500d049101c0c415845610852401095141c02c1b407081d030925204010f00307000e4400da0b5690340140e42c0c0c1142c5a00c00e9100342c4420318000840b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 600101250 1250 600100000 600100013
    0x304122109110301050105060906070c12030201090317060307090507020c03100519050402031b060708030403090e070201022107050c06090a0605010f120209130609050708160b0f09040b03070b07 85
    0x1041e0049001340d2400d001480b168440808031209a1019100c480da600006c0c504003040c48507070b600c041c01c001c2c10fa61002c0101507064100c40500c40c0207030350701040501d034445c55500f007803400d9032081e5150380044410402a280d07a00440e60200031401501e40300741e41000844c0c1000031411308000b006560301d042124405014140385101410114100031524066010030781c0d0b81c100e141c009810a030803820509450f641c10048a01f4030b6481f080c51a140e0a141c0341c040e0941c03a090241e0305142414800080302c5500c14070a071150844640b20300701c0d41d1594038141042000b000790400c4104101000030b410912000c1120b02d006240030001010b000306242000c00441c0c0c0182c210142c52055000100304030030341e90301c080a1350342d01100c0e603401c1500c5840000c00141074401d03008020b94145000c03001403000100e601012a500c841c03d40d9000240300c0009c04827100d1601945d07912020a0000126459030240a00114803000e0320010303c124603180028681211035100900e400800546801000742 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 600102500 1250 600101250 600101273
    0xa050a0c03020a0225050d050c030106060806010c0f031101110c010f0c0921060e03030612010c0f080901020c0601230103180f15020d02210108030304122109 69
    0x21145000c42c200b0410301c500075240e40f0030a6034030502181c01c411081030003014421980c000c3c2001428401f140c2d919181954403100b020303031018402d503e002c2d0300040b028040c41c00b0341c0c07103960165103945c01c03a0030503650302d800500b040005404011011142c0a09080b0034884c4007a070030220443c3d1601d44081d101c440d82900c2440e600610342c68100440103039401c0e000300040041d6801502d62500c0e200c203490720f03501299551a0094030b118101003c0d0300e510180400194014241a0350400c4100740044e031190986e0108596000044c0e000003031094898401d41d101a00902c820300058130780702c00000c400380303020000e802880c0300c2a807a11a8152103009048000300440080c241840f241c5210b1104100c004150b642c06003546410000703040411001100501d40303002048000c6407a2910304414400039000f82041d240b0440341080079484045620080364126a60800294030b0740e50f880d41c0d40003045071800c00301010311241c4a4100b071749219002d0103e0840030400000550308440f030034160900c15 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 600103750 1250 600102500 600102521
    0x2030709170705091611030708030105180f13030c0b0411012c060702040f0f0605040608031201030212030d180b0a05100b0f04050301050a0506150a020c0112060803030a050a 76
    0xd11415003000030b6201e2400e4283d001c110320000300605e401050303090315034440c0036544080700e000c00940720042000040c0a941030f5181618024615402c400c3c18030f1800b078040da5011512401140043c1240451f1840c003001d0a1080c903000f445607429a840451003041543d048a0300c405466402e510355910020041d0020400c4407011030030b000810005059441d100c46d8980074400c009001070540d21180c1140d81c041c80401d00400550054000d094002c1205020f4144078604040700054655000070075a054202208003203e41c0f6461542040f40140000c07100c2ca11030b000900191041c0f05445c4200180c820114a003150841400d1a24460b002d00081946107094542814410180d0900e85e07400252000307032504e250f07261002050a03c0c20b00581d1301c426070543c00c180c208615045180c00c01c41c000c60b000e4460b22071a00c1c01500200280c0079a402c180c005034005107002017158070401610340c2491515000260850320380c40c540f415a8000c862071a14903441d507090010030140d62180603840b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 600105000 1250 600103750 600103753
    0x21f140f0a020609150105040b0a0e191a03060c22030303060302041d0a030c060204080d0903020f042d0209042909060616080d06031211161511010203070917 69
    0x10021383c110281742c89010f00846011344d95030341e1540c0c0181c0722070210402034040c0c04500a11072828002038282c0a03041c00c000800c00e07080c00fa648140e4121480c2c0c100903035a0082c050310641da80c00d10700070610340003a0041c1d00c02428151980003224145440100558001da42c0801e04a003580180030030b03541c0007042400311402c02c58990038100004501240c0e641c3d403500d40b0202e0240b450524002a0140da0800d0209000d103070b90103018950401d806074212842602c2100e182c42e080001c0104941c20b0f110303441b02c0301e945900c9104000d80e42c40b10000c07201500d0b0b0401401c00c000b200c007040484420801d509000014103182951350135000700012100d0b0f80407600203c152070520041001ca01a03041d5107202c0c800790000070740802040307509840c011a80d04c40704001c0d1650720704044e211082d941c04240c01103001d011001d03140f10004145400110003e0030800e001c03500c1d10b101c100485130407241d5001003114400d441c484a840a000940c01009580d41e0b85000604090280800d080d07a108000000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 600106250 1250 600105000 600105013
    0x108150103020d080306181f09020a050a110703061b080a0501030c05041104030614160815010507110a03110a080609060f0618040501050f07030207021f140f0a020609 73
    0x50741c90040f10701e0510b61281005440b900c81c440842c1d41c0700b03209101201c180c5501002c1100c04442d601d00049803100c1303100c881602d25603a00703070381c002c0303214008203000025010030a84415038065001d11240c80f40300000c60758a25500c0e1205412900c0c0d6049103c9400c401070340102a5a50108840e601703c1e107140e000700714039407556494207086042c038401c07903010700e81300d8008a42020507181964000c40e0030a10038010340841000d0501d52400071122a041014a0361400003080c0c8540c0b051840f40130200b100b500d807200d0f410019240c50704054400c41e03200301030700034404158468450800c0118464a0b407460720507400c004100108589821a403074961159040115040c80003904070b41014402d07541e44c10301c1c1c44400216806000a00c06200e51400313050501003003040541c00340d0701c02c1900c03030210b0b1103544944408170103030f00c0740c480302a502c80d0b00208e00042c1c0c1c00001e80060500d45030350404008420101442512a4011000d9000944004125526401d4040c03290903406841c15015140303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 600107500 1250 600106250 600106253
    0x3031602120a030531050f18100515131a0415030e191a060a03050703030f02060f040b0403030e03090a0b0c0f03270103020f03040516050f1005091c0b0108150103 71
    0x140c22411b00c41c55204480b1818a80c2003500c5259407041160103030124a4248d01d42404444082d4205204c2c41d8011050248103910f0461864140c0d900580b0001e000403040345000030141e10b0860b001071803000d00c441080005101510388605e182191610744001c40d4151058034003030f0030003248032054189011031107030074400140300f5509001f00d45590710304407002c8c0e00e504002c40c60115080c1c02c003e046100d00c10001c010700d600103508982c0c0c445a603007110110f55820524490340e10054400a0000c14030001041c0064000e81000c445515a101100e08000b0003500040841c0304a0b84240d0b864a00090a100400d800340241c64819a200009611b0000f00c0420f44116110005582c0923545140212101c0e60384a0b80445030324030805208280c403810300e070074100c3e22450040c101340e401c10391542000403607041001c400b031100f01d0028200c0d0a1500341c05c00c2502c0682c0040d9030740f03905c000c00c7c0520801d41c01c509484100440e000d0800300b191981840034035407800100300911104421481c3c0100f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 600108750 1250 600107500 600107587
    0x1a090108150609071b060b04140a050a090b070c03020f060705090a082d070308040314010b0901051f020106030b0403080103050f031e07110a0e190b03031602120a0305 73
    0xc0031505c40c40b80101c20103000d410f0400c020b1240d24003c5074014100350041401203140c0d0311540c00760110540400064451007114070440781400301c000c0085035814000b030b941724090b88000c502035001e401035840713608007070521908041c1d04a4003440400c001080b10700705c508101c00498080e0040c070008015000340100c101100c00e0b600c050106900d0010140840181414400e07140115400b04c5950384864903440d04840307601020405071070302e601c1d092050102e0b1030001c071418102c5034040c05140d410102d10800907007104201030318000b51340d200c500000000303280f940b40c64801c5000365941c3d4403650445c80d01c1c40c204181404960b041d07a106000c03038843d0880b00c14140719483d5041300d00903a604e01c03520b440c0213900c52011407194000c005000c000f51100000003054450381545800c0c41101c00340d82083ea044842007868640c0580c07060201517081940019100c022a0008220409078010310340403d10345100343c170040380040c0011a403100051000305002c0d0f00c6002c91680301c1c0f620030f00c0d5010300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 600110000 1250 600108750 600108767
    0xf03060e06150408060901020729040809030c09040b06010825080a1b020a0203190b0402090403030e0f100605010c02060a0f030213030503031e16031a09010815060907 73
    0x1c51003801c0460000e96161000c4080780e004001c200180d412a103888203c85000350410074041d5003c855441c000780c4540c40d23400380e80b030140d0b0105124580b2600c980d1984c1c0b00ca6080041d0381601886401140020b80ea00c0030019841240300304c00b080007600c1c0034800180b07103180141c803e10400400c038018081540000c0080c2d0161030755490102c002d0b41d94401002c001d0000100d81c410104014402d1080f51603000c981180664002c0d0304036402a0b80820b501d10410b422030b14094102c50060020030010325285942c56001802858041407040f00d0111940c10440440d11442c4079621030342403101c4400003801003e008040034200313500c1c5a02c42d900400c0d800e114449030401004082030220280501030781c1510100c200d002295246651030b403070490342c0eaa009031459161084082c454044a01f81c109180744650b801440303540d44a43e00d0070066000e45010141d920161080e000c1401c0c2944490103100c1c003c144510050980000c443c40585407207501510040c014456001003181094120614 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 600111250 1250 600110000 600110011
    0x40608030a05190e0a0608091515040902040f020f070506010f0608071803080a0504030b010e010f0303211103011401030911240304060608060901090c06050f0c0f0106060f03060e 78
    0x70042c1e90f03204501e0407110f4070800c001d00c07940441c4031600071681a070700490340c03480766502030119000303510300328040d00c0c8011040b203a148400000500b412941d04094100340b40e00d0f0b20191002c40e142a501405005a030800590503000c100c011031901d040c40803c004150040c0303035150303040c0031450030401b000709050300040010b0280035002e0040c000003194890900001c5d40c210100d240c42d150700a13801840d41e80948000da6883d41031f44000306002d003140031000c0c1285e1251444010a0340f5582d8161520409171611002c045000c402e41d159498a501030007100828601085680390704186041402180e081c01640c10145800c0701d00d80042c0c0a0114401c106504840c008141007641d80384101034150715549502402e008410700c410000580c1204043d6000703030056605599450394414200d954200700a44080c01d600d60800110740640004e00010101407511440d1410b0012081e00c0c04480f0f12000140780c3d9510340820205a2040441344000103500c0c05010300351520720a1105620301404 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 600112500 1250 600111250 600111277
    0x70f03110c04060b030a0614030706030c020f0d0903060c050940020703020d140414040e19030f0315150c141f02120a09030908070b0702040608030a05 66
    0x1200311000030100040389080c48020014032119454060007030b416082900c480c42e41e1400e165000c0b03611411009805017021003d0000d20000c0d241c40000c8002d4403a11100c41d003580200c44900c140080140b050031750030032650703c90340b05003482d500c0c015003110301710f07110755040003414090303e0b1440c2c0e0780c501c501115060746899201194148000340722407015800c3c5502c1d00b070500403294040c040075500607182c02c0d03000341c080e1001960002c0f802c3d50b2107110195150902c0c030040109100e0415460345124024102400010340c90090f900c0041c64034400310822841c04240500c44c03002c040e8040450800c00c07615190611040ea0403141c40c4090b100b99010f9000031004a05e01c144601d44070b0600008155004175035130100100803000181c83c0c0c00c0352429614082c0715140e0400301103542d80211071140350001c00201181d41d4124910000300900c2c0011420011081c000084000b820400d26001d40907188503140e55101c20b0bc1084102e0307005a011038003a400030b000e1803503410b0300a07064900c0c030843c800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 600113750 1250 600112500 600112517
    0x905100e010909060e160206012105070b030403020a060b0f0a060c060f110d06060302070305090118030203030a0203090f120601030f080d02030a0504050c030c0f010f0306030b010b130b070f03 84
    0x100160707441012a08401c0f5014501000040d0705403900000078021040f000d88a8003000c002c0c030040381c94010901400d0790403201e03003001031001079244040361542801042510a22078032008152420350007039500741c0041e442030400c4070034051035100e5682903035411a44002c002e2401e40111f0210009803003044140619010910f0900030340740c000b029030a8981e0301c208418014809032040341e4110b0100490550b06d004808155580a4400c8030003040d0180c84a508003491140112210703c0450900c1c030900c00d81e0000000181c4042001c0d207160703199a000303162a11015024060134640a500507440340801507090240100d000c5203490540f41c1000300c1e00300d5080036003030011092181d2101c0400b240e2002040044c602d841c3e5102500a9110b841521203007411202015078640f4281102c0794005104095030760550302400501095560342d0078003041c200d94a884407241204264483c9070504000102d45040c110380b030f0014000b0702210f0b80701c80c6c00c101c000d8075190081e545402c0b008040c082100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 600115000 1250 600113750 600113777
    0x1011060a2703050f0316271703090414090f1f0209190308122409180a0b010302090f040305090603180604200f180a1407020a02030d090510 61
    0xe8080303c184500d40d00004d5a2410513030410141090380c00203540015000300e908040703201c00b101c2c403c20700d140030740c640401d03083c10b107805602840d0645440743e90398402004412050b442d20700030038440240c1c0744103d048070320b403982d607032801d105400710100c1c151b401410780586205500c9024004810441d5801a210304482011400c1c00c8091106c54482c50106d0000104000041e4010a0401e51242411141e6141d075149080104410030f24a081440c80304071002490412246059202c0c050400d05040c4c90503810217241030100e0000181c452300000801031055082480c0c800346c00c0302e0106034210b503031314040e14010918020040314034400c1c0000808580c0b01801800f0a8840a0b984001d480d56401c1c01e240c00c00011a40d10b004e8070054868580d09c01041c0b42040c03002c54445405403400c03c808023403024800207501c00902100103155a5144600c0404c4803015007032084040d6002051041858010140b03084000c0b2610010860020310510154407000c0d50740041528070304051070110440e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 600116250 1250 600115000 600115007
    0x140307020c12100c080403050702090a021312061407050d0902030c06040e1819031206030501050f0712090f020105030403090e160e06030105010c201011060a2703 71
    0x80418440d4003102c0520304940c0c02d040841e107190145040300c000c0140780705480050b0703090381c001c440c040c01042091101a015040468106a221001c1d41d801881c0c00780c87d409400c42c1e003410750004982062051423039010460f50f07102e1156002841c1c0c0703242c105850140c40043c20740c426141c051025907100c035080c80441d102042146000000100350310340f6aa280c20160020403811038031200611504500c440f0600400301d0080c60040d44802041c8074061251000e81d14002e03481e41d100c100c81c0c0e481c4000004903400380f080c05d0007400d1580d1480040c0c140f8501c018402c036181c000c0c00d45030078034007a808400517a4520745401c840d135081c2407880d200e0340c0d281070a444201c819800340c441c89a0140402040b00030455224800e09074a032100383c902d9240c0414800c04d40402d0141601060065040c80041070340171010b1110360384100c09080d41c0602402c0071801800c5401c0d0660040781060f10301142083d41406520350100300d41c00300300301c0da90203500320703008003010140c87c12100d007102c0b040801414030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 600117500 1250 600116250 600116263
    0xb0306060f041809060c09030302030322080406020c0a0e0105030705010c0f021206100e0c040501051b03040828030804030807020a02040501080319110304031e02130902040b06040614030702 83
    0x820b07491141d00f601c200d0800030b02000e41d02294a645001295001d542c0204090016607070164011800e581d03500303218004a2419881c40304550400404410008600d8030080010780102d07400f60006205540a0121030b400039000740d041300c07410700010300881e140001c982007112404d01c0c152300f050305282003e0380408111306010b504059140c01a603880000003540300d000c1c212181d403c0c070390706a4400b4850034a80c015102000200740401c4104081d41c4254041d1140c044c1c1e51004014940c0442c0307006240d81d00030390142565400c03951003c00c1459074010819940001c1700130041ca6040d03070342d50003404072800910080070302032890003040a0740d01c20891a1681907018108108958484141c656682c0110303060702d90402c1042c040030b1207103108101010080702004025800c2030b0840e540c9d9160007400440d580d4864000b030740400003580d00c07001c4a0096204000000940720250b0043c44196400701e4440303070241000304800c000d52a8000c103c240000035944805413a500c60020890a000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 600118750 1250 600117500 600117509
    0x1101050405180405120a0c02040b12030d050a050601030207050c04151a0301030210050702010f0503040302030f0d09022e080c16080c0706031a100905040f090302160b0306060f04 78
    0xb600e4410090440b8074600d440d41c0514050f804881020208201c0c0885520400096030000380d440a138040040c1419000010504001000c40c01c40281151a55156401c011480800d26444a05116482c42e940c4500c0e50403032000c0ca000c2d881c1c00c1a94850036562944402914000d60f80c52038204030711030150100038064201908900c0c4054030600c207100d881d0300203001c01c1e449070000408403503805000d402101c03401076040c1c60340c40c0c2e0316043d1001501c2c50303040104194190700007000b07005120020799008007807058108500041003621801403000c0786500d103450103510550b81c1c54601c0303124000c401e10345440c1010315106003035945088c20f83c8490b00402d0320b650f0b21b21504c0e03e5030800b04503600c1c0c080c0c41b074014008202c03001c0c55901d000490940362000c0c0c4602800c0d02003100040541400036058502c0d00803030a02005580c0d80d14007140461b1a03841c006030030342c1c0d82c841c203140406038140039002e07000b80502460103079070f42805500e454911020b03098034407a450004040f011910601c0c181d030000c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 600120000 1250 600118750 600118759
    0xf080c0a0903170a2d0c15151403150a0903110f070e10050604090e0a0c08071e050a05040929010e06011b02120f03030124050301121101050405 63
    0x204905400d50455000882944040f8141701c810440c48141e1041c030000c9288001c0c90890b412085600540f404500d850080c3c59a5114480c0a50355034003900405a40303090903002e58051a140c03901107a4141b90070000740784260850100aa000c00072240140e420144031600001d11070181c0c070f0242d071015035101c0515618010f611242d43d9051000ca08030741254402c0313086444d1340e43c0b800f92414680c0118021503170300080a0100f48101c903080d600c846007550354203041700c0c05079410781c946070044542a4000111a8800f000c20300c1604d0307070302c4020071401120a61520f599801c0100242001c912405001d00640da40c1e0758000030b00043c0350420248004841d01210440c400c50403039842d0217400d020b00c0a4504a04020540d0b551043d038448510b111603582210f5140c4042d401c1040340039507c00d0041c50351040000d0211107007000e10040d0300920140007000803540c02000e146908050414a07142480300500c0104602d1103d4440704085560003c050360390f0800c5280182c52030b02580c3c0105421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 600121250 1250 600120000 600120023
    0x61c0b04050601060e0102030f040603090f020d060c0e0d0b010b090102010212090102090a0611030306220204060809101b14040e0a020c060c1608032d04120f080c0a0903 74
    0x1d114020408038182c88aa90303400074441310640059a680c800c03e11942d40d40501004204511403180d44048004c6201760354061030101140c0000c2c80c08402598151021aa150060b050907500840201c038003401c06c1c0d80c0d011402001d5110201203403414454401500070000d001100c42e8400c1d0b045583c118114041c81406007010700c0054004c3d0040c481140c003c0b516250046070940c0540d00f0f45040112800082d45590f942100b0301c80c00d803c9581e042c09007402c10f143c0d0a010111140098000740480769036401c12840c1c9002e110703140411110b4400c0c176041c64001410840540b050740d08401c00d2450806406540d61001038290921843d07000c91005400d22052207100d4010307400414070f0fa68480204d4146458003c0036180c0340c4503203082406142074888080000400680140d0303409040d4415589041900100203002003004602428681202c03030204010401031314000d0611150b5840d00c13030190410000c001d003010a0141510010020100701740c080c440c403450b0600c000c0d542c000c070950a07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 600122500 1250 600121250 600121253
    0x150f090a031211120f07112205010e0c0406050f09090f06010810060519020c10031b05071a06030f0f031c110406081003061a27061c0b04 60
    0x4044407a107010100007410401d8143c3d00c1000080c2c801c006080121142c1d203001d0b16594455020b44c8800c1c0d040302c0c60b01c4201241003a5542d9410802400441c2c407a1303081150920703042c90011624142c01500030405081c09115000c1d640343c09540a540359400e1165907100e844070054054007030742c401c640d4455100000c0101c08ac20284402d8000d5000783c0703424030300d902c0d8104504440c42c014040d000001c0c6040c4882d050700400340c0590000748134580142d81e41301c020000851420320300303042d64001080e251414101c00901c7c000003030300c44400c01c0c0780403400e0150b203a5540000f219000c602a40446034240443c011303540912466220790039107030031200c102c503807d0300440c6c03241c1100701300785804a0051406000d401071401000741804c001501985018100b480170f6420403405410301007440c24004010000031818450a51501c1e900403560200f0791140c010020b5902090078000b03070651402540b99050010b21a02caa040303502121a00340240c80145007201d0048403803001b51540b0f84090900c030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 600123750 1250 600122500 600122513
    0xb0601180821161212150f12030219140d0c020f010908030306122119090302010c1401020910120507110303041101090306020d0507080a0b150f090a03 66
    0x1120b03601c0004031400340701e0001c522080ca0f8000c80400310f10320755891010320009150145040b50319401410b02d007041d054845001c004441c8074501040c2c542c801d4142c18807035401200302410050500e07a481c4a00300c88a603500035103e00c112a055820b60080345991020480545203145250400c2c0c1c0480b004007001410041c51980320f0041640114100e00300111306507c80d007213001c19107481c40300640c45c58483d0000c0c0050460110305807506401503142100000100220000300c40100451032511030b40400d1040444040c40b020180900c8215907003000180d822201c0720002541001226100b013600c030202c54064030a10030a140c2c0302105695032050950082c044040320003000c503081225a88642040e105210010032005050b4400e100280c001103560144404030201803410450b42c036a02c0d520316080c0d070041944d21802d5030307c40c020400179903030100b0303a0359110900c000c0034019038891001140542021100d0340307072072000001e01141980b9010307040751103041d000741114461941c2c86c2000d030b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 600125000 1250 600123750 600123763
    0xb060a0804060518070509060f1915090e060d020301090b070c05100905060f0703110301060306080d0e011d0f062b0b09010510020f0106080f0f07120b06011808 70
    0x881d0340070f00c0c02d00402c40300ea101c586201c5000c203903000103000031070414080100c101780040555034080c52044040e002d0385c4a0f0044403009450080c4c10314001800c1113040f03c1c428181780700c0780707017001881d007010060025081d90251f00120240e41758034a144680c00424054050004040c101907001010303c0541607200d001540310502035000d650303440700030b0351882c010f64019400c044c1481c0d00a401240d80708080e00215a0064094103001641c03021140078002c56401c2681306e040880c0d5140b00802134844240603a2030200614039204008242031000a0070010004008008500301c514041d03105889001920312003960007040380d620ba444401c444004a190320b051104890703010303040c94440255a00503002000390052031030f6400d070f00740b1051181d41d011b61384c00c0750b0031031040c4044080040000e200d00c6001e869034101500984403074a03c21850000c60210140b140c0d40301040400c02d000344171200d003081951240725141d0544403407004a844043e051820203001482110000b00300000040300c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 600126250 1250 600125000 600125003
    0x10e0705041d03070602130f0b070b090f10022101080127030c06090206040e040b0f070219061d16030b06060306100f050d02210901091203020d0b060a0804 68
    0x1d000341000b481e244846024550803461055005012031400244203030040d0040c00840c52240b10110794803000200c503004079038003600780040300050100c14001070820491b44107900300d0041c07420440502c1602c0d0380300c2c400085002a2980841d1103078189100d5083d10341a41e9940c3c09032442541c560040d103009001035191142402402c0d8444211500e07401d82c904030322505a19141e22001581c2c032140064690440202c0c5e00c8503003000b000c1a0865001c8120380102c3c042c03e00140903107000d0102d4001650080d0007041558090051220040030004040310015400400451a000240101b04500680c629140001d018141c96072204405078652442224010142c490242e243d070b10a00c1480d210903100e66411200124519030701d1406008030b043e4400040c50010302d441482caa209049800200c41e030003080245020400d004d008806c5081d82002c07002008008560260b582c03441070700c03d451111400d054000caa41c9040448a9201c05c014020180c03442d9a281d8140c00010a0708804580 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 600127500 1250 600126250 600126259
    0xf0e031206011b03180f0b031501121e0c02010501050609190b0705060a141501050310030b010b090a150203030708070203070611090415030c140a0504020406030c110f0a021c05010e0705 81
    0x40005440c6c0c402000383c3c04403042e2510b000e01e1611240c18000d03005050340d2a050620010340986c18806900340b14040e0b2418110f82c4049a0324000e40002781940c82058582c2e0841e81088010f01080e1784003c122541041c04480714440c1299a0780c2107103420a082e8001040ca4a001c1100000c1c00f802190541c4140084101000f0200340c0c0389030624144810744030b401d40013408041c00f80065000324019900f001c054a50041e00aa0343d550381c2086038003d0700701d0401c011000c15603215500f04404004043e0400601c0c507042030a0840d0029541d00000b880c4c5020031940c075021038110750090040711002070b003015080c40413403280c2c002c00c601079020804d4180581c0c03400b0a9a1480100301c0300c2c0c071003500c0d07104881c5d0b00402d203482800c12085000026181d44240c80d00000501ca5840b440200018003842d10301103203c01c0b0703010b400f034a807900d01441c00070b140e040f4000c00c030741c001000320f100145160704450b40040c078943c00c41d1000c3e80c110060700043c071542c41c2c104442c00c0070100052100442d20101c8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 600128750 1250 600127500 600127547
    0x6020a0206180706170705091504090f020f0304171603050315010503070c0b060a09150602010506060f0a03110c03030708100f060503181c09090f0e031206011b03 71
    0x10ba4540d0ba0003aa220300000640c11120380c6002580e100310706034008207189002410101080c2c006000d5004003000c000042c0e0000504000b02d481501440d106280ba4000442c00d2131401000e0500900c0020002080e0640030800600381d86e0108065500016051094190041e49440d001d01a94030954623f451301d42d200510049a610813800c80f4814141685c6914100c1115920390803604006007034117910840801d000b040701e42d060b1040507080319020032521003281c0f600c03201034216940500b2180c0103160412001d4000c00075141290345007050f510380000c0010058407986035901480d0014101800004180510b0382d901800c4e031409040008500d8942030b0340c4208142c28200f40d4030a80c0302007101880019088a40d1100d03241c0d1104803113041d103d20011100101031400e83d40b50070400420032182040c005101584213032648410f440c4820446030300602075081e80d900915071125000c003841c80010f0690791242c0e8600c21030038002c1c03038100450013252a01800c0c4200316400101c0070307c41d00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 600130000 1250 600128750 600128791
    0x80d050108070f03110108090f0a050102031e100b0309070504020f070201081609090902030c190905070c110409020414070320190507030201230610020a050705010c0f06020a0206 78
    0x2c01c15030132281e02c021040d50032001600195000c50000f031518501c1c0c02104402005002c1c21f0115100071032041d00010b94034548980320407041c1c1c290715904414804048100700000c4c078001400e10540c0c0645d40c6580d101e0761050120b0340b030b00c2580d400c1580c100780003103040c42903144110061b105040c401d8030fa18007a6030342c051150940018034100d41d0300040f28548108034601030f60303004003499400901601d170140e02410204400780c111480c04c50400802c00d400304151070580c42020381020b094a0410a00400c076200d8201400d400004540305555444800b011542d03a0703444a8032211945002034864a00281c01900824100c1180c3d0f00c5418103850b07203032426581c1e004441c903160319011801140c1d43c01401c12215034014900450a43d940c4500e00e00b0080c0080765100250040718915101c40d141907414888604440c040b84002e40d804148802c00050000c1040000e8400a10f020f00690031182405412600c000c0b80181009100289000e541039012034514403a04240c2245400207007075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 600131250 1250 600130000 600130019
    0x20a0e101d0f030106050409050304050907080f04030f020c0d080c10090503033c012117132d1502100c09050405093003040f080403080d05010807 64
    0x104507005510000031000c0c01c0c0140703010070850011490240000421640b46c001150444d00c400b4401c0e40c2d254004034082003145014007019030b0010b464504804207051000c4040c1945d43c002e0001800e001c002d41e4202d07065842000300c1610090000c00c00204030125050200305a40f202c032800c2c596002d0640b40442c00007850040011855100005500d180e590030f240c5401301200c0103100042401400300300e080c034480e058052040d0f034108c002c885083d503d4000080c9503694107500620a45080c4c2014001043ca41d0800b4456034a80703d202d10f94440103840e0018112071603030400989070700b404034106640c9030070a600003034000c0d5046918001d5500d400b02c0c159002c0b96216440c0041e4000001483c4a6403c0c0d0004403800001d82054070503aa00c581c0054207881b0b0031901d4210b140c2c1300160388944c0401c6121800340365001a016440c140c00500f11414440c0300042c40a0400211000080100321040302141d00a5400c24081511381442c030130144090700003072203800040d12a120021805424 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 600132500 1250 600131250 600131267
    0x31a030706090e0603011401030827010c0b091204030605060910180b0a031703070314070c1b150c170f030103030806031c0c03080a05071407060f020a0e10 68
    0x156512604102d602d0525400042c240c001d0000380c155494400314034944658202044c003171840b9520305a01c3d40003115991030031485079001003070085c85250020240e66041100c01d42026005240c01c56259240c001035490421a40c2256400a0f00000c0000901c082c540c070203801103408980000c2a505c40c10720202c01c0004d180501c02c1d003003c0100e00865080681e40c0003074041c0e60060320b00b403072559580d200c810f00011100f0038001c01e510000704000d00c099040c450a800720369200d04203010390420071001041c110f9a200001d1041100f010710114140140841d00018403d01000d02640030140000034562000302c1008c480034980001c0c0030000381c0b080030135030b00e005041c0c1d01210304583c41e44e02c0c00c0380c0c0400080c1c609a010701402c446c5041400059100168542c2c943d2503441c640181490f00511080d401003054090340c0c80e01c414021b040742c0c40300008540034a40d180054031001e55040c2940141030303001944217401c2c4001101e060854108540c09200103007180d00c20103510911303d00303441504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 600133750 1250 600132500 600132509
    0x42020c0c130903141323100c0b0601110316020607150903140408061308070b04120e1c0615080703110109090b0d14031c02070c06140a050325031a0307 66
    0x10b00311740c4140400c0100055050010400c0b08031068594211800f244001105c613061200046c100c0307003090107100280306410741120080c80c0c00743c2c4840c640c0c0d5a10361a809581d02c00080c40c0c0403041d0041c10741d42d520060340c41107608224200c201900d0090408000c188032401140411030019141840e904680140d5080307400e00ca029280b2507035461100b02c000003c0400803550f20300141722100204144040d101c1c42a442210016012130018401030401005a501103120313443d1800404003c00300d0a0f0f800c0c8446034001070104d0301210300008400c05c40300c0b44e0054134591040325030000601031080f0040c00c0441d000e0300c42c110740747c1d00c5445100c2512000d03c4510380240360864000c0008001605550480340c080050328181000003c00d507c09d07800d150b0744503242ca80c001c600c1000340100c1281810040800e8180034003800710011030082c00d801040c400c070f42800008000914507010f2444e00d4072840c503960031008003210320b404019000700b881048140401043d42110409410002100782c2542c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 600135000 1250 600133750 600133777
    0xc010515030d080601031815050a11040503101a030d0203090118081902210105041101030203060a0b07021f050304140f1207060b030a42020c0c13090314 67
    0x2940c0d16001500549112047e52140e849030400c1e0304007040604500c00918440c0700c80c045802d00f05020745005860b800e40d101500180100810041c1e03540009041078100c50740080862030904c100e500300c40012400c845640c05008110041244650110061552038001d80b5030800707901904000101c008454025000b065011081d4000301c1c040c03808034800f000384020484a04101356420003144000440300745800d9a4483e420700c030400880c044086a402000c0c13070114154680b403c0000c1069803113102d5400e80800c0001c40200b0340d1901c5402425060b040e90401d00038843c541c1c00105181d0084400341c0d50504e4201c1a4080250085200360461107a01c009000b81c000320200e4100641c45801d040710f031a03948e01c0c0616460780b000d0054420090285404012144c1e00c0c10600c0340e01122010784c00400c0d0b0340d00c0144107400f00710354494031400704041c400607118040d0758042ca1408040c102d207036901000c401da242c11905030700d40003542e8481c4256a580400520101d1840a5004180d81e1080c0f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 600136250 1250 600135000 600135017
    0x60a090e07050316110f01020a0c140607080c0a0e030a080d0e0705010e130e0715020d0f080703020c0f0a06020306030c040b0d030c020a0b0a05180102030c1c050409020c010515030d 79
    0x192046141d076600c0031100d802d65402c20065019075023242e12120b00328004c00c3c1c40945802c10300c01100c0740590351030441c1024003c107242801d0024025131004100c0b00300307424041003040b052841082c03401c12040707019048480060b51800e010a00390054004075200074140017144031545000310b000400c44506842d80c100d10524001000300301c0b01410a00c11013155038802401da0a20204071a400801181151120b80e48020bc002410701c8a43d5100b4000d01c0400c045210010f036110000360740c440c032103240041c0c0702c40e08008120b00300100e5210808442c42904c1c000d00600000e54015406044114200c0300785255580512055480c2c228030154030450080000c4040390050080380041c074170050a000701c443c0c076410740c07803c99040160b0140c001400400e1425402180c09226921400240000c6040076032104c0400e91300d001013400314010304a060758410409008070190f80180880f80c00554803404c08000c01c0780284001c03035002d40c3e010590038001031141004121911060031a40d910080b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 600137500 1250 600136250 600136291
    0xd1113081c0e060906041805091501060c03050c15070f090e010e04080f0f030618010305031c060504110c011a0d1b05061602010306051c03081302060a090e070503 71
    0x2c500e580795070040e81008042160342c00917640c4c0d030001c001404071030312400d031a035000d503a0400440b2801002c0103120f503c0b1180b03181124444012013070444d030304c0e0320b070022080c00545011150760090b1380c070032030303003032060b12138904c1002a401ca510b0712820507541c8400040b105000202c1e40303642c0d944640304400510000600c0700f61504020103611500076040c4902d010704542c014811a0702c2441148400d40303020040c0101450620801000c00b419a01c08000650440c0c0f2000e0701c84c482e902c0c50200e042c00d407040100d550291900010020107000704200400c400e544a01c0b145544a5901302205500e44044001c0503402e0740102c07041900b0180c665500343e60140d40f0b0000d010440400803070201c1c0c54040000341941c03480300038038030388101e4460b82e04004004c1c800907051707542503000940f1030001c0c0101c0708505207000919244440c0c1500d440311103a1035041d1142428034203150080e400c070500107040f0028603080b58003d004c0b108407081c2201c2640d260041158540030907240c80003040c0f2640003004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 600138750 1250 600137500 600137507
    0x2030c0612041b06140906071a041505190b01020f070602030405181003021003020910030221010501050a0e0111030d15060306031e08130905060109050105070b01060809030d1113081c 80
    0x18a1b5900a0000c500d0582e16854074814030789902e0b03002070342d901000c040108100310f00400702156540b22005014504004240fa01e0380f0244805c00b41d5182e64031841170115038070070410007001455a5050314001070b1942c82c02500c03640700e4090140140006041804009080c1d51401c5c4a080342c0109642c0840c1958200008149404d0005040540900550701140e4698030803d50301582507c005a0340c84580320b500902e80d60844204800030700001c0108403590b00071040b20315945082c90700301d401d1203655005a6400d0306007581100c80b440081650202065aa40700c0030307600c94099a0718200560b01c1c0c101701d0030f0fa402800000d2540203841030000100110941c0701818922604141d03007031441443c410072500910f513004010b42a110002d200f803658002070000c01820013860281d00d029015220f40605040c10b00c89c0030200802480082c103d9202401601c0101941510900c01c04882e610100305980042c0101a502e0000c2d003000034040f040090000851a41950710700750380f141020054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 600140000 1250 600138750 600138757
    0xc020d02010e030703080a030203160f0c0605100801090b250930030e130b0f060a020a050a030c0c0e010e0f06010e37120f02030c0612041b0614 63
    0x964144c0300344400800000d00603400b41001800d1603600507100d10b00381d01812031401258256900740800d55000481155101070b880700010b40204001c15603032994182003108805131b40c4918080c0d480c101d54001000291510f00740075040c034050500c1a400d040c1483c0004041c4a211003010800644c0e04200410703844611052610b404202c90b00101c1d100e0707695114130382c00908218001480d0700d01140f543d00e02006000010b80005c03408010035100f1802250203400810450f921500703003c1980100b091080000c01c51469016090354003525241c60701401190701a48200e40d0700c5840b910208400c01080d0403181228485a00560544c542e1100c400c0520340c041e042e20304011006d82d0141040e110300c091000101000645401803000c1d552408100e10304280030300c3c186c40000c0c0020000318544140d04059107410080c00b0300801242e20000e454904103d8561340c03c1103022456441c64000d40001602c40c80c056113260344581044010781500c40b540340500400b1500b10f030000000304441d0b1014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 600141250 1250 600140000 600140027
    0xe0303060109060305090c120a1203020a121802061606060803030c0315040e030c030d05010f3f0c051c08030106200a050708100b060406030f0b090a0b01020d0c020d0201 74
    0x41c0c901c1f400703580000c204491003c02c490380d91171707010314218002c00510703c900f840f88140d00c0c03804605002612400600c0142c803203180d440000d0325040d2030044c80c0200c8140c12026640240165034a07c000061100120800704098460701c1c9012000a0600401b000b12486001451341003861683d0742604861a0034141000301d4005075a08000f071701d01c1800300010201114418025600c8107030003910202520300507000300300028049001000440303c0f9101030300c1348011202c03040a0440481c591010440d4403d2a4144a908500900700500200340e00d060b09640c8107480f4948d42c0340007041428103602c0701500007001040d042004004d814424090a200e100010034401588507900300602d00c1c203081240d041d22a600580400c206a10042284102d140034a8803340941e90140740001c20a0266200d43c0c414035866201d4052424a141d215170000503000300700c1001f030700b40403004400800d403003604980588241e800b1390801d680104e044281542e8014960109045268011914540034008 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 600142500 1250 600141250 600141253
    0x6030a020f1903320f071106010915060f0801050909030403080c030306040518030a03110912010f0c0309210c0218060108070c03080a050402150a050403060e030306010906030509 78
    0x4040e0645415600501001401d55804902d40004410800418124002c5210504904030790030160888150181d9070004904e0b01704001c5a580741030503201d128410740d00905074000c00c00082594070450f808100d00020045650110300e13240d42c003c1e101c00300b40d034080713502180c5501c0c01004145001000e15038064000c000f034170300b4103070fa9030b94200403034000f00b0000900e600080208422401d051281c583d001000e506440d940d10800d506d456202d2007a11100000c040e1119003c0c00000404800c441c03441002404074001d5200300280d150080202100d41c8800d2030810740d008100c41c0c400c1c0900d8a1b41ca800940c0407041010402c1c04402810800701840140301d08011039002603a15100e02d40310800c2410721450561034080001454440010888800c0c02220303a400c001107580400c40c2a401050f03501e000805480d5030002459485403603224088a840000d100340310154803502400031248211418800003052020081e200d000c00c644080c0041c041101c200078091082d080a50400310000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 600143750 1250 600142500 600142507
    0x32107020a060b041e0605030d020105070f030b01020a1203090501050711100b1810031202030a0903021c120215130f0b130f12080a05040b01260601120311010b06030a020f 75
    0xb6076041c40c11740410104030f0240c0e495008011900f0144484807885030144020081d600d40407001811091a000c0c401d410140d40c2c0700c003a203080c0d00030801d482007c2d0f005640050b000c045944014050b10310148111800e50801020812007070164403190340442e107a8001e4940c01ca40689854010511a2101c0d513100d0700d0b02c61006402c1d500c00506030b008140300c5205d0398070a401c50070010500c2945080520840d8802c0044100c45d80d80701c02c40c0e00075030f035048506581103d80420980c00168080001a04c0c5905915003051032540005001c49618600c140c40780c903a64424141d2103d4101258000d808034030300c18825000181c11503030107039002c5000342d41c0007460100e5484800d0f6428401000700d42100d0810b0700680e1141e007110078980d001c442403000340300c2d501d084e81e50b0200386801803040e4440d0301c00007558200e0700740050307051402800c0302c2400c4030415a5a1001c28102840e62079040d0040380c0120100f08407008113000c0c98002940184c541803554580e404044002d40c00109090b61819051 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 600145000 1250 600143750 600143771
    0x91f0506040311030f1b1002030c01051609050d0f0b06010210060305030301090605040213062001020c1b0909030a080a02040918110f09010902070503040e010305032107020a060b04 79
    0x10360250001e0750042041005a074928010305150070704010024125078003001150300040a2001907501803141500c480e080c514000805a2031409021480300180d42458108000700801c81c000f00c1300340046580d020313181503071041401203000d04198090310b518030355034074040454010402c0940200c8180f0450b0540c402d401c5200007100c1c49070b081151190400801003001200a001341005880c0c01c403811413421210041010a090f814032a081c1440813000114044110502e0740100c060200f5000f03556500100c44203984844840d03030905100c4503a1744a04c00b242c02c00e02d64072841804040015460100484401d41302804014100d140c269000c02000c103400e02240030344160049140000040c070400e5141060700c1c030300083e1100b801080303001943d0b401980e44841c02d0f4110341c0c16903801aa1007500d800d00600303521481c0c0003c80c25411000000082003400801401ca4400100002051b8003d007085100080350560f65600160300c02d11002d800318505d0b038402d0114400040c4009110b00c541c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 600146250 1250 600145000 600145009
    0x3040c03150c0212160308060f060c03190c0302070e090a0606150e01020d05070b0402060403020d0c03050606010915210e01060f14010906120b060712110c091f05 71
    0x45940c070031016480750309046109070100b00100750310034401c0d140e504040e80d98004400320f110b402130203400c0003180408240350351035025030301b2000b001c003428590303460f148090459501d40c0417401075600304010504601c0317910700c1600120348207941035010b48502c51805180c00f000308005051000c880c01468500d400003840b6200f80c40c01452a00308420012042a101810314011210706034155001040000001a80003080b02d45040d4009202c2009840314004142c0501450b000250086091108941400000c0b984207048071f208000321040d50780c07690011600e00082c0c0c40707070315000d001c1e1a070300c403540344d01030b019401c1c0c401c0050b80341900517100310f0352040980d0503210101c41c05335074441061204170041c510780f5003e41074400300d80b50f1480031900001d01c01c1c1160f2090004100c0c0e00c401d01c5142880307540009180710b80c0103114644034101802d000610100c0e14070b229002c901b201c01000e503044070102e900411a6401040011140d03150050003485290215020000c0d00d4800404603640c1c0c2c0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 600147500 1250 600146250 600146273
    0x180a060503010903091e0e16020a050307051507031505040f020903100501060f02030408070603020a1106040c0e0f04020a0b16060e060406050f0f0c1e1602031e030f03040c03 76
    0x1c4c0e034a90f444c0c14601440c0259400600b18001c60780314061b003051202000c5d220a054000c1005810b1041080800b80b089085c100e0714003005005010008200d03050020011321482c0300100f0a2003641c071501d4000d01541250070100d42e90400000c2081d003000340e45400c2e44030f8102421143c5002d85003900640000c1c1c20102102c000342e10707080e070744c400612203603500101140040035140010341c50700d4240541a43d1300e8541d41700341400c150b00024180901c9104105800511386c14000b03c2d03103142894a030443d5150306a0040881010319000040c655424000d036040c001c41c0c01920460410307050110f08011944605070442021103040b00801c00500b103480307644031000d0f5090190215040c1403812074240c96018100e00740e0894500b060050103c48805503c1d04001001c1d042039035001350b00c500e5820004800d802030340039000400d80d9026062030941084142e8421030a03188001101c10040c40c017404024010020fa40c01440b403000803102c104010b50708a40105031485040d07580e580e4800300d114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 600148750 1250 600147500 600147503
    0x1b0f0a0314010c0207090903081f03020607060b030c010323151002061b040522060b0d1d01060b0904090204020903061806130f03080403090513020a120b180a0605030109 74
    0x29940e045544481341d05001d80c60103800e03450010300c118900c0342c500030903208003d0218800b00c0c0c140122a64048010001c0d42c00070f56001c1c0c8a9a12240c1c1410300d0b600410b000c2100d0740c083c0c01140340440c155886481098842486079280c101d03001c05249458041200c010210103d282c00b00c4501240c0ea55942c03480d02c96641c0545c0103104601d0040f42250b0700f102c508001c3c3d8040350062200340440e0751510071403007410360745583e04001d2848c40303018080a0040c5902504024800003008400004503411418196051700310800822885541c070600721001403203400580302003800345007603920781900840e6034640010800b605021075000040d040c030340d080ea0533401ca010305e0450100120028071000303074024440c14400e00b98000c9500d0300d1710b003071080c0c3c1c50080070414403030001820180901983e5020b00009041800034108018400c0c000398010725503000440c2003801150788407000c5024880a644001c0d04d10100d2201c5507060b11a0f0351000780881c042207032610000314154409110351040c0c035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 600150000 1250 600148750 600148753
    0x71d15180406050d08120c12040f0b09070b0417030708030109021218030406030216050640061e0515090106030209010e1011060a051006021b0f0a0314 66
    0x124164040000b203505660101c1d010351807120300a004151580d017a100d0001113200c50380b5941c1e50750003540d0300c68864000740c040022110b4003407200784218043c60301d6035680f04040f6004141c5608040d95681e0a161013804a0503a0800007880140100380700b02c214000345004981c100f544c50303900c1c2d401e030703030000d801c00009182e02041107003041d146164000d810042c6240383c5030124000302c0329540c50380b146025100605800241d10003440c540050303010a2141c020382914070b10704000c0070301480105010301500c19440c41c1e04450301c00e011007400c050090030311f00062a404128541c2d86c40050220301e04c0e4401021010205202c80004a0150500c100c004043c48103020280b40100040280182c2200b42054030500c98040203903003113520560031841c200d8142d0042511403004885c01c4c00c05042064645c01403105120303040c0840d800181c003d144c044d02d407400141d02c40e002281e8804441d080d04070684240316100506040000000710892405030a03407040c130307490751175040700525013100c0003016 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 600151250 1250 600150000 600150037
    0x120f030309120418020304080405040c0306080d05120411150a0e030709270c090c080f0105040b0303040b0705120a120c020615060f09030d08011d071d15 67
    0x1101c140403a4400b5200b6036aa582054100040741c20440720f400305a00300c4035070000114041c80440c40c2500d00410f0010020311001000d46401005030205200c1c441c000d20424035820842c40c01602514480b0788100100500e668694a5240e10498903103821030300113020b603400d080c40451380401411200c10075260880720b650540140762170403a00d90300800549152501c40100c0f50904071208145061119590040d8505070504549440f01a802500740368072304107038100d01e2500580c6640c450540400e50514682e45c8900b17004c265101101d0040c0c1c181c104020601490f101e42018140d800d02a0080b0340381c03081020b1130740c04151701c0701c140c0c00082040280c104990141d903014004070304000f440a0400f9080404601003040d00400031230344103080114041b00d1000000c2c1c142c2e5092a00201204c050003a450340281c1000c07420300038052418410442d11810085200e41c060140c240341c0d4640f00155108a400100e25501c4c108090780501402c2041801d11485805084a402140300380c181 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 600152500 1250 600151250 600151261
    0x90906010602070f0e0106080403030f1e0b0402030103030212180306040b040615060206070318050124240503060102011d0601060e01080108070603020a090911031e1311120f0303 78
    0xb030240d40b5401a041c06510341307018005105140000350440c3e134503080000050701e5501d019400b412940c1092134244e4070704400d15003440b005604520150450303d008200b802d40380814031059200900010300540c0c410320b2502c5202d80c00d84000c107d210b2060130164010319000f13000074180107040e40c0680d0401c076140140000e211039440f03002022900c011401000a00c0d0100c003035150340c001080401410f590300340e980d84d03038007515011010003a0310400810200c030a80078180030b0354041034203070001a030140c2d80110b81d2011f0740c622188540c0a49020740039100508004031119030000303000c42d0455488069480a0504228035101c03640e0f82000a0101581090401810066031403005810007250a004000d13940020411a0984416280160752500001000e507600700c45948031280d241d140501e404000201807000d1070040b24020000c0000c20f4440d4100340404109464030311504100310108400a1900a9815003040c000ba006840015441c2032140c00d00107546003c2e40160000030030041e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 600153750 1250 600152500 600152503
    0x705071805090118020112241d13020607080d05070e0405070f1704080f0301090c0905060721020f100204170703080703111c11070504111611090906010602 68
    0x65000100303400800404044c91070f0b48800300b48480010f414040501050350075007c054112043c0d8194880380014590040410320710782c1d981c1481440c1d80b440ca40e1801c41e240c4441000e156000d003410700b104e10301d01d00a5800f0088260b000c03240482e8403203010010000c0545440c0507081c401c44440d110050300b40c1140713040c8010345000505607010001070f0301121302c040d5003014250b91010090036018846944078030301003042e84501d843d440000b0070b000c000062010116000510004803035030716038922a43d208140f01040c061554000c15852a05141d0a0b81b02000c8104070100d0a8600c11100e90141c810344003820071054610200010ba000a030500c02c0145155240000350500c4009003a21403070f540710032a0600451500404114030303840141c0303814204201010048481541404c0c1551450380c5c0500003118941e04d10145000c0c0e140d0024080c40c040c410095081200c0781454506003503903030003030b011f130901c00003c0b0351804802d401c000081c0c44450315144181d12a41c0180019410060040e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 600155000 1250 600153750 600153761
    0x5030a0f0617031b19060b040e0a14100209130222120506010509010806040f06060b030f0f090a021005070609060f15080307020d0b0601020c0d05030a11030702030c0108040807050718 80
    0x1d0404c2d0388904000035490000320380300c2e0301c06904680b002810b01c07544000074010308031241480b44d09208000250003401510039900f20041000401c44840c203086c55a108180e004150703070035030701c032030300e2803030354403042c1d40d50300202070502c03001d0f284440b0401c040b5061301e06900260090342d81c3c1032103840c603070741004020031140d400341c40300710340c0b6011a42c50062100e99480c401400200800c10f01c00c104d204002c5c054204130b02805034403080984034541101007039040d260448181040b002e2410214010000100c1d5105195402405650158008020584099112a0084070000c0c0c4e0358000c0d002144084c455110403214441011800c0700f8800300554100603150801801a0410014600103030756214450b03180c10341c400c000b00d81c99038500740182c0c2092103000015810140302c006880c104140840184420030b200e4856883c1091183c402d82d949000714100290154440040c01500707601686000354007034031505070145040f50307559810b828000f0f250320800340600d0f192444200f800047c00751 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 600156250 1250 600155000 600155047
    0xf030c10060b0406140c0d082211060c0f120a030509060c03370b010f0f021015030807030207141804020405041506080610090203040305030a0f061703 66
    0xd0115600b051402d00039440740d48108824820701d0440c0d4007540b00141d096880c3e00350740d00d090300ea0045251501500480c401c40f541c0070011034801110b4820341c04085201c9205070441c800d0146450507006000c01c0d6406284020081e00c102c40d104030b034500d000c002081c40005510401078681d0000b003130107801d55030090062101500010104003620400078183c99020624803404041c1d0781e030000c1010301d5010300a116244a00c005181010060b2090f0081c40c0030301d000781e85000141540c8a41121064401c0012a00680058001d203e201d0002e4020711b031661406944409519969600c0e011143d11414084016812000313041105400441e4050b94004041d1030314802024420101d694049000707000230700c030325503600102d014050a04081c50008080b00010441d046d00c0f2031080f50303500d40899041c0e4411142c81c401040e101114006d40303010f0fa80c1512581c0c03c41c0c40f1000070f54050180c0c035000303c0c2415a1804d0018071030114158a99101c481100916911001e40c030b444524409eaa0f42d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 600157500 1250 600156250 600156283
    0x90325061106070c170a0c15020a210e030a020d030b0603150d030225031106070b01170a21020105100e0a021303060e0f15150f0d050f030c 61
    0x4403440c0d540c00c00314165500c1109807400080c1446545004202d980d44401c2400320031700041841484250005603194181e0b00500e40c41c0c0e0b41200d580040026486480c40c4640007071212070700f01c14a007000107004d0006011111010030241c01004050f031031900305003122030060348040221800b064141c0702e12000d04e60291100380c41c518091034109030709201e406085006a102c01440014544280054800c5002c050190720042c2086903141d03000d59601d00055800032100803200129140031001c0381d40c001d606c01c8981c03800d42c0ca0b18000e07a8000101052101e40c601034086400c0c00101040120140198012020b0b807599124880c000c0c04c58800500c1440400d103050002e020000b5020300f581e0b031040c0c80e03d801580d581c8400c01410007200e940d50008101d50704101864849680104026403003042e020121204401002d07036824402c02d082d6501c0350020140000c0d10598100b0080703401414001504521000c2015036807e850084080d1030313081c240e04082410468218103100d40c0d0380c1e0300071160 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 600158750 1250 600157500 600157517
    0xe0a27030507171c021305090f18070b03040506070e0627060d020706020702031203190f1806060602061b040512010b100c020901211709032506 63
    0x150302034907078415010081c03c00035528003081003191402c0100c9001e030880c2011010b065003400c0718203000e500300d580a5000c8942886002c2018100340c01803611485802280e80d01d145c0710390b485884020a904443d046a0240c80c0d80416400d210000540c00349108100a02c02440e04020040400d05840c545602c690000c0003000d2154820105100c447c400c143c0c0c40301050000c0000045007485805d43c030222903030002c04c43c030051282a03405400c4203070080c1d0030b4403030700100c00055a409100031110030312503141420401e1500e5049602455072030305035500001d480b035440c01142c00390310402e100c219642034803607400344682e41e41881a50707013052141c8005500c1078030442110820b4040d5004160103518000b21205011200b500504031180c0c0181121915802c0340600504942c009541a806038982100001d03200700f030101c0c2c2e032001d080030040407144e8034260343d14060b840300616910700200d001403061242c00e60b41130040c00c0100d2000070801400150305105110181216171002c0203100b13514 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 600160000 1250 600158750 600158753
    0x110906010c03020303060f0a181506050901021c0201140903130b0a1d0d060509060a0b0a060503010b16061107020f0303032215061401030b0a031502070503040e0a27 72
    0x2080e240c0000080311f451040e8200200440c04d00444c40e80440807070b80c0790001008080e046680b0049c006180800f20703160103603c440099802d03109410f5082e00690210a11001701c3c01f0003003c04042c0c42e203070f100120b001c0d542201980c015890071346810000b6040011084020f1020003c1c000003414402e480d01d0900c008810050640c844c002c442d22044122100821026543d580c070640c43d0356407001c0100140e04203c042e184da2090100c5d4156889490128132601c07528052084408441040e684c0b039247d42e00b0300b1881241501302640052584241305a00b60000303900d400348030400f5022030b00c031a0725141180100800d03003032004070490182d0010418010102140e110034000c40a001d258542802103d161843d452500411003e40303861900e040410603a01e031140f5085038003400d0344c0074080c0c00501030030004140300500c0000c140e03280c8038200c19100e04140d0044c2500318050019039040c250784160703950b208503046540070305407035a612014141c0d020080c088200c118442d503510300340d20b159 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 600161250 1250 600160000 600160003
    0x9101a030610062c04050412080c03060907050a0c0f03050d06050d0f0b04051006080a020a05031f05060a090e010209011b03090e06042d050c0f0403082203110906010c0302 75
    0x1190b44081c0c0c00c0c00c3c0313203074405524084a12072024800e8040c00401540c50941807071034900f4240c074000c1c400070b0090404100010800300039280651801841c0c03a41503110710805460b158802c40c520f00070300c4206916000424a0002c050300300c50b000fa25141d540f503450301865821142680c0000d0b2054920401400100b45101e641038541c6074086d11203400e035111130030864a00000c5480018038541000804a442c020100700c3c000d84901c256403002c40701d51503001b01926100c1100d02062040940c9003000144451034002c03580100c030181c08007101d213403034582800a46880981d42000b682d0005054005564010720311807940001621401d00992903a800402d41001c41c8907603003e80d4005000320303c5a64a59010300c6401036851a60705e500c0c4d00310607000e09a80018210044104c0c41c050000b030808403004110341c41a04040784840c030b0309083d40e851640541061014962001c0901c501458a12803481210050f60103000440f445d40d100c0000c0202240c8020031072410411b00114441c0080c0c0c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 600162500 1250 600161250 600161267
    0x4060203090d03030b0d0c0518161d060408030301170a020d060f06050913110a050319150c1e02121b0a050726010902010207060809101a03061006 64
    0x4040b20202e40710300890500301e018201803050b142c1e02c40000d0b140e0804211401001a007140c2c000d46401c40b480032007009028111400315903860740380800880003c07074144900403030705420882c25000c0741c00c2c601700f40108201e0341180c1c10600d01548004014842e4101461103088105d214100030075000c4202e0b400b00c6d91110710614003d16958880ca00a9201c0707c1c25081080a40700207001c09101d45000303401522054401581034954499450071000181402060007003a01c0010340100500f03142a40004603038880b42c041944c1010004984039040900360048080c0203416a030b510111800d080400f500d5102240c0780348080d0f500c07a0807205514180c80d030079a004138010b008808401c00d07103511880d0900780320000c0107000b40214900402c0361072884c0c0106003001c00d02c0c161412060700450100d8226100307100041d0150344690b0041044611449000c0da002406009440e40d038041949e008c0e007558905080104c042c00c0f184507046042c141009025800340c036014028607680c1c0f500c0b40103041500c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 600163750 1250 600162500 600162517
    0xa0e06090d0803180a0305192a1104051807060c03020d0e0301020d05010e2a040302061605070b120c09091f0e0c0c07060f080a0c0e0d0b070e030304060203 68
    0x2000030001070b014200b0304020070300400c2400152103601170145401003480d400740100030320a1441d1040508482c1c450382c1c029030000a6900c4400c601740c1030032250034800c0080d03041155298145262818140c499014080c081c030081040c01072444186030429041600d190071020820414840e400e0209500060282803802c0e82d080c2003085000c06c5012a0192007290b95000e0040d0400000003010910044014402c0d04a500d588120141041881d10703464030703407403580e5400c19083c8400c5c070140c9820302c0100900244800f5102c1950348541e02e4078209400e640c014a05008041848500003a02c4000c0c0d035800110401218036003410400018000400135051030641303504071a01489222a600440d000340c0000c4100c6040b601d090088070300d582e44000541040d5010740000042d8035406215041500072440c3c0381e142c80c90703440c034258900815940c04410200142080b020b1459100c070b40f03c9107031560048030360b81e0540c0b0300340744081c1410401950090003503000304070400c51180c0c044142c0d000c02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 600165000 1250 600163750 600163763
    0x2012a030c0f051e010605030106051f0905090109090b0f060d11030124081009080f16020d030216060801080705060c070905090703060e0105040c030b2502030a0e06090d 74
    0x80958180500200b929410081140c41148031450640386003800f50900200303014020f01c2407039201c1090500782c0b05107118007034100001050f81d4107880e505544840d00d1411504e00110490b40d10030001c1ca00000c280d000340f154550f05c90303c290030301020702051688915016625091400e200d0041410000306c1c01c000342200c200d5404a803107581c0c082d04208007158280030781e0007038415800721a81a40085100c0d4403600c0c41251000c071b4445001340038048189810074800350500078103242080d190341c0960004426844003024442c01640c400d011040700500950080081c00100201e02030401050380284091000c084010400e160000480c041034a5003034440a03100d400442e0054a080c1e8540c011248490a14007009090000060b08030210303401114280700401002020394201c40c0103440151104c070000000b0f02c0829040c094580d007003202003040e104520b4179010b650640d400740320807400040c0c10016405c1d0614ad840745400881d0041240e0a500c0c040036200001c11100020a000303041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 600166250 1250 600165000 600165017
    0x100209060f0a18080d020f120a0c0302011509050402011808060703020d0e01050f1b03060108070f120c050301050a0f0b0318070b0f070303111c110708070f02012a03 72
    0x2403d20420060607510841401c81150b07135114518940c840c072541c000400144519981d202c101240011801c903165041d030351546c80e01e5101442100c2c2d8402803a070540c255074a90f1100010210420350a400408082d100064541480d10004101740c3c1e0250004030290304084041c0007441000c101c00d500300d5494100140d03a103030b400c03103004060580b0b0704090503103510f008100400d0800b141085813080380c00003651080c4640b9801540058041618082d00144401d0000f9540d01d010301800e00105405007020300b141c1080c851544140c41104882d003001075008001044035060509500c00030b800102c0e02c0c07128181c20071292102c28000105880404001d88514445d01a003e000000282079124500e50750340340b0112000c040360784604800c4001a10348001100c070204213074140c0d450340c0701d8a0400c0c50030900494804025000c00a44942d2012040140c240051900002015501c0c0b1801c0780c183c22440c0d03070001500701055081c80048000404900404400c2c4480c6040425545410136080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 600167500 1250 600166250 600166267
    0x60a0b1e0109092705061b04030302060403181e0303020c0a0b0909060d02030d02010b0910080c040c0e100315060503060a12030905040908090306060f0109032004110408100209060f 79
    0x5803a15144d04014050003690616428400c1c040307261442a00358041010002c50911140e10040c03207103100140045e00203074041400244a11030b840714262a81c015030444076210207040c0d10042076840840b0005400003410810075405000c01035209004640341071032149400001c0b211441406205407203840c0d000001903480e030702c0008664015801a0171503011601c240c0020b4028006240290320460603000001c04444001340c84c00306481e9503c002c3c01401c4442801d0101410009581c0000d0040828400341191a952481403109213280d0b00441e07017908800d00c200c2560040d8028000704181003041003035a4844c014030358106c507980192071800c002c060070125040c91854101d19402400c00940c2c005128440300a80508001141550309036140c0000300498a018070a155000c03075944107003000440c000e035440710a0a000c0410404802c4407950014013120b1000b0250b0240020200b030600c89400104144d04140c0d185100441c9030070100c5001031010301a4110719041c01400040c3c540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 600168750 1250 600167500 600167531
    0x2101e0e01110307092909040b01020c150405130606020a030f0302122409090d030e121303050f01020901090e04020102010f0914010c170402041d060a0b1e010909 71
    0x400c0c828002e0460b649074144a44004c00c000403500c140110040c2c080121600d080c412500072204a54440a07146811002d20502001d4a14404014150301075110b40c040b4030b481e0120798030045507454904a0740c4500f44000c000c628100010544030f01e80c60124184800c03500003c035031611036058241004000340004c400c80107442601c1403068101880d00601107045941000e404c2e000c889a01c600300040510300c14010b0004007101c0a956640c406521b0b0382c0190300a5110903102c09104c001e40c1c0f010b011070789a0702d038540c2c02910406144d0090b00010018014140f10500140c45079100130b44c54003000c200003c040c22691b00462040344045400b01e01103a00075803151100107010841403100c0d50b2942400f0102d043d15841d000c001c1d50a050300d000c0028800d40c1c98814000724040c2c1015603895580078080109404a00b00700703484040181c001101d001005054407400c070b2000040b60115204051103101d42003c0b0b2500e58440c0100d0080f800b40ea0000840800d0f03400301f41300001e25881492185 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 600170000 1250 600168750 600168761
    0x209010b0f04031b050a1d1801060305120703020f06010308030c0a09090504050a02090703020a08360d02160509040303051b0d0f140c040b0a0c0804090b0102101e0e01 73
    0x1000f1104109940c071007440130703000c940d0803070703070111030041c82d540d566102d94103143d0301138a090207940014000140302000b60b00c0300081c1c07168520000115141c032036841e5071601c6140111502e804c240440c40e1010568100031551034048003030007400055255644216a0b40000340c8a01a854030200e4600440b80c4542501d00003090010418885230410303040003600d500120f0001e038011170f08000021007141c001d00031180054469610940c940e41d800c2070f03100030a0400710347e140d03111050300c804996001031003d20002174107a04000e0201d2512002010746480b1001241c0c05130190005010021170351515500b076030040c2c0608010610b50361b070207510403401420002c55180c0d8400840c01098501e943e602851202c030545004003c08640c8450601c0000c0044034003408010302000240b0100c0280b0000e8905480303181400d01800c181a03444910580064101201c40380d03503004101210743c0d04024000c0402d01c40402080110140000741c0252080840c03152034540d101c5411864200096112 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 600171250 1250 600170000 600170003
    0xc0201020307120e121b0d05010f0c09080c0a050d020118031b081e031b10020301030b0f060409050303070c08040506130f09020c030403030e010e030105090606030115030209010b0f0403 81
    0x112031083c002d400f0060005042880e059010704450400c400100c030b0005011801554a040001407520301401001912403000070201c502c0d5407038811038402c440e668000c02c0c4400c40c040d21442c114600f8460003925111070740c5c0d0050b2150a0a15081007181c66440302c0c20003203502860004d034100407000421803202c00e01e03030008200c1e0804003105c2c0f00410101c03181c2803d80701620151100d005c48003580e40300c1c1c1d5010000103952900200800d030503107d10203024030002040c241c180c2d850b42d044000380780c1c101d810980c029071310380468004004151000d0080107138054003c5a04121441494803120b940340801440701e801d010000d42004e09022405080d5001010b0040c50a581c0e1002d425200643e00c0c03045c03003030004400414a0118103a00140291070a141c1343d00d0040d400c20745152011644507451030542410701c90805c40b40c1031303030352420b000d810703c1048144010b1000341402d805060031180e2500210030701d274000d69028030041e503e08120504603514450312a40310b00307009090005520441c0d20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 600172500 1250 600171250 600171263
    0x70201230609070503040206091e03150c0412140303040302150601020109170313020d060903020d02070303140d2a090b1c020a020c0909010509070f210501110a030b0a12050307030c0201020307 84
    0x1418a84004204c13441c9422b4105800b40c1303011030809a01038030380a40a4a0000094009000620401b450b5411012046010f00407204240d18184da24504590003910b0940040c1c225502203000101e0030300201da00610284020041280280c85180e40541141c0b800c20040c540040800d05086145001c1c002c425002840d01d9811007081c81c2840050900d0310085001d4010414144002800400d41c4800c50b90152a040803040c0442c00064090340003a1a9180c0180c0c0d451141404880c0855091a44010500800d034502d034610000781081c6a140c0c003e500101040180200710903440c004458000c02014000da2103001e4000180e080801e0f0000c2e81c1e0300a15240f0801c402e01005420442c000c080078401e4414403912404004070408040c015544140200c00b00819230f1440300d074410348071501500c00040d616052180341c484550117001c4042c0000d44429000c00f0038508030940c2d400820b22007464100c0303114640c0c0c0d202d440e805482c80c044c1c20301424081c22015a40248210340344154002c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 600173750 1250 600172500 600172519
    0x50301060e0402120c0117041a011217030106170406020d090f0605010b090d20061c0e190236010e0907031e020105070b07020123060907050304020609 66
    0x2650144140c07811038041c1e114034942610056402c10204009440784010380d10030700702005524240f1000400a07004a440b041c17400886805a5154a55180a483c2c0343c0050b0010300800d040924903415001707520452000200010003240c0d4100c030800303c001842c1d1a009529aa650401e08028020003048c407607002d08000c1a803081110400c00500c8142c420a01040b090743c07100c641c1c0a050103001c02d442d070816000c070704400109a43c2603188a0303c11b00d4203080c580d18500032022940a82112801200c0109110b016031100d21240c051510780e0b82e02c800c000c12200b8040300303400f4135070403c480c4007034043d04150a03940b00a414075150415958032102d4411060b014640e81d800c10795100b441342038210545003002c00d141ca003021604600320f94115001030809071152160590221340480c0880c140300c001c011a40c00900c012807030a02c1060b07103800014407000555036190506202558102c2025000c408001031591120001500036085103403180d140d40d521320200c1c01c1840b440038036940c0905a403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 600175000 1250 600173750 600173759
    0x1908010f060f210b040203032802010b01080606040905100909050601030227010303112b0905120d03020d0902030f1f06031106070f0209010e070305010605091c020a05030106 76
    0x281c028104484040d1103400c1c10981e900c0d100400c1c0c01003a84001e00801d00000404041500616000c0c1c0003400213065a26081102d90100100075185000707007c0c098060b102e100d04650280700d0310544c2002806c2c4900a850310000140141c82039000d2040c14982c0c03400860701003003102d20440060481c18104202c2550f40d8201941e13500c0b000d21040307107e058054903a5a400311407800c50102c07088040a080b440b6421641c060f90015404191201c080c1b10301560140ad40030141c084180d6002402000d5410356003c60004040f44400d412960088007180030401e00014002030299850403649401a140d12959180101400078120060f6062041001c2e16015030f0020840c4045000101c01d140c43e0f44828803214004e851a5210241185880e1038080c00c40c1d08180740240fa916220781e0307485010550f07660025852072420307004101c440c2e19550410000c00e400d44949800340c0000c3c2011400c14050500050386401e945060b00b109a100010a1b421915038082035409000028003d00074642c84 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 600176250 1250 600175000 600175031
    0x91a041e03110606040603050d08060102011e09060f02120f0411061b0601061e0309210503070324060c170f090102070f080a14190803090f12030105190801 68
    0x4429072031400e003e00c001065841c50603110300c200300c0703601c50050814010322903030660f42440001d0440e8155500c81c000059500d030304040c4041104641c090000360780140e420032808566286a0703850350f07a4410800d45441702e107040b08540c1e0211260400c0075040d1b83c0c030301d00307a00200310004e4002c0e0410008160003007140c0c8500d41600001d0b070342000301d0314580ea9500d800c4444a800c1102c040c418a241102e0721035a512a4000ba0f01d03050007404919808245014621a281c4403580400b0000f030011043c07140c101e40c113004152076098100c180f0b13820786061501548241090780300392414062000e007000c00b0043d0700e004401c15044540042c03034503080340245d29126641320910380d40c010f00400102080c22040a002101a03c07801e40c020122803207280c0e035201c0b040f03034102c4104403075102e240017040411019813010000b05120f02c80103a100c1c00c04905051030514040500d04040e0400380b581014984988242ca0445404407140b05808120900c020a14840340c1c006028950030041c054801100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 600177500 1250 600176250 600176267
    0x30908010c03270201050414120f0c0a1d010905070e0d1b0807030809060f0c060103030905011409150a0c02090903090907020d0f0c08190c0c09091a041e03 68
    0x60070f07403d12000c5408440a1002d0448400700901044042c0024000680c82490210142d40301604444150b01e10002d81c40c0b50640901d201a00c40e0b200800704100c03030802d00500001017401e0b0428198050340008200c41c05001405401c04140d681c40009401900c12412808450805005041c5084181c01c241046540561a1450710042d0400004171300c0740c00104c14044035042441c00c0c2c00c00300031000f040659403180c08201c6080d0010b21540721800400c1c041d8a000b1446510342107900703840c2030300161504241c240044000001806584070545135100408103980e80310300459036410140c0c1050f65400599040079401c62840030402034405000401801e001e8412100f0041541d01c0410072a40c4c0c00b5a890300780d0000e04207911129019000d2481c4036005845281403505000c00400c00561403400c240c030003000a07040b01c1c240c100f44045c8907078150151011600600c1000010f131104400d60203541500c0340c400031014002001d00c0030b018024040896100c03d03524640c81203040041c039206 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 600178750 1250 600177500 600177521
    0x60303020f030f03010905060109030507151808061b130e01090b0d02010c15061701050a0c09050d03200106120b060a05010e04020a170c070c0b030c07020607030908010c03 75
    0xc03812188080450000065030380f20350035400400d155a00b8071207820050000942060b0600556040c08800600140300c1c0708050300307140c02c001c031004ca510203000308203c034010600c0d44500c00d0000107102c0300c01c010590540c0110304400c50310040c0aa002e011001380721348008894505e00d1800e0128031002e00001160494550100902c0900140c03170400c9a01d02174818001d002c00c0303510b00d10400107425200ca100b800040d0140009226a030351000c0410b140c2006080c40042e5510300400c03803070ba0319a2140c011380000710314108002c03d050201241c20b500c04a10060305000681e941c0c0c040b10314103494000320340d040220080c04541e0b0303229111070b50801710b20012211401c1c040d00142186c00d002e400e00d030880300140d5441da00c0c003404000b4403000b0351042c415502040442d250502d20501c40d4003030107014600c1c5d0280e156880c0044e040a0f165090310350440b10490a0030070a100c042c0d0901c2d4140c800c1035404a8409030785014a00c0c040e02d01503151380c000c4040d0b508200c8061300b503c3e0541e21007140c50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 600179856 1106 600178750 600178753
    0x9030303270307140f060108070501031805010612033c1e110709020c03040501030e10090312060e09120318030d0203010602070b040305100906090602030a06030302 72
    0x1544007a601303444140c450342180f841c0c00802c200034290320440b4006411154101000607807030700e2103071041034105605d504280d01008001d40000705445e40c000000c12031180c0d43d60303003003150300c034004420b80c003240b001024480160b00c14081c5030345003040f134098008440e484959401000402101402c104007810b03210288015090700d118406208a854640c880e020113561f6526100361500311031040307801030102c1b1050314800010b40d0140c86013400c010a202d000d44501d1894840703048016003902d0700b085460010306800c001c1c6003010f030f06040c0e414090a074540e44803040030700b410354000078594003182145080c040b4003000303150031059510156114000c0260030714a503800c074500e88070100d9070001c01004010b0b01000b001e8020107200d41464241780c41c5480e46500d41e020034003440e4006860310101c6080103c00c0d4842c1180545c0030030115240d0401050141c0240124001100035 = true := by decide +kernel

theorem cover : BRFrame.Cov 600000000 600179856 := by
  have h0 := BRFrame.cov_init 600000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 600000000 ≤ n) (h2 : n < 600179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
