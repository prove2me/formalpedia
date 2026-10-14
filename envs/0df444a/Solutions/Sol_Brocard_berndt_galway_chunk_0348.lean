-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0348
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:21:16.24776+00:00
-- url     : https://prove2.me/submissions/ba111f00-d806-4a07-85e5-3934d5e4e6b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 62410074 ≤ n < 62589931 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 62411324 1250 62410074 62410081
    0x130f06030b03120304020402130b0307050307031116060203090708070806090c120a02100302090402071a0c0711130b090703050604050c0403020d140c0301090503030901050c0909041b05060d020702031203 89
    0x28501181e03400765060b47e01584902d0200c5c40e0141004454000c00d007006400b0041050b65a800005940300c0c5005540c00c0c445141d0001c01c450044c4141b2085400706017070b8601040104005d60000e6402a1045080310003d603034466149080140c550055400c40d0070450910000c15020030585055000482d03400e040807680303107081c554451f01504028002d9581c80030005402c1e01076815030305511005041503640d41c02928220300414101c046e442c0300c0036989004034001c0f4811700c0640d0300036039201d480040c14884444c01c124080d0301c050740d8250360070b450340c228190540703c180d420b43c000c02d460745020070681400313410032080d64002410001032000078030040005d84d459030000541c05800600031840242e4150015003440f008100040c0c040d82006410000c0200001c01036105440490080155032180360310b07480300d842403030310155001d4031120100b00030882c064000724540c0034010008019650700e0000c40c1060308041d0138544032913408100e010550034240440e04c22080350300c4045240d0f25 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 62412574 1250 62411324 62411353
    0x506150d030f0201090b15130515040b030a02100f0f0f050403020907030e011107110a060f050d150906030302010f0606090b07080409020c030304052103010303080903130f06030b03 79
    0x103500c0c00c40501001800404945014001c0d0300100503d81c1000d07103101c42e1b140c1903415042003445481e144d8000c0350805a070310415a00c51249030700a001c001c8448002140c080c0402c0007818034202c1d441e9041c0070380b40250340141d03150f61641610500301d8869401d1000407850283c84001403e021409001038448071201c1c45a108007110140c80d41110000090b45607020101c1c01131282e00010441c0b5803074040d840781e8030740300b100c090700788603100c1c0c2e1701009500840414000702039000d00c290710108820000c01c1d07158600401c0900100300a0000020703680e507815100881e41c0505030b021007117542c2c1d586014401d165081c003842000c025900c9040c0709051a082c001070030030740c1600c9811141080842c207241002000750484005045900044d5141d113050203d0644030b60052381e04480030700c2006501800000511007189404060084460460b0310310384050b5104480241a50502e0004010001900b00001e11038405880410f800c6d0084504000d805400c54003c04640c601c00e0344480d0b1541c4041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 62413824 1250 62412574 62412589
    0xd02071203050d05071209110307060e0603060405090f0a0f0b0906240406080a05010605120706020613080c160602010608010605032d0a03030b0a0b0702060304060e070b040603020403050615 83
    0xf42515140040c0940e24801c040303440c4440b45500b92981c0d814420704406101407251040c03003008044007039440703895980b1000d44020260074185500214184001f4085281a0f417146610807404019240c404048550990a21800d00c0c822074102c1140d40640092140c03c04499a000704284010300c49404d020034181406602c034080901c420044440b5400c40340c8850308001c006060410840d40f1324581850038034040d00050040382e0003190007060120f20024000742040499602e50090261900d518050603020304c01c81170152000c44080041045504003000701490140ca2441200400743c03c0c01d0009003500c0c0c1c0399001107100c0e81003801c180031640d03000c81c2c3d56816640c4440c954442102229000c881402030200402c89402514000300c141601500081c41a500031183c5c6142c16840d0a940704240c0980040690002d50500000300010902d503c0075403001d4900c406c41e50300941d00c03403130503145610681000001a8010408000300101041039540104c1c020205019140c500702c007040070b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 62415074 1250 62413824 62413837
    0x3010303081e040b091006030302060108010b0303210402040209130f0c031b050c0109050124050d0c0b03060a080706120506040b010c020d03030e07150f0e06040b090112020c0d0207120305 82
    0x40209810104810305c908105040c1c2e00b006200c010b00955559060181d03e0308403d00c2200025400d0850143c5c4a25002c011a080040385c08103041070300c50a00f448061404008100700e0f0400d40c2000414a0395070b4010450071700100c688808038110f5050051401511880700600e0203040c180403006c41c4070440240383c60300b40c0d045454015114a581580c01d800340002000150065103400400d0031820a400501964110510390b6031803207503660424010850f501c48000f600700c0f119003105000084002d8010760308940c000f0103040c1d40f20344403200f090078965180d0112010a541046400d40615580221035011404a0b82001038491840002c1c1602a260a0082c070035007030780030000c00f094002d9008030807882401086413130403030300d501c1200302d05030a040450380450b41e418192201d161290b400c9040c6034a01a0103541043e00e0030211542c05c0d08204011410300c60300c07190340c4000e400107101402d803c00010000749840500020040d0a04950b41c1145241c1c6034030b0a444008241c00c0b40807104c9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 62416324 1250 62415074 62415083
    0x3030d020a030f0203010305070302030607090614030705070c06030614030123190501060917030c070b0f0f070b0a0c09060e060306011407060c300b0d021503010303081e04 75
    0x2600d4001c180110024425541d012501d0343c800710020007407020004641043e644240c0807603d40f0340302c4050a803041c0309036102d541c0008240c002c0f071900b00382d5600c01941c0c10800f9424031b1411304182d45d0755003400341c032241c01c00800240e407002c040080d01c41240202c43c106034180d000b0021442115604800c1c0203c1700c135030030310510341070f0f020416040401c01519103081e070782c0c80100042d5848500003070010820b072040079000d81000148001005010003103030003601030300004040c2285003480c000b0307aa4002d11600d09441209010700301c5021540d4000305111481a0008466841c01f5404403003114800e061401c10000d0300c19080c080d16802000c600f0804004803900d03a240d80d902e00049414541d91820410109400305041d400c0048a80010141c022252a4080d0303040c2c80072a0b0003c3c4a4912003050702c1c1403002d8150238400c07441940503518440003c2e16440c040030540e0003141b0301d0004884003080e54400000100185940043c05035044414088451030813981600e003010b0690f0040d00141 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 62417574 1250 62416324 62416327
    0x702011403040c030c030302010509120406210e030a081803040b120a02090406060210050604051314010b04021c0e01140105100306030b09030403051605180a020903150402010f090503030d02 83
    0x2010300000f0b698a000840e44040a13040d80b0340c903858024040e11046c0c4a40c101c91090004044040550f441950240d946980c1d03142c1d01d00a84940c020480e410300340543c0d61480e602d4032081703201d00084c401090214002e0321b81501908050030714001d40c40580060441d65001448248040c00010b001c0742c900e4840c50811000e25143d04810030300a204601030680d015142405c0050610b401090203a22034409640402c0655940300c05e000907520115041c2c3c0100e0380c13000301080001d030051407100c0031440040000580355038040c0401c0032640429000d503240c042c03004003007842501e2405070800c5110310400a2040c40c5070f0214a054960060140e284610000c04510710342c144254480707002103400911028031070408820707064070b03a44103003c203541c14001c2c0984009580f5412540e50f04440d0040c210292000c580c4031000b800c40c20252007241c81c03035000c1103240420383c3c042000d800e1101c0c5540c518042400c107440090b04113400840c0407c14010244020021070340c01000340c5505601410026 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 62418824 1250 62417574 62417581
    0x50f0c070902121806010819050c1c02100207060206010b1612090807120809060912060405010606110609070308090f0d080706060b0f1905040b0c010b04110702011403 73
    0x541003a1640d00540d085501c0442c5160580115002c0540500030007020054001d090540311a01c1e00401d0050815660044101d1800701800c1c001030b2900d140150f0564030000001c40002ea03c40c103e9100d8160645241030a21040d031818046150161210380010701c080303850424003035210310052007660003c0c040800c0b1100b0740c11800c420003400c10b921062010500303030500009040e00032203000d00c644600c90103c01160382007000c9403001190f41c2100e030881c10121440c042007e990301001c07a8135040014080090700110040100a00a80c484c0d03001180407400d0200c010300200c0d800703c240e5641d034000740602204505c0400c4040a4131342043ca07803591408201d000c14111803940c44196044400f4498070401c2c01203403000350a80d14840e00081c004180d035a000c0140324000c1880c44100000100600f02071890314000d45603446040381002802c2a075141e14071941904028802c0c1c109946035041000e9501c0c0c0b030b200300c100c0180c04550180c2080d0503030300005d18044042c0d072030104030036000012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 62420074 1250 62418824 62418847
    0xa030c2d0903060c0306090b030f0c0f0d080403120215012103020319020a1118010e060a09020f09010201110f040b090f0402070f030e01170403030506040e0304080d17010303050f 78
    0xc14040e41d0400c00074403041301c020034024001d08540c403400081c64600001c00c0c90900c1c01160440645a070391000b4a51211200204040c034491070b1000355020341d880707100600045040015200440c002c00320442c090076900e034041c2c01d1000c6800740390340400c102c40050214006480c00d450110007150040c0241c4401440c1c03c2e0f265108150110402609003142c691000f540001c1081d0a41c1c03260b118540e4152004040c40000c40142002020071840000144010240340f20250381c450708c01071198010560382ca85a004a900880d00d080c07182c0310018956003c0e58090003000010100c15250b42d01c1d100b0250030301c3c050350040d8000d644c14050006034184140d42d0704064480b0a02000700704564443d0146040c00d1410551032044020500461410f00158040e001450b101108510030302000e81d12542c04a0082c83c000304695032145d42c40301c442c01082e0040020308040c144c41c50041c600160850000ba1220700010744c2007821040c240d0061001950110a41d0810080003d1094a442d001b901 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 62421324 1250 62420074 62420087
    0x30207020109031b1d0606040b071502040303050705060f0606251b031709010e040c031401030b1b18010c02030f0129010c020d1104020409110a030c2d 66
    0x301030080b82d0401c110400b40032288003c3c1017164074100d10b11140c501003e4114546860403120b4542c4180280420030240c2035034401014214401d4540e0010340100e858450708a800c5a00194001000850a4030401c0f00410001c5d400c40c00e1101182011300c0c1182c00241a807064094900002850b03480c0700b1101c010031150b07071a4040e0301181e1000e0044945115100e20040e5204c01e89103070703810204402c3c26401c001c084401801041c1d540f400b40942400c1840064480c101d0b0780ba00701551180c6200c610207584007884d01031880340e20031070014108202d5014172500c0038441c6104102c1c0401100e048410070b8011010100b00c00c0c03c0c41d295020070341c00000d00b030000280d11481c80d54201a50380d074020540b403c400149105030849040541c2c03945004403554805242e000307400044449642000c1006688002d032107110092001d86465100d45c0b422046d02c410800c09905c00c100450200c005503003601925502401038034140311030401c0c140103503842e003400c001510751420705540c0304000c1500c1000e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 62422574 1250 62421324 62421329
    0xc120e0402070c1203180312140c010213050406080111030a0c090819030f0806090a0b1f050301050301050705090a14032404030806010306140402030604090b040b1012080307030207020109 82
    0x700300c416055a030303501220380800414041700003c480d1112a154400d109001c10280c0741c02c900012800444d0240a1701c1c0240340030b01c032206451040c401028441d0003400141a03c40e0001e007101d44143c03030a070611050700e25a405c00491a41840064652540d0b8203080e0390b407251001001192250a420302965511030f25040007040380a0010320300c54102c1081160382d1514800d6550074040a80c1c0501210391140a0350700301d074810380032408118042419080034122050060640082c51002c00c12a0110540604144089800880100300600d02071003103540c0107009082052800083e81c001404140781070082c86000024a1000c42003a00c04000c040c10801081d2000180340c1d0300070102c404507031f01c00c6604500264001c2c0009445522a0041504070b8110703000c0f03001c02c03510700010800030b508002c00300c9412503514500800482c8903403807458051409000706c203002c1c0c24520170f01285503525810650700b11541461000014250004599105080c3d180060321084240b004030f906a5480d07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 62423824 1250 62422574 62422583
    0x120305160b0106080f0c030c160303111b010e0304030f150b130204150e03030d0c0c0f03030507080a11070b07050d050106120c020105060a0e0414030a1805010c120e040207 75
    0x190003c60559003000c00326000356440312000140341c2e901d400000365444121565034050100f4040c80c111840800c116002c540d219043c049440c0180c10150350058004ea401507118503103001090000440c00c0c8038030f055100c0950051450716095484480f0307400e0b9101d4006000d00140481d11442c02c03555480700380707100c000402e400c052031312941c4468040c0d0480d000f600303489001c000003000c0a0f4020319900041324000380c051401c114041e8103c2c4001e010250004007480541c0325083d00140d403144010300c00b1842900d000402d801d1580c001011204020094100d0601e003070a92201d0075490350a40302d40b643d0002182e100c0e982c0d0303060b04a4080c02444070640c500b40c10040007084040c0c024030004590720120034100000d4180d40c02c00c07400c0e03130000d454150300420103400a10660030070182c9550320a002d14030700714a0110044c070305440c41d0300c229031240028044101d080c4c0c0a10311000440002e041c00d2806660350103454440c3c400e4041e6080e0690144200780101007010744854051700c8075507030031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 62425074 1250 62423824 62423843
    0x809070902040b040f0608280902090a020d0c0813080a0309020607030c060f1401150c0203060117150405030316140a0c11060a0f05030402031603050a0b010f12030516 73
    0x321044800c554016000e40805844807107000f0400d00d01c92406544900d800500b10744403039142070300720404a040c2c9119404449d440d942a480503880d080312840c090b07880d40d140186c4d41c08111035024101c1d40c0004144040041c12820b04c0140d2040b400b003a142c054200c40740655078441e04905800410340050300a42101c0c002c00d0241c241904820002c0c070300760142d081408405c8903103441c0b034102c0300320004000307140003008010b001381030303039071400c0f410004041c03c1c0b070f594060b125000280703010070903880a1503005002c0400c904e5088107100c01e1103020a1000c40c0c000030309041ea00d26449010040500003030f6901c15070780c030017000d108040c500034081d03407862210b98070444101e0042030b02120100030b4498140c99200c4441c641041000c0b00c40200c605d035901d2110311048102220301d5400540b00741d90501c69a0a40d00c001085140c1440045100d0001051190080c1c60103110f03840059101c0020140908810806288400001e607650faa262400720f40d2000c1c50038600c14410000c01c8090b054660 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 62426324 1250 62425074 62425079
    0xa180203100806132a030c170105060112090c18020409050c0c0703021c1509030806241303140a14010911010e03010e0d0203180909070501080907090204 67
    0x1a500450190075001840100e09840d1440b00d65655001d441c8406400e1610041c54045014541d20b81c0d9008400c500f56052014200c1406000050641041c2c80b080c0311004100401811014000d800220000084c8003514100c40041d180e008503c81c400300c50358640d01d0101c20003504124001c09000c4903071100891000c042c4a54000350014000c005500e460302001c51018480a8140c5a01691040090909034119400c0c400c0012440f50341d0074034030103d8191080060030f0352102000100e144070780020194040e050003000c98801414090140014840c0b40c040c5900074400030343d44d070f0014806c880d903940c00800301c5803a14010380c1c001f070000da00d240414120898089285250035004080703a02d00c10002105030f40c01c03501022002010000c0f1104001e07084e50003045002c2e800400200005107201c13102c1d0101e41002c032a00c02d0b440050708006486101100061001c0344400000ea40006c5035107030040708266200018054103040c8401200024082d040c1048020040d161070b420a42d120b90f07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 62427574 1250 62426324 62426369
    0x20a0204050a0c170105030d0f02030403120507030905040e0d1b02030a061401060503090616030204030b070c060e0d1b0503070507080609101a010309020303040503031201050301060f03050a0308060a 87
    0x400b4000c1840004c5400c01000b040c02c800801581c140d480c0100949824071580405407812100c0c842c01600b0341c08144000000714000494001040b8403d0b01d503541c0e5114030303140c02003e01c1040e4000904c124680388030200c00c0c0718000313940c00994511342405800c3c03d5408002c00302e0800c40380d10083d030501c145180b410407c45140c00a20400b90100c510002c0b030f90b2600016a070b640811916810320368050000a9405880c42001040410007410014501a101c2d15007084d042c80448034038000c250800010010800140f180da00112a11009040c00300c207480b1000340b180540b042e00a068102c684080001d20006000f1941100d07804400c44112079a0b071702000e43c0305c6034120b80c415054010040f4140040d4414040c3c094501d00d005d0140c0300c203103850720054004200c0303c6000c8e031300341c0700500012455403030400c000e00781c40041d1000440c09601d0042018250b03041742d0003410307180e60004000c00010340001003e5080c1c85d4036007031030220b60790f51002291911030181c0c0114818102c1170300303084040303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 62428824 1250 62427574 62427581
    0x90a020d022101061707080408070c08060f0606180105070602090303040e011d0402010e09040302070e010b0c120c070b0f0d02030c0702040e01110405060a0e030102041706070305130605040201020a0204050a 90
    0x2402c202103445856a40c84d00103a038070000c0840c00001c48144070307001403281ca1041d40b0207940139100e0f02526081c00c246403110b106150072038100c0d4290b81e004000780f040001c1d84803d52680030008881441c540980e00000d45541410f4441d11414420003242007800c00c20260141c400740300780901107036201c955170040c503041c10400384074080c00d2040c04507907050242c44440740703a4400d94043e122030602222000900c950340d8030042040e0b08600500c8008a854000e10070b00d2802040030340d40d400e403120400e420321424407013010074208000c07008101d80800c03004082070b0321007215109500d0648409050001007184d100300c0a410300708600c000100514000200043c0180500903a03042003290549205203080300ea10003240200c8000901c410000c41c9010b0000304900c11883c5400741e040c00105010900703a03009600701013948400031940e00c3c0c0c550800c2000c0d690040d50b6180510050a01c0c010074440d08008a5024050588900025003503900810803015860b0b4040c2041240d407403d64640782c0103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 62430074 1250 62428824 62428867
    0x8160f120b030d050909010e0903070b0c090307060e0a0803030f0f060111010f1e09030e06030601020c0418030f0503070f0c020a0e04030c020306150603131b0815060a14090a020d02 79
    0x3906c0c0080003041506007082c01504c5074090500441c5461140d49a04140740001811002803072010011342c0c00d40d440600480000749426121003028000301401c005c0fa507400c5030403c566a500038000c01c41441345410003250402883c2c0580e00a40c0c031401b004940c11071540703565040c55803c20581001c0284a45d0000d5041c3e444201c00c4901c40d07400e02002800d03a1174904014001a01040c40b80b809031420b10011908100140115941c100f806001f14096070460401d522419020301070031001d064010700c01217a03a40c120700c0d08520350f20302400c0c09010404d0884c1010100080c10021600315103c0313126072009848a801c1c0c10072180707031600d0300403c1c00c10080c0d000c0307019009120104100c26040b0307160780d030190b500030462402e580c2e9484200301c0d2400c0158083e2208405490a44211000350080300090481034000d40300c068640d0303804503100381000d0301c0c040c060740c0a00001c00107500c0c0c030885081400070031104642c2c1900c42d19a00b9001e8007404010003030907880002e003107180c4101c0c2c1c2046840e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 62431324 1250 62430074 62430079
    0x30301150311191b050312100f14010306030b0c07030e01081e1308070b0907120b0a0203040302100c0c02031b09010b03041e0c0608160f120b030d0509 66
    0x144000011801c40030341e00c80300c03540011503905002d0f0300d00400c010649400c0440c0b07603140880c4c44884d080e010744152020200c0035240c5410015560a9414007400d2a030342c8103c01030a55003603249065401c00c0c2880062250002d415000c41102ca01c0c0e0f842900410000c68001e040a9507a0070b0849002400381c0c05040100c010880c0c00d00c0f00030065010b5850300348503400344803e803070b400c020075240c00080c0c4000034948031405501020b4040010020400340c150b00c0c0c011035824055182080c1d4091600d500d68000003120041122000e0000d00d9207409560f00500d1136074096104d0300c83c0e140c107902d0041c1300c0700b01c0440d141c1041030b031390199170b400501d160a03907008030215070100446c651181300e40041d100d5100d030800005401888103c607200020740d0070500c60150324440c1c550010204500c200124000c854000300c170701080082991260711303140c1200d208040e110b0100005107000e010b03c0403480880f414443c0719042189111040da0041840d11006400e0b60705a44440c8001842544035640451 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 62432574 1250 62431324 62431349
    0x6070c0501080709080c10020a0c0603060e090a0f110d06050408090a0b030903030408090d050102030403030506040609020306030d11011413050d020a030e150d0e0a1221110c0708030301 81
    0x100d203580f082d02e00b5405c441c1c8090242000b102c1110501000342c4405501e04103621030440402e00040c600741c0f07071070010520b0f540c00040442c1080d06010034410003070000e41175a8080c0b805400810780655840848507802107448868542010120b81142d44049015004626040c100f0050120000080a01080803031300c0c0e40d202902c4e41c08078050781c00203452a9101d0b90080c4001400210804010007041c64001d0090200201507503071355099910840301180080e45a2090007428180741c00344201802c42403070150304520b400c0005c41d81e11444a152141045480184c1c2080c0b820b0030340c007254071000001c0451005190400b0a038100000f80c40f411541d622a824042c4000c52002c82e0300400300f070380b544e00d10f2002a90343c0100b20405c9540c100d0700722520000c0111002004840c481c00403a008000050841d01d5464102450240441003c2809001126001c1100c83e00c0505640d42030142181c0c00048045c1c072a4002c0640703014140100312a03115050003c03c82807070000186040700c80005441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 62433824 1250 62432574 62432581
    0x503060a0915020720011110020903011803021f06050310090c050102070e01090e0c0603070f020c0402090105040b0c07030f03090801061d0a0b1f0509151206091506070c050108 77
    0x140120701c54502c020b04002ca01c1a14a010707085107815001d117503401450605804410814000d0804802030b1641101950024944003e07050a0041e0309503050901075240c50000d00b1b84004c1d486801e01c2600700004100200c1d540600300b020350105014000141c1200c076031500d0060220000c040303810054074051401c040024040d0320004020782920040040300c8081c1e407030000d002014103c01088400f143c06107068070b0a450705d030362020314031071260350b982c803501246103a4000e810300010700310440c051070041105d01c3d256608501103904071342e14055241d9507000c2c40500c1504040300d50f04028030b00c1710310210354418140d1014090054421500080041598500585074000c41e00c94428401c04191300c0050f21000041e8091071510760007514204541d031a141c011550548181071038000701c0d001050703440003810001040c0e072000c02d111411a141610008030101c0101c1e00509141c0700d0000540029021395002850452850018210944807005803a040d80c6141031030155900080e52400007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 62435074 1250 62433824 62433863
    0xb030903091c020f10110604030f08100e060607080d02040b0909010f030203060a0b04150905010602010f050408190203160c060e030a0b0a0c02070b040906050f010f02030409050604060503060a09 85
    0x1002d0035a0f401030a403054040f90900380303d03200484014081c2844044001c071056442c0070b000d50351049110743d560500c41c0b03490f8100604450b201170044030000c205074000344120310303580f00900d42000741128800c2e1181750074a0084220301c14940c900d10080d001203000102e480460001d4611240304842d982038581c0c944038040300c86811840080d40c107502c21804600c8148a075840030607090741c042c00109084801103890158958941d01a004081d40c0d0401040050360a2183c24286a80800284035508003900c1d01c4d2800d00031800c044521802030303000b1118072070003001140c400030039000211074502164288084000348621800010541744140c080b107d1802090b8006d219500c00348019032901c3c0c425074400107100c015904010b40c420314401207a29002c0c500640300408942c480403640c0e41c1040d0500000a41c60701d6543d041c002034400440000740c000c0282c0303041e91052000011146c0d52080000d0280c620f0303900c0035805001c1e0f2010700020780c1458011044641c050162450840c8801c03a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 62436324 1250 62435074 62435119
    0xb01020a050a1502040e1608090d0801030b0c04180b0f040b130b060912100c0806100302030702030f072a050a0302060711030303091c080c0f0703090b03090309 70
    0xa001d0b8210020410004068000d85443c0c03480c0c012005041c030f519072a00d0003401c0000d075042403040d445a020049819440040e90ba070249511025185200244601030032a0314180001440c003030303c20000a400090003415107005109540c0d0703001c055080c4001a40007024480c280900643d188041c050345420700740502140c4041c050021601b805010a403800107040b40480c55500103030800c4928025603560f234111705500058000351038502c0c8488015012140d2070501d11090040810800c81155035000e0400003038409400c01503070700d54072207600f02c0c02c46c885d000c0c8888000c60081000303030502415001089242c103190380300b0030540008030013003031510500344903595128260400034001030410501501c94148900d58880c004000030300064210740040341c070001c0780d80c4641100c644250080b0300c207034074001c25070034078402da802c090b1405481da206d105070710200b54400040f00010980305000080040c451444001c3d00c1e07040802c01305072a0307881030000da4811381e41440500e071700b07254400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 62437574 1250 62436324 62436343
    0x1050a0c05041404060f06030e0f0a120f0c0206041d06040e0c042301120b0c0703080403080402120f1b031501050409260d05070203030907270608010905010b0102 71
    0x221402d050a107840141641c84201901440c0c10036110310b40080c0c0c240c1d240750144050842902c02054040c1d003107041601c0d15141041a0300c2c9075100b01b00071004a0108003030710784000c0d85450280c600480640090310009400d60000b0b4211100207000141c04007000d40c0308480401e1a01003800c0d039104c0404010a0f240c0c0002ca030a815000101303103036150300d0264050303001a4000c05407070940d03c01e40d1003c03d07200d440907401255890002203010382001070450030310760f100c5480082c0d00d08014503038600404e407640092005051000800201e0300b90360364007100e2000782040c04121804a4992f880840d100c8039001ca44600d05580159104138a10b000b24034075508048076002040940c0c640760030440600711400007510f2002d0145400744210f4500c458106100f410801202d0b43c40036a2205082140c90003044042150001e1080c0903d41c1d1003c075224040700c2409030040d0b10010019004110458942140c51609191080000c1c00610640024480e580604000c01c8a02d00742d500698582410740c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 62438824 1250 62437574 62437577
    0x105040209010522020403050705010207060906140d0e0319030c02030c060a0b0d0206210c090904030e010e040c0206090f03030c040905040602070b0702032205100804050309030115060201050a0c 85
    0xc030050009040c246081c0c00140e039480d00f4250182c4c10004902c04070b03409604181c41c0303a0880c400074010b03940c04111084c0100018034254405a25200000b05044580070081d9016200060110034148985c2c0105909890000c01d40380c1e52201c041c401c205482e400c01e405800700f414144486140c90002c0240d45c101185c082c00b418603513035a900000c0013024044410380d482106608608056110035015100c00305c640801c40301c40309016030b04030090700310007800112101e10801140100da20340c0c1c080150480d030b050801e41000d4a07128010b80c4c0301c443c00fa048a0f01f00e4501034108891035800100e06004030078000c2528100048090940d0f141d1108503205600f1390b008220400c04c51103660310581d4881c5c0502c40045c14850365039100000c1c10000d84134080180c1c408118401c4400b0201401c202c40640f903285402c0d19807400f00441d0048010041240c284078841c80042d051040c00e01c00c99144404c000e0080044504500c0320903846d141600400c80190f10706400240c000020344547c1c241004c05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 62440074 1250 62438824 62438839
    0xd1a04060503010c02030919080607080103050c04021303030503090a08130501080916031407030503070605150a050a0501050714030f041802030603150601021e01020c10050c030c16080a05071401050402 88
    0x440040c02111204e440c509468140e2315080003855220031b1005c02c1c050b2017242e982842d03551440c10914070f0485240c211038030403841001600e10f10300c5840450000c89a15052098881e07541480082c10043c008c080640858000510300710080c2201e4112070680e1001d03216546180c6402c0d11065a400c50f0100307099078504182001d00103c0d0132403280140721602c810440d8440754980e0303100303400c4d9081413200711281902d42e01404003024040c3c40c00700f803a610a50300344294611700300c0000c004180701c0c801e50f41804030018500741800540e9040c140c522403481d045039610000d204000d2050341c814480c0e03202c00c3e5480c1e103180c40c0c1c15140340216801424020018014100000c847c3c410341103026008505510503202c8401c00344000c1410400c01c551318800050b10b860890141d2800c00c04007107010b41b0824900410400381c46064011b994102c8047c09010b9116000ca20842e0041c200d01c0c400504480008144030200940c420018130a42e071250070748030307414403064104178240e8100380d50095010b0700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 62441324 1250 62440074 62440087
    0x110a0803270a03150204030c05010203160b101e0501020d1806080a0b04050f0f090304030515040309080a0c0501090b120a0c120c080405010e0c22020d1a04060503010c0203 75
    0x640a985240c5000002e00707100c0c640fa03499481103002244025071a001d07940210b010414040800440801000c0a002030f41ca409156901c07041c114a00c203000400105120010841d40f402815802028204059040d0100300c280c11011340e02d444980304090041c80340c0546003941134815825009071007200404401c1d02820000140c50409000b40040c1040380d840d20010385966803405084e0249618491803c00c3d0b00300005101004a001405051140d01c2080f0400005c0c0000440d5207000b031060304c03c0c0a0300d0b2160300d41210014059401488188500300c2050700307004010703c2903412518240c98003121207664134403104035130088a43c0055800341d50000903100030507541041052a40034540080103402204c41d40701112122001400001c821404000c20064244603002030b040400c1c0c01004800c0c403410002e0003540042c6983d1500c00ca0542070032602c2c4e11160180c0b61b0041012405200c3c0040038480804528801c140d0288146d0a180f4006102d09041c864003c0b403140541c081d614084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 62442574 1250 62441324 62441377
    0x10e1503070e04061e021201060e030304030b13140d02070f0b0d0903031506020c01030e0109051c03140a0b04180203060c0f070206121602010e070501030e03090d110a0803 75
    0xb940184103903016502c90801542a01c0c5003420031504c01015040142c8543c1900c1049180c2e0905800c8601030128690070719000d030340d000066030b0840784d000c0c00610716a43d07180034024400440c100002d00c040800d01c01c01c0700549001c80c104e81502d1441e401c6075101961f81540c1d044210080c410380007003010400030400110b000d6000004481d001c1c0c00d0100700700c6041403050070525000c0c3e0001c1c005030050707510742450750b905006d141c2c40700c47c2c040028840d05a55458198650724986050f051300c4009001d0108924003070b410840506640b81c00003a00c9191402c44440908001a110342c880d9240c09a07501c0180746207014098240c0d0041c000f45195aa900d81a0209500880c1482d414070810702100e001079440c070004200c00b0201140b200d0190030840303003000e80b140b00b140c240b2040d6410104450040c440c009030001c2110024a03000c0303003041a520841e41103120313040145402204480450b414000c02c0b0f9181a129041a215041c05983d0381d0315264a03801144021203045804000204800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 62443824 1250 62442574 62442599
    0x909210f07020d060b0103180503040905061909090b060d1208060409060204030807140d0804030e120d0c02010810050a12050102130611010501060815091008070806010e150307 77
    0x26600c54039118500030980c0c000810503009500121101e0703446280300340d05964940a0310616200c4203150300c5c0ca0b0b003031603655035840380101d0090101c1240c1d6440010915600c0d5210364043c1500c0c0c0b00c0d641d01854841b03100a01521040c00c0603100200c04802040450600601081d48150040d00707144850309103601c106d5010401800c070070350103900e0303501c0c50000c030398907100402c005c500c41c892043e691740304ca10301f00910088601000c2c07955001814850082d1f038010212640c032946c1460600d00c0e00350010009001d51040d0301c0e2899443c070641140441194001c000d40d581c2078000d0301c89040f03a6440b2030204a108056010750398220051913002c000c030588140072211528410700001d41002440c09101c0800420b690224000a00c40d034503207038020f6030a05c102c40c00340549140071740c034600c1d050145510b480c00042c0280c3c004c0701014000b40c15034003036040300b038060444502135410f050b607560040f80c2d03140030a0140348c0e80d903580000800c02e80d0500482c810a1002c1c040e014200d414034044095090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 62445074 1250 62443824 62443837
    0x807060c0f020d0c09020c03090307080c0a030609030309060504080702040f052a120f0109060608040f030503090a0b0a0207030306090501080d05030c09090a020a080601090e13060b03010c030b090921 87
    0x1421311034040403402149138006407010307041d00002940c55403c01c6041510b0207100e58020f04464010080d0a000f0742c07070381541c00080c2c076003140c0c021900300c1070351a044000305900f0704003a10051420040c4810018150000c0001c20b008890a101513410341c00a042103a00580700514403014061050002c20620003122040407425401e183c1812100303644421000003c856010340456144010300200c0700034440e00c00076010034036000303900345460355440c02c40441c0004007a0922030003200140b0300442c1048603a00b030a50100c20340640e4100210744102942103410206c3c0842e05140c0b010034281e40d01d1152604840e0741c1001002c15442d000829541035201074503110700c1d584108502c800503110910030230b000d590004801030303075210700c910300a000347c201510030f80c1008900c9104100c0300b24034040c4147c11600b00900c2c01310141e01c0b0710700b0100902040300010b415508040344003d01c150140d00c41d1a00c010141c907214250707942c04110f151034007625006406112201c4074140c0c50200b41d503010f00308 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 62446324 1250 62445074 62445083
    0xb0f040509031e070501060312110313170c03010e01020307110a020616020d060c02100f0b010e0613031e020a0b040815100e09010f0e030711040903020a08030c040807060c0f020d 78
    0x60501285c46541c20356010350406e40359440c02c20024425103a1006005803695401c20256040c0091704000404c0d810241c441c0803035000c003015170548014014041e85006850080c003c010096042d0906030103074104032204008110046902c913460030f404144901f0156005103414135181642d02a81c0880951000982c0c00204011fa200002007171845401407200c002e0f00184800414020392000780c0b4240c400520325282480d90001c45640c1180041d5104031085a02c80d403907032500c1d00b070380c2d42100c227660000d0002510302c0d4015880d00c120984501481c2e0003541c2d159001c03615403035882c60910652052a48550000801a092254409041c1d80242800700c40102c03482d50340191703004021059030350f1045039546a014090a034820300c10a000c0036607004c00383d801d0050701d84400401100d0180001d00503078694100000b0544240805a0150b902c1400603480f41800400c42081da04540901d4450b88507803100801d02600441c5481605a808508405180425420300c1003089040070103e9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 62447574 1250 62446324 62446327
    0x30801050f01050406090e0c070507120611120f2503021b0102030112030809190b07080709080a021909110c010b060405060f1303081b06360307020301020d0b0f040509031e 75
    0x1780050001d1082f48001c0c00c1400c0c01907903210043c2003560480380c010081c271075404010406000110300b10682654000c00f01103810541d6a180741d40c0070f024040c55180d1901078440d8102d03000d1060342503809001e04503401241201c401704102c0350b441c203e00c428018016100611154900028030900760950300c0381240c005c0e148404040000e240704041e803004101c2e005c071081802c001c0f0140c0d10a2155030f22420902d404035010340381006490300d6980c100702c007a0044900c280008007801c48004400002d2400c6030040186d21800034101c29250008400c980c090350030125203100d07a00e4607500307403425940010701132450001290350303401c07803940051032148000041c560b000010030151000340c4031001d004400c404c413242c020f0490501382a0010544204800c03050048000102100140f05903103c000003104051030071207041a03d1030065101c005d6040d0300005800c07480c032119400200891a00341c13a01e255260214003044181c0388202c2d03c2c000d03642d105214466590004101d40302d4110380c0d00990a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 62448824 1250 62447574 62447587
    0x1309020307121a060f01200d02030c0d030608070603020a0c0516150311030c0304031724060313120c020d080315060304050c09070e0904030801050f01050406090e0c 72
    0x40d0501003154402c0c050109051985802c0c00b4119085000d203d0303c0b26102121450813400041c9500c0000201030f040000303105c4030503414070546810070b40e00b541d4041102c081c0303102ca07280207589500c107645c00b03240b501030400d079090302a01034000c140030307202c0c1b0038050b2600a0401380100e0003904000407520401802c0808600451010711104070901804d020b520581410520b100c1d42d48581841c5400425140c01c4024a0106c580d90aa079001162552201d98948417070504888040304175410010984207001446084900041118030b41d20755002d82c0701d02100d0703510030402c4501080710352500d51000c00c40580c0c0024007046003000c600c0210700746000c5042a60300410020345c40c1000c00c48030310070004103100514070784d010040c04608013102d040b440e600d09a80c9103502c848103180002e001e06008000320f00300f0f40c042c0c0c0001d0319100c0b0107010b0109501d070a0074003c040e04020b21a80d801680e5209241d00b05520600445080e41c070141c4401e00c59034038010600000c030400038000c41d001c2d041481038 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 62450074 1250 62448824 62448829
    0x4020d02030a050105030c010c0c0e0a0902060414030114040201020c120f01021b100b0105120601030207210306080c0a180b040903020a030212090f0f0f040f061802030103050c130902 80
    0x6140942c80d02200010b0542c14001454500300d070200c2128140700f8643ca124001440c0d1100c003d01f92140e16440d6991600c0d001401d8011340070301c09000754041b074007141c08a05009130f61005480400c08900a01c51a096214240341c0e104081c1d0303010340140c0100f028504c160404840900001c0003810840c1d040000c03400701c450032600b1009921900e60404800d0440c01c65040104040a0350031080400a206144001030b050340300d428603401302075035044006032083e80207074151114282c00019107640c8144885017594114400c12211020030701e001000b003440c03540068850381c5610003a102c001d0081c01d1000c000d8500548036000750341c0c81e8441c81d0390760b0340d5160340c0540c21105100340c0080014150f240780290819401c03500b04010503600340440782c0035a82c1e503030030000e062100782c0340301e10856040d10200d01110000a00d00d9005802c0c50794050aa054035442002192050801ea079201d5440792512400d0380f000b0b10003d00903500403087d003103643ca070541c01010740001e1b42400113544143d5502 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 62451324 1250 62450074 62450077
    0x4090309050301110703110318011d090a06181b0309060e03040303050c0d0f05090d0f061d0d030e06010311030a0606061706010302090102060408030c04120f110315130204020d02 78
    0x894019000c0049840da007019000645082c00c124000080c6042030352903080f14030406082841e907810007000c1400e401c10051800b440703040c180400b91520cc0c40e89041c1c00301c0070240020307124046031140c103500150342c003103a944141d070189041c100340c1c601000003074071003100502040c00c4280d91480c1d88038100929034000300b0007040154440d4070b5084d100c004204249041003d6204100184410009042c1005a10400315940380d00d0803110450b00725500d05000505a000e500002d209600d0f24030710a00302c01c445a4640f4454001908965081e000c6c1c0034228161110807000592030340c82680140b000403006d0041d0700d503104015007200e400e036115843c2c01080c0c60a5a0201c80402d0341c08800d0b03a4880071100030994001800e003020743c41e103030316400000d55070540184094582d40f808004240c6810f010b0f02258000e101148040040c2c030034508000c015802c9500301103801c823040010a6400c2d040c0440c001d07041100b0640000c07001e5641c0c042d20b071294100d02c142261b01c00e50070400c03a50007034111310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 62452574 1250 62451324 62451341
    0x1509060d0b0a120809040207080f0a031e0c08040b040203150408040e060a0b070b070201021306020705040609051b030603030906030a0507080f0907090905010905010603030c0314031504090309050301 87
    0x140c08980361070440c00b4408091965044482089405a403000210301148201c400c0d0745825074005035a0b20150030984950b020b030580741142c040e0002172600381c46925401c181e1a0300c4e101403d690f4048a480342c60012211015080e00101d08524006408a5151881c1c1980540054180c400000310b03e00110781103c400c540403100b010000c030b8107000b4803042d1001940e0052043da51001c02a0903c222007003d40519940285074440b0400003900c0710b803003901951012444054080040303034403814045c3d1204180d004480c02549022000a42140240512401038610081b0381002499803861000e20707900045c5006c2d0940f104125045480d160390006500c104c41100001442e418070b08801040c0304d03405001c0f04003005140e4140301407540041403110840e0000d81c4005003001d40b41c035105000d041c0241014040c2e51034280300005054102e0707140030240d8800c0d0358050b040c1e122920300c850b0600080e10140b901d49000c5c0110341d007509190b80b08a038024042e0a00400d455500c40020b82900c2140c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 62453824 1250 62452574 62452597
    0x1002160f0311070603050c07020d021810091802060f070503070f0b0601021015121721091209130b030106240201091a251d0f0f150906 59
    0x640031502c0748052140f00302411485c80d0034842070034071100030940c07030051500180c40b4441182840d01155910b0b00c10103450490315a181040d4a0410845415036803d481007024260030300840c00380102c0e042c861001416030041080c0d0924040d14800100d5404c0302108441621040010070b0125150020310700c0410300c51030708100310f8078140e800241404c0780b000e8404082c5040c492000d030454000300f050010b640511502a8041d071060800c5881318141c04450401410009200030200c00528012205482d5006400380075403121f001d040d0b99035845044041070b101d0b0621a5004600d84000c15102c801e00c4440e02148150805000900715030040d4040e04464a100c8400e0015600d00000d00010a0480c002040f407000c45444241d40d26030604000c0410382111400603c16022080d0f10742001c82e61041440c0096140c0c80015298144c20500080d1810111510300b0f01c5240c450700211504d1406454007941d6480841804500084082544004942400380344482d80300e0102400626110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 62455074 1250 62453824 62453837
    0x703090507122108070c02060a0215150405010b03130b0a020c01020c0106060909060e0103020906010c0c03030801060207090207031e0509040c020604110409020901030305180909060901110c1002160f03 88
    0xa20b00a881d0f510b00316100f40e043c01106810040300d2078024540c10141601038400d26501c600a600480c03c15400c01c8000c19826901030a0041211805001401002090301c00b00103e980303a020342c52403800216001031030380b8050300c85040065080400c01350420b00d205009400c000102d03000e1804c2e40c0001074000d00c03070b0b07644400c2008580c0d03115281c00f000b003d50031000c10551782400000290f5200c14080a401401101c02048070381e4858001c400f2290b410090b088001c2d5203074170340101407660030710400c4010b03c502c5401140e02c01842c03086a9506a140d243d090f0b5000405140c02c2110201281000501c1024840c0c10391942715801400e00da81031503400b42c09a860945058400c1f010624007007400350b4505085280180c03038030b01034541506d406050441e02c98050b100b0610300c01103060b0080c2d4110080c401172020b50140014030500a41c2c41030020b11400011144c1c0030200e002c1c0c54080050799022150341c41c8140e840b40d006200d09004109140b241071140e0702e4001880e8410704c000ca00003901c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 62456324 1250 62455074 62455103
    0x30901050105010806130e0709090c03120206100302010c15060b1c0c0f1202040b07030801261e030d020a0203041a03131e05060901050a0c0e0603070309050712 70
    0x4080c420340e4094403007401c05041d2400c00303101141c40c44400300e00e803451075030b40c4904600341218200089802094000d40601803c0740f140b900021300701c454401121446007139601309071030074001328800c4e124400c000e00c84519076185400440b80c49041c05000c0d2050b4044072035001c4400c860340a140f000e8520b46201c1561404030000d40e52100c08031250516400380340c4400c0403603036a03102e43c0c3d00020075031900c1c0c00e200f8003d0340101345001784182d90203070300b01400c006510300030185c00107000307812202d00002c0701000349a0340c3c1c140591003081020f007a1490304000220442151444020111000f0714011682815413060000040780d010140482c05a031010a0030040f08070300b50095014443c060303c0b01070440c00c3c0744001028030001000014469449051400c00c00608407241000050f001340444015080c40e5011034020041030b15100010703414251540300d9107001e4a10401ca080c4003402c0d282c078543d10088110010840040d0882e854055030b440000d068800400054542d8001c45540c01c0c405c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 62457574 1250 62456324 62456341
    0x6160501020a090b0403050601060e120106090b0108070813080a260f0105180105040b040902031c030f110315120625030c08061003020c07030309080d020a050d0f09030b010b03 77
    0xb0450344c80700b000c0c0c5104110a00004101280321411103103a4201090304002400020307027500c0c40b20290070410340c6001000901002240c01c0b10502c0902070b00c070701c01541c45032402214585411540c074952012a80c0d0748a001410000041c05040300c180303800711030000c802000602d00c65121040f041c0c0d0450803018001704082100d1030900402041360744400d40d05121040d907410320014441c192180d607070b4001588003a21103070009010294000c1c255140c1d224201d030900600401c070f07424100007920345400c54026403018420064078219991006003190f41d00400c0645040d200c1118a402032002015540500b00c100b00d403a000355080029000d018502d21051010708014110344010142403000b046512500032261343c2c1c1060042d2414058810811420b4010303101d1450014001e21540d4800424958050508000d8030000819500c42500061040341d4034100c00c5c00203821500304080d000d5005001e19030f0114004950304160401d0740d525250542605000d81c8401014000041084102e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 62458824 1250 62457574 62457587
    0x1204030b011706040302190809180a060504020a090506030a020c0105010b04090e06010e01120218090109110405010f1205010605060a0302030f1602070603020711030d02070e0703020307080402040b06160501020a 92
    0x502c08900412461401ea10300958031a041d035424030a40600b14106824840020700b1107000900143c18122101031034a255540c0c0350302258010801864030740046420300e802d00072582c04404ce5642d10362040d040c4810407003107502c050b00e0804400c0c1d0030440c0e003015180a025480c020302c24030b018603803101c1ca42900c1c0001c0e100480002007041e0400c10040c40700c4500c005003181503618200c6a1442000188089040707081c80c41100d800942214041001d42041508410813040c401c40d01500d00900ca001800b02b0f4400030b0003007501c43e82c14420144400e44107102c0744140c840c020b034004601d003a41d850110b4060b0344010b00d5140000c0c1c000081100c1762a0b6400b503240c0103403d282810b00302840c0e2280094481c2c0490051004158000440703c003406114003190748100d6004042d1880360b204120069a64034907442801c0280c0f5142c000126000d0092080d06d00c110500e0701c41c0c50799035540b5800c220040800d03440440d03101400788100325041c0201d100341c45d035440c0300e0800103a65220040025000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 62460074 1250 62458824 62458859
    0x220e0105180103051c020a050f07080c0102010207080f0a0918140c030403091505090a17010c02030408031c0e010c03091529010912030f03050105040b0d0f02031204030b01 75
    0x1801403003070040002400006200c2100c05107140100c2c040d8000750000ca0a141d00540083d00710b120b41c1e0302c041031001001c00d01304100e80c202d10480300c4020503036006900303038003032140007802c880c2060007114600d8030f05400a000c050031a2a00420785916011079140864100340301c0c00f99160341390207442080402101c81d6403ca803a00542034154035260b60002c0100300c09006051100d00d039045400395550240c000e44140f907800030100c00d075580c0c8640b003120051024812648556080ca62605805800401140c0956031400055032a202d208485020543c00848900e022280d48100e9038110000a20135041d20001d6a030300400e8042050910600001c82144014a017628002408810041041d0b60741d058a20001c035410b024215400107a80c05010390b40038540340d0300100c04450400d41d00103516030310f00031180c60400450340c83c4d409000859090700e00c2039812280740700276000130a41c0c54080c1e503401c3c0d100800300c400e40040c1d010300140a070446d501c00c60300c0d81000c01c0103028094542e12400301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 62461324 1250 62460074 62460109
    0x40b010905060a210f14130309060509060f03010801020703020f010c0906031a09011d100e0406050901060f06050909090c09010b03100306021902010e070302090c220e0105 75
    0x104241007400085007445007203411018001002c0e5030b013059504111085014109040f81000f0704010b150072640504a41e0440300b50760040d4100003000001808640096950940d030340d108200c1c109941a180d80d1321415001c3d900c10428842003985280c03260046001c1d00405001588039802d078a170103440c114681580104590414024944003a8004003c504580d01c0c0e1601194032010090034002032041c0d0100ca6802ca441c210011945e503500c400708942200c040352482c03515a90b0f4291005010701c190046078401c240040128000c5419900320a4000503d0f01c00024000e83e1584542840f800740d52024001c0307034000c0f40140705498075000c0350341d10140c85d8028280704405440002e2201c407050184411442010002c26400303c2e60190707210155501a1003150366122046001c1c41c01640c0d031912800640c00c00b450040c0e010700208840080780d5028004841d141c40702503a07008c181d007105544000508500000000d0140113a6410f4000c240c3c611410116505100500801c054400400b40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 62462574 1250 62461324 62461337
    0x9090506011a0903010c0e0118350304060c031209030c170c06040b0603070b0301051309031103120103060e0d0f0509010e06120108060c13090506011412062d040b031906020306040b01 80
    0x1290796841e514160000701035148803054005068500c1441c11962b81c071182a0344800300e400b24410b900040c0780f1501600030341303820103a91606403242007503e0b41020004e001079180400100014038a601007458543c6282d0568103191149000d2031505e60115400c1d280c8000c004240046401c2c10f00050300070b00030411845180d0746c10000801d141140a000c030240640c0c0c1e9581020034107100c1c141c00c008207130001050301d50b541e524000c4440362140a0009483c80c1d40742c0600d01110345000121100b01e070302180c4845c003881660b90300585190300002001414803c0140c00d90303419a13908001000c0c2c48400500b071840030350411242d40c0c43c0c200e00030034000e000b0104212190309841420103440407100d4650020900f680c070000100c504107165480c01d020f0709008102868190382851890b4450710013a03855003904881848250003910b003440d104116030314040c40710700c11424542c00407a0110300280031601d2010000d1130307002200b15802030590350545c1c040284861460301d401410030032442480e000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 62463824 1250 62462574 62462579
    0xf060703020a11040603080d0605010f0f080604150503071707050306060105160302030d02070809040f0b0109050d020a1e09060b030c030a05060d060e0708010609090506011a0903010c0e0118 83
    0x3030b50310401e01c4405400700b052001c0021050392150084009503501c404007648030b40d208520640503052034000c070b80c0441c180c0a13101001c603110710b40c1c0600a4105955150094459030284401080c0d044005002c50341c01c40008646500c04004880c02880b0101c005d0155100c0d07071060364145466034200704d1183c1c02ca1010722456a074081e00f0b42e00340c41e000440c03840ea50711079480c1c1680f440c450750a455900f00d00100e090030074004640301600d0700c04003d0360140030140748122004116044a46102d01045400105011900300703500f5080f56688040c00c034604094941da8a024001141901c5001c06078843c4c80501200d221030007010f00401e1428540390441c2007500c007034655404010003440c1d101d5507800000e5000e5807913800801c94250001410404200030340350f040d46074400c6025400c810b6003448000140c0c2040792052088450304000500020790130b01c0e10380044030300032127084210b5031b8040c001600d02d541c0c20300c121241340d81c4039296480c0c8040044005040c0c1010441403690941900f40304 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 62465074 1250 62463824 62463827
    0x1e0c02120d020d05130302090106090305060a050123060f0d05040c080703030e04020c011d0115060207050a050607030203040308031e18100b011b05010606030e2a0d08030906060f060703 81
    0x204100f080311800e013651580d03101411004204903e9001941c820b2007640001502e41c0c0204503101624012000d481c0075a49056003081a1b600c00e02c5564018500b100000100c1c51300d020440312041c400400c0c03d0319006000310402c1e125004100d5048465031795105010421240b040b96800811111010f00442480c40e10f0150a24003000d070134a014640011390503000c4002903000c0e8030140385a44c9016440407203c800e2500034040094205600e9054000c0458914000103070003003107480041c5500031650a01e028440560080b031411010b40c4000d100100004001030080d52003040e04881801c40a8010ba0442022500181002c2c0107644010460213000380e010038001142c8074000000300303010700580c00480d6580c5000707041c54030880c42e4042100170040e0642000044855594061201000038880711f0303101c02d6060400d02a408092204409925490300d19000100f40100040d6195020362541101030b401200e20800343d4206404000c8036292051403000010403e031046814103d40340d40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 62466324 1250 62465074 62465083
    0x150a0e040515060a0302030604050d02240c0a031103070f030c050324120a0f020909030f040e10120b04020118150302030a15060c0515160804031e0c02120d02 69
    0x1115007020b5440c5002441a45a604030800210341c0a0708444061500381000340c0c82e87c24400106005004270491552179001ca4081d080e40384a5240c0175900d19154883c1140e01035010045075020b15446450240e0701815143c080c41c41503065840303280140b4003001004048403c6d990003141800340a00a000082d0440802d0075001d031400c1c819400c540c8603040001c0d401d04070400b1188030b44d22800b030036002009905d203c244081c0c0d1003507420900300e4440d21241c03500d90040101c09042070b00280410800880e0200e9820f0b00a0211a000545261a440b54950025074904181d0741581500240411940d000114580340780e1002401007178a401c1c021460300c0303d00c4800540301010340100c04205042103039400710078044900f00442d00b0543da1000c000d80078bc0c10b4884103a03114042c03e042d101c80140982003645c42072101c0c0418901c8600300400503107011201502c1902080520081150000075034840c040842d54543c60f07031912281c0601c1041481d481201d10312026421414610368101d03000503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 62467574 1250 62466324 62466343
    0x70201050a0306033c11060315030307060219090b0d02340302060c030c090103090f0b040c0f0501030b0d060209130f0c0e01020a0317060a030b150a0e0405 68
    0x603180399a25150041240078040e15007010303100030000545005162081c02076001c090040ba501c2c1d1740d003a80070501c8126104104c1e01c003e0148031054021861a2802c2c00045a0080c808080c03540c1c1d80c132800c03000c28607640010b80d04803001c40d4000384034200941a03c1080b5007110061038036881c032a092503800c0c4c8080c01840030810700780790003240c40420007017490348043e114816400107008201041a4009010036400c0c01603015010310000704603030725280002c4034817034a06010030340e2800c044000118000c002d04c02050750024242d240c844000381c08140380900950082960350726207410700b1507039684a502360b8002030600d032610b02410101d403aa0030759003130700c20340040300180c075080b42c1000700c0c0fa15541d03805615030089c0b500c4500580d462055100e454154200e5503050780160105006a0382c90420100c00b50101d10340c03041030400314608a03940c69201da0f01030202000d650b43c1e42c1e1101c54101e000d4450f250051042080c00e0303064100030b1150f000815228001c000141860340390740c0e84400071103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 62468824 1250 62467574 62467577
    0x8160c14010f03110d1a0111030a05160309080d030609050c0c060a0b06091009030b0114090a1e020d0b030d0903120f170a0209150301060203090415031a0106020111040b070201 77
    0x2100d400069007640410740d03201c3c1183d15170501813030113442c1c4113001600b983c0031030303601164016442e0390307a038540041569404540354488503c0d1400c1e40c01d1442081807030031001c03020480c0c159400710b0f500b2014440c40400640c182c0f000b081c400d04101e0f1480940d0401066500e840c0c500b1301c02d045036000c00090580c0c010101c01000110801c01c8004105544600344185410001c0030014059003607103d841c8108a901074000c909080c1d885031414982e410001c0390300380c0d00907841c0d404a60302c44859400030304050b58221010802d00003000080050381c12211440d81c0b03880e80c0b901c7c098a18242030104641c040598509030200d60304690b46c00c01c03000e0030000481d0401900740c7c42e182c08a402018900c1c2c009007400310b500854645000960003075486002518040c827800c10380742d20750b81e80d801c06030780c141e502ca50081c504000303004080c400101086502c42c50450205440000420034804e440c00c26a10800b000d140c0315810024081d0039035030400d000510102c0c04000030000c07108240190b44856909 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 62470074 1250 62468824 62468831
    0xe010522020a0e0c07120206060607110d06110901020f0c010519020703080403110319020906010309080706140708090d0903030c03020f0609060108070501050304120e0d08160c14010f03 81
    0x90002c0340c2400d880e82c108101c0c40c0c1c8620306014006199402401d00c07684254040c04000c0c0859070304a84518085d680030b40c00141c248605030014011010400003150060660f08254003903882d41001d6421083c524600783d00005174120345941d05200140d400c02001c2c004000180b10400028001d2103920760311082c2075030074840d00410342d02c00e004000007182c10802050722035449050400741582c00d5803001e1b110b8400c80341801112064000e0508086400401d0340225564160065001d003005920403604e4901c1000a4000510305104540705500e504010703038840d183c6407002404850b070181070045180d20081c03000d00340550102d000d1090342d5051600c440003401c6840e05030714060001301031880d28051002006401000020898100c8044400700c0341403503500c10040d1018803040d00d010b40102817080101e40007034024070703007051080c2025111294842c010384451410380c0200c101c1d03c42540da00040013090000c081600d2015004610180d0454120f5200181030320303e42140c00f42c18543c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 62471324 1250 62470074 62470141
    0x10302040b0102071a09120d210b030a050d030501051206060409080d0504030807090f0f0920071101030501150215060402041a0d050708010605070314070204060e0a0e0105 75
    0x309201c0c007001000303401040c150340e109030744030171040c1e030131189841f400f505480c00525440040040c1129003100d48d1b03265100901c0b61b15402e03c42d9859640b0b43d04c040151501203800c06610100305211503240908060301240c511090010262075044c1d002078031030b503240c0620003400b110110b9030581104c4101c90000d420403023407502c00202c0c045c520803500e0013450708042205264000200600ca401d00350ba400d1502c0740c88039148100913180e4041c0115041807000280b000300002d51015030180c82008400203076681303004040d00c20760302c440c208451914000c6d007400a5540c05008a45c09810b501e05011f02c43d14000030300a648010100c41c54001030403400228449460b0ba0341200d024104610080c0c1030132004400054195204d00e4600340c4092600000030312042c4075041c6581610a10365510389415182c0e141214202c0640400b4140760004000a40040c2e5403031040c20010701b9460f80c03503072151038592410421076800300700010540c2d041008000b007011718184005244c10b6101e50b203850008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 62472574 1250 62471324 62471327
    0x302070b070804171e1206010e150d0e0f030408030a020d0f14031504050a0902120601030c1215050703061404090201020d0521180d0201060b030103151503030518060f03010302040b01 80
    0x80d0744002072044140046d030314000d1851901241d104460071b88500d220400c01c0d2050000d200a049180c07113250300c00340103001d40061160400d0000d441d500003216900945080343e1070a44c0c0c4160b05c2800300d41d0001034001c8a403901402103140300e1046003002800c4c4020107201410487c840d0b02c041190f446e00100140380f803014440503c0208401510800041c500011704400500c01078a050348121103010703040485160025659041c0ca911680ac2c054080c603001d4400c0c2c505031060401c955496000000c016540b032a0300c6024803500c8550340203e42c0c607140183c0a40390484c040c2d03a29004c4c07410002e040c0003503600007640034041816440c140e0b1703a4000dc545c0300000801d0305043d018502441105015140744050382100c01c1e41c040c0c006603072000e00c03a070700c3c1642243c1062041c200041000d000400c0450411030b442030302001680c1002c0f640c428805260000765500d500300b1004140301203841c0420078260405011100c409503101442e0403400100302c089400141f000906c1036880302507048559 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 62473824 1250 62472574 62472607
    0x5070b160302130b0310090207050304060f020f0a0605041e050601061209020d050102070b100f210506071e0e03060109020903010b03060406060302040c1b0b070e100302070b07080417 80
    0x5040301d040803081140c5030201982c00c3d90051b1920030320000c2d600008205c3c540c40d0b10840300040c0c1d102000354a468505070058400341176000015047d8040c10640c200c1c40e46e0144007034901c46100d80340002d42d6150a14092080c400500708001c0c0000d01894203400041000445070305465607410700c00c2242036074280040140080703000094020820185079000c000054014001403441610441000d540c2c001d5800418085880750031010480d84404101c80b541803014016120070450005170700503620303100c407860000156101c01c00103091055000c140c20789503803001c44405035841c100240c154240b0000b65180703c180170708981c580d8000b4007045141e80942c4548404000501514038034076240c00c0820041100d0f00c8241e00440c18609601d1030f4070b02c60160f126407103403030022030750a010240d22102d10755807004100c0000d020210090703011a41c0c644103281c4040d80d49550150351402685020b0301903010283c254800d10554205120004000b101404074440020302469143c494042402100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 62475074 1250 62473824 62473837
    0x91109040b0a080d02030316050703050f03130b070e131a0f0307030c08030d0e0312040b0402040f02040b131a03070804050c0a0311090f0103030806060702060903060c1905070b160302 80
    0x41d1013403103411814141c010000d9403248241d0320801050996102c0c0c140c4991041110060000d4003c02410b451001c0b00e03005190404e60411643c01503034502c0c2e03110050310009803442030209000141d0f04115103400c5031801d642592001b003d00c051411900d0000ba042c4120a0051042c9030f11680b042c0680c90801c0444011354000840f0140c0076614185c8944030380c41400c0041c4aa0f042061781d80103018008101d541045444d962101aa500c0c0c0e25413003912503014108a034400d0b220560400202d2550000d44042c03d2180040c66843c84c207100c070a07041c41c021f640002450b002d50984034010440782c2c1d055a5015540d13040c900540e0347c6501d0039504214080c60210b502c074032680404018485c00c0444002c0d001004e654545081d00c8142d010350321400700340700003000a140c65001654504151018202e0144050402403d001004000a080c80000c03a403100340070102041501021040003403114000100d4200316207003501c80e480b40e003e080340040560b01081c081484120a05100360b0444a4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 62476324 1250 62475074 62475089
    0x50d020301061823040207050114100906050411030f06060d09030203030412110d030e070302030a0b041205030403020a1e12030603050f030901020703111912020a091109040b0a 77
    0x16a981c4441015100071601c808070002003100c0f03070001c10302c0a46100c2002400c0c40550303200340c0c0c040030030003040080d612030b2804135125501c807542c6d408a0050070f0b00d41d0380914508035100c14803500300b80640c8111681580894440c5080c03801c070250b014090801c40c0e40011880b0524801589d0300c001081003445071a85642416103490140400d00d940031010b18042d83c8a9400d52021901d4000200c601906060b400040d40c0c2010001d0544103009034031984d400a080d00640d0101c9a03640c0000e81003040c00c802c10f8484410f548100001c00880c0748064071203401030b05003a400e40c145a10025a00d05030240010441280c000502201107541010b09070015449182c5520301c1d007501000402501c25480111518491546c1206480c07102005403844220103900800c0201c0c81e54072005482d1030081903840e04080300c1907080c01d400a030001540c02600c0c83c40b050300d07007401003881071102d04c141c1944000720061401280780c0d03404042008980c6910f2046030007140e4010404000740160060340c1c001007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 62477574 1250 62476324 62476327
    0x19110409110a0e01090507030b01020606010e01021e030304060c020a030801140604170f0f1c05030c0903010606090e060901050a030b06040e0d020709060b09010c1202010912090e06040b06040603090201050d02 91
    0x6410000c0241c10f410b85185c00002e0140b80c5894200303a0980342c42115643c09038215900188255108000685840c4014412106500180c112a091507548008000032035000082003009010860160b600d4044062004241091130364a0060040c8018020075164010740ca4000385166180c1c2d0036180a404850450618406400152a5141c02102c0c02d071034039001e0200b42d0604540003007070b455044044414003d4000c405c0b25402c0b926548002c05540310300d101800070020b1034a003482785038098403854440c0917000c2c1c240310841c103420701d004040c244106c20000061001e0740703072074143c00d0480f903100c1b04112050300d1f0718001601400134803c038456203104940754011000d50004500c0100d90050000300080ca0b240e61030744101c2c3c030440c40074078080360703022000c1000102c14030000103144015200000344104c8550b00d85090402c0728103444002440c42d80b05000c004000401c1641110048034100540b030042008640c81d4001c500c22304d0289640c03481280d066901800444910b40c2c20903a046 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 62478824 1250 62477574 62477579
    0x307060c08040b06030105010609050d0c08011401050901092021041b0803090315060102120a120b040507141e0c0607020705060a08010509071205090c010219110409110a 74
    0x100441d00444040c3c62094901001c02d03140d04061041a060762200c0e5a0441c44a00341170500040d5001200b040721784041e07070316000650ba002031040110b240706070250401d442d403402c001c0003940f9006801240201303203400b0742c810004008995a090003a1000e101685402d524030009101011603800c5080d0400d024013000200210449501e10011400e040f042039070340c480e943c0d0760780c0380107200031740d6050342c0f200382c50320304030058100d0840d8414014412101154000190301c05160448284100440d120815100b10000540251b0340c50840980741007000d8070704540c00406440014400c3c014500c400940c5618a000811024072101d5182d21b04607500c0d00d10f25442c9907201800c90320300005000740c100c007044a10305003044900c94449551a50300c10f1342028100301f045100030385000c003405544000c4000480072409401d118130701c100c000d0700404426100283c1014403105142c15450350b030300c0864001421103100c10040350b50aa4002a06502d0303850070300c2c11900620700d2301394491100d1000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 62480074 1250 62478824 62478827
    0x311030a0b1005040b0906070804050a09050406060e040203151b2a03070b04060b0d060c02030c06060111030f2d0a030c14070b0a0f020a0906090f0308030708090307060c 74
    0x1607180c0020349500c2e206054141007100c0c02e000e54000c4213040c400810401419280041c0900200b601404d55149090382e00c0c6c0004201160f160311414070191224100800e0102e00e208a0000740081000c4800920b0140d0000384c42c0d044200304c800115038140003041003504112080041c040c00300702001c1c0d6400d258940075a082e40410b10701003030810302801e03a802400d808000da031034403a848411224240c07960342e1440040c1954401d895000814542c40d40c01150702c600920780c16603003c3c1c0207940d6640910400314240704008041c141800048655048501000801c640079094009070a549035a103c0da0480014041d14281d00e881c44c0da28102c00d0140b00b1464010800741070541c808100001010200303075403000c000d12907103e0b0000d013030060b0000301d090b18000daa40480c7c00030740020900340c40315082040380c00c03080d01d00001176120001840400d030410b025030040c005800c01e04071003034a1913448086511000740303d04204080030020601c01e0f9801c009460744994044020b010405201c0380 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 62481324 1250 62480074 62480081
    0x905100f06020f061b0a050d020d090c03150509031b0109020a0609080615010f03110d09060b040605040504050a1b0314010c0f031506050f040e0a0608011b020c010e010311030a 77
    0x382e2803044c09448003041c009941d001410b03540c0715542e0f05003421301c1c029000a0301c1940254125405080e0200303c021210900340c0310341c40c504c910910105011505504140c807500c0009041000ba141c0b900342030040c100300010942d00d00d0440c080091101c00243d40d005c50151515150007500406400e001069264204803428262110743e003c0300c403196900c0101010408030502d801e400310300007007202580d081c07090704030303060408042000c585000348811142c400c0b0380c8142c5d02514926580c80700c42807141b429001e018000e0104a8003401581880d4803266243c035903204000f8043c9000130b15210140d000c3c40180c000958100050040407c410141d55029141d0281240c00043c0c2c0500d541c50064000e1103078100b100d0305407401d0000e55042841c103642503071003400003654042062000140a075000104944602d64180003c5200c52030203084030709403590002d6070200200940c0001032195800a02c60300030702000d1070803001c40f6201000580081242c0d600c02016180f0000400820610340c1c7c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 62482574 1250 62481324 62481343
    0x903070c0e060907180504050703020c0316030e0f1305060a0b070303051e0103150b030316050708060109090203280209010312090e1b0904020f03040f03090f0f0905100f0602 76
    0xb50440c60f50b44d00d00d401284e01c4120701c2c44004da0304c10b10581c00e1110f42059441140d01214a050040c5020a040d00c4a0f10b981c01c00000b0301003030f862144c170b420201030348020641e01c00541034507413800450104001422210601f10f00b4400c0c142d0f11000210349545041b0350030001c040018a4a549030a2401c004001c0d10303040303070b41040e8400c443e14a40e0f5a03074200e40f030f401d04903a0060380004075000215418000f0b0304080c050a9850b100a214400b4208060380d050f480d100c4c070503c000d01e034040c9046041e5051080590060f0348083c5407200c0800548c9002ca41c2003214510340c00101c49a9813809400c001a005440c13000e50890315100c000700c01c003c01c0940f40a0840425212207450596500c041d01580c101103540903801e01d0a01e1241c951014810054441c0300c900034009070034070346100d1102d40c450700b00300d0341901c10b003001c4004c2e9400c0c1a04085820043c00c40c034000090f05a0400416040c2d0954610905620306d46d28400a03101c11a50820803025107100010204001c2e622003000b5590140d05d07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 62483824 1250 62482574 62482579
    0x10605010507020d03030f060b0324030304030302120c01021e030a1d0d0f020a0f060b011d060a0f0c020d03031e020309120a05040e0c041a0c070e0903070c0e06 70
    0x15008205036005078141c44090b0b038010050400303844c01d41c5e0124050722940f00c2c2400103e071140381c045203107802c000146220f082c80c0e80c0c0301c3d5400007c2d80b00b14140c85842d68100d0740650001c000901c0441d6020405c05014500d0208a965030301d200c01c04240284101850042404004040491101d07030b00340c0114010524140c0c217112850402e040c0481d541c007504203450050f40000c0806030214060302002e40340e000303140142c0384d66403640d0f03c8000b0001d118a6084920341c1d03907080a01310390341e0083d180041030391000d1203400391594001d000c10b20724450006280d003441b0800e0b8000081c144078810580081e58007070054102c941c00da2070b015018002c01038800070401324419040e0310039070880c804c2d648116038400050410703400a2625a0183d8821082042004030402010801e17400321180035004000a500d6140d4a41c501482c00c50780d54548010309990f03400401c2405852200042d403038042d14a0880ca465982c0c0b2a015903900d503200d07994005207203018074400010b059803c41800c9207d181c05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 62485074 1250 62483824 62483831
    0x50106050a1e05150d0e101503150b13090b010905060f031f0e032715030a0b041d0601051219110f0a08160905160c02060f030f0901 58
    0x48050180c08400c405114076000c40104904000518044513a94050303001c2082444c90444200203030016241c03100040b040300c0d48090402c05403195203115940903550300c01c05801c00181107a5071640c7e4600040c0046c2c500544414078041242ea8001504546070150f4404018414041c504052002000d2049a0840385801c1c0040c0701403c3c8911070000c1e031800100600708482160700f0f0a188000200006144c9607952034030144180d00030801080c00001c100c4000313f810419210205c51851180d42084c05404514010100c850001040e80c2c1c0041c101c1001154042e109408500104180900c0940c072004850288410030400f041c800c0c142d540030b8800311a00302118000c196180040306006106c107100030412004582da194030b00b011500020a00307040d41d61102d000034180300040c1c11605d03c60304484503c101c0344030740c0c0207d407004200c9103e0602003407502d80c1c4a400902c20001110341400f141d200f8507411543c0c1d0000b00d42d0300c845c200303400c01c3d241d05207407000280c0e21008980d40320f8a5842e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 62486324 1250 62485074 62485079
    0xe070f050903030706110f03040f06050105030a0b01150216091a1503040308040606050a0b2502031906090501110306120102190509041b050c15041106030c0f07050106050a 75
    0x30030320856280a801800841c42c1589981d101d01c000d050310a0801d4199800b40040b0003881e0401c0021030049014820f00b500e0300d1401e0400d0000ca0f501030f0f0005229520083c00800068850b18503641114a5011480d04501020f4020ba044c20a2090404954004098041030450540c3c2c4001d070281d410b540d29211030b80080003400b126060910300c4906645040c0b0010f0000b03480f40c0ea02c0c0f0f034071610840000c02c0481d60313a070114210495980119450b0840440e052646018104800b0700105201044514000c0c00b038020a456100c0746d00f442200104c208400720601c8040d0f04805281c2da84100200311043c410f02125005070425140380c6d2084030081c100d038102d07080500070b031040c40c40a0481058000008681030b5044d90101580f203800c13603111810070b094001e101c0d244c440107010740d803160b558403402c0e02c1c410741c20240c440c0b0011100c24407070003e100104600011440c0b200c02c00781d42c2c00f0340c1c1c0d4584000b5801140203020344109000070028101007040703c103400030070446a041d0752100c009034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 62487574 1250 62486324 62486327
    0x9060e010c050c06011707030c0303020601060305060603040b040305030703020f0706051503060106020d080a0605191e060e0d050102070c080c01020115060c02040f020d020f03060307080109031e02070f0e070f 91
    0x1040103002c3e042d6502c182d005209404220f0704500242c00c0031000ca0f0341c0d040c1d4a0b9500c0c1c9284a00d54003c1d009600040010094240c25014803548901c049405504c1e610b09035860200e2130b41b01034030140400001200049101d40a98115100c000890212a4441c105464114040c00d4201d801c3c2c2640f40900c0c0082200b814002340c1241a2240c81d00904a08401100d040301e00d110014845110251079440002c2d56485500016580300744c402d2040c100755042103401e111a1101d05411012002e400004011b51a840b0054084e07404045a111905940d1030404078068010b04c1009000b88e9007103078000a0a91000130f56044044003a0004d2125912000b00c02101d80340c1780c480c5001140c1262400e90051030540c0c888802c1380c030300c40c0005081c00c2200f64407000f01c1e00043c0000000342000400d1141c6403408008030310041c10321400900c0140c4840e0360062a00b40001c0440460b16850551130311164001c4c07080c000503064020710b444509541c0c07210110540d4050343c0d41e2010907108403510310030a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 62488824 1250 62487574 62487577
    0x5070503010c120506060f0307020303070f050408120711030d0203030405010b1c030807090e0a020714010c02031c020405060313062004050d050c03060907050306071b14030d09060e010c05 82
    0x440c00b0f89035200242c1485502c00f01908000f01000d621001c200310b4039618188520146010304030b00e900440c0c5910344208054071000341c9c01107090a11000b40030420420500084c26214140d4182d40b17035494401c64900b00030004661142c4a030b250250f404d0340e51010354000051031090380120024410480d4041c140450b4110310858007440103007800c69440070030b0080406a4000740c035880d08201069850045501d8100b080e1141031640c2c1c0c0003c0c000382440f10041d081d20b040303580c4200070000400e801d5006580c81c441c1c0c0c2d5a140f01240140e10351401e040e01c07a030540b0300409020344119030701e180041d085000307100d540004503031851514038081c0400c2a49401c100050079200101031810b4140005c01c102080f6240c0c2c121100e11074400001d400d034400380b20301030088071310b44003d000440c1468201414000c000701180200001d240c0644061200c804c2c1c446106030300002d40352000c68000300c00c142188180b00100200c030341001d01c0c04041048552010140d03403000c0c4001c002e40800d0303050441d1203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 62490074 1250 62488824 62488841
    0xc05100207082b090606081002030c030615040b0409050f090a050601050f13112809050d020402040905041a10050904020622060302040f09020c151b070f0507050301 72
    0x4190622403c0d40c5105450312000d0107125049041c0c000e40044000e140550f01c0c0c04600700c4031a0b45502d010040b0725000c1010560404880000f5421441c00350f40030509400300500c010302c12522200c4e05502c1440d0142290060b00c01030300341c0742daa103484840e988040d10060b04c1c40c06600721944002417070385802085560039207034041c010784203d910b060204908010801d158642c0550300300210401c0800b40e2040000315410807005a0719000c2440000c1c42c10a03003041f5520b0960751001c2203200580c0c0c000c10700d40c2954801c44e035202d4007400c1800410f00a019507007206c0100c0b03107441d00348014080303265441c948807100440c03a0049a900c4291f0500c02e200c4611442d9080040000400c00620f80040a8040c01210b9505040c1070238100041e954148210307403040010a6001400f0b01122007443c0641d80a03104001e410751400c008002c0055503400c030400c2d4540150ae441d40829503080864028583c0c1042002049459a0ba241450388d84036501c50022140e80c42031140000c3c2904060007017201 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 62491324 1250 62490074 62490083
    0x70f050f03040f1b030f110103150605130e07020105040203070b0c030f091c030c03080907030305040b0c07090c09060912030912050f1603060b030606060307030b01140a0c05100207 79
    0x1c42c1c81e59610180c0614411000300c1c2c0c00c41c00c20103884c0150401c5141c000081d0300079003040401400d24101000781d200c030099018101b5040c10281004100d0020300c04046480c180b41140c0e44d4844210821000a0300341c002542041c140c00c280840740ba0b05410440c0540d00860540345e042d80d0310410314045104844803102180c2013401610415542c13800130745442d450103000c402c0c084455404102d103003441e010003200070401542c0c014080c103500ca411181d201d03c0c1040244503c5040d030700d000d1710900a901c1f41c595504030006921076840401d1100c50010701a40e135003445403420201c2c001e841c0700c0c03407409020009040c0300000541b54000340e13113481c603150305038807550800c90400c51002c48001b80d0b048240c0b014480c03002c0003280c642d01041040403020038001600301460441c030f0004265031840302058865800602841603540e54070003202e40200907800c0015075900700780010383d030a600c515070650418502040352104142c02612100c0e0041c131403004c2d20003052003a41f61b00120b000c2d4180c05003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 62492574 1250 62491324 62491327
    0x150f0918090b010308220f03020d08090a0b03071106160f0203042705070503091506010207030b09070e010f03030905010e0607020603181c020a1e0209090303070f050f 73
    0x10030345005004480180a150340c010a030307120300c0c0d10b4a4295900c281e104803180440020382c10075030300d84601004101ca0a00902c92401031070180e500c401180d041c040640f184459201680270000301204071075150102512952119565989104040d001100c4802c04034109003c050400704c0c02082d214840c0c0200340c09480085156441122028031000111055103c2003001007030b03040101c141420034501415100402d414242d40e510300791080030f0082005d0050500504c141e003400490b6582c0c2003a8040f041402036560080100d1030301045504c0900300c2c441030000d004058101054041c1911103802c46010035998443c2c0404203042c461001400140110130240910341c440e0a904100810083c0000e00b480110340004589600640d07049244203202e41000310040414070050410300460441220040340320400652603039281c031802091480b841c040840114410164503105c2038003d00820014908204141d80c0d0b03a10640706034001c0782d00b0001340c1006d18800c0c011115840039083c05507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 62493824 1250 62492574 62492579
    0xd090303060e16210905150a11070b040204050603190503190c05150903042409060509060403060b041805070602150613050604110c031804020708030105120307020d0c150f09 76
    0x10413100304040400c03006580314407200340401e00070064504210591031103403040307042505144081b500d0780c44002090380c1c014080100851202d40507954032a4041c0c801042c503035101b2000a060000c01202a2029a200715042007070140020191641c0c140c0d425540754030a60b0b24a003559210b62504d80280b40e0782c403054442040101202c807107038200c80a030048908013500c03401034641c1c8000c05882c80c0501030b00c04c1c0180040785da00020080c010078040c10000e10303205444007c900c1502c140c0c040509082d8450310000c1c041c2e10703558003407884460b4040c2c0207441a0505c1c942251621401c0c0708490051198183e4418208106c10069000f0680101440e50040b440e104010141c400201201e6100390b9130001d217042101c50b00c0082c095645000d014555682108010000c4014400013843c055807040c051340000034000011641540e0781118604088101c0c110100d14500c030300f02c0c0c02504049494400f10420002c80314034025950b5031002c4031080305021300304880800c2108410000a030110204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 62495074 1250 62493824 62493857
    0x50c130504062402010e0d0f0f09050321040f03140d030203010b0d0b011107030309230a140303070c12030906020109020109031403040914010801050c0c10110d090303060e16 76
    0x104034a4075240c1c00003051b042c401e091404d04004007406010003043d2a003030180e11890b4800d69041031188507042c1600d000c0c2c14034000c40ea440c10006071a4095003481070b0211803070f032800004d0350000c15550030380030391107516072070001a00b00305071002076010300c0f80c080d9080c2214040d000762410f846880c06580e00f0132a0104004000e090f0140701a0b040c0312241c0c1c03140d903000340c0074480e44015502a03100c24843d03a140400188540c660301d075091050294880d881c0015503034480718041103948155140402c1c68580000038214418004024079001306100d00203080b5407101070107030882c2c0c025210030b1030007640c130402a400c4c0c0d00300f218020300259000c501400012020552012102110404c5a0806442e4068032003201c65155265a40b01c0d400301c01080403010900400390710030b030022035260074100050005596800c1c0310101c034042503100d8400c81c101091034420f94009540c021001d002d840c10034200035006107000e00442841400c210b002854400014000281000050780c0d45802c9400c42c110 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 62496324 1250 62495074 62495129
    0xc01091208030a02042c01061b0210090509040510050105010302120f0c0903030d02030108011b0f050a03111215041a010804061104080d09120b0105040902010e04050c13050406 77
    0x960340c80f16400c0c03001052103840c4040d44901528844280c8003041400283c41c85070004c16440f00081042500c2508918500368508412059040d40c51308088901d11406a40c04030241d040aa040300b840400c11060100008207052060660301d001c01031740c0d89400c01141a07214000d2400c0d410245880481c840c0c01646d450303150b11449030702081e8206844000060300310f90000040425280e00030005002030b040c288940361401880c40748031090b00b8a0400c000d0000080c0d03c02003c284880841e03403204042c02900210700003081810310310b47d55002d858184148000a5a48011568500d60650700d1401c01d0b06c40c800b4641e948201000e180b041d508011501c90b08014811540c0c1c035250074010340e94280c00806040035041d0100600008030091a00411000d0254000600a1016006080450780c2c130320050b419920142c0c1d0115001c422400140c0d112403540341e009812500d0300007001b203942400030160568030b000388110701c001c0341c0d80e10400040d2800350090049803400500f140ba2003078201103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 62497574 1250 62496324 62496331
    0x10c02060f2202011b020a0b04030b060d0b070c051c0f021005040c0b090102070906080a0b0a02030f072604080406020106080307120e1302030114090a0e0705011b05061003050c0109120803 82
    0x50b170306041454035030100d0580741103607009082c0a00c020a0a0041001010032a075118206440d20301c0103035443e4844540c00311010303000c1014072000207403543c240442400128801c07401c0b070b105000c032072041c0c0c3c20040c00349580c0300c05d10300103000c0c1d4003ca0b40c090606003d0301d4040c1c1d410070400070141d0704205c0c054204c1e80c004261181503200d03540d40081d001d021070107600020b24400001e01050342d800d0822001c400c1005080300159071040042080c440424012142c00c4604c5207000009483d40100d101c020f05c3d03414450780c4c0340708120000c00c001c1000c1940100207232030300e95000b8000307140d80707010f1541e5900135054024802c402c681c0602640070320174a01c032071460200410001c00342e0200450007080760f00a810400c140e40b144001c5c24410b050132242039800007454402006641c00f0600764a0b150503480c09441e042200c1e8180c026a449003000000c881641c0207000e4850504000c1c01c0c1c0b03040f0180301c1c4811633680c0210049002c0d90740c06080c0035030844515507200b64000545568419003644001d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 62498824 1250 62497574 62497607
    0xc07020f0d03022d0601080f1212040f0303020912010501080d0219080a0203130303050403020f0a0e1302060903070e01030203060906070906030b040609020a26060f040902060c010c02060f220201 85
    0x90404c000e090400c940c500030b0007040054400056005c112a00301141c9051106490804114000a426801441c254040c5c0c00000318600c80d0326928044020748180c400c0d00d1341c0441207074842204680107500590480b1080b00c21106402c2800a00b40c5c1c903100f082104062981d03074001900d000c5504500104035506041c8190380c17401c10820900d80209500750070590005101060500450400c030007205203801003101c03030000340e42c41c00343c0700e43e007507a4028014822010450710150031500c1340000d03215155002030a6615480d2103001003040d0070380900c020703842840b4000c0807401000000c28010700505440e42c44510860034500e05501501e48002d8007034010f551440009407a210b2807003d0040000c10390f0721a02104040d940d565151415414034454452052003849016500c1d1184404410405e0b00c02042054041c00001d6a5000320404e43d5829402e04801c03e49541e408280584248207280b1f0b070445a44449a001c080715402c00083d4002c02d003c85440310141d0b000383d400c28040e05a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 62500074 1250 62498824 62498893
    0x1050c0a03180f0c08010f090f0f030c02040515040501210b1803031501080601030e032704020403031e0203120c0f0c070b03090f03030606030a0915050c07020f0d0302 73
    0x3590f1011403c40d0b00303000c1581c029911103411300541900380160040b983c01504107002d618803d0725a54048600740c2c10007086c4641d4045a2000c01d8058840104c5071a0004c0081107503103010002a00c0500d003540300d01d4410317840c0c0000460300040c80c0880200c50800c030b0001c0d40c1900407a40e0307084030b1f4050161002c014121041c1b9410342d102d0341000110303c07942c8500c000030b41c00e0400f80d00260541e480500154141800c2c050104c918201c008190b90703882c005034048a100003001c4034103101d1350000340c10003a005400028003100b415080036082c50010038002c03284c1074120b03050f02c00b240c403070150300340410394180c026011070b1711042c10308040e085d1181c5a001080ca000f03107084404d0310340341d102d50000d40e440e48080308000d0740d803805001c0d003900c4d1201903000d1469441c001000811034440200003c4240e5561f04010050181208107050102c4e5020740810150802280203601c1c3e400c4840f0413440f6640c9044028800d0070b01d09180129564542c0080c0b00320003510107141081419007000c00880c416 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 62501324 1250 62500074 62500121
    0x304090504030c14030307080c0d020d020409050708010e010b03010603050a0e0d03060302030c010207030305091c05070b0403110f030c0915150405120304050a03062f12060301050c0a03 81
    0x909108440c091071082d00c40000314000341c58003d050007220b1100d80c01c4e640090003007002c03443e00001402c0d402513002c01da00d40e84100c6494400024001d41900110061001c1408140c811042d4002802101e06443e15842a82d0716061200c400d07609000d090501c107418001007180c2c2d80a03800c03603074100c0010000400c52188070752806103480c0b03240304c0c0360000a0700d65000f041981130038014000b55040c00c2c03020700320041c00e5440150180c4034008001e80904c510408055000021f8040c4403513665001e1b058070320b826901e100d0310045800a0009030707500344d0004141d000c3d52a00302034040060001034003804021010030108900f00304000c01070200000c02040901041c1d40351403401c0400070f04014540e480c0d40c00c2c04240070f014143c00c014071401d90f104002c02d00490f03071040320480842e43e101202145441d031746007a20f1088030310150741204d80241c0070700e4407403150340503805000b0034881402e1502140d03403540201400e807402038501d001020003c00001d00c04511030707000200104600d1400400c80308 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 62502574 1250 62501324 62501339
    0x1b020109030602270303092803080a0801090e010c0c1e080f07050c0a030203070302060f190f030e06160309020f03060403020606030712030203190e0901090209040c0302041a0c0304 79
    0x740b000c6200440050080c4d40c50020200c041e5040c000503400342c0081d810002040e0102d62081040001c00402e44003074285c00140c111440d103401c01843d4881c03035494a5510301100030b000c1403000e020361034035a0700b0048803d603104014030402404008035030750b5080982040d00ea1400c0460010b0f0440c00340203000d1101400f0594210081000799108140c46940b2480e0341000703420910100226481006083d5040000daa8001042e000790b0717404660b442e980e880d140050681c52302c07c1603040b182041e112001d40b6511030300550030700e030000e21540b41446194110304040f510b40c03204903100c082d2071000901041340c1a1080e40000200352000e042c0b00300f8185100700203071400401f00c8089006034082d40801003241418410600180354810071401007010690300651607014500040ca82d0b40d01d0381204d421464414289441a40b0003d8216541541c5424004019520a20b9503a0107542071204100500307101744216000c482c1c0c521404032900c04a40c0c0b10092a83c007603000150244024080401d160 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 62503824 1250 62502574 62502577
    0x1031503080c0c0409080409050618090109021302030405100b1201050a0c09080607020303070807200a02040606170402190305060f19020a0203031306110705060f01050301020301061b020109030602 86
    0x314003070444161038100540c038441c034283c107182d07010b03005508061840b800036000c58182c0d003e80d940c06001007207540c1c4400c00b01d10381c10f01d40071302c4881c5404d841c2d044c461307610380660160612038002e03078598180102460a0405034801a940100503a0045070f100c500415a07900036040c00c20002c010f250038600300100e9500356201941c5280802d59182c00300a8640d8220301810010818030026145502d40180043c0d103030b0000074141c50610202400003840c0a00c9075039002c0340801c840010100341d18011041544e110f09070310003240100d02d004004580140501000440d011420304200b0041e41d0715424001c080a01e580c610b00301038000c036004800180144899407050483c4080d2100500d0840010044021030b1850640961301c10040d00c08456804000c6907880604402540340e0016140303090002403010031440b514020001c518081000300c04945240180d42c90062210240d032180105402c070700c028419140800e07411311216074800b03001401c8070b80d1203005040980d103280d45c07511100c1c140e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 62505074 1250 62503824 62503829
    0x30415030203060a09090f171603050a2a02010c020d0c0b0a120606120203040507230a0503190209040302031306050a080a0c1b05120c0601030203060c0c070311010315 73
    0x801d401200b04100d80c140b22810400401752040e0511486410761140a148101103c020b06440c0c00311111042198640044070060b4200322100000ba40e0903042c01450340c2c001004d681c00089400c00d903400c40a280c60006010750f03000c02c00041401c103042e07005442050140e1001c9070030924645d21080800c8101072000d000742a07140100d0340d1003000c2c41004001014122620810381d181c8402448a00d80c0054104980b4a04800041e925151410030070301d02729130755006400c6c032880c01c50006003002c0d050000c03480000e420703220615030303c0d20303071041648a8254002984412480a14000c00351070103052040d00140a401500e280800e00b02607a00d8284040e0000700c0031920000b05404682e43c05000d035940450f8124040220305201e440090003900b49817000c51030004124045802e12806024100e003400c51074451542e1450b0541c4400d03241c1d03409100c240d1090058500151506011004070f42c4030456848c003900036507080d81d03589071001001c001c0c254101135840d520a0b40100ca4188203401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 62506324 1250 62505074 62505077
    0x20307030f021005041a03071815090e091b0604080607090303140903060105041e021b010513050c0105070f050f0a06050702030c071827030314040b06010f02030415 72
    0x25071420500500049005480c0e82c2c0c0b040110411013041001c4c0d0000301c80c03035101055081d007640c941701c40030f04840c1070341115905085140c842ca03001a80000c031165410001001ea15000403455941c140c0f981800c1e02199443d036241c1041614180c003491000d0400d0030b0f184c000b00320710f08164441c8003007454088210b5031040803981c180c1e0241b051503000150055000310041c03400340340040c10400701e41c0303801e01032146500079901c480003a110000b100c0014203401900f20340454942944082d407040080a0308600c0720194078243c0411192144409400141c0b50080014599900070b600112880d501401040c0c51100059500c50f002500c20301ca0808090390310001000201c056041900845e07101400c00350a561082041c2d0354009004940d40e0106d4410700c00c1c014060360001d0000000d4078420102442010300c9c440c0a410110075401007201c2d0341c3c000d59041000f02c0000040100d5031009480103045250000009000d540c42650031250040b183d02c181c0c1d060656400035000d8001e445142c220 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 62507574 1250 62506324 62506343
    0x4030b060604031202010f050a06030515090f0d09030c080706050f0d0906020a021c0305100303120b04091a150109050d030309080c0c0906090705031f03051218090405060c070f02030703 81
    0x46404c10364082e02703402078050102001010300d1907488a40c0c588140351000c1e00f004040c000205100c40030301000c08450182c80560b51041074186c00140003d185000464089080400210350407100262001c1a9211926034501d001440c1d8070a0700c40c2c0d0020300a40c805c450701e0343c21403000551a0300107441da10366150020110440c1c020044075401c480107134400c0c2003525080030800c005c0507410811040301e40605183e4003403d000130158000d4a01c020840f90082d0400500004014680340c0340f10b1141c641440313258154444201a80702c400c51101c030640040c0228000f44540c0c0f030080c00c0601e026210b8180000d0b06101e90b0b0744c00b046600003c82c0158940c01a00b408041030900d0100382c3d030300c140d040314101c480d4503200d1340180050002a101c10707001ca12000c0103482d00040c6a0080d005981c00004907544948840105441070b81310020804074040c10003000384540c01d141c02a14000c039806009484540c1c0c51202e00d2081d908030721300907180b1190342841400562400d100d6100954050b802ea070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 62508824 1250 62507574 62507591
    0xd15030303060e09010903080105012006040b061002011119110a0b0105030d2a02150f040f08060402130c0311040801020316050a0203091504080f010e0d1404030b06060403120201 78
    0x104000c0300c3c0106001026410b03c80381c0700000394081900f0b0b045d10000d0030401c0039201c2803000c0c001c1a00000d2207400c0284541400c0c001440701402160b03106080071601901d60308407507075049090f00c901c90040c2c03a49140600c03030341c0505441c046c411074800440346000210000c140b00320a01e00b1600719004d035185400080144a903040a112507002d1b45401e0514446420106021550313400c3c169181c400c0a2020070043e0045682c3d051141400aa1101080c1d480b1806400050480c5d40240319295402c28080340024030000e0105043d07108580003400c0b00c1001c240805074101400e035120040c0201960b03035110b80449025a00608042e2408500040c0c4130f10f4a010b2004201c00000124801c1c40300900c10880038550000407110b140500341c92403070001e0304c803500000c02c0d400303250000e680900912024504400c415803046505e162620300302c074030000c4001000d80b9010324005007a80d00c1d0130208000e00c04600c0030312031700c0c2c0c2054001d00f880307141603a40e07141c1d2080038500406200050f5184d4503034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 62510074 1250 62508824 62508839
    0xd060f050f03030904020c01110304200103090308070f03020903100b04050702030f041a120a0207030f0e010f1d10050703030b18071b02030105090d14030705040b0d1503030306 77
    0x614000e4001599008020600d20002035540d001d05950240303d2500000c200410780740039005254910280c1ca0720380d44a0515142c0210103141044c504205010140c908280c0b662003405420500c50701912142019111400c1c02c50b43d20904800b40410725400f00030b00c0d9007546003000315500e91002248006410f802c0358003000140d0b6000b81c4140300315403061184031203000120007141c085680505050408a18000b008002400b482a05140c0c000801c4204604010503400400343e2030301c03e60380c4600b0b24030701c3c24050700c1d000d0074038500c2400100910300030f11309180030b00303082407401b040a00b0710100103841100140110350040000750001c3d1340854803004050301405a500061000c884401c0240200d9a1350007020f8401000c03c810059004185411550300600400025401030f0083c422860120348180d528000c4402081c00940b0680c81c2744e403052a11400d03079010b038000c2d544491403d403600300304494a8021044103282d0550b11408255400c42c04000e240c0154441d07100840c07250f242c0ba40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 62511324 1250 62510074 62510099
    0x302100c06360f060203010902190207080606100309050d030e0d0c080702010302070303090c030b09071406070f02060c0708060f09010c02120a031e0504050c0604030b130212030d06 79
    0x342c000002811800c12042401c0e40030b0450314400c0800750036148a0741c00d042118003040702010340550310000010400440f603400070640440d0305495103140d10301145080b42e40300250f10400e01940c00c4000071446c02d240042e00049042c800d49400f09550a0b99103441d400c00e014002d09102081d07884801c0c440000c81030108480f540c0b0380b17003800e21f407100e51034032070700020300c035045009041640c0003503008101030081c2d10403581c0a800101010056807280b400326080c1c407041e40e0000703641c840e400c4001800300120180282e10390300904610708015190b031300da11810b03580c0b000407a401507062020941e1604c080200c14000c0010000400e8941061030003074139002c1000c3c01c102240e9042c4050504e1b107030780000d03000c0d0254522141040d6030382d5101404030001d12840c0b040001e512030120f030400c4000459082180200d020b141500d0903101960200141d5100b2072200030174aa00d6100042c1440031a9403010307034a03900142c44802541100103185003503070f0100c140c040c141f030707a07960061000141a01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 62512574 1250 62511324 62511341
    0x80609010602030a080c040e07030608070504021309020d06030b070c03030c0c030531030602070204060605070c03030507020301140906041a0c040512070305191401180308060a0302100c06 82
    0x4401002550500d07100035168800d0340c0821003806100008a000c8100c28000c42d030091910000c454440e0030440b8000b009082070f8455034809103c0d40e50003080302e1030580700b1070b801d00720101401d50f8020b1820700e1001c040d401100c2c40c29030345a903481c0000041005022828428070455458044008031851f000c0c0444071180048001c0140706070000c00003c0c1c000c0100c8a40001194010403040b40e04041c0142d0003420302c041090f9143c5410000003003000076000f50124a1084509001903034075440103c07003501a141c000b0b80580d0880d1401c201203401a00145181800a0004501126602d10a20700703d4001ea400c0c003c1c3d50300c10800c01091091017016111100700503100301d00d40e810491401682400303070f400380740c0c40780348108695042c815040107400000c0d03130300c170081c0c0311405900e0114001d002071018058400800d07090a0022102043c0b007051644030844207004e040040b9910110742a107001410309070802d841c8000030000d0303070b5140500c141c0349202c0c0da85d10f4181d441910f8070300103442511 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 62513824 1250 62512574 62512579
    0x50709020a122702060304060b060f0a12020f0406080705040902030411100c020306160203040801050a021e040b040303030b040b09091b0a03020f1207031709010e030a110909210a0806 80
    0x500c4080102e10318040903c010315012205241c907030312941040380040400940c5d507a441800041c449064280d6200500700a41042c4ca03071001ca032080d20301060907032003814090040c498040000740400d6002d101010b400681078039190341800e07111501c060890b80241c0302682c140403a0441e1010f02d1809625038100600946000b01e20340380e10381e000c40d1303031480054114203c40482d4214601031500c20801d440050400100030301480c2001c2104e0360080d80a0612030140e174550480390100c03580385074111070841d6a1700203254074061030341d1030440c002e02c0700b403500755403080e101d9050003036541d01c0c000507a001e003c8000142017540880307584040d64100010009004052011003000981c2e00c1c040310480160003610b4608021468410160030302c209a00000d150b6081550642501d68402012340320f800030030388482e66105c50076400c0558400c549a0010f188401c2152201c0d1542002d00686402c0b004000c2120880d0440d00c0c880421103400182801e020341c0049018885c2c96840204550841c005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 62515074 1250 62513824 62513861
    0xf1215140109020a0e040515040b27060a120b090c04060f0312020a0503040303020f0c040501150f02030f040e0a050a050103020a0e09031303030f031104140d050709020a12 75
    0x101800206060340501ca5103810b6540400c600c0015801800340b1040c0e070380300a004000500d00320070050584007a0140a80c000c03850071082400c941040c0c0090340807428074075000b8400446000c0004910140102590340200c1000c1000692015001e0266001807044519410601c1e14402091614100813030381c46c880d9042c8001086451345403120031082c1d0f0740254140303650840584041e0314207130264400608510001070008140760b40801c076104010755040070341d1800e40900c005c1000b5128203005003220004c1c00c040038003205006105407510102c490055034101400b03000d15980c00e80056114400c540d040c2001c0100940007840744035441034102c2c90812017541150041010300400c0e018891060000c40c021482010003081624108202c6440b550b040548901e030045c40384110100641c0400e0070301c020840904081020b070f600f41c600101440824034101400c01001002d00c813810746250040c1000420721003050300003802e1900e000d0300d50044a04080600c4411a500e0000d80940d0500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 62516324 1250 62515074 62515091
    0x5070306050607020f0307050913050105060102150a150b03091f091a0a0209060a050408060a0b010e060d0e0106060906110d0804061a0a03060c020f070b0307080408040f1215 76
    0xb10641070740c0d01182c05031703440c19244070348070007003803510a071904440d5000f00404104084041078038400d0b0b078540c3c800c0c3d000344556150000160780e030312500e084d0040446400b500191040d035265000d840b98070080c1d14107040761031380c503c0341d4080d59000f5903461510b0b4214003140800c0112101d841142d1503542c0408100c0034900e92500e01e40b02c0c5200e080b04160223200008034620580e25010344117032032801481d8540d13455000c0b02c00345c0242d21500c00d81c00319016460006074884914402e2020100040e190303c81d68440301020041140d0007808682140c55941080d00c514003401d12400010348860340b980090345041a102404400524800407591b074000f01c00c2a00315603000001d1a006903025001007a03500d4040c642000b52407010105130f40040801e4800000d0040315085002c943d1400c0c0c083e50b80d0600c100d00360070b44980c4140100900d801041020501c0d079480794000d80d03801401550107034200741d01e9a00c40c00792101c256000e0844c032143c0740200d4084c00039100e464424050000800c100c00034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 62517574 1250 62516324 62516329
    0x4060906090815071404080105070e01210c12060e041103161806030b0702070501080c091509040914071a030609040f052401090e0721050c060a030c02010507030605 72
    0x4000d05900d803c1020000c007148000e0700869110344014103440e03440c0d0b10b45440d0b80b002070003072000b120344130000350504802c0c25580d4001d039000300d01a07020148941040080d00000b00c007403c40c28402800f040b0b074408181c6421007480c07003500c000e0040015190310900785410080904201000d01c0d500c01c2e04040300c0d40c0c610b6511411b1000c1103c0504004003290221500d803640200b20580c0701070943c40c1000e04000021f51301044030030588800740c884a000741c490701c0c0241494014500555041041d6031230a072030505c00c42002e02290640244003040c189030695461078035144805c41e0312156403203200240000c4401003c00b4036a00101a1100d00f10b280440000e41d400340050000b6103194464284081030110600000c00100e200f55580c2100004d0381406915000d424410070400b28038001c007100b0308040110b100400c8074000030040ea03550302040700c0b0342c0c0e141e29800e034100c43c6c2b44034080040314240c5801019080c610103a49000520104400000c1c1c00c8d564001c04500c101442c01d0014012035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 62518824 1250 62517574 62517583
    0x120f0d0f180605070504032a0b0a020304050f0f03070314060601021c050d0609051303110a0803010b1c060608090f070509070f0e031618050609040b0c090904050102040609060908 78
    0x9a0080b802042540b1119020740711803086e5080a0031011410341d1740a59214080c400c1c01020101448100180390b4460700d0303481ea801000c4681340141c000700070800c032600d0b1a120410440070020190002c034070503c40041d14026084e8000c50b00c44e040c40c16251207000302400002e50094080c0081e05801c07031105803009141c65003211542c00d100c0d0100d408410301404c1ea12101c0645420b0300100428100345045401291145e0b10850010b540d20810f0700618a01017440e112040c0d2042e030a508590902080c600c164210b41094460b02e4080600d800385800d980c01644010402600e4210231418128181ca090040300301c82c42c00d25512181c0b040165490310422180d02011510f081e419800f843c42c4100c500034480c64100341d0510842c2e0f4040148080c105c2c0f000c04680c1a0500e642030a01e040800409503401101ca1a6010a054001502040c3c02800341548600034500807460440c1b2800019903076802030394245e4142c1e40c08030f0103000040d0095403a038060401030402d10301c807510300f0a03a16070700d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 62520074 1250 62518824 62518871
    0xa0f02160806040609050114090c0a060311040b0f0d060f2607030303020a051216030e0f07030f020103060e10030b0105010905130207061103040303090302010c050c0d0e0102120f0d0f 80
    0x3690705c1158105102c429800300700070064075203c42d00705050503ca0b85a85188000c03185101d4240a080000c11a0280c0300b2680039a101704500c504151419440e4400c5400255031410243d5007041400d076581940e2050201414020f031042c84018107290b482084070041740c55000d801184c0b1500070445410000705c820440360705180150b5204c02010045401e030282000811200c0c0481d418441035484000c0360001e0b10000359810040a504092810b55a0b0500100c2d42c0d21608440018004a00c1c40800c10f80154018100840c01c65620100100022000c940505047e00c180c4402d208003d00480d499004003070034a004248681000006041940b020450030300711980040c400c002c028a0b60020305110280c518040d4413403a09040c050098400c0131402c0300194644080c000a490080c82a030700c5281211000b0a07070940810000c0c0c50710b402da5556241076119031850401056076440007450f441404142035601c5a08100c0d03607106640160189514860510310b499520b0010505031010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 62521324 1250 62520074 62520083
    0x80a0c0806150310090606090e01020c1207020d030806030109080a030c02150c120a09050a030c1209030c05040c14040609030b0108011a060a0e1305010524040603020c0708030a0f0216080604 83
    0x10f0351805d92821800810035540070000710390501342840168001075010f0121480000155000d0141001d20540c552194040082d07000303020140302404203110b0703140c0b02e42c4510003030000516112280c440d00040c0e0006540c400000f03032135800f580600b82e4180040b4400382d0a000c0341c00080c0c200f1111014103400707200004080c40b42c0d810005038011045400c0002e10640040c10f4a0340d0180c981030040c880070030b510003503c1c804246031040341014455400789080741e4100c02e29100c03a034200020407010b841404540010014805103021040b81c0080c024801000715865403010545140323444941008141e11405003645081c03021030600b000050104407514044a1040c0d40c0d412148080c2d88030342c1c550758815040a0f50800422150400307900481c142c510445060041300390500d9501c02c86200c4101c85060001e00780070030002240684c01400c000310040041ea84060b4940c07154600d10381114490400291047c40c03080403075901070000404200c3e0208045400c507042c0050603684c0c44020344003c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 62522574 1250 62521324 62521331
    0xc01020f070b07020f152205090412020c04060608100e0c030411010216090209040e01020c0d1223010303080106021207030e1507050106030507080a030206010504050709080a0c0806150310 82
    0x855950440c1c140198030300901410401141c03026440d1b9603003100d0a04451418a00400d9030043d096030607800c11110000c142c01e4940c0d80719a10401c080c81d020045200354030452400b51516030f2940204c8010781219620b507021031400038802e041410304e6a01c0f1000c00d501b034901780241c0c11a08022079038026003200a01c10700c0e0101c100102e00d41000c09081400050303203107a0104100c0119001400209401c541c14401c034240c5401c00d031308034829030604103003d0b4031868051085500950540c80b035101c1c0d513000001d15503000b00c0c1d101041540300c0042c4000d558100014400c05401941070360240c0214401405004403d0380321496070b100f00200901031010740101c221841c1d032811000c84400384800e03040c03515000340f484c01c503010b000c1600040340d03030b405034043c0072803600c00000720704540f80c1d0140e00070080e0303910b08021301c4002d00010300003000304210351a0208006400700081000d4910900e07050789001c0c07814503854240351000c2d0001c1e40782242c1d80800a10782e80d0000b071a11241c10b5a48000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 62523824 1250 62522574 62522587
    0x8060402060903120a09080c010e1e030309060a020a0b090105060303070f08040b040b070309050306070c15140f07020c0907080106110f1c021603051c02100615020c01020f070b 77
    0x920340301403a0061020303400300017842500c10341d00500243c2110178090490f00c810021f40c005543c440c048071501608410b440e11110703810b088001c0310111500c8090160ba01c0c18841d400070481d15400300d60280c000d6800f0070100e400700003038080c0440e4840c05020007003040381050310000b0744074443c130030000e00402d01000140d002e20030345004560060941180c010380d5940c0d500d0394422a600a15001e42c08112200f10000d418100031030824854259503450051640040da030303807a001600f4560b081a520f6445080c43c680a0202030350f0ba02035020402e18640c54500468000e1070040e50301505801081144244000b1941241c169819a580d13400c0c0040d04822944840e840d2610640c8022003500c00c008131009100510460079011100315420380782100b4440307100101d41c2038948001040360380202044201c2d1100c5101c2041c0007201841550704d04581252003506440168120001c05940c080f4000b0900d50100b0007140325003003e0015001000c0411031031500d071200341c07142d18032020001460 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 62525074 1250 62523824 62523829
    0xe100f080c090a03030e090a060602070909050f121201080a0201020c010c02041b08100e0105060415050f03040503030a0c030b090106030e03070611090111070e0601030c0302040e131704080604020609 87
    0x1a244003000107064a034a55a890030003c046d02021580302d070044c0d040e5000308100c554103024100075143d141e002804058076107121030f80204034810f42583c041c002e09041c5042150309001041d141d280400c1d045843e201d12103140c141c0b030300043c2d2198449521101e12600182d07004245810f4800302400c00e0340d1018070500105018080181b0080e4020f03050801c5201000e81020025008078041d80369001500d4540d400301c4aa4602805015400001030104002100560114440d800032902d080c908000e42d60040b02581d4009644c200d41a803c02320070040d00030004c0c8546556502c8902d03041c041140204081032005006019060406403162010311000f00200b0840c2d8404c2e52105041007400d02e080d201003503641006000034009804400c00c980c02c0500026844103071340a0a107a9026515910010360007407a03410001010300d902031000045207203984103224480c040401e0301507041e010618100b880c0b03c0010302d040a4030740003800103000800d4009285c95000340d040c0c400341c1d641c080d00d200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 62526324 1250 62525074 62525077
    0x30605010915080a0b030a15050601110604060e1903020109020f0409030e10020102161a1609140a030c1403011103011a0904020d02031e060414060f0109081c0e100f080c 74
    0x1d80581500c0f601450f48108092050225181d211a981c20000ac0e03c40c10300440d0b0048051a25080c00e9010700d0100300860140d5008030765400d2180200c510580c40182102c22000d403001c03003a03016035943c20b40302040d42010116004280c204a400700003505640d074007d410400b8041889004120001c45400d146000758110f8a402607098500101d16a0f10314004810402c1800390454021383c2c400400e086441845c01100c2e1501c440d00d030014101e080901c41c50001c40ca544a00d50301c1100440c000001c2800100319201814440092007004030201c0141829613403280400b0b01e400e80200010040b43c001e000031616031a21050109680304000000103010b4041c040002450610000038054140c4031911081d4084450170122081a41c0300c00800003140e4818020b040ca40c003d1800294280c030b0700180440450805041090000e500c031020325140140314032041c9d0f0100b8000f041c00820715044050700d40401401c0340c0d1151064444800202024000007020051003064001b082c1707081d05040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 62527574 1250 62526324 62526341
    0x507030e010e130b13020703020c0618090a020301031406010627030209091e06090601060309050a0516050102010f0608031905070f050c010813020f06030703021e030106030605010915080a 82
    0x6140418115103108100010004080c0640c1700345005142009085100d0094518464041e00036000c04d83c030355030a0002c40e521000c02e040c4480004d41641e20740b55908200980511300d00d000042c2c9a60443c9400c0000c80c0a5012000281c0d1004004103c1158007034580d0341c10340281c5825410720091808640c5441c030303541d00001d601c480002c3c10800070b8003001138103207452040540c161040706000b107160307900c0d201c0c2554100700c95080900180101360181c1c203c02c441503c51404c80701440a40e803500ba007131954030f03a2101c04846002604105640c0d090294005082104004001403031074140c001c0d03900d104031401c0d80070015020f802c12141c00c2c00ba9068842d2150007801140d40029146813268442409041040c0030505c8da1020500001c40302c070416000d554003806401013840c003a400c02c401500002c03c0c960405408101d060551417961298100303d1600b0051540c9a50611401506946058109504000d6150410401000b030011408100000340c2800c0d0030765220368400324003401190f07 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 62528824 1250 62527574 62527579
    0x20f060c0f030d0e070f0303080103020418021003090204050105012607020708070801050f0705040305060402220f050f01050d05100b0a170c19060906120f0501080f011401060507030e010e 82
    0x201d0f0309010b00301c4a4005400080c01002a5002a904d9074010119288180400740c0020103000040c00103007404e82c0103154401040150001d403444940c009150254541c44010020fa00c55074403d003181810301811f4003400c42400c020510341240107a600c220214820f104910090b00740c04240080d0003400800c000c0c00241e000d4510040c4c03500103907401b80c001960f03414144aa42030024240510400540341500c0e40f0202511841d00c03560204510344032421280070001034008016079a014261150006031105040041003519001c02d60003540c41c8164400d078044c10b2203604940011300c001c6410304190701e01d4200003c210001e03c02055000c11540c12007244054204100008a82c0016a200d546101116191081941e004010201c14540d101e0000403e55010044c0045070140c2c9800b00380c0c0c00c68401c00030b00c140410313500b0b500340c1300300303a220412540100842141c079030820f025003400760000000f295695403618000400030320a000000e001c000d140d030600080d0760f119921250808000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 62530074 1250 62528824 62528827
    0x1b0f0c0b0c060f01120807020117090721020a030b07110105010306050f090714040207020d08070602030106110328050c0d030b0f01020105150103090203030d1a01080112020f060c0f03 80
    0x440c001800d00c0ea010072035001c01d5110702c2c000030340c01c0c0d0424500203060b10340303480746032141258035650907019800001c0100e051000d208003d000780c42d4030154540c4500d480c0780040210354070300340c60144280040342560828120051090000d40ca40f008010200c03980071038008419540d0300b004694803d60440c004000354280320002040c404d0940259001c2d0302e21400b1300406444000703480765600343c80c0c40340c10514640c96140c03895a143c103502400c01280003418031801018155140da0b140d62040400b00c6601780c2c040010320600740d006030141c51f84000765008614001019207407008501242911a280d15140840381054511420984441860610480d001402000c1c0302030b01800d01c40c0030580c060080d00c004440a584140101405030f410301c9501e26044500340011000381c10001000d0703070140710030003d465413602a40708074207280011102c41403079030403810001418540e0680c8403c0700120301c0911980540d9407182c54042144045030001d40d030314103c8074542c0c03c7c0480c100c1045c143d07000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 62531324 1250 62530074 62530079
    0x909101b0e01080601020a11010c0804090507030606080c0712030902090f1501030908040e0c07200108060909190302190305190206090d0c0804050d030309060b010f1b0f0c 75
    0x104000140354a80c8980301d440c84480040c00448142c070003110b10f14016409082010003144407004007003501c1006150000c0340c0c40c41500d03044141c3e0303c40c0e44086000c5a40303008128005034148070f0880501054070349a0810300b01041c07003500c540514540a001544184200469640a07500c10050250302134500d400901c2e05141a145040303007111051100b45a0700d03c40b40d107a40c400d00c502d00c41d039584804040d042c1400c1c0780d440340c5401c074000c000a129541c1044690080340c4501c240100700d8001107001e40c0515403070750005105500240c409405110701030b00b40000001c001c00c4c0e207400003c0c2000345668003170142c10100e14090b0030885001942c45007500c641c050650200050000c4d50900c8940100030041e49401c82e40c0724401c40d480041600145040039006101d0000c0f82141070207001c03402d00f09034543c4006022020880b500f100031941e01c19a0404002e4603000d04468000300f400c15403140210034401030301c0381855907007500700c80d19a075441c2c0b0b0810000b5124448030541000f451429242c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 62532574 1250 62531324 62531351
    0x304170313120209010b1c050c070b0f010f080a02130504021809011410080c09070519050a031d03180307030f030309020306130c0312120c02010c1814090910 69
    0x1c00b80304141d015107180f8002040c903a2400d000c907198050102d0800d03402e090f4140c41e02009000c017410708407081208020342000b107800390356500c2c000d00840b01c1c80001c03545000c0e4500001c220961000456401c15880040035a036605e0b400c500104800e14041b0b10381c0e88510001e0203105002c400c0c1803400b0700a40c144101c00d24150303c1a51205403055050b000d540301d0382041c00c15814a44106146a405a02190f40e2801c0135124940c2062041c2007050078803a03841d503402004003030070400e400042c10228005091903414061030190007010899036200400900d1025143c3c41550703210313810354581da04810390341e4504210550003103401090080003c886032400a010b8403c880703081c0e2003407040d940410350721802d4840d450091513005103004500c514564818040d00301e12144907080c021402c100c2090104280143c941100c5550f0002905600c0c41c90050002c4403005506a0214200c01b0300b800100240c184291175440222045a09a61001091454080328486540d0b101703003003a10300203104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 62533824 1250 62532574 62532599
    0xb120a060c1b020306310303050402011b11040203060a1205010506010306051f030504030c2013060501051602120d180504020f03070305090f0a0c0e07020a050304170313 74
    0x6580d90741c0e8242071218404208000b460080b10295154002030301091800480c64a400544481408070108045910140d43c07180700b40b444040d40429150700400045607484113605000003120301e80c0480050340d0b9210b0800316054940028010380c0d0000100d5400e90700c409035040100384200c1200034030000c618003070380a00026122940401c1c18004085858503214852401216109001d51503022600c1c1c0d080300a400003a00c141d0901c0381101404c408279509400c00c108080d22607487d0700766001c1c0d110070310200c0124000206100c83c034201040c40070fa07038481c0c00c4810740d440c800e0f503401d00403505000044080b4907c54103085c4602c0342c42c04d60010150050f480c40c44401080b445500030710340c2c650511082e446040d070b0341d2248000800c0004c49041c02a480141c01002041c202c0d54140400d41540d80382080b1641c003510b40e81e000900c00c00005da0b080406139840019480546408103290b5174440d0703603000328040e41800b0131501c0d0704d40900305c40800684600751840307000c00d520240d07219040c0004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 62535074 1250 62533824 62533841
    0xf132402091014120a14360c010503090708031204110d030c06020706060b0f1209070e160302250212010504080d0e0a0b090304260706030b120a06 64
    0x2c0d00301140308603800e030040c0710540359000d2908419140440d10a0141c4a984009083c60001da0381d0360050071203107010006291049051503010300e000c04442c9200e18210a50486510b145165103081c00c241c0f400108440c1c070740920a081c05070701d0b91a25560720341481000e4011030300a220110755000d03000201c0600318055070040380088000781918085c42001603214101401141c8104104c50010b40b01d9401407440b14010741c130009080b9240c4c44d04c495035038000f540b0384060348000b043e620004001c0c403100980004801d001005041d103018402103004c8070040102d0741e55141d0303404070464107020ba0100e035001b0805106290681d145121307100248840c00c20164000c455600c94240c03000014420540140c0e0400f241d1414048c4100038413001d804510070500c01402008480740005001c03d5007603004100300009035403160300b000c000d1816a901400c0340005003400c003108a000c0e44020072850199441d624022403620781d2600402c1e2000803004105400e44620099982840686d80c04401c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 62536324 1250 62535074 62535079
    0x10605100305010e1302040b090907050109050d050606061c11070308010603140c0903030408070306020c0c01210f09020d1203050711070509040f0804030605040c06080f13240209 78
    0x48110342103004070100c800c02d00801c0000f900c0040440d400045415154510070b20050021414100d5500402c12080081d140c49040e9840000c003445290780225400010704429610612500c0854540a03910440503040d14001d070360014600d02c02d09800d601c030b0001d001c00c88400b070019859005504005a20203101078002800d243c001040d0a8402c0c0500d0f000300c0300d010352109458890030b80c1ca400030b0744610b6501c1c1d4944001c000c0000e040005000071070096004240040e00c1d2020320075102d09003036064041c9810084800980310207230090095201c550b4443c070b640029228004580c81c0010a030000b0f002c0d62200244800804205030804220f000b4405641c0034030568841c69020f84a020b81400b07045881e0300310f58803d2109090088802d43d0080c0203418201040226850303441342036005400a50358562a901000144090300c181c070002841545041002454814503404800c0009021030a90990900b0204240a00c001c1d40300880b104c902c80b00e85040721208036610095000f54100f90 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 62537574 1250 62536324 62536339
    0xb0c0706110c06182515050906040b0f0904050a090c051504050402030903120705070c06020309010c0209091e0304030605010b12071119060c0305180309060a170405010605 75
    0x2800030110000381c40c207204010300202466150360030500e608804c6a240107031240b01d40c043d00c11342026010500100604030b004101100c1c0c2c00c2160b441d01c1c43c090342880805000c800c000a94090300e60104850885080e0341d40c3d0340d00e405900c94211014400c826609602c90b007090700b803103c100340540c0070036010b522500c030a4840d240c0d11001c0c419281100a0743d45414481070204125504041d00190f521075001002e0700d20300140007151070740807001901c0e2400040d102080802c00c20100403070b01c0c00a0308140c0029800e1295120000b071000031a010028011a10301d000300325404010020302c200b607541c47c070b01d002c008560100c1499690701309100507506241004000903d0808540880d1005d00060300ca69005030345100003602c00301d940b19030f50036580c441c603908000410300c412690444103120341d074041a04103400700b005095401c0603151348861301c110504002181000811140d04a00c10b503030054803900c1020080d10408100400d4076040d9a1110421042040c194482815500100d0340d64 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 62538824 1250 62537574 62537591
    0x40b07030f09031b02040f06080304050109060809100c0e100810050405010e040b040f0503031609080d020a03140706050c0307031b05030a090c05030d0305090105090a08030109050402010302070b0c0706 88
    0x40e4252160700b00090b010402d105040120943c2119043d404180080e1000c1903216000c0181001c9a04c654003c078690f2708081010b000b01d60303125020742d000703210300e10740300b60035081c1621825101c5013070054020000e65206a0060701c01c2c003d6035500d142c090014607011018130300c401e003e070072003108555a02c4210300b1700f0382c0424245040d00c60396050303401d5410541d40381d54031680c44d8803003080e001d4007c0c4d564401c1c002071400001c1d403c02c0150710400c00c130750340d1000b401c1c00702c04054040079180c0c0080380a9040700300b0400000e40d000800c00103450b0986001007441d19500c110303050910404002502160600d0204891240160002e50060886030740400c6021103880546c2c1c40e80f8604200480018000c0001c5000030b2500d411102c025400b0b50324202c00603907241c0000b80b40c60701011502c004030b5141c2c010001600b03800e1049c07903404144900588882d01032640d8402c4140f0050158144180c0d0318000304056920a90641d404217500c00010072071820411b42500058000b200102c50503030034540070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 62540074 1250 62538824 62538851
    0xc02010603030e041107020d030e180108061b1303030203090310060b07060c1e26010f06050c0307061508010506010512060d02031c0f091e050d050c0306040b0703 71
    0x8000c101c0707030580d0f42c0036814a49801000f0240000d11303055142c80605201c6580540c0d078250b4040111486501c0ea40300301020382c2c2c1405881048600307940614134006004001c20400031481540c0b0003603000000454048440c0940d066001d03480c442c0d480d51100c00004010960008010200101d0807001c40306040d11840758202602c4c00ca003c0c00e00002e00601c41007000811603008070500b1852402c1c101c42d010700f0f141507050b21550058805001469820150134080e070190070a440d459800e0404180560401022a41c1e000c01837246d501000400a00621020000c2c8140c500701e6501c82c00920101c0946007041c140d0340300b9402543c403d1351800003c01d50383e6014004449484800030803940455035413508001d28891800020381c0c140c05101222503402014200110628000e51656264a030f04c000d80203212005940180d0541410020b1101003460754000e240201c03002143d00f0042d9400701c1c50040e062100300e0700b0607505482520140300c1000032510009120f1055a50f0411084042c2c0f5407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 62541324 1250 62540074 62540081
    0x12071e030213060f1701091e020909120313031e02070807060e01020a140c0a09060807050319020f01021f060e070c0b0606030a02070503040803071a150609011e120c0201 74
    0x3e072440452006400c0025081c000d184403106a0b11a00001d0380c801f064540ca1103540d064000705401110500601046160003011035400619a00040c1704010351143d0001944c03002510030118500c86540ca02d0415214000c80304004200d02c1481c0c43c3c5850f00300003e90790341c806014101c0380303002c2d03a03402088291103020003019070ba07016401002101001c0d22000d02c482d449450244903401410701444403901c0d0600500018400c2407400a40f042c43d2244030750901a6035009144030303400c00140700c011203901c035025203029a0100c0d405a0311892150050740361070652070401042104c907200300490520305038018400c68880984450150352910011103000d05204002002c8000390008516a0705000c00030b1903011015038801807405240e901c1d0903165804c1a807010705543e00003d5100e04100c14020a44401000780c8100b01103410199400405000f090082a00628002c03412400c0d40c0c1c031a544800c1704d4240e001030a0080306450800030101400c1c08400c148407820303c408000302d14414030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 62542574 1250 62541324 62541329
    0xc100807020303060d150c0f1101060303080141030106060503091005100902070f051009021522031209080303190f112a01050403050912071e03021306 66
    0x40c042d52455481c50104641000ca0b2882611000c0301c800601c040d0780b031944150710009400e82c40340c1140c41c10782c000042065201000a035140d03410705008100298008019a064448108981d08205800032030300305a1a0f824440180510000074212a2840190b2019480e20001e40080c0b04698548206840702d20081e03c0040c51903101d00b5004e0140b080b590f1019400c880500406240b040d07440e6403c9060703800484055030416041040c21080040070441d4404600c101603007403182e11881c1d000a507000064010361213440c0c0c000900c40829465201030260058950041e014085489092130503507142c68051420110304118030106070740400000752880f5400188100514100c0c882100010b0001519001420b07a100e02412441180340405404003d078005540800070391441036540a0030109500c80c3c105902d82003d03c0b0100380e1142c200c03080888140c4148680b422140c6025141c400903a220ba0040c102001070000d8201ea01c00707a51048030300890b000d01024010320070400c121111407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 62543824 1250 62542574 62542577
    0x50408030c03100f0b1305090903070803071b1202010c030902130b1f02060f1806060402030718060504060e190608040c0b0d0605100c120e03070f03050c100807 70
    0x620026807200e4070310004542c40341c3c561071126207956030b50300424003900f00b9800002642a000c905503285d0710307514039020018841110054041d042082e280b6480744581c50000d0480340d00040011011170203210074003801c0b60500c1543c0d08801840c288506c00b840002c1040c00154240562650385601c00e0140000b11500140500c510720030b46c801400090124030503581d040b1342ea014104c60300400c6d406942d00c03c40002d8016150500e0030009000e01c407040104940410b03541d18004000e030030340000311594002d40c140c81c010f03600e80307440b0030a031011800b00e030481002130364461000c07440c9c0d0340c0007001d40101d41c00c0e5107a04c032461075030f00200002d20300c950988000c4460980810040c2a1041840a81050183c031b80310100d25164804207640703134843c19113103080549500082240e814103861602d1101040c1c42d00c080d100640d075031804810342907500200104020000206a9581c0c1070000900808191813602c840d0307662460b0094035032141e820350074450b807802d405440005003c0c02485125040780e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 62545074 1250 62543824 62543827
    0x3060109090c0909050a0603050d0203030c03010b09150706060303090b09060d050c090310140a110909040311030d09110f0307060f0306170f0d1e03090206070c0b0c060901050408 78
    0x14100e001d0020030646040008211a6240000e4050082d00c2405d020720540f0340c0c08610300d41181052880c02800000d04d10031035004104200c0035191010550341505c54451800340d803440d401002980e92212195048070a002c0090032008000382644001c5c00c6910a0b02c5e41c2c41c0380d55541d4082000d03401040e03019504024104014283e01c0d038240e020361350222514001c40d082021a030f02291510b28440f18004040340d07500380c01c4015082010603a07030b01c160303d52170070310900305090a5540365001d9190307c0ca0280c030b240400701d01050301941341307000c5114540084907100e4200e0490b090240940880640305510001040181402c1411019660540250081000624140044514103101c5001c07204141e079030300d000b00340e82d0601d009144100040740e00420040054841c5541031480482c44c00c020300c10724412003214000c01c006608200785a43c00c0001d010041c0d0300102c0c00301c0c414614000e058001c000000728200e100381000c0d01c20b1010090840f1007954030110f4150880c4e40564010301050740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 62546324 1250 62545074 62545079
    0x807030b091002130810090c23040c0203120109020f030610050418020702040c0c0b06150c07080601080f0a02010c0f050f070305062e05010302280c06060602010203060109 75
    0xd2008150004001c40c1140c103040c1140300711100f2a0060780380001004001c040400c00404200845c5164001104040000411503a00c2c544417240300d10900c102c284a15a41c104440112843c03003400100c0604103008403840040029201d038440d071100b2810003c000004145514075100f034505e264030051806181d44c50b10802c001590a26421040410404001c041281d401c000301e00c19031081c01030b01c056200c0c00c0034030400058a810741e13094410086480200400306034115000b41d0000010340d01c0440741200080c2d403103040d1041c8141c80314a80300c1c2c0c210024011600188242c100d4540d4000e8461098117560304a45901c501500680007580c130a1344000880c501149507041144503070102c8009954880794282408242d500559041d0090303000c1150b54201207a452003240070000200c65040c1800446014000035070040d1410183d000c00d010400c6402002410b00f450000088060441c0090b50018900319290400715691070802c030300000d0741401402a00d00900c0c0503100c2400860 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 62547574 1250 62546324 62546333
    0x7050d060b121b0906330702030a0c080d0503010803090103020a0519080a110a0c063204020316180b0a12110a050f0105030406050405010b0a06170105010504080703 72
    0x718005800342d000c0c141e10030441803280c040011109501d0100884004402610100104444010240c5004600352100b070395566144500e01070403951244064a2000c014805000c418050028000c5d05031061500140600810120302411520341c00c0c1105c60f841c40e404021100c50200303204410060307000380a01c0c5590b60081e0054607a58100780745c181c0c2000640130101c40201c040212150109007a002030100c51407542c0030781036144500d500e51901d05062148001c22200e825440039290603a20000140c80d2005140800c17906260006110b0060544540c3c1c00011481035074224030030f04c610039950140c107405e001050b00f00e803402c24401c05a2042207540001070900c411140342e101e4503811001c0384921507808041d540c45e0090608001a119840c00d209000980303810036841142c1030b100c00d00355130f03a001d012264404d0748a0b00104440c1c480740ba0203030141007055041a840300860300c011850725840b10302e80304003500d0700105060590365207005542d00d2040307001b61f030144e400410081c000315 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 62548824 1250 62547574 62547581
    0x6090a0c0503071115010b0a080603010c0f0c02060d0c021f0b09040210021c050703020c04020c03040303120605091e0601030b03061f0b0f04030c0603110702090402120d021e07050d06 80
    0x1c426900c241c5e011400352220841146009803c0000c44103000310703601da1070960000303c0b554050350540080200c2d04100700301511801d007103140281003100e01d8240380115181c1c4000c0d19091800351400307010300b90600001a494226910010100015440b10320384a000103028040ba15030340540100340d19121071b024000701c660070340c410074298841d08880300b940342640801482d1504039a40c459454150500c1c2c0242841d40b42e000041c4228018400c031000c224000c0105c5040300e0703260401aa60301c0070004060042d106550000754040500010402840c0f2103c418190741c22100c011241e0b9503480398015411280c0d0400d805406500c4400042c05007540c001100e818201013008030030f06503a984803a10b00c964400880f81c6c00c019008102001040481e025603c05000103040a1203c0941e4044921050203040b030083c1c072540c40a0041029520788104d94002d008075207043d503c03107018060019660350a8071408902d803100e141c1e0100804000428071109450303006042100c003c4c440d07260700b40503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 62550074 1250 62548824 62548847
    0xc0304080705160f05030c040509030d0c091206050106110d08040201050307090e0c09010305090609030d1a04140105030c040605010509090411120a03030c0f05160606051806090a0c050307 82
    0x643c400c440c00c450a00c0190040e850050000a80020465050034181414040e0321101c0318021740c100f0b0140034803c031012041d215a10404080010039003000c03201212055242d0344403030b004090025200301131040a40290741a6140c1e62180d0a82040350b40440e076940b1b0420003075400007004103000c41c00540c403c3c5c0007940c02c1229803815811890700c4a1a06200c007105481c0850300741d200240100103960540669503101031400040c040038a030450380603440c1d1252201c2050f505a070344a04e034138ac881c5c00b100010202c00c0043c001700946424400c8004040f0030078010780f4400e01c03609422025a2610f8002d00090701d4043c4d55240c02c2000d25400d22603508800b40003120404c0d00d03c40440090303200d89802c910036800c540c00a000d040580c0c24068225403006c24402c00b04011500081741907504801100c141d11280025a03080c1c1116040c48402001250801688414511382101282d5123403008a800344104031941000350702c480246200700c0b40f6240c10800414800e10000e002d05000300501881c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 62551324 1250 62550074 62550083
    0x6070e13050c0d15090c170f091501080105040212010203070504051306030206070807292e080304030201030b0301020304030c14010207170d1b080c0901020a08161a0c03040807 77
    0x500208010034016104c0080c0203580351034846004029664490040c2000281c0b542012a15068800d4901e0600503006005820317070052079000c544141d1081046200801400722100c0f0696114a040c5010301001d480c140c2c41000803100c86002a0310620880e401a81541c80d07246c41c0c10b2404090010410b142c1550b018511f0340e444000000d62160f138000d0003214890300625554011601d40a01d0b00001c00c0011007220403142080740015144802154001c2d043c07000190000b0100119580242c0d000c401540300010f0400e00024136030000009801a240700f40c07070510152902c2403d240c00c03030000b224007400003404a4122400f103172003d40c1c05100039080f5400035141c0000d0b1b46541494507403c0030101c0d00c0b954001024007020308030388555030080d0460220580940000c4c0c20081078600c0c064514034200d640081d104c52540e0003000345c800c2c000c0e40425001d485100814410b115461121000c0c0c40348a00304100b1303060346a1410041d8400c80300c24141500b591202d4840341015040a0000c64 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 62552574 1250 62551324 62551327
    0x1b0c14030d020706050a0f03020c030403061509020309120d020c1f0e010203060a090b1f1206050f09060103020306011803050304080606030706020d050d02070f0507030507080123060316090e06070e13050c 89
    0x1200044140001e00145000b0a0003061500c5033f060360502c0e215a591003000820310600c01c0c4088841c003c078000045074146030019440c5e501c0c4401840080c400c4010900c0a44180b40199500440c241480c0f0031000364028200500c00c1040c0c821400d03440308039401a8800e01d20201444224910740c00343d004500041c000304961081414140340210501017030802040070003040c0c1810050500501010740710541e03014070b0b454a80c1e00030420300a8054038850505402000007145a449a032075800140b442e0b90b9003008543e90790130219202e5116000302e0925000300c41c0000c24504001601400301c410700d5005103407100d03034168216201e8101c120b12000c0302c1e80800c810004640d079041c01c00c120318021000381c101c480c42c501e0005d1412503982c1c4240c0e1a03905045002d0128150500780c0d1003204d8954054000c281c3e00d620000307003403a481d0201c80d250f403100800007240c803030f10355800424280480c0044400640300d12105440d074000404800d503110401d0490314a24250070f410042e0407191200d40345 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 62553824 1250 62552574 62552587
    0x105090304121b0b03071e0f0f03050408090301091a010603060302010c12030f0501090b040c0e0f0f0307091407030c050708071101030905010c0309030e0603040b071b0c14030d020706050a0f0302 85
    0x81caa51760043da51800003c02104a400f0800c0c40600207c2510040b400c014144404180011f0001a5140c0406003455035400009040c000210201c50201c88018002c210781090303458480b00340b54104403840c02512103840003217407a500a21500054a070161648a2145101c0d5106280c492400f05450300701030301d580e2504048002400b52501a002d915000314844410400780412101221140400c000d04440308201070740342d5010035042e030075042d25030410b41041c103c003081c5003e5080d407042124074500b12030503101c00e402c145418001d240654003884030b8061110210f4244c040d159000d40403080070000c10300050510700f4004d521500605011401c689562502d07030031508050314120100791603420160030150b11200405080c1011260b01e030450030705440312401210b0052006040c8000307143c0f00100b070f00c0820341310041aa0300502e0300c1041d80d190005103449400d0b400c40d250203072044004d00e42c000c600200700ca00948415039a0542805101d5600b12100c40d46904003600b0316a080080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 62555074 1250 62553824 62553839
    0xa060807030c0302030d0e0a0611150403030203040b011401120207300e061602040207031b080409050f040f11060408240c0a0804300e030105090304121b 67
    0xc0000660103800042515469070050600f40f0507910845070820525402c0307046c00760b0755a50300005031205c500d040101101e0211144e4680310360f0b40c80d00b102c1c0c481604c040004041d03042d001988524410311182080783da0310301c004030f180314040c6031841c0450720303408603420803a04503805001e1070390007040100c259000c60707a500000c2042406a555142d88092601101145c12100b4444411400d982d42d03841c0005400040030a01c0c68000000d10884d0002011700070300d8071400341d08804d450840c400d49240c1c455481e021115a210f4425044030710b040100150301b034030a00314400c0c0310300d41061840000e60714a41c0d41080703480e020345d84254018130501c40030801080800500c00401d40c2041701e0302844100d050740011001000f00702c458414410440d0710901c55000f001c182d000390303200580d003c0002c40803650718900c0405990190b017103140700c002d006030b059201c0001e251602058000300078980340c07405541c1c0ca030f00c582d0150f000003101c20240c0000042d4841049000b00c104c0042d20441140c44190 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 62556324 1250 62555074 62555083
    0x5030c1e03042003070803030604050705040515040302011706010503190f0c02010203010e060306010b0a08100317090f0a0f0302150c0610030b0f0f1501110d090e0117060f0a0608 78
    0x2030943d4078000c1d058000428210355911031003880310490080041c50711b000348440d500d200c02880710703000315100c60200d5442401441500d002e4180105180040101050070340e030150440d00c002d034005a10720b00d001c40406480c0601d9401101c042c0c3d03485246079651058295250405409500140e41d02c0c4038603064542548510041201c00b5400940d49500d003400c131071004007001c1d0120303120b60001401001141082d0044485001b090304200000340d9a940741d501e080100340e40054000803400c01d01c1c645c3c001c249001080036010031540c65030404e5041007803003102d540c04e01680d00401c40209090000d468514138050f2003202200c0070516003440c1c0c1000d40d0404c1c0043e203200c888418510018020000313801b801c1c41d4003250b8550360a0340b5107170140025400290207044008a81c9584103002002c0e4418080010951461401c9840c803400040c002011310225100354129445041d0006c1007a00e04180354004a2880700b008042c551908140c5400700f10000d402c0180c05540c40000160030b620902 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 62557574 1250 62556324 62556331
    0xc0f060324060c120306080328030608070603020702030109021c0209010e070504060e01020307061505120109080304020613080703060c080f060306041509150b0411040605030c1e03 79
    0x9401080740200c40c03103256890003410910460400000700140031035640003100781520f641003110302015042050003540140001d40040c1120302000a84107140269016210144003040c2c298001f10039074080200c048038800c1c010540c0f190011101000b01ea44039401400400f400100000b914034036541c00201845003451a0203900210098900c0662030608031650041c81c4c5800811903c1c9808000140f8522850107044288002c0802075100c0c0c0e4401c00541d130348180d0141c0c0821900b4094005000004968031510f44105624007078090030300018010044840d0740050170901f03640b1203500704801c2d900000c4480178200c441420001d010002086410000c42c06200005141d08010800910600e0000c00b445d2050340c800c020b000068500181143d030207504009003240d403026441c1d0f014082c0280c42c030050500b82c0d044500000c0d0300c0c1207601a0240c42d0701140c0402c010640030703070306c1196030045d489000d004c150140002885581044010100c9508200e1400100f02d401c14500e5a2600242c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 62558824 1250 62557574 62557577
    0xc210124050f0607030806040f0e030307090e0c0a1e0201110a030c02010b060405100305070509030304061d0301060f1406210f0c030903040308070804090518060c030c0a03090c0f06 79
    0xe641046035003012156030b80c801c101601d03003920384085074401400b030503005030040e4000c96407541d00350011601540320130080e608240c1074940e01d04254000424091050182039084007001c00840c10700200001140d506480f1503c8168000044410720901c448112800c40b0a554a41901303400700c1d00300030014045858a070b200000c2a440780c0703200a0840d46031039805401140708002c140300581d640c06081e9510170356480e0100d00c0390751700b5000700c5c2c46005040110742c06100109003c1489904012a07407505010b40500c145030701c4502c0105401d0740c41d54032940c911404060002d10007601c1c400c400d009034a1001d0000d034541040348910301c820340036280c440c24048440c60103002030901030081c4e4a402604000001d410b500300350544c2512032080384001001800300042d55400c1042480c113035001442205001c200b13514000040c880c500b070140e91107407124041c03800042c0100507820300b038a0050340c0c180710841c01e10101d030710207400400741c2000507100d4100c02a400200043c1c580741e02d40140109 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 62560074 1250 62558824 62558891
    0xf090507080d020c040911040e070b030c0c150f220f06050105310f060f090e06090105040308070c240c0e0f0904020108040c0f0303021c020c2101 64
    0x2c0781c400a081c01c43d0500101c1c4905d0400481c0d0000c40c1c882541c2c403030b03001d0003243c0009042c1c4515034843c1ca4041e4a038003098440f4004003c0120041b140805084c42c29005020f4032030039840c40788038841c4200d00b10380341038100340107201140102e4030105103200790900b1511821480959500c44070280e0210000840f8056100d400510440c20550504e02200c080c4203c1c24103a07015041044000d6084d058828030410303501c06140001602a0f0401c1c7d0003002020188529244c40340c054002411f482c09900c031070742c0305071804104034000c14030a4501c540d8140c0e40f18902e030740b61503a044401014090003901d048101054050161140b02906065651300c040d00081d43c806460018125191240c00c0e2482500381e22010000b81d2215140359500c00c2e424070740345445c1d58403850804600385854000c4a0341001315140841090b40000300c101d05420030601d145001c0341550070403640c458100001d560420303041c08480000c00704940000300b1002c0b403030002250b03010094000031300c0c01c0740b442d8010145090 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 62561324 1250 62560074 62560093
    0xa170607030c02030a080a020d061a09091b09211005010e0901090803061203040e0c28020d0c0201050903151b09010207030f060b100810170c040f09050708 68
    0x415100e200e000c52020700286003441d1170700d04003400c0680024000c5a002d40c00040340340e8415499400702001d4107120003810b102c81c0b80020b4032143d40c0c00c034421490003100100d000c40c0184500134580c05a4a01404d4400d00e040c40d03180c184140318026603d2842c12104140302e03000391030428032407144203106000d4005032962400d800d9040c9c43d0b60180c400911649016800030207e04d1000841e90700c0103080e540d04864800950b11b40e8914400c560281342c21042c074506000114480c130006003101c45490500b02c1d4150414280d0070081290603500300056802954400071481c01100c404d500f141c014140181842200000b090800c4c40070460391007800ba101082180c40071001d040c00d192010181682418007443e0b5001035034928850001070140c03070300b442602d420040c640d0080c504e1450060604c0303140e640814406800960165070798004072031070400c0490000d4040222455245004000780f145040c4242400010070f8050040c0300c6c01a1903d4002000c10401c105c803800400e40d1038020040440f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 62562574 1250 62561324 62561327
    0x3170c010605060906160807020d140c040c090311010e030d032c0a23011104050102010e06060307050d02030309060c060f0f070c0b0a02160302070828110a170607 71
    0x20a690440d511030f100034400c03801d00b9113841e800d0350b41c0c1109217440500d24030124108000c00d805031000080d0701c01510720320307402003060300724000300001c01c140121403011150303a081005803480d04003a00c0000d0420740e81080490781c0401d144128803010f05080031002181300200781020550000c1b10046620384c146419020b107441042550404001101201540450403403900c0706c2008401a02ca00440ca590560001802d005203411103c02d10082106048034038200d502d903049441207a0142d443c01c200700e0101000032882510904000b4064545107051104101201801c950240d030103200c2801207030101d840d440000c042c4400b41c1001091545001c103280304110000400c0d500c4140040014048243d800c40c038400c21665200000c40d4596903031102c00c80003401107021090364034040e40b103e00e050503000f08861095440e540c050718001101258081030b410005401040300844d03100321040899648515520800070042c8a03150311651500304401d90320380116030500355000b0354284191a07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 62563824 1250 62562574 62562581
    0x1506080603070f03051c0512150f0607051507030f02070b0a1b050712050c01050f07230403020d020103060e0c031e0f0402041d0312010f0e010b0409020a020703170c01 73
    0x3c102100340b001d507450843d40c44517115149001850710b45e105d00c08500c1c80440c014405e4034640c121000b1440c50070318000d2846c1c10b0a820325584070b401940d1202c9891158140316044800b540e8100008003140800c42c2441c82c9034400041401c82019550542a809442a400200031083c0506201c03c0507050488504044406410440b001d01a90145c5444240e8012007070b40c0042e0781000481105100380001950144625034080b001d9501e44804c2008080c0d0f072610440c0510710300c0ea101c050a10340080c03100d11000b028081d0200003541031004100610b0b24141c461401441890041403e9980b100f000701c24020a50f40c146004001004000e50111004244411024400b08021060415019107c83c809004d44041c0c081e5031a110200d0b00c0300f82510901c2d00c00110b1108890340d83d841007181080180e400e00a105548008802c00120200030b00c01c218103031080080480d1170245010b070050001e5010790344c5030096001b006000004a00d50400010000044500880d503400040c0c000703a00f103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 62565074 1250 62563824 62563829
    0x305030609010803070c12020a1a0a0f020d0c02060c0102040e0c0d0b04090b010504051f060f0e0a030819020115060c06051308040504090501090203010c02010b0328080a03150608060307 81
    0xf2070740305000603004209409110b404a0b0f403003480d0300030b616040707001081000b0f04c2030b04840c0301038482000000c0c91401100040024124a030b58203650300260040482e00c40201c40c58030000100c0031510701015103800d100030040104203400040c942030340d481c0e000c4800349088582045403a07012819005a84042c003480c014240111020055400c0c503503075440c41120103004c0c003801703907a0b10000114100b41900f083c0980c100d4a004c00c80b085e139510360000782003440e1001c0080000d020380680d0003090910800c803000340c0754015041814400c0c40e40c074080d000d0031100e0000e002c6640311819020661010700d807120207051559101c1c00c4843e82401c0030001d4400203403817010320302100c1491802061165080c0c9003610f000303c2d000b184442450500d2805002500b5002e035040d4038081700b440072075805620845512005405541d0400c04050303016407030700c9a1303224900100d803030f4848207000645000c0042c1422080390500140850052039203154032000d9411004c040f5014100340110361a081004100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 62566324 1250 62565074 62565089
    0x30180f0b010f17101e0f0209130506090f060303070b0f06041b0903060c02101401030b1303050a0f0318050601080624090c0912010621020f010f09080a030503060901 72
    0x2040c0d01001c003115513945070704007110113042c1d94243c40e164840000245842146080c40e09200d41505103060000951042d0156403040000c4031840d152450136000740c600c10400240328260300c1c1c0d151000030042c0d24000740106e61600040100c0c40015540c09900c030b00034444078a06409603d00b0b02c0a02c01104c0d40e91000340c02c0103030750555082ea107583c400c40d86d10503a9807000c3c0c045100000b1071030680c5400c010082021519090180c0c1000144400e541c0030304a034003641c50842241c0360041e44180020490f180030300015002c2096060181c0216074070820a06c3e01d10780082d0b40c2c015410203840000407080b0440b41e51704604010841102c0c100708094000c00740c450412045030080a041c1100012140d201c3c0c000c40b1f44100003014100c1c00c90039103400d200c001e0001c10300c1155032400030f402400e20740228850302040301149200007000140d00c200c00703607024082022440003d00103559010703d110343d040420152200200f05000d060004200007442912060703101e051003000c110420390140c01c1040d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 62567574 1250 62566324 62566349
    0x2120a0902030c0f03120c0109110d0309092403081b0706090515040803040602030406030f02030601080a09050a1b030303060519031e080f040630180f0b010f 69
    0x1005a40d000c600700f58003200459144101d80440e02c0801d0030120000620841c003480460701c0291102d064100703a010398800d406803196015418200300341301490303035405800140282001d0201d0b1120360b0145060303800004000095401c001800c0d081c0c0d90722504111025080458506880c031003040102000d410a0009000310340d04145000b89424818460503101c1c008040308090f8200340b00003200d001d0808203040d02d0752541c840201030356a0384070744a800002442d11800d14090080ea100341ca00070a0705a40d44511034070b070400d080c400740c501014181e900f40034000170300000402c3e4200c8260300211041100c62958039609000c1d0881e10190720090003401082c0b0400518641140400c0942e40d200e526007440880550380800e000c0d8040e100200416400a4041241e5000704064000c840043d50380e0f4080c5e0f10b404807141c071843c8031144403110b013039a1100c40e26400421a0080030504601900b110300341c10a98840007030040c2204019500c0d8281d41c0014040c5400c0c009160b03018041c8d001a41 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 62568824 1250 62567574 62567591
    0x601031106090415060c030f03110d090201050d090b010510020307020d0b09070e04060501030605091b040e010f0219171e1003060903020f010518030f03070e030d0302120a 75
    0x14100154144124401d41c80000c41c144140d0300c6910488622082d07460000610b0748813540030301130007180b80f000c2d00401c5410058140e482e2203402546a13081c08100028105025102840e000d0709a0101c103e040c880107200711303410b0440302e114450049006843c159003d525001c140700c02c0c405505903610071500100170410140c0c6a028402c0221039019038070b19141e0351008501418400e00e9005140942000e80034001484000d4110030b060700d00407001040540c0300d40c15140e80c1c1d01c0320f03c1580c4600c5101840c1ca0780722071074591705c0200340b440510008100f0007040b5a02d0f004a0f84443c030ba400e284005140f9004045034002c040200761a40ca03202e0084d10f0400d911120701d02c64000c46800d00e4200700c84006071288614003014001581d0003031007031080b600280b90294403504000c503000c80d150b10f0a0000f40c0035100004c0c01511a11031180554a04568070f080c80d80b89520040202081c882c0c40c001c1050241c5080192011786e51040d5001a00c441001403164000c45025100c10426401c02c03620 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 62570074 1250 62568824 62568833
    0xf120503070b060d0b0403020c0405060901051c111005040e06010f08160c0210020c011e0c0b090102091c0b01050a1406030601121d060f010e010501051c0203040804030212060103 78
    0x11181229082160b2001030f5a074000010031010351510000c1080d018002803004154000031040403081e02207070140300a513034040a200c28403109100f5140d01c4040710700480c00c0f25242076000010f140c01103400040c2c20f01c0e2440491420241c28002400240c0c1c00a8108141d0302e50000180d0045400d1030030030a401390a010051800002a0a121350407103500c411081e800d01541c1003c4540c0d80c06010800c3c40312040720040c0d1518021b181d09400325002c00f0302d604241483c090041c0e0b00714040d4a4288007540036850b5003a40800003402100d50b990f0030043da01c600c0c0d441c0105084610880400c850002d40107150103204e280301a40010b0051000e84401d012034417541f042e181034640c05803070207516584c8910040b01c180c03440e6003a50480c1c0349040e4141c00c101189600d995402c0c0d0000782181d140b9141c00098070702180092042020120b038180040c0316642c032034401401500298000140a10100c0540800b00d0344151403c0f541e106d40000c0c00c00031400c003100c0c9580b07914200d41c003070080d0b9851a01c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 62571324 1250 62570074 62570077
    0xc061d0607050f04051011011803140a1709010207030207060207050a0b03060d02090a050115080903030f09070f06090512010b09220c03060f0b06031003080901270f120503 75
    0x41e07005100000c03441104140c0c540d030a0310000d250003800386419500542001d40b00710803c1c2c070151131035401c0006400514118110300081c83d9856a20666500d549100486075a0007201c010f07403c00c640a8945402036518421a6001f5080c04000580d90b13082441c02a15101c440e0340042d056400248082180c0e40ea509440402c548000d852035640c4d558a00002d0403140005900a44c0110307224184580e002c074640c040c2d4140c5003c8018422018130b40d010555418400300d41c081d10f664002c2000400301e1402064603038010b005401120110360300d84d4080320590200b90000000a44080820011490106080781140508200810440c1200c0c40440c500040083c98060303c00c2d2041e0300c903001c000740504a43c0303001b50440c0e04521299168506900580108040002410b0903c0e000c800c0914220040301d02484a092100750012300c0e50b603691519402220441d4140413074144441d058040c03500d4246030807503c0c2000d0501d8241003e065020600d69608140034038482149810000f603000070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 62572574 1250 62571324 62571331
    0xc01181212030219030c03150b030414030906070609061104081b010509030d02060105030d0e030d03050a2316180513060b04030503120f070e01180f060c061d06 70
    0x1000c0d04070141686034103401a108849a00d2802c0d42c4c00013aa80103281d25500020490703105550601c50b50850405a9410b52803030300a8012811003000401d00140d905039500c18506080390603641483c000000041180c0c200c0f01d41621510b445001c00001c10045100d558243c0a850a44038201824038004a075500054450514060105502c1018030303070164040e501e9002c801001c56402d0320125038000e40b00c4da401c0c81240c0c00703803007800d03651288a40200900004120058000c04034080000d00c01c9010700720107801c0300c0e83c103943c401e140054115000080b829141203020000c079a030034a200d44c2c1c0c0101260885000c00c0002c10b0b0030150328440f00c480d40500b01c4070111249416407034240c0b0740d1002841141c0c0903001d90100020001304006000c03028103840720802d000d501580e03807a42c45518011900311405000941034041c034851640c010303011031200510703014000e8841070b200c42140ca1009101d4010300d01140c0d0b840444001c20096004203c9040b05030000b0301410851000403a0341c401c4043e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 62573824 1250 62572574 62572583
    0xf010e09031911010e0d180905060102030a08070507020d210216050f030705040e010c120b06040b0703030207140105090f0a020a030816080301090507090b0307020c040506041404050c011812 83
    0x1143c1500403000c0940245208000560940e8004001603402800400700c02d00075102d0501d0b80d50340010503200a1180070712500040e0081c51038100008000c8030001001880c10060000c288008005610f5029041401e18072420440d0b02c50003c0e81c40080795509600400e00440d445241112650521615001c007200c2c010f5174052281c214840010f41001c21a03000030380c009181c043c42d003c5c00141500300c0310b01101c040d2a0703d81d100301c0c0320526034280c50409214940001c030400003008004032003c01011840d000b40303001401d00c00d581da1100c5e03043e012040628134a81d1a80240400c1036424025411100f0410008101e00741030340e40816081002803101900352240810810b000f8441141803c611640c00002e0a07a65030311030103030301c0050000390354200004055100101e100111203040364000c10f01c44d00104180343c41e040c2004090039005002c0c581045d122541d441074000d400324000e0003244a1406005000c0ca20301c0010003560031505510f10f543e070b528804001e92220300900c4099240c02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 62575074 1250 62573824 62573837
    0xc0e04020a090e15090304090b09070c08090a0b070b0603070611070b03061f08090c01091d04021201090b0a0e03030709170a121205010b1c0b03070504050f010e090319 73
    0xc00440c030b04040b02d200013220302440b40c1c4204001d0b00b034044000c1054404d800010002e1520a8003484030f80d030340848640000c0744400000501042504c0058061140700402c00304500751038090044203a042403900321a1100d03250188945484c090001401404203031409100e00c1d6032062140d07607126014414103c68260000124203903448071802e951190b5000d2807400202084d01c01700800810040300d24104600600c24580312640c0715605542c100ca402ca148074403001a040f0b4044514070024000300c4c0d0001064807015040c1d0002e00400402c40c0c000c0c1040c2e182ca24085a0720029502d03918404a81c0b0b410030004c11502c15000007001e81941c02d0700000001c0300842e004800e190146280c1c01030181119201380701000c6130301042c41951814440d105008990380c0e40061205030191009003038040c2c0d04107400b6040704034568020740800f00000c00301c0f40b80c190f80343c0101b1304641c01074807806000114400103203d001d517803410f060b4001b0f0b982ea004500d4214000103070894560840c100750201f114 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 62576324 1250 62575074 62575091
    0x303070f08090c090f010305010501060c0b0f1503160501030612030f05070303060b04090501180c08010501320c1e0709020d0f05010e07020c0109050f06031b13030c0e04020a09 77
    0x4104020514090080e00041070340c00e1454805c8515082448100c42560078007001040142c42840300c41d54030350348880d661407641c0b10b01034a42000c420041c0700c1c6103220f601c680b106105940c1084120401482041a05001810940010180e60407604550503202c01c0640301400a80e01ca006078205a4040c50000c0d1140140d140460140005510040144d00045000300d541c0d0f590b913000030304903041c0c66031080061441c0540d0500303490009000702c0100b42030b81e004018a500401c10160391010030044214200c420300b129021000c0310302030800f121940450403c40342001008100041ea0040c909040c6040042140ca035443c0054041d000c080350f004281c801c206401307604a0b8440344500e00c020b001544c1c440c03449019041017101c0c0c0300300520468100f2659540580001c509585014040c070140440000500c546c0d0303400500030348041079103c0c204507410410200a402d1034107040c440e0f4038034a40f940c1402d01300c44c40550010480745020302d0a000041c0d468400c900100c800b90140801c4c202c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 62577574 1250 62576324 62576341
    0xb0a020a1101110a030513050d0e0301020c070e010303180305100906060e041b0b0f0d0203071808160e070f0e031c0e0907050703120506031906020a0e030303070f08 72
    0x280c00881c2295560030240c03502d074005103a40c050b082442c4150f50800080d907440d890440301d9040c02d100900103410281d05002d0103482040d07100c5240d90003800140c5400070311107483c0d14020555003d00211041c1c000144101a031184000702c1d4881031007020000d060440d00c40d02d459100c11210301c00c00658480c00c00c0108115a013103800140b4a60124010f031b46001e082c0400700400c58403040d420005400070200782c0189020a0b00d900c002e900f8040e9003401e40c0740400c60002d5002400c08024031104144d80c03682d1982a120003406483c004001c0c1a9010210b00440c49610312504104040010141000240c5074070044614a0f0490b92401d01c2402c0c0c900c0001c01d041c08042001201080c5000d0800201c140d0000e104e212001c0701074460306410740c0d9840084400c1d0094580c001c00140d00c12010000c1010345400694000e000101500c5980d200740840001a2006800c200c400d0341d00401c142e55000e40011350030f945620306030051451031403c0240140511603c0202c0000d100d118008500001d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 62578824 1250 62577574 62577587
    0x90f0709090207080a0f030e0a06050c070c0f080d0813150f0204080d021207020306060105070c0518091005191d0102070606081605060405060a050c150615070b0a020a 73
    0xe00c00031008541d034080f00d06008072503500c0404444007003403c071110040c0d094845d00c1600c4141d003481d40642100c204070795030389004e030401401c0c0d8144160140850b5010440d400003510082941105246440349411103c9041c00d1100c0c030008103101b40c0314201709005942943c1c0079590b075031196240620700c000108200060144030b1140d9602032000c60f02003400e0340e00040000703800f24260203c8508184200000c1e40703500c64a00c00a4154020001103061540140090403a582c813820100886a85400114080c0e10700c40d032811100f241e001d0180030b6400004c1c0001440488071050602c143d2401120b050b441d20840f01480403415500c1c0f80c402c54149500c0b0984031801c69000080d540d0300e0306030420310007410b01030050303d00e90302602021020107034a80d14003500b00c03440038080c141070038a0301080000d140c2100117110300b4050304002d039200c002d0701844030116800071044030803100c0c1020ba0510413501c08141503a500000c00b0006030000ca0759150074242c1c080f0000a0144c0c1e02e8074940c0044840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 62580074 1250 62578824 62578829
    0x6090201120606080720030a210c02010c080105031b1201150305070509010b03190b06040801020a090306150308030a0e07050901030602071a15011103040b0705070302030c040209090f0709 82
    0x81c149040c401103501c81e440019980114045d555000280c449400c400e0646110741c44440f0055004000809502e03014400409408032804c69652116000140035410388501480200c0141d41d0340441801c915001400749000d800700390700905a04c00350584404e00c044880390788a201b0b0381404018402c00b64250441e44a00d0101c450085200380c0d24900165070740c40030b010342c038803403d0000000b01d8401c3c861419203218010100ca403070a05003603105810001e00941c107015810410030440403032070042c24001412074008079591066001e1442c10f051084030b40104c2e2003082810100020004902d501c0300b42c980040300c0140024406400318040707458000d01d0f50241d0741007400b030000081440180d5025107183c80c001d0a6030003000c2c0300ca480384e1002038000c651002860b400d03e2000720b12544682605180c00710201c0440746030644803200b40c803007a080700604031a0359100e481c1c00c0c821810140481898860141c0d015030401c64088006068448000c0076445c9000800c000070382d65034400c4900100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 62581324 1250 62580074 62580107
    0xc0d06020d02070b09010c0c05190c0306060e041203060609050111010b1f02060112080d050405010b0603090c0f270c0708030c12070e01140a0201060b0c060103051209090406090201 79
    0x40c0c5100030f103441303005a04100c0302c2158a519201c9a80c4125010301c000551503548000a403840301204011880703080c0342050f0036a4200d0310072002000182040c454070011b020b054041c80d41d14549840c1050103200c0c1414000c08150500d001001115041030905050b00c400742404505540c2e0850b0090040900c0c0c05039680c030280d03c81942c444007078000203082c401c842940c2922400c0c0c2e00c414081401c05000c2c81c2c020314058007080300020380002d0b5030046810910620012a0b004c3d84880024169001542d0040194000403207020142c1342840c0c401d50780c0700e000c0d030320440400c2c8078201710581e2006020020280111401c001030559000e4401c40b81c0c03456101c070243d0b4480c03c0803c855295038000500039510f000e5540007044041c1d00510701c3da00e00a0381607542d010441c00c424a070b07600700e8001418500666403104004240c4106001c05402000d424000800c107541c554102507182c20061a1280310304101008108070380e072030b5100000d9003d508501c0c0455039260031b2004960708254001c41c2003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 62582574 1250 62581324 62581327
    0x1050d02040f0603030c1e05060609060102010207061d0f0c03061302060403050604080301050a0506070f060e0a02120d02060f04031b02180411010306090c0504050d0c050303030f091605030c0d06020d02 88
    0x300344c1c0210520889501440c3e00700706a1507e0a5803005061003900094480d40c4200b00003180742c42c1450549a1044041c0700150030a0b0050380c0398016281d80d40c1d81074201554080b1240d000070b404002d25100229a9001481c19a403940042038841601170145010b49001c0741c004019503c40b40101c0380210303401421208d440c541400d040300550004c6c016a88902201440000c55280070300644a41e25002001c409542459603140710061480c000302407083d014509100c00503aa451000728564403240d00a8981c0c80b40b81d003402030400c0d4000b804100b4060380c59081c000070a6100c00303042807034036030110080c2001401e03000161000c681c1401c2030076140312190411041244040765840c03080c00a89003408a191a80e05031020340d04070030184000164140b0040280d0b2030200c50010507140100c1101d0080340e1201d000c282158000c40700304030380c117001c0c000780012003408001815245901040d450045410b02c000242c50705205800140f168102c00e0006003405190340c12030f03071905030b00750045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 62583824 1250 62582574 62582579
    0x403031103150307150215190603030c050c120304090507090f030f0203010c09051302030411100c171c02030601020c0307060908070e1b0a0c0605240103060e01050d02040f06 76
    0x1c401c44442c00d580c140c0a8094074074001856200f01d4800d00103a91725402802d501001c0a140c0090004010302407840c10000780b40020a6141e91f120b0100034500035503a0343e86414650a0141c5020181c420a078014100b0081c5500b24400210654050f60b80b1201c0108243d113607403d003102c5000b01d0307800500d030400c1020030000c10031036405450010144250001d11150660314025600c405141c804ea0ba0007085d090103218819920340d005692040c440d1256800083c1d1081c00314400f4003001d0f1115012496100030304080c03040c911189215401c0081c400307860f00e6007410b480d1a0790b00a5402c000b0025802201060140e070003401885100103000e0210b454070ba81e1117100030210b906a100d503442a001d041800b25001c0300c1c0c503c002d072041c031a0454504c800d2000d44000d0138254020401281044120407134031000078468010507004030810b0520458850450000c1740406010411090501d03182a400b088041044010300c1d0444004071508403140200c1e00202e8060000c41b40d10008139840c00402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 62585074 1250 62583824 62583841
    0x1306090518010f14010603090602041e030203060c0307020c1e030a080a030b03160611100e0102120c160314070807051606021f09060605030105160210061d0403031103 73
    0x1110408010300003e00200d180c40c02280f040b251407140d0070421400d018014004503029030802e041e081d1042100514160f9104441c8132400c4000c40084480c2c0d01c280710030820351408010094020214400ca64a113007000d81010303507601c545513180c2e0701405101c0d8a080c18490310300c11032140e50304040c066030705d0005640b4006649502688011003c01d10f807080d500f403181000038903030041000f4040111501410181d099441a403403041c455030070310800000c490754407164020984180300010000d030b110b02c00711141c40326002000f4402c4048140500001d00400815400e017084560142000b520700445070801000074452540058040c1b080007417848100100040e0101c221b05143c0d4060700590f0316010100e032121000107200441c1c2c1c21904030010302140c180c0c0140324040c0314a800040c000e81d1000401c2c256502246d4840c00c81c030802901d03030700701901406036040600004408000f85070414480d5540c1440502155181d6a68280001c0416009500003003103029100c824944a2500018 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 62586324 1250 62585074 62585101
    0x5061c120305150109090e0c0d14100903120b01050c0d020304030212060106140d021b03090901050f0d080d15081c02010606090b0724020904050606070503030613060905 74
    0x1200092034800090503984101c44074a00e03d00059403010001441d02140202901030104042903d020709885240e03540c0d10300420b003011502c1581580d0300c000000c0701d80e509240310001920310360303401d180c06180040e81c000b504180801c0c486000160910781c0e036004880c41d006900f0408180e202c1c5212807007104d50000003400c210381c4200e4081030b50302c900c6541a030f210b00c028400c480c0401c1e894100ca0300b101c800d120283c10ac94521003070050500841c0e440c551040300280c00d02c00199040018051030740d052010003e809010203585200080c0f2081000c0f880e1102008800341c00b0b01d0011402c8650901070b508694800c88200210000f440d03103446059482d4042035858040840030400b600130402d0060003141c003140c6168403111050352510040840782e80c031102c1c0454410036040d501015104142c2a0340b0203d12580c03400607154a900f00903c4115a006802c41d84079100074002d072000101c0010480fa0300600076240134920707509160340380340504102d800510309a414001007044c07071024039a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 62587574 1250 62586324 62586353
    0x1205010b0f010507031209021c03020d02010506060406050c0309040609020a02190203030703140904141006051204030f122d020702010822051b03010c02070806040605061c 75
    0x300400d25060007042034a005220626010a20500101d00030030300403001500e0110b121076001c50659240e500041140d060200c0040b800c8a01c200310805050341000042e03248001400204213604101000801c10b0080c0c1c86068100140010640000740080c801d8505107000607105020158880c13400034040d40140c0c60705001403060703110300801d40020031b2a0081194001c2c1c09103161101c551001c03a0001c801d405034808100c000c00c100e43c000c1c0c5aa124500c001c10000f00c4041041c144049113110850b00355004c0b00c100a824005011104200102e40d0380042d80360410151a000d00e00e020344031075100104c064240703481d017140d00011140d04140c40c7e2903458850391808502c0c0c107102c0804c080307011341d4002a002400340780001d5103048c03210702d0074101c0045035170401d245503195682c0d25140100c4c0c44549422203807c132205074401d00307090107002401c9015001524107181001c1d01c03c0d0f85d503203008202401c030a440d080800d82d9a00c460044170002c0c0141c007a04100508103040480c02c802050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 62588824 1250 62587574 62587583
    0x106080f060615090915030a031215030201080a18020d03090e0109050408070b1f031a0105030a0503031504020403060f0515031c0c080d15181406010c050c03030412 72
    0x7038002500600c0c2c044900541c0f50242d50165040200b41c1040c800e25070300041100c0c14010383d442d04035482d41e0b000c11a103a9010705c40d03a5070680d254140002001541c0703214412140b1400c100b001800103130b030408034495010b505075100013035000d00d602e441040d00c10f041d1806034000f0225000340080c16031003248101614040d28486606907600e10f075010441e18122006040840705200980001d9a04502c0740c4e00070700c0c1c42070014110b0781c001c0b0301d8520320380c410741c422036131484400011420382c000303911000e00420049001d0300d90311100741c40d0143c980c4001419050803044079101458a9076495060f01c0c05143c01900421407041c0d0002e1103001044242c6488901342601c04a15585260010b12084040d03500000822490418034064502808007d002c4604070000e0000c4031171005284140540f00c508030840f2242c2c1c5103459008604965450152a012401c2c076546084801d001c01c52560400c6080c609480001840c3c00d01d182805070b5021318aa00d0b000000b00020102c2161181b4034205006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 62589931 1107 62588824 62588833
    0x406180504050a0c12020a0507031809112503120c0918091e0308060603041b0b0306100c02030601120c0312120c020d200c030106080f 59
    0x480c3d4081d94181d4a610004045501284104900000c030000714902504028000c10900c02c404001c4c0500005c0c0121200303030317001100c01d80018030001504001110080080c0c0c0444d500a6650000241c191540300160628024201a010f5851303103401991203546806007001d84a100114410711110031000540815142103c1014007040380700000d40100c1450b04e0042c40308070f110250700940c500e00701e03c0000ba400c80501d940102040b178805071241da5600d02040040340e156001c17120058441d0700041c0100d9200050341c0241c108031449110807180301c00c200c0c0c209450000280d4103a00180041004500c0c0c400818444d90090725525000b0b5100e44900f092005100e1007040081e4100c082c25190800c548078080110600f07101070080c1800c1c0038001400301071500781007465448141c4500c083c54108010a404044018009202c1c0c2581c4418054403a02148100b010030b000c1e = true := by decide +kernel

theorem cover : BRFrame.Cov 62410074 62589931 := by
  have h0 := BRFrame.cov_init 62410074
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 62410074 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 62410074 ≤ n) (h2 : n < 62589931) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
