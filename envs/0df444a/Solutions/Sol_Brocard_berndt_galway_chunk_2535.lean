-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2535
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:59:35.976793+00:00
-- url     : https://prove2.me/submissions/dc608c0b-769d-4c12-9dac-834e83ee6a57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 455755395 ≤ n < 455935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 455756645 1250 455755395 455755403
    0x70b1b1507051e0d0c1704050a02060f0d0921020105040b0726010e0105010906020a050a0201121508061617060f060d05250203030f071407020d060e0c030a 68
    0x38541d03403006400d4a20b50f10807211619103400e000d003a03d0102c41120080c02892002c000e001c02c20084400d401491224040101d0380c4c0190800203110018000003031410603194107449007501c03101545e414030314500035100740241050410080e8410005d961b03d440204c40f072a44c03d49840754074556030032400c890301102c0043c890601c60002c074001d9030065000036480c01402c408200c0c4811441e0350300178445800c0c0d2140000880080051120b5a0416511809004c8a1009103641001621001c0c3d80c0c1003411800303410702c64149020403a841175500300100c845240084400030940e03614035030b952007034116102401494204420f11205200d0030024916914625603040641c071804100210003845914580e444813040009202c0700415014491068240c00c42074005103648100c0c5002e000700440603041103400400800074255105014a600503180d403038003c5010300d0300a8805c1c614461440041e50200b84aa9040c0c200050380e044000c01001000554040d0500c09080c16030711a14036000030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 455757895 1250 455756645 455756683
    0xa03080a05040320100912270303030c120e060123061803150702010e060106030c021c050c03070f0212070f091503020d11100e03070902070204020408070b1b 69
    0x3801c0c00483d004c0300301040384803040c1c590201c0c04081c0301d402c40b24104000c50f89a0042210156156001068001400f1400044652144608c00c1407699403141c0e000c0207007407581d1900d00014551141c00407480700250000c003000b01240d403078101907a559091141442c40860451420b03a0354401c040c41c1d0201610291110307003442c141e1044260349000c88000aa0944a010711000f60001900c401134010009a0000560305580e212400c0c1401030580281c024181860a00da120341e900080d0078028007614102d855240848510407212172007441c010513901d110203e05075041c46440140718bc801031080300c0d180e5885c1002140c4503194003051103058164a0184c1c000c111061198010709000c1d569030500b280031a44036030015100c6860b42c0380030780310050a2284010b071403c1074010420600781905144004610403800a662180c46028924104d5000314000c400c644654060300c0251440c2026149000d440344100405504200304481107850b004d520820403882c00714140c512864805994 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 455759145 1250 455757895 455757917
    0xa0f0b0102010e0706080604270309060806060919050907030e0106050406121203020913090203010b0d120528110706080c0a11100e031b060105180c12090a03080a050403 74
    0x280c0340200000c2100360019150464103c05010041400100145d5050300144010082c00c0040c0900340cbd50304840c0c203124440082c00050f940f0207098030000f0f0310882c1d0110b250321400c41050988030b080d501040c1c02c65040c406000825800d6002500b0180c6910020040c842d62181040141d40040c07041014049000d441000415545002808800490304003d807605c3c0301c0d0070100340314084e5070507003450050f640c0100608524081c0103070300499904075400c881445240c0ca66089100900f141c940c1848000642d000c1000c5081260011900b6842007d2102c007001d18405400c030240b5510f110018000d41201103907080c002c28000780604c029000b017038145074007200e081c0d03445d02040c1850f04141c4601e007102c0e002c64625018100b1084580ba000c0c60321500ea0a810685409600e010013407250005e50040c0010b4546504000d401e44001140e42034645034005811410b12a84121200d6200000100020080d00040c40c1803400c0c4691381c4e0320300b6036403004101011a202680e00600081341c41084c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 455760395 1250 455759145 455759147
    0x1030b070f020708030f0406030c05031e18010603060903080c0a0905040b130207060b0f0a0b3702160617060d0c0801022a060702060406021e030a0f0b0102010e0706 72
    0x7014003a0802401220302c0c003600c0e04283d030303e10f400500e0801d1502c100040c0510005915010b8071842044c5800c1c0103086082c10804900318086000c141040f8070910b000240d8410f001030100c3d504803c101c002001499141d051000140103429410360200da00100400e50900840040301d12031140d5923a0f01e0b860504140401010b82138080219510040844013031030080082e10003882c010740f01e00f02c000741509400e424414244196034405100c0c5a8001081001e06c035900210781074044542050a85440d003078400400003010304410750111049030080060490300018013203d244051130300184025982d210446170302240c40c11898040c61824080342ca641010303142000f66520030b4810344101a12040e10500f2030700064030100440702d5030a00d0b43d0804078500391002c000716020b030142650303148c540c41c065540d40780500000e06195000400c82c011441c40c520400d00381003000841d55403400d1a104950161011000c0810300629141422410b036005100c1c1c50103100031070016003400c600c1d044c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 455761645 1250 455760395 455760407
    0xc080712090302030913360b10080d05120c03070e0d0c150c060b060c1e0a060204150f0309170c030408060703090b07020604020105040e07170a0203091501030b07 71
    0x8406603c4180220001a40e81b6800b42507080c00106000508038085242da4121007291800c0440030441352601e072405074586002889503641140b008e601d140c0341d8840041c2620501d0b4094a00f501884003c2140b882c2d119000381446855000c0441c640e4035410f107400c44c03d2200399a0480403400002c1ca030310703140c203005d03459500c180d0180d8039508969030382e06030400400081b440a40d001481c00461402080b80c0e070720807040c403100190f4801c2d0601500c0d011295582034080030300c0c1c4148a0042454120f00702c00c000c080035482d4051000d42d101c5585006000080e06855840b9000c50541503603201003501c81d2042041c40c1c0d0b008000381d0f5601c2d174000d4400e50241d00411440f11580020400840c022a0421081d401954560340000d81003500e8101401c0204001d000582190090350138480940ea01c00d00795001d13200d07051007180c00e0792524202590300d00905a40410112006000c0141002259028510404c007003001c0e120100054031107030514940901000784030012420104405500c00e80d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 455762895 1250 455761645 455761661
    0xa0506130c02150a1d160e06060f0a05090405090a05100b010306050a080307050106170714040204380702060f1303080301171911090417040f090c080712 67
    0x8010b0380c0d04100615035a80400394101c2c4c40c06030440d1034103500018540940c2c0411054001c40300a000e5152840000760001140e40c400c00840f8400308021850541e80c4c84100c664900341c44203a203945850704d0001929580185031824400d038680800240303031210102d5168030803540300015244c01e00001c40460002d11005145904040d40e5a801141d203446554142010300f280d40c00070b42d111621741c40d043d800e42c3e40743e400441c280041c2c410050b10302100002e00b842503881c1008040d000381181c00114000380503d52000f003a20b2204240c0461002840807003082200700c43c11418881e41565115100034820850000d4025904000388900d8001ca030f0060451003070240c0d41864241c0e81ca4480301010740003a00200640c04545c01c1108236000700300110081c2c800710103089007805811303031117600c840d41035404c0c003600400c1c8210005041011030b07045000b90a95405030b1548454031b0b100d840030441440e00030617803c0da1034044031184060055603000e2152076241d0b542105000d100c00d1b030002800303180c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 455764145 1250 455762895 455762897
    0x51c111504081c0902041d0a030809011515021006050609210703030f030b0109031e03090e0702010b0102070f050f12010b1e03010516200c03100506090a0506130c 71
    0xa00ca0003c07070201d1a403425a1900a00001283c02505401013000300da44511040070682c204400c4801424004142c20304c0140c0c00d410105102d90303800070b1360360141501200151080324001001b1038030210207841c450030f1412580c200e82906420010607030481c0c026004481e80a503041c40b80e0900b0780ba00c440000382810309000b0380c0f1221509428450301d01704007030308202c0104240c0b0505820681d4035129469044800b40b802e41b40701442d68a5094030950809004141041021541d6040c9802101104c0041200c403030360042038540321000034000c1500d0b001040c0140110394000a001c803c442181007996401002c0058800000040000e407502e403400c0401c0b5552901e000c00846e580390300b41c481c190510490350804400500042500f1a00c0003031106516410002c1100d0000c0c1c1e0081541707805100301e001000a07600c0d4216500e1a144410071110340c07511850201d9800720805070042ea009810940e219034039034581c46024000c2d2681210040d4001c1c01c0144090710f40c032003030b800c1141210342c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 455765395 1250 455764145 455764147
    0x914010201060b0f030105011404050d02040b0613030c0513022703160603060906080f062d0c0414060a020d0c0206042d08010908091219051c11150408 66
    0x43c92043c0704140e006040180c90301e0b000400100000e580080c4120b00c05041e007185545000e003003030002410790252200280c0215503840003411117407100e800702c41840408035404003807030743c2d2450a100062102c1c0110740c0205000c1540c800018541e009407010b40304240403501c444014030070464405d202d41c814040e45442030721111403480c0c010301d00803170180c8425940842c003541003030003c03815542c5681c0140c15a50114482c0d0590074000b189280d0000880d280581d20b000592046070540a014400801822020380a0054241c840001401103940c0b12004c800b08089650030005035014030300720301c005030b080030301d80000c079500c5130404c203184920040c9242d042503125220100318920845006240e0000d8840d65a03842031003110309001418420020300c180d070b8035940d440a41c0d01070740e91080c0c0580c0c25036002c1d14100205015007607022208601203066042142080d5640f0348200001d5501ca40d15108030620180c82810032203480140341000f400000ca003c410070b041054010420b44117104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 455766645 1250 455765395 455765399
    0x30c0909120c01060609050a0303050a030f06180203040c06090b04030b04150905030705060109051b130902190f0f05190e03030a0f0e09040b0609040503120403031a010807091401020106 81
    0x214001c0581141030555000080950074903c000d065103400e41c00c40e611400e40701c8030400000c0c0d44003044440200041c9030104882e0540840a809032049130050a0f403540d4100c2240231024065000d188158082e54840309100c0c4e0300c100503500ca49181c0102c0142120800c81400891045c2e03102c4e81d002449051a201c5240b06681a0401ca42040d14101ea403034000080c0030003480010012280909120340c002c00c51800c020a0104d01c803589200100c41e442c0010410703451075412a18420000c0002c400103650703518400c44141d0040c000c0680400118011070032011003540302d62504c050002c55502d031189400082c1d4800c1041440d5006100c042222600d00c040301c0c0e48082c4040c0070609815101c1d0342c040d0015060141902015010380c501902c0d01000700030110703030307191106900303c0380c240c86006e0140ca850611500790f1050901c18401007103080c05000170554182e001200c488040039480740500440310046840c1b03c0d050341c84c580000d00182040c0300b004d400342081d05529005000014200c1c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 455767895 1250 455766645 455766673
    0xa080c0c120a120c091503060503060c070219050d06180203072c13080c15090d0906030902010c02040b1c0510060501021f090809032b0905030c0909 65
    0xa2604480e401076204041407205425030008204070680c0512141400a41c6100b03030001c26a5500d03215100104070880c0a2591480c040d602071000340c00050151911458012484415540004012802050b181041314104170105403c182038480084c0000c0c1030062a072180380262030540080541e80342c0d090840e01c0165010400362004020403285030300c1d0800141c0c030b0a440f01c01d54901010003810351104010400d034050403810685648007141a48072100d00c60307110302e086000c1e030034080c510650005100c0600e40c005801c000090080d40e410080a80300e50040341034410390f40c0000c0c040f40c4a03115082c010300e0107820010000901824038074000781c1c180c00c030700041100c0f000240c0b0207400c82c0c83c085400701024091f11028201c20b0008001000c001c02c150f110101101c2c41c4101c00359510042d030030030000b0040488644640040840f00710040c20314031401c031609401e2072888c810840d1808449054007410700c8800700d0b00005c010b42418507001041c403003200f000408000640c010519204240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 455769145 1250 455767895 455767903
    0x1050108100e070c031b020d1214180a060e090406050703270204050c0715051003060e030307021006080c2b120809120f0d0902090703020703090f03020102030a080c0c 73
    0x1603c0344e070344240034420702e81400340c52840e03280f68543c0c0c4d042c51602880050b0312039401090b051a4412030039041d84a00080c00c40b03001c5d48842c3e400e48944c000080090903022280d140300030640045a03902d14080da100002c1d00c049550842d00c640003000c1c00005004282c160748000d41c0050300341404074a018003030044c64120f000c2c41d500c00140c10300c40a502019030400380700c0e651340000108400b034904042074984405410030b20101891030f90311240010020061000d469008607840782c01170010700b005c0300c06162030b50011a0540010300c00c120300180c03807168901800d803c545130a009000c96006441c00d003c0d035101c284401600b50b1000203e27034144114070215a1490500548015230000c1e214034004040f40c03c040c18801056020400d080c6954108100f00c1c0d0a42440b0b107140d41e5101d00d403041090141c844440007075070203e4000100300010b90107400418500740b2075038801410325151568060082003600000e801030f4020300190340c52a001d4485950441207055030682030007000d02c000ca141c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 455770395 1250 455769145 455769151
    0xb090a150302090c040f080a1a0405190c1707060e1018090c080901020906040909030e0d0305030a0b010207080c01030b060c0d030b10050a17431701050108100e 70
    0x10840018108072005101480e44040c20820018006402244d1580d0314004214009d130903c040426000c10704200b81040b0050010440b5100c04e0b64900c41c81c10f20300005440d1f03105008400c0d02075030008030b0a447c0410f641c800e54026440f10702820701030b0014410010403c41c187d9061102070b1121007400140cc1141c60001d00b0303403030030200303c05000100c01051a14050100d1126a0052100045a542c0c06040d1800d41c0d20886000444201c00e0074102c4101000544668001311280c55440515501c44007e40c80343c98141e03018019403024100480c1d481d082440350403c15085040d90315100d6102e40c0000701500c80003801c8905240f144030401d41004000d241d5440030941d00c45881c1100e0800c02060404201b403400e249052003040360001e440d00120110105582e04070710009020000c103001c46d24007818410401000d0b0080382429442d09060442c6486101042c0200c41c000c0d240c0309184120700160a00b0001c03030141d2a0600664181401401307004010780180d401050722000250b100388 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 455771645 1250 455770395 455770411
    0x9070e0a02070c061b0602030c0f0a0804030e030a02060711190f1409040809040b190815010906030503042c040503090108010801051b0d090506070807090602010b090a15030209 77
    0x1030b4481c59890b144640a42550108090000c002c161880c0719880c0c081d00404190018005a526500c84500003251b20880000164200c0c0c04501e4207411940010002d1180b40b080d00c8e40700003000c40d0781c02c055440e90724407030096000004010020000c0d15000c90b060110300b018141d1001c482e00b01c224507650f2141a080380f00440103040003007101c86138070388080031643c409507400c54003400c007030b101d1030b049102d8120054003660715440c0c50b04041d210484615405184c50012101054648010545503030340c2c58001c824002e2a4070011030b241010b07100700000c80c1d0b80003008501e800e1a25402c00f844106100c862509041901100c004a20000c0c01681c821441500070755a42c14030034001400c0c4003010380205105a160004101140e40c1c21104007120056201c02280c1f41d210a0000700007504a01d100200680200000e00c5026a0000d280718007a241c03540321a0340b40341e11224128201d4164107280d40d03010408201042f08169140e0002d1940e1010700301d0a0701c450707100d8002c54405102510005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 455772895 1250 455771645 455771647
    0x1419111507051b010810091503020a0f180209061b071211012c01050f090303120103021c0b0601050304060e0f0c03070e09030906031e01090506210d0809070e0a02 71
    0x309041ca040e404483c04070300242095401820842d512010101181c044d92a80642d40c15013607082010032000c0f40025640241001082ea490b8049481001c01c40d200e104455000c80c40c220405103a24000da0310120005045141071005213030446003507940000408d02d05005a10002c1065410101d030244000d002c0c03002c0d040d00650030b400040600c09040d042945061503070b038a030034030361045000ca4294030f4000d280898441141c00207a520a215070301c1119454400081c050f42e520300700070300d80c6040b40c1c022a0b4201d040708503603d14142110080c04014030b00305a40000a48942c06500074503001340c054600090f079424440c5900d450b10402005410f00f07079002c2611a1010700d001c1000c4400340002c2c00b200078403820b0454483e41e50340a5404990f101340b01c0880001e42007501074000b2941d40084400410305542d60344400c1c4010300c801c4d113060340904c51148420208069002a0508180041008014110341c05804846940002e00464100d0081550000d0001c2038035210030700502c80030b2401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 455774145 1250 455772895 455772913
    0x60d020f03100608060a15120204030c0602010b1f0f0e0402120117071a0a020a0203121809060915040b180108010f0608060103080a03091e141911150705 67
    0x1c1c1d402c880c1039440340c0b0411210404209007620341d20206001c44031440c01c0180c807090500c03410342e0241004003a10015a06c081400402d02510143c1441100c0e140d030001c01c190110502400b100c14000048110003684594601c8082481903000301010b08840c03078041c01c042004000281681e01c61081b10110689800c010700c07856050425547c44950718000030125286040755070403a01d0100d00d510b028810002c100712501038028804800002d5006003901e00c0000440e82d0303040c00c1e4000c0301100180240d5010000c03c6420700302201c0b4000c2c07a00415040441d560000380c203d41c42000e0388856002601c88402440c162140c0c003000000c0b203200440c0306410340c1070280180c01c44a10610011000d0304010b400c2094017008680c4906580c7c10220841d42c4484261095001d045e4042c0024101c024200c0041840314011001c01501440360080035001021030180c00d0f592000050000038980b01e001c000c5000501e1302d4a100108c85001c3c00e170b002c0300d0a948120300071a42140105556907046070b0f040d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 455775395 1250 455774145 455774161
    0x1501080702010e07031103030424031113090506010c05060a02071b05090609070201060b030a0204090b01090803040504020c0f0708061006020105040f0212010b0d03020d09090603080f09060d020f03 86
    0x591a44100c0300d2008114580d50a00800d94807a81c2d88009441c0e40d031182c80542c02d54400344220780c0a03180a502ca03509500380313180c482d400d050201c5c4c3c1d00c100080c600008100e203102ea907002c884d0035440a44010260604019000c002040064100e50502c0070107040b00000400601c00b8034403a441180005803201c106e0308140c18a01d0513408070035211b00c0074010600040e600d01c003210b80c100c90180c910000c1a5a9403c00368010700d20b81d04102c620650200c20401c82c1941a0000c0080d104080020312103002c41900540f4800031030f006094658005020522030760801364040c010720034a140c119000170440186250410140b0740042c13160703400c25001c1020b00c0701e090601764000c091510007040304c0d2400e5128030000a00d911030091007521183c0d00c000f0b44007400d4000001d0004024051036540c100c0f80f801035a50402030000c107010070000b0500183c0c001c01e910400c0200d03030b0803480c060316041100d000e00300b0799403004407100d0344000103000c004c541d840f2501c0a4002104282c405542c0ca06029035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 455776645 1250 455775395 455775407
    0x60b0a0906080c03040b04080f0309070f050402070b071101020d0204030f2102030906030709170c010807050c06010909030201021215030c150a0e030106051005072a0b031e1501 77
    0x42074080c401d141c1c0a2111102800c0110b0b42e00a81007030b0b000b4000d885501e01042184110358490040b420044203203d620b00000c80c5580840b410940081c1a0f195105c05000230f0340207543c4050001d210400015041500500e08000050041c0c800140743c003146e21901401c036001a0070503940300b40700290388401c1155502031142d060900300c00301c0d64211480b86000f546c078403910744c8072400b80e000032020400942c0107042d460003800d0bc1180c0006040c003c0c0840c80c1d0303a10304036180280007d00c0d0704042182c06004000710303940c580706034018214070781c00d042c0001d015185240040301159420010600c08c101049040d500684045008800340c0c401d410070180f07080d0800d42058400c05030700c00e440c160303041c81070100c1d0b007c4009030500b602014080d1000900501e80c80d440550070040ba5051404001e80c00300040c1000741c401e011903200f1010004100080d054dc2800644444846ca2024045001d0110283d03604c4651140c030b0991b411500c01c680005030009503801c003030504046d1104407680d03801c21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 455777895 1250 455776645 455776649
    0x20c07090b060a3e16030507180204031401020c120a0f0804080d0509030d110a0f0c020d0501050a0c1d01020d11011506050a0e1503281d07080309090408091201060b0a09 74
    0x8602c40c00c001d4103540380c7d41d80b54040b030310808002c0180f04c05071103e5940f198045d54001c64000e83d800c84ac0c03080b171021490203540a80340b0489503005000c507810644842c03405036140344519540304059014541c2c1e0a41c0d40b036030058816070b9244014010a42c0c101e42601485210320100e00156448102408811013a5120800391010002040c440b070020140d0018084044c044145000802c1172450300220b0034a10341010302070404c0d400c09003000021a000d80000700d1260182c0d0320400d203045001c2da9442420003118085005070042c00c61000410300c1580602c011703800e8800002070140100e03a2012240c82d03117901100202c3c0300400d01da0100c0e500308030b2441c034400c802d840000d4010703050701d03130b1101c580b2004000c0d040046110101085c3e12121010f507649007540c49108105854518442403241e00000250203223074450400c011030022008401d48078500f801401868040e11907035509003840d00041000b58112090100c144129102409154010f00304600140e507110301c1032500820041280e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 455779145 1250 455777895 455777923
    0x3010e030a1e090b032409160e04090f022b0308070809010219110a050111040e07141603030b09040f0501050604020f160201090f09020c07090b060a3e 66
    0x4440400034026a903041741c0c1d021309048001e60304000b2403102c2d049079101c010b184c1c43c0c000318410100103000002c1030003011802e400e610703111030002c6844c0810050314206d0000802e180d00302c40c10340d0010304240d00003c8803900701034181d0011503022490400d40c0855024158005070822040c8a0020380103040c0c65007101d52000213518001d90f01c410800b40300750310040c242c03c000038000c26002013039080c0940f02d9010b41c03004c020300c141f00f500301055030340350010b025000035035690402090000d070149031014145044540458108000c01050f14400c03a80b141c8e055080c551a6540318005a45801e84140300301e1040e91140b1326a00a0b003030480c21070340001c1c6070310b00070b501c100410104c41300c0000c00d546204404014925403c2d1180c40121074249c0c59a100c201341c441c0c071160105012800744c000d8038080d082c000868607075580d41d8640c40156041c2d02c00707403600507000700b00e02443c0502c142c0840301f094400341c101c1001001d04c1030114443c4107241c2c1a035180e405c0f6084c3d9041c1d90074010302200b01e240c405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 455780395 1250 455779145 455779157
    0x5030711152502030f12190201050603070e1b040306051608060114130801020f07171c02070507080d0c020102070e01030c0b030703090c0603020c061b04090b03010e030a1e 75
    0x5039400c01c0e01850300705104464801c0d0000d4100c0308560301001054403480c4900e0544803155420a030210007500481c0c40e1f82900c01307121103280e20704c92052040c5403040b9001801080414a40800408076104c0a00000042030400c0d402c14076108100b4010002076110b10070020300c030310b40003a0404042407a01c0020f42001521001c1c02820303a0700282051f0009407400c03005503510740003910000200e0f81603104800c1c65001250340030303011000c1800b0744410b0b0b0082c1812199007540c82e4504a0751711452084103200c130001c9401c0f0f800300e140d990103440121310900441350a1b640301c641c0d80346021750300c20991000980d000074510071564180000401019501d003101400e5040d9500c01761001e005004071081a0008070000310340752311a4100010031500580c0c0302071f440f40c0341c840c004c0c00381d84100c0c849529841510b000ca086c0b0507a5402841d00f0b0240804043d082070b04000c0e8400243c100302c1800b039495900e4551401c18140d040c0010214011551244003410a040c01e0603800c59041002030814001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 455781645 1250 455780395 455780407
    0x103230f06011710110c070b0f03130f0b0c04051801051309031803150b0108091218041a091807060c031110060611010b1305040c030503071115 63
    0x12040c2c10359041032801a9180041d0310020b1a0140603854004000d007007000d0961101405402010a00360a0046d1034000e03031115038603c2d4510801e003109021880801c00215180900740c0642503087c407540c0760402020258465140040d001e030b40000e0345d610001020001c62401903a509007090f50a4100501036140000003928080500303802e1120f55100e120860030036120701003400c200c500d441e082d200030b203841b4149020121010b40141c040070b444c2011203072040d0700a00e0458890050803006100011600980c04010b0300026a040d4056590003212905641c43c3d0103103e401500100e01c4072210320f5a60f081000294014106407850b038040b4600445096000c42c4601c15280107040400365260030740740071120302e8100340f0700010502412201d0300303991071590080c0040351040c1d0343e003582d4049020360060880d0001130031240d01007031546d24002d0b40390081c9c0020f81d1190040c0c001c1c0c1501a50780d10380c42d055900c40c80b01140c0481c84100c900d4520302c0c2055101281d0100d00c250607040c90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 455782895 1250 455781645 455781673
    0x1111203040b150d15050a2705030c011d100c0c0807080702060316090510020a031101022a100516030e010b0a0f0305120705060705070c030506010323 66
    0x320018001038040841d200c001000783c8141c0030380da050400e002d021800300c0e69040c01c007081c49400704040484000c2c24580071402c80c0da82030080c00d031003130301e0205104020035500c56944e44082a07900102e07002d00051001c5003841c4020712400800a0300310554000d0088954012030402950500c407941b2070b460712822000c2070307501210110f4035a5111f03034101e5032400c42d402e12421a0107003c00003540442c2c00400c00c09800c100302c01c2c1079001001511b40c0644c5588a50406c0802d952510500c801a407000102101083c81100f20748021090341d40010b02d002c0c1e148014220882c10a031810701d501a1404e003440c0d117154100104000c1d001c0000041105007172003159070711a200314041d40800c054968030032011000c000c0d402040304040007403095850903a6075a000100c845103200907074850251103090960b01c00024112940940c3c440040d00940d41c9200e404c0d1105e8218000a46000360403003030100001d1402c12805010310b0142c90072145200d0518031000c100c81550400c1c080641084501d50495 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 455784145 1250 455782895 455782897
    0x518060402010c0309030203012c0a050316110910031203060602100c031514010f03022a2a100309051005061309080901030b01020d02070e0c0c01050703050105011112 73
    0x42a070901e03164890070200c0c1000c131180c107043e41020354503520700080b460341e044559403110b0b06401900d640d07030071100140d203115486403201040030f0203a400410401c40e8208898500380c18091080007101d99000d80400866004602150320f100400d0f01c0000500034000e04c1e800c0000c0480700392609011071410100700039181c41c0050321407401300b070b01d920052802d680603412010b112101000d001c402c440d62110301e010354081910a1902003208503040480507840b038000ca4003500c0300611202d074042520600c03200660a030100752400c0d80100242603640146401c1c00e510000d00d403c1e403510580000008001000c4040c8400c1420b1610740034480000a0020885d141c9144020318001f4640d516030000c901c01c03080100c00400d400340350201c00e40822040001a0403000000c0e41d00300405640000166036402030b481e80b00000d40e2140c0b004108946032150050b074000f040d10758140c1018090f8841a0a42e01c05842c01300200c1c1e201c3c40103101c1c2d560f0009030b0511045070000289102000c03000100c9007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 455785395 1250 455784145 455784151
    0x50c15040e0a060e0405010609110703080411030f0d050307031a03150601090510030219080f0c0307050d020301170f0607140f0408160e06030a02060a050913110d051806 74
    0x50a5a40040c00100003640403c00518071950414018a05450030754001c3c8958012800258031b80a40244054030a40c1a036a080e9031540b00c4112544460303d07440b0014456130300c105e9061294405140041005001e6000400303081c1d16139941701d00f81603101505440810080f41c1c503c2c400000b0480c0c856030300282c61450000780700314040040e200c01380100e40c045281c0e0040e94102e06843d1004511a80c594020703d40d0b003900c031000300d50240018004481140b0295542001406074501041c20f0020000042d60084898203005140c10207070110f103010f0380c00990082c021184010f0548440280a0010148841d40b120240074140391401018154220300c180b0032600e6003000c00c3c0e070b17444590803c0c1214041e007010411644000540d100f40c0c104500a800340340b980c0c074020408124603080c001500c8803800d6006104c1410070160880460711504801840350780304801d1400b034a282c002a2051070350300c1d003408902d255a400d0100e100d9080e1080038000107124442c05083e102d50407030101b06150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 455786645 1250 455785395 455785409
    0xb04110f150315090106200a08120c04031502030115080f01140d0203010f020c12070c050114190f020d021606080709030516060e1f050906040305030f07050c1504 71
    0x246035203d9004550058000424250b00705503d5800400c0740c45e044084032401c072030410381c40c034040c50445200300c5c0c130b40b03040d6100180b80135000d03c14000c2d401d55944100b03078024507030302049003842e9a944442030851795005003103401e9a03002006019650b5618400181d03c2d0060a0044950804441c0c415402c40140b00391400145071a180c866a40e65103100c410009070010300a0082c2c2e116506114001d52041e4061030203445180060860030070004243c0b04a650000da6202d8a5850180151499005086070001455040094a0b412510b0403241c0d0700700503080d9141c5001c40d10000d0040d10304540c48011005562100140d41101c2d8000401c940c107a5481d454001a140c45031581507504840a40004005005840303004030803000c0100302d88210380c256a02c40340c92410030b8040c803140c010a00c0c0c1d074022540707118403c161518080c0000303200b8002c0244c04c00d4901580d030344038141140c001780c09540c0c1007040042c804c01803040402016203400c4045642e0b0500c80800308889404d845140704045d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 455787895 1250 455786645 455786647
    0xe0f060901090f02090312180d05030a1b0519060b04060b03060f0105072a0b04060203030a0504020a0b0a02010605040e1504060515090103030c0209070e0f01030e16030b04110f15 78
    0x104803d203a58041c1c800c5680041c08036180d401103845080c400b500045072040c45019003580c03800040c941041d5000c07540382c0010242d894030325012811110704680c1e14006900b000c0040d203c2c3d00103241000070b044031005113030403007185418502d420425140404440c91041d0b0928000348038128407402143e8106008031941c0440c10345041c01a200c900444078007900000300c524040300740c10700c0040c152004828407041480305540315898501203005074010300006901c14000900c41d504190300072604240010034400c003403590f0321540750b210b82c003080380400140d444281c04c0085003028020b2082d05012500901820760201202d43c2da0002c0007040a0121342d100e0b80401e181c000d031070403942c5105402401031401c9607100c2c1805820400c1c944012070181e0074900c0041c1045100d00d401040ca540d0041a01710b11581450044010300401d00d04d4444502401100e041180b450010718002103204188022551400e4140640308403c03030b5450a0280300741a040060680e1b03030210fa0344034080048a49 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 455789145 1250 455787895 455787911
    0x50603040219030c0e010b0a080a1505040f021b0309100c0606030807060903020c040b0927010e0c13020903060c0c10140a0617030a08220602040e0f06090109 69
    0x8007026840e0000707800c1490892404800c4c0403400c2000420781320000d00f0b44200782d0303a5202003c0351b4450070445c4400241004040340c4900000d0308000d604140e00701d00350242d1615900020221450130041e00103180d40010304074401450b10608041e0403402c0e1000d1402c1845520110f071641400d40c0d542000c00504a04c480100140b640c44030340030315000401c00f601c80307034645401e100031300d04118140d0140c441e00544d45d45914140c00380d1509600701500418290300d0700000d0a0940c001420780c0c01c80c1044030b0000e460781d150240310316030401ca00c000040c00350400308414032450f031601d201920906401006103462035100001c085801420412000303a6410400110604103140310154560440c2030028141c2c602c0f085280140c05048580d0040194607541c09100414480407008820590002e01189441d82d0141000316406100e448503d0107907403106000780d07881c44031703140111002c03940410144141c412151009920185075550b291260034007100084118a05200d25185280c4076191 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 455790395 1250 455789145 455789149
    0x3150b03030418020315060c1506030c060d061d0106090501140702031501031502041a0a02030403021f23030a0f0f0227010e1008060406120b091011040506030402 71
    0x4a8004250b61031900c20000f03030890b900e0020354419103d40800d1280c04142145500d05030040343d51031141d40001740604c0f680c14104600040c0000c24469042c003034141c0103e8240c0b2645c0c0184918410020000b82c29810305008880d915400b0f6240100f4140103001480001c0d0000610000d0394001d0a103222005c006545000d142e1085c558001c2d003500841e140034002c07504001107503068030710480328404100c0107080c240e8120b001d00c2c89034016180c1c1400b0710a115101c513400600015101d8030542e4501501c17a004140ea94210440082c4201810a04c3e2101d0030342c814500444900000303801000552080c1382c440c0345000103052603078281d5451020301501403050b884510b40490041c029500c46101c1d0600f01040b8406420002809800c000c0d1444290321842110f942c81000030300fa103c40c5000303034070204c6030088020f001c1d6400a540c0c06c8003040703c0031030486075030f0f056200c0c05a101561420040c89418100a0440c1d1144a800c000c0d6a00400c4091000c1d68203441040d0741d8142c89503683c1c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 455791645 1250 455790395 455790397
    0x506060403060e060f01140a2c100602060a0204060c020f03010e0d0201020a170c071401110d02090f0f1c1a040533011203050909070809010605030703150b0303 70
    0x1c4010000d500d4403d180c1c05000d00418110b1294a501e030700303104035a98171500d000800f18103050040e07011505000a2000b05420a5108541c0240c00d01c0d2503041c0360f0a008618502e0002d580b003018083c2440750420086038104802d80d4450b09180301581081d10740300010b04442240080284103a642a42c441030742e4809510003241904000201c44105150240c040d001b503018018090005954007284040b141c0c02c1142c0d00c0c0034003400c83c0303000e16080d800e8656444181010040d21000c1d52038429089400d049400034140120080100580d151800410460741d00d0110304028003030711600701c042c3c07520303691598032a84020a485109044c03c40c50b02d080308203001111907070000030862605200c1803020024141040b1006001e416441c29001d0351030f0351007080e8040515120802000062044058510501101610032305049082198840c001065480c00322035000c0060020020002e859a09006040080900b41c0140c1003803411611040fa514440c451112015900d4121640b81514200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 455792895 1250 455791645 455791649
    0x204050d120507150605032a0103050601110a060b0918061f090908120906240f090a1a15091009030f0303090c060914010309030e19080105012705060604 67
    0x8600704038001a524048001001d407401807034020f2049072001508608c8094a51105950f0402d200f5545501600111f000d070000504a034100aa03020703884000190400008a0b000e1280c0004100400300b8010301c00c03091002071540307007048400403a03094650720100d05d1070382050080d042e002c031400c060281400ca000d0070303901400c0301c60300d030540f900140030080c1c02408160400765051072031615112426a03850744151181d003241c04c0e80803564421204c4800500040c0e9002808185c141808a400101e20100864080340c0d89621510702582d02a045001e1035050402120115401c03c24480070b03440320300507030307200c90701a0030081c4510404501a07804070000315030110f0a0001240940f81c001c001d0003c604003101d002c0c80e0241c0100e40640108158403d0310a0707441540803031744216004401400c6605426001d0003003c1e508246180c44600c03440355507140c2e1000d03030308420340b800d10f101e1300b1200164070203054005141003c480701d00241c14100542499404c003c612500e440000130028071441e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 455794145 1250 455792895 455792903
    0xd080711012c0120150f090106062028060b03160905040f0804121a0105011e090f0b0903070b0a080609180114070e01090806012702070f02030d030204050d120507 71
    0x5003520f42c0d005c2d12103503824032402c0d01c81c034141c025132100c0390100e00740c0d560360007402d005c82e0000e00f007014441c00701c0c041c9000240f510f8089460400341000781e4400310030703118a2401a4445040d48105100071402212510b01044e80103240c00703004e4000a1186071142d001e801505070719803003c01c1c01c0c0084000c061080640060701203030390701c0c1d48052486100e02e05d03281c102c50b0300c590b51301d00c0d070145101c0c607400324129403040e102c031142522010400810b00048204003414440d065101041c01d8104c82c050101400703408511030303074441d203842c1050700d040d00650004442400400c2200c254a03032001c1c003290820402c1c1c442200b02e86942c0302c284440c14110504000d10341c07800600d80e081842842c2c445000d28000d0301e951500a11036030046030807400f54055034413540d10080c0104102d04d03021408030001b040710000390300481d6005c24401c003a680f084005a820f44808698070043d45014480a00003041c2c0e4181149028541004543c40307841112001e0b0020880246d101e140500460441e081d4030b0b40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 455795395 1250 455794145 455794153
    0x409061d070501090f0608191401080706090e0112030c170f0d1b020d11010b060d09050d021b01050307090b1b0c010e0d110d080711012c0120 62
    0x2400309440c1d907840144034842c00103481050014031400605901d1003510350b199507400c0302c2d5845809a0500c0d0040a509500d40c981c0c030ba10b0411601e0302c80e110b01d4040c00c17508000d050035078500040188615010b40083c4003403215800100007101c550649445019498244000710104030706240300740c08031541704007140c0200003a400544408480c01000602c410500030440020400c14821141303513107400303080c0580d121a03003442c0114021540d101e690320b0382000100d50113614401080b101c0d0814100c1c9401d0680780c4a030001001014802c1001401c26403000300011106450f2a005142070604000d060020000110754500d200e84043c6014101c40f020a0f03a0710b115170001203003030032161400c140d030310b00508610045542c03060b18880000c21300100303000e00000780c039103498000410302003045500628007076130100081c540744041c21980f40138284c081d07185c04030500050301d02c0034540c2c0d40c45028080c9031840f00b020903402403070800c00711003880d20b611400c644c140c501802c90000c050380502482 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 455796645 1250 455795395 455795441
    0xe0615041203031104030f06110c0d08090f010506011b170406051315050d05060f03010504140601151706120106170c0d11090a0b0d2d0b06040906 64
    0x1110000c0c141d05601c40c0e6800c0000380c485407001803003405180030050080ca950070318040424001c1d0050481414034004007803a00350480032080c43d0000c0110308802081ca50b004115464100b0710402600d82000002841949000030008096480464580b40c441e41d121004000b40300703880c0e40c4941c0d84c01c00101c0d00b6946d5925440302400365000611642100d1010220120f00f03903051b41003000c40c022980c0c50f054280740101d120341c009003000911081d04807a2986040b002d50750309006003401240100d00094201540c41e41c1c1a080441c160020b01c518202c0205640c02d0503880042801d255078804d0900019031503410006014241e0340c00b00075035540c00d00c0c2e404210496604045100c01400c1c00c2212440c4070450180032800e401080050003402d0441c00050403420680946540031803020030000b40a841c48002a4811701d0400081d03510710f080d1440c48041b4806007840c2180c484012105c0c4440c4000c90f601c1540114000700710501039a1106107000810616400c80c105940f04085d508500b60 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 455797895 1250 455796645 455796659
    0x14130b031f020426100e06180a0506040602040e0c0307022a1504080706110d0f020a0f0503040905010b13260318010801050a030803060904140f0105070212090a0e061504 74
    0x41034104c20081d6010355403042001242521604002001c120007500c4503070380f000d080c1e0301d001c07040a009884501507850480001103040c050b00f889940706000050b122130910070a008003110080070780d01507030741c1001801003442e00016608251380d00a0100700d90b001c0c00480c10459190800d4002d074008100c0940c0009540b0900080d005903121030003240c1c011a510711084030007040b0109040390b80d82200c18100c0419103c5c00101142c034446004407800d9512a640c1c0480c40c48041d00300356000c1c2c1010070705000c0e04407640183c0c1d0050024581c02d0381000c03203005903d411250148600420303042d83c3c000e03000d0003465001020422080701070903a5200d02c2030050445100c6424503d441c0020350940010800c0c0c035204003201c0c02c3d030b40c0041d959801e5541701001e00c8180f0401510039103401c2424030811440c070404000041001c95240004989400c0c1094043d290100c0f11003108902d44050041c64400d4450360f450300220750440002d40c54945035a408070b00c11110540c051154a440018042417407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 455799145 1250 455797895 455797949
    0x3010b180f0907110c04060303050433091e0b030f0403200705091f0b2a01090303050a0509030d0908090616030f0c1101050d06090614130b031f0204 65
    0xc071400800d17244050210390401046a1303050100401041040c48244407120880c0131040854130006048076564400e1441400c61a03000000c00000400140061200c6250b5040740540440c804070300300000d80c01c200b00164680001002111100203520006040c035114440030508146412550500d02002c201500d41b1214540a50741c0907004140c040344698004283c0040c560945112140815003050100d00b1154803105103940068a282004444404540f030062000d0b15000000605c0c000c0350302d00901500c1d0002c080802561600c030401c51070f220007000f110001d4504040014010305503282038601e9015415020750440b101190605903002500ad156032203d000792550049003144e00412240d040c13096500516019008090101c5940213401800c0d03100624240462130303d40b01e024400403102c0b2a849991812500c0c2e00c40314807801c20040e00350081c0001001404012240c0000c00e6907101205208045d0b003858145c2d445070310b05183d040cbc4003d03001b002041204c40c182d1950290700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 455800395 1250 455799145 455799167
    0xc0f060c0e04150302150d0b060301092c030a050f0f07060e06090c130b010203070f0c0918020a0506030402060d0c0f030f05250c050618070b03010b180f0907 69
    0x1c51070f014078440e0100b80c00458408495005000d00c0b0500815281e80003207421005441c240c403910340c2000071140d6140c40107140a07000300400001c0100d05001c5640307100f0a08501d1480c45008100c10706046840802199541151030410b40e076541226401051180b01d045000e00360324402042c07a8040114a0b0004804d820265040301c149480e41d05200c0d4603100c0c000000ea5120807103c86102d603040c280e40000d510b0040500641f410200261640c00c01d146d404001110800841d40080c0130312007031849011000d20408069015040d050b80c0491320101c42402114031821001c0001800c40d43d5000445030f032094203000030310050f42c4810024014001c0c82c841d1070046418004000240c442a100e4a4840c802c4818119507450703803410082e18a08444004200f040345049507400412410054130b4001c0d40c0e40b200c0300e010780032190386a506216030380d007195602c5030042004110000e02039080d240b5460000d9030040c4021006030000310f070146c1c5a41d81d02c1c0c021500300d08004e103094010024000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 455801645 1250 455800395 455800399
    0x11060a0c02010e0d08041e02100207080708030f220803070804030201200d120f0204081507022103060112110d11130603050c0d1508070e0c07030c0f060c0e 68
    0x448102ca041e601621800780329420b000045e00200002d010890b1201602104445200d21900c141a02c0e00890022008034000c2c402692160031b080114880402c03032f8070010314120000c1e6003040d545804c01b9456101c1c0052552012008400320b0045000c0b0131201e500401203041200d680703040c01d182c11049070300144030580c00300d8007400e903440e4101c2e100c40300e81103481410009400e6a0300382d15001e0b600700c00090100b55542d41c1e0790302510044400c82c4000c10151040c90b00401c07002d6008034685103602001800b00f03007150024950a07074000300103000440302e12070103510141c036076443c180121500b0164910820301c103801c041141d147c101c01030340280300c03074907034100e007030000ba00c41180648140c03081c020b0444034014201020094988030b079101c6600821502800b07860242480483d205450740c00130840314140d0440010411070000300401e10080c01a4004c015040c5426079510f503041c0074031907002c0c0600c90000701e040100300d1903415141d100e642c0100d0803c981405d0050040c010013000195034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 455802895 1250 455801645 455801651
    0x11d010b09060904020d150b1305030c181b04060806010206060d05031602010903020a030501020301170601030b1603090507080303090c090103050d140c0f0c0405060f090703050711060a0c0201 84
    0x10845440c030204981004501910461422800005020007540501e100c0e010090303840c804000000300c1d0b0380240c1c00801c8104000d580341c40310f03151411030030f1001d40c1c4901c2c80780d88103081031841c54845803801c6402040346801a5882d68541b444084c030345c2d11201e40400030700e200241c0850446d0b00013079890300407031081e801ca84c816030322003003805200c10307003040068010351040c005185080b041a0361001c91500c1803400c041e040365681d011810041c50764004030380e240d40100c0103200d0151168104c00354415181b008003490b500d152510001d006028100f26060404c5448412419010303811104d00c1940c402d046030100d84c0c3d14515191650000d650b00b0409008580c6014007500e40406490705880d001805817004089050065500401c443d11020703240800348000c1d0312920303083c401400088148000307031a031a04011708220449600500306480b0300d80c1c0640b515025200d40c40517642c0301e655801d0000d81c946418205a880c4206240c23107541a2182104210444085030401300384000c05070028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 455804145 1250 455802895 455802899
    0xc03090b0f071403100306090b07030507050316050d090b09010501080f011406330306180403050304060b040204120c0312050405010c2618030f0118140c09011d01 71
    0x103054150a94800001914124103803e412444200864112006141546002e0340e40e5032450103858541d101510b801d001e0004010040303805001d0160300070485c4c94024a940b0304404220f24542545500c00100200032440c0713103405480c7d41c026545c0c00d412070f880c408a40707441c8441c54041c000074000c25402d0f0041c011101c3d480715050040181d40030100d2411506070391000705110805000e0000c48a1030364100b1540001c443d0004070400c050604002c6a41e520324080083c0404041160301c3d890b440171600c42000042544801038941142d40410040303040c80d840e400050280c056034100601403a21003174a2002c10502031007070400c5a200788069002d000c1000030a5a15006510510380880c401d840580000780d0304000c03d034017504154036603589a20709a09200704030340080c55094100d445c00340c0a90001d107020894901c280e10b0b45c10080c0710a009a82d844104241c01401c010702030000b2440901d070100c4e0501808803520707006800e03103020b03613503031000843c5070344600700b0100407810200c0c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 455805395 1250 455804145 455804161
    0x609090b07020d02121b0a080304050715050913180503030907030b06040b0901030b040516060e010e0d321014100f0b2b021c1806020c07090c03090b 65
    0x964145491700140b800d06000008800104140f41c405100050b401003001340800601c895000d1070282d4020350040200030300309a0f41d41c4084400131809000d002d0103014003110380c1c4e190000102301c40c000d45d1000c0b404810300c1c41703288282c0c000d0200041aa000100c10050540c000180440403a07002c0c80b00002ca0392104820300040b1404260b000f600700c0b85ca00010301c049803041413402d40046c4684e00b150710300c000101880441380216008180080c0d8502e04105403907074041404040c400c0121120201cac8040c2d0780e2044180c3c2c491403100a407001d003c41d01c0c640c0240b02e0384c803403401001d406016600b40752031114040000b85620300d08080c41004800220b2000d22018104005455603080c3c0c808649060035040740580c1c100484080340044480c82d03844140b60250380482084551820150302c80020082c84c8118042182882d100c0c60700d4008680c0f04002044d00f54a000d9400c403500680e80c3c0c030072a00c918204241600810042c5040a02d80c10240b581584183c0d041b41c00340302e40460503110b85c02 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 455806645 1250 455805395 455805403
    0x709060c050d050a0210050a0c0e03011a15040906080703020a0e0c0406080c070609030806151e09010e06070c031a0105030604060c26010306060f1d060102010609090b07020d02 77
    0x25010300581d1000807140d00c10b41c000c0c00140040c1c400380c0121809090000b0b584020703100c0498070040f160307032118500941c1d950071a03241c03112084210000c0c0318681c15018a02c0f41e031201c8454142c407a0301c658000c0c807009801c1c541241d021f4542044144101c40e00c4038611a580c950610040780191502ca0001422540c0f5050490180e010070f5459441c19250042c1160039100c0600100c08030f070380c1084103800040d1540f00b040103041c842e4480d03210918007001040850701541c2c0c1241805682000300221150849183d07200341070010300d0700360f21943d40c00c004030b4080c1e400090307090b0000400200030080c804502c034900102c038401d0f80d41100c80c0707640c910400c81d90002842295010751266001c5030000f0f07140d03040310185980614000f9100380c11074a01c11440c001d640702d950b61b100c40841c014000d03c8494081d0380050007202001196540c41d0032102a051502d502044842502e04170200700306a00c01c0d0803580c0100701440f000d01c030b28086800d01038003003c0c09844030000352041c9203009103001d002003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 455807895 1250 455806645 455806667
    0xb1b0c060a0309060b220506060c0705010809070305012a09030209060d11061605160b0307080901020c060c04080c100504151403090303060a06080105090c1b070e070906 74
    0x2815841c10081c4002058000e049044021154140c541043c4445511000321701c1064040d07105d021841e0030100303800c00040f500058460342c050501000700c0d580c4454001182802c880b428a81040242d0f00c11081030300301100da4100070502d50070314030752078445042c0c0000481000040703140310700c42c0b0241c00010b941e07111607848002e402001040004070b0b240340040803c0034142c0500c44100001c2c0311341e4001801a802010301120000381c41a5180500c07070104061030a54080004034403809042540074245400028206010050b00c5400100007450071340641d5100c003031110403610582012030403414250400d0040114612440b0107000c7c1510b4900c020300009141030b02d80380d181c681400d01400010001c069403e081c408e109002042c484c800000551007000c08601035516420150b0410030000c019900c80c000300401c0d40010700c16070b038600300c00e02c0c0c11071000542141c0e1010210b0301408a9254010350340303083c0c02030300d0001640c03c02074180c55100380180e0391410380301512000b007511103803000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 455809145 1250 455807895 455807899
    0x60717010905190903031409061906080307020f061905120c16030f05041e080c090f0f22060f0612051b06092101180b060904110301060b1b0c 62
    0x501d0242c03d030002d5990000c12410302038036011802c0344201c0315843c90040290380c2d0030300f41d51050003009007101740c8003580c0313084c0340100d4001d04c07141c0d10b44070f0840da5030300030408043c2c440c498403c00c442ca203a0754282280c0c803141041880c4003901c01e46d1000600160860941414900070840016800a82d6007044860f01c0041e109007280c1350f242501d007202d003c000c6e41d03480014000d04000c089144411000d011703013006600840045200c0c01c0c400a5420480d544143c2c5000320615002e00c003400d4040240254003074111100313010300344c0d5051403261850340404120300050340c5c0051400c050000030b8002c1035070110f02314001d20641d603a408802c100340380724032000340598000008210000e10800096443d080008013001c2c1800100d00c0041d405241d003070411003481e49002e40114102000b8001c004038402404d13850018440c003516a968890380c0149050b1091080c80300150402500e02d01c086084180a0005c0085030f071621301a1a0b00d40c00468904044084040030309802500051070070020140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 455810395 1250 455809145 455809171
    0x41b020604112103040510020f070b07020f040203010605070c0e100513020f03010f03050d0201060311060a0c060e210901020a080a02010b0301140103020118050306060f01020a05060717010905 84
    0xd6070322004003110314440256030012100f07000c0300c9510904245600c40985440c09141c1d200c2c50b05040052982c004003c0c2020354000d175903258100380c000b082c450105c0314041c030069035460803480021040d62941e80325552141c070100010512607440b0010b0034003d44501c1201d010380707403284c410402da04e07400c41d0709500c1d000791510140440e08011030080a045803041001d400c2c41030102c44c01700f0303a030001d030400707861700e0b1303c088007082400070070492503051135604c0c0020001d40e800c42c1c41e030340d06100e58000c0c00c0340200f000140d6080104c0c402c50400e0100e03a00b107001000076590945180703403904142c2030407100c0580301254206103e41140d040b60010a416001090000c1c25641c5400490300541305090030755588011001e01605c0a0246038160303030200c500a0030f07a40c114400942804404040318180344203455041c000c90310005401c580004080700c414415641c1070340109d2402d44002ca00800d00e000c0c000501200e9500030b2103401d2071048120089603540c0c0c8403500c440880350f08550245100d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 455811645 1250 455810395 455810401
    0xf1c0813110f01020f0a0b0702250303050f0c010c030605100306180923030a1205090a021516050109060c02120306041d0303070e010207060c0206090402090409050f0309041b0206 78
    0x10b0400482c00c0182018010744210f04a207800d02c0b0700301120003000341d682a81c52800c0005855052005c005400e880d200108081000d140100c500c1118074000202070010004981d41100c192070141d4102040d005c0092021800300c0c14024007421f107a21842e80030704107040c1e013903c20a000c1c3c060b030802e980c40e4851003180c600b0100c1e4050003030700300c0b05016074403d41d1000c03051559100c0e40e40300309040581c00000316614a00502d0040c644912031000201c01d074074050600141c0170011513402149901122014003005582e1302a11030f6106284a0341001307140001c1003400c210301900010076460040740c0400100d8401c0380b040c1e8407209410000d0008140030070015902c0d00d490381c822940740b00e981c1c8100803265203183c0310360318543c0b0a03100c04011580d041c03102aa607690400c1008040c00e41882e255001d1561036000c20400d00440048502c10783c0c010980f00c44130b0f00c480e4029048039030000102e84207032040444140c0c0341d50003208802c0c0a1804d02d408007c5800b144103205841d040d1560003040555 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 455812895 1250 455811645 455811649
    0x1b0c0f010221160221100b18042406050301060506120f090a02040c02010b0906060408030a0e061303150f200a181e0e041208090f1c081311 61
    0x60312100a140450f0341029100e009625030992102c1070006805404240c40c2c0f00000080c540044402c140c800d203070a08812607400d0b00e4400010000a6036595500125215803030b1111a0100005800d402c90b28a080d10000c1e0104903000b103811603206030001c005840d183c100f4007050384a0f00003006034410700100480c0c0894a10b0f400168442c074400c05a49115616a0000d004d40c0c40d5440303400b0042c0e456404800700c904d17080c80e803184c00690407598149170030320f05082107440e4016000101c050001c214008074458035108100c994017010240f2080e42c5030785900e031054040f881d180c1c14550091070b0030181d40241849100d542c480e41281c403411118000584075038030707455100310714040030004480c0120ba0b00c0320aa4100d1130240c0050b50003010326150f0b805c0604e0081c0c0c1c05501c0082e501000000344404150542c5080c106012a4503103802e495840f4000681b40980b501c100d2203252003541001c584081624000060000c103580e00c0ac02e0b00d4490381207a103030840c0d210a000c1e26503e425000c840080c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 455814145 1250 455812895 455812897
    0x40f0f06080714070203060a0204030605060108041113151520190203011416020d0206060d0605060d0b0906151f0518090c030601020c120a030c06021b0c0f010221 71
    0xd000e03ca4614507080c4682e011a04055007030780c032400081d40101d800e20403c0194001c45501c020203180503c841d18142d121001200d00003a00180900c5007240c0fa0a110917040d0040ca40d9104090702402020365200080900701112074028400101940c544444400010b041e041c0c1e0302c0c0d4088010201c07031008041c1283c1c1c2001d5080200c0e0306642e50340c184100e0055084029208417003100b851045034581034406418402815042d00840d081103040280c2a9506644070001c560800400141c0d641c075100403540048406002804034412081013000941c00064003a01c5544841d12100c60300ca1007000380040e01e88031002c002c1d25105c7da0b05080c2412403144010f007003160038200c14285002071740b5002c9030442005807402800e401c8000208001e55804100e202ca030403c0544074641d03d004072660f1640c640c1c0c45400300804020340d42d00309505002d420b406031641d40086014010446c0c801c5030080d55201c01c50701d103840c0a03c10402c0f07000340c5503002250080e4030b80c207510b104203800800700c0268111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 455815395 1250 455814145 455814167
    0x10809061302040c091206090209060105090a030b04020402090916230328020403050606040b0904120804050c0a150210060807060c06060b0a02151006050a08250203040f0f060807 78
    0x204400c0300e40c002201006c04280001e101c0c050f0200003a0030b00c060040c401c0000700204154140b00c001c0100040301e07154092580c0481307820070b405119a40307462000a020780b00e14a00c49921003c0d82080c400d100740403040c408841d800a8031041c0e8222608150b440700320f02e680703051955070141800015050780d0381c4130403010b0081407844c4024400103c0644a41280c0107504162038035400001004024149031288400c0034008503261111490186c0e5480403420b00558014200802c1c04081003c216080000d41c001107001014900c220742c558500d10042c0359230020620061003044481601e001680c86420b0984924902400b00e6909200003030321150784c070389001c4604c03558403000024940c2910b0082c1c90780c910300ba4050300c061101054005050b8070040c04036685513500c12002c00c2201d03000310460760240d8280c10403403043c0d500c04202d5502407120507001c40315007041c1c5507010301a80d070200061050303071207109801600585074140d900145a480c01400046141100812003131070180400c0d1076 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 455816645 1250 455815395 455815397
    0xe0907030902060f0a0305090a0c1509030803192a11150403020c030709022b0905010507050408240c130305030d09060e0d020d030e01021215010809061302040c 70
    0x61609041e0b001c900b665000013003440600f640801d41a802030f905024031500440100300800c071130b01c2140c41d4080c00242900c125030072203910460720009079000300c42110040d600400b4040c3c50345000d441000400307048648180030540b42030154041d80000d04c10110082c4203e002e121130100c1001300c00d44d0381e101c48034100c10440c40f405401404003100701006600c240d00c2a405440f000c5182001d051411106070002c0078031070300510200c005800b0b10038004011541c0300361a4a42c0180c40c400c1c1e0001020140000f07040c650822040094198000c4001c100300e0350018210b0fa08a042c14151040a04811200450240000b40890400b004400140801c9080c5180b60341125560fa07030b551b841e543c030100c0740304016600c540107101402031030b00c00c06002520349000b40a0166540c0c50094580405445410138182e8480c0c10f00d400840940c103884d00300d210341070702190300d080103641100c1682c0421402800245035100181614401145a50250b000713401300010f525810341c00c01000d0705c0420b28503c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 455817895 1250 455816645 455816651
    0x608031e0901050d0906091a1306111b010e071a0f03040201051303060b0102150106200715020a021c031b0219060f0906020c03030f1308070f0e060f010e090703 70
    0x40400a0325201742206144100c5c80040c480b0700c1c504c0d040b420390100381c032040b200352004010884007032880f003080c407813082c0d00480c00204010807642402d603500680400f0b41010002804a2588800561003c103124400c4000c071019150341c6c90f800b40030a4078165441c201c0d00b206000b89030408080001454100c0d10504090342042801ca1114000000c01e500c180c2d5095102c9041490658042c0f2005003940d10344040e490003581448800303491000540d070a07101c12603a400c1c68241c1a803081c0003000c0507101200d40000010120315009541e40c5190006920030104040020419805043c44000d010383c0b41d140e610400c0340000c1d120800070b148240a82c1c003c440c4845002d907110103521107a010304155201c2c289030b00c2c40e0050082000c07009406c803000750340c00001ea400041c2d8000003581c0024a0b1065080d5540e66112446100c0680c0d84d4041d40d0305d441101404103020326007165100c203440341003e00e88000e90340c000c2000b20b52000d01c0481030208040c0e80318264541403c240c000d501101505001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 455819145 1250 455817895 455817907
    0x60702040227010c020d020f0f04020a02100b0a060206130f12030501090f09170a020a08040e0115080106080606090d0f03200a05120c0709020a120608031e090105 71
    0x206099a21504089030380d4441e07400035a2161400b8030241d98080d4080c0b81641c1d10007900d90100c1e5000701c608001a2007540c2401d01000700780d464007110004250b011304195150b03c904000070359554214400784112605010603200300b8100110310000b00d40f40d0b60b0040a160b2280080e5040000c4030f41000d4410200d8034003414089906e00e803411500d41000d0b5400241589048020307800c1741c0400100e08221402c107822200461540000c5e0144d09000c62000c90340c400c5980d40681c034041d000d010007000c2c0040807900007550348811803040e04880407011100e01448a0100490391010240a0000440c9074000455040d040000240c04030320405420041c0d503041c2d030b8482040d00c14541c04200c2c009611507041d2007044540d034840700100342c016402070440d004d06a44540c1c07a03d01c416039004c60442c003c24000581981000030000900b081c5404641d541e081c41c500900d0150380d0300200c1180e81c10000001804e0f400001103601e84003800c080c2006102021120080c603030301100d5814108031040c000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 455820395 1250 455819145 455819149
    0x190f0903060603030e180f04150b0901090c20030d0b0609120a061b080f10031a0402010305010f150c03110d050d05090606090403030c17090607120c0c020609060702 72
    0x86070007960003512440e01c50408101002801d0780815286c4903140c2c007071018424020112030341030303400070f92209081440114000480d0001e0072040402640001030100008601c60180e2040031907410960320102e1014000c8030140b030303060105000041070783c01000b10481c281800d60048488940040072640749c0040d61002900e0307113007000255082508070013080010414030b8800c800c1021b20071742000740080002c00c0b000d0071004000b040700c2d1031100c0010000308055484028000076580c0071507030084610443d8400c2c0c3c43c81c042118102e000c02d1605001043ca0703070102c15214202c800e00000b00c800760304a0242110140c8070204101c0c10302401601300203d0a401348041004181c043d51860b4641c100556900140d0348042d04001d12038100d20103122464541c91196644150035040104101116000c00c843d5108446d0b8005155001c3c1c000b070204403480821007600489103660b50142088240416038125680060040089040c083c07044005007444400740c090602c00810701d03401e007481a00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 455821645 1250 455820395 455820401
    0x825060c030c02010b010e0a090f0f0216152903070b0c010b130509070e1015050d0c020f060610030e07030501021e03010e0604021b01090305040812190f090306 70
    0x10203180400c0d1034681e510742c156070904c1801c86880003441e005000004200108400d42c002d401004065034840b03d61030070009042e00f00c900b800d411010110758410780d0b80c118140300110302108496665014844010a00e1540901000203a0251038021440b4003040d002d2400a5449119a0180a0914001390511011001d400324007590000440c00a80e8001003000d5121040c000d05511458a014010709060018114095072812400041c02c2e84544440c2540c80556a100480e0b4181c1c410001c5013241e03000c00600f15010301e540e0709220807850180203a031034424001140c1d11690065000521903d440d000b1030710400f60301e0074002510311020084030704200642d00103880d280e400082250b80c1110f100c180741d1059500c0c40c5014215414401207070030224015054500c50b6801048425100406540500840c0c2610000704804a99072a001e00341d50014450f220150040d00a101070380502002110220415500c900302d10b07040c1c403001035400c0c00301c00c84584100620001d0204c0090b100744 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 455822895 1250 455821645 455821661
    0xa0513021201050735090f0d0f03060e160509040f110703090f12020607060f020a09030b0c12160207030206071a0c0c0a063209010b0d082506 62
    0xd000401d8600d06140040c05e00701500c00c0c0c5884103940604040b00810102804244070050110600382030340b98488038a1401c07800d482d4035504e038080d0018801995800290201d90940d0684040c01981e50b202c01d08007211030f04032030241c09a04410100c848280c0701d00018400604014000605507485191410071100c80c001d9081c00e21000092450030b05800c010410700905e0800c1500702c0706030424410030100707001c1d0311000303000d1480850054200000c036007010040d490410303000c54a51650a2004100305a144002c1d180943e0140200750905404001c81b5110655489080e07255101d0640b4440714805c201041d20460140080201c0180d03031760300090020500441c000c1d495114022441c3e00c032280082c1032000c2c90b075410446800510008206024801e402c0040011100804c55030040c04100001d440f0803c80c440b40c24040301e5a403c2265513000f105884020080301001605011020900c060b0180c080702d0300703000031500d000b1050801a1443c802d0000c3c2142004595907407003d0303848903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 455824145 1250 455822895 455822929
    0x6040b04090b0f0603040327152006061c1a010b0a09060e010e0409050c0405161106010b0405090a06030b1015020606060406050f13030807031808060a051302 69
    0x160b440c04480f85410861a070746104100d80c414914149030b50080c0813600b086121000c28803003510140e4510710040c5208004003500103240042c000e0070344005103000705c0b003600c80b101050540d0050f030403800d000500303500c01c0d203018119020290000d00103c4c500b200c203000840305c160100c0c0d03040c0c03022800c6650319070080102c1c03a1141d0b254585040041c2007041a9040401004440e0410f903500e43e0740a00c8144000c4400e440000d04ca060310f050050030050288035107900a0305100c240300900c035003182e00300a42043c95503100044491001e009032100028851840c007580c051109018034070704815403e0704060300307040005586640740e840d100e4061080322076a414506e851000c100251090343c1c62004c1c1105c84c07000d0a124503007680002c1182c001c6000c3c40c002c12001280000d2540110021503041918110042444550764a0010340329801240304a0000e81c1d003c0188100340010040300d004c3d40c038007602801c030a9643d90f88400080c200207103601100c0d5940d400003405a05c5152030700d4903030084 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 455825395 1250 455824145 455824151
    0x13050a0203070e18010b100c052a03100b030307081c1a090a0903020a0b09011e15170c01140918010609120305040e1015030209030c0a12060b06040b0409 67
    0x2160101c44c04072000c140121000b41d060000c02c0b4a25a0b42c1031a900301c50220382050002c12046003042c03423410104041d04503000c41c4041000ea04001c01410b0802400d10807012103624800ca522448241c035040c0c2541609684107004010000c0d604002520090150703040000481040344c031454242c84a0b414040c0341c2c80707001c0d0050041d0b070401105280d40031035040c4050058000550307000350307604c5403494003130b0002c18800b010034240e00c401e412000b00444411049060303503411080800090101c900c01c03000c441e211540004004503d098001000c0517880301805004404800544034100351101c44040d5080030010449150b49541105000e0080224641010342c1801400303800d9041c01d4000100d1800541a80340009502004503030698040c030100e001d46417241c02c3c6e50403110085400a210140383c028000030b8071035041d03018100c840012802c483c414030080d0b007400028080c5001d0f80801042e845542408501c1ca5004014060400b0b42424540365440c0d21000c0e640e0403503004207102c252 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 455826645 1250 455825395 455825401
    0x215011202040b090c0706050405030405030f0c0a06111504030302041a0903060f130807080c060c0d1a0a030b060d060606030b0102100b0a0e1b040314160b0313050a0203070e 76
    0x7800e103c2c10a00c01825245024076090031294003560340542540104130503143c100140401c8418000c0d0380040201800b100c0d402000e0300403058845e0040c01c601030140340650320018a440c822006080800c62050281c4855060f9449217041d0110062003a4140741d004c000000e500f04a44804030310210b120b184a0740c41d00b000c9400c26080200c050481350701030030b5100c28081c81c0031450701e1540a0584c011aa6175030b8201d140b40450300d40c023409508200502944003006108204d0a00400c10141610b9042003100c03400f054a070404000c00c03200341c0c1c010451810a10008203400d02464101c9401001c041110b111961014261a42508880006a20f555800d10a5601000000c00301e2208140c00d0008055000100e50702d480d452241c4c00c44882a103010500c907101c00c883d00000c81840050080c3d40e59100d0400c990150701401c0d200c020b500c00c040f000c03141c4003040c121040c00c0e901e007d8882c0d0300c0e64681503183c03442c1a104032001d54542c001c40b4a1400103980c10031000005000d92691400180f03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 455827895 1250 455826645 455826649
    0x307030e1e031203061311220e15031002071a1f03050d140403020f010c020105040e160f05072a0f080106090c0212041a07050102130302040b0105070209160215011202 73
    0x40036940d24840d48904001d841c0c195186940141c0b007105001a159000522042412342c14008042d170102c440c00c480801486050604c0c2d0741d110204910a904590a00b03000d10103103c101d104012003d00321400e4a007560070080b082d0640641c10941c0c0300008a02d80031201c50100c140c0380c6560080340c127548000c0000e580c158206043c00401d80041400721304080c556008140070400a6249504004003051030b07404682c0030714180e4010b042c01c0350020381030780fa1402c10f01c01c170f260f15904020046112a40c052070001c0c4201d01b21005d403a07002820035214026540342100e09482490041c42c01e00352000701161800d2000074030300051010301c00101310145495200800c4850440b45001150031407643c016811511504a034211600200742458918450360700342c0141c0290382c0014959400003a014503188045618007041e28000ca8082006200110040d41c8900c0380d408000c1d04840d481000032808002c0f00a042c01484983c0150340d807a101c442201d90490901b6001042003e18200d041c100358 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 455829145 1250 455827895 455827909
    0x23151602010810030b0609090f0601030809091b0d1505060a020601170c0a18110412050607180b0f130602071a0f1909090c09090e0307030e1e03120306 66
    0x301c40700c40c080d0f19140b801c43e2a400b01342e007002490203010b003020340045280d201c1d08001070004094054159070390355840e031421400c207901c020783c614858804030001c10800644007a20350715011105e03200b2840c040f0a40300c0170001e4140c10200e031000e0300070700200050685070040140020300955024181300d6040071142100c0303600d40140050b0580c0300d8204041030782c075003148202c10b80341c0c6800300070701c0020081c0725900075280e0601c1464181c42d011074002591415100729282603446070060390301c660369000b8100e49420b000601d441c100045400100076076401c5000401c00481e0040c0c0e0a880d001000640d480d000c5065406480140c1c8440800c1050b5070400c0e9000303117440c0c036502c940751410f8a2a5640740c030724020002074115444007504100b0089024410034001045035945c103100000c680f0700003909400003880764046241c10304c5c0c4500c02c00c00307012084491160341500c50240d00c00c4088140300c410030940645603100b008000c0003240903601000706100e1400c0344204640d40b441c08a06008003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 455830395 1250 455829145 455829151
    0x3060c1201091109010c1b1502010f15060c050a0c0e0105180606091c06152d06080606130e1501020d0903030e0114030901050405010e07231516020108 66
    0x2814508000f49081e4100441102c2c550002480c002e2421035650603c009000d1801e444266114803103c0006084d914076200c03d49000d82d2038008004500d003000b03420302604c0307016a08075039051030341c0b40c103010180c0a0361161540034007030700407240d001540d65203e0502d001142c12030803540b08404010070461904c5d111400102c6a002604055400c0c840c2c040b8603240a00c0e0001440303240e00140e040701071100c84d50b1000e01c03e90446014800c04041c4541039031415024000d801c0c00f1944010707602c40c24250700700c0040d00c011000c2042903180f46002d10864542001612055001d841001499001e442200890b00503002009541c1a0390414001e002c0039050101e41035815074011110701911250880030110440303030035040c04d20119101500495603d1000802c903c11420f020050100d01641540a90700c5a403064008001300c4030340c90410356440000703200d5222b903034960003515000c081070310f81c0072040000f018005c542ca40d152031040ea601e03a00010221400d020b0043c114000390b6074000081a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 455831645 1250 455830395 455830409
    0x9030715080c0d0902040c110d05070201050d1a0d141615031d0a0f3e2202070c24050708070212070806010b0f03061e03060c1201 57
    0xc05a90521000303404114000e00c1c490441c04045425260f4001c107401901e61998000d100300000100120043c0400c0b541031401e42c82071294482c1c40c00e056005d9400c0b5010746405071070701800c2c81c2c0c3c6018541c0161000c46598910340c512403440384a0b60701c0d00309142d905940b080903855940845403c001c1d2034801c0405010f101c0d001101001c03c890203000c100390800c10361900d4082005c410341c41e01180f83c580f200506000600c909080c03d000d000c0300c010702c1002c207485000214001844c0b039050320100d91450031140c43c0001407a0f40b04180a100c104184400200603142e0000c441c8110b0501000c06409011041616000500d400c10030802d0700404001c4c00c003900a45110802610400030030103001500b403403d1000007d080307010710541071b054852181d03000708101d14050460502d6a142e040b20710888499100745400418040c07904000d0b00c0901d030b255003c5500710360340c00003046004640c1448001c1c884d01032018a280c08e44050000368030401d80e1848003a503c201c213040c000e1520318160f100d41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 455832895 1250 455831645 455831669
    0xd0b0a0302010c0b0402010309080f0406031b021c020705220b0a03030807050f1312021e010804150f0609020c1005060f060306060408060703090c0608070906050d180503090307 77
    0x3000503078200c0a5075008503004041c0d02e400d903403148010ba000345070520001d400b2841c00b1503400003015100d8002c0007a00c19595043c0040000d1210441041c00214804000358010001150700c28480c0a0644451444c0313104840c1d026030b8034004a9100c1407520b140125900002d0350500400165000d1007548020684001c0360241ca10780380107201d9400074007803e04000000403681881045101526410a0003c0742810311903600c0840d440d07031785101c84040340070711444255180081c0581c0c10b0b200c45201e042c3c44040300c907030711030303480c0c40d00120310080d161806541d845146941d0982c0f440342c580a4511060010307540c10f681548186040c4a100204001d40d00309420865103844201c00c0f00701d201025030741ea903220344901c4001101400b070380c5c02100307a605c22401042000355040d00800d1020303016404d503010864450717900b216001c0040756010082440d041d07042115501c5980200014002098002080b07004d0580d03680d00021101001e43c0c0d9980046805255450148030000c0207200c00c59600f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 455834145 1250 455832895 455832899
    0x607090e0f18010e010f090b010f1409060d0b100806090f100c050f03090d1407020d03080402030709180c141c030e09040803150604140409061803050d0b0a 68
    0x8480798140c010010107200304280003442e4100d80940120035820342c84030003070022083c0349140c2c000509105c08103075041800d01b400041c2905900340e000043d2580c164140044040d494103004541d8805800b06410030030a01448012503200d056440c0142c4075850500d4030b007454045031901e441000b600011850f0881071420042850001340c0154051040c8030100709800942c406a5113405032407048840382000004002c440304d070204030002414800d1b01e07007541c44490030094203503601445000a40040c90560900042402040641c0c0d02500c010101d4402d552a078505405648401c0e0718102c407075040d107050310b00b0020414230380400340005030300180305000010001110003207404000801200b000d4900d0060504c9450044a00100503060342101e08051800070031652084421480043c01c6000e1407417a45014030445044518800d8403d0320b00b8906010000207107c42807048580c1907a540b090f038805c50304040003a01c1d20b0f000303482c0c2948070a0994810420340381c2d20400710307105103402401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 455835395 1250 455834145 455834161
    0xc150c12090c1504170703030801030308040f120c03030f05041a040f05010c08070329040f02040509010305061905060916110105011e0e151215090607090e 68
    0x29211100000340c5840660340700d0140c1203051204402c94983c00211240302684080040c02c0100b0440d0700e14561096a241c020041c50b8948040380001000034184100410110b032042e0455030700706000321200e00e2032000641e100d151400308201b0a601051849110713506154040c415042054078080003800b0600d00b5a681d01d070140c0c80250303601d1490448901040c10301085444404440b54000001c120341461944040c11890045824900107400e00c080c2d5003510031070f4180b041c285028a40071501001c0d50784104000351400080c012501e130750034880000e844c0d4034101070a00860141c00981002e06180010141c042d90448002200909000902480d40c445c1c0034400e41c41210301b1410f09024915003c104c07040714000c6c1c8966125800c1c400040380c503106491141051900764440381540681d204081d083c4000d00b2528a1502055401107000030b040951001042d048041c0990303082900c21446a420b0b58426644a0a2580b1000400c402180c022500f440a80001d005d990380c503242c1924 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 455836645 1250 455835395 455835397
    0xb0f09010b0307120504061509150b0c1207081b030a020a03030903050408060f010501030e010c0507020f0411120105150c0a1103011805031c0902030d08090a02090a020c150c 76
    0x20400705a9040000000c0d0724a21812044581064a9800780124246814100040c210080054490300d00c41000010624194480c0f103902e41401c0030041c2556142c4a65900c01c0d8114442004143c0074040c0e280460900c401e0080c83d41a1084802684865600d94011010b0001a114096035402040078600302500060302d9030a03150301d0314000c01d6454076841c00b15050b008030f03405240548a41c0301404918441c0030341b50fa05a40d000c0c1c1e02003042e40c9c0100344040c00d0311006490a00810342c204a5000517091841e242144040044c002041344040900c1c00d028030707030041d164940078090400041c40350b071416a040d4080c103004800814202030110060341d80720b001c40c00c801405185540410040b42e28203410060302150125078401c1500064206103450364080401500c00c0030035020401c0381c1e0f446a00c2808078580d0068024950741e5040002540c070030030b02904040c1180b00702d5031928010b80d104503040d4811039032544090303111078000c3d2841d454a502c10000d004413200507005c01c41e0b4145020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 455837895 1250 455836645 455836649
    0x40f270612080a03090204020c010e160f1404060b0f04170a02090f060a05060f0904140106020304030311010b060304030e030c0d0b150114120405160f150e0a15030b0f0901 75
    0x882007590fa024840e500b50001e004160b002504030740086108010940d065010500310510740c01501d043e00c1030640c4034140b152440c0100410f00254260a00c041c154548105001d900003500000f09580c54242138000b54000d14801120705c0000101448000420000c483c03030142508024000b680d0a42d00281c24200024114804040d2210000351181c0d00d0b150608010000a441c20f956480c0b030f200140ca0603805007a0303282c051414078a90b980c4e00701c4290581812110581d000c0c40c01d10303080d660201c13800c155103640c8400540d01c4031401c4000d942c4040055000e18401d4680500c09006007042c0341c203280007181528450f05840302a100840da20301605980100e090000b00a00caa1500050307620039400c0c8116103c801001c07030401805008590b40900480c0582d00b110310b2805640c019000399051809081035204901004004110701516002440302403402e120000c20000390104021a50540c40041c0510714507107007154407a058411900249002d42c0c0c24036640c9141e50115405007018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 455839145 1250 455837895 455837903
    0x201050403021b041b020705181e061206011e150801060f091206090203120f09041508030a0915020106080316050307140703030201051305061605040f270612 69
    0x3000d10f03406a83e440b40e01c075404c1c04440034a620401044920020b544e00100d006440c056100404200844011300785000d1040c0344510310001c000205842005460502421745504922400304010428809000c202d01a0982c080c50307940203d00100c2460350090030781d0001c0c280e40500c01480001030f83c424001c0341900c40340c1c00c10060481c410401210300c1c030307501d9026440050646560304100900c81d00002d01c2c1900071821100c0380c8400c0c1075441243d01c00e003210104807203004c018150301750805030081c1d500c02c1c1c054400d4200305a5543d104905680c002884a00040c3c62032034140319044100e42e280b4843d10380c3c1d10007008620305061107141d9a21903403c020341310080141c25402040f20070412104490760180c00e09114000810416a442001d400308a0141d420071002030403c43c1c1030040d03003d5044c0c00c900105065251103540d48034500481401c0010030008000125040205007114802040700749820b4003200f14602a940385203910420208150303041c40740400442d9590319480d43c3c06904 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 455840395 1250 455839145 455839183
    0x203061006020a0f0201090906080601030539130509030a02010f05060f0607111c03020d050a0801090507090e0c1206030a1a0903070f0b060907090b18180f070f020105040302 76
    0x40c0c00161500900e0303034881c0d40030700d0802700c000c1082c22001c5030300c504030b9108100311034601c0c00e188241031030126030501c0ba14500008081810308444090f405020b68000904140c0314030100340117142c00d84000700d502c491070350300c00a00e0000c2c140c1c1c240306040345010305070002c00690601e0b500150210a220280c24440d4102080010900a00300f1102a0001c4024803c0c00402a0752603000f83e003808100c416405400f6910804948500946c101e0707041d045d0b59511810640c0c01c010031031000b8080904101c0800c140301101081e2074603400b0b1002c1c000c0c00c0c0c01803015201c102103144141a20030040046000c0d07001985130324001030b202c17012102c1c11074805052a42c0d9a65990280b40365000f00c00c805050640360600c46414403a81c1d20384640900380659401c1515a503440042d5003040c254030070440800740400c0400c40c0c0c0d000010028100207001081000f101d481c1c0c1d5004600340f88187c5101001598000a111409810034010320a452007030000340030780d1034141ca003e0b4a4000980ea03500d105d000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 455841645 1250 455840395 455840423
    0x105120d1e090e10032105070201050a0315230102010b0609040e1c09181e050702031e09031c05071b05030a1401050a02090d060902060408030f03040203061006020a 72
    0x10040002d01c0c00b5285000c00d80c00180390070520101e0709041440244e408403000d54129007600c4110011034000d0550792945071512119a004503070a5000b5103005d000c15645a00800f036600503192064000d09029003540e040c11103264218105003801c00900d4103582c0342c00ca41d00703071584403502908c40d001c100f280c1c00940740d5040641941070111100307040c042c15205c0070b5010180f03604a0031413025900701d0609041c0510302040c0c440300300c4180c0000e26100500c41c0c110b042c0901d586411070b036804400391066a060815443c2030004010702e440d204d028850303010070200b440c2d00b0b0400c062500c42114000c1c2e94841c030b01005024005205564000c1c024940b40c840c80742c81e159032129010000c0c44090122030711104a4281151034011a0100c1841d40d401d1001156a40d0014004d680f40d1200c01000c02c1000286a9034000003031400340800c98000e24184400203615000b44040c140d10707408402d51560768a40340c4109800c00000800310444d4140141d410301804e45c2c00640d07120b6240d84441d0000da844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 455842895 1250 455841645 455841647
    0x2270a0e19180302010213060905010e040c09050607030e28120206070210030b030d080106050f03060d0c12030801060302041428060309020310050702031c0905060f0105120d1e 77
    0x80004644050880d0b0700c1e4100c07204040d03055004060a940c4113031091043c58035000101e4030a081480307494006003007400000c2d039074a884c2d03001004d00c1c102820700f01907095880000c213210342c014010a4020a0448800300814100f960707600c1d4a90f5140301002c3c117080400045101d07000898055081c12202e10020441107456000c111181d040c0c008110038880c0500d03641c010094200d01500a010307014400c82046618040e00d80c65041e1401da80300c0d02c0c00c000403204d030003055400c010411948010b500c0c0c0c20320f01041e01c0e0100382016028910b07444200401c1c90402614514040e030020381003501c100300030088041e403000b00d214080c0301111010304d82c2d2a0240700c4005210200c01e482d411440380701c40020100e030540e101c4806a0b00c2502030b40c1c209501c03c0f0010044031801c480e00d00c09a00100030722075116000356441400c01c0c90f000400640300b14291140c929001c4112440103000c0030940c014002ca1525490600e406007a81006010380307841c0001c028512030545454020124001c03162105071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 455844145 1250 455842895 455842901
    0xc1b05030d050c07151e020703090b0d0204030308100602100504020d060e03040501030605040b09010e04030207080a060510080a0f03050901090306050a0c14070506060f06070602270a0e19 82
    0x81c0919009000c182080c5990183e03d520010080b030f41c0800d4044240c2c9000c0460003062078074600c080404484050040018000e5403103224110304200d4241c0020500650b84405058001c0c3c102200580301e82c110300c1c01503c000009000c08100b884e0410b020401c0c00d500043d11000c0703c54014012400b0380741c40c40803444403078100b5002001e036400c000c1c1003616070070000064401c0714000d903800d00c6442c0e81c030010302048950036034801c0c1d08204000c0060220242c00c40c039103038000380300b48100d46410380e961000da414007106040440b0341c50b854005005e00329078001d42e070001525064018118620b0642e80d400204103418070001c003480f1000c110100b45a0103010b0100066802503000d0081d40380861036080181562200400420f0b000220740d4860f599010a40e00600d40c40001080d00340c640318104440794a1150400b60b00c40810030500001805a0028112804082c01e201010301c1c54486030514480d2411005400b40d4012041082000e080440c0c1c2078000e0451000700d455000b07070b843c0b00009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 455845395 1250 455844145 455844157
    0x100e0306040f03090603060b090402070c0503030f07210c060c0909020c10061d0406051b0a080f09031305060c0703020a06170108060c07081b0607020a03020601090c1b0503 75
    0x10500600082100b44500410308280322440703540c0f4108095107904007a0304548050150011082040c009201d0900f02503004180c0030703000f5040c000e80300d03580348006403441c5c0c032010820307800e8031000c0b41c002d0400c203091540d00005900250004026080d40340d00810300c40d07c020b0090300040c2c0342c1e15603441d880c0c02000c2400261207002d0081d9035403008000302640d00c40c1807c8502e08564903080340091190320201203240c0080380c0304000000d5031a43e494100c05804050600c444483c41c400d084150b42c024440101035000e100e448184140c600803d0041701490300610201440d0010441c0d40d072003003080c2e490f140039120216886520b480807140000e140c0203c5800c02904400e8010000c141990000c5103440250492104001c41b40e03243c0701d103191075070b106a41e0014441c0c01404001d002841803809000100c01448441c2400100c0c60744a07031900c1c405803a0b10300581c00c9651a0f0b800e041d81800300c68050000d1840a01c03044480c540b00a11040c291000411030414008041082100a10480c0c038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 455846645 1250 455845395 455845399
    0x1020703151a06030c0a08011a07080d060b0d2921030702040609060e0c04061b0f060614153108060a0516020a0201090e131502030406061e05100e 64
    0x14403171400300c3d09251103600440e1554040348040000117081214865040d21005458000a040503040c3d65000c259810451091500e9a181d103800320740074020300301421742d204444601003203078107109010081001e501c05007d10011154000c96046440745180b0080449422580840c400c061802c40c50a600540b403001794401c0c140040050180c10fa9001035040c4d031024000e00307080d80c460b0440444a4404d0b071080303902052440d040044ca0200d031282d41c9510300d010f0496104191210343ea0340c0304540391031308404031000700040c00154600b0400c1c016403c4a6603051094582483d001d1000b42000003010300720216003060308500400c070359003d0208014248041107031340d81e05009029070040c2c501112242400c0500c0c0e200c0c651094400282c403500c26406845030040780d07007814500312010100400481c1410388529400000682c00210704a40a04011005840f400e0a00c2e01c1019542c1c240d10280c00358036152421214152280008402c8941c1240e4031250800411425218902411101d41d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 455847895 1250 455846645 455846647
    0x2018071b05060f07050703020706080601260a05100812070303020c0f010b090f0403120b15070602030f0105060405010801060806030c120a02010f1b170d06061d01020703151a06 77
    0x3400700400016078500400c038600310030840c0c2d590042c040341d190040010140040e440320004206c803d0044040c01d42105043c0b52a0380910b4042c990b1038540c1c804442c1c3e14107a41038140800000349514480c00b0303007100381c141400c10894a07044542d55502c181d04144032940380c0000310402050700950440d00a00c2070441a03130540d24032101c1160003050310315200c0c1d0040e602e240016a07032101810300d0380d204030b500d5150200001080200034000707020f008011900814440e041074000a039a06c00f03088458170403040907940b49400d00305c0c0c2c0100c1006070f210078001d150611091003542c0e01b01e8942d505440e00c600c2c008400ba5203010001e0f2038285120300c41600040119148014040c003c075070088800d0003038031451800c951400b411204070034810546440b903803031442104001034119064815640c03501c030103581400c0c3c503010300500b121040d40c13012010500c40f15041825010039120354081030402d0024000240ca103494000d0380d100c0403234002d01c2443c0d5411103001d400d41110414003800768040d00302 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 455849145 1250 455847895 455847947
    0x10c080c0a21390804080c04022a0a08030117010e070b0f0a03020d020f0a2c010e0d1506061103120a0e0f0607050904060f081e030c19201807 62
    0xb25003940d0090103004030340c0c06100740107ca28200390085034800c0440350810403440c22860044046602030500c0700120380140c040a20102d000c400285018041c07139440c3c111020500103200d400c540001d5003a814641041d0303c1000307100102c9060f5140c181c003d12070f203503540c0580c0c14118001c0c800c403021403034406e20110303080c2e200c0d00d00707003000c0c1254045984400301001a840599200e40141e580cc50150340e864890100c90b65200e11030034595014090900303014102241e070b89c411207081c0042d43c0d20000e581c50004103c201e9020300044508443c000c085c46c98151003482e03041940ca030042c10848403503211281981c02c110108000c1144d0110441660780c82e0030000382c020300070380c000c0760310364030071814034001198030003450860304c080b40c1000300100000010150b40f00603054091041400783e01007800407070b00b41041444801d21160190490000c81040c5241c0700111509040003451304500070700c0c2042c15511101a008401d411705e001d440029910000d0071114499406482c8440d40301d92550 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 455850395 1250 455849145 455849153
    0x90f0d0503030c03060112060f15080f19021204140610032a0b070f0b01090b031e070503070303020f0d110c040b03010f020a11070611030a0e010c080c0a2139 69
    0x220200350ba400c0d040c42c0503c0c050188044074000b00a40c0c0f645d070102c02101c0820162014501030381d214074a0f100d005070a01d54503f00000620000b2076040d142c8407841e0423740720071841030000350307807058084070f01d0402a8203644486030050400c0000440303240704a080c1503031150041c07072481c00500385900182c3da9680b83d4581400740040300142118074007010030012810b0040d9019146105402a00806880b400b041c0d055032800d09441e5110306a001d80e10f03000c15503031414840200914000c0d0000e01001c0c000724010343c0360010f0418150100103880b002e034100d1032000b05003144d0301c1c1021180130550b4100780e00000d00600b16140d144442901c00203d100d10760360003041c001c18a01000041d60780c2c4c02d540340c4041c5d840c94403021500c5c0b1190401c0004002c2d643c0240d125000b4420107140103014110700b0303521102241d0180e00d02e0304660384001d003d04200260b40701040c0118400821a150321054041c001d80085c900040403603441c48002c14082030401c0b0000c4500c6110034003030351440084030500f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 455851645 1250 455850395 455850419
    0x306060305010e0d031b0806040e0d08070f0816050307030e030a090609090203040218150621070207050109121104180c0b0f0403171e090f0d0503030c0306011206 71
    0x602c0d01111300614180c4c1c58014000c1c800c008002000029500310103540c80001c40e80d00000402a0764000d0781d46a941c106010204001072600b101d40d2601c10050400c117801410032980b4a820004012034001045039507051030301120304019080c02c0c0b481d02e80c6c69550741076003e00641404500184000310b02603102d90f61107002402154031a80f5a064200d07201d203918010380c4000c5030060740120400030400104030400d0689680040101000d6180244000001d410384d401250044042005c070a200226000d500c000c0c950810101e000500d0300520381400640028890300c24500c1e0b081d09035148000f8410084203d403803451000f1300401c04188440c00c502c03408029210141c1c0c05841600001c10200286821141c05a40d02c007061414149141c2e540352004074550306419501c28180110140c00d0020030b17400f03601c1d101c0131580304d442e580064140200080b041441070320458540d14506c01203240031003104e82101030081280c1d034070ba9a0f8001078448030720211401800924100b030004000048113 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 455852895 1250 455851645 455851661
    0x1a16050a061a1008092d01060303020c010e06120105090a060f03120809030309062205030d0902190b030c0705011d0609070b07021c1113020310080109080403030c030207030606030501 80
    0x441d101e01c2034072003d004840c004030803501c403000e990107911062441d42c1e18107000380b200070114240c000300c060714081003801d41e00580d00031409a4005c0a0050f00d035a0400c0c1c0c080401d12007a0369a40c1080380c2442d81410301e06c418403e00340181000c202081001106421a10207890b01d0403408050941c0c0f0300c0c003100240e810039034540c00104d8420100350145400300449002e010801b0081c0110380301ca1100e540e4030301c03a00014105401c0c00c22800800140103001030440700ba0030000018050184c0c0c014802210031140051600701d081a8007440420180e1056070b0b042490007400f40d1310780c241c0d07141417401480c00c0950082d02c00004461920032070400070b48036110b040c0c44025505602d43c1e40e08807071000d018440e0001d40c81021000b1402c0300903003074203a40038281d001c0c045002060403100041a8030131500428425026000020083c490039a002500010140d80e4000c0001c0790868a40b441c0a0085000040800002c00000307030906200f00150405036030004420880c155891030400e008089070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 455854145 1250 455852895 455852899
    0x615171b030f07031b030c0801020c010c09260106030f050a030225090509120301090c0e100e09090c061602030c0f03100c09030501090602030702071a16050a061a 71
    0x3603118555040200d5440304008164009110071815640e0301001c80d0303041d1003a05011800058004041a107203040c640c010b0000100059a920809182c2c500356001e0544100c2400148882045408507100643c85000c83c80044c4103150540302590301d0240c4a107078000380c0f0b030801c051914010b02002240506c2101d20940848140d05440044070440d010000a007003010340c80c92104210203440c5e508416400a1018207980200c0400c1c520201203030401e030802305101d982c9075000c140160700030703070b6184600c40221000701800004a1000f0310b09500c86040c1da00078084a00800c607588000c000d05038000344020800c1d5241e00c14051085440310103010180d00c0703840b40f081d00d1071036401c0150854407440f80c041d001d001e05003914a104030103808841e920508000c050308000010503020310851031010f101e5000982d89007070802c4000d00c1c0034510703042084466074080c80384100e011148100c42d418044041100340c2400617040450a082c02a03001070490342c01c01c8120203480144002e60782800f102 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 455855395 1250 455854145 455854183
    0x6050f010801091106030a0902090405160603020f030103081b0303072606010c020f12060c07030809190201030f021c0b1e030a0b040807020604060e040b10050304061517 74
    0xe01c1450500ba2280ca00001c2d007000320815914007582040d80c000c2d68881420300001c84d051040b98041001a0411581a103654001d4404ca61411103100070980003851645025420160704128203001c0f07100c10301c4001c165041c0001e1195411441d001707000c0d01d961058090380d48038a42100c0107001040e1460380c00208a50005170400c2c00c00025000341d009050694a04035126502d900b840b009001d06401c080e403010146481e03030300305982006014410401c8403940da44400a80c5805082c4880162400d04603800685621184401840d000049550240b0340820801100f40c2514003d1003906440d41c12079604030141d40c8030a4250f0007410740000e059400a0148a503008808504a007076036002e541034000401d00b5000c61444001d00b60080d0140c0001d920300026940040c00d9544145e128a010440c0c10300c1c1c0d2040f078905131140c40c0320f9510a0742c04900c280580b0070001c086210080000f44415903c0c0b440c40f60fa2048000400c02600341c40d2802c0b090110417295003560303020303a51008605510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 455856645 1250 455855395 455855399
    0x70801060b04140f030c0402041409070207030f0f110a031b05221a040203070215090a0305070308180102130905130209010501050a03020c03120711010606020309010311041206050f01 80
    0x81c4420499084030b2620144090300012601002540c0703901825096140c03283ca426108030395101d2000300002e01f903e0114103c50000d03202848200140188001c0664000300000c1003c9000c554401c0380c0750358072040e40c5144011610744800c2c4104442c0c00349401034040703c00481001001c000b00e0000400696000d021259940704101d84030401d007101ea0101420301135040118251078001c4c03c60424400071b0009900311510104040780c0003110020700603400700c480180049040016150444a0304010b0008800c1544001d801807055500003010026039900050300a22005d0400b0302041e40f04000350b5961161681030000d022150082800d15841c00c00420a40303400c20841c0e4001c19070142001c21280c0c40c140056441360040c0c8280018180c0070400302c8101c000510040c4403e031000f2100600900342004010302002900e0310900030b6078901141070000755000400e448904c0000d10740880d8507603210906c200b8600581e40041a10f014680c40e940412280b41c000c148158600407540c0e400360f07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 455857895 1250 455856645 455856659
    0x1107030b1f05010905060c0709090c0e0a020a08040807020f0907020714060301120204150b0f030a060b0c101d01050a02040816060903060c030e060403110105060402040609050d0f0c0807080106 84
    0x2110382c0c811640410741c01c18081201d070401d000600b03200f0640a090305c40c02c030713900c141ca44299403c5402c12500104d0342403092040910480a82d50400c2519204500f80001c1c05000b620150300504041c241e00d0300401e00b5030840d540e14500d1010b000e0301401c03500c0c01e801c0014002e5a074000c140510350014030002c180000c141000e00590b8100c0300396100d50444075103030350280002002240c0032002c004a40d40340100d14840a500288100c4021248180e0340f4608a218002100d080360132840c60b0020401c130032142e0802c0010030140c0c004a602c2c002500382022910320b05d60b100e0740603498081d5400c1504001c0350348801d82c00703041181c10090036601c400c0380051000ca02e903110760062802003403440b00180003240c241d6100504640701030400044042074209101e14007141150110009400d0300010041c1410a024080e041a000c0c0c4041d824030b03040800c05480300d81c543c0030f86d60088480d4000c8805210400b00700401550b000581d0440e915221920356807600c80760300511000390b0820303030005980 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 455859145 1250 455857895 455857951
    0x901121b2c030a140102090d03020d0215060f12100e0703020f0105040b04090c030b061603020106140f12240708060a0612020306010201060905010603090c0b030f060d031107030b 78
    0x2407000103020f0400c2e400982d5440b40e0042ca41d180300181c9660921250019450300a0259045806038005110008a0b180028a00312031030701d00510b90343d0f0b000203010741a00c0301070100c280524202c84422101607626045807601e058142d0014525091504001c10858045042804c0d0703402503440004842130000103441a204621034030320402c8042104200441c0143d022202c035103128900400c181e410080040c049810400c0856003004521000e40101a024440c01009100000c0c89a4400b1100300c00100c5010002401034000c040e09071001c29412401c2c000f5140d1211212445800c07540f02500302d000d02e0070221542004a200007021507110714103600c0d48812140301d603403000b0861540d04400d202942002d04a50705541d03c44402240800141c00350b14082c1c0741c280d40000c0d9a01d018140400709040070392014075481000c00900440121402020398002030548004d52400351034901210b001040d240100d0b4140103a80c804410030a10030301860064901840c040510b4121440040c90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 455860395 1250 455859145 455859227
    0x40f0e01090c1b03140403121107080705060903150a02030712021314120109110a0f140d030c050304030503071101030209030c120f1506150703050901121b 68
    0x320f424a0003d03a201a45101c4000c0800d20030728200d07118100200c20318030a03400c203400882e031005540c22525085903101c1d20184481c805180184603440c40d0001e541c1d2501d8690080d54000c080003d9031031615182005110602071611160b031103a8603011500200030742094030640c001a403880481141d82419009481805040300d003800d14641c50182d03240d42c1044180261608025112038010310700c3c000380304148490b8000c0d03000090b1128424104001010746811005014900c0c038010700207404a005803400b1207005440c0c2030450003160170191651040d0381c100804600c000038007c8108040070000c0c0c02440c1c85441c207900c02180080c015000c2e40074001800c4e406511030600c0100d00d1900070000e07041c0000000981c4d203043c07c0811000c0c02e05071400703414101c10300e0b010240400c0e4100412850701c003174803004106081078165900182244520405607040011a4800504101e01c581c4038004421b45a0640d48050014901c00380100b00c6000c407005842c104140c070510010000101915 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 455861645 1250 455860395 455860397
    0x30c030304150b012c01030902060706060305070b0403080f0a02030f04030f06060b1602220903030b0f010f09120804150807080a0b280909301e0212040f0e01090c 71
    0x220b01c2d41c2e04205c108400c96031052a41011b494002d403c0142c1c4400e40141581400b031072020901c070741182401850040315a101c0348480c8010081000800c00c076a054503001c000098041d592001c04031001c80c0b85018006011411900000c8d0000030000c911255440442c41841c003800000d0703485008004a0282c210102c040301d801c05032400042c609111130004641100032005420306046541030700725402100c1c1140402e0b9100412071903490107403210710780740c0c600740390111990809450040218030b1a10904000c0078040e0f04240030400d090007a1400340604240b02004040c4050000b00070803001d542d803030702103206a00481c11203600c6014407000e140b000350024501c5003000c8042603c44913506108074014603d14004546807805000362214140504510b4420055200700100c08050501c1d204540102e81c0d2038184025070400d0f505102c10381c42d1140130b00791049030310b82a07040c40c040c18140c46507400001008521032003242c6107001a1080041603001e10380e00c4254140486400b01c100c3d030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 455862895 1250 455861645 455861687
    0x60504090f12021f02070c090203130b25030c031a03210403060e03041508010602122118010b040203040b0f04080d050a0f05070309020d02040e030c030304150b01 71
    0xc0202c0d0701c040e40c0c2c00496007903104035902c1c416104d05100c20b003042065842c5410743c002505406000c111400b04010b00b1a0000440c51400c011070701d00701c1d021802c0380041030001c80500140e60440c0091003a07200300044148004440c91026000740101380f00300ca0746c00800d14284102c1c140c036807050100c08500a01400821964820200b12210b03080048440d00c0e07e428100b0021002075200d014000d002c2e958100210345580c100384000c008482c41400960802070860010002a68009414540b0000f00b4058590f02c8142a0241220075499072a010315041302d8400d201140c000c8202c40a032113641900204a039113a00000c02041c2c0c0300548014143c51b600300046104000302481d0203030403038410040141b034621400b561405036403045500b0140c440ea600030382c4e0000c601501807a030780118903280c204103644060f400220000036201d000b81c01241e40341c1c0501c01c016001c00032034081e203049804698907441e0600d4400c0491412180908110b42801800c2c480c81d406140e12141c0c80348070841741 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 455864145 1250 455862895 455862923
    0xd11030403112a0a120f0209010e040f060f09140708120c030910170a02030f01091413030e030a0b040510060b03131a07050702031606051b010e0609030d06050409 71
    0x4060061914444540c00340b101c000000380769103150b441700300302841034022000c004028010480f04060590040088035031210400c00041d4100909401142d80940c000030040e517a030845400030000103000500c2c80140d144809100140040c0c141c00b2941440229403002e46c1c084a07082072401501d5a00810703910610400c80149440440c070b140c0c0a60501d003041d001103408003090400d50017941c054481607400000d010154040e01501400b61100e0704c4280100700080200541c5c03000e000f440b1101805803c409013003054410785070415002c80003000c40c0d1100c80070341081100c111050300c0c21a07440c41118030b004581841c60298004a80340b5500d8107086607541c0c4852000f441400c04100c2d402d030003050507000010010b51010f400381c0355aa580365100c1c0301c14810b00d894450454500c1d410314814860030440154480e040f21171054151010410b026a0301a08500ad0409010420301c0343c0120020441c594800001a00180c01a01010301031140d464062100b100d02d07811000d09101ea0682c84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 455865395 1250 455864145 455864203
    0x7030209240f01020309211509010c0e0d080a0c060c11160f05010c0305071b0312030e2802040e06091c0206040209090c0a0303030609060807051e060d1103040311 71
    0x101400147d4203078044107a0010201410b42001c0b441030201d000c089100e0107001010380309100d46045203841d82485031445c0340f504006410f6101183d00101007503000100701030080d1240301403603c0d095000c4030074094506084030150040c218000c5048051003030510b03115911880445c01c0040728030000c40f10941c1800c040c01194448000c1d001034090041c10130020300050500c5207501d80303018150015400150071460302e5400601d0484065042604000216100c95030109880a4041040555540d1100910003811200c5113094002e94000e15240d11840001c0012803c0c0d0710506803001a210703030820148200d0004012000484c005901080006006081a2940076004460f200845000202d507100062617040c803504110000f9444000c200902402401a00060305151010b40b81d641d09003000f0410741c088090440d885a045500b1610441d00c0d00c3c01190800e00040d80c0520051070140d15081d503942c03042e41c08400140340c801140025210105010303c034109210001c107640009411 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 455866645 1250 455865395 455865409
    0x260f031c02030105090f072105070e0301150b0c010905031908010509190903091707080105070516081b2a0a05031005060a17010f0506100c0b0907030209240f01020309 73
    0x81f140c1305101c5540b80701c018540c100c103496103060540c82404074a6140812005000c12902c02511340640c1c10140761204900c200395060301500d8180039940c0e140c0c0a510b00070f5015001c3c4500142441c000002c0111401182d071070700714040700c0c0c2c5458820050342e8502c188102d100d01260658102030440c00000d0200c1e0b00c68010201841c080c0c903004030503d480d408101c0862000b240b0020345940011000c01030f902c030078060150300c13180358140203013041c01d02c50000e072910030343c0f0301c00620404000a0725803808180c0c44855003600401e208881041018080610300404040e9040d000c0c07000c618404e44481c501aa40c220540748041d025040228030400f10002170030000e0700441d4072114045000c100216802e880280c3d1200c454004039056540d003c0100803a540a44068003504c000648294020782020128210aa100b1416001641c41808270360403c40c050304002e5100d240c1c0414490326580e1000b00f0121340505c0303070591883c206d40310f041150749a401d40105015030014030409802d490000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 455867895 1250 455866645 455866651
    0x109020d0212070201020702100906090308070f1a0103051603030905010507050705132702060406050307090b0414090f0f22020d1202070f080601260f031c02030105090f 74
    0x2000c05414401c1010841c40030150888030000182c1d4049038020551070000c0c0035040351402810310703010081c10500014040c00040c000a0041540098810108821071040700d4034140c1019540d0451414140d81c050200d100b888161904d102d6401c0c864121700016040d44101caa0544460342d4003031400c4015102500448420340305802441c00010301e584a80c000d40c641c4000798440002c9501d05426041d0342c02007940d0100c0f40d00281c00400900580b203c0c42168241c50190030701c603403203a854800840d400d043d40c0e00001011040410000b4400000001c0c42049201c2160454181c0d07544840c184082c060840b80c0100d000c1c0704e0030229402d018803129101243d40c408032271030051711054001c100754040d0f141c01101c8000007041c15010716503040c404a030140c082080390000f41881c0c81941c640d81c11042c001c0014001c03036880031801c171000c1d2216104114002c0c4064031541c4040403046610b81e04228104d003d11003200d02512110741340c510032203040c3e540040000c01e8a440e0000b00320b868800003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 455869145 1250 455867895 455867917
    0xa080f1c1106040b01051809030403020f03210d0c050c0a1104020c01063f0204050a1b0c1101020703031b0206120901091707020102250f0e0603060705090603010902 72
    0x141580032042501400b031644110700400d400c03055545030005114450fa1004007070300c1e0705009a802d2082840c004000c80b0304507601240e01207228a0408002820000128804101c00066840342041c00c1092030142160051483d4200100c6005420075260343c442c01e00003d8894001603140c82c00142003541805040902070801800c0284043d041401c548040c0c1209150700511010502c2407850301101003909110600045d400c0814524000c10b00003105100078030071510381001810170082c0e50f1100c0d005142c1c1ca2010000c0c1c010250002d00b101050410544001c1c40c200d0481c01b20b54000112002281e6060340c1c2c001d215060b10b4500701022088400c102d0f030090f82081460503800b408202103014542e018000120b4035040d01d4401004480d644004040000c148420000740c0c1c1c0204802c3c480181d405c40702080c8031140c1e141d680c401d11040e00102d2403103084100c04104800d0b40a84140305800030307400c40b01d0544076030a043e1010701840e000142d0140c1c0c108014800010a900980f00c0c031410 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 455870395 1250 455869145 455869157
    0x203040b072019020a061704061a09041208061e0d080f040b0c010f09032c09240a0b03010612020f0a0c0b15030d050a020c03070303030b0a080f1c 64
    0x30010a5007041e9640100e641c1180f01d0400400540c9002d1050000420b518140100d82643c0c1001e4a0848100180003800655442100850003008044200e0018100130aa804a4940340c40d00140c1d08120b010850002201140003550300c2c141110415a900b1074941030329004079030a8204147d4024004044440500c28441c00214104020240c0040c3c60504000760300c0d11002000b80342159605070400c9051801c050781000404d420100044680c094172039001c0103418075801c20110480a47e024980100003e802c00c44049007410441d000c808002c1d1000750900070040030010804518000d00310b42d17041c1000100700c1c1a00840b0b88140a4030202d03400740c10000b24031384c20045074006590704408610744005440800c031840c1d5842d07512900f0b0045076080714039403201003503580c09070030701030014082d0000d501e4a8080c0200071800540720000c08031060a91280b4000300941303011640280510a014400300d038040c008181011910382c20801802c84036180341d8483c040c06984200e503024065 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 455871645 1250 455870395 455870447
    0x913050c09040c050909030906091507170c070e0c090103200c03030411010c05250306110901030606050a051801120e011409010b0a030206030a0216061e0203040b07 72
    0x64034000e0a00c40c900407507803580f0307103481c0409010810030000c110840581041108209036555070003582c2c200c507402d41345251425800000f201041c441e4040203003800c0f610301c03000f640828600c0010000d24002c4405e072030950303954203810148000107807901d21000310700b4000002107521035482805000d5030240d080a11600000901201d81d00072038420010b90000003c01c403c0c044003138a9034128110a20344a10000050340b6155200d4070702c503c0701d100e001d46480c0010244e100032920300020b550810400c004a000c0d04000040e9580000001c2e40840d090140011302207002d501a030f403469446445040c50b0444040d0034100c002c41c640071903810f0104181809880e0341580c400e01110307032801c3d000021281c00f5070540501041d4024049080c50381440c00031209601d17021641c00840381d05552864898a42d148107202a02480c8110115141d85250220612130103800003421001c0c200c034000c086140f00350b1030b1030a03440b084a002d4a4a5410030110703211b54407500c004901c801d2a518032010307803c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 455872895 1250 455871645 455871649
    0x40902030901090c060c0c1202061611060d0e0705191e0b030705030628090e0f0a0305030118060b041401120e0a0302060610020d0f0c0218041506050913050c 69
    0x903409170080400150400345030401c0115104040300640484501c05403440c10031360010741c0ca03105200302c40085000c0640c00030100200741cac0d81c414158000400f0191520540b192010045c0300c440074641e07891080042c001994288070304d004004012080398800400e0400811141c8002c4480c1d0364640203814800010745090400090750081c2856501d6554a04004040000e006043c004800c1600011400c0c40d01d20080d1b81c00c914125558a00c020503004c0e440351045040074400c4000d4441ca00881c1182c80815501c4001075041c4c079000e0702192144211484d40c0400c03162940103140450b1000c100c00d200300a84001c40d03c41d820300500d806801030a540241009a402c07007024180c03594000e1040314201b41c0c041c000c141e4040402d58030032020b005000c400a6940380040d082034103102041c02c1c0410040d2103081d48c90841a00540243c0780e00c003101c0e801014200d000c0310b00f070f250201c0007440c1c1c00c6100c0c824044c60301221070090042c80580c4071044c2c91480b0850b0400210703918454440c02c41060307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 455874145 1250 455872895 455872913
    0xf07080420100306170714010f11151602060105030c0603060622051003050f012714070801060c02030d1803170301031109130f02010c05010f0e010b060c0304090203090109 75
    0x40c0003036070041080d81c03802d1803024420000e040b005680346c0004a042c00b0584000c11100328014091030b10584c2c2910041090b1554914400c4805050042031402d0108000d0404030078091151100e0780401c07407103d184103d0b00d40c1021300030150b040c0c20012a03402e4a180038809980c2041004182910301036801044213001c0c1c144804501a480028008000d00d2134140c0d51228284101d00703003031141c0c1c81c04250402c424401401001785000820f000c00c605556000c8840780001c018140c10022113080941368080001c0440b2032000080d4908004107180e80f2448000080a80c064000c0400725449901a659103941c250701d51203554441c4030010220b02c0c4034542c1100c003418208060768a50460a0052646850000c110b001d00004428844003a06814aa128407030b00300c0d80d2559401d52a20040b00c0c2d0407080030f0f0250240d800e2107a54081418294002d900d400c038040d0080209a43d00420b02606001e252a444100c0c0c001744020441e50010f074004660045a0303000000e1420310350364400c500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 455875395 1250 455874145 455874169
    0x602070b04050904150c031a061602040908040e04050a020906061c0509030f041725060309050c040501140a05120c04050a09050a0309061115040807060f180b0f07080420 74
    0x351100304d00e64820400505003003d00009582c07a0345440ae0110102d00c800d0300200000340a1fa503500709403c2440024010b94003e00500d0080d58090700f4a41080740e0b4650100d00c041c0c0c46906620041009031400100325406034200d514110b800614014505008200040c940103550008019581340009400b0017840504200782010500d110f4071500285409150134802404010750002030102008108469084412a1a0101b15104e00b46481e80c18102e0015550380c00a08000000c0341040340c40f120305d00c98500503030f0f52003543c1d0b6032901080702030744900703003c48042d811429840010381015049107900906042022984a80d80d51307940d49000080481940064000041802042c0c1c2c850080741c07000d0b06c80310042041410040c00c0102c8e20a016200400c800c40000700c034010014541c1015104800280d410404016840c607900d4442c040e0300000c4a44142110001d00300d481c0e03140600d4091100d564030b4031426030b5140e490048802c0f01c2021400c0c2145182804030603560340c9008c03034030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 455876645 1250 455875395 455875397
    0xe15041d01020a030f0b010c0b0703060e0a0516030c0917030903060a050f011a0406120b0411031e1302060304240225030c02040209040605030f0d090602070b04050904150c 75
    0x10303803103c0c03941004084680c0009581d22030f60034800743c03904503039000075042c076500c0e0040d2400d0300c0e0743c40c0c0313000942c010400c59000400f00300c141d0041000e400c4050f88141d01c13890503100e075202c807206d1400e0120301b00d030b455620400c00318508002c140304501c6e5801120b02c499411104907450076201500003440c1c880100d541040480c0c035502001516242240341754010a0304000701031321442c052804811601603070142000f0421003121500542d103a80c1c003d10042031018008101c080c00803038840b030740c6030710856a4040350114243c0b840100d2108400c407a204000894030800b1072030040d07003001141e500140017601c20455034011144120403012801c4d1408401c00001680c0b1000b210340702045992800805800c40b0400c880d410110ba08091140f0545904039401a9901c0c12440010028070860b00aaa018850a151044440c200203040320380740c409911041c244598500003240d94000f00d001d914541d00d8140f00800084c1445451280c12910820711009049440da2400b8212244003e400b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 455877895 1250 455876645 455876647
    0xb1515030903030a140103080421060207030c110f031203090102071e03090e090303070309031202070f0c08060105030d1107030b070c03091e050f040f05041506060201060e15041d0102 80
    0x254411140c032504008090701701c8000c5e500d40c51a15581c803c4d00941c07007040300754100b5442c50405c413041d800b440c17146503610660031910f50780e440c1401041000665002c44245285156031600c1d458114010000c100d0001c0003003241c8807840800110a400c007a11012071076409105920015641c980b44000511a00003000152007081c103001700114a154041c0d6010202102807062069012044951120303290a01050381d00c0240340c1201d585082000202c4001e1021907244104100030028001c520f00030035020002e1611b805080d41c4901082c400d0503490791101140921503409013003070604d0300e0b911200b601c3c4190f0741c4c2c0c0c0f100f850b01d503001c4640d4000100403000150825810200d20070142c002d104091040c1004030340000e50208003809898400c0070030f1038000030696943e170407107030300b507284c010b420711540c1000e207000c1e40d091940d01400c103102c40c2000d1001c0b0f030140c41403044204440e00b400703140d10070361121114042c1540c0c200b480303250000d0b190f094089036800c454a200d80307050a004001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 455879145 1250 455877895 455877901
    0x90c06020a0510060f061803080f0a2d031503020907091715040f110a0e0f0a0b0121091505042603060d1a0c210105030a080a020316030e0406120b151503090303 70
    0x800302c110cc1c501452400c500c6076a0b0410000036401c00e080542c80d18100002e81c407504000c0c0343c1d095092039000170341c441a1401001010b50f8000d24001c00c8642c000301d51595030300002d1405032a015049a01c10030303800010b002a0100380c03c080c1c00007016010301c101c40c41130b003240b00110700100385640085000560b50b5050080310407140c030300e455100403a010100140001d0400003860f2696824116110844100d00c00d0514461a03000003195075010f22490621070300400312101a01d011a4147e400720703030340d40c180d106074032070600080c5070b10340e050107140e203155141e01c00c02c41486402030041d0f44103038011900c410703040000c0c0081e502a2140d400d2480d229107030150b06d5100b449174044821491100180108503d803400140b200794558886405901c03000d6504049195004641c81c1510090088034400149a080b9034411900c180656080c091642c880c001c01a40d641208801001e0b140a403000494120160101e03000ea5500209118000340101d00020344541054a143c1c10b290000018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 455880395 1250 455879145 455879147
    0x109030f030c02180610080705092d090910110c030309061005040902090105040515100807090b030601021e01020d1113060c1203090501090c06020a0510060f061803080f0a 75
    0x920000e000d1a108501892805c1c4c004180c5200421505805124070700010405a500070802c0d01c50001000d40b00c801501c0c030302d0b6a0000c00070b4507418586155109900c03140418101070340714501c0f8914140040c925804034401682c01040c00c03002c1c42d00135807424413051040d003005100440c09003c81e04c00038196402d006131809401656035000c03900c12482d200e502001600c450921604503501283c1c001071a40c0c42804940c5000b00801842d07521103800c07161000c3d0070b904801300d54058a29070b076801407411b403100404002884160391080c00f592200f11007044150011341190a0f00140d0800941816103c0d514001075070566040c486115402050000b5072503212251440200700615180c080139078151070340459000420880001c0648491500c010700100750444030b4815800100c031207005c2d9881c40000d480d205040d004030742e14000c0b121580502003003401404240c403004180c003411a4540441070700d041415003d64850f00c040c5050000100d40c410780544000c9040c1110180e0350b82140300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 455881645 1250 455880395 455880409
    0x10020c04050a060609060c02040902060403050a030f0503130b04060e012f030c0a1b0206031510030902010e06071e0f0201090f140d05100c021c020c100e0109030f030c02 74
    0x1050302e9003071400e4000c1040c540e0141d00782044441c1d82c18441030050103400410054140000003940000e00020000b042103400039070700150300c0c041d0f40c4400380116580c2c402c03541407000303803a401c0305078020442001c00b240050f14290b400134403800c1c1c0020b10b01c80c505241800e60f03c0b0041c800140000a105031a640d6504940681580c03002003015032461801c0344070705005000c1c1d10024010404102094090468040003043e0381a800401d035588038a00320b80c00101c00203446503140d000e0b940d444c4d50038200a00a000c0c41c8881369050311803202c4141e02c0002d03c041074100080a58000c7c15140e81c1d4404801007021001c18a40a40c9800c00c4d041d5007400090701c41103032940009038102002101b0420100504401c0c0c044040071202c03800d80e0800b40c1070a0786030a0441403840000380c03610601800e643c1d0001501d544040b0707142c0c42d801c0c11507840002a0b803100d030b007400b400303400c1080070b80c0007603c45104e42102d0300000e8050506074034290b201e03262140d03c0145101c0480c04a9101007601d815490003030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 455882895 1250 455881645 455881651
    0x703051b030604080406081807270203130803090703020a030c080105090601120204090c0918051903080402040507031503050f100c1d03010618090204140601020d08060f10020c0405 79
    0x2a004004904141c2d6490300903110710f00ca004c04005100000c15446407542c1c4212600e17541c14001c0720180da8498502a0781c0311850ae0b090308004030700c1925403001409078021f032407041d1021f51018159912546403072025510003070550603a40184074000c4011b948092240c0061802400c40e01740c0d0505008400b0b08454014020140c10b07807009004200c00326a6103484580c1d16819903000c201c031861441c114021040e00e0b0010345039141001d02030404800d801d010900218018400c4a001c034075035299070542441100b40203030025040300700041c05400d054001c1038000304e051070005504299846461320982c5240c000301ca407a009045840c4860600300400601848030400420040e51440005054038402a04a1211854030002e0f41110360302980000001c00170a090343d2a1060000541001007240100c1284103528100d500c048844840a15510500341031300203084145440c0425200e00c00c004100c00c1e0301c00d680d0400010385803543c0c809049240f805400618806260408000a0319402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 455884145 1250 455882895 455882899
    0x181b0801062d05031e1c030c090603050c0d020f0706020f0c010608010b1011072409080114010b2d0a0305060906010914060d090b040203060c03041104020d0209030703051b 75
    0xb0240036540e00031442c08100c26070081c003040c001a1010840382402e45c0d2a6803ca4000381d2940580c1200350140c00c485d00030600c80e50f803100065141c0c801601214415144001e40c407d05004000081c1e195030300801c968404250704c1401c008407507aa01050303a1080c0f10210f418203000c28080707905e00c0e09003d1a0042e20ba040001e001120349600481d00104032020400d00300544441c1c01d0301814401c0c01303400d026140152101e98001e007841c1c4220300aa501d442c03030100041c103500c000182e1000620401c140d0401d9928062096403825654542d00e420030300c40781180d0302c90411442038004055810b20f400d1800c034a800c3e40c0311140d01401a085400040890b030007500e052040080300e0703030b1011944003513502c04c0c0d215111400c00100440d225004a4402141107417400c1d800f00c090044800b1850b00c207510841c03c8802d2596a40e1050046000a813802010741410450019403032800d50058041c0050002006043c00ba440c40003914003081c513403003070340d80e5040441c144401d2082414840450001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 455885395 1250 455884145 455884229
    0x1060309170f120c03070c060207030c0203010515030d02070e06060c07090c03050a1103090a0210090308030c22032d08120106080a020a230906030a0b1003181b080106 73
    0x46d6001901d4140e04800041070258000342860805002e11728814401c0d802070001c0007645030080b00344002c5240307544554802e1140d1512601100e2001400c0c40560b04400801e00b410b8882009110a40e00110124110f502a500002c00c2c0b04c2010320800304c020043d6540800c00b81005004c1c0c00481e40b0b001d251400040d401c008126034014000391400255a043d10703070000e0b40d1103c20045170401c0b0740c0e810041a01000005204030003442401030310040c20000c07074203514148580d0303284182c0c00e4548802000c2500400c90400040c2003260810702c1c4445007074500c20441e8181e0303100c44082d848000502020000c040040c000d0691007002c1c20350000305d00000314501450842c0180110100754100e070f21150404820132000350000e402c0d00c1103440c0142c251a01c9040c4a83c1d603001401001c41c9441c0995451580d04061030721074020300c42051540700c02c00b03002c0d4480703480381940c0340c05008180c080e5403001c86001038040740074415070300240a0b03000b01141442500d910f11003c0c1c08102c0300b401d0300340c0c5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 455886645 1250 455885395 455885401
    0x20a02101e05190c0f0b0a0213090b04050901061203030924020c010510120803100e040b0a1b050403031101091202010902130b0604052e08090c01080103080301060309170f120c03 78
    0x1801d2017030380010a070055100503a698504c21070360043c0c07180708290507018910040010b40d500d116042614030790b030219030501956640400450884009200e080503502014224201090080d0b108521013401090725070381d400e1000c1010410003124441110544ee800200012800020f1040c0c1c0d8020894001c003202c2c1c40c1c6071801750051003150301000f82235028004081503007100403180b514000d0a44144180399450301c2c0c246207410314011201102c18a081081411141c0e642d5000c245025880e61200ca0800b03046403021151614415140c5646660310340c01c80300031500d41c003a40503503101181d00102d0441000c2c4140305c043c04142e10321503400c2d030a00c030440c0800c2c0d807150306440c00e40d0700c1502c0401e00e4103140d00301500fa4456000403a80e21a0801003144552a40280e0042c41107501200700c99400180c00c00444200c1d40900c8003605014047c0b006210f0144240c1107030317030841e00826080f0382c680c0701141145125842007640c1d50040500049080a44002d80b030101d80c020712101800c1d056103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 455887895 1250 455886645 455886653
    0x307031a0307061409040606030e0d050702131d100f15030215030601121a091e040b07020c062107111b040230060d03020a02101e05190c 60
    0x201c0601601c01400400c0302a000c40710070103c00c0d101d002c64006c0051013040e954940180080041d900030380541d01a041c600415540a034084803201d9a0180c045003e0440e921950707001803c04a0010341554103110701400001420820802c1660045800040000c141c4400404560940c0261750011007210000c01c00769903141c130b00801321480000140c0c2d40e46d4841004a42d07200031000001c1002d8030345401102180d0360b41c40d15140358401940d40040d01d1b154201d000044002c0c002c03840c0080c1150707000040004801502040d0012028012615001443c0700046c9082d0407a204200c050420400c4d40482c10480040c6c4640141c00b03420304024601000003041d80741d6100d020b42e00d428040006a03810325031901c0e4100c880482d8120484280152003507415039802030300c2820f0510883e5800c002c640580303801518a1070303055054006083e024496401d11500e240004400c3e0144544801e9014059072034200c81c0720740c050303a41c1e20103944608820354207051042e950320803420000d00d2103503e0002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 455889145 1250 455887895 455887903
    0x50f180906091b1f03060503190b01090204121214071b0e0603060c0306150406030f14010f030b13120816020a03050301090216051929040311010209090103080307031a03 74
    0x410303004c401d0400d600b80c040d6801e03405021154407003034140c4105107050311054203030f41c01100b00520411540501c2c0c0d03a2145124181c1c0994003824041c90702c030350f48150008007400c40484d02081a412b04410654041e01040496086800309540b102c02141540c04400b4802036400040c10713036210f603440d00341007840100740e44000007003843d40c0704000000890000d5890f2084c00c88205c0c0480d92555590b52030710700060289c56040400c03400d41d03080c0600d101c4413622988100e170584c1c40240c204444503286480d40f8240c104040c1881c216221341024420209019007003c0150040646031614181001885001c3c885958425881190000c41c08600025071040461741102c01d107a00140e240c183c0e400e01d000c0c03240f501c1d00c1c0062540c42000c10590302d0442c502943d040d8113000c1c201e80c0b00508010f51000900c2d001c0702c2840d00900030300000040009004130302c0300301c041032040001800c000e00340c0d004c1a00c3e81020303002510250000300030408440d505025003801403818002d014000c0c0d1904000c20340d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 455890395 1250 455889145 455889169
    0x9030f1207081806041d0906190b0105160605010f09090305070201110c04060602010608010e030418020a050c0a03030b1309240f14071107030b01050f180906091b 71
    0xa000d60004807032080300101c990410384084002c001c1c84e1740d6550748010b03088103c10242c01c1e0b85a403604000051050f800440c03502c5c03095400e610b80c200d0701d020308001c2100818131490301a05000c014071107054030100f000090b4204a110b0000000c882d41825905401c0c40d400740d010080b141d051010341303c0069440000e0350103d50342800c22880d048050990503040c508207070f01c01c136001490184001070041d81500070700d00f19054940204131848024a0b025124480c42c001d8a00c0c000e40c003040c841032820503600030000e0501d28036002e07052250b00305141d410540c0d4158240d001940b12100c00c6583d103024040900d600404a4041082d00d482e135440402c0040b902007040c0080d44038055104441071241c00490b80b0f00c405000c10010030340d0f1040c0040c40848140c0340b0200148410841d80c00032000083e1080070740c1e0300303c0c0d5402040ea103884108240c82c05484546504005510b01c0713001e8a03200e0301c2025016621b0503001d0a0b0300e10b003c4094a19180310340c40c112420210079890042a615101d1f11026 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 455891645 1250 455890395 455890403
    0xe131412190302121e0709030c2312030703020105100e0403082517010b120a180609030f030b1c0f06020c07030b16030203061011010b1509030f1207 65
    0x10961018105400a00581c0d2180011030442010000d030800798044502c0650f17500c1500d540f003600e490720110303468403240c04014421312803104240800c00710742d030400c1c01d031180e0040361f6141c00000c24082821900060440000c2d0350000c41e04900b0140c0a015140d40a107040003900229071601068910902000c2c0000d0148100d031030101d00303c807208402c42c0f103441c14036404124408000c01c2c4010100007803a855561a1042080042111040c502c102c4110069a1143c1c13005030f11103030040d44c001c0c80b0302c540d8560780d040359000d00b00c000340850080d0340c0040d0080d06c0c5e510a440d201940501035500108085115607036039080c4000d001448581052855040b85104219114620340813000307100d8240c075900c3c18810240c00104001f200c0e202148034000c1c4001b010b590803401c640580076808103070b8880f9800301e8100c284143c440d12840300415005000c8002240e00d54000340400c07002894060301d1005031000151a03081c6060410540b820668090024060308441c0409a405801082c2c8010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 455892895 1250 455891645 455891677
    0x1c02120a03030b2d030a0b160809150f0c1c020309101506120609020706020a0f1107060c031205071d06040308030a110c030a0305060a1203021f060e131412 68
    0x344c02c3d1010440740700743d02c0e4800700388111420203201601c0d1000024004c0c80000300407000091118030b0110b80c4102d11410714102d8009601c4144a058980c400100800c3e6040400d00c43d010340580c1044020760780700543d0000603074038180140181e0a10320340d4980d000069007056200740c000e2003003c209104865940c0b8005002c5000426014003400036a84501c0e0041e0001c6844014003e0541c000c0c101c000030f139100e520003050944015581c03003d65100c2021580c120801c20080c003030007564114a424403c1c03070071a00d00d102c948000c41c200ca501b5115100010a850a403c801c603650a0000300808400c9a2960074245151341d541514800100412142525200c40a91080041c0161840c1030620425a9100d850301c00008004000468403903205a0204c0000103180e9140c007907200340e194040d405008101c1c110840701e84058420800f00b2021030b0b03a800001040c921450700c071070241c06004c61540001d112424040c030101c0035440803400380d0300044032044100792410200c0e403002c10514408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 455894145 1250 455892895 455892979
    0x3060301110d051e0c07170c0d0201060312050715020d1404150b06030103080910020f0d020604050111040b0409090c030605150414090c1c02120a03030b 67
    0x1080c0500301408044848140c04a2502c18590440d00700328410703400901081c004640b01502145107210070b5410020b01c000c10048070011608a40d00300e502c580064190038640f8154501c40d614020b0282d8a000042c0d40d0b03000d05004103c144d0103031000704406850500d0816142d61145940d103004207410340d000590025844000380f900345c018514849190078000124030f41803d0a0188003001d21000300c0301c2d40b03091080b401515200c41981e059a400021082c1840031050900800b021601001030039403081c0900b02d0030003c800c103c030803940c00b41c0d41d01034005800c0601e446800d6a00c0e105489003c604203100074890241884141c5044521040020418003003501300b00484ea9204c1d00b01502e144e007030800708070220f0081882c40307445083c1901c04200020130701e0f203070210101090b6070260080c0c01a511040f25880c00711400c0b0250030f1020b9005c07801d25404c0d8001f030907042e5642c0f0320015940150100405254042c8150101410305440f526041d100030340008407020301c2c080c019000340b80719a00b9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 455895395 1250 455894145 455894149
    0x30e01050a0f0c0f060905030a020c040917160c09140a020301050325080d05041e08030a030b060f03070f080708060a030b04142a010201021c09020d0b0a0b010f08060907050306 77
    0x105029558122008114031b451030704009859500c1421240d0140c0b00d800c1c0c072580c0760f050a22600305110b800043e1074141c85610300d0302800300d80c0010901311495007010b4006c40130a45140d8800c009085191001580d04910301c92103668030801400808140d1052004000d141c4011400041407490403840c07000106441d90019540110768000070168802c0143e5241d8a582110042040c1c0307910310410281d81c8a21140180d00b40024042c0002d160800e01103680c0980c040d40000341c401c1401849281024083c1b406008503800c01c4400e00009406892921000b035082031300e43d500011031746018141c0e4075049010aa0700c0b000c510000b0040d065080008040c0105501c1600341001d400058035030b48030000d1000403c00385a0300140c1403808881c444400301350300500c21a0100f003042c0e0035814445456060020003401a40d0302030342c0240d291138a0100007100b81400754072800c124480002c641300900300041060700c0c0a18424240405502448820b5a903402c05550181c900c0c03800c50703a02e6446c800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 455896645 1250 455895395 455895413
    0x60a111309110d14070e03010911060c01110d0204030212070f03120905091302130e07090902030312010e0f071719060f06020f100504020a140d080412030e01050a0f0c 73
    0x86030001462921104884c8044140760f5517000303907116960f1090351115402010700701d800708000205141c0803021032717a0460130900f0140000c440d5000000590301e40c4070075500b05c142c0c0040d1440001903130004082c02103180c011110041002c50310000c01d52682012411502002140805030209603040c210400d520b00c107004040c013504000d8041200741c00e240013100744c0c100100008074400c0391490466410061240300715200034250034000c2205600d0603007034000501f00400107a030180010480000400e21041401d07009116041c04c0b0060307842c1c03203140c031410507501404010070400340d12440c00301088494501e540054030310a01d03071144030605148800604a650051551000d110400200140c0104101d189901d41000741c54000e0707005000c2d007045600c222002948070410540030301500d050920a5010b400c00900546081c8a0980b41c0c00d845401550005e0314011214020b4800c02d03074025181c8903410b4080c00c1060030250a00000781165613407451040401c0018180c0400707004a00c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 455897895 1250 455896645 455896657
    0x507141621021e0115030314070819181a2a030a09080703020108010b0304030201020c100614182212090303170f010b0309030d0c02060a11130911 64
    0xd0715203004840d6010300651180c1c51203150b152501004160b00a040b141801041c08141180740180b1882c1d0170750394140c8104020410034007105105010741070016003032800034081184071001c2c204203010030702070003031500a19403204200b026101d40c041102011540c42c03540070340b289203c050340300c0e0403c075841a9103403002e51620080703244242d105080d141c008002405443d115a0340c0800c001e80702d13040c1542d9040d4500c40240003a00d5600100101001c420240d03820510904c005450030072407030074141c0307407024880c00c24070f0880c3d480004122403030415100290b60041070b10111440526070701c800c2c0d0942d0009140c101d9290304c803949461110b0b0340500740c400d0700d60702c841020503601800500a01c0715415000072804a55001c80d120f0145541d010312030f00c6503d1103000d104e1581c0c00d00264840b50b03000608408028030041c0601003101c2c00c18012a000c00741e490b4018406440c01c6c003404800e90301d01c400b4003d20300d10100141515014460351301c50582e0300070700000c01c06481050700c1c01034901c611 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 455899145 1250 455897895 455897933
    0x106030c05270c0a09090b06040501030e160b12091b130207150203040b010f030f0303090c0b0d050a05070903050a020405070207051903020a06030b0603160e0406090f05071416 77
    0x280040040f0709480b04090240b0308201e50311004216115800744040300c440306c0c0420342c4050300344002c100ea588650440080305d012a0300307440b143c50403000500c6402c6919000a468190040740101802190078681e0383d001104a00400840442c403076008121201034500f18010000700b200c0385254000c0e03804881125a208191500300b02e51510360340b00a4009607001c40c3e0301903c4500015481d0903441244050b00c0c0c0001c10010403081d142e605600400882508440c19072104500080300d1709060050800e24100510200340303860402c6c214412100001d240e401448000758060000c9080010403040c034a82c103503000078058403507c1e416450000280e2140d540311116680b070307030303520103070200314034205d0741f094420405017610703840160140d07003507008103641008041c000540101001e0482200d82c060506104240c000c3c11030200f000e9503840d0300b011494a031070b0030480b507070189184512a4010031618003005140f5141560403103c0c4121100b410016100141000c24421141d1100700c07a4803003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 455900395 1250 455899145 455899219
    0x1e0606040f0b0306100503040305032d0106031a030d02070302012102070515070e09130609390e041401020d1508160807050d0311070602010e0f0106030c05 68
    0x3680b500c0e507126a008070f4002d401485200440003240e801001074034040d551544800303042d5600e084070600d0080b003040359044044100006454000c00c2c5e1240503006e00700d9660007141040394140b40c00c0c05500c010741014045d03441440642c0080f83d000c01c0c1c110070790382d092906c0420b15880703000702090003401400360210310340700203a0b0740100000010817000e0000300741c000c0ca0032a03440d41780030f48418101d0301d2084d400060103400204c040d03845030084a03605110320000200c171220307502c40034891183c2098800c1d002c080d103000714a40328154002d004428200400c100c0c0c0740d48c10030040141400c4050720061000c5030154040b00c0900e001c3d01a12201001c5403420403e10342d0f078481c0d0304080620741c0b1640115014541ca090003e00c2a941d00101b5984010014698a45840103000040910100c140c0400054100600d500c1e0024003070500209000e03030004c211510501c006c01d00b000701c1c5800c071a59503803401c201040041c0c0a141c00744c0c121907048800900d100b14400400001c403058200d098101e0720 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 455901645 1250 455900395 455900399
    0x60507020a1407050102060c0702010201090506040c09110915030403110a0f12050307090302100e04090f060b060a0c12051902070602071208041e0b0a0305011a031e0606040f 76
    0x10340062110741880c040e2450b000190203012065880720080d0182c2e5006822020000b1031800c044070081c41d843c0d02c10b01c000164035500c0d0310344a05242c0c0543e41144c021001007020000803a181c0210003507503424030b440c5407a0200c5800020014000000200401d404c007000050a2502a100b030000100105081d01c030303002c07258a801221201582822100b4440b092900c008407441a01030307038800d88264039000c407614150b80811019001e170f484400100403e540c035074003641c1c5036070180b034808601c5801c42c07900d8980c0525102007a01c154803415402480180205405140d11886411101703821091954541c1d01c2c0c06c000f200d0300d21a0944004216901a001e14001540001c02400701d441c1c03079086d80c50140d02c0e004031340e110000000000d0400d400510080c4440400040c40f2000ca0411896044650b40e5540c07558655810104c0c3c4403010a54940c0100b0031a8040340d010040d95204100c601d00c0c42c03078000110911003203c158442a03500741e0b280028a9500c907402120050300c070b03e40041302059 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 455902895 1250 455901645 455901647
    0x1416030f020103050109110d09060b04020703021e01020f1207050f0313020102010e0f0d1407021804110d022d06042903010602030417030706050a0623060a030e0703060507 75
    0x168003a908900292402000003000a0244950b00400d0b42001300b00345400200c6000c1405085d817004245d91556580d030700398040c2c0c0e840e0720080c106d01e4401d401038140c0c1101070030b44448140440c403c129032030340100205056001044206c035003004000d51042c0041e1111901190390b070044034541c2012031000000c2c00108031020210010f403034400d900a1002e0501c81200c80c1c0c440310148540c150aa0003d000c0e00c1a0354018840d01001c0000880c86506101041e000030300c00c08880700481c1d1a140c400400c0c04148034008405a458202c00d0b01c82d20400226a1b011417120b64681e1424402c0c1e00184440c0c60307111a00703510480074454024840d58969031508600803444c40340c0e0340509200c404008218031041c104400f500e04031106500610305162801c600c10305402d10100400401e40401c00141d0005141d03445070303a020741c208010008101e81481c00f420400340414a00c0030180c444900c0c0c1091540d0f4420498841031654500440c0013190b5106007031810906410082c80c9030705000404c6009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 455904145 1250 455902895 455902913
    0x6100609090c201f1a18061e13020406080702010b030c2b0b060a0909020d0221030708120108011506180e04060209032503022412071107060903141603 66
    0xc0301c400010303240044005c1040060441200718810710a00e508400940240342c641405000c400d2040c0034011004003000006200040c00020101c80e80d83c00f290500c0381c903501a0301198000e0b103500003040084003580009554400d600389880c894040a0000d0507021181c1c00c0940901c200390780c141840c02d10515001040100c00c450143c050070f403400d8005004c603810b008000444c1d4001d41560032a021917007d0150401d842c40c1c100d0500d0b01c8a05001e61032480c100010004d09004010180c0c907204505041a0502c2040c1c0c0a0103050b0f040c002860041d400c4890400d00312a2282881420307035800002900e00030001d03500044003d00024100b206120503500140711b9010110107551900101150840c10b4603d11203e000c03041085c0d4400340014104954088044c4646412000e4910704030740007284a540032401e0070301a00c1c2d00070144a0003d8000301c4503200c03250810b014101e500e0038100d00510300303807583c44050600504d00e0b10005405109100300701012040e90340800020343c0300d08110040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 455905395 1250 455904145 455904161
    0x9070207030b0606090f0603090c060712022b030c02010b0d030903020901050909030d0c2a0b060406181e110a11150105010c03030b0306100609090c201f 67
    0x90b2003603a00042183c5803003021901201c0d00141801da10004000520015400041074540c0300e10440024000b41d07a1001d0242040c98810028840c82e640c44500003414980420404000300480340311030901e00700740000006805107a85400640040d0b689000c0f40903100c00c0464640040300e10700104245a80700444200780d030b00946406100c2c2c0d03078400074011440342c11507e0200070f41042c030207106110025003020208000501c0c0421900c080c0384170404110103141350320703035071808101195070070070445c403200c00c0c1e0101d4100c03010801186026071401d0f21803140407800b0780c02640c400364007101590034200e6444085044900700100c1d15240e618841350b900411015011841c0c800001c00300e0b210004140101040180342c1480b140d2070000152450054914120140b5844120b44401d58808010a030703ca0a4160344040c090780c81c1050207420a03030b058120107070042c20400b1700203015403c80d0700b00040344c000032040265407030025552402c01c01c2e0941e4100d0380c00040c0b03603880110001600401e503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 455906645 1250 455905395 455905403
    0x51b03010f210804060507030c150903020d180909142d010b100318021f1101020c2d030c0610060c03020a111516110d03120c0e0907020703 61
    0x31280040000c180842c1c07500b80001010381600b0441070001030720407800ba21925201e8141031800032295501c8600b0304c0e503000300c11140203035229001000d00d5410042c60040c1807076420950030540704410020004201402801441c907141e030b030000108403c0e44042201e00d48078030155014020080e2b07a030124025520340d84004a4444140c100c0030075418801d074200b51200070f250320800110300b402600903103a20000b0130301c1456814000c0001d41c581d00e008001030075184010040c0072440f200058500c0c5660700b407104550303205201a40b00c1400c0010240803117660303104035005400341031a01200500800c2c4505540d8000810b9420311100300240c5680507442090602481c0340d02c64038200c644103604407000d00140c1c070184180010449041c20070110030b1025140240000140c0302810280e480030710481c0070703000800c4549061014881c204074682004903200314142481c0d403402000d48846954038907011703541d00042c98030a40501c0c1404007848003d0942e0310245080003010b500d44480d444161 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 455907895 1250 455906645 455906669
    0x30f070602070c0b2706040819021323040203190c03150c390b040b0903040e0c0f071a07110d12020f09030303102301050d051b03010f 59
    0x400d80116031811341c0c04441c0148101700d00d40158090342882c146102035002d400c40340410010400e5074003817100405010040018140c100601d1040c0154844d030f001030303800b8245c070f4100031004003031120000e01d85601c0380c61255107198640c0d000003030038101808507420104440000e03480800030903c8800c82128000d003001010007095005000a4628000398140003446a205040b0700d01004481c41040c82003c06401c215110f0007184d0403c031b81e00d5400c05552602800c1c081000b00300030000380b60742c0010341d44095400c040c41c1648181c1d08141c0038005003260700780895810110000a002d44126a0304801c0e503040c025085e009001d410601603440c0000110302c82c10241303884000041e1a10b2401c074555038a810030218010010080d00103429201007204100400c1c802c61303404001071030050490306401042580b501c2c0100c0180d80009414100c00d681c1d05600b0140c3d40e81000035111402c80e00180405c1c0390340c41006601c4064091027103068548400b03c00859008891003943c070030b50740342c840c0d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 455909145 1250 455907895 455907899
    0x50106060203090108060d032309040605180705160501060b0a0e0108071409040207050f0d12090b01090b030316061d01051009090503040801020a0203211504020c030f070602070c 78
    0x700d8580c071903c00840d01243c5981c0c0441c07154100f01e00c403042c0d118028078110040b06200e2a65071030b66410514080c2c80340034040340c156507501e4079109400042070225503802412400d903d07c18400a0300802031340900501050790703000d040121020940d92030f440360013080903545500580d240703500a003500030005004410b01c9503440d4040e00c04503018550984908012071010b4001d0340850f80500316540e0415028424100000d6081001d51143c000701d1014200c400840607000704001e49050319000c0b000e0900101802141c0301042450545045027404100c181c80b804c082031451040301d10a0781c200d840840c80e0700c144a510303805040c9040c3d880500204030706804940da42610403d4414100b8020846010404011954060308096100c2c005480c1441c0d56403074501d089070000100240540c20000329441c40d840a40c1e01d5403041310034000660b45034201814101d961400c80003645001d0340d4002540c564220081068881081490007125910100c3c2c1c0b40c5400690082075007100e4081000c140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 455910395 1250 455909145 455909147
    0x1803050a0c09060e09060109230108010b1801031703101508180102040e0105130e0604030845010b06072301020f0a030504020103090f0b0f01060503091207020a0e0f0405010606 77
    0x9105c1c010400440200708507401d0490140042c030040c56440008240000319039440ca0307940000c01c0c02081d054000084005000080c000300d900e008401c1c8400781910f03001480001d000c2c0351003485400c0e504210036200d0340d4030011105130301341c82e0308402203c80840242c000f0003684500403038403c80710f05084207001050140d0749400d034040d6010f10300e0400c5110005104134101a03003160310801984d02c001c0f81c8000d00703003da1400c00302d0903075098000074241000c210001541d1091400025040703513540301400164400440460441e111a914002d081c040c0c43d0a0000b094000a101c24802413440d507940645180001d80518450314a4000c43c4d41d8180115814106100b503030040c1100725070652420280d40c4044000300300051040307041c96a501d81c08800300350030203641400c0d140300c1d100009240c1050454091121016800401044010820002e01c860081079906045140280c0651510310301c5c80001d150301f00c03541240c003100d0464401c1020000451682c1d501480c007441c001c01642c0d480d000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 455911645 1250 455910395 455910419
    0x30307172a031f180b0d08040b0706050907060905100216090902010905060a0c0305030c0d050109021b12041802090909010b0901090c091406070b07031a0d121803050a0c0906 76
    0x130400c1c0c0c0720000016050360002c502d030064070340100300400c407009801c2d85a440c81196001500f0000342c8110201c1c100040041307034440c02c1e4000f40510300804e4200d240040082030382c03240d802521b0266030400007940354503000708400305a1010041000c0340c01511840000020290400b080c1e0005200311000202030400700110390402ca0156240000341c80c00d51400c4c1c610754405040385205410401c005800c505080c89440e01800c50701c40050b80c0c1e850209445240c0c410400910241740d00080354100c2001ca800c8120707021031741601105034000303102140441c024001c4d54421074024481808204501c60103502003045c0300b40448103091a80d0700d48082104560304210013401090210000344102c01c100d54051000c9034008121501e0400c0307c5e61071501c1c1100c141c41100100307072581e017200400d1203041c00c51601d251080c1d81510200c0c1450320394071070000c0c0304e108000501441e007503803502c0a00d041305558083c1d0341110840d280f0852520300418107405030b10442c01228507044020614581001e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 455912895 1250 455911645 455911649
    0xc01230724141f0f051908061626010320040e06070f08010e0c07020f0607060605030106060e18040203070506040609061b050307031107091109040608030307172a031f 73
    0xa09107100080c1010244100500c1d0426000c0784400c0700708001030300c2d907c2000002d00c2481a88018400203038064005011311520002444031052101c01006c040344d010140941180e030031800e114130038100c01c903401900108840c0c00c40e0300507040100c2c07040e000c036002600c00d0080201d6a00e40350740201165044504800c28029503001e20300c00c0000c10f07031100c6d003640038050041c0014610040441c8410000d10700d03610020007115600d40300c502c10041c9143c00e2041200420003800c01003609002800080c0c0d201740700e8580d104203844800041070554a080080030050100600f445035202e0725020050540401c6118200001d503218082d02c1818018045c800c41c5250320000441c00d10307050703079001e846621514603520402e03c40e003940080c4c504442d00a404d911140301c940c180d660b4000a0a01c016620180c015819990040040c4004a984800035104210003115501125180d040d0103c030b6101030440031030a07010603038001c43c0594800320021805103a4403500baa648681504a1110110230b034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 455914145 1250 455912895 455912909
    0xb0a170304080c010923061b0a0213181e020301090b0f01060906090e19061d0a090b1909060203040606140102060412050a09050d050c01230724141f 65
    0x1c40246c114481740308008031a1102e005040d01c0c2406030f80b2000041200303451507034054642c050f030350140950130507a091500c07035802c03103405124212107101c480c0700040411200801e171650a400003800500e01030058441a0b030700400a01c0031081034144072401c11f50540705a0a0483d010f070002480700d014040c0c03030045440360348464490307d1900400c0c3c0c000c00402010b403044150400030f6a0803650152080700050502820201c1050040740702c54890a50000e250704042403030700b080180401d00c418000c951011841c00c844e0100e200c0c90182c3c0d00600441200148524004401e100400403950010026511200c4031050790440d80c1e0012030391003c4c19200604248000c00503960380758840c5000b4554101d107403c00a40311940c92005ca81655840303842903949401203443c0039800d6a20104001440c94010740c00c904488101074480401c0c49054001400f103104c9a0710032174104503116121003041045e000401008a0342d410b0704445e03000c2110766020030003611140000032121800d011040e5140 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 455915395 1250 455914145 455914169
    0x70f021822050705191e0e010f1d0c0c070312020d1805060c030c12031b16060f0e0f070611060702070504050402130f0c030c14120c040f03030518010509030a060b0a170304080c0109 79
    0x1000040d00030aca00d0283c4160b9a0410410078424040c0c1d0070001c840003140702d8401c0501140300c41a000381010324200e2810204203044401c001015441d83c03d0409860007101e0603036440c6102c4150b14a1032040b03044c3c0008501403005450096020360740507521a8a002280c100d140c4100c40300b4031118417926910f0000c51045001907404110260b0000640b50b12400d00041c182d020803034400e24003140284880030301e07032090f40c080c0004d541c04114884103400c01402410103050142000c0e4890519002d6079000720f50f50300c00103042d5505c423010f9031402c040c1501d0410801d41d800c90729001800300d54100030301080c10050b2800780240325401062000c00c2145aa41c205601c140b0703003803216031014110840d1030106000201d041004200c0b6503000314803c1e29226500d0009001c4000d420b01039803400c40c180314050202c0780b25518040313080041c19500101c001450032600c1c002507411030950f00043c0701c51b00704185220008038000010010b075110002201c000c1203e41f001100d541040340500f804c5515 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 455916645 1250 455915395 455915429
    0x108070b0c03030a0e010e011a0414060901090917031905010b160b041a09030c070e01050a1725050114030c040b070f021822050705191e0e010f 63
    0x605070700001080d6203400c004240b441f5500401401c4d00c5070b06508031064141151055980d00e040d12420095056031481c421462030500d00190102d00144107180103591501040402c10400c4041c5a1001c400c0c581100d441e41480703040303400c5010034441c3c0f201c0c002e40b6080c0086100d20010060f0b0ba0071040780300000d07803000705543d15103a100801400480385082401c07140000840b51103860741c8614038610086131507070040200350f49440c07080d40c041c04803003445400502c01911844500000d850820341000007650380e1520003880d000c25001070790140704102d10314022001c09800c6400c111f550903681e01100c03101c0e1100400c414882a00c0d40c0044c40381c104020400201c441000e00070144c0908002045d9100c42e80200d8030014001d201d4014444003a000c0044140f900d91140c4100b141004550800340b8099840d50780d102860b01486103d0444400e0000b44541401202e801914883e0300308140f9214081e0180d0b1045194007440108080c0203002040c081c40c4002d000c0d0403070310f1800703096070040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 455917895 1250 455916645 455916661
    0xf110714060d06060e03060f04030f05160209010e0a11040b1603050d060803190804050604031b051c030b1504050d020f0405090a021c0506011a1b060108070b0c0303 72
    0x250028515800c181c003445100d010440501c2104003e201035169004522641d1007014100a401001c42d0460f8140c0d00901c00480e5202d07017165166600342c14102c0c1e41d00d95196100400c01c03103500c1c0013503201d40c419001194003200c1131a45e901882c7c41540601606940400f0b002d400c0c05140520b44980005200811401c038501028041c140d009091440c0f820b08842c0f5003500f55030b0070340c00922103540300141c0b0302208202d82031282c01086462400901c5418075a9406440d12070161000c0c04001c610340342d000120901d00003441000d907102c400c45025009007000c4d400b10840a04420000c40d107444005162070810504a8112100c049401407038281084d08001c84401840713000c5c0e0b00501c43c040794100c180c64510500b801440c0c014020f2400001c5071040142c095000b8030401b1900d4481405040081c3c40024418107443e02c03504245951000c26000360441e000e080c20150741c4002400f48056280004200c441c1600c0d03404040c0e0781e03290f486000c418120f124505071264103a0040000404071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 455919145 1250 455917895 455917919
    0x110108130228081b010807050301050f0d111201060503060702030a09090e1207060b090a0216060504080f04230a0308030a0c09080106080304140301060e040b04050a0b0c07030f1107 79
    0x1c03002c101c044801958481d4492441e0045040440a04000340441103c8543e00703c200568040d031145400343ca10740c1482d011840b07440000d41c3c1103000d04c079000b810343d0400c40c01004109449002800c1e0308040b445050106003c1d00c0a48289400380c001c840108034514804001c41d0106200c507103410406502c1c0901a500600c03030700c10503100074003038481c4105481c130038580200540c600424000c00e1035030340d000030071070060005030511040b10701c10000152942c500300700d600486a003002f0001140d41d241d04101115100c1c070b800b198410751001802180701c18103c5182451203900c0c0d60b00040700c15404061013070600960002420402c03041c030002d00803041c20703000440165510b14040a403590f4800c491829560150041403042d000810248400c0300d200100000085084009128207842c01b258030102d8071015001400504682c0001000d00c10100f0903c1c2c0740640c81000c0c09002d1410601013682d540000b00203d0000e1450014032068030710644424460302503410182c0030b8035182c00c03049a01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 455920395 1250 455919145 455919199
    0x307021f1b080108010b0f0312130513050712090305030604090201020c03010501090204230d030e010903050d120c170f1b0c0f2b030203221101081302 66
    0x9038940324001c40768032084100c041c40000034551100009941070400540c250346001002d82e0082040b001030251a660010751141500000000b0a5070b130501002c0c0ea081921310788e00b0103504100c01480012091850750710180c03003500d5903610383d4180aa1a07010300140c5d1501080500051070030b0010984524150307000c0e106182c414011130307010002150109080d00c80917070000c03e4440d8041030800003181213034a20f001c0305000720320740c01c0c00d04e500c0000070302c02030003068000e0b0030410717481e07107510329a4000d55424003d581c10a085030100064400010000e1601482c05c4024500300540741002030301503441040c0e0910044404222030369a140c41c414480300080c80e103180e24140882d214600c1a0701d43c020b00641155032702800b0400340e02d40c0e10b10319120480030705943c400c207034100918000c0414886050395034040d14016903a074860781d0441c4074004021f41002000181d4400700d00c204080c007128160f070304000783c07541440e80d680c569000545a050380d0020b500030181c0e0034550080c0c400100300042d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 455921645 1250 455920395 455920453
    0x1602130603120201060608130c03080a36060e0d1103030d090b01031b0e01151e02010209240414130603050f1006050d02041d0d030213050303030702 65
    0x11038954940740c000410b40500c60010143c0d5482405018541e44080c5065000501c0c44000740325214642d00d00861a4261001804d10000401e681d51810300c1422040c580340c0800e65035a500090a040c140361409441082090004c003402c2c0020300f0500a180f28503100c0e00003494001d411049440d00080340000082d0280d150008101c01c5c10090168810207441500a944204407981949003413100c0d420200c194010800b0544c008015041540a40b0750540ea5018640d0049003485441500d1001e003082c13901d1541202009500410340d415805000780881c1121440000f404211822100c1032200c014801d051004100901006290f041030221044019180b19081814600c42074202e52258004031600c2d00a6032241e440d244c010814250211980c035420041c49240800007a082c00d490721000b0302403500e9402c0c2070703910905125000030594180090b5140e4000140e0002d000f9400200040c000341c0604201280e40c3c1400000d0324480c3d4801e0700107115030608007046030400c61200e291a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 455922895 1250 455921645 455921651
    0xc040f080c1813081b07050301090503072904081c0c020d030c140d0b090c040e06010e0105070b07020303010501090e190e100c0521040f08131703071106160213 70
    0xb20001c2d001400a05405c20801103000001070708030481e6052000903030210303200341c2c10283c4400218801100b102c2040e64031180b1440c60340c0031022a41d284c070410320090090454600100b0041c0b00024005140d5428580025030401c2d20040030340085070b80490204005038010030005031024003e42c04607200500900b00704620400048244816a000780110030b50280c4410303a00c61a803e050007141c0d00161050710b15070800741090b20801129000800441c10020b10701d201030300c03990080080712155a0400d00d42c00c1d0074a80310501a650341c4c020b00c12203000689807072001500c151013510784d40c00341410048000d03510304105041e5018107140101d40e45140182c07a00041851a144510000391402c0e07101d05443c0c20304405020640c4170280035070300e401e0002c1800c000014145a4a4041d0b9076400302d0b201ea1658811503007520b0903411508000c00c1503d1401c2020030348840000a0010b02d0f1250103103040c045d61764020300016004050618900c54000016a0010700e02220800c402c60030204c400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 455924145 1250 455922895 455922931
    0x30307170310080f0d140403050d05070602090907081008030a121109060408011e0212060d110a0803070c09151a0702040504060e0106290d0e03030c040f080c18 70
    0x440c4c00d20b03140c5802018240e011150440d95150821085c5503034180b03c250042c202855031301d4464131401341100711410480c00080400c10040c41da410703140d030a2400f82c541261440c1101c0003800600041da0b540c045864240740005d50500004102c030414045680d482c080002d415401c080500310004882140c1c0d207081c040a40c00303484403030103000104100790003c1095408088030080b049000d51241000da4010044c0d40303112010301d581141c1020064580041100e03250400118440e0b0600d0b00c2980004050b100023a011030000241c8842801071410300302d491b40e00c42011040b5050307203080500018401c101041045c54a901d00301c0f5406042d01c801d450001d441c1d000904840d800c0f50100e401c99618900440c0d000b2092003918042d101017051104810040f5002920451601034094031188002640d09400c00c81a00042c0b44034001303502300c0b61241895a03401825400a000e0b082100307010b080000b840c00750010300346040c05005880001c214941c00d00b03800d03c0d81d8005003208030700d08a138003031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 455925395 1250 455924145 455924159
    0x4005040b0f030a0b1b12040305030406060f06090515090d0213060801110c10051017070905010b071203063f06060501020106060815060c100903030903030b030307170310 74
    0x3404251602c5030b000003442d49084405c1c1d0010003020004802071103c24452560400c070115501d41d0029014201140c490341c6d01d20f81000030b004070f81c011446c120801c0c13100107901e58000c20003000755441122083c01e4108018070b454003600540480c2c0b54084081c081070000f6007480080400c3d08209080041a02038990010034255040c415000320100d00000c0c58080440b0180400e0f0f04190b450b07401800103082800c8150303204d000c80d00403060710f903404040d141e202d15030820415009180d4110203006540e035071b10f026091a0000355054440940c0064038051452092158005079800311510500400104070504c00124542d1820080c070039000030760316074070070b41034807840c0d80588258004103044c0d040074002402d50f2072aa1000d01072000c1e0b9001d2007840c541e00d40500301454825141e20391a844060300c800c4c64066000340c1803003c1031074820fa4200341a49900660f03401401b9850170700c4102010800d03d0b0f40c034822144090914022544c0c00454a50540015034109801540440a107911002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 455926645 1250 455925395 455925403
    0xf0507050303090c0901060203034006090b01171b010e210d03290a051504050301140106080403080601030b21060112080a110a06024005040b0f03 64
    0x1800408a60220a01c0c000d1454100c1c1c02c1c50160840d44007450030360802f0341601c2c500b00c164601b181d1100c0324245403015903083c00407450361130760441c18107804040050b0401100804414000781c0b1200d4200001180600b9100307520b0601c010710400500101c40e49146000805080d4401c59040184130788808200340d0b200d00312072012043c91600500907500b1111403d1070300c01688048010b0500340540c4c5c0b0390311842c08445600801c2031074115401d090f4a100041c2d6500d5035a0070003a84142c086072141c0041091b0000381c0155135040d4000c000700384075035a048020503004d100e0440001d00c540d00050009110700082900a038041c100424003001c22000903076182d41c21004940304084c52213550081c0181081a240106440c0540c10101260354943d00c806116250420060020085000b2a13000f0100014018a90005030454550503010029140000c41c1d0064440c242d410f100c1303a1403903216078000f030800c01d4144131094851502e0131003032101030800140d203e031303100030020001d001071344040c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 455927895 1250 455926645 455926651
    0x510270f060312021c02150a060806010f03060606020c0f0402130902160203010f090206030c0a1b0f200a1701060e070504030519030504030308090307020d12090603050411010f0507050303 82
    0x2600500b02d100f0200c5000b03140209240d0610001900146400442d54001c100a11201e00c820b00285840c0c0c0d80001d20409002c60f41e1104042d403203400c0000452180003c1c040055a2140d80d0500c45142d48800c201d030789185100645d0b62001345e405021169140030360040103441d40d403190f42c450700c540c0e4404074800c0342c002441d00c0441c040061701030021480c00b0700c241030f504a10000104520805a00801e102d400010440b0144400c00900201124051903a002c5804910f90151070003420514050014000050084440c110000040da01030f8078504140c00310860003401c8030309a24074242181041284403030880c10319550302c1c01c01144d00701c17010019034414134103034480c81e0b80c0307078a549851850005400840d040d00c1503034082a00019070302008640840307400d881d14500c02e40f00d850045080d03114091000b50701040d84100301c42008440c0e0004c1c0c86842d040c0d200c1900580d6900c0095055502c201c40c0201900001c9526003115801482c81084000b844c0c908503080040c40d41d10249554829 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 455929145 1250 455927895 455927903
    0x90c09050118021c020306010909050903090108070314041e0605040b0105030c0102071827050601140a080c0d050a1b03060b01170f041502040f05040510270f0603 71
    0x500014040d40d080d2620b03500e00b048100108514215402d558021900c1110703080c020560380000115506a00c203071800d1001d0850700204100c09d08120300d1081e80c030350044441c0b5010414120016030700314020b2240c0318454190692545c2d4540c1c1e0303580c9440072446c1321200618441c840c00404004a01c2903c10035200d548912040078865060200f054a410785a144481c11135101030310600c03c500390300410035003044550390045103440c520401038a0000d58a00c3c0d22741c0007192007941005009000071154100d815000404082e00710f101d003804030240345801041c04a41c4480c0c4d000d0114280300c00000e04290042c410394500110303542d0798a01d00a5294140500880b42800500034401e80340b01d84482c0d0745003400e014450064045480d01401c0f40100f001c040e0920b510002014400006c150826005209500319512030700d0310b0700d40c180d1b01c0071740c001c40c1d0050b86000c0c00158140344481c0400140e40700140c1100182d0262102da5204401007490000c0301625601c0003480007440b801018041d40c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 455930395 1250 455929145 455929151
    0x80c190801031401180321020c010c090503121611220507030911060309120a1805030f0307150b040204090e0c01091a0a0e0a0602010507080c030f19090c09 68
    0x155003041100f0b1411500d0310100e992510782640329100641c28a408240e80c0760402a102c140c0c0a01c01c144070a02c591b00c0740c0a858000500550800010b40c4407a440c1c3c17045844004525407108103141c0d55a42d8010022100c007010020303000405125840072591510070b90700c0d410011001408030b5040309102696500401490b507103040e0488660003030603401843d81c94200f190304410346442c40105003100802e405040000089514848d09008035405003058031443d90b81e44858010080000d2a0b20b5210080e0321588000807891346400308846011100d00b100850030312003103460701d2020000466403491402d03070300c400410040c1c403540080d1005000d46000001c2c0900c46100b454105030064070510b0400800c802c081c80342c41b01800748985900c82808030380c4c0d00c842c0002c3c02514514000c0d184180c0c42220480000781055054211910401840d5100c0c1c0054842e0910700c240b501003641e82040c081c0190002030850301c4100d408400020b003151000c14400003079180d4204d4540d032904003802440d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 455931645 1250 455930395 455930399
    0x1f090209040e070f080d0e010903020f0d020424060207081002090a08070e07142a10090803090c010f0807030b06070f11040c02030c100f0b090a0203040b060901080a03080c190801 78
    0x203004e029031b2a03500ba43e81008482c1840c0c200000741650164017000384580d02d098000b05403a00c840c1400030500e13038094001c20505241c40529500304000d803203940c007000d9454801060b103620100d0940d0807070742c0801c02021404010480d50010b07400c81c4451035041030800780001250b42d01084080c0061001c180d40c0e9125082019000705580c1900007a155000010082201040d240c00c000062000071820701107500c40d501e940b40c500b82030700000d00c12500c505010400042c060210300450003031442c00e089034040383c8003600640e10b0f0322000c0210782c0452090b000040301c0034001d4010180305407005000318681151a510840d8880300c1d44426512424140c2c0045e0701400e191103926001e040c40d000450402865603c015542d0700c000b2440d03003040362108800d40e408011500310307010410f401804a41c040ca44a00740d10000e407c03c440c00e0b5a81103180b004100103040454490b4144c4150b0000b07405643d640d5102681c480c00040d001c1c90011108001c80300d8440c2800103900d03c034914650b140c81c040c2d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 455932895 1250 455931645 455931659
    0x3030a0f200d051b070507090f0c0c110a1d1509101a09060712030506010e060a030c0c05010f0e06090f0d0f0504050a03030c0b1f090209040e070f 64
    0x1d0314201d40c4548224164568056030240200366280d409032600c0c0400d09668940042600151a100c816450360740401c3c0b9004003c008034652041e01c000f10420000805040220019105220400030125880c9c0207649c2c081060035400c0181100b0140c8002c2c0380300c0d41c52410240c1c5580000791a00703103000c0303841408220410809044100e4104a4544000d030800c0fa500e00c1200c02c05208a01a4a8899850f03603c440192000ea46410000030440c075200c020900341680100b082e0752400c8000f9280c0301c000794030b13580030300c003c46090311025104a040c040c03000c40079001484000c0d0b1f501e003400148222200051001d02500c5483c5860b160b000c40c0e4042150074440c80c00340041c02d1101039070044c903d030038445180011100220041ca140500b0890650308003602da03840b4640101d03411040c00380b00070060641001d18820400c0c03140c07210044035aa889080010543d0084505c0c2c501000b2040c100b10507a09600078200b0120028000a04e160034406058a00b181991180002c1d0820308000c010741 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 455934145 1250 455932895 455932901
    0xc05030f0304060c030b012118030804050d03061d1905011e0605090d12090308120114031902060915030f0103060b030303070207051003020c0f01050a0c0e03100203040501090503030a0f 81
    0x1110744d0381800c1c00380030038840000e4491066052500242d070404004e8a10006080d04480b8400c00551030740a00c104050500414040c0d04031011b540c2445051135404405210b486070904903000b02000558101992481d0400c0329000ba110041070f8018442c1172080e8909446018000c00b1803007440c0e1081492400000300d104860727400801440000d200c05c2d413494865a1655461b282e00c0580080e440301040c05c10f48001e203541e08007908100700446c0e0000829804019117041e120b6094005d2100c02c110810182c0d913100c50212881045120380780100142407100180c0000100108042c07540707103005980d000307190012142094444070031001081070295034403e0482101c0140c01461039460004d001075070710141031140500075504c2604c2109600e110394103a8400c0f41c1c41e1415100307144074003035005000c0c04c4180d4071800742d9890200600002401108038002c1000c010300506040400141d0000003500010030030f90742c039502e944c40680061428001540f2903070302c81400045160b14680c49000b2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 455935251 1106 455934145 455934161
    0x7030e0402070f120203031b03010b1209100c031517030319090819121a092502070603050108010603030806090907050a0815090c0a03080a0c05030f030406 68
    0x13a4640c048000c40c01018910f480980c4010343d00c4c020b030041c0c402071140312003401080146144040d030742ca685c90b034800050000d9030074514490b6041c006a407000981c00c0300003682e070361440d040e6035112344c0c09a014107481420703842160000381045c0daa900c00a030030300000d84884088018001d1171902304913007090b0300001c0551240101e45601c030300b0003415409070b008181803100c0703000701034064032541c40d1080c06002c01b01d11480000060021030b00e00030b400313071111105602540d4440288200284415801c5078000c0c16001e01d00031005045903c107802583c4641d0604408202080d03100c1c9034141c0150007101c4440c5503444458a0030701e441050381c0300d95005200c00c1000038a0034004a40c481180c0c0300d0140d129000c2e65124541a29050761741869030388041035034401d00102d144800030b4421948541440601c03043c10752200343c510380280000d804214000000c010400900303002d4045 = true := by decide +kernel

theorem cover : BRFrame.Cov 455755395 455935251 := by
  have h0 := BRFrame.cov_init 455755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 455755395 ≤ n) (h2 : n < 455935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
