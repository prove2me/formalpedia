-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2447
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:44:27.511805+00:00
-- url     : https://prove2.me/submissions/6654d09c-12a3-4029-9f2c-32020b97d4a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 439928057 ≤ n < 440107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 439929307 1250 439928057 439928063
    0x1091a15151b0a05070311060a0203190912080306180c0403170d060e070828020702030f0d02030d0e060618091c0507031205010f12050a05060103060b19031e 69
    0x1405224107480341c4100110f4021500600150642d20320b1803814149501032107002d90302846041c003848070a9600401030300e4408a00100c0e0304003080c440202110303030b0300d001d0304500d942800c0c0d8a4000244074000f40510b105000c19107802c4481e00b4007007090030510604503030b103510a00301080b0030300c0014a030466200c039400003000024101012481c9040640e00c06401080c944550f0000b000704044d845400303290010003070213504038108075518522003544000703a05030070b1260300040c80c002151410403280003000e0007141070740c00c10720401800944940c01940c05014050070b03c9103050958102113a40c0c1e0141d58010022091840103040c0c800c28407000411a5050703000d040880d84d60401030b0b940c40c40381c22030290758459651080345000f0f0590071290040c0b1582a1038500140094540aa84041642c3d0400708940c2c11241c503180040c9040800304008000e402108000010403071035802401005600b101c07840040b604c9503807140e4030f02019110151800d80d0a9140c68880c04e02c1700c21410143d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 439930557 1250 439929307 439929337
    0x1f02040308040e07020c09040203071502070b0c0c01020f0c010e01030f0f0911040f180807050a14100b0103020304020a0501031a0402070b04030e03070b220801091a1515 74
    0x503481e15202a0398016602410445010600b000041c0d40e0601060100160444003040c3c80d00713081d0042507072115140190300386c0360707034269503800b10500800c101c1c80104910b000c540c1e55003403096a00781d10f50200640c40c501511400426081500c8085941c0c6142e48d410b94a20f10707007108200044004d00424490022450360341c0d0780e81c0d03010620306c0c080e00d10f0190040f900050149044400c1c002110454103422401c589403c203d0f881c0750010f40303d0350414a800c020880d4480030035050a6082401c070400041882c5100b42130030700919030109140362402d2101c0810060a00c080f00190160f100458000f54084c070803910511481d070180e400001422003d2a0354070a083c10f010105080340c3c02000e041e075865441404000806034410192410140290041c001081c5030441c5030b003083c01868070030021003100740700070260150344c070112800034501c0c04002e00c4a0b14490608503450602c251100010403150800509600041c6c0709000f1070380d40c0617001c40b01c480b0740741499800b15040000d034004060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 439931807 1250 439930557 439930559
    0x1103030c0a0f140f120a0e130b09150a0902091504080f070b07080d050711190b090d08041106120129090105040324060b040905070903020d1101030b09011d0906091f0204 74
    0x41c59004000c0700da10542c00000461009d218100080e907403009181000030303204507680030242e0f02d907104188100e45001c10090f889482da58002072040d103014000105a031000702d0005402c01c0c0000f60003a42c4000a026600e4054580313005076034a2043da5005442c2400030040c035050600a40d10407507000e840c034a0010f00d010050410705080c002c81c0c0744c0082e6003940034030f490814441c8a4581e0780e04454607400519415400f10b00103400031030000d10207001d00c41c1c1402002d01c1502d0304412902d5205e1012001d0a0340c2d030b12001c022650040950300324148030039004022410300f600300300326007051805845050501c0d24564481021607100032091900c01e07540031848a000c2e80502602c0b0144c01c11080701502c6a09000000c01141c1004200408101c0008400c0000d40c82d03080382c1641040d000311251815000e0384006070090301c90032080c1d9801503409400090b400100c003030300440034004031403c40660f8540c920360990b9104151845003098100301c000e034841d000e5103c403040c07858031080350141c141 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 439933057 1250 439931807 439931809
    0x10060e01140309010b0306060a0e0f070903050303042d020a15050d1a10180b0c1947180105070e040b030102161103030c0a0f140f120a0e 60
    0xc0e081500c030240503a45030b03000c0305e07201c1c07400b4892940c0c008410364404044900d0800506115070b8040c06c000110054031020810795885100d840c0050f6802c40200c0340c3e24281454581c41c2010900d000c41d80500101c9071040391070b0301c801030300203002d500101000701440c24800240d881c0d50040c40500b0510000308100c43e078002c1b290068140030000c5a01c5540c507500e984092255203c4100801001c208015150340b403e6002444844241c030b06229041d6100c020940d0818a0f060040c1501c0e104000c00d8009075040040c0030850040f0181204c2c80001d0817071141c2041886002c1d031850724a01e14244542e40030040160241d00356000107202405484010945011800c549003035a482000460034010860741c2d00341030140c5c00b00e07070905600840c5410a4482981c038880900c40c0002c1552600311080d0001e0b40d002c00c00d0303403020b0b03a0301d5055aa021180e4a009014043ca010f030407901e200703025000240d402004110011410300c1c05002e0f140345209094207650b1540549528001d00090070841c1041d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 439934307 1250 439933057 439933097
    0x5181c02010e0714090609040506130c03020d0f110303070c181d06100b0903030901030c030608030d050411040b03062e150201060e09070909020303090916031410060e01 74
    0xf03020480019207401128400c0c020141c5c0b00500b00c60080040e8003d00001540025415034070400c08010300d4020325a6160881c500c004c15400070b036110201022100500c060810100074003031103000244003810b001000c1c103440340240700d805030505103101001c01255000711441c0d01400288140002d8048258a50b0184480c021241c001c955020301c08220030b0a8a030040030010b405010340b5030342012030050004e6600d100f40c10540d410540c0303848541cbc110320300030f030011405405202c003540d03111103125403400d00400301258151280a0302111100d01410700d441450001c40c0080d0182480d0307a1100030a200e4a680c51003061241c0e6881980d0203405525016000301a007481b07480b080601d94101c43c001d007034072180d400c00354400c10001c0034847c8c91000020380000300d64a198021a041c07140b4000a800c0d4041d503c505900858448208010101c0c5d603040346140070190f0320100b002c0710f2948420301c07909004648003503c03403030100003c1c40242d01928040c4501001450038a038100342c1c00d444402 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 439935557 1250 439934307 439934309
    0x3030f150803030a0506062503020f0f010207020415030206160f0b13120f05040512030c060412110c010509130f090302060a14060d0305250b0a05181c02010e07 70
    0x24960b08040f050103007012480c0100d0342c03c00021100d0508282102404505548030305007407400110921500c001094000e010212000ca400001c2d24104210003103514040d52010804a105130703e0840034500c403400e28100c40041c0e94000d01400e0810303074400782050141510798400c1d034007641c01c0140640000c800a01d207521450380c004080e18007048618044c034412402c0e5071008280004400c2040c03c03e548034054500f154030071181106045280100c0905610030406240603034003038035041005020741d240350540741d00c6030b9903100d4804c245044412a00d40c40b60341c4c1c0240c000780d401c0114504a1501350100d103020b2408980000340e10380c07424501c5080355484882200940c00400170041c4101251144400c0ca11039146041014a401f500081040101e41d200409210700410701d0350400a14000c0030000c44125070766500e1000f090304104c080740ca002c550b03410003503042c0b1002501d05081e014a900c2c4280d103a038000c1c04030810503200906c07002c03460440b03c400c541d038519821040000c1040864 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 439936807 1250 439935557 439935569
    0x120905031e160c050114070506040b100305011104050102060717010306090c0b130801230c13080a030c05060c16030c022b0507061e0305190c0509010306090b01090303030f15 76
    0x2e50f000d45003d0015007080345003454582180360901c0794002107500440d00c140d00541c415010500c40d928020300c00740c072410350b400c007034120b42c03034400301e03207131503d4000c00a02c10f0301d80c02d800312110360380c45038011200300910340030120400340b078a001000000d80d1074014500b80d600c01c0028506482d20b803006000e03560415480045003408160013000102020710495103415005400b07002c0c48008030284c0c0680b4200a000b941e070100340010200401510300081c40d01905258041d1480c0058030304004100d164200d100b50381034001d4002040541c50688100c074200302050340140a4031040b40c8094a0b88022030805a1b08901c0103d448600102e5842c400500324200f910103914803046420b12500d0400070b900024240801e90810680a40ba110b6540050340d4a600e801f28455070b84000d29001409401d03040c1c20200d0910800181c40e94100000c0c0c4224542070340c040142595440910b029a40c80d109014081280d10400b44003280c800c2d04401010010404041000d060283c05003120b00c030a54408 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 439938057 1250 439936807 439936823
    0x90e01020910050c030417100903080f06030610030b07030f050702010905010e030f0909151c0308090705090c0a0201180507060f0905220b130c120905031e16 69
    0x40d0707240c64511040c0781008507034a03145080500f144c3e003295030f80c481e900819500352241003094160b0701042005c2520204555414840d10203140703400703802181d0580c0c29602e110510b1001420500740052054842c00725910541011490341d1590391104001400c03080c00c0503110000021112a03a00030103001d00071540c000110070100381051070031180c8519104c0450b40042100c070f81c460b40103034103440805100719900c91198440781c80c003c00c14020308502da0b0708a0380b405515810300004600149805000740c941c0c4000d503072502e0f00b43e81c40d18032034010303598041d40707500c04110b501000201804204a081c0000200b245110078180c0303011a1642003114283c0c06500140300140c0d110181590030b07a00c43c2001400241020001481140c640c55000313001d94140e24101c10103685031300290080030010701030600000d0f541104201600d0805800004103901d014440305801c410b1181c1601e00380c11030003541c14000c42c0040c0f40c01c601c2003054201c601c00e0080c0310f40e4461035240340610a04a20070414 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 439939307 1250 439938057 439938067
    0x18050604151406060316050415050301140d03020a030315080a060204080114090c01141216111203010323100e0d030b03150703020c070b09130501120b0907090e0102 72
    0x4805603074004041100e42d241c64001d0010301e0b16001c080d6a081036101307030360000d45024104125868003c5510806000f0000b215020b48260800d0085060f105540d0716000d031100c0e140e05106035102805001001a4018040003010070f01c0b070f50100441e01704013414030b11220783d503c0442c0d00e0007052080945a603980080d041002203024803540a044500d80400006843c24000c90342e02c9020325903c030307418004024a4180f83e640788800301c1e0810f40c842c010400b018240107002e0741e2160b503085807035800310b441520750807500710002400002c95003002c81580d29503030035a038a480c490200300c1c4040d1f000e00c00c480c03050812510140800303004010341030030004154400050041c40d00c0401074000c0141882c0c000c08043e140c4010400c684481010041c1c45120303150f4540490083c468560300c4051409041c1c0c000c106003103118014100d00c1801c94100c648412500101d070102e6100b8071400c101e2802b01602000029480c800f20745d400319000781901d24851b503400b04082511074004200800381d600044c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 439940557 1250 439939307 439939343
    0x91b1707090612030c0302070e04030e09010501030513240504051b150a050912100c0909020c21130e22051e0708010e06101d0a18050604 60
    0x104a400400311903070140050740c42d0001c214102d0700711120103001c00082024035810f140c002c0001c40c00034190041040314510706030030014101c0e15404e4405214090110001420758403901805008540d0001e0082d00700311540e90340000003161917050340c2c2d203101011204d14904514810079124a01900103040300412a160b0b60380400c08020707580d8850320001c1a41080702d0700384019203550740314906200b41e94400104c00100e0040018041c0b42d6144507255505030800c081c0c0c0c0250313090003074503100c080c1499141c1030030406a0040e08407060f00303680009086c9014601040103840713a80d000c4040036260000714245400c4043c400e41004025401c40410b0102c02d401d82c20a50000b14415107042d03080f101c0e9955090b0301c0e100941c01c6440000d14a030400600713034030141700c0d19009040c4200200420300b060f00000e0b403200d1080b0b54240009030101c03c000352442408042032003210441402c040340d40d0b14030303c1031801444010100c1c61a240c81040d40c00c0010300800006005034060020480410110701c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 439941807 1250 439940557 439940563
    0x12091a04050d08131e02030a0311010c0e06090121050112030905120c091b07060b0a050102030c1005040303090f050708010515011b060905070e010914010810091b17 72
    0xd1580081052010403c0320070036142d007100001580c02000d602d01581c01175504242c8843c0e10030042d5060040c0d0300d0010030160807074200c1143c120020020b0000046107042941d03800c00d0201c4c50354000c04e08108080c030300d42c451103910544c00007425101100d089014081d034211002604240e0305046440380c05000d060f08002c25400409044481043c400000700100751200c1108a845024000315000303e02d034001c601c41c0c1409152003011046072150340c13600701031024203044000305028841054011441d54800302c03c840450145400616200c000c480c690002820000c00a8041590310203054000030880e42400b0702540c0183d0080030860b080c03821031821140040d002c0d20191030044018800c990300401c01c4c2c40031130320b0b084032210b07002d03618141840508540341c4024503d0158402c007164528203030600381c0c10f940003140c00300100780100510112007034080c051074503540e00c6080184e4a1440540101c00e0291040c0004252a200314018035a041804c1c0c001000351101c40c409490003010030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 439943057 1250 439941807 439941823
    0x9081c02070f03020d060b06091c060e0601062a080a050307090603062907020d0f1115030619150309150b090f07181508090105100612091a0405 63
    0x45114200782c5245600244580d03c42e2400108504d45500019044e070340c890301600e2929501030440d0400c0c5249128050518142c0f2200f2940d0618101c0c4040c681c82c00026114142c0e031090301c0710f40681e4600e40c05003584480c51504072072402498001600000d0000003c1e02c02441ea071f450b0192a424552000b8140040381e4200c80105860000100424a15081c1d11420121000b254202d00b0007203501170f4982e07200700b21001c0e4010b5150300d940380c10001e0074603108100324050320650203240130400402161070040720009035200c0c401c1c00401c49601e09048840d0390818181040040303140e5801a22076003104000c00707000860b81d51500007045c0322015a184c07030125501142000403a840b0b00000700b080002030004080c00c8410800103040300d00a02901c0c4200e000c0c3c10f4070340c0186560740d01c00404034140c0da80c1c00000a2008000c2590301d281409207501a0620202c040304043c10b000d0225440c0e01d44002140101d40c0300d80e4400003181c0c201d40b14a58000c01406000d1540c40e060400714a40a01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 439944307 1250 439943057 439943069
    0x60d020403060c0c03050a0302090f04140f1b040501030b120a05010b120f030a1b084003260309010609201c1e1505010906090308070309081c0207 64
    0x3460304c1043c0001d500508441c604540740c20b005854a1049009c162504841e0600b140c100d440e04c00011416015202194410f420081d200d4203581d6401c00e030024601d1307052803042c500040c180014000341d80281c0000b804221b000e40802c2c1e8100c1e182c2542c6181a01029050300c2c40c0c2d640f4a038108560031b0008500410a1047d80100140c180c0c041b205980c901c41d03400b10504101082c8009440100b400200302c0a8135080340f40d464079460505600e2040c011789009003030741010103071140250210031000f1801d94501580d40000c00c14078645824002d181d03050960b0b110010307a2407040c0030840380345029501a580c5500002940350030400207404070383e0070710421804c2d8010312a8502070000c0742402c41ba4490000350794441c0d11401222000c002d0407426502d09a07000010908002c2004154030011640240b14800c00c0c6a503074030401902c2040c09409440c0002c1d0280d0800e0005c62445402001c1003803181c0b5041c1c0031195207242c02c50801c2c40402c0e440c0c525480303c180200c100d030b40c1002964081d0503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 439945557 1250 439944307 439944317
    0x31d0d0f0c03021906020717070305070314070501080f06100513080601080d0206010b031906030f050d080a0b030304032d080318030307050d1a1504090f0603050c06030a0b060d020403060c 82
    0x5c109040070303548100611903a03c050410072501114404144030b241c1c02150712200310351070651246080c81300210704040c04d046601c1440000129580715800c02401910000025080c2e505e5001c00e02029020401401d070600508002031070407541030300700c038400910100000d0030003941840c02440c00e040c1c001c249501154030004c014014600d0107811250052070042100e4030034074041c1811006811594800350103180d0900051041c0b0401064801c403c115a540c3c1740300030f50310900040304031603070b00e002d65405a0081c481440040c03441e0303242c00c80042c060140e0340315100c0707000080c04020540c3c40c0112007429011052080720b084803501c0f41c00b12069100614214613041c140240180960900289415114608501003c40002504142c0c07c005070601c0c000710010610801141e000d84242c10f9440d06d4201034020303405103403040360240c0340e00901603e0b440300d1080410055400250030340320880d030348982210480e03880340020181c2946501000da1541e285040c5002261080a58042031003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 439946807 1250 439945557 439945559
    0x5091302040f020f2a1212070c030e010525030c021c12080624030106020c011d0d0c0e0a0c0806010c03020d050d0b1e040c020a031d0d0f0c030219 64
    0x13100c02800c0d50700c134000403022074810000054500012440c9400398000c2d602464403610054810b5038000c00344e440f108074140e04a0f486410381200c41c12210b52018001481a900004007980304100a007c88481400d40f489060000c0c2020b0160b00d0840e6401c03004207500006a00860030b0545001d1402081c0203d42645028161916486488542e43c51410040e003080011250340c0c0d00510308004103280d00070400c0850362141069007a51013070051038094031912a41510380d602c02e081215101c446222401d4409a0210a002854051320412110400040800308400754200c08a80c404c2001e0f50011603000e400303a034043c01904003c0c2180781003000f0002100c0110341c0010b00745002e02c41c82d1400b90340c0c6504014040c40140780003800c80c0d03840b0802d054a480c4c044480c0010665034201110100001840060180c0ea5407545503001804602082004148407402d001580b0039841c000e082806014110382e6108030050701d0950440302d030304288000b0f03c00e500b0b01501c440765004004030000c1800d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 439948057 1250 439946807 439946827
    0x111305060414061e0c15060d0809040f0605060c0105270a0f05010f2a05130b090303041203120e0601051315030f050a1101030506130207060605091302040f02 69
    0x41007502030b91074001e80e030001e5007240340d07460300600380d41c00f042c12040551241c070514443c41e01c44090411020b4074035050310108400d4901400e082d42d0301036121522038607010311101804080c02c091440b00c14055a03403e400600b50b2103150082c60108100800000c891a1010060341d50404000a050303449407020100c80003d500024540c070103681107214600c1220701031804074007404111207440ca06a040c400407a4503d020754800702c900040a00e0352030b0070316aa03144112180d01030200c140030040c805400070000f07003541c1c00007440b60b03260142c00e481c90540c581c0a4101800343c0c014044001900007265041c3e80d100a00c10304040303201003c0a094694034000009000c400d40201c17280c13900355514070124510054400c210002c41c1d1041d03000800b03580d2800c00913181d0207030000c1600c1c5585c080c22045540c0d880303440f40324480d020050402140e079100f0380e072807002500403600440d44143d035401c01040d0742d501e0308040d603c40c2d0032852519804861906c1440103a0b0302d070400c510400382c018400341d451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 439949307 1250 439948057 439948079
    0x5031327020d1e023105010503040f1b0815090619090b04030216060e0916032d0b06030f0105040b060d0c030603020117060a0e0c0405041113050604 65
    0x16a0300316440160319030745054041d10040c402c12a810100100340f094400c0e074200305401501d6a1698102c80d008640100004d900d808004da4240e04106100c40708140455030140014541150062914224043c0107690b000c00c600002040300c5007581c3d5641c1c0822100b60300300100c000c0d040d201140b0545604218070b0060f42c440010b0104031760340b00d0040030141c0c3c40380c50b603100880030307034000c00300c1c817818249814040e407500614400007000315111180400e201340128401081130b007026060740380d2590f610f0b00c0303240350640506a00081640781e802003150000341049980e07285201c0c0041406c0006407602c1d00e800c595180c071ba8640074103401d004200400c00119034107030440707030183c0e0042480a01ca5000171464412050202022032814104202a0703234181d0002040e00c2c801e8980440200c404030382c60710603003030846280340d10608420341442421890503500360000a001100c905054455000609840c07041e400030542510201c0e074024a0300300c0410740d5005010503140076240605240346548 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 439950557 1250 439949307 439949369
    0x10e070501110c1e04240b07020a170d02071521141008011503080a0f02010e101506090602070b0f1b0109150b0a031103030f0304050313 60
    0x205024a900c1140b1860409100784031a0080081036a01390f6034900d81428020812151078030f0007580341190b103d02550642c130095080509811050300050b01d410200001d40e801070000326003041c070000d00040e0340210390010f1811502038070b02403c801c2c0ca02c00c40c001d00d0800140e100802e0115400c8903440c04039008000c22a1202c801e0080b80d00014038130348014003070300c3c605013070080340f8901d4000c01c01104c0c503003003902d019980c0c180002d0103101c40b8046c5008004c41d4a00000e40288000c000002c9618080c203110340203040a40000f03c2d098103c01c071101d041c0380e501c03400052020346404124143c0c8004e850031401908040c101440c0103401c1101c0203589644601410348020b100207000c2c02d040707902d10251001481032452010200c0403603140c860103018070b000c0c1214040300c142031340c1a40304140e02031142c038020040d10285a0a245443d0310050013070160302c40c0c1e05408200400303020010070034010f6200740e000f800296500e01e0500540c0d88148880e500007601c0001c414003030788000840ca00c080c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 439951807 1250 439950557 439950559
    0x1606050f040b0417010606032304050c0a120309120c230306010612140402061905040b0d0b0a0608010b0714100606020d090506040e040605280b12010e0705 68
    0x6600d03106040c0d085005480795400c50b01c040301c0b010500007001309121105003840c0b24000c0082c040d007030f640d480543c2520316a240040002088003c406802c000d4501142c0e0300c14000d004440301c4600c1a40841c500d0f04180c2c00150070940d1031858070080c5a007102030003004110880c0c00b50311000d413a03220510f4204190044a6402c1d100c0031500324030021100c0c3c0d1850280d0002d003582c015503515000030341120003074515098040e007030005c1903480407400355005100c0d680113400c1c0c91510141000d484c4030314071142000d405003e4144004281800030341c0141504030070000e0002a200c002400f0800c03010800d40c040e0341040410401031250002e1b080603079103281e0307000f060000b00c220b9840b0f40b00e0403d500642d5118040b0b1505d1000607100d64006099a0401e0b103e071a50601c0301d44a80c18071480d44034034040c00440891500224001035482c0c0c0c4225400001c0128007030071001c25140940041d400055042c007501c0c0c13118051f032410700e0003900f103000002c03a0200800551202d82c0000751203004a108003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 439953057 1250 439951807 439951817
    0xa0b031810180204110c070605090604030506042901030317040c05030d08100b0c0a0b060301021201030c050a060e1c020f04020703020303091207031d04060b1803010b031606 76
    0x1501100000700a59122048486814000700d010070150340b010500166060348218140000840340c030389401c0880389071181c0e00000c0d101c042d081a10644c3e4a500c8412500d40000d401c000001c04a4170605c1000d0207203200384401b020f25074219900c0c1048440e0702210b0400c000e6203100400c0042d82044965900021100c6560200d60b1541040c85130288030f50f1017103825014083c4260f2a032603109174503070312a0100540a09055071140c0076a4100c2c056401035402c0b580c40444401c02182c0f8007078030300741d100900400151403d07a020030350000804003a48100e8046100f00c005104500e40a9000d9000c1c1440b46820780c409200800022070040d40b040030f0b958856000e403a01c005544034190400c40c958006441996104114a0029034030b41c01254500c855020b09400c100c0c51100711400c9640703140e050b554003038018603854217800c001c0034210902c50784503a0b074800020b9612002c50207401c2c000134980303036114400e00301e405041c00c0d2507180c4070940c400d400150104907816144038111301510b803d4505 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 439954307 1250 439953057 439953091
    0x804270e0601080d1413090905010e0606030c0402031b04170d0315050d02040b030d020309190323010b18040b1f060c29270303010902070201120e030d0b0a0b03 70
    0x3001c00c680c400c085207002006d80440000c40c08441c607030852001d1700d103d00000c114420b0403090b5103490310030030390b545070703040c0c00000607074001d40b605802440d0000502d0143c1041c19100c40c0c110180341d0b1090340050081d801100d800034280400f445122042c00c2242402d01482d61446020000d8540600400f8450041c000b2000150740301c80d40490f8110310041e08a6a03030b1564090040d42d01e03048031035040e01c503180301c514521010601c6240c0c801140d5002440154044d1481c2203903800300d10800c0750307010640d0380700045211175807020080d01c00e2450070701409000d8107140c142940c0843c0024000d600f181c1d200020b8402d05c0c0700300362040e4101c4125180001c0c42c0240da281100710601070303400c021003034000c07266801c0e00c50744c010200a000302003110349034900101c410754072503111261500ca040150401e01c01000f502405400900c034283c0705150032046542c125071101c003101c4c003000124110b0391020401c102100c06901c101c00a88004441ca066014941400810304c2e1000802251441401d0a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 439955557 1250 439954307 439954337
    0x60105061b0a20060705030a05032a030f0108030a0c06020307050d061509170d18053a080322021008070f03091e0804270e0601080d 58
    0x140c0710401c034900740c05561200c096418a00c00703112128100c00400c611000c15040985090011101d001e584000030b1418034121100030740e904c0c0c02c02418100c80303140c00760002c4600d240024207044529124049540c581c00c001c102c0d800e50b074405810034141a482084080c141d2900050030a8000364130040240e030329aa20782044409002d90480c2c0351003a0f09011001c10030b10f020100306c110071000d0390b540200c61583c0b494841e58035401414800b000b5006842d420304c0c1144901074854042c03080a240400d13855803240810210071503003040b15081840550615094401b90408801e60307600d00300c3c00c0c580d059441d113600307401d44030160114210802005065038828041104008581e40003005841c02070603100d000352090600711040710010300700c2188240715502a2003401d000d50b0308200820511062103400011230545204280e80c24003090000107100d10020305101d048102e60120009a05005400078040d140720440900513a00520014828810000b46c00c00b1000071502e0b0006922403042 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 439956807 1250 439955557 439955587
    0x1407140d050414120909090114040b1b21010b0c0706181e0e0f010e011203020a0501050916050a1406071b062a030503130201090e07020f060907050306010506 69
    0x3c0100031150281e802c0207131614030404094000e060080c2d0303428615a4410f05214200c0700407030703a50074508944501180200d01482015a0f000c5581510300203070f0b000300c42a0039102e41090f0554241000c40105041c01407110400003401000039140039810440101221a1a0106402984204000d0750442458a985100d03d800180303110307200344103090602d031003071500329000780100004900700002044040c00c0205005040340d59030070700c0160716401e020710710010b007020010941c00c6100700480782011600a2148501402070440144100c040000c00c8105507102c9511842c0700e840c00c401d080240d0155040301a42d89034045403615900c2044e40382c40800d691a4200c00842c900ea1603401080558102070b1070406407a4040c418850024290003031124030154810007000070700140082a04a48494040740d03040b4414103000001d00d44a9a040c4100c48088802c1c5005a0050760140800c0c103062001c2500000524041d003015401d00b400b02c0d540c3c2c0740600c140b50168000260045050b5004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 439958057 1250 439956807 439956833
    0x51021032721020616030c0f121701060f08130b010e0603070b07051b03070e27010903090306050703020d050a020a0e06030906040809060d050a0603050c0627150d1407140d0504 77
    0x22048c0c8507110b80203400d2012224072a400300c035000ca039400c16031301c0000386980200c0c0d040351642e80c1d030356100358089202100c0441d0094a44d454283d852415600020384542260707010300009046041a4540702007014680325031a802100081e60402c4030078041640451500c0c900e1190301010717940010418042481d014080d40b0801d003900d040414403c8201c006203080c1517100c102441c0307000070138450710103030300b02c1e01c013504e008001c980003490800c000b50441d04a036078090740074203006040060040208060320402c407501d58800380d000942e0620706410051080c03070004280c1f0401d00f180b800f02881966810045c0000e4031080021480c01c9095481e241202c112074145c8400703001a0902440e004041d00607808101c4070380c02034681008850601106407060409103020841010300740914960040740c20800342508412455004819120a240180b07041e03e07050100241222a200107907440c100040c2114080120244000101c4030070a4251100c209546500060340c1d1141c0c40c05524080c44 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 439959307 1250 439958057 439958063
    0x30501061d06031e04060504120509090420030f0309030d03020403050304121b0303021c020129040b06040b07140d0c02040e011b12051021032721020616030c 69
    0x9460810040200c40d1f08010300a601c1030400300501b24205000f900c05009040708540c202000100040214a4107581840c8070740883c014a00c400141201003820000c0d50303201000180e02c000f6a204007030408002a00c0140010719003142468150340d03031540c5030b100760310030410403121a1a501c01030110790200319a21111014103c0c030b42960f02d240c044c2d1102002031411002503864000c3c0c1e81100c0c0103005460581c1d050a841060210010200d40308000000c0c44440d0410380d02d006c0002103480d240300800c081e0a82c4540d998a0f4403c40c94081d4140c400c800d1010001d07001a04508030907038200c07280d401c28981c1164041500d1408a814a0051020b43c602c40010020702c0030520401e500682134140d1000c418009206a9a07003c9880c1040c00740c0f885042091a014081c0c01071210b694100c00070103c2c82850039600751101c4c0c0403403003031440341010ac8950640040404000d00e400080041184440705d6005910748105c640000320a4041c204070304003c156a040306200301403140d004c1010301030b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 439960557 1250 439959307 439959361
    0x60c0b07030f0f1e0e060105010c0503040509010608011701140406022d0a120b310204080105100602010b0108061302090d0809030d08090c042712030501061d0603 71
    0xe41e1003564080c0030b07407145a0f8024100700c00d0180c0913201600501c00e40b44c400f40c0c010506a40b814004581c1c40c10040c2d01690503001c180070216a5a4603040014002c0415646441c1c0b25410125401500015a440b01009a14054402c3d0918255070350b07403076110b600100c006841d2400080c1c400030301c1200043d82d81c06103403800e049841101c10040500f030016419030707070480c031514045c1c050002c17070b40850007440d07100c035111810164202110071001c000e0024080b030007811040c048800826600147c01c49010307a5104e404102d40803400b9240c5c02c0041c902840280040c29070800040c2454101812490084000030b003030689d074500c90340485031f41c0c210203468441e400165041141194000d00765042c840e000310750150030000d02c12486107001d80f8090018051100c051810400103150340700182d856103d4440c2c014000018210181c08020700490034102542c6a00d24002d040710816003082050000300030300c14038a00000d064040100806844240d9a41c0700e040c1803c0003d1112050301d80024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 439961807 1250 439960557 439960571
    0x91f080d08070e0f1003060f0512070e07030e07090c0f03050c0d051027140403020601140103090c060c02191a13090207032c09060603040212030a090618060c0b07030f 73
    0x9a81035100a048854040b0030800719038540007000440c0c03020244032b1041d07031300140e024000d20a0140407075821640505000a2080c51000203d05001c819401070442e555a2580600381c9904400146e6006c851481e042019182911603524039000b44241031134119901c400060307071024029058400750260000300303a03c420ba0300d00051209410520300550543c1485141140d4180004105001d1a81a009090340c2da00340000c0d04003c80703600c0c560306c0c10162211100004103030505804e02c086c0c40d80b0343d40c1451041380d6005100d0f11000f41d00c4842e0907454014410058464240c640415030101c4029031981d5001000300403204041940086106520014204081680000c440c840c03010302c400948441d4290304201c41c4100021515040d0008400f200150052134600025a0310034030003014001c41c80302001e1802c1c0385070000c074000804100f026506010a17600206600c0340a103422a03100c1c10300d402d1000041c50900060380040032555990041000b0314003d42041002003141ea500b08101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 439963057 1250 439961807 439961839
    0x50a052e0f090b0a120f031d06030a0902040c08091b190b0304021903020a1809050d0509010905030a050c060a0909050c04030605011d040210030b091f080d08070e0f 72
    0xe03d800382c40188100001000020050300d440345503130a032a04003402e8a20408a52000d88541c207034006101d48101011803051036079a20103015500400b5401c1c80014145046c2c4107001c1160b0910188c502805070601c10840004400990341903102d540c81400c40c62401d4420100b0003c2c0468070003070541482030100898010b00c20400740d4400c500880700011310042000f103841104800307000107504000081c00920500c1820000003000300110400042e02070520b80307450b402c040741c182e40e110005800040300a0f6560744020030301e010b0070007140908200111507840b60398bd0100215821301420011405015050160000700c0040840100610403403922009440d2107610031300086491070b00c0c140c00441c54407941840c1c0064203051019500f8191115000c00c00c0954803000000708044e19500404003079110381502d0750140340c444604542c607458040721280400c609400c030408992004803030b80000c56116403129000072440c20110714180c000004105050300c4445030301c0d00702c500c18400300d2407 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 439964307 1250 439963057 439963061
    0x405071a090315040b1f090b060f070303050117030a020c150c0a0b0a0507050a0507151e0923030a0e03010617030703020c01090b0d1104030209010b030a050a052e0f09 73
    0x104505c41c00e0303100ba80d607881c250140b405400c00d40030070010b2803103288117005686459201480344540280303c2c40c10030040b4070560159030b00205027100001e460314010041c248000d422061502c0c50140550f007040d1580800a50f504004600584681d40d449285422400000304036020350720b040064400c2d02d0003c1c28642c000d610250303a403686031860040002c50341d610603003e80b603031100d040d591189482c1d4152138040c04600c100312245070b001d80e03c0081c950460703110035a44907000e035110301c04110034003182451040d0694204403542916103071016050f4407500801158181c90090a108030320440303040202c1c3c01001290009135440045405583c04140000080c0500510903800c845080030039000450315403555104201080700c0c140151140907540d500403540707030784a80004605044e030301e8000640f906404c0e40440382ca08400400c1c0414654180242d60340700c80300210034003840c24448104211041001c08855001101c0c0320b90002d1080500c465000408140c0044110252a14000c0380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 439965557 1250 439964307 439964311
    0x6061b110f10110d03020301120b0402040e010c021608030c070501050f04081207020f01021609020c15040c030c0e0f040b0a0912050301050a08060405150c04090e030a14030405071a090315 82
    0x81148a80c408011380036200e4000c49059034181300c0c0c5450000c01c079940303480311440090003c0340e200e600d9201d401c109d8202485900100d108503030082c00c03180301c9241648082e542580282001e500100034001010b4000a00b817001c0750750a1030415030300e2181c408c0401c1d080c0216048844c0038001e044030148000d40c00c0019169407070088410041d0204035000580e6030b480c0395903291226429003c0200a0114030350302411445000100340c3c1d40c1c0a0b1000f40c1c030454001c04450848170440003078030074020b210f03800c105900540f42c1c260006030242040245034001c0750f0000e10003010b01da400d100160410340950040803000c1e90184000605100710040900b494009001ea14003807401382e80c4c00a810140016560300454005015003107c081965a4440582000b40b46008540d010800065903030550b209080204a41c030019540f520320382c0310010b2520035080c0c0e150004520600030710010030800b00d02c0d9000c0380c1580743c5040c3c581000e4600c0c50000e000e12840c256040c007444150301c00590310550070f18 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 439966807 1250 439965557 439965587
    0xa0501020a1218030c0b070507061b090b03090a0f030c0b1806280c110303071206240c151404020901050103091a040f0611090406061b110f10 62
    0xc48501c1d000d04141075240307550f0b84040c001030280d1035590042002e50b41a45d411001601d0064076028280c0c0320301058a10b907034120545c009100620b813143c07030b51011203800a01044c01d01c140c69401c2100d0318030341c7d60121010141080040008140400d4080c041e00d00f45183c0c00300003040d2074a080c1724a5566424040000da01500804000603000d1240c9010620222214180d28108100070781454000740110000007041c021106a0032020900c02c00155104a1140ea9900304141035028150140d44030340e480340c1049404201c142084a01280d049901c1d00480e207003c0d4226411810300b0204140b240071019a410700d844003461017406908202440345009035403820251760380380011030885aa1071000f8092010800d03a12110302401603070541c2250180724814600303205500e0302c804071394003c0441000d0850006904500d0304107802910024001810120807081c94006c4200c00c0801a1000904505884205041d41d41e200010f407010000c0c0030b803040c4000071100c0405801026154125 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 439968057 1250 439966807 439966811
    0x10b09040b060313060e0f03030c0309070503011401090c18080c0901120b04170705100504030e0d0503030c0d09121107320d05010903021b010306260a0501020a12 71
    0x6001d8074204901100e000707072200002140040c14035200d041c003c0c000301b03018103100d029440c001c400854040001d0340c069100c00301d020f03580e403d0918080f8a8010f0070b0723110a010380d0411407400118800520700034110307040c0060105024010710403c448a22603220614410300441d000407800d90400103000c0c010034026594040141d0b03c42082c440540702c01007004000500c180300140014a14a045d00d0140e50008a00c50074082c40c0e6070b80c1401d10b0050019240555915400c1000f850351010042210369800d41e8280707080c01c1c02c0c1e241c0a03160312004111410140000411607064403d5500007940150416008aa2041440c800038003103481c2d412211102e108508002c100c0c001189012410b05e000066400c11b44503c521015941c50400c01856a0050314501c0030307800306800703010340750b039203882940909001008210804100c00701d003a8000e04042c0b92007001c4c40400c0c0d081e01000d81000e6103140515600c0380b5111b00520789921080000c00ca54001300ba0554000d401c00e01c0086507420800342 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 439969307 1250 439968057 439968071
    0x312092104050904030c050a060f0227090a1503021201020a09270504031713050706020102090603010e06060f070308250f030b0111120c1c090312090e010b0904 70
    0x1058039501071401841da100550324013050000b4014000709901034803860940e05611030584400d41201d45604072100c42d6600007a0401c001c000140ea42d907400341c0d00816501d80c4810340710214142e0b5000404200410b591020a100316442c0c91300c0030350065500074903030068660055141c5000c1e400c0010b01801180c000c1c80d0104501c10500704900c51400c04003840005200c4030403c2c18064a006042030f801c1c8148009040e0018951020702c610500d021401020b06032018a0024602440350f40308404591042c04004a00d603a0b03407040364111105040d4111554840000082c424031800f1184c2100d040009a603074101038015480600c507040050221408422a050102d403114140d0031030301c00078400c1c09031075041a010f6848601050018500080b0110940e05c0c0e003440d110622148001207180410b01c0d5401c3c0c0e0b030402118203c081020340b17401c6001c61108000d08241c501c0e0100030220144801c2d021101442227081d00000c0411002905240d60345101040050b03101c2d031010f83c041c9060000b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 439970557 1250 439969307 439969363
    0xb07110f01060b1903050702030d020a0915020a120513050f030c03010e0601061701030f080c0a020a08150a11030f1305070321080103080d0e1005040b0f09060103021003020309031209 80
    0x40f0b041e107e8104e5030084c0d4034000d074040c0414000e502c0b10400106124890002189104070745200790309441040c2c008080843e01030a140b0707002c4000c07441002c200081040900c0700c506007811108115281661200d0740102400300090401c468118465055840d100d00d41019120008401c2d040313441507100d011560307810032601007000b81c003400086d0420a02c2c81c90103000a14060041c03041c0020342c400d82e0181c60643d800144100200c0d440100c0e181d000160040c451070074807682c0da801c82141041042884c2d1420307007100b40c074040102403911603c0d2030750010740d41c00c011502d6860400e5200041e10020798a03450503824403c2540001e420b00313114282543c0340c0701c0c05221502c0c180c98002011070704004c240a8070f80060560100079000e02d001da4140344801d0030f01801000d005070f01c611842091490001e100c0702c0e40340c40c01014000c4a40c48a00100056241c4000141e03e603142840c026a0f0b0341e40b06105145144205050704450318044820404c100c2c50102d0b600c40c0100d804209900b20380c00240c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 439971807 1250 439970557 439970561
    0x20a09020306150901110703060516090812030619030804090501150e09070c05070b030a0509031303020904021807090323150402210703110406030b07110f01060b1903 73
    0x182c405401600704805400c55144400141124030b10516088503001e443d50107040c107044213030384215444c80c1c88100b0b0011a1008029906441c0c1103031419156452800710340d6595284075a000305550480080412925112181e5038011a9008075600b460540c1d20b2800c104076a20901c9140244c524100000c9808070800805042c43c26881d81d50701180a803078001c1048040029280e1024020005219000954107100340d1000344402031595450307117031058031282a12401091600981c1003000022415500c1c400d014050301d4040c0d83e840c1e107541e104e201040031012031440310702c1d010313240d05d081201041d44030980e441541c1c840d060304100c005c103050310540d5480b1a001801c041d41c001c680700809440b41480300c0c503442400248090302041d4038885201c8100c541d2501324480d40c00c01d80f400d009020b100c01c0c07850010030080e80d00300b2403541386440300d064200d40503200700c0400c102800040101c2004110481220034040000c1001c1641e1300d15625995016881a6207c9076a800e0201e0200b80a8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 439973057 1250 439971807 439971811
    0xf0703090807151d0319050601030c050f010f0f14120a15051e03010b04021909060822050f0115140609030d0f0203040e19050a0c0203040b070305190309020a090203 72
    0x1540301e0b0000c40c00010400e01300f60f051200748a40502c42e42c102e00030100c00000c456421540200c01425107541503042c5001d80900607003000780110210305180e40240d03407000e050104068a4a080803000485040c215240070142000c21507521003c00d0b0010061460600213000355180081002030903e900f08204291446214031076000c140c034040d04000b4146002c40c0f01142000600006541450100240c102d0704200340c02000e980c9805401400c01b0303001100e40b009010542481d000c4c9242103401c42c030402800e0400c0481c043c11242403241000010011051a01c034010002d0000c03440c2ea070821420280544244001c060408070001d0540c1840c80854140c40000750103004100300320001503c040056156290841c8420040003170b001581c0248140581c88220940300e28854003510702d42074500160220003001d140804010030305130000220340440708640741c81a16083c0608042d9110b01451407030694000600b0711040110740d055004084c02da01c02c980c0e00c06401e0700c5964a01c228001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 439974307 1250 439973057 439973099
    0x50601090503030f0f130e060315040f03030c050714010b040605041103060d02011e0504090e0123130c080c100f0504030209041e060e011803090909080f0703090807 72
    0x41080a13a0561100c2e40042c03040060902e18a86009101b641045000c41c0c0340c5e00171120600e0740c1060040e149014016120070f1b0000e03401118850800c2d072550300d0b5001c3c1d0901c0080c01c0c1030341c1d5100300300c0441c000c6058804040d000355010b558090700545a41c0a03000d50618188a41d141c06400305040c9841d00c0349860101119040909680d07400d0305004800b04070346c6041e41800320842070800580f001040706060120b16980e20350f1594501401c48051303e041032091150b07641803180303580495400b07001170447c15100540e11003540d1140c0c0701c00007408002d120060041400c42c20085080395000500c04000c000a440d03000d01000340110496841640c500c5000004030100320400141c0307852170b80c07150014000d004241381b04801080701c41c41440e0b6000c046800503142c88050380110420301c00ca40c451b8041e00800d40e40d8001c20384e4001d210815038001e110445540d483e4010038001c55900b41c6994240100c4c0700c0f9034480780390a000d05190b03070034030407206103214401d00072500e140380010381c181c0362030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 439975557 1250 439974307 439974313
    0x60d08220b0a0c120306051309020a140612060609040f05150d1a060301020d02030103060504020108010e16210c02030d05070f0905010c050f0118110d02030a03051305100305010603050601090503 85
    0x700e19134031485055028241c92040585491b80803440741d403444442002014101000614040030b4410300001991a60111412030089025210740b52180030440c0d0003030b010041c040c1519901c0c08000782e118050848442d82041c0742c0270304107446007070aa100c0380c0120044420484840d01d82c00800451107443c4034010a2406491540d8070030741e00c4900604c0d00046d0080001d0b091016000c40007089030000d03402030340d1194a82c1e0a120035940c00401039409800390100b20a0107250008030041d28130344017102c2d442042a00652850003900324100f20b452082102c405100b41d1011000c000d55a0b042070400c812640d280c200070a07102c90045107042291281d039128488038600c3e280040d10068684601902c044c0079031480b80789c1240003840703070310940a0000100b030001130042c1001131149031401521802002e0400040c000340c1c3d03001801d841360562610f0002c7c0e42d0009420481707403907125584490b40042c85900b50007040c41d09500305070b060302c100355001c000070b680b200011241c4018610030240c050b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 439976807 1250 439975557 439975577
    0x130914070f2a0b060405060406030b060f060702030102040306022107020c100309060f050a0608010b1c141f050a051302010f030204050a0b18060a1205060d08220b0a 72
    0x64000c2408448000895122202c14000c1c09070008801d060140d040740c80c03819a4040144915082c4200703074108030140c43c2086460b00359500c015145002401c650710804103c0c0b01e042d440e030b451104132803801d64058003c4d920b031a03607450490b0103504240180468140ca48a0403200c501c01c00b020103214150680c010400b030034030700c1e00f80030803c203545581c5003c0540f80d42404011545900521101003120640000d9916010004204a4281303400091241c2d05001c2d03200c20945e5110710a51420b0319051451030035041914001c980e02400b0180c1a01c2801458030075290781c2d411417000f1800d03080450f01172000d0350324000e54404450b004c48400f0a150440c1c40c1000140d4456804102020414280140b0f000d44910004104c42243d6020804012001450000d01c01107043c1880314424140d82581c18595400700160050119101c94000250742d40700080d001c1c0d540d40800820380b900141083d940e4074402c0340d200400c078492110140e800c010b1090006c0c1c400700c01c0080312808541c603602c804442d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 439978057 1250 439976807 439976837
    0x360621060601230a0806041d060103021c0308160c051b09010911120a0204120f060f02040609090c0c060501060305160f020c0909070305030307020a140d05040302091b13091407 77
    0x5117501504480c3c01c40d6031040220b50b17038200400c964128000c04801451031b0341c514030410280452070302d1103510010040100200203a0030030202c1350030000c10703042c408070f034100d4013400c4400c241c032808042c00500ca8145051111071891100842c030060603a03c00d090380e070300c800441040e0303201028011143d00c0100007500d00b01c040242d10a4100002241c09860669184001c9072500071604043e00c01e204501d0030782d8200720542c8100e015444000d90194100740c0b51003009003607039015200d6600c440d42c8454844c00158070030840020b00d154072903820001541c603000f00030000c2c00b0441c2c0031960446212642c2240c7c6000e0b100c080e07a120643d500400c1442030301e0040c08407180c0e014041840b6071080c86000302c0002c07802d001461003420a0390041103000740a040031070000170060641011034001060081c02e05920004940076a50181da00207500d4551125551800e10034002006014902046220750381c803103003255600f102d952081c1071118084c0c1c030381b4507001141c003542c00e100400c9500e4960046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 439979307 1250 439978057 439978067
    0x60901021e0901031e0c0305060f010818011b030501031506180b03030c031b150103030e011d040501030c0501090915050d0c080d0905360621060601230a 67
    0x1a42e4040c500402d042c0d035440d94849103565072a54503611180c50b42400d2002541c180310b5181e00080131506031200d0807000e00040d104080160038920130185068080000c0c03402500000030801c40340d21680c141c40c100650040080600b0301044a011001c110300900d20340b82401440305a801c107241301004da03c4490500d1009000e28418150180014000201484c00c1840505000c0d00d2a084200f841c44c0c90b02c00260030403507190801c40c0710f0760a62005001103548540e28290300e800a00303001a50f4407000040c0094030980f01505a030080c1040008410000c0d00b6000c0001c41d0000c0c1c9400200301e40b45c02c004425202d42c10290180702100c008204828030346140c01c0c0c0c01045c040d660042000ba03c840925003000d100b041064041284c0c05410400c900b000191000610b400040309504a10403600d076800c2c051112a15005080400000c100a95280d6580c08155520343d0022941001d071062a44e403259006c44002d40460ae07498202c0800719000c090a0200c51400038681d881c01402c200d055071 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 439980557 1250 439979307 439979317
    0x19200c18040c0504020a180e100e0103050c01050f04050d1b090e03070611120a15091b1d030304060917060606120a02070b0930090103091502040b040602060901021e 72
    0x1042900040102c01407107c840b00f001414a642544007540782501c00c180f900b101e0b991009ca440007082004001040f004514652104024070b48290740d4164040c190149015940100ea4840e154509040400c0000c850104080c0d00d4903038400c2001d82d889201c00111209850980803a4000300b00110010b03465131722002c254801c0100003400d03d101b2408400701d0280c101d440311011a601c1c1038800d0400303a220308110003000c0a078000d10800c24580e14143e0b0210124235483c050024603811040040c0122000d280c0208001c1c0469466a0b500e0381d0050100309540b090302d418004000d10060908400b0400ca48601009481145000c080e00c81400742140300074582c00503664240019000142e00841c00c5010302c0403c001030801501c0080820741e02040d2603007820000c4c01203400c7c81803002c40c030001e6600390300c0d09013400a5070b103644c0d0800c1c41d0740742004600111014800200420b015000001510560394181e0889042e030380d481c1403640c01c03031117081e604c2c2c1c03070800d2458208072340002d0400c0108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 439981807 1250 439980557 439980577
    0xc0c011103040306050106050c0c151c29011e08161b0602071a070e04090201020721051608070b03180d0201021c060b19200c18040c050402 61
    0x20300c2c0550ba5164501126400e0304108006140081d9a000c0104200440c2e140141c0480700c51a03848100c0180320828401c070b100c030105401e800d40d0300d643d642001e50711150402c401d00e03616121200c040c144010000b4034400c042400304040300e00c1c0003148600c3c0d80200c0710504198499503142e449000c848812070015401200c204580c03215000300c690360044041c07980c50f100d084003603103030542440c10303030820080030340000d4040703001e5010000907a0f40045250405c2c901610b00150500301800101d05085868001c03105106c2070070001841005622031980c03460f8002e0040c0c03505104803000503a035842d4140706407122a480850180141ca020170021604000c010a411003a825001c580c1410b044850081d0b00240c0d501117200840701120300b000050f80400044100145030030185d42d020980905000c07100c40b05030950801c54800c1c0107010721103840014941c0703490001c0d41c1440c101da4450039405c81c0360240641010400c00d80d4074804282e0301035a801001000c5035030504043c08020740110001d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 439983057 1250 439981807 439981813
    0x606091216030f021305190b0d0822050d03020606010f0c0506130b0a090830040b060a060c120305060f06040602060a0513021f210903020f01020c0c0111 67
    0x2008080c0c846030a500070341c80349460f40306041c61801000b080300e0344207031549107550804007001000c070505408020303000408180051500340c2400455624a00304000500052002a808030b160582150f00c9403207501209030400265115428010240c1000000901580c00f882c00304845600511429080000f2841c000703802c06140d4503010301d0208251054000c01581c0f50829041c4240186c041d03230b0104140ca03060140c0d140f84e54824200d846014a110841480c03040c80e07021541c1000d4240b180008480003c03402c0c0d0409051031004100b00b55401e901c00c81c029040040c2c003a000c0c2440887c82500101d140301040a00213082d405484000d18280e44400d4000312000c0700d640d002e000d4400341a4543c000c1106142c6200841c00300c480180181d000941e00109400042c0d90300d0321003140d0b424a000f10441c1080e09100b0940301c0ca50440c0d0a465060b003111000700c0030b2803095101c3c0c0100d901a908480e03054040c011000c0c201d11419501c00f580d504456038058a5500640b40340c1c082c12218821 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 439984307 1250 439983057 439983073
    0x40f120317150d080d060504060602070909080c0102071b0801151203140f0408010617031c0f09060c170f060607080c030c0d18210201212306060912 65
    0x40d0001080410489403002c021031117040300d20b202c1c0b2074200a0441514100041d83c202240a5a9501c107403240e80d005c80c1d103c44815003040300720001d075031445851400a64841d8121724012a040c98445050001103806a50004d900c9905000381c1c031082054410380b00c0681c0c1851054a0340740d03082d030000c1e0f092180340180141e450990300300800008940115a03511603003032080e81420349850f503006010340d00d5407080c103a1204402000b02d40c00404006000c00445030551100340280c51700d019061a428600303001d03002849540e4001017210307800c90b13842104503021140e0140c074201080c0c8100b089400074500040721418641c0c000d1407010301840040b803d08808021481c07855000401284150f04440d10003071505801101c038800204800402d20881400d100c00c542c480300e030b100f440d80c85140492019405590040380070401c4031021059a50061111005140282c11012845410b0481c0011140841c0106c102c5107401040000c1c00603242060360303010071a00520b034211a115a00440340 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 439985557 1250 439984307 439984309
    0x1403030c0711120a0b1f03050322080607030507030522140a062405180627091c1d240403030806040f0e1504030201020f0c0102040f12031715 62
    0x3003861340303a10580c031003009440c06800c0c0c030700c0700542c0b4070b60803000c2580140c092001540c044180c80c00b2095035202d60680c0010b410030515418071590140741140a82801d01c9801581908200e1080880762004d10013a11440c6000f00d0300200d007100d9000101030300320f031200081e41112071500005100300454944110a4440d00200d40b141078105200d20b05030681d040701034503500c0184000f8242169004601141c00c0e0740c50082d036030010100c503ca40e0708054003000e842d0100d0481525040d43c92049050362901000c0641d883e02d018041464203042105425441d5105088464241c041c258003801040842c030244030821001605408564042c0e99140903140c2c25280500f004601076a54000c071801c0c080207020880c1c81d41c8a103995280e003003030903a428002000540360340911640c500d4082940c1d80d801c040b0300a01a28501100042c000039803207001d10070540182081d2011103a0960071242e8a01c001060305611110040206950b14000744a00c20606200c541c0a00c1100071310381c517804840c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 439986807 1250 439985557 439985563
    0x1608063003130f05010318060504050a0b070507030e10051e04171005060613051324050102060609010819030e1009060806101409061b06041403030c071112 68
    0x10440150390b8645003001072074807200b18400144000c1c01d04010001c40b0f2900304900b06025000500707500d4131070004c5010440200610001290843c107140032034201200004c3c8140d0000c0006c0d0001013200710201864904070a032010441717210303140d0034603090036910b00b5040c4105408a0014604003800700090b1100007486050501450b000500141c040703e041c00c404461025044078010807051090721441540d20180200341c410860301012603561404065015043e0340503518032110290422031003860701c2100707800641b2003d07002d4403015910310080c008803640034401d41405512044804014414034042c2d500c40b24064980a802c0342c04590100390700f800c1ca200d030200000d01081d410081c4039440a90135800610440310b44000740b010b03e00041c1000000b011964003502c00240301142c56488500b29105103e103c0421454000070314182503c80e2400ca5050341c10381c006040c12842500d022080b2071282c1c052078900c600700301054441a8000c4500f2411a401419450b002e0030310090030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 439988057 1250 439986807 439986817
    0x60406080f15030a020f031f0209040608060402030307110d060606051b160e0c13081e03040312050714011a150406090b070c1d1608063003 61
    0x50311064401d060103070845030807000007450040160322891500c800342d9004600540340b07980403103104170324018500000b0b0528644007150343e0002d00214001c990300c6d050390061701c3c07500000c807400c000c581d41d1410b500c0e84540044034001e515400c00c0145200145010b00015189400507080d52070702c580d541d9444040b1540340c1c0040d00815030124400c809038000c4868a00030310004800b40c44080c524503a104074180745800355280d00c000b4900040e8054040d1403c0d51510041482c8000c3e000341d4909555442e43e2110102c001140c41e207184d10000c961000080740d0440c0da101c00c150070b813060340000855883d0001c7c401100d600d4101d008144042c1e2090240c0390b502c200e1b5401800c000820401006207006281c020408200001e101c10009180c010003944100c0740141d09081e0ba0709010f142150a5240742d42000030407e8100b008030384040004a04584500784452080d0311000240304251120107003220303020341c40f00c0802c0000070420303a20906034502e0010000f003070b40c4500d02c0351070080c196041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 439989307 1250 439988057 439988069
    0x7031e030309141b0a15030507030e07030602090f0103020c3711130516051e16030e04110f09030f010c020321061005070503130308040801051b031f050604 68
    0x11138100c0fa4030702903519090b00c048000482e240442203242101c0341545000b082d00c00014543d40d4400a03650314002d4008600e03120745036090310081922072074900000e4011440e00c41c024040c0c10203000c400d5000c1d05c01c544009000000406a07203180c12015030403d1050b0240d0b0040d0500c0d4400d29442c101c806403026410384c481d501c100b020a445001f8019040301d00540100b00d5401d04040c0b000700c01040407800c01c0005580b81c61542d800341202c0d8061031489603007900458507400500b900000d80851901c40c2d01740c1c032075690541d0300001c580c204025507010311902d1410190030040615038000100050065140180580348180e5280d1003850031103801c1380e181c82c0580c0001816041c04010001c1001c00d0100d4440621000d040001c089440381411507410030510100085020500c6000c01c1511240b103502140300084544929004030213401074400c0850940c240004103400181a001d10792800d000342e41c140e4110f0380c583e21100c80030004001162808090890302040c9501c43c04020300140c55 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 439990557 1250 439989307 439989313
    0x13090206040e1501020c0604170337020a0803060609041515020d030e30032503020703080f130506151002060108071a0c0316120207031e03030914 64
    0x152015500300c10101c450203d904540100640c85c0c1190394071020303602660010001c1d42c4400301042540e038611b2213005000780c4808010541804602c0200d04004501180c000c06d240c0c0b5140000c1d001e90785c82504410050003100144001462820044082d0100c102c00400c003240c1c0e040103102180085005400030010240350485400c4030580400101c1c400454500d82048400303181c100c0240c0710007c01805000c118405100c02904892404d0783c820340da403018084566a0801d200c070b0190b80c004110403c03541c8402c44041ca5107450080c400d561115405841d41c800543e11212405013001000702042040d0b10240034600105c1c8080090318424000d100140481100700b07800c20008800d905801c10441d070007040144030f6102c0109584041350f0b050300005813114074101d4100018021810a0507041c400451341222200d086540380009500aa40010408040d1441203840d80001d00018004040c003110240c106000340c1c030410420b074068500090008400c0c3c0c1e90f51070702c0300002c154902941c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 439991807 1250 439990557 439990561
    0x112022208160315020d0e0a0605011406070807030311030a0b03100c02060708180f03090405061002031206010e151918050d0c030b040c0e010f12080304061103010b0a031401031113090206040e 84
    0x27001707100782c40c09001c01c001c6084c0c02c0340307444002540501c1060340003828140d0200340301301010b001b174101d070f440f87c0c2c02401c04640300c0c40c0c00f1403000700515240041a200e84540f0000500310401c62044c10500e0605601034501e96885c1d11090710112405005050b0400300314039000c0c900c0301c0510190710100d0045000d5651954084104002d6500c05090248201c0102e00d9503003211741c0000441e024040075001c00002541c480005807211031300c821000d6005421282840b540480c0c250040410340d40b40011a02c1021040c10f040340c10340c00748000c2c40d002d5a4408418030291414020302028280300c4c00241035a01d0b00c966031442460415501207464407054001404248880050b2750b014000b22528a04511302e80788182604455000c009040c1040c0000843d0034000c203074019142e412803100c8019540c1d6034645500300c003940300380a02d40c0000d25060800d400a618540400c0c1200d42051006034460040d10030025803040c0c12019882d0140d07030740c00e5000141c459030040e00040c000b20004a00d94 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 439993057 1250 439991807 439991813
    0x30304080106230a15120c09050915011b2a1706070503010e1302040e0f15130201032f09010306080309090f060112022208160315020d0e0a 61
    0x20000e600b140c1c02c104034001c1e04400007a259514101d00711030f17411942000300d4907036000545034000e401c034002d0b80c400e01b4000d42100c0241c2051012045403002c0c0c590003c1c60342c2c2c1d000d44046144100c6005400160b80c00300003101c030344a05aa404105000b1004c54441d10b0f0540d8812410081500d40003200a649903420018485544a11007010002c80301a100f146050f41c0d00400d1888140184408280920080b4920000190807080356980c00380c42000300c4481c65030200e03503441003907180f0301141c4685200031903298500350720680607088003480e24681480542c01500908008602d044100500b031405449541d40e0740040541c1010301d150303880d034030b1481c1c81c0010309446103900002c0715a841003001c00850784034130000b0760388081520b01070b4410341c44550040b290442d0100100f4809800819010034000500c00411602004040e440b0402c0ba0385890040d00e90649040001061001c3d800c1040491480d0741400c80320111300c030005281101d00d1030504221007401c284103910740d221500c20010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 439994307 1250 439993057 439993079
    0x60e190b010e061e1302120906040b01090603020102060a1119050a030c08010e04030e0303040b0703090503010507020c1e0d140a26040302040b04111606060e04030f110c030304080106 80
    0x541503405401c44031321500c072060010305024502c0d0040c07402c00f131200c0e190102e65040e55480704254580c5400b80c2811080c0da95241c0041d28151141d80d441400050031404510034501142c0c6c2c10780103005c2d20f64440c0a4a8010024005500941c003001c2101d2840f201c04814862900001925880e03200c0300d85000c001c040341c02c005803035018042d1140040c401e152100307044039800b550500d0314600c05a0705101007400d40c02550300c006a850800300d204000c064001204a0070b07140190001c01180c1c0d20754600726603550051a21130340081180302070780304403035031860301000c2000080c144000d00c80559807858411480b07001010001c1e00075141503410007105030352002c081000fa00810a5130030040e0002882c0d4404c912000303104aa403502903003d191a60b0300b24003080b412030300c5401d484e0856400a41070b035003501e100460382e542c948800401c6e203400031035245d070245415580b40d00710f040d00c0040517034004c464010b8140c024800d5400c214034aa600308001c101821a0100100d011450100380f030b55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 439995557 1250 439994307 439994311
    0x703020f06011d0402010c050712060b10080c03100e010e0f070c0c062609010c0210020a1b06020c1e0c0d0825060222060c0b04060e190b010e 62
    0xda400000040082c1c910303101c45551122420b1103030080d541ca440c40113942800c101e400c02805401018000940071418207100e1100c58003a42c1c0c140305449000080180b080c3c1c40741d158002003043c80d80440c900c280c1c0c203405181c4c4a80e20800070619070380ca03429100c1d14800240e210f0f81c000c1c442d1008001241e8000d51406030042c421741005e00541800ea40c030005d10351564061941001b035401424000c030100134008500d548108021600c690a002407034601801c0c160260a015100760782540c03810101901c00c03135108051659034540350811020305021565408102519502d400340f0a164007100d0511143e144030394038131207400504070815000c90030809400b203064400c00b150343d50080401c0d010011617803401c0e041c003200855040b10700c40d4141c401c81c0c00d000c05081184082151202007403181c152201840315400b10741301440c0d440d50202e03090301c0c13515001015184004007040000e842070b0070001c0d2444c80041900c01e01300741504100350340d202a0000f0360b0341f81490340041003484040c0740696 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 439996807 1250 439995557 439995583
    0x20c0712170f0d0b3003040905010305061608090606061c0c0305060405060609010c0b04020a0810060e0a020703050a2a0c0302090c03040804141c030e090105030118082d070302 77
    0x204400e082e80d4090f1108550f00b24170001a139103514100210011300403a00900054002003041d56102c0c100f0b01e907104000c54002e0800058140030024250281c041d280c4290300f0b58008142c944d850f002440815003203900c0d0484450b100c400b0104032545580075a0840195603034000410b03213091400c11044c2c174000380c49680103a004010701403003642c2c0710921005098000720783c0600d546a03480455060401a8044c074868003501c19111189400c030f411960884000b0f01c1c408400c1e8445140600492103100c00c0107020031020000503240d5409942d0305190a61551051017124541488a0f0040e0f84a40c50440740c2080c5554180110315242d2a0300d0381001070300306918118a01079076206000d110b9801080c1100480e200c601200381c0d03500c44100440306030a030401180b50803038580940007045c60084284075100400012a440c18148030f409102c070741c02c030218103200a03251a40d906507408000c20b20700300e8080502182502d211014407450140090700c03482d5940d0b446003030090810f209420703030f8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 439998057 1250 439996807 439996819
    0x2010e01030b011409030a0618121b260a0306080708060717100824090a0203031c0f020a270b030a1a0a030c1701020c0712170f0d0b 58
    0x20b00d0560364030010044903d1203610461342d803652002d00280c40d00c1c00e03091f8010090b03803c101101040013182108440000d2081c4811080801500c1066801d03d061110000044040c1c2140d440481c82840544090010302e4090b905591506688904158800341d81d00000c240c6941082085002c01c00c0500014080e24015014605100c038008140a0864600707007680b80448003c500d40c48801104840200106021148181c040080c1e035a0f03500300c00d804401c00030002c07400144202f003012440d00c50b03c030340c02000380d40b509008601103240c0400180b2101480d6603617071068041c0c1034052000b056140c0d102d48801040180780558a10001442c0e840c1c80c003100c0c2200750411a03241d42c5801c1e6a0000022030307000c900310b000f051f4110102c46941d1011a801190b03400300000340581c4d0301804050700e0a95981941030420f000306d1500742d01c102402280a503105070380420100c2e1250b855100c1140c41141030514199a8007000f8100f5040b02c207004c0030210000440184200c210710414034041410f40311 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 439999307 1250 439998057 439998071
    0x402060714030318031206060f040f03030305060a140f10020a1401200403110f0d06051905010605091e030c0a0308090a09090521040816030611030105030601150512070c02010e0103 79
    0xb4038400d00c3d60185c280c0d4011307000440d405118403270440a0368040d0600c00781111712070340d880c02c000340600000c1c0c0b0903a01170b1107815008200350f0720b1aa000c070140c000142481a40220150902c19010b69003040c007021802080924400641c3c50680600c08000a0001042504100003000788a585241c0080c8000302d040004000050404802c00001202120300c002040c0449010038021030307c2e0640100520b2410741041b000c40e1b40f0400219500042c0d2030100010703a03d43c4001d9900d480380d407400c40d1b80712101e8400507008140001c0b0b031000040c0060269800140c81c14081404150a608229002200841c0003210b6003410741105004000c0c0c0c1c6003c0c48440d080da00d0383c03511940d107810381030011652440740162015500c3c00b02d0f001424004100d0fa0070a185010900d034401081c00226451424000403072001d940b1482564117031000100a01032503440c0003041d5054965000d40042440b02c2400580c00401c80d12041030302c5801c0f00d8643e10390b400c68a10005100c4503052440710b05152a10714 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 440000557 1250 439999307 439999327
    0x601020604061526060c0406140d02040510050301090c020303010303080c0307140f0702040605040b10050a02010e0114250e04091a011202190b070209040206071403031803 75
    0x684a40c0080e00034800107081c0300b054109072034661440c1c0241055000c4e80c2100c0d01d034042d103c0310740540c000258040c1c401e1034032105015121403003203108200c005034150440c500500881030041c481548020001450103a4900100c0c0906443d02450404a07002000401403503100c0c0c091003860302c00d030348040c501d55070440e54080c014900150109039100f43c00310008038401d010743e5140c0d40b00400d21208948035006242c4001a40d070180408900440c03c0030000102c078185405402150b100090904040e0315000004807000d4101c4104c81003150340710350692280744000c0c400d104006072070361549550f510384040043c1c42e03060305e0754403640c0c05140e00c0510741d00c0c03d602503600034002e0b10440c0c02040110349800c0844414900841604408100c40000140e00420282d040c0308a40309403807020320402d03514407602e0181d54a21849104000c01c0204400520380b0540c40d0b58414401030443d420040c150b10382c08490960300c0002403007548004140030b44c081c0c090914810700c1c112103004600d8210214 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 440001807 1250 440000557 440000563
    0x61003201e12190b090103050f0d03020f18011b150e0f210f130f0807030c271415190b03090106030b07030b010e0402030702190512040e1608060102 65
    0x1d081409501c1a000c4a100e5480c041c2c1011850800017400014556140c1c24520b44a2960540c40b0302180300e5102c009d02030034040d009455070141042c00341418074041128240c3c1800031132542a040042c0c1c400031852148007a680744591a0040050b03480c1d411404582c4030444c3d600c0c0e80c08160540c09490310010071140041c5200c480290030180c0e402c0d20100c9a0301501c60b0240d0038115480c41c101003410040e507008804044211400c1460040c0400d80d01d04070940c4074841c81c0400342c1108440c4500740112410f00c00c101701c140740020540f0003140000514041101e0b8040009441d041600090144980c4003140b40040e50008507980c06030342011a120004040c45da10600c501c072040400003411424007988194001c58100640360414607000c00c0c024014010740c541517000c681d10394800003844c20a482a680700310b03c0c1c0e070028000b210b0780100301d4100c0864002c003203509100b01c84030003903007840400103480101400071040d9141d00700354101c0c00540c44546106000c2100401c1003011a82e800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 440003057 1250 440001807 440001811
    0x110304020616020f0d03080f0c040302060a1b06020406020a0b010e09190f0609030221040e01090e120406090e0c0702030a0305130302090f07030c080906061003201e12 73
    0x40c502105001c42580302040c1a1101c0b000d071300754440c0b117034051901859000742500384108480509222141e84404404071a8021804060f41051081c4140d9001e01d0148048103a140c0c000d00301107905035001d2345e43c20f003039900ca500303c040183c00201c01c0b50200a0038810b00c3e40901801150b160305841d09031612603940d078100c00d4079685440309045d15028400c0b440c001400c02070f0010814044101d90b820041d6070746a00701c4040c121304021440c0411840c0c1d0f0102a00c0645056001000d905e0b4a01101400903101000e06241c0030f0007000e0180144100a10041004000a8a07104011071420650408924000f0025925070302c0c01c21803000140c0d00800c2152045506d41401d0380c50b151818018840030850b900003d420001c8003052042c40e210794044244514401d640510601d0403140048030700c1d010030340e4045220340c032000210300c04e45050038185018400c103280010340c02005501a10b1070074030200c0c58079101c00b40022140d400c4850000900707c1290307440042c500c0e00c00c0500c1c86100e40c00b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 440004307 1250 440003057 440003077
    0x80f130f0b0c0d030b100f03111615020703080a05180703061a03030421030917060402040b0d0209010e071202040902130e0c0403020f040b03010f1a040e060604110c100f1103040206 79
    0x203840d0301c0d03402d483c003039440030043c220309e110030a031120000300e0315440d403c0442106460044803c0b514031501070303a600860301d0740c40d41a6107040c0140ca13407929400160101501078085044d0243c507544080078104441001103000f5107020841054240032858440d2954641600982040000b1b11846543c0154050881c1e02046491105089802d0484030180550844c4103103008810014205200c00036002d0f0165000302c0b030401170460160200708406d0705000000790811805d000400082c0c00d140c3c102540440c03182010038642000d108090704036401500034a20f600c0d40412018980d4011a180101030803d000d0742500c241401c6007119014001d07440000c0c0700d54510075440d1619126030b00107014403e0045d0090001008041c03242000c2d00300341032045d8283d8401d1858417103c2c0b401c0d0294004010001c0301074076042e118981488013030484030104403201c0700104403401080c04c0c2000354000c0a42115000204400d10403012001e0311071410800003860320600034000580e449104480d90446 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 440005557 1250 440004307 440004317
    0x705010b0f010c02150a0e0307150f0c121d040c1115010e0a05060102012702010e03121804062607060914010e0d080f0702031207080f130f0b0c0d030b10 67
    0x3000400455000880b00407c1d6051300500d0300000301001000036542d000031030750301c41e1341000004003070071a03205503e050054980e80b100c4002101850142c4101024500c480c4213018074020000040b800343d0301c40459650002d00c0110100b42003120900005450400b202e2030a06175500d480c82c0b0f1007540d90060714101d0060355540114071580e00035400082d2564a410704003100a40807010450201010313a4140d0204a07111110380b010720300400d2021144088130030b00c84c00c0038040c40207401c3d2245001404c03071300256034140129208400e05200c0101c0354125000290382140c42e50700500b01001a4011300c00e1100407001800b04810442c003035050b000c401c2c1303003100c440203644c000200751051a020280074100001016154a400b1070b00030640c49000354100c1c1c04500400d45c91f2324282c4680e0390080d140c0e036000d101c0100c0c0201c11100800381e41235000c4080301201e84030480790022900660100d100c5440000f1004141007040c4000c0340451842d003010040e10b5510300c08240941007050507042003007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 440006807 1250 440005557 440005567
    0x20a1403130503390901090204060210090b011a09310b030607050f120f0114010c05031b0307060f14061002151b03090102090118031a1b0705010b0f010c0215 69
    0x6854644a544c481400074003841d501d582d6002100000e42c8540202e43c018014100516004101c9000f00c1c41141e90280912170560320b00f0102c0401c3c84580f107081c881120741000080e2842e40c41890300c00120789458061141a05054071018944503000c01d00c200b51400e203050588559004940c0550200b06420310030380d9090560011480c920070440521249281d86051104005501340903038140c540c0e219200c281d480181c40191840307400200d004040d039000b00800300f0362064020101d00006629422681060040daa03410240c9105800d212507480d6154880758003102401082ca40100c0c00740c07116101e880c40c0c1c09009482d403032000842d1841c11310880100d20000c04560f007100880d000d00440a13283c1c2417000c241c038080d50100003e0b42c002040e02e03460040c803032401d1003180200d0b6845413031074040c1c500000200c0c4614000821018402c10404030000035075103484001c0524900c244000034100341c2100400405c00039022a0b04c0c10072518800080040c3c1750a03a04000b0038140c1d0403699210 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 440008057 1250 440006807 440006893
    0x14070f03050709051e04050106050316081c02010204051c150209131a10080906010f050109032a120606060f02120705010e07030b040507080d0905010f020a1403130503 73
    0x441c5c3c0c0d084031381060784480c5c401c0009001c0d06600107400c0d980700b2000d84809900d03141826040c80224080c00350b0540204d130002000741f6050480144202045c00003504081ea0750f000200007910b40500440d8400c501d1042e00d04000050150742000c03808840110b0034a5114004a0704810180d054807103207a6407075070101d1054a0224a88282c020014034601300c242e404080201402c0e0140c034504894841c0900208070034828100c88426581d060b52406002890358817211168500040da00d2510f1440109030f1490034010031030302c40540042c200407440300b0024a8203004981c00380d07128004010f030b02c540b207640440d03010400d06926400c001486494811a08085005041c1c040c000030481c80b8640f0700008000c035002c80b00d07100724001c1d0156950280d585580d5600c0d5002c01f8994030001c1ca08210a02c000e40c091580e0f050751500302e02c1201ca2040b05a99241c900011010301c55006610210307c8520100c0002c00041c05040b0030f070301a03c0c00c4100311200c20b0f050240c42c1d4140380c070100c8500440f85c01c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 440009307 1250 440008057 440008081
    0x1030e0601060c0b0f0f1306020712030501080f151305010608010911100f0c0b07030e0601140406050f060706090521190c02030d08090c0d14070f0305070905 69
    0x4440825400d540c0256542c48001c2c1080304491400c44100390b00c040042c1a08140d0500d8510541d41c18405560581e1944030f4014a130039030030030840302a80d0a00c91800414401d404d0055440546d0320b0000f00c40d4100b4852514240680003c0311065001c03924501c0c826072106451500100401c0302c0e42c0f1040100d10700b150141440f60800754440d80b90407500014032540c092489103110007130310650601071044500b140c0010700d152003440862a003500140028955055465000905280c001200a002d51a0600300070080c5d11414240c0c2150b41a022070345080d1249000502c2c1c04c0350030314051900400841ca0078042e50740c001e000f45a07101d0402003070000600075204800c903880c084025180000c1030030a010340000001d8005442110700c2840100d0285107402e00441d0024001c0002042c0c9801c11110004014180303242d80c0107418418040c0d4852007409809580b0030b034004248a18540e141c0e900d464291380c002c500000190070104003180c808110780040d511664008500340e038070940c000031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 440010557 1250 440009307 440009321
    0x3111e0f04020c010f09020a0503060f04020105070f02030a030905130b09040609050312070801090501060f0507060f180501050f0f0714090402040b07081201060806030723040509070618030804140103 87
    0x807055003040c0410700c045d5081e074400e030b0300c0f030b40300300e03581d150064031141403540d202e00072035500c05004a840082009036000d040500119031003114a050312894543c0880d0802c00824811404558003250902551802030b020303510355203030902e0030080446001700040b043c06005d04044c051070354a260080c21b0200074000c951500d8880d4a00c0c55280c1842040102024000d21503441d07164a071400200d80103109442034400340c0c006940d0707c0d041200640759030b40107152243c400c40342256036110034140c41e1aa28060b4203d180200000100ca1406c0c21000700c0803400140400e400c00c20300c0081100741d80c0c1004030041450080100360303441d2202200441c00a01c035035004225184004560201081418802441880d078001c99185190740d0b2071805980c015019101203506800c003103000d000d00e0503540c041804038080316801c00e01c4034000303001282c215041078648580680101d0014401c0b550042c90780e025500c04404420b02492460b105c2007110301442c083c0d004100e9004100481980c46504840 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 440011807 1250 440010557 440010577
    0xa0c0207180e190302070504090b0103020621090d03060e0c030712020906031003021e06030105150712030b090c071208090c13200309060403030e2503111e0f0402 71
    0x800f1441c9181d50600c9144120604500520a2880214840c1054000e04c1c11140d448a10180d0603400c5030300700310310b1f40c01c5120b0680441205410044024080b59030850054040d8006400140f0100310014103559098004c0c9005000c2c490500494450100c12260b010145290204207a1480005c400c0a44207212600780c0c0302e44040b0610030450403c071904000c0740d100310713410382c01c03c0b00c044111446050704036100b6030b001c20706000400103420102c2c1500141903020301d07060714009690f540e00b0010000907105500007955004410307030798106140c0540e002072300381c5055424811203660708d0100d0482c661400f4100205940403824001c02080b0108400d00001d2424141c4603e40c4c04d0b00004040313644211201001c024050403051400000f1a809451b415015007015501c45d142a400f40500c1d8141c0c414910503019007070324140340d0007040c0d0807012004400035900d9180d03041ca4035241e00b40c00c01c4a8450b5400b0003808101c80040260200a1401690081070307048407500020000d0140160301 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 440013057 1250 440011807 440011813
    0xc0f0605041d06030c010e0109051507050d050301080a0210090803070f0309060914100c0c150e09070f0305061c08220506220902040602150a0c0207180e 67
    0x219500303800030003034000e6a00c50680c0d40092920306001c0790340b840c41514025015006640308095552180100800d1200d043c140308000a0f40c600c0410814181c4141c20450302401065001c1005007c1c08040401c0d00d551a00a05650402524540350101c20302c000384a18920381840307403030300c0c0115124001042c581090b65250301007400c0000260f40207a1044000403900d843c042105030044a046042d904035945080c02c0440c0441030151510b4103180900a00040d140030100107111203410f0006080c01400e441c0a01542c2034024150010000c43c1c148202c00f01e008001c4801d81c8800e102051009615012400c1d88641700850000c8078010388814814a021240384203000645004107090103120400f02c5900f940c02c98200eaa59419000e801ea20600800404050250344403074010b242a80c2d120b6148069624100e030000ca80c0654403500143e040f0400c803500c441e842400c2c9030343c000c0c1e89034400c1c00207030780201000391100030b640100d03108080a111120504480c651102034407810420131 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 440014307 1250 440013057 440013059
    0xe100b0705120d23010b0f0310080322080d0c0605070905090705070b0615042d14030c0415090c02010e060702060f0702010c0219060e0a0602210606030703090c0f 71
    0x5080080c0c07030b2500d815414a0031004c4003092264460603d07a0407600e6411205003884400d1801c0001a84041e1000907100701010000c0b440071001d00003451341800780e031615000003460800d41c103450f2406034002052078001102803030040b900114980c04456101400040c0c035078652000740c1b0507220036040a60030601d040200304056030058002c01c0b000b405000e10111075a18175041001c4508805510050080c0a20003003103000c0b0a1300807002800540181c00c0c040c60b0710003151808074002075014586810b840750225040c0d0074240082c1c02c6220040d9001e1201070400805500e203840c00303220b10345900c7c2e920300d51001c1d010300c01c2d07110004100004017501d44600782090002e40e03039201603a60402c40103102c0007107029913005125519104405402030a95181c0c480105080e0118a04050758490b4990071822000a82031014900c1e00344521001600c4082c28680030944105409090110342900740a2181c15502c00d82a01e600095074500440c80b61034a2a0190000b860350b40101040380800d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 440015557 1250 440014307 440014327
    0x30b240408100207200307031a1006112a0901120204050108060f0f13050a060623010c150b0a14010315031211030c0f010b0a0e100b070512 61
    0x4004a800361811039080b0440121102c2c128071070108001c01c03107019034051000300f01901c80c01a400d1140102aa60070540e80c0d19030880d624001501c0800b0031022034208407100700031003400005088a4075000344482c00001200c0e03505c0f1104c510f01621000c4600d911101e488103080c80501540c0e02406080407544e50b00c400140700d2100000880c81142420004a102040064000d00c12a102c907808209515252007640c140a00078100c003a106144003080c0d4081142089a203141a00c80e0a000640514092840480314036014080114035060040104030745c1c0d0007102c01202d1070304110307407004285030003015000802c0e0b00c000158009400001c00141c0c007004405901144000f0b8a0521225800d010030319800103840c040100080709403807221401c903205440020810395040c0480f807400c10000c10980c608a2000700301201c0c2c1c3c0d180e180102035414101c00c0300d0018150701c4100c68842c2000d060200c3d40034a28054004903603400f160020901c101080b1788940d181ea0000030300c3da1403121030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 440016807 1250 440015557 440015629
    0x4022103070f05010f09080403142406030106060e030307150e0d12050a4b0b030f0d1b0c0b04060f0806180c090105090a150f030e0c01030b 61
    0x60b8240c40301c1d480c1132400008081e450049200c2154082e21007880c10342035a8614007524070186070303040c2e07130300c11060b810510721080061000742c4070038100001c00d14507080d000c02d42921070580160080004040240e0007944001080d240c0d0a5840380c0f80070f0288606a010000409a80100340014071400300608117441d088a01203201e1000b01201388090390311414154240c0f803c0c80e0f03164120009180c04041c03980c441074102200756002600f05030400030070807400000f2441e4070800c40d404941d9500000303214981000b9480850001801038003107254400b1014012180401a0003c0c1003ca8a4030340c041102140f030070b0340942007100440b5111502c0f14802440300307028440b03680c04241410003003510340c60511079000360450305507010241980e80245420081c0c00004400741402410f10510520b0b6507150000c0c0d000d440c51a9580c07441d50404000101102c030b24000c0d110134940f03041c00e010110304011410300c10414080c2030110b0040719240c003084c00c42c08460558071a0502200d85015091514 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 440018057 1250 440016807 440016833
    0xa0e011817190f0303050903120103060e240403230f0306210c040209060405130f051806040807080d0c030e0706051305040b04140a091b0b030402210307 67
    0x1100880c0d007103085000b01e0701c0c4800282c02e0050445084404514002407003604201d0340b12904c1c90582c3e0400084010321803a0f82d0080c4c000b15044c0340c42c1d4140070800b00c0100020b25421543e000c44001c611a03140c000c010070400a4070117401c2240e812015085200405003440d50220162a40e80d81e0381c0f100800d00c500380d042035814a1143d054040e411540d03900e052401c1c5c2520309220041e01100721114100b000a520003008643c1141083c04005220380d545200c5140951f203803440030405030048299a0308641000704100409810442664280341001030503a0707200e0fa1000c07500783d036120700d410040843d010b00d154800303200d8100442d10064030741c0340d0400417003032050808582c0460386500c8103840714001c4480003102e268040c0020040c1380303400d0f08030100000000d840007545224400620701c0c0c0c1031080714410320450321410f8000400032160b41e201c074003036180084444102c0c00d12403048981c0c030000e0006031240807007181003c071180c032010301000e00c1070500049075035034006464509012862 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 440019307 1250 440018057 440018099
    0x403020a050105040b0d15150309060b011403040f1106030403030c020f07080c06030a1401080312060603010501052a061e090c1f02070810050f1305030a0e0118 70
    0xd6400c000800b940941c06403000d80b0500e0710480e08244543d007000b0010072040e81600f520008002e0700040c020b0f181900e030381e45402255008a00c0c400796082c0f16095410300600203041000c41441da03038036140f01e0000e8070740103544100750800c3c4051f103003816042390503440c440c00c1d44481d001061004041d090b50106001003134a400361409411200b0000e6260642c9105d1041990000404070038285811001164802080080000c050b14425240300a00341c090b00284074960001034524202d001440c040380d8099005c8400d54519030501000803c20701604101c1006c81c008840b072414500303190494020052070700e0085442625040050404080009415461000344040401c15001002c28112201c600291105842603206000c02c034078144940c0d4030600718091188c02043c0300c1c1d03041c80a24500204c40300e021605040141d01a268014040c090012039034400a00300002900402a10600b007254100142400d400300700503181120091407800b1200982c05001c909101044000445400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 440020557 1250 440019307 440019319
    0xd12171608061009141f050301050a0909033906021b070e07050304020a03080a0c060b0616111c0807140a0c300302070303080a0c140c0a0803040602040302 68
    0x40790310a000021500d25160030014240c3ca50038480c24000c21245c058038413001e88503c80c600c184a0700380d003030700e030700d80d0301d00310000d000080100014a0101041c0000e029a00d4003008101f52550f000343c40c0e190581c1740f04140c8020444581582201807200f41074200b82c4130303c800403146035843d00340b000703611a485d800300c00c24004000201600f0000384034003d0340c0c111802d04400b40c4a0b00410349490b0001072049034407502d00b01d40840060300e240f000d0905400d140e21906a1180e0914210080d1a41e01032054010241489000208180106034864403500b01030400c00c0d0030850400714015545150750081c1c501e2000b502603040042c0c040c028218a40116802e60a00420703d00c929164445450058480c41c0300520510000100382001c2c044094600600240119035811484a07090341c2881503000d45c0020908000389508002c03426032008101d81c041000405041024000844254200302010f0340429442c0d103c4c1403c111a1a200385c01a009039228039062800c4000f035031040c00304034000c03a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 440021807 1250 440020557 440020561
    0x6031a0a18081b0f151e04111002030906120a0f0501030b0106080a15120c08071203030e030903120315010207060f08091c020307050105060a050d12171608 68
    0x2050310400c103400c0c1079010811070702c2c0902c0d0325a022003c0c1c1c640b1031000440c0c0039034204200c4104080025002e4180040d1a03040245400c03d50030925021041c2500000c413240402c200014400746550340600c00211200350083c3c02d0b00c28206e00d10302501000075040b0a00060036040d6030b40411801c0d02c5006240c0091001605040010003600c0307080c40006c214020000042c00b00b00e000d00099a8090f2001d84001800d00044260492115155001c0414242d445014000340100c0881840103820900010a086464072012202100c5030f00009010544e41d00007502c0742d400244115130b00180010111401e600148040120603881070740c00c007041a01c25101d041440d40081524422110300b51501d8122003034540c400d407006000200031079910f0080c0003243c0c3d19400130640b5404200300980c000c54441d01185011801c40b1005818a88240d03a18001005541c0c0c6104031001c03072580c01440c4400400b40800203039680070462040010b201c1a01c0200071305085030388a00340c4503c406035114051a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 440023057 1250 440021807 440021831
    0x518070b070305090d0f0615030209060103061505091201020c0304080706030c020a2009041209050f090406020703020f100f0b01230310050315072d1206031a0a 70
    0x910460714020042842403003500c499190007500d0703400300c40c054401d550b900b0020b0f0b917800d000c03110348085418440c0d00d008002d0013076042030399031700741c0c4850282000c220150034200f451407d82c0550302c1c10020003c00040441ca1070704d4108108004003c000300a648881031010b00c680c582d00706014090712031150420001f2828070038002d03400516501c3c1c01900c44000e8a440d6003540c640d41d44c1d015108441020b000781d40c29181c004100744214015810307400090792500000700614180d07805588260143c800c1d10f101d030740e00c10311102c6e00305a2080e001039031501e040c60107034108034030b40072602681c1c014110040a81c45280d00083d05404100404001c0814040d006485150f82080740208810041041080b0b08000700c0c020354000180800001c2515601d0740081d00d010100802d0a403050780c19800d02003903170b4200359609621801c010113a00101109502c0084010664122000300a9410401094409158030a1002d1904103407103409815404e5581807626078250b03150303001580b42003025044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 440024307 1250 440023057 440023079
    0xd061415120c0a0323060901080a08190c0507143d02010204050d0615090b0312030417210f0912030a0f1d0106050f01082206051807 58
    0x900c941d141e121640e84a00800c85201e0704085010418551307039550941000401d10324000120031449944841440c02d101404154401a84201020f50141c80040000341c00070040d01c6d0864003107101003082c103890050448042440002c00750140c00340c005d002c14580d0601140130090402514034440c060041030b1180e07840c0080d02d601e0302c45d4501c896030000c806c034200034404600c81c40c0c1d4800035051544900c0007a01c10740800600700c48035a80c400c10303c0d5018105007031000040240240402400800321b002c039490b40154000442a148000002801c0000145c02c460503555416203207501e611f5041d441030707140302400c01c20906010300ca00c0005e03043ea04d0054564411a0b0f000080c04801070b0807980122260000f401c450707082600c0e01401c0c1007020040c800c1142280c1a801c1c500c00015040380358a0868250ba0016401586031203082140d0303076040070b903131034211545900701d000380c0d4094603030700c045c098030580c0c02410345052200f44802c0c021606000c12801c101030090300c200c1a030301d41100e44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 440025557 1250 440024307 440024317
    0x8010e07020c0a031509080406030618020301030809010809150a0207051912030905100e03130e061509041b0807090e010f030b07020717060a11070b010302040f020d061415 75
    0x10f8081201c010500000d40410480c00540e10a00d10106184003640daa070680d903006a0840341c0069a9035004024200c2c040d4030008602c0da04200462565041d80c540d01940e00c90605464144245000454140c1c2d2040108906416111000003c0f6040c030241060196002ca0020744aa05c80e00400c10810450b402e910b00e21660700003208000b00e13454050035070190046400a5400c0c0c02010642010145c95000340150401c43e6809503076141c007031051035007150202d134020303468104010040200e10303102c0b0140c1003000400e4540658561080b400050081c25502800410001040440a62498000d110180070ba4403940b1081103c64854142c0d0081303240c2440340e844412114103080010450428401d41c00c2405031050701e01aa4440c4d04001c078034141613001140301c0e8406c1080008075040c62203501022840c07844128680700741502c41d83c44101042c0401b0384110391780c26103080340750850303811120f007503062940501081d81c0d58650320005101d445030150060000d00c01d9540c1c403401c140100c034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 440026807 1250 440025557 440025559
    0x7061415040b0109090509010b0a0b0c12040b1e090310050115020c030303220507150f0302040b09010f050418090203210a08090a020a140a2108070c03021008010e07020c 74
    0xb00c01450f180140c0c018006c044c100d00043e558900c10070784680c41c0d030300e000405460710b00c1105030360f440300f80d640c2440c08408a5440409480900c010b00c07000c000364048841d00300b04110010050003107507000301514450b81c442ca6605228103000d0101800b60b0ba00058122108007121403c822069101a40c83c1e1503000007040d03151b00f080000544000300d242400541d00c5850b441c9000380c07021aa60701c0d1410752550041a0a9030907880c50502e4198003605000c4881980d140543c142454480114a81d00566640a041c41a1082c210b0003a070320690a45008202541b1440c030131601c000200d800400fa45a820383c003d02170150400003050421001e00016101a40c2c15858103541100071995040f002e44840000e005000140d0056a140c0c52450007600800c10020301290102d01001038201281e40708101400307034000070710f80580050059a14194000524517501d2809251442c02484141c1000358001c0c03c40c2c000703125641e8000c600505072422a6850451a100c4540c140d03038440e1419109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 440028057 1250 440026807 440026817
    0x10060614133b0118020f04031218050409170c010e0303070e0f2733030610030201020303160c060608010213060903111c0515061c110f0607061415040b01 67
    0x4136981003090360003000f82d4400042001e0900740c03a42c3d07030049464060980c1e840011400c0c0c040b02c0d0012a822240c400809c400c48080002c10240d5840d100c4050f500c42c103c00c10b0f03120116402542c880300b1742091000c10319510039650340c1d140c0400040c140700c121000c10b0b40901d00c1c080c0c001d03100c6d00305607004c4501c0b0003110500c2c1c3d421182c0c40d805a010391100600c90403203d10301c0c40f066200e1441e800e00005a004451020403940310001d410b0502c4d004004001c1c00c600000d8000800c05030340c01204498005c00e6591860850b01c8031a48107442d249a24040206050310700000025001c00640c040c00201400c810f003d0140ea940c1c0034201c44403480c9000103070250f00b82d0010304c0717000e10b090318003058541d22075503d01d00c440c0e416441d05400c1c4940c0d8822041308540c0b0004001e560b141002040c5012400e090003070622211680f504610b00c0040c10220380100020140e20640d682c0b810150381d00c160303005030248860f6007040d110003a01c0074103941604006083c011008940c0c50607021309070311031106950f1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 440029307 1250 440028057 440028089
    0xa02010807032d0c051c020c070b0703080f070206060906040b12030d0501030606060503070210020307090506030a0504111002070e0c1303050c040b040204060e1e0a0b0c10060614133b01 81
    0x3100c6c025400403921030910320540e9000118070048001402103a40039444034421032900003e1645440001003007842103401020070404140d0b01e0000403900480181e40004010781c012012845880e10038008044030311000c103915522206580025041e41d03c00c2500380112070740c444c8251410302043d83c0394800360b08a1211861640c11690103950321600300e03c0d1001c40c040d0345402044940d07005076001100c10351180d04120a0140d42c0e100c501c1a85010b441ca61010341d00030b28001d44845090050162601d461404140003002484c1520210303461040000c0c9400d07680c1c54002d5503a040c5041e824082c5080c0459800d144c07a107842a201212480c1c1c541070800360402040108100211003007d0020212030440095511000d6404011303003120303100c181d030340c8852010003440d0260256aa000603070420341c0610880c3e074062450f030722400f5210036140d00c4030b030030002603a48080103801c40200b661200700111005a0307644100c20040015000f082203a80302402e000300340d41002d0088000030851128 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 440030557 1250 440029307 440029357
    0xa1a0106080a0c030f09030c030e030606060d05130203030f0304120504120308100f0f230607120302070602130312171305030f0c0a140606030a02010807032d0c05 71
    0x3c800d0800c0d51500084819641c40c0420444502c50401e90008255034102e10405400c403900700c3d103e06003203001300b00c41e00c4c2c000f0025a13503110f6001d211107019207407008220803000c001200401a58000c0c15680c54080901829169400403030382a101009140f8824034414092002c80302640c0403501c10f050448000c2d10b0a80750380d0405860140d1051031300c24000382d20702c400c1d4030410150900d154002841464a291041c40300700c0c1e60101d03a24103030045e4030a480c0b60f03900000c41d40301a5000f03400088403050b030f000076002400b4000740500054000112140300016100143c401d6030700c02d05c41854150882441210003d000000c4808001024030104800c0b05034030343e00302551413068045034640700650004240c2d0b07820452154120f030340081c00e2a03003000994171165070f901500e00010080b41c9043e1001070342e90340b80148007134144200300c2c021a240500c6a00841d00b88044503903051034141d201040307920120030010008240f5403800120130a2103101d50129a136005520b5407014a070742c103c036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 440031807 1250 440030557 440030561
    0x3305010b181f02030a0f14071e0c08010501030b070e030606011407080c0d0206071d040c03020d0914011b0903080c031e13090504022d0a03050a1a0106080a 68
    0x3150591005031010b00c44542004104000425001d5502641e03c5103c400005842e0480b00304400e41072080d852552039400c641c850a4405441c1c1018100301c100818141680000000a00142003c41c80070404540300405401440c101c2e8851140c5054542da20031088030b0710890607807010343c0354210001090041d8464010140090113805c403140c689006913503403059035401440042c4d40394006510b1042026018005603510220070305041009507002450b03c58004480e1200920a0342c2c0c81102c14181c41c42641520341c00c60b60b0000c200312031036003800c0c090144854041c0701c0c5050340c03c090035000700113024904040c10a03426251000d405043da0703141d00c12600f2080c0c01c0040c92100f8045052850a41004d00c0c80640c80051095511003160442480c0c0182503000141c10500b486c05120042c2c0340c2400552100020a40d6181c500380321130020311540701703504881b550018840314040305200300071590740300f15840b40c1c00001c243d4904410301518164244600e4005c80c0031040001c13181c03400c176 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 440033057 1250 440031807 440031847
    0x20060f03040b09030f0a020a02030f07060f181706040209061509041112070906080601020a03090905060307090e030d06050a050d0210030f06030c061d24073305010b 72
    0x80075241404031841d0b60710206c0e0440440d820042e8800c0d251001582001c0c040c0303d040305100030103405a6820010f0180003030b02c19054000c03c1040e5420000250003500d2801000340c00401460758032100301b001c040380e44003c02c0d24103074803518901d0080381044c43e0801d01c0001200c1c084c15481d081c05081e108003c000c0506900a07011040100000055015a0061580300700c1598072003e90351400c100b4000c081e4400108240d0656101140583c086074000402034110340e4110404100b6070b4400d0013090401d00568003200095080c100c40070040540440070f4580c540e4200000c2002d19a1041008610a91031081a0304003001e070340e400001d800c0442403040350711384900300888d05000c403d1003c0119581580141c601402c41003081c450954045400342d40c002c0e2044403c40100d004c0e80c0000ca180c914031640b1401c00e0030308488074a03ca081c03101980c02c407580004001d40d02100d50350144031440e804280b080e1405250109003124884248109030681c0c0d01014009d05000c04109984008100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 440034307 1250 440033057 440033071
    0x703090528020a090c110c06030a090809040f1a0d11010c03050f0313060b01020a051e01140f1605040308071b090513110103060e040b0a021620060f03040b 68
    0x1541401c8056101c0c1640364000b0f14900d41c000440058403000105a080084001115034000d03480250040d518441926080041c004e0001001402780c500f01780c091181d2081150070a05200d150344c4605101c3d484661386040c0d000640300c03159090010040510001d4400030301062008208603c1c55220750b01e8400101d201c0c1c1000381ca8008803000400300e0703030001c584000340454584504800c0210741e002d03c800d4104280020601c20001e540c41c5521145036008144e848000754a07004582d10b801d41108178440340ba0102c0301510b04181b0340c420740d601802c403100f2a18604040c45904032074402c108641c2200c1c2c00442d01c41c1001c2c1c1e20340c0c5112a16082d001d00032801e45c003032900032802c803007039101350f901070341841d0400f582d08001480c00380b14030000481c64078141445c0c01020414030441c441c01c10384c03083d48420b45480c0d17075540800400c000d00482a0201012a41030b02080c00c0007245c0b01c5446540c010106013900c030420300c40030407186104409140310b1220092000c240000e6501b00c0050f003203c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 440035557 1250 440034307 440034373
    0x127110406080f0705100801080307020108091006080c0f0303040305060c0310050a09021209030a0e0906060408060106020610080606010f050d0e1006030209060d030c0213140403050d0507030905 85
    0x25603805907900d080c00e04400391a03d0740002c034080210303141010810081020600703000c1c0c43c0358502155240c4900810078040d051010990010b000755000303001440f000581b04004201c0705442d840c1e042c3d03030340c449c85070310a015110742112461a460300000307540031a0390120013804180d03107180b0304420a420103091541c1c2c02050f0344020a450b034803074608401420000e0310050700c41118041c003030349107500a0281c82458004001c0ea10001d1303404020b980001000b5a051842c607194100800c1c1d040c8074543c0001c60501458001044c0d4540c003181c041d00a881c54514824030385d807079050058840b9010354441d800300f040c460415003031601400140c510840c040000051501d44030807070318142100156000c402c20780d03c440510451030078003c115008801030b102e0510315881c50350094021400240042d101d4468403151400162040d08100e50b0b207060681543e4a40c02c0c035103002740441d0806203184603410309100000369020300c01e10411528a0f0450001e09900c40e03600407c3c030780541c41c1c2d500003241107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 440036807 1250 440035557 440035559
    0xc051813051212240609041e06060c230a0b040f140607030606050304020f0f0d05150402010e0d15020a110105160311070b06040c030b18090127110406 66
    0x10b03141c0c03800342000c002080780c908058034104081050340c00c00803088107a202066501010300392501d4050310741d4150151000a400909035010801e15a4000000300d500c5052460201e542c90380000b404140034440c03a02e06100d030041d20a844003c5000034181000c0d91b00c01d00103040442c00c032059080e00a406200920300412868071000c001e00300c01810303202554046014800545e80c0f41c45484014285031500b80e003982170550018100c040c21411041c0710f1560030001007403d0755450607500c0b0241c0d05c80100c0c1c0e9400300c6454118082002120306a01040c01902c800450381032a64841d03180560051a0141c408100c201c0c0d00c00039001000241c0803c0508100c50768241030900c03400f8020000c0d22000e8504088500c40201901e91640c0a001c00a00a001541c00501c41605058128100300d03804502005400c1080f0020920350760b03441e51280002d1038800a450300700010a0054120f10000e020340d65901c29035148110400e28203042c000102c8858801181c40c841282d640c1400040002c5145 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 440038057 1250 440036807 440036833
    0x80c0a12060b040f05070807080a11160302151f0504091e1407060c0507060207080d2303010608041505091213080f0d030b0a03030909090f0215070c05181305 69
    0x4501c2140d101c8007150944040c054515000396294ad80300071102d0040c042e1342d210445003491402003104410311498440d03401410103000b4005510f201960a21215180c44c003000ca052000001c96900035a0300f0f00303c403010400b4281402400009900812440085580c00c4141800b4480c00c220940d0648404034910440700400e100100007000c081d0340701821514142805410300010358031100075580180e0003000407850108500d6060ba0003420007281d100b500790050f88491301d100c4441440c0320000400030031895007100100b1b01450182c0500c0d0340d1205c14620b40c200300c543c2603458200c0d640c000040d140386407881c60014600200d81d00403007030743c5c2da40e910516032070000c1d030842440d01c94000d85a0b000c0366903030501c29060036140031a00002042e1841e00c2c081c003020350341d01840d0780003900c401604091261100410310020360140180400301201074082030386070485801112141503d4900090b64a044054098000c08510f508102034550200091440d40f00304000c40340e03400307800b41003424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 440039307 1250 440038057 440038061
    0xd0b030609010605030609030a0e100203370f080a09020a08150402120a03081308090d060b030f2a0d050102030a06050117100e0c070206040807080c0a12060b040f 71
    0x4041c0c081c00814800d090800b0903040100052a00c1d41c503078014000006a0f603840102d1910a487c1a03440714454001201c04a0451195019a1100d8001d84805000320003040550725009105c0d0f050150008030a030398200d07610f0560703134442e100292030780d4080b409186803540030725015440213118500350f5176542d00e0b0f64140340c0740ca40407204104a4008000035800c1c125840aa103800420141014030704540e00a80ac200c005403c01507070301c0c0561024001c1108182c211156403070010041c40350716440307142c00d001800c604030205001780100754a0040d0004002001c4441c4820384281240c6403440000440040a20030320031035018444250400c082402031000314011b00030680d02241680c102800945003000d955041c1c030b00429210b082140021030101f05a051303495064100e201500c07141059079441c055004081e40c4407000003000511140009038180440e948001030301e108100d02010000e0000e075921445041320354009a40c070020361540e01400c41440018400103441d02c1c90718003081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 440040557 1250 440039307 440039311
    0x9120e04021b0706110304030b0f0727090f0e10180b18010501060e0d060e0c120609010e01020304030203040b07062307030506060f0403020d11040e030a03051f0303050d0b0306 77
    0x460304030321420700c01e09034095128440002d05c0e1008514081c81c650b10346181ca1320080c000140194408041501c4501c1076002d40036214418046c05070b0400441e1440c445616a413003078480329813500550380303801d188a0182808261100e4003401d04002d5403154980900b018401082e6640c01c0240500e00142540c01154050398480802000a070740180340c00d401c40740f06070440405c0c04800341e00450780b65102120203504079802800800e110505200640c60040300649659018a80c07500030074080301c0000702c0d0f500c609100341c0240324648510848074200d00c42550064016041003105000080500b00204426071140000103405040503d084c228a40f103150700c85140b08103070050111040c3d140c050700e0303002101100c000f460800c13144a5400b040c03040d03200c024054602100b07a1401d100a40780540e55503070002c0c206000452040006984a9100c01c0001000c83c0c03800f80032500040d0105000d00b0300d02090103c020445095482c113481d20707006181d00d18901c40c3c4076000c071070b10b5403001c0c00854 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 440041807 1250 440040557 440040607
    0x1020d050f040b0a0c050705040908040b13050406090f14100608090705040230060906101202030a091b08060a051f0b0306030705060c0a02060313050a12080a09120e0402 74
    0xd0030717207816103402810b060b92948210710450815003110081614030044500b1170b00954482c6540d1410130303020300002c0c42c4030b80c0541e9019160101c00a004d00c200d80020070310500c140390810010340343c90302185104001b96100007032001e5044041c407045000f82d02464016110908550361503641c3c000080030b0368070404024540071071546094000b04040205403c0202190500381d003585890004903612400017810288990101c041ca4070070b01c1e0184209422006085400b5136032454800191805064407240444030b558a80c45020460348840c00c0100a40d00e54201419054031240242005000301a000702800390200103000c0c62000c038a00d40030000c015182982c1c0d03da2411104160a02003164001c41c001e03007080100c207010b060042400384009904941081d01c0e91500510440444c02100300117065101d00384d40310041c4012421072507150501b0f40c0c4c07803450300c6e81c0d0000c02e28162a14111300401180c10b1854440c02d043c014002c90f044004054401824644503451003111144040014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 440043057 1250 440041807 440041817
    0xc030c060408090a14090412050d11030919030c0201030f0b030d120c0903030c17130b04030b06060901020a0201230714210d020d06090e01050f0702010b01020d050f040b0a 75
    0x10402e04d00301203251030000c03c0d2601e03c900c0c0040d8034070301240118000500082c044e280619429010501417829504a0010254208401114003035000000c2d8800c6c3e503501c2040c801d51001e0224000c603c491018019490b0341c50b83c01411a0b40c0c015030223440302c14860300703d03651100188405518100008201c0300b5150340c5040c039009200d1400c108a8181d0700c0307003904001040c0b20a10119403c07084000c0e00e181d2200b101200412104a580007038000c100c0003104141c4001e9002868802050107401564000d0840c903c50340c030780104100c410300c83c01207601d000d40c12164404c400356000d030440000e400391440003101c0e140161441c00c1d5440d404a0300c00c492115280c1041c040b211801c02401100c0d44580c02120510113050b035019110b03000d0b44003169001c07074000a04649a01607508420010140d42d2428000101003d900c13a003c4c2c14200c80c5410008650300c00681070910501586c0d40701501a00540710325003038548101c980e580071445a030b5811504200001c2c2c0d64500d00001d020b003040640d1030f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 440044307 1250 440043057 440043067
    0xf0506070807020106051c0503041a0a09080105072a05030a0906090506070203031b03040f18050a05190c031d150c0307020c04091e0c090605061801050c030c060408 72
    0x81d100d208080c105000b10384c504a400d003c40d44481402c0d4a41241c40203401004005a103000c40ca1031107150819030801000103c4402c015211001620400c200c640b2007000460311425858200c0e10700316a0759001918420321148482282d00090161440000d40c051a0381300941b1418596031000300c1e01e40001e40d20140400150398000c00d04005044100d45035854801c554000a5580c0a284e040510200f4050011a03281c3c108108a400a082d5510510034950340c038800210440144055114031038246000070310041c00b1841010f11900b00181c58201802400c55040c00a181e8941c100c4249591032807041200d032120350b05001d0f100d42d803400611480d040c40209003503504010f440105618030600a0040c800e03000b0502007070105060300c0c009600c0059090421001980601c21401410305a803c00c052045825414060311030300c0000f0320405507100184920344c4180080c10b9407076218040c4204e6958030034070003062800340c0078040342c0c14283c20400d45400c2c140d0550302115030f0b16000071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 440045557 1250 440044307 440044321
    0xa0b120711191b050f28080a05060103060f090201020d0e150408010f0606110303070e0d02040e010e0f0d0206010b070201090e1005010e010c1110030e070609140a0803071b030f0506 79
    0x1501c0f5015203800c0d00c011780640781510200d149120203851000c00e45c00c2e0400c40700c60080c50240c110008110b41c01c100c0d65101000d0170003a841f0171007804140e4101d41411080980e03002280035074010194103a0080004100e44c8078202c400c90022142c40d6070043d6122144645010710368040c0c405402c82d40000101030907044a01c03011a0110740c450740c140144444441807100e0301106407544503400d42061a0000e03008400142510141e440007548503280041030319851005500030b01442e04864101ea240c110903100d660780d500d064103000c0e00180e00450040c403d403505900508105803040c1003458185841c0c403200034500000303c80c0c41c2668881075800701301545c0e0060142006200030300b0681d102034000e480d2814418244c031545070141071183c1010740320718444c0d407041031400010800d40341c000340c0343c5400a020748410b01c02d00301140c0c02c3c0c8442901b1841c00b0744240049490f000d005514140c1d1139650420918646604c1d000c081080390b0000010507404548401800c2c4968050000c1d031030030304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 440046807 1250 440045557 440045603
    0x1110030e06090c0a030f0203071814150a031707050703030c111c08030714041d0c1801080c0706050a06061d0102100b0303190e0a0b12071119 62
    0x2042d2070b0480e441481d0700000313500da1801c14025241c11507201120b0000318000310385450959401f003008150101882c925140880d480420070760380f440c80c0800d02d91194080000d10188175141c05501c0000740c2e0b0b0420005003151940712404601e410300c5814010306440713407814880203034000d03400320360b011850a00708092603540c1c485c010801ca488108000042091082a130506c480080c11008008040303001140952000700040c002800c03100d039125113a2503081180c128000c0200d03468488a000300c0c0d000c0c40080140c4110200d48044107610340b03001c1e40111011580034081c1c000b5400100401c4010801c2802814804d03681040003007201480c007180140100034000c1c86500e18446102d9031683c50f80c0c0801c60300c0b540304411602280c60a4110300290852180c80314006142000e035400048094004001b030056050454000740070940d9200c042181d8814691041d1f69100c0380340000341901d0003801081411540d00040700c1c03010202c81100c81e8030403243d40c1c007900c80b04140da0028040003030072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 440048057 1250 440046807 440046811
    0x1b0515070f020f0d030e101104090f05060306070309030504090609021308010902030705041a0306090f190c060c2f1003020a021908070203060708041e080d05041110030e06 75
    0xb8402010080c01040815840d51800c201ea02c04140e100c56001d400c4103c100400103200d020100c08000e0a07003000c2d100803140e400b03482441c404c0d41c01d04070303617118641c1507102e0716208101c0500508a070b9a14130070228010051340e07004906200303007840f01041d030920910961001c0c1c001c24038010303030b51440c02d14034000c014195888070800b6814448070100503140400c0c05030440b4004c0e203000c969803111000d580000c0011100f02030705841100100a180d4800240720204e0038482c0007a00c011417510900301d101408009406010f0150020341009050b200c0c9a0100c2c030180204c00444c4d460364040c1c2a180c81c00f0040c0113801c0c2d03102140c85000324a15041c03070920b4070310440c0d00f41140b402c140000c0207510303844601100713002414090444c0c41441507090442d1031899004040d50000e00e02a0707005030002109541c1034500c00002c141c007034a010607502d800e0f01c446420054003401d003018805900044c01c0c3c01801100c80c000c28410390803a980351040351031710781c0d080c644011805400407102d0911704480 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 440049307 1250 440048057 440048087
    0x30201080610020d120204080a03090e1302062502060c0f070605040f060e030109020d0506071403070804020d060f0e03281b0305090a0e01080d03050f06011b051507 72
    0x6410b6030503600a0300042c0009a5a02e0390070010b10502c21764031030744004e004503400b4203190702603101c001c0109503011100500780e580f0418032410980b0f0362580030701c07500306c1020020341100d0300f0480488482c82c1d2144020030501185048880c110311640800d03015001441c410680d540311490700c0c25056030a21102c005401185855400d052800003c00f034088042e20580c0d091102030b03031410005e0f071029004801e42c2500507006440c00d03006441e0059403031074110340d45000201c2c041c0c20700200e55050000c6074003403d0302d60b07242d030055102da0302006a111951001212029981c0302d03040303103507641c500600b6200000c0401841c4c403883e645034000320b241480c00c108000591031400c84001507401c01426107000c09010b0100d070403084a850252a07502c10002c0071235019024402c0040c00010000505040e0b03942e05040d07429645007442d09906407002540c07070a01c103c50b8040000d00e554482c00c42a0240c10202e280780c03440f4485034443d00d0801c18540d1f5510109c40c00e003010056041d03005046049038880f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 440050557 1250 440049307 440049319
    0x15020606040e0712050309090708010509070c020102070501080a0e0a030809190b010e0402151606231504020d02071406060108090312071106070201060509130309050f04020417070302010806 83
    0x900c02c40003a880341c0960113510a484840f80003041885820000e6611500000e4420811400c0800d40500009000d110740c512402d12400000c00841c441e050440070182c3c1a002880a603082034011b40e44014010170501c035559035000e80d2400ba1b442080180400fa0194a07074418500340f001039642441001030350300380b014109400800c000ba0056184504441040820a01d541c482d4800648840120b01c50341c0c441890103d10034004401e17114555810720302c541c104001164821008012005103982c403400c0382200400050407030f1203c0e03540501100401040140741c0b44c40074203c40200d0b04410710640340f0307030345d10040c0c5e96041c1c0040040030b4016109003003c007070500c1d00d02480c7d5600e00c80c0c80214147c0c60a14008998110f008080c040500b18400e010b0794141c0c0342c5404001d008103024814580304001d0180420382e01c003418400c150341140c155460b40c82c12401d140c1881810019001c23031980143c5c1c2040f0014500b118003c1c469040141c0b4400b810300240fa50000600d03c130b85c042c0966200388 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 440051807 1250 440050557 440050571
    0x703080a1107082d0307080105031e0303060409032c15070506190f05010b0c1006180b1f050d0b1806120a05030307110f0d090b221502060604 62
    0x76120f80c0076100c07120103c44c195130742c00c94118040c0310b03d0184400d002000f50030200602040540014619060318425000c54020030105410100110b40b21000c01d08280c0080002c6138960605402110105010f410402c0c500d1414203e403410003e4114850708403130310004131503142458000310780030b1500182c0384200c0c00c2140c10f49882d0b858550241658140c168517452400c011100d58011810389001800100019030395024982856801184c4030500f500880c444481c204030780c1e01c03c0c001560341e203181d042c80d006400e01c000c5008100324217410b0380c0102c03049451004a4002070b2a1420780e506036403001e40b80d40640c0c40c08402c0e618000a0702d813181e611000c43c03401a11104040c1da0340681c0072281c9182903040150800d0420303c4400380a003040c0400030400040c04e410107a032091904d4060210307850000e00c1c201541d02c845407038000f040026142c940c20040c00e400203003e022000e04010480e00d00ca0344a44294400802540c492603d208070482d00d0b604981e014054194080800d840c1032100c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 440053057 1250 440051807 440051813
    0xe1009050c070308010605030a0f0906020901030e16150306150f021603120302091201060b13051c12110a05010b040c050702010915110102030a02030a0617030708090d080703080a1107 80
    0x704c01401060100700001c400120058540c0c0c00c10000805120400c00803480c0d1402c2842c040d500820125012908120026090460025507006800e203139000c410703040c50030701c80c50381d02e80c201640302c000405856410100f4140400800743c1c035480000e855500300030b07041000107030519409008050b00030700c9100301003000c6901c800d03110000c200c0500e40180e491004d03100040d1051202071100500b0740c40c000d8003040548604009000107958503101e010647d076030740100841d55103260b120041507181a2240c40000701080d00c8064510b0351800c10319001d2043e114058906000380809641c20303074655203d0165400e0512603004090000d00e85240307401c03401d4001901d0039030300384036101328551743d11a100303141442490030f00b00d0149800001d41d617a007000c00000003e90001d03240105050300c2d00c40d0004110119000380c244144400d4003079407d1503001d8503450540d4000d811030341e401046101901000440703080003410038910940782d085040c10120b000000701c841d5415504a8014100700070004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 440054307 1250 440053057 440053067
    0x106080706090b040608010e07030e0303092a0a03060b030309031b1f0c020d02010201060b0d0203040b0105030f06040b0402010c0807060525200703020d0b04060c020a08031f0e1009050c0703 83
    0x54501903c03231008107441d440412002400e800c4c13038007000790101209000011601048030a80d003c0032055501800060408000310740c9440e4142d2130f48401325100030800246c50750006003148400030192030038002410040381c10034540200000c4e00c0391100703031400901d1030080c9016181070900c0d044245240311545001e014825400c0d4080d22a80c100c0d8464011a8401d4104034050b01d241d00720151a100c0140411010350415501118102003000c000b141c2030070009071803444000c103d030043c50036031142d495000c420b03000600203034100114004c0c848017056803400202561403142070001400d02e040e1034020201c0700320400c024034070705020400c40841c036408101c111600c444150350040001114410305e1030051079a100940042c0346400724020301400f542c0c904d108034010760007404000031002080362104c1a905009205d106d050011540d003044042c3c0c20760440001c9082e10f100340d0b840d1849500207403021100705442c402d241d4000e12440f00d06001d03880d003080e00c0c03605541c208074041e500501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 440055557 1250 440054307 440054309
    0x9030d141506091504080c03010f090308060112020906040e0403030f111b0114041208070c020a140423090705030303040f1103071205030409050c0304120e0d050106080706090b04060801 81
    0x803190101250038400c3e41d4904040c8480002164411651140c0d5003280c2c54846640300340d254820351a08030350450b41c01450085035400d940c582e503011529580c0800659000c0e1500440000c3c8a030b00b4010204642ca407540180082c0c80802907811140c9040d10b0005e041c0c0d00341e0010008224102105065080303550800c0d02c0740078405034440303003030030f84a40c50060061596004480c040340781c26041c001404040d181d0082100b40c641d07610b21495807068030998004885002c020342001d0403441c00c0110b090344520000d03011800810204034031b222408a940c85a4102e0902000040001e0034000c0900c0200300070001413505501541c1145082c4c0c44002218022440c00b9040d800920031620300d03550184419005004001100f1038013242c241002c42e980c0e000741c0684050607140ca00846c28018490040d02d00c9035a002c405c004080340c9076002201c41026441c0e0041d00300792141c1d10310002443c207000b100d000d010100020940c0e0f62821000816584082e0300030317080c20004010902040d43d200d8543c81c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 440056807 1250 440055557 440055559
    0x51903020609030a051608060c13060c020d06020a0905040507140d0e0106080708010c08010e0610030f1808070605010611030406230307020d020708280c050909030d1415 74
    0x754407008000c011030304004041c20014141e0184003400b11b09480b120111030103503050201120380640e03420000c83c01901c5103000b20750802c5044801001030f41e220300d000c868464030161070303115a0304007503803001c06a0b0003800300d440124010003401d02c114142071080036403204261424401506290805c800030f845404c5d460245a600c0355140400900300750800c000410069085a00c065941c0c0c8015000b880c00014440008004071f00029100e87d200c4069405201d00510050110745140f8058000b85107090b6401005030b190200300c40300b070859410f0050802d011f02a150b075240c080340307042012508144c10a2051241c005404082c4840010079102500c3c190f00748001c40310f41842c0b10308510711442c50b10705a0420004100181039030701258000d0318490701d4003101d4860781c8806202d03451310b0b41001d0030040c0d4060f92a2815030708191107105644180200a4a1007168881c0041103c00000f1075840c0c002c3d40c000200c081d84503480380704456612800702001181d0342450b9040003480d810881c651 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 440058057 1250 440056807 440056819
    0x9010b01081b1e041203110d140d150909020108090a080f0307110604080d14010305100f0b031c0206071806120b09040c0816031e0f08070602070c05190302 68
    0x60701c1140300c0100721042030b034480c124403030302c5030307070302d080b80c20740e007600480106d0010b2240c400c2d01070074490000d04c0c40449421a110300301d21041314480f01d1104d4001c01e200703000c49620340380034400881502d202c00c4042c1c240c803000032a550f0703105e00005d01041005000c0005550011b000240802c0c8608203039107441c41420340841d40d940340c03140c0403070700318081120b50070050150030103010030400110300401c1e800b400e28806001010803c6a0700e068081c0911009d8000d4100d5005d182a0000e0396222104150054500085810040000c01d180404080d01d94a41900041e85039440700d0b010040382e9880702e40740c68001210546c0841040c9511801d201c1c50080c0704c04403041c00700d080d61340e0304000001d002c00b030300e20441407030f0a081c5046c205a152042140c24090026070300040340c48140c044c130030b903500400400240020b000d425040f400310400d0a64034103225030b100d4800984014003c3c03000d103001c0c841c09a10f414007801c2c040c4000d1116030005103e04052b03000c3c510b0001c040003440702200c0d011200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 440059307 1250 440058057 440058067
    0x3030c03060d05100204180c170c2b0f1103040c0e0403200c120c060702090c28030609090f12261506040e0f07140f0309010b01081b 58
    0x226602c0c040c8000013601e98940040380124401070807054180d0b02282900050010403a07042e029030fa5008200c904103a04da04400c000781c408031540b00100072000350100002c0d4039007224a640080e09103a507031100c0d8807585450740e080000c0ea4502440c2410300c0380021305495410142d0700d1404801a03840b540000f88080c800040038075004044d40c00c2102d00410342079846100f86025640c40c0d02106a04502c40c03410700d41c0c0c1440945001400b009288005000c1d40d282c84a641c0070000e40c01001452141ca030b030000c000c04058408030b10820741c800c070b0441c0c060442d00030700ca4202609860103500130781d0515252440000114001d0302161803130039017000520000901200003110740304102c2e400005641c0c000024020180b5617040a035100c2d110350000d6140c4650300c002007141034440c500c1200070715000c0701d001c0789a8261752042982c05c01814201100c162880204002c5103030803da0a00c821243d01104202203400d080c001c00240c00000d01e80441c42d0725207421114500c005204d1480013102c00854 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 440060557 1250 440059307 440059313
    0x203040204060e011214011803050c160620031e030f151e030c1c05060a02091005031f091409060115051b060c0915090102030406030c0e09010b0d0c0203030c03060d 72
    0x2105c0c003041c183c1150812141515400e011b01242e100f0310b0b240341c052003486800cc2841080b15101820350b1a50398861489082100d50240e00c0100c58117060b200d400300700030003403281e444040140d025513005c2c01659143d103001c403036080524100a0020506c00f13240b00002c0010b079074046854100b00981c062101d032000c048030200745800f000150381c503049000c40c0b0048a002d5016044100094490000c0b038000d541e61148900136406900081030300003a846211007049400b803000f0f10350022000d14181c0a225619000000384800d40d0300c100ea00b2642d4440c0b2400b400d81c0c8034901e560001402d070081000d5450400e1401e440703044440383d40e040003804500342c59500140c030360079407051892001b1505103083c9400501c0a42d40040b901510030301c581000400d43c2d026540c15620080c10507000b13035051900d000b1040c0d001c1d01d10707504283c0c00c001c041d0581040640d200000140604a503806a9032115040180b0408a88960210905540c4240104005c0c08010030459034000020f846100c1c038640545 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 440061807 1250 440060557 440060561
    0x30c06031e0f140a051009021303020607081204061d0d0c060b15180f10020307020409060e03070b240a14010512090d090b0a08040303052205010203040204060e01121401 74
    0x24155654510903c0a0119400c0d080d00014041d400701910a01c0f6590341c2c6020340200c0c0700c0d100c0094440c0011110030009883c002d1301130f10002c0e01a00185240002c4000e001102d001c0883d1704a900c55030390084180c41c002181030800422170840024072020800807005020041d8100c00200750300d499020940031621005160303060301d142c1c960090340359a020350b00d26801c0c40321116494001c030038070348964800c1c0c505411190100841a0003552411100d6000c3c8406410500000c0d10403c3e2104644400e011040004004103070040b0640ca680d8204021043d00d81c402000041810050700d582400322642c135400248111213402e000c1074666210341c4010b0306c250048003184c0f100c100d503010810038040000700380b004101c0035543d03400660720380340d141e04003942c05144002d4000a0300d0000060003e8003a0b80607a81000e26020320090804100d40381b25003811410404850b2a5008020301045007800e010b2000a015000350042044d0306150304000c101c0c4400d903001d0b0010525070682d500c60f04088d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 440063057 1250 440061807 440061821
    0xc020f04090507050d2609010804112205090c041a090a09060c0903050c030718180210021e07030b190204050307140108090601080309150d0606030501030c06031e0f 72
    0x2403c00f003801001d13400c01050722012040c10305a450012001024081b24080c100d51002c001610303618080e8845440f240084401c0311042900100400c0c14100c02801c0d4401e054185d034009240468145400d1030090704210000001c2800b0710700307103511490102d451003054501c80e40c0c182c0742c50085035900344400015021404018000342d160607181e1074407030340c045c500100b500e00400488107008041400d02d640e0fa0018070442c031000601c002200d107002203a40024400e4032094069081d9040160001040f21401c0f685040150b802500900e0110351021144c03012400c0800142540c1c1c1e2840c0c482c0c2c0707004200100310281c000c036400300e64002c5040c994180c8000d081c0141c22142260f032100142d0103d07200c07140341c4a01040070440051040100000c0340c0381a12030260246061404d86000d01444a1061210001100051003272103400085440b480009100303a03603012509500d1400c140d00c8148103600903408060400740c856002850b44491240d00840c40d110000382500c2c14041d001c028105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 440064307 1250 440063057 440063059
    0x20f16210611090315040309170a020307060807020c040e3c030a1202031302060d021b030a0e010c0803062110050f0a060e0129040807090605010c020f0409050705 71
    0x50029103150000c1d491025194500c02134003262a030400c4000c02200c4444212801400610051002d2010359520031800100320342d03a8044600c0d20500390b0000342054020b801100018149008110300161304100c00341500c50300340d034200000070070001104d48406498a00e140103085005600300d0006440744500784648201c00e01000494035541d106440307a10419007c0b00141d0740c000c0c0041400c100344212801496082d90400e039012069092000d190082d05c002c0205950030701100b1340b0040c00744e41c03040c04048074002442d503038181120b024080d208540d281c2c42c10003a04d40000000034400c07204072074002c13008990301070700c2c411504010803d1a12070001e4007c903001f210080440740e81290401c90040001e032011071501c0d902c2d25001c008550140c42041591210800100049034402048052206809101c0001c1704801c4200c000c0c00d42c0154071140c5107a00031001044a40041d10031400504401d284c041262603032a000503250300c2e118a1a40c0c40b450341d810040080000c01c00120008043c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 440065557 1250 440064307 440064311
    0x1b030215070b07051c0b060d1401080609012723011a101704050703050a03021608010b0904020f0d05060a0b03060a0516050a14070c06020f162106 64
    0x2400e800150060380000c441103403102c15107004640598002d03015030b035200c03002040498240d074001d0725000203021203030f9003690400b004021001e400c0740b40c0d00621140205440080c80b05500d0491601d150020041080f00c50341d161641c1c4244003140c83c40003c03d410071a18130009000342074107104040b000d00c68151444a210918403440369001904410707a0042c10199803200c1200301c8051180700712511100100140380c03400181030340540c080c1c4403504140140100c0d1034035522990741500c1d180003c1404d4000d40c0c08962008240220704103607401a25007000280409040000444c401d0a005031009100340407285a000d0039855070021411110382010440323802c1d09200d00031200501607007103018020300030080001c156159500480d801041b8031501441083c40c001d9007151183c006900c01000c10022000b10360000ea0302401800000d4014085047c07038070f14140002e8a00384c20404070b003080780c2003009000003101180c002507040310342c408904200c100588801034400c0b0030341c0750300500e118 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 440066807 1250 440065557 440065579
    0x2c030105072d0203031b090405010b0c0607030209010e40060b0c03071b080706050a09080a0b19060807080d0e030a0b04240203040f03090b0708071b0302 67
    0x55110500700c54002075400d5100b560b80c0c2016031a0501103122a501d00540e00c02c1000c2000501d403460100c0b450a0000d000a003400b9650002900360341003070f402030360703104030119007601002c20030b00040390005407500f42189030402070800603207a07040041401d0703c14400c1920b645501c8000d4102d00f00d40d85800034031540c1d030442d00c0b40300400034450b05403072003a45072800300007080102d0307030000312000d408180707008605001071075440c1c41028100500f0b03828090403d00780000e04d6001040b21001070a25038407190b89032800381000900b40700840d40200c0d021f40c0400840e82c04513105602054110000300101c1015082456841000e8503050780900d180740305183c80095103500105666959015650310503125540d17880800d03584d5042414080c00040098001c40c0004140880112107201402c640301030000305403015030200d1300100e4040e40d680910748aa4410594803090b124064101c0c0d0f0b010300e0824540d0380b90009035001c0c03034030001c2903501d182c2200801381040b03034180b800850b40101601c2c000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 440068057 1250 440066807 440066821
    0x32040207080c1005100621020702010c0f05070306050a0c1b03090807060804060c020607120902011814100809030d0e0106030212031206010306061e0924020606030105072c030105 78
    0x2c0104442510b000d031750f02c15000c5001031060b851941034044a00c6c5000b02a200c550320b075002513000403401c0b81401006040c41d00000d482048007032140b4011005030000d07078514100f04c400d0300e0006081d582900d10703003c2c940f00d2207504907290003200e080310104c0390070001c000c2c5000d0303400c000d281e04800d10600c1503500002d00035071b002000511072485004d061201900c1501e003aa82c92034203807520408205050340000300c428190b0b00941301c0c43e005140c42d12002c0c106410440c00702900d0380092100180c00340c07420609060100b000c0f078070380d03440d8584071460746443d040b015240e001c4d8544020103240c03602074540410707009411681c0595001000e0401d06000641580d0380e9500240c41d02c8014881d42000500e20b600a1055204070b40305600c8032120418100342c04084141454154014440820700102d8001004e00700600380c285000141c101b404008540640741410003015984640e04040c00c012040342d0050b40d00059000141d50340004030b062850700201140798656054066103090200640 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 440069307 1250 440068057 440068061
    0xb130c03140a200405030a030c0c0312030615021f0906020c030a02030307090905010509040605090f0d03022d1209030c03130504050f131403070c0306020432040207080c10 75
    0x8000c0c0e50030040030052010380070f9941a4003c0d8420786038160000c41034400441d01902840f1a0343c0d1141c2c0c0140740040e240c0c2d6031903103651184406100042d640340f5003408041c101c660300d90010b4a1500081120341c2100d61004901c4800204c40c0c1580d41d2200c5e40c200c200b00c010380540c0c2d1800303079840559072200e4041710020354a4004846440000701601c0c80041c110686200e514160b85024002001700d584644816001e80340103001800707148204800900644803d01102c1468501070b900546d84070008440741114440703005c44205004000c0d00d00107240d0000c01c048584562003242c0600f0181e44540480b030940c001c0307226094a50000240c1100307196001850b10080d2181202c0c00c018640766500e0b03100680004450400c40c51019664003400b280300c8407030042504520008030f03131034100c046d526105e040049910480b1125008a4240700700d42c400c1b00200c0d0308440d8811659081166210303050099005010440e010340e50004402c800e001d51030f411504040c040f04111210000802c0704880 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 440070557 1250 440069307 440069321
    0x50102091908060112080d090506010f09110403150605090f0109050a0603050d08092103150904051c03020d02070f0302011407050a210504150509010b130c03140a 71
    0x48074000c48028028a100040303118000e4900d004000c0041d81c1c20040200202002000c081c1c455000520070107958034402d000b40200360b4840c0e0082e16055141c449a00c2c00350320710b034200118150402d041840b841035480c0a5400b160741003125405451510810349001b00104c0c9c10684e003008151003002030b880d02c2440c0c80c904a4000d0340301044144d40303811004084a800e4000105030b03800ca6840008205d1040315450b41168208c4142c0700000b5644000008000d0101d40152010360b0100c2000b401c1c90742081c10607401c1c002955001c54a1070a5a03030036446040848104000141114901c66040c0c482c2e8190340c1c1c0d54104400c00c41d45c0c1c0307450b428401c40e0040c400e00b0031401503080481c540c00071060360101030f01035440e070b86845060180c0c004050300c51100e202100c1450742580042800d0000d51800b6044c0510301498032040044a01401001590b0f4028100700aaa040184030142038031480f0107030b4201d502d510000142d541c0303090001c8010f00113040e01444440d000d0000d00000c03104c2c9c0e87c4103107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 440071807 1250 440070557 440070559
    0x3080310140f0109031113021605011b091214071202120c0f06091507140601080d050a0e0d0f050c0102010b1c0303050c0708030f01050109081501061206080a05010209 73
    0x18a480704250200a0310b2540c1d4031a03a4001680304208100290102c500c0d0701195000900101c11160906180012a000680074415552a40e4819000d021081c450741c5850340350303692500054015a00050540704441c13185081100005100509100044800035071a2030075109981160350799546081980b04815800da20032025021040e001b5030340016076004221025018808080c108001c21046421501885030800482e5070494040d00ca44002884158456841e0700000500081614034040c41604203000d241d005940303640c00349800009031190b514592802140201304040440c3d800c40003982c0c018a440c031040070000401102080000c0d400704203034000c00c0f4140d0890704000c4840b4858541040c1e0b16982d44203074010a1093b00008d0703006490a80d1145054201d9850313822551040711511886281c0400620103980c0c00004200202274801c0200384602d01d070b41c0d40200916040c4251018003103001502442d540c46600041d006029040c1600c00741ea009040c81030203035008202d19 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 440073057 1250 440071807 440071829
    0x50f030301060f17180a0204060b031b040e0a0f0b0306160e1c0209101a0c06010b030f0a0b190603021b0d02060a0f0902060d0b01080610021203060a03080310 69
    0x20010071441644240031008001d032130f55040e61143d0058458020351014612000c0c018480401e000d078030340740503040050282ca01007a90360301e0000c1d00f10306030075100005a00041030403c810080b0b54000c0702843d4110708441d40010f450284801d98500900d5840b4000d0f41500a00040001208403d62144c145841503140d40100c0c0254804001d24a665036190b4500401d2081c2c030000582082094240c1c803c2550b80c807000c04580b9002c1501031098050132170b5001c00c1c000151940401d80600515004203d28405242075082290141c0380401c0000c2002c652107507565803060a81d80c41c0c0c46642288682400044204c2d40c403100e00401035032041c60b184407610440f0700d0058249000041c0e60242080c2540940030380c0c1c60ba55050009000107104040f002d0741c40f81400070259858030020b0900c44004017000841c0d05500d000585010401801e5900c01d90030300314010481a0080380040ca41a280500160b4036540e190010f0303241c60700c0340c03c0503209a0011041042590030040304c0d000f1b8507010360342 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 440074307 1250 440073057 440073077
    0xd0210081819080c2107031803080d050601270f120206191809020316080114060a0c0804030f020a0902072609090709061206050625050f03030106 64
    0x1550b1690716030561203121640c2420744003c61050009800091401400d5840e2010600b0310f0020305086003d414128070400141001015080b070800c0381115642c20007240e149207180c079400d14a010300c045950720366031241c001400c668400c010340b22001e0403003c1c0c195644010a07070101722002c00e0f030003080b4664140702c00215100100400f03000c1d05541c002c0109142070b6002c068402d050b4032031442c24080c00000c03210009400300f151250001ba00171942d0058480ca010b40b8000040707105003644205200c81c160040c001c90842c001c401c243c8200035500d00703580d00d0175480c0854440700c040380050003080b0301103400b0007000404007541214178000c13601c14048a4803110740c1c0703049104503180208a07480000c5030006263b8202080c01c07508810101007030900c5014004604001000c070f501c00c00046034a04180103580e0000903071031281e44860b00c01c006032824180440d415202d00a109e029603110f0080104c201c03d002030307410103103541c1f00c4252241d440001c00c0f51540e98100f070040201060f0030b200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 440075557 1250 440074307 440074351
    0x160813031707200a120f11030a0c0b010b0a1211040e0c090928050415050901150f050108010b0d0207170901020d05070f020f060d06240804200d021008 66
    0x2a0280019000340b000710104003000c4c03054501c1ca05006c030f50010303c1412214906804424400b8050010054035484443d425625206804000c141c120b0380000c10103000404046511082e41032081100000c0003402d6450850003807140d0040354454600f0640d03000421100041450103802011020380f0013482c0d030313200c4a20240314050701060000c039403802c52001042611b11070b0041500280103003840d8000c1703c0a00c0360300e0180c900450728869182c6d118400e104a899840a4100003030001c0c1500c040102c2c00e00380000c14644041c401c50320240004102c441a140a07a41140c20003a8000c40302400b150204000ca05650040154075016000b407100c1c810300c4600840407680e0080c1d01110302000880c0503801c11500c00c224060458110308103024070400d0803100c1c40707050064425050f00d20a2250021500e001c46101c141c004010043c4102c02e010020300f4210744020383e05408030000407204003200200d00b0300c1808241c083d600c0403040010608064109561601030700051007442c1007003060700 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 440076807 1250 440075557 440075563
    0x414060915031902070b070f05030712020d02160c03150207020f060a02010b03030a03241401080a180f0201110c060a0507050a0209010f0e16081303170720 68
    0xc0142504041d091108140031080d45009550058455440c6000c81860740c1a1a040340c11088017103c4240703c3c4000e1003d000c0c0c00090301c6012030018600f052941c941880002c0800041501440701c0302d07004030fa8034080090b03e0301545e4540c60945640d006441641c00c010405450a04c0180d030702040705100703400c4d40c0c070b880d0003220700582e009021401c21f0140c030418010135901c0204070360215540e0b698043c03c580e80c180002c003010a11560042150115512a170180985c0900b078040058403030343e010007104205280b5800c0c101000d007032980c0250b0300c1407808406020100141038840d40507411070307420800d003403a0000c0894000c0e65400c000d51250f902141e691101d0380c8807030b94405401d0110241043c4a1401484c00900c1001030f40c50950195001c07a258000c2a000903081d0140090103102d40400310b04400d622400c10404038a0404c0481005445108043c0060b800014000c035000c0915006181c1d00d031480003042c8402c0c40c6440e080900401400340d600c11201c00603420540340010003800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 440078057 1250 440076807 440076817
    0x1060308090d020310060902180111060402010f020307122001140c160203010f050f0c031501080601200d020f0304050a050f0406030c1d071d0d0303020d020c03041406 73
    0x121814501d05007201e81041009103407078030101c0c1d2510680e0521120340c284c601078040140003016025880b0040105542486040009418104034071400b241007110000500790350801d1b02820428036480c0303416400c904500c1824001f030504132600c1c5010040c83d87c44400801c01d200105880d003182992501c2403400ea41240701c495100d5403001000c03442e003562842c01405020a04048940c00a015501013400e403134429086081080d030fa4000c00c41c0000100e6004e0307074400441c1c071200d403a5250100c50712012151420140b41042909000074645074001d82c6400e8080d19900d0007018613a06c8080b10b0340e559034640d25050018003482e4207030f8540e488004107940540b40c0007441e481203103062a00b800154040c0352081d0f9803058898000102044044041e1006840101000482c0390036504403845043d40140c42001000a411401311081689007600382d80703030340304440080c542c03041810210003a00941903400f484074800610601490b0000009004a90320044e4100103101e04d4001c0005034007030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 440079307 1250 440078057 440078063
    0x180524060d150204081b1e03030a080903070f0b0402130c121a18070924031e0e0c0112050105062b0903081e01031e050a1205031602010603 61
    0x21105848000540158603942198040710340182000e40d40d50180b45803a06c1400714100701d080704140d50010303080c440e4010500d403004009101d692000a0046680da1007818920001c0181d400c012803ca013505000302e0782c10540102d1058140102400c6c034183e07a12007a50b040b840703444408034800f002c4506004a00071450340d070311039054804203442c1c000d015004103048034005101d11305034022660f841e1801c1e41400c50051078401c2d09440c003814050600407a80e0081174440c00d003f5041c1c14910035864400b10085228a030206085d08440c9540300d03143c0481c6602c00b0a41e007082811103d07000c000400100048003642d526076920f003003e42c4841102e030280211500010300304011040001c99500404255403026240c104241d2a00e102c00c080304c0c05008100c0000381013400740010700401142c00d251600c0e2151b500d80e40c035451680c40303015000d1070414800142070341c00800720512400f40728580c02c10f078020854140c001c502e05c0d00104668001c0320490001104c59400007000f0f032052081000b5254 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 440080557 1250 440079307 440079319
    0x14060d0b131e091e0f08030f011802090a050d0609020a08060702010f0203090d0f051312021318030e030705090108030c070f0e010303031e0e0a0204051f05040504030318052406 77
    0x2d0301358204003911030652060b61250707044c40000c000290140000d61142da0100c4410007154107010041c15404000c0c50118101401800070008a5488820b594100d40c03040340c0740c4000c000300346805c0010b00381101000e0b62200407040001071114001c240f05104c2c0300c060f80200000010700001c0800ca01094944d007800e68407024074050701900605d408164080c07070303040c118105a070454200448005542043c491241844458411401d100391040c4040041c1a014008443d4003c0b545082c84e0700080081d0800100c00036171107194a050207014043c08014140122a6071940c1c0c10990701d0740292000c400c90300c106000003a8048003040706400b650741c03034401c01c6116407035510220098030380b000200d00d00032104600041c1c0640305124410303050034002c000e0b01200c0424010802126001002214034419400e03802201382c61058074202500c408460003d444e8949081c01ca00070308048032103200c43e02c01c8843c0c481c1400b200103810190119014121660070f015440c952440c20300540d9020b030045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 440081807 1250 440080557 440080583
    0x10605011b0209090c0907020a02030d050406020309010e0402220f1a040605030c1306080f1506160618030c0c050a140103020702040b03030d0e120414060d0b131e09 72
    0x882c0442c2c2a03600104e15008462034008241d001803007205054541d1009a070240e071120046040038041962004114102035092602d001c201075204d10072a510203040000ca8400022103554a43c19248003000c1d60041350702616410072a03d440502c240540000710441520008000c00703c4000030b0911072007601043c0c00c05180c08000c1e40c2c2a0409803011081cac400034010201d881d840d81c1000f50041c1003d6440164509011603d481403d902030400080c80d400d0102065013901e03100201e60854012201010704144142001d500030070003012450f0070400704071600c00504d035210703200c841e070503010710382209103150795004015000d45180714144020984159880b001c0d8088d501030b0104600240010900f400100006402d5500ca940c580040694a142c80c0c4003004c4c0801100300041d003008203042c6850308041031003d07180f1440d4641407107000c0002e040c02865840790486685c0c5c03180039040c80035900d442e040407409485042019604102c3c142c201800e42c85060013604640c0b5003181d1024211 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 440083057 1250 440081807 440081809
    0x90816061112220806040305071a010f15030207080307080601120c020d080603030910110106081207021014030106020a120509150c19060b092d191409010605011b02 72
    0x120601a0303c4a640c900b1030f2a000034034180c180801445248603944556075240c8600d000005800c40406901c0c420741620018402c003500c0b440603c1c284d80503880c05011914800408902038492070200400c00e81c03001c01444207180e0003200c0c05000b114240c17103180e03600400344060001c8500c00e060400040c0c1c04035206680c0c85010b40b0501e90802005800d0707a28105d140701c0454440d1a40b0070981c800a010541002203580080c4038000c09020b2401c00b9064207990380d2402c909501680c01c01038030801040394864551806000c01503549044103c0164807581d407114044e45030000784d841625811400141010640d01c82c00498440071001000780641a000311081788280d040f96544142d18450007203010000c0b1218072010803c02d02c2003102090102d00d90040c0445080081c103010500481c81c90492810f001e0364001e000740d4002c0d446900c07a40e80e107000d41281104181508a101d4070300c0c0540381d000740c1c0c2c4a40c808a100d42e4401d8028025182d0724401101c031104034a441b80710100f9444400c03001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 440084307 1250 440083057 440083087
    0x290a021506041b021509030405090118091e020406170628020f07050f06040b04080a02071a070b010501080601050f0d0b04050903040e07030c090e0403090816061112 72
    0x124101820000b10083d10102e600da070701c204070040c1400f59004140f0390028107040c07007031542d1203841100510304041c0352134007003005104180148802d003a27601300d003030300405802da002c81c0406400c40290141002d52819540b0720341000002603010b6414090045190201d86190710441b40e000001498540d0343c00465100641c4040c0c01c0e120340e41140000580c1c0c803283c03400503014194440d00c5040d680c00390362910030300d404407803a90029290080d40c100f1020546600f0810b5002d5008410a9650031b09440b040741403c9040d00190070701070300d507090268050350707010240141a2081801c50721a9813148010749100c00304460345130015404215a45090212001600307840e1303806840460340032050f5000400b0380d00b00304c44010882d4008030b0308020b0011100c111030381200b840e00b806c1000d00c81800c001018103c3c40e008042d405101035021030101481240c81400500c0c0850582d81410b500c100284000c18451180000160010000640785100421f410038020380a81400303182c81011402c3d510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 440085557 1250 440084307 440084311
    0x308030403030912030e0c0a06020a0308090a05100c02010509070b030c18060417061005011d120f0d0e0a120b091905070302040c0e10030e010f0204290a0215 69
    0x1015226a100000144c80041c0014101c1c0300d62004a03090186841c0f01c1e262038105814148602284201001919000308120325036035010701d00403030280e81c0c07641c0b01c51824580c0c540091041c4200300c110b880403000d0382d20801d0041b400b42d0003401140c44800426540da28180286a8021070800205001074080801820304104030344400d6200c048800c0020482d802603031040c0d0420020701e035000902c5102784803c0b54130a80a0800ca101641444c0000b480c40392820b01c40c0c8403540754170b01d01d0b6520350307a11588502003090550407038495030020405141c5541c40e45510f840811803a001c02d82851a10100000580b054011044403052050b158a4005a8064166091402600b61540304449402c2c2c25240e4103003d00000e14410703203035105110846241c2c03d114800c0100d500342d000f00e159180c42c803c5039031820a00d004035100061252481c010001c401080c95110300c001000203090f03800c0c24900d03d4030814030011650075510100704200c1d603c1601e000d1310046e0880b400c00f044220800704156 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 440086807 1250 440085557 440085563
    0x6100e07110a0f1202060c0a05090406081f06080114041e15060303080a110d0f150e01050f04021914040e010b13061b0303090f0c0e090c0607030903080304 68
    0x81c941c454120301050408580600a0f101000380807480e50038031020401c0e0107540380c1d442c03008256902d02120401694010200d0920401c02c00050840e800e0303940340c22000180c43c00c0c0303094480c50040c5205c016841c0040b245020140c40c241701000840e00018854018803403038400301d11409c2d175110f503030b6030360215072281c24070610f406200031480114a1815031907000071541000043d8442c118200608480002010010b074103040441c4828001c3c4000305650034041030400c0131070030011190747c01000d00b9203c4403882c0300da050f03250b002450700460141d260485030107036030400d04d03901c1103003d22040c0e114182190f1410130700500c0405c46684202503c44482012030103503818182c0341c404000503070900ba400051a0040800d44100c00700d010300c07c0d400100042d0a02c211080701d82d4120151a003003c4a0241c00d05503a0b41d014400d015030100c0e01c1c00015402100c0c180d50f41d485c5c503c200700e0340c42c0075a00070039244648501c49440c0e0404000700c48401f03426403074031702c035480c40e60b40c4d040e48680c0300601c21 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 440088057 1250 440086807 440086817
    0x9080d080903131503050a050705040e07020f010c020a17070305072301020a09050f09040302100c1209030c150504051c0201150f0501111b060901020304030510050f0906100e07 77
    0x70f0700d00c16220004070010700720418441c40c248190820003800e461000e04100a030511306400c1c00281c3e50440d00722411621895001e20075542c4140081c5d050a1000d41016095404e001c0e41c03d009c664080796800c089803050f50360b9840b9030000b030000f02417030060700401002b00700104000d00c0421107109800a40c20440ca0310b4200c058510301e80d86003660810001c88012034170f4000c0c18451442c0495441b070070200203846620480c905a100290f80300100801c002e1529541d0044d514003c0c8654000341e049000c841041c007500340c041c038008100300f40300c03102990b04d40e1644030b0b10690010580600744c0903e4000d8014500e40010224088008800748141c10a5640e00d001603c01010150142c0c801054154607030310203103191500241c04074040351180c8100b50001c0400ba20031a03610116019148012f07503440d0748442007000141d10b1342c8102d4002a0180c41201503020402c015604007901c51a054100311081c0d8407414452580d44d07005132a4268241c1501c5810301001035a030080d19400240352800d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 440089307 1250 440088057 440088067
    0x1050a0b090d050712021c17130b130305072702030c09130c020d03021c051e042402070f0201350906090c1c0203210c0d09080d080903 59
    0x54646000060317440300c51030076103000780b403015850010b1604034401c056038400c404c00d11031b0350b89601e84ca020200e01c0e02450381021a4243c400b40601c18048050408aa80f096071890500320072440c3c4400c1c1c2c44206c8641c800e0031404a814100c4d50314100d40320004100c003800c0a00d0480408019400080161034003080c140001e50007aa14554a0700c0e1240400f20001501c070003a00d0001d007480f51081940301418010460080c0c0385406105000740803401e800000f880b601d0724086904080c0340440d04400044140b0140803d016403100701c05032841e01e40016080e1000d40c0040c05003603009540c80a0b110080700859480035500407800182494458a641c0d01c074070100c07500000858044988170740480c3c50100c104000d0200801c8046d0b04401c000b401005035651240000d00c142481d0104004901501d2807104110b403002c01a0900c003038149590050141e042ca425000150000f9941d05110b119041a8002075030150210105542900d805030004545841054902440140c8444407603c81049 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 440090557 1250 440089307 440089313
    0x19210809090c071403090616020f1018060903080403061d070803090117010e18030918041211190201020304090501090b1201180308090f0106080705100801050a0b090d 73
    0x4184520b140410700d64880c8841c0c242040d44440720002c4e002550310420040500c1d0b0384100c1594980e244070103000c49002c6d000e1021550201c03144580680201692102e004c640b42c0140104194420305900781b41a55a6140102d500d0401844050a812070800092001c2811604500c221071100e80540d5401c00303a08501e2840c1c480903520000054002203403010847d03034405026400898410a80c840d194141903d81e6107528002d0507000c2c520f0a0410303441140308080c001e50301048401080c44900a41000b00103401007001c94046070120002030381210400d02070008800000c030b0400080c000b80c0502c81c0301100356030074004242c0c19488103010005030502d20703005560180203d544041114005803051000301d261840480065074140118030005154a5910b840340d00c1e00f501e8041c956440700340d5100d0501020228810095081c0180800e400d14001000400c07901d05959060741e039590307110200e54000c028040c2c680d01c1900600104040420f00000c0c046815000305841d4402205036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 440091807 1250 440090557 440090569
    0x150b1507020f03060f09010f0b060a03021c020310090c0810030b06130e0c151c0c0509030109050c030f0c01020717070f060f0f030b090a0e01020405150919210809 71
    0x5071022051021101000800402806400d00e0b0f48c00060041c440300c10f803100054514042d004156040590201346010244500d281070055203101000456403420690b16840c0024079030f00400701010308200c8000403a03032051070f82c18441d0b188c04080c1f1003039a055070360b201a02170000c0d00066005108280c40b4070903902070300c180300002d8080002030020401c807005000c80c80440c00d610903c04e004c1840740103442d20340e01400c0e0007422400c200010315603105500580340360080d6809640c056190003201e01c200400050341ca9600c4d9411000c44041c1090741410716620320407c00581c1c0103030080750701000000120400b9030003600d01d1805a520b0613403a6035000e540700800e6880b050014043ca2201118a03421107901004000149801c0c080c1d400e100020950241c80074050102541d50b41024101d1204298142c60190000400d510030380801000580001c8e08507815103442544a4103400b1000e1800e0441001156091104074481403256500409031880c940800d83d82841c3c2008005d1847d5035203 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 440093057 1250 440091807 440091811
    0x40201110f030315010503060a03060f09121809060b0703110c03161406030f060108040c030b010b04061103030405060c07060609090311010c0f0207050f030a0b0a09150b1507020f0306 80
    0x110002c580b2881d0071450b0140c2c0e1102c0e06601c50500c8020030600080e40c541d04540c0040c1c98006a011591907207040018006003400e1901410a030040c6d215494520703440f49007000c003170603042640750300030303864034001000c40706207218003940050100310010020f4000c1a10280017861042a00c506905600101c1d050607210401245074680258044c800c9202c00300c1764003407140341034803100c2c15450980d62035110440041c26980c10302440000003010444008454400f840d40702c000301d0700b256901c0c8004030443d04180503440100b02010303500e00f110880041924030a42d000401850681c0300c20401c2740042d84101410744142e82c03110030101c4e02e02914044c2d003507036078881d40c4c980000b18543c40700e170760840b24011404010000303041449040503600061000030303500c04450780001c1c604940000f030b281c01301c0484018004041d140401c0f0a1700304951020415900170030110303000c02243e010a2044400a401060307100e03502001c442402200c181c05080b0080c80600381c0c81480c02c542000a14000c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 440094307 1250 440093057 440093083
    0x402030109020301180e06010306092402030a0605030307051c090b120601030c031404080d020423030c03150f1b0714010b030109030905040e250303031b051204020111 73
    0x1000495050b2043e00e001c00c001d07010400030031b4000064181c5404043c4405010755858011f03001c1030200011000004d08101c0428142214241800070f0181d00100c40c0c0705a100d20700320000502d07081c00700480d0710465014001d403416011902d164400030910b50021420070210325400701c0d401c203103034000700f03815466149080341c1c5180c00800102983c540d12241401c150030b0044048001000c1c00d00c0b560040d038404103041e245c10043c1c404000a02070380d807005442070101c000103043e0800408080e6001c00003503058a000400304810301da030311300b00c00001d110358552a50000f0701d251481d4210700d80103103403403100c4a036443e85141a0321242d0802e91080d81c60340c0160380d484400320350034852002d1381502a07000303200c3d00001d44c50217000a8410710846001d81d8640c0302750844042c0c10700c0340304504200108282d071800b914018440002d0054001100807a14200143c0086004003103078003501c0b00543d990794646070519090a0005a0291040303061058004460424190920081c5001d0b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 440095557 1250 440094307 440094311
    0x12021c0e0f1e0d020415090902090f1918060504062c0723040504140105010b1602040f09021e1f021509250e090c010f120b0402030109 59
    0x3005010000860440300c00d0074801c0340b4008820346a40c1031410072860708441110300c038154010500228001d03101d101c5031064010300d820b9010814200c281c0c0403030801ca00a0b18600c1c1c155a07a0180f0409640040d030300c074501d1b40703440040c0610b2800740350031031165030034000d81c004100112a80c45a086d2017081e0340880e2025107650460f001e04403120060a0048800790000601c0a0752404240d00e5500d01d01542038144080c1c4000350b02c05401d0300c40302c0001c032400b070400c002c0351070a03042c01155035050300d04500541d4249400000d01000300000d8031032342c803207110090300200104e078200300003801e560764005406070b2100382e1400540d4400c1d40110701d801190810f0314100044100b04800c980c0c000ca201c82c07950380141d41c0d17540215400145040c1e4040006201852500e44502c02c0e40340c24400c0396504402440300e4410410420501c05200031510744800252080e00e47ea143c05d40c0340c0020805c0d85000401079500040300d18403880420000c032004920002d2901015008141a64000d81024035aa6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 440096807 1250 440095557 440095577
    0x170412060501060f02011e0c230405030d18050d02240a1202040e18070807060e01030c020d021203101e031e0b1b1c050a110703050712021c 61
    0xa400403010900304d840c500c0204604030842c1201840034580c1d83c0c041100903510381c09040300c1c0d07003d5480030303131070484d46000c264100c0b1a11445c011654082e00486d07000713004001280700c0250059811440f0740045500000ba410b0400050080c01c0c4040042030341d004031490711454000024060281348041c134402d036140d440100c00c1c0301404011183c984084c05034410401049000300020090760050f1024441d54004000032003564500401070300500e001c2d01420390002007084c1c000d517080300789080a0301e090100a88000040c0c0c0c4450a4811020150f0464910b201d11544451b0045511400c407201507a04140c4030000300c40d5a0100701100011212000828811322203000850401030702c8220f24100c410241d50b80d01409100080c02c031107281c41841020211904000081da03145024007050180c022220394440006407030252508144a460301e1a680c12903886003046805c42030305a21494074000c05503031508218108030741110218040d500b510384004011041c11701c80c0547c940e5441c1d48030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 440098057 1250 440096807 440096819
    0x80a08090f0f1005040204060819030e0a060518240301030b0a0501080717240a0c03050603030901120e0f0d02010506030102090a120203011e06240507170412060501 72
    0x3118600d44201d00d20750100240c500044070001c0c00c0310359900300002c040f50b281c803284046001b400301504664098050f504090314051601b00c000c41e02039000e995166034016280040c01b006a0382d0380240740008404000d184006c0030200c5110740300c0207001e1700301d5502d2200540781c80795400c0201544611224008010414403248108890300700c010312008010380d500d0320950b603a452100740b060341d0f10005007020311040060144240d4040d0f40800c410f107101070300b0341c204c050340c03414040710702404151602d003c00031100e02c00d03c41c40e0702c1071002034015880d1141d01c0303006558100c00308941b40d07121074a0384009448080d0510103405901820700080c01c142d800740c0c10180c2501c1000700214003c2c0c5c41848824460381e0b40c506c01000300d501c49440000044c0c4c442c00428050440300100980b5504014110740301140c1c50760089049540c00c042c0c044203001d4030780851010080680015000860603c910404a011100d104000340483c4000d98038059a610b00e1144906004100ba24895901c0d8010002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 440099307 1250 440098057 440098063
    0x5040e010606270306050c03010510020a11010c050f0a05030c15040206040b1b070311152a07080f0c0103050c031e0703020702060c01200c0706030c0c080a0809 70
    0x840020009100c514104039004080c14940000001810840c004031044a880002860701030b50704484e080c42940341220300514154002e01c16240505403200056085602c08201010225800400074114585a00046513500200c4c0c00c2965280200c04006c04a44403c2240307008442c4078002641d198480b19000f40e050800b0301c40d00360a204656410080141d48641c02c88052398498504030ba12070070101c040f10742e8035811000c0e00d851407249031000b00520512102003035620030100d03503c00c43c1500801e424000d40c000c0e113414903980001308010500310481d001c035050002550703070b08032500713079a60f0312a0038580359001c0e0314014581c1242862104c90b5038035009580d030060a80080761f20318108504040c0c0012045006212400720740008141c0c81c0d40b00e5012918503d400400d6a501c911105006500901a010b96015144c8510000707108819502c0203503081d8960032400741c100395242c000194040c1015018000402c41040030400008104c9800303051802040c1e614001640b51008000d0300d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 440100557 1250 440099307 440099321
    0x60f03031801090e100b070804120308040203060702011a040908090604030c050f090106080f04050f072706032303160b070212190c020316180f0b01172503060504 71
    0x3ca0f1303c1c210f2007004455100840355034101d0b0050300c2c0c001d5941c03d40d410104114040e40d0412410140000111401e146e03118040c103000754000c03401d80729a5103621100b41c0c202d640b02d40303520200780042654601c1c0c40c81e16600011840d0f001d220103624050900e4001030840d80242c1041315078a40403602800139080075060103602030400d80c0e04919075414580301800f0f101004080d680701c1c0101c2c0000404101741401480000c6035a0001c40320450307290454030f01103581c0194580c034002c0640300240d5941c030f00da01410b0101c0c2d0300724414101003504d88003102950810300e4070b00507192008101024442e02d40740203000d070b158016441d24805041c48840203090244210000c000e8920911440300302d5040080c602840f122582405c8005c400c01d0720210382047ca505491601002c0300307d4002400072600c040d0b011032100313010002c01600031141c10350070071a04180211400202d40e203402e01d6140100c003445a07000240700b0082d400400031280c1b0140b1403182c586c8c40b4400603031500c20404c9241400d0290038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 440101807 1250 440100557 440100569
    0x13090e060606090d050109080f0d050a090f030513080a200433030b0708011703040605070605130203010e030c070b04051f1b0609020a0b0310090203060f0303180109 72
    0x4002420450000b0b407039405600e034410301c0790520140d90010070400354003158807554003600c0e40c0d880341c0000e21f80e14038642001811038100c1c4d0800c030000e40041c2180c85841e0050707a201c0c851042c075584d00d442c22a455080b20881541d060440200071800703800c1040610340c154881e5482c0e01c109031302c0c3c00354100300148058610f80100c0c240103070b542940c0a2081600034481002c600349401c01e4040300290f00d00c1c00954005801c441004041c0f11807698041510f506a4410400d80e80742c0d0a4183c80342a134a02c19841000c00140c01800594002031407600140d4101744407a4417110722108035000030742126000d021030703038036507200007596072600034188013290040c0403241116040c82d140c02d020901c0745030364091035007100ca0240c0644000c0c40c0281110100c0380030080d52185104040d02c1c11100420000c0010b03441006980d02c001588201c1030100d034442d040b011501071000e850502c021000e500041c14003a40203030200400301940d00e04101810540704c014125080209021001410302800c80e0024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 440103057 1250 440101807 440101813
    0x1b060f0512010501030f0609091109101211120d110d1805040e0a080414090a09051c021207080d060b0702100c06090c090b040c0503130807080f13090e 66
    0x1050600624a101c103045074820b01300803402c2481480c5080c0104216002000c0d01c600d049000028448240c4140c401c045041d600c0c0415529440014203002445208050007800682030580c00240000503c103d41031003d044001194000078149051480d030000810029550350380d0b000b40c040040295228014040c1000040310061100044203d51039008071400b0346c0e03d07592a000148000c2000c041d9a507082900552102c1d250702c2d00321182110301c8903052094030490003041d0100c1c0284540540786600c01c000341860440006800c01d50544001100154000c15480d107070009541b50040140c0361054800c02d50711000840c0c510111011034100c443c81420a00640d001601c41c45911401d03c0c8640c10880110800741c40c10801a10f14a003001f00492001130b00012002402d403c06003180804840c24442c0210480003112940811210304006038001000840490704002c01810164040d6840034500112190140702640c401c0800c10560030b1100020000e4503903500c10b81c50503845a0f005 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 440104307 1250 440103057 440103067
    0x50a030f0b060423030313060e030105190c23070203120712051b010f020307030506180117010e03070f0323030712020702123d0b0a031b060f05 63
    0x1040b60b07801540542810226510004c1c0b00e4080940b100c80300b001c1d4000c08036503440200a407440c15050041c4141c101080f41c1c115410014541030086d00e01c81c51401c040103145e081d40c10030240c05400b8918404082c400c144140d081c02d0384842031700d01003c44e0001d6889541e07203802d10501d4039094030701450011281003131140e10000340e028403010003030045514003651240c0c0012500c020116952041d001c00750310304078512883c1c1c004c80d00603520501568404004541e40e0f001444101005003801c0c240d110a1200184005444230312410b101008000c00020803c2070310400d94515031042c0e00035265184040e030303500304150744000d955428840c002c50403810041280801b900c1400060040304c1480030261544485442a9050b9250b05800a2110005420343e020301d0f925a500814120b011101480610132800c15041842c0000002a6a1030700b07070030090104500200013464010364400518600000801d00c01141d4400042c851608220150b2804102a02c011217410b603c60620406000d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 440105557 1250 440104307 440104309
    0x31701140a0611250b0403050601090f0515060a02070b07140105161e050715060e01050a060903020f0619050d140f04030c15020a03020306100c02030304090e011506050a030f0b 77
    0x14690060135055428400050503240c10521200403e400a92441e84003003400002d0140009a1a04a5004507006c106802100541d2420340e4021690701c00844080704101d1500d0411100401e90070110388103813000d00340c1303585660041ea4006d000076034006424180c8907891000c02c1c816907070420302c0810202096440c07480c01615002091055200c801d03e94030742d15030f03154000c50444019a40c865413101d2413a00724490000100360354002d00c2001682400080b400707040c03a2034024282d84494441180c001d1a46e400c004401304040c10564120300103100c1101d00e0307003510717582420703204554a8144d110611000c140d82203a03070410500511180041c00d01180010394030881380c2182d0036250a040350242c80c180055000680c50850b040544005a82c0ba1056810b502a600603a02107440c0c80c01d0440b240012a581400e841e4069030603081080b0070800c004260b0f0220040306a00030021440c4101006415a01010f42e40705801044000440b070140303076418480c1c1072034151420740c100151030683d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 440106807 1250 440105557 440105563
    0xf050708010e06061b010e06060f0102031206030a0c0b0d0c0c0825080409090c0510090e0405010e060a320a090809300c011b031701140a0611 62
    0x302c1290700e010b01842c003080305030311100c04a0b9201c81403044c10024040c2400061402000114454079036030003100c02144052414841c102c2c68890141d000314146032040d9080342c0000e001410792130345803041040a00005180c0c042d107200030142c03136124586441c1d00310344010941d18485803807420480e01c600440002152042030301c40c11158508000100c422903142d1030400b8a401d440a040309402090010700040607070020211a4403d04034032909035074a00510468050465454001c40c086010a1154a0102004030b5006001d0000440c01d550460401401d0031411b550f081c1d000d58035898511702810b0350301c4401e80005998107042e0030034940c03c030307030903580b508060b1a8804503a103902c500010f000450041d0703001d0b1100140442c448041c0b80b03004900c4088080e0120304010a00350004050003c00719200d07840000c10b03120a054615aa00000c1c54984040d8044060003042d0300302500c113a450000c458003800902070b01081045c9800d04102406500d80d00c0613080109001c1445c1c4213480c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 440107913 1106 440106807 440106809
    0x10507061505120c03030a032705011a0d020a0306021803070f060201110a020a020118080607030506031b0d1104110309030a03051003081210090903020c040f05070801 73
    0x801e5034544502d07004d0009541034005100701010a070017904666600a04410f071640098a1034a0345610389910070300998084e9903412440e040e002401304015a05042101e4040000d07006500041c20302d030580c000104016004110760b5210b01c107442c15803401e080010207541c18540c40d83c030071011092592046100560034180e8103035003051414110b0340c2c402074580c0034090807203082d001074810241e590307502c014080070751500042da5042072050350300404241d6030204140c10802c0c20103141141e10405020140821980c180d45903454451800030b0750f81c0000f0145005411100050051460040c0080c0c83c600000400514500100003062491043e88040100b6100c43c0c48500e81d4646901005003039100400565810503500708141e540400b00800a054a80e1183c80b618242c420180d000c8000d6882801030043c180303444d00404030501e0b42c08404020714a06541d000300342c4401 = true := by decide +kernel

theorem cover : BRFrame.Cov 439928057 440107913 := by
  have h0 := BRFrame.cov_init 439928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 439928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 439928057 ≤ n) (h2 : n < 440107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
