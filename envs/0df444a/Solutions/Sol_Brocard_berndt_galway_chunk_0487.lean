-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0487
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:03:16.556799+00:00
-- url     : https://prove2.me/submissions/32f69709-2c10-4b0d-9f7b-f22e4c7ab095

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 87410072 ≤ n < 87589929 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 87411322 1250 87410072 87410077
    0x10c03031a0a0b0c060114030a0201180306050115020c030c0604230909010f0e0703030e010f050702100e01020d090302031902060c060a06030c0807032003150109021c050c071205 78
    0x4880d0701441a42c00420010711030005016181c4500c0100d0341d10341d07611101c00d011185146466034141c1c001810718005540a010241c050540360910b0000342503070307511140c04861003a001002d580c0210b017082e24541ea4104000384040f50110050080020140005800b5210302e204829403030310b00c228801c4801c812101c480c400940003030100ca0151520b02e05541c0200750304d14a000ea11840c1c4000c0075104500080c07003009036545a2a9401909030f80c20042d00c800c2c20300f0340d0360b100300b0408000314001a1202203496011495075102c0141440c50000003900302004c441004081195039281000560380024410305a01c5004d181900e190b0034030b0001c0382e0303980328400c0341c4170203445a5002d02503c05615406481104e003e060404842501d400200303417250f0b59403001403c4611360f444503c4d228150a40e80d039801d45002003c440e06000164406034454409034801c0b1034481e40031a060821001c0145030211009128800300541d22701101244001d004601014020400c00d011829401d03006108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 87412572 1250 87411322 87411371
    0x2040501020735011404030f0332060a03060606050a0806040203041a0601020c0a0e1501020604110103020906090d030306140a060816051b03040824060d060b060a03140f06010c0303 79
    0x5c030600c18038050401500d6000d401103060000b03454407500d8007000d004501e41d82e0748030028103440b241c00d00b12004a05960fa002501c02503100580a000000150703040c400c54006003400d1300c8903511040000c10280031544001c28490045004200b0400028111902e09050f45044071007000c150311070b580100c1c41c05445c03880c103a802141d0150041151406161400c0c400c0300d108904546120000f8012a100c0f40281d800415081500f0302c00100e40d80290007501c0341c071030060021802d1824004c0040d81c01d00c1c0109065000c280e664400303200d9210400c000c0f0050b00c4056550180d8075140c84002800c3c05002024031041d020364040b81d001407440b41040750754401d071188000c251806500710f09a12544248036640b0244103980603000711401d418640310149040c0c9803087c602d96203020a004480c12080400c6880d26650b01040c83c859444001506094800365030000301000762410138101900080c1405010044150400c4001eaa2080c0c4a01000303505180200300e488000d004141d4100d00703400b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 87413822 1250 87412572 87412601
    0x1309110612010f0603090f030c021305070314100803090f0406030501150e2a0a020a0b09011a040902100c0609050a061a0906060d0e1006090204050102073501 69
    0x80019015001c22400c9040c2c42e1041c071101100e9694140607002c45800e044010090707001180484042400307001d41210080c0040c010003800300f294401d40c41101c000b00c0c1c00c01c01082e80c07441d01000c0081c0ca003940c40d5215a402d8000706070581090101c0d0b9481c092a140c0f41e02c44c0c1e9841301044000d4a40e0740003e401190303c03000a10051a02020b0b0711002046400b40c00c2d0a031b401d02c00011042c840c21203480140c64802112007202c410740035003203103a40c0c2c010711049081d4840c5070140400550351110706032190450b035000007103040d4820b240c440f81341082d844a506c503904061056025070303903004040c042c3d0705003420304003103030f0390b00f0300e0302101600c107040f0301174041d02844004030140003007600001c1d104501b1b202c0d151600c2d40100104695060141c1c1d0312030300a40240828840042c480d4801e6601c02250002c0341e4820341903082800c1034441580002866a03004202040305580412000c40a0074801655484400380c07191401d203090850100901c0e4055942000c054148086d40142510b003c8003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 87415072 1250 87413822 87413827
    0x17070302120105041e0c0902090d05070e2211091f140906040e0c060f090d1511180103090f0602180a09020a210b031f11030613091106 59
    0x148100b802080f0465082d03030031030b031100c3e0f02104131003103003031050807071640f042c4410700c45410240c0400094200d503005942040090f05003038041032040080400420600581c0340541c0350031841d0741d64207440200c480c0c0c0c11002011000e00010641c0d9400140c04c10300350740041d403079902c0009a40c0180c19000c1060396a681340b1601207039041e071226031501da20005892a4410b80c0710740c0203100c111426012000c16941004408080e2403a2220040c010032002c001190b061042c07100c0020b01c240c0709900d04a46070120605600946000341c02842904c0700c1100070107044c5400d01d8002c001e10070210b2089410143c2d00e0b030b02d290800c9403442142c0516034119900b1074a035180042d4512083c500d2110561081e00744840001d500c1649000311a01410607540b150008500d9a990034044400c0c001c0046000c1d444000d4102c031074074204511030108100216140c10b01c0d4880521604607802001048081041042080710b280c0301c10a5680405464140c00204da41990408503681880e40902540c1301600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 87416322 1250 87415072 87415099
    0x51219030207050108011d1303111e060903030609040809060d0f0b040f061503090804050d050303041a010302010804030c1511090a05041808160b040308071d030717070302 75
    0x80c500b0a40d4800c4c1c8940c1c100e030740c03103003000c5d12403081d42d48000700310610b200d000428030001515903e02080c440d003803602d840141255206c0c20a544004071420000704181a4a042d40081084e076400c0110071000d507255090030800b2605800009001601080c2e0001e902d602549030034003141c901e000000c0040113908442030b4000c000e44104041c3c1c42c42117003400d280c510840e5084c4a07080c212060054180700d5640d10b40400d6000d40407202c8243c40d10641400009600d454400c2c0c41c481c01c0d0300c1100a155289024a000718280ca842e66410001038106001840141d8002302010b0300190103051100070755403d0320b0089003a9000c84030958905041441480d84141c04402074401001d0440e0b081a0482c0caa0342840b085542904e046190300c1203c0a156020070691001090040101070140b000313600a03840748483c40000744e800303c0016035004200011194000600e0b11400e220420694091204900090352840d00303019016640700c1d0001310003540b40c820400880115409052a96041c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 87417572 1250 87416322 87416327
    0x20603040f021f0206061c050d05030103150504032a061b030e060c0d0c02030c060103150605060307020d0e0d050609060406060b03070516030c0609060c090504090203030405121903 79
    0xa0404040380074030f00115440540b40c14601c190100c0fa203030360703004140369a283d03010007680d00400a6030340030b00f13140540c145004c035005201240008500d610307116520b500d1031505100030001d03803140c086418a03007001e100000340e202250b15882500c1e6000e0403e8149842c10398241100901c9000340715514200c840302c03000c240b101081c0800100c98504010110900380800d854100c00c6402c0200350004008580c20480036501c000345040107441100d00308806031581c540f9108003030700282e480720000122012407580d10b01504004e0803094032007600307501300240040c1d50740581000036801c0c00403c003960801a1541d0640190058000c000c65580782001503456896034000d5500f601d440e8144440481e01e61581412030f401011560340741450b02d00040210b2246210241c0214100400d814030a8007140d201c0c05003110090060f04000b500c6034140c64050800b10140e030003a40920700300410034025075000b00a940480307100f90b81840510003001050342c20301d0071040303a84010344c40d40d1011034103166 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 87418822 1250 87417572 87417593
    0xc0f0105041b1d0403050f03090304081c0c0f1110030b030715210b0409060b01031406010e090a0e1203041101090b030106050a120e0c040f0504020d0201140702060304 73
    0x30301071090800001a280c0604100c02102c0c00f8412224150502000d04101c00d40d5400b684940640380903810213158101d50f103960b50040d5019501a840482c1c2480300e84401d01140162100c60700c105d144c0c420384003038040d040164440002c0c080031010040ca2051042180d05118140d1000389030f804d02c2400044c0c068002c0c007001c0a001d00920a018002ca4040015004000c1c80e68103511254007240f20108050340c205038200c81c81170142d4551009d0151920359002d07015643d403003180301182090300d4000040c101d0b4043d01c052042d00e46104113000b020390b000300c0d1808940000f59a2421184c0c2c400c1c0011001c0c00095410442a01c91013042c0070003c1103581c065400340340300d0210518a012500d0046031280e0701801403000c1c040c410001000003e004000a110061a609029001c800d441122004580c10000c00155541010f801c0300b0b1310745814400c0c000303211486107007000141130079008114805a0740000a040c46800d55090400284080681d18070035401400c0c540e6a1415203002e21099 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 87420072 1250 87418822 87418831
    0x80a09020102160609141014030c0d0c0801030201031406101d0303040303030207050708060103080f0a0e0a06110708060405030a0507020d0606080c1804030c110f04020304080c070501020d091a0c0f0105 88
    0xd5208006e2030300ba00c2d101600501200481e640d03844040c100d2504440a940040e102602c5c0c0001007120b080c50b081c07a80150906030141c0c2d2603a41481d85035000150540703003507542110080c025079041001c1561401617000c410f505500e00194100310203020541c0c80c04150a450354107200200f0700004050345500100149032140080c0da003804c0e9146e003059558a400e000040179030809010f10b0020000040260518808070f203130a00003c402000403911907000c6400900004001580c01c080e00b560030400c6000408080d801000f152405450b00e80d200e0050b01c901c181000741c0050008255a0350700a00d44038a0340007081041202d50f550782590350b0b030a543c02c07000c0c0195007408114104110004900d0320454041c0c49018041540359106098025500060361340300780504900c40503074407140301440c0708601c075080e4250364030719400c203e502d0242507034800e504640c440c2c401c10807026400600780040700d0035080c2e070019003c0f50612030f1000e0300581d0b004e110a481190390015a1000542100d4042c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 87421322 1250 87420072 87420089
    0xc0f0102030f0a060e0c07020603060a05090a0c0806010e0607120201060b0a121407080a0509030f07030503181606050313200906010503061005090409050d09060807030c080a09020102160609 83
    0x395a42d0b005e01d0030001e0101d5806403040382c10f00c010009400c4c0003006583c400c0b4001c022280032501d6100003400c1200640384001d486030384001c130b081101e400c61100c070340102090900b0900b0021450000e33009100702000102030030702c003184080f1014000d400080140100320b0600d034940701d05c0c00000340b5500c5100070301384801e81041e09945012000041040c0590342c1ca0b950f445c01f6541c0e250580014180141c00c0d0a01d6120400c00400020b20300f8010b0708103648290780b60360352403c100101030000c0a0240306840780340c00201140030310b2400c9140c004120f511504029850b591402c0b480c0d0100740c0d000b01c0180601c12041d1000d10600d800030340e00d420700c0204540d00911034591400446003030104450340c40c1c0040008190350b45160085020b00303800c440c000c00101f00000070b0b694450920851175110004141c2001c030a10015411450140e0300c1a90b600d02080f6800d42a480208401c2018180201c261750300d05a44081d641300348204408502c0d0940c2c00d11181c3d54400700202424501d1094402 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 87422572 1250 87421322 87421331
    0x30515070504050a1413060609030c0906270b03060103030504090c03110d0f1107080316030b060711030a02120309031009050a0227070503180105100b0c0f0102030f0a 73
    0x840c0110156400e43e100a020858040e080501c03960081d010240095440b8038240003164078440140110400b401d075695039044c200c1c1c514503003c0c075284e81d80d80000391740324141107060102a003e050740305407661610795203000c0e00d9400740f0b59400074401c801019070507004030000402410b070070034000e108031240700604101e01c1d118008214121040038a607042890001c0001d4a40094650418960b109840000090040030005c4042e525400385c281101c000c0804020400028068500203412a40d1414144040016100003075841d2042c8840242501490014801c09880402828403065409804c00303a81d240c0309821643d40750001d0403140d100e0300c01c4070102c1e056007540740a1580304551100c010054491030360300700030390460b0152120007070b0501c41c001100003105c840110b40c0548200d0705c2d00ca551b8204105407100b840801c11850f24503a0502d0700384031070100c01c68008000c03508402040d98440b801681420b0070301c031044481c00c15540c0088180043ca82c544241e031802005148030412 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 87423822 1250 87422572 87422581
    0x3040212030d0c1b0203121b19060501080a260408010e010615050a0804170705100603020a140d030c02010201020d0e0c030c0a0303080f040c0929040513030509040b0a030515 76
    0x20100148000003509500400781031f05842c14024007401440414080030700b500a240080d0500d005002c00042581d4080301e0549000c0c0402441824090012540904540901d94035003c1d00079205030440c03540c454070052610345d210b101100350303405000024000d01000d1072011179035002e02402e0080501050141e810350440600840032140d0100d02d50702c9620140e5070300e0f2600103c03c4e40d002d1070446080d508001c1c2c1e000080090000004200c0e400c07000148060450050001016080d0011a001c010049c0035502cbc0742d42d2800704940301a40b41c074200c5095226031004034061701034507035600651030410094201c0c034400416078451a2030250f0440b11400000002c100b40420b55100140c046981e200201d50010308500c0300c40c1d402406622800d00c0aa40d03070000e107003241c00401e02c03518110301003845103211040c00d100510280d101220103002605105403000c0844021440081c24007170006a020b0b031544854001d2440ea240c010241c510003540c030b0030310507100d400d403500b031200c842c200c2000503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 87425072 1250 87423822 87423857
    0x8061002011e05090a080304050a0303060e1504090614090307170a05090d050f030d06080c0f09060103090201030f020a0509090f27030d06091d03030108060a0203040212030d0c 77
    0xc169548401c0041c0b4810000c11180d031009010180080380d1901400d002200420a202e0085000d680300d00010b00b505181400d00604507483d6800c03d0411100f0f000600001000d4610940b40880046900040d0070324a89082350080800b03001c0d00805070710400030840ca001c0e000c030141c070380035000310803044001001400074051442040c1c0f002001c1070701030102d64901e00b0030b030741d0f5981100e20030400c82c0d805000242006185420200e03e044071141c94403400c0c802e8410a00c807035a20514141d440e501501d14040000da068900101002e0406079540c03140e8095a1003504007150b4103415031021940c80307105c1c080040c040da2009070403500441c03051005ca441c83c02201550361050108000240d0704119402001703010500c0400d54035158802404103c0340b8001922a200c014054007a000800c8508560302c41a1504110032480441d00248010000c041011803420703400b070b02603480140d0700c1e6a0303403001070300000380300300856110311022840d00508106503010016040458556111302141d40307124 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 87426322 1250 87425072 87425081
    0x20405040e06060a1208121314030702030a06020a02070f0b0909010518010302130905010e0105090706030905030904050c12160311030c070b07091a030613020408031c0603020406060806100201 84
    0x1241e030450403410082008a240c40b400b2041075100d0300c4558500b07143c7e00ca00703840403101034402101150361155110100268446c0c0c980424100001a50400e502c680009845040c050405002c0513000980c040d0312502c02e03c0035201520858200b1011182c03550b10240d641e030041c620b000d0040b00c2d1180046a18584008039409113100b140c0e981d16580e01316424049584091710007501c0c1261102c0c52840051802e020381d841803103040000148074500300c44264a0110203030720040c2818036101e80a0082400402201c1214070b0565000c030340ba0b15003415601c058800e0001161a0702e1300300d8248107451171030b8160074201a0056506115040051400000710710041d2866580003000700300000000d0032030410154003040908045220b55501c5c400002a9203000c1e40030100a03400000b0080f1920345400d003400083c201c0c440c2142060304022a13150340b842902440270b1806095260140c0d070214540114010b0355002d0002d20003140c0c0d0b60000360240b601035426522a60490340c2491000c0d10521a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 87427572 1250 87426322 87426331
    0x70807270203190c140d0c020c010809030403170c1212091204030b1005040e07030b13020109180e1903030b0306070f0309020604030c1d0a0c0e060f0d0c0201020405040e06 75
    0x810f4850b80c80c40c0507410004108a01c0c141040c8001a14440300c22200903000e0107081c40e504030302045c00c0c0c150342e000a040c00b845158143c10300840e0400e200b91070704008196401d880d800f404400184200888140d83da003e02e03289030b01e05100388401218140080d4000c0c0810700c1202c2c21032075064441c402c2103601c2e00b03103081603400d06180038001000440c1c0c900d48500c0c0c111989010000b03000b034850000c02d041d40e5184010000300e07888680d003001000750b008601c50b4000c805400c2500c80001a41c0000c00e03110140c8943c4502c100380c14808a400c040301da0200788a005030804841c001c50980070a132824443c9600300350003180c079000004141c0d007004100c903445101c0030f83d10781a4841c00b06805800810181d481660815028400400016034149044000c0d00c0946440385145854660350200c01000611003002d06040803000344400c2e030402c2580741d00e11404c4032041e460349903e14500840d03000e1180141441c07418a628100404e03010340c020400c1d00d40c04e071400c0c4206e0301d0032001e882c1d546070140c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 87428822 1250 87427572 87427591
    0x60e07020f0d0c020904060b010e04060f08120405030c101b1b23010809120f040504050606040806191b110607030b010804060c030e0307060501150e06030a05040302070807270203 78
    0x50000340c7d955114207041501410300a120704070400c040381c210707001074224000d48042d01384184160702c0100154513003001140d90143ca05810f01c4042901c036100707110513501840a0742840007c1d240034165410b40319581c803094020340b807482e00705101d0000b4001211903280514010104840f01035504145204008401e4002c000165100460b0300b6040105040c07a1405103171908125076251400800004c0c1c00b82c3c0110b511942000108800c03500c0182950784a130008000c10440b424000c1421948032480c503001d456681c0000c1e0f01070f000340c852011880020f258100741c2e9409541c0140d034041d80003c602044842d5a681c82000340c00b11009584440d001c10b18180010b00040c0050300311302c4d43c00186280101d0811400d1850615580180000311019030301d541c01480b126250300e541c24845a192318010381200b20070b20100380c0030310025001c80c0c0f04640301c0001038241030080159000a14240044495281e518203042c012440074180c040144100c1c172100401240160080e070707018091701c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 87430072 1250 87428822 87428839
    0xc1003020a0509012f06060906040204030b010303030902040f0509013e0d02040e0c07111507030c14030301090b040f0504080f031503010c1e0906080114010201060e07020f0d0c02 78
    0x48005443c1d505030107004150048810603176103000c017101d0f071003204800c40030001031210781480810007030001e5000304043c1c0a948107210400c08074914403806411203815003400901d1840b0750001c07802900705051141d80031800c0c2428071592400c15448500111071200c06420380c020400d40c0104004103400c8100200300a450500742c2d00e10321791004003000c0c1619100103281039514100c40e8800b580c100c4a00ca060980031400034184509114800602c1030125000e0809410104c281011405004406800c204000601030100503500c020099440036042c1200c0c0c40c3d44e5114441000391034078048460186081c00c400d020384800c14020b4500aa5000703809a0800c0b5a240b1a402c15400c010072540d0b02c00c1da0956243d105d600c007031080c44050b020580d1482c0010080c5005004d84210344010002048550b00007081816030000245041d2924904045020020040100c1c0900300c142c1010a4510001040c00700041d00011394440754095001601c000d015041404e41c0c064603d0350000e034015001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 87431322 1250 87430072 87430087
    0x60a0504110f0f0409030c0201020f01021e03060105070b09010b130e07142b0303050c0a0906300615050307020c0108041a0703060602162916050c1003020a05 69
    0x400081c1032500e02c040c2598801070071050015041d1210000d0a0303000c14569140c1c07a05650b814032016003816800c1009500d85a5100c4109011100325141400040004004105142e101f4000c54580b0fa801400c80041820440d803e02d00070148180c4d00c41c480e20408942e8102e95205000c0c42005288007070203400c4591a041441d0b20445440d59852340c4071525903050007001e482440c09000241c1c007030020504180e1203141c09001c4030303800350000f482c0c01c005010b41401d00d9408512001941c045242c01030703030606c012090940c1e0402d05541c183d44114900340c020480040c590100003162000d408901c4a2040841c1c16a60b510042c0d1fa044016002181c00d85030f25409074040541042c495140a00303000034030f007040605c407071040d504040080c0c0c507110104085641000010101d2000c27201c420041c0745480101c0c6500a000b1050110004400c00d54a88005001083e5403ca00700c040c5c0300805219913240044e00c510f01301301c9143c131410051005140051082c4280d80801d41d41c1d0322114a8100c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 87432572 1250 87431322 87431329
    0x503030f160506040809030c01050306030604020d0606080714100504030201080117030706020a0f08060f010e01080a2d060603060302060f09030708100f050919170409021209060a050411 81
    0x8049036040d52000e10407000018104104040c401e42c0161000780d2180360032001c16051034401c181140c1003040500500c6480d81d000f14847da045941120ba41104051a1402c2c001800a561242c0c00354043c44400050420300340d150700c41344880031981050349082c4d00c036050b56a40101c3c00064000713076040e00184490340d011882c0c02080340991302200e05110903590f61000743c0c5e01554850002541803019032804c207810455403908090100c13201c0c00c8030396500c80000e00040b511040a410070045002240040c51560b102510741d00d00b1603603642100c2c200340c1c9000010550024030000407447d0004c0018418824401c030700075254024651883d004548100800075004000100d038180541400001c500313100b0009580841c010351030114600442551410071254000c1c40c1e000c868200d126800019040f400801d00d0355540401c0c02c9001c1c248440340e4084a00542e0440d164140c800074603048080f0440400910540d00c0400f128415911484600161401501d0081c502456901608039525 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 87433822 1250 87432572 87432577
    0x2030103120c0507030203070906180c08132a0315050108060402010c020418230102160308070908070602011b0e0f0105030c090a090501030b0708040804062102070b0108010f060503030f 81
    0x90143c2e00702c3d0402901e03900006e00703000301a40600b844a070740c0d8100700f2005005203881e810841314090b0401030b03c07003d800d01502c101d100402d031400c130459031000402040810600d4150304589000e10015500c0b170180200305d0352849001c00d445444035002030300229220390080d113050700c403024007070203594440c1d80c0150340c4500e1900049078456154a01884444c10b283c0b11b030400507004514003440400b021614800d42640310000b0071040c0d0040003990000c0e1514021540c009a1510307040c1580c0c5d45056085890000c40e400641a5000381c0400142d015070540001d21011028680403141001d541070a4512180060049400030300998a2a0066002e40050350b07024101880c09482c014a00b030014100d0002608003140107a5220014401d00001c0c66102c0e80c45140c2e420402d8076401c00d40c40e04000e0f401688964400c00001800c141c0003450381c0365540c0301c0086121002d5485a00c545021800b52000740258141d2b90b19104001e504500d00d409040221b54028010718507001110400c503d5170b9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 87435072 1250 87433822 87433847
    0x516020f072709080c07050a060e060f090301020c19020a0e07080f0c090d0f0b010b070b01030b090c0d08180105030c0a120b0307030302151f06030f0902120f100203010312 75
    0x1030f5a401e000001c1590310b8000c12122a51201518000b810f01c4200900c1c2111074000300d003001880d0b07a02d40c0f407075100c010031143c1d0401c1000d13100d621000340d400080d02a110301140c4e000140560b03050043c0d480980f5545201c094800c4903812417298444c0300315201040c080380c82d180010488000b04202480c101000c503004011003a01d140307800c08090114580d141301c4182100d08842c641900001d000c014030445001d8054400f4652820720141c483c01d25021041c0005401e01400c400800c0402c00108074100d0708200c082d110348070501003030030b00740101e8000d1250307000c4501a1000e010610741c8035004607480b0b000c0d0341c001c05040220200044400c0750150141450031581c548071080b0a9608224550045200b03038020b001d082c0c1e01c00c081c0c4034a10f00150220052020074881801003982070102d01059904500d000103044600d60504000350502143c0a0b40041c4280250301e40c017400801c00821004490045680c26200e009806040784400d21020701600764140c0c040010600c03c10195150 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 87436322 1250 87435072 87435149
    0x10305090f160513020301060203040510091a0306030606040501030302060a020a0c05030712110102030915221101020f06060303090f0a0e0f0f06030c030a03030209010306090516020f07 81
    0x1204a250a02e440d03503218180103040c4140c44100001d18041c00000042c014100e015411549405006940e900680c02564810040d100074601141d104040e01030044c04207d0380b07036000740c500d81c41e4840c00c3c0d801500c206020340200c1c070020b40c40e401e040c02068122541940100310982d01c1d1401c43c002500211442410010700140c028085070b8100f014080e854000e081100341c24000040141056651300d079034070700e40d9005104101032440f000c01e1144000c0c06c158005290b980e1342c04009e072030340c1c030568884001c6030725404406030904c0300390b54582c22811020b0b001c8640007620510b40580d41c020071079180d90b050b4002c000090176410f000c0440e00120303001522142c1d1098646080001200c0221104113040306100c08025028065800c615003294081d40644544502c5002007a1103110404001c3e00b85600014103074100e9102e5072200b00180300c0c0140800c00b5041101000303580d0000004600010b00c81c51412884611002c00e0000407540416090141c01070110b0b903c40c0fa03017210300c412094 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 87437572 1250 87436322 87436333
    0xd060b030c0402031602010e07210606171b04150306020a020a0209090109021509181b0406020102040e1008030406030c1b050606030d0201060f0e1506070507030623040201030509 78
    0x680d074485001071170203107031400095090104801002421a032120621242907417201c0320801409a0a1282a10030481e0007600c00c03181c806400c102c809001c907684850490805c03a8001c0442c081c011442a5210324852102c60041850100700030981d0340d050460074030419012030130000510700b80d0041224102074010b40308060303401d4000030400c04040300c1810040c0d44a80c445011490a0001c045c0f21613543c444060402400d034020840411400840c15400451100420036154500c2200030260305910f0401399a0b9444480084c084c3d00142301e250786c14510907010a0582c0c4414145070292101800298105480c0c10021005044440c003a030b41404001960034a61645c80010a0605070094000300720905000c82458504812450518110391610b0000c4c82904401d94032030046400070001044a82c2f1446003007660031a042c2610340d805800002e42d1000c20502142c0c49040380e016003070800c40d005104201d01c140d43c00d0242800d40180440300028010f42c002c0d40b0042e00f011520b0b08481 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 87438822 1250 87437572 87437593
    0x1020d1805101101050604020a0e01030905010902060f0703080105040905030a120f051003020f191403120705060708071e03020f120a1a031b0f01020f120304030e0f0d060b03 76
    0x2080140045964000118403d0190000c0c400901070990406419601149480074070034004014030f540c084054105511201c160f0300b440000d402c4148140e8008003800e582d5040100d401c45158400705003200402c180b02c0001586240a10070103034000d8000000d549044085801110750303010343e8004880180c3d40b4502c0443c0c11603e40304a40c898411054108199411401080408020545224422844581c0407000100c88140707050440354001c6100c00d88205420009051200c0440341042840c004201002802800501d00d401414030b9201c8030040e4995a60450740300000050481410205400501c09203219030f0042038120ba00c5a641400c10703104111340590383c034081c1e50100c03103d40c4420249150301041081c0c44c603d50804c030004d00e41b462401c00180a0054100307012403040300801c44011083c1d000b8000c8038041300034a4141c52019141d4101d02c01d140c0c005580c160009000b803140d11034141040c4545d0780d01800014000100d01d1210380da030034060b0071142809a0140103e41044 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 87440072 1250 87438822 87438829
    0x13140109090b090423010207050721020a0306020a0e06190305011217090d0f03030e10020c07051509060406090303020c0d03121a0303130e0f0118090309030b0c030406051501020d1805 80
    0x14945c6901c180042d041c024548001c84c408bc41413000540c080203031b08155080142d507080059011207078400c502607161214410103541212442e24a41d420680001d00d82c0c4034001d001002c00c0038103140e0707101000f46988031480c40388221640d01c0c0045c80b10000204400740c14078001c000d4450b962000340708a4407a0602d50303400d40700d03c521030301c100c010136280c2241c20181c40c0240001800401c19100450404000e0081c0d00c0e80d64a151180d030380158810b29164a404c41c12070100c1c1c2c050300700540003d544594032500100310105520003903006001e801e00152440c5043e0080700c540079059501c0000c03111083c035000c030080c560104c10000c65560200c0308602520140040c0440000e400c101d4401c95213030450070481000c00500160341c41c01c8400040c0880800003c88040305401e00c040010070080300c1c60150740c24610790f00301a00314444042002580541e00c40190b216a2041d801406142c50725400d04012a05000010f40580c000c44d42e0709040c4d41c490400b4031420001c615070842d00a981e10f021 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 87441322 1250 87440072 87440077
    0x302030a08091e01051005030f0a0b0604022203030210020702060306040b013e030403030207030b13020405040605040614060f12120a030522050d05030c13140109090b0904230102 78
    0x510001380d440700f00304002e40401090010052100b5000ba0908100000700241c07100e444400040c100d100d100c01041c030710b84a07035041c1c1c1c03001c0240b01041da6070000d4030740420180c81c0e2680300803801845000c003103420b1081c0c00e000f1f68105a80c0644483d042d40c68000030040035100c0e0001030350400000070380d00c50b803110306200040c0d0300302641e6820a0340c0005801c1d2a0356881071074020180c080c0e0003044204000790b4002070070411a5040106020036856001541c00c01007951000607500904040500007402515400540941e104003000c006a0950460406001004840301d60f80b042c1d0141d445086410301c0036200c440c90025070241d0740d11fa40014a98060360700001c28440020b5900e00c100010414003d00e0340c0da50000003900b0320815801d5a8034559259034059583c0c040000c0840820000c1c00e82000f43d45081600d011038015032a00e4245200c1911540b03000b060000740c001c0c5000810300158440c01c0c0c184400a0813064885d45c858481e6100340c44001c10141283d540680340c4c0080c010207201 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 87442572 1250 87441322 87441373
    0x81b010911010e01090509010605090d080c01021809090604170c010509060103030e0a03080f070311061f14061204140d02060402100f050a0309030905040c120f06030302030a0809 78
    0x10300860800300304001442d06081200f86410700201c1038013882241d076944d11260440c3c203285421903a40d1200004942c00d2a1000d41c014109040800d0a800902c8107401030644120806110580c0c0030300c1c0010400320f5202540d03034000a402c103c01007804502150100c56203031006451aa140a1040c1c003050300319101207401800d5030300000014410541d021441c10354040d402c8070078910b6a411612015110304c44d0728001c031b6040b900000e8100801d4040d08408101002c0f0009581962404640322204401a040301440f200c116140c080f4401d0303502c40c1204003207440a402070381890b18031101070303a030398001a10a1b9104540054000170701d29081010059410056000e081d040c01c00d4814066180c00d201c0400c800c2c4030746800e80419050303015042d181c000d00203240100e5004202d00742500c07500510f410184c0c0040c00c0000d17061545400030103444c100750380e1500822000101c0c1900c501214054000100140c004100b8104420f101e04062a00001e10b030055031041140036800407071020b610304 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 87443822 1250 87442572 87442583
    0x150306050907090509100506011e030e070b0406020d0315050d050304081207020916030905030309030a12140f0417030103110f030106030b270703030e10030216081b0109 74
    0x203080103006501444800000e041c0120103104500302021403685030f841184483c540c5666a40004035607078402c0c1e8100145038441d0b12041d0403074428040040251410000c00a83e80c45481000580f00c40074508580440340c0c035502412400340b04400440103018040c0032500d040c200300c4000b089982d035210290060a110380001d566403031034030050500304544031140c810a408144140c40243c3c403058101903205807180085500708001c448107400030007006030040c1c9540b0000c4100840c0c44000401403000307060f40e4488030680807166250b60180d90541c90304141380415400400c40382601e000f09950014800d40c4443c0010804d014842d40e1a0400d81c000c0e1250589000395090b40d080880203900b400da070650003441050304584489446c2c401c09400c1c00a6880328030b0f40005003101812400c0c183e403da43c400e0b9002144e0fa41030003042040c04200305446442d8540c004034455010b07108036440c09200300d2001d80990310300e03102c41e007094202080b4604140c0008172103101d492020f116100801e40b090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 87445072 1250 87443822 87443831
    0xe0f07120201120902030c01050c0f1507020705030303013807110a05030607081f1703030421080411011205070c120c02011202130f03030306180614040f150306 70
    0xd0000402000e1007020f000516880d0903140009a1000705120241050031f003032007a0b9409107036114a180c03203070700380225006000d83e003442c0411860070100305004a01d258201c1e402030380c490003059101e10080c443e0340d00c001124201c04c80a10b030008410346800888011130b500c00201d00b80d50b842d85a1081000f29001d014503008000545850790010f0090141070b002424175282c003070b101628032000070f45002030340280c001941281040b61202c0c1c00140c80704802805d40d500e82000125030301d400c1603d049464100d2010100c84402011000c90008519035a0300d00994507541c6500c1060400541b80a04002c03148404501c03030b18081c01030034011187c0e0390300c0a600d00140e092020b00c1c56588403088041140503c2c00d4800b50380c0c000400c501891286030300590710111090701202804039a4030000c83d0b0b107a8010004140340d010380c0100211040002c498000c0013a1000c0b20301214014040e00c000c03000c2030300704021142031540c00241c44014000c40015004100c00c4059a00d139201d6200700d0b140b40d03c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 87446322 1250 87445072 87445109
    0xc070803131709030312090c27010b0901020c090c0c070f090b10020601060c030215070c050d03060f180204081212010806130b04060b060f0a02010e061b030703060e07080105040c020a0201120e0f07 86
    0x22701859005100010003582060308880c0001c1d140c00b04110000e03c100c108a0202d0320358140303082103600d240c8060046600603aa503080111240a43d481355074a0989401200a40380c184048203829848455014054681c2003d0040d2a184002042a41144034110701540c00d04010007020f8000c100070345907a5000d05d4a40f80c070030314000804a0030001c060421a0030010007407091001800d407000100f240076072003115030808000740915481940c4a118600c030360411800104018010303c45d00c0c200c6008962b03220213415a44040554111000100002c20349002c541d187d02516003052142c00c002c102010f2401c0058681e401c9034203201d01c0c00720300180d402d40903034091068050810700400034010030300d062141d2030820454282d80304126000000000e44151103544000080c160381b1408140b1424400001080000240182401107281400b00000b04e03000080340411254141c0d11101060140c1c0b01e03032000b0b8840ea1102503031501c22801c900380c5001c41031040d1005007080e5880c92003658007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 87447572 1250 87446322 87446389
    0x2040b0f240d09061413150c050d02031609090506030d03020a0e0d240506060d021303050304180515030c06090307030f060c170408070206030c070803131709030312090c 74
    0x3001b40545070140412841c80c80004da032a012203001c62a00c950000720704540510640340f500c10005000d001ca8400030822003080c10040174075a12819550390223210984030340303051007100c9055414550580c400058048190f00c81e400038580d0302d4061030007440000090004c20b1442c041e1000803100707440d5800d44826001d035800d00c503074480713400024103200ca4204000030a03030520940c040c44c2e02d0241c00180b041010210640031000031a4060700310b9569503038400c1c20100354441c2450460805d4100f4001c544001410385d5a0071058030010003410001c04450100700c0070342d00c40c96116425000e40d660000c046000d41d0980e04000d40a030070040349030003035000d00500346100800151017012030f070000d0001145140056a149680c141c84c025600e0f12200c5402d2480d0203207110041284134000200b24014506e4921b2106162240c951441c8a05501d00c0401d002d0049400c0260143c1c818440010f4100e603070b0000320f030031040c014252540742e145c000c00700314040d001c07041c40082559003124140401a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 87448822 1250 87447572 87447611
    0x9080903030c2a010c0f060603080a0f031401050105090d02030f0d0203070203071707090c050d02030108030a1106071d1f0f02060105060415030218041802040b0f240d0906 75
    0x1ea003c02450101c4480010f40440d054840c00340800124000c030388104060b45e0300010184d0f0300400340c00e8666284c1304004007410740c54000d044c00a8100508250100c3c0800050350507680e050715050306000d13916061001d10b620f0303e4004d0f03906215442c180d8024000510810244002c40d07400303141c2c0c3c0e517202d0040c54607181d810b50241852610103258465811004185801618401031000c1015000440c04507254050080c0320910030344000000500300d00008020122500591145d0034040080d03403d050b122030301200c141010650012105404082822111060050003008030070f41c078110751034540019140060200202c0d0300c2000c0720401c2a010055980149001c4941926280c10306041645840818841c0720a0640200314184024503080d410000543d0141040204a00382018041820380100d003da0181d450520292541c0c1480800800310007405004540201441c548007240c0041c40441d03400e450304280078080d03039a00340f8000c0e44021400382e20f0214204090522040c1c4a9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 87450072 1250 87448822 87448873
    0x9090d0e06090a050913120c0302160b0d020c010207050312061206040809040c17090318010c0804030f020a030f061506110c100e0415140118030609080903030c 70
    0x148010b002c2d16015030760f840400025035405460703a1802e912581401c5c01c5071191004028601d1904c0a202a03040d5404900c4003e040e0182c0d007120301140c0e920b8003a40320828240680d01e501c4000700702e8000240801e800030714001c1c1400000600d030100720380f6054119000034005028040c40c107814000545010807001c0c10510300c840151006007031566604d051072240e6142c2d42d01039a140d040a040c410f0181c0c02080c540c140d5000c608682d81f03072010b04140c0304e6001032102c0710f80d68182c0d80c1c01409544106039910180d6404500c0518050850300c0c3c04003800e0840d54200da21080380d41000c00050b004480d8806030a02c0303004040356580c008009105020340b107030810b03004c2111341e05101401000000b1066101c0b101035500712001c5800034000c131440003000e000b0b03030340150034007102088845c10305068404407a0142084010300413488011603204c2c0143e809100c1c1c2c880320100034004502207510040c2140d02c01c42c2c01510700f45c800e0010908540282d41c070240107070000c6810341488240b090651051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 87451322 1250 87450072 87450079
    0x3040e010e0702010c080903030112061407030506040507020703080301090509120d0603120c0209060d0203010e010c080402030d0c0305031503031b0c010206070e0d032304030f052103011401030b09090d0e 89
    0x521f030240740a540d0340414415815084900d10b0510b080c004594003607143d2014030421030380c2a142104014028020641d0218000c4d441d2500203008248081809010360741c0c0001070314690303480c1003818006494080d25007586402115000c10b6424038060081090b286111404038000d461814807500400c10445c41c0b10620032002c0d0103000594410002d82c3d409082182c4848100d09240042030040c61100c16182e215842c0131403111101c0c0e000076100e44640e10840c10ac1e80d18091108040b5010038032140000d02084041c404192080c1c14800b9804908d0406000c0300c1c203141041c10a120000c46120b4404420b03009903000b05502d5074140155030b4400b0950a140f000701c2e00c800c002c1080000205000b604000c240442c159085d201d51071b80d000c07617425000005440c0d580700e04080725120544c2404890030702c207513002940e0307418441c2c24564884180c0614142907a00c0e0501c824030300e881d248101d40c101039403031071000c031543d403641c40480c011054000104521021140050305020404860500c0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 87452572 1250 87451322 87451337
    0x23070908100b090a020a0903151413111201090507062f0304120201090515030106020f0c010e040b1c1101020106091526030a020a03031407020a08090303040e010e0702010c 75
    0xb855110784002c6a009050020700594030300300c203c421100040036030001000c40e4540420382100c20505c0d0081c190b9110880e800902c16229500300d600c00d01c1006000400321411491a44060300e01a4203062414410b400041040001c1340e980c0d0f03080c000e00d6041038000c0f40c030b13032142d145652040d428209582d00302a6511040c01c050305000c41e030b49006a208480d15018485904030469100d0707842070008280140c1a0001c28480c02c45084a9030424003a07903005100d9000c614035404000100084c01313a41c183c4170540080d42280031700015080301076007540c2000ca812000c21114814590f210050b0b030080f0f4440f00b111070034070b000909403060355102e6100903007000d14641821002c010719108441e00340f803080000803100e400181d400e03d89410103181500000c02c1040d4042e03000309540e00598031a03038080000341074458040501c49000d46411006034030103250b00000075101d0004100707100008085a00307040d0b58006c4401990401d802200004070f1050912070942c0d024001d203e01c8948900f440308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 87453822 1250 87452572 87452591
    0x60c0c05060a0c05090303041203020c0d0312050705160b0108010e07061409040b0d08090414010b0a031a03190b06060403200a030b04050105040b15030c042307090810 73
    0x159504406040c40c00e0b4541d9861010541d240104200d44d00244050252500c855440724030700b10307010850100b6000340c0600c0010306d4440c9440354884900304e038144c8034001403e0419803464000c0000400e1034082c0901005803102d2100da8148441c4102c1c42030340d1614540d8140301081382502e010760711400c0b20341e010302000d210031b91700a07a40d942d50110070f00384030340c42d40c81c65000200949203034440942c000851003d43c0043c00520002010360040942d4180144a84000b031032114043c244652068400180302e4801800c0c0b003504041c040c00280b4071001d0410140c080080d003009000400383c0c604c0c20750071041d1010040b0034000300d40e21043c1180c0d020308051851f16030803220014404003850046003910004101da60314007004004c0c40d08010044100e10781440d107103000f0101030318181c451210180000341001008030340340d40308400c00f40140440103111070602c40a030051151800b40300745507418049558036103c0c500c500c54402d6075614004c1510b4082e405084c603483e9810000b0f401d05021050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 87455072 1250 87453822 87453833
    0x20106080a0b090a0c12140a150510030605090f0105010b1201060f05040305070b04140301060b0a0c080714070e0c03010302030a2301050a020a030f0207050601050603041b030807060c0c 81
    0x1c02a040924622035942e9000c290b42031000220000b020000c00380c1d0040b5840c251001d81c115000e200706480307104071040c4504150f40b04d813040402030049008400104451403c1d40003d60840a00f5007040d02e5207407255145015124102d901d01902e51010400881040e024004d4500420b2070418061509228000e51807405805000d6001444007212110013801c2c490401c5030300860300082030398002d5485614841d400d80c40b62055100e003045000180380780303241c1845600100c8950042407803501c000410183d03091000034000f91401d82061000d50040b8211034540350482d01c4000c09051507604120500e1b0700c001c4007034943c00484405100501c0161070001d40410080d4112100761000c000c800146501058008004451942044203105600242c2d401600e08a403683d18288400112586480d007203000c0e2010242a941c0003200410260400c6001940c0003401200080c40c02d584214a0224507000c5034411506180001380c0d1030184111031140442ca160305107480b0740c0466030750720f50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 87456322 1250 87455072 87455083
    0x60e0c0702040c02030c01020a050417060603060f0604020c030c1c081302010507110d0606051c05031801140f070b0f04331a040608010506090106030c090b0d09020a0602010608 77
    0xc2c01940d403030b4411149540200255841000c2107402175640341d1881400500f160060710801001302d40c01044004e6060010409074404c2c0006401840310790b803035094400020b14090002134020754200909000301009000810150700300e08010400007507031042449140c1c080070101010081c106042c0a140b20900a40c2e400454091070040e8032140b071818015184400d654500307034040135840c444400c00407290070560440c0c40488014580c0725201038080c0580361041c0b030041803900100800d112a00410400d100080b0040c036000c5110450b59981d0b20440c0c1c002400d20701d00c00d10205140f0b0070041c3d9011416413019010840561505040d55000c06001c100c1e40a100e07030100d225603c00342010040900800c1c5114400d041c01012220f1402c0200d803040300150074084c0c0d0600d040441c1441050064a0080c040034080d1000c0c0c7c1c0c80c02c02c084000303116400071a81004042980000c08030464400307003540910784140001c100c203035481000000da446521610a69041c42c2c820003000b03002090 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 87457572 1250 87456322 87456337
    0x60a09030c12120204120312150509040c0e010f1401051e0d0b090115020606040b100c030c062c060403020c0f060d050106020616080f060d031b080a03060e0c 69
    0x620800750a907040143c441d4541041d40d515590b1001c030b400151000d0143c40301940c24000c1d11200f4000c0c100031402d90556412400121410223012000c01c4a402c0c4103d203c0c1cbc1c000e00802e001840152031314880c0d80c4294082c0d00004030580c04003000d01002e0000800800b141a003401c065180610420b0000304881e4070341d014280c07141003c50b81590000980d0030081d075440300100200010740e181c42003102001c2d4990080341c010310903c0c0000c0c25a051503c00ca00280d0740080c00c0450301c14030038404450300c0e20307800e00880801802149184c0000d10b00e000b0f401c6d420340c03102010951491a050320890410700211080e5243d0711034414040820b0700070074601c80100c400d4484520f00403000000c14000e01c104601500081c1c0f60900000b0b2255020900902500e2040107141c40045072910440b028401907030841048801c1c10046112898556007a4030a944241880098400c2507521451001903641d4152030580000408115440d8103110f150041d01da10084031029040101c503580640c0502e20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 87458822 1250 87457572 87457583
    0xb0403120807020102090a0305030307032702040507120504030305152211070c0b04030215070c051c0605040b040b0106020111030105040c020a0803010f0e06150304060510180e060a09030c 82
    0xc08140483d2007034045500421014144164061741d0b03107000c0d66694021181100041c2c90001c07101c000d0002c0e900c481c90700d8040e50701d162891103050380802000703250284c0030701c00340090149c0400c0340c01c2c070301c1c00b480384030b940203840000701450301c030302428036240a01c2d0707030f41c1d11510080341d0310140701e09034030007180901002d08800500140034141a0800e8441d5400c040c0040003005800206090710314002c0c4166803003a20324160410564a2105450096031802409982500001e1083e4100500b40d0030a152103018070781d8035110261540c43c11204250340176980100107004202c01e2024a6809a004181c00d2008110f212254403d0007210f00041c000d445c0305686600c42e4541c11442044030742a65a00180b1640d03895954024082c1511464840c891414281c0c00005030300303140040c49908891910b4400d03500d169180d035601070040c0303001001101c03611298440440c05c01220001499070900140002507101c000c41c030100e18192004002d200402d003417010023000207900c1740302c01081c1903200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 87460072 1250 87458822 87458837
    0xd0e0108060607110a05121f0b091311040518010b0303040501090b0c0708031317010203040b01050103020d060b0f07050c030d0903330f0509070509011205010b280b040312 75
    0x7000010030b00e00c02c0746d010541c008a5551000402c0b607000c9070f4603036004003003640c26103040d4003992400c05558141c2c0c207050b03000d50420300080c0c2d86802c0072900009144110360300000d072a41c0c10700081c22101c00303494540c494070290b404100030110034404c0e40490356040f4000c50615140c0000284aa81503024980d01e455001c541d00200040401400014000000035203495011141000741008414400c505140410410401c1402e40c10302c2243d0050350800c0069019030300b414010740195201c500c0001207545e40d18400180f09a040f0b000c0c1c480c109064000a40d1035000d4103040f03103032075034211485200e6084040c0c448101900031804000b100c0d486003807825580501443e01d6400810400480c0f10000d00550100401c4455480095030280c0d1800c100f0143d212184503c0d565a90780c00351603046240c10f4010300a185440a004550520900001c03904000041c040fa9890a5141000440801e51410a0075001510240001a0580781c0806003018036544942510302d000425000610100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 87461322 1250 87460072 87460103
    0x60609011101020a0215070906020c0906030a1a0711030f04030605180d1e21020f041a030402120f0307080307032d0501050a0803040b0a03090b090d0e0108060607 71
    0x41c039507500c2100d5141e0000c42d2100c1c451403010352280f04400104440c681d12200003640d01c5d01510b66030003500c88a50090100442100c02d0140503800503000603418420400036200185000d2400074442d180c8174003048546c1801440a043c2140c450000c0c0e495030414420703084204070301c0d0165021030390014004207c80c0c950082d94031030f600540710000345501585030804d68141d04501c039030040301e41c0d02c0040c0807a500d40000c100e07034114098040d03221807034542180b000c08400603000340c00d200555410300743c500741c1e4900400300804024503105e0000c41d4088100015441c200c0c43c03100280d03803d0380150440c040c800d040b640e00e921811000419030007004c00891900c610035805440d01d6148075902c400150344112850030783c00705002d04200c08908003800401d00707040c0020b03403c0c2110b401c80021400d00c0d0500444800540041e0811010907507220054000b0440c180000c0c0e01503500303040500500b00d0700d500700030103040c88030a0382130500c8420000e014081c0c56400850301d4003034110320344a2483c5003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 87462572 1250 87461322 87461327
    0x10c020907140403050703020306161b0c0801020c010618050108150c1e03041104060b07081e03180606060f0d0506030a060f06140a0b030c0c0a0f08031e040b06060901 73
    0xc1c421120442d58102050120421100003800070541c1e0085003201c56030b548814684006030000c00c490740000354100102030411080007038101c0e08610488040c0e044640f2040302c90300b2a0800160441c1e169164a41000b003040d2a0072004080c04040c1c00501c450b604041269660b182c9119614100d1080e130300020789a4640740f815207440541d40742c2205804000c0c0c110804581d00140e07000c0d00d0302e021a0300c03d01d00c0380c0b6192243c101210b03100308030141004c0c03503501c66580c1500308070417102042d81601215410150001d00440c443c90691354048801e814460009144c007a0050016000b0341040042c5c485a03845030040c0c80b0720003000800170440380e68001c04641081405400140200e080c0f4000710b440001ca90800c80c181ca600c2241e142003a0703e02070821a903503d140c42131031000042040414000d070100704c02040c061540e00c040725060103259071403000e4510485800e82d11550048140700b543e94484141107005000c2e2062905039080c65150f80c2c4128038041c1156106000019648070702d80d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 87463822 1250 87462572 87462587
    0x240620010609050c04090b040b100c0f051501030b090606030309040c030b1003020d0b06090d06150b0a031407020f070e06180c070203060601020f1903090504050712051302010c020907 80
    0x701802c040c40349003010f0300d0058080d041400786c20700c00c60070036410300d40a080500c02c2803400c00700201004074240d60309105484084810310305660030b40b080c40c00d140c0864010010092100c40d52170340c03200e20790700d941494861414081c0c0364500301d40050301407294541d40081501c181f00c20858000500d050760304400d07401031451080e075542040c0c2080c061122190180d010f0300044103510401d000f0030358243d042040e540719000c5000d5102c001c801d492008124240d2008112500c1c0454071182541c0701c60500c82c0f00d402043c0c8c40e100180d180c48209901840080e200342d04600a40000c113807070184101801e03101d480f41c0c003600301c1c14144400000d180d543c40218441e04c525050a0f03000807130a004081d003440c2d1b405a00d042c0c2c040d2283d50003080f965440003852400c03501028020300203407942010303050740c100f2146005504019005001040703d07940c52145038080e140c01e03141c642138200b4501c1c80c0401d07100300920010b07011907a04d160001507600030640c000380d0b56044403c2a2950b5402c201500c020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 87465072 1250 87463822 87463829
    0xf06011a0901050d0f0501140a0807180204030209040501020a031a030a02010c170a030e0705010504050d060209010c0605150406050a08030d021315050309060109180803090a05030d2406200106 84
    0x10743c2031115000031701c651340d03001c03c4c1a47d00c0795007020026541d60b81406007040d094420401c480d0702c0880d0401084078040302d000202608040f02601e019a2034001a580140655040c0da40765400940c1c035108640600c181c060400708060320031004415640029102d00307000101074140708002c0c100c03004016040001c0c5100007954001c41e03860741e5031004028028050060100e02900c2512404511580038005840484000510f140c07803040003980c40d40c003e500322002d554107100c90b4484d40c00004440c0e016940c4a0840c9000c03182c10070031030300304200607115141e026078010807101c0381c05d1100260201c121447d90b552020056034444000f00d00140503041680700150001c0c20303012086d0100e5204004502622107801140c1280e622416000c044075403994030b240360700c0c24001304a000602d0b5030003d135510120100950f10180126150b20341968003481c0030b851b05580d20f4441c2c2080d078180c109080c0031140c0c040b0240401905007000a401c000d82c91903100d20303500e1041d0f90365246980035007110014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 87466322 1250 87465072 87465097
    0x801060e04180201120b0406062303010f050d05010e01060902031f140118031401050907090510090b06070b09032502031509030409020a0203030a0605040903090b22080f0f06011a090105 81
    0x45070365509e00604030340d4640035900042504030004c110b280c01c528240d03416210302d5803201010a141c03d04101501662a004444a540703c07440313098601c00070f101d8203004080140000d071740c074580000030301744080c465402e034600740d600702105210055070702c1c0780c410f600402070034814140090003040310005255a0f100828110703070340030614040907040d08001d006003a170000300c030142ca0b1101e20001c162142102c5044c2c1c80ca100550070001518181c20408130144040c2141d4580045034a8000781341c01c5c01c0302c3c49070070303a80000f80503c207a141e025441d0000b05040841207020f4a5154002502c03603658020105000b00c9483c04118400c40500484004040b800760865071a41c0700140a9201d400c110740c0158904e10f403081c0002d075420280602500c042d810b03500d0342e10310b5081224009440d007100d400e100c03089601c0624031254101484200e80600003890081c041c00c0304031107074580b42c0450701d600c80041d0b4004400401c1641c006c4038591481545020303000391146060001280d950017035040c041d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 87467572 1250 87466322 87466331
    0x206030405240103080712030b10020a17070b0f0a02040b130f0e0f0f1008070305070f0b120c07030302070210081b0a050a140403120801060e04180201120b04 69
    0x400500045104108880311002c03a00002c0c02d507041201202d09110103040c44c1401c0140d48002050001003150840302c03410005200c90392100482d2084d80b083d5050405607104014410030300c1400700281448001d240921850410f00b42d03591098400050142c00030b182441010504840ca40d0301600e01074405900e40d01d85403518030418100d480f440707205e000704800703030700001044400d15121154405c072546121030b10300d40c4459007419a0114001e200250610748044040354210043c8950001140140010501c040c11715550a285c07942d90341c0035401d0303940c0070840c0c0944206a1404658000390404040b030710b620725410250302920403560b0080d4407164440c1d07110410f5812a0415001f0440b51000180300e80f00031894482e94440c0c08840404681c0900c403e6208901c41c8004007402200008180e0604c0e54903620070100498545088010030300b100c0c010300265900c41000400c3c01011234040c440300000e040d0141e00c00d2041d00c0003034100710416101c0c0d805ca030742a800203421190090401c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 87468822 1250 87467572 87467581
    0x50c1c020904090b070504140a060f0806040902030f030403060b120c06070501090807060606030c030b01021e07030c0305030306120d05161b0305010501090f140609100f0b04050112050412110703020603 88
    0x1801b990181c0900b000c0000c0400e440281400c000c4080e0056407855140d503000e01e084c40c902561a00c038014a003039441a162600480180c4080c0143e4090700000c0f401542c1791400d520b071200c103a80100d46824002e150350000f00425504c0041e2000b00c100c400c4e6403a564410043c00c049001d806100e4014001010005900080000551198080311800e070343c10005030440b00001c8098410130402140140d0013140340801d8070101d2501c008d14042c0ca001201c10040e034a507503420800c0c10642c029500380d00017008011042c200b418407e030707468010f03602601a41101e50300c06080c074019170701c1c12070408412002941c05c02c404d5420740340007a074080700410030041c1d0301d01d0700a021f00400d0140015050800f01d45840a01c01030003114032450f007000040c4800d42ea4001803100b40d44008222402c00f003040000010300c03414000030b907400381c8400104640e8a40c01c0c034001518014500c00400c4401d450541000082907200348400113040c058500800c21804004940f441d02e402604003940c406000400d20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 87470072 1250 87468822 87468827
    0xd0914070f0303030b010509010c08030c0c060405060105032e050c09040f0507120605090c25050c09010b03071b21021b0604031721010315050c1c020904090b07 70
    0x100c02c036446503030103200d00e60700c24004440c240210000b440c04142102030440c00202504c3c040c40d40004117080032420001d400f241940780100a0313401b520290440001400030341024824031a90380303640b01c0001d500859a12450302400d914080c414004d82d0b071a0049500240b0740411181c1c1094010400d0180c280a806282c0051001790707042004100e03005801d0b4144a4503001d01e00840e0402072005040c0d58817010b200c104c940c0101d07a80405003041035005040b106200d81e00300c2200c0c0c0200002c1603021070a000f4420f18020681040c44200c50600410103115404105415030b4040c2004440806e0407500e023050140500c1500b00c441071071200b480980c019030005150420862104c0d030240480050003d000c86031141d8040a04000e40c1072a400030800e4000707000306250200310500c940510070b048460300c40030380c00b0b8004480152000708450004152030007082d400190040120785001582d910307400e40c20002c1c0403a100c0140d00844e81c1d1883da40d4582c446180c0710b4011104021910380403100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 87471322 1250 87470072 87470099
    0x6021e07151107050102010506010c0f0f0c0312031113030f050705030102040915090207020306270118030e010215011401020708120a020d030b01050f03040203030702030a060b0111010509030d091407 87
    0xb511103d11824000203200d41c81405518080c2206845c1c620001e41c46da15049201000f51034241c921413568254040090103c10654000710300400503600c02e00303a8580003d0555290711000041d40c01c0038801c1941c0c104421040c0f20449a000b100a480d02c50180350042c10120307141d2140358154404a80007514800c2504203c0d070900e04801f800b85440c1c2c50b141030760124056001c0c0a5010350000300011892105041c0300400003607403141c0c04001e0445001d501d03094174809440da40d082c4204101c00010181c000c400b00b45216000d00180009060541103c2840001445201440e6901c1034044c14664001d1215070054034140041e1038060622010b40841a0320a501c0e4200601c60202c01140140c030030301c54950010350581d2060710700b072507012104559400140c41682c0c58017003000b805006175810030408074642c0c404d05000c035003070410720000f400320381c9108003043c03442c3d040c40d0801504031408011103000003100580015103070150b0410941050310900e501d031081c406c211001c40c9942c41b0241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 87472572 1250 87471322 87471347
    0x40f150e01060503120307200313030b0105040506090a0506010c06060321050c0606101103120703050a060303020601150306080a0312050a11030a0b060d0903030605041506021e0715 79
    0xc2c4141c03030751003091560350402e01c0080e50000d5014808110308501c00d4a1108ea19207889500c48050f00c20002040c1c15917010119030140f03424810b000b00204900040b04a0040100302c0c0d04100034504440401d044000c010102e031000c50740c50000654580c05461496030080d04018108045a181d24002040501111200300154445107034084424842c80031182c130081c5041c050702d1240c403446d0901c1100c5d00d004082100b40300460120a200d0300041000d40009800269490b026040c440d6006e0201da8000e01540045c5051000620110781c00117121411035203904010340b07002c190304008500030129900501014061400120141a8802007007440410001340c200402c1d1030340ca03e5842110b000f0300190307914203824000200001e02a0b40800c0da2210090074051a1240e0002d5147c1201c020000480c0401d03600c4000780042d08103403085000200c02c01d80d004d807d680c2010000380d650340394001c088000131858213689070b030a681071213400b00034089030a02c1807080d1030160010300200320285 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 87473822 1250 87472572 87472601
    0x10803161b0e040c081614010507062a0e06090603060402040b0f040e060a03120509030a1b0f050a0303090e0901180f03031808040b0a0203160503041d01060503010905040f15 76
    0x7500420304000124040640e06c4002458151403440d1071840441c42030780c096030606002d014400300001c0b42150040f82006c42002c05540c440058002d0900c05000c101c2c80e4079401c220303c22404c0c200c02e8960504503070308001c045424a84950791080003d002c0d20964122a803005004501010005100381c09032080e01d0b0307454002e220503a52501404003038101c5200c00341011b04000c0d0b80c65000c030302a0f40105034260b03000c1c2c162a14003c0039103c601040440314003612007610707841410841c142055003000090402194100c0c4098034544000b807107050540241900d00844401240414000354400121141085180c0f003071140c1c1420b10341c00d1040705500503030102e401e282c0078030484141e1002240582d03074801d034454105820142c420f40360f0b400c890042c0c0103520007000b41014030540444902d1015200d00000e568860800403441d22080e00407101d0000e146041d0014054070b83c1003403e0380e0540380110400074450791241405542c451210402034218000707003111203458082901304194002c0000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 87475072 1250 87473822 87473843
    0xd0e01060f0b0304020319030302070606031101090512060601031d0a0524070807030b01020f061015140301140d060203101e050607060902010e031207030e0405010803161b0e04 77
    0x4500a02c45403108580003035051b0030180b50b00312594500c40301c0400150207845d0040c00c1c418150341c2d00b01110801d0700256103489001002450303660b13000f5000d06c061720054420b40002240070412954892010380040d0515454480c400c00b15426038100803c1c02d031a04085401c80083c03410410780350300e5502c0c000305101c15403400a202c48150440d2480c0229070720396800f486a6180c0034100c0042190100701c90450003007441024050b07000b0088180106080d4844103e00c86ca407460b07100740200040001410702c00015404504069050140d81c1103400031000b44036a0000c020000d403590207940710050907140b0210074131202080280e594001c1d0340911103041d42e85403441c0c9100091a010340b04170380e4400402c000180000300a0340064040c984103040c110000f12139200004e040804541c0c011586031303000700b00c4100b85940306008001400b4255030810055050004c9a6280c0c4200d02da219491140c4940c0401081500c01c0d401e019496110114002141c8078000300ca00071505460039101c40256 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 87476322 1250 87475072 87475079
    0x3020913060302011b0c121a070e0d120306090c08090c01030e0c1207030b07180504060e070507031103030903120108030301060903021e0405130303050f04020105030c09060d0e01060f 80
    0xa120304820b80b50161200c80f500d2210444103140c0040381c040840d10401d802c0c10005054811110301c0341100d114030400d48011010780b180340c0f0f0f40140100000c04001c0782c4c5060141940340c13080b1540e0303242d8100c644195054480682500940704c40e40c4090402440c00c1c01e9102d01a520503001405001007109481d0140d2040300118280c584000380e04a242d0030210407150755142a041c02c09400b85000706403000301d560b0381c4858034101c00c101c8801d03000c1100c00992105141d00c07046048003a00044404200f00c41c213000ba851100c130402001141840b0340014480c0600d80204400f1480c942c2075400c9a540745440c1141d661a60800030321044120341980c004240c01802000b03881c107940362556050019032450302045861034507100341038140c0d2181030f4041c4c100c3e10380d40150f52048030a510f801d6a40300691500030203e6000904c2c00030300f404554144001030317902500302c98020000c0809a912600305800141c0305111b513802d41207a10307180c010502ca21038419004482111110010161103d55 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 87477572 1250 87476322 87476359
    0x10f0807080c0901170f01052106070521070504080f030f0702060a090b03040b040b0609090607030e010e0703060507021c0509010311040308070b0402030706030c0507020f1f030209 79
    0x60035511500400d265030000b410350041d600142079000c10514201048501107680c60022240560f01c585010040000500c00d41c185500b0541003092445c0211440d0150b083d480307500da4001070803803401c0000008022640607440950394cc003400300c10440c0c40c000e040145002c1c10a0307105201d81d0718240112a0010104c20780403081c2e580d80d0b90038041c503c0c82c0909507400c005c1d1030780c002902803040c400d40c00d001090b10090701002e1b51140f8811082c81c010b90515081000038600c008001ea4402e060701030800c611440c011901a400c031b1110b04021038481c40c418112409044100282c5102d0302c41c5102c00000e0000741e400580c010b85140d020354030044c0b814145190101612032400c0080345040182c0390031548240d001c08001e1903140005030401d5185c2d0b85010450303205000640d40b15a00c0000d00040d0b103021300c00e41004003400d040030805146c0700003015009008104000e4800d4800480c042c202c0c0d11140f0080d1010140c9590203c0c080070700c140c0103002504400011401803d04c0c8618580340078 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 87478822 1250 87477572 87477587
    0x30618060709030b011e1d0601090b071a150301020f070c050108010e0c071a090a0303050c13091817120606030c031f2601050604060b1605030f0315010f 67
    0x2500302d000014140c3c00c00481c80c100f40c1704224038180d10416071600041c03900004405100403a507c00111340c040c03c1c800001040c54800f03800180310b0503010452007000803c400300c00038407010540a45401175803090903864002107400019078141d40000f604440c07007408040182042031241d13041c00101380e00c6400440e4030110034040c980000c509540400c51000c1d9540192001c0e03440f50342c0100c440c43c40301c404007240410945420807650f2190030385500300358041c0240b59000c01c0c050f201c0340c102000c51209001c010300780d21517048081e1b540c12420944142c1784071010324440c1c115400c41202410282601460380c01a2140c0c2382e5401504049038113031034a201181d0064020350000c900f0b54983e0400518882504140030245450310400010300b002c0b007082c004048400e01d0001004a113407421000e096840040480788107a03e84041845207e07a40002d80320002103065800d141444d140c50410728610861104d400310307101c040200f000c400e09040b150802500c00307985a02e0150099801540c001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 87480072 1250 87478822 87478829
    0x40f0302091f0302090c0403051c0807030b090c0708090931030c060506120a0302010614030c060a03090503040909062a0c02041e060806010501030c020f03090d03030605030618060709 80
    0x1410b001c0c01000545042007640b600001d0980106241aa5995440b4601380030001d101c03180d00f000d01e04075090650044407040d0301ca40300b13040034401d44820310b0010350030040007030907407018480220f051341c1030140c00000e41e80000d1000d0b040c02d20a0402c40d4a040200030075159078901030481d124015450304400c075000680c664103440d004500c407987d0f039611001d050010300140c0c1101d410503c0000c2c00d0402c0000d8503980b8000e4000145250404204044100101401600981c000f9480e05507035101c2c00308448070701c1d20034600092569040e240c0141944a00c2d030100e103c0d01d041110f0b000c24800141e00c8406684204406001580c4c1c178014000c240f1035182440c0d50104100743c0006025040a030040d80340050000b440e11003206e200d4001d030044401a40101c0c03404d500580050055507058030030580b8968030750004011005c03200201540d81c5c41181c0e803290107004204400f008050017a0009d001070040101030300c0d42d030303e4081e1142414448d40111903c02d8421240440e041c1409401144d00761b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 87481322 1250 87480072 87480121
    0x130204061205071a1204060f0501080115150212030403110c0103090213090303110708030417032710020a1101150f0303030b12030c15010f230103090602040f030209 72
    0x30700e032a200c02d944c4020070324100014498000c001030000214041e48691045104000005154012840805c100e44058002c80d0841e89400919440c0d280e0001c032100894003030100803002203625002c224207114981144650314440802800304040d08085110b031017110800488940d28681c000450594940000103500841050520840110303d900701303028050007810f010804405900415459a000e041c0c140c51044010050008100c1f00005043c550004940390a0450408a05290031194203080d641040010340b216040c21007014090003c8003594403408540350301840da00075280361621b0710303002103d52815480712030440c41c071781d01503081d030314180c59082c1d00d10b003180d40c25001407040103401a400600105090f01d0541c00304010315060f06060047c20340b41d1020180d91998040680009281c1c10801c103050100d080c82e000c10303000d9901c600700fa5a070080301c4840164018802c40070047c0c1241d00006001c10004610a607900c02c0324800d4a00d80000c1c0e407914428a810780c0b940014121 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 87482572 1250 87481322 87481333
    0x18070210050112030e0f061b0709020301061b1406040f140706090603110919150c0503070209041406010e070e1903081308030c0706170405061b040905130204061205 72
    0x20030301c12401d003405c04001a20096001581b803000400b00d821007030120f01ca1001314004c040078810240203800c000d0804503410350071541420405000006a88800d40500d0100b18001d8180b08440c4040100c596070784040d1151414181001d400d42d9128540c1a40c1001c00101c04020701c450004d81c110880c0d00613610000c0c1241891400c80180a040311468802c02042c0407110103513a07010b4000010380019003400030b8591030110b00382100c00200c0c3c02c01c02401918626034011880102c2290b41040d41100c80c5140c5655528003520030300000b01c490605849039400202c0e8040341c485d20580101c1d500e4a510036124869070800559000c407815440c00558034110070000604004040e1503c00b0001862807000d80e00d4155141ca0760b000805022501e921141007040401d07004a452a002c141801307540c5000c1c6481e40320f5039038428002d400c0b920a4004200300142d41c3c7c400600340c402900c17075080280000d007021a0710100c5403410b841300381e00c40d0380342c00c0d0000780d5a0070311828040c036103034400003624 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 87483822 1250 87482572 87482609
    0x6091302090103080a05091c05010e060112060b130930142b05190209031f1b0201050414010608190302011815050a0608030405060702030309180702100501 68
    0x13500e60080d2000c001405800d100c031040300d5a45d0003586100d1004c114604540600720700305582519001e1410365166041480144905401547c0710a0441d400500200360001c0036404602c051581920b41144a40f030401c4030b0080044506654005002104040584910350310400c141c407020310490001140d104030700c00000c64840e8019040840722020300c0300f05400441100e000900c03032007010b24a503a43c2d44040102000c0030310340d8000c0c03114050601b14141068540800d81d5012021005a2000c0200d41b440e807480c00c642d081040001d211103401011b540640c40040d020703203001d940490f0001400d491424036502e0500c00c0000b2241124002c040a0001442000c66020b00780010307002c5548441e070b00b0319800400b450440103280301d041c0c040d83c034aa12020341c80488401a001001c042c1c03c0c8102005082c2000065800340c410031601c1a68034103191002034510711500340e00d29041074201e9181c92410300c00c51082c611941c1b403a000c0c2d481c0c01c2c05180140c806c0f0f039403d019a862101c004201c08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 87485072 1250 87483822 87483833
    0x7050a0f0e03010b06030f040501050a05041703060301090c170c06090904030c1b0f15170105010e01030b0d03050901120209030703030c031709030a0207080c0a09090f15020306091302090103 83
    0xa40c1c40302405000010b2807400c01003c11070a6104480003079220445606000c1001b109108140e44210200000c10650500d07540713104800301660744280c4100404004100141c2d000c1d0700102840d548017401c21111a5502000d220907044101400700310b004101c80c100e07280c10200211950003600400300e450680d00da640680340d805c880042900c442c60b5080c2c83c000860807103001407010701240d4840370141850818180308079080c1d42d0190040258180c00b90f4a821042800241958824240b00c00c010314034600480040c01c042c200030b540075180300c4107d0103050b040320007000c0c250801c3e41c4540b280c00100c2c6120060744500c58443d0f406600c080c07010000320780304284002c4214071034584117810304035185412501c0002a148880b42c0d80001820028003501049060b004011000151032640e105200041d0701c140144601041c040d10b605100c030070808400a0743c800380b076106803030312150f82c6084501c0c0c009400444507140508004ea01103440b08605140c95403003154002c100100d16030a65450 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 87486322 1250 87485072 87485087
    0xf030a05090307050f100c11060115020c03070306090b060a0b0f030c090603100510110718150e220818010203041205060a05010608070c0f020a0e0106080f07050a0f 72
    0x3080c85400b0501030b04001480600c2075807480c038108002044c1c1d41010340d07070302022103c0014449060024484038601000c07004030b15a0704460071811400c841002400003079080000200034980d15000790321020080000c240c0c0900300190190710901d1041d0303248802c1c410b495025018013950309005000c14810380020300015680041031100302410720b13240c21b01041c01c07504155040400020707603280a0002c1d040005540c6468145032030a0703a180c0c0c201a001d1a03c03004140a00503903001641c0c0300d03c00700e20403604000111021403402c4491aa640c03a43c0c0e046880003902d441040b010741c40c7d5003000c03142480c01e0100565800c0080545080141c05810304140b1200c51002d055010a010006001480d1110f51400703034059030184c0920328043c0c002008840058115600380f001c0a0140100180d10901d04409180d1201542c0c1454295000149030044150300003090103401c14000305845502c041e02034020791030301c0103600c21a150101d0696040c0200c0e40341c0c10000d8207024071285010310401d034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 87487572 1250 87486322 87486331
    0x120403140a2d08030a0902130203072304080708030301090b031b040c0c06050c12090102030403020c090408130f08011a010e15070507030609140a02010c0204020a122904020f030a05 79
    0x30b94804591440d954150280c0046500604140d80c400031542507041c0b01200c110860340342c00c011440c504d0325410103820307150803642500d8088107000d500500404280b08440280c1404422584100c0e41c60007015500d038001d00a0003699401c103000c043e01410f001a00d003030121400d1a6141a01c0660014000200080425182009624209480411840d10441d400f0b881d182c980560342d24000b480d030001e80e0354081c3c04443c0c584e2040003000301007a404600100d03030360012940074210391141d0504400600030162050358103030318154005004d80400d072541c402c80340004000e101e80c0459103a00070b480050003a00d2804101480d848244510300100d103902c02c9043d03c082c25080c0a4661602880c00308141c004444440d51420301100388800072040c1e031048000007009110100169000170302d01002014000c0c043d0b40c011030032401e194050b00000e41c0103007039034404000241058042140d0301c04c0e00c241d00300c0e09001140560203d0305050084a8101c0c114200a81c907548500c03050600a000051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 87488822 1250 87487572 87487643
    0x5030703110d02120d0905060405060706051801020307030501050a0b0315040e25030b1006020703080a0c1212110a0203041404150603020405031b0d02040f060503120403140a 76
    0x2240400503602c80b09210343e101c1c0c84c00000e105003005800041d114803c0d94101c00d1054806000c20041a6581d004540225620540100b990345070911a034115680c844203869095001000700043d00380c0c19400103040b00c10459040950655450484101c0d10050b0392401c001001c0440303640c1c00d41443e401c07500d60400f405003255010b81c40c1c0c0e05020b8a2100f58440c2c2200c4250290003082400600d030a42900007000a00c034903007a61034000040d540c1c928900c0010300d981004140d00054038010020302c1d502075044040d01c41002d8210800610124114070505001072401c0c4007981c1088118081d588030744c501d50000e40c5020709080c40707101b42e40d103031018542e4442c1d241c0c10f0059139544001e81a0f00144815240581c5550038101090f0515090740b41c414400082079034008103030b1380d0380038501c200e154042d1000100b42c5d4400c41c003400580200e402081e018451500c15089040442c4021301c02c4a004583c642c0031005136071100d40d11545410005090324582e440c0510410781c04182c41c001e45410305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 87490072 1250 87488822 87488839
    0x18041104020d050a0f06080a031202070b09061f120b04152405010f05071104090210050d06080703080901050a090509010605040e0610050d0b0f030f01240503070311 72
    0x40010142da2045202c012100c1e00c500a00480c1e850502441403801002c800c140901824507418580e5034036000c00c040c3c104002c8803256000c1c40303915030440c2c04140c0c0001c5d1101d0103180820341da44e03607040d00f501c0c100701181c3c590070307590b5032240c2805180c820b503052023815402c0d15115403030740b40d100d800c040c00698100041200c04c05804a442c89100c0c45010407035a07417032105003581d410054540590b4402d60622a1440a019a860344101198600c1d40c1c4100c58800503a2158040380052181c00d0b4000d4008010690400f45650400041c00d03003100714400c24001d494442138003e488400501c0002c2542405101d106950360141003c2e000c0c9259a10b01242010340d10000a580f500082c3c1c090701c041036001a003404100802004140d00080c00d480c500c0c405411094024140c0c4503044051400ca642c44100801039a12504004c0d07000000038102c45102c540424014020111400e50300604440030414405c18000d0300c0020046a40007000703030414a00d1600c50306920342d0800c007007540c042201d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 87491322 1250 87490072 87490103
    0x190302030c0609120d18240c0807020d0b10080a080403030305070203130b0301050114130b0903030c01111b0613060207020a1d150301020708071e1e02030601050f1804 73
    0x800143e900b81d00309646004181c6c6040c0813040010441e50030800c44c00da4a00308112030549902d850b8140580f0500e421040d85500381415501400b034030900941c05412100340c1c0d414400440022405508030495600345940c0e02c1039101c2d0340c0c074610000200140790601c001c0010030b00a502644d40000c0c1401605e01e041c0451107450340003040c81e0824a413201010006000b1543d000703480b980c10410001d22545004910300002128412501c22442203140c0010500c01a03203040c0b00b0744401c079101c10700078401c07001d00e07828518480d000112003e405650045070141008000a14240284400d203400c8440d4002619850044c1d0b100d050140d0b0440b1100000080b001e501c02446500760701030100e0341c0d2450074850004800300311003800080c0311303a005100140c0401c1c2c8410407152001d42c040b40104062540462440552848890140c403280d5203c6078071610004202120380154400c6040da0f020707a80b16010844446e44031403280b40c20004460315003121101d0300c440d15400c02c1c081c00d400c1800041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 87492572 1250 87491322 87491359
    0xc0b060a21030e040501080a0230060108010b01031b080a021e0310060905060f18030a12020105100e011418130605060d0b0c0a090803040f05190302030c0609 69
    0x181a10201d0740c60101511410526038401c0b400c21440408507001d0090f0b51400006994076142020060b11403d040178482d10000c810b1005805220f90b00f0007014100d0448913120b544030042403003219055424402901615031007841244070000803554002c1040b0800c00013221103e03001010000099402c2101e24484640300903d80040042d0408a56403481c01110340b003e109071075405a4203021b00c0103004e10880d41c0714402d880c100650054400c0e1110060780869840c806145203454041c003446a035401405581048101000342e9038000348681d40340e0b1682000c070720010b48a40e0340d40ca1a00c1005100503040c0f486807081240b001401426003907040e01d05400746560544003030500042c52890802080601c2c05503d50180b4211001141c0104903214500c0c0e040e0700400d082400e000c0050341e0b90859003c3c0e0b048102800100003225152612411109440c3d6424000c031403191441a400351101e00c0c00036140c000b503a0340a805080c004a10100340055a006160580c0d0721503121507503d9803041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 87493822 1250 87492572 87492599
    0x1407080a0624121b14071a16141603050d0c030f06080102070818150406020105190504030c0204050c0904020c100b060a0e011409090403080901060f03030c0b060a 71
    0x64810302041880845268050001140c0700d0f2000c0b5481d040c80d000d00e40020540c444d442e115a65410603201a55000145e03035110300c51440010114031424907100803030708616003140e202d05221101143c1001c0301840913103a2990b102054001014101301c50032400d0180030b840c0541d58401c3c06c1650400c01c0c40500070041e60703108000f800002341c0d034411000c20032440340208001005030380003c5191031801c1d00c0f40b0040f4403462403141704020300008034002a480d841c14000b94010b84008050f111516010000c2c040c183c10f42e5800c0e0385050400c0310740000c3e107603885254042c0e680346d01c40c10380b40041c41c0d0070310026210081030702811a00c1845404001d4545000902d13190401401030801c500c114080350044844900d078482c0210014809000f03466040710280840c2202400d00f9403020741c0d00c0c0042c9070f0f68401c2c1164a50041481024401050340107510301d401003601400900c411902d6480201c0114a9844040c00080c4100e256102240032034074016000007000c1e0220706801d40340c0403100041d8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 87495072 1250 87493822 87493859
    0x604050606060702270603010606051303060203061203120906011706070809031e0d05010f120602030907090c0c030e0603090312180a140d03020708041403160807030b09011407080a06 80
    0xd620085c1005606c0c81c00380714910203000941400703801c001c40400080c811300c07158080201240d078000041001c681d1000c42c400960f030501c0003241ea0359070b0b108500108202003030391980c80d2849034800106a400c0d29640c084080180c04000306029507400f03504072000070000e0719800643c041000b40840d02c85c5820b070004e42032122842c0c42c0342d5407140d80c9002400c0b250140c0c0044e1000d080502c003413050704420190b60040c0354000c0800351302c031749a620740c0d1420300030960b2000080350324082190a9003600f1410a0070814060744561071640442024091316103c02c54400711560010405c00980680d01d03284240c01c24140c40100c2003d03010301044514140c94503030140c40c0b0b240d1300b00e82c100c03002c50f04110506842026250035401c10740301e9601d0810754025806450b44001c0c00550068541e1002c200310b144104030720709044400b40c1c1c0c4600f01078503219280000e50f0080074840c00521403407014040d080b0803a5030300f410150180d43c2c0907000c48907a00c001c0e02801c03105860380000103000c00c80c8400103500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 87496322 1250 87495072 87495139
    0x6090203120705070e010503030714030409061d07020f190302120d051008010903020a03031e050a0b01120e0318010909050103050c0a08010b032a1c0308090604050606060702 76
    0x95002c40d040562030004154040c140b01e03003840d401844184c034040103684805a002591002500310100c100d42540100d030007011015242c0301c0c000852040e0300c400c11215010903000010161602d04080b6107560709116019019031000440d0103030109a18203401541340280f05486036090300310740c014001c0c3e0103c2c1c0f062070143d817590f0a1100380450f2140d90002407001c078008120a221558020b522407803c6400502450780d1001540c0c1c2e10607440c4c0c603407040790001440802c0545043c0300e071840100085c1c08101e0008106040d0080310040b1f9102c0c0c10140c00d060300056041590040006a003440180f845904000001000107444055030180c24040c510450184c010407a03850700b0302481d442541e1000314075a040032420f8206072000b1030b00610180001d02100d42049066801c42c0440c0d00a80580760043c01c1d12948001181030450701400b45482581c41c8c10094850719031040e550401a68054400d400210205030a0f2910200a20256101810b4803d80040760440c1141c96591100b14a5030b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 87497572 1250 87496322 87496327
    0xb06130e061302281b060c1704121107060503010308030702030c030309210406170a02040b0406080a0f050103081918150905011d060702240a03060515030708040609020312 75
    0x40909004c0c080302904206032401c0c03e411030541040e01d072030019800b4084e0249075030340d03103070034905200e00d003c5c1c00c9011100b010265541043e04e056194210040d014034001490704129a0700701a0211b1041c04076040c90707031014296421901c51041383d030300c042e050200390310040141c20581c04040c00a0b51044020364050405100c7d60b03e41003d440001d00020343d0842000c000503c04142c0024031005000c9072580c500400c0e80c4c801d000b4000a200d20307040342c401c2c101c0c003060001e4810790004000344142e00710201880f40d040540b440340280c44003070000401c182c00034000b801c852150413001001c50055860f04000c044120030030110107103055008204031120300b01244c80600d40004040008003405c2c40c201c442480e40c20b644c40c4803840c021901038410000005e02c0b0095607508101020b15000f01c840c2d01804a0200d1913544060703010009100202c1d00f41900040d051030074001d0f110340c5400c040600c03480d503912440c1c01c403981c000007030044500642c0c0349903440260300c3c2000205031400d0b64044859 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 87498822 1250 87497572 87497617
    0x2280b0414060603010207080307030e01060e0a0e0c06040b0901080702031c0603020906030a03080105010c0212010203100602120403080d09020d05070806010501030e06011a0a020304080d0201020d0b06130e061302 93
    0x600b4030780002d0040f406a80100030b010005480e010071254440024900000c4d1111442da02c640504041c2e800b20001d0304142080c440044240c0d4040d0241200d45001c45110140c0344081c00950701403489856a542014480c554495000d001010f50080452054074944070983c40005184010700d900e500021341d6456050045041440419400890403401070005148070b940080c142001400f82d0340c100030100d41c0d0801103444000c0821480d00b2800020340d1a440c040c0500c0750f40020910507140144680700c0c0398182c140c1d4410455040c1c0c3c2c1c014030440e14195012103031700c0142202340c200702d800400540714075011400501041000e0103c40014226035413400e0700050640b0211200b000464000d6801000380b00da000f11091600810300d03a4860710307906483c0c2d05a040d40203940c0040c0490051901c19003015034194020300540c070652104006c1d0241e05414812a4080e4070008190601d00e10310600420401d0181030364403100c0108603545503108240e20b0000c5e80c014104603c443c0c1c503107204c2103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 87500072 1250 87498822 87498863
    0x3030905030c1f020102070512090108060a030f0318030618020a09020c030412031403010914010b030f0a0f0209030a030201050f06030114071b0c17060a02090102280b04 74
    0x88000c04007180141038000403a40091458401c0f1038804080c0020b51207030340e403154000e4055030381d0150000180c0d191042300148003007a0f0f41c001840c01c1d000900704000035001d840c00701103600c19039400410100395140f060b682a0380026803ea40169920392310400000003e515000f00091400655403006e489041807040c840c8000041d085115658014441d641401000005a8044845c44c003807110240710181819110054031038080300c5c00360000400414844c1403900121094044040f0710341d0507030b0b41c4000c3c1800c9404143c2c0c1000340341c4541008500001c1c01c940100007060b845510045c035098803080080e1411a00c00f000306c2c0580d44810401034000c0a030078040ea40904140c00a02802e4110005a202000018040c0050051303d03111288068224215550710712ba020307200403210340c0c4604c4d142e6007100140c0401c003118454440000da00d200140242d40083d1410707002815000503070071403500000190030044002002c0450f1075008544200304450085009189080c50b11480c000e2a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 87501322 1250 87500072 87500087
    0xb04060212100b16020d060e030c070503010b01090509060109080303011d18060105010807050408010504060e0610050f1c0b0a02030907060203030708010b030a0f14060f01090315090c0b0307090303 86
    0x40c2d1031504031903141000782d100940100c40081440ca00842c130415090302c009034034617084890181841c0d281c040c0c41c2e070110794000001c1000c480c1788001c944c940e950f20800c06080e224200c000d5400035802060401c4075007442101d044e0000740504001305038a03110141c080c5990426807005200c12400c200b185142600143e00365004030b071510f00c95503d00001d54020350364030010310070641048044d07030020b280d15120782c2c00d5034003910000009111038181420014040c010158000485001c1c40d0301107810054074002c1202242c81c0603000401c4502c414041201050301c1e4410084103a007140300c0c1200240c0d0703401081344039100c00400180c9906044140d14984a00c03900400103540c0700704180071005401001250444110f02c05084d500d540340c0c62454090014002000b58880c1041d181444c0514101c164600c22030b01500c404d01c032080c03180011900b203107141c070007d40108000c61040034904990b0b0442416180542100418150345030340c202d0160f8411582800094680c9c01c0c107004155000c4003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 87502572 1250 87501322 87501331
    0x14060307120c031b090e010b0f0c0d0306030b010b030609010311060f030109060e070206090316150903080403031116170910020a020114030609061002010f06120501060603061518030b04060212 84
    0x10408810703030400090080c0c8036010300522381c0c42e4001090011070aa540412140c29200c85010365000c202d4200001c0c005e803100380011904013036900c00204e030701514101036900c5032070010424000e60b4a0342c0c4440c500b002c2602c248d01d402c201e0810188039510003000055000b0300402c540010658600102045035060103040314045421910510524400000540d0300c030f03806140f11440c140b031242c82e10701198902c0d1142d43c002181041c01c180709050f0000c014a11450082c1c40c240105c44681003000554850030f0202585040e00004840c042503c0e2480310105070405282c440c50405031f5000643c0b4181c19040e804016031181e04801300315644005401d8114480d01d410a00b1402d1400015100a000034001d90090540e144040c800718800d41000a840030103050400140c0d88074440e08202401ca000142c03465800d002e0300149551091042c001201e0100e82d84454002c0c02c0c003001c40e581080001511000c1c40e540d10080301141564110a0055118100041e52801c040703400702c141c10340051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 87503822 1250 87502572 87502577
    0x40c050703020601090b0f0d03120b03010608100911040608030406031404030c030c02010909050c0403351b0601060503040506070309020108010611011d0c03070b0414060307120c031b 80
    0x3010009400244030f9043d14800e00f00480c40120b100701003074440c1c1460803060340c000300b44000307c8145a0406640641400070b01c03024030041803030800389401e0320701d280300d90109980300d4450318041d061594000351001e4404c0000c000e600708000006426076070302d60088100c0d40c00001e420030881b0781500c698010040070000e1712006141c10f8401800740c80c4116005001d001400360305000f113a04c140121001b078800010108103504010030311012641042c00120b500703248145260301e244282c01c00480e10401c2708191906984444040c1c6240ca400035901c80420a500c084101c001c48403d103da1406403009940e15902d03803400d410564940b402c00780c14101030610740105040035036402009241514000c1c1003120f010030321545802c1c010011040c5040800d44e42c08414502e000380880d20401c00401207003150400c644804009000c0c0c465403040c1c404039000d01c84005a070b820400099075005010307040504000c1540c003c0d260540d00705002010029544448050301d403081000304254070103d40c13 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 87505072 1250 87503822 87503827
    0x402040b0c1e03090f01020a0c080d020d0215060411040306050705070b061c03110709050f0106171015090803030a360b1f0f0e16020a120e04060b09040c05 68
    0x40b0345840344201002540070b0415903038400c0781030b40204601e00742c50398842c0011844d00e943e040e2443e191010401c2400060240000380c1040c0da100081c0341d0000025021481410780b541d030204030041c840c3e100110650748d014000040492480d200b00e40c403e440e5501c41582e55180e0345003440315030000410051050442a0b4940030072603085070464115645400c0943d0000403049145141c6001c0d90b00c408132403400d1004100201d03902c46000d504941d1692269a00082190103212011108981c1d109003103901c820200410402440c0c104d105080c142444412580c507140c90710300350340c812905403420a80319586a12012401146141065040f8502038446201c15401c01d485000300d140240c00c41502c4804030714240381580602c4100081303162019010fa035503903d0700754810800e00c62101000078580000d4804c001804107504010b005501030b02920130113695442d002e82a100c0c2e00300410100400105003a207a82c13280c8070180520640303031519011108100004d4179680f100c03000820106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 87506322 1250 87505072 87505123
    0xd030e03070b0c0d02040602031c0c08040f0f0803070f0f0216030308040611040315050f1009020c0c0a080a0605060319080d0f050a051e0f0c0c07050402040b0c 70
    0xc41034848a99001940000507212842c85449030300890007151545403001900003000c0c0c2c3c00000410545d20030027400018500001d8509040f00c4035030300b80d030010403450000174001908900805813168454448010300300c143c3e81740c0a80c1d64000b200e100c40461a0455091b005541081c10100c1b0303207078144000d1844008500141c070102c0f0b20f40c80020284200000460104040c54005040342000780721619181c2d0f590341000c0300342580e40794001d44000d02d4103000c90705103070f032100001d4418040036145c00344291a02c09441c0096000200401d5140180000854250303540c280420041c00088010007403086507042410031140003506030352081d440b641081c1080c2540700e0080c1989070300902c0c2c0c16122006961803001501c1c80c440d640d03050529002c100210000e250f840399005648900c01050381c01d44000c98203a03a00402d984261081065000050704201d541004041d213094990540300303907540c1d44011805070380250b0003484800801042000f10308408101d08940540400b8054501070207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 87507572 1250 87506322 87506351
    0x20603221a090703170c0a081801080a050f0103020d080d06030b060109060e03101113060503041203021c0221101e060504211a0403080105010203091e031f05090d03 72
    0x44015061758403000304d01e01e8100d0106001c11000d140c2c00000095484614181e104481b520401c03800b03003c15002ca02048610069108152041c0749a0301c0c510b4459086408200a0701b69907102100c000c0c104000d40c0c800c00b030841c02580000c5104900920741418000c0015007070303402540102d010003a1190002810355130029503014403201802000440c21a084000b040301d120b10955103008a4201d000040c3c990b03448401507124600481d940e9640c00d003004800c80c00c0c2e1042040c0d6a00b002c4442418201c8001c05600504012500580c9808810b09c80c4445003d201400c0b5503140828292000412541d0100700c0e03007516401d100220004d8581c10181c0240071400380b401550041d0041081c0c0b24031a6155004001e1040e0b00b0401e254000d05e185512451004011601140012004800090700b940008191030112000a00c1e0041032840c850300032000f141c01003420765141c4150380880604559584024500300411040440c4500e8140001854052240b40340c20415140c4100b0310103488 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 87508822 1250 87507572 87507593
    0x130c09050d06061a071205030f0703051510030209040f0605010917070902030a02090f0616060e210304030e091003060509010b061804140103050604020603221a090703 73
    0x11400c8408926081c01810301c400184000e4003d0b19408556403110840c201021000c1c1c400ca51183c581d02e00101c4420700b040f00d003400140d880283c140e4180c1701040f550b40c06608007584c44000e10b0a8006a4004100020f480301200c100800c0429400524102a03040c180101c24442c2c48401d8184610303464000005e1182e036151060345007521007028444800c41b014800e80380100a0254295224200450103000a5006c00d004a2084201e280000c0490400c401501d040403031141c14081400b82c43d45800c8040c00c01340d00c01450501071000c02c040500002e2088020807421180c01545915262802516410321612100e11840e415000c00494803580040803050301d074030020220742c988600c9451744c0900f0413030040d1039020300003003146407218400207074641950100300c405012101e103c1c254000d40d28020b00020302150481c0300050b01604000c00195000500360400b0810325041d03d401002c404504d032000c41d02544403001a0b1400b81001c00490f0300024281c02402c00d043c9555144101c82 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 87510072 1250 87508822 87508829
    0x90e030702010c03050c010c050d0c0207050a090e070f090207200904030f020c031c020c1c111305040615050103020307020a02010807140c0309090702030406090504021b01020c0705130c09 82
    0x141d403c540c1c801c140c4110141c80d2012840300c003c1c041c500902d0303006003403904420401c00c8030514021a0b41da2444c0b0000c4c03840222500036041e90000b0341001c0d45200034115110710002039100b404e80c005440001281c81200800500100503180c4965240011801c082400400660600310964100300c1e6280819030b60050b5043c10102c1c2c140a0004050b17040001c2d4142c0326916000340240304201e00d1000751944840c02051b400c0c0e0305072075210700800511507540d49503001c4c1510802c0d40d610003e140481d403849401d00003040c00241099201c1100c059500444003144e01c940c8941c040414124810f0000000e08000d007025401c61400d400300a41d260700ca114080e0421400390045920300c0d004440c4c1610681030313010142d5840d1070198080f9940d03802218a1401050000002403240d8404410b0b1380035646195603035216103291a0400000e0341000f040d00b00c02e0245d002c100e051201d4240700402c0400c04c6280500082443c040c10085100c0544400400242c06c02d20708143c00e950000103007095 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 87511322 1250 87510072 87510077
    0xf0a03030806040b0a15080702060106030905070b07060b060c0d081302011e030605030f0102070507060e030d111014040209150607020108090a0b010e1801020a05030a090213050a020a0801090e03070201 88
    0x10320074000700003080510646c1c80130030f0a20b50800c14103007256024400501c60003107031302203444c1c0d641e85d003004908650081001802c9600151130a00400804000030440c09006d030f480410780040c9032000940c140c0c40500510700f0799000c8000c40310000c0d00290340d268042d20300094482c64148030340000e080f042d81e6204040c5070504201300070400c180613910032350181401404070766444101c004800e000354414007082d10140314081001038158071641c192154000c010b4058200305031500d90590303201d80d001040751000d0040301e06c113005041e03051141417108d58114040032001c1c2854014003030504d0300a025180d4240390700d1500c61a40c1c03906412604680d9082c60120040c2c0d031201c582c54100341140030000e010b1800807000060807845c0c0030341c96000b0314034982800c581140c0740b103415080b442420300c0c241c0400c07018800114a840103a10500800d40042c140a840e604800d401904076407048903564000da0340072580b250099409030f04140034094031481042010303540e03801c3d0340d50382c054000300904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 87512572 1250 87511322 87511331
    0xf0e0a0b070503060f040c170703060315060605070305030703060b0a0c1505010303021902031e0303011d070806040b030a0f05030c0c010201090512030c04120b010e0618151207080601050f0a0303080604 88
    0x7e01e6104152240701906d070700c1098492070501010080240c026440240d42c04003005803074580001d400d110700d500b1900300b51a04c500d08901d0366010394154100415620074581d0b51a00090491302030030003411410000c2c1c1c0c4003001d040161a0030300c2c15102c1d554115034003c1c40c0c1001440001d070002400b41c541d2840a0100c00204103510000340362400c041d19456841d82c2c10300c105a0024800000303541a58000c28822180f02d80f40a0a0a0300c508200c0707801d8002030302c40d0701240807410a5402620b907124041d06550500086850341007010030380350300854503540002110700303d0460a1080544804c0248001d1000343c409840c0c2c2c0b81d0700c0c3c802d9081c403400038400102082d020443c0d80200c80050401c400c0e4200300800904100642740030034451820b080b141c03000010118540807000714915180c0002021030b946440b0805849803111402c140d03041135655050f0501641d04211040007401507074001c040c1c4d58140402c0c0304c9015015503110303000d411000014000a900030f000e1581c444001e440008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 87513822 1250 87512572 87512591
    0x3140102091203070302010c02120426010e070503010605030c030a0611090d03052215080901021605012a02120f0d091217090c04050a0f0e0a0b070503060f04 69
    0x5009105228189510070b55000404050680100c05021114000d800030040101150002d0f0380390803125101c20501c00341000203119015180c0b43c80005609030014411100036203c0c005402c60744108003599444e0f02090f0100070900c0d090007004060902907015200103055540841d0303540d07681020040010380c581d10801d1003404079506032180319500410002c0803018506002e0001e2b80104402102c5007803200c000d804a4002c00d071944212920705e2301d2507030710101c00c3c0d138101c560040103000440155020040f8050708040c6211008015014100001e4110650101284c01d20541501140013815000015013a1070f00810380c5080300080c3d01885070348001200c52607281e885405010182c07a8a0128000207000b080e02074075018241a44a00207035004000756940d071024100d89425469100c0c0c0015070980c01d1981002c1c0e00b0110401020410a1000502c6019640d1580300303c411039205a04040921821031985c070380040c95400d01c946075041160201e1060407414200c00d01441c0c44440c002d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 87515072 1250 87513822 87513863
    0xf040b01020a1e08030c0403150612020105070507030204050c13080a050d0c03090504090b060306092e02040312020c03120702010806010c05031207110111030126030d06151b0203060103 81
    0xb500510780c4102c4d13080da01e01c0c1c040f0b14038200703800ca030100780d030301c0c012034036602407042140d00c203c0b010f48003540c0724020501000e0340115401d42c01420110340300d0044000c00001a03d50f0b0042501541020304010384941b4000c28205800041d40d0040c040d40d44848051000f040c4040352050600300a4a04000c0302c8000781004d65984070158031041e005031819880b04140081c8507540340c041e50b41102038070403c1e201e00c03003169668000c031200820840701014401c00030300780380c07901c28070b801c07403035090141c00c0c0b40d6640c54484c00a000051002c000d07030400f6041c26402c1c44d0501505500c2c0500002e018100004d9030002014104000d040700e044c00080b00092040c400c0800944000304201d0301a0350070351500d2030004020440d0b42071941c000d0360900c03528401c05580c800c140e81c10380d41d0b0000c0501807103460030407004000d02040904a26404100070541415001c1d004800142c001c0d040420a402e0300e204008040c18441d5521421802c03290880c20300680e004211103046981121600380b9080700c00402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 87516322 1250 87515072 87515123
    0x5041424090109081c030501060c0213020903100204030506070314010e010504050c0702030a050c0a05030109030e090403091e0302090f0106021009020303090d0b01030c0b0c06010b0c030d020a0e0f040b01020a 91
    0x24002d116070301140c0020301203a00d8503c41e17000b0396038060201d0f0f681e0300400d4440070007510000707502c450290041503c8245650142821000003422901d15640000c0c2a130103e03031083d082584c1b80d800100030030036080e806001c0c400440b40600f198140b95894500705c90a10107041c040c2c14031941e145c1d0042035603644140151100c0540050070784150200b07a22301203584030140b101c0d081c09140900000202c0d4581072003070301009505912040c401981003070420090081c01003085003440040803010861090109444081002e225105e25402c1c1c110b0040041c0d121000b4071086241d05201c0061010680c04521315400406801020540c0162407000a041d4040c402c13005800c01c2410500000b4080050040c50480c1d01031001b240351a91690003803a0584151b03019024180e019000402c03c59075081c0003007040842050035030781480c040c00c0d12071041e41d0180c04814005500400c02c85001e1030318030b95481c0000e81c1141c00700480c84140001030745400340c2d128003a204040d8400c1c9485c10140f41e4a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 87517572 1250 87516322 87516329
    0x70f080d0b090109090b0105010f02190f06110a021009111003090b0c0d0e1b011101020403120c061406010212090604030f050a031b02031903050d0c05041424090109 72
    0xb0480180da100c035105001003c0b1540280e481000389400010154001c0b00c25001868039a40030b0454044041c84000754442c0100d002c541079014560302c0004500184951409075801421031a40c413088000c1c000c1c500103155003120019454000d030b8800095000b441d050348201e013503032000e84003d9904002d6000740380c20070000d00350703058000411020322040b070010543e003034082c0c3e010084240c441d14142c0d03807a4410820704022800c4030640411540c02942c0c070484144603000050324260712603451140b0000d098a2420126401032032100410195005050b600142c10282e01c6e001d281000000b951101c0041d0301c1e43c1c0d055400a03d490302c80c6c031040304540c0615045070075210303100100c0c0380c200d40c2c50b65164020303400500001c2080d114100d101c0d88600030990014010070300e018101c0540c85900041200c11003c1c09401c00c00c54608034500d001e00024904180c0703569031074038900f01c1594040000f05071f4981c460b6101d450b40c6440e25070703070320060301e205980461282c0d250400000140c502c03101640 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 87518822 1250 87517572 87517579
    0x20109050703110118050f010305040f140a11010302070312020a020f0303010b1b07150516240606050408030d240f090b010503070f080403090506070302150c070f080d0b 74
    0x401209100c0900102240e1440070b1783e074810310440c8040c0c05044401c082c000d15030320410b04002c49031150f100713030049a0400e0040c8400038a4102c10383c0c07200e04540280419052a8125480346001e01281d00800741503c034080c03e05514200303099600524140448003071005003075002c11100001c510800c26603c0d00c034400c0c400c40b03640c0c3d40c483c02511111b400991013406e06a00d0003590070188603010410604580c0b000d48452424501c0300410f03500b54209100310a680003200c89441c0c04580c083c4440d41e03240103900640d214160040440c030040e10903d03000007042c8841007000f000302860000485120404031000000d04040c41d1a8096500d1100607440411044071314001c1651302e440c85011044034440d1804120181d500001500e83d4002103a1100c0450112091812094059651035500600c01d01d00001469204c000150803034026240030740c010383c003c1d04003641081e0b507481003540141604100a00b460f010b5900c0071080003001c0e400510082000c150b4092014903500070740f46021004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 87520072 1250 87518822 87518833
    0x4020d060e1014090105060a060915141b0c01020319110109080310090e070308041211060a030c1214011707091a0108160e0d0807021003090209160804060c02010905 72
    0x3d00c510a10303120150352003e40340d480c0c030300407600c0d078030749000408102e94154135401a00303841c0413030303141e16002c0c00b00c01103040c0031200c05407503100e601c050010031504400f11b07001910309050166084c5000d43c0d000002d41558810020116810144092001ca4042a2030070720110000020003902626510b000206409004800d108249058482660a46002040801c10340d40c0c42d10090355500541d11001c0e0005d83c0c10041800211289206604070a016041007088104203001080041d800302e100c140c0020740c0d411a500300c8560042ca414039080007040305201440b40200b60815121040c0f05000305400c408824600e210401d0000b040140b40c1d6020811000301003a5242e003010f00000d01050008200e2070008001604110b408400051282c0d01c681c0c51006030b0b014001d12401840090302c0351341050002d50016910400300304135110f40d80c0d03000700b44594940705000000e034003e41a0702c440d20600e0b0001c491594446083c0b540a0f400801c08140c0c0940d94505a0051a0b86a030203811800395 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 87521322 1250 87520072 87520091
    0x80313110405130515070824030703150608060c0406050c07090e0a060f0507021b0406030209101706040503030a02031503030309070602120a0207030f02030c0d050604020102011404020d060e10 84
    0x1942e40c2001c501403000d5901700f0100310541031100004881c0c64001c1038448004c60402182c0ca40101b4000c803203000e482441c103841da40080d15050441d84202c82c0116401186848400f203400307034000606483c00100214100280c101d1400d02480c0522810000301086400421104020401c010008404108a1940503140d11505c940100d1802d4813020f0804a82050058140c072030207214000c0d47c0c3c05480c408605040d02243c211826402d594056144d42c00400580c3e80e090205028070071084034a03520516041707503200d050001c0ca4004105401c09420000810808001c60b50301c01070312180169265100021002000a0700c2076050f0184800710401c040c1d4000050040d081e1041d640842c0e5004036080040c540c18481c8402080050300408000c00000710386081d0910701d284010161011001c040c5c0104441c1e074003114083c0d80b0355100c0c205000035560284a403542c0c000030b1855025207403810f40c01241003845800c0008210395035801c640308100806100c00304511000b440d0a0000425 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 87522572 1250 87521322 87521341
    0x4030305030a1104120b1f0620070b1b0d090e0c0d0617010b130b030a02011d370e040b0702070302100201090201080603190803070c0210031b0309080313110405 70
    0x10101d815a01240e20400100e0034004000c030881d04488c8c01c1d540347d02d07540c01000d8030f459000c440c03a140d120051040020224503402d001c400790034010b8500c20039030360201d01c04402034940890311000340e0500040c03907804d000d4a462100d200f03600548164016507100e5034625414001c181d40d91000e41c008000b52545207401d4819040503200c1c80b021507030140c1c070201c1080c07008102c5044002c050341c1075011240d98001075001e211801600840710000701c0441e011800400c11001c141d031102040403c2c141007192101c1a03200e1403560300322000303d46022160820412150b803080160010341091405000034102510810200001e1036000e4000c86040070040c1010340a4201400b04a0109840780001a600e00b00001d0b40d544c80850080000382e0f580b15510352003010b80c0702401d000104202100c0340380260b00c64081c010100e90701e651300080c0c502003003001c801c0111420f802150402d420300d100040803401c0d2006480c2c0000c3c2541c02c000d0100c0661034414032a61307000380800e8111741030100b00910041c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 87523822 1250 87522572 87522593
    0xc190b0c12070308181f0902010c170705060702030421020303090a060815180402010509030f07060203030a06050f0f040f0b040f1401080a03020a03031a040509010c02010c0504030305030a110412 85
    0x20140103503a034031401201d0301c182e1140700e08082e04006e00340c1c44d040c90f03048001c0f0340c001e0783c041401810140309044003034803003601d444101d519001c0300080c0021400d00b003003c10480290304c400c951014509081c14460300d01e10100900404039011402918180250b503418070840f50385510041c418414541d840c4805040f00604844e9003078885258a541041e234100100496a49001c411030403d1a54555005641d150440400340d42c0601c120501e640b816030741000110041d01c5503800458580c680892030009640e1715400c81350040d000e0101c240c100d40c0303482c1070080d90200c0480d0040f80050181790f013031000f0130070949281d910074203040b8200c40000300d66010704ca01d9070000c401121030781e803074880c0c45a40303c06038a402401a8005a514004240320b940803140c80070f21a0f0098000302c00180020b402e0350402e07100920280d550714071402241da024824410040c0d83c60825034142465038402030210b0100400d10000360352681c000031014442c03001142c021b00b45600120400078014285400340c0d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 87525072 1250 87523822 87523831
    0x4091503020f0f060912032109010c0f02030d050a0b30120d020d0204030210050d0c09080a0308061c0309150302040f1404140115020c190b0c12070308 66
    0x12040c0b20301491090802c140f101d0a0048054502481c2c01c04680610041c09030300301b11840940000c0c081d2100c450b125042d407010a2007146e41c2e107540750400c0a07a0908441c1d0368010b0000b13000817208031042c19030700441501c5c00d891440038002641c1d901c4038050400f800c0b40001d91680221043c0d071014070f0a150340b44d8410803031218454808800c0c1103507101685c4140058030103000752014003000508241640042c000500892005802c283c0d80e54041500d034001c0380c1281021a9000c1840300712920613100b0603144018500d080c59421b490407035180d8803900c005002408100800000480700c0d125182c4440415841640010702421103080042c03000d04180036034031212018880344610a8402e009541c00c1e181d511141c10080c41c90803805c2c6004e140d807100403c1e00144c8846881c131804c03941a000e40d00070855104c501100c3c480402000b41010304021400b031180103406070a844103006001d0480546508100c001d81c0c0340166510240b130081101c400c1101c542c0c000138505d0030180d2100c2a640135 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 87526322 1250 87525072 87525079
    0x40b120d0f17010509040f05010b0402070f05010b040b010e010e03120304050601030b0106020c030309010503280b0a06111c0c06020301080c04051510050a1b110906010503090601050d080409150302 86
    0x668451800d0280b001e50038812181c0c0008000045004201c40300070440103248610000560602043c0124081e40c00654003612050181a51442840f00a005105001c0320481f020061002014000b80c69000c00114190401a000086040365101000703000e081072211551140c0728a41454200d0b0f451500b40001c072182101e90b4000a0700c5070000a0700c00c08080000c0c007540c20005070303000440b03031508018000c0c20403000d02820025040c2d103c850200801020600c080703000c0c80d9540070700c841c45410368080410404502e00d69402007401088200400c856419940e510a00460040750440d40600010309154400000060240c2e4001160041104241c406025503501c0786c90b040e8884104249040e003024180052034111841a00148081070090902e04009070000381840300d0350803000f07001c5840052003510102c9a151840342c066108000f4a090791852502c0f8900300e0702d820040c440c40f40142003000842042010038015900503081546041003010701c440440303c450031552200341d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 87527572 1250 87526322 87526337
    0x160b0d0b090112061a1003060608060625020f1e030106060e01050706050a0204090e07053a02012a0c05041506050c010906090305030f010902031302040b120d0f 70
    0x40e060249800381240e08402c640403030080152100310203484001c84081780d89030a9080900d45a840d0016119030120a030f90020b1900d0402d003000e050410090500f034420f6a00f80500d0006a0b6070190003105080da0201304c05842c3c1c41403000c210440000d52000b507100c2503040e40b1200755024002400d612400480007407113401e684040964080a40c643e40a00140d0104206000325046800107034000503020001442c00da911101001101ca54549400380350708451420421807030210f080244040d55114481428080302e4032444072164036060070655108441c0c410005d5a004091341e0314045a040b4114000710418044108074124141044508001050740440eaa061501c10305045181e22030b078400c85641004c20070740e034940266080302041c0d92142141e600040440c01190341a5100751a495181d081001ea40151110140c0118800a00c14410000001d141c0f0301401801601910000380351703290b4102040b103c1c0460000902c6a01c00e24690305051076020100054005071070b9202c55 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 87528822 1250 87527572 87527591
    0x3070b0721052104020a03080a09171209150d02120403020f0105060102031602031213060909020a02100216170309010c1107031202100f02090406060806090106050309160b0d 76
    0x1595801038400f880000c2542c814448114008812200e8006000405032103650340c0e2a6241051a0701c122240780015540c038000700302d014110341410341c03c40002c0c4050302801080740302410b1305019508104d0301c01c696102503174003108031100840790f00c6c1c8403002d4203664030314400345024121801542d04a00500c200404940045e130184038090103000140d024501d03202c03661221030451406800142d034140907100d118504915108020240d2441d10000d280c821464860701400250140c1c0c800076400d401040007200c01e66010036002d9019070b0805d00140c0f6041000320714005041c201d10b0003401c0315800b030112032030302c1c0d035510281d44180d8418009000e08000300074100d0b26400f00302d0400074aa4090003051000a140e68100f45e500c1690b88112a01d0342c2c12800e142094502140c114400f05078005603a09880c106809042c0140c501c030f04007041d081c103015000c10b000b03e40500c110340801030f0200c04695403440500032590030000c800409804551240b180c142c1540c800100c00650038600800d86 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 87530072 1250 87528822 87528827
    0x501080c03041109070e18072307080f091003091b0305070306020306062101030201090e040302031605010204051002060a050105040501030b04030e030304090e06060901080601080a02010e03070b0721 87
    0x100d02c5143c0c4900032083c40e08240080c0120081c024150301c0078054040102d010603111075040004141505400310322504200390003030188400020314814031f4003016044194011020100e039590f65004407641e950300d4181881d01c80c0e034000c0d100c0440d0302810a014005205902d50044030803d409807041c011040c07100400d6807859000352200900d150803882c002c01c04035119078055644900c0180845190030502c000140405ca01c0e015469500320720343c0014011f5580c0584030002078071008a0480042c00c00d92806541c1c0c2c010103070403404000010454000b040310030f4054400800015007035003294420351401945a0300100e4210403582c3c6404000500c42c034042c041d050482c4d810894007842c80d141d03910202c4126a01021090701440104070004188000d4801d0a40c8900800c000e0700590800d03004108403000306901004207030340801c2c010300400a001c40d202c14219424201007a4000c400b03c0420b082c142903522000c400940441c001040c4070f046104400c100d0008a8121107428021905 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 87531322 1250 87530072 87530077
    0x90d14030105030d050f040b1603090503031303060b1504080718020a080c030a020405031605120a03020c0f041d03071a010e01121a0103081b0a0803040204020319150501080c 76
    0xb42c560540c000d40c02c055006014100401c3c0c240c592121081c58a9243c0340f50410a511a4481c07298900140c10b14a060552100a26000c1c000450156140a250242c590400351243c0805050706690b51010b0401d550741440f55102d064002e46015241c0d595162255180e414500c10081c60305603001c3c8413038401300903208484981c11203444c2d99003180c07942201040704d904014500307800c3c2c560800c4046060703a400c01142c244680f062041d070300c4250800040c01100d002035650f80304954000403403500041c4c3c0205004030300040c10b940080e080120140064040d04030200080d0544111444070000c502c000702c001c220507030060003000702103540018007201c0b902d400d1182c002545c204d08010302280c6100100c0d110410300405050241001d01c4140b0702119200380d104844c0e2000000d000b4814844010b24032044031010000f908850010740c0311201c0511000b44002d00c12640040001e080b0442d42c07110b0310365802c0882c1c04012400305081c0e01c1c000c0705d03c98040c0b203002c13899800000300450b607145d08 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 87532572 1250 87531322 87531329
    0xb03151609050312030603100e0309011d03070b0a120e0708070f030507050603041a10030c050402040803030a2403050d14160204150513050a050603120304120215090d140301 76
    0x10a00100c0c65900070b000c940000d4546d0342d05000304091160664028054180d000c003215000c5d555880e600b0307002506041103c9400360b15414285060400ba5a000c10304401711610410b249503030741d18000c800c8401d888a41d9100c7c0d10320307180c80c0c0982d504035030001d503c1c8241c3d50100b007120704054482c0c5090781820228880184145e00008041c055814030002850b0010b22030041581d801400c5541764030b2204089641201c0210194000c00900411541000040c1000e46045280604198410b41c8038440141000311150329081107180d20800b10905280d034441d50702c400d0000700c3e00c070f282254440c00d0751282800002d039101c26154007a40d040c02111000c10403040d0030700400f411642400060030701fa0100c0c0205588180c0300140581b100e1044541c074010301c07040081c652518000b101c00b150320150003a4005d520203054200b6815800e4101ca4005802c00403100745100c284104915041280303400c031103140700880510151500c000307800c0300120460348403000c0004031504540f02d240004d20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 87533822 1250 87532572 87532579
    0x30a060b0f04170703120503060a1a0f1305040c11010b010e0f010e0d17040504060f08030a0809030c100905060f04030906030c09080d020718050f04060f0b0315160905 73
    0x4010803200420f650b8483c0e1010104080d81d03115543d90b180c3d1402c54820100b0900401c80010030850180351070110728025265180328100540e480d40220b80c018024059001c414160025105984006080103c0001c0c0310003482071040b0391010a005060b0080e00400e5480c660074070149080300d60080c0c161401044c3c0240c00b0501d4201e683c401118004120385229412400d400c406001003080c4a151403030243c4903410031950740b032400c400e110844441c2e61080b107000c0142d96060007494004000c582442499141c0202c00361100d0f03c1c110304511503520494050f2140c0d02403140c0103c0c0c107411481c0128060406c0e00c105030b0b640e41c0e414800380300490700200001c46941007401034078003d6000d200070000324a0700481c0540c80c2c840043c50305010010741805640210420044890204004a1800c03901c00c1e05102c1820042e5103640d81c00700c00380000300390035201c181c4110094420340c0024007002c002407c40b1100c000400020040440c16034007164044403241440c0016401109400c04948024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 87535072 1250 87533822 87533827
    0xf14030a02010c14010e160801020304050d0e030709060909030806182e14030d051606111614060105010306030f2006040303030c0306050109030f02010819090602030a060b0f 76
    0x158011070388440c2886013126060b602c0c0c0c40000135881d0900c15a411061014020b10380c610000a02c81001255540720031896801081004000380001c00d8458040c0d4503818001d1412000400180c203251050b00000d1009161500004200a85800080c10306000752501001504c90360148441c3c255000c05803500c0aa404011540e00443d11040c1d031300c3c18010740e806860b04400f080301200b4404942c1c3c810348601460807100019480c00784200440c00c03406007000752400e0408038410040c1071109401900443d0380d0441e00311890600c504440d00c25840c003804516a280310720380b8203e10520710004081d6032003500f001090715406031040e030b4181d0340c004640283f4404540c1d9440096503040440b0300c2ca4411005015000e51141c00203440518820f8502044c684038400000f022220307103038017490401c0030351001040030441002840c0d172442d80a180030750301d60340d60004100310070304042070050150f850944140e082c442190b01450149000380c0702403051940c0c03500e02e008180103c0703d8a020706d8104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 87536322 1250 87535072 87535093
    0x2120402010804020a0803071103010f0207020a0e0a060e07020607030e031312020a0302030a03120b03160509180d050a080f060913030210050f04060e06010326090301020406090f1403 80
    0x52942d0079846480102001c401580b00d50816013113070480b02e411620028810003402c1a49402e0140d05140c6050b13200450500e25030b40c002890107201440350b9040400030f4004505c0070354003a000705010701a03010016005003018a030081d51000100c46d050000382c6002003480e101c0d4004001c8405980c1d001042c1100b150038461422001070340018104d0784034003032043c00401030301c05005c103c64245c003d48402405101c0c0000348425200c1045501d4803a400080111108034565030700340058803415141e004403a502d1030ba6451400e032a8252810044c8240e14044005e07d601000905040d40d89503118125629603120102c0041420755445600862910008491a51882145125600a2049429401616050004440d81900c000c4070040705002040144101d0b4000c0a0301c06c0103000c01040698910b803610321021084c40b150107400c540c1015070308643c0070000180d801c0c051000f4003c640d11a42d90304090142010b521828045007212403000904801c03000611043c15005000340c20b20496 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 87537572 1250 87536322 87536327
    0x150105040c0e0901060504030212010506150702010c020a0f180e030306060906070f0602091005090f09090109020a090509010b031c08060a0b0d050708160c0b0606090d03030501090f0212040201 84
    0x6102005508010b4100a240ea2a03a10488514003e02940d00c88981d51415401400b40100b880701e540c1095a042c001840311607100d1404106050301000100c58030342c0c080d840101d4003034581a101035400110382034003203040e0b07a41c800103500300d03039025000300c011001c02c0720080207481002124a03c1a042440011100c0c10801c005102c1604014612032074241e40707540c0c244020800070381c1a20701581c04240580f03281011489400c41c10100c0c1811030078036403102e0010302070b001d40004081c000c000801c003080c00c548094010b66103044c2d000702042012503e40307580b1001414102c90000701036003420410741e0241000b00b00e0083c1080b050038883c4000d080d00f08282c0b81040094030f03982d04108120720020314440c07602c02078440880143d2010a0500f40980010218071018040800300d0268114800020342c01a09001803640d2010551361281c1c2d8480000c0c1c401e010307030f910944d041440d1170507103010140e150744923b0507501d0303940042042003c002c481000b280902d10842d80003080c41000700d0055070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 87538822 1250 87537572 87537581
    0x1080103110d0b0c04210b060d050106080a080d0b0901030c1e0f0909050706020102040f1a07080a17090307020612090f07180f05040f020d06020c030301031101080915010504 76
    0xa0064000e030b84101256440112210040701e00841e003500109060080502c0d00184110150800303051103008032031602d80000211004e010144100c0321107060404005d400c5d04030800500103102611168074085c24440c1c400d52026a4141a0902e081801202450072000d214181c980108000140351708100c0c034010071040b078905034040040c07410300002e54002140500380107051900c1c00810524220b2800078502030362070b0805020b590040c042401103d10f500d0304001210542155103c481500211840ca18410320001802c1b200000400b404d07c56080318610041e20081101c0c2d4109a491110150300c03401200002944150100702150070a06881e038030395007040300e078000d80c0c40e0310280030507641c070740160359000c20f081d00d144c5050700080e414030f44601c0c01c0300c1d24076520601480c94103544041c031100707003400000d120b10380d426100001d01079242d040c1c502180750b4408a9550f5610781c1050b03018030650303110160000d1040e00010b20807041c049032100c8068505940908980d0a02c010031020b030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 87540072 1250 87538822 87538853
    0x14060307020115181a03030322080a0315090c02150604140f180115210b1003020a05030d020c01140d1112060616030815030105091015030201080103 65
    0x1503407070350394400729180c11142c00ca0041804c111900410614104d2550558080780b403400444668911142440d80707001c01241e910428442c1e080c15501400d10030240f2a5042000141c00880041503041d8199010752001140101c40d1a84d107481c155551440c009441c0c0511002005801184072070100058003001035401110081c0040303100007403c001c243c9030500c111441c055095a400070301644203582c01c0c0c0b8064160780306000703001d404203558964100655512442000c041c080e00402040241e203417440c00b14a51100c000d12040c01d011001c82d261036524081640f00300c4040d54001407a250018040341101103c0e0003801c2c282d15400010b42d41519403410684a901040201e5215034100307102e0351030314a00407400561206481100e400340700700000c0401380204010048010350030446820b40c0d042540c14a800000c9513540491203085820366407241e6010b6003808144440307080082080c01c0c80c2140c05108004c82800b45040c000c400a2910011380810074041c0140040340d510305101450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 87541322 1250 87540072 87540077
    0x20307020423070f0801060906081602010e0f100b0d02010c14010209271b030c03070905120109052104030209040204140103050f0c010f05040509180d020c09060a14060307 75
    0x10b601000c5000a201d080c00c07508280000c909810025000750030086480c0540030914007080c1007410302d0009071200002400129140320402d456103100c034400d400580005c48840c0544400d000f90144140c0d459040c02c00b0240c00724102451070440c2e0400090703880f4050740580d40d9036813040003621030302c0320550000300b042c000355020881e0385804d45406141070440790103d10b64862001c0800d807046143c1c3c00180c42e030050318070140c145548920f60b150541707410003244282d0640e641c4a40e201640d501d0910b5002c290030094100c0055a0310406610440556011b07074281c45107209402c02802511407082e6404110f0703001848144054288041c00d96805031010b88001000c01d02194100030a54090b8800c944560049401c0b448102050065401c03168082c00e018003a11065440504203002d0380c010b607030044024030b00184640714003d121148400320107042c0c501c152400f940007500e41600d000c64902602c4081c000c140f45003480841d420488c0d4017601390084680ea01c104003c101d92014050104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 87542572 1250 87541322 87541361
    0x40b091c0c022b0b0901020909180a02031002030103031d01200c0409140d030b0d03031109040c020c01090b04081c0504030b010e060f040b0916110610080f07060203070204 75
    0x541c3c61079101d03c0155219800886506652030449040c00004040048503401845044000e4a840c10159000a00034003c8000b2040c0500705618103000d050020b94144030314a4101c6052072154002c50690380250340b0803903400354510740702d014071041c1c584060004855035091042012030303e049070140aa200c0a80c4d05041c80d00f00008c040e503d8031a816129010070a2030750f2030410003000145c281d806241800e010300901c5800044940e0504e807005002c0c95254500d24442a03902d4088800004000340104031131685800020f50b03a540302d81c00540800c62800380400c1840b05101135404442070300005142c0800700e15411446480c80d64225024040b0900006c0005020410654041e01d004140c6000501e4400c1c1040508641400001c0c0514541540b0f800e85403201c4410580c09081c0041244555221440403144114010160301e0503020710414400c0c03400b45891282c0c115582076086070300013a1445201c54441c05207200ea4400341c0d204208480047c1426000105085101e000c68003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 87543822 1250 87542572 87542599
    0x10515040801020705010b0a060f08040f021c061401140310020a0c020607060c0305010f050904140f0114160203120a0b0402160305070614010f060804060905010603050303040b091c0c02 81
    0x342a42c101404c01c80e400d135107660340c00205040c240c071820020603941c504444440c0c900c4001400e904400303030010740300140360100b030800d54079506102455182e02541c0007041c01200d041078070050421000095009413240e0000a0742e1207100040400b14500170050051a40100200d4000350b004507a82024032601030483c20259582d00c016101a50140c400458040303460f4034018116a4160040120208440c209005a0f00d50308015640f15500031603c040401c0c41410700752808036844405a407960800100e95500820300ea0500d0003010101d1050360900c0c10303200b050784c0b00e020380c01c03078400c0701c41d60f8400007000e040542d008401d004a020700300501c1c2c01500c2229283c50340900342c064001c54000201c41c070401ca142d01c220040803040314005c00895042080c08101120644100d41c20001c0710341c08079048c008154000e01e075281d030000081010654901d020354880d081203c094400c000743e140040ca48103400704000340b04c1c0c0702200d0003861195541c038040d5140507e42d44142c0e006000d03002c084 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 87545072 1250 87543822 87543839
    0x60f1d120d0b060a090905010506030c04140a0b0c0c0f060703020604030f050f070303051f0e061905030f0c0111030a0801031e061401140607050c010324180c02010e0601051504 77
    0x1031150344425911780c0055402d03c0500b105951060348003a000e0342040041101c0748000c0d005850507140404880c1d045801104001401004180c101c041259000144480b0312500041c59800c04034094130000503602c40502000050b006010003c1e002d600240b00240c0001e0ac5100b100f01724864a050080c28400600e00301000c82d08000f60880220740d58005004a003040c05190ba0b030320619421007031081e1409d00c040042141c0c4c0c0600b00034001e0300d507045140e0303030601c0c1c0400c0b010240601800b101d400c2081c00780110b580b030708034800107404500c071000f0b9210407190201c200c1d02c4840b0181c950f0070050f440c654410701c00c01c0c8800d03034060410440445903000a0511b0090680c420703003504100300e81d941400c080302680d80c550341007070f44038034420450500081c01c0451403002c40c0b03109003400904d8000208072640305a08420b040e01d210804103201203141d18000c4458007445007103860410209108110a82c00c07100121343c40741d15a4000001007059180030184404c038450b003102c486040070f0785da2964 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 87546322 1250 87545072 87545077
    0x90708010c021b03030306130b0a080a0f0b01050603040b0112030c0501020a092105250503030d0218040501080316020301020c07060905100801050108041205090d060f1d120d0b06 78
    0x122006821000c245403420f120034007401814142100558514200b80700040e041760b0135050200101912100d00c1c101c01d0f55030048120003014400c061b901d5180c11841c2250703550562440c21940e00c55884004a03140c2070140030b6901c6550b10030201b80c0b86900f800301414098201410813020042c0160212001030000c0c00581454076641d215694490b003805100d0b911a03000c05112030341060b0403801e61000c1407002900780802212810010700c110360382031020348052010341000d5010700c00010240c6402c00f40e13034000d0140000b84030031070b541d6011207001c01c01541e01c02e21648016610a11800d0a800c051400b4055154030081c0014039009404203010f081c4406544040c01007110023000f044541401707016115451141e2800c000a5070420002a24420024101501c01c0310b81c0387c5000c5505004400b100d40342c1c000109011200341c124503040e400752001003da41072103410f21800480c50a2138145a809048450b00a0490440c4044410341580c0188170143c0d89580c0b1400200400d072141c400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 87547572 1250 87546322 87546341
    0x3307230304021c06050702070515040603151a0307091202130213150509030105060904030f080a1103011403100627060504020304050102070b1005090c0711030d110d0201050c0d020309070801 83
    0x885e1500e082c1c07034041d04000706a80700e2805003100ea40b00c60000b60981c0101ea041d1aa1030500040a00c105a92492100b40d00e410a9600c1d040b040342038144241020059481030f02035550b01e0061303940320180b03085420b0110320020340200d90b40d48181a0203159030007600904c95a85c42030003040d0340d21000b40c0c0001c816603804001007280002c0541c102d007001c3c0941d940c0b0010540d4500442d050594000b805000d8035508082042000000300322040100d400210b0b004079a08521031b01c0356104c800740d0800fa0b11141040d440b0744121001806036540c1e0f8040c0008403190040481d200c00148000c1515014004400c3c3c03003100d507941004103007590303030b40b01642c011030054000684490451412500c0071f00c02500000404400150400059a43c013540ca54050001c0c0c42c0740b901e9030001d280441c034500c041615a9414041c1c220f00814495015005401c0d42201030212544604503c50130b9089481c241d42024001c5820010b844a5162940007590004010000c8030502275403030110728215410f111 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 87548822 1250 87547572 87547583
    0x7020d061a010e100509031c1805030d090915050604030507030c0b03090c06091206190f020a08010b0703090308041403010b0604061b0201023307230304021c 69
    0x11040c00003a0014003201c419402802c091088110300360018a5034a684807001c01005400900114a0340b41840881c40215548424070f0090716400c0740940942110146100307220780000300016180307400200e03000500c81e6916510440c9082810400141c0624000320f40040d2500e40300107079a44812004000a50117600075000c0700e4110320740203030070045541c0000e004180502c103101c0c10b81d0000c6100c000003201224915520342c0000003140c0d8443d44805403141c0c60190340204a0402d14100c0e094461514010381040340c04d4403400200201d000380901c2500060241006112004d148801041014020706140c43c80c0d6960355603011030ad43c000c2e00b040c101260981c540003081d0a007405042900d1004035081c50415050020007400b07038122a000c3c0b40c46c0484c003810f14007564000e0110381d0521030b164500200c518001d100320506100041c1e6540c031001d01e604006026244940390541c0100340ca2000910051820100394000d41c00182040c3d034004082c4091031034049400f11805400352089 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 87550072 1250 87548822 87548831
    0x203160e13111902030c0d0e0303030a0519051e060a080a02150f1c06050609090a09020a080d170603010905031903020f1803010c03060e01050d030909050901060302030615030304061407020d06 84
    0x946d243d00340a0341403070400600400088420042d0340200c02d403036101c0400e8000040940e214030304c1070a2200015412080c0d42e107807800b884814041b03559000131400c400600803c080c1c50794024494400c05901c260049900000e60910040c1750141d0a4242a81c220103514101881c41c4e41205036580004480c0c6040d44c02d03e21904569031050080c4070040500b1a459801c203107440f0085019031034010b146411181d41e0f441070b00115501d20f18000c010b01040f1040303070311038015024040d001c0c1755148400d86045d08040001619071605020301c41500d0b52001c0510700380f170542c0c070928154060303100000042c55024052044003a51550140016820840c08c1d080005c40f280281403c50f004a10b5007030805040042c24006410038519035070445100342c943c0840e404143c201240c00d000c81c3d4120b05d12850400091102c8045c05400c20b02c140c0b0300860036202e440d10f8903409101c1203082c200640f60160024402040210300441c881c1c3c428680c84009545090000da00061060701c20041c2211031990300c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 87551322 1250 87550072 87550087
    0x70812090105180607080601030b040f150614190305060105040e160807020c0904030f030207020402180f01050c0c0108040f02090f090105090d090e0603070302090108010203160e1311190203 83
    0x400a010a2114000541460704258100a00c40000100307e60306064448000c806282c80b254807102042c00545000c1204a5115041c04078007002c510a000025041d022140c003085070301d5080f103c80e4211041030381c0048800c0c1d4401d41c05824001c1c51141407140c10310000409441030071815210700300c5910030f5103d01c03040d040702a00e05400500010210b60184c50f0034101c6488a280141d08240c01d400d0400c2020f1038404210007911401100030b42187c0045507030a00c200e01c3c21403040c1d4081044540c8441c0003051001100c89000e03c2e000c40c00b0070741c01080c441060707500820386075800600035180c0d0118400c0c80c2d00402c4a11805483c1c041001f1140c40402c4001030081c0301d425041040b10f03001e800450020b460003440c4074003a004a210880c4841c0110320703d55010070842000b1035012f06402c1e071350341c1e4440015000b90021641d810001000e400b40320000c900c210210b013048180100020040503110368004001c6c1041c003150080e1880800000440790512541100c01082e00c0d4000c595030581c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 87552572 1250 87551322 87551341
    0x6162003120f0105010206070c02060f040e010302040f11180d0807080316080601090603020c031b1c020a21120222080c0a03120e0a0b040302010f110d05070812090105 73
    0x1e044840b44600c00c0010311190707a010500070b800516901d00781d10140150f00000d440d500c2032500a586000b0002400608c4080d12144103040701e0003105c041104500502585054500103000001c18400400150450301d0b9002c007a0828028007404a0341c440c00281e5840015620500d825100788501004108112001044c2d4401081041c9000601c41c188040040c0c19000180142428150040398040011104000ba100503100059400240c041c03941105c5868030108805002465180460203a1050002680e10f03200ba80c0258540341200454141200700710b04124001c08103e0605004da848818a001402220f142402c4288441ca04520540110007842d408045187c0045d018103110369102e80040301100d8004c070143d02116884003045940f9619440c000307074400f10384140462201724100250058a03c00c2e203603c0080140c9440c15a1210000c80034140a40e00040da1286114404e60280880341e2044a0740790800341824610301c03d4040842d80d0101981d0760307004103c014034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 87553822 1250 87552572 87552607
    0x50c130b1c1e02010509060f0c07061e020102040e010b0c01090c0b03010503100902060304141e030301030b010602391507050d0c0c14010c060e0f010f020c06162003 72
    0x680d142d0310b40940c1003607a001800a00804100c10711845010403540b40c650707080d204981400c6000c40582d480103468849c00303001492402402c0d4101c40729000300714411070051088400750381403a0049030070b603071810f11038440b41d6100810030b42c0709540700d0726070700001240a11701c80d010b44100189581c903503042409140c64582c6600000b407159040045640c0035854a4048035000b503006015950140c1102c41880d1a280c034114508035040e0003e141c2c00407410001c406941030328800c0b070359a0026640d6100c102d985040f40b2030403e61100800080c3e00040d000d080c089040c106e81740e580003901d40e0341100000d08410716a1503c81035510000f452904110040c401d900e810700181c00c2c01ea42c100b00a407100036407043c140c01551104a903c000044181e07029440c40c411966000350240b100ca40780301d90f4a9110035042e002c0e1b9900350f00303064841041e11000d00039034500405c0c42c00104080d60707070344000c2d0b40e003403050071890b4061001003c3c0120504c62914045201001581c004680e6441d40303005200451 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 87555072 1250 87553822 87553853
    0xc0206040302010f091106031e010902070614090606040f060b070501020409060602032a07090f020a020f0c010f030f09080a1809020f03010b07050c04150611010603050c130b1c 77
    0x1803919030450700148048001c2c0e0381d11b81d01500c040d602c0b40da44290244c0c24601020800c0301c1d084100000103070b02c05041d0001c040d4244514018002c07201e503d20003040c01c00701500c120b1000d4100300300040580c1041d40c0b280c409280815008502280e41c4e82003425142d10034503081e200b0f81d400007801e000010350760160600800d041d1000b14070300400c4584000d8540300c4105c001005107104404106988000c001c3c241c084e00030500c1c20401c030b101030641d1800030b41c4200a2000980164401041100780119000743e8241040c0c5405000c9407070071500b20000c040d042c0180403010342c2c4502c080c0114140324040c01409100d034980320300020f04241c2c15080000da0b5403210030424010004006100502d1003a070381150003c907162501c8030402d103491810700c0380c1400410f0300300e841d120a0b401203100e403085880855140ba1122140c40303011585d12826038080380000740a952007005d408602d410b100c68540c1001542c10f00024040b02c102001031038020311454401007000100814031705001120083c1800d8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 87556322 1250 87555072 87555101
    0x312110403031d1f02010908131e0b0d09020a0f08210702031207020f0d06021902061006140409060b04060305010b340501020c030301030b0c040608060607020604090c020604030201 79
    0x18609110001d50b80c1c60600c85411049003050060700c503260700035040004c1440d4004d41c034070303120290428200c0500d00c9d1482210017816003111041074142510407200c09480380702c1080d0b0319008043d92071002500f0781c000101d8206d120300324006803600c0a102c11002404c0c030000075084040702207544410740c1200d40e003000d001c06807c125842c0103a4001800c01034450b60f0f01c2009407200d2450002801083d02c64050301d8000306817a00d0300c0e00308401a0700030f011f5030403035075000b45400007101c8081341d031900d00300c48014618401d032200f8420380340200100443c0341c0803070204924068480741c2e00c4040c1c1d00305520032803002e130010400344031581d0035015450140c0391207100f003400c0c00d40c0c41c0e0300e50230722422602ea402c00d080414500c0c0d241c01010758554010082e08240259507440c541c1e8011962a44240b0050b1000c810540101c0c4070501c0c210100c404030780a0340d070f0b0650251a580704011a0f54400342040ba03005104201c002154091400b41420120043c1c0151030341d442e0504010f07094902c1800da6220 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 87557572 1250 87556322 87556367
    0x708010803030f04151a091b16060603080d0b0a050916120204080f07080106060309020d1101030b09040506061302190309050114190b0f100c031211040303 68
    0x102000001c0e26484900c2c8030703003903c041d1074906004145444044c0031820340760600640302c66080d401541004250010354440b0010382d0340c807100150703240c404480d103c02d00104101000f0303144024000d008220380104030014020703940e1b42d83ca46950740f00103075186049881d040007015601c0c100c03100d140142420781e004456880d00030444900341c24204102003d1011009201040d1500c0b83c3c1690050303c030810480d1205a03002040c1503488945e803140b1a019800c2c4600422068424001c3c02c0c1c40990291014030301d546940d40e4070600d40407010119040560f1002241540e66038041a00e0250b40150040c02e25400d0400a02802c0c0c06403030204a441c0d8010855004584254520b440102409240002d10032000e440c2681c050074030040c8100318405154240074040752115049541c0d0301882c7d0041107012180b0061120700c141440c00140d0003941c0b4100c030744640340250000c603800752091420591908400051a0481d40c910304016030030310000c6024401c050300141d0520b040c0111800656 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 87558822 1250 87557572 87557579
    0xc0e0c04060e01110f030d0f05060402130b07050a0204110d0b0f1e0f0a06030501061e020303010902090414070915090e0103030f170703150605030403020d14090324070801 75
    0x2010944540000c0f41000011408100c107080c0c1404011340000440e02503d54644603006403c000c0c04403103011001c1c991408011500521b0284201e9406551810001c03041c949090700321004c17900202010744e15401760a100f20016503692046a0580309030201003500d8903149440718048400400945000c1c021880500e107040e640c0807002ea120040c00b1218620990020000c5250070904000c0c0070f406c0b1034182d402117040d1b600740d0405070685040b9603031002c901300500314001e0010031480000c00582c10400040c40440083e0b001420300000150000c00c3e4026254403107a81d4003402c8403140d00181c801c81007440a04042040c1001452881c500369020702d080043c0402003020603c002400e00008244440700c0c00c0c0204c0010101c054040d0f40c6401500e00460090007400c0a61072188d90003c1484002c00d0b41406201541d0085801d0340c01404ac400e1140f0701596000c0f041e440710783e007820050003c01c216950400c450600050101605e0701c00681850100200d44006440901800840c0e401071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 87560072 1250 87558822 87558827
    0x60509070c0b0a0603050f0a0506070504030c0e07030b10030f05060406080615120613030e09040305120c0409060603140a020a02031804060e040b090714010c080d180c0e0c0406 77
    0x2960907801c182c05042584602c00785a008016603817006140d800340c20070116507d0404210764901a000b0002c0e00e0441da1840750450311845140002410003034080e0040c021780304400d045d981d10a031681400603546d50140001003440200c0b071171850010b80c0701c01071003901840a01505070020402c1d80d06000c02da00300381015443d0b1030010700c542e495048020907003420780c2d22881005042440f01c4180c61203030816008510700c04200031000d902043c9924801d000c01d00304403070302031310407609580d40c0341c104003000c0740c0d00030b11070000703010003621003018000440c0441c0503101c0c0030000d1196440024004071303003806e411103003917006090300200d51040c49110481e6402004543c80324513510007100c5601031100004006166a0f00a11703c080400e80c10441001200c4100e14000c02200d801c5440f0b850f82c40013007218201c42c1400342e0340064200031540b00016403007009070425104144000c030700c0c50401104000b001081241c20350302c030b805951040000410b28601c103900003c40d0003100340f502e0b0800002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 87561322 1250 87560072 87560087
    0x17100501050f040513020a03050303072703020d05070806070201020c0601150203040308030a06120303091e02030c1c05030c030310080309150702220b0a140d0807031710030606050907 80
    0x26006075107510004005814003501c10179100e41c02040813002c40e8072400d080380c3e20340040320181d0102c0c010b14100c80009a4501d001d650750070382e10641c120707090b04660a00100c03850386034048817148034402c0e020484a1b42441000d101d00c640b03500058641300504a42403600e08180d0065070004000100140b915034084100c6095a0704a0704c0f035541d80d210991100700409040c0e1001203041480c151000030140d0507001522034902038425112074000405c069002481002c400075410740c000542c05c0d00b241400c1e04401c3c002007907507071007100c1705826450f0707117007076601850000b00980c00001c00c11551a554455a2001e071071110015803c0051000c0070902181d41c2c40341c100c060000204192003155200842c040500203090320101e80010600c80900141c030300311032142d203c0da0180e800840c40144046948166510040c01441d4a80842d1282081e40d4040c0c50305030200319002e0354100d02c1c0c40310020790a01841500600074903091450401c14100d071702682103284929103030010300c580550702048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 87562572 1250 87561322 87561349
    0x1e05191508120a02031c02030f01090203100e0a0f0207060b0102160605090103050c04080d0e01080a091a061c0305090a06170a1512060204080705042a03090803011710050105 76
    0x1c5440c2da404503d0010391a600895106265107140411019180801c1e0f4001d10b0240c40c80043c02d00d03103030340c0366810306041c3c0c0801c0310f54040d81c1e4444101048081100d83c05260003c03c46000000c18015040c2c001c0160790054001340c4465413181c3c4203d1865074100000d501001c2d8260403c8462420214014040d106440d0b110b8101521200030074803d0135608100ca0007090814200c484c100902c41c0b0183c41e0507100c2807014041602d81c0b00003521204240038000059034444141403041d6901e01c2c003070307040c0c403401b03001c0541001c0d10042220341e05c1645150780700c219000e5181d8a0311880038500b0004002c11a80000c02003000840c1384520000c018030003641c108800a0002c01c80d10803480715551640030541c068803402590003d01e40034844183e00401c203494445059803941c6495105110a0b611468a06849440304101c440c1c04d601c03a588a130714000900749030202e83c1e0103003038594900e0fa070030070382010710b01403041c24244c070190204101203d1221850a0b060240703600d440d002481406081c035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 87563822 1250 87562572 87562603
    0x105040203092128030e03040f03060911090403050d0b0109050a0b1e0301060306051f0203160c05030307030e030d0309020112020d060503010f270807061e05191508 72
    0x400c80524580c011090314101c00131813440880c07102d000c000c905038944444a051010174900110400703840e8010080307030140c40062448000d07043c5166903140040c071013502c00b612140d01c0c950b000c0842d80d80b00d021984c0514080d03a1400e031030ba002c0340c814401312640d203034140b030500600500c100310a03100c0103001e204581303074041150741710b005410408a01206004482d0000e807000800400e006425510140c1554420307070340740c42c114001241c40a200b10101c03152601507881880f03140400410010218126442841c640c507080b40d03914080703890b503000780c0e4045003c0b4401e082152442c1c1010003901c1700c2104c45d49000c1c8412500f035000070707240709191a074440301320307800040300da220f5403003900810700a04018000304002070003040d00000400b01c8041c42c2c803100030001d81c5040040c03d91083d09654580003600c044c9407024656809008009032485c085941c5c50b07903c000c45001d151486414802c0418600461212640409a00448012040080d0700007210030341405a40d000044462441d06880b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 87565072 1250 87563822 87563863
    0x207080f030f10032d02042409091a060a0905090c180f040b0601090f0e070807050a02030f07021201051f0812030a02030a060308072103050c0d0506060f040b12010504020309 76
    0x642c0c2101c15554103201940190034600002c80b9900784071880c041d03035050702d0106108c05468405400580b58206005407402240c055014107600441041c0d5400603402040c403c3e003665920100d00c140c4000b103030036641c2900302c1c500481e214201010480c2141d400380e01154490300e400c1d420f000380482d0141c40644040e0154000507040d034001c502d2900a01200c608205295980b22003050004008131091000600c51802080e0709600800c04d5411a205903005035080881516048960b0703001a0070503a400030172008100861402841154010f0504450200340400500903403081c601c0d150f8402002688021101c0c0e0060130b00070306070703130300417078200d40c096644d4070382c512640c01034000c54101030094800002c00800b00050313014409150710b851804c20100c80e40261080d0100d85c40ac85410003446010800c03080c1003043c0b6400198440d82c010500c505021160b50041d94913001a088007e90010004518440e045440c43c6580100f40c1201d0070f40c5503103013100c4195160442c42c00c0c0c07800d20300c045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 87566322 1250 87565072 87565133
    0x50d020d030e04021c05041a090706050f0d02040605180916080a090c150905030d0806040e1f0902120c0d0213140f060f0a03020306070e040207080f030f1003 69
    0x4680441700da420004000c2d0320000c10b509440d1000300320039a012140e2102030780030aa840c2c14020b9045101c0c0311688041d000b1035103010700544150b0701080008006440c10403882c4820403503440584046c107400d556581d2149132503903030300145040003c007403032040d50401c080050f0b108124400241581c0c8600e4462896120032415101030155400c00500c0d00c0d191000200d811401c140c0c0c0d0310352400322036880d8145540d0b14801c0c5900d07a161003000c400000e08180024840d400c090304aa4524100d00c81228094501d03407440042c15101f180c0410901912103c840d401e600e8544818046c10405e14080c20f541c0302417100250101c281080024022100148090504d03032145c1e0000080da1121031160a10307180c80d000e0752007240c0c1c04803881c5204401e0080c8005042c10560411025030b58041c004010a07154101c0550340078000180f201d51264080125100003040314002c0c11a0b411a8441c0c2500d909149600c04a8110006e205c0d40d58805515130400c00305400e524a008060021080318122048 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 87567572 1250 87566322 87566329
    0x140a0c030e060a05060112020c060408070219060906110313050f01020f03030403050405090f0603060402010e150f0703030501060816120605060c060103030305061801050913020d0602030f01050d020d030e 89
    0x140100007240c140203101c00c102c18500301e50000c0e442003000742d9500c035440001d407400c0d03000c07070003010107d00e520b500c14400030300029038080007803000d070b40020306503078080454800040080029400410000e4180c1c4010007489070848001c000494408000c0c604218000780c0e0300040010b07034070409206024142d00d13540e240c2d0080c001449200030b010141d903030303070b207070a040103042d9a000b41304044c0a0001030000032504d85041840b5402130b030000b009002d40362100e400440d6051041c980300c60740003d8611039200d0324010b402c01482c011402068003510361003c6d00380070b400c46005900c0141406044010000c3d03d1542c038250035000296030412455070585000c210006000c01d401007a0026030002d80320003134210025071141240d100e5a0180a43d55960302440b550220901004540703e0010b0010302442c0303010384095501000590051100d40c155130001041c00e14044002e680d030940c0001800f20b20684152583e014240c2034484d11643c803000d03404034045880c250340140c100310141c000c0c5126640c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 87568822 1250 87567572 87567581
    0x120c050918180316021905010e0909101805010c0c050a06020309030f0c160807050109051e031203040606140607110d120f02011401080316052505030c04140a0c03 71
    0xa02c41141d0702c42d60101c0c540c56003455800e13000c1c1c1c814000440c0d000600c0c80c1d0210740c80b00f0f41c0c80680d12101c192403020f041c09444607003c6c00318461402001019007500c4c42c944103603042d90404140b055802c02a9042050858a18201ea10204603031010a07a010590018447c42c00b5580b1440050b074030b548000070141107000d1410120601400004c4068079041c0c0042c1403910203072107007001444282e480355000c1c0d482c502d03489a50f000c103440b2101003002d4544240e0070b0984081c2c0b85150504001c00700c000030f0500c090302c482ca12290101205100c180b00f000e00c500d4024001c100d0f40c4417411440140000c055000c1e490004100410000420019031a0070a900c0c0880b50300500410300e02c010808060241010109920010b603e09504444483c2124400504980c0010041c5140c090b1505060008030500d50069403248100c3c10005081091642c0d901c241b8201d81500628850030b0604041c03c003030381c01c041548628103040d200403078000c1c4944180d400c000107007000611b4107540c090550280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 87570072 1250 87568822 87568861
    0x21905030903160503010c080610030b03120f04031e0f0204020a0c05061602010f200a090b0d020a1209120315030c030b01050301050606070b041e060c120c050918 71
    0x5005901d14000030300e01030300643c002c0e20310440c0207018180203003a0403100001c00301d071256485080030013007841240c000d6110500001d0f02805407103072034021080c4100740d80d1258404030205100000c0c1001404000745840f20203c1c818000459010b59075103c116036080400000391160368000381e030190b501d015800c02c1d60b034282d10006445032440c10504000304103820394003890141d402e0042c8108010300920440401c0a00b03406a68490a900e4890395400d400c04e02401d03043c04002c9034045140c01030307100600401c1c000020003581d5070004031401060001c4441d00b2401c403d080c543d43c07a00060300c0c032550380391038101d524000400e829040340d1144400c0c0d07640d0010300310404d0b581004c024840342d070003000d0584106030002d0001d51146814000c0c14071500f80060301003900b100103e40044c00090f240c42c004280d80c03000145140f51500c03000203e801c1e1202d01c10109102c04038800306120700e8000e142c4510b405040941c2040c8000300441c100d03d010f440342c10f40c01248000003078228020a03445440c02d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 87571322 1250 87570072 87570079
    0x50a0f0608180d0e1c0305190201020c030304050307060606050304020603060f060f0c150c13030b060a1a0901030c03020408030406030e010e06090f0c06030106170a090b10030c0b0304030219050309 86
    0x15240e254090708001800325038a000d45c109261540d034402042c1072441c1c1c0301d0b03495941c0a01c0c040c1162a0500c0007034040c8024001c41d50200244007001d10104051402940a000915130341d2101d450240300b00c5010f60f12507400d009082c4104405a5140301c01c0d00d0344100c0a0712880101300301c00f030008866100b0604900354088011500711400c040006080b2403081c40b072042d000c0d260f241c005036a9007a000d198201e141e80344030903100b0b000041c60081d040380c02c104007134405c0846580b901c0861881c503403030180a00d84400c002c0b0340a032a070340e4980030b0035400480d1030030114542410b041c09161070f40301d00d0040c0c0081c03585808040001c81002d42c060751481c51258269060703400c00c040343d0b0780c940220403c11079107841000d59680d22441c115003141d048907081d1b224010310f1b002c00640840c2907507006000481c00c5a98a9005001c50400c0c00414172890100790b0300c82203141076180c401203050841c3c110000c00141401080b00103600050035011038085400c00c40328660880ca006440d510490301007641 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 87572572 1250 87571322 87571333
    0xd0908030a06030629061b06070816030c0906030c170408030108060705030c0702090606071205030a1d071e0f090b1002031806030a0e12030103030207050a0f060818 72
    0xc0d00c0d101648242c0542e44509824003082000082c69400302042c484400c00d0900030448800c400e1034640010720500e910070107102c08071000c1865481c1000402c680380303000b15100d40100301500100c42400790018039141810060081c140d80c0080c03401d00c0c0e0340a000d0516554543c032020480c012207036048800c10306440103881c1e19281c58800b141d50821300c00c050303d910a8601154000b8000c40640e8400c0a0448030030342840d9203034007008100700d806805650061b8080068801242c640d10300304090140a4450541c0ca04200039210101d40420017580301c0c1002d40c03048100700b12000708048044407480c050038120204a4151505075010541c06a10301d5085400001815020f9810001d94502e04441c228119015944160389138410000410405e421114220701c1902d0607002842d08903100040024000c241d054200b890440d41c3d180442615402100400030103504001d0f10700581405d455064560b454045000e0803402c990080c1400c2c4401c070000280e0380d50000c007000c401d4450140c100c03007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 87573822 1250 87572572 87572581
    0x90c0603011e05090c0304080a090312090302031b0604031202120c0d020c011d0405070323010e010503010908030c0d09020a03030305100f0f0509060f09010611060702070f050103020d090803 83
    0x10350790002d120250503540d000d000192494100440c40c814034600c1c3d1098a1990399035285c22059011482d88410300500c030070044045100160201c511310a5606c1d145051400c5004151810340c15003021202000300388100861a00e440044e101265401000f12040031084801039040034500d028803801031901080144e1241400101c0c98800318480d002d9441c02c1848900459040100070001550000b015924080c90304050780a00d5211340e9174980000c1e00c201c0a100c1842101c0d500d04550784240031440148138080a0495080c01040100c00810071080f02e07649014590100501c960402400442c0501480c1c105801c00a001ca03030007040080031540380e1a015004105c141c450180d401800740005c00d1080c0c104541e001a5080c0140b4034254034500800c00c54a00c2005003001d4101107070081e81c005903214500068041d00359a00c50780080907000e482d15260090060110307003107601c1040c0411000c41d92010074400e4410038039002d0382c1c1d403c040c80160042e007001c0030024040c080000800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 87575072 1250 87573822 87573839
    0x30506041b120207061b021006080a170d090c260316020d03050d02070804061d030304090f020d0c03021e0a08040308130b09010c0905060f0a050c120301080c1206070c0605090c060301 80
    0x11402c400230002c041280988801800e907560520440041c900d040c0c2409800c420071256026141401c038607880800c2c8048943d913115104401a401011000c0e807500c02207220940d000c51526540c1309240c002c6041100c11031090900e601a01d4029018640514100b028544144103c803581c0e41d6286042d541c4640d5850005002c1d4028800e007000207000c100c1400d0820340c2d1400103030540100400843c141410300388a10300800c05015000441d81d400c0040140d0080d07a409640407500d901d4400688544c403040090060880b004000d010801e410490115015040000d20f60003680500d007030315842d5540d9802c4da0303040018800290400c001102042484d00054010808202c030559031041c04a0b9560180300650081ea240c08107490070a1002d0303000584030300061f205084842d800c0360400342060f080c84100d68000c4c0c014140c0e58100c098a1482d41c2082000e5030202c2c0100d20051105152042c0000c080000c0c03054010115070300d50001c511b82800030004e44440072002080717150b50f940e40c1c4504 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 87576322 1250 87575072 87575083
    0xf01020a0b1314031e03060d170304290109021605010216050705010207030c09020901020a0c06080a060e0106020a120e03011103060a0b03090a030f14030106030506041b120207061b02 80
    0x45030a115070318039007451680c02000341c2d00c000f0204070014011005c64034003213010b900300801c000d40110705805a100400e020a010b00702407160104042d603a810182401d00311040d8106a000600441c400702e400141c540c1c03c001c03811588200320050b00c03010416115000500c000002509943c0089480c50300d224040c007203000c07414402c03030881d10003564030801643c1780c2030b0500c80504200b48040040104d43d000707030024585018148181ca4400149540d032000c400c007290030480020743c001c1c0c10070a100c0528414440075003400101100590300d0564001c1d9103a0940100811422504580083d1140a80c803140e00e25007004000703218400c400902ca1849400894580384107030b07425000018056581d40849004900c800080e0080c6007054509540340d45c100036030341d4108803480340c10081064580c00079501a0205580205240c1802002c01c800e89540414240766559500c80381c2d070100341c2000c240400e400e9140d20151310303908142041d40060440d141c3d0513580c00080752040000e039a02050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 87577572 1250 87576322 87576361
    0xf08010b100206060604031103070503061008060105031b011b0204020f120c07050a03051e03010f050f0a060f031e09060e060a0501030c0303110c0a03140c0316050f01020a0b 76
    0x1010041454000c000b240e84400a4418940010f0100010310102e01d0402503402562405411294502d80d104c02092424070103d5903155000c1c010380c001c3c404010305014841c010700c002c17002000c190341d06075101c01100780c0c9400c0c0141440305098046694500050b046500c480d00103104540300d8801c0c100116065100344602400402c8410000d0080440e0b18155048590450000d00c1062042e1b5400d441342c1e4044003100100f805030408400200282c41f00442c040c01000040710003092509003446a940540105a403040d01c034210309100c840e07030090000158031914600807030b03820103901c00100512030b40d10011451a04045092040c02015004070120809040841d090355135140380a0048038401c0c04024a99200d0304c1040001c00e126040d880f52000e2408280c54402c0c0004002840c50b0075154012a60310280350ba00124181c001c0c8415100c3c5039003076012f48003103080000103290f202020f00a4a21844500a00c11016403003000202c2451354070904822441c2030a03140102c5a54103200d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 87578822 1250 87577572 87577579
    0x140f030109120f0c2607050a05010902150c061b04090513030e0a060804030c020406050301050f01030b100b040909050c030709021309020405031515060d15060306030503070f0503040f08010b 83
    0x5080038146100e003100ca05055000b40c6440705c113803000184068172070b1101c82036a000c60402e000040101c1e10520208040601c40c0000094001481c41408102c840360b2540703156016060110305040c09002c074405e640500813403000c14614000f410b0300c0c034482c002c03078022240c503e14200810001101404900c0311060003030b100c007414400031a040095000c064000c1d140001c0c0110046800a0b000710103070010700340f004201062075501c4801080c212001140c114686e90500b40041013802680029581c100805900108000d030424403440c90301c1c8030310712466131415642e1443d101808802d11400740ca011005043c2c0e10700d01e0f514003001010b9001240280201c4101d420006810b205910813241221000340103444983c0347c4400c1782420510081004c5034213206115490b07600c0c0d58143c000c0140c080d5503200001d2801c1004e040010b50401a000072080c1860040144086400002640c8119a10007445a03100859240c01403d5000350b5114011240a008010440c0c003019080b0340303404170056 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 87580072 1250 87578822 87578837
    0xd0c091a040905100303020706030209180c0306090f220602041a3103031803060203130b060415030b0405030d02040b0c0610060e0d06060509100f06050a09140f03010912 74
    0x104c02c5200301201d6440000d0142e0b0014100708040e41c000e40107089002c10040070f40c02030800d6507100030042e850450f07464810b602c0000801c000ea180100045070401c0e510050351801c0d00e041c58000f41281c0e00c002e21010350320320240802c0200099901140c002c0c081116a8000c0d111810054080540203007000b090082003421031090007081c079141c0b8140d0300001507602d0060901d1034400b9601c1c04d4004140800c04004400044082400341c0001e6000e80c954603e48114610181094800d048015040e14802c80c1418280907804080b05210410351750801d01c2d170b0703080d51034070314081d85103204040741502194004a00081d103800ea031000b5102c0420386009460341580d80c4100284240d03000e009950102d0b08611951107075003006070301a0140340c070482000504984540c0001c034820f038211040e4a214450030b2045c80f03241183d040120003400715040c12070030850b0780100540070700c1c4140602d0305011440c80c2480c641d640d135030340814180140503008000e0403000707041c02900300000c0c0111134042400b9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 87581322 1250 87580072 87580081
    0x9030f0706020609012c0a1b060e0301141803160f0c08030a0f0e0a0302040203011211010801081009060b0d0501050109050105031b120a0c0801050402030c04020a050d0c091a040905 79
    0x601480c0c890280c3d88a0320841000d88620f4404c24420344904411580f060461640010740014408e041ca44840f5904480c0c040c50448020503000c0315013000307402239043c500040101504400c4554011540c1d0780c010401101100340145140980450510301c4504403442a090000c0e046410f607001d801040d030300b20b0b4039886211881e581c0c410600d0500004a070302c04080b240343e03c00ca14054028100030812291541e403600050240d0f00300307030414200c60303c440760500c00700007903100fa42c80400d07020b00f060725496240044454841d00d843c0010158142c903075054601b08441030b4000c9240c55001045091807406c0c5092a600801003400384035201031500002040714900003800b400320040402c9601034010b101014014076101d400c44d40c0415100341801f0074000703581204080064a0040c0000805240500405161404405042e03002d248104030320318a282d4032404a40c440c00c6451804200d4022100044501207025031101c40c11f2640215003e400038004c1e0000e00884810400510242d00c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 87582572 1250 87581322 87581341
    0x12120306030d050702091302031f02180109030803010b031b03180d080603030a050f0c0d0c0308060901030b0a0914010f140603060106050a120b03150103050105180d031109030f07060206 81
    0x481303401a50180f406000941902030392070b028011680301400351400b49032480e01441420346c4c904500d410782c0381c000c2031806010040401d405901c04007468003a0043d8034544817510644418014106400b000000182d00003108410a5640c88c002030f250030b0392031070040c0b008800046042068040b900804100c400b06078490030910740296001005103107404210384c803c0d20240e1007200c00c2c3c8040c000034003804608100502c00e04030000d02e2600c40c1d80400907240340c010001c4038000c0035239201c0d00070ba03401400030411140d2110381c009064100000d1080c00f5080c901031301c000b48401d9800c598200b030164120b00c08207411020040f5003c19440b00503444000070113440309402d006e800f0000c2c00c2440980f100724801c0c1c10600300e45d0029540000c100100d000400c1c10402b0400b40c031a1135012400040003008001d104041d4031122000c080c0f004603003040030280c3c5907241100790307804040e21041c0191541c1d44003011519646070013011a581350305841c0c556034840001d44100340150282000003041c118 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 87583822 1250 87582572 87582577
    0x7051504021906120e0c1002031b010e060612030702090403110d0519180b04080703031101090f020114160b010f051c030315050402121009060501050301120212120306030d05 76
    0x1011611034003004c40008400b13400500760031750380030120702c100840c41015481e40040100c0c0f14019a02541d59040ca5180a1240811684001d030007a890501c6244c54820046012500b18204450200512000d40c54092450283c84000f9510003540701c20f00c010560049001e0030841042c401f81c428440e42402d0a85807800f60612641012501d07000c080c0b80329100740c0e80d49802c00d520110080e04503407142e0080915800c15003260195600c4a8000d10038950000198907403840700c04004c0c03103820301d182d0751400708901034000241441203c080000103049010141c4440804040c1461070b034040904190b10090020720a45582c00788115010400c1d042c00c40c410204440c000b0003500c075112041c2d070120014015800080011041140e0100d541d43e6140010014040080004d400d281404410209510101e80c84a0102d9107070007003c00c903907600103054904607000384480003000030042c000714412000e40c1800c04218080c03a8049041700085102035802444260b0480381e10000b100c2c016142407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 87585072 1250 87583822 87583829
    0x1b17012a020307110411071a0105040b031c120c03060302090601020c060f0d090803091b1009030311070b070309030302070605162010170609101802070515040219 71
    0x40c2c1003002007801180e075042e4580ea80c00c10140c00000c0f500092280d20100b60441e600840d00054880d03000c507401071450398054094403041f00c040010442c2100001e54614208000001600f01000291241405207910303510140c00001c0a1100c528107040040c000c00307940c001203204080280c0494159440001d680e00151030282c0110300d0403100d010120b0045d0084850004034a80712540000040c0014001d980a505003400622200d00c5808404100d128201151800340440c0a1a150800c0d071040003041141d406003011041c1c1d0421080c4107040c403049400c00300c4030050001d80303a41055889203c00c800c4034040d0342901d000603100c07401280c5034880d01c8003021500c002a080c00010032089444880f443c00d991040d030031102041c0010400341840b440c4180c4c04544401511001003036900380780e44d440130301200c07040c51030701d00180400040b003220300982c076203061044060b408104a0713904039950130703402070125403c3c841005005036209504580403030043d42c2c1030304c044015802c400c100d502038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 87586322 1250 87585072 87585077
    0x31207061a0a1806050a090e060a11091207080a0f0c0b040f032405090106060306140a15023f090f0f04020702090a0501030209070c030c1b17012a 64
    0xc1d00e4002240c4144160f80021201c06640310400102640c03500400e40003031000745e60100b081c4103035100c40c40c10120018400171190f401c06080d0041c8400c004211640446c045800d12010078898404901c3c0000030b401005841c072a900c01d107421300040c1c08840500d40c0c0b00d8804440600d441e03600c600b040740590306c03130021001803840060000455114065001596801c220301c140e10802111310b00780e503c19180701d400e507507442509002c003075450700070031000d404c20b103108804c03440c0c1c4000072420440c0603104119141f40c821880c03007c018824010310407140d00d0801a01d02202006100200e00360712030020704100c20010a1000d0105841e0003030790020341000f04031040140780c00701444504c2e85e0300707040c169000d9401c0040500580e114424103004208802d000a140c1d811441131002980c00a84800c041c01400903070b100019038403007054000c4990150b00d02940061403040c96881c4d03c4260416192a251b4110403011903c055000c4d80c040440103408009044030202c1074a030780d5500032241c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 87587572 1250 87586322 87586339
    0x905100f060206040803150618120d050d02130503120904060e1911091201060905060607020303030705070614070206040510020c0c010302160b16180608180c031207061a 74
    0x11981205c081c55104201a0b4160f490b08040340010f04141d102d48c1110180031906e00f59401503041192400d15000d0b203900c014000c00c0c0c0d403140c0103841c4e4044c10074a001e4a80e000220034194503007910702c01c0c000740b10180c111041141c1982950482c1c1d040103400074040c91520b40c00140580c0c103041e5080c028528248184014082155000050403c0c12440946120300b0000701c2082c3e203940406e11070600503400005180d80c10310085c5400c0e02e03000703010b4a104600c240081805030f58044101d9800c51305504101396507c0051400001420126400d091442d0200c010010044e4011881c148a14880c01c10b841000d042004d02504034000c07103206881d02c2e88810052000c550007a07004040c5400002211786040130243e484503151034040f9004007003c141c3c036a50100b540c0e00000324000c500c00030061050321a00f0f00703000520510000b00003041d500303280010154246814424909815006016185580919601c00d10240e1008034111a094984446008080c0d04046958a500c1c0002d00f0280c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 87588822 1250 87587572 87587581
    0x9010204050609120703080406090e06060a051204060605040f020c0114090c190b04140a0609080a0303090609050607020705010e010e09070f09080105070c020112090f0b150a0905100f060206 83
    0x43d075000120820444ea21407481d021000c500288050802072400741d555400d142c3c00c1c02444120803c001e0284d42c0503100602c0b01d83c08040d0007500f40c4c0c2c201008603d81c0d0710199507030304101010340307450b600c4640c01c50320741a000030a201d81d623001854030311001002808103040021000381c0c07600c02102c04201542196075802142d1074405403440d05c43c3c0f04010213002043c2c40340301d030f48881d611991000d03620346192170400019050089040c001000281072804810f85040f283d5915620300d01802020103503a10316003020064a03034456250950000c08603219440e02c1540659980035500840b40811082e0035910300641c4540c80ca014880c002501103281500c0d0100256000490312220800740011f0075408211540248551403040c03207140d44071240c2000500001d8805800d03402c000c0201401e05850308045902c1c0c42503100b10700c0c0e006005404039501c85462801c0c88400403401c039070210030340710005a51000c035000301f4026200d5000c44004680e42c3c3c0961001c00c07010388101c034003580001e03000a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 87589929 1107 87588822 87588829
    0x40305010213140d0537060f0f060f03021002010b03240c04140f0105090604090f180510090507120b0a0509010507020309120106030813030b09010204050609 69
    0x502c024441d2903607070b140c46061501000c0840c42034804c100c040101a0400380c040c500000c0481c6c82d031180d00c4e001020385000c4020203100c60801c80f111840b0203040c03250720b003110103928040300124030756404d00c011071500100d00c10a55585a0500c503060b00d042c0010581d290101c1c2d58070203400c4d44028039030031000000d082001c1d01e100c244070a01144681003064203c50300111111a404171582c00100d6451081c0d0324699000b4001060005048031030380c04c000414200b450b0280801383c9826010354105000c1c2c080501130350312074200d0441c200d50650104240030701401c1034500035500c1e060241c0d01d40030039100880e01011800304104215060780319040e000f111900c02803201c2d0a180200964034090407006c14840c0d4503105100070400c0095005500465101810300c0e01c540301d11031b00b000312200620050742c4190407580090040f8030107100700d40546e80d0040125040118840c01d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 87410072 87589929 := by
  have h0 := BRFrame.cov_init 87410072
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 87410072 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 87410072 ≤ n) (h2 : n < 87589929) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
