-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2797
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:24.524866+00:00
-- url     : https://prove2.me/submissions/4e2c9517-4c00-428d-adc4-c45e07d66e46

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 502877697 ≤ n < 503057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 502878947 1250 502877697 502877737
    0xd030c0213290f01020d0f0c17030f0901111306230a0903052401050609040e010f0f180807081605060406140f04020102070902072604031502 62
    0x800c5248880080d101140e5552008009602c02c2d02e07680408011602c000d60785261203010342403240782c010940ba12410b6500c904503a450803030303024603c5c031141701491603c284e448100749440c0315280b500740b04140e080203000c0309010711755028810f1103016102ca00000c0094010a01130304800c1e000303d038100850b440a0403800c00403240504c1806000d203a2100b400300c1c0e880d000d0740226001390440010800021003070355080c010840c0401400610b04410a0800460350004103285010201400341c00d004072404501044c16071125040034080d00600b100078400206440201401418800c40c0c0d11301150802040359910351610102c2c0341c0b400d0b04505814036092254480440310341c00440c2021034045080b01003004a0814803078107000310700c100b0700410007110070951400ca07014045c00306400310044206000c0181c0c0c00051070000c594800c0d00140c4c0f00d1080381400c005820907072040c1e200401924440051000400c0d00910650f8494842c0c03542183c02c0d02c034800124003031100c00525440c10101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 502880197 1250 502878947 502878949
    0xf1c0903032703140c0f0f070509070305160f03140a1a0901080c0d020102030f0a0c0b06060c0a030311070203010509060a14010b0301210f06140705120f0a0e0304060f020c0d030c02 79
    0x100100a566000c0b907405d034102d0320800b447c3c0302e0000400602038004a4040c84035240010049400030868a0107002a0070140e560f0a4000d00306c4411f181480038001a2900086c001d4102e41d000645101c84401541b4041400354050403032541500d424036013580d801a000c0c43e06d4031207a8180d450386c000820404401d1820300403011a441c0f0142e05500c070910060b1040401075004006082d01552417110700d03045880c0800310042c1c0649190b102e14810710241c480d9110000707a10342107030380500e00800d4aa40096404600d4441c5050194140d42001c00304030004000185c00c5001c0c060260042140c04101c82d25604404800e01900200e90001c00c010481040100070000c030040e20641900203d80315640d80d1090112004401c40e00640c464128413442040100115400729143c01d1072407038288400000184510000c0c84040d0741103907075004c04e54079401170744545101c181240840703540701d880b0300010f03058041410400c0c00610030540d00c0e0940c3d083c030021070440785926440b5500c855809074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 502881447 1250 502880197 502880237
    0x5060a1b050d0902182a041d0a020c03040b1902191712070305042006090105030408070534030803010e040318060e01030605090403050f1c0903032703 66
    0x3070340681e480740d01400540c41040b8001c0c2c0c164055140380c0002c2da030044502c2d140300703801081009000102ca46c188800c11501003541c44101e8a03000313a03101040b8903035545000c000240500164041c5c24400450b011800000080c002c1800c0c004000c89000d11003000e000490399501900c1c8460f0b2100c888440103400a980c0b18440f00100c00e8030446c2e2820070186940c0180c1801c4112601d50010303407240244402e111602440030002c2c50b54101310817110200c00c01095a6201d1418200e0400100100040c1480300803410344c2d100750b40c048190760789801040301d00c0d100844440ba403100f2129000c91801002100a84080101d03540840f8860640e86009048001e0500040041e424403c10000c0d03002400c0d940d9942402801c06911084031180304031000508660283d0002030061749000180804030780c01c0000d8030b44120404040503602c011005c900b26082952040808101d03051800100825805410100180305098444102d44400700c400c0a40c070400a44090003248001e0050540c401c0700e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 502882697 1250 502881447 502881461
    0x10f18080f160f020f0409120f0e04051509010e01051c110a080f07270c05070c0303080a0e03031b0a0e03030d020d150605090103021c0905060a1b050d 66
    0xc00c660070700302500b280707003480302c564041d000700d45a001002100c0110b251221012031017101c1540d0802071a50207941c0c150b103208162482e2014008149500301d0b607588668003039110504080d10522480c24203076483c1003d1142a007010784030349481000030400030050071510b41200c40080140c2c031020aa205445203000541e5002d03203040030400741c20415521a0040c50004012050003841100c2001c03010703074202503941c3c00c40b4840b07040e41040e03020a040040b4050501c0b4030709041c002800344214605030703260710424034000d003030000c410740010600d86c01c080b02c5486104802410721401c07201c000c0c902c6c0c41c0d110031128501e40c02286038403c46520710320805414032544508100c01c80c5030140b40003e10b9504a0358081108680019164030305900a0040c03241081ca680403840c1001e08002c1d0207080ca00608031224101a404604088808480b40c603545034030440c00d40c00c200042403410700c03944400041b10b00a900070301b0003601290810b00c0c18031000480d0029a42c540c00e0515003042c100240100c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 502883947 1250 502882697 502882717
    0xc020f01030e060f04050d031a1c050f06010603060b030c1b030f0403082109060106120f050a150e060109030f02060403050609060f090c0a0308090112060f08010f1808 73
    0x1440d00050b1100740108911030203250010720740c109515003490241d1800800e04031010415040c044420201c05000c074190304c0e9114100c4010440c44415030400c01c10101040c0058070600c1020101c40c50110041040e6068801680e03040c4009500d40b000d80751940300585003150002e40c200080340c07510f180040d6080000202e1f400380e0386030010102d149030168005400030f40303036003800082a0010038111102c0c42820207409028442d2842c25183c03141c0c5580b030511894081c0144030003181c1d00005c2503800b640c00d89408a00400460400c00c546500901d507100d06800c0c0c4000d041400b156076441c0d40c644c00e1040b01c05030343d0b94200505680c2c0d5844410000442260402800d020201c001841407242e00d00c14021500240700610344070420012051000c0c01c0001d45400404580c003142d05e13000c0f401d000340c0f5001405259501c9603400101d5000171024240380710703035203010004600c03890844507000031100804000e1058006083e022400c5419400d10103176030b100031985d41000205074002501d0040b00c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 502885197 1250 502883947 502883951
    0x310150f0806040812061906120506040608060f041109040803161e050d02070b01030627050a020405060315010f140f0d0b220809040c03020a0c030e030a14010f0c020a030c020f0103 79
    0x407c1d03220340c00c07200001d0b42007000801c10410300c50305181076034400d540d80700b6800c03101400080c2c640480740e0b4803558080c20188817465840c00003800c0c03165500b51503498200c090034681c4940303801e00b0030007219003043e500c0020320040c54140300700007072080c1180070000d0820001402070701c25a034402e031a40d504c90240c0d40160390702404a07402150400320143d0080d4007502001c9540d03a1000928005500e0715002101d4aa610a408002240740050101170313440d81030f6000503058503844e00003490407069407414070200c0713000000400e010854041e402c046403403003040718906980e0035040098560f010303100c0980040704d044e6a1800b00c0c400550301a00720481d44162511000050b4502c0240c819414059809610004441000c1d0034144207030300b8124030500d021800e1080c0ca4000801c4044120000340c00c01801c0d80803040f403075809104400e101b44d440799101031903000c3c0303a420901070146010010103d524001000f1000b90010a03545a00780d0315654180c0e09420a82c20414200200700c00181099 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 502886447 1250 502885197 502885219
    0x4121e1b080c030406090f06050f1305030604061509111603030e03070f0c0f030f060b0102010f090b090c06070210030203150a0803070512040f140310150f080604081206 74
    0x107034428008110510740b55000e582d4441c200b02d070151800d01d0550012500c0b034010740e0b0400c40c0c00e500109407039030416070b03031800f9030389500001c2c401c001ca41e80e50b00900c1e454019441400208141a8001d1000349011305840707101984d13981c0c1401c222458100702c040c2a2904003e4a440c3c008028448a40381d842814002003109178a03070424555080381c4002c0b99101908030b8880c0038007900c800442e005105101110341d2550440ea9501e0a03071581c50340c020700705070700c651000810303038000e4010110b1390860300d0041005150320709043d0070405050300e0540c1140901c100021281c140070b022240b03402d4002e0541c0000c8a440c201c210002d40c002041d00e84003408421013501659503000e0705400504005005548941aa0800360306110310810128800882040200800079601507103100315503005c3d0046c601541d89101090030100310391240784a00c0c0c03074114003204040302c03007a05000307440307103010501c42c103503201c0b00b24655961083c0d4001c0c0105030300344441c1803110502908542e20140c0a4122110340c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 502887697 1250 502886447 502886453
    0x302090406090512070611090a09021b0d120b2e0c0b0708070201050601031b12110f120f060a350601080c0307050d0209040c030b0a020304121e1b 64
    0x900901213214000e0700003d240014132040740150308850301000c0c03581e860110b410307001406000007441140046074001c42c150501c1c3d0001440d00000d82080e1050340e0320600c030f295008120f0240b03160700e00b084030300e0241130f4501801c011540c0000503d4030040b01c000180c0b040d030303400c400c019030341211002c1120102086002406a1209a00910301030b191001d46027480180070b0b0a5607001400030b410103140c506c4c3c0321803040d840525641001418104007920202d138142d00701c007a00c41545540d4449900007402c140d01e203002001420031176070500c0c00701c40382d03220130800c540c2d5140103a5200ea400990b113941030002c3c00700582c40d03410324802c43e0840d98440b02160082c10500710010000c0c00d9a4200e500100003a11043c045851400030440c0a0f212403030a0000192100c1015000a8001d524810010b07080101c020303001d034003845d00612040800e10f020380580c400b95004840459402c94400c14051100e40100802c0c01c0d407003004071024000000b4004200d401340c0c031102c038800740c0c51110700500b804 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 502888947 1250 502887697 502887703
    0x20417030f12040519060507030b030f0703030f230702180f0c18120105060103060f1a0307021e0a05073003030b040213030209010506190f021212270703020904060905 73
    0xa80c0c446c040102e15441d29010181c12a0400e4078000d0003504107028607080b018002ca54070040d240d260074980f441c100c1c603003c101c81046851000421103203091038050b001604550141c121030f4422110070a410951340b000b101400000c2d0340304034036140c00a0204100766800c81c05412a004864207910241010300001901c41d0301c3d000003d05035035520b0052050702d50341806040c000e0600701b41a1074039640345c0241c040c01204401107039184100003101080c0581c0c403e21901c010310700c000075405104914440e18607154003d1410859841c800e03007000244c03000301c0c0307080d51410102518650502031440c1e009000070229610303040b410141c0c0d40c3c02c1080c09607500c1c030241005055982e071020340c2ea8154030510052800603007100e482a4400e21419284c25010260040046428a8414140100c5110581c0741071508800855541800300e0301110422501ca1107620814582c0100b42642c10140764a40b24072056000940341900480c40a1001d070424010311600140300304d600041850300e42c1c503641d003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 502890197 1250 502888947 502888993
    0x11a0d0f0b1008160e0310050a0b030d110114010609090e010902062101120c1a16060f0f06050f04090c0503010509070501021b030a02150c0d03020417030f120405 71
    0x1041050041c08804c1c041a020aa45102c142c104072503a04410000296600100c00034a82c0407034407000040c007040d040b0303041850407240286c222202409810005003a0030030020130032505d981f0302049055015080840701d81228015155800d0f080d041034890405088544c60300446592940400d000584941005010040c2e507540001e8440c00c9588255032800c806900029080042c22a0f002c04140c240a0070400c40300041d815a1040d050f01860074043c0c000c0c002c5aa4030800044450b03014080290010305441074450010010b81e04000400c0040742c035503006007a000814900c000d040b60405a0005070703107034000c4c3c0c00500307881d40c0d880000f030039180308940403d01034122084c100720950b010010040160420951030702d02d440104003080da6041a180040d01c151146800040d5035180310701100d000c0150082510040440e400010340a580284030f80c0704040010380003010516800301c1036450030625808040d190040500e8150b08110380608141c80c28000e045c0d80a040c0780c66281044 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 502891447 1250 502890197 502890229
    0x150e010b120d030f02180d0515071e17010905132003070e0c09090a111318020a080604090204110301030b0618010b031b0c070803030f011a0d0f0b 64
    0x840520342c00342008007500d0780b90300015000c40c0180f104041616070b080e000d01c030111044d2840307100b01805007840c42c50029410301c941441a8003130284030050f94080e007103056420740c0210780a95160300880490759070351111041c0740d406818a006026003503180e0031058002107230035100408101c840c0c5540c00c0040740c6079400c86000c2030010130b1890038141404201c0c02404504900c03500b51138000030784550303481a43e410600c00c07400c1e2400070300e06400315030007100d00c6c0c04440f485a0300c5a41202010705820400c1c0106c40850601d150110104003950088400b4168507036180a03880c0c840b20b042c000036280d8260102d034840c2e00c800b2407205d40c01460016600850103542d95007103038100201401075024a0304840540f0204070801444034802c3c91007183d41280b901c820701e0b510798010900440c04c40c0500203201c038060081c0600010000000009140a01a101650411640e031000480c12400100000011782c1400342700c241d001e61402e91214a0350440548041100b0b828800091120486a0102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 502892697 1250 502891447 502891453
    0x21050a2d050a290301150e0403030b12030a0305060d060c0816020312070c0c050406270b0307030314070503030f01081006050102071701060503030705011b0804150e010b12 75
    0x140310200032034080d1541011800c90100080d00d01c503207058072840503030000c50411841486440c46144c50962040881e0003420b128101c00c25120410000c2c01c24040c0da01780c2c002030800c0b440c0b42c194584401211a0112494025440e06415440036805400010b03c100c8c3c2c095074050729280815900c0c000c14490b44010f598603500c9261181d860913042e542040c0900441d03005000c509076440c0e0201c03c294001c40c0034203107100e94615500d400741c820509504480c0e041400e014000039001c44004440d909030005003a4055852901d6080b14126841345107440e9050784403640800c04a401985601c56081d50b01c0501e40c074092054071603900d540d0054850f0461420b080c00104442c11b024051815030b01c0003000c050000500d0240002d60780d245034006e501c40d06107146010008920b095105030002c0101030203a0f03807103005504000b070080105845009000001d8614413100030b00c102c210900c115070001801140c580c0500000000380303c29940070f05590b58500d04500c0d148e43e5003c1e8050140c0c004401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 502893947 1250 502892697 502892771
    0x50310022703070311130f15060e0609010507020d06180c050603252705010e09190b0f030a1103011512020f0613060509040c21050a 58
    0x403090072140701e0a048800d0288844560180d030390100e80c0c0421039410036446903d07550000700203440b00340a403290001407441c01c1d581400e02d0116030081039011005038165104540d45041c00c0d10488003800b0481d82c04801004510a25030040010f41074190001c2c1501c180000e0690b11402103a5203140c07040001c9100b100b00d80d00704415500b011001d000c06450040c1542072001c4003009603000081c1c0034244078494042c075285648900d4014060701507000050203503e288441c0c0c04145040d501a40f030001d06004008a0039040c02d20708907000300200520582c80b44e5102c1004001840ca0351031103540305000d607004884603502040190401c90040501c0ea5144200f80f04260031101407085000b0b0070a9401c3d0200200c0352007039110fa81342501603a00c200461100b000107103852043c0c22030300307000c2d0340b5500011410542c44005050060750071794041002040000065459080d03540c3c40e010423006407206010040140e800240d008815420041005500356407101010000c011080c8100700903004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 502895197 1250 502893947 502893967
    0xf031b03021e13020901020316080f040605090406060c021e13020c010f0e0f0705190e0115020c0402072d061107050114010e07050a1b200102150a1505031002 69
    0x7600f14244002090210700e0035944c0c44c0040d4032402004c54038108801c1c4003981750300380a650b6040f5142d406561200300e0351030380c84040141c825003103004428010741c5000408a1542d0050038000d0740c580d001003a0801c50105105920040c0310240c60094111b010800e20340341401c02070010b4006046003034008611010481c003c981101d40b0390417000c0310b42d0311550600702d03190b0b004240300c0256801a0b0354400305072494a90342d4070401459019900e13071076844000041e840c440c100710041c80102c580c20b90388062804030420059000c1c202c80a88071880c0c0c41c0c44044199501d10552448003500325210214540070344404003120070094040c03140c000c00244a20402c60203116101209050720f05a040550400b04001d0f0712040041044040c000c00065841049010f5031040d07108020703410140044138090b103040c00c0b605034101885500041c82c0c0e001c40c0010360010601d840304000c4440c2e520040d43d1290a614040e060045a41010030503866021402c0d844c207000070f00800880c9074025940f55113080d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 502896447 1250 502895197 502895209
    0x20406030e0613020f04181b030b0f1b0c190309050a17070605030601050d0e0703020111030a14090f0a0b040305060601090b12270d0f090f031b03021e 66
    0x300340f01c0b1020300b02250b000050b40ca141500f900a90213880005c1d0f81d0b0507010100a42448a4802a00c03080d46291091001922400c459054a01c185002d881c50784401e4103521031a0015190566156640d5043c041c08030f060802030310b41c1d0165101200c0208000c46403440003200504810740005491080c00c1c04603040140043d070080c0100b90030b240800d606040741030b8960249000744010000700201081c0c00368880e40541d01c800c00c60040401c0550700c0b0801082c2e03161001c0c0b100302e020480700352216131050740210654050200a8581c2e08061203d07498901e0070740d21465071540e01c07426401c81c00303481d0303281e4030b081c48060600140a61b5550b415401d1291a00d18001e04940c10404403410910040240d13005850030500032020110041e11141024082c40b016100300065405c0300058400811a0028281078107a4098807400c95448819804032081c4410380980710b00315044000401c002a030480000d0003031100303403440304540782d240d0340001d5a07440300b82d0781002400042c50420120b0f107407031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 502897697 1250 502896447 502896451
    0x220605010614090102071401030204051f0807081e060a081b1228050307140319081e041703101a0703082703130609050a031703090f01020406030e06 65
    0xc0b9400c9410118003600003540c13101180034540c05504105088940c070b07402070b01694042c050060400000b0644050715101c80c0031024003000000d000b0b10042000740740289034940c010070070992031010401c1340002c02c0070781500140c946030300405c2c6600f0002e6203940501c10341c05001c000000a600c4070804e0400c00c02d00d404081600301160b0424648c8040d10700b840004641c100c0b40d56485000c410509080c41340c11405510809400031001e100344456480c0007200610791400d80304105c1c050400000c0e001c468044045176040358540f001c0001c2c8041f040c81c0340d203071030b4014070800250900301009055000c00d50019103a90300fa043c41000d003444055a044020800c045080506030b0a04d81d02e510000c0c0402c070050704c2e401c507440599644900d2440e89060290314403100d8030840c0d946402a40700750000303907054031800c0700041d080d0303401080d01d16008460008898000a0400529003000000d0b50294806882109248201560803400c148280040e0000741a15240080c4511781654a00e090143c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 502898947 1250 502897697 502897727
    0x6110c03060903120403020a080403111c020a090e1009030809122802211b030937060f030f0213090f02070204050c0c0106120f02092206050106 63
    0x14000b00034291400100340c0e080340c04031150300c04268130386040076418060303070260250812400280100600905408008448500ba10400c03801c0a4030411780e06070100c01d0000942c001107554040102d0701c501d40042014004090968850303848058550702100c40b90a003c4000c2a24042004441002403203590061613904c0d142600e400000c1200d45010900082108511160703034001241d014030800ca13030b181000c41540156000c0a045010314420b4004201c2e80710b40c0c60002e0101070b6070840c007205a0314a000007a00d00460800603100b0b40c060b01c015035100d1007503405c2d02400407030411514051000108181d40711070b33010030744865004081e07821085111000600402c0086c2c083c010442044080720002c41c1300248140422444030042d1240b040e0284d8824101420302103808052002481006800e20081107103582c1d5825000c13072402020400b4140510a064031805801c3c48a40715512600402882c1c070a1000d46800c018600a225010341e15243e0f15001408403681084081c2c1201309 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 502900197 1250 502898947 502898953
    0xf040506030a0921020703021003020f0a120b0604030213270b09011401050105071202070803070303060f060207060c17070b0a1a0105030c0711042703030c05040b0904021b01050106110c03 82
    0x81c00c0c04c013966446e0640b100030b006101e180004030116201c0c1d41030302c4603601c00490842c2e840810764001003909180150000780b151800c001601c00d460007608440403680d01512a6620300b40d607a400d10001c1034280507051400020100000c41c0c110710f00c1000d541d65106880d10651410310b400c0e1142100e0079000b00c002e650101c10014403403603800c0020384000356480000c0303d40880000f0002c0741030103c0f5902510161001180200c2090b400d50441420303503425640351000969600c408a81c4c401403489510081014802544c0c082111100d19022a0f483c2d86070701480c02c1036550715040b0512088510541c003d135240311014071121240402002107209180c1581113040035100304185110365a80140f1080081e008171000b40c03941e4010a10080c0c082d450200301c907281090525641426040032800130303150148942c180e500400a81d020360740344004550402d041b07041484003d51008040c6101c0c40203152210903958424080c0317502070400c80c1d580824508006c5405c515244003003082e01e210b50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 502901447 1250 502900197 502900253
    0xb060603011d070909062d05010503040f0c15031b0206040206030a0b010c020d0309150207080c09070c0c141017040b040218100f14030c060f040506030a09 68
    0x164056022070190b02c00420b01d003040c2d0f21411420765500c1441d902041e0414217010b00000c2d04426071044a0a1425000065061040004074018000c2c0c00c0c0c0903c5000c0782060001c200850103070400382042510840e520001c56031034800c00d0201500740503a50000a4854112800c06409298100c07403044550004192a042a50002d03000d400000c01c0501211b0380c0f20402e2544d40c3c8580140280e1039000f0344480311500d40c40c24010000703a01409520003c03c1d040b00030706445d0384001000000c0b104c9500180034034030615400c0100807140501110100070410916034040f564a02000000303150850641750504000018401c041b5101d10024090225902d441c0c001c2411121409502c0b680c00030a81100750794910004114100e6125099464001301d01000199500d481c00d00c400e8410794041000700302ea445a500c0c008007911003000341c0641042c408052141000009003591251581d103450a141d2124041007403a0011900b80c503006880300400c0c0d0034805440320140c3d1f08817102c02400040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 502902697 1250 502901447 502901459
    0x715090528090f0203061c0201080408091c08031e0403050307051b060709030203160302010c020d140d020708011107030c110a05040f0f060f050303040b0307031104090c090b190c05030705070b070b06060301 90
    0x2b00500400180c914800054084400da5921030b507030300062a00d0b0310041402ca660300301441c10741c108580701810042c0300240e03a05203680d2001c116105940c1a9107103481c41c1d40380001181d481d0050501c4070205a40c1d0850a0800da01c2480514840c501640c0d030035103014a1401003624207045d220003000055420030040c009130740d00c02d203140d00d11a019142d80090007107500d420380300d00004d80c014086a01032a440400c0c03007a408908813048a42c500c0081c040201c4081402d50035220718200100401c0c00e0341c003894002150020b040c500320b2001400018056600c10106e810384602c0500100100d984180c8204030382100e1041c003014180c9050141141402d00c408656607208a02038455140000f000160680d4425004001c46a0000071919281c40d50307812404080c0113444490000304d09803a40100b148070320107050303d0780d410156040b040d0ba00e03031a003000c2e5001403509600781e039980410009100401d204000c4070008044062806a8034070440c108012144006460300d44511030070401000381c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 502903947 1250 502902697 502902707
    0xc0605070503151e0a120b0a0204050f010809070b0d15120215030a022205030c0f0604060e0a05040c020706020d030c0e04050c0d05090715090528090f0203061c0201 72
    0x20f80c0406480c425440180c02031201c1d00710050b00410355008501200108161482542248219105108003030207503c03080d404406034091070041942101d201c803c8406158807c0002542104140301504c00207038840701c1c6240ba50348801c864000300c503143d40c60644c42d030390f841c800384000f000c10b1441010078003501c0d4005180003680385581052058040049a05109a1350407a8031000d4048130000090141380c0340c010340400c40c3e206261190043ca04101c1c26400e155850301d0380186d00402d01071030581484070035640c0036200d0061076002440f010000c01c1a4580b0310408035180400d80080c100c0301c2c0f0f0200000c0c50030204001c01000c0500302040091030300d030800038450043d2030464012070595101141102c0500445101c10300a41c1440240960280040703a00c07410f1707402d80a80216684d003001010b681e601c20701c1c030036141c011581c005218203e28003170084041140c8800511810f0b140c1d52103088065070198180d620007036900009014445c900140c82c058200441120903a120020b0340010b05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 502905197 1250 502903947 502903981
    0x19050103050c061c021c0b031f0e010b0d060b04110a020307150e030d1e09050c0d05010902061305010e01110c0f0102031c0f0b06040f330c0605070503 66
    0x400345201107400c400740e00744d200b607241d55020100c0c011501d0340c1c00200381c03000142c0078000d400086132401c05050301c0360078081045603140f0424003044521080800218004010800c4444042c3d5611989103410359030703543c0c001910034010040840c45110354001c0008542c840400060448810442000165000b2040d54841900100e040e1b1440321450100c40c054500245405601c0c000020710000c00341c484da0004524502e401405141c440c00c41d0a09002c883c40800060241d5204090114051400781c00d2140340c40e100300e00100382c1c1452a0b000c40e001d40c001203030001001486810911003940e004034446901030091802035010380301d0385081c0d5203c54010b00c80701e0103030302c40785024a0706034020012200b415290220113071071005c107080c1d03c0e03008004266a629085080a01042051034800107403800c0c3c5001c8081c0303048892a1a18907108510340031441c0108071003e40c41c4207280c034620680e182d440c80c850344802d485a1200d25009013111002040002404424410b1200000410310114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 502906447 1250 502905197 502905199
    0x6031b0c05060f0907030f0b040b010807050618060d05161b0206071b080d0926030307180308030a02221a090102010e0d020a030909050f0606090d06050103030819050103050c 76
    0x400307241c50780d408080c00e01c241740c1c001910010110740751108121a4100f4644250f000ba410f40c0890790b203c0020b11b03207550780d52007024cd00c090103200b02400b08030441045041014002d100d5450100d4010602d400e885084034401c07a241c0c540e01400c5030254003c5001055500484a1120b0550f6542e00141c0a4040c2d0a0050045600c9405689441d0010742c1c0303840c081d0071002d0441d43c1d1400608402132a52020b401240041c620b0303c040700a129102d00c00440e0210443c1e000341d819961403450442d04400e425150034050b501c004030000c041800e0000440c01044641d10140e500d50115001d0000340304c421059004107904076004001710108140c8046684c1417400b40c0a55804151004034054480d101040120340030b1080851400d07900010340313000300d40c460740303882d912075503250301d50b4040350350031110507020794401c1000402500d0310000401200c0c100908078031008126031141d5080f508241c03c00c601050300c1c001403090000a600002ea860360507081e082c4200d606503968207490b820b4083c40e035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 502907697 1250 502906447 502906471
    0x3060705091305070e030a15110705070b09061c0501061706150309010b090a0c0e06120a0216051f0b03010207170d0204052227020d110a06031b0c0506 66
    0x2041c0813500c6440c1140e80454001d00721101440e050a0403000c2c00107281210903400d00d80900c0200d40e0415100341d421154101d4081c01e4841c1c50641000c10a034402d00c03425500c40410024101c401998480c0081c0b40041c0302000a6190b040c00d001415001401503402022040703c001c00c2925940c1c1c0c2204507208154242d003d03240d0322540c0e01d80f405422411401c41d8031a81c50020460070413030743e502580030044030380e80e26a1000350402c240001ca103d003101c507018040840b000200d41812a40040582e1107433803000095010440c0c8030607081800c9031b1034244417002208c1d04140741a8480c000c4510918040b0001c5103080c0c1c007582c030200c28201e0309900c1c8016580c0450444840080d40d41518005e08003d04038128080840c5140240c0340c414110b4442841c0c80c2c00202c02c110303c4d281c08000502070104c500c00c440c04005400308403400084031000c840d444501b904540a5803154280d00b002000e0715140421441c1b48480c2c1c00620504c482103000c100040e061244021842c001078090f0481059541 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 502908947 1250 502907697 502907701
    0x308180a151118040612020603180c0a030b060405090118020f0a0b03090325020d0312060902040801021b01020a0206060904050f060f0a0e1f0c02010b1e03060705091305 74
    0x34035014200e030100c600b040e2140400c0900c840200a12510002c210440d0308115807510303840d03400c00300940c005029400c19010702c001854652a8141390201a161400b101d24145544000070200102500100c80205070902800302605007809555001302d0b40760700911104500c02c4021000440041c006889100c0c907074000c039026140c943c6008040d012402d03000d540c034030f88800040c1d9290301442c1d11031054a0300026019503c0c06580c1601071140c2d00400000e9140c103107032012222000c1602502c44659030312800040c10601510080c8000c1c11544005a00c501070f442103604000110001c0300c060340d004200c56044542e002c9030301c503404041141d0310b907001d440b00e040c00c2e4606a039040e4040782c03d00c621000d000c1100c243c41096032096107005000d0042c00300c019289901c4103550000386d070080801c588107804040081d008014100e2841c0300000b080d0b0600d03c00074040000100d111440d6080800070030099017001c2c8001030380708500d0304100d0700c2c100b4180f0100c0ca001c4c2c0b0b4101803c48241e07603240 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 502910197 1250 502908947 502908983
    0x50d030c11011a1c1101050919061107080106030803010e090f010203040507140d110609030c090c030609011e060e0402070609060e0607030911060711090903070308180a 74
    0x1d40181840700940080002160b40c60921043d50240c0705101e00c03600e40c21003440b4030781160540f480301083d03220445404c101301480056445401102449170302944801082035000ca150070058002d00150381c612a44080c085215401c1c10015001903116904008080c0b010a103200c1c103e0f41121b98010310251150b8030745080c24203104d0001c0004070103500000601080c0a000658201030b034072358400401d0000e2880303003004036280a6402c001d0103480300c18003a61039854000f020301840c41002e41035031416418280042c990038030807501030711011800301c00e10007141401e01070303280076200300014095040e5210604080151030380c81103400700302140c001001305c0d03100ca030155030f001075000c0c10a11400c8800d2504501904810580c4256403190740000340304075100340130303191841c0d4020783c1400c45c4c00400740a20001c0e0b0310822080d140d10300003004c1d000580d202c1e20300c40e40c4510418800b030340e119441845c00900c0341c0000b070214020700d078040b2020a205480030a99001450340140c0d006004e03444c0302 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 502911447 1250 502910197 502910207
    0x1020c06191419020d0e010f030c0e060d0509060703090b0417190509011e0c0209150d12030e060106170a0b0a140306011a030c0a0905030d0306080105060a03050d030c 73
    0xb00c5580d41d0b954002c544003082c1d010340014210900c100b40c0a41c2d5110f130302d040301207518201c0000401c0c0024080f140e004a454020341c403524107460a860070a1140030400f0220794907501060070040500e0b6030741c4c1013000e00c40d000d005807138001c6600e10b001d1083c1e49003515010080b10003c0c0026001c40c144c1c24414900401282c05c4852240d507156081ca100720f01c1c00c07030150032a00040c20850201d680c0c0401100711564401c00c03082140310f113490b50104140141c0034806001c9004203052000f829419808845541e156082c5524074882c41010000850088000301610f0f143c4202d00b07400e0740108014000c40e034001a07c010084485094551181d03a8040400c0c0038102c02c07800c00b1f030800b03850a00030a103900100600502500240d0032615640d0b600c1c0d04828558500903480c060095003400070910500d0320740020014030080f8940843c07003680780d00019092480c003503800008a0742d210420003881c4002c1c000c0b80d900034812542080503900d1a241d0700d84030441d400303d1342c081654030f0072440080340c090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 502912697 1250 502911447 502911467
    0xf070f0215250207080616030e1902190509070302070302030904050c0a0906320c07090b0906030c01320409061a040609030f02040906020310060e01020c0619 69
    0x14211100003401d10049002e04150b040001c00b200c1400c2c1d241d0140a90b000103011800c0780e9400d00103100540d11481615032200d02c400240d010107480700210354007908104208010641d44903c032042c8020b10344100106c100304586092502001c0742030401c2140d4850000917488090380c113002d83d80d14507601c1c0407802c5224001d6a158401d182000303200c944011200640321400c85500d848a400791075000558624a00c1007a41211525400e07445603903c00c00f1110310603042481851500b00101c402599003802915040034100c076541d011000401d24010b03001d190400c2055002c0e0500041081c0020004524040318a050010b09281c100f061642c0501c11143d20303402001407501c0d2615131000382e01601482c400c029084400628444140e0072080841d0104e0b0440d80707034041580e01d035994101000080740020781c0d20560303c0d00c001022540c0d600082d44141d400711600e0752118104240a0311000210030002c0c110f601c000110090ba840b510308880302c41c825060701c1280142c082034100c8a80b021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 502913947 1250 502912697 502912723
    0x83405060f07291806010b0c07030c151803031b020f040c030f0608150a051e0103030f022109040b0301020405060f0409061221030b10090515030f070f02 67
    0xd00b200889100c112600128035000e04410f007691030343c803281d40c5034550404001400c0c0031504983d0041005581c040002d100c200c02450599840c1d0b542c81d00d440000e01031690088118805892695000c20343c04880d00030054281c000c825502c90841e10002c20003107072032a0244503040804410402e65070f401500d86070900c8010400d101010302408020040c1c800045901406801c2074404144070001042c0c400d44c1c2242c0c2daa11220503038030138006e0b8000c1d0602600d110707491100e01c4034848400d0908040c45002e1800b0b5160314000741c00900f402444c20119902c0c3c250000c0c8600e94080d0607034904c900f00da125420840b0003251080200000038024411680402e0348110001390034115201401c000e0000c903104001d007008450790714840e46c80c12445031540200146d14104140a140081e20b80080000400d071600050000a040102d504c86100c10401030200300d152000700180c2c9488440180c051140e49002415030404001c9810b952101411480500400d4011140064400c0006d40c0c4445c04c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 502915197 1250 502913947 502913963
    0x506040e0318090a0b0f01080709080a080a0f080903030a020c1212100e07080708251d010e132003010306061a0c07062001020301083405060f07 63
    0xc6804030704155140800d0500d40100c4403e8000b490714042403044441d040c20260004052911440c0115081403000305498107210b0402804220071100300a42c4401501c5610300c540d60305c0700d106025200c041e101c500b03c000c102c10701c001c000313200d98080203481d044000001c02603120340c0700000035400c00340911012140c441d80412048200401d004c00c1c0c038000d10002030320b000b400343c0701d082e00d074140c40c01101e000f03010510507801320303030020701c6880243d81c05030000e486103040044080d8042803641d011410000003034004910300800c00d2102c1003072900c1403024204810303041c0044010a80560380c002c03c203040f180d030b40c2811746d44d00c0c038108035507503110b54024401e0f941d00d60316858104020300160190390002d448041c0408528103010045038101c04546000340301d12171a0480845440989000056060740812608580c041d001d0000c6c502a02000002d081c014010720369204000d031a000c00841c0710340e40302d10f05541104001100d401a101c00781c84450741c8000360740c003520547c4208000101862 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 502916447 1250 502915197 502915207
    0x1106070c2606100906080f0a2607050f01270803040314070501060f05041a1201020903032a0303011208160206190314090705040b03010b030102042315030105040506040e03 75
    0x10361100080f003a600312600411000362511303891a034882e001e81907007007240c1c829210702010681c5152200e042904135441003100e07002c0ca00002030150001c039400c5400754460030703041c955907a00b1b02500784644903140f82c10080c0010410081000280664050114074000001c10103040c402c00c0401e015080103245595104281e24bc410b000382581e02c02c0484c130610002c00454585071900501c030305c141c2c17011260a2500c1c00c800070016603049100c000111590b00b0000c001071030314140040e1600c1d039500032002c02800e418a1501d09042c0e100742d400900741d00104018032001c040c0c5043c550429070002810303178884800200d0b007800801e058038065880440410801c0d0300d1061400100000040d43da02030020321542655282002000c2c0c0304910542c10200041c415410580d0042c1040c40008001007404004603010900f2688660031240320024a82e40142c440000070205490f070b10b40c140c03000c1c0c0c400c03204401403c0c807600060240e28440d6858402094460b65950400c00c20100254143da98036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 502917697 1250 502916447 502916461
    0x204021e0a030e010c08151212120c070f1b0806010e04030e0f0616050c1504061d03033007030203011701150b1b030406020a1106070c2606 61
    0x1034104004160000f82880c2d1458000101030250794510400c0e5116241981c49981503072030000d01c014000c0782c2104211800700c0024000300708030b20182e0480800f940c1c0d18861554152505032000301030564003d410040d44000038070f80c10710181c031541c1102429503144580c0300c043d44481c03034645c040c0c1444c0c81050004254043c40040c410b000b180700e9101d0750b503503481d1901804080700000c503c20b54806814040f9088581c01e007201001080c3c4a48140c0380f01c2000e079000520300e0307800786051805450b07003c9030a104464114819a82d02901c905210840d002d0040c00a996840f0b60044010700005104072040340469480e800c03c20b2504809075420300d4507000e03100030001d400074410000e6403000d501500304400c03818841c100c0382c109c3d40c0c801c61001d1400e1110741d1400780d1125240040e803070813500c1000c0c00401d040c00540040c04243c1d02625411105085c02d58207801d107a1070543c86002c04010314000034500c50f50320000c0710b0103003c06800102903040b40380041d4014074400811409039070100501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 502918947 1250 502917697 502917757
    0x80301082b020c120304090218040b06040e01120c0b160507170318010507080a0e03101107030c110d0308040c1a041202061c0c030e030c0a0b04020402 66
    0x54450342101101c035003000095107001551034080440c02503000101190060700309400c01c10f40c00d00a80c0100d9241c00d0352141e000d0100d034004500c2202200e84100c82c0d060a2506000790003516504440d4035080034201141c8000181c018824800c240c22400c00520400c2003100300c1a0007444818a42e0384c807010b048107522030441000c0c1d000c90340c0c0e00034044082000c110060001e00b004018000850502101444103500002d90207100c9043c004240078540000300420001d210301a40c030354174005068105c000340340c82c009805490b0074440f41051700340e0109207000000e8032a42c0703802d0f1401c540f4948240c2072460b5140901c035821a013000c00113001c4424944c00101c014051032040000441050b41c500c0c2030342420b03c1c015540e82201004110401c2901410002c00b48000c0c00141064070f0102810100081c40f10b640310792503a45a1504c40c40f08840c0c0e0148920140c2e4a04103020b1480c155007040d000d81c544503480e000508040700200881c055464550581d44d114401010a10300c0c0019030303603c248 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 502920197 1250 502918947 502918963
    0xc0506120609070f0e0603060d020a061107060807210b0405090a0201020c15040509070905031c0315061e05090a0b280c030f0c15020406030c0c0803180a08030108 71
    0x806080c001000c11841c904c0764500007120403050f500c110780080f002d8100100f80c1d0000d0300641c2d1040b03074218200c0160340c0e00b2070614010002603d0b6000d64884d003200702810b20b04d081c3e00c1101032103121020040d40540100d82d91650344803c40d400d92164036807042d104000c04c502c10b071194110386007400b00402441e00040007003a6034001d03000c4030420b4400808100e2502e88488407401d80300d00c10700c030400907428001030090f044a6207042035034406817074102080c81c2414140e020302c81c01100030141441e02d031305440b502400140d80c80084e00001e0500c032004e840000c6685c5410a150400380c3d8200281e440b40003624a5120001c00c5071200d40e543d00300381219900071020034401403103a400c100d0b00c4002c4c1e4030840c206c909061f44420700102c059031000d07192041040e41c1c800920288802400004030f2000007505020300080005840f1801e03c20000d0458201c008882d0030f0282d070a10600c042540304044e2940f2401e000c1071464040c08600c00700c2c1c00d001c042c0030b00404c80080800041060340700824104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 502921447 1250 502920197 502920199
    0x50405090a022a1203010f09090302190b0f090a0b0106050322050c01022a040c05070f03020a0b060d110915131a0a0b1801270312020105010e130c05061206 68
    0x2507181c02414070b2132040f48420b10500100d8604050208540c0440d0703080500024040c0c010754200a07910310000c0b800300d10468080b6400300d1010104042c80342500d10070354005480728010418006903039070f218001e10041c000d0f20180500480098201e01c01d500d80c1098001a403810000e02e0f805e00c3c503056589a1581c42d0240c02341c041c520a801d0340400701e00030060070801000c140c1c2181401c100500c00248803003c005410043e04000001c04203c680c800380d04850320035070082c854201a810a851200300140459224142c01d0a820000c1000b1407035294001408139440ca58a4440d03210a040041e0044403458001c405110315000c1c0484961249090351803044410310f010341440700700003c4007054002d4001c0713085d00f03000000804a0300007100d03925a4040c1031100c10a0200e1044015148a400700d4807c2c11001d107105104021148010000b40a0140002d0200c0d5045c548482d041181c000e01003180e140440804c401440320320b0000100500300a0000c2c5e9480241460340e86c00003008440d46 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 502922697 1250 502921447 502921453
    0x9010608160f150c03050703050f0f03090708030a0f03050c16030f0212120103120315090617010c141608030106090320030d0c1113052401050405090a022a 68
    0x1e19a1410f4441c080b4181680e0f62046001c6561380c042e00e1542045800b603040103014418058400d5040c001003a0280f1244048c030340b6031400d428a685461300c00d030040c07001c54106002c0590f0003600a1300c400e140c101c80e8180422141e4621300803050901503ca00c2c03100011141d6800300516030840d6495000403001e6086c1e6012100500e014107042c8110403603618085881e10040012412860000c2d092481c2c500d40441c8007421004041e98100d810b8100c010000c0c0d4403e0100a5520300e00524810808810002e0110703880018024250410399040380d0a4851b0000e0195841085250200c20380b5034488042a103950b1100d07401014034a480c04121070781e01020b080344400741301382000c8140d1300200800070811207545401c11941b0b16070807623080340c2260181c5a840803584c1e6000000380184501c0d80001904d03e05040300b070040c0b406400140c2c00c0d862181074412200d03681701d0105d44c10b4480076551151113848105888000b0700c10103400d00141c40c1001c0102e00e28131900c85c50050912030000403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 502923947 1250 502922697 502922699
    0x807050d0e030304171c09080c0f0306060120030a021c0804170d060e01030b151e091008060907090c090f180204031b0806010e04031709010608160f 65
    0x41500e18001001c12598168800e0200700b00185c842c5074854400c44140040d02c2c8054410340b8000642d0750000b51400c0496040744e02406184005c019a0004080c04c80e603801042210030080b81d00c651010300020704010651103450300d200b4640d604500c20340c0011003143e0b581c0c00c5442c1d00a45071651031922a1404038072281a94005100d402964003690300f028040580c514812141c0741c542d84a00b010100311621103600040c1404c403800c40c50700960003036500802034941a090032a000900c0e214003481403840402504103d40c1e07205240a5015081c1c03554091603c41040c100700781d0004e6400800700e48200410000c40b001d003c180002141e030860024400155081c0003074900306880c1c0100440207049071020417402c410184110442c054210005180c5926504c03442c0690085504803800c1a19600c0f00b081103a41c05c0281c24010308010380350490b10308107940c0040403600450041021160f183c8040350300b16100394020001061100c044411100c140900390301c0b08440e034810f0b26412499110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 502925197 1250 502923947 502923973
    0x18040603241a0d11012f120306062d040303090e060d03020703030c030c06020c03180306060d1506080f210301030b04060b030c0907200f120f27030c01090303091a0d09080705 76
    0x7c1524040d5800900315070800c00b01c0a0035070110800307010b141e440006941140c80d51050014020f201450080d0703240b01c0e5050a010007941e191102600c0e290041e600c0a18020210754046242c0f41034a925140c028018801410b08030f88507090084060012840040c0c48030030030600000818030041d14501001c494860b510400d500c4034000c540d5035410085100031b680024404000c4801c41c0c41591000084a41d2510003072480c0c51404030010080c0d600c05c820a05c085511201213003400c0d00c11042003841c1d5811030b915120034a50180c802800941c4810381e0302040e030360910603280c907043d010701000c1e10b51818203401444000107111728503070301c42c1412034080085004918800d072090707014010046200001e041900d207500107821120381c0c0341c5c180204002081c1c0300c68260005955102c1108100d100303c0100750402d1a5000301c0e03414884001c00410001c1c0c0c0007824401111202180ea2554140003c2c111200303201e200f25041c04945412102d00400032000081e0800902810803101021081d074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 502926447 1250 502925197 502925233
    0x30f0f0c060c0804060518100e1002040e040312060308091e0916031107021c02060c0a080306040c2d110601090e0c0a080318040603241a0d11012f 64
    0x403006c0300c1d023000c1c619160400c402d070403490000e46520100c03522005e80d648988101d030045c0c2c1004000e50500f9042c4014990704c16600c1a141d00a1042003111f02e15580c0c030300c50b681c4507418540740600400841080414500210709440b040040d20210701441d1803400c3c2c5000140e0070141c1c0d40400c0c9404482040c03610307000705603155950b01070000421340b02080000360403100d04410881e40490200720b800b820310300510401310800c1c4200c241c00e844e41400b03010401900c00c4101c14100304141a01d400b0128035049115600e105400485200024840350088480e280804c00e008640d00c129800001c0361070459210506e11f0128809441a00301c0340c4040115140c5c0e03c3c4607100040d4024419012541d040f424035482844c001071000a0103a078994601140d407203071030000200c121404c94203004408140c0543e820b0100e109900190107100b2100050710b0740c52010000d803142500078024800c4e43d0060304490030b200300d02500c0c0e074020400c541121410040c00b4802c2401809200050b1a02810304 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 502927697 1250 502926447 502926481
    0x405041508010f061d2a0333010c02031011070c0f060f050d0f14100905060102030a210204170c090c070803042f0406080604030f0f0c060c08040605 65
    0x240d4400c5c0c0301003190b054420b0300503101411888420000162076a44900240003e00c0c1e08204245640d41307034540380b8405110044011501c0d4a1070308908403400c0c00141c548040441850b0900f001100d200c41e500102c6d1400c00d00c3c05070112403601d8104815070a00703104014091030703840b87d1100c500312030702c40f0100e0352a605580701d0300000c84c903080194500c850050002d40b40e00c10005600080c0c01348a1440c2c10107403140483c0f403905440c011001e10200c84c01c002406405451090420f000c5410710790b000035079921130720160034104004201e189004406c400c80d0303c2c0d5220006a0223640341d0307403110102d080402c40b20202d02081d00c04d100b080103c50900781c504030310400101d0111400c0c201981c551000d154001442205c10f4000748140a403c00110420010b2815051020102550a00040c0412904150001e4030660311070410440061385c02100c2092811031072511440c001c2000c00191030030a40000b0040c001828480345c078500da94000f10382d600c206e000f004103200d2626a07000fa40e40c0c14480c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 502928947 1250 502927697 502927709
    0x50112081b101e02070812070302070515040201120b0105040504020f0408060c120f0919140610090612020d0f0c03080c0d0e010503070c1205041a04050405090f030a140405041508010f06 81
    0x501034804c034a07c02c0002c141d4004018100903151241c03541d03c039801d01c159848409000c1c42d0b04400d020130365901070281c201070310030322000308441da2105002800d240511321800c0c0c484d54000910404500c1244192401400c0321070032a000c41c140b9014030041608030b04120041400301100041aa0303580d80044d81c0240c1004014045c072110400305420b00030041002079030210103815045042810030841140320316003074080321035468208003080055903643e501101421610312500005607513800c8184600d158400b8022a0807011440e00740807500082d40054158800030840100155000c22000e40b114450759a1080c002202801500c1c0c50205031000400600c5150b6035000003510640003100310030311800c00900b4540d84407102800e8110510100b02000300c041801c12450510340995504441d030030018001c107403040780b03d07071341c1d240100d480d21410490400070100300716100c1801c44002d041c1c0074005000040b0500d00c000f0203d0305030700c50385800b5840d0040188003001c43d4407034030b0b042d903039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 502930197 1250 502928947 502928963
    0x8210c03220c062006070908120c030d050406110c011424040c0207170f0d03230604090b040803090c09010f0303080a0216031d04050112081b101e0207 66
    0x10822008981c100c02d04c64007036524604120800312080d0080004902c9401103a4511030500e003010503103400c0c48845444071f98034460900c02c01418400100c10394146e45040400020300341d445050000140c003580081c2e658064001440303241204043d08112003504880c00700842e42d4603060304e000d03003401080c403c0441e4040706080c49540c510f40f503008210502203510445002d0354449620b80080320902c07038000681d41c070100c8902a502d0041c0004506000d00b13060400c28000e81001c0c01303070800c12042003103600c045a0000108169180cae8440da1440d034202e039070301c0103e14103864400c041c0c0d0700a46140a0509c114038600441e40380c0f070035006068500889ca49540c0c0c1d4515076041e600040054034140f000d54091003401140310081520ba9040c900a586406060a00801142c0e0100e81c04400d07500850400c0018000400c285449105690388990021742c3c4615503100e4a8410a01c1e420300555405101c61503411200c40707030449815107004404844413460940044001c910a940000385164 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 502931447 1250 502930197 502930199
    0x405150304150e0718020c0a02060a0c06020d140a1a010c0501110a020a0c0b030103020f0d051f0c020f0105090a030e0d12120b0d0302060408210c03220c 67
    0x980000155411522074031411852020715420034060710341c60b110860301580000400c0011030001003101390000200c1400f18030304a413002000d6101c0c451100040c1c0506030000d1102071a5114110183c40c141d0070020454654090140030800340204140c01d40f1402300d107070042222a02c00c0d106441001c2a41e26640e109480201e0054801525004040e100d6540e0b40d50102884d00114000f03090040e0503502030110709485150040400070a50413083c07106000f4070042c80103803510043c4034900402140c011480c001c051510030b02d00744401c407048900e02048600382d10103600c0b40d00082c40d601c400b902074402041d0000c0c4c00300d00701e07041214141125841060340390080b078000c03110111f20703003c0900200e140c145591a00141202c45000314000248a510036030002c080901c00d409801904403401240344240da10700950b902c2001e000070f004c8080000d070403001100c01c003980103100720410300003500e58074255403e594260412240c0d0b40450542c140201080100c02c1d00a80000d80c2c0000240070301 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 502932697 1250 502931447 502931479
    0x5060c0a14010204081b12120301060c080903030d060f05270c1b07030c0609150e01020c03010c02030d14010308070b1b070b07020c090709060c020f0907080117030405 73
    0x500703401e10070441c155800c000c007281c01c000500c0001c0502001030704000b90a00300c002402000d01034103030490095000342002040d440d40200890741160310514101070202805d061000b004c0c801c40031400d074140300000e00d515054031203030031081c01c5a005840c2a044c180d582c2040c00402c1241044940b400261007401030041000300e44a1508402d0805e003c6043c0604500944c41c1d0301101c0000710115800060204208801201540081c1c02c440c80d20110300b5190544020707034004e07880c00d10418409001c000918a9200700800c80803c10020000e206420745410b01940360b50001211400981c14030341e14145118450000c18100d0741d2241e4020b103401c4550303c6540e851480a8102141c00710007010000c42002c21a0252039850301440b040381181c100228080d16120751030814034000e0700355a00304951540c0180c240012200c06040007811082184001050f0880c1200f82c01c2c0c0c4442d0043c20b00c5583e550043d2014103884290941c103280d030001d040b0251756806144581540a01d5031801a094 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 502933947 1250 502932697 502932713
    0x15020d0201112b0b060708030412030c0512090a08040f0f09090305090603070c0f061413080d1a0907080708010b0705030405011209060e1c0e0306010509040219090209010905060c0a 79
    0x1000c0030b40310000c4c500840f400002c10300d5006840c00da40c200e03000300501040c0400c001000642d204541020041043c1200018203e03010342e5001b420a0070200000810052080c800070028540c0045141c2d0f640703443e860041c01c3e8800501603008407440c0c65a02081c4c050962040192454145e1941e9081c441d403402000300750b0340002c2c07402c0700300702010f40304000040b9440101c209443c8254808a2081c2c50091584a4110001d15842030b4480c0c099286c00425040030481c1c2228a1101010442260440c03401c565840c40100464102d01d82c0c0c800c005a640e40612860700524090b03a902010341d17039a810804c202c0c0120000030b006600100010080d82d0b00074001a03488181402001c16803000d16100c00e012107081101140050b00f1601c0c041d1200c400078465120300200600780080901403400100380c7e2408140901030182c50f00801280555030342c00d4a40000342000c0c8440c02000351104040e00194010b10000d9010560001000c96a80b82000075291900182801840c04244030340f00d501d0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 502935197 1250 502933947 502934017
    0xd030f060e0f190c02010f050708042402070b040b0f01050d05100209211c110a0602030c0909010f1e030b1f08100227090103140715020d020111 63
    0x104030011070601c01c00e030f00030301034074807280000e0b0000a400900c01b2407400944600400c850b04105201c07080100007a1000000c1000f890070503040c079a00c2d00c085110100074483c010003d06000c40c107400300001c00844c52401c40c030650401d05088142e90740d800170710140114900d802001508820101c4251000036070103015039100081411168a10b0204001d503050071724200320115070400020100072052265011011044a00d405100c0483c1d1038180c42e218061010000c1489400101080d0300500d000c080d0745003d000107103003c015517502c0540c1c1801c1c01452050b01c4d803a032032400c01d410180c0c030782c0d244200031039400040424095907208076445d40103886400300c0d20205180c5401040d0841d041010300c004141c22440103a4038882d0348002d6500340d01c03081d15200300d1a40c40f243c12045456401c0c201d81142e5003c1c00d960f4914100d404480d007002d145405c00c0d51316400244a03104019070002e907040460354181c000300b00003030300343c89142d20b988641c07800d905c1d2040801641f48a000880800d41d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 502936447 1250 502935197 502935211
    0x290a05010314390d0501050907050d050912120f010e13110111070605041703043614071b0c1202060c030307020307050708060f010303050d09050d020d030f060e0f 71
    0x1401c0104201c0f001c04030342e250502802107403400420392890010882c481c09025000450f50b0300c41a15225000501e03600c00d82c00e0507101c1700d80396400f141c540001004450b90340c00e0b44545054940c842401d12141c41c080031034500300003c092000004000c02e1185170140a49004480b03625040d03441e483e4088043c5100f5030032030401c480422040b55118050203804041d1600d82d40d080d43d1350b0b01e40030420640d0003c08000071500d41003004100580c64400c40074a41c40c4050000e0b00055100d101d003000d800e80040c0c1c1542d240340d410403060300b0746003140c1d0240038844c20158441041c034455100b28516000041d280083c6030010301841800992100d94075010042c1c4010b021174642061710700c10a0541c1c1094034414007503031000c5110010440140305110152107113038000c0080d46401c4502a5500d0f106200240510000059003a50800b068105000454000c400c44800090441009545000703a0070018000b0b40b52001c00d03e81c030b0b4818011581158115100f01071561102d4080c4010201c01038051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 502937697 1250 502936447 502936501
    0x150215040317061827072d0305101b05090a0501050c03160b010819170706111602010e190312030207020a080a03030f020f03040312290a05010314 64
    0xc80c2c1c200030090810388508006240b10f030b6910803618041503400d00058404096070445001444030401e1080703281424040340c50340c5d0030344c03800501414801c41151b07000a40304ac00749d09840c40c2c0136401c640000e05c820b640686450068510020220307014021040c2580d07010743e00c04020081584900040c0100002d0103055902d403a49092040c0c2c00035050250803501c0d141e400f4010808000b0074804013500941445150341d5a80341641c46402d03035480000c0c3c004410401080b2401480901c1c1e0040701c0300d0409018259842e10001c2c00070b4510161a18120b0020740c2d80d050003046814941e8a1604c140000900742d00c0c15400c50361404d0000071840c81307440804d41c0c01d104840c0503940701c4002d2030091542c00702070403031002641030040980707820007903211031140108445485640c3c520308481c0d0090305454102a2880c41e0f08141020304120304c1c54406c0449a40b58002e41ba254440f403541c0500c030100c0d02c44280e5503840c0300642c251100d01041901c4507121900160540c3c600c8010080c40c0e000113048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 502938947 1250 502937697 502937719
    0x15030e07090e100b01051c05090c0a03080c01152702070804060f030e0309011e11060925060801030201050c150c0705061e07180504020415021504031706 67
    0x2800e0403122102d0360001654031032a4803901016051041c0d50301c1240c2882c0907850701c200070039003124607508040c40c840ca040e910400104a0801031252803140c1c4001030001006035035a080100c1c582d0019240c507203665207031200c204224842418100c0032144200314903409414a414106105156402c0c1002d4513502004501d00185200c4000c00291616880d0b504403d18107010081c1203481030720301010309500030420101c10b82c0c1c00c41a08500c0500071050340c2d040440e002c1c0c0483c1c031052180c0081455200d07501c1801139006010641c8840b010700780ba020903100310100c01270541c0720300303d00c60311000c150680014009544030f18001d202c48107045085500e0040c029840000d003000440e45032003110b41c0403070380304100700080c0070301908100300d003018404004158214010b665800f91014007070003101800c0125056800e0601c00040600a2086440c0e41d079601c507119900f00c090306402c0c0180164240928000c90202c2528002d640507907404034105419603500e8481c04024015551000018031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 502940197 1250 502938947 502938959
    0x100f0603080705070f06030204031e020402362706060408100b0117040c05010f0207030b04081e040f15051c0f0e0f2802030d0503010303120615030e07 66
    0x4000c0450601c20001000c0c018a01043c010f044175080d0031000030180104001c1010600c401750319081668030103080c030301c21500c3d440050001c0c4200140180c09041e0343d44031804010021106000d0300e800070340301007141c00700c0c0c80c00c20102d24455621500c82452410304410390302c00c03c644050340841c02501191900e511620301a181c48401d8a608006540744e81c20a2034950740880001c005c0007407440003101a04140d070f902c1f400c2c0300b85400b529041020550519200b035100b084030b10021904001b50b50024203007410890784079403103810715841a007503203030b4029400345e202d9003124111007019120403040c2c3e003000c24031b0394140c8a40102c0380c01c108052000e0318002440e100c1541a940d01420006810340100040500303841c03065843c544c958002207000080c0c40e501282c8201c010903100761380c0007954400050031400d803074051001394152040c1d803a50b03d0840e820000a5050701c0c0251160344e940180303596490700352071850048400b4007040b89041642640641c000c05400000070080c2c406082c0c036a4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 502941447 1250 502940197 502940213
    0x81605090a091b0306061d04110c061501020a0b01142d03070806100612110316180302010c0303020d060b0f04060e09130f0c080303070507050c030f100f0603 69
    0x340281d0340c02c56070b881444007090102440700701841040d003820300c001e5180a10161090f082c082416101500c8550703800340550b501c0d88650801d42200d800b81d07469a4401d01d00ad40d58150480d289001005101c00398100c1d50700000762600c0c015440300070242181e007030124410540f088039882c00d03003140c2504414240006e0001940c1c400e000c2600716820440d28503010540307003612583c0041f0701e64003c0360910410429041859085c1c804030f0410760065145201c0d00d600034200c514080c4994030303002c0184a0315410940407289902d95035602c42a8030748001201d0020700e00f40c2c1c400240803c0140710402e0010340070350085c04110020000000b411560f4502d409150742c000e1001e4054403000140900c50560007160401c2c079641d0a840015003480c1c03e60701228030140480012b07101c001041a04010040413188000103410b008081d6912400d081102402c250006075088400380a0040c0c10702d4142030005218500e0041031000b00442c1603e001c20f04001e00d000020910420303200c00002c40403c03109 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 502942697 1250 502941447 502941449
    0x603050f10030f081c050f06100912021216030c080102041d070e0301050f06030f01050603100b03030f04181d06040303050a0e0a05150708091c030f053301081605090a 73
    0x44022481d468030b001311501f18200181054441c80e409501d40c280682c0c0022400195107003402a0202c0245a000040c40100460400c030341505c80d0113084d1860341d000303032044021a8440d100300d040c09a1120b038034900f40d01132401444041151184801c8014a01591b440e80020719030510851652110001c01c0c01d40d1801c5402c0f51940108009200312814100b000400c800080340080055041c0440003e840c2d41030840d00c01e41e000d440e158110411383d8140b00300d403c000d000f0150130360360316507655140d40111400303508640d5292416072403020a031038080c0d480081d204110040c000c02ea4440d5003d90003800302510f80d0240c030744e0742c00c89038040e56402c2107207410b100e005000821420068074030040800340010203001c00c0102c0726040c410150400214040315200381d0301d0018082c41c17143d504038020f122034005002c50b241004180841d60400000c206a41c00030307640d000c21000c007215480c3e0440c5c82c880d03045031b00060140000500c014425a0440c072080382c1498041d241290303d400283c0038000e1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 502943947 1250 502942697 502942747
    0x807020111010f1a040e1b0103021b1f0e10050901020f0703110d090f06050721030b0a08060601050403140c0904081305090c2d0c03040603050f10030f08 67
    0x1580c0da40200000302c0d0160070102c0381085405001c040d40d00702d540ca8072411120310310036000c031507c007641c11240e0080d0150307061010882298101440c4c013030542a5a181d01044111341340e82540b42e496400d0155002c1c1d10350840800008010032400c60700b40700c000740001444c81000b035500344135007a0405140c00013010304c140a540d462281070300480009040200d0440002c092040030101008202c01816440c421140c490925503181c0d00c0702d042c03100a110400085002d0700d48611184042607405520201c078400042d119501c41d0f80d03c6000c0d1307654400c819600c05004c180240002c00018403c1040c4400c1c02c8103030b500390b90084200002044940009075401c03101d03000040340315000c800c0c0e9804600010312003150601c1c1c85007811400302c0858811000707102e08942e49a6084006441910303079988a40c5480780c1031740d954601c003240090b109e40250140400290410001c103400c40031144025000321000d240000315246955034003140e07420a0102220610f400f48415010000140101c1c03040c0c0b85d03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 502945197 1250 502943947 502943951
    0x21f0504030c0504090201020a021210110c011d03310e1e07120c17100801060902070c090207231c03180209100e0103120306080d05070807020111010f 66
    0x1041d40341200c1900001d800983c00b4501d0b2040a0000d03030b030f001443e419a150103a80100003c00010903603418204081c9407510308071304080003210706103c6c49008044080c28000204222030b500004034280c001d00c4a01c120a0750320030310070058030380e944032450686201c0c50340ea0002010000c00c00700fa041c2e80340e0b0b400082024004c00402c103584c6221059115000c03100f0100410a1400550207020800c04450941103d9a00d102090b107090048807808810407a031802507540b0301d410402090503154038010800ca075400d001c1c0005040c8042e000f41c4100c1640102802540780c01c0052a40c001c0d005208155950400c0201141240308030200d00030f15001c800300035100608414a0110014020030f400008061070564511782c0900300c2400381e190b50707a045546186548030700001d0280c820302d0384c0004c55540351800000040040310721401014150b90388050182d15603e50200c1d03190241c101068000c0b500130000600095034100051407118814184501c545030801d0040e401c5501c810b0070110015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 502946447 1250 502945197 502945199
    0x3110103050c1e090604180f0b030a0c030602181c03021917070c260106060503040b0411060904140402030609030304030503182a0a32040e0a0b150405150d021f0504 72
    0x108c981d010702c0e540705c141600189482070559a510f010342d17406110240c901039010640c0804107030404110a50034200900244c9083e1450f55503280c03801030310383c084001d031041070940c04060324007041d5081000d4121200d820301c0742c20111038445560000004903401c04004c0400704051100100c21000408400400c2e50a050741081c1030b4219100780d002a01030010502c104000074003202601540164000700c00d034402289031002c00d140d401226245903100b820051000004040410b0491080e80220308441e52a00c680010070380742d100554001c0c00098081001458106a9603a2141c5c110003103400c072039001404040b402c8042c0c40c00724032038049241449845101d40741800302d10f00507041d14410003400d007a020030164925207064a14a020700c000d180140c0031980e6030703801001014010f8040c0d84201c8106d141c40550008100c0c0c40c96500e04054400c01400d0606120341131103240c459810812480c8400308015402c0b07041035040342e000404010003948800082c80b00041039115840b45502c031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 502947697 1250 502946447 502946471
    0x1a1906030c090b0313030216092a052502030a06060810051005010e03010908070804080616121d07030506090708030c07050f13020403110103050c1e09060418 69
    0x203107845142400030400381c001d040c407502500500312174219110b8036200d141040070745010390421401c4451440842c8101c1800510062983c0010258028410301400d0400c0340f0703c00b00c1e031851884a03001d0000b402c140980441c007100c0807404940f06800da580d150400c80705034006072a04072902c50407200262a03140400c00080104455000190000c1c8240a80d19103c8940c29008180d4412301d410040000000b4040e51000e6004141d140c2c0c00038000740e5078280074180b131900d40c0e001c0e201d2400c1c14403031030001640c05002c44241001c1c249036595000e000d0740c2c01c0c00744a0003a0007043c1c4400320034840082852000710040140000462184001d80000e00c2c106004030b0400303001e0390100038190010040038025030400b0410707000703440d001c030342d00d50304041460042000203481d12181e0120901c009004020b0103464101107810300000d80e028407260b698150b0725603060103801801c0d0100c10740c540041240d1030018010b0507141c1c00240c481d0b8202a598080d07822001450401c140502e603a4101107002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 502948947 1250 502947697 502947701
    0x181e05061302120606130507032009090601050f0f07030314070807110c0d12230c010c0c0b06040519180c0602010e150903090d03171503030703031a190603 68
    0x510f11800f40503040f90725020b0b0220b660702003420300f10740c0c1140e0f903500041c1006001358804403450040400d50b12401072130000050b4140e02c00060310784241610703000074203250b00c200116090742820100c1c007800c0404008100c1900d40048d030301207041c95200e4030a070070302108016003a8030031035543e5211005401c1180002d000f2500c00c01c51080660002c00c24048a900e4000c012410207074425202c11100d20070340c2080fa15103461800d2803050540385180c4648080c10000540440346010000304000d00949a05075140c0c000e645008024002d9440018103618113a03005541c0030040c264411103009100e90440b0496a05515408803c03548601d210240491004e080c00030b01150300080042100040580b55507508800a0464070b00d00c00b80052420502402503441003803001d0901c0003008003514000c3e0100301d00000408a480314500062094004240302040508010300174618005030b0781ca089002e095407024207041410450510174142c0c8490742164004985440c803000413031304003500101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 502950197 1250 502948947 502948969
    0x90405010503030a0c03120b030303070c0303060b091e22020c060f150d05070519150315060c03170103030f0f0207030209060603040f0b01090510050301181e05061302 73
    0x7020b0f80c8140a20384007a034111442c901001e400d42001c0c2111b43d21700711288040c0035603c003504d8040c000401844407039904920501802c074802c0c3c909110481d180c0042c080ca50003480310099004099002e0f55120022989021508030406004003060320007240c11136250884001409440c50f9000a41620007801440902e030444480c0c0c40c0900c803802d0405840003000c01008406110746691118101005020800c0d0001480301802c0e220900a501d0b800601500c43c6118404107a5400300340c0f1300c0c0045c4240b240e20b10110440180c50b4520341001e40460304800303125030031010300c0410520221904000c0da6035a000f1480381d91480244006000028041c10032104400c0542d40030000078001a502d518500d40d001c4403e80e002c540704d0341c0340d040082c480400d00380d01030144c2101000204824085801080c81070022001101c281552901071600b00c0d40c64244488120411088220001d802c002d56410440c8040084c00c10640719a120981060801d6444c0b2104207108503034402107092815100b0303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 502951447 1250 502950197 502950199
    0x6050c0f0c090f092e0e060601020d030b03010906021605160806061c0816120c05060105060901020708030f12010e070c0311011b210c0203160203070510050904050105 73
    0x29075852032011540b44500a058142244614000915050010410242688280c0000d001102c5011201410004228442c81541800e00c0c0064504000008100b80541010790092034004e941c1c040071001040c030070080c91380c5952203050401c04140740340058a941580e000f00d036147c81e41e25241941c80c0413903a105890b01e00c50b240c8030070004c1460202d4403541c0314200b6101c52004100309400c0b1010a004014004c245000100740503c0702000d0700440d5072420320800c0000e4800b1007580b802e640a4805a00080283e4010713401444141420f101030508980103004455181d40c664003002d003503400c800381191900c24041410f60410380f05425503401402200c9003071001d403d1100f0000d1100000c001d0140030b2210642601d1094502580032624160303e40711800f0140c512600014100a4050340301035449400003c00f100102251140da160303000780350021441d201548529940b2040c103418140da041c095150001600e403100b8040d015203030442c0e550b80c5d80d0781c40800300304001c42e0070603007000b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 502952697 1250 502951447 502951453
    0xc0d082703030a081315092a06030b0d020604081c17040b1009050a060603110408060711010e07060c021c11040b06070501060806160c030818030c0706050c0f 69
    0x140c64a0100803115004014508440241da4505100402c03032140c040041040b1494111010313403041550090701c420780704051000ca5150303960703c00b41c400959080011441d0f0f1000e001008601e0107588080c888940103002b02e1780801c01500020455005a800180c694100c001600d40790803003080c000044201900700344000071040c8412103050350009200800250986000c9000100355100384001440541001d003d00c0c601001d80c40d0141c400f0b403144d000800e0411140394141d680705000e40d410381d07106c400204441e59a03090104c4038a1401c0701508425542c0d03440c5680074038028031158001d82243d8032030100d0201c451042c030000c207100c8405641e8010b9101c11003070000c0c2d0b1718082d01841a4040764042144525a0000703030003807147c0740d0020065840d0042c0001d9800300821070a12511000300c40c010b85c540c0c034039819600c0d610782600080000e05140009040c6529000301c80301e80c48550b204032400c01c0600595540342064a8104c10081500031035044154042001004080701001c00a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 502953947 1250 502952697 502952767
    0x608090613030807050903010908090109061d060a14040801090308060102030a08010603050c0c01060e07030b03030a09091517060907090c0912050307020901090e060a060302130902030c0d08 83
    0x401c481c102401a0090030895030354042441d0500c1034058503100303800207000300b0001e181d07850100c03065800030b140640840d019210014106000d2808080e244081c04806030080c007041c002c0041952040c0c2c47c08092100c00030500c200c254104001d00701a040715400014616454100507241e810000e1001e41103500400c015075429500208080c1101c149050206164030340c50190040f074005d281c0c031200e641d0700e08000002c0e6002d101c40c815000341c007507490401203214920306040d1a40b06c2e0015510100d00e9110080041161030740c4071400030000d080621f800d9545032545414071403540d10050350168132080900200c040d00303009080c0200006031081141c12403031080541011b005110b08064030100d210b4138400d1050030f10450300307511350040104200790f0719a0071020040494425440c1144680400209200c041c1d00c01c81040d640c00618801130309402c611440301420b0345a03400c80e01070103074109401c280d4452590106280380725060300c41d100d20308500042244021035910704141400c41e10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 502955197 1250 502953947 502953961
    0x6180509071406271002150601110d05030601050f0705031b07060e0d14030f0a030b0d0b13050a0501021614060f041205041503021803120f0714030a0906080906 70
    0xb04840704c68946440e5107400c1030058201d0402c00602c0507102d90800c1074881d00181840d030200c0c000c0700f080d021a209000e82c0d101c11004641700315040c0010292540075048510043d4003407806503a21103414541289002010ba59a14050300300343e07401c9825030301c082252402210a000041602ca400c20700800419252100007080c0c02e003040c60490141102250305010b20444107481d0070020601011695aa51b0307054400001d6400384560600185ca400714140140c540000a0314510780c1180402045071600b20401002120000c1e0844d0503201d208211000220280058400c105810300040d1450b94103090141a00100111040706600504100a10a510314000325080b03604008040c4002100e810140c9040c0302d2508a002000071304c4120300000c0d641070300241300e004901451040b00740d1003c4203240d503c8964440f840c046070310501900c1602281c02001d040ca840c0240b4012402c5036120344000e00f1544109199070024074902000d02801d604130109070b40154928000b0200da2801c09 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 502956447 1250 502955197 502955209
    0x10020408150903090d060212010609050111120306090a02070b0109021b0a0503070318121104060b09030a1506120c1a03070c030f0903320a08160303061805090714 71
    0x24200601c100d02404105007403120759810383c1caa4121008c40b1308071355616510081e100d0551481440d0028103105403404820b80c02040d4950300483e140b0b1802e056880e81c0b400c22248510061114510b59824461107001c9110451054000c000c54040181e03252800201c800080e003e244090010780c1c4606050400100c001007141e500136018505203502103006511201c4a01255110049074109402c00c0818062410080907010f03038211020400307180c4e1105240c04034059108119810b4001c2c480e52404103180a91010061040510002c0c1c0152245480880e1280740f0100390b6482080700302c1802401c114481d14149408011107560030f5241c6010002c1c41d20307000320401070421400c4010705411900030000c034005160700819162a121001201296080f07000c43d007070000c1442c00040d105101c40100705408103a410821452400c0d10400780740403580c182e064110205559000000760b0070800610218548030340718800f0403141489031305d1341d24200c025004022a10036620565505548030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 502957697 1250 502956447 502956457
    0x90801020c03041a0c0f0f011a1f0302310905060a1e0506120403020c0a26030f0a09030507050402030118050a0e0f280507062010020408150903 63
    0x5000381300065070185540c004500a082c4007002c18030a145000a1421021032203000c42901075000b0860034021600b03440815204a41a035001100748240714009040c4414a01030b101079410090b00e0200b4585e504030385062a03440c40700c902e80703c0e04c00c00c143e0003044404141c01480c9454041c005400c104000401100940c45001251542c40c3c03905410308540030341c00c200074200100140d4440001b1741c1e514680300d004940850050003400c4101d140c42c90606450001d945a002c10501c046441000c4181c494040c01c03031550103803205000310804480844001d1075114026a94409100d1561a00c0c500c0d041c4e80c6c4c0c0000d40f18500500040c0074038130300340060640d01036200780c0205d415120200c81070004c11301c0403c07540031030140844545078101c0000740c0c14080c04000310030720544035600c141c0409111100a008206810a1400304004c45c401c10201c4103150b00c80c00c003034118160100c10b01d80381070741203c4480c0c20290041810030403130000f409039450b200700c91004080c8a1514901c107549a101d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 502958947 1250 502957697 502957709
    0x135160212130e04030e190f090e031b150c19050a0e0301060e100902040e041101141207080916031b0504020c010b0a1d070e0628090801020c0304 64
    0x454440c000b06800024500180681d40c1562000d05143c2401400c522803e80c8440c0100c2c500d4801d40e243c0180d850b05581102e498800c2c41900030b081c00980d5014001038080d05400380300c18031140442065000b003001c2ca00d0b6504c0c000b0724003045441206415020024240015a00103201c5a2101c184250100413001c101c3c1c9003042e81d4600c42c0e2402c1d913005459016440d010346ca8050080703100694280107500520703403044a100c0135070791001d403141a03114038040c036a03c0d42404004038000400140030310001c00c00c1410002140e0061403948109500404c0c11203544072035480030712450f40c0d00700c4000c1d60001001005490111100240d4a907241982d1100511001c072812a600c42e200727006070326501415005009550f28002c00c1c500c18060000628400e20038164035000217811400c03e02031441d0789101d260080810f58a145c0159024021211074503080705081182c42d41781a40ba0400c030f00322003071004c1e00020b20740780b215000f4000f450300d811600f01603204000d00550303480e00105507821552 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 502960197 1250 502958947 502958983
    0x1090f200a2d080403091d070e0301090321021207030b040c0905010c12022505090a0501051503040804090e060a0b0105030c0f180303040b0d11030f011401351602 71
    0x351460200c1d410165031f07201d02450000d004030f4000180c0042d844c41d01829003995030380e04020800341090700320b0702c00c04402404103820744003407a500702800842103600b1510180c01400d003a07000e4002e900070b0380c040b2220b07030000b6952080b0038101d207040c1c41048007111407803a10620490500c0006841c0480c03500340542840400303021090b646208003c0e002202e102c0360240310039008510362005040506000b8030b07214203614070000380c07400001c1c807440d0f040b901c00034000001d400200212554652020b081506d403050100000714003040540211000ca0000400500042ca040c0691200300c601c0782c014581000350070014403207855400c3e800d4400c10010348803241d41d1004c500c110000c15402034000a50103000c0494002401500b1a000c0c2007602c04542043c850101500126025448126a42d035410290340c401403000c200074005000c10900c0c1810000080740c2405098240700040000f0b9900c004009200001c1c0c0c180030107052504581800c00c0d6911405400602a44410504003c04100c1ea = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 502961447 1250 502960197 502960201
    0x516090b27040902120d080903090d0f0302330a09030206150a03020a061806020c0a092c06150303130306050c0f030c0d05150901090f200a2d08 63
    0x2e0790380d6211090003607000b8200c540b4031817000010350329541d81214410104002c03100040803800c3c04012190b00d190014111900b003580780d80e030080300b40c580c20002c6c1c08521480a103a00740002c0040c0a00c4030400401110b00f12180d12813108521050040002845034180000000003c1d0005441604608005018440310301c10001154014403207a202035030203041c6690000d9400e40202c1c0e02000f0300d400c0d4141d80d0a640d15500306981e1110040399103034100d03042c4101006100c0b410b030711407504941e2612a088448151010440b510404038032001a035400650a006000360341c24000c0d1000501507002c0c5003028a034000d5003112140510000e0101915440040d9070100020110780c0180d442d40107442d22401d11134005141e580200a44d4080986440c0125400e0701c65183c036200d100d40010100009030703007000e01390006080d0422042401c15140c24001c222503240700c0c003000c1441c13074645c0040d444900003a030041009054022802c4100060100c80000c20b0040c0103006e014030240c11b000b00b481e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 502962697 1250 502961447 502961449
    0x9030b010b0d1b2a05030409020d0e0a05060f04060b040c0315080703171e0a26060306190f0908030f01120837021c0504060210090204020c010516090b27 67
    0x1104e0100e01c0280503020004002ca5010003503401b8056a0076440000c008000e44800015078801e24550b001e0083c0c1c0c4444001052200d00b070710102e43c020311414011401386188030104081d139404d035911101080c1c8800c20841085c0426611500414180006020003891621036940c01101e0102c03003814040002081400e100300324035041800d1070b079125515030340c6e886140c008107800e800352410301d01a032104200d1605d080c80c03000010300485c0003e01426854403840e000c1da161102803444400d60584818032000110902c2c03081c0340495000c3c0e69295601d250000400080000c140c1110384541150815030003c5641d180c19100030f503c0245226040c64001c0e0610007040b81140c134191104289003034500080b81c0d01280346a8038034184500c06062041c4030f0003d172000e000e94003400c00141d0084000c040900b01c99004142070b0307030010780014a850011007500c0e0964800722440b1002540311341ca81e0305030a500c118000020420108020308145040c2400320300c00d89004290440994a240e1000c09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 502963947 1250 502962697 502962767
    0x507020411040b070b0108030f0f03071106010f080f0105090a14070504110c0c030f060721050412020f071520010e0106050f0a030506040305070309030b010b0d1b 71
    0xc1c140d2004642e1159a1400c0e40c0e19a40e0000204580ca146100d00006800c18000156010070250403111030801d00c2e140c1c4040c01e140c1001300f90800b00000004024805402400f0480c041c00400c0c41d000034142c28012841d03d402404544441c15a15180410540c606c0106418214a901c4000c800f401c2e041c01800500e4154907400c03c3d60710a282000040d405a0520001e0007084562429152380290010070503440d001400d00d595004d0b001400054248c1e84500100c15000c0b04010385d501810801d1030f041c10403540119411101e09560460410350290104440ca040d6520034000303054581c2403034108031640000c8181f00051000c0c045a41c40c035040d4100b00001c00c1c41c0c2e500b008000c1501e000001c02c1c0a000d152260a0007483c40081c02d2a0908280324201d0507070390018020b00322921281c3c1d0031151a804160240c0400070000e0001c8001080f01c0c6c0341d940217100500b01a07480e8280307400da1004568100c0c0c04011201d25807242c100c1c1150700301e056003144c2e03201e030034004080c08107241c6a446 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 502965197 1250 502963947 502963961
    0x303030c09150e090705031306050a09050105150a0e0c1911030d05220203060610030212070908070b0712110c0301060f14220e01090b01080c0316060c0305070204 71
    0x903400d001d10411072a80500c0c824160740e0110703084120307520341d0317801030300c16200680352003104111544114001c01e40b41c1e00000c1c1c1101540350001034982c09a25000e0031581e040d02e4210220800b805000e0311841e26801000140052004100d800c1c104220000a240f00790b07000361401c65042040d082e00c0901a201e8901c4c0c5085403030a40b0b07035918244030f07048018a0100c40e8140c0c0700c945448041015a58071070a441142d80c090000d00c025202c002c20007100e500100c80c00d03c1011b03001c10100400c0300e8110082801030101d5102c005400e0306160201e400c003e89a00621041c100c00c1c880040800e084100c0e414021034a4284801040b940e038940747d003410052407255130907600b0020300060b103615491603c0d044603040c1003081c00100c0f044c003c100081c0300e604560440e034088554170302c0c1d01070b9550340018141184000006246078080e44e5807040345109a000400c50b40040a04900303a060038042103000704207a05c070b0700a41c07600300400508090580c00e07014040040108001c4115240e90b48440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 502966447 1250 502965197 502965209
    0x102071203031401060905100503040c0504110c061b042601020307050d060515270306040803010501030e06091b0d0510020913091115120a150501180303030c09 70
    0x20500001a04014001d458000e4024040343d24507400003418500c51101001034801c010b03c88020041c194800b19000d82001d8400d60300600952000950b5070345511030407000702990701d174198413180050303103103401d1610003005042c2c010008550308040041040403103050390110400315400d044003a094400b080301010085800350300c000f040c0046150004050400109400020312041d0b8031030303080c080008410040300302840001c0c800ca08029480c1c203500c10a0282c000d4215000d040002d00091400c0380a43e02600c11120010061105580c103010f40070b1143c1c40200107210302d050185040742e0701c0740485005111442d8900f040d8210b941c03010442190244c0110460f07170f032804089a040002d40c01082118070480140540c0141406140200a0f03c0c540281c40000d00700302d480c00b070044400301349140300b2002404110031541c8000319030595018400700340c0000746002100490884900c07658011b5130510080c0b424182003041000f5146c02940d5240c40c003c2141920b442003a60710b0300f9182c01c20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 502967697 1250 502966447 502966469
    0xc0b18040903021c0c020a091a040f05060424030308090307080a03091101081003120521150307150c022205070e0d0c031203061a03091e19021207030c140f01021b010207 74
    0x402f107040000d0704840c1c040c010882e001c000701e901c043c2c004960407010800b01c1c40000041c603070800c00329000e4090241c1c00300f600c1059901e0940c4540d500062907201090481c082a59507039034205000c00225203680910342070a2900b00d0b41440f000c045000032280c80001d1400490400b0805e5040c4036001751129a005203c2640c49501240c41440c103030401202d120900407061a20403010346000940b440c103c500c002484427001c40c0da000100c80464031040c1c160303000f14413020215602144040145400c3c0301d480710001c1c1c1401c00ca40018111900c1c1000d6905c03074a0b03c2150540458900078414040342d0780500c9181100d091a24290041d00140d4001240d501c0c0d03561050700340c0c580403001144110703502c0e01a80c0c0c04114019142400d402010b40c0d0101076444229460540510190b4480a00740001c00b40483c940380701d110b180c40d02035242c00841d030901800e503041104140c20310840d40611012103100605030104030000395144410030241e003401d0220442c40701070b03034024080040130705400500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 502968947 1250 502967697 502967711
    0xf0d0611070c0f12110d05030f0d0e010e03160609031707030b040f06080d1b0c080703110402120f10030804080c1c0302030708030a02070807060b03060f040c0b18040903021c0c020a091a04 82
    0x4ac00001c0c12400311070311595082085900254a000c000c48141d141d043c6103540d10300c0844c0d25072000a01c82c80710210140030300030300a445040c4102c5500c62041600d5030300440c5245100c028070085d900c040701c801c41e195040042c140104a00802c4030908010b040c54032540144031002d8041031100311034405080f40080c20b0000c5002a80810900b00b80c90252016001d00d00c21b4100740030807485400400800c1ca0741c10710208100340403003442d068102d0702103005210050b850341c403a400281e00035032040f156580421118a81803c249421500d2200021400c0f0858680c80c1c4000c1e45030302ca6018001c0640d840000000c11001c02c0b41d0682d071200f6007203204191929600e2618000522640032028404d12500300000c0c415001e20111030b104079400014022401e2411240c002203070004921307030303084846120500000d5103461043c01c1041d0301a80c01862244071030b07079810b4001c5010a01210800101410503001f603102c03504800101e401400b00003c0542800e020f6203001c8440c04130041d1301c03500303243c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 502970197 1250 502968947 502968967
    0x80d3906020d0608060c0f0315060c010f05060112141501090b07030216080d0905042c030304020a06051207050d0b03061906060504050f0d0611070c0f12110d05030f 72
    0x4480001d644c8002d00325015a10340300301410b0345003c1c40d040c40e000c0010801c006071030800c040e04264a054000340000b82010340c2060b40b1405d41d00d040c0c6000401a9403541045030307960340400c40d00030750440000100300742c8401c68035000450303c00400c2034240b000d488035026070303e03440390310068010101c200c0e82a85078411841d00940b1028001540d100045030b02c1c0d07021038004000308a40030701400303d41318051710900d03180a010140c420412555a48019010012003c071003920401052030b081d040550340c1c9180034410401182d205400801c20003100340000d1300782e045d4003410150001c03924182240c540403140f1060303018000f6000020381501845003031011025400107078003411425204284100c9449140c103c40b94029485150b074441805400308505051080c8501c408500404001c0b904803040200800d141e071117010110b5804014860411010006c403840308050812007d101d41ca03105151a50142e464005043c1441095040706000400004000315903120308820929600c80060407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 502971447 1250 502970197 502970201
    0x31902070e01050f0d0201031a0604060c140706080705032a09030c150d021308010606021b0108060607240e0c13200c03120f01080d3906020d 62
    0x1c8a8544254690400800c052414074075580701800050000010703c2041d8004401900380c1c0100c0e000701000c03248048140b40c441070b0092000d02403e41f51040640c60710702c2c0000002c030504060741955003011200303010030344d404081c0540142c034038035005440340c0312103c1c0c01c1c80891081c143d0303984032064200b1030000045000003800b01ca520403001d48041c0f4042c0020701200d07100d018002c24105000b08001000801554087c2c855080c030340b4440100c850f200d00354942198287d4100e28050307800144840c2e048605240600c034568400c0c42d207074015043c0fa0303000c1815030055050007030921503c0c00e8000d042480c01502518885540c480c1800409d0021464980328546241a24014554902c88a00481d9540150120403001d5500e000da200189640d85a198000b0021520580810860380540c02840703040f5900440f8418180e44855240003010b61030000d89080002c103010617100348805011024900400d0821540e040d00e40c62400e0b040d80b00032030720082100400d000c0c404945030803070704220b03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 502972697 1250 502971447 502971449
    0xa050403030801410901260601180c020102040b0f04030b01080f19020301020706051915050d24050705040f15140a0c0f15060501020a0f0305130e0f060f04092303190207 74
    0x54401f120283c04400205030705c60b6000d001b4602000c95600c1040d000c550b007503122003915181813000504013900c2e1b603d0080583d0002134402c861040104050040c8240303454903d00601041008025072410030000c113071104101e4181d500041c1c1900ea070101503403002e40496460640c05141004503103400ca4041c102081512504210340e0b103020340c003203c550f03040c0c240d00b0141d40004096080f1032102d5554003042c46240308141c1071003060000100e02c41000c03401030724060503d43d01d0312a01c541c01c06d00341c19440042a0302a4109080b00070700701d00030070f030401522071001c1c00c445000da0b0f4071141c0c583c00382c03000f0b035000000910b00e0100150020a101c048412859102c40b26241400749035a11401260707a041d0508018111a400107034800011b80030300c00504251750000100e140072a9102c610a11802088507100f8641024104100c06840c0c0200d41070042d4004980c108031040c0151564614050268040404003001810300d046001e410015150700c100101010f00c00c94401a070020344480d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 502973947 1250 502972697 502972739
    0x30307080103140d1b0f1e02041a0105270607080c010612050d0f020705040f020a08011a04090f0e12130503070e0720030a050403030801410901 63
    0x240c00c02507181c030880801c0d007101c44c001d00e80d01c154406200250720180c1181d03641040722041ca5201800c000502c0c0300f4002940d0300c1e8200d29205000d00c4d10300510050794810192aa9181e01d0f01560720203d0385c00c40d05444900621651940b4000d000741c08000c0008440c0b8074044e400100071841d4810444d45c2002050321140100c000d007d03195440d01548007006540e14020495000410040c01e076601c596086158459248100c4507650742e070b580418110f981c607012011050360002100c41d0b465800c0540c0314018201080808228000180c15070458055401040c3c6441d8a07044004c603000c45980143c40c4d0205c0c0d903019a09901964808084c0503449141d000e2802d801d01d80e8001503d20380810b4110840e00709048200031640d0340a0b080310403c2e10003100c21008242c400c4401c000c03880803c003510300c00782d035074039515079644c2141009071802d031050340400c864640e500342205528514125010500480d48480000454109908081c40141c0c5042c01c3e041452100002340c0d614540782e04400d00c0c51 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 502975197 1250 502973947 502973963
    0xe16050a0906060e01320301091a0f10020120070212070308090f030109050a080c010e0316020105030709090510061d0306010e0603070902030a0501050111030711010509060c030307080103 82
    0xaa01c40c0c07054241d80c114410003020409000c40040c1a50090030642d1440c40c2c0517407003000000740d0000400c0104040010070507003140120044c050003040b48541c04200600401a0800d50703c2403000900d078001600200d4080e550740042000c0390b034000d412108410803540e62000c81040c03c01070010282e045440305901c14800d03078881583e046404244002a2504441210f1a140e4242c0500c00840b648803010307074156607101920008190203100650b1420f03c00c10149a854205400441c2036811990751050140c000b006030101d040f1421b10354840741542030030700c0c944944d02d540050707810130056403114094074140410880074203000d0380e401003980c140341c442036070384220100000b04501ca03103510b00d601640014010300500e4a0040083e9002000030200d0b911b65807915021000d0f60010b40380d815000340c44a005000540e009a50301da50320250800070350410000381c0b40d4858041c11100c2443c18802c0c002400281500c1321821030382601840012a80d40e42414800181015424401554035003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 502976447 1250 502975197 502975199
    0x319030612150911091302010f090b09121f09030216060c0b060a080312060301140613020a02070909030e0f150406050c0f0a0b09060105010f09060c0201030e16050a 72
    0xc0d9100400400c141d0700030010302c0c0e80140d1110b0203002403503e507500751020300e46011000c00c1940c40c1d040d5581b04102c070740794039240c071074039440050a20001320b6001701c140400c200040c014103180034103540310f43c1011100399825104e42501c050a03c25042054100710005031183c0c0c0d0f032100c0300d0b00700c4e028003403282d0708980f6000040782c85451101d040e402004000b40d409445100828142412240c100744002c02d800300169681c600c0c40c0ca180c1c002d108003001c80c2d05000800c00189400c0c800d00705c154860411082040c6030030350000e1080100e089080000aa0102c0c016601d00e01c01c0243d9400303032800450412002169040c060108091391061700c1c03017440701414540f03503410048594602060303406071680c2072504201c0d060b5060740014181076540d1045503440c55181d0360801449440340d000c2c0ca81c440c2a810481401404d01005030462070603c1108608550301c15800b0780c1e9a0100c60f8145000c40c5012100c3c40101c1c081e26011515240501c1581915003410a441c40f01a0071541c045915540301 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 502977697 1250 502976447 502976459
    0x30506010915060302090102011509092006250f0305030405010c0f0e1002030d1d06010e090303072627010608060a18051507120b15160503190306 64
    0x7440510b0032000010409010800010f0300a0b000b828124005000100c3d0540c2442c601d07042e943d20baa4070501890b034072503c4a00c00e009c1c203803028080f00e40c4484410b120350740b610070100e50a44103494501c1c07141d281d18000800318150344003109048a81c03101213807071101654103000304190001d0302c0a032069440d001403c3c3c2e025018140380c10b04500c240c1c989040b20810b40081084611000c540325080d400100304060101440b403081c1d4450030040308090322644613400f0090b02d07001058002e4070990007100240170190030300009403540003449281443c2c24040084a000f1b0140c4e10281c1c09118207400c00070310692120040d404140048411695004034160080f00c50a982da68410b00c8c40347d401c0100400d00e144000e421010ba0600b102d0004e90381c854040e65420b26000e04c800c54185064505000c0c062182d0340840e01c1540300d850094184072100103407000035000c400300210640041d40c0095030300028150700c0070030b03641160410306481e11100724041100741c0012062482c07000074900321000c101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 502978947 1250 502977697 502977701
    0x403030b220203070212031f05060406090504091e05010506030c0f09010308030714160219150f020c060c060105091f0b2b0f05060303180103150f06090305060109 71
    0x1c00e0380003010306994000d070000350800a41c005413050f02140581d00c0c0111105202400a50044901c0200034820703040b0720710070116249603904130340c0c85810100300c10400726030b2107100c400a440080354002030401c03151a10400308101c940030149510621442d0106010065000511404003981174449283c0681c003009408070003072007000d0b4040c03030b070030010b2000c03e9140380a99402221420700d145551051203400c04140c010200701100000017504800441c284141c407024900602c5248204050032300162074030540241c4110380c1008804440248846d108020f00d4500e088007420709541c94022120480e10750409014041c05104400c021603040d0700b43c0c0b100c480941403100c406640c0c150404410f624564044902030021810035016250a0115404981d5128121200c002103d80040801509803000180050f10036001802000000008010f0000740e40c1c0092a001034080c2e203081c18102100c800d82c100c0d006030f11211170081003c81d00001c501c800c0d03038022811903001c1c1e0390396040c144c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 502980197 1250 502978947 502978969
    0x8090d030b03030a1b0b2701020f16150501090b090112030c02100203070c060f030c0e0906040c0507050303040309081902031914100c030f0e1b1c0302060403030b 71
    0x14140c0d004020a0314580c2c0316080c01110b00c6444941441c174400e113500d0340742d4081026a03000b03444019240500361451583c0403c1405594500020750610b11802703103082450003600d0749443c3c1001d0f2400280200700402c19042028588210100441e58590032200c00500c60f136a2028040c01204001181e940382c003201041a440d8980d46810404610b90f09001e07040080340c80b00c0c01948410b0181000040380d0000314009482c40da61120840380d040321004095030641061481440f4600c3d0320300445442e000d00310740c1d0000090f9400310b0f54000030031003240c65110f118406091400040148010564840c0960040783e100c1d80403203044590051440401c0842410029890740c09580915090200e51154111503030140d16500d0342e40e403c403004542080c1c0366111110100d641c036107102211070341603c20070b599070308110385c00c10a91070b010028a03600c8100c81144114404150128140356582c903841d221440514080340101403003502c2d0180d40d03980f00341d80840100f42000c1c130700085410f051042c61 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 502981447 1250 502980197 502980199
    0xc0102010b010921051009030302030a050c1903050601200a050c1e040b12010203130507060306080309090603030c0a0803011d06010206240a0e0901050a05011802090604090c08090d030b 81
    0x80070303403040e10180d4121380d81000341100c0d9405180341d4480000001e2040203202c44c000d480150b900d1428004801c2111001445054201c6088c00b2500d20600500c03540c042c96000c90400082c04d46594005880c0d9250080e40080a169000443c010120010803010950f500c07440850301080705180821003082e440314001002d0b050b800713120001500d45900010000c040181c5030b4440011202030042c26a0302c03c031010800d444100c2c600c44108001002100020b11040c902001001c1c2096001f039181d1240c0902640305030400008204a81d07814011554851248021035180305424a05401c540d0000d1064001074000408584402c1140500f00c070302c11001680542503903900c5029104420103079444a1507251203401c510007031382d280e110310744020341b0705c0300d6110481e0b24002c0c0b4594203640c001000e5000f1582404010040c0c4004450b51010041f0240c80158442001d140401d242d03002d42d6001a1195080c01c11841446070030150850098528005451154403900c03401c1c2d00f80c032000351240d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 502982697 1250 502981447 502981469
    0x50606030c0708160804090e12180d08090414010e0c090a06030c2106081c020c060f0d050a0501081c050406180b0f31030f110301050103050c0102010b0109 68
    0x80c0e000501020080c02d01681404c0c40004003101a1660031454000ba0000e0125550b100084000418208581495241c03548181854040348116610440d18032111b00c038021005113030f11308100f0180c0400d559800300003400c02c020648000360742c1c451450b801e12070369002e494500041541d94454108651031220043e161418107440d00104030b0003401100011401c010907004d40302c09030151401c000980d5101c5480220f0b4143c10400d450742041082c08070f1601003040b81500c0b809e026004a035800c45a1030845286485403110840740443e03110761000c20a0003803504041008400d080d0340168142c80f284004c40702c0305401c8034283c925a120000c41800031070410310081044511410910800147c41c1c0d11002c40b644e0340c0c003038000072a00846651030382070b1008101e80040354440d00203407048940c0400400e440186880c48809090101d0101502c1c96121008e003400b40450580d0400b17a40c0b4014008100079a9139040564540815012607030041d42000711110707056211b4030a19094840702002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 502983947 1250 502982697 502982707
    0x1a07020123120a0b0d060203060f0a082806060312080c03190b0117240919090201090302180118110d0b0307080a0c091d0a12020708030403080706050606030c 69
    0x314a891030042c05011070320b843d0304c0c030400c282d20303070003030303041c1030038411080540c032810004100300406880105880c050748200c40208070506000034000c450304031900c1e51894030304800a03000441c6210000282000382020000810042c41c40d084e01000c6015030740b5424540c03285100800c880c4802d41f40e9181480320885400c50403880d07030b0304c113440409050401d02485100d5a803000c5000d0b00807039100c2944c0315410341c0129485854021315480c5401164041040c0c41c24000c0c80804288103090264031f00e81d145001000c5902030101103001d55001001442d4040d0a9580c542c0401c0d800d0141b80094001041c80290b81c000c07038041d024040900001e140d0901405aa44c240103001c219051545880b0f00d110015200d041403104c1c54100380104000c5000302c0c10900500107980000c4041c1c0e490004c2c039801103210790000b1070074005103540099030645500290004910b002401d40050145000016000041009040c018000036214080c14070160b0307105400c200e07003800111602c3d034442c441000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 502985197 1250 502983947 502983967
    0x20118080d0c0e1801080c0402040303050a0302030c0f030a200a09141915091409070302031305030307020a0510060b0912070b04170f0106051c0c1a07020123 69
    0x240340d180d1100c3c640100c00346140d800090122907810344064888180900500410905119011000c101500c00750303d0281fa650380188584a151030758030030550b01001284594680c0e5080360584207030880020b407241480408030004120001d8200c100100e009201d400c00e00b5002c0546d0b410103510340f582c501c890311b0300c141d0001c442019440d0580c04080c0251005c1170341d03a824035400c054030034011000c4962003503940103080001c1a4110410b46030500d580134526654094040b607020510340350160305d03a11441800c0c2e0441c610080c000304140030110030000665030011380810214007810440c4d055004058550f01182c3d85409154030b0014204503101c0c880c140403201400700c030500000c41e00050b640d8040050f05400c40c2d0003441c03a4070070b50032000986d210100001e40c1c01955801c0200301d40303854003001405044042c6a43c4d000d545c44c041043c4240702d9032811201c0200800c2c1f802e19082c0203190500c681035403001c0c00c1280820015100300002606210f03030360808555480b200d0389000201d035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 502986447 1250 502985197 502985201
    0x150305120d0b0d1a0903041a0a0c020904050d1202090f0409020a0e07080403080a0e0a021905090c030a05010e010e060103092406090605040213050405060402130e0403020118080d 78
    0x5844010458032040760780a83d48400d5507940b22640603818003016500d407210307400030042c030151031008583d209010a11400c41000f1142e0f00910208808030355500c090b48081c0c039940b9a10740e02030340c449901d80c10401884008514149800f0440d642c00c0201401d8580203422402550074094100d100e0094100300780c2443d501c01c8000a0008004540041c1c1d5107020350741d0300008803003050004030700742d0610042641001c0c18542228250034184001c01c1044401540c5400c2d60501074810301e03c10407400d101030118100500a054098102ca50900d040d80e203028071030384251111240b0503e000700010f44841c0890001e41a00c1031100c400504e521450b004501500000c00706030b41c1c40c0040303014400103410351420001d107120307070f201c0106441e4500b09001c0308850ba55441180190300403c03038640d00c0b07800c10f4011415a10100d80c0001c0035140c503004034000b40540911000300c03210340e1001090030b00080403040d00c40c1d8460341c02032010101e165205c0c5003040701480001c1a4610074450390049860035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 502987697 1250 502986447 502986457
    0x911040f18020915100e030c01170411060d06080105010f0b0c1911181510020a020108310b0a090213020c1c050705011407051c0b0d110415030512 64
    0x40d1300300c0071401141c000107459214540140004038032410781400c00c03030a0900600340b903450709013400280f203980d01000c8011071100420040c517a074407000f90321401d03503100c01c143c806206940b02c08010f403d0310703224024024402809420354480442000055044c1c14000b125901016200a0100200044482c44c405405e10804079100843c410b0b2811440e2076090b804400d0504800d011001030511002c000d40200d070355444503004043c40c0940ba030744980c000441801140d42031816112560307a40c012042004c06060b94000044524a03c40d1440d050300c100c0358805500601050038a03807100c41180084aa00d108025001508034000000090003039010300707403002548003903802d018403c001d6511354001102c2c0350300200b1404288107007801003d12030f032840140c0c05012b00c01d00b405c00030806440e41c015001840d1310041c911420381c08d1400103412814103003e01170030141c01c50030103260034980100784902c0c01e409586088600c45074065520a1203040700d8004c2c0113002140c003c403600c5130341c40d48a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 502988947 1250 502987697 502987711
    0x30e06040b1e0715060501080a06060f0e0d020415031202150106030908160804080c01031e0216050f01020316021b060d110f09090c0c07050d02130911040f180209 71
    0x428071900020404140c51359400d40150000051001c0c00c000024000c960040d10300c41c0c070ba44c5030100610004d034010082d203030001c80701d0402154807013200380010540000b29000a4215080c148000d036000c20500c081000d07207206800a6034940081030040303039140032103440301c400c4d444584010081d80c1c0c040d50001100d18024a20103140c044258401d4445040000c01203410190004003049100d030140310091000e4800d1900307001801b964620740741050914650710701d10590005100000880761009140b1259012054926024201c800c030743c001d410858001101c1c03007030591502180c2d440841c211650007500030000c201c41042100b403001e141c01144040010550b551144000d90303a104e00640240f810003100b050b0394003045000e101107044090b011040e41c2505000c59254420040340321070a450099544c2d83c4503001a000040e180e005d14264204031500e440c580b00e082c0220740d020f18000d0003040c0d505004d521070380c01c1c8400c202d4001d0713080e01c05401004104e4000524003c5149030304061 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 502990197 1250 502988947 502989007
    0x14090601141215061e09061201060e040812160203030f22051006080a030c110d0b1812090a09050c0c0f16050910060c050111031003030e06040b 63
    0x42c2100d0880e240c490034522940c0c107a031403041080b10354a40703c900e1144070701e454070410a14407214804111404c401500d1107200c1c403d1692207203009502540f00030010154902d0f403072010b0403d0300f080e0364a54400344002202488500000b000c40c1c080560080d0b01e0081039004500d0340c2d442d0340c4d27000d0500d00080d117103a403500c00a00054600031180492626602d01820140c00c2803444000030000701d80c1664004512030300415000c101003600a261010304076004180c00d0803540b2002c000511500d90030300000c00341c0001c01c007403200032071071076090304440740001e4120f4500014400071002e4030b000382c3c0451a44120003136030a018132911904055044503104d0721035410007e80d40480c5082903030441d680c0d611603000c01601000c41c105d420f141001440c041d100d2400b1801c101201d2041803005004403401e21240741004010080258880d4050054034010151641407891141c10078100034842a00050b1002010214138a0035001711002c40380340b090850b1903c2d80001803040c2c0c0581400050b00d901c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 502991447 1250 502990197 502990219
    0x17060402031e06301e07030f05010e010507030b030c121216020306070305070f03020f120c13030507090b1206040f0c08070906061e23041a07061409060114 68
    0x1031007802000c00c0070710041d0110000320149a04c11850501094000041d0000c040c00c040040c4002042d0300042c0c03600b00c8140100000c0c43d041060240801c0340100140f503107000204222181d2643c084010118100d054076600b804c4a410050110480980311030140c00503503101d1f41c2810084010318808180d489101254030071500003d082100440340940400d4603401080b10881d4448a034000b01501410211b0402c000c10362000e4185c0039184009045d0a00140803801000c152001e4842c142d0420501418054a81c90700035143c1c480c42c4120018a0f040020003142841d200100700c0e0b007020003000a00300ca540b651180c82900890300c0e425140107424982c04a48694140a083c0c040c150002c0089929482c1802c02000c0e4400b80054141c0c0c1c411111855068a07800b0342c00000e1618136107419103400d0001e03c202c5001d072240d075210f89a8070005003044643c004000c0c4c0640b01150107160108840c400001c840c420708002211902029001b41d4018000c001414900e1250008050903040d481 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 502992697 1250 502991447 502991479
    0x3060a0b1804060506012a12090b0c010b040c0201200708040806131a0420031207051501170d080714070303240b0d1a1017060402031e06 60
    0x44040c0d078103035182c0342c0f11010000156003140d103e40e0f60b01e1f400c050000200401c0050310700090307000c000051203103000800c20195903114034240710161040102c11903440e12800107190080078000e503540d01940c20808400031450040c82a02982e4888040340c2090140307028541d00d465200ba881115061018800425801d40c00c20540d4410030074140002c9008125082c034a90006000070800260407a22080100044514008480c14020800250f00d1440c042d030010382880e03415112100316150110b44141401f800040300010b0405405001e8800e036200d841508401c500000d855106611401c002d84211f44603c0712154040e80e02d02d0540d040c80c4006d207068001c1e5105410550000f03840d210041c030105144100900c80324102d0b01c0201503a49007a09189107400b500304104501f40d5106800d1909160120350300c8108032005082300350450064402a080050b01c00c41502c2001500d000610241424400c80b40100d0102280e500000030100394280c0c44180145441e42040104110000b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 502993947 1250 502992697 502992739
    0x18020415142101020a050d1b0e0405060a030b1f080c030a0b091015090c0f02100c050c0d110d020d09260a030f020d020601050f010522080106060306120203060a0b 71
    0x100d00106d83d035041e0f840c404440010142e40500b0310203003103048520342e00908140c01480001643d1426107003c1100c7d030301c100c005a20f0003ca54070203021040103204103d8051203034054070030030344213550051401685401243d0b40d90030242da00d030360b019804240c9443c00300e10031b026800da0001058084401d26160900e450013950000d103800c45076a190b02c1002d0003074104900034402c56100c42d00d400e000a0700324100003513403404007510040c2c0180eaa040c842101510503011100002c8080040b504c2804040c100144038000c808030200443c00354000345004e0318030101e101001404c403135940380c9016060114042c20241d02c02c10b005d200c0095414000b1026600b40485c03800f95010303031900180f4108111004c0c1c1012035800b0307540b085400c18001408541d4406070441c01e07001c03080c07a00903120044407005204244c402d03090a260b40c41c4041c000107061b075054100d802a00c4c181d0343c2c14064940d0380c40440180348140500298160006c0c000114126a181c0c005001c801c00245000b9100b02e034a420000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 502995197 1250 502993947 502993957
    0x60105070c170703060c08070804061a03030f03010609060804080307080a060306091109010501030b0a030b0a0b0607121403040b061005090a0e010306050c040b0d0c02101802041514210102 82
    0x15250054101002400010310444c010440785042c41147c62520301001040e410008000424003591100800640d0481c20544101c4c003401504813503441395045184855500300344166400554100e4010684620401c01d42d40116800741c0f1030350440c1c8617a075040e20000e40c0240007401300d81c0d407104004003155003030080039074545c0100e40040e5105065420b20100c102d050b000681490700b4011003441d162103090001b021030b900400140d40b1900e03044d80c4071000d03007004500c455004402144041c00d01540d152000200c07090350f00c0b10524203045c2000018540000c5030090308000846d80080c0441c1494444114500642c3c50300e0f9240400410004003050060303004a820301007070034014000c008040c4201034018441002031400d051410403803101c00d21032800072128480d110742240c200140200250900c035601d01c0028080c0c3c580d41b050890b4600000c1a080c1d105a0402560302049128514508296000021100300c140f090b0402d100c045c03082c80d8025080b480f4408443d002040e800e2010340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 502996447 1250 502995197 502995239
    0xc030d0e150703090b100503070302040b0d1406070305090607050a030b2409010216030c1a0d1a030d03090c06210507030903020d0e010e090604090c03030206070207060e0603060105070c 81
    0x1816403117403d111a0701d920080091a5500d00d000c2c0901c003569001509404903541158082040103650740030581c500c848040c0180790300182d0482a10781c0502082d802d114040a940801003642d40481e0b0542d5000c05580d08404103008015507030b40a4800e400801d070004010b007580c25a5103800610000060048070244c00c4000041281c000b15a41071003c01d504024031200180d400d421034460201e50401c5100700203502d02d11b01d41102c3c1c0040502c042d10950203a910041161200041c03c04600b0308156080038032038092002d501000900902c9216202900030400c0702050381030840a881a421aa0f880040c402014201e1104054075000320b611a050310b036004607220b08540750203803400301f00c520014140000340c07901c0c1c0c241c2e990041268003c01000c681516840e210038002c41c0050290b00ca000c0c0240f00304407008402d15400191060280009500316146a603903580100c1e59070a24207500340d4042420408280590b01c00c00141c200c4a00074032a0b081a03696410084410041c3c21944d5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 502997697 1250 502996447 502996451
    0x5070b150a08060405061501090f0b030f132d0605040614070804080d0203070c02040207030f140a05120405030c0d0903030f080c0712020309060706020418020c030d0e150703 76
    0x2030518108804800020032064000340b405080694800b51280b070010580300c0000c80c0301aa41055038401d0078068014408403080341c440a481d094146001d500465044240d41584d00100c5c55001c800d0403080c400541011402e2043e41c0205102c1081c5601d0503c00c06803641b038282148041a00d622581380140d00c900d400103034a62a00e4003490300d1020040c080401d203c40d040801020507000d40031074004003a21500180d0740e946151041c5c0d00420341000180d003051001c80e8000415401505100c4c0711101925418100400714103861f280b13105242c010070000f0b1047c407404042c0d802082c4160707080744c450000d4a080042001ca5913107842c1040070000002040c1ca00c0800916800000084a10300f05250801161401ca9008007080c07041050051580d9101c44001c05401d1081c000d4075096040104079560303581e004e04081d4043d4019004480c680714901c201c02d020b460043c402c80b909010b40320003640c00c02400d258260700a090031012408540143d81159080e60a010745d1144074a00365280 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 502998947 1250 502997697 502997731
    0x15090e010501080d0c1203090201050d1d0c0f011b0c08010c171012110301060b0d1505180408070c0305011e180c120501060b0414120a1502030705070b 66
    0x220f514004e03100c910031041c880a107020501194440aa000701107000e400c000c100010148012100d502c1810803078001c0c28a0060880203110314080048080d5001c071089440604441040101c481c00340d02106d800b1511404d000d044210b0410343d104162401101105006070b031395844a82541c1c6d030341c085034001840b8141007482d014424100030350000211130041107001e044c100c0054100b42d4021002e00741c1c3c542c0782000c2059a6003500071201401407a014951149418580035010348841d40300005031120390030001c01c442c100f805048981c00408048186251141e4a8000e03a41d44a0346044c3c0d000318010b0b8022000c0b8209009102d44007410408041c0c17490019112101190800801c10560170741040040c030110702280d000310159140801e404644250500e8941d0040500d940710303030640d00300880c0c00a4900903d440c2c0d5140000141d4000100c442c103100e03040d0b1603524051004001d00c9036100c00c07a41d4612584e003d194010024141146008215101c1246c1c1c45402c941d0307482c0e003140c0150 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 503000197 1250 502998947 502998959
    0x31c02070213091e060b0a0303090f06020f06010e060112060b030f060f0d02040c020a0501090c051008010803030a1e140103051e0a02060315060f07051b100315090e010501 75
    0x22200700b403454001c00c00c100e03600d001d0b81c2d1100340d01520a441c030303111010880c0881c1072040560004029601c01852007801944d00c2c90b014203201c0b01407040e90180014090001511800411804200500e0030050718241e0b081440e01882c504000d0030460401c11409480c202d000b00341d105040c0501f40c01c0c240c0030784901d03260018048610f0000d0482c0c0c06489518842c00070303922402101a80c4990481b400b1070000c0040400700c0c42c010301c0007800750566003032058640074011551609029100191002599091300c4c29041d264130400388280c58071903104100080c90340080b070380050245180f60921540e10105c0070b03116015145000f6001d101da04803140100200041003003190700d00008100c140707100107041c407005a201c446142c0064000c1100000141c800d013007042c1450740002c401000b450729000c100c0700e807109a0308030707007030889140c0b103a00012000745591494030021504000c10a003d030f000c441034210050000c104051042121060010550050f90300039801014508000000e156251203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 503001447 1250 503000197 503000209
    0x121005010603060503031e0c07031a090d09031104021207050a0207061b06050604140702030a1101060b0901030c11100213051915050f030f0609090c031e031c020702 72
    0xa4006414103182043c2081591000f02c01d0314030300b2842d413210a002d4600c41c50310711a14801c10003c900079001e00d40000c020000500b0420180850300c0d02d00110a03600c1800c9656103a20080207200840c206840030000103aa0b0400d81c0100d1002420141c00c1a0030301f00c0c3c6890b42d00c0d00351920f80c0800c7d404141034255546c108032000041905182980c440d02c00d94900d202850081c2c00050403550310f031400580c079511a0341100211083c16060000f03140381154000352a5007040350043c0c0003030409041c004a10005000c1c030750644031204001450b180d07401c4015001007100c0c242c2001400400e446070342034108123114086442409960140e616400e8002c50240c0b20481e41041d80700b1030240001c4050940061140c20039524030182071500182144000d4903107008940051a4102001040160740c20290140d030703000d51001d8403014200c0d01c0d6030080a854481c0540e0f4150150b203c2c0117040c580364140c4180d092101c0c201026245051910b806200d00e41c441c1d0000c0800094002440a08500b44a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 503002697 1250 503001447 503001449
    0x20d06091a010608070c0804140109180212010807051302180a0303120f110426030d0204050414040b0c090f15070308010b0307021207030306120c0602010c05071e030e12100501 77
    0x107140042c1b81072055900c000c1ca50007a03008d48060951240043c00d5564044c1c007404000c1c101d05a90418030b004151103c038007035400300700596aa004140000900d80748005808015610001c02c220740c072000107000e000082d004403041c141101d10b801c0300c44005856100d0a0409580030365142240301d848101c01c0c4050b642c2150402040f9454840c1c4c00700003003042c0050301c00f03480c00103449840f080c0540c442041d08180c4640a405513000c0021941c402003002d6000f0f004841041d10188444200c10031070114051045070050715020700100050354070000f900003080060402005864001000004a2091480b04c42c102100c0580001c02400380b507001280c0031300400b2500d904600d980b51414009483e410008450800740f440030070b40c181094020f030009009050000084a84050303542012140c18140748a12009546001800c0b10128452003c66401981000c3d490600700f100c3c5188484a9082d1607013a0204000d0404c552003a56986030b2982c202c03003002c0014100c1c095195040d20843d0301c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 503003947 1250 503002697 503002711
    0x1903200a021002150103260a0e1008061003050612100e011503240f18030e0603060a03020d050f0d0807030b030303010627180207050615060403020d06091a010608 71
    0x2105115510f84c0e00c4010381075a90081c801d103d1401030301c1d102c1c000105080142d502074003006c2403201c1c015520440d241c5002d003084915a4801c41842c000b0f440107042500e555800650680c1091201c6001e90006500144064a10141c010742c02004078205a21180d805103115290314100c4054a005d000b00008141d0f403c0d201c1c1400e9207540e0382c1100f003079008500b203150420307d9424403c112800f64010600c869000e1401d100380055941c410007508299441140440d00a01481d003a600300f4005036440340d2005231403406c600f403c540800c1640c4440c04400c803214401c0000c0c8948401062103240144411703034490034698140500d0140544864540c0240640d009100422885501a04503450b40d20182c1c6504150720041211000380c602903081660224810038151b090002c4e243d0061071801e016005030f443c1600e4042d002c407408542c1c003005692184040c017041c00903103442000c2c0340c0c0c4144a2080013a50101e26550b56214040807124080c940c8039007001004001d401044031580080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 503005197 1250 503003947 503003953
    0x140406050301050114010c08070605040803071101050123150f070b0c070f030309140f16060305010810150e0a020706060b09031e07081606020106050307081903200a021002 75
    0x8100000c4444039084482e1740343c10003845600300418003e8107000ca61003181c0100c0d040c0002d190506010705181e009441400000741c00350700503412504180308083c142d4000b401400c1144006101d030225841c12005101d41c0401c03070b95645041e540c44030000342144070390300200a03110714843c1440351949034001c20048549000b0482c4c2c0c0d0014010303400d03d00c03140703a02d400d00041300305403410050b680220a80807110544180d00356201c00c140300040c00d092604135070700c14244c0e050321070b030701103043d40c200f840780c00000d6000b84602d40c04032215130482c90365010344641900902c0e56a050028500c01c081e0b486030403180e40001c1410911805004450140c40100246450076250001280d51030f000788994800c012a6180f14105c20038040c007010008040e90412140400400208501c290841e8031402016601e4403400143ca81804508001150b04003400303000000b030060607c00c08010480c40c214100a09280b6010021a1103400d242442e00c40000800c0c07901c0c2d07140705101d0550031001c11001554 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 503006447 1250 503005197 503005199
    0x507020f0610051e132406050304081b03040b0405011b0b16020f030c0c040c2102030a020f0409050f0709080c01110f1e0d140421020306011404060503010501 69
    0x490700a81c00c0480e04103481311031a00d048154200c1402850240b220761140c007a1354600c2417040182c02c51580712240703c2488560080480b140c0398594164854140454070510008002c9031f041c80c040e00c00507491030b1154100c584000c50325400d5a001707806c008211800800d0900c40d550b07010050b5075244907c10590b000c804240d071150320780280014051b8404401005030003420900c00e0041541e40a5000100c039115201c08401544991f19001c90341d01071460b04111a614900c40c0e1020104100000e141d14a1303c01c8802c04400a540010000c510041c0c0070000c021214400000400c001d100d0a800000d2a007002d0701c0300030317440c02c010f05003508008018138103111a0f0300104a190000c1001d00f0045803010440503694180009000c144489000d4000b024020080c84840080c0c688095816204c609c200300340155080380c1280c01a0850210601c018001c00520a5100b003400e070b2140c042d08002511940000c0c44c1c1780098010400340c90324116031082500b41405404050001100240425 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 503007697 1250 503006447 503006461
    0xe0703170403170d0e0c13021b0714030c0414071b1209080c0d081c0f02030a0506010215130209091f0209030115050916050c011b0f0507030c020f220507020f06 70
    0x1c0300b0b80202009180340e0009d50f102000310f500e6880c03400f144500095488165840300f04010302c0b40d00801082c0240140740000c8114503051052800380040c2444228513030f03c0303031b0300304548801c4018100c021042c000c01261021a080d0030401c0e040101950f1251940b17420720b00342e2400c0010040c0705038082c602c0c050740c020001d40c07200d05640056403110b4100404107911003981d0050715814050ba905188000180007150400d500010303c511020703021582031035144c9000003861681201c10214900401001d280149844a5402d421900d00c0e022500d402212505081c04480c030076040010311035000444d01070350305007805106007079202e180c00c10101c5458134000c191140002012004138039502c40705803a00a0040e03043e1190388020070020403103414000c01050b0304008800920300850044907400c1c0706240f00d6021183e240d0f034580c1d24150204140d13401c1c841d202c14545050b82d80320b0850420180203028809580103140910031012132207040c10200a030800d640703054040c1d0140c03c034034200180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 503008947 1250 503007697 503007709
    0x50a0503030903211506031905040c172814011a01091202061903020f04030f0314030402130b030111130e070c031b02010e060c03070b0a0e0703170403170d0e0c 70
    0x1611740140d5086a80e80d5400b030350749041201c200c58039074407685860244001d00050b410f080007690791403400b840d107151300300f100550b40d4101550503320020300315416140c04010007545034103040c031030307820003540301c07500f02d5214291104034030b1403040c042e15110010301660f44088100002c2101041d084080c010780e801050451007003c141c00c0d0b548202c3d400e8180c450b8440c1c0e04842c140361441c07850300d464940340e04d40305a804c083d081e400d0740000e03481c1212aa6614440040364051503004120b05404900d0b000414060402d60701c1e0640d25550711410b003000c03107000313100030580d2455240070107c2580c10001003800f4101c0282c4400200300300c216200700082e8000c0ea0014481001c04001c2d24440c1d09480129031101030003000e250040700105a9000f07405000028001c0e851003000543c9059417000785041c212001d030040d071403030340d8040d040800c042901100010606400c500300c503480e03c2e8807901e5644129000d03a244002c050000984072244a0f458800c44802c002c1c1c5c50f01414141d5030030000100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 503010197 1250 503008947 503008981
    0x60a050c0a270303050301140f2d090c040e01090b012304032012011407180504020304050a120507051e0f010f0209040c0c0c12050a050303090321 64
    0x424048112050920503400c03030844084248071412010b2000c1c1c5a1034000d04d00d40080c480d801c211b052041001410b031500c00c040f500400b10141c012546071040201d0b140100454500910124038038191184080c1c561664051240951200a0355914940401d8000b001d105a200800c2289071a00007155a070748184040d607000c4201044a98002048414800c14807175036000030001000102101d00304034103801703ca440b00c2401c4400c1024511100e440500762242417040d0603180071160002650140151711895102094040c50b1120f41d480d200420304a905c25241503401d0750003000102e080281c0b0300c0d06103070148814036149003005441d075107159079001d25001580c8105501c030103000e4400307010070030009400e024000034011500780b42d041c0802540520105c500948c2400808041c0d11b000354025504030381d00c8964540e03414505041c2050181c404a02220f06001d10300071000070500400107035000e024480b0245640e5600307103406070920303e00944070480b0b02410904024241c03c50321407641e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 503011447 1250 503010197 503010217
    0x209131b17060603220c090506031501090e070807080109171204060203041a130302100606090b03041406010605030f13150504032f12030f040f0503040f090e060a050c 73
    0x141c2c4903210707151780c441c0d100c07104500b491540b6910110700307007804240a48201111121002080280c031080305054444200300142241c442c0000010800c91105a101c00740310320025080da00c40a450703040880c201300095000140d16074480072034006100c0f2516000c0c0d4403000c1403040d6440d182c2c9940100030706050092019080075800310010f0103200c0c0c40c4030104881103400c00000e0311440c10500c0780c51b403c10a860160018072648205000c080305510800094031000e850b1074107007600e09020742c41d40303030300c01131045a41182d201248003810038100f1007507000e0f0505495958685c90041c0e0604101c0400401d040c101d81440c8140e140032801501ca0108462420003003c50243d4a07401c00307403070140d10307001300350410b17034014544480381c200b903d440116848001080c0c800101c2d003201c582ca62400292800ba101c4480100800c0000e20f525032a04006449401034905265803121088050f089950006010303a49803203452131943c00a00c501c99014030794403001c0044c3d0400b0201e41500740030f0100c0c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 503012697 1250 503011447 503011459
    0x2121f060c051002040e10090b0a1a12040b090d021203070309111e0102011514010809210316090b09010c1104051e10080c01120209131b1706 62
    0x251060000603c0f4802c00400c0d5404150b684551b69040401920300c100c03080300044030750820118203040c480c021040c1c0342a00030b00c1d4055540c20702540f401882e01c3ca184544540d0010045101401c4030540a68800c0f8000d83c26420103203428070015091041d0724080c40115001131501100c0b403250300c0141d90700401b151600081030b0543e407811180703540c40c2000650780160740010100e4141803602103484141000c3e40280007400350071108445600c00e5028102d148980c010b001ca00c0d47d445010941d500100260441310910b081c0d00c0c1c1072000525007403140040c1c01d000000c2184a03144601011855606c1e442c0683d012407030b0004600f901d0080c1c44405040101d040649030620030134541054040000500401240c140309503000d05280100c02c018000c00880d4001a15081d07c1c6c0145408558040001e0880c0c541c040e0300440b1981e00015101122642c00d0110b6041612414035580340046072000c0001c0740000c0285024080000803103131001c004118005034038496182c4c03442900702500b50f6403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 503013947 1250 503012697 503012717
    0xf150105040311040f0e030a090e09120306180907050114030403080a020306130e0a0311030403030203030105090604020d0c0804031806120b0102010b06220e07020a0209040c05060d02121f06 83
    0x24010786511721081010b01e041c10560350b002d01c0c0102c01015024a25259a00c50b25614658005e1040e011a1075440340e41106000d80b0340900c4078001543d1062004010425021040343c42e510000310554203a04550300000c414000ca513004100680009402e070340c624250300d400da5009180c02c100130014100c50707401101160740d503101c084600c07800c4403900d841405a40605000c641c0d480022510960000d000ca0601410104010080b03400340d98065002c0c0d4656800c0a0500504503400351038160020713400c0003440e000140c0c80c40b51800303412023a603400801c0d05003800c2c01403040e04046403040d650a1480b0301000a01d811091050003d0080b0001040e40314074080141d004251030418181c00c60000110f40d9170b40312070004030490301c02d2100250101641c59078400c0300c001600b2a040c03000360b0b100000d04405071030f00c8881725031b10500c1420218240c5454501084580d004012000b203c1900490b027024420150018542d01601208038076003a9441100f058039062054800c0b0802c0c0900d00d28 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 503015197 1250 503013947 503013949
    0xf030a0e10020c010b03070605090d111815100305010807182c0f010b090f04020d081909080a0f03081009020403030c0605060108010614090d0506040b0f150105040311 73
    0x1c4280840c0c681e410003103403904003050746603003c0c00700304003140c1c802c0c05050390200da818010780540341d5041002e0709048580d11550b564180c2100101640d99100349418245c018601001240314403070aa8001e00587d40074000082c000041003001c0500181030500300140284117000030000304880c00c2e0840091452a12100311006050410312103080c4100030301440394841d10004403450400f480300468454002c0703401d85500f25480c0c0402c1d25444a034540201d50344104455086410900090446000220316591001c00c0da2000e401ca1f200190340b200f6000d012034018030840002c1c0a0803001d421005013665462800340310300c0c8001424480000007240d4080e000c0c21103030014022180341103541c0d0b601c07070a01401c0d16580a004840e0342d400c0000041075075205594442c100d0314a40c0300c0803040781c4000842d0b4915004462905d4001100030344c0f07a40811b404000c0c03940101e0003404800010306008000d402802d200a14a55038044c0c01c0894910b00c0c0d0b4401c0031a011684c118941c101c40103a260 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 503016447 1250 503015197 503015203
    0x4020703140c061602120307110c10210506060304020613030f03020a121107061b020405040807020406050d21090506030a06090f0e0304050d030905090a050108120f030a0e 75
    0x8003012040c01140c99082e800c03000501a000c2d000b5000b080b550411440d00c02c90355038440710018480b402e01440421101070048a0920700c0c8800d074010782d200b01041c000445e136981500800f00d0006502121004c030b11122080c5640c0c001070b00b522003440700d89401c0d00411401d11024000900075000042c18481003d16804640040c6601c090540042d8001e41802551810800410f0711000c009101c40d0322414040c0f01c00121944410001d000c185150401c04e031181ca1a600b46641c24840490480006035140d11419205500c0382c003078291a22024014841283d030030b608a240102d03000381e820008900b21040d200c02690304066142e1001d04c0b002000c66004a06521494008a022040c1b045983c8203030002130540d510928104241c4c000354428405031383c0800c2290666410800c014007860411003201d00304039020381413110343d550350f400101d10a1017040f80c003480001d64440040c00b0360f030018042c9034000504030030080e0803c00ea05000d40ca043c80050701001c0c6441e90340c4141d0118043c18 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 503017697 1250 503016447 503016467
    0xf0c1701030215120106030609050a0504031d0316260f120708130603020a08060109060c06150e1e0115090b0c0709111b06010b0a110a120c20090604020703 68
    0x134400d04040c2c0d40e5900c0050701400c11806228407681c18400021f42440c40c40c854103100c0c3d6096500c441641d00900042e0000807071482189800d802100080da5041d0390060160340240340440741481850401c8602c80b250340c0c049079522205410a01e2925250500010341a03c241e200c0c5100e15644c10039854017203980c0c0308841c40800c8114a030400040d440b80c041e4003a1041881d287c82e00003560340c52100440d6009154003601c4041200e00702d0040c041b554542c0400310782149092141d039899143d070750142070000102e605942c4108083d180340381c4c42d0b01220500e8010000b40e6491f00c040c1d454840042c1041880c1c0c02224910400400e0b650003500e01045503c00500c11020200555690b241c04602207a000e4030700361100d02c05403101d152760000c0001d800d40c1241e00f410030450900c444000122004410080ca00860344140842d0101140450b410441007800c25210102851000d02d404844460506013400c1070b40744294010211b9200c01c0c41c3d00364403100031103005913211401d02c1d0941d080161 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 503018947 1250 503017697 503017717
    0x60609150c210e090105060d09031b0c03021e0a140613090e01060b0903120a02330105030f1203060117040609061d030403030e010e03010903030f0c1701030215 70
    0x581e540c00c440c41ca050440b80804030020b41d10120490754000501140344420322a154100008100c1038070710414a50042080c28460301d01070700740904441603504030340d450ba942078801d00c200d40010011450041920343d20862201101c03031201146034002501042507103d0084428503c100c211042e40e140c0c0b003105c0d01c1c00008580f007104641c8071800400204442c0c014a1195841c2c50300100d0007044001c06e550361050024001c00d8108459039010406400000c2c5140c19031103003442c440c294207200751044400c3c81441d03e84414000409551103010f0308103a0015000350003481c0700c40f032200300c003040d0055000d140420459030798030344200480760f03603110b5545c0103078a038003800c14442081020742180711214044d19050102c0310305150f510030500043c51102d00300798010441000001d00556112188070414101303003481d504101c000c00e0035585800011030000ba90740b4030000c0d00710304910521604031480c0c508400c580c000f00d03401280419060101034422200d4041070b01061a85404a17240203103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 503020197 1250 503018947 503018963
    0x7020a11010e0105070602270111060c090303090a0314060106030e0613050c1c061103070c1704050402070f03020d0e0321040305010908120c0711061e031513060609150c 74
    0x1c207070b8123030b284a5a2884403882c02d883d1004685100d6108207040f0b01241c01550103400d40707440c0d44100442a9100741942509400144030300b01c0d903651080d002c40d008600680d024030340c09003041f0a0904020050f044201858034200000009040001d02c0381d502030345a104a8803240c00c281009403400401c0e4491690000d000100708084004440800103d28410b0506109d000401040c1000e1070004550074000101301d0350f510000b0411081000124030b202070007031441c00782c4640108059070701c450b4080d200c040500c00740d1010194104007000f640405482d0161403d008180000c1c0c98013186010040c641d142d2540f40c4104207100c41c2101c00540d4804000c000b005543c0c50909001c1d04442c40c440b40c500c0f251000241c00e8a80c0e442100d0089030703c0b086c0780002d00656020000707942c1141c1d94448112590091652201081c1001540210707407a03008150122810402c000f2a0b500d2014008151420000100303c0d682d0003422100c244c4400b6030201080181d81c00b402c540ca03003540c0601400400b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503021447 1250 503020197 503020207
    0xc0507030c020f1e030111040e130602070f080927150411070f0b0907060507030813170405041d030a081b040b12010602011506080c13080303090607020a11010e0105070602 75
    0x4000111511001c4e054000b8450040c450b00031400f24045d40c8110004c0218181c0001c0101ca02410380c1c842c80c0d4414179005080c241c0548604004100b00c2c2070845803079100082c540140c0ca07181146a040d203200c1d602d400b03a091741d2103a05010910f0050100f001c0d0519107011207070390781d50315000380c0310ba00200101a61140403a040035501059000801e8505100321030100e00d4180300400c07804141e4425460301403920481d42d80880305040001d100e843c604161151900002d0059082034000d84c1c1102d90722500e0703608060812017107030300c0400c82540c24800a00240300b00b400c04000e542072803a0034203088400795601d8030406415454a0703058400510001408102c4c803010101810240350141c01e804510fa0301c801d4180d080f0381c03503807010000c0301000c0d04041240034800d80da055400b60080c3c03c20707070411044801c035108031052030708101c0f42500048104461100208081580a0841c4c4002c0041d8403440c0c49200303442c0e1800344154104074412200c1d850f02d0340201300b1a4003036540310710700b103540d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 503022697 1250 503021447 503021479
    0x70f210308271b090f010302191502010e060a020406080103020d170d0218090f04060e0c030d170a05010b030103060b06120703050402010905031f0f1b0801030c090c0507030c020f 78
    0xe120f01c1d8403c860b503410101c1c1c0c2c01c002c0c0c02d0071100a88501c200f01100c4d080c503420351b001c0040c501c43c8241f480d201179581d810045020782c1c41d85480c5c100d9049603000404e034150280103003810410000d1241b41710503c1800100480c41d40641c41c2411a0f405541c5e09880e0411400e02c018009032038082e04400b0500062900d07550750b8281c0c01402001d8103150b40b0f50780c004c000b1081000320407058610b10701c0341035400040790111b1620b0f0b000c0bc542503c07100483e03000e0440032012a042428180c22240456110b10740030040510002002d54480880d0100304019030401100f004180818003000c2d084c243d5400301011315860f100c00b02c5e401c2c0c180c18003141b03040d85000391000303010f04001c44003280002c5000d240000d45050005c1c3d005210703001c6100c20b10060b8075200c000300040035032442d4440030740d443e00e03140f0188404441d0280303005803160b075642e8029815410120040e14455200c2080c080c070740501044000e83c041c0a4803001c0303501d460700030300700e111a00004e203040c807580c10f401c2d41c0291220005824 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 503023947 1250 503022697 503022703
    0xf060308071a0f0403350702030c010f15171002041403100b011b030215042d030c11040f0f050703140105030d0f140a02070f21030827 59
    0xc048081152690541c2e2240d040122040c81550002c012070300c000e090855503a1200c01c0c3c2c4a12840360244183e00301ba070030409a02c60341c000d03190a0b001d07802c00074120303542d10000c2c003c00340503404001060104844a0041a507080c00900c629624100d11a005d0344000d0340910401380b85800c0c0342420b64031380d40c0301c062840754503680c0003920780309103e1002800d802031400d000e014102c0005856061404552032009000300d21041c00c11001c42c000d0640007801c1103000d050090050b802038181c01a9001e40403501800d0a540541000007840007844007400030350f00c00c00c071140440d404440c0407815940e01c400b1601030488152a000300c1c904206040950000c154022445029140d8041c000c5115811350050780782c800380650740e01034000c0d10004010707078098410b205806c043d500d8078418414068101c40100d8114000704401600110000c020320607140c20800b029200d4000c5041c19150241c1d86c1541c110240c4c0c800809010007480003034418004500025103c0d40f03500749002c0040130441c20251 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 503025197 1250 503023947 503023973
    0x1303110f010206040221100e01050103030e0105041a0f0f0c010f0f060f050906031207050105010303080615091509030a060501170303011206020c010f11030f15060702040f06030807 79
    0x100a0103400108440d0307600c0050000e0240e0b401512103000030003901c1041c020480074040c5503400b0302c00c03603090380c000c1000d6110740d01850300c5540002070b10754194500285181c1c2103400c090704002040c8001c1c40084847c008030b80c8061400ca2519076200ba100380104014000c205075186185030209072482d00c04010f40120903c2e42c0d4208040140f0980c65a00c7c100300e40550043c2c00300441088824415400c0500c00703150000d80c010101c070410501d800e0b103c29a54814101128165141c80040003050740000e001c542210046030302500c10355010b091444c060240750300f03452107031413240c48c0b00c0300d210300d0481103039045d1002070151303888121641081c1010309020f03c65001c10288402d5070246c551008010f0302d0680e480081640f0f40e41c40326460b218043d400c510913600c030656030346e44072441c500414420005c04007c0e860161307442c0d141c404d1040380b51040c002c01810f4001c8040001e03980340e030341c1d07801250051035040714001405804000014024003207908000c00c40300001480f4000d2250380c0e20814 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 503026447 1250 503025197 503025199
    0x612050d02060a23040c0b0316030b01080403052209050115020705040c0e0d1e0f02010206180d0507060f02040602010e0f07050a03031103070507170c01020f0c06030705130311 77
    0x1005501c6a41da16021508003c0f000b05446512407045504081c03d01e10141e00980105e010f1986d1a8071f404622540703034000c0d9204621600b0315609050700b42d402d405069480107003400c000034607160a8902a20510680c403803070440d0420b0325501c2e0f40046a52004802601c01c0000c20005581c484032a00144503500401c480507102d45000095186003600804502e1003459580c0843e444804e000d00010441c80001203a002520b0882520048032360403660001901070700c2106046032480c000641460000790910342a12110080d10311088000212010301321890316245e41d8135416814600b008050004544550310300000c0e0005005605402001480103100140e401c050713032070480700781d50b071110b07120703040e000550301c10100302090240315610141d0740d1010a883c5445800d554241c00c3c0f00903508140034043c20115000d05d8802c0030400300c2d000344003e000400034500b42e43d00040d6a8850005098810040000040c9110b4450070a5600481500310100000703070700e0346086141184043d1241d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 503027697 1250 503026447 503026453
    0x6070609080c0f0a051e0f030a030c1b050c0f011206120b060108150609040b040203070f120e03070b040201020c120a120f320403031e020303060918010612050d02 71
    0x280300c203c140400c20400b40d41d4084003e01d242509060fa5040b0902c0b04200490940aa01348805e10b00c0d0091004005100c8260f90008440d552850050300a5400d07210007181d03030351651580d100081d4001498040c43c00d0441d5583e40316940e42e40100c070b55007803411f240140350742800c0002861140c25000600c0751482030f20000a59075a00c00111041e450465181c440c060080c614000e079401c007840140407071403001c0d101041c0040f0a0b008101030707030300c103480007000990909005445281d0200c0c0070460121217035070a201300018850a41da47e030140880280580105a003c1021a0b00810038661400b80c00b074502c54040315580102506c43c1c041c00d00c103992a0200215644a1620a000c01751407171030b80b41c40320030500300a034588105481014014240141e2a40744c00c41030240d0131005440254440e0b60f4080c040211074248005040641d00c44000303540c030900c2403101a1b03984031881903101003030b1034150b58085020a84035002d498950f12924544183c4414001070180c040f8000d8000a502d80813 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 503028947 1250 503027697 503027713
    0x501050906070810030609020f09160e0f03070311130c0815010206103503130b1801140d020406080a0b0108041110050405120109030f09061b0206070609080c 69
    0x2040d5800b00045944c4c40541c000d110003800000e000e0ba0101c0111030000e03002c5680340c01b8001c0030801c1410203540803810400702144410300c0300d41c4078460004985081c0c0b1214441d20021011a83d200e410340002400701c20441c1018459031145210b8110002010200380f0a0b2304038a18041c0078020241e440c101c000c5000300c0c5001d0903500010f207141c014072040c0701c0d075040b56280041000000e200c0380d05032400c0017042110342c0c40b00c011807104030a180080320003841c0d0703452003c0601075510034a0b921181e40c000003800900800700900303107444203000d420701f000000d003415000c401c8810b01c58040b01d80d0640b40301080206ea590740c4030036520310540201d40108032607142d1400644400204403401004a03100500241b45420802ca41498010301410810300702500c80c0f00107100141c4000c01076005031354428090041c10f80c40b118141210740c45081c035500c21414014010009659544d55000c04540b4041403400c649072042120b40464011204104421151902c298180d2003805044030900c10250 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 503030197 1250 503028947 503028961
    0x30105031b0303040905090f06070e030c0901150302220909020a050f0d060b0f03012f0c030313020a0519050a09110306040507030603050f030d1406131a0a030501050906 74
    0x7034503030300d0aa40240214202880d1010170000f400005213101c1a070b0044403240140120100300c0346004403240d8807003003410607401d0306140c5030003d1090300600c02c00840004004900303c10450100004041c070300981e4901001d040145100c440301ca40c141003040084000440204a500c0000500d200700c40000c1c485aa60b0100640707038186001d41a8001042e07543e903c0041c04551002145160150001032440f0350b1000181c00c603000241e108400f0984401e010050030031340010410300140c0f0b03603c064207140390190f001e6a24000207099007080c801200140e000e44d600c00d10203500404000300080303141a440107125074081d640d40b186601a60034400007160004840c001d100744508403c155509580e174402c2040040d203000f408800615030388400c040b0114138140550395100071150000d5035a0034012150b2402c0b0b4400d540b0800b003425580341030182c0e030343e98190000481c040704140803404c982d01c803890304007aa0303044501683c80f11240c00c0010404c20190070031841046400d003920f8140d9a809 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 503031447 1250 503030197 503030233
    0x9060a0e10090b01090510031e09150e2407020a080a020f0c010201050615160803041a010608010b0706020a02010f051501020f0604030e120a02040c05180d0312020915040b03010503 79
    0x100400354464218480b94182030320942c02a0149542c24110042700d03500d03181c16400712060900180c6201d81480d4803001e00318018041c00042c040c1400c000c0c8400d6100383c4030180c4145805400421103c400c4021520b041e1003004400e40b06508488881c1d500d8000b010040e41e90310302000b1544050250351444020b940c011b00c170300b92250700064a008030000c071041100c10541d200c124201e000c0352003420030102042d4600003a502c924400d910b030716110ba0a04041c2e00501405a001d001040006001400080c00400548002a82c04800036843c0c94a2141c20380c0580861500703020098500b07402c1011440c4c0c00c540140740b0400a07000c2c3e802c5c014445c0401d0303455171801c450140106101000c500040d0800b04054198920b0440c180d50000701154001025540c001521300000303500800c0b42820100341003946103040740103c1d5034400503c4140d0300075010000180c041d0300c016502042c0051243c540280c59412035190503606503030b8035117414601c040c981003030088070b00070300c00c5444020400c007100b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 503032697 1250 503031447 503031449
    0x60a060906030e0109050706030b0901080c06090103320105010320090130060f05100e0103050717010b1201151715060c0708060705071109060a0e10090b0109 69
    0x40d60350341042504200c001d80c0600302811103421150b60ba1030415000c10000d010b2180030b001d0765034001c00e0b0a40428100514400e041e00031841c990040720b0744864942e40d905c22280001801c1c280440c080c003d81a8002c41050098602d07011001c1e213200101c1c94078001580795060300e600740c908010600c88568038251041c4d0205504000c4d40c0b0410400c10158080c4190f0442c00455490902c0544406500507809503a003520301c00740c5a844002c00c0c0000b002e00004e40f400ba1005989540300f1070400b1200411347c1c0ca21661041c14140c2c0d0b04040344e101d80c410b80d403442001c05c1514421065584d600101d01c031550209001d41d0f40d02e00d507440040307807050701f12440c0b40c103200140e0f0303903106410b103c400c45000c885005807012081e46282e851b0024513817511000390030403e00c10005406907601d0014a00e00f4114011301a40c2000410031401001446102d91901183c1017514021059594040410503900a540080da04c0040045c01c10940c540c20884d200f0a41d02d40003000e004c00ba8913a00103540c080c0b62 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 503033947 1250 503032697 503032709
    0x302120423121501080c04050723091005070c061b0b07021504080d05161b02030102070218041103030406050a030f0915091e020d0b09011413020108060a 67
    0x603407071220020400595001a180c900400c20030002c0261600e051800303034004041c2029006460042180440c1806843c542c0c14069078240410b00d000140148015100388480389a0001e0f4015086820782c0441076908143d40a03103242c00000c0d2055011b05660000c640480b50f00c1001c110216800340300395444035100d080d003410103160650940c1e960850783c3c3c00420035004c520941d040c105039090302c40480360045004498044d40d0304080c01d8041c09540b001064046134005048a0b540760301d90060b9002c400c82480300309885645414800a400383c820901c001e54030110b21032039120003c0402d0351290145100c3c0107040c9480d05000145503ca000751301c1040c01080c0f003800904031040c041d0f08000c2d0000300c0e60000203402c0d0740654401040d0f0b5031f2000301600c5140c1d070b44010010007100c141c414100ea90704885e06408820154001352242d01400b00061a9017000385c0416000d0009410100100d0348400c82140c4c20f01e05400c0c4034401000c40032090340002d04c440007103015800c00000003025512 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 503035197 1250 503033947 503033969
    0x40618061508070c260309010c080f0703091e110a09091728081e06030c2b080310050103021c1d070314060106140301120f0203060403030903021204 65
    0x95601e000343d515840c09001501c407010018540407240d001c5d41c1c0901031044802c0455512424000011421603440110f120207000c003103c00c1c8064041c1030103a1513800740c00307443c000c03403072210070301e0f0501c0400e4026070850560019a1011000c2040c5180d035122007110982e030306201240d44400748001c0d04c642c40000f0309079140e5500d80c9110001e20000500c2411240040041040003c03081c01a1800c2d629000300000344102007030100a00b42240038143c180b100d400980705605023940001c1e10340c1032400440d44640c186070042c2240e035090300e803944280c5200701e1410001d080c490502c1c0805e43c2c8112480708041340810030203d951760191080d01c0c904080c1052243e001a44042e0500081633669000092101c03050149443c042040107040c0103103101d504000310003828049050300c4d00320103030041d40500201001c2c4003502116981034a04441a04001000702c000c9418030710381d01903100402030f4150080d007041109068040c0c0068454a02c03e0342250304251280c1d0309030740540118000d140d8844 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 503036447 1250 503035197 503035201
    0x1211030f09331602030a05010e07050102211b0609010605030d03180212030d0c030207060e0f0a03051c0c0302070b0105061905030c0d15030b09011401120f02040618061508 75
    0x19241030050000380d10380544554071007403c2c0d0002445d000700c200046a0b56034403801e46c0503080340140b00081c002d14082c002000703000300c0818420801d1001c2d1262088c40c100100e1195003040704030044601543c102800d50300241001699140070b84984d000d05030180c40b6001c2104070691007489060764040c040c070303004144a1b41e070303508000d02d07900c00b08200301051001740464020b1840c1441a03641c4020036840060352048039103441d4086d1040380e0b140c2d60b50703a002144040703010040403946003442603152505e141e8610100110700d8840300c0d200f40c10f0116034034000aa002d015010303401090342ca8040c99007952940c0ea5034007044050301c14104410303000e8560b0380700300c004580150080c54000c841490081d040844840301001102c40007101403041c05220a030400911643d007400760b4000000382e00901c400032008100b40b072504010312404404d681908408400d106042c0340b58a07800d640200207024075070342c4584902e100e4401e4000b00005620f4941c0c000388c20144680c0c0050320300d01a0320b50301816 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 503037697 1250 503036447 503036539
    0x108010b09011101050109090b0a06050f131401030b011e08030417071d04020a06020604080910020307020d0b2e0504090804080610031203090b01031211030f09 70
    0x181c100c0005a410b011030701d24a450840401e00807180a40540c0c0000503080441e81004c078480131014044c0c4503068a0310000b07120380d03200c108807480071080a840c0685050490a10840101100c910b60380b80400c03040004010003040c030414074100e0311204040701c1031a210809181904411744160304041d80f0401c802c02403d1140d00089802803011008e075400c0b030340d64050416854442d60348560f01c0b078006404010840c0f0f403155a1030081c1405100500141c600765a800d0410700c91f20421601c511a16518011401c0c8200101c5450f541e02a00424454407240b401000580702502c080c41c569000700740e2090480129081c2d82c98180d89034401c04c21070f9280c5001d000c000c2c2007014041d101c4440421002c82c0c521400c102c02c070300542c000320305c031f002103495070a250321f01c801003100f1318040505083d5003501050070b000701c0c0e44c113481c1c0000703090000d8101c5600c2980e1b22034030448040403e002c081001e9110440c40009455104000d40b02e84000c8168071604003001910405c10101100c0007407034010351 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 503038947 1250 503037697 503037719
    0xc0201030507200703120c0305090d020a090e07091d030d0f060506040f05010e0d050a3305040506070305090706080402010203090d050303101401051b01060e01060206160806010801 79
    0x401040d0410000d001c00010080d00c0350385840c0c03c9260b42e079101c400300b00b00704051a0400c0c4980c1c5441e00e40b4100606465500400754403841203110302c550b80849184080d075840d100008010000f4840030499491001c44243d19501188101401d50349490603401e620b11800d0010b1582e030f04a1009149442c60310038100c0002d249146d1409003880ea1041c000c612034840500600141c151440070607071207031414000400704440074441601581500c18108005000002e8801010364405171811080406082c002003580c036410700c4036040924a401040905100e9100c03500450041c01030301d60310303501d002007a03098a0050f034205865a00a01042040c207114070981500503105205507031900e50b030400060400303074043c2c078240c405e5000002400100c03450200e241c001040c074041d03503d425100100003e030aa00412039840d681c1040d25a02086901003940071038041c029041c03a1040c0355031201c10095841c00126040040f000b41d03101264070481c01030300305510504050b50f4240c0541c2c01d00d90381d520 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 503040197 1250 503038947 503038951
    0xc0f0f0a1d030123040609120507050f0109080901030f1e140124111f0e01180302031e040b03012606060d021011151b0301031509170403060515040c0c02010305 70
    0x1424540e5154540300089015050048c550f0742d603519107441c1c405500f00541010740d14140440243c0c503100541000074403c0702a01c0021100342000166240713000006405410029a41102e00e00504031340200b0109550014000c20713a0b074004003840d40c4e240c26040c141240101501e100900301c410084883d90f10418940c10001ca0260076640c18000c0c08000072040c950f103178a040c0c0c4060711002c200e00003501c24480c0500c51241c410705043c80030819200603480c3d210301c1e041d80e0080c400c00e000465101c80c441d4111002070901c3e0400c5652580c2d0b0b4102003003900078840320f20b18100c1051100d03040c05200002c400e4001c5c1401000310211400950800002a190161000601840316900098840c00b0311280c9007140c0007a81074030551814004844581c0d1000b50b40b0071a00c8014801400070510340403030060545500080001c03041218100302440c1c20f01c0c6000160440c00010300402002402d82201d03024240e02c5070300c0c0050a11300400c00c81a0749041e0f0340000007500807002c000140d0700c2500016 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 503041447 1250 503040197 503040203
    0x1090b01050d050c09010305090a230a0c031202010b060f0301050609130e07050307080706090e0a060b04181a010c030e040b0a0305030306100e06030c0f0f0a1d03012304 74
    0x103180407040014001a6001252000e81e090130210320107280e07503018000e05500020324800b42c031903001543e640c0c0c008001d04183d0f4005200c625840c07042c806d01c0c208001d004960700f020a00c403c0654a20703001100400700b014100040d42410120075042c20588261004160150199030039a8248402d010840c2c105444490f0b11103d01907062400c03001078441c8000060b28400039208442c1008103040c40c000959110401030b90000804101d00e9501040003c20703078291203040e0715151a8034481d800074084a40000011003c00100000c0261a92040d4245e4982046050008444c2031207003600c6c8400d02d41c540344c00f0994108128001134840c51580380f215100038000a42c0401080210f0038024503604100d40a81c0000140b1540b8a040d164403252490603180854086000c03001103400c1c1c2c00040c04a1452031302c00f091403030b0200185c2080d00e6001680402807030700c92141e008024160b603148025810016143c280c00005403c4c1801400520206414030342c00a4281104030348004400410070b0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 503042697 1250 503041447 503041457
    0x706020f1209070e070c1e020414090105060118090510090c09050913030c03081315240501020304170f010504050c010207060c03020c011d09191103060901090b01 71
    0x180054248000140c1468503698048000500c2c000400702e242c05015001010015004c00c20070215907400865185c4d042c0e031180050081025280e417018404032013440080d802410901d159011741780d0740c5115807240340780780000e00c5543c40d100015140d0301180031094201219611061094580ca600655001841c6038082d84120307544401000480d100100c3c400300107070511000700300503c3c000b07012070380100804100c0c00825206603009010035244120082c2407040c40310002e031042d511440d845e0300091300080e550364803500b5040074800030041c6260314195a030884600056100c0d806084a0680e00180c0085190904007811040210129454141d05128603512814002030070702680c0d019a100300c0c010040e034840d9400180c02c01120350801002c03c02014000c20100358001020260301c4020b007403400900c240c1d520f07401e148038040b44007240c12100404c1440314030145199158590b201a2004004100442c00101c2d01c80c4001d980b410340c2301c00011700501240d4040c2d440b00113110014141 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 503043947 1250 503042697 503042707
    0x60903120f0115270b0307090b030f010e0903071407151d1201020708180117090a06090303022206020f121b03040e011202030706031107060b1203121f080a08070602 72
    0x130741d011890107600203140c6000d012090060b19a0080c80c0c2c1c502425071941e10908520704a00c030074103c800140f0440601c11701c0c0c1408038005102c10b004940c20260045100c42030500841c06869444c8000e124250b050900e015044c90400c5c414190208490300f40719540c038445100380d08000c0c2c002c403480d446843d42d5508000050000352007400400210a03000d01c0f02c0d01c821400e00016240700c40508050140261981c00c20450040c08100115211f1307000e50002054106410100d00a00071000b1708420807500031050480c03030359440072100c22280d05908a03144052103140598a69a101e03600320f000140901004442a24420220a160100c0301c1201e092a5413400e145081c041c00b0383c031030030b071511201401000b5400e090019001401c2c00e41828080c606840300c074295248209100506a503680d45031400050356117504886400341c0c0c00b42101d450700341000751549946420348100300c881c10703031198404110803125113800494a140c2c1c0038014102d4580c4071217107650300ca070070100d9003143c2c2005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 503045197 1250 503043947 503044007
    0x402060c0f01050a0501050d08030c2505060f070e010c02330705070806040c05040b150408010b04061202150a14040b0403020108090601051e03070305060903120f0115 73
    0x200c07454805107141d00100b03203030600348405400c40b0300c10f811260048004005d00c00c0426115070841e074100c1d240c0d604444c0c0c2c031040d40e920100025400188421040c561142810900c0381c00a23502c1d0060304174a90302000741c1c80d07050060302c11448080310782d07010410030b8186101510b00810365075091603801010101e0189003a800e491086030b42c864010341080e0104a041c1801001c015080c080e1403070303000501407810640c4420352080715902ca507a101d69180e10100100740c6504078500c90300d1540002458503140ca03108107a02800c4035400c864091450300c070f0000341c40300c01c62aa01003541e030040d200382c0d40c04c0000403080b00c86601c415070840c24089038404002501c0d20641c000c02c010030308200d9098032181140300040511070042d000c03d0302c0c0c1d0321280044c8640c0c0c0d02d88038a900c0c41002c42030380c1284a50440c01003414454180c0c0003070480d005890070130041c0f0b900480102540700c414651400c8540d84c501e1010744a20302030189142070301001c1580d034a418010380c80e01c510a410560441a0008501 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 503046447 1250 503045197 503045203
    0x10b03030a020d0912170c03070c0905072d030509190302030405011202030f06060a0e04090804090b090c0909040204060e0702150703110d051f080f0c0111030a080402060c 75
    0x2555a00503030021288240303990744955884017030700085481030200e0342941c868280e004c005c0070b10010380443c00100520159810400c0f188425884100081a03c0d9a820001c0c0182421242c401c04100c070b034618035560380404400030301601d004510184200782e80240031401030100408540051280e00e00c1422501c480903128044907110780d000355601c5003040001092030030082901d6206900610900400c000030510055014030195445615108072400880708030b0b00303813250160070030316204002090081c1e81c070041003035584111051113480084000d000b64000c04851074042c1280034090b1891030700c0c003003c2c83e9400c80d0000708003007031294a41c0d180c406444825101c3d1005070303109426000f5125118100c05500c5115810100704c2e15414800808042c07150101c0c92640641d5100025810203540c40440c0090300d0b8440c0d03030403039291070301c514581c0c03402c10008600c074921403020b8880503584114104220408800301550400300f030752801759a01c54001c2c004a80c0a001844080c4038050300f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 503047697 1250 503046447 503046457
    0x612190f0b0408030109180201021b01051c09110609010c0b0406060e0a0c02060108161205030d020f0d0614060f1303050f07030b18030a0f18121b030c051002010b0303 73
    0x240c900383d5035039403400f1750309801c41d04080221802c01c24056407000140c0c0c0c0100301c41c4054402c01c0c0355804d40c40030000048425204500603258020001d041c484649020303540078a294603c100030007410260300b50104136081c06189c03020381c001307040300c076282000a02555100d41c20600c141400300c0d10a480d05080d2408800c2200d030b0300403003a5500c0020a9103a4100310a900503d903810140c12905084414003c5480e01406202c101e04a04a005010440d0810440d9013030400d10b0011925110f103041c9804a660003406001101d9007070031008100d0050941140810210040c0903a18010980554104540007045003005030350302d1100c0040400d0090060b0585080008050b20960b0704501d01411202c1010700502d80c2e04503a40c0c948495404000110b41469007a0706020051821041c4120381441143d40c1d000b00403aa050000504002d11440c10071026105560382c1601111032440c0780540b1005100190085458000400c5075040c520134014180011340300100f4140c0d04040030900e50b07440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 503048947 1250 503047697 503047703
    0x120f12090308040b1005030309040213080a1410050601050910030b090103060209180f0708090f030703030207060c05070f060c030605040e030a030b030a03050307211a0103050612190f0b04 82
    0x780c04000c2000b5030200e82d1340d401150303c4000c9495900300404241e4a0090b400503034000d17076000408524507550607440c1801000c6034403c540701608185004496456141c0702210f440c07086000540b00701130340e40a101e1049506035076050404000c18108061420101d40890615584224003262500c038403400d070380070318010800541c0e03840754030090040a490313a0504488013030b40041849445180001150b8000304145410f51094441ca6022400c00b009a02c1c030009030f2000041200c10150550003800780d00f4083c00c010800809101d105844900c0b46000003000c4441c60800480041e19984c0035500e0310365203240005805440e0703400329048a0715800034250700c2c0e001003140040c00381d05000d1202c144400380c001e020300b40b400d5940606680805400d080502102604900e1004da800b40072801d85845070105000e039801290b1622000f801018003140041d080800080d1a4200003000f02030300c000940040152141c031000c0d003645081404400c440c5041680146004a01000c221070b000f240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 503050197 1250 503048947 503048957
    0x50c0607090f0f0501091a13031406100e190f1806050606070b04150b040903030506010f021f0e03090409080301060206071d060903010906060927120f120903 69
    0x41007000350000280c00d030740009103c1200907070501203179034460401070846c1d44041d000c140402010300f2000041c0038051450035565200c18001050000314900c2d2801103144e8000c1d00e81076119240901c0c00c80c1840c3c0255034000e440071011903010550621000844170019a0008445012030450010344004e410b4070001c50845000c5002449114810990402012a402c0f4504441c5994580e0301d54802040901801502c05900701d015620360000640000024070812411819260250081c00c0c2a0350850009044051004015000140c1c1500c18000c0301c85100c1d480040340c0d11034004c2d02010350041c0346400180490b103540e80300d1340541d2450920480c5038946940c1001c0f00249400702c000c0c0361008001094000005c0305100c90020340342d154043d42c0766551121134102203405046001340080100d440c1400002d03043e0f0752030780501c2f10350403150100303038411020b40d24000846000c500041d04c426404030000d540ca42c043c0000b40c2080721a402d2941c0842100f03110441203034002901035012507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 503051447 1250 503050197 503050199
    0x11701050a0b030a02010c0303180f0b090a0201080a0b04090503030702031b010614090a1409030405010e15030703091403040620031c0c0c200907020d021903050c060709 74
    0x280101684500500350070008080b01ca030020b41d442d1802c00b40607047c4400055680107040c406e4010748203007880e0034001400c00c1000e00d030840300503201038810340380007a084d40822480d0001140070556940c05959490043d11556107640040c002c61013103d03441640c460440000410610141d4032814071a0051600d4590342e641d0009502c201501c0342000d0f9141030000c2c04140742d003070540c03100181e05484442d41d56490800280041000282c240d10420b0a182007203800000040144203441c1c0c02c0c1d882c1812290601c00b40810340320307466101944a001480085c00321817080e840118114003840495034074402c01c00005081d0b42c09a001b4100041600b408601180e00031826405400a400c00542c41e1040704810340d0311b2000d50010481c0c5141d01c80c1c0b03a030109203100b08011095250400d10141c000c028644d88040305c40c10080541d8091069000000c1e0174a00100305007402e041ea0f81c0203481d000305241181c2901c500c0c60702040b014008180200a1307a600108041841403103940c90f01c04080d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 503052697 1250 503051447 503051489
    0x3020d0806310e0f0a03030507030f0207050a031806050d0203090109150b19080607030e07080d090f09090210050a1803060b01080a051b03040c03050f160b09010504050907031401 78
    0x158281c21202000f81d40081a8000b2441000441c6a48181c2600d00026540c8410308128050000400503400b81030020034030605010000c076101802034880c0d02e611000740300340f840f01d07199900280300d03900100d0b00a05c01b003002e042c070980045520001d00c00001440302c0081c0e950390040b02480303110310030042c0d4610258126081041c05413034080114041d54405c00d10b00500695200402441c403010162642810b2004007400c01540001c0c014090554080d4072440c0c1005207407103101d03c0382c0c3d201c40b8010f4100246012052241a00d296000307000802001156402507840350300252081d01000401c1c6200400c0c400b0204110014520441011543d0b42012000414041000c1c040d100913514200038008800003070010310303d050030450703616526036a03035080c0b403002c280343c40c2c3c005051405000d10b002501200031074000804541c0c02a40d202130f03505c0b0f0760031060900494400501245082209111a150852110f68046224900411007d40d41036060b00103100c280c0c0b1807014a00106100004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 503053947 1250 503052697 503052701
    0x70f02181806061509040207020415090e06060d05120a05040b070b041a0906070c02030f030304080c0712020f040f0f090b0601030f15050904050307050106060207030215030403020d080631 82
    0x304204607183d188040b0924034013605807081c0b03544c01d4411903002614104644a50700060203618120f003603034080340e58a80800c0c014248411212845004941c0003c030a0701d020803c442c1d0540d04000100070312101d088030034581c1d601010580040c440c040c40001508400301c0c4c004c0041c544503246041c060b00f020700d809416038141c04505902d010800f010414500300020f401644020300e8030304040c0d83d150f240042414040c07103000424450000208001c1440a510300601d407803a0444100c2d000107907501c0020801e0320038030304002d40c0300d4106460501d0a2500b03400c82602c0c1c00e02e40e0000103a0b403a010a40703004170342840c8011615490380070100201580c0603c90342d0071408401c681409002003500007601c01c1c02e0903006080c41038220b000800d0520500b0401c2e00c61507036016008200301600c400020b0759540710b03440105e1107001003a002451600094041da80039070340c150002c1514030b03c0c0380006c0d07074903081c02054603400514004441020485d0b05560385100710745009003854480c500626541 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 503055197 1250 503053947 503053951
    0x4170c0604050703060623270f060f090106080a02131701061505040503030304140a050327150316050c1f0b0405010f0308031306110a030f0c05070f02181806 69
    0x15294082070060f80800c40003450750105040807500341550441c25041804101d81c48a02380c10801d0300d220800c2055140c0c1c59107540100e004581e1140e0f001080d1041018140c82405031500260a07180890007103001d0790050a8101d400e180c40342c00e45511000005100c40e80c2e6010481c40ba91118820421001c10f41000803a1101c07501d0082d2800d41400d010a503244800b6200800000c4009102c4c0440d4a05105134400035503c0700540e540c4035403100c6001070310310b0713558007020b480081320101c6442c03480c0001000141d40c02106c074103411a5201012007062209040181d01130000401450083d44401e01190b0380c000490b1b0b103c0c140302c40b10700b80190125003505084900441c601001442280586030303c4508880c3d000b0b10300c9942c0d5031a8050101d031084c416000400d802d003411080207603200d031940684418142690104007200424902c101556a01c14980010800c01c10140001c59292a40010168005000e441c4001071090040300f06c1802158003615000c0c1701a00c52030030703040500c0403503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 503056447 1250 503055197 503055209
    0x305031f06020c06030c0702090906090c040b0901060f020a05070906080709112704020304030504080d030c0f0c05030f0d1e020406020d080618010806070210050f04170c06040507030606 81
    0x3251850400d0406075440c43c241500074814103000c400581842c461100700c0308000e6000d0a03500e5181400c003901d642d1a50b0079102009280101e03403190130305042500c1039043e168001818400ca41c0d10340301083c0c40104042c0c0300c2100714000d211101700491b000301f14080c02001180307000982c080c580071002d4201882900041035031420002061f1018a80e8810344001040c00c00c142c000c800c1d41c041000002400540300d86400a00200c20401450b80180141c003c031040c0000340c3c0c85215100f4000c03002c075410004540082044042d40f010340900c41d2505820052280c4210b03071031318075034821104441e081103504540c00d94039060400404c1503800c841c88216a15410f040d801c1908118010f501c40d00000c003000100b011820019000350f1707691040012091405441c60300650310b5100d5162035603070440f001070240c03180c028035160200041c8541c921403016405440c00d1510f8640e91741543c220b401450094001051110710070b20241800a24011071080d0000c0041e24614501941a60811b41c002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 503057553 1106 503056447 503056501
    0x901110d0806090a20030601030207050a0b010501020d02121206040612150614090109021b07060512100e060f0402040909060204080f0109050d032304030503 69
    0x1801581c007603c4600030780e654003103080180c0705020845000300c05006410719110740e9503c00707940c02000516000d45021460b0711020700e131040200c03050700c201a000b80100100d6804002e1130b06208001c2c00a001b000710f890154000500410108038460502c02001843d107540b10b50101000d80813190300700e07031114424104582600401303600c0201c940e01d4440c020031061340e4409003c59400008100c580a070782081c0b07124004e5000440d0b6200c10740044458815068024003046010708000d41e00c003034030307104145035000140101a000300513100442d4001e0007071410500c525a884203003510041d24410200c00030900030300c00c903400440032900d424400070403c010b68009004a40421007120080000951b11508071403032740e41c1c0140558000d0001d9420b45001c0d0b0090308815456265a1034111807614408581f440200e804400150001042024101d40c92120500c01080400302c = true := by decide +kernel

theorem cover : BRFrame.Cov 502877697 503057553 := by
  have h0 := BRFrame.cov_init 502877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 502877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 502877697 ≤ n) (h2 : n < 503057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
