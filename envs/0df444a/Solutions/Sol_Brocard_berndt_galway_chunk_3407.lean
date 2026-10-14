-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3407
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:34:28.932329+00:00
-- url     : https://prove2.me/submissions/33d35893-81e9-4d20-8943-96d07aeec298

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 612589928 ≤ n < 612769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 612591178 1250 612589928 612589933
    0x308061003090308070c060b100e0406290f22030c06020a03140306030109060e24150103021e0a0906110d020303010e04020301150b0a091512050a0b0406120212 70
    0x144000690042d560781d4120040c0c0c200300a440c012407603d200540b048690494000c7c9181c0c0110027800d40051402d480340104680a000041c0c0340d5200408900300318030508074031010828410b0344110104005c1c030384000b040c0007003803404040b0b0071000380d804001c2c2c554000d40014602c2c10000d102154006e01e02400951001d846d0030721440d10024100300c911074040c600040c000010903030035602580030210050744454188490342d00e411801d0384170340319200c40135080d04140c000e100c400d07188000060306c60784840d2124403a0020641c0114000d412655200c44120030200c0c201814000720000313007101d40c240342d448492941c100031000305401d002062920700d65011f9400c01600c160044140ca0644501e034070440105d50340c500000c0d016203c41413403201003c05405001c1400100c1800400c0101d81c541c44410106649804800007018468001030000d000200c0ba080301c61229040160002811540414210b801c070000902f06d030360fa540a2032400c0c00300c21900c4214140884400f8010044101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 612592428 1250 612591178 612591191
    0x702031c05120601200109050606040905150403140f09010908060601021009020f06190305010f0608040303020304140706230304120c0c03150608010b0d11010c02060909040308061003 80
    0x8041c1c55801042c00b42001c54010100040f400e910445030141d60041e015004842801d2030705045008005c4400c00340c41e24003c1c0c0c0005065030800b80920401c01364018020005210101022803a000010700120100070340074248440902c0207001826480440c1c591030340d81c034181b00001528190141d4402c7d0781a800c1101006841e03a00421083c0d50b0000f01e4902285c130194500c00900d040c0c841205440d801540403030303405442411201e15002564950324100080d9803107645412294015111307110010b0000d40000d400a031098000d15001840707802441a4140744d441d6090a0113841d4002c88000b0f403800c801000b801c00800204000c500d90090348910b98107180d00d5224006408007210410300040784600e50420550038015030082d50800b001c54084051021210301500c101d101c0d002c800d40c02c10310365051a24000b43c2c0e040410703502c190305025420742c0b000191100d00c41c1030811380e8080300074088022140c80d408500c2c0e110710700c02da547c40c4080c5001d130200065602c2908029080518080d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 612593678 1250 612592428 612592483
    0x3110301180b1603020d141609080d0f0c02100f120203010b0304030c022b0b16120f0b09010f031703090a0f151803030501060513090207060603050304030305070203 72
    0x1010349402c50f60b20074498000e2101e40d00183c0203846070403c5034414918092040c030400d8040e0202c1c0f401040200b00d29080d29010590031105400e1038011305205810080c04030340890700416010300c4500d0b060800100c2c00c103442d000240c0c20303002e0740d0b0000c000c2070189520252581d4400c80002e61000a903d00318215414249888600d0000510007414030040032214425540c0b00320001803065480ca41844c5d0980212003840502e45030240120b804007800004266940c695a130703d000544c10b40d030b844100c04031900c40400c024101d140031040c410380c0d545450b117403251106c1e54014041c100780945d1000d030394a14a46034144900c0841c00c26655013060092000500c0080b440c203030496000800010420424145800015856841841803528105800d20000401d84c000a16503000e500d0402aaa030b1350b0100362031710b208120410529420400b03050011002c90790242004500500c0002070080c0c80750758042c5190711640065001c120082507000441c54108500c03407451081022a00520302d003d13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 612594928 1250 612593678 612593693
    0xa0c0311030a1706062a0105280b0604050a230a0b0f130e090d020f21070f0611180616030c0501090204050c0d0f0b0f0907090509010311030118 63
    0x4180406051000010407035581d942010b4880c108516030111414170901c49406034510f906d006218410f50030600060801c002c004090b68680340f82d03c10340c100aa04108030745d8000c01c0502036003a400300040c0b00200d455111000301c8401303024a0110640c00c84441031002624080b5145101c3c132035800e1110500c112503507202030307607080541d010095850780c03400445220a007480da04040c2a40c640d100400004400000e6445030058031602560704c21210140c00035128000f4468203802e128081c4120186441e14000820289008a00801d405000b9988030400d49440e41c5500c5403003500450919414250711000c69090700040341c01915103203034188644502031824030f02605001220400d281481829048804075690041c020003e030301e131200041019401100c1c4032050f9529042280300e0940d041d00c41c1d4980fa060080200203640320280c01c00c4a8814001d0141007040302c001000078082d11208801030107984a001c901c6170344070082d003e041c21919145e203c040081f20200440001c0b4118 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 612596178 1250 612594928 612594947
    0xd151a0712050d020f0919050303160305190228030f0509030c0a0f1d010f0308031f0303020c090c1206040c03020906040e06032a01080703060b0a0c0311030a 69
    0x1c00303010306007042120750a4030940540400540454000280e0340c3c084e1071904001c0100c940111855100c42c00480640d8040d00c40c28041d0580507401041b501480550418030f40f05220700c2803410b1807910502d0030145507e44401e00101c009070f4440d00c0101c02d04131b040e503100100c480888140c601281c3d06a28001c02808d030b2071011000307000700000c9050240d1020b010004580ca0080c2c00d80000315910401da6010700e0052080014403403000071000b60424005040504032401a0b200e100c8641c01c0d511a00b03680d40c4090b059029084205a441401d038110300d0291000750301903005007003e10000e1040c00300c07511000740520030744130040041f107040b03000d60303041d0a0304800145c03400a000303a204201a07000b881007480590740b21101085c00500414184c1400f0321a11040e0107a0b450759998980240119082c0903c015854458201c4400c040d441070300b03a50740c000700c54507003c01c0481d556400c801007540614010000250500401820301d900441150348400030240258540b010400000704034080c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 612597428 1250 612596178 612596183
    0xf0e04050606100e060c16050307080a021c0b07020304090b0103092103061d090f07050918070f0801020706050702071412032a0f120909090a0501020d151a07 69
    0x100510f06014540714113a65400710700090052a90b0340d4240103210342d1440c0120107000d5400b041030011030b6508003c14484200c951000003040d01c00d042c0e9013000000030702d040c0801007410040030310601142e41e41341c240f40a0f984c55009582ea43d401c0098004c207950404210034145810202c1103000038034400715004252102220720250344401e108120003400055010460030300ca079411710050607070070500b1103004508007401c1341c1c0500c4080c141d5a032226520b104159004100100059414529110740c1c480c40d001c2d0401e8030182d5032540c2081341600c0303407600008916036010034584100800f40c41417030341080950004044041c035101005a203200031203181401303040710f08010305800f9020001d84036109070030f11100e4209842ca17000520f03000450340c96060540700d9008003843d118408101e00c10030694a44015250040507410f101c50b180001d0f1284070744e071041503148004034500b84058001c05039004d4003c00c80c91412418000d0307400c01500802c06211403603240d00300c142501c104480000341d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 612598678 1250 612597428 612597439
    0x180a060b030c04290a05062506061d010815130809090a02120a050610030b13090f0c0f0f03031b0f030e181e1e09010204090c051e030603010914070f0e04050606 70
    0x3c0c0c2d07000c8e0000c0300402c1070500070b204600b010300215514850314429690340031000f044400a83e43d510000c0c1d40c03011201c0303442000c6480000442c0031148020540c1140d07602401c01103280084410100e080e1000454030000c0303007540403500d10146503010540ca41c104400c0103052000c0d04101c4001389003804250007203070905560f902644950703186c10025040c2e40003480c02c2000900e8440c281a01c141c0d100b03110446070500c100301e02244c1c00c03400158080c01c2e1203150304215000b0741143c0d0255910307499031192400c20984a4050800280c03102d4031380505038406d640312180820200c06020307040c5105020f9400320750040c4c081008509081d124845001c951580c0040f080e1101c0f08000499a08694013135402d22101d070410180307941c1500207104440811800b00035401c104a802c0740d1a00810003060b041450807195034401168517005140c202c0070041c00045c0c2c140c900d5503100200b100140030040c01c3d1b00941c00c00c000000c1d8a1001900509906400ea1841e24140c0c0e01c0a8a403000101105d1295 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 612599928 1250 612598678 612598717
    0xd020109271a1e0a050d2105160b0402060d0f090606080c060f03100302211c02030316050c0304060e030105010b1309020703050d14040b180a060b030c04290a0506 71
    0x40c0d840705184001810040e04c003480168050500246489401c2240030380c9001f414010404144114100c51812144c5012842d00100380d58810780d6070140500281d0f4442d00510120715400d0180c4078003980d1030a601c2000502ca6110700d8040140cad0381940c400c1880d60405600e000d081d40768030b01290003100071031283d02d90300c0d52207a6001d9403000ba00d40019402c160300c5100030440d1284a0501c444c020311010440e00c0040c2c018904404031443c0c100c80400681046c03010812742c48024030b014411001c0c508000f81001102da10385882c503000340d40300c0700008062248020660400380b00c1d80f40502000d10080d442d04031480010017800105d032080c0d140042c2c0c0014118145031190301980e018032400c1405104503551182050f00720b50050301c080d1a201003200c086444805d080c0f11030400540504003800c80300c103035a1281340040c240103040d0754140c003030004622290f45d55480359612200041100e000004c080b94440d2103040c2a000c03540d805030450003018001a61441c0585504211900c0f060010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 612601178 1250 612599928 612599989
    0x7140f2a12070b04060215010806100521010c02490e030703230c1309110a0b0a090b0a120203060f090c0316050708090d020109271a 58
    0x2400c0e82d591084110366804240464400c0e4086403108554055000d0800300380d1700c07010b0003a20b0f400d09944480003444240300401c4581080c55808082100c81c10081c1c81040551070070030f00392800340c2842001a080000d408241e8010760f12211101d01c908803204040c0728000c0c5400140c03441081031400f48450ba003603148802441031040c03500000c4007070306030341d0910760301d2403c1080d1880d4078a8000303000441031740840d40140c0010fa402c45d080f000604c0c402d22403142c958450001c1625000070384494808103107542c065106c158003c8000c02200380d50941d10b0501090003801c1104036084024201c0040080c1112568060070b00c4000340203400c00160359448040002e00c1c13180801d41e40c0307074000320f070407082040310041c281c00385109030300f16608810400c181307000c05c5035244508000101a00014004940c050400c66a8092000d01c1810451131343c0b81c40e03028050360798103070390480c0341501151901540c4101050040b6004014000c0e2404082c0703500c1c900080b404114003c941480e080410301d808503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 612602428 1250 612601178 612601183
    0x503060d0f08130618080c0d171b0c040c0239030f010c18060507150b13021e21060301240302031e060c070807140f2a12 53
    0xe024500c054090001c2c0d076503030b800391540c0c05d043d045128407182410300043c4660301107140c03091108000d1000c660049196a0041c81d24201d00da04400f2050901c51140080f02c058a91075031019000b00820061103844d0400c0f0a580000f5143e20843d00031000c4100040f0b11910980f03031001c50b21011044080c0042c1c103103021207054803400d684c1407040d8207508051312010762000c1143d0415aa403028043c1c41c800c140301548000c1e105450000310104642c030003051010f140c440340c80c500c0c04400304041d14050005043c0d0200c20081200181e400100e0a1464000c400c0240101001403422402d03c400d27456817600d20754400c400c4900104003a40000c0596800b0350003100450030840d200c400325441d43e94511100e500b0390204a00030301c651800032030301542c60391190514120800c01031180e566058441c0c03225811442c0308a6442f0303c01d00511001400200e00441c80d40d504400800c00c2e07042e03494810b440e1003080042c1840400f150408200f0704d030f4418050b42c569050a03100850140d4148154a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 612603678 1250 612602428 612602437
    0x20307060f030230010b0307270510081e04020f0111070503030406020f3d140f070807080f150109080307080a090f0b1206060909010b0306040c0503060d0f08 69
    0x1130840d0030b44d401421856a0000250955030203015003540d10340c2c4c8802c000f0016220580b080c0000c682601c00c03c0743d4140b20280c00048085c611035220f07080d40ea0b94400300d092200f0710300e8190301080b800406c010814106a050045074881002100024100303a008500c951352580c04103410071102c0d20000540c02030801200c03008240140882e030f607640c1c1e190b5000b9181c1040c2d00d40c500550141007182a24030004403040310103180e541a03d8440181002e02c2207140c0c5208102c0c5111881d2500c1030281101001c0385c40920030310292940d10002c0c500b900000b001000021320b50001d002d0800c2c14412030a0342c04d09103d50211203010408800d00d03030140180c40c0800958020300c41c81c400064404100421540942201d0707515484a81c1c8080d214050440c0b106100d00907404182d4050040080341c01c3e90001950f01f05001400317003440c068076035001c614000004d0b00140b040c910000180255401e0512481c001c0c080280790035404e5041420008a9480d89508007a018400c00a010310030300c860401142d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 612604928 1250 612603678 612603697
    0x2240a050f07050a061a0a0b030112211206060206070c020f0f03060c070203010b240a030902060a0305160c020a12050124050a05120c040938060607020307060f0302 72
    0xd0311300261920b420006840c80302d01030860701e80c0c1d0403902d06241c00d107401460141c4403c042e0302390541c0e003800110702d440103107001e09950014440b00e030003040e100305426031002c095084d0b4411b505490042e10310401e0743c0c0154803100031580528104038005600c03201035140c05604881c60700c102c0d800180042c404070130400034258540503c07018007000203001d20003484464402e500a0200e2074004040240c48514000c40c00fa505108000220601c54880028158200c080c1130008c1c0341021750700442d0042d084034042d880807076916400d2020015161140301c161003824641089000241e6003c10030030a6507222740b5440d110200009020044290048c620300703030040c08082107002d60310008030b81104031442914003841ca0140b011030315081c22843c502442d001d200040080c140d240c01404003c06a0483c1941c40021440c140341d803c803501e84903140c034100304d2a0315280c4507562001030a528000580301c18414201000304100688002c55402d045a103e0b0911520114807030000b034010348a13411070f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 612606178 1250 612604928 612604933
    0x6100c02031002161a01031203050406110c0d0e031b060705010207080c0d0806030115060f0c0c0801060e0a060303020c06030408070b0403050304030219031e0c0501050705030402240a050f0705 84
    0x100b030500500041d41c808050191045042d034815a640c0c402c2c2d170090a000203809040e101c1075801c0c0060207500415000351291300700003082d414201d2802d94a40142c0741420041d0002c03560310b10f4080d40803591241b07544044000e0074030440701320740c44000079200100c03c0c2d0080b10041841030078810290705841c0a40e07002081ca607501c4014140913a11042d503480c1c2070001c101502d01081c6181414030810310a0103407000c00e01542400c0c11070948000f0300c0b0650030341c00c1044112000d0001004000102c0c01071a41c0c400100e651410520000580300e00282402c1e02d0b140b5010007000480e0b0f0019030310400000c11f440c03555994690b41000b0400348103820001c0d08484904d401d02042550220085120358000e82c2511009182020320007640000040041c0000325000c0c21842001000040e42d0001c1c1040e0405034070004107036540d54250b403c11230344036010400c04010013041d0308102c052a40542c184200c0060b84140018074600f040c000c004a1904100011454000d02e040d613404807010b89410a04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 612607428 1250 612606178 612606187
    0x315070c0c091815060b0306060f0c0d030f06120c030b18010c02150c03060d03120f050109090c08030408060a090303020913050a0b06070b010b090619081e06100c02031002 75
    0x3403c0030740c1c8000c1208071020030200445000c056020301c1001c1c01d8420b0888842c0c95901c1c0c0c10304000c1035400c84104898528030401c501d8242d000208500c00c0580c1b907a07140410500c003124000000c8500c42d130300289080060342001d4001807181c403603c41c213507079000b101d00a054071015800110325910703800d10680c0358684480404119000074100b102414402d4644d505507032491030030019400141e80c0c50b600020600450b9002074010070440c85100300428001810903460070002054803000e07401012782c00c0d5a001c000c014821075080c9000500b040000441c60545040000d0356505001030000c00400e81c0c55040f1000c040c480c4e0100c49051700c3c000d10200a400041c0201c0c00200380503101c402000d441c000001e80c0d18280081665889034001007035018681ca003020291041d80070b4030503564091020402100c0c9104d4246030080034140c20b9913464007070718143c140421a800280b200c0601092030703900f040318568909030308409451b4645400c41060940307102085c5409402d901c0804860700205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 612608678 1250 612607428 612607451
    0x2031b040b0c0c0d0210030b03030906070b16030b10030e0a08031503060106110a08031806010b03150a12020d02040e010f0225030926010207030804060b0315070c0c09 73
    0x3010340003080b401d60548030031084907000c0020500c0e141900135046103200c24407060582c084d0740202c4400502130306481c034080d921000500745a20540d011640e118055050210261440038250748141c0c007410b04000d4294102c3c005400d80d080800c021040503250007901d140c400043c80103984050f40030920513240e0a1040086402c401499841802840b45600008200e446441c0070480000b0844c06403080c0d08403078441e1801507000910808a4044030000252069400c020700b60003045540300d210385034104a41c400440000c9408014810f0110f40380501880c103c181070303800700d180d048171084005a00707440890064950000c1000044d4030303050075032480b03006503001441c2210700119a80d143d504004c00c05c1c0648951150003a001a04205d02030003140903c407560307070308165020f01c5c18418800c0c800c00c90b82a0b038004442100012598428403007000028010784682c00d0040b0044c14590340071480f00c61107948010100420000c2008542d0709010014810070701900c0520428800310224a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 612609928 1250 612608678 612608699
    0x5070503010e070e060406110c0a060306030309170c010e0f041b09080105190e0a0c080a0b010e13080913091a090d0207061409090a0902041802090a02031b04 69
    0x1d1003000402c00c0c00c4400078648612410810307200f900010402c0342454103100c4225000c0006040f00003403440341d8003894110b40d465034000801024941c0e00031a0050451900509031400d55000320701c06441034000030340c44980810b548620071006c0c68200d000d441c503040001c01c01c00810b5000c41c0c0041c40c08014441901c55074804032588919a2100f0313400503940d1013141d00726a0100c460030b13803103650b18140c4800781800d5000310744c00000041c1101c4d18046c0d20740391103200740360a40c0603180303d4ac4804c4800c0e0070800c00d00106401400c4d849007c1485182c264100c0c41d80ca80c080b54010465140056480c0322651003030b5402007000d5210108014045491505070521250014030400c403000580014206031000a0341440038240c0d41e0203028014a044802d07103058201e400540b1132483c1c14410301c44180c41e41e1034014410a11040c01007160300407401071008a49494180c8070380c82600301d03507010150300c54800c03c0c0c2d081011810010394954a010180d45400303012180f110b1688000280010f1341c5459 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 612611178 1250 612609928 612609931
    0x1c030216062726010506010f05070b1e0a062301021b040204090e2a030d1b060e101a0d020108090127031707080103060518071d0a11040e0a0e0105070503 67
    0x20714001c011710707102c207001501c0c0c8641225108002600400407400042c030240c0c10305400074074085030b40580003801c2c280c055840b901200c87c140202d41c0c582c402c1101c4810408540588880b005090140001e4040000c0d00c44520341c0401118501c40c01001310582c50b281c2c1200c006149004080044882c00040551100c0a1481003032096070704e05001442e450040c4414519140d001340140f0f0a02c00e088400da039030003141001c00b490807007004400404190903003e80c8003034a002102500c2561480c01d44a01240d003100b1a064152400c01d4140503e41c81e52890440007640908019206985944000d4050640d01d62003d9003030000c525212500000b20b40c03055201032117a200c40e0001030801014600381002100c0da0f200140c40440104040f50641e0b008542011a0318654841c4a46a0140794684aa980d001910b5882480c460740f00706c0042441c016000701d154032003030000e01030380301c081d0401d405140100440c2c00481004603d500340164015012902e00c0c4009019900d400800039055800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 612612428 1250 612611178 612611249
    0x8071e020613080c18062b030c03180b090f04020f0a020a0213020703020c0603040521040627061b0f060902090c070b160e1c0302160627 60
    0x303410344d96030f0f1501d01010300b103455160807454440955590004c2148090314a41d404a911503a10385c100c8003c1103107152002a28029160401010801c0c900103201c01301d522010384c2d882140c09424000c01c02000c08a8415031803c494444c001e003103403070000d0003e1007582c0d2444505003000800c803891580208411001500864108141c038120030000340c203910843c0c00090068011100070166450010b002d540c115000f01c1c1101d00e450411608400c1d205c0791800100000c0002140030401103910040c46074940708000e090031305c6c0801c25008019a1902c5001d1074082c88000100300100c4451034400746046031f0004407019940d4401d080450051280d4481079020354030310383c00030314649403080440701619440140d08501d0340c0c4000d501c804a298469600082100351a1800310070b035a584018001c1841c20b0000110541c1a441d02a260801c1411444103c008505007008083d0300085860004519910369000780007003201d140d402d20761107412110a001840507010711003071040c10101c21810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 612613678 1250 612612428 612612433
    0x6051e0f0a06081c030f06031b09050702010c0e061e041401031103040b06130f0c0e0906040b10031109040c020109022d04020f0c19060b0a0308071e02061308 69
    0x740c0f12000aa1a109503801807101c20320340303c0012220754800d078003201110250040c002112501c1c1c2d9604c02c441e1010b0015860010700042d801d0150b003139241700313680e00710a050008202d09007803007102425003100450228400c1001103910388104542100c18040d01001d201c01c2d40d990341c0c54040c05254403050012540c002468006810002d00002c02100d024503080f900c100829654001041741c0030380b0b2004c0360900c05840c0c095400700e514440c042e680801d40c264884441d0302001c0428040085401042603100d141080004212512003401c039604040541c90003043c0d11000005079642841482c00c8503401034038150242940c50f80c10342c408200c091084071200841e2003072800291700242034000200c41030000841c14451841e10380e00030500042000341c40707070912144100c92828030380c0c4106110501c206500387e1408112241c840d10319551421500020614117548810321325010f000030041c6011542e80c002c1c140f03048413022074003070030b64000d1030b071541c03010404d22506c8000d84901c0f1328a610b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 612614928 1250 612613678 612613691
    0x150b0909160b12060409050109140a020909010605010e10020106121211070f05100309060501090219021207020d02040e1e071202130c050d1503030f0e0a0306051e0f0a 73
    0x34124141298843c2e0a40002c582c07503a100c503810000100150384085440c2e660740c070002400104c0480b4003c105c512200d010b0f04901c8650b0060091840d0000c0103c101d5900d084400d010981c0c2040080c50000c400b0385201020010082c0160b006261a811240941c3c20220209041010410590072003a001e0390310103041116940d5000d98a01d00d5018110841c500b0310000e00c11070501d0b04003c1c544000520740407507207a031991030310421188280c0204540540000300a01282c031200e41c000c160400b244010b244e1448000307040324036802141030003480f80c0d820001010540d80d440e042001003003004c0080d1507201140303101c80705818000a00c1c10b4010b0144450010741c520a1404000f0640d030042c11102001a15400c00700c0242400640e80d030a010040c4107255103200248107a106010003002000f12040c11410080c0034089184e41c00740804c40402852146612100308180490342d00a001055644910780781121940b0000c2000b003c0000b00410411402d00c60000c003401a0341c1441c040018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 612616178 1250 612614928 612614939
    0x20715350717090a0809040f050f0108070605040609090b060c0f06240906040f060f060903020405150d0609051e21070f120905150703140313150b090916 67
    0x30b042044692281c0340d0015900b140110382401c00609811100801c0003d040900d080b00d082240c0003900c181080d58400b9005001c441c2042001e070000d040242032060400d4508240180204410b00408181c1520340340c1400b1240c030340c03c050b10501180350064590441c10300303025545d40d100884a5001c0d82c552040d80f9907185040300c50034003d000c0091701d5441251346801c1400058a40190600701b000d80d0b80000203119140c41240743c010b04411b50700c0703501041c40c43c010001582c40180208c1507001d241090740c50b5543c2c40e1001c1849480d8442c6d40400c00c81d101c1e08209080168004810102002c0c0394400420361802241c2d14045403c903440300c0c507800810809052480c02a480000e01d007540c072200c98008500c01c040802c4820480d49400f400c03003903c2e2404240c107440034a05401902c24041001000c154000e505c0f0449d1201130400d05046261019a000002c244010064122344d107005140401d80304c582c01003043c1d064060040318140c10180c86055481c11090800258403c070110301080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 612617428 1250 612616178 612616217
    0x10f050115021905071205160b27010c0b18060a02030403053a050a1b0f03020c0a0c030b180303040218070c020d080406020d0207153507 60
    0x1910092580200b1036940f4001d0380031201c0880700016191845840707800a00c4011880d440d40515104d8000f626241000d0311556100303140581094081d50b1090006500000c4084682078003001c80c6607011010640040040e1030381c184198001e8807810380030f0100a0742c00c0d150030340c00c020418120211a01c030b903a841d0341d00c0100e000540e801400510104407030002070001500c41c1c014000208118441c241c0111620190351005401d14100513446904000030315040f84030b12210509104100301c000883c2da640181300d101400000d400b45036001c2010314049004020003240241e110000050725600e909105002c9036084030910a0b0a0380c1003509488002d021040d0b9001e1903002d4580c0c02545e1180d4101880170100424000030465034070a8280940c0d900c01000810b0703070151800540d80c50034148024240200744143c8006e43d88403202c00c012003503040c0351581c0501d01c1890213045c00340310789040032604428961000e06028030781c02243c4101402a800703a0144143d6190040c0c507200501114030f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 612618678 1250 612617428 612617459
    0x6060f0d470a020913060306050a0e01051e070203040b0c0307140316060b04110706090309050303091e03011b081005010819052203030608060601020115060e030106030212010f0501 79
    0x6420712650800b00700c48040e5500a0301507410018458a5101241a101c1048a0301c0754001d4aa40d51610140300e05517002c5d200e0204454120300c000d000e1854180903540e60300d00302400d422588401180000c0d01c9502c24000d5030080d180950740c03140e40d020382020850b580e0b08101030690300c82b03035241c01810040c44000110f07850000c01003200707542c1494540f1142c0007003510b1030503580c019883e180300c10216400c0c03200405800d4031694000800c90001d0400400040807a0841b9000382c3c8204480300d801c0d5140801400903010140110541c43d00a602080c09043c810001c024007003050a06404e907160400486441018410394042603d9915030044410800c10303101c01c031007140540800086200c154002e07036400030094250b0600d4201e0720510028030f605445065001036a104c1003441440c20030f000703180d00840e091009218107840501002c2203028580b15240501031890750a981c65142034024030015900104031300782c001c4080c000c4038003030007503203580da03240d24985800460491141d04505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 612619928 1250 612618678 612618803
    0x6030305040e011e030602070302070f0902030a0506010f12020310030218040b0601020106060f050a0c17090906031606200703140607030c02060a0b040f091212020c06060f0d 76
    0x5492862861b100c00c1c00940c0140c03c01e0701140074102000c034407042911800c40003040f00d0f0030700503500e00e0001d1074141190009001c0504000280c03181540550703100c1f609a0100008420040c1e4a4039503840110b04860300f90310003900035402c904c8011886c0007c0040522441c0a040d901c4020b43c0c81c50012030032136855004090106491003007850060307108101400c0c82072003604000111454646840007000d100b511b0900320290001400c0c2d00c0303801d1104c0e009801034400d0300206010951203925800c141900e0164100300031951500c555200700b008604c0101d01100002d4426290f2a81401d0310080d5450001d41120700c29000403600080c40391081600c101100d40c0070f03000c0d0381c03220030320140035180c2681c24540c0161076960703450312240c4d5840343c00c1443d03100f03205d41d50410307450047c040d0803030040416120180e841400040300c5440046016076001030304a40c007490a044480001c2c50792050f64201034070500d4031100c03802141c4003a404c00e400d03114030001d00c440c80c0710f0b100000a2220034080c410 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 612621178 1250 612619928 612619979
    0x140609070f08030331080d39170f07030b010509031f020c011401030302061015030b060c0609070618081207050f03130e0c07030f081906030305040e01 66
    0x40d1601c45200020001c000c9080170b01d441024902110410b07044e03190b2016a40d542000410481c0d0740240e11a581c2c2c096401c08052030700c50001d000074400382d070301c0030b22042c0308500c80c121414240c0c2c400c0c14107044107404d0641041c26410f143c000e195034a00c08842440109241c540300d1089580520295092100e0080c0208542c500420000b0311036508800f203201f460307400b40026a4107400a018402c0510040c541014056144d8140245001005084074403a010b0b200400d01040e0401003072454460f046040118100190901042d460f1165650242442c001e800a020a17071101040980481d0f000b40d03102c00d608042c00d0801c951000c6da43c0302d25030a55104000070400c00c0708650182507214000c40544c0d4540c503203100e442d03055500c00c46021a001c45000c40c2030200c010100c41c03603500201000f90795070918520381d401820a0f102c803141507090045080019038000c10000c0d00340d1000c01244d0b03090062030f540303203000303845504540584610b240f03440c4004281504511000100c01110050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 612622428 1250 612621178 612621181
    0x9020d030e011110091209080a0b060d020a030602090a05090702070e04080712080f0c120703090f0203120405040e03090907050706060305011514040e0607110307140609070f080303 79
    0x4066030003110252145060043d19200000300c0d500501158040303000504011070314108a00d01100505000d54020041c0882601c0038400040c00254645255902041816454440c40001941c459407060001c1d401090760700044104501038001d014030750416034081c405c09407a10700f00903009000303d6107000141d0044500b005418a909540c0f5046402540c040d407910038103032110800140082030203c0801c11a105100d01ca03188a2401d81d40501d410b460075046c15000c0115801030400908000101a1524102000d100e0030980307012115600904070740b012110305241d49101e402c544212407046141c5036010701d24000100854840100090081c1115500c5600a480740d4106490071341c0e0300d03540d86802000240d800d101e5040f64800004411801500d0400e46030211500c030a6030354059814104004c0c4079100c001072650700050241400c1191246150351149140140e020107801a103030101180110750000c80c560f070281c03001d10241d81826441e442089194050380c460180700390b01c20030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 612623678 1250 612622428 612622433
    0x16091506140702040603020d1101020609030a05120718150e0a030b13210e0a05030a0b0c0901050d091a10060c06050606070b3909040905031201090b0306010909020d 72
    0x5190883c401000000d1058a07600800d205070801134089980c816402c034404020360301041580d900031085c0300214a884605d0000070418041c0e240c00711744d010400d078003044049014143c1a543c0e4145130100740e8030300380c2d20a442c2074012004e0000d00041070b4640d035010101e0130b05142080030307a500706104c04000e454050b0b001c05001d00d441c00580d005004c03103d0702c61164009204c4400f50505075580c42600842080400c9030281c0d295200900c40d6201004890005080c1028540d114403045103c60320b40d0a1500182c1d4113110315504c0303204130303440e0506030000c008070090f1502c0300800c3d0395a048002d544100c41000000c1a601030000490012005500060120b0300071540c4102d0240c10b00c1d05008403a41c441d0280d010a0700c40c483d6070440e64140340f0055a40310301042c01c808645440400d0740d0514144102548107602c101400707961a144445d09210302041240c4880d1440d00d90f110b034540c0c2d511100001403c5c410035061090048900000e15000c0130300681361219001025200c1407102035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 612624928 1250 612623678 612623717
    0xf020703050405190506030406050910020c0d030902030f1f0606141e16060b040b0405071b020a0b0a091d0c0405010c05011b0c06051f151116091506 65
    0x440c3e0000c0b841031610011a4944501b805140524030901c4042085d04203852001e00305115841042c0d0041d2041c03086610303071240010101000c102c0d41c14001084100c0780046410034580003400daa482c410361040d020022003c484507030450040100400c8102c0e15214116003c25000b58000845c03903090040710049150354030815200311120344040c1c034200c201d40310010500200903050f1841c1d5901c01c0800c242d41002c0c0502d00074000b003290204054640b661307020f84400c0d0700024030111007110018000071525507115401c0178100b8901c1007501c0b413a56030002070801183e8083c000904110903a0030340b00090704000c0320b000c0c4403130300080303420b060400e401110681e15401c2d050300c0700d64886440c00c40e403481c5030142880d002d005660703540c451640c5060000550303501400d9222507451600c004904403480c1151001561940c2013044002c0c0340c0240101c41030104984600f2550107000c4103407903200c10f1081004102e5035503c0050041ba843c002c510340c019002403181c070002c14210600101304000701e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 612626178 1250 612624928 612624949
    0x18060603040b0a06261510170c0306040605071403012916111207080c0409050f0f03030627070f1713110a060c020f0103140702100f020703050405 64
    0x1150f50004015030744141405a81604142d21601c0c0002d0110341c410f084024010b41c02c944041080140450074681804000c481042c81990075081e000441d407415042c00703015a1a01200040c200d0360141000c3c100800105000d40d0360201044444141c3c054400b4504c066038100d80301c0440d108401c1e480340c0c850203c0c00603140d1a202c3c14410400240b0740c0c801440c80317018002409072202c0605501c00d1014803459140c2d001046066070301208081106401c0012200701c0c441c410b0b2004240380d05d1515080d8a812242d0b01101e100d801011400c0448503000009540b007030230125000000d813003001d040e240c00c00e2000288240d41c080150300003803d0318011172058410040b90f240101641551a40c100244c00040d109000e58200600b030700c20500c1007006100062560481c6d030f520085182c00c3e405420306000e240000d008500344459060b40d80c0c0294030000d510303040341c000600103260003131000351240040486003002914290b2a030508020920075500280c1d41915940d203894101170420802322807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 612627428 1250 612626178 612626191
    0x10e04020d0204050708070e030115050f0105370f3c08040512091c110d06150618091e110703081b03061306150c0218060603040b 57
    0x415207941c00507252442820f106454542e5800228144081c00904040c03070b641050780300c3c2c0e046c1200d05c04007000b0544804110b51044820001841c150001030b5494029031070140b2440071100f05034040300c81000d04e801510b00384200c0d2003151032640c03138069540c120604200c2c2e001400300324050090518114085919450030b80d52211403118079110282c1c2c541021134944005049507050008009040140e400000d406d112405c1c1400160b001007040c8104a40c9000700a091072100311040c851080e03c40c82d00058042c0180c01030300100d0400030041e02801c0d0704200e4250014100041c1d262150400b80070100c045600c0b21000c52074406c090000c0c0c0801c044207200c51840002d04a0b1920b050b118a01e2000f554041300d0340c50b07013550b04015007050300007000c4402c01128040c55400341081d0381c1c2140c1d8006070440301d440d02e051209101e20014000c176002512200300800010141c1030300001443d04041c82228411103500400c0526030640d40207031041c0f908007105201040000d442c0003681a800780 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 612628678 1250 612627428 612627439
    0x2d040311060c0c0303040f140a06021903050c06070818010b0a050402090406050d110120030a050f071a060a05030318240d02040603111603080604021e0306040b18010e0402 75
    0x10b03c400000f90865202c3e50107a0000c1103080020403407800202c41d0078005050032244025420300e0600040c2d241c18040d1705840740e44400aaa420400d8000c07000d1b07504074000042110341c0703880d0503030025106a80c2901d444a50010006114403802d00c140240001180083c040c01280c5181c0b809120285d042004145c0d0b0003030301c0303a0011816444203640040e44601441c0109144009100050320480446940d40e10401541030303a5810540c0c00403c075004103e051501654600308460320708154000c1c000c000b803094800c10040410b00c1c600d042e001c3d01410f001c03107400e0704481d0f80d0410180d4a208002d5403086003640800711110720714001408035071038810896900a40c0140d040d01e00c010398800e003640441140c0c049803e001d226071503c50046a030b10204041131130b2100c2103800380398a081030340000701044440b00014600341c5850f0107940003a1964100c4020b41c031402d01414001d600121021030050717107081411211480c01c468031401030104003140d00f001d6401c1036010b00014600410607a0002d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 612629928 1250 612628678 612628693
    0x20010b0a03121b11041407020604030503180607030e07140f1309170a08010e09060f040c0b1c0c02010c1403070519020f070506030c0d02090301060305032d040311060c 73
    0x41c1c600c40782d2040e50620030b03c04044c0c1c0b0250300f01040122202840700382c3c07040054404010b1003e0f0001078251700305402d81000d54a9542d06103080300388a1686020412501407403090142054040d0015241003002030b00350f60405403a14444010141030103202c0707038840851004200c1c81c1c2480903a5500d418804034000c00d1000c040c1d1668100142d80c8518603141003c000307002c1c2c2169074030920417405041d200594400c14180301090a95401015181d8900440c940c00810200100502d4400c000d0040540d050b071104484898405040700b0180003200c018100a14600600d1061003440d0030621b4546540071111501c1031492100c0d0402000c22041c0b003070801c101c0407401c18078250301e940c00b00c1c3c541c020000e01ca1049040350503c1a6a0700c154001d40080c41130182403000303203055a1112440700001070721030144c00002030143c102503201130041d00000134651552044016401c0c040d420701f40e6003282e0340300701b90403103d40c521881c400a8040c00d071580014041d0f25100f001001d204401c1e40031130b00d40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 612631178 1250 612629928 612629957
    0x30c1c15060822030f03020a110f0f0f1504030c0606050a0e090c010c0510022a061e010605040302090a020d06081c02010209030a02010e0a03060c20010b0a0312 70
    0x10300400d81003540403a41d00010400c100218002400101c2411100c22441d0b9a1a68003d409903040da242a42496000b040410307000e485003104c003030260070300c80c01c5a0b0103441d84000503031a0700d901d8003454154054040d200031b04c030f003000400840720031080c11404401c0e60780c1d440841e0030030029013046410b84c0d22890000352907a43c2140a1000d090f66980c20786260a01000f0140f81004262060b4180010811550003043d0085109404100c03445005079a0713800b001442080c050801c03403142da00751081000b401340b5000c0000d145204094902c2c8203c1c1c11460001d00c00142e2400344550000110104014801800c001104a0300700010440144c1020300c40180c11058a03455040420503030b20503492122200c21940e545d6807410200c1c00214a000400380200b80c562040c03000180c1844a070401088113911601d1001000350381001041100300b20a02d0000d2401c001d101869030048202180242070020612401c500c0c2c0200070518140245540ea0301444014070103482820b1154442d5031680 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 612632428 1250 612631178 612631211
    0x1905030c0f0304180c0804020105130b0d02030703060e0c07030c0311031c0b1c080a0225140916030b04060b2d030903040b031902040603140606030c1c 66
    0x1034880c0c00c14051601d841c10002d13018440303201d0840e14180c075400d00b5000700000340c2080710281c010780c080ca4000d41c1e031030440b00d0101d00310350994801d010022000984003180784096010f1401000d49581c00e000c0c01d0358441d2103012034503081c0e13421940d4441c00c10600000038001c2c0b1a9041892081c10b01c0c6200703403041e0b00440e00f160402c1d44225031880310303c1485c6606150610603403640e4002112070b03c0d850610b4040400c0c00b0020701070004d001010001d54806443e008001c0c0c03240030008552501c40181c460769102d000c440c420710507102200c010b052201620b14000c480703507120341d0740d500e07882072001d4540e041200607001c448103072900290380304804540a07256500400c2001c000000c05d28940003201503c03103424013118020100400144140b01203010044110b40445a0040000e40c4030348641480c241035440350035101d000148002800502c80d40c144d0041e0850445410340b84070b4a55505003446110301c03040b107403014442c0d02000000c14480401c50440404144104005243c43c030340068002c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 612633678 1250 612632428 612632443
    0x150e0915010e09060106030509030d09050708062404060509150f09070504080613050c01050a02070e27060727050406090b242b1d010e0c031905030c 65
    0xc400380b00010401c1075209007000746900510851400f0840c52405580361502c034020180100c1ca1341d40c40c0c0302548140501040610040c25804003910451b0419110100440510241c0074030241d0b0780304824100d82c40e00744a41001c80301c0c090704d1898159a104c10503032041018a031a540d00c0601e81c00c502055484030f40845120390060b071079040d911803d160000d450200002c250103003500341580c0c00310000d40c0214281c1840902030a00945502c101e01060303061041980244415016005c100010200001d80f164688a10300c0c5110501941d01c0d0301d03168555000b140e14a020034511000701e00d51500011850303568401c00004c003c08151170703000003820341e405a800365020303a4846d0501c3e1680e141606007100080c00551860308008200e00f841c00c201e0203502c0401e42c090541c0c034180b2452038a2150540b0081a82007010401e9148101010000c01c4c4054280000c561804811000083c000203007500003501c010700922000f15800000402e41995000071a45800300f4011400612801c00148 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 612634928 1250 612633678 612633689
    0xb060c01051512060603071a160507170c0a0e0a09050604060c08090304030309030312020405030307060603030f030e07091a0d050d02060c1213061e0203010e0a150e091501 75
    0x30341c2d101040720411400041020a902c401c2d0440802c0c0700707590760009a0741c801c13240c4200404440c02071a0201d03503d04e0042e841140d945031200c80c000c1c0208030010805205032104100900c20b04031498460b15030b2034181c51b400307681082c0120400d2000c0d000300c001c0640c0c8100a403501096400080c1d070741c02c1c100700c0151001c83d001919120207080307040c1c0103d502580694010002c42c1018a507480c010310480192002405100d24040c042901100390f80480c0c02501c0040c0440769904014503080008004a01c42500010f0003030000c014003d109000e0034500b80d1800d80180200f90030010654020400c4504050303d40c15806000c404907160300e20002d8075140030300094103c00d0403440303019023002e41c010800c0701e160038200059041c294485845903003140000d84560242c0865151102c010a2182e001042d91140315051502c3c015041e00118180c81e4081048003450321921240740649103224030482c51010001c5081c00400ca4030185564022014030807076140c2440041d59030400300c82a00710 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 612636178 1250 612634928 612634951
    0x603062b080c0105010504090b0406090c1703030a1d0c1201060302150c07050102031c09050f010f060603060801020f0a0503070c080711090f01050901152a020109060e060304060b060c0105 82
    0x400c2102c9500303105081c010401910288232480b4135a41c1d03807c110300020002001e9954812400084c40b004ad40030300040c08000d02043c01c041da09143d4903550360070407192400d806003030a00100095500c2201c2d2810044450014294210f00e00c04101405520311520070956589500003c0984c2c0c51240d90f002d030310401c10092307a44401d101c0005003860101d8011a040d503004110018558884501c0c0e204070031001100062020464a41603041c818044ca05200360360814040713141d003142c9035101c0d10407200030b920108685540c0750b56050a034040c203030004080303030000e10003020220b00440046600003100c0c40d240038011519681c001c501d80103200300b9102ca0122070884c0c1141e0814448c0103801444003006402c40b980741c140011540e201c14040e03100310111151844455601800074600700c0100d558860031000d040d0010300604030b503460743c10f0b40014810040018440d004150507661020081c0840d482e56455403140d4014150005030305410910410121503044c100703103e010b0080e011402c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 612637428 1250 612636178 612636187
    0x30a020405030714010c0605060102010f0504060c09061103040308030c0c101401050f100e010509090a0b01020d050c0303060d1109071805150403020f0a05031f14060603062b08 77
    0x80c18a8080d00360030a4880c00d4000050484c80da800003e600a03e60b4400004645951a0350040780074050b1502801349441c20032090104010454000000ca080c840c0d071803000d86681c1d0b48040368040c030052055400c1f80c004000a1000c03e0260000310342c0300d5450310250303181c50080d50000e880c1890002406020369030b501d42a906d10342c0c50007085801088212030b0900041070b0440020304410b003660f5030710103004c201d400b03000140c0d0081081c0d41090000070424611840e16000d514054099440c40a00500400115607001401a416030380072581400c02141580d641d8010b0002610230350b0400c0d194aa000517044030b003a600d0200d031074441d6602c0c6e0780310114140710101da03081030700c0c0e2500494403420f4580310301100c00c64190309580490b40c0407180c9210880c3c1020110707403150300c10f80220790513009420141c07200000c100c80d0b242d110629200c00308000005901c82516404081c0d81d220b0f0310120800102c1c1e100c0c54000c0018024440341040c5062048603441703d41000d0002d540b0480d010304000c0b0303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 612638678 1250 612637428 612637439
    0x3090f0312040c0603090809090402190e0901060506160b04030519020f06091b01030b040f0e0d021501030b011202041d25030f0f111c060c020a05030318030f030a0204 73
    0x185001031500d1706083c00428015580c102c46030141c5c1140902036060300000405554400038024069110a440324094680714000d012051302c085908445c15070a09030006210304201c0111240d20b0701a6042012038940b9030348581c1813440140c004c2e01000418016a00741c2030500c402d841d694280c6400030300c06460b20501c0b42e0305117007000305400c6064004203100000b621071080110000303d0240b800042c0c0b000c058000900802440c1a521003152410b144181d04460000c0c682903400f0207502160310304801c10510002000c1d09000080c181509230004221a034100003c01a41c9407009201048000301c0d5807906070181c50040310340850f80e12850503205100103800a0302c01c2203003503250540c9404e003561140948010040b000030101200c410542c000d004040502c02d03000c280040ca412085544000b030b03c05600ca000c0803c0c0d54440c0b811130142d0711680001003003108a139012018506654130240d9540c0c1101007a05661030b1800b0030045011826501002107200d00418180180c81d00d0424 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 612639928 1250 612638678 612638693
    0x503030c030103110a1a0c070f0f06021b2101022116090b2505030f07060605030604120f0221030f091603060b040f020a110f0309060f03090f031204 65
    0x340b04d081c0203840300d40c000d20417108103491503d00317001c0340404170b42d441500c102d115282402c2640a02c4489012003130202d007a0224139075000894205038210b408032518180407000c1e000c00c11a50b241d020800c4882d000703000c2c0403034042041764014440014103180c0350030214035891070519100700d4003040407002c0003007140f400c617034100d01d01010b4a00340302044c1c142000c0004511400040600250300d10001040044117031001c0044c440d4413000380c0740c80f035003400c81600580d00550400c99040d82441408151400c1c00911a0f204035044072440c84004841c0005403401f80c11000100114014400850055020111418001c4525400c1c00f6980e207440c91101054000203042c0c1e0026401041c01441607030030300040c101c180c07038001d00c000130344200c40030004000303050306103e07042220300124a007000c443d0051305c0010a9201007050b0f07000e802091580944038440c0b03044250b482081401600307030301c09075140690740c008000011250300102c8000000e182d904942c10103164805084200400c02481 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 612641178 1250 612639928 612639953
    0x9031e050f150609040507030807060b09070507080a0807180f0e060904020d0b0921130e0106090b030a0e031c0606021b2707181406040b0d090503030c030103 69
    0xe04001d00b440078101c041c5114000400340c400391140041c3d10104040c48402d21205004541c44403a195981d08103141400240043d1004180b04800783c10005207824081d500701d0310090742c044041d0380340102c0007030182d403034040241c000c000300040c04e400c20109005820500001e040041d240f00e001c0d9140034200094484024001c5001d100c1c440180001a03d0354110000015889034a405041c0e4948402c9441c0404c00009840540b00b0584020030311030607a40145a240e80d2941c900e840c1a44400f13002d0b1241400b0302c41ea40005a0121040180340080400340d40c200d4600c800103e00d104030301c2d03415451034201428008041c002001207025418141c42410002d1034a8005014400d200b00a80e5007406210036001c3d0145046041c1c07a080c0d0703010443e0803030340080c41c408500514103144200411040703401301640c00c0c0c0307201c03100702254803010b0307a240c0304107a10700805417443c147c10480703075802079004450001c1c174450301c401020000031000d0001c0c3d44600d0302c550009071258518204070f401d0511 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 612642428 1250 612641178 612641203
    0x20c092205011805013c11070303052a04060c11190f08010506030a060c050d38030a020d030203071707021503040b18070f1206050603060106020307021009031e05 71
    0x1812080040070500d100d540c08040c00c044180c1400d29504e45070318000b41c81450151f810140d00090784008140e096400756024031696021105504440c40b4190740141d4010b04a000da03a005000800c00a849008080c100324420a00105007201c0100030403c0011150480004421010000e11103005c11b100300d40018140300000313105600f0200003194646600c00c5001e00000c0d00c610054900c01d014404640441c00090403c0005c0740714155001a1103880d50744150010051000c17030300c4048160071541d151050001c002d000000c00950800c048545006021030540c00144880000315810040c541011510094107503175400180c4100a0714280038401815444421700500c408201d5019041e54071031240300c88458810f0f8550242441c00c0c206500c5102020301c4010003042c103440030040351268501c078000030700c0b4a8503448101340d1640000d0103500b005034011302520000d0301c0c000c41411030891060403c0000070391aa103410910302c442c1e1a06141028610449504000c41008019000312 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 612643678 1250 612642428 612642461
    0x130e060a0c1b0605220f02130b0102070b030727061e320403080702090f0403051c0f0e011e0b1c0204022101031101020c09220501180501 60
    0xb007200c03200c0c1d1009402da00e405440303544d50303000003a110040c00e1050343e00c12980d080c008001c0303400da16140001120300d4008a000711400a50051101424007a010f61900141c000d0040d141c18941c181542c0c1d00010040410442c1103101d15010241e14130341c2d120f440032815604003459003001c0c1701804444180302e100c5500107004006c0c55200d540500da0b50b02d5400300000303a081c680c0d50054100c1d131408841c180f016040307000080020030040c00728020042d6501c02e407206041d030750f030703440c0c0c10800601e08542c05004594100550004c07a00040c00a8010041c010000622241c1c01c1a00c441102c00c4a420b00301d00c1e80d99100c01c0c011aa5000303120540d800c1d0503003000e02c20a4581008a1100c40d04800d107c95010000300c450b00c1196642d405444a000d181c4000060f200c0c000c9030703944503001c001c1c0301c19505503145060b426055480400c811903203000240c000d12103170329000440e00c8200712350400c001001c0c80648007200054820702815036070200c000020001c0b45100d0800d242111001030084405a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 612644928 1250 612643678 612643697
    0x915091f0303112b050a110106181a09011e0e010f3206130b120412030b03030304150b12160e190915142707050f130e060a0c 55
    0x2d40c8060700c42c2155203200e2802e6500c40d8601c01040d2415421f01c2c0c1608019420040003060b009141240400f00420f05c3c0c40034132200500614000314091981e007140c1c0c000c90100c005000d420b11020640108480a0355107110036580e8121209140c0004e07005805004005941041021502c040241029950000401c44070252030b5002c5171022000084a00a20300412000d860301c4081c1d01840c010402a040940c0d959080b94086100000c100c40440d00390301128840011244a442030040b1350348003400441c610388503911181c4024101c2902c68012a4803031100c4a45912400f4174a83d001d40520010001c8102d18030100040c540c1a400070140252107400f001425890b4200c400816900d807400082c00389921709100c0508030342c1c0c00060180d43d051802d40503140c602449580d2055610340c840e4450b41d80c2c0c0841c08131034009500b49500399903201110a003e0b5140c246510300007103000074480c0d444881401e98480a6800d03505010a05030050f00810906150394029421344054030310f04003560 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 612646178 1250 612644928 612644983
    0x5191a012006011413060f030204060f0e0103030e060f071209090e10050907150512060d0206121515030604060807030b07080705070609080901020c0915091f030311 72
    0x1c5080510480078480414901590640c65042c45885c03071800f030381d03000d1003101d407501640d0401264900c0300703d02541c50300800042c000d0145903000e041e10070943c84420035034270b9500c040750300b80820800300d40c0c8503108002e03801508038020010701e01144654801c03410703082c4d0707094050516042070f0b10503805182400001d07109218049902140401d40041c00140b0361142001c0925084407038110030310040b0002c000070700c3e294010004c1c019030351030b41c4214441d1b9959001802042c516003500250010000d20032840341c0840c0380030b0581e01c124036000100000315040005098001e0a8009640020000048c4030841c1024040d400c041d04090b802414054074682d80c005018800138099420403140c000440c4405224074200da01d0150005024007540c80142001400d81d40406000c1d13000d0702c1414001c0c0c1c144c0c02c0008100d4800c2440503450500704139203a00f4040b4500004090b050002d6410b14501386220b8000016001386004c0e076261100038106d4900a0b10f07121120340340140c00b040781c0005201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 612647428 1250 612646178 612646183
    0x5040b041e08070f0e130501051e0c09010c11280302040b1f1b21030c0311182202070209070201020909070c05030c1e16030206040905191a0120 63
    0x101c17051440380c5005980c6c1c3e00c0a00e144058564002030555080c4424000e100f0b0030410044075030303508200c0c203502a0302d030840c00024a2140a12050104151110301c00101e16402001c4064000103800d01111507149034062601c05660444401d010f998928140309504251098004e010015600500e42814921017030000502c0998908100400e980d0034050ba090191304060000798064044000c000003030528030440301d0b10b81c1202d40042c3c588091071404030b2003030083c5442580040400c6141001c00c4a170303c1400c0e00c400b2007041d0003a035800c03902c502c840319801061003601c1805000585500c03052040044a000c080c1085046a0050100903000d680e406001c03500b20a1320f04200e1070300003081c513000742180140c0120380181d0040702019844204407400008603000303002d00f902d1a1591200700003900c40c05500019400180500c01400854803542c4441d0300940f50900c01d445144100344003105550103004217500354800c0e14048102e9582014201103145005020300d084600d0030000c040c1d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 612648678 1250 612647428 612647459
    0x23070e03010203190504080d0e0d1b030c0803091e0c01030c02060c0d02030a0906050406050a180302060f09030403120f09050a08060402090606090406060206010815010e011505040b041e0807 83
    0x40300380d44e45d00082410040c3e02c0084403001400303035005203d14800d03510707031230745400032841c0203070114000d00c1d1240320000030b5107405c840c1c00354903032070b8100c0c2403000e03032580b220a030002402c84000d03200311000d40c04000c20382d40900401075001030081040d481414001000d54140c2c40d94401554815030030310403002d00303200a48140e5401040010f80701d80c0c621040704050182690090300392446c0000380b0003400741d9600704612070315171410180000200600444083c2e0006400940140c11070004903000c0c03407503c1032041d00144042c00300c904064580c0c0b43c200081c40c514903400b0104500c5008900f40a0f04402a000240001c48100301000e1510020720b85400c00100000c0c0300301a0880040d000b95200c100752105e840015004100f05915002c0180d91403200703001e0000d251007200f03c14040e0032007034811517040e00c680d045801480d910300021458001c00414119003848003d001c04596a0310752000740c0003c00c45030710241d003c01090400d8022142c5c0b02d03040150150005601800700d06400a00384 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 612649928 1250 612648678 612648721
    0x1060f18020301150c02030309090705030f0702030c0c0402161e050607020606280f1e05030615010c08040b070b0105043c0b040507080f0907050307150323070e03010203 74
    0xc020400c901c6c40082d003144100c08034547e0041000741482481940b0101031840303410f0410300740c806a1a031403010b07a41c0e40110100743c4000e82c883c464002050030030b60084c0c89801031080d500800c1c1411a501c001c520b4207910741c5480d02140800b420801e0190810072507803c00c4035800a4929400c0000c0841c04012080010740d03241560348910169030851030845800a11071401400d4545e6101c60134810744240082c8902441e00641d18045060700c1c02250850003001c42c5520040008040c2e401507400c00f25440d4141c0d01c100f401d010008900107050700030041300c1d203d001510419810141040100c44070314001f00010220f91000e12000180115100402858482220100f0f003036696071601412a8024846d0000d0920062160075034000d001540998100c1c03c29443c166540d090b5541d96200c14400c0562550181004202010038040410400082c4d4500814401141c05a500a015480842e07660b4003100604001102c3d50010701040090000c40007980380d41401002c8038101d00004441 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 612651178 1250 612649928 612649937
    0x2060a0c020c03010f02091503060d0f03090e090c09090d090306051005060c0105010303020c0d080d020703111507020c04060b09101b0602070c0e070c140f01060f1802030115 76
    0x8102a8000c11002c0005038004000b400426014140ca0002c2e41110a0f8070780101800921501d201c142c43d01600d21a04000c2e0424401c0e448545510b03090302022807060b001d115000754003107030f00c0020407076441c80380340b10304028808040e400302405168440102900303c9a004032003440c100d01d900000c860201d9401200101c0c040e144c03040482502e00a40d40403503800301000507041c414182c1908403d04030b9009800f91411111000c05001701203405040c001d03c080020082d12210014941c080c1038114020b1605d410f0000c84d01d144203240600f0180c1c88021004d00c3c80401c000d05904118458039014151001d002032841c100d0b03404218018000002d20850102c2c9200780700034424161003003543d003501c54084041005003070410003944503040940702245291408640281c188003800d000c0d04540c0c1c3c94500707402e10380d19050040499400c00242a00408070b914074400c00c240140c0000e083c03900e020007101c51500c1c404920a400d40702c00140391038014001006854103c400c4002c0740d6005042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 612652428 1250 612651178 612651191
    0xd05030f060111010e2e150603180602180301050105100f080402062a0105220609020f060c0d12090b0105060f04030816030210050115140403050613020a0f0602060a 72
    0x403614003400700d4098040a0b0b103d1b820750100c040c1c4540380705286c40340c0b2060a0804540c000c0350700d0701c10750746644100046078405007130400c1000d200c0e51000420b0100c0d52080021814980c0d03551003030b41e020108401e200001020841c407546020b115050062204488080084410b000042c04c04e0340d08055441c1407000c1c40c40080c096440d61000c407221085050605400300701400041d66001c000740b504817510750700c0c1c2000100441f40d12902441d4800400c03101d510090071568800b0302520042a00701c1e08001082d400382100e4071010054400c0c001c0314000f07051b0102c4400d00061000d43ca43e40c05010003418000b154022503d02e100541c19200140e6119a03103000703100a03500c151085900007080e01000080d6009101c00c10442c100e40b051081c0d00baa04010925165401640d00c203015208d900c91f07211647c906000d000d001c1c41000300d407203040c205040035500c0e11858100784044684440368900342c030548003149000355000006d02072018181c03c40c0b5007051030003540c404005110b58503140e5900c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 612653678 1250 612652428 612652457
    0xf0403120213030506101a13030605060102100c030506040b0a1406210103232d01060f0e04141209010f030b0904030e040e03180609120601090504050d05030f0601 71
    0x400c800c0256421200f122141c1c106018100404d010321711414510b54220000074007103003101f5007202e5000c040340b8800b43c0218216214940240000342401d0305503c0b0701c018820f100c9805001d0103a413901030391130020f214901041404144c4060760001b601c54149030030103208200038071040300045001941c1054036a203603001254112880d00d03c641c8000500c07040000700b00b1541041d001c0c1c100041086240c1640015403220381e0740c030303543c2480e032100c0000c26010400448095070540031040950001242c0b0a0b56188850350480103500821504140c800401090040c191809440c506098009201d45030040400b0f403131034014260000c1c10000310014071032005201c1d030007401c403004000f4030084d050706042c500034091140c801c02160042d800d0a114159a08000c0709480b140b018000700f08180c450a02d0170400107600902030190b000921000300c01d1044403c01095018041c3c501c00001c0031f08007410601e01e001400c5c0c1914040000400400a00f030b520529a076402a03000e081c640e900c0302030b22 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 612654928 1250 612653678 612653707
    0x7030803060103180804050307060e03191e05010b04060b04050604060c0c09050703050405060f100b0310090606021b04050610030510420203030f09010b03060118050f04031202 77
    0x36000415243c130000c410700c0074060400010011a04100d041b50032060703036064191000c03c5490002035054102c002c0c24590200780c02900c4034440d00c224000a00e14404170544803840d0111744d002d545980d55041c138161030341842d200710b0303019248180280d41024500070015105210701e005500800c500f68546204100d00c801c2600042e2244900c02d009030f1074168802001010121740540d1144a441c0125840c032001c00d01003030082c059041c030300c0d52041c00c2030007050361680090030844c00c03d140080c0004950085104040260400b58082c0851030300160611119174103443c0310314031840c41d103801c0c02a40c1d0b96214089600385034508001c1240c0c0d40307a1081d9401200c8940c040c50041e880c10900e02c440852035800d4964500c0c40303e082d841c6a803580d00b4000c41c0442d100500c0f90240c4d10400c040781001041d200c0955000c080714001148400301d02010030f043c4407083c0d10100003034100e68080c0344904164051141e010b0340f011800902c81c40c0c1034400402644030700524404595000889030f2480c48807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 612656178 1250 612654928 612654941
    0xa120320030a030e1e06010504091407060e03060f070806040506060c0106060302040f0f080a06271113020c0d1b021905030f0d0f0f21060807050f0307030803060103 72
    0x40c03029251500141c1e40054081e01e40340300d074400c06001e5448200400040c003108040590310410003860183c0c01c00302444014050010140c03412807500c5213040e11910108541000b81c1a15501c0300014640041403506d418000f400b4a100786840104000d100b80e0720005151340110308a4000c02c1c03548460303001c5200f52080e820130410799424510085020764041c0c0080c0201c501403035840076160f584550079256003000c0d02921045410151030301020640c0c03604002d80c00380381540b400c1c40c445122001005030304e10780c031400c8032069092001c009040c980044d0031480c003a03001038150b1508401102c07650300c8452040000c000e202d00140a418488100507a0ba82156030141049091000201c045203402049202d60b903c2271052040085401e0030204904403036407084e8072104c3c034402c24103000b80e82c01842c406071241000314081003461080031300601214050141c1000090700c5040c810081d007400f0160b007155015000d2140d004c83da50302c000070510203d0b80c01c2002d031501e94440c1c0c40101d01070f041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 612657428 1250 612656178 612656237
    0x7120507020415061b020f0f040b060406020d120204271d0703140705030a0b0a021204110f042c031603090609120206070809010c05010f020403110a1203 67
    0x3d4004640ca02003401c101c1d24042e14000e07140e4810f41400303e842d244000240c030100075000140034003042917074104400c3d8a050719a00600104440c520b05001c10501d41096100d030300180d011140d0241c1c2c080c0c000101490642c1d034104194985810304030300d075441c001c6c514598100300454030504001101160b0042f4050442c0719002944010141c0445503901e646020070384043c01703903108032411100006401c0e4220303200a8060448130b151915409034990008055084a0350200b01c40429421503c08451041c1e104410302280c40011380b040c0f005944403861214091490450750007054060000f440c4403800b0b404086072650400e00700712070304500410074244c40c0c1110780b0351114109034000e811507050f5040d645d154520b241e5240071600c41a0082034021b500032500304601001300301d4901c014603041c030040c1005491000c40703a40e00c90031254080aa01c40c906c0d4040707828030800444000306011000b045440016042c1841e442c0002c81c03500080040a0040e624140f21151642101c400385505 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 612658678 1250 612657428 612657431
    0xf0e0a1815080c030708012a030f05040303090618020f04020a0c1b08160e04021c1718012105041406010602010617031905030907170708061308071205070204 69
    0x20380d00c1e00e07860b076242e0f40c48448034420302075000c022450320814412100c4001c2056106d03e240088010803d42d0344910303841070700070503403140c40401d080b80c044c0c000c00d8001c2e44695400124441c160030300d1401c94451503610400150507a9010300540e403400c104440e030210844005075240303030101c01502e610307181e020010312202c110a07100c01c03946548080b000c1181c02c80002d0f0380140c89185011102901d0900400c0000341140010a01508004c20030a2140000903055031000405841d09042007289410901c68040d0000360000c0710b072076402c100d281140081c204040551841e080c212030400900b6801c50070640c1c0c40c4001814000b56481c3c40000450080903550035503122140280a0711550007204010b40e07034200d103d409503a0006c100c494400d51020b0781c80031500c10690840b0942d0016152441e1445030f1f040100d03252a4182800040084210090102c14540302000c1c0c1000f20080200071388201058004001c03504003001ca41607140d002e1801c01c262850f155050380d03d8000c3d01400f94005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 612659928 1250 612658678 612658721
    0x90b0a0317040311015c07050607050714030109080301060c061a090a05090c04060611011407051e04120503071109060a03080f090612070f0e0a18 64
    0x300c10001d02c182d83c0940c0108080341c102d4001503400c004500c081060310600070850f10860b104419140700780c40f4031114000c03c020105032070211500c0210144600b190101c1501140c07519040100d08014001590403604040050321210744036103051103801d9140719422905200c66800790b0000c0031072944441265100e507104c1d000140003400d180021544031380707060b59002c20000444451031482070014094181c130b640750350201f0060700000d44080c1d401d1240c070030020500d50755406518040d096694400c42d02491006d45c0c80d013591200c205080090100d8002c1c488401c0d8880e0440b880441d00203c1d905c150910f121080e07130030f48100d50005896a00d4a031900c1c0401101000034040d00780100078070b0b00d013581c0802c03c103d45034000f40c4106500c03014428040001a03910005400c0d1002104001814154550003145640d40050481500321104004001190703400111206100c41c00e8075041e080b18403520042281104907008030003542c0c80c0380300308881080b81a08103a20151b04080c843d10f01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 612661178 1250 612659928 612659963
    0x9010f0e03030106090e15010e0a051c0c0e070203070201050c0307060c080420010203090d050a0b160219020a06080901021605070807050102011b030b0a0b18011409010207090b0a03 79
    0x200d0b0000c1c001c103400903242c0354000030350300307000c404181c0500781c40051054000c0c8400010b5520b91482e80c10380303070090490200012265500c201d59031084102070707600e410390441752408000504d00c0e501700002c400003900c01c1c0049603600000355600c4590a09190303a84003029406c440c5140501c0700010881401c1c4903400401552246020340940d11911176000f1221520b0b0724105c0c49a0b44200c0180164000c3c800b00c0c00c03d10340340b1001151107010f1000d60b00c0b40c0e07400307855500c4079800c1252190801d142c0341c048020021b81c100650074046903819103680a00d0581d90000340700e11450321420041040c00d0000c641048001c2d4129541e40c40c40f282000c0b41c00c001460850f413075a82c680301b04c07203145c01035960000d050750041c001c260f00012400c010740d0400e03040b01c5040c3c00925407000c1da142c112138844404105410410f00400b802600f4028a0081000510004180024528100303038103100910031a8201c0c0d0300002c8600a80310340314404210100400701080c2e80820640c00542960a101c405914 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 612662428 1250 612661178 612661183
    0x191815031a010c020f0103050c04030b090f0601050d0c03020103022a0c091302011b0807080307271203121b0c02030d0e06030a020a03020d050a0c1707050d0509010f0e 73
    0x1403008004140407900001900d400d10f0801d00a50000d00060164a0350761180d030101da40304c3d0910304000e040075102c0e102d101e040d080440d0058400e62284000000120040001d94010902220b021001c220151b8980c44d0707201e41803200905054012030004450341c19034443c8080c42e000e440c1045400c901841c4c01c41c0c0d66150b00d103115030184d039801c4003107490740d410300f0400e40000340c0685407548500d10034206410940074201051324008001d1140e00b0004220f1001103016200640d521030a4250707895002c5031802d00c3d10350341c25800c070101000b000541c0000c17101705d10054050600c0a45000061086000392000040303405c10058003101134500c0d1500003d504540600039011540d034841d05402c181e503d698103403071080d40101d040c80084c4050b92690001e006440c0c051601500301446003101c1000d0b90400c3c1e8844901ca501c0d00d0169407581c1c0c0c0f1481d80501d445015400003801d0502805c0030300305100340031101998540300d2002400071a42500f040041c0d004c824030801203105481d00464 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 612663678 1250 612662428 612662441
    0x60312080604050c0a1b05150c19020106052d06040902071403070c030215090d08040e330f0a0801140901020c0c0d03110f0c031219181503 61
    0x30b124a10384408541c0400b0b0074016a4810007668460201a0700d10803040303800003462002c100c902d44100361000640940e2000254010341680882e03070348402c1032409840016650315100760840e0f00d4400100000d903034007112044260307140181840e0380380362182e00040c1581e240000d250080e000180001d01c15065600401c0030600615100c0b100340c00c0001e18036181d108041016200100c418428000751130042000070048107807802c0146401c0311000840c410aa12240503103110300041070400000c120442c0059119800001e440c2241e80508081b00581c10014031511f00d8407444140d032400c0da22244c2d01540400d1000341030b0f404203a44c54000790f0203044c14070100245100c0e03020101e41800014000d4980d41560040a402d8051985d028062046144d4000f0343c100b02d0340041c05d0141e61070902002c010840c891000d0480e4415483c00d0615289084082c03102503003040050714186a13240d41280c0da0060107142007401c1815079500e44006410302c2c0c1021001d800503c1d505621700390950702c0391 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 612664928 1250 612663678 612663691
    0x708030a18081312080405010305180601080c01031a01200f0102030907140102030a0c03031802040e06040507050105090913060b1807090b03161103041205031803010b2206031208 78
    0x11100b0b0f6403640340141c4040e1907448000c00203201484180300c1c0d5030180e04140d5000c1c210142040c4040030f4115442d00e0403c0aa11419058110030014070665a0501071400ba0049d110480f00708a02103000003031044484082002e9089511200c4501c0443c05100c50303500c0f0134940c8020b6449042005079280c880c0c4141c40340450701c0b4418a01e004040d40003000ba11503200e401e44412030240b041d510f080d0050001354011041c10381c071011a4a0046e41c0d603224800340729008400501151510f4a45249082c00ea82c1104d030500106001ba00302030b81e03038065003551000701c181e80001a1002c52500301302915441c4038641d4040b1a00409401d4070b49407480b0940310f60400d41e600c1d100560307952f07400100d0784019500b1031031070006c1d401134503070715405080308140c6034602800720380c585a41c840f040051001a280126900e8000180001045003002010060441c003200204003800f403880000d600f500c104041902501d540c0c186004140205a0184c00116041803030030704941020354004110701401c854a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 612666178 1250 612664928 612664957
    0x601030c1b060b120a0519020a0b0c0f070504020c03070323040308130e070503010905071106011d1b1606091205030609090601380d0207120305040302030708030a1808 73
    0x31610010004810380143d4202d009040301c9904a600001c1c001e0410387c051740c0105603000700217039500020000f8904030304420302400041501c410490f0502c8155485288030301d006210b4a11407160100403948801d03414106003030041602075014203201004040030242400c0481c000062180030001000740a0141e010701001544455024110000940c0c50400090701800103121101140c1e10464201c9503a08041c0c1c50b04184c200030354034040d001d0f080f90281400c101c4d0380325400041e076103180f90011030010581c00035003e810450303c040d000d4100140030340003002c8914003e010301c81e4014820141c2081006144645802d805407480e4015900c1a024840b00e400040341070101184a038162079a10320100300601e50890301e001001000f03a00100704a0745040c62040d03481d600d000a000710a4440d001685a840318240000382e000442903640a141c103150411000a901104888403103500c000001c1e01c0352510003d04000b040100d00101500809550703004c03d0009000c0600701d444807a001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 612667428 1250 612666178 612666199
    0x10f0e040c0e011205010f030b0402011e0221070b1b0408150105100540030c080f070e01351e0102041406030a090215030703050106050a080601030c1b060b 68
    0x4d10340c1260001d1080c0700144c0c0c031080c4207000090030740c0b460640082c0145418588184960600b080300c5a00b190094056801400400309101100148000e444603030001142410f040f902c46141345d481c0105030090641e0411091151461120b094401801503401105e514844c1c1d45100040b41c602030161034802c5a2004a074400b42e4414070072907000340340d0700c0c101e0036070412104002191141c1d0050f060315242102e858810801101c110311100039030082c408441100c4c81c110019041c1008038803000382c0c0d60008076042c072044001d42802030441d130402c41c2c2d04403440d4061210210000314241c41408801002320744001061000608221601281074448500b4003070b241c101d4202c0c400c0344100d210780000300309088034900d0100e025542c000415480421b000c01c260f4006113003400b21501928a100e804803d118660381d15100d15405455941003030307407412400030405003c001c401450300b0304154641c1d0f07502c4441071044154174507015007031101202400c11441c04101070040742c0c4006009444032013 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 612668678 1250 612667428 612667457
    0xa020f120301050f0d03030f0908040906060203030f18031314030132060d0503030f0106080a02040501080103080a0c05011803020f010c08010519121101030b0a03050c010f0e040c0e01 80
    0x4044034100c5070024103001c5104c03100f1060198049080c4010303424559105048150528140202d03035801d4850001c255031a0f0034200340c4d2084641c0764014004541c003d00804c00d8608500c208560052400d02c006101c0809c0c07004910f1440c4907640c2c54111002c183d400014143c00e03400d5040380140802c030024002e00c0c0b00005400310040114004110406370f2400c0e8002e8405000a8190010409000b0181c0c0c1d42e40c603240d807469944141d03401c0c042003140c0401008501e5020120503089002c0b5442540303020701e4000002c14864041c003000c2c2220340d000803c003c09500400c070100c5c80741d5008000340004062140d01441c1030381d54510650260003815081b0303040404c10f1107101540d89458440c051183d0a003024049501c500344117400e038a104411011070140703104100760540e107100d142c101910060000c0010b00b915481c0b00f00900684c1220418000501e010458952100080c68409840c01e6080402c0390755090b00c41d00260414903180d8003110555121100c2d40c1e0310042130b01ca0000540300d15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 612669928 1250 612668678 612668713
    0x302041410020303010620190312090803060105030c091008090c040e07060806060408010510050a050306070c0201030c180f03350708041e0e010b0f0f0313080a020f 72
    0x318258401a0020001400fa0071f0103188070102200c108903401139050085e00303100d80352040412004541c800c000958204041c0d2225008060446d003903405d0168000c80d50340e0740400d0002401c00b40c1440380210000307020801075020f44081e00002040b084a0004c22078000c0c24a4070309031103102c41405080c0381d00f216807c1034042c00010034000340c01401d04a1428508451a0300080d060b1030740542c08110020340341c1c009004060044400070008900e40f0b02c1c0504000c00300031030340d014500030b41010041003401604107540319403107030302803c010401105c121403c13200c081054410b0541c0c4044194007003811080c000d03030b10003520702c1508194070046201141c1450002c1c40745040e1b0444401c02c529501003401c51001e401740c580f080040300d007041d45540c2081c03c6050540c0302c08429800c038900c10028102c00c1c40240b03004224541100d448c12000b001610b00a118816070b100ca03882000011404807402914401d044940080000340c480740c9070b15000b511000e2894402c2c100d84200b42c404001e24200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 612671178 1250 612669928 612669949
    0x50f2101080a0819051308030901200a0b060f06070c0905071e0e06210403031a031209030705362203020c04060f0602071d01032003030a03020414 64
    0x3c800340c24285244106201d28000010000d0020004184009040c07400c03903403880c43c040d05242c805036803603c24520004001018070840c01000e540b52045c500c02d1302e072020440440302900010305480f070b0303540e403808501c4920701d81c250180c20100c00a209006d026a04072210203a8003040e40034040340c0c81d0792600700c6489010800c4c040d142c0c1e0342c282c0100b0806001d03160150004c00090041400c1c0b48610444146c00e091081265044000840801081640c1841000c10300280039640e181d944944801180d542c802e01c0b0205140401e0001d82d504142e81c0400c46030008080050040422900000d041c008010080c10b0381a8025a51000051071400a14065116a50b148c1b8180c0354a82581450b48a80c1c842d49420740c15400b03407060782d02a81e10750f0b00425000d41025500705150a103440b40003403505040394400d00800fa00c0c1e90f00c01d00d00341d00b445e00ca40c1c11280c00c5480c3c20861030010039600303403403110940700030380c54480060700342142501500a00211005902c2c030540c801030341401e11488c3d908 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 612672428 1250 612671178 612671183
    0x10e040503090909010906020307031a0a08060a0b0f030a290105060307080712060e180102030f0a0230061e090a0c020106081014070219060b01050f2101080a 69
    0x1030000035030b2802c0062a407644031803001d0010400d501181c41d50b600303da0040e20042d00194076000319600802002d40322034115101942c8802801d0b14084d45070751a004007524503c41c454554428400940d15610030080b0807030010143c5001141c0352510094840d00c0c610300301c030450403107480c1c40e65410ba41d540e468100d0f0303000791080c0c1c03441c0c0d22048111b41c80d61000300311340288584524596000b000382c0c450600608842c0d4041051820114140d0380c00315080301007290560300400800500c0300c1d00b0304150390801101c0c4000b5858440d80d68900040e403903500000807030b81c2c4070011a060300c1d0741c5042d2040d000c1d24040c0d4041010703007a0030052240a890203141c55802000110100e96640c40e82d90022568070100e100000e0503603141c55042e420120651415a1034546a01541004001110040c0e8000c444d9000804402255590b243d400c102c039400c0143c151540c86d050f180d110b901403800c0b134038590884403c035541c841d17030003a40041c03d50002d002c96940c41b0b54100040380c0600005a00ca54854 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 612673678 1250 612672428 612672433
    0x3f08060307030c0302060703050c0d090e2d091e030a0f0c0b041401060b0a03020316031b05030c040e07111b0607080309010b0d15110405060a050a030908040f0608010e0405 75
    0x4d04680a00c025507002c103000b101040401c010307030752038000103219420200c140350f0349500b4410700e031942c060b0a081001d17021510500070502d2220407800e40608904844044000f0607209a44258240e801d1644500c3c41071405100181ca9161103880880101080002034a8886081c003211004541a041d550300003803640756040042804291004007051422507440000303d411a15003030303010480c2e0071144140010a8000c07003802a40496540942600c0d6154a810018800302c95038100d09160490284000d002c07001010484080c0c8002c03c0b1000750080040203209401c1801c4002d18000c8000301007141400f440d040480d6440d42e02c02d00d41c01c2904000c0c9003a06004860f2a0000d080c1d20190243d1207566840c00160495284c0c1e00c03201c07611034041c0741c40400301c142400d00c00c01070340c03441800001103d10400080c80113543d50741c1a245400d1803072a06586a10001d00c081d402054030310000340080f0780104000810b2280c0c20900001e0714116a00c0c40c24a99030740c05a00d8000006940003449034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 612674928 1250 612673678 612673703
    0x325030920040b0301020a0e12010e070302010f0e0306330a090b0103140109090b090111070f030201090203060a1a0406050a14060d0911010e0603070c3f0806030703 72
    0x800c0403140e07001000c800148000751168080000900320382c02000710001154112001d100d003450310885c0c1d004e140800c1002030111944034880b0940b200f81134000281030000300113048404d58810420110200300103011210281854440c070120880301510740d42c013443c401c1206800002e1240b460403110400901040404c82c142070b018005003400026040c100740d80c031400d13100d0003481124807900a0410900029a0040030f04004052030310080185080c2d80c1440400803103411503000704c50340d054000c2c0c003030758001403103203030403400b40c0620b180207513061084005010381e1130069031051040195011000c46070f022003074240320540d40140b05555000102030403c115844038018102245100100954607040c1c1d00304d21001100c0813120240c5802c4951410099a56003100000815180845055040d880d100c01e000b02030b40202440100140c0413400f0020508048254450759421041159056032010852002844100040c54000141040c0210b2a14203001c941d110590350018680c1402 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 612676178 1250 612674928 612674963
    0xc14100f080604110d2711010806042c0c2418031204050f04020921030903030f0924030403050c030d090605041a221703250309 56
    0xa801004010a401507214101242d00c803580e40001e115201ca211400245800e044c00c480b10500e0518582031522059002c540020520000012101f2070382440c000505561b0040818044c001114204c451010114203040d44030140b9054240c0c2c01c0082000c4481200c000e6007007107210000003040342ea1101c001323140c0f214541910f6008000b0500c001320290348042007280802c1ca04000640541852003021505111034a03004481e18200a0700311070660402c88154000f552002107468411906007080c900b441c6030040900a031445800700400340d03526100310345001003255104242c00d51150210002c0c0b0040c0040c06400c1c00e0f02c8000d400c00c050f085503a0b070f640a40d401d07404090191501d01c42800700521110f070314000c05401d0f03841110041690b0910345010340038000100500341c1c248000408226929401513581000518078010f034468514250030300200d40380d0044508010a000002040b0200440d00301e003401c039550441c052521103061030380c11000c854003601c1c000c080303a0b20440103c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 612677428 1250 612676178 612676187
    0x71107050d020112200a0201141501030902030c060a181a0a050c0a0b0a0e060f04051b040618051b0a050703030b0102031c06080705030703110105071704030c14100f 72
    0x1503500c0c4d80c840054200115040440d55080300046a00c1c81c00c0000342210481750b0a000307000c8040d2414662010342e041c0700943c1c001880341c2810560406a4941e800c0c010365804001c0944142d00280c92560303200f8403000c0081a8420103418080205411000001e2005140d15090614440c1061403810b00740125411035490f402000810715500c0782082c40740c00314010b6200d003070003180c50700030014112070000c01c1d1034102000202641c002d4010f000800007c10404a5402507136148900340d40001010380c40020020103d82d0450b5107128080500c0421001aa43c002ca00a5006058810203005401001402d5102d01c000540c00144203000010029000703402000240f60140181e9041c0000204122520294210300724446600c07030004003c0d00c0002d000420103840d0541c05006032a045480e945904803400c00e2040c10860700085410600c80808810f4003d9503070a00310039941c88d9039041c528010f562500a41c441204d0040c0303903001e6843d04034080c81007558076444803201010ba280c015103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 612678678 1250 612677428 612677447
    0x7020f120a051915150510031e0e0c030718050705041707060e03070602030f1b0a0303090204060e130f05120406210c0909020c01020f0a08071107050d0201 68
    0x80c0e200e207404210006005200c10410380810f444004181205814100020b0a29200071408585040e03d02c19166640e0009001a54410f840305080c010520b2400c900038010b81000810112400f011a84403054139003086007200c44000032108440c0c4c0381010151509594452030076034442c00c0481c0380390b8403ea83c20141d0b00c1344880c20a9420300f80e4558003070039126002000041c2035003013100300b44841034000b01e514009200641c024051503040500181d80c0340f0400040400ca070b000862a0315014290707044008401c80e1110035031303000110901d000360140007003590403441241449404100315128810580c405c655164505483c80c41d00e840d6000d0200901c0320030b4895014050b00fa80c034544000780103200600300d65a03104c0043c0703850817840f8181c00c0c0000680c002241000d0407066020b907c0300d222015103107403281c01039999443e58034090083c821611868640e44010034080303c042d4224200c00d110342070a441e1410f000342a0f098107070b11218540580c6e0ba000b0000e44031800903500c15954103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 612679928 1250 612678678 612678709
    0x61308040f030f05070e070e1c050706020d090b090d08130b0f0d1803090e070c050604030504091a01120c03020d05040f120309050615060d060e07030c020307020f 71
    0x52420351503401c0440c001400d90416100d000b10101500100078007009140000c18090034007040b181415034000b050141080800f500c94514214189200c600c0c1c9030305080c0da59032290031511034560328003003e910b4401d10b500f414081007903103070005001d92586e0100d601700c0500603c3c5840e81d005a0341c0b03880d5141c00158000c10080241d02000c15420740b41c000501c3c1d801c9210212a03200c809051441c0306036400502072000b1903110b603025000003504a0b07581025900010813241159948240444000d54010342c05041c1e031290324140420700d40c100e8020400d0316100f940030301580e802594101c1c001003068200c1c50010b0302c1e010801c2c1e98507481c2e9000101165241c5800341c0741440f802101020386200751010307113064580f0f5a0400411400704249402c8850f5801e0600400595441d0142c84860040c07240082c503034020f04030010b030303540e400c102c505241c12100100101c036129540c0101c0000c040311020042490b00a4482c0310720700000c151410207a00400d40c2c3e401002503414000030305040c2610 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 612681178 1250 612679928 612679943
    0x30507060b1009050a0506042301020a0501090303092a0905071202040e070f0c0b0a110d0e010905120c03040902070602071e0312140f091e2d0613 64
    0x40e0185aa602c4114890110b940d070b40c100c42c4034180341c20040c03c00712a0740b16611582c410001040801b211094513001810b0780038540c510000101c2c0140c0c2444802c01c0b004109500c2c0443e00e904041e0154001e084a90081c05000d152003881c95024010084420380062100e01643e0104091410380d0800c1c0d50010f01440c0042c40308142c0241801a6003180e081034800e402c010b0200000305901807681ea44040d03030b5180224001c02a910355440c41039020344100c0c5030036281c2c074500c402001341c01c0c203c9160900c0d41740304010400240740024020080d4580c01c6419006140c1c41100c001c00c074000b601e0038298044040c0d440e16207040b0035600258031008007184c559130248240c40c0071400c19003070000c420f54440010340c0381e02041d280080440308510a0309110130300e464400e0702d4522505031050791203200b1200c0505140c80380760b0410301e840200d102c129010b100da107104624118003c1032040010030350000740d2130001032280502104034225428004545d2040c0c002600c0e0111240400426a016143c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 612682428 1250 612681178 612681191
    0x10b0a03211b0b2e03260d0c0914030705040e1c12060f0e06040504020d080a030209040b090f190e150103120e09011a0c010f0b01020f06040201020a03050706 69
    0x440381c004101c1041c0540d00d00b03d041d41040f5014201a440c4200482c800388003403500807405500385100c40c468003014020f0b0b103217800018010b0491041140501a19060b12038954000800000180010850540001d5110200060310400380705a03201066001030152454508040c2400010085a14440d0031031140c3c003900034440c032014191b132a40a500c2e948090380c1c00341062403a402d07110fa030750015020b96107151042155154140aa980104048030045044e4840740001004490b08400c0a0314800300054600d4180c0d07010f034018098800c050380d05000d080ea14008004084c10f0858841c0c0c160101e0a0015032205007c404940012401d41c0b00051000c550807142c1e0315013034074100000c02075285103005200303000d50310701404e0f081c0d00146003820090700035001069000c0c0c41071041411085503440d41031100e029202c10b4650f0006c046c0000c0109030426100d13100940a1406054094000c4c0c4800e044440404100e0500c01d0340c068006040e13100b499034007100c450740724001c2641c16560354038 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 612683678 1250 612682428 612682457
    0x1505041a120f010501090311041b050408160302130518061f090207030207141311070b0f1005130b100207030623010920070f05010b0a0321 61
    0x680e1800d221000d40060300e4944100c010648075001905120036001003034010449680d008800a00f926070080c826030180e102c020104018141c00c4241c3d4421015604180944684c0500500304903044807089542d90550710f5042c000480480c040690051a4503500000c2c3c454180c02c21038003c2800c010803901709441580041c100003060712500d0f10049140100f004840014201d44040e040481003145860240d80d0081d54402c0d50744101da292100c0505e02d0056a030350382011400982050600f44071241e0061b2000310140d01c040f100312054100c50010a028009114507144948450030140c01c10034284000c00c49070310f240b0206160001c1d00d0b0404000c041e00c8074104429903062070340082619500f140303091740581e55815000c1c490707a08150110101d07980c0e00d103859411034584210014001d19107401c0c40e14404080509491019070008012081001c8542207020780e0f8003c0008005c00b03c003401c1084076400042c8000307880f4208203181c1d4407a03030841906814034440141411948019980b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 612684928 1250 612683678 612683699
    0x7020c060d020d0b0906060a03051f090b090c09030d03050a0f0f0515100c03180f080d0905010815061b011805150402031e030f0304080403060c18150504 67
    0x1100520007082d00442c40b080c0c54640c5001e60400480102c0d030070491460040c000c10034a003e1121304500b01504d82c404505113558401c05449034141741c854050707000d0b4443d0b010a000c3c00007441640e00a0355402c002400c8115124259241008001c0150241850102007240070b080040c100110081d90784030008507025040c031860b5003501c40340a02003202e10341207036070720034050a2085950040840f401d6010499070300c035864419540d4581010800c0080350190064403101300d0b04821074021400001044060000803489030241e03a0340c5d102100c00d51941d004544030901540c540c0c0760005000920171040c604840944884403c01c0c03000030000704004101400d4400506640c015a09209405400d00c4000d11085c01412540100106681460340c0480e9881500c401050032000d214000d29141260520484611301104948151a420641407110141d44288412a915071074014884d007468041c081c600d0099a200340c2e0b03148550b00c0c0c0031091621f02c200c4c0b10000c040003010407010a100700300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 612686178 1250 612684928 612684937
    0x3110a0c150e030703140607030b2101020c07080a210207060c0201030f1103071107080304090e030c12040603050f100306021b011a0a08070e13231501050d0c0e07020c06 74
    0x308046441ba114845582c5d0421101900385e80c101401c0c100e0845103522307004c0b000b181c40601c4080d0740454001e44480540240508007444040e8010b548000620300000181c0c61480ba0042c0440180d2103811500b90b0103110203070395040302581100c4010003209020300440104a030041c18007040780a500400e2000b102c00c2481940070b110004002d11059039440003480100090000042c103645060080e419905d0045100f004079041e202c1034088103021040c000c1d07544007289a0304989260b2902014120542c00901a0707000003458080019232140319401c0440c000c0c1901c1c0d03038400a190441c0c50740d5000c5d521032045008072020000c20301105610904c580c00f0002d140c03403444040f038007801e0200b00292106600c0580c41c0d5004240038814854080b070300e01c2e0003029111400700b103500c0614107070040c440001040c0040c0074404030841c01c00300011400c0401000d100400301c41c1a80c0f00c4041000d1010701d500e000e4141100028140006111302540903040070302e9004031445003510b0000120785511 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 612687428 1250 612686178 612686183
    0x140d050f0a0507020f0604120915020106031a070804110102120c0622050303010902030a0b040c050d0e070602030715060f03081309140a05040309031e03110a0c150e030703 75
    0x40c65010052112002d104441e00460248090401c0e4401aa9070b10359580c40a48041c00c5440a811740b41c0d0700b5400b580110004220080207003441702010340c0068004c0a542c401650348441044583d00c81901100d4040e2042610740c842140c3c41d15241c07103400d16184845206815880b5280f0326804229284000e42540e0078004028006864514203001e5100e10707200040841b826108007090000c0c1004c429603044d584881001030f01d0341c5da070b0708074003014085000125401610f0318903200d0700c01d503001000300720807011540c040c45001d0300c201e003440c1d41d01002c1c171640c3c0050b00140100c00c0040d2000a8141c403005c2d110358041101f5880d044000104025540225440301c00090b1481c8200020300c8028020603419604000303c0b2940c010906d4002c00007440c0080c501c0e9504002002c16000301e0b038410145400128210004411030300307464050f071803101c05030041600c004404010801c0011808501680459090022840c4c07190101c05c6002c41c0e01c114003400a0810396480548040010100270350 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 612688678 1250 612687428 612687451
    0x20313080c0a081317011b050d020d06030b011d0402060a0e061306181707030210120903120b040b210a0503070308010603064112030a08070c030e01140d05 68
    0x203207130840e40b103170340c4180300021050760b418a914140701e14410706c07610748480400c0c10328030340e02d00305525050020703c1031160003011107161510100a118840441b64180c8a030080c401d01c0700005e8544806039034204680003544803008000b028080c510403000c8054024001e44181e040049451600130b1000141d088040010001c81851208002c3c0608200c0144002145041d00240300d810300ca4a031422400068041d140e89103e8400161280000304512540f88004000451003032034000d001140c0d2035980b034041c03806c100d034100d850b2405214004802c080103200e00d60f110702100002c500c0380100488400d40380540014440452018001402c100c1d1003503554050560400c1c1b805811207030f01e86c200d150900018100074171818400b003681c15901c55041041c1040184100031400c6146420120940040342e080352803860f82400000f420507101b03140c91b0021207030381d002411168125824800f80026481000103042540500d805c000d000b07a0a0041c5842c040e903841468061301e5003a074806488c0c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 612689928 1250 612688678 612688717
    0x60b040305030729070c1a13030f03020405030a26070605041a09030306150c030c0a11030d08040f0507050612060f120304060509030c03010903180603020313080c0a08 73
    0x41c0c51050228142d003088032000004c2c402121070b040b240c003c1801c020b00c4000702400040c000301c2e1140003404a480d800984040c5800010f07118a80c6002d4000c40200340f91641c000141802030080e1802c0c0e80002d00200700c0b102d42c503140c004906265441c0116051310010402a0b400304c114010f1200740e0007480701284a042915006851185454a400004407020309016103060084112a0082411241882d000410000040d5a0321076501440d41034440010381840c5040b01080d602d901c5400703540005e401c420703100f0925413103c40c650130100c001100b800003d40007a10758095450018011000c5503c4030b622480496501e510020040042c02118401c11180b89001d0900406410007a920303401d02089030003540380d0340c0c05240200010b21601017984000d51700d0402009840307603c010002d01c00d008880c01c02400102441d5044a141e000541000ca40d4501034002c4078080c810300020b0740c501d1001c0303855141058000076070400c031900030341014034045251b0b00060b00b01c0300841507001006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 612691178 1250 612689928 612689933
    0x60c06160e0303040e010627290f09011b0f06022706030711010b150319021903090206070f0b06032a10020f01061509120b010513060b0403050307 64
    0x3652152000314443e81c02004180b00400d5080c80703181c1120000c1c2040c0091483c0f41c000d1200544415107189902c0c0c0507031a0000e1078103010f0100b01a4401075500c480c1c0c064640c3c0d104070145200310340044401071000c02c2070802c1540700d0513400036540111070340b03003410319400e60324400800c810110980719190041040b40b00c0e46058101f060041c0e079070340d0000440c1040c100c0400e52501005140009200003004840388240080d040b11500c400b00800403007460185401c0468190426114030388c0d45880d49140000e402d1135442182c00310400010004181c0400785012005401c000000300d0308a034041c0000d4000682c400c00340365140d0300c2801c1241903890300c078081c10315010300800d01e40362541c032009498101c0e54102842d2807582c4000d9420401c00c0f82c600c503050349815100032030810203601e005030004510406070903005090410b036840b80c10040d0f48185640c0d4840e40323803201401081c5c080004208900d0001084400324403043c0380450410380d103042c1220315400c01c1c1d10640300c507080000d0740004c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 612692428 1250 612691178 612691187
    0x3040f060203090d0602160507031b05010f020c19080604060603060b0a1d04020a0e0408040e010510120f0b0d0302010e010b0a0f09180624050103110d0902060c0616 72
    0x682001d100a40c10150f403140010300400d0307002805070003e0360005004050380d4981d201400816040002c66620136a2441c050103810790028800380541c00080c80032503150320079800c07400c0c420003070350040280055840401c4992020f2402c100c10741d4000c040c001880d20310510255105500a0300001045865814a04107461500229500c41ca80400e401d01038000c1c150300c94520140d1840a4000658030303440407820381901d9030020001c2c0b09c04002044200000c503001802550001d810b08201c076640c50040c4558806d40251a00101c3c03e002034902e40300203207910005a9600200010980300d00030404180c030516038080981c010303515004120100c0e0340901408040c0001507071a001181c3c41e00401c14400c1c08213009184d03420791501005221410741c1c0d6441003049400c014100060740c01c2003000212170b520505c0000042c2c50f030880009046d802031033600000c400c41103031240b8200004651500a2815040c101d0303101c8001d1040803014901001414450354a48456081e0503000030300252 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 612693678 1250 612692428 612692459
    0x3200a0b1f090204050a210206040e2d070c030216060f030513111e150a12090302030327070e09060c040518070516050601140103060f0e06120303090304 67
    0x100c60b40c0c0100810040380e141c4c0b03090807041303d58641c00800198003c0002d03400d1483c1044019500850200d00800c00c011002e003424003034000c01403a1242e10850030507544012402616172551803201000146405002e801c4242e0041d1080c03065036144185180c1d00000f9801c20f80001d000100c0a400e00f000c46901482100c0d04000740000e03289a500300c69480300a50550900780500808120000300c2c2d4803502d1030418280010f00601d00300008032084090300c02c42c2c00c041213aa0005010006000c55011b1900c18900c0b0f40b900350f40a14074540c5d039011002d0805802c4a09080810f0b0a41c5515402d08400d11a0601801515158452904101c0100380c45c044001c3c100000440c000c000421181e0b0b516294a00b0f0500f40c1c44c4021002d69a88000b62031900900c541031030588026010b01c8104400803411034140c80140c0e03800042c8441c400e004600b1990a40940000c2e90107580c01402009010070109902160040c10002049580c00312903040d60000d0b1105441907101043c1071000000c07044241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 612694928 1250 612693678 612693689
    0x60307080613020d03090e0108150a0c0c0605060a0308030f06210d0305070318140d1b1709100801050f0105120a0b06090303070c0f09050403200a0b1f 66
    0x101014200b6000c0e036204641000c900034403034540100300304101400354601400802c5500240442582e6400819480709000c14940030341900200c001448911076100c0c000e0009107070b0381e460f50501020364440c00103241c0648040d6014410090002c00074a003100118480d0113a4dc00d134405c0c90a108051161a103141000d140701001100200d000b0540c00003851960306005180104080d10360030b200354002d0030074000c000c158150390620201441002100c00d1008010301e001c46800c140154021144c111300400c40000e551840b40291010907803c5a0f01040f0340400c00302c1610703000c060000070b0b4441d040d81240e000030a0500c0e00401c0a07142151182008220a00381140340098100700a90700490050900355000e03510503c601880e03c0b40c8085d82e06001c00682101d0703a5100508015a650203180310700c130900c010440b00810101d070140180b501031703039064550f05038110f0a54808107568034000c40c010082c0c400c001992000c00d42000926000360007441d4002d8840301403951400d01d50740c035a00075 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 612696178 1250 612694928 612694933
    0x19030c050f01140406200a0203180f06070809031504052103041104090f0210180f0501020d0f0509060414011b12050702150a0201021b010b060a0302070809120606030708 74
    0x4540d10f60240d1400c0035441a4400300c0018016460101c000d9036182c5140c94202002c2c0101e03054054540000040000f01081a1000600080c01d001c01400541c000d40303581d0440d00502032480000c440d100075100f2048020299801800340004c0921149021142601c59900101032208441c0c06150307030210005100d840c85286103400d8480b1003245800e280c605000700d50b04e61142050203100580700d12880e034010f00009840508141c002e002c8015007450600640c6120800203800f0035004151045980c10b8001e44400f109026090b05c18420005c004014400204100d08032a91071000038806031802c840d8050511010200052468080c5282c01c2c07910542120a00049080017103803c500d0601481c09031340d42c1c40301e8030104510040c1016a2100c0c1030012500c8031007250107401500680d403581e041c484201d044da160340d50a95000c5207204d40c100108002c6108030718841e400070b1a031540035592442c6010107107004941d0308101103840b400c1070f8010707005004052400780181401000344800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 612697428 1250 612696178 612696191
    0xb030606040e04050a120e030d02060108061501090b0d060311040203090606120c0307080a120203390f010c0e0d20010e1203030405070608010b090d02010219030c050f01 74
    0x1088252107a4007901d4018039409001408200c000c2000e4494142d0101c0541d440451400000d09014070f607140562103805004240401c00e440002d44e68100c80342d9400900054403044509580400300c000068100101c0c0c11001c6440b081507402002e886c80b582c031000130054503508003d80700034540d00c62544035078010014404113010002d0015008901256550302c146007a600007803504c0d04a81d403140c0c05004e071200010341c004000c03c6444046000e9001e0f0703005030440c00c00890b100d100b400080030802c4030b40c00e0340c51401c2504038034190b020903010808440200b103140c0020310b0048690000741050b034540201000c2154802400740c100002a10340a441374120341c0c40442508441c1814030b00c0307a8820200c401260b104118100c0080d6001c3d140c8000d0720800b27200603413603520880c1e05481030310918400280051041a02078100c0b03071414081780c103100340803003040840390b0095400c1e0f0462140c01048a042c2c0c0103e0624441030344651039021541040d45403d40c1416480d9003ca0700d0345c4d16015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 612698678 1250 612697428 612697441
    0x10305060c0a051c0609240603140a1e0603060c030b0102031608031f030506010e0603030a0c030e041b030c020705040603020d030c14030d050a14070915030605090c0a090b03 76
    0x401d507400d080200a06508244d6500001801014950300900840341480005110002c81030282ea0710503203010200d58503d9210a800c1c1d00f0707102030b41c045944940b100d200290414089a03c00410110030403090008294a034a41c0000c0e03030f00c0c40d041034960035a5403014090050b00352055480c84502070026600f0300c19030304550414020302100c040c2c8150f01c00000a00c0d01580b8a050282d0910300c1007120051f1501d82c14410b43d201024060301641031fa40001040a030302d000016140802d0301d603502c1c10a80c10a50742c0450b03000c0c0e5240c9100c0d4100e605c0c0c2007028001110b00280044540303c0d40d90000703643c515074000918049050340414040c6140103030602c05610703000c61f00c3c42001c0c2c00d03080000b081c0724240362070b802c1010400c04c3c0110600020452080001c0107810160280510060a014010b0004584508540107403a4000880e0b00480100070500c2617669621100d00c440c00c00051041d560320101d60500c0c022114410030360000100c09031415009102003000c0e14024540c24114034040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 612699928 1250 612698678 612698687
    0x20c0108010302210f0307030507120c1104020d0b042d140a05070513121401020c060a0b1212071719030906060b07060504050c06071509030c020303040e010305060c0a 73
    0x1103203800f24211840c131400c001d001c000410240c1e20180c1141d0352a600c0e824002e2058012100844004c102d140e000482180b04402500300c440d0404510342c995480c00c01000001c2d402070b0f445290054443c80c408101c0d640707500ca4500125803000d09201c00709822a854202500b028020960031854084450303559044207800035407140c0701c0b1100244940342e440054030300f402040480000c8140304100450340e000a201e48108051040d40080e43d0440240d081c81c0c02e0b4058900b11403440c0d80814001500c00089802c0080c0da40805414140400b0000e081c250800c00203102103404000000381c0202006000c07000d20040012401c00d850921079032140341c80c40c0d120820075000030161035a00030414404254811402003010560306540d82c503642c548040501401c440c2502c990043e408019410306080f01112a032a81c8900c959070441d0301d0010b002d00501806905608000c42034000c240140c504000074401341c9003c08110006600d54a0124500200101350101c10a818403954041d0340c0c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 612701178 1250 612699928 612699949
    0x533091f231005091503010606110303190b0a060203190201050106020a240507120b090c04170c09071106130f0b070201110d02090f03060606161a0f0106020c0108010302 74
    0x11401c40d4605030700c6503090890402c1c11030f004264010b03200b04c28000034860444480e4011034080d4006e0106c590b44050035a189010700c0c2018005030400c100113500345000e4500403011203006800001c0080101c0d01140d44d10515400c80c1d4050792000400112030300103c040e286030000e00c1c0c0300a128560505000035100c550341c1c000105442d401c008a94002c20400003030009121070450200300a1500500c0200300319507101100841d00c1c80c0c20300c0e4801c1803c05030200342c170400e83c3c80c1c101458680f902202c1020001c0d59040034409028104141000d966010f8940b8055001c03640c58403514901050510705241300070b800b00c62590240b40000c0002a1158444071940b81c0141c0d0001c05c6540700041640503001d80400b00340c2035400081c00d10a005002c0d03010385400a802c0d500400343c18401c00500d9619841610190f42c4541c0c00d00c03802c0c01420440c40c4195040c0d1007060005001652000c1c1d09034000c600b940c094055021203401845400d90412040c1000c0f0760900c0d1903041945140c01240407050b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 612702428 1250 612701178 612701231
    0xa141305011404050a05062808070e090103081b012301030b0f09060402060f070c080d02010c02070531090c0510031802190b0706050717040533091f 65
    0x31f003c00e00404400c599950b071021503a410f0145031266248a400601d500c4c000c46007080450942020343c270447c2000140181030321380c000310052401a001c60b03804400c03c0c2440311141c1940d20b44503031011641c0d2415081e050f4010611f02e0b41030f07a504510f0318541d003050041003460925003102c2005041d410014100d40c01c241c061740e003140d0f5003401107404191132040368030142c40395680c25000039003d4400a2110301c61304443d4001c000701c0a1a8004903103a442c07503c1020780c42001c04111038036044550034030801c141000c41001c00c3c4115010700700015101c014070300740c1d094074103c2c03420070641c14401c9030003004085c5440d0401554440e40a1464040310254010380503040010340c4214044040c910b1101174400c00300d01d1622004145043c0e000381c641199881c002546075a841101445540800c0340103e503c030300a40f109950300490108180a00801e40c000003001091003000036045a00482c000c0742c40c0000b6115413070300100c490484915160441145130b1030281c007a01c1010582d0125241c100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 612703678 1250 612702428 612702439
    0x705030921071401030209060a09090f0902031e0106030b1501090504050c070f0206162a120f0519032d05160c030210051306020c0105040b0a141305011404050a05 71
    0x440c3c20004900034018042d1094100394000b418020342c6800c13034500800c80d0303a00c074414094107420320700c0141a03030b4060360000d42503030046580301c0b85102000e01e20000c52064000004003a0381c2c4c3d441d0344010441c25039030001c03985101001d400807940d0054043b0041e00c42650144807131306007000c000c0620301c165070001c0d05000c2c0303142c050f00c2107540e000c04a0b14030320b00071501004018401d090000348000441d910f1035540031284520415000c1c2c48124004843c5c040c0302c09413803d0080d4942c01c040c0703481940103e42c20301900319000c1001801c8001425158043d558103a40c91080310940c01540c2c800119110800d003842600055843c1e101d000c07610a245070140920307400d545450003030303030032616070b0070080d840111055000010b0b907001c4054018102d1460742644040e0ba91402662071f84078040c61a070001d00d0400042c00142d456000130311480802c0c1c034103051440190915110f40f0740040440d00c41d10300d101c2d0380030070140da8440c40800f900b940107418907241c1464000050303811051449042c0c000d5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 612704928 1250 612703678 612703709
    0x9270702190b15190f0e01050d0302070e070c1b05040509060f070507110a061715031203070c050f01060f0501140a39061406130b0d08070503092107 65
    0x1902e43c0c508446141103283d0313007050090340325000d10300b10350034034010203a500b4420400090740b0302e841d1075101c2a0a400d500074112403400c02d5000c5660010003000c3c001031000074810440094216016804041503802004d40200c0c10700301003100361440649038031643d07407018041c46004104010415041402420225075508040c03403c548242184051140d000a0a0b400001c00e59000303242e1301c20341c0f0340c82c0d402c56400380e664800003c41600710182503601644913441c441404c0020324011500714295050500340c00003203503101440e240c481e0764220313110b94485004215040400c0b451501800090070000b01c0c04410809a940500404040c6000c00c008062560300039a00000d003044c200c00000810200c803c0d4140d120048561800b004079555460009500c0103001d07000d10326402001e00405a091028503982058090842d01d0180f981c0071074060b1114002403e20f00080103d10f2141c00074546071514030041141140e0400061421098440d45207006404041141c0c41500c208049a2104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 612706178 1250 612704928 612704971
    0xf01030203150f120f0102180604030c0303120b0301020705010e06010510050d0c030b060d141006081303050910080105091b03070305090c0a06021006050f130209270702190b 76
    0x1413842c100c01140050244005200001e801034005103d084940d840c0141134038000011b000543c880c80c400130300082c1e840031090001034440c2c80d00889481e14a100894200800c0c80020708a9021040403540d07a9961141c03500d41031001d20440307005040448217004003400714880035180340704215a00036844e41c0e4101b01d40c1d07510300990000180c2c400c098110b6484006542d05a0000d04200b00b030004e01860f500c00284074180b140b054501035600e642e0310601c003a218142c094a018404e90000c905010003032101d10b041e61500d22251400032400e03607c140007545410b0038040d0030076001e42020a4100140074070b065610030302084a81111451400003241d903128409181028540a0035503400001078000180d910780c0003c50f90f55900e0101400c00000d0f81d02c0c000c108600340001d42003500800c161065404180140d409420a0540a0304010144a11031100d000c500c07084800c8020b00d0119100b84540194104007134510440700d6903410501003842c0d204e00702d003488010b00f140400c5440750354200e003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 612707428 1250 612706178 612706189
    0xd020f03161e0e070915170c0d200714011e05041a1009020a0e09011212050903060f1f08060a0b0402072001091d060f01030203150f 58
    0x1120701c00d01c290300c00d5240c2c8905454504032014000e4116040c42c0b1180071422400c20a0103900400140d102c100a86203807010041c0303181400b03060340040c4600c80d280624054a1410380612440c85080c03980e03a20320080403540101e80b00c003051030341185101e003180f141c015041c00072940e03d40e800ca9000708955840c019500d01401c1c0c2038203204240000103808180b09466608454003236481660301d00262218941000c90700f5004480b020403812004ea002c00442c4a1940240050a103e1130001195000c5e24003041c0392034000c1c2c0c042c196071030200943c0da0034011a5540e0000504e16443c00520380010480020350782c100180000048a10701c0010404025444800751450030701c00403003001d00e594400032035881c3d01d0304544100426081c2000c940d0989810b100b00c9040b0750b44a40f03002803c0380b040800da40b010020182240c1130009038140496070103140084c006010b503665a40c9602171509106000702c020701280042c2c1414014414000c80e145009024203600070b040ea04251642c50020003c1c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 612708678 1250 612707428 612707443
    0x8040306050c1306081e07020604081e040330080103060b04061509150e030304031121010f0b0604080c0906012a020a060c0b2212020c040b030c0d020f03 67
    0x1403600c0e015140c001240e94001c3c1c001c0348221102411b03e50040c24003140418048011252040141c00110002d0000382c03409000d0038802c003205085540448400640c244e01c0c2e40282c000381d4aa03001c0700c0c6400351100300c40509000146c4201c8002040a1079070354003030700034603060100901890316004041c583d9248c1d944181d0042c138100c42081030401c81c20602402c2200c482c001c000c9980030580318060007078002d0400c20000c480140c01145406e20f5503c0b8030060510404400d54040c1481010700324001001c0c01c0d5140740090100009110580c440c1c00004580c0c10306240c0b80140c8040c0002c000401000c1403480111030b0030f68000d801079031420012164800c010f002110541000c56404224503d030002d20303042144299011085140c80740020f41300001489001020045040700080a1418040c695020380d1400a0200c1c2e40101da80e071002174178060464242d005a21411181c0751a10700760080b141d403540c068000e03020840d158404070b0180c3e80d503d04084d0040010300301b100030f280c40800441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 612709928 1250 612708678 612708697
    0x509040f091110091202010e030f0303040503130807050d031d1e0112050606040312120f020316140a032c06090d020327060d06090209120a08040306050c 67
    0xc01240e0361500e0b18500c000d03030204109003e4000507000720700803030283c0c51140c15100c10500340386402c1107990044510041240d40c9940500400e40280840350040028500643c0300d000078544030000460300f600304d42038a81c0440c00b60750280074200100e443d0905042c0c02d95800d4540050320301811441101d00c100012286074024081081c40c4008a1202d5072140005800341e075120781e600c1c086100841915410b544240d4880740c1000100002202e0402c100b01d02902e0b0706004401c034440c2c000c0303081101c402c41c442c0c024145d000010000411a9442c0c1c9000106503401d00102a28000b0403086003406011201702c185903a0300300f450482ca00e0110a03803560f40d40043c3c00c81c0b002c5800d401c560b849241c19114541c992080095107120310f07001100b981c682c005044500301c00c9900340003400b400b40c114400c0705904000100074051100e0601e00a040241480d030300d000d40d8078001c0d041440751140003641400c0e025000010707413000040c1010116030460360003210219554907089006803991082c0f4100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 612711178 1250 612709928 612709931
    0x60106090905180d022a0f040b0117040f06110307091e0803160c0e0405030a0e040f02070501090203070518010506030403110f010b0a090501050607150b030a050604022e0509040f 78
    0x2c2644265001030700000002034505500400d1014501b810041d016840000381e00141c07500583d0b1b0079040c264048114603a05143c07880e03c105214561a8491006650640e0141d94403038100c0f040c0b00c2c250003070903104000c240f005880c520380a400103280c0d172400d00864100c05101c0440c00300344520944140d024000110503290b86001e01620b41c003001c40302040413103030110501c2c400034012110180c0782d80b04a0b0408051761800205070011588003202420160384180d44007a2240300c0501d500c0a818040e1050000144010a500426207411010340c0320b54821000c0c0c11806060062000025044550a0f01c00513203a0f12103280a8030201d881c10300301c1032031744501c4218080d151015040070800300c1096651500540c0c482032030304241e503401d0060680111040103901d000504219825111f0b00f4592000a09003890000007401c20b11009829101a071003103041c0700540c42c1c8101d120400d41546141c8500c0000441d81e5890415024103040082c0100820301c500c994031a60410702c100c1c10540030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 612712428 1250 612711178 612711193
    0x15110c0106030b010503030403050d0503060a0e0c030601021b100315050d0503180409020a12150e07050405090d0e210d030203090f0705090c0711060f071406010609090518 75
    0x24218020401840240d422408580002610f420040103d50035680c03c40c000e4400b40d020303110181c801d544064401508080030400001e02c1000780841140a000100c1c0101da407410080002407a025800180540e51b5000c1000140e00340c0d500101002017000c2814080b9001713845140940c8280d61903408642c101a80a02e04002c204005c0000e0070303560031400c00204030516240a1208a48901c1d8009400c008010414031441c8051228100e0b40c601c50610f45061b03141c0765601c0e80c152a45800202e11a60009078240960720b000d010b00760740882003500808030b100000400620310903600001c4c4d8007800210b882900800001c01491003210051011140101340b29030000b00254800c48080307215008601286d14901c5005c2800000c90350010721201e101d80310503003600c54540c8451011210010384004440d41d5440310b202812896221200d55030700d0300e03494140034101c0f0030700c013495400c0c68000380014000d02c3d4220312620140d401a400004095450f5044040d414401896800c010b108500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 612713678 1250 612712428 612712447
    0x1107050d020109030801060807050a080a0b0a060e011209170f1306205803050603030a0c0803151804120504240504050a090f0c090b03041511 62
    0x4000c00f03a80c1d88255a04840341c0e03a60002107070a103030203940c00d80008004108014aa5102d182e90720741103510100b00140614000d00051145207203030b40001c0101e05450481c0c000c542c3c00504060780d90100080500030041e40d540e40707140c500c601c594014407c5502260050107a04120246c0300c0700c11036140078149440d15420b0281400e600c11002100242600354504034541001c1411801b04030416880400c0207040504c50380c4561103840050311124503a080310000301000c5008989040e8050180c1d51300301900314009096900040286020368401c100c0b102c2c00c280e1080443c0301d956008080a51a600c80d015000682800c1c010490740c805408203040601801c0070b003d40d40124070682c44c00d100c00c0300c4001c080c0e0312402907125a001c042500ea290701ea202c448240b02c01e02c100e14928106103415103900000390320602c50b4002811940d502d0b003082100c41054450300140c1400c80c01c1c481401481c0c040d40107140c1c03000800081900400740e0700644a80c500e900404181c224041a00d80c41e124400b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 612714928 1250 612713678 612713681
    0xa03061a070606061103030f0c1303081315020607081b0403080a11071436100501020721020414090a030e04050903040501080c040906090e0c04110d1107050d0201 71
    0x401c810b64819240140c006600ca0150b0388104000454201131401c580d00c040402300e07c4140244607030b00b00c100410402d0307075010485400c20041c6100b0090191900d071042180017281140f07030031070717441c00750070508100d45035400062041d0300150a103401d003850350304c4604103610346200c03000010040a0124021040110150180c4800328165455040c03555082c06981d90b1256144910100010b916852107070782d0800c6252801c0420419800604c40a12064185850305514000030402032400741070203419500151100001e060910003080d4082c103180040304856051021160007820200702c0740c0854403581c00c080d0b40c4001c3c0b040341c4c01a515201c40200e486022569044000409100780c654480c5802d100c0d990080c01031000550605040000541d03c4640c06442803a00003005d03c40081c0c2da0949001da2005808038000115811084000072840c15490301d41992007030303081414107048500a00280d034801e080b980d80119104900d607800307651510502d0005410303405201000290345805 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 612716178 1250 612714928 612714937
    0x1e072c0705040f09240b03070c05011d070515070809090702010e0d08070909060e0a0e100c020c101121040e1005030706050301080604031815080901060504021e0a03061a 74
    0x1c103040d000101c6040d8032036440500e81801b6a00403990f09202054a030b61140b0001c0d100c2c2c41c4030784000640940b02010f060506108010810380319440303440140b141e400c00030341404440c02c1e001d40c000e051030180d81c3c5620a42c000d2400c068060025580000c04091003508658442d0b9030301400c0d5014102e4828000300300b02401c595100c0407840091001585184600c02c001c00c031900c0c0d20f4006429250041040042c0425150b030144500c03d40c103800304900010701ca100903122840d0010030300355080c8014040071035869000e0f10144114942082103200000c152108240d00250036000070b40c2408a50103c40e014503000f04c450b2a000031704200c2d60301c0440f807540c0180c90b000c50031101c45035a00c800c01c40b0396202c04d01404015402000104001a0040c2d04114154620003d03030340403161920b03144000201055102d4000403c840140151850203118607005490161070039440c2c400c884048404914200307030303540310000d000210b61143c80c0c42a4401c0020708a40c04010b005800d140c5940d0249411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 612717428 1250 612716178 612716201
    0x40308190315050a090506040b0a060e0102010b010806010f08092e0f0203100e04150f0213050a06020d120209040204060f030b0d11060901020f1e072c0705040f09 71
    0x42c0c190280103020646600d201100e81c001c04a9808900b46141203001c3c1c4400f81203280c00507121f036410340303080c3d5508005a01030082da0f41c0d28a58078002000082c02e65111045d00340c1405260018800d899a0280395004001082d040c155880d407a2900d1542c60201d240380300304040c2c500c40d2542e0740312300e03c0d919561510103100c04050244003501d0024004a100c15141c00c106880002c20422061b90700d0b00d40107030b000f0b0085041c0e44440e201103010308140e452207010b082d00c056001900c1d20040a1080c4440050101500c800000504001e0301075503a401840254050111407002091507400940407a28003000150007991210769400003c1c252402d0714034500d001c0790800061030030b18141803071226206900708100003141c076175050078000c1031760140d41151b046004008a100039404104100f88000d95440d1f024503403040400140c6045c40103a8005107200805d14102c14002550881c100d50345070883c2038001c0d01c1c1d031125142a01d0b54403172940007005200c3c2c0c241d0005100031959004040c240b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 612718678 1250 612717428 612717431
    0x10903020709151e03060204030804230306060618040905061b0f0d180209270303040807140f0625080709060f050d0f20070c05010c080403081903 64
    0xa4461506800381c3d4010848580e4100030f61204002c0c0180014440b41001a04020101102d40b25143c120603640300b03802c1507039418030004080110070f501120052003842c0c0c20054084209400780003a4840c14007500340d9100f0000450303501c50700c2d09809103c00706104010001c010440b12450101d80701c00003140e40300220100c1d031081da445580340c441110000070181c0c0004d4a04104600c0043c0103045449000c6c0420000745403240041e2207900364140500c0c03015200b5440071404802e10306440e85e25400e128000e400070300500001031000016220555400345400ca5104240120301e4134140400f070198071701d84552018810402158584c0891521007046c4110140809540030b440068081c0c810034001043c034141041141e10070030003200019818a046484c002d4010440717003e9800f620690b414050b80c0d9400a00942c800e0302190040351408000d407400d011a0780c43d001c0d84210315214140c18003107000c40d07840402500c007080b0340145a1280c8031036228072810101444407071000010b4004607 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 612719928 1250 612718678 612718693
    0xc0905220219170a0210030903050301030206070f0f03120b01170f09070801020414240d0c170405060a051f092403050f0d030213061d090901090302 65
    0x19003500c26584090250001445145000740e007800510000400b10540d400440200410803a000c000c00703810b8541640020814004c10313004014070f40250154a00c01e040c98003222200013500041500e0440360101d841c940c58010500300403c1c0d15aa00d080240685201440c1c04105900001c2028003e083e01c00100040101c050041d02c000c40842c20019110072481d0006805040d4224110390000310101515003d07643c0b50403050170f98116070041c900707442071128902d840d03003010383c0c0c01e4a0140000c642d04012585d0001c2000c1a880361400340705a032511001032a1805005072540d41441d450500c8001941c40c09040180d120300703003610401c00040c108000314110341c0074801440b01050408c61050741c0e06181144c080300a01051907078021440b0700104a82900200e440040c0056005402424803985480700312030511030400445011302d4810701c4805403448401d120345c000e40701281028440140002d0403500040c0d1006d0007a603000c00301c1010009050419005109460720035001c40716a03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 612721178 1250 612719928 612719941
    0x15100321170609040b100f120b161b0816230a0203100b010c020315010303080f04030c020409020103140c0d110306031005180604030f0e1903080306011b0c0905 70
    0x4411007034070b486602516842c04540400d405241ca540c0021210001028190740c46080c103104650b0342d0b002c000c080403060b85003c1844000310745241c1c4000142c03015503d901030010007a04400041c10003c1100f0a100d0725041040301c950111502c200b90100c0301000d50b18980752118061840e000b05401c40d11000c494003107422000240d00021070343c001c02408800c1d000004840003820400031450400c48103070441c0c005038409010b608000306d00100b0300840b03036056060240101d80301602c0c420661540c0001c00c00843d0f8001c1a044a444c2c3c100ca0101b004041d6000407005044000007a0901c00c030b88209101c24011810300500c42203420700c4041c0000e814609101d41c540c08100c0300c0c0c3ea09600301c00c50502c01007240390b003c560b211420f84a1107606880024a10745031110480b8203c0100b007220502030400ca402c80500307203c0300d404482c030304d1091003649048400c07011a40b1000f807a0301130100c08a0780e1603004030003017000c00c1d000184800c00485181040008250584500013245107044046804e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 612722428 1250 612721178 612721217
    0x312160f02011406010518040f2a1209060609021812030f03061504150e04062103080a0f150f060c02030303040f060b09070f081815100321 61
    0x12205644000d90f002d80d244e0005507015408142c000c80e040022017490b0629940301d1190604950700d0100000d035120184881c2900d4600650340002800e1415600440d400c0d4840780420961110360008244260107161041c0500300d150088980140040303101c1e90003040d0450301f040c001108071100c640660060314110345030310841094282034041007000603003604003c1d007a400b2142e46020010700e003568503404c09000c00c0b2110001000919600d02c0780e00a8a06400341801400d00452540c81111002e17100d0701c1c440100792802030030300c0310b44030000d40b481807a036000c0024125003400c1030000c060302041100221400740500001d403007203104041100c41c032030840c032184250b01a00452450725503456084a6030f03881282100c03010303214984120640c451500140c00307007409843d1680b5141109402a0038084002e1440b265122540c4800318520300c00030308000140035038203082c1c1c119100e403a0b00211000301d0303802c0038200303401c058500344150103008100305440255a80e101131a172081c41e030100307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 612723678 1250 612722428 612722441
    0x10609020a090324020f0c010b04021206190e0109020703170403020307030507051204030b060f220b0a2c0a110304030e0d02151c05040203150601020312160f0201 71
    0x10020b0581a000d200003075100036030300d10220303211920a01410070740c251803003a6030145500b040e0920000c910b43e020181c0034001d403007044600f26005d60900f030b80d00030050700c0e0400c000c0116100d801082030908981d002e5141402c0940442c01c84c0107502d684a01c49200a90701c131180c100d0004000c030701c080180c02e41410700503000c2c0f9407541c003440c03030f00300c0b151000c4400d5008020103982a000341e00460328800b020b44000c0c40194130075030500c0003c0c6814810010b00c4403182c00705a01032600c1c0c41600e00000e41c201001d0142d0300401000099143d00c3c1e00c04105540440c0d0000c101240402005203007101c540c049019040c40d80031480c00711179540d10140d2040d1100000b0013200040180b02080009010b030041040e00b00d13000d0402c02410005400203902074001c0030b508581013600040c00c4d07030000400c00b2405010101d42d0000e2100d070030a540401d54501c3c0071042000a43c81c20350102e0324036032082c000c884200341503c07403509003400c000010320640606070100c00c000c202030103454840c0c0c0740180100c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 612724928 1250 612723678 612723697
    0x71a1501111e031c14010b031015110a1a0714070605070c120f02071a07020405070e091f1a09010e01090803070510060b03090a0809010513060e0301060902 68
    0x1010201c0502c0c10204040c003861240d0100b5000074030500c101c1c0c2401d002103100350150040045002450391084204180060b001004e02250030420007000002d030340102001c484118150100310035034041d084910f050741c038041c0320103030213606004400d001040307000d00107200040150b0401611502c43c152461114011400f81014084c02071502250303513944400c0c1d0000302401c228804210951381c01d1064524044904007047c5240304074400543e04104d08000f400e0340d204600d12158203600c0b40c60040c014160020b01c41c5440d1400034101c0707441102d140840c4c03200035007400d101e400c0c4030720b14542561440d649000241e0300d450700003c40c0c2e44038640c0300d1001d00480c03202e1444e0102c10740044603041c100202e800e05114201c01d000449850400c01420320768001c1c0b0160500004c3d02150400340c1c0c0741a4003090b0310f40e000f4428402405401300b030750034134158060219903130707400a04016100d43c05100d07103440b4a40c40131440066115001050310711102001c4008129098440010404a00500402d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 612726178 1250 612724928 612724933
    0x30718050f0106270321021c140c1908070b1f050913050d0509130c0806010f0e06030f0a050f1b0928031208060d0206070602071a150111 60
    0x503403000a10800a0503081c90014a201ca140391a6105c000d06d10443c2078032440d40d00d901100c4a0030380c5a040c0492010201c501c0f848007004009071000826620500d80c01074119040080c0507001c01408002d01c210480c03114042d070307010304900c0c282190150420700c0180d80102810380001c2c02005000301d50f4042c440e08160200c00d59050a0601c44010002400765036050141500880424801c11404005d00303a280c1c5d2b495600c145020900c091501048140101c090900c042d0300485500010b500d41d0201c800e181030301700601612011100b5541240c021134025000006024042a1003880d040c442e180f0410144050f8641c6400000312460486202c0c2080404811000278100e00300010b01405900a080c4d2030680c070710510007070808080307464984d40c0085049003001040458141008403c602d804c007500e4500d026404101090b81082c00244a0325000590000308920b03581556022900b20b800e003101c103182034994204030081034070f03140f01102080d061040158400d40b03900c00ca0392a0b9101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 612727428 1250 612726178 612726197
    0x6090e04082115040b061c020f13120309050d0f20090f01171204090b1305040c03030306080313051525030f0f2309030718050f0106 58
    0x48001058011070071031058009029490305501d0314803003407240076400d410f8011001d60080420001103c940f200d0a50050300107210080c140d00403984054100e180401c000b598031144540400118892140b54030141d00707070150027007440c01c00ca00d0800c1c000e911a4541c0820719488401f042080015810700402c49960000ea81c3c001850301080c0d00f001003007403480081d084481d031002070000380c812a4200751a050610041080801040c98070340040e4859000e40340142446000c0b04e40b9105a000e5041c4594881d03580510303940340c0741800440d1240b110401c20890030315243c45420502c0380c1c0300940000c0e0034090040f0b00341c44040119451180000d041c118142d01c0c2c0b506106488030600c0280160b600140b1002c0110313603110380322845d01500354541c100c41e2035072132602400d400302d10380184c0e0030050702e050764848040d0017010300c4071a829681854004210745064080715841242c444507058007a4950000e00009268544881802803075400d00081c2d84502070082c190a091041c140002c2d419807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 612728678 1250 612727428 612727433
    0x1b04020306100341060103051003060b0105190201020c160f03030e15040305030409111905030405070b130501120b060708070f211205071e1b050309010906090e04 71
    0x1c2c014103c10300304c0a040b039403d25204500508074200d2014149007404003400440c80a914900f503e58814800d00301000076080038052017214030131074000100a19941c412030022680070360113803070f83c40b001000c43e0103008100c2e10000707010b50170503000003009108134032003040110300d2440342c1005c2e03606125080181600c5c50310300700d82441c245061590420061070000c0d04807054880140003440c040d60040d50f5403840c03c00c909040714101340c0c0c00607107000e040c08091400d21b45000011107126491520340d03140e8179142080307401c02d607143d030180071140d03000603180d2502042030341b400b001c880c0240c07140d00c29540711081000070f507150141c400c0d0b4890070030021000010800005004e8140c01600072628030022039580102c0c401101811b1111468031000403448590b01c0281c08640703640c040418402c034140380d0b80c05030039548417034100502003000032968203e1501c6108207415103a1912081701a40303107507040c03940d100e61002c4122800102a1a00811420b010341d84d0802280d00000c140003d030f41c2c031134 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 612729928 1250 612728678 612728681
    0x206010308030705130503101e0501050a06081906091b0302040312200307030302090a0803120c211008010e120324040212010e10062f06091b040203061003 68
    0x40017072140141d14041c1c0401c3c280c4042202d1280ca069000c0001541c02d090581c44e1015044e8103800741140c2e08220052000f925012003507801c450050504100e00d456003400e1140c40a8041c0028400d20f14040c1e0005611142d9009000c5500220040000d0607030100412020f901c00d070f00000d0000c0c00d10a242c1403540b881007a04110010000b0481951815064122411a44801400c1d00003031f4005c03c40540c00e18004032908010b2800000a5142c105054030320303804804024a001c01a40700420511284e554504880c0340c825040da1007007111346440c040181e000c600c0e900803541d541d0300e1700c00514800300f00022201d015203009100d0a0659490500746890809020340c8000480c081c0c00c2e101007903490350f0002d010780381a1820b070f2100542c100300d241030526500509504410078449000c014032508109420140648420000100c50100a00c1900b070748011a003252140f10b10310800400e0540400e2801e8100b0300f985562035500202820001640800e440d0960701518040400348154081d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 612731178 1250 612729928 612729937
    0x20714060c06071106060f0904030c020103021c09140a0209010b0307090f2711090603060d051e0c0114030612011401060203070308012c090106030b0a0212070206010308030705 77
    0x20403241c50a1404540c45040c081c003910210301007140000102ea0049040c13020542c4040b081d04c0c40c2d90035012120009031102409031001c3c003072203c00081441036912a03011a0110050301c2103170f81000c80e094030348500420400c401540c105007540f030b400203010404a4888030241d0010030242c001d1b401c202c0c0c60303003090703001074a41c0052000701000000e01140a5040100421805e021350441444602510401d03014030020b94226501e03000f0244180d01e48141595550281510403035100d40d109004645004103245001d01644281a015502803007200000d10019144405031154010000300550303520882c004006540e410900c001200d900341026406e80350800c0030000702e00854500b00044c1700d283c003030704514016000080d01c0d10034103402c55489401402c480b041084100b4440c98015034a66030700182c544084443d0021418007242500a41c001c1c68000d07040d0140760421502400081d44210003c0790050703046000900c10500101d07441d4101c94000000038a95a00c101c0e080314203501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 612732428 1250 612731178 612731219
    0x17041d07050d0f1b020601031e14010509010501170c010c02010309031b0b010f170729030c1305010302094e0118110d0c0e0f0601110a02010207 63
    0x5052102c400b61501c02d0040045041410000141c0741c6100307450b400581c5188820340c1c09561200c0300400001d00e0200314200f5480340303016401c206088600e010342403c2207400c0030f040344e58200803d000d5071031019032055040715010b4100f070000800b0b42130902c6d212245a005203010402d0a0300c1c12015500a0304102021407092800781200f50a955101100b042031080503074940c2905001440680900b0b224680504620060f03180c541150b00c081c5070742d0300d8050142006030b0b000d01d411006081c13584d00c102c20035500c0000f011900c1e0701c2c00010142079504105040488400c0351b07170700000d45500900c200c0300801c8014203101b8030340e052480e950341e10400010143e0342d425181450540b00b00c503c0c4809202a2a80c4004944289580c40d40c05007940c2115400d4204015944916000100d010600c5201c5100580700d482c0202e50500b01107000403002e030703c0a80c403040c0c4c00c001c1141ca030202d1300206114000036202c004542c0c0035512100c0c2e661303045a100030b02581c40202c0610500c29401c0c1840103214 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 612733678 1250 612732428 612732437
    0x6020312130803100e0a09020307170f0f06060a050d021e0f04060b0310080d050304032609010b0102070918110607060c0924050f0313051917041d07 65
    0x100301c1d40d00c0e8140b5a200301c50035603d20441e00b1051045030106842c00707802c50704135013050001c0c10090f00040d0710340e6100d1040c1460420f410386119080142480404000c54845040ea202009260109615640e003181d190348030300c2070b200011515107007940c1200c24858010342940844040071304103010521a98032020f5204418158080c50341d5140d0103194050242c0c0d403400e0382c40703081a00000b000e10805411841e1b0640191203042c071321581c0041640d42c05a010301e010228484106107984c0200801401218070180c2d0314100843c1d0341c0305420001c800c1c9020307070031241180e40c2c0e100b0036021540f03180130721480034403c101c2100c041005000c40801e04440140858900001550b81c0422505240a04008a42c400808000c100300300d141607103200201c076941a82d04900000000c10300c2c4500e01a01c150a58007201003940c404a404040d403865134031000320340c0d1071400403040c01c06600044808480102088522100142420003035604440f03206651000500001054a0311350100030201001c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 612734928 1250 612733678 612733711
    0x506090a0321200d050108030f07031404080109080903150105090705070204020d06031b0b1207030c031d01020d11160f1a101a09010f11120705010e0d0906020312 71
    0x1100e41c0c43c05050f440070781c0c0410580d9000218100d8040d51416400b1120a400c00d10280018146d003401301c031440c552515042110014885050000303000b40d40201ca42586005407980810000100401b081c070030440481320354040f5404820f9460400340a501e4001003410003241d4034901450103002100c0c4028400740c100a424184241110001c2c2e00603a0410410241d448020001c5840d600240c4414000c280c60b008050030964040380300507102104050f5a03c159041c8180311703600c0500f000e5001121032407100d0703006403420b0103500506241c009140c508840f4a0280706440211861801030018a400d510003588401450069164040c0d0341f003001c07005010010180d49442612800000102060003814416503650f85100741e039450080d03000410003585941e030800101503062205207072442c482807d1200d41c1b42040344540744c5609100d40410302d40c1c108401134004041ca04400421603201c0c080380e4001302c1e5411003d2140c0001741c2c0080041000042d035407e1070550040096828001c107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 612736178 1250 612734928 612734951
    0x105150f100f032004090e0d0804081b06040605070801050103060f350a030305100506070f05120d140c120a2f070b0606030108030a050903280506090a0321 68
    0x440c1c03801e148800d15200005050012103502c0c441c003c0d40070b90010088c1281c1090820243c04280048c1c8040c2c1940b1010a01c3c02c0004280d40780e40f0550030340f4806851580c20700e403070801302501095940d0b002064031000082501d51091203090122866010340c1d034815403400f65100b1084800040d0803d10300c04824bd107102d1140706491480c2c08921103801090544804e042c014100c54000c2c1110111500802041049039110000e8410007900880d0305070a107403480c0b52441c904000000900c00145010800e01c01c00078a561003a194841028000c10b402d540320840c0340c01030301c1031505003070b22601c01c4400300d085601d10351700c51101c151181040e0810003164466451400d220440301d26000350002456408000360369030490b4124500391192404c550601c9011610707402915010400c00501044510240da0100800214171400080b02c415a83c800c0b5400c0300c6d500c14940064501d4415080401c0d0311190020f0f920223040e405980e05e01d2032801100d2400c901a400710030510351a0b072501403803141c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 612737428 1250 612736178 612736211
    0x3070b01060c0308150f01210c05070209060d030206040b040606031505041208010b090f03030d0f0204150509100806011e0f180308040509060109080f0105150f100f03 73
    0x3a00803038a80140c40e202c180f8000f44500c4005244400806003801c680b40c058030781c1d0040c03041d401ca007405c1058103103a84066202c0c4028000c01c0082e42c071403d10f280c105010b5040700040580314000c0c0d07a0107546903244000d0007401e00400e100180103034080400100812203081d04103420620841c404030780941c3c2c80c1c4601c0d14001c100b0b0308041c12075a82d00c0c144001c002c0b0142c0105001e40b840e0403e01469850702c1440701c8680212102c1502824a42d1102d500039503040c4200c50014140070003c00801c011146048000d400ca4000e40c01c95201503041000c00a003d9800c1d80d03188a0000c003190b01800c0c3e1070000700c540310302c00307400c0e9030501c0710540755141b2241030103200d08100c111543c1e5140301d030fa080c503a0003071607002906802d50340d140c0c4034182032020412b004100c9051301c3c015600d00d141030b1203420040302d000e000da1307101c422580104140c5103c1442d040d0096406400c0712000d2400c0b00c0c91701e1041208400c0c41d4500340740d1003425002502c11040c01180c180e1424000c4d802c00146c4003480036040345 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 612738678 1250 612737428 612737431
    0x506190303020c12060f0105060a1404231e130e1c090f0e22020a0b130b2a0c04021602030d08010b161e0609060e030f04120503070b 58
    0x240540c20010b0000c00c182444c042e5260030514520080c201400c042c0140c031290b0b2010302401c2e0013541e000170141130b07042c040c47c80350000c1311b0b070081c685903580d6403003070240c5d24581c25450b904092450300c5201200c1e0720700041e941801c0341510f902c40c0300111716a03042141d00a6a442c031100c8040c6c44400c020580b10062040d450405c0140d64400d071010706440c001401c40c40181c0010488030b00c200000c0c0115882202e40e0365101c1d95031300e41081e1401e500200e50210030f641110081d40310100c48070100700040030901909030712032100101000e481d2240b8840b202d40c051074621003001d0903402440c40002101244c802c030b0408820082e41c803075400c0301002c58141c1e8003000c40d007074405294114840c00c5040c10040c6401500d41d03441c200170654107256214495204441140070781951000c2c4100074401c0c440d501008040746080040300411282c904640505030f840c101f51003461030145100c80254020084608440c40c01c1d071001c0c6010308051078449a821103900665041c40140720320000100c0414949 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 612739928 1250 612738678 612738683
    0x15050a0504021807140c0a080f0d0c0c0807080a0905060c0c120102071e0c2705161e090305060702010504050f070e04080f0d0f020a230d05061903 64
    0x4191031405006110f0341c0f4518080c840f180b03001c074070100204a907024500f420050f202e48401075a40c0c0700c000038a0310707054020b2409864044002081d0001000080c0200106983d011051014800001d000d4a1000242c90041c0c0b101108200784800500c40c54010315001c26a4200004401e86450200380320f900400222100e991024800300502d2500003002c00c0e0f4440c0040c001c0d40740c0000340d607d00c4074200c1c0c5400400030860311000c511042104c4102c006024000c00481c0034580c0c041054030300d62030100e1504880c42c8500c0c11000c150903ca40ea0405111b0002944500d03880100110072a824120351841540c00c0046080002c00058410b000807401080355900100d0241414104242082c242d100b0414165224040c01c00082e8040a20141e01940042807503460390240c0d4020714080c81560b40201c0403910b00a016820941107502a03c240045543c50340d041d0b030784c140c4188482c0642e10380c1c1c81001705001d0240514440030f581046a02003005000134601c4094103020f400710038400c2c0c204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 612741178 1250 612739928 612739931
    0x5030c1e010b0915150d050a02070204113901060902090a210303020307050702030316050c0a030c090c11150a110a0507030806010905100509040c0f05031315050a 71
    0x203202290401d010701c2282000859810010b803c04c0c12000c4400241503414a0040055500b0781c42200014415114540d404020034005490b00caa0740700000d50006008a01c20707403a20b601c0075003420b03468050f01e00c0d00c2c86054440e00d1502d84015034022584040c940072040440161192010f0082070141800a000345d00d005620f5a000d2400c2201c2081e164000d804540505040c101e002012804210205038046c180182d4a8450304011219407091050184d094840000c00801041c289042111114016415107e240d841d10f002c22408503105d02c03018010a440c0c1c002800900490b600c4101400510b0070100705003101045c000b802c103005103510004001084040081c000302500811586503101a0200c0c40d1441e402406405801a10f01c060204010f0f200080c685074083d02080000c0d1900030708a105203008030300010440c0d400302240d1030140f4203100c955a1024040c40c40e5100d0941c10341c484d80c0c1580d60b50081014010984c0d0000d54080503041d090a1551116110301401002c80000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 612742428 1250 612741178 612741223
    0xc12010b060c070f1a120402300105160504091e090308010e0604020a050a030218060c0a0219050913031403151207060504050d050304050a0608040b01080a080409020705030c 76
    0xd82e040840e035480201035203010600c1001c4c080ca17030400c89074420082d142810081d2030b0781c00031072000000705101e804025200300311544402407030f0189400410018000b031205940300201d45814405800078500499000e00c403d002025480d0092106c500d2842070404d00700d180010365005a0b804500305a000c903103500010702c014001c2d0140c4503030010b8142c5080d413400c0301d040c0b001415407143c0c01040c020954003040d80b80c02c82118801c02084440010308154039120b40d688110389520500104910401d00c1c030030200c4c3ca803101912605c080301c200804210942e43c6004400c5070121440d4002c40400c81880100300703010b1238440145004030341c208403c604c00c4d1100c01c2800b92100c0c50142007089680428400c0181d207a0150885055072419030b50340344084001d280851440c026504010b134440e18903000881c441e54070589151050340615078408950740e81c1c036841ca07192011030601402100c0c00304001c0c070140328607400400c0c98601c03400c03c0368a460f034a1541d0314102502c552100a01080507031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 612743678 1250 612742428 612742439
    0x312140402180c0d1814010c020d0804050c011b0c06080615120a0c05040b0d050708060901030c03021519090603050a0e0604021003110708040503010f0b030c12010b060c07 75
    0x581d0340c0601104201d14045003000c08800300b040c0505150103c080740c503054241540c17001c61602440c400d40c0500449001401c82514038044c00085640500610510302c50039100c80c801d040c102c2c041c5800502510034688800300441d5003024402091001d00b10003a03000d03000490740a0503500a1500b41e40d000f1241c01d04004008903a40010703290001198280b00704c1d0580b0302401c201d03641215a02400007070a4080001c2650140078550106100c2e00000c42c43c180310440682000d40b0407481941c8603500c3c0d42d1548108003a5403020b000290030040c0d100014401824980100c074021100e201c401030030840c040b1550580c0d0145000007100107065000200000c640501a00b604481c500b6414003112000c1c000d00740e41c903c40200b0203407041c03205580c0450313054000d90011201d911918030044c0d0b19941401e00381e410340d0052150500a40c6400142e05100d849845031442030540240503103400003800382000074a280d032111280455603603810700b4096079211801070010740340100c06081c20f0391410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 612744928 1250 612743678 612743689
    0x40905040b01121a2a030105030c01020f0703060f0b0418140106050d0201050912060f070f0f0f11070b04180614030606060304060f02340b130312140402 67
    0x183d106094200030900d185000403040102200c08041d003120804082d9201d4000c04410301d02d01456540316011171014420307409060004505030f47e400c8d402c0354020903218004980d20800e02c03070300003140d03000190144002082c9400c0440fa16819590108040d404000040c00b265140440070710007100f110607003410800000b100c018400e1480d0002c0218601d07040208100680c6079230000c0c10481d0001f084d203010780c2c0f00304881d4000c00408003114007501d445040103600340800c1d0341c1c01010882076039a10000303030f01c21101e0743e1128a071035890707106c0750030201d0064501c2c1041d0001294540508000030900c0f6488030007600050401044503040684d0010ba40b800321341c1d149d000901d0040307164042000545001034500d030004001d03544940e40783da440c14040d008044100e03243e07004a0001686254001601882624012034903000d11008024440c5250001a00400c003c0801d400c54002a072400707801c0103000422030082c104260802104003110b41240d2046540f8030071400080144025402c05 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 612746178 1250 612744928 612744931
    0x20903011109180606030a1d010903090f0e01300b07020d03110702060301052209030903020a0608090c040c021207062004080c100e030d0801140a0b0909100b040905040b 74
    0x1030b03c8803c080e03003800004121349100051020700c106848175405071004e00b056446180d5401c2810080000564501e030041c070080c2c0512880c03551940500c0c1c003040c044c001c90101c50482c0c2e041049000202c464403c6914425030303031000444501d51f5103024102003032000280c07610507085540a44107a10000401504981c0d01012244d154107080c00742c0780040e01c42e5411203055075022034848441101081e0700300784038409500400070f91414108201c08168008240f041a03900c21180d1460050312500111040c05088421a030300394022090504203007442da2281641c17030401c0c41582c00d40807d00d003002c10154025003084550583d6a4054011045a005021255031110406a141c2450148401c0d591181d0100e0701d40714084031300140040e90b0060041c00c021a80103415604002012100605000e001b48901107003002141441c1c2004c0ca0025884002e0b6090f2804840c1003030360b0704013400408071008084810503800c020002c219a0300382009030004010f140c002148918091400d0100d0510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 612747428 1250 612746178 612746209
    0x309091113030f0212100902090a05061e060d0c09050301060f060f110118050a020a08060601020d0804081b1e0105040c1202010c080d0e010b031c1101020903011109 72
    0x8180820404524002400380031a50490081c0c400740f1000c0c0009039a01c2c1021280c958188603070700a500c0e40e04c1180e04004213a42c004c44108c42240d895098070000d4034821201c555001e40c005032600514400340b0001e19460f80b001d0011801c054003034200c0012154001c150708017144080ca402c000500d070900071540540140f030342880c8154a080c5024200e4001014203105004c0b03820380f80ea0312810258010003401d42610f41f0038913060342a0a01d503888010301d28041c2d0182038081c00114425000040d1103015903810303801401030101407c022917000b90081d01c03c07a140d10013000b840003e034a142580942070b0031003101800d1f030b60041160420081000b0200645c130b59040204100101d10741001c440c0031103001a01900e1604500c0c4012251814981002003110201040e1140e660000c1d45c4111100c808400007040300d04598070400d40d60340b4491082400c00301c044210400039501c9800684510607514001505085450300000c2c01e50f400781032401c200344004180582c1d04d25092103480127652 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 612748678 1250 612747428 612747461
    0x3131103030f09103f140610020a05120a020d0206060a03290c04081605030a080c1c081608150919020f030a0c08090c090c040b07030909 60
    0x10103244015445000382844180705505034640d04d000075028001140c442c507421001c1002c05080100ba1040781070320410325628200c00c5004c00100408948034520000040265500300c9560b5038007009444104000c011085004070184c090000304100b11080d46010a50481c61311200c1401000b4580385644500b002103501c01c90a1040a4613180c800005480c3c101d0b1045010500100e541d00c94600c40c1d80626840c3c8008908000d124020b040c0038206540700b10044d40c0910f804e010b104020600d4500403550f2613009028000d00103100b450003003079403041ca60185c2c0c2804507201e81170502a00301407452408500305170104007081c5c4421085540d581c0c49030510120501704242c110003500d000c4503905008011000100d07580c80260040268600e04c010b005546c2c8080580b60050160410b50f21051458240120700d44240e000d030300d401d441515004020b140c501d941c502006a407110182215102503400c12020a5682c0b0a0000f00160303806a00e403214030070b141412000403a03180d01521030000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 612749928 1250 612748678 612748687
    0x90f06030f09160f062f0703020111031c0b03010e0d0e0a050405070f180b1b0d03050c030a02030a090b13050d110a031101020409020703080403030c091a0a0c05030313110303 76
    0x132280c00102015107009240400d000c3c3d0f544016011007071615150401d82245c0000105419a8009101c1d8250781c800e9071814410840040c550350349000b412403c0000741190350040d050210a44c3c840101d41400038008a40d03660f00c07041940c04c0c500c030040041e00050029000010a0401d42441401000700342e5042003103150000009004000038542c140401c2205503448118825013000e40010f4840106403d580d000380710310112044400002c11100c0c0e02501a800720303c28000e2003442d101d08200c0c540b6030324603540c04013084002d5200801c141400b0781e40f0341da690085030310030b9400c900c16010b201030004100c001b418000d2911401500310010044002115001c0007808509540995898204200050004003c141c0a400b950f007003282d6a610201d003d10516a2040800303000c0c0e8000d84041056a1240400700ca915250b4020a8508060710340c1c140c0f03400c4203c0300200588511850254152901c0b55903947c116803060310401141003100c42e500003485090040c00240c544101c006510340f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 612751178 1250 612749928 612749939
    0x306150609030602031504110c01060816030807060608010f1a10020318040b10051b010608030906030a150b0c010b2b050304031a1603140606090f06030f0916 69
    0x7040c03031804000c0100e500440401c0340303008082072208014000030020310881031658100800b50708070724200b160641c02e008000a14a5020582a10f040c2151a00c2c50b10203086440d5960740703902004007102d0542d65000b000a000c8800c2c0700b20048140c5840000c40e5040710340d552030b203480c454a480309106428624070b00f25400d800000303c80d0488844504150a50030300d20000b8010807031690941c0d0003c80c591980d84440c1e038088002d0040119030402d80b04032080020a0781c0c225030b0503010301d902640c02009103407801e04c1d003440a568403403484180490b2180207074000318109000d59000c0c02c3c0c001000310b0301407003424080c0200461890140c0307403101003000c103000820306200107840c5060602c18106440f070500500b802260701442e085002080c00300340180042e89000303800c6808024012500001d00c00484c07182c0101005c0440c160219201c0340c0b20b0700d0800c001c56201c0321400e644401e25044800c0350382c9030400030394802c812000a03071981c3d207415500241481c1c005180d1600300d2a00c244140310 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 612752428 1250 612751178 612751187
    0xc040c050a0c0b090c0405090a031715060304141b0a0602160e040c1505040614040312030e100905031207030902061e1b010e1006060e010c08070209070903061506 71
    0x1407250304689003c905448a03036070603082c0142640c0d0184c0240c00e1004010b0441c00000d0650541c034400e641d01400c2140d40102c080710040306a502d0a5004842496031005140c2600655001f5004941c0c150300030492071015031903e41c0d081400c0b291840310180300b01c0035113040c01070710380280781070b00107005071035174440042c48140c001e8000c0c0400c0c112a8008a414455a086201c01810018500e806001c0c000d07017000d0166049807141c100006c41780240c8140085c0c2400c280c5088075480720700d1036459850144150003400000f20075000038070031494240d40301d80c61401031410013406800070316901e0206407401200b40302c0043c650014581002100c00050b01ca04084503440780d5480c41d00c0d1080085a4007000c1244250425100c0d01761042581f036030f40200c10760090003a09102012140c00c40c2680030f070581595501d05c921804a5101c1000040550051101c240300b10b12800e201890540558000303400d050058a1040000344640800d104010007840354007519154400c04404503458520b0042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 612753678 1250 612752428 612752447
    0x3030c060b04020a0804060609020a080613091e05071202152d0c0607020c1e0604150e0a06050f0913020c0615041512080306031006080c040c050a 64
    0x4041084004200050208540c01070061403402001950b451000030401862040705581c00c0e02c86074600007000400100520849005101646403c00703e0313035074601001058003140704440061038854444c034001541c5900321401d03202212000350f15040490405a24011464120007041402000c4402c0135a8403503000d8849031410f8070050740d90300d203003032a40ba054840d810003546010410290002c040c8001d40c000c0c0154003020350072105207544021003242d5031000005096008003504015196420300b14000d44003054001d84510b10702652000c108e91b6501d020841100051a1121014001e240420702d0200401c82031034507600345075540700d443d4241d104440c1c01c00d12950546070b808100c00090b030103580c400f8023048161101e528002c074002c0203601850841c00c2c8903501e05019085900700083c21b4205989a5001c0400b80c01e076181c8d5944943c1e40040e0045a1611401008c4641407441d4004d100c080d10088000c0d1503190f00d240d0611043e11501082078003032020a21100407490703072118244 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 612754928 1250 612753678 612753683
    0x120305092a062104060b1005030402010801261501061403010608160e041b030f021e1810020f071d161211041406160b040203010f06120c0b0c0703 64
    0x43e82c552842c451207075014410720b0400001c03000300d41000140aa04c0d4002d901d140c07415940f4480740303091a842115544421940240030581940040c020b0513005d480da02c03031181380641d0720484403030182c0d0510714044644212114401c9000e00520505d94420a4002a540c400c280702e400c65060004c060584440148460b03002801610000c852a204000100f81c03a074002d0420000712409040c0710080f00c1410f9032032030129080080d48186020fa6108039003c4001d28030600101d46540c3d200c00c0e0190b4028040100310000c1c40c10b210a25a580200703001301444181c0082060700c2c0c02801c5103081007074652000e400000c20285c003a840541580c811a445500803055440c1c20140040540e981c200400c5491211840e00b1010b04e481a1040e008200391100d0b110553740d0b00c000700e8200141d038030448c00b800d101c4000c000c1c00200090038950300700d900548005c0002c03c025100000800450b5001e500080004080c80400000d005014010802a003c400900c0f450a003241200b01e695070f00d00d1000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 612756178 1250 612754928 612754939
    0x6060506040501050a230c06040c06021f180206031602010515010f0c03020f030a021605030a0f0f0c1e051905010206180a08030c04240801030618120305092a 69
    0x1c0302e0442e10301c82101c04046d401903482e00e40f0f4001c0045040e039500003c95044030010255000460880e000041c906034124507451034100d61507800e81281c0140c00b40040c4d40018140950341070005907180d001840c801d801d80e0340c00743e1070008122002420755201404500c0340340c070660320440d1540d9102c44004400e8055040902c9030344c40a140407440c2c1030034640c10aa80c1e0002113680f2551550115080282c1d899554001c45041d8461040549410f12044010031120150301840c00241e000e8012000050286400401469944000c00314280381003421411660b641d03501401149042441190182d05580c41c40028605100c0082d43e20750020b89204c580fa8a07001182c00c820b00c0030800100c0c0c030740e80103d009440f420b000c420703640d8a4210740545040d04180c10700a40a81c084410501180070081e0359010f05a4615240e505c000d100340c0e101800044da20101001c0855006880040700c3d10712580c00080728a01a0405403c001c0140c003035110440e01011541100c1c4510070f001915404101e40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 612757428 1250 612756178 612756197
    0x15090a02041202060a0e1302030a06050906100311040807150f0c0203100e19063813020d0e0c0f030f0a1203060f06020a0213050c0304120e0a1206060506040501050a 72
    0x1020b446c81c0f03181003605c503800583d1460200722614140c001e1805215941c409012a40c0c4500c10040b12910440300300f80c110181d40c0303141100382d100750000c0c190855004001c51609440b01d41607800c01203141c00025400045000320584036602c201040310302d0002d490300b15030000c074560010384c039055000205140c84d9280ea0782c1d0354640906002803041c1c60120702c0903001c0380c025840d004e0040c01665220b8a2808104444d240000c054540b00290010b02d84810701d419019040401c030b01001c0d04d000d0302001c16400c1c421447c0c9800644039000f441208000140030b4420204100202c080c007688502c3c6c000d8000001c02203503840000360284080784d100140705900b5078060400c400401f0941e10002202a100e180011003a80210303245c66454000d8401c15142c0008101b010203840c0281d0f000208800304100250204200802d000e60565140c64800341c0d02000310f00207940e00300c254100300307030000c076040045007040301900c9000700415040e00e1603400e140c9402d00217451400764020781414480d4050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 612758678 1250 612757428 612757447
    0xa0303050c16060e060f04050a141e0606040c0302041514130e0a0e0d0905010f032a090e0c04030b1f060c030e090f07030c11030315090a0204120206 65
    0x3070640300d03211040005000500660700340040a0040b5a54842040c003512000c140044c586200080c0300b1904200100f854142aa90b07010040c203080141c59218020303403007607948107246a43c200702d010422030020826801c02da03040000700e07000031000106061040208105d20041801d120450303030380d01d08045071b0a4014004090341413044800007143e0030203102c0082225800e10000d00e0003125001d80400c00c4515045003240d440300403140d04000b051018070b040002d0b600c54201450341d400d841c80c020402c402e42c0f21103100c2d0004010303c0008a080403020f40b0884552000000c001087c80c551030311100c0c1040502c4c10700f9845140009000b0300305100014204c800146a00c210311a1001145008281e80d0307a001400e40095410880003d0088002040545403000446d07004080590400c0d4403511600c0c815801803e0304441c4e1010300031020300604c00d11100740007552282030a03a44004040614a04002034004000c20004134544103001c184400101c1c4094001d03502e5060b03880907690b00016 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 612759928 1250 612758678 612758701
    0x16081507080114120a060213140a03020607063b0a0c0e0402121006060e040912120905010603080d110a0c03031e0504140609030c10090c0e01081605040209030a030305 73
    0x4c140c0c8400d10030009501e00300803066008050049080380b501c6100c0e91503800e2650119050220294030074181e003020301c0945040c4d0014000e203032003a00001864440700c00b02e9034001c60010b0110100e5012941c56104480142c0800c500d2400454084c0540900b5a0350f290580b5000b03014051ba482d10513030000b011512050000c1540480d540c0854085003402d000340c02c0035168500070507000410151842483e420980640148140c0c0321000402c14443c02108544210040c8141404651240710345000f06d82c0a10405003d58010300d0115541c00c005140b000a444142c1d104c0b10400c8410804a1203450f40b0034248502c01e640341c134010488080440c2c90301002d8541d50003000c015417814090104015040c10806005041001078035440e0b80c0f40441c0c2c64a9014040524409410a480f01410200168401d0298601c44c51054a07510740390180700c400940c0980040845600c01442d01e01031b40c020305100801010116411340c82d01c8c1c10000801c1e00c07480001c1006007071503198030115034060583c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 612761178 1250 612759928 612759949
    0x2030618070506030f0105010f0918050a020412150509161809080a0201152313060306021b06090c06090618060a020120160b07020f16081507080114 65
    0x500031038481c01c102c401c529205c00d0a00c142408a00c55a0300b03c5007003401a02400c0803164210500d5201c8d0100300d1060001e0b040041000e1201a030811000c0f41c0301d0a03960301000b070180140c4030f100e4580514002042110350141600010350301c0814190040c0081e159410151141d17141550071880c4814070500141611000050492070045004005568150300506a440f250407024008581d5060340548824020000d80326024034070f04000810b0902d2903014804412242c00040c0a42d9a504d544c002c17030700101e803035000c181c20850010f0140320081251a40052480c00640180848240003652a1042640f114001c200c013151008131b800c0f80c1300c001c071601580500819039072a100d0400900801c5840301d00c10562000c4404050380b55039420641d81c4d0b030a0300806550158405461b400300c44c0400615a50071032048103010b110481c0305001d054400c0c010b00703605840c081c1c140030344642441c422083c40d01180314804100705109074460700c442c0c11501c20300044d4407201000c1021428403001d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 612762428 1250 612761178 612761189
    0x105210a05040b060d03022d010c180e01050120010e0109030e03072103030b0a03080d023006011209020a03260f0f0a09031407060e0301090203061807 66
    0x1102000403000032a00301e544602c0c4156032040d9150340d20f904100d400304c0240d2003d030060740241c064001c03d2a058100c01800c00d2640c3d03100303501403010040d85082d00d00719001c1100141120f2a07501c5041e107101801d030040e01111010400079810800005c01d031044160044004081c100507c1080c10003c6d80601c01c1083c151009001c548090300340544402c0348950403d01234491390000156440084d800450001c03084401c0d00041c081f00e40342180a0004a118150700000e0700400000140204004100d1200b03c4040076859030402c101b180c1840801c0c03000b0003503c074000e0320070503e0350a08a003400d82c0004242018000202882d200c2c000070516080001e4000c1340c1c0960200501030b0003592440030420410701d41f4031030908803000baa144d000c0e001982e940001e06010754007121000c54060311fa20411494040f40050744c030740307614034043c2d608424098640c002480c240a80390b0711001d41040c50800360024009015070780c0c0425911b600042c190311022996001050241400f845140010803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 612763678 1250 612762428 612762487
    0x4060e0604140d031503080721030b100914010c110301110310080c0901030609051603150e0106210606082b02211303050d03091b030206090105 63
    0x251901d4410014260304480c21980c0c840c44103400003462003030007085d603c4c22003925609891880d540c0c940310581c104d220102e4112074000036900200d02d44a00c1070880301860750300802c1c0004e03c203042c080135007100e1002e0002c01c41c15040074040c6107403103140d90352072410a103040816916503041224400c000c1e01410b69065080800c541d0b4803054602c051802543c82a024464241d030310112542e8824401620b1504010540300400104540764003409a81c0d000710144d0710344020140c3c03a200841070641045840711016090300140445500c04c81da090700145000b007220604010f04c140600e00d403103010201403003401c071900c020813015800910007010b6000c206e07001400000c044c0030740010f540c1084444401580b2007a10f41d14400240c108402e07086805412580d0142001060180c1c800300e007030202c2c02611500003001031020000783c5000301e040c0d580020980c1513454450300c4030300403500409030351403040c00c1400540d0341e40080b5000c440090030031550354262407140d110022660612141002c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 612764928 1250 612763678 612763681
    0x3060605031504091e110603011a030c070f030915030b01140a0306080118200108060f03012406031410050904020307212a0312020a05160e011502031204060e06 70
    0x40300300c40f1000b5405c3c1c0301d094000c003460280720074002180001d1044a0450240400c2402041401c1c0d00442e04079144c0464545012010b40303403510715010136031003100002d800180400c088024003055044861840c58217010182000f00024800e1072514030490001c100040c01d0041070f4040e80c8003900802009009200c204c0c6d00d410527038500f910380361081e103034042044240c021001c13180401900d1070704141c660810701e48691041c4900b03020341a40c10b58156603215140007100700d4180c200b0000050006400c40114200207006080d1001c1a850303101652082c0e05010254030040c9081c015100d00303840309400c41c2d64500009241031075590080705100e00a4440711100c1400c02102e240d80c502030350340451507958801d20b140d5201002c001c07814140410b5441400040c0044017440c0480f03c06104a990324203050300c0d01410418885690070070380c3c0e80070600f0031038500590741c41c0d80100a21840203002d40781e8000040e489100c0c204485084d10004c500103410488a03500240440c41a0001c40320036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 612766178 1250 612764928 612764963
    0x14150109030c080307021c030504180914060916080c04020309011b03060e060108010b03040b070e03160306110412080c160603021c11370c030f0306060503150409 71
    0x1130760720006069004440802c1502d00c140907660840d101c2c035505030f443c68a05890440b0110f64501109003402040d500c1d4040080800c1074001d2a071080d4840d48094080b0b4100614440e184c1010094041e4041351111810404104007190200c4680703403c0e5000741c1d8030369582140710f00405000600c5e10f84400483c817450800d0381e15600c5442a691324031158120381e10b6410041d2240e60091250810501c020400100000c90310000c1c3e43d0440131350300301003100b0b1003400c000a08000380c8400d04400c1d403421820403c180328032801000b405c0440400c03014545410030040e0007544444100c007400703154000904668410082010858040001060f01504d03600d03a600140654480c201d11641c0c0340ca0300f0703046018036142e8802c00d0383d8a82d40341c03d114540040c0e08166401004401c000c034904c910322840c0380790740c2c01c44224405441c010580d00c42a42140902d8003800b458a40a40202010319204060000503000800c4030341161580c240c81481824120000b4068040c100e001001040d084000004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 612767428 1250 612766178 612766183
    0x270302100e01060f09020c121b06160f1107030c0f06080906010b1605070f0306090201090803270f130b03070819020405041e05030702090a14150109030c08 68
    0x203203211103440611807030464403841800d9400d503000c0c40c1d0b144540c3e80400c1105058a038000d0210301d19003000d581200030300c403220b111660003070000c0c020f0802d080c00808102c0c2000340000ba0340110070440122044015100080c0f004100d0074441061050a03c44401000c00400c0310b03100465100491000880e02c804280e03074040030034451200420682000b0800320722000c0307040c506079820518101d08043c608101e00156000c4c41c44103444500030210041581c7c0040c043c0b05000e50700036800410450242c2c80010084042644001a590002e1100c44400e40308800712244007a1b42c05c00b1100541010300004003612280d4241c554440f00064559800c0e5400790402c241a4104034183c545866641c056192100c3c16203008040c000c0000b90b02d0001450701d94442070300301d40511a00e0b25040303507043c2041c403001c0c4082410342d40c0380c0c0045103020451810b03503900c0b0f81c0a00c0007041407111044140c440c500803070010341411040c0344200900052139105060600086410012451030581d60382c80494 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 612768678 1250 612767428 612767443
    0xb0313140115090c0c02060f043206180402340c14152d1e1602011d040c08010f05040207120c0203010f05162a06270302 53
    0xd05041c402c580080d0108662003404055400d544454182c400e00d94204040c0d0741c08901c1d88011003009210100720010740040103050429401d0144103880b01394009203203140c80c0011903a11490301000306188208210202d80e56810095801603140c03100444540591541030100120030b280d18030700d480b00c203c24640010540c0b40110741d03c0c6c85564403450f02000640c00840740682292208075000344000b4410014284150450494030075148410440014440c0344903010030740c2100860340c3e51060078001f21140c0e012180040143c0343c0b04199000c180b10071400b02002c2d05200942408400035000c0681840f10b80c0c0008208102604004401601441082c0110854a2501000845c15013814401c0350755054004045c0c00e4110030700340c42100d81f480c10490890700355483e1184018050001d015107802070b42d60304008182503808042c000d010200001c55030350040c494030304c5400000c0b00100030003031141e0804000705442505a445061a49802183d020900e4945807001c4c01d06a012800c903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 612769784 1106 612768678 612768701
    0x1a09061b0d050d050705040312080411040f0f0b04090b04170c12040513090c18060807080633010c1b0608090d020a05070b03131401 58
    0x300d0030001001404008540e02041c480ca42c000c243c000c50358451040d15200303060514649582425001c14036006041c40140320100c1c0c00e200481c230b85404082c0020300280f10704020302d80d040c4000c00b40c0003402140286001c091901da840c003405030803420b640081c0d0a0700d064a80c1e07120145807495551030312205990400090305141c00c188007a5028a800a0b6a00d44983c036000c248104401d07441c1c1c1c0c1e8140c0c0d6140528580c001001e800421003034076402284901700c2644024240010801c07a0070001e00d44c46114000980000d0009a9030b1050440b81d8100c0c0608240411000018030408440038411500b07007041541548105405034490f40540442e9407002035a03040d03801c5600030b42c1c00020000b4480380402c0b0b4040f00070080340b071480801d440102114072540d100c2c40d8641c403482c01500640c1c20b0000100e0020500300d000740010702d400c00d026140c001c40348644140241407000d1380 = true := by decide +kernel

theorem cover : BRFrame.Cov 612589928 612769784 := by
  have h0 := BRFrame.cov_init 612589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 612589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 612589928 ≤ n) (h2 : n < 612769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
