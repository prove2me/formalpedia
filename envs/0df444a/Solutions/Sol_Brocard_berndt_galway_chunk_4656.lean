-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4656
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:18:55.04799+00:00
-- url     : https://prove2.me/submissions/9c72f2f7-3fef-4f74-9718-1502b2590976

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 837230215 ≤ n < 837410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 837231465 1250 837230215 837230281
    0x16050612160c05030c070f090207330207060902100212030f0c0c06070c1e0302030910020a1a010302010801060e1f14040b07020a060f080f130b0108010507031103 71
    0x540b40b0894001e0094014080000c02c4001c031500091000c044900f0800d0010505a486544504034028000c0060605001c3c1c960000d0070301514128180c40e08080d0580160403584d6615101240c0c09103200f19441500e0309128429850109040c00101c9198009013420002000ea0180d2038800100001c6200340880042005030b004281540c508120b04e00448046040034240a1704c909070301c400849101c550f090074203e03040025078001202c0d039071540003541059604000c00c080c07900c1c6049100114400d569072035000c1a011784140b0144500a20740042950541c0001044035005030804028001700c00100e9115490b12440c00403800c508031803504800e5100300c01121003494522010b9001c10000c40c0100d0050103500003010b04620880b03c01c04400e03583e24094468070700401600020130382c404002920b91586000c3c00e98801c1c6441400340194500baa038070042c0500c00c0c0c100c030603141c2d520320400040503054440c41a04400800502e820740c0343c0b01d01076000c901130503101041c01009400308 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 837232715 1250 837231465 837231467
    0x610091e0e0408030f150625120f120924110a05090406090908030609100801050106110d090311062101082b122a021605061216 56
    0x2025001d04000341a096460a003402e140101d60400e40c0c030b5500030b200000101c1d01601c2e5048110b12010f101902290802c0c03044104007011100c2c0b0468a4811641e08034160005216000544a4850203032a00000c0740100306004249030761456292044a1400c80c0d40c102090b101c500010360122600042403a50381900340c142d010708155040c1080341035010036048440e507008005001700c1a001e480c10400c00c0d0307450381c08100380e40c0300c803070003500c11241080481c02d17506140030002c1d4070003621105986500d598641c80740c21680241e00490003d084030b4200440c0c60414450f2035034a010b1441c20146580c01d43c0c84040c0250020800144521030009082d25001c1303000e40c04070f0842c00725021900042d81e65410103034540075503580180b011409240318500e0b00703481004555000ca100d03520161794102542100000740071364401200154012441c0400348110302446818a55490b0b025100c0c41c00f51070142010681c4903000544205801d10503814a00c4050781010752200d40b0401440e4900900e0300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 837233965 1250 837232715 837232769
    0x20d060c0c0c08240c030f090307080c240702070b031504061203110319120b0d03120b012d090e0106180f080a0204110f071a061009 58
    0xb0074691803810005480c08011807040307100012000300c201403001c09150100640720440d0041c050105c10300c007094013401c0a00300185d00c11000030450b480c0541c20b46503000c80e50480b103041d03400365000000b40c03c001d803240c141035410f401410b20300e00d15a0901d506c0c082e449209038000c041e414800400005c00e040c168031b400911450000d071007001155241c4040c10446007020809070013255402285450740c02c3c0020840c3c1c41524084020440e0345401e060480b11a031114044900d40c5880c0c4a0006440e40d6003c418101607100e80ca0b01c505042d22032241d541551081a12641442006000e005054483d0441d101562601090065020300242402e840000c00c0c0d812025403001a0710010906e0350304118000b1188060769004201c2d82d039965000a040398060082e1000c0d500408074503001401d10350002d503a403209003041c550a1490012900c502604000c1c400e4516000b0000d85220f0351180c10015504800255251440d48140c8040503103441103038401d40394015266641c04000764a014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 837235215 1250 837233965 837233987
    0x5151014180703091b1805090706020601120f120210060605130306090c030b0403110c091618051c030e2704030504030b070c02010807081014041104060203120c07020d060c 75
    0x6014080180ca81040140c100c00b180b1b00707010510700d0180464107581000407803608a4109600400503a0f080490408407002c00800c01c55101750b00d1000c000005000c1e80451554410b10b41c0148003030304048080b0f6040e00c0c40356103c2000e02800300300c0080c3c56042c082220782629004000814402c00d17600d4640e10305846039001820a518441c180010183d00c00c100b07140c550f10300c20440b50200001c008108941c18203482c454040f8103450304000d00c81c0d02840c844001c0410240c410012507580e0008941c4229038003461194240401d0556020103410032000ea1100b40140e80041807901107217451600c06031300228030428484500002000c15102c0c1c0100e9001e1a484a01e0150900309500042d0000c0d0502c2002c81c0481c3c10b0340e0006500c1d6100d000c2c82ca10481030000103111080c6091010400110815407640e0003039103680a500d060301054000344014000c030381c015961200c0441c02070b84515006008600690f80c10014440582c6d20842040110381d003064002910400c0c0410658140c0088 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 837236465 1250 837235215 837235253
    0x90b07110a06090506040215030f0a0f0209150a030f0e06010b090a0305100212070806010206040b070c020616033513200103180b040b040515101418070309 68
    0x10003142400c0050214085c1d01403442501c3c1c501e004940141d08c1201c41c00111500a111008070000805944503a00310b40000c2005a42c014a071842c080c000c2141490281e106c11003426000400c0b0710696454404c1042044e03c40d4404c000820200324200d03220a010300c50b0303500b0801c01045074903a81c1d41b42000c000007185d20004032807503c3c0c2d07403010110107500400006201c1010403400640b03142d0241d0003841c40b1343c005038050281030b035030b07560b50301d020313a40181c050810460302405000c016150440148240110401041c800c543d80303240c001c207400002202501c5442c0307038241440030909421007030a0815117440404915a0b160030384a866100c070180f002d040a80f001010007158000d0b03440100904000b0f076420b120309801e40c428140401d203090001084815080700090100303416205440e0401d201c1c800391030740d010b90320541c01e015a505841d0700c9800290000204881410003030390300c00d0360109403a9001c106202d009c181c0718002006000c40c4c01d254441000404114580305615802080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 837237715 1250 837236465 837236471
    0x50906041b030e0d0c12080c0c0703050609162103030b04020a26191d1509061b040b03060a0b0c1005011d1611070621090b07110a06 58
    0x1070050010050035030209810610300810044156031803040c1c00c003100141d00415000000b4407850710031188880300904119140405014080700c924081c4001401540184010141c42c01c100b10301c541400200c0d10303403110040c240c0300200010203680300f200e00800c2034036242c1812502c2905041d03014184880c3d90b1540b203440054140b1000781c12a14000c19491813805000145211340d451007445141170743c1041002004912030f107030181c80740d00540c1004011015441e03001d03074104141c2d843c14121072580d0008076101c2040108400c8200070b034540c84880e62851134403810300807502011502c035a000e180b60300500080020800e48420b81801c00400d080b040300c0b40c3d141030001d00140c49d500480d00c980d41c003074242400020003200019020b14100c040b03081085090b19640c542e0020449c110095500340300c200189079507002424400c4800400841d00c850348034035035181026910701d1340391520110b450325260840d00400d42d80c458a80d40040035003858441c0800d1082602d282c113036584030007002581 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 837238965 1250 837237715 837237761
    0x606031f021210031b060203040b0a020102090310140a090b0601080621030301140904021e19031109010819230609010e19030509010302031b07140d02010207030905090604 75
    0x1030b06040c002113a01a9020003030b025042000e000c1031049521500006900611050003000000c5004061400b614000103141481d5100424200780d14014994404d607a0707a01b4540c00016500521944061150410410009203945400c221403015001034100281c4500040c9162202c01103406101001c1c421140b000c904086030300d5803540309004a40300d00fa0051840e405074188540307201d004d682e005010744403c00211520b50110300c110b00e04242d20490340c03075050ad80c100383c203400040914010804500300d15050400e002c1421410b0b0b03c8a8102d51090078140000c08000400d041c0007548002c910f1809405c05243c1d0304c1c044552840281e0902404041c4000d14105520003942846103030140c92054203c24400002c9543da810040d01107042040004201e6100368001c50788030b01c1c40360302081c840c2380b801c58003000c6400c80d0204440b074001c103413a0081d000e0804c10802c8490302561000b90f282c506140d43c0245040d000e4450341e1b0050b01c4107030104075155102e070004040000140c0c030117a1005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 837240215 1250 837238965 837238981
    0x1416050109030e040e0a080304230c04060608070503060d0203030c240718170109060603060c02010605060f040e060d0602030f0411040c0906050c10060b1201080606031f0212 76
    0x1009107030850102d01c1c10800302045003018010070b00803c2d4504090007940d9415140d40901d0740c001007080b140700040700000401d0301c00010351050300810307100c0241052036400e003d0104491043d0082070510802d2800c10442940c1b050449030302540594195a44440501c0170a1440c0940c00c5031201ba40141e120011601e05075200c01041910b400c040800203498044044d113845030030721250103c00300d0001082c0802400c0d41503000d07481d0b204030000500c400041c1c441c03408440c1369030404c48501c0c2d19170340c0711341005509000f11030103000222600e925040320f651a080b1640b040c1d1049603840000c4000180c10342c0d592540304940a60800400e55581c9003c6101562010048602321444036200d140305400e07007454840c000c1c1c50b4403d5250a1540c1f8200402a01c05030482c2107240f020788540d2050407014001e50140328001c04034581d00719140d00300da5128101b6410141c205d42c2c000d42c4a40700f042204d540003c0d00c07000565000342004801411300038004003900c100d920251000c032001085c40808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 837241465 1250 837240215 837240221
    0x16020a080423040203090c01080709050607060633030906090c0b280c0209090307150b120f070905040201050c120315030105101710051311030312040314160501 70
    0x60075500032003403030b1803188208400c030f002c02e03550124182d0140e45841c1e55540038410b00742d00180c0609016a001d039441e00041ca2660281c1000c41c1c00a407202d10400c56416402e114105480c01d02800c050001c0c180d400307512b040101518514201501c500b0031a0a01815074020000c0c15002420045a980c031100f44c50840e921200031031450414542d480f401780c01d5001050554000155210404c01d01c00e078080060306171003e065002d103800300300130707e4000440035407548418034415140481c0305450101003000c104407078060001550840d901c040f00c840310104086040d5040e42d0000076194646000407140b0340104406600705200d000311344540c648514010b54030454015099100048800c003d1509030f0718283c9000d62184507052003400032881900d40880061074020486001541e128000c0040da441510000c0c01d95994507160010301584442c9004210015030007189440c5004110550011008001a0401a044861039141071500f801c4803001c2844c00e00048112500c0d061071802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 837242715 1250 837241465 837241499
    0x11506021506100513080c090606030c070803070e220b0109050d060c0905061c0506040e15070201180b06030601080102030412051c02360a140409020a03050a0c1d16020a0804 76
    0x104000c440700040050ad0b15008980c4108100ca09a030b08042070b5a99450160f00040c01150501c09440c40c0500c003900c50140d0b0082090002210b03200b250803a4100004580b50142d4503810030044010038411500c61502d10f03200f203640414009180607070303814201c0f0802c00035003100d40e001500140f412103420680d04c0d6030034102100d002c108681c0d03c80740c0c00c210032540e02c2250055590000c0c0d600c0301c00b8844a0702c01d658002c060340008294521102800600c071402c21004a81c0c90f40c41006010032400d00f00283c501504bd4600210324500703080c0c80b00c90380d000880302101c040001c0099580015816814481c5448200030800d54031040e000c1042015441c0000131240e240f80440801c0171104c0032448411a440e4001d001d0189050509082ca0310b006c402004050f000364541c0e0a000058441615030001940254003034024500c6924100e039176a0890390007481d54440b006d1640c001d40c0e0b10041c940e90407041d9a40c801018420881060341070040b216000351442501040010300745100052080e9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 837243965 1250 837242715 837242719
    0x2007030801080102090a0501181a070c093803010c03020c010c03090b012102060d0b10050705070e09100c12060506040819140708011506021506100513080c 68
    0xc0d0503a20764801508034041c1c245d10680c4030511103001c0085500070300d00c400d050f80b0001c00c42040c040d240c1c0707100280b0444c41400540300c040c002510f801440112450100503200506090005e079401511031400041c246840c404002d14250381114421041010707001102c030058003d2200c25400b41000d0025000f800c0200c202c0d508021034900198441e100f0703007413002d40c00001303820140d0810003221842c00595002803180342c00d4144c0300001d0381c0c90502400c120302042c10007082d44150780060100c20760461051509125040c844640000d90204125003a0303001e2a214101a0382e0701245640740c05112007000503110300d8901c03422661a40a08032802d6000d096100784125595941402481e00c40c501c2074102c15080940000c11061036105280b4429000b05072030761212020000441c1000c5da02e41c07007480780b40e64841c0d040d107000506040440041800e40003601001540c20914101445c000341058400d225803100195040c1c020b17802e0b0f0b000b0341e1b880e5040003440f544400d0f5803556900c5030340c6468 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 837245215 1250 837243965 837243977
    0x3030b0607150b04020c0a0b041101260402061908010e01080f060105040c020102070210031401090504021008040318030c0305010f0e0709110d11030f060609150d200703 74
    0x20800e0804000319032000e0b81c4480504510380b0618021401800003500e05944076800300089200001c0c100304905a0501402d0711072690304003403401e40980c144c0c0b0304400d81407007440307022114040f00b81c5861882c2900200707104021a581d41c800038285215080448851201d05000c0038000c6074081145816100c4903d981846640c03108003181c0e94421514080304c06a01c000c2c0140000d0401c0d4025403c0c8041ca4000035081c101a5400140a4900e4680e4034000a640700e001950070304200c0203c50048c0b1480b601081103003400e802282c070590400b040300e000d0113000004501094405e40b0320300341340c016580b85801d80f503440c0e05e8810740300d10700c03440243c03125802d0502c440e0513019076100745011211070b000245031051030158200c0c060721110700d00500f02031091000c0d029540c0076000d0046d60035414142e06560b460503040e00c0b903403d84003503c0315000b52030a1000b072005440381100700040540101c001130311400c0c03004044001d000c0710702c801c0310280030008401e1540c10b103000143c2210340c403c0e02c0311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 837246465 1250 837245215 837245231
    0x30a11120601120b03031e040b040b221523030c072a031203060e0f190c080601110106050d06050f070e03030405011101020c0a14070815010b21040605040303 69
    0x203d007030304c5541c1c9420354103030000c1140000c8451540004800283d8076610705040a940b42612100d0307400c0341d40102c2d40345400098142861161941c80c4813204500042c400d100303424840e00724410fa5100c042c41007807107440f604c194044642400fa1010a40d81d0f221001e58034a0314825040480c0c111759411513442070301706c40805c4c0d03400c041456030407250003200e0b00fa641c840c61510341c072a80705016101541850350b0345030042888143c0b1040360b8401c20040e654102c0504001d03107100c00414410a08040086c0381080b007002c00c9901400054003d1424130f4000ca1041c08007001d14010140c0d2352002d41d00c544401d072400b080200c0c90300b02c14442c0f283c2d02c000c104a950b802e841950500112302025a00d038104000c180a03660050844040348084000010705042c8500f24075490900c0c0e119080d95000c07900344401c89000001c003d854042c110403805010030390210b6400e0b10700c02206005200c4080c01c045880c103000860f00c04070a0b02c004a02c4100003850400d0300340170000b44020f490a0300042e040000c0c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 837247715 1250 837246465 837246497
    0xb0c0a240c05040b1219050901090308011d0c0f040810050720070e10173d0e0a080301180c030603080703080405070f031506060c17030a11120601 64
    0x203960455209104da280703080d03aa031420304c400c000e00401001107500a526038002e501d94900c21544038007401000000c655216090182480340164030003543c01d40c201c030400081500c29500207070000c1d40c14101c030361289201d02c00c4e08403a000d40c1e000200180704032010a101010980c0040d40901403d49075503a14942042c120f801b1204010542c0300c9962120104100103003c09042c0b0340d0042c101c1001800742610350040d00c0414041c030101c980f407035025803100000a11140c0c1c00c1d0b2490404800c00c00700740e4501600000c11400d1620980c00e002d55518000509005d05220b080c642d81e134804032039136503076850b0706002a094002c00c003440342991078000200144c0d0b001e8802c0b002034030f4004810034140303982030740c0840d050701c4000d01c1190306001e80400011f2104500800d100650300c507441d410307610101200103100b12034040d0f1008081054400d0804085050380308602d00b80c03030180710003950342d9644440304c1c000307840319807450404281d00282c2e414000048204160080703100f41c1c3d03044081d10440a07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 837248965 1250 837247715 837247717
    0xd0c021f20030a0b12010f0b010305130201050d06031e060c0e0d08030414030406110115050d200d030e18190b1318140a0b010b0c0a240c05 61
    0x150112070401e452000d880108288405181e0040f1a0800031804186643c04203414403510a174882d01c3d030703446400000b041f0200c1d00803152041c601b0300e410800c91502c19401041c0150411020b414031000242da003a01032001e40151020b550002c0100301e040c008e10080707414600d6402415200245044405e06050307114644604024400404040d0421030546602c6901c2e407000d4021612544540046202c041043c000340004100503103890f00c201807910501802d645410285000c00c1402140501c5a9035400d43d1042200d60031840320146998842190304824114200955010180c80f0750030b4101540304052880190302a1005003003000b4528a0b06914802916184000d82c051100c1817550a0640d1022000752401002c0010002c00c0418410403034900d86200319080080755503100a005801075040708907200d0100511000c0f4158450a1891106004410f24004001026004014204851050540c100303400c1d605450a428009544c0100722004412250500c400f850130b20380204 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 837250215 1250 837248965 837248981
    0x109090c1413050406020301210203031e21061e0d020f04060b070b162309041d07060f0f020304051c080d0b15030c07170d0c021f 57
    0x804403034405040004034a4038000d50359126070011001c024961951416000380d0740603600030b010060340c95042c21131651030f2504e0a00e0780907020045020100050b100001140d140001c161800c00d03441c113990171034011340e204001c500714907040c2c4e405180d84d250004a000c14080c1c0700807110140d820202e0030301c07402c0c400a036540040d1700249640255016042580350301e88034407001880041c60326102d0050442c0c0340c0214000313485c00340d649000c02c02c6000841d11883d92243d4181020b08440d04200d070000440c1c555079000c0c9540c9140482c43e01c08548941d08650380f811720030080840071038446256555502030031300c00c09000689030404604d900d4024103036200c6038485540654034145c20b04040c030030003400b00020444841000740121000c924458054513000c00d11031400b0030100c3d2054104114001460091310003507a0800c01d011800c403281c0c088030ba03070030b07404a4052600400d010840e502801054513040d0341d50f0804080c202c44980c081070296482c18052100610180300c0f1548400300e503002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 837251465 1250 837250215 837250223
    0xf0e07020d0305040f0f0201051c020304170c100b0303040902071212150528060f0f030501050d020925053403050f0c0d0909050f090309010f020a06091109010909 71
    0x8005c400c085201d1140b119650750040c1056440c142210310381000383e0540b03444460101740d001c03041c00304010303c4020540071000d140058a00700480c450605440d1440a50f0600d070542e0345074846021034074148240e90040c11116411520348142d818260651f50b00059450002a102500c81c000c03907540b0300c81d0240041409815152140c1440d05002c03c0fa80851017040d45100e4901d290711074501c0351281c2c071002d01403c0d6900c12070002e0342c090280840a04c40411400d150520300184029261510b075455090f1f01111031300029200c0d507008401c89040b0021600d00100e56001e5070590070381010040004030207960b11005405110481138100505041c09072000750040c18248011030300c10b0000d0301c0348580c4945101d29026100d01490f2510100240c140042000010104840380e401d1092a911201c451035817141c40c42c01e5041580c892203820491414004050b0800300c00ca80f00f040400100d03648900c041125511504048210308241c0024921444510001042d8000b03180a201581580 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 837252715 1250 837251465 837251483
    0x60307080712020301020c010c09030213050c070602072f1228020a0e070c120e0a05041112090304210c06081b03040b09160b040515040f0e07020d030504 67
    0x4201c58002d6404403150160f13030640d0248901d9003000420300c0b41e800220710a407120540c1a1841c814045448070b003c00c00c94070980341504201019a807101110507080c0d008000603512100752400c0106900040004d00c0c0c1120324040110034102201500d52000204603040c0391103004241c0410707074801c1c4c0140710024155030700316141c1c8036182d102e07000d140b03203440200080740b0182c9510400754140300841d82d60002915104051b014000c6000c804111000319141901c44a240040490881c0d0154822a40030340d94980a408004000205681031983c50040800a60804c9110255a504039010303901c0000c1c4101c1400180001040d010a00190f120791101d80c0c20346401400c2d01d404e41d000f0103c8403207051014a824210035010006c5200328813a1300c8400740750410110645c901000c100e0750340000d4601d008203100342c44c2d40c02d041c0d4088490849000800380408081c0c139889015079032014400c1c41e42c1d01c0010803103004d4161118440d0320150b080780c8a118181c00200e0560717605890203014080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 837253965 1250 837252715 837252719
    0x40f0c05090613030b070e01030b090403020c0d0318080f010c0203041d04030314070507050d080714090a09020f0a0e18070e0409050f0703051c02060f0702120a08010501080603070807 80
    0x5046014010444181c404860f1880d6207448105d48000201d448500050901c041c1d80c1da19a0107200c3d42548440a6442c4c548034641694040e5031040e00001091090003130f42640d0080510603030400c00040d8030841b00c1a4140e54410704290f43d00300c0c0000116455007000001c04641c3d100109035811030304074000c03211000144004444049078050015410075440791841e81ca54150409694010100782d6039040c0d641e003982c00c000d410280100441d0040002c40c60034050b003a94800b90103450040446401517643c94100005509010180c1c07001500ca0f002141e1190008849005010512003d0b00c421004403c403038204941c0c110205520304d0000f29075004181c2d01881403540e105d104002a000180d140c80c0c58403054901000c40d00541501d6001013018420000c060142200059501601010684451002a403581802404801da0840c0e0000060401d8801c100388a29014011403043c0d1b120358040c401000c4075070902929000c16a21000b2031802c1c280001c40008036010030b00a041414 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 837255215 1250 837253965 837253969
    0x172e0f0e2e0f0b0c0105070906020c1e09091e0a030f050f09090103110406050126130c0b04210b070e01030f14010504050708040c03120c0605090c040f0c0509 69
    0x10700042000d10100c841107a02140b19909090204080e0060030354107612224900c0005080d03400c028115002c0091381d840070400701d038000500607080380d0108c4424450105401c152103501c0b00040a5a9010318010113009480070040f9030010b005182d280c8505200c000b020560340c0e6003056980c000c00240d06a003001d40180c2c402c0014040d02c0300c00c80c510714a8841d10701e0005d000c000081c5c2041e506140c120a1150782c500c0d0074890712000381003e0030a4103440b070a02c80041c410071001d4068800c0c580c61080060701c0e0031410066039030402c0c0d110b09204182600d0b0b071541d481c903802500034450850900c0c1800c10b800c50b05454410311030b0b940140502d01903610b8420031030f2460fa007400842d06058655864010302c0c0c2a50240c00d0b001038480220b240d0f59894001040290b4402404500074480c0d2402070001064518110505581d04100380180700d000300d83c0100e5100c0b55030100500300e540b80030305012000c40013043c450600d6074120340600101c0d1038465450201d541c5000c082000c50402c0200c44428 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 837256465 1250 837255215 837255271
    0xe01060501180e1902030a24120609020102010e060c0405010f050922022b0f141302030c1c02030f0714040e0f0616030e0607172e0f0e 59
    0x1c2004c91254598500101805041c2c0e0400d131252000c503070b01e403008101094280a80c854003241300c44c2d41c0210042c60400704844454800c080648242c2e250703620001564001d401186001c1c079808100c030710500e00603c20a0068016000700385c0015424624001c5640c40780702600c2c1c00d2800109403070990701c03521160f0b10b00f4241094550b61000d80a021b01035050079400903450a00b00c0c034031071b01c40c01203458001e00300455005000ca52501e030301e000c0403941a044012086a840f042c00c00940303c4103101800044e00c0d0040c00162103912000f451a10b0300207a1000080b1074100c0c1c0300b6400c135104407550124150300c07500d00b8059441c8016050076941541d144c6174200c4203964105a00b900d2180c260103150030304020084a101090032031030071050454560610070003011022040c06000311b400e1003130700200301c6001c0e4541c2a88110180740404c80782108007400c1000f420f100b0041451400e0f4820103a18030407014422101e5070b07a10078000042c0e400d010391150788215007072000003c02500403482c124003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 837257715 1250 837256465 837256471
    0x1204180e010605060a0203040602060c0f091002011503060b0102010c08070e040903120c05040f06110705040915140106020f01051e0705071401020310150e01050d02090604090e01060501180e 83
    0x7592218400245911904000c4c451039039240d01442d50303075051060103480d042016001400c01e240412440d0300c0b5081540c10b03181045030484203007550700d0103a02c0403400f4222038410b68410328000c1c84000204503d950114003500005c0e0000e02a025411006a40309107040314101c000c03034580700f0044a02e00e003540c4010250b03407007420805078010240180b102156602c0c1000000f00e0000241801600d0003e200e600003000d1503d4003000101d00350b82140c3c0c80780000c1c41b4441c041c984034a8103108106105402020311204003404000301030303104502501d2a0020322980015000740400d00c03641702d5040c0a0184180e0803003030003080c021002c1205c0d1005540090013882042014403000001402d01510101036502c0d2000158590814660081600b0400c0c1e02811410307017100100c00005401c04624102d07071b2024202a6258090b002c10000a445028038032a0300c000c001502184503065584080480780da910002c003d942e440304015208140d0703a9501074020044407800f001500048100107038 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 837258965 1250 837257715 837257741
    0x62c0a14150f0307080c0f0f132c0705250212100504031803150509030912010501090e01231e0408031906050d0201110a080318120418 59
    0x380a00000e040341240c1040b060018080d100000340807443d07512544858011401d101c03102d14004004403131781d007980300f21714098003141c5002c40d4440019101d0705000000700684a8413100b1031002d0001c41c80580354040050000f50341c00c4003c24920303440303001980c0110720030110400201110384d421131804603d024089a0012005074480000703802031042c20340c1d40d01c0d003040101d101c0c01c003482e01030403080c22040d603032900181900f010004284000c4401c111040361040010350340e2503643c80c0c0b07400c500c228100c0b2072300034a40b9a040d0402480c15031020341240d002a0040250140d00301ca100c0c01d03036140320030540303991424440b042000026007540700e800c9200f0040702e0400051112154180e088212002e940582010003000703060043e03042c0012081c003064001b000024284400600c140c140c11038040d04021883c1c2c5150414001006048070541e00b00c13112540764602040c100940c1e00090f00d50b000d503809268420200d46038500156000e840b0b410040f503030070700c80000014000389001e100d541 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 837260215 1250 837258965 837258979
    0x3060b160609230a0507090203060901091a09100f140904170403021507120314130311060f041509170903100501062c0a0501030213080106062c0a14 65
    0x5842d00e000000ea40041a01d002c1c044c000322401e50505a041c40301c103502c4444e4407401001004042e94441c200380c1c1c1520001c000010b1070541c4106a00b00345115109a0f07500078007448240045000c5000c0840c0444a00b1402c2072000c42d20f03111000100101c00605076081405000800c00184201c2a070640d0744828a402c5818130360340380c00141c01504000412184100000b0f01c0009200c0e1011640340807105600301800004000308506802c1a001071840f01c219000d500c0d404101407003a410903050780000c00403100d0310708000c1f0380c08075401c0c1e00741c0c1c045460010601e0590400314580c09890300440e08141100c00d881802841100e00790300600c1c00c2d03075142c0030701d10080244104601c11345028010b680d803240f50b03801c1d084211071030303518403240300f40f6011021010500c1e5583d00c1400c1c0e04151842840e0258580800102d41e1a10300c0d565085080507500f412004544d130f5900038110b41015100d0307000c0f2800540f2150503d031096a04032806500b08d103c3c07640a0003074140c0075904280e50f9002404c48 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 837261465 1250 837260215 837260243
    0xf0d1116031709131e0c03021305090a0b03010f05060a0608041106030406090f1208130b010306020706021303110103060f0e1f050d1a0606030105031905070515030703060b160609 78
    0x4080320014038104d00c2d203201c1c0350b0300100360704080d101d100c244540c1da040440c50440e2440049d140122188034880c403920541c1c0000d070344c400c4190041000c07044044d00030700c00c0620700c242d5000074181c100c07a000d01031034032520700081d01881032400a005540143c035103032580d2514002c3c8001540018025220551a884240001061071204072009806480d5035a4069070b810b00050450a000d8803144907409100140c402141c00306412904480c4e000c1c100582d64a56850820064040c0701c01100c034005904100005000c2d210080710303501082641d040050300e844c1d0000d680d00902600440118031a400000303004010f1190500c2140d83d1002d8506a0440d40c1d48002150041c02d1002102d00d1501451522248080e818440717400030f00c119802030a5604020110760b40700202c3d500d40d44048200b20000e41070180510640000e41005000005215441c4250480e50f81c415911000000c3c40e00c500042c2d202c255106a40502a450b4001c60080c035a40d00c0c0c4801400c00c0082c1035440c01c500e5082 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 837262715 1250 837261465 837261499
    0xb090c06121005060d0f050c090f010804020409020405011d06100f0c030909150915151d09010605190306060207060315090204120308070e150a020f0d1116031709 71
    0xd03000458080c903021884068006c00d51060390740182a14602c0802400205203603503c3d40c110440500d401e191456081d80c1e10f0000a010b81089a4003075082071030400086030244100c0f0b611607811701028500c04003611507000b40310941e15401d040000094507800175105c1c0d18811015048054040e01c0c1045019448081103001c480e4031621f0610b44038507101007001310101e240102000340c0340440c054118245045146241003030b00441d1141040784000c00c0359031342200c030070200385406070240861a40b0b41c0c440001070803070341c4144034821003089401c107242c2c0344901c030303025080690b16154003502c0c4030781c6000000c6d400340080100e0103c2400801c1c802042803071140c030280c4000c1c000300c00102e010302d409080c06084140041d00d1001003100c100120307030f145c1c0c85080400c29554030440700035549000100c0228244228602900786070f02410342092211507008030265140107006003a40c80700c001034a100700034094540f00040c40742900307048000c0d030b54506001416188101410542d030030011401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 837263965 1250 837262715 837262717
    0x2b0201120e15071106091b010504031505150303270103020903011103060a0f0e1501050f0a09050306070e1c0f080c01140601110c121006120b090c0612100506 69
    0x16000c021812520104819190f04c41c02e103844080700c900290206040c00100140c0b94002c50300b4140440000041014869100310200c40003550429041c0d0b44400300d03c0310b0030003d400e0984800c0204d5104580c81e0709280740c088200c0388400c690142081c0c90350750800181c401084150046418103509210802e1203807000e00404072414140500070355a4a40031081016090741600030f650594491038050180740114103040741c115650044030107070160f40e100104c03440e101b2150103260502c00450840311a91b084603807075090b96011401d45109a40d140c900302c078031200d01700b8030690102c0c42180e40d174a51035042c000c0c0403840d4003a84d20900e8002c1d40d03031a1860b82d0b0307128190500450b075548004071740d00c46081c0451604a2400d181061010300f0641c14070307a036202a0700302148200d50191008a1100c001c2212544108114000b40501a0b0701c0d0583d50360081025015940d00840c8000118a0080410002344082c03008080900b400c07040903020140290092003042007001450b8003081070340c2c64030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 837265215 1250 837263965 837263983
    0x3031d010c050306031014010b16120c021f0c0206070221060a0e07141e0a090e0606090601050712090306020d06050f0d0201020303011e150c022b0201120e 68
    0x526440e58034140035050501d4009144006c01c01c440c0f0703001201e0307400d9004921150440744256011502e40500d10310f80755442411110080800d10465110700b6041e03000709a00c13032068000c55414a40c0140710b82e2140358041d1388441c060029605040000c01803902c240078250090020300441d440b648801d81c1d0042000240544000b56030011040040390b040a004100da04400c10010b059118500b080d0002c140200c65411031103841a10712402a000e400001450071030001842646502e070b42e02c00d500300070701c1d0210310311101c0d01031100011070724201a12000d008003410703900e152501100c2d8948103451070010b070502c410004003080020200e4040e0001c0c1200075020b8400040a6141008004079103203400ea0040c0190034402036800981e030040103403411a0200c100040c0b400103502c1c1c1015415000c0d401042008254100e002c84555000710641500b074400c0c0e80448030b40c40140390105001100c0030251840294001d5080d0065108400c242c0220f459101c0c00304504000c3c190362030405c000c00e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 837266465 1250 837265215 837265217
    0xc0106050603150a140d080c031e040f170c0607292203140310120c080f070b04051e1f0206060d0206030103060e120d0b030c010504050d03031d010c 65
    0x103000e401909190000d40d0328010017406201c4c02c500840180841e4900742d24403c094200c1d94041815200700d80c06008603007541e00410308404011042c060f0214454026000e9a50b00b04102d450200d0034910115201000c810a6802040c160f40c440341001401d512280084400d0f0041c22003d03a80039556403a170000400000b4440091450210b030088034020f8006140c10520070740b10700540202c3e4010601203204044082003ea03203640b01c002002c07101c40140c1c80b0792481112181d81400b44100c50b0303401010740303007910103440e0f2504080510fa9910580c600644004240801040001d840e1000c0e0380da0074540d02c103004001204a101c0000c0069818072044054181c0700c1c041044019810b2000580c4101c3c204c44c00d2009010a40204941d4001400010070150760390006e0074458034104850b0080344c12080400c0e60740d287d844040f4018040041c41c0c2806441250721400840d0701420984040e940d000c0c11804883c1116241180646443c045510719129000042c0000003070070302403041101c0701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 837267715 1250 837266465 837266491
    0xc0b160c1b08010c0e01080619170109140105010b031603150b0c0f0303010b04030b091c09060e060909040308270114150904080706020f0307030e0606031f020c0106050603 75
    0x5010342c06420740b140d0320341400420007120900407007680c00c8440284c0191090700c0c04540d801c04d2054225004005422500100001c1c016940c00c1190540150030401d1144603031000704858840400c1c01d8600038083d11507000024800510014411a6104040842485d010880c10001a071151540495400c4140344800c000b82c1c40741d001c6010030000c5518800c10000350300c0d541c50401105442d000c0c40c00014410046500854502c08040044560099100e0000c1e04072205801e0060801c0c3c00c5807149101103080020107010b107141c4082540c0c1100d101802d00c54283c1e881e550111914a00240031415841d100c40001130341d1100c0886030035200f60f41d0000060030b1016290b20944100d80140b000740c2c0003189105000e40f90305ca1405180e041548208102c0e110156860900c010f07000e1052030000114000c81040703c0d4a9064001c2c1607500800303815142c0e0307074603860241500c40b03090801400c1e40018954440c5600150307075009251400d0040f0000440360303110000141c2c96807054405103100b040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 837268965 1250 837267715 837267719
    0x30305250b1003021e01021c050c1203090d020105060306040b0601030e060103031d04050105100309080403060e0d032304110312071110051303230a050a120c0b160c1b 73
    0x208400c541c0c848117000d0040c8242100c0c4040001d580380c1600390141c00d0f64921564503080c150040c010340e280c02546034144e50003101c400c1c0c400021504202c40340d14072031043c62107502c0424018859180244c0024021341000e640f1600c880707041d1580648014105503461000e070603589030900c126406503101c0d0f960002c0003c44040a440d8440001407640d100b6441c1c000100401d80d100c030000b01d80c2c45178904000ca00000e05060207941401207074000b03487e0904041e0403441c3e101c00410004110185520100101542c0b4245920301242404250f01c0c10030f048408103000c249125554400f2103001800c40344810b03c00c0600c40030a801009040300c4082c40801d4001140c07400c01039006600c503a91400350305156058800d4022100c06200160000000d001e0b1a08050190bd900410849064044034030385400c40c50065900c941e401c1056030054207a04005134614441e01d10f180100b600405482d405403908000d100150162105070030a0004510000c0700080e0750011400e90480034420410f200c1d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 837270215 1250 837268965 837268969
    0x4061506021605131b0c061503022d040c020c040e0a030c03030c030b0a120308010e15040509030c01060e011811040b030411040e010207061104030305250b100302 71
    0x11056003000d41990401004900781c032101480c1c0c4001c54008440040f00c580400c0410f00080800120050440e900c116840000b0354006c020807040c02d100314800c000c2c50096002490120055000095000c0c0c1800240800c6c07154110301034228024101441000b64001000a01240c0401080030003603042815030016515007481000c044110039030241070307154103940e0001c0415445450040615565454498909109900c81024100c014082c40c550341c7d00c6804c800544140c00ca4110006801100046801c071200c02440c1c1c010420703014650141100b41d030802c005828001c0c00380c511440180403e0041a109000c0c041c0240394518030105954100b00c0c0c00d03c11801c45840b514074081c02d050141200c08010012103045900908415840b61070b00d14000d25141c0c0c1c0c0320313101d607030207802d1440d00780340c002d019030003005010301c107500410034251404c5100c46d660040e0302c4050040303130742231000e400a00a101188061030401e40035504c0c80707440c0d83d070700d50f0340c0d507076040d0303003502c044156140c0510441c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 837271465 1250 837270215 837270251
    0xb07050d030204050f103b0a030803071d030a03050c0f0d0210090206070209151c0305072a0e010611150604050c04030807150b01030b030703080c0708070902090a05100c030503060d0b0406 82
    0x10340740032303107400c0d16160440c0ca4a0189200c041c04901c200501c000e4010b0720003840818560148400500b40c503019000d50a00901540080040701e03c0741c019500751940b04c0b2070009410047d030240380c020b0201e40040b54a04401002e1201c0107a801c54800c00400d40140d070b8211109100e80c04020b03140b580704c1080310a00142e81076007001405608040b0074400c0c0030a030890195546241d000c25070003811600d901d2007040141014081880c030564011010a800b40380741c0e0454123840c21562816441c03520498400d64a1003008540c0030040d18000c081415401e154101c01d51003010f940599162903074039580c0103810707489080141d81010300a840e5a0040316980680c0e03402c01824a01030041d108204000b0f519404507100051a803500003641d140140c4051051400500d02c0f0b0054420b0250b84800d00f0010350f01c2001003611404100b07001254914080083d240c01002d140d03070700d40c1002c1d0349940035202644040c140340c1c0d1083c0b00c00c6010002801004080e0311a0380b10700d50200d400c0924032048205 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 837272715 1250 837271465 837271577
    0xb070516140f060f0c1e0a09140102120d0209120f01020405010e040e0c0d0302010b030f01050f0a09081905040504020301030302010c0908010b0d1e020a0b07050d030204050f10 77
    0x6a04041c3c2802030f90111078030a82c0d044058071110541d1407400c24040404078409a076070200d11000402d09508450304011820222001000c1d40c1d13500100034001240c40320208400405445800e205526904400b80d0145c914810f0113006111111000c20b20305140200482072500d481c2c6d00000d05006550340308541044641081c0e900384400064102d903a6101e030355004650740114480001310301454401d420000442c01b01405640840c080016800d010b81000c072040613a4408010214003400007030b10411840c250007070030540c1007400345290300c4040d000050041042001c01d0001040070346c0e0701e10003140214820303000001c8400222102601580c04c503800900749034908040241d00e034071002c651a0449038800c4140c0d003001164040c0307040b030400f210030107034010304071000100d500c48010004003249406a8205c8207502c020f404124164451070040b6600014940c4040c8a5401c100c000b4084220f414200003210301c904d100612a6001d0190004407112480300ca08508800003c0e42c103c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 837273965 1250 837272715 837272743
    0xa060b010201110a030507020106031e031b0812090c090a0e0f0a0302030904020906040905010801051b0a09030f030c06050a020918040b010605130306110d05090105040c030b07051614 80
    0x2c003c201421421030540540c941040c103250b26000003a189138400c0d8004000307540d22042d005884280c4544520440341a00d404030003058018014051810100050302d41c065444415031345481c1c10ba182c0151108030107011043c140c07207a1403c036151a80c820801d14400c115a05001410001841c01d8915203155005020304a40240100c1c04c0480e034040304072044118107031805656800d20401140140c8030755800450b07200d143c40000325014034107410140c000d041821061084248041c0c150105225400700c040101d0007056040002a6860998659484c02410403094000d15070300c603541521000c4030241281a400251044a440c040749001401201e182c0716985030f14082d17480342c1c0914018042c2005008001c0360082d08076020010540255078000014070104121100c0c200e07a40e0480e00d0101d000906040015900550510442e8456600321440a040c0361564841d00d1801801030000000c201007041522511204461030528852084401d4014411401c1c515420000780001c506 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 837275215 1250 837273965 837273971
    0xf0b041a190b060c07030c0f0b040b19030207020612010f0b0703050904090602071401050103020112270503040801140412020706020a1212050c0706050604061a2a0a060b010201 77
    0x20035400c03a03500e080305001e40520300007103510104000402074040e801c405070030380c822208080b0402107107800100840d10515018a06a500d61350140110300503801070f480b043d20300380f110036400305030100c509128076401e0400500d024650f8001c41c400e603000740c03858003610600b0070040046184881c1c1903c024504940158140980b541c6c0003401c91180341007544c03003541c0b600c462205204440d4100d80040c0e0f400109403004907900c0d00064046c2400f484140e0105d80420003e90202110340124181c0440414a099043d24038801a510414a000c4140e44920080c000030601601c24410720040907020000f501082c0341c10b10b071003000304030301440310b201310340002e54200440b9400040701581158400341840c032021080c6030450b24409150718400c5200d041806010064140304e0007003817003034000c1c142400580c3e05d082c1400700707454142c071034001c050488541d549103607183c0d8030280c0003507034444206081c10158844a0007052414402612a641110101804101aa10070100b00c021300380024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 837276465 1250 837275215 837275221
    0x120c0e090a030e060405030a0b0712110406030218060a05091507170d020d1a010f03050601051c0207060203090309090106090302030d030905010e0a030f0909150519030f0b041a 77
    0x159150302410780000d06210440e24600526902d0302c090b0381c05000b0180455103a41c28038142001008401c1c0c4540c1d01080c00200b051258104601400c10480ca52400681c541850000c0481c0294402505c0118003402e0544c20f0382c443c0d450800504003541c055841a45580546c0308104206100080411207003c0421403c00050500946004902e0040c8600c1c2c1d04da4900e00f01e9500170388585855085428908000f0138492a205140400046420780c0c03184c8140140c050309608540c0191034850116070305009040e0b25038203d80511841d00c1c001d000240c10a00c8a681301d1042e0f0b04107a8030350700c15420208180b8141d05010756100e0042c055440c0c0342d082a46940c01007030b1200d603503410b4131041540f200c10100c24401d00350855038607054640201d8115044c0d9040040c48907400c844400d00080641000040504150042050002001404111b89403410040205c900c0041c0c248a0004951201c000045001d0a42c50000103014140720140703458a45454030400314882c40090642e0802014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 837277715 1250 837276465 837276481
    0x1090c0c0b0114030f01060303021605062704020c03370509041a030a0f0203060703020f0d230f040c05090717071407031d0405071205040f0c120c0e 65
    0x149904640081c4224265007280d040840c2c01e09980d10080c545c0c640c00d1500000806a00081508040300280d004407000c030389420400903a03100e40302c0070103107010403200d1440702c080010b01c07403454041e0b00420061401d500306100e035086411503040c038404402c038610307021a040c02c50029105000c0c0740405110345003407100b40c05060380c05485074581c00780d0b80c0c5502024440b04403080c14002c07064004c003107030500c070070034903216020b1014040100c0c0640600000714002d41d01078025940300690f840ca01501780703680e108600c00100140c1e001043c0300100d1b240e002c4103101d29001100d02a00180704030905924150401001c80b014903030149005a085200700240f00358850a5005400c1c44104501d4840e01e4295040b20002d901c0c0c1d82e100f40044000509208068101c0c000d40081c40402c00a078110038002000c00c0200d50040303d2050210342d451100c800c0c44449644a294041d10a0041618444464480c40707003542c0b21b034100d10b82400c404030b200c1051000a51001009080320703103501d4014030b0046a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 837278965 1250 837277715 837277733
    0x1107090e03190309020904060b011205280207230106050f06041715240a12020909070f12210504050d1104050f10080303040206040e0a020c0109050601090c0c 69
    0x200d200050310b60070b00e800c0c0602d01c290091071100e60002d1800c50301d0308290912a004010030001c041c00308401c10190313162401103006141c4104a852801c0c19680e04099500050450b03101a81d98850f900300b28180c002030001034038010855118081d0401516a100c446003141d600c0d8003c2803194030094400d09060381c5070b00484042d1003128000101c0011605019490200c08040c1e81c16543e001004020710110803040101d0701e103015a0021815242c010300384040b504450017804205818844daa0b8054185800e40030b4110094404030340c0030a60300c0c1d4403403090003255080710200c2e00101303862405100b0000c0f801c948041c10954004ea00c00700c140c001600c81d104522499002e03400c0001d0711000d01c0074041a88141142c0944148118649800303407101092040b1000c1c00f8402810070049000302000040d00d1055a000d4951850700d400d00c9010410018001c000580598003084541c2103980280107001886210303800030074055043c80b521405030b44101e9649420041c04040c10804034403494 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 837280215 1250 837278965 837278977
    0xe1903080a350a39090806040302030d1a0904060b1302030a0e0708070b0f030a06080f1e0111040905130b04050309090703090b060f0a12031107090e03 66
    0x30410480301007042020003045510a030310041d03050b2001e07001c28070203802c0d03141c007900ca0304008000300020b218505240d1080c85070014491114001c0700c4024090788004001840c100c2e0070350420004481d9210105450480d00301c5040300160800701d070480d40d11010707008540c600d100c03141080e403050b038944001c0f403024030000384040d04481c0c4039905000b0a4807a10300803503d912001c00e0565492800d0050540a05409114481203104402002600c803c0118400c0b06072902c10000f2807900074051282c0c049034001503c0384460669401000580c4c080c2080074800080f030800243c080d03980d9850040c0700d5040304890326180b82c0d0401080d00f445001d060704490a0781d205450010b402c0c0c84510400c00000042c0500402e030004030b9041c48140f000000107044100400c5600101d40e90720b8003c110280c1d0351107440144000e54403000f00b912490300b005403508003040036001d484104e5031255450380501000d0802c0d004943c20f41e2003042c40000501030007016240540341840040910700107203640384550 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 837281465 1250 837280215 837280217
    0xb0c0d110604170d24090b030a060e070b0c0a03020c0f0112020c030f0c07030b0c12040209040212010c09140901031a090111040b030708070e03070b280e1903080a 71
    0x400000780300c0c000f0410907103050b1164080e0070400c81e101c80c1048140c0d214040704035041c4030001c9400094504250060310302c203050142c0a40b4150744607540382c001602d050610aa8140211400401d8034dd41030000741404403071080040280c8001800c0203402d109040581038001c035680c000412160760803440c8402e00c0c0300d8140005036941982c3c40d4180c150700415941000c5c05030b00213031044243c2c00004962050b0380c020741c1c2d0b00411b074880054019061081480720f01401095100080c00351408401c4a9801400540003861521031111810b007103803810003055004c03c0c0000d2050011f090180070010340e604007500c00004a5066071100e019260407182210205d00a44000602990082d000706550300030b840034194031a51104510b0000d03400466600c0005034100000030002407140150741c2d6502d4025000d07008490030014148284d07444a003d080d03100c1c6442c03a4404400440d80c140074406e160075661401c2850412007000078900e40791000ba009089148070601c00300c2c2400046800b5060a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 837282715 1250 837281465 837281483
    0xf050a0603061401031110050c0601060216060e030c100c0213051603060302091f15030603141b240301030f1e12030c0908160512071208220b0c0d110604 67
    0x287c00c104840a1081040900c800d00a031000060700342e40018190102100000d141507138151520422140414604403555040e48421002201800d00c986490040c01c41460140640c6400d41c0101c0d02403402030051100b001c0c2c0c0c1e0401c00c500b41d5104501e401c22161146014000f8915540014000800c041c100c0d201c000c0009010407090b4142ca81032900501080e142950304402c0e060300540249002c2c07009580c9400c850f030741039050920120740c20100008403480301d50b500544d442401072106448082204403a01458022a03810070034025500940c4510705a001d44152864801c601c8500d403410740c0c945150800c000c000007528407502440e41607003440d00142c0d00803409821100c10405601480b458000c45440d0304c0c98801140b4080b00341c500a540120b0040203281110344d07a0082881103075521140c1c006050001412280240000340720202140341d01000840c91000011044d400350010b9840000c1c0700039010070034881041d80f0981c83c20311030204840d079034071581c41304001403008161605c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 837283965 1250 837282715 837282739
    0x151d0d20150c0c0f060609010f03031b08040503030714010b040c120506010207090e010b0f03061009021e04060503090610030c140d080301060f0207050307060203040611010f050a06030614010311 85
    0xd0700c400d440f4401420000c41e507402c401d8186041d02c0710010745151303026090720000070800140c140204800c40c2c2d8103503943e08424007030085900f90701140440031950170f08208400906594100013a20310a40500491070b80894080582803c564070301c82818059800c1040b080090ba40080e1941c4500003016004145503480d140104d0808010303402c200b6455152404101c12814158400d008022080d1903090008074861700305680e4000440300c0000d5516828418888021140c0280c0043d4503500d1ba081e028821640418000340c1040d00040b00042000c0304010b12510100601900a281d010307007454000d056850700c41a2108034021195540ba40c103050003010384034a51000da040781c01c0030883c2d441c0e58492a0041c0220350760303401c960040c0704188011038a4a00412164112401500118039262501e2003d591034080004c441d040e9541e0390f174045240720b07094003800d48164029000003030302e80d04500c0d00310100c61000c1c3c15412090039140040c800150041c060150000c0100c40a1401007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 837285215 1250 837283965 837283981
    0x1b05041401062a150203091b030c04090303140705030708010f0b192f0c030f0a0609050304030503070b06041802010906350405010b100c151d0d2015 65
    0x352204500130442580e02d0207040070035900394041c6001d420103009940c05c1c20150f1448540c0b2220041c1082d9058015010f400e105141a600558501d4030905000c03424650340800401201d02c00c0f2082404139000104009807950b01c110750341e015120b446407826281e41000d1103100c0900902c1e00031b00c020b08003070070040c0d000f0703000306030201e00300100c11944c804c24000c145111040b4032540c01248440d10032030422404038580842c0c43c2a41c00c0c2079000409007001c064031381e41d000d0aa0a04161418001000003001144d4248014412240543c0c0c0c00510303401c048040c0021a0f01d440c03a40d14401e03d0713030119100141c0e800f6001404894407031400c0c0e1160100c0551440d407040c002d1340c9101c025220b104101c0c140305d650b102d1075403007a4064802005140040000e01441700201900b050004c0d00c0540d045001550290702c900740364414a00000d900c00340c0c00308003685000006001c84c1c0c04e074803807818580c9913136201502d040c107918940c1c1d4002010420410107075031040d98200c100038400c2d2a0740024091 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 837286465 1250 837285215 837285287
    0x121106010e0a1a030f0a02100903080d050c0403080a02061605040b122211040c08010b0706021809071d01090807090e0a0203010c0c0c0f050114090d1b0504140106 71
    0x1003d0010180c512240d03910446550b107082c007220880c040c0311280c5034110101c0c0207190103000c99821120300d0303161148100ea4076000748001018000e402c035003404048003285080002e031152103130a80003880141001c04c2c4030003207035041c034002c5d1042040403c024041c55501d41c00382c1e48500d44295801415840d4005102003182d00e10000504408801d0100c0e4280540c0b0f82000b03080ea0001d89040000719070501080b1103c2c00b003409030500096040082c03c00298140c1d00801c048160702010390303d0b81d85500000f4210440c1514000300141110900704a020000300e918100400300742480c2410a162220107502d4080c81e1040042d100d64824140388200c100b03000800555034014000c00011000040240c4618410f00058941d80d4030008046400601c028507441a942c2c142c440c40c00c0f5180c103140304580f03940860141900210012103c0e0002000516903200c0074505501e01c0030b2443c2000140001c80b5404d0707800740520081880100a0160086c602521101c0340b40b2102c00c9110711342c0031000c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 837287715 1250 837286465 837286511
    0x405060a0b13031728032a080a0b010e040b190815090a030806060f1c06090e031911120f04030309122d0b0103121106010e0a 55
    0x29200000038000c0c05050b00d41c425006803841030107480f25489140206075400d000f5041600c0e51615865111640c0c0c44401900c000c2c004414940407490803c0e51440350040200c6900015203500b1040d1346c0200c040e0480d11855000c0d811070820420009040c0008294184000340e41c1d01503503541410302140d0310760108030b0f00781101440441c0d0300196a8201d10b43c0e503400858644840c0c003102404514444404280c90030007540559450f00342c2d88400d000c11589510000d60005610800c00c202d84005c9107007803d00380d4180020b07a0019030030b85041031103025100c409080768503540007041300f0002d0002d184ea4021040700e8500c0c12036408440f16600929010151004a0081c000030500c0400141040700610030b0320b01c01d5036410107440d03072121a180c07034130740000004000c244009045017810b014108030b40c1c00121040060b41901c0c41e20385401d08004400c1e041521207459809944000b1034004980100300800040100a95071400441096181010703103035605ca0307511403140c883c080380b541080402c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 837288965 1250 837287715 837287729
    0x31020f0706110d050c16060c1101140a0c030902030601170f1605100908061f0b0a0504051905091605040509190c0f0504030f062c100902010c020405060a 67
    0x4000c0b060b9001600a8100c0d08040c480f041c1410300040e200f03081c240507248954028002011450344680d2908094955143d0040810650b40c0403000c0200b4240225000c0d10310158200d1858141818440240d0b1500c0c1d90755800d26040c800c5420050710001001e50454030018000300b00860303a510050308103a2403c42c00c91241c4100001c07101080011b44100c0102c0708100c0e007542041c172150704203130f48a400511400c000c0350440700000702482118007401885105820062200c1c54a45144801e113411582d01d880c00590041810b0003d0b081c4003d4107142e41d181440c0700b0045030315000c00030341c14a0000704085403511806800c05110f50140094034050a00100000d8143c90500343e8260403005008aa01d0b1043c1051801c2c00442d0180c880c0b142c42180f2551481d241606648604043d5103842d402283c0e142d1740d90040c16803440e40b82c9004444200b0380091040c0c00450241414179040070b10480c01c1401d40f0b0411081e00507070b04403c184046680c10384000c01c091380c502d000900e0300d0645520900c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 837290215 1250 837288965 837288971
    0x62e0e0a0b240f040b0c030406080901090804031407050a0f0504051b07031202040e042d022808070e090d080f040b1e0403050c070905010b0d09051e0c31020f0706 71
    0x7415602d011002d081075402700d5607411119503034800f082d403e81d03002540261030342d14100310074030101e440000440944002d99080342c00003942c1d180403a0036400258015000c01c902850180700918180c09080d8202e030281500350240c0c1d81030f4444080310711985c20024284900f0301c0c02191802c400390161001071049548940e40791606042c040191002e400714208214100c2420391b404644c0c480300380320030a0300503114032221620600085070205031842440083d03e0b0501d030010b41000c040105034083e0180a210103154140794500520b840003144851003480100d034200110031800244007540250801c220f5240d5441d680f8501030131007441c1801c0c07140c11100704100414503820400814a900003917045903801c680d60b2401404644081c0601c42c80450200900040c0d41037139040a03101602400640741c20b190502a20581e0050000400780640c100d00b890784e03c02e142500003081810041e06c49140e1102810500720003150500c015107803410790100c3c2d012460b030038240c1615102c45d1b20176010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 837291465 1250 837290215 837290227
    0x30c120c0a060906090201080a02160204020306010e04060801090b010501020f060c160206160c080c0a0909020f42031308042105011d062e0e0a0b240f040b 68
    0x142c0c00b801404000347c1c04948144040b900c440c0c0148200e400350001d00c3c0741c0306101da1040d801c01c0065031001d0003240c10803406d0380507501150f03224070601004090103000022003110520f04001085016072205056411003810a003282d0008114580e1041603030b600f00d66116101580407550484151020790002004900d00c0f004010500d00713200514010180800032503521608a81da82c0d8013513000640010300306604205207401a00200c202510003051100c46007480c5012441501030044180181c9900036050b0401b0807070909255603080c8005419130a080104540302c82ca03100c054071480015080c8030012051110040c02d44002c0d009444003115004680c180541080d940c142c01075445501c0e000351030000c03180d01c0000607006400c0102800140e901d5910110100e2074a00014580e850000341900f48586c032a070402c0c01034007801c802101c00f410b00403920700c12034007442d140383d028440030f283d00c410b03c0c085034030301262000d04107075203554900c1b555000550600440d0f01403d08940c0100305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 837292715 1250 837291465 837291473
    0x50405160b1201080d120b040e0a08270114070f0507080708010b03010506030c0d06110a0309060e0606130c09170120030c03011401030e100f0608030c120c0a0609 71
    0x288422451000c0c01000340e600c425503a0384602d0740720b040c000825034a07811510303543c000c2c1e000403507c0304d4000d02c0007402c0311242d00c04a0034000c1c43da0085404604c001550384c0c6d400e900d81031100c917414079014540a50306004c40080c1c0030a5405061161441d40403941c0c0040003601c16400c0c00d01c9a000c402d44290070b50742d442203a03071040d9901032911654200400e080540c02c05200700d603c0380200400500454a40300180201090f81c40e5065603015191307881d4820081110004020030b1b106a500020380407000e041000c2180c01c030024200c000d8101d54240862552001da8000c9010030b800b100084204a5820a4403211001e031300406410750b424104220f510010f41c002e040d000d0003400350a40d18904d60014101520046807240c45415060005004202d50519042403c44d01814001240401c0488003450204180910786e0070a0319903d1803102800c00740078050041c40b2040085091103c860b00d072076100e4100b500200804480030543e0318801030300b0088072552641010341041004401c5c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 837293965 1250 837292715 837292717
    0xc100305011a130b0309030c030406020a02091312110f150f0106050c0a2d060b1504051f0e0d0f0b0708010602031206011404080a12140d050405160b 65
    0x10a0001000d03191580300b101044000031940a50303d02e40031a00074a00b4241c03e980c1640005e4a02e00a030321007070141882071b0340100000c1c07028164540082001c00e400e07104100300140300030280280403200d4042180050040030a040541c0d155003005207100c00c0e001d501c1da1501040104051442c800c211903800d019014026442c0500401a10a040b40c1e803a02d4080e40d1a00c920031485840f684546a000c010984402c514003040403030190200e4140340107880da448401203800700b52485580e48101c51218907007181c0110b80784440c1c980803414140340c1070004102008076685410310b600092030805146214100405000c40001d05100c00a140c60802c11098104c843d4100e52801c41d005c0400c144501a4034454100c0301294015860520310049412400e240a03083c01d05001d003007a41501023503440c8015002400b407510080090415506280e42803c4085000700140888a005a00c0c442c0350b400403180200342d20f10002ca2180c681d032805501e4010040080c40051000c45000704107118000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 837295215 1250 837293965 837293969
    0x1c091e030915081e060307180e10050702030702150c030a08070e030c130c1404090b19140d08040305150402030d0f050a1103041805072607110c10030501 67
    0x5940b240300e40701d10120030750b0400303c1503604a2004910032005140c81d20100840781d0303c0709000d0107841d240e03a81c4165464001d5521010802903588440092416480420804904c01c0c043c03032090000c3c0c01d03c494081d45910846e0300203801400341800000310901c2c004101d421100000c81182e03581c5a08a80090074200c081d1209070001e404509a2002403400054202620350000c0c1403501805d074405940300140032405d018410300c40300f10380c041c0d0221b402ca40a007000f84040c0780040380c1c1301a64010003507148079441841040d20510503040c4000000c1181621902c031058912007045056420201c1c03c0c0d009941c00246107102d286648041c108000e55031030301440c803e80440d03d42c010606000d4a0385c82c0010300403c0054000e12200100c184a80c031180c07800d8140c181900c0c0307020f84628141e002c620f05070b50007110454a0b0803d0140c0c2c2a80081d103150052814025188030301441ca09080105402a00c0e410421400001d20b0003c0c207410b00128079000001030003008240c8020340044d0141c5024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 837296465 1250 837295215 837295229
    0xc03020a08210a0219150609021801030903121112010605190e040605180912070305040909061823030c10180b01061106010603021c091e0309 62
    0x400c0004188100046a52a107080c2c01419030a54003072a58031806900440401c0c0114814100140d801520503450010514010412040090020300810003a24048d5104000d40740c4100082d1400c42480140c0340380b19142442d001c50984c0b42030400b1a012940c1000707110100380780c59915501d01305180d0043c9140c903260880020b46a990320010344882c080c2401000e01c166210550090052081120300c0c3e6000000b8030000d41030f81c5400100c1d41920b007015000d00d60040850900485000400c09043c240da4a01403543c0b074030401c0e950040c032a000350b01c9842d09060b10341c00d00800b04a0107030004484051806200e20360f485640c14520610a40003d4503a5222205180f205401502000b01d6200000e1100180f052940492100d8001c19041b20740e101524103410409000450861034240200410b50361028403500d4444030604040040c0d11001c1414410054420090f102042d049403914007010002109106070404980200c608003ca101484c0020745500c00c154201d80101d041e1040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 837297715 1250 837296465 837296479
    0xa3f08040314030108100902061605030c010510031205030a180f020a0501031a09060a03140708060f06090f0702010e010c0f021b03030304150b06190f0f090920070c0302 74
    0x141c0070061080d4030007801085d0460b0803a151718030710425650060040d25102801141c84c11661150074a84517895407012110f942000542c0700c00c81509000c0d01e500028849254202e03d49565102c00d84481120311000600201000191018056a12611014980c0440c0f0500700056203002010240d003a02c0481c4100c00386000451194440e1150034503c0c400302d0150914401060708010782c0240003403c00e0341c801e41c01e0304040700090400e40b5103101c45403020b004104080c01c0101c00b5041150041003c4400c0c41114100130280e915200802d420000d2400074a14903103612000b24050302201c1042c030829800c0840032881c080d0700c030700c050107440d015034240c1c1d6a0a944e1035007242c950050111650341a40140041404910700c2c0c1c0180d1300d0103c22080004100005001007502c0f9040040322840f01c40403403e2107102c0796003203080f0203803071034052a01020640d002000134052041703500429010a580300701c00901c1a1446003a040c6540c0d02140058441050f440c084030602e4990000700d0042007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 837298965 1250 837297715 837297737
    0x9030209100e070e0607320d0f030f0e150106030f06030809010324090b010905030c0102061513020f0a020111130303050306041b020a050f0a3f080403 66
    0x441c02034504142d440e0484890b0b0207454414044031408201c4c1d098941c420b8080254400203400055a0740441d007408402c2d402d1008040b155032800e45419001c0036031a00418040900e0750350280450040a00c05c1c00c00094081540c082c82004203c00104103c40d031040c1c0c10309814005803024524100d03403403039600b4088006004002d205482c1d8a110003807010701c00707010f40d0040c3e42c025005100000c00200031030005654481c034107030401e9103591141c08115580c003000c80c2c481d68403a00300c0015000950050590595010000f036680324014054814003032202c3d02d101865860504107440845c0c080c4055441c0d5582d00030041196101d00140b0303002d0345c41c00d00880c1c140107051041e13902c001d00001d66403464034a1500d054499501c0180000e81c020350314962140703051051200b00d6100c220b030b54018140100c00e0b00e482c034504001c0a0009035035034041c48006000a88200048046071070701d0b2100d20b1160340e1410070740c2a5030000c901c014103a4100744280601c0c0ca500c101d82d40e10a9019658000d40f0715 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 837300215 1250 837298965 837298981
    0x40204050105040c050d0c0e030a03030204030501062c181b180609150d17130f14012129010c030e01030c020708060a1a030f28020a030309030209 64
    0x10607050310500481c07010b10001c6c03031a509a0b4064407282840b41003010a12540340300190425110a8085000c03a03400314041c011f02509100300005800950a020b1300380700d655204418180715088110b40c90100d0400080d005c3c40300004280300708840d02c0440343e1121f0180607481079510001e825501520800070200458408440030300c5c040c5001508118440e100d02d03414541100011071859040303400300304d021002450b4400d1400354130206030605034a810070008840380b10030f51030b840382504c03100e00c41c024403400400f03200300300742940700f402c000624810382402c48611140d1400e0f50b68800d440c082075456070b1035001d401c0c40100c7d41000c4491400b80c1c0312000641e0740c6112840013400050080300240c046501990003c1c1600304940110342440d541c03010043d10b4044102c4900b00119201c95103034003046041ca1240c2e5080c07204034040d203070109503940c40c2a40c903451101d558003863b00c0c0c181880f402904800c21200c4441e005804d40d00400d4403810043c10714007140c0b04c01c034011038815001034144 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 837301465 1250 837300215 837300221
    0x30703060618051608161e08070e0111030a05180402030901140a090c17190c060216050d1e1a060f0405060a0506091207140a0815270a050604020405010504 68
    0x2443e4207841e1a14584c80b100121000b591b81c109402080c00f10894685400d0080d8001c820f841184603514080b481c030305440700602d505850b0403600c0c1071000304c0711034101005002c13003503603029003040c5881e0b501c071009a400d10480208807241182c20a2001090141c80141900400d000c6610400841c0e055142e10f0b40c01d2003201e039080400f40c0309100c5d0107414080d014030340101c84c0220040b0700841c1d018074050f29032000005951041202c1000c01c0b90401c0000c15010f011380740c1820307080d420440e03c0314602000f00390060f00b8140c0041a0203881d1012141c00909030301d10b51205a0072441c044a80c071a1018402507c1e80151a07180c400c000e080c11070000ca10b001c0c01101d10a641c042c01e02c00d152482c003000e1001030780115480660105141206002400c001c10214004118000044603250000d0040c00381000150f0001d20761904003864010410422001040c2c1203080303c044000d440c0600b0b0300400444035546c60782c060038018503c0c05824800700086075802103000b2501000184d0303840c4104270031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 837302715 1250 837301465 837301501
    0x51b030a0c030605040303020c06130c1a070b09031c09051e0a06091502070b01030b090307200604050a0b13170705040509030c0609151b1803070306061805 68
    0x101c09150180001080e40e04102c4c1c209102e030401504000094004600380607080790325400d503500300c0340c0803410700c1642c1405030001c00c0c021a5040e00e880c030144e006010b61150003006003110180c40b001c28000c1204000312007201034800c104500d02c50030b4484a81c0500300a1030180c0e03803407081091010322500415040d0141c8042c050003880e00e00042c0e03a4560203002120015902054945500b5202c912640003d004241c441c01e41b0307101541c1145003030403100b00050040c3d1082d5006200200015464030070701526100b060258800d0a03204c2c1000491a200782c0d0171480e04444c05080c009a035248040180919802c41c0002004083c0c445840c804058483c4000001542c0034000c208a141410b901c2240c00903a403006582c0b809140c0c0700600d28080b030913a40c181c00d9030301c80c98180141000141035660400801815866400d10181c59801c0c0e50040d0314000074201200c3ca03d10310a81d9080000c08021540400d050091540d10b041d425900702e0f44100c9000224103000000e58102e48803040641 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 837303965 1250 837302715 837302723
    0x1050c040302093402060108031303021c020a14010e010e2206051503040201080f0f0c0306060d110405011b0f060b1816090504140a0507021504051b030a 67
    0x4100303440c6408001140303034050001000000c2c40c941080107403460401900003c405052007502c0b44030b803d01d00900d0900141d010030340769002230110941c001c298083c100300b00d98046a4200e000d00fa040f9142e01c210b00d000384001d500c02107401000419010003104811000005d0300d54550f628103800064400b01206000030f070303010420781d000c11109821040010001c4440a0001a18039185c001044d20203000e07403041c50a100000c410001103682c0302649a91000040740b1000385410450503050041101034456004488003000061aa440b0074050b2000d4944201040c480e00c0e6801e484c3701c00b01c1e8824002d040c00158520810521241e03d07400f2405c030640c0c13101c103500c4880f50307945a100091007400445a800b0001812502c07081807440401c0d40110a890314850094250380809007000c0480d5200c113000b241804404002140740c2d2000951103500f6031070101d40c035030b900034080b03040032008044521034031111014001031180024010903c0a07081140c003c1d103031455010590307a0313800054018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 837305215 1250 837303965 837303967
    0x70302062e06110c0607050304051903080d0c0512131424041e030f09091e0b13111308070515070f020a030317150607111c05030c010501060201050c 65
    0x8064420002c000c034081d03d1506940380d049016000690a03881480d00790380d258404034040c00030f032402c080b201c460364003010950723110700349140d40341c010303e0155800f0031503626502d10132516410b00410884800741d810203100300691420106001c2000c14065083d00e085120703e100d140e02d000009150300907207506d404540495810040c0461001030014000c440c80c40c01e890941825903040b00c4001700d41e070b210352261384440d0710a11004140401c9540724409603424280901c0200ca0740d05c010388454040400081400180c103c0440c0300006120318009d441454003581170b035100c4285005d0050b200b03801054800103035a030880b26550b5071850151a0744030448580c080542c42c0000014041313180f14407403242c204c046a400140601d05281d20035000b1840c12040001c254013070320b80361648281c484040d020341c91450301c00b160003400340d580c005003034040c49500750300f8603565441203000001c59032900080210341864801e80b44d801c1400410070070340c00c00c0008542a8010300420748280c0c2b0550050f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 837306465 1250 837305215 837305219
    0x3010203190504050304030206030c04080c22020d15080a02030c0a06023301060806101110110702101707020a02010527030706030606090b0339070302062e 68
    0x94001008080c3c82150684001c100000041c1c48a801552182030b501c00d1007621149481c0140382004030140d00f4911400b5480d140010f1485548501c404502c424040103803a032480603a4040204612210320180e50005500002d1452001840d2440c15100340c082d00c11000101043c404c5130b450501400c0007503001101c4403440d10281401082520226260208408840d6615908451803c2c1c005800090b41c110070490135003001c2c2020103a454091500c070040d0008622215100e401c0c1e03200c01c40348d2546420007010300c0c101d00020b6441c2c141d0000c0909011b041154400350007005681000142c0d0400c0100142585001003841020280c06849080c586240f07242d150f01800c0300d044418540c0110001da0804545040011102810294400141c5103041000103050342c90542e010f02d413115070030420030000d11422542c0b4409205031503500b844e07071b034948030791049001d00b400c040020481c40400ea440505070b0000b00c0c240158003980321101d5040300c1840c5031914004402411024000c0b8001c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 837307715 1250 837306465 837306511
    0x1b0705030d0801051f12022a0a0b0f07020a06050c0d0b1801030602090d120f2c060f04081f0c030b030c09070339031b0c17030c071103010203 62
    0x45002c03801010320b004581d0a8a20f61b414003203802092100d003c00509295400300395050759500c04150703a4140c0104043d91060f641d00019031b200909200201c0f0000e8042100b0f00c0c003c0015038291540048203001500c4c1c140d114541d10b80003011280d405a080c109101d4803810010040160444203900c4e0072010387c2191100703000b13584200780c081d810551441c079540104a2290005850510f00d0751260820100b10310000c051881c204010b131244c0702419200070640c0122a0000360203502585d00e580c807031300d03a00a007030528000c84d800314805010704d680e00c4074500d80e01586160280d110300d00230005015244003c0301120000d101c000d801d607004264403102c034079000100720b038050141c0c036010905656240340201003510182c50040001c02e040c800002070860450000d400c00258a02040040d0b00c44503022060510360a03400c040c00403c00030345043c011b00d10103d40e503e02e0310000c42e81da28100901c08034080e0740940000d45486034925480c00c80c0b494103000322400b81818203000202c030091042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 837308965 1250 837307715 837307759
    0x190e1018050d02131806020316020c04050105370608070f0219020906031606110f0f060117160f14040c211b0216081903050f1b0705030d080105 63
    0xd0041314520105d0746400078a5a00003184a01d8808210607075108501030b001e032629210070b1220f031169080074014040f40c0c8400c40b1541c0c0301760f104070240c000800324002c0701800c40400811124065600c0b1408140c15402c24401800360b01e030f40e501c40a010042d000101d8584600c07140300111001a0f400e5800589000c000c294ac02040042c16202528410104400c0b41203c9622041c081102c040d642c204100041c0700d1801080c00100c05013618600a28865849040501400b080006840159550000204205020b000441c055000115150010524040707480e100318107032403c1000480150341410b0054a076000700036166249204441810002d10300f0744403031201942c0c0c0ea00c0d5500404911b81c8000140c000385036402601e000d0020104521001000b030700400c01c0d95116084807050341580c20340303480410380c051611300e490300010000c0604030310a0f6500d8002c0c440707540c8018402101e02003072180c11104101e00b01d85088200107001d80c0d40e072009200e1b0340c3c0c1c441c0e001034070a810300100072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 837310215 1250 837308965 837308981
    0x30302060c070524100b040b0304020904050307120206010f0803090a050f01140313110108090d08061f0f09061d060f041d15060f190e1018050d0213 65
    0x36a14060b401c20000815065132851003521821000103001040200c0710507000900013806005180c5410b20700ca0340241c0c0f00140000380203800e1840091f09001c000d009503400c00c1e9004110303100c0d10482442c02544d4010a00500400b135008250020302a080041160300200c0042c181d42d0342c580c9050100506002d01903149414025607013000400349a8910045110b075036410b4400700e2003034060806a1300354440500c0641030005000c18054100c0b8000b5941c0d540700c64a18200143d55200c4c001300d11100355034201c12400c00500d0b00c0071010740f908001100c0e6406901d40e41e41c50015503c080450b103800041240c061154984094110306050042c02000501c1107040300391704d07243e5035100d5070310003440d004a028042c480ca107040c4044100e030a910031106031400c80700c05061400d81c130300140d02c500c240900c1c91100c0d0840600c0c1c1c160030b4018041409102001040c0140000082c403014040042d01c00030305000f0308100c03802144500c0c2150014141d80c0d0090701c50411051b214100c04020104031f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 837311465 1250 837310215 837310223
    0xd181d070203190503090d0810170c06070501020309060a0c0f2316050d0c150b010e1207060e09071e020a170a0206070e090c0d0e070806010e070207030302060c07 71
    0x10010841c451200582c3e40c0c1a00400c0e82c0c40d10f60780e14028440320306102110400b0020818844148980140d45050304000c1d0b4007205170400135288000c09191428020141d480d0700f15102240c08024000c06602951281c2c0b070400a550351907031281c00005c01c803a060700c450030214071580040c0030070394030501600851302c1c40c9512480144ca040c001c00c16250701b092130540c1000305080ca0700c8040201c2484200a00c0005080a00d00d0038500c0e6110010390b600015000c0c410380e500c0840030f072603a00ca000650140307034000c0d0100c00300400400340c26490340d5280c0100da0100300c070914141c019041110f0f24170722071204c1e96140341c1c02040c2d845604c00080302c9115a030003148038400c0f484012581c901d0041740c4500e44904c8542d070340c0809110184c140f640050410341481380741100d505079911003c0c0c2c1d5542c480c6109005542c2c0d4840b14070301000030544541c2c115030600c541d02001c2404a0300180e01816140f00c07039128803441d5a1220101c0e80c030320140c0402001038000b00f012480002101000d007440c00c3c86 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 837312715 1250 837311465 837311467
    0x90418050f07060e031c030209042427180c0e040611071527050a0b0c13060c020a0e07120615020a110105040e090d181d070203 56
    0x10005240211028400035503058000648014140d041008031100810032030804c080035101d10b000181c0c40308941512040f4500c15103500c0355030940300764101c6803d540014410850900218001c03115920488160b1182d001e00f1000420120320002c446140d549d1601d040c0c001400e20733040c49030060866803184d0b4500d11200340100f40005e1030781019001502e60786404141c24a864101041590345803000b0a5a0600400c030001c0810040c220840c0c040080640204101501e44504460302681c490844a0112003400d031008110002c202c224101c1d0241990741c803170b5102e41c442d00c4081d100d404520203000c0c03040e0400300041c2d4010143c4e11919400203040280c15541d4500e0a2071041d403c854a40001c0c0c040100c1c400c3c0d11429100d040068100605803004210400f240a59034181d031083c0540100604804080142c1c420340444002d0485a40182c0441c148083c42c507589402c101071040204150180c204031881180c0310690485660187c0e07420032090b4510a021440405400d00045000c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 837313965 1250 837312715 837312731
    0x4031e0c0e0411040f0501080d0f11030a0c0b060a0501090e0a020f1605010c050c120310080a0503070302150c0f032e0608011e06320a030b0a1a0904 65
    0x40301c00350700c0340380581c20041262200c00c041004036403c24850644903460f1000501091000140814180c0d29034100302d4404401c0319400d075080755252080c14460f202c00548071020340c3d44194800c0c20a03100d00344102203500d0301000c2014401c1c0314041e250000342003107001c0042d04061240b1507081104850010703d0003c0602c00a18554400d80c00c84400390a074000c0a010003009100f0740510220510389681001840360116441e10090600743c51225000310105400211440110300181346000443e000400c9620b07000da1a6040300c0402d0300035000e41d003010200b80a680c8d00c054400c0c545040030360724002e14141985810340002d0100e0200060302c080d420071402140072200c041a855132008102d60380f03021001025034205801042d10700d401c004034060003d08035040d41c400d4a0607424280304003c40c80d050f80c3c80228060b280010002030040030352092200700001051100740d10740c3d003403000b60700d4481409a001c00c90311a0001c074072558001a1407240400b0701420212000502c0410801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 837315215 1250 837313965 837313979
    0x140a1106040b06030c01030c140c07050d0627210302090406090b100c02060901080403020a121718071a070507090606020d08010806060d060f140907080304031e0c 71
    0x94001c480448030004002c0c14061240360422540e0350340c1d24240303411301c0740100c05000140101480744801c02c0340700c80424040d03400d00050001070701802c005404070020380181d05000018218818040034a07850b0100c20079111440081110364194100c0114101d516880c0200b041090b4402c2d0000304140c2d09211540841d901e074015000100b18030720011500c05c14400c20020700c01800c100701403c5c020031314a0310300146c07a0f9900b44c50000310b09081000c5580d55034241a400c02841c00c1c00240380c9500b03012101c50b11500300000800e06011070303400c2c000c245c0d6885072842c1c0d08040c4080c2d00145a00000301007264400203100980c0d02c13680080101d05020340d07036961900d056001d8000750342d407035210241170000c2681001089144915883c2c07800040d45020950742d02c40c40c01505050107240e003070f174221091051940100401c0005607800708226842d4bc03406108140e425a5501400d0003000c00000e040b250000959098903001344500641c541004100b040100c02480121003913968101700040780 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 837316465 1250 837315215 837315223
    0x60c030f0819023415050705040b03090a061b0c06110906040609030b0a051902030a090f1115030c04090510170304090b0604060e0d1505010815090c01140a11 69
    0x290314100388460a55a01191201c0c43c00611386030b0751a240e0014401008140c0412450050b030714004000251070700c810b401181d603032180c0e810260441c0b000005000e85e80700001202140d15000340c0c020024426811003949544610070724040003d0b2860305080301117501036002c42c45000d01000003e242c04030316000700c0d410b03400550042020070002d0000300705003c200111a86d001d0000c650030450f500e000786071030040d4207400c580f1640240e404000545003024a600c0b001d0201c0c0c0001d50540d15862500d88100071041c0740d40d80500503111001d211052500c55010350f400b1303224003a81c207400c1605211400000300b800818095807688c07030b0100041e4642108000721406806500035503550750030501e03e041601c50078101a40100c104010130445941c2c80b844556052104403109480141c441c10107040120220b0301103800c407498440001003101d0300040c103180c8442c0c00c10a82d0741664416400704d440e61201803100740442c1d0500c3d8a40400400d07a001000c0007182401d00300d07440f1003041c50841c50 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 837317715 1250 837316465 837316477
    0x62106050a0815180d050c010f2a210b03070509010f080706020c0a120213110a0210020909010e0601020f0d0207030309090c120b0301060825060c030f081902 69
    0xb207030840e08450f070f000c1070b04074030140c1e00c4070080ca1890301c03143c2c9000f1042e9480380c01094800070418017081b00382e6290003c0d00015141e10070700506100040d010003018601c01e503061440c09800311000e1303000000074080ca1081140741e442d040c0c0d80b115a1444915030300500034810303000347d1500520101007480d0f6141000180070341003030340c0c44411343c6d4244500070b45450311540104083d5402028095020317075889013006e05890000a95205252030b40c400314040c4000282c2020409060107511801009080701914007400c2d103600f15213070700740310440c254101d115034055141c2200c5003400600120401e414525000311f01807040320140641c10a116050650241400b801070300500801c2041c10b51254014000c2c144a5034200701024010002400c03030b0000400c50030302c182d00d40407008020780d0290b000344018411302040e00c4200d403900c9400342804000141b03215002070000404038040d40303e00c15500360154542c64402e420000b0800980d01a4001000d04a0100002403020780681075800a401c07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 837318965 1250 837317715 837317729
    0xf0c04030f0f02091e0103110402070501380a1502031215090a02030f070e0f060c03131d070804020409020a08160e1308070c080a03050d110301062106050a 68
    0x3402109620400c15400c00140c00c60383d40c420084044440c1d8000c0900c0c5c1030449900041a054030312281011502038015104086e019500c0c0000756441d4049a0b817010010941d8031140e10070003406d144941c10030508100310290020540d074400c3c800c0c0c0403000d81c2c072400c0400741c1c011607082c40e1010b0200514100101c45003e1004a501024480c604015a10310b4000c11500d0b802c1d829440e005624032070400005007a0002c00c14082d108a44031b494110640d03c000002501d01c035914052182141c0d5603034080c6000e488249181c000c0000c610440041e591840c00d688032114040344ca03101d000b12038061001d08140d1f4071544d100c50500c0140d60703207101c0c1401005000c1c090b04850001540c50030101d00725600c4401c500000000300716003050351400803d8101c0c1d010b5501d603102c2d216030800105640782d5030800300b098821001d0b04410706811138060300328015915014800d1580081ea2001180400e200f2003001c0b030485030b00035450041c01c200f0f010340030303141c0c0340d002400c81d40c0c0e0f00c0058807900707850b40905 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 837320215 1250 837318965 837318983
    0x3040c21030206061e01210609141b040509070905090106080601030c0905011b0302010e030d151d07080c0d06031112060408040506070510060312080f0f0f0c04030f 72
    0x14101a0180f00b10f07640601e0413520385441e40c180450080121503484410b904001e02d2543c4815050440e084142c0b0b8400d0746031082003415241c0403403070018078441c1c00200400c06138000140401d0341c1840d9030610040c1746c0e810700f42040d14281c1030080b480c0015290358140070760314101040589440e40c00ea80209140e503602021030401070005400c1380c030f5144900c42088980141488142d0f00103241090900c08002d5220641e2071030f0034101d00500c07860b17841c44007034000020360081c240b4071038120b0084c49913500035150320300c0d5403840703460030b0150036980614101802c04001400e0302d0241812031740c01602c1c010716600d02224600306404540300e40d0070486020030740400005150901102100c1c518440800610890a06840b001c41a000e180f09451207424005000c0d000c01006001c0030b0341131484240b040c40071a49030b02d80460500c03c076595010000f40c0d02d000107814020362044ca41e01400101c00d96081503142c44420f1075400d200104601c0082104000c0000022140d00312000d0145c0070340e07a0341d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 837321465 1250 837320215 837320279
    0x7080d02031e0f0f090f0313050109082e090203060a05101e05040b03030c151f060804110102030f180a06020609060f04060b1507030201060b0a050403060203040c 71
    0x400c0c900450b00c0d15240b07900c0310100400c001c88901d00c03c1142c12100300d4600c2040c507502c080c40e03949441c0d03040901d982d0300e01010580d080000d10000710308040c1c1d2400d803600c4140d41e85034110030b5031310700d11041c0070380140190b204030040c140321040d0601c4e0b540d91208004118003013290040f91401d00d0646407108081d0351001000112003941d40040003902d040700c1881004100c8042d0700000f83d000b170041c0f52088d540e8414001c230700c1d0340030402c03101c5100011f07041e1030341810f0400c50349801b12400c40303544803285a5800d114081e1064013581c1e01c00e0316443c1d00e03519555201d54854800b08103e603180c807030641c4800c0000f071900240003400752101860034541d181181c1203020500440000d1940310b8002d66000c1d000703001c0303c9440400c0c0c0582c0400c004014802c0790b555400c14401812007003040c00d400a079038040214110350310074021701106000350028040390b651814045803034454102c42c480020000c0c04207000140b440d400035504903010f120540502c94541941511401903032400702c2500c0d1002d104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 837322715 1250 837321465 837321481
    0x30901081f18090b19180f030f02010e030f04050a090501030f080d110f0d1d0613171b100506010905090601031b021b03061308030c07080d0203 63
    0x8030a6200300c64040c15070151582100d00ca4004209008000c1903024003507425042400d154481c11029410403611015418621072803030b00c840c03c042c6090080d40c00c1c0040030500f4030810754001c1da00d65000242c54034000b0b46880c1181d50800d002018400c554032001c0503008854104050948207112510296440c0c1c82c0408125040a8581c400748440341040010008200d4801030503080640020071182c0e1100700c0b04510004001101a014030820302150452519440c40054601703181008401c00c100302e104022040000380100c0080465806280000c84c24128074800084c01c0b841094111a02c104881d00f042c40c541041542c400007a03c2c1200290b00b4400411a511121268a10411a606010700000c0c4042c0b424003403240140038a1010a001e80d2080c0e104103c2001101030110180c0c560381e400a454604c81c0010468005039041e004069140204129014042501900b00c06002d10340d5a00d425800080c4140c50841d400d21046022444080c02012081001c00006a4900e00005 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 837323965 1250 837322715 837322727
    0xd02070504110a050a180f0302090a020306100311120f07030606050a091505041805040b06060a0e0f2e02061510080604060f1202040b040213060e130e030901 69
    0x110880c45103003400c8a0841401e050402c4982c40b803840c1c03400645e030340f02642054840003075091142900c040170030f40c000b441031000c24070401030707030f00c2262441156111516008107900041d20820392000300100a10f810a000c0e511407060541c400d2581c60409400b405c0030090503d003150346681c40100d003810404144d41c03620424014041c06d04245041c4941150003c00440017409607081d02c8242e0304007015410700a006950081020b901181207804100080002900099404407402c070700c010041001d40c40d01909442eaa01c100c2d070345503074803000d01c2403c20900000700b00f40507410a05201a2800c0852107540f0703610100c021140400c2501880c3c072000345800d0b0001c0000390940c92185c4250696940e0114950f02c06606140180e842d0b142d00c0c002400400d010780c0400c600324440100014111104c2c9207030100c00707000b242c04001c0752400c07005010681c0700b04100c00c0d00c100315280c014000240114680310b44900041c1c0070318000c0c00143c3d000005ca50180d140300060350700101d0149083e6901030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 837325215 1250 837323965 837323969
    0x10c020a110405010f14010309150902040b1e0d081e0c10050402061902010b130c030e0303041e0309050405070804050f0c1e011b030e01090e0108060613020d0501080d0207 75
    0x3441c00c010f507600d84003110704480e041d805050702d0b03006d403140c0200e143c2c0e210750804104540c0100d00603505094030540e80c40101140305040303015134180501a500c07491312003186c55403000c5408220340300d0740342d280070000030109040c000c0369603034010f00c034a200ca02d13040c140245104918072201a03a82040304c0d58140703080d001074140d03541e0500346000c00c401a1035480c10350310310301e40007074041c40c4865013030382c040c5c1c0035051643c1a15040b01000750f084540340c0e800e4110140c0d06115480421040c0e9100c070003542c80e0300c02150041c00461a26008040900840c0c0b0180210340c00780ca0500010741d22503000406455007a01d07910001a102c0062005000e014051007840d07140c0710f002004044200030120b0101c0001c0d1240a2034440c000d443d02c0071a0b401404981e82d01d000000180c00340c51000d18000d85229074002e00380b80003403042c000c0401c2500d25000254181c0f0a040b00030b0a0a95415040200380c5c1032600205204640034020140000e5440c020103001c2c2012002500301504842c0000345880303403075 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 837326465 1250 837325215 837325219
    0x1050a05040b0f0319060b181827070806070c02030703060c050304150905060402010e0a0f0f0e070c080706050613090c03110f0f0d0f02030601060203031605310503010c020a11 77
    0x46031b01042982c3c0a0340071501103103c889000f0024841c008001175000d4200342d1000c200c0d0070500200040100808100304070f4140d00252880c1701d118031085135581c0c4506000312011580914080f03450f040c051500d6010f200d01c0142100c00303442c2c990f40c0361410364041d40144070200e00040705000800210640000030901c0c807041c100b01d02c401c60744035280d460380090006414090464124040c548412241201809501c0002032800b40ea46d41080c81d402003604c659800d040c100700c08543c01c1403003040d00500300e9402190403401d00605480d14402014042d003071690100061140240d001c0150103801006130140a03600605071a604042500c0200001c0091285607041c80e0251207a603a90401030341d001d0103441004aa00c91403508034824014032001a615101d941c000140081e4004001c601c00d490901039510b0707000101c401500d06020309201462001041c1420401e5001e50080031a4104585c4102112003641c90000c282102c0c0c4200c0c110005801200c4500144a01c3e1501d05400d8841 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 837327715 1250 837326465 837326471
    0xc11061b0303041e020d03030504060b030f0a02030c0307060539011a06090d080c01020c0105250816050c070b0c010b0301051f120524010512160501050a05040b0f0319 73
    0x138503800030385107003841d00d0028280b6545501044c00c4c403403250f120401c5100b002d004c03136100b1845800c50aa0750803154504a110384aa003445c500e20703081c0070440c071003141e80d940ca6103070804500c2a1104c04010844030420424401c4031410404542e0881316104020804c4000040400307200391211950881100814041c240400c008440c90719180100d0003625000308400b034864850b618518068407c844081c03049600700014060302d02103c4040b10081143d00400904c862004070056031081000c81d01407415020444002c1081c40c080d0f001084031920301030548031607075102c071007524494002d40b0340001d05a41d070311810b420b507040902c6020380012101303020f00300011032170807904803075011401f03081d10080c00381e2000400c100d0100581082c00655807009840d1591100c111429018244640c40c4a0300c00d040d60950603075008100003920a01c2c440c500a80e0b03500300b0006560b950700c8a0140001c000c010000010701c00b0899014001580107078080303a650f810000390030785540c0c4982c5049908145 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 837328965 1250 837327715 837327773
    0x1921140105011d09060d0213020a0806100201060b0304020603060f18100b07020310091703012403020a0c060c0c081c0b10020c10170a1b0f0c11061b030304 68
    0x150313601e0310f15404902103072154118010740c40481c3d4aa5488a0883d40480c00401c00104443d00001201e2080405840483c0d00c0040884100c3c01d98031b00307129a442e500d4040021402504245000b984d00602c0a41190405d40710400411364400b0030aa040e002c0c00161402c1c13040e00792812100c0c40041030f12039050380c20300490340c0010b030302c8030052440040b02c1e80d42d81c40c0d41e008009111440c11080e90b0306409030383e100e60303440220815100d4106d203944428000800d01041d854001d100b0b07206858040e50300c1701c0402c17101c1c1e5100c1000f0041d1013032581c140442440c0300300c00540a400200410003001403c50500d100e040801d0064450f120815449000510b0350700001d2035000174a00060b120407101c02c03000c01c00c00304d41640c03010401d000c80e1741c0d10300c07120080147e103c04c03e401c000700b8403a920f82100819000080c0444001d041c0b01002c80018000ca940740c0c02040210120740501e150041c4424904001307030603103145c08401e055486009400100030041840500c0164000800401501e811040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 837330215 1250 837328965 837328969
    0x2b090206030a0f0b06210c160b10150903120906020d080a06050a08010b030c060f1c0e010e06090c010212041502070b030c1c021921140105011d 63
    0x2020060404003800c1d43e5000c4880c808102c1d03005450510303409402a40da8075440050314034003024104403200c08207440740100742c40c0f40000045408080703402207502a240740e40c0c0d6500d0f504a601800384444405c030f0200c04200e10b010241e001400d444103480300d0800300c3ca14900036050341e2940c2c159205006914504100b010f80100d100081c080061601324469036a600640b001041e01c0c1e000180c0100c03103520081519801544000c2c211401101107800600e0355408000b058410121882d8940300184100040642820869140c5e100c0700c001c04601d0346075040e101d03401c4840c9001d1003002c503408103092005401040c45890b040c04422701c0941a440100c4201c0b00540c0300c1d40c424003041c01940021440d145100b44a4080501341c44048255a4100b4a218a5040d040060f042d00800c8100b040a00040c0c2c80e4800c44070303541e203c0c0b0b003941900c0040b440b080d036a0882d10406400751200c0040b5a06114606215085240e1521302c441c0103154100b100041c9015141c60700e18517440700c880ca48103402d07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 837331465 1250 837330215 837330217
    0xb1c060b0a0b090108100e040f0317041e050304051e0a0b030c12040f050a030e0102010b190501200703060c0e030307170d110313030f0206011409060d082b090206 71
    0x110f000703091400346078940c0c4a801549034400d512613030880b0600424401044407140406400c00e000c1e03030360001c900206040c6590f5100040e200107109010014043c940002c25407980300c3d13128080d04c152404c05a8440210302c10044030b080d03203100c40070000b04c03106241c50052502000f400e080c8551900798904031200001d00d103c1c021842541d0245500000c04016107444140641c4c0c1e44442550402c0a0600d0054030450600141c90301550030407959110f907040c0040c082c0421690344011074403052910006440c0320840c00400c1e226284c2c022a000c001031420040c4070002d500c24400000c0c2a00c0c0700304020400700303820040c00d1003600100121004602d203c0c10004180e4400400140e84014a004280c003e02c50f01984070104a808070800c01c6410f07c0c074140300a0b01d4001d40fa00c00300c60b10540c0c006c03038403003909000d035205108041034481c401d0308140701040d038031400150095007940c03000c0d2202c800c1c2c1e42141c80364281000e040c2c07442140e60765015404100750482101c050040402d80e43c00100d04e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 837332715 1250 837331465 837331477
    0x12051623190915060801140d0b07022802010815180601050c010c0305090f070f1a0d020f1e0c190204060e01080303010e0108120403080a030b1c060b0a0b 67
    0x3040056401050088151000d035100414190800b0040d22000071142c0700481d07414410390000c240c04000018084243c7c01240035442d20040c00421580100d541c1d030f5840f00070143c40c040440c45148408011103802c0b0820001c00c5420902c4803100b071000d03100040094400400c0d10f090350080c82540b100c0e540b9040444074140e8a82c500a40e155510074004990600440e011280d166081c00700a0f00c0c401d4140d400b260088040f60b05075031601c00002a070035540c048902c0381c104a440310342c508001103503000c0c0a6494182000e5851840c1c00034542c2c2240998015442c0151074040000c4c03408003030f0b00306c0c9060340928126169220f0419000c4200c0030f03150000021000d8401c6101c404040441d51941d100102030100c00306420607558417114015525002400f45030502020000045030b00740700026021400700c2c0d10b0054516103402e55413403240c185c009442e400e080c0f54440c55800080d540c0c0f070486051080000c4090340d11480c4900b0700905581010300c000e8003990b4951030901c5200e26880441d45 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 837333965 1250 837332715 837332719
    0x501021b0d0302010b040f090203010e030f09011d0307031211070602030f1b060405031909080a080708071a06040f020405090103020108220317011502070608090712051623 75
    0x280e030794a141010303805000440c000c2da5015103420382140781402d07254010f2036014000c2e0020046102c1003004280c1e03034824030078142c4d00c00341c05100b611041d6201c2c090109502d10400040c240514845020034500b098903001200c211904807a9001d60592020198200404240013806041e181c1000a901ca07c54503140d8040610001030b2940c0038074054810408100241c012101d40340761504001c1d0310f9030010205801503030000100d1002c45c901c100a21401e807031209003d40384022840d0740b80322182e4044182111912000d00489002c00e0008007120f0142c40300300403039402d510b0194104011120001c0101040c0361040c030061101d40c03030781e54807a410b41354282054240d40d01c03003d028060f04a1142100300710100d2240340c40381003507448800240314110380345c40c110160740c0369581c0541503109410f5240040e40003003c01c101c0c031441070b0501900404030034203032101c40380c4545a49200c00d44918082c0c41d80e621a0800100c44003001142c0001400a610030001e096601007644500c03840071a0243c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 837335215 1250 837333965 837333979
    0x20a12030b0103060b1207090e042012030a0309020a0603020c0309040b0409140a0605060a06170c13030c1a1e0a02030d18021008090c13111309060501021b 68
    0x107480381d000c0c0e48454040d1200313400d2291100401c030b11644490608803507420010741504d1001809400a104082c01580e100d02455200100c500c640201ca800440103075900400240c030300c0518100a000801c6810b6050b640410314007030300d0052221100c155070080d800c251040142a220040c08019180710317000807140443ca44c0d0400d8009001303410140e20160000e120f00c0810260307020002841c20340c01c6d00c9141c051085588500401c034070110113202d81400302c0d6183ca482c9021228904400794404138600c00941040101071108659420540080307421907000300c1c05208080c00300549012428214898501d440011500e104042412581003060b0490120b05083e00600074070588032080217031442002a41d0200a20482241e282c00080c1d0052005c10013080c40d90f4420440184604d44002c004e00c0655131650521005540808030320030007594070b1000058420110000b020712440e01c0207400c3c0802d0610141e9170031181c59a122a05550000303107001c4200522000219034200112200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 837336465 1250 837335215 837335231
    0x7030f080f040b03010819150209150a02030a140c0d0f03200307170601021207060207062a02061501030903030f0e031305010306180903022119020a1203 67
    0x4034880340100042000314420218000c54441d0320100518101c546020403130700030402d07801d0240103801d9000b0015000c4c58200062088450383da4005210b203040142640f6045d904040400340c868000009220041e08001010b1540c1a40600070220050301c040e425403818400070301c5155141505161482406204602c617035010307020b035100309035034140070002160030603964059940d25401214400041801c10204200364100402c3e006e00c20794043e00180003080b071451080c0c00d01e03080740380304a403125000c10400002403070381e000c0d1054154986204400c4021106031b0703841013424050408003158401000c0003629880c0022600e9048800c3c200052161590b0038114058590b102d846540b85003851000d0342c1041c000001450481c140c1d48540310b002c2c3d180d40044003503400314031403000d00d40d50100c03080e180c0040542c00050900c0c8240101c1b800800c031201800181c541c02c01107145a44c01c0802d080010701d05004207515a102c251028040300001c545e01c449468803941c4c0b0800c101070f0340f6115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 837337715 1250 837336465 837336473
    0xc0d08090a06050c0d05091e030304110405060d020411030103030e180105040209060c0d02060a06150815030a0b040b1e0601080f0a110403080315060a09030813120614090f07030f 78
    0x200e51941a005d0070a10452802082d21603403050580e5000c040310b00ca001000020a1003c0152401160f1220803034030318100d1041000f0141502a0403e540a0300c40890381c0c0040e0342e1b44c451a48140380941d1100d459600d14180070303082502e240c04141c000ca901c00010380401c0200c0345101d040d600104c40040e12614000b010a040740036005042416204d01d80c0301c00007198000414902ca0b0300c4021050040079140c008c40000c1401d000c07501c0c0c1c04a03c1200c085440e03101c0010126014803405002c541e40080c054030b910288103419034043d6450b0850b40240f1420208009844140903001c0c3c13041c0540d42000c43c0028042c0c00001d08050060344480081001d61405400414540c03424104440d1a581c4905091602d54030503200301c02204c074900d601100c2030070220240e881c18821512003948a80c43c54483d005d0591100344440c4406500080c0440d03404000103da09426014420004d0104402d04c5090318142028001c0b80283e48612403103035444070009003100942c1d80c007010714103540c1c00c1850 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 837338965 1250 837337715 837337717
    0x30215071511090f0307050307061202310803131e1a0c012009130609020409090614060625020603161e0801030b06031c050c0d08090a06050c 62
    0x1a108491030500b620751a82d0403402000c0c0000c003000701c0d003104039000040c04040d59070040e40305681c0c258000d10010481680500c514607000900c0490140c03810040700c3e170004440305002c440381403482c003d81200b141491143e0020000c0c0101c4002146015141300440307085000e90b20603004c10400035031462001e42a89400c0340000d110880302130603241d40401d802119070300407424a03050b0750318000382071192101040c000d0b241300d201c1c404031510b03000101003440300a0003000ca80d030f80c01903101d450000c1c00180d244000c1c0020b20401c10000350800c0d5500d0702000b681e400b0348a24027154503481c00d115a03641c1c0c400844034503410400310000940300b10030110350b14001040001c1e40c80030000c0308110424400121140300502140d451940210051811101000c104418840042d80075001440041c502014890b00008002c04517092031140c09803c24003c45003482d048001400400d111100304410000c00d400450301d82480079107890005421943c40c065200c000d0041390700d5401060040070140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 837340215 1250 837338965 837338993
    0x172703030d060602030a1d060702010f021e0601030c090c02060a2003010b03010e010e010815070e060c0f0c1002100902180408031b18190902041e05040603021507 71
    0x800078010b05903205000707074417900001500804208440003101002111405d4100c00f400300500640c00d11185400442c0d9900c03034035514909500c40d01040c0a5191203025000390307402c3c1d02d44020082c640c1145408400842994041580d45080110b100a041c1e00483c00c1c5a00c103400d0f0b440024480040c03000c08400842601e4240450000080003040034401d0b0001581600c904101444240e44d94280400e803482091040300d405070028100114151034401c45250000041e103042c84000d16402c00141059211140c0e803000c2d640840b9000001d03c40621520701e001c407044454040500c01104040d40300c000c0d9840c0c601c0d410350303600704c01000c41d03940d048071030308500e411340d0140740c1c61810b490004131650056588000300709410643d41181228042186c000b151904580c0c1c58a10240302480f010001040c10405090340480b004941c0700110b00c0a80002e001001c03501d80340d6803040070042421001d0b030b003010340a603050007002c5c40075031a110200b881d02c1406600a035134400044c10301b60041c1503d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 837341465 1250 837340215 837340237
    0x1704080d0f02070c080718110d020d0203090d0f09051320070c0e07050d090303092910060207030b07121508190b07050c03090a060c17270303 62
    0x11a0360031010120640c05429070502c1000c0c13000d101625041e54669415141c0305031000c0b640344003052200c08005421400c00380355007844007410008104980016031700301038840d00d1000d50100c01c000040c0d01c201718640544240742000c42002c03400003001000030409010706405111110015904145164014140051030111120b24902880e0400f100b6510035501960780450041001c01d110240110a40c042c803413507103e06241085c2030b101c0401402d20184140d0502d41c3e41c54403140411002844402180c2c0e01c42d4800403030101c052481c0c0392540c4003401d11500c001c4005014000710b81c0000316941a41d0b0040c00c0e4420540d10041c0c11601407034044809200103040c21301200c807001940ca402c1003a0741001090300d101080e1070003904d01d040003041002d000340030f03c0c4010601c05805a0000c1c141c2420310800d403403070100e03030b900414204030040c1e02001c00140f20300d01040600070714042120703000c040656403074a895000e43c2003800400c1070102c003000109298110000a84d03080044901481c5a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 837342715 1250 837341465 837341471
    0x140c0901140c0613150209031c03140c03190207120309140d051305030606010e01030507051e031602061302090c0d09110307060e1807030e03072402030402011704080d 73
    0x1c0a00c2c0160400000c01342114107003910b00c0c858408018500a45610b06001780040c0080403055031410005545007088200340f5a0b47c014622480b1600384420f80304000b03540c00242c1d07904090003502d000140800210034910700c140701042c00a42500c0031032030480d040703140105100055003802007500886d840000414840c0e11015401150000081d0200d80e0030302c5078002105a0303032000d242d21000300301e0b9801e000440c4525030540300d41c029404035400c00f0242c40c14a0170585402d1190034111000449250b002c00c001c01040400d4928100000310800d6920107462982003d00c3c8952200e404054000e00c20b06500c0005401160600142d50080d80011024060102c490410b0f4864036140c100c414000d009001d004900c0c1401007080b403400c0c0002500004000d0840b0046003252080501603008140c1c446440380014030301007002e01034450103606031a03011720f0b2402c00a046190003020199000f80180100b00160381c0180c010705003011511a2000941c0d55071612820701e220f440c3c9190450f1f46 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 837343965 1250 837342715 837342721
    0xc12030f0d0b010f0e0d02010324030f020306090d092304050f1512071e08120d05150906060c10020307030903080c071707060e010f020d140c0901140c06 67
    0x5207503081003458880a0329201d4543c1480740080303d00707109000e07030150007030821804500154442e511040b1040c103612a200b5004807410008510b4000d1680151051000d105c152000c2d850b0030311080da006928440240084072400102074240c0c245841034081c4020606201c0d407840c10407004155005200510400c403514083c410781d00001420364290040d4210300f0140e103040e041c00d043d843c4003200f81c0401040d142d45804440c4100700b82c1207066800100c1e0f00c4c00c000488000c104520184100d40c0b150740341d155030f400034040c404c88200a22614085081d04c91811250300e50410303090b0018010f41d0b440342e079010f0b400c810900d00940d151080d405581b002003008401a4103500c09030982c3e00c02e070780c2c080c400d032240c912800d0fa90140100190580008202c4880b188180500418029100b0b071400304482c0d200707141032402c440d1740c441e00360640390b0006410810b4141600c0f0701e2a9694254194a815081500641c03015000f01080c182c1441601d409012030443d044080d02c0f0320030201011150245 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 837345215 1250 837343965 837343987
    0x106121b0306090c0f02120a0201110f0304050d03020405060f0d2301060917060133030c0905100801060302130302190608060109030f030c020a180b030c0307080c12030f 74
    0xc42c2c0c0c1e100d00220180350900c8612858407441d94501c0c0000958020401c1c2001200040300e198012070542081d99602c0b8840c0a04180301c4000c0c0c94151509507c158403441c06040c01401c00756061240d10070148100414000c41e5030300d609950f4070002c241c04e42601e81c0c088105800003061030390308003a10102001080140321a0840c07826043c0c98803640c03043c030fa541d40e4a80d540c12084082c50603050316001240180070b00c40b20984403182000340301d0040303400010201426003100118158040002e80c42e001594129500808404018101520301190389044844002e10070030040c0191402c0640014940c1d50313800344c410440e000f568005001094240148010b00750300c42043c41040f0118006500048856024621034022070750421006404880c90740e408031040758840304200da00007400c44c40031444070748650180901410b00100000d600c813110b030405160944000c0305601c40c0c2d2200401b4001604042100110304a09a520800c0d100c0c07011011811400b50b80d010310f03071515021440c108a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 837346465 1250 837345215 837345221
    0xf0406080114100e0a1508030d1e060506040b0f09120a02100c0f0b0604020d0608010605150c0604110612180601090c02031b0109020603040c06030b090f040803040c1a070c1d0106121b03 81
    0x600c4403110ac40000260341d010003c1911a07a02c64a03030301180c01c0c0810403240302100024201801440281c0d49040221000103d01c003043c02e146816550100720a0411030404505d5030f802410320f803e05280300400340d50f0f9908548000140201007081410204075140c80c0d80c0c064898181e4820810320440fa2184807240c000c0955220b041d2240c6c145806d010341c50b5459500321282036101030003505030b59483d17441d8400703082025504280c000404119031000e0070290b42c0194046c114070303650240302c0b10810180303d1a148060708500daa29103011000205243c0000c12145034001c0f0303144d40c115142c0d8443c800c1d401003c4480002e5088080001007004206500c10300e01d054a4050b2000c201105d00e400c2800080d0004542d0040050207107030126020401d4031001c2c6600c58481c08020700d280e500c0710f00505894500301c101144100d40400d002081100c80c1c10020003801001c42481c40d508400151407500b108103200f600e0034001c0c1001c3d182c00102154000b441c242400c40300a010213a00f5450007001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 837347715 1250 837346465 837346481
    0xc0d0b190b0a18030c0e0c070609061d0f031812010e01021b01060605030114210606210703020105090d120203090414040209070e0f0406080114100e0a1508030d 70
    0x18421043d640d000642c10350310b0000e4039040b28069502906101c4103120404014003085150002407000301c001800d04d0060141d542c0c4201c40200d02c0750150000321041e01840c0c208010305422040d004104c54a00009407401903c26000019031803a411000c59a500b05a5203481515403d11a4080310018150003d0003909218030001554080d10707100903080390920b00403100061340400c010401c45006080d020190b00f0b000b001e80b00c49880305444140404440c0101000c2c60300101d00304041d42c600782c41000b900b00624203407840c040c19100501a00c4205500009040c80404200000303703490740c0a60030b407401d50001e0184110306050f83c0180d540e80282609a115900740010080031500e000015802107502a0264055441d5440e00b501c0303000d40c120304182c001d03010301c3c400381550b50395000c0d18006000c404000100c0042d05c060340b04041c9401400f401c0901d110340820404002d0003d02694030250b010000110f001990900d08980085d03507106c022184408189202c5220b0190b0184c0f0f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 837348965 1250 837347715 837347717
    0x609181b0f1002060c0a1e020a0b0c0705060a0f02270307060f0e090c0f0a20030c0601140d0b090606040e0118020f030c0301060b0705150c0d0b190b0a 66
    0x300545080e001c00ca660b0410303001039001a000400858081c400c014040c11800a003828044005034490910580307010240c0030200050b8030065148040c0f01c03c06418503045043c6c603274031a10300034490300c0d5903540b840098070b8103021955130b414003404111160305403141c0420900746907111003540708203100c0404000c0010b80c4640181c1030001002b5004040ca10b240c01d01c6a01c50b2181d131400320007044114a001001001c035503008001a0481e995200000e162901283e25541403003034040d5840098045a0051100e55a100700008965004001815411614005500c00300c0180c8070300070405d80307030340010300500e4001282c007031020012010030510b100b0392058400300014010101c005003610f0006122030010300d1f51028002c007504040b000311b00d01d07800150884084101d4100800d01716841e0340c1c044910442c000c9183c0d402c105003400041da070610003000b540002d062040b006c0440d0310030207420380001540c2d20b0341d0004907200d03158251091141c0c4110304141543d80c0c03081080e40d40c88884200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 837350215 1250 837348965 837348979
    0x40203271504062408030a02100c020606100c06060e01051320090a181b030e030f21070305070e090c0405010311280e0906090609181b 59
    0xc524654005035000050114a88480d4942c9a58480c14010440681050310f2081c140c1e418142101018500c10002e010080003113598805c0413200034100815000c0a940d0242040c50107440b1650025503240c100728202c8401909506a100a40e101604402c0090845050980c00110785016111042c102c550654154101583d000303603e408642428041140b40e0307103403441c0040b5030840200600390120700035003000a10358031444021010780541c0702c4405140d4440031050300e1386c4012440300da94050303c1d00f01400b52060384401c094407405a09043e0781158004260007015021913010109140d851544c01d201504080c01300030080d01044603110b01103801840240707c1400c0c806400303889041051001e90072715080100440107080704615100103420203005c0050640240c9262080b0003100c101200b080311082000034101403014001c5a03c21000d20080284d03030f88070000c05960082c022291024107955940d5051802449900303003041c14400c607007080c40c000402100004500f02c04542c24 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 837351465 1250 837350215 837350281
    0x30050a0b0607150c020a051b01020f121c060308070b180705060702041805120a090611100c02010f09032f030706020d060509090d08010803040b12090c040203 69
    0x406124480c5032002403010304540b890b000070703510b40e0f032022489942030300c1078544100c091f455040c6860b915818518403098030400c8402150b804101c100000700109016140103022501440e0041c01011086054581c3c0c180c82e101d580c0200d40c0c400c0c0042c582c80b41d46140c0300d00140c20003040008003220f0b0ba00340004100c7c142c103003c0100243d904121240101003e150144e030341c5c20f00001c0c007d0700b001d030400c03905000300d11400904240010207244e074404003050384139150b11744000c0a07891258840c034103000a01500c030506101c041581300c0a026040700120f0f004000c420124018031201c10b41d0760000d8074041c049400c00d944007289030300310000c2c0b80001c1031051003404085c0c142e4400030500c4155a0041220314005826074018003007400b0040300028925544001080002108035068800b17604010028481603402910150140450f00c00860400d0309000f02c03142a44034148014032000c3d80c9000103480700104008034503d10102038030654481c24000d900c411403074400794060b4140e0f1401101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 837352715 1250 837351465 837351469
    0x60a0518190203070b18030106050a080c0f0d0c0602030a18050d030f2a02030f010c02071a16030309051005150118080319090803030f04080306040e0a14070e060a030330050a0b 77
    0x4212f0a071070b010b00281030034100ca842044848a20b0400d0f0306e400800b01807421000c1951004240014250b6402842d1303101d0001030b000702107940c00060022103100800c424851a00d0b0066040140e580c0350400d401013041c0b030300003515016590703140d90300d41d0940c0345040240c0000007020701802c180b0035002ca6101900c2c50b4900c90903a10540791420040e80710b81410403c60300200000c3d40041810b8102500e0010743c2c9000049800c030350300d002c1c1c0100b6110027464081180401400c0d4803241200700c01c02003800d007103000c025914400c0e10002d040083c2402411405455403a43c000205001b0041301ea0b5501e040d0510249401c0312030605010480c01580010007090100c01c80b03225010400706054141d1712a035440303425070000f80c4000c5c0c210341c0d50b404400e5040010031040c0407c074080c03800880341900e140f03003e5103861015002101c69180803818840c4540b01c0c4a83c01003569410704102200500084c0000342007944c003085031400d15806034107a0060030b042d44c4510f000c1e400741c100a000270700d44107003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 837353965 1250 837352715 837352729
    0xf100203010305060f040311060a0207020f060a1d0109120c050120120a0e0316030b090f0c1003090206130609090203060102030a0f12020c060a0518190203070b1803010605 75
    0x40b018040e50031a00015100481c0000c225030300500c42c4c20140014604032540e00d01d05441103a803a84130f19070020390f103010f40c500711000c903110880446941c0d01e010700995004000c00f0700341c0d014010002d0500950a5a68090000840030340310f0500e0000c00304140f402c1009035481644030307040c045807100d40d04c6a034400201c107000502808003001802c1c81e200340315001c2620b5202400d034000b00221202c19204035a0180050711300341d00ca00444800b064150308041494a10240c9403a001d40c5c414040c0c070f1841c6202081528042c00201c8241c0c0f40382e441400140c010b00030540000b0341c080d00000e02d494000d0144101d91040da02c00c2e50310700f03900a1311061b00f68100c5c40300750360081c0503030301c240001c0101c54401c1c040c512092030a0b1409001d80602941c0540aa0b0440500d50b030b16500800100308803c01584202680034084c0c02c0982c0d0340c101c4074122251100100541c0d40d4030303281e402e048841951403c00132900100803207600150758040240c200d10b098511a011071b8425400e2080c00a40c6240c218 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 837355215 1250 837353965 837353969
    0xb1309150b18040302010207140109050d210b0d060603140105060409111e06030c0a1209020603040b0709080607030509061f09180501062408130b06130507020f10020301 74
    0x58214504840214051103100034010402c604547d0200050b1000032224003810500110040002c100030049203400c6080c04441504e01040103081507107800b224200c03441103a858848000000b40b0b151180010564080c04480080d0c012030401d517000041003000c490200c09444001c008004644502040009454010501821b1441003040d203e82c50300c2c11603a02d03860075400400a801070507040c00400ca0300e0700120b501c4000324070301003070601c0403540204621143d80c051100030000d0012903070000707140d4040a00041c003038041b481c00041915000f20850405050b070030003219542d2030300c0d0310018050312080301c4075882801000041803807071040060324854000c0c1450144c50341410850628000c040100f594841c00e241513074070001040d402c0c0f040c1805062455000350140b445580400740031040c00e000c1504002c3e0700d40c10807244400704824010800d90040c10341e140d0f61074440004240c400b0f04c0402040c0c0d50f06d003200b40005140c00044a1044018810556801054407034407042240424 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 837356465 1250 837355215 837355219
    0x31014030c1c020d0b0711010509071a0d2d0c0f032705010504050c060a05072006030a050403030c03111b150a050708060a051c02040b1309150b 63
    0x40c0d01000246082c110020b40300d40d0340e05902c1c084240300d8002918041150342c094980d003040f030741400245940504195801240c010080c0042d0501c0e00e14640d0f02c1c9071078030070003005000a00344104940c0401044500c00b18403000144010407607240b0352a00302000b007214045161200e035500c01840c0f454001c0006400103503c0704140c0d00341d862001c0e000303008910700b04144c0031141c0f500305c2011004841e00102c1c1c60701500c0001420303d000e1820901e001c0b054652140700d01014402011403541c0642141c03400c45c5d04c801894201c40c12038041d030b4884480707000510707400b54020041002490303071544903c0c407940c000d540c1404454280442602120068112141c0d0b0b0081008403907640503940d4845180c0002c05011544180340c0ca40300c50650382e0b8280c9040c03030030607250411710140d503501540e03154020900721844156145004000b400c0030071003075042c1c0403446103038100c48155903541d403100b00c00d150041c2003a005102e0041d20178004010900d82102c0c040503140360004a0b014500c41d2007811000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 837357715 1250 837356465 837356473
    0x40b0c1603051f0605030f0f010c0e28050d0303090c0f1a28080912040e070f0c02030f032d03060120192f0d0318060503101403 56
    0x8030040000340075110f1441c481c0d060f01d80744006115241046070013105503200c0080c207038941411501da420b440306240c100007001410315045809503901303810360421000302d1f041050072104407205030409441d503a10866110780c924409105064064010b098840d10458487c000c44c5d490300b04400c0c911840d4005ea01341800d01911345500342070004c1c014202502501040c2c40c00b0300c081c0c1111070300c1414007100400010b800c4810b20200031401c10900e51003145c03400c0581d0400342048115440080018600300812145440305c0750541d010321692304101e42c0150668031006030080f0302d00d6503644500b48108005101014010005400c03c00a01869443c0e01002e80741da200c910045421080600c140030340c5550404407031044404c104002c2c8894020281c40f681c0d0b190890402c601c442c1e50b0b5202031f129007420b0500350f01c40c4508958500815040031122440d0b100c046040888160b0960030340d407150040113580100d559500800518869200030b01440c4126480303030708040462003000042501548 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 837358965 1250 837357715 837357733
    0x2402151003050d210b060d1d0708060106050a03091b0603060f0e04050c060c1603150c08040b1b070b0c1206150307030f0f0207030e0306100f03080d060803040b0c160305 74
    0x9a507008149170f072030010850360400c10300000d80403c49a40e001080704c3c840b150f0100303a0546205000e0741c0020100c03231001d80704039854080044c10a10600c6030040030035940326680b904015260b0000b06692100e29503007540d040d140c1e500940106018081c444140e141c1560009200c00301c208407900c202c0e0b0220141c18040d209a0a00c1580e4208013210899070185040001d000304d41d070b11801008600803011000d034030032107001e400c08030b50440d24940100310a144c03c01c070100e2055541c694001400030004031604035640b076403400c50b004030715005020340b440c43e050000420f501c9014000d50a01445444d1440d04d49004201c4038a80c1c0030040340c0000d00034400501420b009a00042002d1070068020407140c81e40c404501c00c0740d12510003240444d0203490306c000f40741410000303242e000c90720342040c400c05400d1070310000b411166440000c0c110000080d00c0c8001040300c1c5c00c2000280000b40459446903100c091100542d00a4000c0030b07042d200e21050308a011100c0c10501c000c80e90804054440c4035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 837360215 1250 837358965 837359027
    0xa0b0d0207171c180f14010209030f03030609071803030f05040306020f1210050d2a030507030b16080105040509011b0507020a0506042402151003050d 66
    0x1401c1a4000c0c1e450068018049884050000040c40b00c0c1000e2401c0f9854800003140d02c2c001c0701c02000d0741003144030000c8040c1c00043d00410000780d00d00c2d003200c007007420100d0100f101400f91081c0e00301d02c1d8043c0a1585d5aa25a00d000800b0b1401000115012290f070380d11210b085400c034103004203910b404942c6941c1000464020103404000b0909407508515041e10b81e02c421301a81d2110801140350000050001e104061061046800000c01d0b02a00d13020741c034010020380b01c01c036240e40140842000c4520300c06450701600c0d0151020317281d8044c410741e29a07a802c02c0c3d0780b16421888142c035840060300008208006201101480c0c41c100d40380e06151380d00b420180001013000903c0d140c1250361720711807240901c528881c045004141c0355a50350b51590548107010402c825540142c0c0511000d110034003070b1080e0100400c1138a8500001c06404000c108070403881c0280c041a50800c01e54004140a075890740a05060140c03401001200c0d035011100404440725200302c00c0c40c100003d090710340702c0c50007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 837361465 1250 837360215 837360217
    0x80a03061410170a2004090b0114090609040209120304060207060813030c03020c090408030a060506070c15050706020703120b06030709210c0e010915030b190e06040b0a05060a0b0d02 80
    0x2104000c280010310305510303120070141e0741d60207031007404e0404c0c00306d010400211140901841001c080c81e00c50840324608003005501d00801101512a01c00840c1854081d101c1c0d50558078010401030801031061a0180c00ca40c42e43d0045c050707400140609840815160f000300c42060080c06001c03e0140d02c002b50b03480841d0141d01e00002101103000d0000b282c0d219980710880c0da4040c9004009690f640d0030440b2144048400640c8054010f08040c810030300454000c0c2c10003812240141450b481c61040e40400311210322074050000c2c5070b14030104940f824076900209000e03e20300c0080d401c01070884840304104140c0800c6031100005243e45a003400b0031841e00c400ca1170036110101b120191040303d0350341c00600e00110341000400d440b402c401003100b0005802088107131040780030900780032421500e8081c03e20b140141030f00702c0d001c10f40c140d0180122081c0d20101e1054154001c2d148141042d240c00c0600003025205881030f241400c0210706c1500e4450b4120303046429401d0300e24907102c1070800c902c0103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 837362715 1250 837361465 837361471
    0xa0b04050f060c1c03060501110a060c0e060d1e1107020d080d020a020f10110a111504051b0a080d1115010617160c03050c0703080a0306141017 63
    0x1102d02480b007800103075000c00020395625034043c03143d0503980040c030006046035115404103040000074003103044143d00128031040b50303580007000401d1030003280300240d0f040700380f81c0b0009811160008200b10141e102d075010070540c54030051010720500800340c4d405e0980302c080e00004180c0c40108900401031074007810f0650f0084c0b06000b41c509141e994039040d0100e070030000603000540c002c5503003039030740709400d014495900c0600b01040040d9140c0c2900031702103014101c10355040c4100c0d000540380d030740703000c0028030300c142c90078642c84596107030502c2c0154680c400030b03031400d80c23007650340300c4100180c0f50540040d8203a4070300720001d011550302001308403070f035520350640c401003401442c0000c0841c100e4425050702030b040f60388031140c4060000c05c0c210b219140091030503441c85284007000007000da11041c1c103602a13816240c51034442c03601c64000b83c1000400d071710080a40303a0004d04014080d8150f084242103c40f045e0130711201e0a01e020a01c1140241314040400140c6440b103a00b4044a404083c503070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 837363965 1250 837362715 837362719
    0xd0b01020c0a180e0609070510050c01050703020d0e0c012a051617011514061b010c03060e0c030703020c1513110f09070818010f0902040b0a0b04050f 66
    0x80388407440c0001c5002c08100390000301e400c0081c1c080703641064809000b161a1945040c000b0b05da41d00c1c0400d8001c0d2a0285801081e1080e500344a060383c0046c4914141e54000701a1002040716041081d0040e009610007003513110f82c0c1d800c022800607224408141c0d1220440706840c0c110f1f030b11186901c450303c400781d401007103e001480081e900b40070510420007640882071260200240604207241c81900c00209001070a490381881d54520540200c0300c5100112030715214032059914460000410f02e0203210640010519880381e40130b0303020b0b01504800d115654135102088102e40b202c1107802e00500c1184c41d110003000800104020030b201e980103100b02c01e403d000b42c405040742c032003c0e1a14200280c500041600a040d40c0e101070000c0b00c101c40c400b03d0400c441511012200f040441d0302608000c00c2d050501c0081c400003a418920480580350050340c24008011201040001100038881d034074069002d546010820440303818058804410356a55200040c1013a00c0c18081044100c0c4200c0b20035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 837365215 1250 837363965 837363973
    0x703080c03090f0f0d20030403020d020f04050411090105060403030905060a030e071409100602191104111b0f060103080a09031208041203201305100504060815060d0b0102 75
    0x103d0740c3d01080c49a1489181c450003d0480b861880b42c0003031402c0c0341c1c1c480c0340180002d0707486170701d40e1032800100715000c03a42e043d1041c000f0440e0300d00010b40d000fa52006455000790622003040200a040b62100c0c07080501110343c8600383e41c03204203100090084c1c1c00000c0c0840c0051606008524102e0301828080100340350204480001c041304608142407030307100041d541c0e1483d28000c564504003103036540c840b2420403c1100640b904100035958a10260741d20b0401c1400b01c0214203010170783c04400072039200600705026224010800c0344481d0b01942110034040d40c1c04107454a4550080340c1646140100b0001340482c4e425a200c180e40c41e4000c5214205110184100200140d080c411205260781c1984802c0020310b442e042c101d400685d1110010100351400907071800302c0d281d150f00304004201000e1036903140d540e6800c400da81b04035241c102550250070100b500e5103040d408002001902c04998920050ba250f258040000c042406521a84114244050b0611503490b40c44609640e40c144122 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 837366465 1250 837365215 837365233
    0xb071103091c0f0c090e03090f0904111e010215160f170c0702011707090b0d021605010b10020f1507050d0606020f01150e0c07050a1205030703050c0703080c0309 71
    0x40300709070010f41c08440c0c029030202c04000f407426520802000b4244036014529006000c0001241c00704014031007031003506944042400c0c070241000088101c04040d00b4004400104264a444040c4901340e0900502c80c04c1034000c40040100e5615010350b80480b00c480013120308244c241d402c07070307101c5681e181001030946231014010b01d404c1d030843c0564807022905645000c2c90000418060790320401c3d0b4403490744502840040c81d4000c0d803490031100400c00550f140d103a204848006841030543c01d0721340410510f400b80501c841176000a40000007284d1402c0780f091301d0081680c840b0441c0b9290344144d004001000307141d02440459590098035864280d180680d1341e08064202c4815412060050703102d0901030070068001d11405040b4290707980c48001c840c0ca040c00b01816004010201800c4210108009040101c200103130152158031110454984081b01001401500119035900001c0c0c00e040118440d070300d004003140d20054040d0743c0d40c220741d5030340501c8101a41c8041d151031070300c2c801c901c90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 837367715 1250 837366465 837366473
    0x209131b05070f080403032a12030e0309030f011a2b14011b020124090e010b09150307090b03060a09021c03051306050310090c0e1305040b071103091c 66
    0x2040658400d450308803140c0c0704c01202c512002c1003162310903618400c000100c40416440749140c120407107113140206203059080d103440d04600440d928181c1610450340440e5240c0d0307042d04214200c0c001500c6110310400090200036a4586074400001701c0c46400321441c0c5056190200301d40b20718001c40b80b4400c0c2814a002c050f0840c0c000c0201c2e84200204078049200d500d9083c051420b0540f0300d0001161400c1d01d0290150411036584115041141d4524003d02c800000790090000040024072140c0c1c035242403141c50310f00c110103001151081c080c20700d0200b20302c9094822440412009001044e195a81281480083c14034010070313644568410040341e40c0303042e41120042c20501c6a0350765912541c0781c884601040e2100e800140a200c414001c00800880600001c01200c80c0c1c000041090307000c1540955007a462814515000410000400c1c0c412425800c400d000e00c0c40780d500094144c0e41e41104423000134040c00c08442d15082003001000718a4030040c4c1c145641884281c0c20012881a03803 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 837368965 1250 837367715 837367717
    0x10050702240901020d0306081e010e060c0301140108010308030c090d082209090b1914010b09030f010b1c03020c0d0f03080c0f04090c051c0209131b05070f08 69
    0x3021161010700142c8100c0c6540c0c140300701c4841031000d00301401801e003880001600c51044a00034001420440321b20100c4682c03d4001e4800c500c00702054405900700404000f256074005d00800c00200d9821545808a51080300254126504030b08414110789849140c1c1c1c10742e5000341c0e00309600400d400201070200c0c031b8460080c000d2141c0c140350300d00800240c1c0c2490554513030503800080300300c0c03502200300302190000035003950041070204028800070000030030360014044a1181103140c41d04400203d18140e00400900f0046801c4044462406015000070b01b0313070781e8070250300b0341214000c0c084814041040d018101c50611900540e44203000d1840840c00007800c02e6015160005201d2400302415084100603821501c29018181360400450820b42c40e8440c91003040111a42d135400f07440b03464840c10607507003074018038403039914030108114040740a504070151b1103218141140c0004080344041c032951490980482b203650b1926407030141074a07079402400c41524014000c039401e01c00503210030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 837370215 1250 837368965 837369019
    0xf10090507030b12010c030b1c0f020a0312080a0f05090d0e012601050f121b1c06140603030a17060f06040902120705030c0912030c122710050702 64
    0x200009440003503586c001d0948662440d224042c0c1c400100d4080315000120801180d16000a1510900b40a074408210440150351010f88244080c040d108200c1d13902484040c01a46045400e1182c00d4255207031200b00d0b02c0a8a502100d68050005030180d41c1c001d50f900700758048141010070640d0141d100b4043c01009070349505100c040c0c0880140594545507001007106081501d24070880e01d2100038080d0380c0c01ea50004040d64401d01000c90f0000d40d203800038068100420041040e00361210300e0700034060406034410320707130111481d00010b0040c100002a290540400e0740c3c0d541081c084030034101e5003c2d070060561500721400d407003041007684545008100810400c00016a5403114600b240151100500010100b080400621042400340801d0366407c440c11185800c81d10f11150340310380340d4803034500405034078003a0719070201c0201d01010142100f050205504410550725403070781d4503900800000780364400c80d100c104656481c4154040c0c44241d01c040c010001e1900e10803801d0102c1081c40b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 837371465 1250 837370215 837370249
    0x50c1204021522030c060906050301120f020a030308100e070c0b040606080f031801050f03041e0212010f06080703081e22090b0411030121020a0602070602060f10090507030b 76
    0xd46400c000f00200321102c0001805145040580707c0c3c02d0050061141c40184500d40c1c040b103000f1050420b002408111005c000d50042c050304800e81e0707a150182c5a5002103e10300c02090421000180000b0b0b4012090f03c1019555180038038a900340e910300022120180041d242c459940d8408a070a450820020222014200c000c0d502c4000c0c8099036801805007402050421400340509000341070f212058035005075102c0e410030300342800580741409000d03015401035440324005007450824101907204189808014405021641d200c80c51503039540a148401000f80340204600c240441403d40000301080300c180e0b034145403443c8001d41620303680c141e0141c1c20010444402c10002141d032031080d890f50a400b55424003c4a202c410b440195020501c03650569409a00203098840d103011039200120b0b40c02480c070004103407100c200075942c4506000d9000544030b96008116024440083c0328403e420f000300e140b140c0e608100600c1d01800c4c01910380030030705895181d0601c141e1f079940100403d50210b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 837372715 1250 837371465 837371527
    0x13090504050f160f0302060d0f140a0b0a031a070c0c0303051810020714190905010509010b310504020d0b04061d27060106080901050c12040215 63
    0xb404003180c1c108074039039400782d0354150042010410051152003aa049a4040321055241c01c41c07003026101601d00d03250138000282c1343c40219540b0300101c2a800780591080501044501222001d002c01c1011900010701018180342003d14541070356074600d0f03071010840c80c02558503030540c0e403980e480c401c00b034004402190380483d01080080c1420000740d1124000c4a07400d6007240d51841c065261401c45c050303094642c200815600c4035031510030400d11742c5090403450b0003007241e071010100010074080c0a070900ca02c50a800010b16845010152044488498030740101c40007101104400c003110a08500d814103090880010b1310b035a03920150580a180c0c00707010410072003030810002181c0154111b581404143c1c40304040c40542d40440542c0250f0b600342001d500300342980e241114001161400740148140c000110350160310441150141c43c400703000744000e45a0310301c1c42099009000c3d620b0109a80700300050090328007420101c581840a550981c40c2c00300207025951425000840642e5000c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 837373965 1250 837372715 837372733
    0x5060a11061012150209030703061b020109080d050603100c17070f02100b120a03020a031b121b0b130c080312010506180d030903060f201309050405 65
    0x30500209a100612500300d500c00d5060124440c0c0c410b120080c083c250030616002d0301a00c031910f44c1280c07612a402000c8600f4640c0d240b0340127014060710495402201c0544040982d064014062035160300e0f0f002c107083d42800544040e20000740700042065500d885040c482d0481c1d90303502e12400400c42d21641e10407500301058410105084006813801c801c200115402c03807902c560104141c44043c1c60360f400820760009003000950700b1141c0c424040d6280c05560031003401c1640005692002500c43c2c0c0345c1c030104629003407100c2c2c500c0c4541c3e0000340841500b0207140e80020b108906042c0b040c0390507042e2501ca000b190700c0d0311211103000c50300c41180c000c44100c41b5062000f400c00c41801040004010b40c41d200d140070451170300d010306100d00d50250901050103501d4480e0b48006001c1d5503c064404620f00106007030090082c61140301c1a00c15a2a1400e4030f03503100700710300941115176405000c0e05260040c1c0340d424182580451003d071840c0c40008000306036a070305030248500075401103004080307400d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 837375215 1250 837373965 837373997
    0x34060f02090f010f0e06070c1503051603090213020f070c03080a030b030a05030a112b09050d053408010905010c0503100e0a060b19020d0306080a020d0203010605060a 73
    0x180801034031a06219500d440146080da0040000108500c103030f401c41d45461f01071408011a007030a4103c00301c000e03404040700a405504d039004034070680c031154401112056925040d000c80d485903c0103904203140c0030804020301001c0d0000c000f100024445c06141440c1d588424459102c160002c035000b960000c0d8401c60240d0600950800800440c003601c41c000302c035618180d59100b01c00c81c010900c5548032029861490900018140c070341c1a000c128001408100703d84807082c13071251103501140b030901d4082440d0600204440300d507070348880140f0964803640030100d10058205c00280d075030082002c020000d10100300c6040001c040d00e0700085a060814500310f42591085480c9504004090042041c2d0b680c90040a5003200e030601120065900c4408210b00600080c0d0001c500c0c0b0100090901c000341e0701e0610b68043c880c10f035820b560300d00b0311411045064550b030740f2031414036074031420080025203029841e8266403403004000040c0c0558410119030280c0000080002103040d90103174107250 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 837376465 1250 837375215 837375229
    0xe19020f0d0905010f0507050a0c02190515040e0f010308180f040e0105010509060609031c02100c0c0c09050c093601030b0a022704060f140111010234060f0209 70
    0x47c81410314a040040040e0010081c0c00c51a4010f1300c9241403011003941007600d8a0080e01900007e805082c9c0070034110f0103017405500510441c402c040105d000141600507042505041e02d505c041c0700d03881c051045207020b080c540d04403003040d44007051043c499400d680300d104452525846400104056250004004c000d1400030071590280d041007008098030b540100d41c030001680c2c40450b12040c075010440403860040d49100301d1a80600e802803400c101c40d0004101c80450303210302c0190700400e8a03826801c040c2c48003903d030b5404201c818010700c82e8074a010158042c403040c00b0400c1a9a20aa00744140b00f4449040341805030f000b43c61005105100c16184c46980c4000c1c0d0b80d505629001c0211a2910400060780040306160f811a112403442e5449400c040004c00140b648002119140d4880d8980805140a901d02141001e8200c071070711074040c02138407401d01000500d88005400b513628104c00c4400b10a03484074048010840c4000614103200711740d00c40103540c0380145ca420aa100780300700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 837377715 1250 837376465 837376471
    0x2111030303040c03120c1e061b2a3005120103060902010c0204050c0903010e340839091504020f0318070e19020f0d0905010f05 56
    0x2500300300104404030318404684000c0b00c0d4406030544070b0090401003107030340080465005101182c4011100000c04414448416103405a6020003040a10340c1c011405502d01f280c9007800710700c1003121054100c02c09401c41c000425100e031204405241c5540b40049004680c140c50100d080c20305505007105048560303084c1080d40f41c20a645014104a00700c1501d84c01448014900758075403d40300b045910074070100c3c4406502800c14401810250002c5000e030308240b060b107000390310b008084030b01a07400040c440303140706100c0e410085c06489029800b0390001140c550f50380990300d104000581d40410031541900844000146400ca44845185070081d00d800b03c0c0d02d000043e441d1110070303950b501c1c8401a5044492440130410440e02c0d031010502900030b5030f4603500144004810851f0760720f1840c0c51160304810710400e50b584c00b600d9000100110354280c441040181c103020000b03400d581c03103500801c82c0c0302c0b12005071800c240300c060f103070303015154181400c03a50780c1d441302c0300702aa440490150b00c2e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 837378965 1250 837377715 837377719
    0x190207060914063706050d051023010311010311030f010f09060303080612070b0c03030a0b03010608030a110a0b0915010801110702010302070c2d080a0f0b0a062111 72
    0x310484e20585041e130b01c440041052001130090b03604507482e620390700100082401a141c20160074043c286603442d241001042104a820f2600c1800041500e400a40708400048420100c50b425902d840406000710040e20341415034071583c2851886204010b14482c84a01c000d071032596040c070114594080d0346a105603659801c020007400026003184100303074071810030b4400e50040c010480800b86081503641c0608881c440c001400d482184000c00118414140d0718420b000071032020051500b00d03142445406950303041400785900aa10900d00c1400b149451000c03540940b1440c0c543d80d600000507104454152f00c016941c0c00035141500c05203004040782c0000304142406071140c01068030600300024100769000601c001000800c0c0c40d07030005010700d682c02543e013a0850411841c0001c222211030484900254009800f01c4006544902c0a0f40300400b48019031051707a805101074800b4054444039502d0365404030702d0100e07405103c4807031500020402c004640d14202030b42e000e2400d8240e18 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 837380215 1250 837378965 837378991
    0x130203012903041a0702071502033c0a051306050702090f2e030605010e01080f0f120904091a2d0106180807030303020d050c090919020706091406 64
    0xc08134100f161070b5400b00303210710244181642e42e550200e04003c100c3d0440119090b40c40b9220302c54941c000094100e00b410b14010007a403d9201c03035104903000c1040c04007048c0310b01d584500c800c100b8550021349101c400034100035017044a0241c02d11a800d0594021030002000803403031000794a0564881904a1541c04489000d810040c050030304461596290f028090660f46403201300860781d04c07520f4010740d000081080300c1d584032000c0c40f110410030f00c42c58030070348a10301c0810b000c003101113a6112400200801802c020f080110011429000040c113070f944250f5610070400402c10051201c032031202d101640195920740700031040b50110040e4403800d00d41c205120243c527182c60395680383e0705450680c14000a15082103c00f0f8507030040d070b07411002d545d001d04039002040582580280c0813040e2403000900446d03032403096400c0180030303c2e003680b1b601c5001c14011800348548100c1c140a15248190090f01d01202e58403003005564220408540c100c811f05c1c0b0000300c480b01071100c107400c00d888045c24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 837381465 1250 837380215 837380221
    0xa03051b03090703030f120920090f07120e010e1e03090108180f0a0309080105013206130e04110301050105210118030201020c07050907170402130203012903 69
    0x303030780da1112804024240110400010482c1c0e02440114040c01034421f020700c20350155240030322a500c44101090480c83d207514958501e07140c42c02106100303481201941445a558441c101c850f01c41c510011240c45075500c0b03007003140340300a000340380e044e94051005000029001550729420141100c0b400c0382a003090104030f81c0b503039111844603003245000c035901c0c454403071108910b42015010b4116000d1445a0061501007581200070b42045400a1000308880d0307980754036203c3c45c112151070071120f001078090f42c1700001c108110200070088010b04541c2c140550900c4002c04d65549402000c0070500807070030801040702c41c203424104000d040d002070020794035050100c2d000e803004c0c0021a21070503030b0050003c01c1d001d09500c240e045003c10403101e060441d00e810040d00070b41c40445c000c805405502800320710350404520041c012a0035a85a81c580d881d202760701c407a00e69019108903030011402c5101401550389001171800780c0314110300340c0f00c00e60842c9210f0144070880c100750b500c0700f6410320030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 837382715 1250 837381465 837381481
    0x91b0504020a0c0f08090a03030215090d0903031803140a02041808030c07060f0f020a020f01050c030c0f0f070507061e050f0304150905160609080d0f140a03051b03 72
    0x83e4050b0698031080021121115241414903070041944084e0040e000c001d001007459400103c4800d01c010328282021141c0f18080c041d52940b50700f03c100382c0410f800d50801c000007442115a40d1700900c14092950f010ba4a960b00d0700c08442082c00c00cbc021650003401c0380ca0035480d09200380041000003031106c0c1168401e0b03a45101282c04001c00502c2c1c50700c0e02003604410f100540c0c000b5400c1883c070350401c10426024005e10f90094200460240052050082c20180da050500ca035501520b40078011500b560740c0c80703001402d154064204051a004c060011580024000c005408003510482c0600f603c01c0c02d0001c000c0c0300d01c15412050300c00c20a042c0c210742c2707202c1c0c001c0700315041c44c42410307042662036036a410030710b00d440302004007220000e05d441191400c3c00f9020618100001c1e6080d020040c2941d1090202e845c0811806a8405500031740c82490641d409a0255a0000a5828004902c4500719207050715600031003a0038020a8036482048466120300e4555880a4481d0401500754103207051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 837383965 1250 837382715 837382727
    0xf070f1503090311030d02120a02030709030b060607020307030b01052403040602160506180d02120f09030a020d0501020c0111070f020907020304170a020a090b0d030819091b0504020a 80
    0xd80501455036030011071003814858003611045100e140100c0760b4030b0b091100c0c0280254002c002c04d18070784c90b002c00030071042d00581c0200c90045010380e48103070940e8155103d030030980384040e290303030780c0302c2d008001520058a05100001c0110700460081c0c0107985001c00740300a401d4080703010300350310b86646141e41911819100b96904550001e40c01600e810f8014040c011f200d1012901400700c4c86040100300142e006078603a10490003907003068401c260300210701603a0303d000a004140c3c40640a02a0f045003c0c0420090809041c008084908002c2181c01094802107041d0050710b5030f0350005000d0100c1c080034000c1550b40381c3c6140210f442c0940540710502215000790009100f0504d00340801d050500c01c100340e5010b021800d2850700c0e4210604201e981d945100f0008a010350340b80c007400100700c00c40f07108144643c03c020b030800c410f080c600d40d0708031040800108500900940e02098510a164a1245440061281011241481c41102d605441081c0380e80110300c00c900400c40d248006602c06 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 837385215 1250 837383965 837383999
    0x15100e040807030909241406040302011d06030c070c061701051002100c1107081513080c0d030c17060a090b030307050109060221010b120601110601080f070f 69
    0x9a2010b0b11004a840c044a00d4041c1d6400306529508048100e40c10745440b000340305003200100401c843d081c2d50780c0703a0032810240d5084029071101c5c040c0401c2000d5402200914824a400c01c98150b08000e00c000050481d001580c1c100c4070303083e0104088040007280d00d0b024001d800a4145000705072558502c2c400780000c14090203001e41e20100c00c40c1d01840c000c0041c880315a14812050144001e4244001c064003000b210740350491040d03160005010340c0c0800e09490048002940300284d40d21030240e4000760286070b8013122901c070b040000f03844442d030030b20100c2e2a281c1566000b0030000e012007401050492400601e0019100001c1800a103585001c03141d0101d600d114000304515001c0360010b41540a0a0030181995080031032000c02c0203240e80c02040c10392103003405640700003207040020700c1001c424080c0c1c00580c60704102d00b00c0002e50041d05c107984044145803500c42c11f646100310500f0920b080c1e01c001138a80c0a82403034a6424010b02600020702001c403403c00d503551500309c81c02d05004050f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 837386465 1250 837385215 837385223
    0x3041d0108010e0a320c10031a010e01090312170108010e15072307031803030c110a170c040e0c03070e0705070b01031a0703020c0c040b0402130815100e04 68
    0x7041c07080c1481511245e0803420010364203413100300d29501000c0d210600921494840c0d00008000300000c0d000380b081d0410764040e20f41001d11109180d005494026030b0303805481c148804000000700140c3d20250030380c0f51152660f580c0da00d810b10707107000e17410404041c3c1140c0016410030019400b1030303400164030b1040042c0707451103607590384a40070f0039940001d41000030a12040c40f100302490224480008200d814425580d43c00e054154009421031214103001c01000202d00740d00c68804a4089512b05104000c02088a0032072030780d03034854440c1c1c1e040e020b01c1103000e900f000e40850303040d00d0b00307100c0d81581800036006020b20071a80c0c1c00207506d940d168020b071000d00611101040d5034a114100340c480141e4010b030810915612800c0c00c0d04581d40221002c10003200200009550380e1003030095a514615550041c40f4402c02141000040c2c00c5001d64507801c19800d0146003200500740620600074054140640044a103800403028013410041c80c503041c0510000003042200d04003000c1903802504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 837387715 1250 837386465 837386483
    0x10c021c06020405100e1206100e04051e1006050a06121e0e03030901050105030a080406031805011104050312071106071509060c110708030d0b03010e03041d0108010e0a 74
    0x40d5240101c028040c5410407600030b4141c0b001c50b100745411008912403581b08960850908422108090751003004641ca00c0f14120342c514104031030a0489180750f0014840d8080e1107103280c849038800c07090407400070303600900c2d0700050100e1500d00c13007403081c100540029118145110f081c80d0300a068600c2181c03c210006036100100e600d90812007560081c038840098062081c204081c41c000e40c1c9030070594500d00381e5441e240000882d442d00060800c1c030181d0186010b41490701d013000075802880e0b510009220501f43c1c81c0d682e00000c0d070030300c6414920410b045071240c540c4d0030401030500e0880102c9940d041c0310001c01c640c00101c0d04005482c80500d604444295841c170040c944008000c681c0b042c0080824100810304003008140c0d0007140382c03960242d070b52000754565500701d60f40e514114400c0018641041141850128550704850b012010180011925009442d123852035a802030b80021104028a40201c1c6400b00b1440030130300502d00c040080c06000341e00d601240d02c0e8411114001c0c10440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 837388965 1250 837387715 837387769
    0xe030a05090112020d2c0c060702010c052a0103020c070905040c170d0e030313030605090304050901030c15090608010b0714030a0815121b0402040e10080c010c02 71
    0x8814050801030030f400640c29501c4040030701c002d80c00360a08589862001e24200c1d04240002c40070041072021140400091041d001c0103024032003a584800d900364100a0302c6800b84010513000c004410409200c48502e03281803144e00c2d0002d08a04414840c24100b600421040200c440c0000b8004c0c00c0c5e440d22400090076444501d480c2220068a1f400380c0031103480c103c824448020045440c92088030191111800000f140c810141c40e48075843c1425a025a4200188049405544890b9200b0809002c0780d113001d454000040e101d802c00d91048500301d01e002014440f40e1082c0c10580c3c60054242400410103042400240880d01d05005490f489000410980144500f49402000c00003c40c0c040d0b9640351603e060050000000300e481c50640c0855501e8084503081800050314402074982c040c054030581c40f031480344130764018000954810b80a20022a2a014121b80799010f2403c6a5005840300d04d0580c003c1d0410f1101c0a09038148140b5480300c0000da1950218000b00e0000d04947c070007224 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 837390215 1250 837388965 837388967
    0xe10150804151503080c0f0f0102190f1d01020304050409080705010605090f070f0e06040602101a030d0e040e012903030a05030a050402040917040317070c0b0d0b181602010e030a050901 81
    0x11031003840601e08d1003000c59045c003500e41940104003155001c010300c11001042d00040c0c6a058191410800040d101072001c0e0a4610480302030303040f2203052041d2858580d039000060f0640d8a0b464007038a01e0000094503a0801500f445407600402054410400901c0e1990f5200041400200101c060064009840030014030402c40e40701c410900505840c2c4075525500025a2040444180c210413440c000515000022500b10008400c00050040c6203010300d841c0102c0d85114111a6150803030744136000d50a200e40c003070027004000c4081c6c500c00a6403450080580311f64050390710000f402600304016151071281d000742140d0b8421070202010a0684031031020800508846c00060304a203c05403005202c600124000d0003100e00801080c50003607482d90580e00148102c01004144068810781000040040006407480701c0314600000b65000d0308001003502d482a81100e0034141d060742d01008038611980c40d0441440400744020010419006401c580ea48103041100303040c4000458108280e03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 837391465 1250 837390215 837390223
    0x923070f030b09010e01210512070201030f06080331060815040606050c2b0810150c03030e01020c06060f24210c040e10150804151503080c 61
    0x920310142030f502c407940c3e40300b039000d4800400b0301600c480c0100e07503403c0e100300e0028040000d46060300304001c1c110007510422100301c941d20000c0f0881c14145c441c240c607003406d4141d00c1204010600b03c0003850342c504682d6243e00040c00407103000d0556003011303440454150f03100c2031008142c030514144144551962425401c010101e0841c007607010381003160200c0c105034040c018140000c8802d00311026584401c000404141c00851100c0d00c020300d065194016510034806280c0000318100244c0d44a0b80b64554841d0200030003c3c00c40205421000345401c161b4507204141c41100298000c50a2500140e40507440d02005080184034111325006424035548101941d00d070078109511409416450000201c0325400000c0b5601801c104c00c07410007620140018614454480511420b2510f418031070400412140a0040000c0043d0a10040744205401d407070180d58481d02e0b180d014051505181c5800d100da8055210b20f049410035001070880c40c0900f1a26042d40d501110154032030b842c0711810707403070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 837392715 1250 837391465 837391481
    0x306060307091502300f0a0903020316140d05191401020d06080f1c1409090a0914010b0f01120e0a0c031203021e18090109060923070f03 60
    0x203c0049a8100e40345400003208005000590005003c106240c00c1355001126000140c0004600402c00c2c0d015608417036009041c411a5807c0c002c0c8a44e40300d401107482d000001c0301494150300718010900a00030201c4010006190031107a010615000c0d0351115142c1110011004840240500302410032612118015020003078600031074503810804c02d1400940040c1c400d0151901a03070300550003000000c0b0380b66011800c5030300e200e200701300c0415045844843d91000752034054001d0210507200c2e40e0f00d4280e00d0084210600110b0320001e9802c1c03074200b104140743e02c24000d80c5000c3c01c0c0c10054072410003005442d442400c0450745541e1812512021b031070302c040048858050039080e0400c2200d07440b052000c0d00e00641880f503080c04038a0b0186c04a1060f401c1c60808584a210000440e0ba8101c00500c0e142c0080910001c109080c1800705001000c00c2e08076684050721241305005000a902c1208103410300c800720310f4188526803805580c4110f0103031000d010424400c00003c4514001d03085104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 837393965 1250 837392715 837392729
    0xa1b1e0615050f011101060b0c0114130f030f0c060204061710050307061202160605091e0705060a0201020c010f0e01110702060301060810120303020712030e2a0306130c060c08030606030709 83
    0x1e503ca00308009172b402441552120040044200f0100b0100d0044000c071001413640305224090403610707514103541c180e1980c0304100421034646141c000240d25400175000901054445034107500302030b8000440c0000c014003001b0b4003240360340d0030011a0380000c0c8140480381c150500907c6094018207100191141c18641c0c1440c840c1e14a54804002e01d580c4800d100d11030382c205598150760f0300c000c800081030503558013017100c0d840194280140c2c5003100c010440c21989000043c07401c5600f584072030030f45005019012005540c0c06040703840d09801e0088a83c494020031036a0f10b01412035000549500060154808001c03c02c070005d650f91800d50408406850310440410040204c3e24008010754040a02110b041082d5500703207100074060300070b05a04865100240c00c2d00c21040c1d144040000107a800d00b0b0414400c0070b03030300c1404d890a214050090441c8074800d0084803150900f10030f400d010768009010001c213802c0c1d81010a01040940344c11400450f80d80755a07440c0c00b034040743c00980c0d6800c544 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 837395215 1250 837393965 837393967
    0xe0102010b120a050106060804080f0a120f090201080c04030816140601090b0a0e04120c02011808061f050a060507050304031514090f030a1b1e0615050f011101060b 72
    0x4421000400e90b20f2644180000e001c59500c487c012503560b84103407402004060107100c4c4031140a060405808120710500c2c2051009100071020819130320a0700d03144c205a41d80304520402e43d41d2090303040e544803003e0139140303142034610f5880c100f26118032500c1f0300c2100c0c004429a4100f088441d6101c5002c3d0000741116000d584914031403000303101d0003003024030603009003d0009001e0070b1982c030f146c41141c0141ca41d80941c04204825109200300300012410800c81400104030040c0610880d0050b2002da00107040624041068590001d0820100c00c0c0200702c41104003e03580e9440070303000039a13038207150a64903000c481c80c000303242d40a941c1008107145109020146013410710b52000b080c0050511080100703403a641342c41c5441d180c0c0c0da0b114032605e0704200144126513024070035604008100ea484500c5110903600c4513a00c1c9011110340e00304241040317050300c0600c4040e0007144260031801d4803040f0000c0c60300001034040d50026003200d043c4246141c044014140c20340c03141d002400d0512881e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 837396465 1250 837395215 837395239
    0x30408031306020109120507150203010f1d060319030918091b081207080f121008010e030304020907120507030605010906020a020604090b1c08042607060e0102010b 72
    0x20540320703040154501e0803640004030014865105000b0211490781202243c0c04403c039103041220568041c240c195040c046200006404031003520040d4000e00d000304054144070304050b0742e800b2030010b5500005481800d00c0500010796070101d036400381080309006207400d8005600e0283c400c480151301808004c42180020308049107140c106021140c8034000e01440100660494120f0500c14001d81500e644070010b10400822188001c4c0300450050010a04040501c0c2002505511404418456444107803e100300c00d050240f0510190950800920034020740000380d40e0b8a010060000e031141d0042d001150f200c500407c00e20ba014998040d0030f001c14a0203403005406400300b840307540d0001b0340192000545c9403010907a1040e00781d004110a183c01e1901603284007810f2040c024550010304100c1d600580c940c02032300c401c800e91040030381c680c0f20380c607040c0380301c56030742107003944082d0150042e0309940d140345d000c00d0a6055848904100b8021031555004030700400034001d1203508010000c02e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 837397715 1250 837396465 837396479
    0x507030515091c030218060d09060b1e01030b012f071d0109090611040303031505040e06041b170106090c031812020a060912110318041d0304 62
    0x50508010003152181d180d44400295941c2d80303003440d144901c400c0002c0c010394009446138004041d0002160303a1541c0075988040010030380d601105000c260165203080c0c900070042280103a206440d01102d2030310030812038809003203494849403181410556640b488914581c011a5000039102180c0301d4154024054010a40f104604003000b00c0c042c89650400101d40480040c00000054a9500388020b64688039aa101420310090708031813254803121016010303409080503000940c001c2e43c4c041445a5180507140c0b150b070f803c1e0040b9000320b0821485100340000000c0c0390340c2140d03000145007110462801c907401007415941001407031810000c1a0506104150040300070350300100c404100f0203442d503006038100e88040d80301000c01541210f0210100780100c0842d4010801401030320201030582d03541c10212601c0345012640d411000d10904031055000c04011074401424000718a409a06a07512100003990300741c3d28032070394880380d800000c03010f0100a9400000c10804594030386480703040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 837398965 1250 837397715 837397723
    0x71106131518120b04231c05030c090d17030a09060b040b0a03080c030f1605010b0306150f060f03090a020909150c030606190e0102010b0108040507120f05070305 71
    0xc506000501c0c0c000000c54000700b0802c1d00d1084581081640040b0343c2603640d514251503000340140ca42c6a6801c514071101416080c0780c82c45030748190013404c0b0180c903a800e03001400181d45010001c2000a00030032503010410402c65560f943c0485004212052520f4005102040c2550110030b918020041c003802485603040341d400c0c83c0c800c0c5c034107101c00740110051000b103490000f00700303901940714042000130810b01401411002c1c00203066a01d003249040030b10440780d1105940d00300c03800118801c101803040c284104407a0b403030118064480b5040015909040c0f201c4408a503200d0800007104400c0b0b552540d0403941064800b03407945842c2e14007240e07510b0f01d540e2088004e034025294003000804079280401d2460386aa003640f403817400341e00c0e103120080090704020074a90300b01c0e908114110100ca0007850031403005d1883d41d96001c4d50301c6a5000282500c160349403142c1400304002c00d010000e00049104800d132500464051005c1c4250304002e481c95026031800f428502881602000303001000c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 837400215 1250 837398965 837398999
    0x3040b07051c140a0f02121b0c01050709090e010203090c1203090a0e010801060b07080a050a090b13030c090c0909090f08040b0d05010b09010203030f040201020c1011010c05090607110613 82
    0x1410802000ca044a405e50503031040074241544182c0c0d4200040250000803112040707011080010b5046c0050018180d0840d84155181004180030704070402c9400424001c084148822800a50541c03d080810b26581c000c800011441180d1028041f810b040040080e034410b96001403100405075030f52407210110090a004044c2d10794203140001c900980c0d05803c41c2c10380780e40011064508500800c0840746500058404410070003249000104420315401a211030001104c20403052881d5250210980916500c2004001c0c207100003180090380240d05070b000c0300d80354040030440303804d945012005c008208400405c03091b0080360200d00000004064644140709200402a03a602c031072000425000b003c500d503005030b008000044407484400c0540b034000b441030045840c00383c0c440c000500784030b403034107400000104143c04040c0c03001400d0060f0b00043d8410b05000f4903000104010460318400c0303200c0603113010ad144c41c01a03c19203a010031100c01c2c0245000c0000d40716250306003041c0106501c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 837401465 1250 837400215 837400231
    0x210140c16180221041a0c120610140c011d07031412040302131e0221070822050109030503010801140c03160c060603060605030d0503040b07051c14 65
    0xb100c00000c0d20151071007201da11072246442045880c01c2e8100c4008880c500500c03c81b2110307024182004014400e0004901488a030710b038113600c5d4441442d1441c928440186480d10580c07143ca03560f0441038000400946c00384000c100540d40da40c0b2484064054424514146804180060b1503407546002082e80000d0303d11503134003030882d24010040580c1d200650915141948802c0004000521744481000351211103000041011310406030b58603000c1502186001445400148900c000c0001c012072400c4c806031114075110364140403000512110b40107000301144110080040c44210301c2c83c541c03c0c80740e0b9000009114008252a006000b0381080c4214405582080f00394100fa0020071074036440340c01e40821250440c1d07100c01e49519002c00f00c0d9110ba082c0100c2500c1034003c03440600981024502800012803510b2902c4103040c504015a1134040c100301e024402c0c007000070740a1451035000f1500786011512017914039110000341e002c1610741c4e04082c3c0b4202080b10380708103a105084c131a000e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 837402715 1250 837401465 837401489
    0x9070e10090803030703090f051b0a0819080a020a050a05010c090b0711010f03060504050a020301050108010608090d030515061801030b030f06040f0320030c12070210140c16 76
    0x15440058401c1402030007a110103800c10300019440c24801d5012814032401000c0429210303c25841b2142003003400c0c0c0304040c54000286001c0018100149000000d0040301c005211420700900c04c8050b041403040020981071000880c10b04451080000602c060342000c10354407240c07950b00c0c16034020a440c824103008280c03c2d0500183d100c3d00403055a1109030088948619154003e0046070b00032000d0b402070081c590f4400010030184c944d80f2955200304460b00c070058bd03a5041000241c42c5000583c0f20b9400c1000480c10041ca034100401e44c03465807a06c03800d02003081d454640d2100e26180b00da03041a500100080340070540140d064040da08440701c00e882c100500c1c1e225000f4152100510181f22940750302c80c00105d00000d4101e4510f420881c001d02d010301001e403c068002e24010700380100141c19500c086400c1c11254401e0117994202040c0301c02251411003958082134210541d04401018814041c40c80f1080d500d4100403200c054032180e050700d043c0b0207140c400c40d14100709401a4818541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 837403965 1250 837402715 837402739
    0x70e0a05010f050616030207080a03030f0614060f07061d060703320a0204050402130305010f0207150b010c2108010902040303200a05030a051b01060303050d1a09070e 73
    0x1c0300d4200d82c016104041c105500e004111400d00b00412582e800403811031040a90005050708107102010340c03e03100381d901141c2d0000305441c3e90309403461a000105c03505181c424202d1155200f10898041000001c98680c071580c441c200318008240d001d2191908209102045845010100d406032117136015450410800b60503d190030606022009034024500304011000000d51080e1306c039aa010301500005071400d40c440000c40d059822090040400d013400708014820098203009503408000000b03021030408415803a0446103c152142c1a03842c80c0e40e0f62540b02590740314000200620790050b481c0c8540d00c81c201c030720f14450300390506c00000203100c0320000701e8584d605008450480340c0590701c050242c111800244400341031091000c0040c4140301068000400c148040c203c50441c948900381c80f0040c0d445074560490701245160101d0745001c2d0140700090b0810165802c0100c00360002504001d041907070504050400070700381d400440b001c10030400c0e680c44070a2405800c1c0c1a505988141707 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 837405215 1250 837403965 837403979
    0x1b0601030210230f04060f020d140304050a1a1501170a05060303040e070203090103110702011707110f0102042c014b0501051e03040203070305070e0a0501 68
    0x1102804001e500900d0352088825561041d25030400c00700080d07080b80d50207104003004100315400550070b1203058102103410403074030390004078224000031a40060030b003851845000400854a402c0e0440b00240c001c80840c01b0300000704400c485e0190b10034a141840c0c0b00c6024040d030400c00131240310540513038210382040c0c1e551060394910704040d04102c001400b600e80d074108201601c8000d01981c0c0610007840002000980c4040083c081c44058014690700c65040c000101070707484000070320901003820080b08005076441075003250003181c1d000b5400700d00d4a813418203c4450140e44400500c600c5898160722080d50103600800448981c107400710f01101c030211181c8018401000b10540401c4c60000405c00c0c960011020541c1000c50301041e00e44940050f941c00085641c1c0031441068500d00045c1d078103807144941c00c800600000d00340b6030b080c82035048540043c906040d10002d19501e000c804181191010041200555446425603000c50303107030000100c07040303000c89504080c5400d08000103500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 837406465 1250 837405215 837405223
    0x331b241d2803030209030d09031e02030a030e060c0706030f0c081e070e0a03060c080a1b11070503030a171003020f1e1e04150501020705150702060f1b 66
    0x200080c21a100c07084000030020000948640364141e0a0680800c40c07207550b907400344403046400302e460720b40600703107425424144410708441c500d21216403692042200507981c0062201751550741890031101920441000c2051030255940304041d901c1100303404200a50075030403210f50404000010041c1803400c01c0c0c1150041c13800d4a00103600804002030481c010f030142c040d6070303100f2241d080980500001e400450318941507584140c035450b540d910314640448c3c2c0f05981a030040d0070044c0521801c949052410000c040d000140024450007401d10500d0801c01d100c0174000701401001c2c2e9440f82da513102e001d0070136800a000c800c101d000b160f000038920030740041c1000c1901d8010b81b010014160250502991030f01c0076683c3c43d9038844541d4170b030060740c2d3388400e10b1b0354031102040300d5a1840c5021080c40103582881c44411840000c80301d0500103660700003250350880300100d0303029070441c4000c582c214442c4030300b201c0a90400d0b00001d50f007129100903002400b01c0d58a20015210b0345e07030940300300c03511 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 837407715 1250 837406465 837406483
    0x190605131a0603060f011b02090c030f07020105040c05010c020f12010e19030206060d0602090907021c02060610051b0d0e0f040c170619331b241d 64
    0x1001712600301520311075102d541d8003101c0030088030344484d1014090300000c1c0001403c1303070040d4051000008200e040c0300d81c1240c15400c1490b0780004c0c041400e15607900c200144290140038100002d80300d030001991b980c907154090194029080e460f6000540034154060400c0c2c0301d61001912039840454134070019108280411900341d4042c14440c1c80305401c126003035542500c240d48203502803010041a5031a91101c502501458004100030150311542c0c0c5001c8401d80d24802c1550020003c100440c2c680d02c0340c01342803600c6898182d9864244640d5640004507074201030080e4490b240c02d0140c400e0704030f03070b180b2041a000c4400840611080d0100025600079070034207070010302402c1840e12140d00c1555141d07000440104015103c04418030a17034200d43c0503511405005408807130011501d5070264003044480c00180e00d00d007011210342001f510a0303c1c0e00801030885d2040d00e403810144040500c0d10424140380040782c00151500c0300100d4054040718030300000380c10039400c50b00c4e0b00c082c00285c0300300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 837408965 1250 837407715 837407719
    0x90216020a0b0309121b0114040b0112110405060d080a0905090109090312090c18050f092a0406150c1202190305091309030c0507051008190605131a060306 68
    0xc1480268400c284a5002040c0d00106c2c540e2990410758282401c1c084d1500d0610050500b034428941743c244041c0424041c1d101d0800070003040910400725004000d010802d52040e01c010541c0e032a500081184e048200b40054150380000c1072202a40360301460410841341c048985a030242d0301c824035001128001080240810586150190440142e0b04460341d41802150a004100e50303841c010100030811a94082406550301c04102c0c504440070641e41d0071000e000c0042003004032407003010440c0c00101108072008801c42c003000e0265034443d00408080e1100e02850540ca40f14844084c11101c030030001111000d211810f0844410320000e24010380303059010424100a03125101550150301c0900c28640140d030684c8040441410b50280b030707007002d100e550788204c01c1d4a60b0a0850500d40f0540285100300d00401d69102d426500002c00782c0c01c0345c0c02145501000550552030b6005000f96801142c1080d6620440c2d281e00b656039110380c50601029640000c0598a41d041081074441154007036 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 837410071 1106 837408965 837408973
    0x303041d090106050102190f02041503030806010201140c0903030408070621020a1d0d021f021e0d0f020709050c2503120510090216020a0b0309 63
    0xd80c1c007074031080080104600f4100007e454081741c07a4410181d00c100e141c3c400500032004240c1c0c070402d900910030000360758034000e90320722046903100036004200008005003d40d4018019140d02860400284065640c0c4178802083c41c0c02011655405101c00d01001c035100388104008070181010303454060824071560120840641000740780c5940300e005002520001d0f0f0032150355542c09450756100410543c03a070001c5441c540c69403030043c1d88260b5810461425540c00b034101041210940d09590b41100c002d000c109a05410f040d280c61140d04c0450200070052051848190f240c4a0f80305075894540d940001100380c0b88240c0c1c3e007000203000012203031a45503509008888480c80e050003000c000b800b03030320042e10145c0d202c2d905202103a254000162510000074282e005000c001c0c008540b1246005010340c60903d5143e800c0340900894800030444662010a40b80f00d003054000038 = true := by decide +kernel

theorem cover : BRFrame.Cov 837230215 837410071 := by
  have h0 := BRFrame.cov_init 837230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 837230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 837230215 ≤ n) (h2 : n < 837410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
